module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpEnd0
import CFSG.ClassicalInvolution.Q3.Sec13StarAE5Model
public import CFSG.ClassicalInvolution.Q3.Sec13EndMin

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem endY_mem_kPerp_iff (hs : StarHyp Ω) {L J : Subgroup G} (hL : L ∈ Ω)
    (hJ : J ∈ Ω) : J ∈ KPerp Ω L ↔ J = L ∨ Commutes L J := by
  constructor
  · intro hJK
    rcases Set.mem_insert_iff.mp hJK with h1 | h1
    · exact Or.inl h1
    · obtain ⟨-, hne, hJN⟩ := (TC.mem_omegaNbr_iff hs.thmD.hyp hs.thmD.two).mp h1
      have hJ2 : IsPGroup 2 J := hs.thmD.two J hJ
      have hL2 : IsPGroup 2 L := hs.thmD.two L hL
      obtain ⟨S, hS⟩ := (hJ2.to_sup_of_normal_right' hL2 hJN).exists_le_sylow
      exact Or.inr (Q3CP.l67Gen G Ω hs.thmD.hyp S L (TC.mem_RSet_of_isPGroup hL hL2) J
        (TC.mem_RSet_of_isPGroup hJ hJ2) (le_sup_right.trans hS) (le_sup_left.trans hS) hne.symm)
  · rintro (rfl | hc)
    · exact Set.mem_insert _ _
    · by_cases hJL : J = L
      · subst hJL
        exact Set.mem_insert _ _
      · have hJn : J ∈ omegaNbr Ω L :=
          (TC.mem_omegaNbr_iff hs.thmD.hyp hs.thmD.two).mpr
            ⟨hJ, hJL, Asc77.AscL62.le_normalizer_of_commutes hc.symm⟩
        exact Set.mem_insert_of_mem _ hJn

private theorem endY_mem_dComp_of_commutes {N M : Subgroup G} (hM : M ∈ Ω) (hne : N ≠ M)
    (hc : Commutes N M) : M ∈ dComp Ω N :=
  Relation.ReflTransGen.single ⟨hM, Disconnected.dAdj_of_commutes hM hne hc⟩

section Ident

variable {P : Set (Subgroup G)} {n : ℕ}

private theorem endY_map_comm (I : AEIdent P n) {L M : Subgroup G} (hL : L ∈ P) (hM : M ∈ P)
    (hc : Commutes L M) :
    ∀ x ∈ (L.subgroupOf (pSpan P)).map I.φ, ∀ y ∈ (M.subgroupOf (pSpan P)).map I.φ,
      x * y = y * x := by
  intro x hx y hy
  obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL hx
  obtain ⟨m, hm, rfl⟩ := I.exists_of_mem_map hM hy
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc l hl m hm)

private theorem endY_comm_of_map_comm (I : AEIdent P n) (hinj : Function.Injective I.φ)
    {L M : Subgroup G} (hL : L ∈ P) (hM : M ∈ P)
    (hc : ∀ x ∈ (L.subgroupOf (pSpan P)).map I.φ, ∀ y ∈ (M.subgroupOf (pSpan P)).map I.φ,
      x * y = y * x) : Commutes L M := by
  intro a ha b hb
  have h1 := hc _ (I.mem_map hL ha) _ (I.mem_map hM hb)
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (hinj h1)

private theorem endY_eq_of_map_eq (I : AEIdent P n) (hinj : Function.Injective I.φ)
    {L M : Subgroup G} (hL : L ∈ P) (hM : M ∈ P)
    (he : (L.subgroupOf (pSpan P)).map I.φ = (M.subgroupOf (pSpan P)).map I.φ) : L = M := by
  have hle : ∀ {A B : Subgroup G}, A ∈ P →
      (A.subgroupOf (pSpan P)).map I.φ ≤ (B.subgroupOf (pSpan P)).map I.φ → A ≤ B := by
    intro A B hA hAB x hx
    obtain ⟨y, hy, hyx⟩ := hAB (I.mem_map hA hx)
    rw [hinj hyx] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  exact le_antisymm (hle hL he.le) (hle hM he.ge)

private theorem endY_not_commutes_self (I : AEIdent P 5) {L : Subgroup G} (hL : L ∈ P) :
    ¬ Commutes L L := by
  intro hc
  obtain ⟨α, hα, b, hlab⟩ := I.label L hL
  obtain ⟨x, hx, x', hx', hne⟩ := AE.exists_not_comm_memBar (le_refl 5) α hα b
  have hcim := endY_map_comm I hL hL hc
  rw [hlab] at hcim
  exact hne (hcim x hx x' hx')

end Ident

private theorem endY_twin {P : Set (Subgroup G)} (I : AEIdent P 5) (hI : I.φ.ker = ⊥)
    {L : Subgroup G} (hL : L ∈ P) :
    ∃ L' ∈ P, L' ≠ L ∧ ∀ M ∈ P, Commutes L M ↔ M = L' := by
  have hinj : Function.Injective I.φ := (MonoidHom.ker_eq_bot_iff I.φ).mp hI
  obtain ⟨α, hα, b, hlab⟩ := I.label L hL
  obtain ⟨L', hL'P, hlab'⟩ := I.label_surj α hα (!b)
  have hne_b : AE.memBar α hα (!b) ≠ AE.memBar α hα b := by
    cases b
    · exact AE.memBar_true_ne_false (le_refl 5) α hα
    · exact (AE.memBar_true_ne_false (le_refl 5) α hα).symm
  have hL'L : L' ≠ L := by
    rintro rfl
    exact hne_b (hlab'.symm.trans hlab)
  have hcomm_twin : Commutes L L' := by
    refine endY_comm_of_map_comm I hinj hL hL'P ?_
    rw [hlab, hlab']
    exact TC.Thin.memBar_twin_comm α hα b
  refine ⟨L', hL'P, hL'L, fun M hM => ⟨fun hc => ?_, fun hM' => ?_⟩⟩
  · have hML : M ≠ L := by
      intro h1
      rw [h1] at hc
      exact endY_not_commutes_self I hL hc
    obtain ⟨β, hβ, c, hlabM⟩ := I.label M hM
    have hcim := endY_map_comm I hL hM hc
    rw [hlab, hlabM] at hcim
    have hne : AE.memBar α hα b ≠ AE.memBar β hβ c := by
      intro he
      apply hML
      apply endY_eq_of_map_eq I hinj hM hL
      rw [hlabM, hlab, he]
    obtain rfl : α = β := AE5Star.eq_of_commutes hα hβ hne hcim
    have hcb : c ≠ b := by
      intro h1
      subst h1
      exact hML (endY_eq_of_map_eq I hinj hM hL (hlabM.trans hlab.symm))
    obtain rfl : c = !b := by
      cases b <;> cases c <;> first | rfl | exact absurd rfl hcb
    apply endY_eq_of_map_eq I hinj hM hL'P
    rw [hlabM, hlab']
  · subst hM'
    exact hcomm_twin

namespace CaseBU

variable {K : Subgroup G} {P₁ P₂ : Set (Subgroup G)} {g u h e : G} {T : Subgroup G}

private theorem endY_mem_omega₂ (c : CaseBU Ω K P₁ P₂ g u h e T) {M : Subgroup G}
    (hM : M ∈ P₂) : M ∈ Ω := by
  have key : ∀ {N : Subgroup G},
      Relation.ReflTransGen (fun A B : Subgroup G => B ∈ Ω ∧ Disconnected.dAdj Ω A B) K N →
        N ∈ P₂ → N ∈ Ω := by
    intro N hd
    induction hd with
    | refl => exact fun hN => absurd hN (Set.disjoint_left.mp c.disj c.hK)
    | tail _ hbc _ => exact fun _ => hbc.1
  have hd : M ∈ dComp Ω K := by
    rw [c.dcomp]
    exact Set.mem_union_right _ hM
  exact key hd hM

private theorem endY_mem_centMembers₂ (c : CaseBU Ω K P₁ P₂ g u h e T) {M : Subgroup G}
    (hM : M ∈ P₂) : M ∈ Generic.centMembers Ω u :=
  ⟨endY_mem_omega₂ c hM, c.P₂_u M hM⟩

private theorem endY_not_mem_P₁ (c : CaseBU Ω K P₁ P₂ g u h e T) {M : Subgroup G}
    (hM : M ∈ Generic.centMembers Ω u) : M ∉ P₁ :=
  fun h1 => c.P₁_u M h1 hM.2

private theorem endY_image_eq (c : CaseBU Ω K P₁ P₂ g u h e T) : conjSub g '' P₁ = P₂ := by
  ext L
  constructor
  · rintro ⟨L₁, hL₁, rfl⟩
    exact (c.swap _).mpr (by rw [conjSub_inv_conjSub]; exact hL₁)
  · intro hL
    exact ⟨conjSub g⁻¹ L, (c.swap L).mp hL, conjSub_conjSub_inv g L⟩

private theorem endY_mem₂_of_mem₁ (c : CaseBU Ω K P₁ P₂ g u h e T) {L : Subgroup G}
    (hL : L ∈ P₁) : conjSub g L ∈ P₂ :=
  (c.swap _).mpr (by rw [conjSub_inv_conjSub]; exact hL)

private theorem endY_conj_mem₂ (c : CaseBU Ω K P₁ P₂ g u h e T) {M M' : Subgroup G}
    (hM : M ∈ P₂) (hM' : M' ∈ P₂) :
    ∃ x ∈ pSpan (Generic.centMembers Ω u), conjSub x M = M' := by
  obtain ⟨x₁, hx₁, hx₁M⟩ := c.trans _ ((c.swap M).mp hM) _ ((c.swap M').mp hM')
  refine ⟨g * x₁ * g⁻¹, ?_, ?_⟩
  · have hmem : (MulAut.conj g : G →* G) x₁ ∈ pSpan P₂ := by
      rw [← endY_image_eq c, pSpan_image_conjSub]
      exact Subgroup.mem_map_of_mem _ hx₁
    have hsub : pSpan P₂ ≤ pSpan (Generic.centMembers Ω u) :=
      pSpan_le fun L hL => le_pSpan (endY_mem_centMembers₂ c hL)
    exact hsub hmem
  · calc conjSub (g * x₁ * g⁻¹) M = conjSub g (conjSub x₁ (conjSub g⁻¹ M)) := by
          rw [conjSub_mul, conjSub_mul]
      _ = conjSub g (conjSub g⁻¹ M') := by rw [hx₁M]
      _ = M' := conjSub_conjSub_inv g M'

private theorem endY_kPerp_pair (hs : StarHyp Ω) (c : CaseBU Ω K P₁ P₂ g u h e T)
    (I : AEIdent P₁ 5) (hI : I.φ.ker = ⊥) {N : Subgroup G} (hN : N ∈ P₂) :
    ∃ N' ∈ P₂, N' ≠ N ∧ KPerp Ω N ∩ Generic.centMembers Ω u = {N, N'} := by
  obtain ⟨N₁', hN₁'P, hne₁, htw⟩ := endY_twin I hI ((c.swap N).mp hN)
  have hNΩ : N ∈ Ω := endY_mem_omega₂ c hN
  have hN'P : conjSub g N₁' ∈ P₂ := endY_mem₂_of_mem₁ c hN₁'P
  have hN'Ω : conjSub g N₁' ∈ Ω := endY_mem_omega₂ c hN'P
  refine ⟨conjSub g N₁', hN'P, ?_, ?_⟩
  · intro h'
    apply hne₁
    have h2 : conjSub g N₁' = conjSub g (conjSub g⁻¹ N) := by
      rw [h', conjSub_conjSub_inv]
    exact conjSub_injective g h2
  · ext M
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hMK, hMP⟩
      by_cases hMN : M = N
      · exact Or.inl hMN
      · right
        have hc : Commutes N M := ((endY_mem_kPerp_iff hs hNΩ hMP.1).mp hMK).resolve_left hMN
        have hNd : N ∈ dComp Ω K := by
          rw [c.dcomp]
          exact Set.mem_union_right _ hN
        have hMd : M ∈ dComp Ω K :=
          Relation.ReflTransGen.trans hNd (endY_mem_dComp_of_commutes hMP.1 (Ne.symm hMN) hc)
        rw [c.dcomp] at hMd
        rcases (Set.mem_union _ _ _).mp hMd with hM1 | hM2
        · exact absurd hM1 (endY_not_mem_P₁ c hMP)
        · have hc' : Commutes (conjSub g⁻¹ N) (conjSub g⁻¹ M) :=
            (commutes_conjSub_iff g⁻¹).mpr hc
          have hM1' : conjSub g⁻¹ M = N₁' := (htw _ ((c.swap M).mp hM2)).mp hc'
          calc M = conjSub g (conjSub g⁻¹ M) := (conjSub_conjSub_inv g M).symm
            _ = conjSub g N₁' := by rw [hM1']
    · rintro (rfl | rfl)
      · exact ⟨Set.mem_insert _ _, endY_mem_centMembers₂ c hN⟩
      · refine ⟨(endY_mem_kPerp_iff hs hNΩ hN'Ω).mpr (Or.inr ?_),
          endY_mem_centMembers₂ c hN'P⟩
        have hc : Commutes (conjSub g⁻¹ N) N₁' := (htw N₁' hN₁'P).mpr rfl
        have hc' := hc.conjSub g
        rwa [conjSub_conjSub_inv] at hc'

private theorem endY_ncard_conj (hs : StarHyp Ω) {N : Subgroup G} {x : G}
    (hN : N ∈ Generic.centMembers Ω u) (hx : x ∈ pSpan (Generic.centMembers Ω u)) :
    (KPerp Ω (conjSub x N) ∩ Generic.centMembers Ω u).ncard =
      (KPerp Ω N ∩ Generic.centMembers Ω u).ncard := by
  have hxN : conjSub x N ∈ Generic.centMembers Ω u := hs.conjSub_mem_centMembers hN hx
  have key : KPerp Ω (conjSub x N) ∩ Generic.centMembers Ω u =
      conjSub x '' (KPerp Ω N ∩ Generic.centMembers Ω u) := by
    ext M
    constructor
    · rintro ⟨hMK, hMP⟩
      have hM' : conjSub x⁻¹ M ∈ Generic.centMembers Ω u :=
        hs.conjSub_mem_centMembers hMP (Subgroup.inv_mem _ hx)
      refine ⟨conjSub x⁻¹ M, ⟨?_, hM'⟩, conjSub_conjSub_inv x M⟩
      rcases (endY_mem_kPerp_iff hs hxN.1 hMP.1).mp hMK with h1 | h1
      · rw [h1, conjSub_inv_conjSub]
        exact Set.mem_insert _ _
      · refine (endY_mem_kPerp_iff hs hN.1 hM'.1).mpr (Or.inr ?_)
        exact (commutes_conjSub_iff x).mp (by rw [conjSub_conjSub_inv]; exact h1)
    · rintro ⟨M', ⟨hM'K, hM'P⟩, rfl⟩
      refine ⟨?_, hs.conjSub_mem_centMembers hM'P hx⟩
      rcases (endY_mem_kPerp_iff hs hN.1 hM'P.1).mp hM'K with h1 | h1
      · rw [h1]
        exact Set.mem_insert _ _
      · exact (endY_mem_kPerp_iff hs hxN.1 (hs.conjSub_mem_centMembers hM'P hx).1).mpr
          (Or.inr (h1.conjSub x))
  rw [key]
  exact Set.ncard_image_of_injective _ (conjSub_injective x)

theorem oneClass (c : CaseBU Ω K P₁ P₂ g u h e T) (I : AEIdent P₁ 5) (hI : I.φ.ker = ⊥) :
    ∀ L ∈ Generic.centMembers Ω u, ∀ L' ∈ Generic.centMembers Ω u,
      ∃ x ∈ pSpan (Generic.centMembers Ω u), conjSub x L = L' := by
  clear hI I
  have hsec : SectionConcl (Generic.centMembers Ω u) :=
    c.hyp.toStarHyp.sectionConcl_centMembers c.u_ne
  rcases hsec with ⟨⟨A, hA, B, hB, hAB⟩, hcomm⟩ | ⟨htr, -, -⟩
  · exfalso
    have hN₀P : conjSub g K ∈ Generic.centMembers Ω u := endY_mem_centMembers₂ c c.gP
    obtain ⟨M, hM, hNM⟩ : ∃ M ∈ Generic.centMembers Ω u,
        ¬ ∃ x ∈ pSpan (Generic.centMembers Ω u), conjSub x (conjSub g K) = M := by
      by_cases hNA : ∃ x ∈ pSpan (Generic.centMembers Ω u), conjSub x (conjSub g K) = A
      · by_cases hNB : ∃ x ∈ pSpan (Generic.centMembers Ω u), conjSub x (conjSub g K) = B
        · exfalso
          obtain ⟨x, hx, hxA⟩ := hNA
          obtain ⟨y, hy, hyB⟩ := hNB
          apply hAB
          refine ⟨y * x⁻¹, Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hx), ?_⟩
          rw [conjSub_mul, ← hxA, conjSub_inv_conjSub, hyB]
        · exact ⟨B, hB, hNB⟩
      · exact ⟨A, hA, hNA⟩
    have hMne : conjSub g K ≠ M := by
      intro h'
      apply hNM
      exact ⟨1, Subgroup.one_mem _, by rw [conjSub_one]; exact h'⟩
    have hcM : Commutes (conjSub g K) M := hcomm _ hN₀P _ hM hNM
    have hNd : conjSub g K ∈ dComp Ω K := by
      rw [c.dcomp]
      exact Set.mem_union_right _ c.gP
    have hMd : M ∈ dComp Ω K :=
      Relation.ReflTransGen.trans hNd (endY_mem_dComp_of_commutes hM.1 hMne hcM)
    rw [c.dcomp] at hMd
    rcases (Set.mem_union _ _ _).mp hMd with hM1 | hM2
    · exact endY_not_mem_P₁ c hM hM1
    · obtain ⟨x, hx, hxM⟩ := endY_conj_mem₂ c c.gP hM2
      exact hNM ⟨x, hx, hxM⟩
  · exact htr

theorem ncard_kPerp (c : CaseBU Ω K P₁ P₂ g u h e T) (I : AEIdent P₁ 5) (hI : I.φ.ker = ⊥) :
    ∀ L ∈ Generic.centMembers Ω u, (KPerp Ω L ∩ Generic.centMembers Ω u).ncard = 2 := by
  intro L hL
  have hN₀P : conjSub g K ∈ Generic.centMembers Ω u := endY_mem_centMembers₂ c c.gP
  obtain ⟨x, hx, hxL⟩ := oneClass c I hI _ hN₀P L hL
  rw [← hxL, endY_ncard_conj c.hyp.toStarHyp hN₀P hx]
  obtain ⟨N', -, hne, heq⟩ := endY_kPerp_pair c.hyp.toStarHyp c I hI c.gP
  rw [heq]
  exact Set.ncard_pair hne.symm

end CaseBU

end CFSG.ClassicalInvolution.Q3.Sec13
