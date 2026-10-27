module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpEnd0
import CFSG.ClassicalInvolution.Q3.Sec13End11
import CFSG.ClassicalInvolution.Q3.Q3CLWylA
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Sec13PerpD
public import CFSG.ClassicalInvolution.Q3.Sec13PerpEndModel
public import CFSG.ClassicalInvolution.Q3.Sec13PerpStar
public import CFSG.ClassicalInvolution.Q3.TL3T35
public import CFSG.ClassicalInvolution.Q3.TL3T38

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.TL4

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem endU_even_supp : ∀ α : Finset (Fin 5), α.card = 4 → ∀ v : Fin 5 → ZMod 2,
    (∀ x, x ∉ α → v x = 0) → v 0 + v 1 + v 2 + v 3 + v 4 = 0 →
      v = 0 ∨ (∀ x, v x = if x ∈ α then 1 else 0) ∨
        ∃ i j : Fin 5, i ∈ α ∧ j ∈ α ∧ i ≠ j ∧ v = Pi.single i 1 + Pi.single j 1 := by
  decide +kernel

private theorem endU_memAt_le (α : Finset (Fin 5)) (hα : α.card = 4) (b : Bool) :
    memAt α hα b ≤ aeSub 5 := by
  cases b
  · exact memKStar_le_aeSub _
  · exact memK_le_aeSub _

private theorem endU_mul_self_of_mem_both (α : Finset (Fin 5)) (hα : α.card = 4) {a : Wr 5}
    (h1 : a ∈ memK (emb α hα)) (h2 : a ∈ memKStar (emb α hα)) : a * a = 1 := by
  obtain ⟨k, hk, rfl⟩ := h1
  obtain ⟨k', hk', hkk⟩ := h2
  have hkeq : k' = k := embed_injective _ hkk
  rw [hkeq] at hk'
  have hzz : zQ * zQ = 1 := by decide +kernel
  rcases inf_kQ_kQStar k hk hk' with rfl | rfl
  · rw [map_one, one_mul]
  · rw [← map_mul, hzz, map_one]

private theorem endU_vec_of_permBar {x : AEQ 5} (hx : permBar 5 x = 1) :
    ∃ v : Fin 5 → ZMod 2, x = mkQ 5 (Wr.ofVec v) := by
  obtain ⟨a, rfl⟩ : ∃ a : Wr 5, mkQ 5 a = x := QuotientGroup.mk_surjective x
  have ha : a.perm = 1 := (permBar_mkQ a).symm.trans hx
  have hA : a = Wr.ofVec a.vec := Wr.ext rfl ha
  exact ⟨a.vec, congrArg (mkQ 5) hA⟩

private theorem endU_mul_memBar_vec {α : Finset (Fin 5)} (hα : α.card = 4) {b : Bool}
    {x y : AEQ 5} (hx : x ∈ memBar α hα b) (hy : y ∈ memBar α hα (!b))
    (hxy : permBar 5 (x * y) = 1) :
    x * y = 1 ∨ x * y = zBar α hα ∨
      ∃ i j : Fin 5, i ∈ α ∧ j ∈ α ∧ i ≠ j ∧
        x * y = mkQ 5 (Wr.ofVec (Pi.single i 1 + Pi.single j 1)) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨a', ha', rfl⟩ := hy
  rw [← map_mul] at hxy ⊢
  have hsa : Wr.wsum a = 0 := (mem_aeSub.mp (endU_memAt_le α hα b ha)).1
  have hsa' : Wr.wsum a' = 0 := (mem_aeSub.mp (endU_memAt_le α hα (!b) ha')).1
  have hperm : (a * a').perm = 1 := (permBar_mkQ (a * a')).symm.trans hxy
  have hsupp : SupportedOn (a * a') (Set.range (emb α hα)) :=
    (supportedOn_of_mem_memAt ha).mul (supportedOn_of_mem_memAt ha')
  have hv : ∀ x, x ∉ α → (a * a').vec x = 0 := by
    intro x hx
    refine (hsupp x ?_).1
    rw [range_emb]
    exact hx
  have hwsum : Wr.wsum (a * a') = 0 := by
    rw [wsum_mul, hsa, hsa', add_zero]
  have hsum : (a * a').vec 0 + (a * a').vec 1 + (a * a').vec 2 + (a * a').vec 3 +
      (a * a').vec 4 = 0 :=
    (Fin.sum_univ_five (a * a').vec).symm.trans hwsum
  rcases endU_even_supp α hα (a * a').vec hv hsum with h0 | hind | ⟨i, j, hi, hj, hij, hvij⟩
  · left
    have h1 : a * a' = 1 := Wr.ext h0 hperm
    rw [h1, map_one]
  · right
    left
    have h1 : a * a' = zOf (emb α hα) := by
      refine Wr.ext (funext fun x => ?_) (hperm.trans (zOf_perm _).symm)
      rw [hind x, zOf_vec_apply]
      by_cases hx : x ∈ α
      · have hx' : x ∈ Set.range (emb α hα) := by
          rw [range_emb]
          exact hx
        rw [if_pos hx, if_pos hx']
      · have hx' : x ∉ Set.range (emb α hα) := by
          rw [range_emb]
          exact hx
        rw [if_neg hx, if_neg hx']
    exact congrArg (mkQ 5) h1
  · right
    right
    have h1 : a * a' = Wr.ofVec (Pi.single i 1 + Pi.single j 1) := Wr.ext hvij hperm
    exact ⟨i, j, hi, hj, hij, congrArg (mkQ 5) h1⟩

private theorem endU_mul_self_of_memBar_both {α : Finset (Fin 5)} (hα : α.card = 4) {b : Bool}
    {x : AEQ 5} (hx : x ∈ memBar α hα b) (hx' : x ∈ memBar α hα (!b)) : x * x = 1 := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨a', ha', h'⟩ := hx'
  have haa : a * a = 1 := by
    rcases mkQ_eq_iff.mp h'.symm with h1 | h1
    · have heq : a = a' := inv_mul_eq_one.mp h1
      rw [← heq] at ha'
      have hboth : a ∈ memK (emb α hα) ∧ a ∈ memKStar (emb α hα) := by
        cases b
        · exact ⟨ha', ha⟩
        · exact ⟨ha, ha'⟩
      exact endU_mul_self_of_mem_both α hα hboth.1 hboth.2
    · exfalso
      have ha'eq : a' = a * Wr.allOnes 5 := by
        rw [← h1, mul_inv_cancel_left]
      obtain ⟨i, hi⟩ : ∃ i : Fin 5, i ∉ α := by
        by_contra hcon
        have huniv : α = Finset.univ := Finset.eq_univ_iff_forall.mpr fun i => by
          by_contra hi
          exact hcon ⟨i, hi⟩
        rw [huniv, Finset.card_univ, Fintype.card_fin] at hα
        exact absurd hα (by norm_num)
      have hi' : i ∉ Set.range (emb α hα) := by
        rw [range_emb]
        exact hi
      have hai : a.vec i = 0 := ((supportedOn_of_mem_memAt ha) i hi').1
      have ha'i : a'.vec i = 0 := ((supportedOn_of_mem_memAt ha') i hi').1
      have h2 : (a * Wr.allOnes 5).vec i = a.vec i + 1 := rfl
      rw [← ha'eq, ha'i, hai, zero_add] at h2
      exact absurd h2 (by decide)
  rw [← map_mul, haa, map_one]

private theorem endU_centralizer_five : ∀ σ : Equiv.Perm (Fin 5),
    σ * (Equiv.swap 0 1 * Equiv.swap 1 2) = (Equiv.swap 0 1 * Equiv.swap 1 2) * σ →
    σ * (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) =
      (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) * σ →
    σ = 1 := by
  decide +kernel

private theorem endU_eq_one_of_centralizes_alt (σ : Equiv.Perm (Fin 5))
    (h : ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 → σ * τ = τ * σ) : σ = 1 := by
  apply endU_centralizer_five σ
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)

private theorem endU_mkQ_ofVec_comm (v w : Fin 5 → ZMod 2) :
    mkQ 5 (Wr.ofVec v) * mkQ 5 (Wr.ofVec w) = mkQ 5 (Wr.ofVec w) * mkQ 5 (Wr.ofVec v) := by
  rw [← map_mul, ← map_mul, TL4.ofVec_mul_ofVec, TL4.ofVec_mul_ofVec, add_comm]

private theorem endU_permBar_eq_one_of_two_normal {X : Type} [Group X] (φ : X →* AEQ 5)
    (hφ : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → ∃ x : X, permBar 5 (φ x) = σ)
    (N : Subgroup X) [N.Normal] (hN : IsPGroup 2 N) {n : X} (hn : n ∈ N) :
    permBar 5 (φ n) = 1 := by
  obtain ⟨P, hP⟩ : ∃ P : X →* Equiv.Perm (Fin 5), ∀ x, P x = permBar 5 (φ x) :=
    ⟨(permBar 5).comp φ, fun x => rfl⟩
  have hconj : ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 →
      ∀ g ∈ N.map P, τ * g * τ⁻¹ ∈ N.map P := by
    intro τ hτ g hg
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨x, hx⟩ := hφ τ hτ
    have hPx : P x = τ := (hP x).trans hx
    refine Subgroup.mem_map.mpr ⟨x * m * x⁻¹, Subgroup.Normal.conj_mem ‹N.Normal› m hm x, ?_⟩
    rw [map_mul, map_mul, map_inv, hPx]
  have hA : ∀ c : Equiv.Perm (Fin 5), c ∈ N.map P → Equiv.Perm.sign c = 1 → c = 1 := by
    intro c hc hsign
    haveI hTn : ((N.map P).subgroupOf (alternatingGroup (Fin 5))).Normal :=
      ⟨fun t ht g => by
        rw [Subgroup.mem_subgroupOf] at ht ⊢
        have h1 : ((g * t * g⁻¹ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
            (g : Equiv.Perm (Fin 5)) * (t : Equiv.Perm (Fin 5)) *
              (g : Equiv.Perm (Fin 5))⁻¹ := by
          simp
        rw [h1]
        exact hconj _ (Equiv.Perm.mem_alternatingGroup.mp g.2) _ ht⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((N.map P).subgroupOf (alternatingGroup (Fin 5))) with hbot | htop
    · have hmem : (⟨c, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩ :
          alternatingGroup (Fin 5)) ∈ (N.map P).subgroupOf (alternatingGroup (Fin 5)) :=
        Subgroup.mem_subgroupOf.mpr hc
      rw [hbot, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exfalso
      obtain ⟨c3, hc3def⟩ : ∃ c3 : Equiv.Perm (Fin 5), c3 = Equiv.swap 0 1 * Equiv.swap 1 2 :=
        ⟨_, rfl⟩
      have hc3A : c3 ∈ alternatingGroup (Fin 5) :=
        Equiv.Perm.mem_alternatingGroup.mpr (by rw [hc3def]; decide +kernel)
      have hmem : (⟨c3, hc3A⟩ : alternatingGroup (Fin 5)) ∈
          (N.map P).subgroupOf (alternatingGroup (Fin 5)) := by
        rw [htop]
        exact Subgroup.mem_top _
      have h3mem : c3 ∈ N.map P := Subgroup.mem_subgroupOf.mp hmem
      obtain ⟨m, hm, hPm⟩ := Subgroup.mem_map.mp h3mem
      obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hN) ⟨m, hm⟩
      have hmk : m ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hc3k : c3 ^ 2 ^ k = 1 := by
        rw [← hPm, ← map_pow, hmk, map_one]
      have hc3pow : c3 ^ 3 = 1 := by
        rw [hc3def]
        decide +kernel
      have hc3ne : c3 ≠ 1 := by
        rw [hc3def]
        decide +kernel
      have hord : orderOf c3 = 3 := orderOf_eq_prime hc3pow hc3ne
      have hdvd := orderOf_dvd_of_pow_eq_one hc3k
      rw [hord] at hdvd
      have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      exact absurd h32 (by norm_num)
  have hcent : ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 → P n * τ = τ * P n := by
    intro τ hτ
    have hs : P n ∈ N.map P := Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    have hconjs : τ * P n * τ⁻¹ ∈ N.map P := hconj τ hτ _ hs
    have hc : P n * (τ * P n * τ⁻¹)⁻¹ ∈ N.map P :=
      (N.map P).mul_mem hs ((N.map P).inv_mem hconjs)
    have hsign : Equiv.Perm.sign (P n * (τ * P n * τ⁻¹)⁻¹) = 1 := by
      simp [map_mul, map_inv, hτ]
    have h1 : P n = τ * P n * τ⁻¹ := mul_inv_eq_one.mp (hA _ hc hsign)
    calc P n * τ = (τ * P n * τ⁻¹) * τ := by rw [← h1]
      _ = τ * P n := inv_mul_cancel_right _ _
  rw [← hP n]
  exact endU_eq_one_of_centralizes_alt (P n) hcent


private theorem endU_mem_RSet (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) {R : Subgroup G} (hR : R ∈ Ω) :
    R ∈ RSet Ω :=
  mem_RSet_iff.mpr ⟨R, hR, le_rfl, h2 R hR, fun R' hR'R _ hle => le_antisymm hR'R hle⟩

private theorem endU_commutes_of_two_group (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J)
    {T : Subgroup G} (hT : IsPGroup 2 ↥T) {R R' : Subgroup G} (hR : R ∈ Ω) (hR' : R' ∈ Ω)
    (hRT : R ≤ T) (hR'T : R' ≤ T) (hne : R ≠ R') : Commutes R R' := by
  obtain ⟨S, hS⟩ := hT.exists_le_sylow
  exact Q3CP.l67Gen G Ω hΩ S R (endU_mem_RSet h2 hR) R' (endU_mem_RSet h2 hR')
    (hRT.trans hS) (hR'T.trans hS) hne

private theorem endU_comm_symm {A B : Subgroup G} (h : Commutes A B) : Commutes B A :=
  fun x hx y hy => (h y hy x hx).symm

private theorem endU_conj_fix {M : Subgroup G} {x : G} (hc : ∀ a ∈ M, a * x = x * a) :
    conjSub x M = M := by
  ext m
  rw [mem_conjSub_iff]
  constructor
  · intro hm
    have hcm := hc _ hm
    have h3 : x⁻¹ * m * x = m := by
      calc x⁻¹ * m * x = (x⁻¹ * m * x * x) * x⁻¹ := by group
        _ = (x * (x⁻¹ * m * x)) * x⁻¹ := by rw [hcm]
        _ = m := by group
    rw [h3] at hm
    exact hm
  · intro hm
    have hmx := hc m hm
    have h3 : x⁻¹ * m * x = m := by
      calc x⁻¹ * m * x = x⁻¹ * (m * x) := by group
        _ = x⁻¹ * (x * m) := by rw [hmx]
        _ = m := by group
    rw [h3]
    exact hm

private theorem endU_omegaNbr_of_comm (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω)
    {M X : Subgroup G} (hX : X ∈ Ω) (hne : X ≠ M) (hc : Commutes M X) :
    X ∈ omegaNbr Ω M := by
  refine (TC.mem_omegaNbr_iff hΩ h2).mpr ⟨hX, hne, ?_⟩
  intro x hx
  rw [mem_normalizer_iff_conjSub_eq]
  exact endU_conj_fix (fun a ha => hc a ha x hx)

private theorem endU_comm_of_omegaNbr (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω)
    {M X : Subgroup G} (hM : M ∈ Ω) (hX : X ∈ omegaNbr Ω M) : Commutes M X :=
  TC.Thin.comm_of_mem_omegaNbr hΩ h2 hM hX

private theorem endU_mem_kperp_of_comm (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω)
    {M X : Subgroup G} (hM : M ∈ Ω) (hX : X ∈ Ω) (hc : Commutes M X) : X ∈ KPerp Ω M := by
  by_cases hXM : X = M
  · rw [hXM]
    exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (endU_omegaNbr_of_comm h2 hΩ hX hXM hc)

private theorem endU_dComp_of_omegaNbr {M X : Subgroup G} (hX : X ∈ omegaNbr Ω M) :
    X ∈ dComp Ω M :=
  Relation.ReflTransGen.single ⟨hX.1, Or.inl hX⟩

private theorem endU_mem_Omega_of_dComp {K X : Subgroup G} (hX : X ∈ dComp Ω K) (hne : X ≠ K) :
    X ∈ Ω := by
  rcases Relation.ReflTransGen.cases_tail hX with h | ⟨Y, -, hY⟩
  · exact absurd h hne
  · exact hY.1

private theorem endU_dComp_eq {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ dComp Ω K) :
    dComp Ω L = dComp Ω K := by
  ext J
  constructor
  · intro hJ
    exact Relation.ReflTransGen.trans hL hJ
  · intro hJ
    exact Relation.ReflTransGen.trans (reflTransGen_dAdj_symm hK hL) hJ

section AELayer

variable {P : Set (Subgroup G)} (I : AEIdent P 5)

private theorem endU_not_disjoint {α β : Finset (Fin 5)} (hα : α.card = 4) (hβ : β.card = 4) :
    ¬ Disjoint α β := by
  intro hd
  have h1 := Finset.card_union_of_disjoint hd
  have h2 := Finset.card_le_univ (α ∪ β)
  simp only [Fintype.card_fin] at h2
  omega

private theorem endU_same_set {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    {α β : Finset (Fin 5)} {hα : α.card = 4} {hβ : β.card = 4} {b c : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    (hlab' : (L'.subgroupOf (pSpan P)).map I.φ = AE.memBar β hβ c)
    (hc : Commutes L L') : α = β := by
  by_contra hne
  apply endU_not_disjoint hα hβ
  refine AE.disjoint_of_zBar_comm (h := hα) (h' := hβ) hne (c := c) fun y hy => ?_
  have hz : AE.zBar α hα ∈ (L.subgroupOf (pSpan P)).map I.φ := by
    rw [hlab]
    exact AE.zBar_mem_memBar α hα b
  have hy' : y ∈ (L'.subgroupOf (pSpan P)).map I.φ := by
    rw [hlab']
    exact hy
  obtain ⟨l, hl, hlz⟩ := I.exists_of_mem_map hL hz
  obtain ⟨l', hl', hly⟩ := I.exists_of_mem_map hL' hy'
  rw [← hlz, ← hly, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc l hl l' hl')

private theorem endU_memBar_ne (α : Finset (Fin 5)) (hα : α.card = 4) (b : Bool) :
    AE.memBar α hα b ≠ AE.memBar α hα (!b) := by
  cases b
  · exact fun h => AE.memBar_true_ne_false (by norm_num) α hα h.symm
  · exact AE.memBar_true_ne_false (by norm_num) α hα

private theorem endU_twin_comm (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J)
    (hPΩ : ∀ L ∈ P, L ∈ Ω) (hk : IsPGroup 2 ↥I.φ.ker)
    {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P) {α : Finset (Fin 5)} {hα : α.card = 4}
    {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    (hlab' : (L'.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα (!b)) : Commutes L L' := by
  set S' : Set (Subgroup (AE.AEQ 5)) := {AE.memBar α hα b, AE.memBar α hα (!b)} with hS'
  have hS'2 : ∀ X ∈ S', IsPGroup 2 ↥X := by
    intro X hX
    rcases hX with rfl | rfl <;>
      exact IsPGroup.of_card (n := 3) (by rw [AE.natCard_memBar (by norm_num) α hα _]; norm_num)
  have hS'c : ∀ X ∈ S', ∀ Y ∈ S', X ≠ Y → Commutes X Y := by
    intro X hX Y hY hXY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact absurd rfl hXY
    · exact TC.Thin.memBar_twin_comm α hα b
    · have := TC.Thin.memBar_twin_comm α hα (!b)
      simp only [Bool.not_not] at this
      exact this
    · exact absurd rfl hXY
  have hp : IsPGroup 2 ↥(pSpan S') := isPGroup_pSpan_of_comm hS'2 hS'c
  have hT : IsPGroup 2 ↥(((pSpan S').comap I.φ).map (pSpan P).subtype) :=
    ((hp.comap_of_ker_isPGroup I.φ hk).map _)
  have hX1 : AE.memBar α hα b ≤ pSpan S' :=
    le_iSup₂ (f := fun (X : Subgroup (AE.AEQ 5)) (_ : X ∈ S') => X) (AE.memBar α hα b)
      (Set.mem_insert _ _)
  have hX2 : AE.memBar α hα (!b) ≤ pSpan S' :=
    le_iSup₂ (f := fun (X : Subgroup (AE.AEQ 5)) (_ : X ∈ S') => X) (AE.memBar α hα (!b))
      (Set.mem_insert_of_mem _ rfl)
  have hLT : L ≤ ((pSpan S').comap I.φ).map (pSpan P).subtype := by
    intro l hl
    refine ⟨⟨l, le_pSpan hL hl⟩, ?_, rfl⟩
    have hm := I.mem_map hL hl
    rw [hlab] at hm
    exact hX1 hm
  have hL'T : L' ≤ ((pSpan S').comap I.φ).map (pSpan P).subtype := by
    intro l hl
    refine ⟨⟨l, le_pSpan hL' hl⟩, ?_, rfl⟩
    have hm := I.mem_map hL' hl
    rw [hlab'] at hm
    exact hX2 hm
  have hne : L ≠ L' := by
    rintro rfl
    exact endU_memBar_ne α hα b (hlab.symm.trans hlab')
  exact endU_commutes_of_two_group hΩ h2 hT (hPΩ L hL) (hPΩ L' hL') hLT hL'T hne

private theorem endU_eq_of_map_eq (hI : I.φ.ker = ⊥) (h8 : ∀ L ∈ P, Nat.card L = 8)
    {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    (h : (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ) : L = L' := by
  have hinj : Function.Injective I.φ := (MonoidHom.ker_eq_bot_iff I.φ).mp hI
  have hle : L ≤ L' := by
    intro l hl
    have hm := I.mem_map hL hl
    rw [h] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    have hxl : x = ⟨l, le_pSpan hL hl⟩ := hinj hxe
    have hx' := Subgroup.mem_subgroupOf.mp hx
    rw [hxl] at hx'
    exact hx'
  exact Subgroup.eq_of_le_of_card_ge hle (by simp [h8 L hL, h8 L' hL'])

end AELayer

private theorem endU_isSylow2_self (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) {K : Subgroup G}
    (hK : K ∈ Ω) : IsSylow2In K K :=
  ⟨le_rfl, h2 K hK, fun _ hVK _ hKV => le_antisymm hVK hKV⟩

private def endU_repOf (h : EndHyp Ω) {W R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G}
    (hr : r ∈ R) (hrW : r ∉ W) : Asc77.Thompson.Rep Ω W :=
  ⟨R, R, r, (h.mem_dSet_iff.mp hR).1, hR,
    endU_isSylow2_self h.thmD.two (h.mem_dSet_iff.mp hR).1, hr, hrW⟩

private noncomputable def endU_rep (h : EndHyp Ω) {W R : Subgroup G} (hW : W ∈ WSet Ω)
    (hR : R ∈ DSet Ω W) : Asc77.Thompson.Rep Ω W :=
  endU_repOf h hR (Q3CL.Thompson.exists_not_mem_of_mem_D h.thmD.hyp hW hR).choose_spec.1
    (Q3CL.Thompson.exists_not_mem_of_mem_D h.thmD.hyp hW hR).choose_spec.2

private theorem endU_mem_kperp_iff {R T : Subgroup G} :
    T ∈ KPerp Ω R ↔ T = R ∨ T ∈ omegaNbr Ω R :=
  Iff.rfl

private theorem endU_ncard_eq (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R : Subgroup G} (hR : R ∈ DSet Ω W) (ρ : Asc77.Thompson.Rep Ω W) (hρ : ρ.K = R) :
    (KPerp Ω R ∩ DSet Ω W).ncard =
      (Star3T.cent (Thompson.muDelta Ω W) (MuTab.muTabElt ρ)).ncard := by
  have hP : Q3CL.PartIHypG Ω := ⟨h.thmD.hyp, h.cls, h.thmD.aEmpty⟩
  have hrep : ∀ T ∈ DSet Ω W, ∃ σ : Asc77.Thompson.Rep Ω W, σ.K = T :=
    fun T hT => ⟨endU_rep h hW hT, rfl⟩
  have : Nonempty (Asc77.Thompson.Rep Ω W) := ⟨ρ⟩
  choose! rep hrep using hrep
  obtain ⟨f, hf⟩ : ∃ f : Subgroup G → ↥(muGroup Ω W),
      ∀ T, f T = MuTab.muTabElt (rep T) := ⟨_, fun _ => rfl⟩
  have hRρ : MuTab.muTabElt (rep R) = MuTab.muTabElt ρ :=
    (Q3T6.Mu.muTabElt_eq_iff hP hW _ _).mpr (by rw [hrep R hR, hρ])
  have hfR : f R = MuTab.muTabElt ρ := by rw [hf, hRρ]
  have hinj : Set.InjOn f (KPerp Ω R ∩ DSet Ω W) := by
    intro T hT T' hT' hTT'
    rw [hf, hf] at hTT'
    have e := (Q3T6.Mu.muTabElt_eq_iff hP hW (rep T) (rep T')).mp hTT'
    rw [hrep T hT.2, hrep T' hT'.2] at e
    exact e
  have himg : f '' (KPerp Ω R ∩ DSet Ω W) =
      Star3T.cent (Thompson.muDelta Ω W) (MuTab.muTabElt ρ) := by
    ext x
    constructor
    · rintro ⟨T, ⟨hTp, hTD⟩, rfl⟩
      refine ⟨by rw [hf]; exact MuTab.muTabElt_mem (rep T), ?_⟩
      rw [← hfR]
      by_cases hTR : T = R
      · rw [hTR]
      · have hTn : T ∈ omegaNbr Ω R := (endU_mem_kperp_iff.mp hTp).resolve_left hTR
        have hne : (rep R).K ≠ (rep T).K := by
          rw [hrep R hR, hrep T hTD]
          exact fun e => hTR e.symm
        have hc : MuTab.muTabElt (rep R) * MuTab.muTabElt (rep T) =
            MuTab.muTabElt (rep T) * MuTab.muTabElt (rep R) :=
          (Q3T6.Mu.muTab_commute_iff hP hW (rep R) (rep T) hne).mpr
            (by rw [hrep R hR, hrep T hTD]; exact hTn)
        rw [hf, hf]
        exact hc.symm
    · rintro ⟨hxΔ, hx⟩
      obtain ⟨σ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hxΔ
      have hσD : σ.K ∈ DSet Ω W := by
        have hRK : σ.R = σ.K :=
          (σ.hRK.2.2 σ.K le_rfl (h.thmD.two σ.K σ.hK) σ.hRK.1).symm
        rw [← hRK]
        exact σ.hR
      refine ⟨σ.K, ⟨?_, hσD⟩, ?_⟩
      · by_cases hσR : σ.K = R
        · exact endU_mem_kperp_iff.mpr (Or.inl hσR)
        · refine endU_mem_kperp_iff.mpr (Or.inr ?_)
          have hne : (rep R).K ≠ σ.K := by
            rw [hrep R hR]
            exact fun e => hσR e.symm
          have hcomm : MuTab.muTabElt (rep R) * MuTab.muTabElt σ =
              MuTab.muTabElt σ * MuTab.muTabElt (rep R) := by
            rw [hRρ]
            exact hx.symm
          have := (Q3T6.Mu.muTab_commute_iff hP hW (rep R) σ hne).mp hcomm
          rw [hrep R hR] at this
          exact this
      · rw [hf]
        exact (Q3T6.Mu.muTabElt_eq_iff hP hW _ _).mpr (hrep σ.K hσD)
  rw [← himg]
  exact hinj.ncard_image.symm

variable {K : Subgroup G} {P₁ P₂ : Set (Subgroup G)} {g : G}

private theorem endU_two_more {C : Set (Subgroup G)} {K Ks : Subgroup G} (hC : C.ncard = 4)
    (hK : K ∈ C) (hKs : Ks ∈ C) (hne : K ≠ Ks) :
    ∃ J J' : Subgroup G, J ∈ C ∧ J' ∈ C ∧ J ≠ K ∧ J ≠ Ks ∧ J' ≠ K ∧ J' ≠ Ks ∧ J ≠ J' := by
  have hsub : ({K, Ks} : Set (Subgroup G)) ⊆ C :=
    Set.insert_subset_iff.mpr ⟨hK, Set.singleton_subset_iff.mpr hKs⟩
  have hdiff : (C \ {K, Ks}).ncard = 2 := by
    rw [Set.ncard_diff hsub (Set.toFinite _), hC, Set.ncard_pair hne]
  obtain ⟨J, J', hJJ', heq⟩ := Set.ncard_eq_two.mp hdiff
  have hJmem : J ∈ C \ {K, Ks} := by
    rw [heq]
    exact Set.mem_insert _ _
  have hJ'mem : J' ∈ C \ {K, Ks} := by
    rw [heq]
    exact Set.mem_insert_of_mem _ rfl
  refine ⟨J, J', hJmem.1, hJ'mem.1, ?_, ?_, ?_, ?_, hJJ'⟩
  · intro e
    exact hJmem.2 (by rw [e]; exact Set.mem_insert _ _)
  · intro e
    exact hJmem.2 (by rw [e]; exact Set.mem_insert_of_mem _ rfl)
  · intro e
    exact hJ'mem.2 (by rw [e]; exact Set.mem_insert _ _)
  · intro e
    exact hJ'mem.2 (by rw [e]; exact Set.mem_insert_of_mem _ rfl)

private theorem endU_comm_identity {x a bb : G} (h : x * bb = bb * x) :
    x * (a * bb) * x⁻¹ * (a * bb)⁻¹ = x * a * x⁻¹ * a⁻¹ := by
  have hbx : bb * x⁻¹ = x⁻¹ * bb := by
    calc bb * x⁻¹ = x⁻¹ * (x * bb) * x⁻¹ := by group
      _ = x⁻¹ * (bb * x) * x⁻¹ := by rw [h]
      _ = x⁻¹ * bb := by group
  calc x * (a * bb) * x⁻¹ * (a * bb)⁻¹ = x * a * (bb * x⁻¹) * bb⁻¹ * a⁻¹ := by group
    _ = x * a * (x⁻¹ * bb) * bb⁻¹ * a⁻¹ := by rw [hbx]
    _ = x * a * x⁻¹ * a⁻¹ := by group

private theorem endU_comm_pSpan (c : CaseBSit Ω K P₁ P₂ g) {L : Subgroup G} (hL : L ∈ P₂)
    {y : G} (hy : y ∈ L) : ∀ x ∈ pSpan P₁, x * y = y * x := by
  have hcent : pSpan P₁ ≤ Subgroup.centralizer ({y} : Set G) :=
    pSpan_le fun L' hL' =>
      fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (c.comm L' hL' L hL x hx y hy)
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcent hx)

private theorem endU_lift {P : Set (Subgroup G)} (I : AEIdent P 5) {x : AEQ 5}
    (hx : x ∈ TL4.aeModel 5) : ∃ y : ↥(pSpan P), I.φ y = x := by
  have hr : x ∈ I.φ.range := by
    rw [I.range_eq]
    exact hx
  exact MonoidHom.mem_range.mp hr

private theorem endU_permBar_of_comm_pCore {P : Set (Subgroup G)} (I : AEIdent P 5)
    {a : G} (ha : a ∈ pSpan P) (hc : ∀ x ∈ pSpan P, x * a * x⁻¹ * a⁻¹ ∈ pCore 2 G) :
    TL4.permBar 5 (I.φ ⟨a, ha⟩) = 1 := by
  have hφ : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 →
      ∃ x : ↥(pSpan P), TL4.permBar 5 (I.φ x) = σ := by
    intro σ hσ
    have hmem : AE.mkQ 5 (Wr.ofPerm σ) ∈ TL4.aeModel 5 := by
      refine ⟨Wr.ofPerm σ, ?_, rfl⟩
      refine ⟨?_, ?_⟩
      · simp [Wr.wsum, Wr.ofPerm]
      · simpa [Wr.ofPerm] using hσ
    obtain ⟨x, hx⟩ := endU_lift I hmem
    exact ⟨x, by rw [hx, TL4.permBar_mkQ]; rfl⟩
  have hN : IsPGroup 2 ((pCore 2 G).subgroupOf (pSpan P)) :=
    (CFSG.pCore_isPGroup : IsPGroup 2 (pCore 2 G)).comap_of_injective (pSpan P).subtype
      Subtype.coe_injective
  set N : Subgroup (pSpan P) := (pCore 2 G).subgroupOf (pSpan P) with hNdef
  have hcomm : ∀ x : ↥(pSpan P),
      TL4.permBar 5 (I.φ x) * TL4.permBar 5 (I.φ ⟨a, ha⟩) =
        TL4.permBar 5 (I.φ ⟨a, ha⟩) * TL4.permBar 5 (I.φ x) := by
    intro x
    have hxa : x.1 * a * x.1⁻¹ * a⁻¹ ∈ pSpan P :=
      (pSpan P).mul_mem ((pSpan P).mul_mem ((pSpan P).mul_mem x.2 ha)
        ((pSpan P).inv_mem x.2)) ((pSpan P).inv_mem ha)
    have hmemN : (⟨x.1 * a * x.1⁻¹ * a⁻¹, hxa⟩ : ↥(pSpan P)) ∈ N := by
      rw [hNdef, Subgroup.mem_subgroupOf]
      exact hc x.1 x.2
    have h1 := endU_permBar_eq_one_of_two_normal I.φ hφ N hN hmemN
    have hxa_eq : (⟨x.1 * a * x.1⁻¹ * a⁻¹, hxa⟩ : ↥(pSpan P)) =
        x * ⟨a, ha⟩ * x⁻¹ * ⟨a, ha⟩⁻¹ := Subtype.ext rfl
    rw [hxa_eq] at h1
    simp only [map_mul, map_inv] at h1
    calc TL4.permBar 5 (I.φ x) * TL4.permBar 5 (I.φ ⟨a, ha⟩)
        = (TL4.permBar 5 (I.φ x) * TL4.permBar 5 (I.φ ⟨a, ha⟩) *
            (TL4.permBar 5 (I.φ x))⁻¹ * (TL4.permBar 5 (I.φ ⟨a, ha⟩))⁻¹) *
            (TL4.permBar 5 (I.φ ⟨a, ha⟩) * TL4.permBar 5 (I.φ x)) := by group
      _ = TL4.permBar 5 (I.φ ⟨a, ha⟩) * TL4.permBar 5 (I.φ x) := by rw [h1, one_mul]
  refine endU_eq_one_of_centralizes_alt _ ?_
  intro τ hτ
  obtain ⟨x, hx⟩ := hφ τ hτ
  rw [← hx]
  exact (hcomm x).symm

private theorem endU_u_form (I : AEIdent P₁ 5) (hI : I.φ.ker = ⊥) {K Ks : Subgroup G}
    (hK : K ∈ P₁) (hKs : Ks ∈ P₁) {α : Finset (Fin 5)} (hα : α.card = 4) {b : Bool}
    (hlabK : (K.subgroupOf (pSpan P₁)).map I.φ = AE.memBar α hα b)
    (hlabKs : (Ks.subgroupOf (pSpan P₁)).map I.φ = AE.memBar α hα (!b))
    {x y : G} (hx : x ∈ K) (hy : y ∈ Ks) (hx4 : orderOf x = 4) (hy4 : orderOf y = 4)
    (hxy : x * y ∈ pSpan P₁) (hperm : TL4.permBar 5 (I.φ ⟨x * y, hxy⟩) = 1) :
    I.φ ⟨x * y, hxy⟩ ≠ 1 ∧ ∃ i j : Fin 5, i ∈ α ∧ j ∈ α ∧ i ≠ j ∧
      I.φ ⟨x * y, hxy⟩ = AE.mkQ 5 (Wr.ofVec (Pi.single i 1 + Pi.single j 1)) := by
  have hinj : Function.Injective I.φ := (MonoidHom.ker_eq_bot_iff I.φ).mp hI
  set ax : ↥(pSpan P₁) := ⟨x, le_pSpan hK hx⟩ with hax
  set ay : ↥(pSpan P₁) := ⟨y, le_pSpan hKs hy⟩ with hay
  have hmx : I.φ ax ∈ AE.memBar α hα b := by
    rw [← hlabK]
    exact I.mem_map hK hx
  have hmy : I.φ ay ∈ AE.memBar α hα (!b) := by
    rw [← hlabKs]
    exact I.mem_map hKs hy
  have hprod : I.φ ⟨x * y, hxy⟩ = I.φ ax * I.φ ay := by
    rw [← map_mul]
    rfl
  have hperm' : TL4.permBar 5 (I.φ ax * I.φ ay) = 1 := by
    rw [← hprod]
    exact hperm
  have hsqy : I.φ ay * I.φ ay = 1 → False := by
    intro hsq
    have h1 : ay * ay = 1 := hinj (by rw [map_mul, map_one]; exact hsq)
    have h2 : y * y = 1 := by
      have := congrArg Subtype.val h1
      simpa [hay] using this
    have h3 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hy4] at h3
    norm_num at h3
  have hkey : ∀ w : AEQ 5, I.φ ax * I.φ ay = w → (w = 1 ∨ w = AE.zBar α hα) → False := by
    intro w hw hw1
    apply hsqy
    have hyb : I.φ ay ∈ AE.memBar α hα b := by
      have heq : I.φ ay = (I.φ ax)⁻¹ * w := eq_inv_mul_of_mul_eq hw
      rw [heq]
      rcases hw1 with rfl | rfl
      · rw [mul_one]
        exact inv_mem hmx
      · exact mul_mem (inv_mem hmx) (AE.zBar_mem_memBar α hα b)
    exact endU_mul_self_of_memBar_both hα hyb hmy
  have hne1 : I.φ ⟨x * y, hxy⟩ ≠ 1 := by
    rw [hprod]
    intro e
    exact hkey 1 e (Or.inl rfl)
  rcases endU_mul_memBar_vec hα hmx hmy hperm' with h1 | h1 | ⟨i, j, hi, hj, hij, hv⟩
  · exact (hkey 1 h1 (Or.inl rfl)).elim
  · exact (hkey _ h1 (Or.inr rfl)).elim
  · refine ⟨hne1, i, j, hi, hj, hij, ?_⟩
    rw [hprod]
    exact hv

private theorem endU_mem_P₂ (c : CaseBSit Ω K P₁ P₂ g) (I : AEIdent P₁ 5) (hI : I.φ.ker = ⊥)
    (h8 : ∀ L ∈ P₁, Nat.card L = 8) {α : Finset (Fin 5)} (hα : α.card = 4) {b : Bool}
    {Ks J : Subgroup G} (hKs : Ks ∈ P₁)
    (hlabK : (K.subgroupOf (pSpan P₁)).map I.φ = AE.memBar α hα b)
    (hlabKs : (Ks.subgroupOf (pSpan P₁)).map I.φ = AE.memBar α hα (!b))
    (hJ : J ∈ P₁ ∪ P₂) (hcomm : Commutes K J) (hJK : J ≠ K) (hJKs : J ≠ Ks) : J ∈ P₂ := by
  rcases hJ with hJ | hJ
  · exfalso
    obtain ⟨β, hβ, c', hlabJ⟩ := I.label J hJ
    obtain rfl := endU_same_set I c.hK hJ hlabK hlabJ hcomm
    have hbc : c' = b ∨ c' = !b := by
      cases c' <;> cases b <;> simp
    rcases hbc with rfl | rfl
    · exact hJK (endU_eq_of_map_eq I hI h8 hJ c.hK (hlabJ.trans hlabK.symm))
    · exact hJKs (endU_eq_of_map_eq I hI h8 hJ hKs (hlabJ.trans hlabKs.symm))
  · exact hJ

private theorem endU_not_mem_dComp_pair (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {ρ₁ ρ₂ : Asc77.Thompson.Rep Ω W} (hne : ρ₁.K ≠ ρ₂.K)
    (hnc : MuTab.muTabElt ρ₁ * MuTab.muTabElt ρ₂ ≠ MuTab.muTabElt ρ₂ * MuTab.muTabElt ρ₁) :
    ρ₂.K ∉ dComp Ω ρ₁.K := by
  have hP : Q3CL.PartIHypG Ω := ⟨h.thmD.hyp, h.cls, h.thmD.aEmpty⟩
  have hs : ρ₂.K ∈ omegaStarNbr Ω ρ₁.K := Q3T6.Mu.muTab_omegaStar hP hW ρ₁ ρ₂ hne
  have hn : ρ₂.K ∉ omegaNbr Ω ρ₁.K := fun hn =>
    hnc ((Q3T6.Mu.muTab_commute_iff hP hW ρ₁ ρ₂ hne).mpr hn)
  exact not_mem_dComp_of_omegaStar h ρ₁.hK hs hn

private theorem endU_exists_noncomm_pair {M : Type} [Group M] {S : Set M}
    (ψ : ↥(Subgroup.closure S) ≃* Equiv.Perm (Fin 4))
    (hψ : ∀ (x : M) (hx : x ∈ Subgroup.closure S), x ∈ S ↔ (ψ ⟨x, hx⟩).IsSwap) :
    ∃ x₁ ∈ S, ∃ x₂ ∈ S, x₁ * x₂ ≠ x₂ * x₁ := by
  set p₁ := ψ.symm (Equiv.swap (0 : Fin 4) 1) with hp₁
  set p₂ := ψ.symm (Equiv.swap (1 : Fin 4) 2) with hp₂
  have e1 : ψ p₁ = Equiv.swap 0 1 := ψ.apply_symm_apply _
  have e2 : ψ p₂ = Equiv.swap 1 2 := ψ.apply_symm_apply _
  have hs₁ : (ψ ⟨(p₁ : M), p₁.2⟩).IsSwap := by
    rw [show (⟨(p₁ : M), p₁.2⟩ : ↥(Subgroup.closure S)) = p₁ from rfl, e1]
    exact ⟨0, 1, by decide, rfl⟩
  have hs₂ : (ψ ⟨(p₂ : M), p₂.2⟩).IsSwap := by
    rw [show (⟨(p₂ : M), p₂.2⟩ : ↥(Subgroup.closure S)) = p₂ from rfl, e2]
    exact ⟨1, 2, by decide, rfl⟩
  refine ⟨p₁, (hψ _ p₁.2).mpr hs₁, p₂, (hψ _ p₂.2).mpr hs₂, fun heq => ?_⟩
  have hp : p₁ * p₂ = p₂ * p₁ := Subtype.ext heq
  have h12 : (Equiv.swap (0 : Fin 4) 1) * Equiv.swap 1 2 ≠ Equiv.swap 1 2 * Equiv.swap 0 1 := by
    decide
  apply h12
  have := congrArg ψ hp
  rw [map_mul, map_mul, e1, e2] at this
  exact this

private theorem endU_exists_T (h : EndHyp Ω) {W K Ks : Subgroup G} (hW : W ∈ WSet Ω)
    (hKD : K ∈ DSet Ω W) (hKsD : Ks ∈ DSet Ω W) (hKs : Commutes K Ks) (hKKs : K ≠ Ks)
    {g0 g1 : G} (hg0 : g0 ∈ K ⊓ W) (hg1 : g1 ∈ Ks ⊓ W) (hg0o : orderOf g0 = 4)
    (hg1o : orderOf g1 = 4) (hcls : (KPerp Ω K ∩ DSet Ω W).ncard = 4) :
    ∃ T : Subgroup G, T ∈ Ω ∧ T ≤ Subgroup.centralizer ({g0 * g1} : Set G) ∧
      T ∉ dComp Ω K := by
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hKΩ : K ∈ Ω := (h.mem_dSet_iff.mp hKD).1
  have hP : Q3CL.PartIHypG Ω := ⟨hΩ, h.cls, h.thmD.aEmpty⟩
  have c' : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  have hTT : Star3T.IsTT (Thompson.muDelta Ω W) := Q3T6.Mu.isTT_muDelta hP hW
  have hS : Star3T.IsStar (Thompson.muDelta Ω W) := Q3T6.Mu.isStar_muDelta c'
  set ρK := endU_rep h hW hKD with hρK
  set ρKs := endU_rep h hW hKsD with hρKs
  have hr₁ : ρK.r ∈ K := ρK.hr
  have hr₂ : ρKs.r ∈ Ks := ρKs.hr
  have hr₁W : ρK.r ∉ W := ρK.hrW
  have hr₂W : ρKs.r ∉ W := ρKs.hrW
  have hN₁ : ρK.r ∈ Subgroup.normalizer (W : Set G) := (h.mem_dSet_iff.mp hKD).2 hr₁
  have hN₂ : ρKs.r ∈ Subgroup.normalizer (W : Set G) := (h.mem_dSet_iff.mp hKsD).2 hr₂
  have hd : ((MuTab.muTabElt ρK : ↥(muGroup Ω W)) : NQuot (W ⊔ OCW W)) = Thompson.piG W ρK.r :=
    MuTab.muTabElt_coe ρK
  obtain ⟨a, haΔ, hconn⟩ :=
    Q3CL.Wyl.exists_not_conn_at hP hW (h.not_dbarConnected hW) (MuTab.muTabElt ρK)
  have hk : (Star3T.cent (Thompson.muDelta Ω W) (MuTab.muTabElt ρK)).ncard = 4 := by
    rw [← endU_ncard_eq h hW hKD ρK rfl]
    exact hcls
  have hcomm : Thompson.piG W ρK.r * Thompson.piG W ρKs.r =
      Thompson.piG W ρKs.r * Thompson.piG W ρK.r := by
    rw [← Thompson.piG_mul hN₁ hN₂, ← Thompson.piG_mul hN₂ hN₁, hKs ρK.r hr₁ ρKs.r hr₂]
  have hne : Thompson.piG W ρK.r ≠ Thompson.piG W ρKs.r := by
    intro e
    apply hKKs
    have e' : MuTab.muTabElt ρK = MuTab.muTabElt ρKs :=
      Subtype.ext (by rw [MuTab.muTabElt_coe, MuTab.muTabElt_coe]; exact e)
    exact (Q3T6.Mu.muTabElt_eq_iff hP hW ρK ρKs).mp e'
  have hDC : DComm W K Ks :=
    Q3T8.Asc77.Thompson.dComm_of_commute c'.hΩ hW hKD hKsD hr₁ hr₂ hr₁W hr₂W hcomm hne
  obtain ⟨ψ, hψ⟩ := Q3T8.Asc77.Thompson.exists_perm_four_of_wv c' hTT hS hKD hKsD hDC hr₁ hr₁W
    hd (MuTab.muTabElt_mem ρK) haΔ hconn hk hg0 hg1 hg0o hg1o
  obtain ⟨x₁, hx₁, x₂, hx₂, hnc⟩ := endU_exists_noncomm_pair ψ hψ
  obtain ⟨T₁, hT₁C, r₁, hr₁T, hr₁W', hx₁e⟩ := hx₁
  obtain ⟨T₂, hT₂C, r₂, hr₂T, hr₂W', hx₂e⟩ := hx₂
  set ρ₁ : Asc77.Thompson.Rep Ω W := endU_repOf h hT₁C.1 hr₁T hr₁W' with hρ₁
  set ρ₂ : Asc77.Thompson.Rep Ω W := endU_repOf h hT₂C.1 hr₂T hr₂W' with hρ₂
  have hm₁ : MuTab.muTabElt ρ₁ = x₁ :=
    Subtype.ext (by rw [MuTab.muTabElt_coe]; exact hx₁e.symm)
  have hm₂ : MuTab.muTabElt ρ₂ = x₂ :=
    Subtype.ext (by rw [MuTab.muTabElt_coe]; exact hx₂e.symm)
  have hnc' : MuTab.muTabElt ρ₁ * MuTab.muTabElt ρ₂ ≠
      MuTab.muTabElt ρ₂ * MuTab.muTabElt ρ₁ := by
    rw [hm₁, hm₂]
    exact hnc
  have hne12 : ρ₁.K ≠ ρ₂.K := by
    intro e
    apply hnc'
    rw [(Q3T6.Mu.muTabElt_eq_iff hP hW ρ₁ ρ₂).mpr e]
  have hnd : ρ₂.K ∉ dComp Ω ρ₁.K := endU_not_mem_dComp_pair h hW hne12 hnc'
  by_cases hT₁ : ρ₁.K ∈ dComp Ω K
  · refine ⟨ρ₂.K, ρ₂.hK, hT₂C.2, fun hT₂ => hnd ?_⟩
    rw [endU_dComp_eq hKΩ hT₁]
    exact hT₂
  · exact ⟨ρ₁.K, ρ₁.hK, hT₁C.2, hT₁⟩

private theorem endU_K_mem_Omega (c : CaseBSit Ω K P₁ P₂ g) : K ∈ Ω := by
  have hne : conjSub g K ≠ K := fun e => Set.disjoint_left.mp c.disj c.hK (e ▸ c.gP)
  have hmem : conjSub g K ∈ dComp Ω K := by
    rw [c.dcomp]
    exact Or.inr c.gP
  have h1 : conjSub g K ∈ Ω := endU_mem_Omega_of_dComp hmem hne
  have h2 := c.hyp.thmD.hyp.conjInvariant g⁻¹ _ h1
  rwa [conjSub_inv_conjSub] at h2

namespace CaseBSit

theorem exists_caseBU (c : CaseBSit Ω K P₁ P₂ g) (I : AEIdent P₁ 5) (hI : I.φ.ker = ⊥) :
    ∃ (u h e : G) (T : Subgroup G), CaseBU Ω K P₁ P₂ g u h e T := by
  have hEnd : EndHyp Ω := c.hyp
  have h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J := hEnd.thmD.two
  have hΩ : HypOmegaGen Ω := hEnd.thmD.hyp
  have hKΩ : K ∈ Ω := endU_K_mem_Omega c
  have hP1Ω : ∀ L ∈ P₁, L ∈ Ω := fun L hL => by
    by_cases hLK : L = K
    · rw [hLK]
      exact hKΩ
    · exact endU_mem_Omega_of_dComp (by rw [c.dcomp]; exact Or.inl hL) hLK
  have h8 : ∀ L ∈ P₁, Nat.card L = 8 := fun L hL => hEnd.card_eq_eight (hP1Ω L hL)
  have hk : IsPGroup 2 ↥I.φ.ker := by
    rw [hI]
    exact IsPGroup.of_card (n := 0) (by simp)
  have hinj : Function.Injective I.φ := (MonoidHom.ker_eq_bot_iff I.φ).mp hI
  obtain ⟨z, hz⟩ := (hΩ.omega1 K hKΩ).1
  obtain ⟨W, hW, hzW, -, -⟩ := hEnd.exists_wSet_not_le hKΩ hz
  have hKD : K ∈ DSet Ω W := hEnd.mem_dSet_of_mem hW hKΩ hz hzW
  have hcls : (KPerp Ω K ∩ DSet Ω W).ncard = 4 :=
    (dSet_class_ncard hEnd hW hKD).2.2 (c.wyl W hW)
  obtain ⟨α, hα, b, hlabK⟩ := I.label K c.hK
  obtain ⟨Ks, hKsP, hlabKs⟩ := I.label_surj α hα (!b)
  have hKsK : Ks ≠ K := by
    rintro rfl
    exact endU_memBar_ne α hα b (hlabK.symm.trans hlabKs)
  have hKsΩ : Ks ∈ Ω := hP1Ω Ks hKsP
  obtain ⟨z', hz'⟩ := (hΩ.omega1 Ks hKsΩ).1
  have hzz' : z' = z := by
    have e1 := I.map_eq_zBar (by norm_num) c.hK (h8 K c.hK) hlabK hz
    have e2 := I.map_eq_zBar (by norm_num) hKsP (h8 Ks hKsP) hlabKs hz'
    exact congrArg Subtype.val (hinj (e2.trans e1.symm))
  have hzKs : IsUniqueInvolution Ks z := hzz' ▸ hz'
  have hKsD : Ks ∈ DSet Ω W := hEnd.mem_dSet_of_mem hW hKsΩ hzKs hzW
  have cKKs : Commutes K Ks := endU_twin_comm I hΩ h2 hP1Ω hk c.hK hKsP hlabK hlabKs
  have hKKs : K ≠ Ks := fun e => hKsK e.symm
  have hKC : K ∈ KPerp Ω K ∩ DSet Ω W := ⟨Set.mem_insert _ _, hKD⟩
  have hKsC : Ks ∈ KPerp Ω K ∩ DSet Ω W :=
    ⟨endU_mem_kperp_of_comm h2 hΩ hKΩ hKsΩ cKKs, hKsD⟩
  obtain ⟨J, J', hJC, hJ'C, hJK, hJKs, hJ'K, hJ'Ks, hJJ'⟩ :=
    endU_two_more hcls hKC hKsC hKKs
  have hJD : J ∈ DSet Ω W := hJC.2
  have hJ'D : J' ∈ DSet Ω W := hJ'C.2
  have hJΩ : J ∈ Ω := (hEnd.mem_dSet_iff.mp hJD).1
  have hJ'Ω : J' ∈ Ω := (hEnd.mem_dSet_iff.mp hJ'D).1
  have hJω : J ∈ omegaNbr Ω K := (endU_mem_kperp_iff.mp hJC.1).resolve_left hJK
  have hJ'ω : J' ∈ omegaNbr Ω K := (endU_mem_kperp_iff.mp hJ'C.1).resolve_left hJ'K
  have hJPP : J ∈ P₁ ∪ P₂ := by
    rw [← c.dcomp]
    exact endU_dComp_of_omegaNbr hJω
  have hJ'PP : J' ∈ P₁ ∪ P₂ := by
    rw [← c.dcomp]
    exact endU_dComp_of_omegaNbr hJ'ω
  have cKJ : Commutes K J := endU_comm_of_omegaNbr h2 hΩ hKΩ hJω
  have cKJ' : Commutes K J' := endU_comm_of_omegaNbr h2 hΩ hKΩ hJ'ω
  have hJP₂ : J ∈ P₂ := endU_mem_P₂ c I hI h8 hα hKsP hlabK hlabKs hJPP cKJ hJK hJKs
  have hJ'P₂ : J' ∈ P₂ := endU_mem_P₂ c I hI h8 hα hKsP hlabK hlabKs hJ'PP cKJ' hJ'K hJ'Ks
  have cKsJ : Commutes Ks J := endU_comm_of_omegaNbr h2 hΩ hKsΩ
    ((endU_mem_kperp_iff.mp (dSet_comm_trans hEnd hW hKsD hKD hJD
      (endU_mem_kperp_of_comm h2 hΩ hKsΩ hKΩ (endU_comm_symm cKKs)) hJC.1)).resolve_left hJKs)
  have cKsJ' : Commutes Ks J' := endU_comm_of_omegaNbr h2 hΩ hKsΩ
    ((endU_mem_kperp_iff.mp (dSet_comm_trans hEnd hW hKsD hKD hJ'D
      (endU_mem_kperp_of_comm h2 hΩ hKsΩ hKΩ (endU_comm_symm cKKs)) hJ'C.1)).resolve_left hJ'Ks)
  have cJJ' : Commutes J J' := endU_comm_of_omegaNbr h2 hΩ hJΩ
    ((endU_mem_kperp_iff.mp (dSet_comm_trans hEnd hW hJD hKD hJ'D
      (endU_mem_kperp_of_comm h2 hΩ hJΩ hKΩ (endU_comm_symm cKJ)) hJ'C.1)).resolve_left
      (Ne.symm hJJ'))
  have hP : Q3CL.PartIHypG Ω := ⟨hΩ, hEnd.cls, hEnd.thmD.aEmpty⟩
  have c' : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  let ρs : Fin 4 → Asc77.Thompson.Rep Ω W :=
    ![endU_rep hEnd hW hKD, endU_rep hEnd hW hKsD, endU_rep hEnd hW hJD, endU_rep hEnd hW hJ'D]
  have hdist : ∀ i j : Fin 4, i ≠ j → (ρs i).K ≠ (ρs j).K := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact hKKs | exact Ne.symm hKKs | exact hJK | exact Ne.symm hJK
      | exact hJ'K | exact Ne.symm hJ'K | exact hJKs | exact Ne.symm hJKs
      | exact hJ'Ks | exact Ne.symm hJ'Ks | exact hJJ' | exact Ne.symm hJJ'
  have hcomm4 : ∀ i j : Fin 4, i ≠ j → Commutes (ρs i).K (ρs j).K := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact cKKs | exact endU_comm_symm cKKs | exact cKJ | exact endU_comm_symm cKJ
      | exact cKJ' | exact endU_comm_symm cKJ' | exact cKsJ | exact endU_comm_symm cKsJ
      | exact cKsJ' | exact endU_comm_symm cKsJ' | exact cJJ' | exact endU_comm_symm cJJ'
  have hnbr : ∀ i j : Fin 4, i ≠ j → (ρs j).K ∈ omegaNbr Ω (ρs i).K := fun i j hij =>
    endU_omegaNbr_of_comm h2 hΩ (ρs j).hK (hdist j i (Ne.symm hij)) (hcomm4 i j hij)
  obtain ⟨σ, t, gg, hσt, -, hgg, htg⟩ :=
    Q3CL.Thompson.Ctx.exists_relation c' hEnd.cls (hEnd.not_dbarConnected hW) ρs hdist hnbr
  have hg0 : gg 0 ∈ K ⊓ W := (hgg 0).1
  have hg1 : gg 1 ∈ Ks ⊓ W := (hgg 1).1
  have hg2 : gg 2 ∈ J ⊓ W := (hgg 2).1
  have hg3 : gg 3 ∈ J' ⊓ W := (hgg 3).1
  have ho0 : orderOf (gg 0) = 4 := (hgg 0).2
  have ho1 : orderOf (gg 1) = 4 := (hgg 1).2
  have htg' : t = gg 0 * gg 1 * (gg 2 * gg 3) := by
    rw [htg, mul_assoc]
  have ht_pCore : t ∈ pCore 2 G := hEnd.mem_pCore σ.hK hσt
  have ht' : gg 0 * gg 1 * (gg 2 * gg 3) ∈ pCore 2 G := by
    rw [← htg']
    exact ht_pCore
  have haP : gg 0 * gg 1 ∈ pSpan P₁ :=
    (pSpan P₁).mul_mem (le_pSpan c.hK hg0.1) (le_pSpan hKsP hg1.1)
  have hbcomm : ∀ x ∈ pSpan P₁, x * (gg 2 * gg 3) = (gg 2 * gg 3) * x := fun x hx => by
    rw [← mul_assoc, endU_comm_pSpan c hJP₂ hg2.1 x hx, mul_assoc,
      endU_comm_pSpan c hJ'P₂ hg3.1 x hx, ← mul_assoc]
  have hcomm_pc : ∀ x ∈ pSpan P₁, x * (gg 0 * gg 1) * x⁻¹ * (gg 0 * gg 1)⁻¹ ∈ pCore 2 G := by
    intro x hx
    rw [← endU_comm_identity (hbcomm x hx)]
    exact (pCore 2 G).mul_mem (Subgroup.Normal.conj_mem inferInstance _ ht' x) (inv_mem ht')
  have hperm_a : TL4.permBar 5 (I.φ ⟨gg 0 * gg 1, haP⟩) = 1 :=
    endU_permBar_of_comm_pCore I haP hcomm_pc
  obtain ⟨hne1, i, j, hi, hj, hij, hφU⟩ :=
    endU_u_form I hI c.hK hKsP hα hlabK hlabKs hg0.1 hg1.1 ho0 ho1 haP hperm_a
  obtain ⟨U, hU⟩ : ∃ U : ↥(pSpan P₁), (U : G) = gg 0 * gg 1 := ⟨⟨_, haP⟩, rfl⟩
  have hUeq : U = ⟨gg 0 * gg 1, haP⟩ := Subtype.ext hU
  have hφU' : I.φ U = AE.mkQ 5 (Wr.ofVec (Pi.single i 1 + Pi.single j 1)) := by
    rw [hUeq]
    exact hφU
  obtain ⟨h', hh', e', he', hpe', hord, hhu, hz''⟩ := AE5End.exists_three hα hi hj hij
  obtain ⟨hX, hhX⟩ := endU_lift I hh'
  obtain ⟨eX, heX⟩ := endU_lift I he'
  have hX_ord : orderOf (hX : G) = 3 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective I.φ hinj hX, hhX]
    exact hord
  have hhu' : (hX : G) * (gg 0 * gg 1) = (gg 0 * gg 1) * (hX : G) := by
    have hcomm' : hX * U = U * hX := hinj (by
      rw [map_mul, map_mul, hhX, hφU']
      exact hhu)
    rw [← hU]
    exact congrArg Subtype.val hcomm'
  have heu' : (eX : G) * (gg 0 * gg 1) = (gg 0 * gg 1) * (eX : G) := by
    obtain ⟨v, hv⟩ := endU_vec_of_permBar hpe'
    have hcomm' : eX * U = U * eX := hinj (by
      rw [map_mul, map_mul, heX, hφU', hv]
      exact endU_mkQ_ofVec_comm _ _)
    rw [← hU]
    exact congrArg Subtype.val hcomm'
  have hz_eq : ∀ z'' : G, IsUniqueInvolution K z'' →
      z'' = gg 0 * gg 1 * ((eX : G)⁻¹ * (hX : G)⁻¹ * (eX : G) * (hX : G)) := by
    intro z₁ hz₁
    have hz₁P : z₁ ∈ pSpan P₁ := le_pSpan c.hK hz₁.mem
    have e1 : I.φ ⟨z₁, hz₁P⟩ = AE.zBar α hα :=
      I.map_eq_zBar (by norm_num) c.hK (h8 K c.hK) hlabK hz₁
    have e2 : I.φ (U * (eX⁻¹ * hX⁻¹ * eX * hX)) = AE.zBar α hα := by
      simp only [map_mul, map_inv, hφU', heX, hhX]
      exact hz''.symm
    have e3 : (⟨z₁, hz₁P⟩ : ↥(pSpan P₁)) = U * (eX⁻¹ * hX⁻¹ * eX * hX) :=
      hinj (e1.trans e2.symm)
    rw [← hU]
    exact congrArg Subtype.val e3
  have hP1u : ∀ L ∈ P₁, ¬ L ≤ Subgroup.centralizer ({gg 0 * gg 1} : Set G) := by
    intro L hL hle
    obtain ⟨β, hβ, c'', hlabL⟩ := I.label L hL
    apply AE5End.not_centralizes_pair hβ c'' hij
    intro y hy
    rw [← hlabL] at hy
    obtain ⟨l, hl, hly⟩ := I.exists_of_mem_map hL hy
    rw [← hly, ← hφU']
    have hlu : l * (gg 0 * gg 1) = (gg 0 * gg 1) * l :=
      Subgroup.mem_centralizer_singleton_iff.mp (hle hl)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (show l * (U : G) = (U : G) * l by rw [hU]; exact hlu)
  have hP2u : ∀ L ∈ P₂, L ≤ Subgroup.centralizer ({gg 0 * gg 1} : Set G) := fun L hL y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (endU_comm_pSpan c hL hy _ haP).symm
  have hP2h : ∀ L ∈ P₂, ∀ y ∈ L, (hX : G) * y = y * (hX : G) := fun L hL y hy =>
    endU_comm_pSpan c hL hy _ hX.2
  have hu_ne : gg 0 * gg 1 ≠ 1 := fun e => hne1 (by
    rw [← hUeq, show U = 1 from Subtype.ext (by rw [hU]; exact e), map_one])
  obtain ⟨T, hTΩ, hTC, hTnot⟩ :=
    endU_exists_T hEnd hW hKD hKsD cKKs hKKs hg0 hg1 ho0 ho1 hcls
  refine ⟨gg 0 * gg 1, (hX : G), (eX : G), T, ?_⟩
  exact
    { toCaseBSit := c
      u_ne := hu_ne
      z_eq := hz_eq
      P₁_u := hP1u
      P₂_u := hP2u
      h_three := hX_ord
      h_u := hhu'
      h_P₂ := hP2h
      h_mem := hX.2
      e_u := heu'
      T_mem := ⟨hTΩ, hTC⟩
      T_not := by
        rw [← c.dcomp]
        exact hTnot }

end CaseBSit

end CFSG.ClassicalInvolution.Q3.Sec13
