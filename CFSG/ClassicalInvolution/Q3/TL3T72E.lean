module

public import CFSG.ClassicalInvolution.Q3.TL3T63
public import CFSG.ClassicalInvolution.Q3.TL3T72C
public import CFSG.ClassicalInvolution.Q3.TL3T61

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

section Count

variable {G : Type} [Group G] {P : Set (Subgroup G)} {n : ℕ}

theorem AEIdent.ncard_over' (I : AEIdent P n) (hn : 5 ≤ n)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    (Γ : Finset (Fin n)) : (I.over Γ).ncard = Γ.card.choose 4 * 2 := by
  classical
  set S : Finset (Finset (Fin n) × Bool) := Γ.powersetCard 4 ×ˢ Finset.univ with hS
  let f : Finset (Fin n) × Bool → Subgroup G := fun p =>
    if h : p.1.card = 4 then Classical.choose (I.label_surj p.1 h p.2) else ⊥
  have hf : ∀ p ∈ S, ∃ h : p.1.card = 4, f p ∈ P ∧
      ((f p).subgroupOf (pSpan P)).map I.φ = memBar p.1 h p.2 := by
    intro p hp
    have h4 : p.1.card = 4 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
    refine ⟨h4, ?_⟩
    simp only [f, h4, ↓reduceDIte]
    exact Classical.choose_spec (I.label_surj p.1 h4 p.2)
  have himage : I.over Γ = f '' (S : Set (Finset (Fin n) × Bool)) := by
    ext L
    constructor
    · rintro ⟨hL, α, h, b, hαΓ, hlab⟩
      have hp : (α, b) ∈ S :=
        Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨hαΓ, h⟩, Finset.mem_univ _⟩
      obtain ⟨h4', hfP, hflab⟩ := hf _ hp
      exact ⟨(α, b), hp, hinj _ hfP L hL (hflab.trans hlab.symm)⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨h4, hfP, hflab⟩ := hf p hp
      exact ⟨hfP, p.1, h4, p.2,
        (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).1, hflab⟩
  have hinjOn : Set.InjOn f (S : Set (Finset (Fin n) × Bool)) := by
    intro p hp q hq hpq
    obtain ⟨hp4, -, hplab⟩ := hf p hp
    obtain ⟨hq4, -, hqlab⟩ := hf q hq
    have e : memBar p.1 hp4 p.2 = memBar q.1 hq4 q.2 := by rw [← hplab, ← hqlab, hpq]
    have h1 : p.1 = q.1 := eq_of_memBar_eq' hn e
    have h2 : p.2 = q.2 := by
      obtain ⟨α, b⟩ := p
      obtain ⟨β, c⟩ := q
      simp only at h1 e ⊢
      subst h1
      cases b <;> cases c
      · rfl
      · exact absurd e.symm (memBar_true_ne_false hn α hp4)
      · exact absurd e (memBar_true_ne_false hn α hp4)
      · rfl
    exact Prod.ext h1 h2
  rw [himage, hinjOn.ncard_image, Set.ncard_coe_finset, hS, Finset.card_product,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_bool]

end Count

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CSetting

variable {K J : Subgroup G} (hS : CSetting 3 IH Ω K J)
include hS

theorem aeCoverHyp_centMembers' {u : G} {m : ℕ} (hm5 : 5 ≤ m) (hm8 : m ≠ 8)
    (IY : AEIdent (centMembers Ω u) m)
    (hodd : classicalInvolutionOddCore ↥(pSpan (centMembers Ω u)) = ⊥)
    (htrans : ∀ L ∈ centMembers Ω u, ∀ L' ∈ centMembers Ω u,
      ∃ x ∈ pSpan (centMembers Ω u), conjSub x L = L')
    {J₀ J₀' : Subgroup G} (hJ₀ : J₀ ∈ centMembers Ω u) (hJ₀' : J₀' ∈ centMembers Ω u)
    (hne : J₀ ≠ J₀')
    (hz : ∀ v v' : G, IsUniqueInvolution J₀ v → IsUniqueInvolution J₀' v' → v = v') :
    TL4.AECoverHyp IY := by
  have hD := hS.cex.toThmDHyp
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hD.card L hL]; norm_num
  have hPΩ : centMembers Ω u ⊆ Ω := fun _ h => h.1
  have hk : IsPGroup 2 IY.φ.ker := IY.toLabel.isPGroup_ker hodd
  have hconj : ∀ L ∈ centMembers Ω u, ∀ x ∈ pSpan (centMembers Ω u),
      conjSub x L ∈ centMembers Ω u := fun L hL x hx => hS.conjSub_mem_centMembers u hL hx
  have hinj : ∀ L ∈ centMembers Ω u, ∀ L' ∈ centMembers Ω u,
      (L.subgroupOf (pSpan (centMembers Ω u))).map IY.φ =
        (L'.subgroupOf (pSpan (centMembers Ω u))).map IY.φ → L = L' :=
    fun L hL L' hL' h => aeIdent_eq_of_map_eq hD.hyp hD.two hPΩ hm5 IY hk hL hL' h
  obtain ⟨δ, hδ, c, hlab⟩ := IY.label J₀ hJ₀
  obtain ⟨γ, hγ, c', hlab'⟩ := IY.label J₀' hJ₀'
  obtain ⟨⟨v, hv⟩, -⟩ := hD.hyp.omega1 J₀ hJ₀.1
  obtain ⟨⟨v', hv'⟩, -⟩ := hD.hyp.omega1 J₀' hJ₀'.1
  have e1 := IY.map_eq_zBar hm5 hJ₀ (h8 J₀ hJ₀.1) hlab hv
  have e2 := IY.map_eq_zBar hm5 hJ₀' (h8 J₀' hJ₀'.1) hlab' hv'
  have hvv : v = v' := hz v v' hv hv'
  have hγδ : γ = δ := by
    apply AE.eq_of_zBar_eq hm8
    rw [← e1, ← e2]
    congr 1
    exact Subtype.ext hvv.symm
  subst hγδ
  have hc' : c' = !c := by
    by_contra hne'
    have : c' = c := by cases c <;> cases c' <;> simp_all
    subst this
    exact hne (hinj J₀ hJ₀ J₀' hJ₀' (hlab.trans hlab'.symm))
  subst hc'
  exact
    { ker_two := hk
      card := fun L hL => h8 L hL.1
      conj_mem := hconj
      label_inj := hinj
      twin_comm := by
        intro α h L hL L' hL' hl hl'
        refine aeIdent_comm_of_map_comm hD.hyp hD.two hPΩ IY hk hL hL' ?_ ?_
        · intro e
          subst e
          rw [hl] at hl'
          exact AE.memBar_true_ne_false hm5 α h hl'
        · rw [hl, hl']
          exact memBar_twin_comm α h true
      twin_z := IY.twin_z_of_trans hm5 hm8 hconj hinj htrans hJ₀ hJ₀' hlab hlab' hz }

theorem choose_eq_centMembers' {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    {t u : G} (ht : conjSub t K = J) (ht' : conjSub t J = K)
    (huX' : u ∈ pSpan (orbOf (TC.nbrAdj Ω) J K)) {a c : Fin n} (hac : a ≠ c)
    (hwt : t⁻¹ * u * t ∈ pSpan (orbOf (TC.nbrAdj Ω) K J))
    (hut : I.φ ⟨t⁻¹ * u * t, hwt⟩ = mkQ n (ofVec (TL4.pairVec a c)))
    {m : ℕ} (IY : AEIdent (centMembers Ω u) m) (hm5 : 5 ≤ m) (hk : IsPGroup 2 IY.φ.ker)
    (hπY : orbOf (TC.nbrAdj Ω) K J ⊆ centMembers Ω u) :
    (n - 2).choose 4 = (m - 4).choose 4 := by
  classical
  have hC := hS.toCHyp
  have hD := hS.cex.toThmDHyp
  have hn5 : 5 ≤ n := hn
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hD.card L hL]; norm_num
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJΩ : J ∈ Ω := hC.orb_subset_omega hJπ
  have hPΩ : centMembers Ω u ⊆ Ω := fun _ h => h.1
  have hinjY : ∀ L ∈ centMembers Ω u, ∀ L' ∈ centMembers Ω u,
      (L.subgroupOf (pSpan (centMembers Ω u))).map IY.φ =
        (L'.subgroupOf (pSpan (centMembers Ω u))).map IY.φ → L = L' :=
    fun L hL L' hL' h => aeIdent_eq_of_map_eq hD.hyp hD.two hPΩ hm5 IY hk hL hL' h
  obtain ⟨I''⟩ := hC.nonempty_aeIdent_swap I
  obtain ⟨gs, Js, ys, hDs, -, -, hJsπ', hJsX, hzs⟩ := hC.swap.exists_twin hn5 I''
  have hJsπ : Js ∈ orbOf (TC.nbrAdj Ω) K J := by
    have h1 := hDs.Ks_mem
    rwa [hC.swap.orb_swap_eq hDs.hg] at h1
  have hJsJ : Js ≠ J := hDs.Ks_ne
  have hΩJ : ∀ {M : Subgroup G}, M ∈ omegaNbr Ω J →
      M ∈ orbOf (TC.nbrAdj Ω) J K ∨ M = Js := by
    intro M hM
    exact hS.swap.eq_of_mem_omegaNbr_of_five_le hn I'' I hJsπ hJsJ hJsπ' hzs hJsX hM
  have he : conjSub t '' orbOf (TC.nbrAdj Ω) K J = orbOf (TC.nbrAdj Ω) J K := by
    rw [← orbOf_conj hC.graphFam'.graph K J t, ht, ht']
  obtain ⟨I', hI'⟩ : ∃ I' : AEIdent (conjSub t '' orbOf (TC.nbrAdj Ω) K J) n,
      I' = I.conjE t := ⟨_, rfl⟩
  have huX : u ∈ pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J) := by rw [he]; exact huX'
  have hI'u : I'.φ ⟨u, huX⟩ = mkQ n (ofVec (TL4.pairVec a c)) := by
    rw [← hut, hI', AEIdent.conjE_apply I t huX hwt]
  have hP'Ω : conjSub t '' orbOf (TC.nbrAdj Ω) K J ⊆ Ω := by
    rw [he]
    exact hC.swap.orb_subset_omega
  have hodd' : classicalInvolutionOddCore ↥(pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J)) = ⊥ := by
    rw [he]
    exact hC.swap.oddCore_orb_eq_bot
  have hk' : IsPGroup 2 I'.φ.ker := I'.toLabel.isPGroup_ker hodd'
  have hconj' : ∀ L ∈ conjSub t '' orbOf (TC.nbrAdj Ω) K J,
      ∀ x ∈ pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J),
      conjSub x L ∈ conjSub t '' orbOf (TC.nbrAdj Ω) K J := by
    rw [he]
    exact fun L hL x hx => CSetting.conjSub_mem_orb hJΩ (hC.swap.pSpan_orb_le hx) hL
  have hinj' : ∀ L ∈ conjSub t '' orbOf (TC.nbrAdj Ω) K J,
      ∀ L' ∈ conjSub t '' orbOf (TC.nbrAdj Ω) K J,
      (L.subgroupOf (pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J))).map I'.φ =
        (L'.subgroupOf (pSpan (conjSub t '' orbOf (TC.nbrAdj Ω) K J))).map I'.φ → L = L' :=
    fun L hL L' hL' h => aeIdent_eq_of_map_eq hD.hyp hD.two hP'Ω hn5 I' hk' hL hL' h
  have h8' : ∀ L ∈ conjSub t '' orbOf (TC.nbrAdj Ω) K J, Nat.card ↥L = 8 :=
    fun L hL => h8 L (hP'Ω hL)
  have hJY : J ∈ centMembers Ω u := hπY hJπ
  obtain ⟨δ, hδ, b, hlabJ⟩ := IY.label J hJY
  set E : Set (Subgroup G) := {M | M ∈ centMembers Ω u ∧
    (M.subgroupOf (pSpan (centMembers Ω u))).map IY.φ = memBar δ hδ (!b)}
  have hE1 : E.ncard ≤ 1 := Set.ncard_le_one_iff_subsingleton.mpr fun M₁ h₁ M₂ h₂ =>
    hinjY M₁ h₁.1 M₂ h₂.1 (h₁.2.trans h₂.2.symm)
  have hsub₁ : IY.over δᶜ ⊆ insert Js (I'.over ({a, c} : Finset (Fin n))ᶜ) := by
    rintro M ⟨hM, γ, hγ, e, hγδ, hlabM⟩
    have hdisj : Disjoint γ δ := Finset.disjoint_left.mpr fun x hx hxδ =>
      Finset.mem_compl.mp (hγδ hx) hxδ
    have hMJ : M ≠ J := by
      rintro rfl
      rw [hlabJ] at hlabM
      exact AE.memBar_ne_of_disjoint hdisj.symm b e hlabM
    have hcomm : ∀ x ∈ M, ∀ y ∈ J, x * y = y * x :=
      aeIdent_comm_of_map_comm hD.hyp hD.two (fun _ h => h.1) IY hk hM hJY hMJ
        (by rw [hlabM, hlabJ]; exact AE.comm_memBar_of_disjoint hdisj e b)
    have hJM : TC.nbrAdj Ω J M := hC.nbrAdj_of_comm hJΩ hM.1 hMJ fun x hx y hy =>
      (hcomm y hy x hx).symm
    by_cases hMJs : M = Js
    · exact Set.mem_insert_iff.mpr (Or.inl hMJs)
    refine Set.mem_insert_iff.mpr (Or.inr ?_)
    have hMo : M ∈ conjSub t '' orbOf (TC.nbrAdj Ω) K J := by
      rw [he]
      exact (hΩJ hJM.2).resolve_right hMJs
    obtain ⟨β, hβ, d, hlabβ⟩ := I'.label M hMo
    have hcu := (I'.comm_pairVec_iff hn5 h8' hconj' hinj' hac hI'u hMo hlabβ).mp
      fun l hl => (hM.2 l hl).symm
    refine ⟨hMo, β, hβ, d, fun x hx => ?_, hlabβ⟩
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact hcu.1 hx
    · exact hcu.2 hx
  have hsub₂ : I'.over ({a, c} : Finset (Fin n))ᶜ ⊆ IY.over δᶜ ∪ E := by
    rintro M ⟨hMo, β, hβ, d, hβac, hlabβ⟩
    have ha' : a ∈ ({a, c} : Finset (Fin n)) := Finset.mem_insert_self a {c}
    have hc'' : c ∈ ({a, c} : Finset (Fin n)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self c)
    have hac' : a ∉ β ∧ c ∉ β := ⟨fun h => Finset.mem_compl.mp (hβac h) ha',
      fun h => Finset.mem_compl.mp (hβac h) hc''⟩
    have hcu := (I'.comm_pairVec_iff hn5 h8' hconj' hinj' hac hI'u hMo hlabβ).mpr hac'
    have hMΩ : M ∈ Ω := hP'Ω hMo
    have hMY : M ∈ centMembers Ω u := ⟨hMΩ, fun l hl => (hcu l hl).symm⟩
    have hMo' : M ∈ orbOf (TC.nbrAdj Ω) J K := by rw [← he]; exact hMo
    have hcomm : ∀ x ∈ M, ∀ y ∈ J, x * y = y * x := fun x hx y hy =>
      (comm_of_mem_omegaNbr hD.hyp hD.two hJΩ (hC.swap.orb_subset hMo') y hy x hx).symm
    obtain ⟨γ, hγ, e, hlabM⟩ := IY.label M hMY
    have himg : ∀ x ∈ memBar γ hγ e, ∀ y ∈ memBar δ hδ b, x * y = y * x := by
      intro x hx y hy
      rw [← hlabM] at hx
      rw [← hlabJ] at hy
      obtain ⟨l, hl, rfl⟩ := IY.exists_of_mem_map hMY hx
      obtain ⟨j, hj, rfl⟩ := IY.exists_of_mem_map hJY hy
      rw [← map_mul, ← map_mul]
      exact congrArg IY.φ (Subtype.ext (hcomm l hl j hj))
    rcases eq_or_disjoint_of_comm himg with hγδ | hdisj
    · subst hγδ
      have hJnot : J ∉ orbOf (TC.nbrAdj Ω) J K := fun h =>
        (hC.swap.orb_subset h).2.1 rfl
      by_cases he' : e = b
      · exfalso
        subst he'
        have hMJ := hinjY M hMY J hJY (hlabM.trans hlabJ.symm)
        rw [hMJ] at hMo'
        exact hJnot hMo'
      · have : e = !b := by cases e <;> cases b <;> first | rfl | exact absurd rfl he'
        subst this
        exact Set.mem_union_right _ ⟨hMY, hlabM⟩
    · exact Set.mem_union_left _ ⟨hMY, γ, hγ, e, fun x hx => Finset.mem_compl.mpr fun hxδ =>
        Finset.disjoint_left.mp hdisj hx hxδ, hlabM⟩
  have hle₁ : (IY.over δᶜ).ncard ≤ (I'.over ({a, c} : Finset (Fin n))ᶜ).ncard + 1 :=
    (Set.ncard_le_ncard hsub₁).trans (Set.ncard_insert_le _ _)
  have hle₂ : (I'.over ({a, c} : Finset (Fin n))ᶜ).ncard ≤ (IY.over δᶜ).ncard + 1 :=
    calc _ ≤ (IY.over δᶜ ∪ E).ncard := Set.ncard_le_ncard hsub₂
      _ ≤ (IY.over δᶜ).ncard + E.ncard := Set.ncard_union_le _ _
      _ ≤ _ := by omega
  have h1 := IY.ncard_over' hm5 hinjY δᶜ
  have h2 := I'.ncard_over' hn5 hinj' ({a, c} : Finset (Fin n))ᶜ
  rw [Finset.card_compl, Fintype.card_fin, hδ] at h1
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hac] at h2
  omega

theorem degree_le_centMembers' {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    {t u : G} (ht : conjSub t K = J) (ht' : conjSub t J = K)
    (huX' : u ∈ pSpan (orbOf (TC.nbrAdj Ω) J K)) {a c : Fin n} (hac : a ≠ c)
    (hwt : t⁻¹ * u * t ∈ pSpan (orbOf (TC.nbrAdj Ω) K J))
    (hut : I.φ ⟨t⁻¹ * u * t, hwt⟩ = mkQ n (ofVec (TL4.pairVec a c)))
    {m : ℕ} (IY : AEIdent (centMembers Ω u) m) (hm5 : 5 ≤ m) (hk : IsPGroup 2 IY.φ.ker)
    (hπY : orbOf (TC.nbrAdj Ω) K J ⊆ centMembers Ω u) : m ≤ n + 2 := by
  have h := hS.choose_eq_centMembers' hn I ht ht' huX' hac hwt hut IY hm5 hk hπY
  by_contra hlt
  have := choose_four_lt (a := n - 2) (b := m - 4) (by omega) (by omega)
  omega

theorem degree_centMembers' {n : ℕ} (hn : 6 ≤ n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    {t u : G} (ht : conjSub t K = J) (ht' : conjSub t J = K)
    (huX' : u ∈ pSpan (orbOf (TC.nbrAdj Ω) J K)) {a c : Fin n} (hac : a ≠ c)
    (hwt : t⁻¹ * u * t ∈ pSpan (orbOf (TC.nbrAdj Ω) K J))
    (hut : I.φ ⟨t⁻¹ * u * t, hwt⟩ = mkQ n (ofVec (TL4.pairVec a c)))
    {m : ℕ} (IY : AEIdent (centMembers Ω u) m) (hm5 : 5 ≤ m) (hk : IsPGroup 2 IY.φ.ker)
    (hπY : orbOf (TC.nbrAdj Ω) K J ⊆ centMembers Ω u) : m = n + 2 := by
  have h := hS.choose_eq_centMembers' (by omega) I ht ht' huX' hac hwt hut IY hm5 hk hπY
  have h4 : 4 ≤ n - 2 := by omega
  have h5 : 4 ≤ m - 4 := by
    by_contra hlt
    have h6 : (m - 4).choose 4 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h7 := Nat.choose_pos h4
    omega
  have := eq_of_choose_four_eq h4 h5 h
  omega

end CSetting

end CFSG.ClassicalInvolution.Q3.TC.Thin
