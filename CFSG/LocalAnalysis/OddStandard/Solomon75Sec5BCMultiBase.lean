module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapNorm

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Base

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem lemmaB_core (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) {H Aj : Subgroup X}
    (hAj : Sec5Comp X n H Aj) (hsAj : s ∈ normalizer (Aj : Set X)) (hsc : ¬ CentModOdd Aj s)
    {r : X} (hr1 : r ≠ 1) (hr2 : r * r = 1) (hrs : r * s = s * r)
    (hscj : r ∈ centralizerSection Aj (pPrimeCoreOf 2 Aj)) :
    K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) = ⊥ := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 8 ≤ n := h.maxdeg.1
  have hr2s : r ^ 2 = 1 := by rw [sq]; exact hr2
  have hr2' : orderOf r = 2 := orderOf_eq_prime hr2s hr1
  set M : AhatModel X n Aj := AhatModel.ofCover hAj.2 with hM
  have hperm : M.perm s hsAj ≠ 1 := fun h1 => hsc ((M.perm_eq_one_iff hn hsAj).1 h1)
  by_contra hcon
  obtain ⟨Zs, hZs, hrZs, -⟩ := exists_mirror_sylow_normalized X n (s := s)
    (B := Subgroup.zpowers r) (aux_isPGroup_zpowers_of_sq hr2s)
    (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hrs))
  obtain ⟨g, S₁, -, -, -, hS₁⟩ := h.exists_mirror_of_sylow hs hZs
  have hrNs : r ∈ normalizer (Zs : Set X) := hrZs (Subgroup.mem_zpowers r)
  have hJ := exists_K0_normalizer_inf_ne_bot hS₁ hr2' hrs hrNs hcon
  have hL34 := hS₁.l52.c r hrNs hr2' hJ
  obtain ⟨u₀, hu₀⟩ := hAj.1
  obtain ⟨u, hu, huC⟩ := hu₀.exists_witness_centralizer_singleton hr2s hscj
  obtain ⟨hd1, hd2, -⟩ := hu.descend_singleton hAj.2 hr2s hscj huC
  set A' : Subgroup X := oTwoPrimeOf (Aj ⊓ centralizer ({r} : Set X)) with hA'
  obtain ⟨Mr, hMr, -, hEMr⟩ := exists_isIntrinsicIn_centralizer h.hypA h.maxdeg (s := r) hr2'
    (inf_le_right : H ⊓ centralizer ({r} : Set X) ≤ centralizer ({r} : Set X)) hd1 hd2
  set E₀ : Subgroup X := oTwoPrimeOf (A' ⊓ centralizer ({u} : Set X)) with hE₀
  obtain ⟨hE₀A', hcovA', -⟩ := hd1.cover_oTwoPrimeOf
  have hA'Aj : A' ≤ Aj := (oTwoPrimeOf_le _).trans inf_le_left
  have hE₀Aj : E₀ ≤ Aj := hE₀A'.trans hA'Aj
  have hE₀L : E₀ ≤ LPlusIn (centralizer ({r} : Set X)) := hEMr.trans hMr.le_LPlusIn
  have hcov₀ : E₀.subgroupOf Aj ⊔ pPrimeCore 2 ↥Aj = ⊤ := by
    have hE₀c : IsDoubleCoverOfAlt (↥E₀ ⧸ pPrimeCore 2 ↥E₀) n :=
      (isDoubleCoverOfAlt_quot_iff_of_covers hE₀A' hcovA' n).2 hd2
    refine covers_of_card_le hE₀Aj ?_
    rw [natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hAj.2,
      natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hE₀c]
  set E₁ : Subgroup X := Aj ⊓ LPlusIn (centralizer ({r} : Set X)) with hE₁
  have hE₀E₁ : E₀ ≤ E₁ := le_inf hE₀Aj hE₀L
  have hcov₁ : E₁.subgroupOf Aj ⊔ pPrimeCore 2 ↥Aj = ⊤ :=
    le_antisymm le_top (hcov₀.ge.trans (sup_le_sup_right (Subgroup.subgroupOf_mono Aj hE₀E₁) _))
  set 𝒪 : Subgroup X := pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))) with h𝒪
  have hCn : centralizer ({r} : Set X) ≤ normalizer (𝒪 : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf _)
  have hsC : s ∈ centralizer ({r} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hrs.symm
  have hE₁L : ∀ x ∈ E₁, x ∈ LPlusIn (centralizer ({r} : Set X)) := fun x hx => hx.2
  have hE₁𝒪 : E₁ ≤ normalizer (𝒪 : Set X) := fun x hx =>
    hCn (LPlusIn_le _ (hE₁L x hx))
  have hsE : ∀ x ∈ E₁, s * x * s⁻¹ ∈ E₁ := fun x hx =>
    ⟨(Subgroup.mem_normalizer_iff.1 hsAj x).1 hx.1,
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_LPlusIn _ hsC) x).1 hx.2⟩
  have hV : ∀ x ∈ E₁, ⁅x, s⁆ ∈ 𝒪 ⊔ (Zs ⊓ centralizer ({r} : Set X)) := by
    intro x hx
    obtain ⟨o, ho, w, hw, hxs⟩ := commutator_decomp_of_mirror hS₁.pair.mem hrs hL34 (hE₁L x hx)
    rw [hxs]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hw)
  have hW : IsPGroup 2 ↥(Zs ⊓ centralizer ({r} : Set X)) :=
    hS₁.isPGroup_Z.to_le inf_le_left
  have hcentral := commutator_image_central (n := n) (by omega) hsAj M.C inf_le_left hcov₁ hsE
    (odd_card_oddCoreOf _) hE₁𝒪 hW (inf_le_right.trans hCn) hV
  exact hperm (M.perm_eq_one_of_commutator_central hn hsAj hcentral)

theorem lemmaB (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) {H Aj : Subgroup X}
    (hAj : Sec5Comp X n H Aj) (hsAj : s ∈ normalizer (Aj : Set X)) (hsc : ¬ CentModOdd Aj s)
    {r : X} (hr1 : r ≠ 1) (hr2 : r * r = 1) (hrs : r * s = s * r)
    (hscj : r ∈ centralizerSection Aj (pPrimeCoreOf 2 Aj)) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B)
    (hrB : r ∈ centralizerSection B (pPrimeCoreOf 2 B)) : False := by
  have hr2s : r ^ 2 = 1 := by rw [sq]; exact hr2
  exact K0_ne_bot_of_centralizerSection hr2s hB hrB
    (lemmaB_core h hs hAj hsAj hsc hr1 hr2 hrs hscj)

end Base

section Models

variable {X : Type} [Group X] {n : ℕ}

private theorem bcdBase_exists_conj {K K' : Type} [Group K] [Group K'] (hn : 8 ≤ n)
    (C : AhatData.CoverSetup n K) (C' : AhatData.CoverSetup n K') (φ : K ≃* K') :
    ∃ g : Perm (Fin n), ∀ x : K, C'.ρ (φ x) = g * C.ρ x * g⁻¹ := by
  let e : K ⧸ center K ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq C.ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective C.π C.surj)
  let e' : K' ⧸ center K' ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq C'.ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective C'.π C'.surj)
  have he : ∀ x : K, e (QuotientGroup.mk x) = C.π x := fun x => by
    simp only [e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have he' : ∀ x : K', e' (QuotientGroup.mk x) = C'.π x := fun x => by
    simp only [e', MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  let φ' : K ⧸ center K ≃* K' ⧸ center K' :=
    QuotientGroup.congr (center K) (center K') φ (Subgroup.map_center_eq φ)
  let β : MulAut (alternatingGroup (Fin n)) := (e.symm.trans φ').trans e'
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) (by omega)).2 β
  refine ⟨σ, fun x => ?_⟩
  have h1 : C'.π (φ x) = β (C.π x) := by
    have : β (C.π x) = e' (φ' (QuotientGroup.mk x)) := by
      rw [← he x]
      simp [β]
    rw [this, QuotientGroup.congr_mk, he']
  have h2 : C'.ρ (φ x) = ((β (C.π x) : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    rw [C'.ρ_apply, h1]
  rw [h2, ← hσ, MulAut.conjNormal_apply, C.ρ_apply]

theorem AhatModel.exists_perm_conj (hn : 8 ≤ n) {A : Subgroup X} (M M' : AhatModel X n A) {c : X}
    (hc : c ∈ normalizer (A : Set X)) :
    ∃ g : Perm (Fin n), M'.perm c hc = g * M.perm c hc * g⁻¹ := by
  set φ : M.K ≃* M'.K := M.e.symm.trans M'.e with hφ
  obtain ⟨g, hg⟩ := bcdBase_exists_conj hn M.C M'.C φ
  refine ⟨g, M'.perm_eq_of_induces hn hc ⟨fun k' => ?_⟩⟩
  obtain ⟨k, rfl⟩ := φ.surjective k'
  have hφa : M'.autOf c hc (φ k) = φ (M.autOf c hc k) := by
    simp [hφ, AhatModel.autOf]
  rw [hφa, hg, (M.induces_perm hn c hc).map_ρ, hg]
  group

end Models

section Mirror

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem exists_mirror_of_Q (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    {Q : Subgroup X} (hQ : IsPGroup 2 ↥Q) (hQs : Q ≤ centralizer ({s} : Set X)) :
    ∃ (g : X) (Zs : Subgroup X) (S₁ : Sylow 2 ↥(normalizer (Zs : Set X))),
      Zs = Z.map (MulAut.conj g).toMonoidHom ∧
      IsSylowTwoIn (zStar (K0 X n (centralizer ({s} : Set X)))) Zs ∧
      Q ≤ normalizer (Zs : Set X) ∧ Sec5Data X n s Zs S₁ := by
  obtain ⟨Zs, hZs, hQZs, -⟩ := exists_mirror_sylow_normalized X n (s := s) hQ hQs
  obtain ⟨g, S₁, hg, -, -, hS₁⟩ := h.exists_mirror_of_sylow hs hZs
  exact ⟨g, Zs, S₁, hg, hZs, hQZs, hS₁⟩

end Mirror

end CFSG.OddStandard.Solomon75
