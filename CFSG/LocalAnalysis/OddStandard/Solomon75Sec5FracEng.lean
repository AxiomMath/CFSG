module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5CentA

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem exists_cover_LPlus (h : Sec5Data X n z Z S) {Aj : Subgroup X}
    (hAj : Sec5Comp X n (normalizer (Z : Set X)) Aj) {r : X} (hr2' : orderOf r = 2)
    (hscj : r ∈ centralizerSection Aj (pPrimeCoreOf 2 Aj)) :
    (Aj ⊓ LPlusIn (centralizer ({r} : Set X))).subgroupOf Aj ⊔ pPrimeCore 2 ↥Aj = ⊤ := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 8 ≤ n := h.maxdeg.1
  have hr2s : r ^ 2 = 1 := by have := pow_orderOf_eq_one r; rwa [hr2'] at this
  obtain ⟨u₀, hu₀⟩ := hAj.1
  obtain ⟨u, hu, huC⟩ := hu₀.exists_witness_centralizer_singleton hr2s hscj
  obtain ⟨hd1, hd2, -⟩ := hu.descend_singleton hAj.2 hr2s hscj huC
  set A' : Subgroup X := oTwoPrimeOf (Aj ⊓ centralizer ({r} : Set X)) with hA'
  obtain ⟨Mr, hMr, -, hEMr⟩ := exists_isIntrinsicIn_centralizer h.hypA h.maxdeg (s := r) hr2'
    (inf_le_right : normalizer (Z : Set X) ⊓ centralizer ({r} : Set X) ≤
      centralizer ({r} : Set X)) hd1 hd2
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
  have hE₀E₁ : E₀ ≤ Aj ⊓ LPlusIn (centralizer ({r} : Set X)) := le_inf hE₀Aj hE₀L
  exact le_antisymm le_top
    (hcov₀.ge.trans (sup_le_sup_right (Subgroup.subgroupOf_mono Aj hE₀E₁) _))

theorem exists_mirror_comm (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) {r : X}
    (hr2' : orderOf r = 2) (hrs : r * s = s * r)
    (hcon : K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) ≠ ⊥) :
    ∃ W : Subgroup X, IsPGroup 2 ↥W ∧
      W ≤ normalizer (pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))) : Set X) ∧
      ∀ x ∈ LPlusIn (centralizer ({r} : Set X)),
        ⁅x, s⁆ ∈ pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))) ⊔ W := by
  classical
  have hr2s : r ^ 2 = 1 := by have := pow_orderOf_eq_one r; rwa [hr2'] at this
  obtain ⟨Zs, hZs, hrZs, -⟩ := exists_mirror_sylow_normalized X n (s := s)
    (B := Subgroup.zpowers r) (aux_isPGroup_zpowers_of_sq hr2s)
    (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hrs))
  obtain ⟨g, S₁, -, -, -, hS₁⟩ := h.exists_mirror_of_sylow hs hZs
  have hrNs : r ∈ normalizer (Zs : Set X) := hrZs (Subgroup.mem_zpowers r)
  have hJ := exists_K0_normalizer_inf_ne_bot hS₁ hr2' hrs hrNs hcon
  have hL34 := hS₁.l52.c r hrNs hr2' hJ
  have hCn : centralizer ({r} : Set X) ≤
      normalizer (pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))) : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf _)
  refine ⟨Zs ⊓ centralizer ({r} : Set X), hS₁.isPGroup_Z.to_le inf_le_left,
    inf_le_right.trans hCn, fun x hx => ?_⟩
  obtain ⟨o, ho, w, hw, hxs⟩ := commutator_decomp_of_mirror hS₁.pair.mem hrs hL34 hx
  rw [hxs]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hw)

theorem sec5_centModOdd_of_K0_ne_bot (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    {Aj : Subgroup X} (hAj : Sec5Comp X n (normalizer (Z : Set X)) Aj)
    (hsAj : s ∈ normalizer (Aj : Set X)) {r : X} (hr1 : r ≠ 1) (hr2 : r * r = 1)
    (hrs : r * s = s * r) (hscj : r ∈ centralizerSection Aj (pPrimeCoreOf 2 Aj))
    (hcon : K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) ≠ ⊥) :
    CentModOdd Aj s := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 8 ≤ n := h.maxdeg.1
  have hr2s : r ^ 2 = 1 := by rw [sq]; exact hr2
  have hr2' : orderOf r = 2 := orderOf_eq_prime hr2s hr1
  set M : AhatModel X n Aj := AhatModel.ofCover hAj.2 with hM
  obtain ⟨W, hW, hWn, hV⟩ := exists_mirror_comm h hs hr2' hrs hcon
  have hcov₁ := exists_cover_LPlus h hAj hr2' hscj
  set 𝒪 : Subgroup X := pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))) with h𝒪
  have hCn : centralizer ({r} : Set X) ≤ normalizer (𝒪 : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf _)
  have hsC : s ∈ centralizer ({r} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hrs.symm
  have hE₁𝒪 : Aj ⊓ LPlusIn (centralizer ({r} : Set X)) ≤ normalizer (𝒪 : Set X) :=
    fun x hx => hCn (LPlusIn_le _ hx.2)
  have hsE : ∀ x ∈ Aj ⊓ LPlusIn (centralizer ({r} : Set X)),
      s * x * s⁻¹ ∈ Aj ⊓ LPlusIn (centralizer ({r} : Set X)) := fun x hx =>
    ⟨(Subgroup.mem_normalizer_iff.1 hsAj x).1 hx.1,
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_LPlusIn _ hsC) x).1 hx.2⟩
  have hcentral := commutator_image_central (n := n) (by omega) hsAj M.C inf_le_left hcov₁ hsE
    (odd_card_oddCoreOf _) hE₁𝒪 hW hWn (fun x hx => hV x hx.2)
  exact (M.perm_eq_one_iff hn hsAj).1 (M.perm_eq_one_of_commutator_central hn hsAj hcentral)

end CFSG.OddStandard.Solomon75
