module

public import CFSG.GH74.GLS.C3.Layer1.Th2HYStruct
public import CFSG.GH74.GLS.C3.Layer1.Th2HYComp

public section

namespace CFSG.GH74.GLS.Th2.HY

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

variable {G : Type} [Group G]

section W1

variable [Finite G]

theorem W1_facts {K L : Subgroup G} (hKL : K ≤ L) (hLeq : L = pPrimeCoreOf 2 L ⊔ K) :
    pPrimeCoreOf 2 K ⊔ pPrimeCoreOf 2 L ≤ L ∧
    L ≤ normalizer ((pPrimeCoreOf 2 K ⊔ pPrimeCoreOf 2 L : Subgroup G) : Set G) ∧
    Odd (Nat.card ↥(pPrimeCoreOf 2 K ⊔ pPrimeCoreOf 2 L)) := by
  have hOK : pPrimeCoreOf 2 K ≤ L := (TwoThin.pPrimeCoreOf_le K).trans hKL
  have hOL : pPrimeCoreOf 2 L ≤ L := TwoThin.pPrimeCoreOf_le L
  have hKN : ∀ k ∈ K, k ∈ normalizer ((pPrimeCoreOf 2 L : Subgroup G) : Set G) := fun k hk =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hKL hk))
  have hOKN : pPrimeCoreOf 2 K ≤ normalizer ((pPrimeCoreOf 2 L : Subgroup G) : Set G) := fun o ho =>
    hKN o ((TwoThin.pPrimeCoreOf_le K) ho)
  refine ⟨sup_le hOK hOL, ?_, ?_⟩
  · refine hLeq.le.trans (sup_le (le_sup_right.trans Subgroup.le_normalizer) (fun k hk => ?_))
    have h1 : k ∈ normalizer ((pPrimeCoreOf 2 K : Subgroup G) : Set G) :=
      TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hk)
    exact mem_normalizer_sup h1 (hKN k hk)
  · have h1 := card_sup_mul_card_inf_of_le_normalizer hOKN
    have hodd : Odd (Nat.card ↥(pPrimeCoreOf 2 K) * Nat.card ↥(pPrimeCoreOf 2 L)) :=
      (TwoThin.card_pPrimeCoreOf_odd K).mul (TwoThin.card_pPrimeCoreOf_odd L)
    rw [← h1] at hodd
    exact (Nat.odd_mul.1 hodd).1

end W1

section Main

variable [Finite G]

theorem Y_comm_K_of_cover {K V : Subgroup G}
    (hcov : ∀ k ∈ K, ∃ l ∈ lamV K V, ∃ o ∈ pPrimeCoreOf 2 K, k = l * o) {M L : Subgroup G}
    (hKM : K ≤ M) (hO : OV V ≤ M) (hLcomp : IsPCompIn 2 M L) (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hKL : K ≤ L) {y' : G} (hy : y' ∈ YV K V) (hyM : y' ∈ M) :
    ∀ k ∈ K, ⁅k, y'⁆ ∈ pPrimeCoreOf 2 M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hW1L, hLW1, hW1odd⟩ := W1_facts hKL hLeq
  have hLM : L ≤ M := hLcomp.1
  have hW1M : (pPrimeCoreOf 2 K ⊔ pPrimeCoreOf 2 L) ≤ M := hW1L.trans hLM
  let π : ↥M →* barQ ↥M := barMk ↥M
  let Lt : Subgroup (barQ ↥M) := (L.subgroupOf M).map π
  let A : Subgroup (barQ ↥M) := ((lamV K V).subgroupOf M).map π
  let W : Subgroup (barQ ↥M) := ((pPrimeCoreOf 2 K ⊔ pPrimeCoreOf 2 L).subgroupOf M).map π
  let Ō : Subgroup (barQ ↥M) := ((OV V).subgroupOf M).map π
  have hLK' : lamV K V ≤ K := (twoGen_le _).trans inf_le_left
  have hcompLt : CFSG.IsComponent Lt := isComponent_map_barMk (isPCompIn_two_iff.mp hLcomp).2
  have hAL : A ≤ Lt := Subgroup.map_mono (fun l hl =>
    Subgroup.mem_subgroupOf.2 (hKL (hLK' (Subgroup.mem_subgroupOf.1 hl))))
  have hWL : W ≤ Lt := Subgroup.map_mono (fun l hl =>
    Subgroup.mem_subgroupOf.2 (hW1L (Subgroup.mem_subgroupOf.1 hl)))
  have hWn : ∀ l ∈ Lt, ∀ w ∈ W, l * w * l⁻¹ ∈ W := by
    rintro _ ⟨l, hl, rfl⟩ _ ⟨w, hw, rfl⟩
    refine ⟨l * w * l⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (hLW1 (Subgroup.mem_subgroupOf.1 hl)) (w : G)).1
      (Subgroup.mem_subgroupOf.1 hw)
    simpa using h1
  have hcardW : ∀ {B : Subgroup G}, B ≤ M → Odd (Nat.card ↥B) →
      Odd (Nat.card ↥((B.subgroupOf M).map π)) := by
    intro B hBM hBodd
    have h1 : Nat.card ↥((B.subgroupOf M).map π) ∣ Nat.card ↥(B.subgroupOf M) :=
      Subgroup.card_map_dvd _ π
    have h2 : Nat.card ↥(B.subgroupOf M) = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
    rw [h2] at h1
    exact hBodd.of_dvd_nat h1
  have hWodd : Odd (Nat.card ↥W) := hcardW hW1M hW1odd
  have hŌodd : Odd (Nat.card ↥Ō) := hcardW hO (TwoThin.card_pPrimeCoreOf_odd _)
  have hLeven : ¬ Odd (Nat.card ↥Lt) := by
    intro hodd
    have hsolv : Group.IsSolvable ↥Lt := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : Nontrivial ↥Lt := CFSG.LocalCores.isQuasisimple_nontrivial hcompLt.1
    have : Group.IsPerfect ↥Lt := hcompLt.1.1
    exact Group.IsPerfect.not_isSolvable ↥Lt inferInstance
  have hKN' : K ≤ normalizer ((pPrimeCoreOf 2 L : Subgroup G) : Set G) := fun k hk =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hKL hk))
  have hLeq' : L = K ⊔ pPrimeCoreOf 2 L := hLeq.trans (sup_comm _ _)
  have hcov : ∀ l ∈ Lt, ∃ s ∈ A, ∃ w ∈ W, l = s * w := by
    rintro _ ⟨l, hl, rfl⟩
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
    rw [hLeq'] at hlL
    obtain ⟨k, hk, oL, hoL, hlk⟩ := (mem_sup_iff_mul_of_le_normalizer hKN').1 hlL
    obtain ⟨lam, hlam, oK, hoK, hkk⟩ := hcov k hk
    have hlamM : lam ∈ M := hKM (hLK' hlam)
    have hw1 : oK * oL ∈ pPrimeCoreOf 2 K ⊔ pPrimeCoreOf 2 L :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hoK) (Subgroup.mem_sup_right hoL)
    refine ⟨π ⟨lam, hlamM⟩, ⟨⟨lam, hlamM⟩, Subgroup.mem_subgroupOf.2 hlam, rfl⟩,
      π ⟨oK * oL, hW1M hw1⟩, ⟨⟨oK * oL, hW1M hw1⟩, Subgroup.mem_subgroupOf.2 hw1, rfl⟩, ?_⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hlk, hkk]
    group
  have hAeq : A = Lt := eq_of_cover_odd hcompLt.1 hAL hWL hWn hWodd hLeven hcov
  have hgen : A ≤ Subgroup.closure {t : barQ ↥M | t ∈ A ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1} := by
    have h1 : lamV K V ≤ ((Subgroup.closure {t : barQ ↥M | t ∈ A ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1}).comap
        π).map M.subtype := by
      refine twoGen_le_of_forall (fun g hg k hgk => ?_)
      have hgM : g ∈ M := hKM hg.1
      refine ⟨⟨g, hgM⟩, ?_, rfl⟩
      show π ⟨g, hgM⟩ ∈ Subgroup.closure {t : barQ ↥M | t ∈ A ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1}
      refine Subgroup.subset_closure ⟨⟨⟨g, hgM⟩, Subgroup.mem_subgroupOf.2 (subset_twoGen hg hgk), rfl⟩,
        k, ?_⟩
      rw [← map_pow]
      have : (⟨g, hgM⟩ : ↥M) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hgk)
      rw [this, map_one]
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨m, hm, hml⟩ := h1 (Subgroup.mem_subgroupOf.1 hl)
    have : m = l := Subtype.ext hml
    subst this
    exact hm
  have hcompA : CFSG.IsComponent A := hAeq ▸ hcompLt
  have hc : ∀ σ ∈ A, ⁅σ, π ⟨y', hyM⟩⁆ ∈ Ō := by
    rintro _ ⟨l, hl, rfl⟩
    have hlH : (l : G) ∈ HV K V := Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hl)
    have h1 : ⁅(l : G), y'⁆ ∈ OV V := hy.2.2.2 _ hlH
    refine ⟨⟨⁅(l : G), y'⁆, hO h1⟩, Subgroup.mem_subgroupOf.2 h1, ?_⟩
    have e : (⟨⁅(l : G), y'⁆, hO h1⟩ : ↥M) = ⁅l, ⟨y', hyM⟩⁆ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [e, map_commutatorElement]
  have hcen := comp_centralizes_of_commutators_odd hcompA hgen hŌodd hc
  intro k hk
  have hkL : k ∈ L := hKL hk
  have hσ : π ⟨k, hKM hk⟩ ∈ A := hAeq ▸ ⟨⟨k, hKM hk⟩, Subgroup.mem_subgroupOf.2 hkL, rfl⟩
  have h2 := hcen _ hσ
  have hm : ⁅k, y'⁆ ∈ M := by
    simp only [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem (hKM hk) hyM) (M.inv_mem (hKM hk))) (M.inv_mem hyM)
  have h3 : π ⟨⁅k, y'⁆, hm⟩ = 1 := by
    have h4 : π ⟨⁅k, y'⁆, hm⟩ = ⁅π ⟨k, hKM hk⟩, π ⟨y', hyM⟩⁆ := by
      have e : (⟨⁅k, y'⁆, hm⟩ : ↥M) = ⁅(⟨k, hKM hk⟩ : ↥M), ⟨y', hyM⟩⁆ :=
        Subtype.ext (by simp [commutatorElement_def])
      rw [e, map_commutatorElement]
    rw [h4]
    have : π ⟨k, hKM hk⟩ * π ⟨y', hyM⟩ = π ⟨y', hyM⟩ * π ⟨k, hKM hk⟩ := by
      have h5 := congrArg (fun z => z * π ⟨y', hyM⟩) h2
      simp only [mul_assoc, inv_mul_cancel, mul_one] at h5
      exact h5.symm
    exact commutatorElement_eq_one_iff_mul_comm.2 this
  exact C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hm, (QuotientGroup.eq_one_iff _).1 h3⟩

theorem Y_comm_K {x y : G} {K T S V : Subgroup G} (hS : HYSetup x y K T S V) {M L : Subgroup G}
    (hKM : K ≤ M) (hO : OV V ≤ M) (hLcomp : IsPCompIn 2 M L) (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hKL : K ≤ L) {y' : G} (hy : y' ∈ YV K V) (hyM : y' ∈ M) :
    ∀ k ∈ K, ⁅k, y'⁆ ∈ pPrimeCoreOf 2 M :=
  Y_comm_K_of_cover hS.lam_cover hKM hO hLcomp hLeq hKL hy hyM

theorem Q₁_sylow_YV (hG : C3Hyp G) {x y : G} {K T S V : Subgroup G} (hS : HYSetup x y K T S V)
    {M L U : Subgroup G} (hKM : K ≤ M) (hO : OV V ≤ M) (hLcomp : IsPCompIn 2 M L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) (hKL : K ≤ L) (hU : IsFourSub (T ⊓ K) U)
    (hFM : normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M)
    (hQ1 : IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))
      (normalizer (V : Set G) ⊓ CMbar M K)) :
    IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) (YV K V) := by
  have hYM : YV K V ≤ M := hS.YV_le_M hO hU hFM
  have hYC : YV K V ≤ normalizer (V : Set G) ⊓ CMbar M K := fun y' hy =>
    ⟨hy.1, mem_CMbar_of_comm hKM (hYM hy)
      (Y_comm_K hS hKM hO hLcomp hLeq hKL hy (hYM hy))⟩
  exact isSylowOf_of_le_of_le hQ1 (hS.Q₁_le_YV hG) hYC

end Main

end CFSG.GH74.GLS.Th2.HY
