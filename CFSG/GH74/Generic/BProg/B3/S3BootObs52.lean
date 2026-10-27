module

public import CFSG.GH74.Generic.BProg.B3.S3BootDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace S3BootObs52

open CFSG.GH74.GLS.Th2.Bal CFSG.ClassicalInvolution.Balance.LocalBalance

variable {G : Type} [Group G] [Finite G]

theorem exists_obs52_of_isElementaryAbelian {B : Subgroup G} (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hnot : ¬ (IsKBal 3 B ∧ IsWeakKBal 2 B)) :
    ∃ b ∈ B, ∃ D J : Subgroup G, Obs52 B b D J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hnot' : ¬ IsKBal 3 B ∨ ¬ IsWeakKBal 2 B := by
    by_contra h
    push Not at h
    exact hnot h
  rcases hnot' with h3 | h2
  ·
    unfold IsKBal at h3
    push Not at h3
    obtain ⟨D₀, hD₀, b, hbB, hb1, hnle⟩ := h3
    obtain ⟨hD₀B, hD₀el, hD₀rk⟩ := hD₀
    obtain ⟨D, hDD₀, hDcard⟩ := Th2Sig6.exists_sub_card hD₀el (k := 3) hD₀rk
    have hDB : D ≤ B := hDD₀.trans hD₀B
    have hDel : CFSG.IsElementaryAbelian 2 ↥D := Th2Sig6.isElementaryAbelian_of_le hBel hDB
    have hDrk : pRank 2 ↥D = 3 := CFSG.pRank_eq_of_card_eq_pow one_lt_two hDcard
    obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
    have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b hbB) hb1
    set H := centralizer ({b} : Set G) with hH
    have hDH : D ≤ H := fun d hd => mem_centralizer_singleton_iff.mpr (hBc d (hDB hd) b hbB)
    set Y : Subgroup G := AG D ⊓ H with hYdef
    have hY : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
      fun d hd hd1 => inf_le_left.trans (iInf₂_le d ⟨hd, hd1⟩)
    obtain ⟨c, hc, hcn⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    have hcY : c ∈ Y := ⟨Th2Sig6.AG_anti hDD₀ hc.1, hc.2⟩
    have hN1 : (Y.subgroupOf H).map (piBar b) ≠ ⊥ := by
      intro h
      apply hcn
      have hmem : piBar b ⟨c, hc.2⟩ ∈ (Y.subgroupOf H).map (piBar b) :=
        ⟨⟨c, hc.2⟩, Subgroup.mem_subgroupOf.mpr hcY, rfl⟩
      rw [h, Subgroup.mem_bot, piBar_eq_one_iff] at hmem
      exact ⟨⟨c, hc.2⟩, hmem, rfl⟩
    have hDk : 2 ^ 3 ≤ Nat.card ↥D := hDcard.ge
    obtain ⟨J, hJc, hDJ, hfaith, hnc⟩ :=
      Obs.exists_J (k := 3) (by norm_num) hDH hDk hDsq hY (le_refl _) hN1
    refine ⟨b, hbB, D, J, ⟨hb2, mem_centralizer_iff.mpr fun h hh => hBc h hh b hbB,
      ⟨hDB, hDel, hDrk.ge.trans' (by norm_num)⟩, hDrk.le, hJc, hDJ, hfaith, Or.inl ⟨hDrk, ?_⟩⟩⟩
    intro hle
    apply hnc
    rintro _ ⟨y₀, hy₀, rfl⟩ x hx
    exact Obs.piBar_commute_of_mem_centralizerSection hJc
      (hle (Subgroup.mem_subgroupOf.mp hy₀)) x hx
  ·
    unfold IsWeakKBal at h2
    push Not at h2
    obtain ⟨D₀, hD₀, b, hbB, hb1, c, hc, e, heB, hce⟩ := h2
    obtain ⟨hD₀B, hD₀el, hD₀rk⟩ := hD₀
    obtain ⟨D, hDD₀, hDcard⟩ := Th2Sig6.exists_sub_card hD₀el (k := 2) hD₀rk
    have hDB : D ≤ B := hDD₀.trans hD₀B
    have hDel : CFSG.IsElementaryAbelian 2 ↥D := Th2Sig6.isElementaryAbelian_of_le hBel hDB
    have hDrk : pRank 2 ↥D = 2 := CFSG.pRank_eq_of_card_eq_pow one_lt_two hDcard
    obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
    have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b hbB) hb1
    set H := centralizer ({b} : Set G) with hH
    have hBH : B ≤ H := fun x hx => mem_centralizer_singleton_iff.mpr (hBc x hx b hbB)
    have hDH : D ≤ H := hDB.trans hBH
    set Y : Subgroup G := AG D ⊓ H with hYdef
    have hY : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
      fun d hd hd1 => inf_le_left.trans (iInf₂_le d ⟨hd, hd1⟩)
    have hcY : c ∈ Y := ⟨Th2Sig6.AG_anti hDD₀ hc.1, hc.2⟩
    set W : Subgroup (CentralizerBar b) := (Y.subgroupOf H).map (piBar b) with hW
    set E : Subgroup (CentralizerBar b) := (B.subgroupOf H).map (piBar b) with hE
    set N : Subgroup (CentralizerBar b) := ⁅W, E⁆ with hN
    have hNW : N ≤ W := by
      rw [hN, Subgroup.commutator_le]
      rintro _ ⟨y₀, hy₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩
      have hyY : (y₀ : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy₀
      have hbB' : (b₀ : G) ∈ B := Subgroup.mem_subgroupOf.mp hb₀
      refine ⟨⁅y₀, b₀⁆, Subgroup.mem_subgroupOf.mpr ?_, map_commutatorElement _ _ _⟩
      have hcomm : ((⁅y₀, b₀⁆ : ↥H) : G) =
          (y₀ : G) * ((b₀ : G) * (y₀ : G)⁻¹ * (b₀ : G)⁻¹) := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hcomm]
      refine Y.mul_mem hyY ⟨?_, ?_⟩
      · exact conj_mem_AG (fun d hd => hBc _ hbB' d (hDB hd)) ((AG D).inv_mem hyY.1)
      · exact H.mul_mem (H.mul_mem b₀.2 (H.inv_mem y₀.2)) (H.inv_mem b₀.2)
    have hN1 : N ≠ ⊥ := by
      intro h
      apply hce
      have hcH : c ∈ H := hc.2
      have heH : e ∈ H := hBH heB
      have hmem : piBar b ⁅(⟨c, hcH⟩ : ↥H), ⟨e, heH⟩⁆ ∈ N := by
        rw [map_commutatorElement]
        exact Subgroup.commutator_mem_commutator ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hcY, rfl⟩
          ⟨⟨e, heH⟩, Subgroup.mem_subgroupOf.mpr heB, rfl⟩
      rw [h, Subgroup.mem_bot, piBar_eq_one_iff] at hmem
      exact ⟨_, hmem, rfl⟩
    have hDk : 2 ^ 2 ≤ Nat.card ↥D := hDcard.ge
    obtain ⟨J, hJc, hDJ, hfaith, hnc⟩ :=
      Obs.exists_J (k := 2) (by norm_num) hDH hDk hDsq hY hNW hN1
    refine ⟨b, hbB, D, J, ⟨hb2, mem_centralizer_iff.mpr fun h hh => hBc h hh b hbB,
      ⟨hDB, hDel, hDrk.ge⟩, hDrk.le.trans (by norm_num), hJc, hDJ, hfaith, Or.inr ⟨hDrk, ?_⟩⟩⟩
    by_contra hall
    push Not at hall
    apply hnc
    have hle : N ≤ Subgroup.centralizer
        (((J.subgroupOf H).map (piBar b) : Subgroup (CentralizerBar b)) :
          Set (CentralizerBar b)) := by
      rw [hN, Subgroup.commutator_le]
      rintro _ ⟨y₀, hy₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hyY : (y₀ : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy₀
      have hbB' : (b₀ : G) ∈ B := Subgroup.mem_subgroupOf.mp hb₀
      have hsec := hall _ hyY _ hbB'
      have key := Obs.piBar_commute_of_mem_centralizerSection hJc (z := ⁅y₀, b₀⁆) hsec x hx
      rw [map_commutatorElement] at key
      exact key.symm
    intro n hn x hx
    exact (Subgroup.mem_centralizer_iff.mp (hle hn) x hx).symm

end S3BootObs52

section SD

variable {G : Type} [Group G] [Finite G]

theorem exists_obs52 {B : Subgroup G} (hB : IsE 4 ⊤ B) (hnot : ¬ (IsKBal 3 B ∧ IsWeakKBal 2 B)) :
    ∃ b ∈ B, ∃ D J : Subgroup G, Obs52 B b D J :=
  S3BootObs52.exists_obs52_of_isElementaryAbelian hB.2.1 hnot

end SD

end CFSG.GH74.Generic.BProg.B3
