module

public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightSL
public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightGaps

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.RankThree.PartOne CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Campbell CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem center_sl2_eq_bot {K : Type*} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Subgroup.mem_bot]
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h1 : (r - 1) ^ 2 = 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    calc (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
      _ = 1 - 0 * r + 1 := by rw [hr2, h2]
      _ = 2 := by ring
      _ = 0 := h2
  have h3 : r = 1 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
    exact sub_eq_zero.1 this
  apply Subtype.ext
  rw [← hrA, h3]
  simp

theorem exists_four_galoisField {n : ℕ} (hn : 2 ≤ n) :
    ∃ s : Finset (GaloisField 2 n), s.card = 4 := by
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n (by omega)
  have h2 : 4 ≤ Fintype.card (GaloisField 2 n) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (GaloisField 2 n))) (n := 4) (by simpa using h2)
  exact ⟨t, ht⟩

theorem isSimpleGroup_sl2_galoisField {n : ℕ} (hn : 2 ≤ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  obtain ⟨-, hsimple⟩ := isQuasisimple_special_linear_two (exists_four_galoisField hn)
  have hc := center_sl2_eq_bot (K := GaloisField 2 n)
  exact ((QuotientGroup.quotientBot
    (G := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc.symm)).isSimpleGroup

theorem isPerfect_sl2_galoisField {n : ℕ} (hn : 2 ≤ n) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
  CFSG.LinearGroups.special_linear_isPerfect (K := GaloisField 2 n) (n := 2) le_rfl
    (Or.inr (exists_four_galoisField hn))

theorem isPerfect_of_isLin2TypeGF [Finite Γ] {E : Subgroup Γ} {n : ℕ} (hn : 2 ≤ n)
    (hshort : IsShort2 E) (h : IsLin2TypeGF E n) : Group.IsPerfect ↥E := by
  classical
  obtain ⟨α, hαs, hαk, -⟩ := h
  have hSL := isPerfect_sl2_galoisField hn
  set C : Subgroup ↥E := commutator ↥E with hC
  have hαC : C.map α = ⊤ := by
    rw [hC, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hαs]
    exact Group.IsPerfect.commutator_eq_top
  have hq : IsPGroup 2 (↥E ⧸ C) := by
    intro x
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : α e ∈ C.map α := hαC ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hce⟩ := h1
    have h2 : c⁻¹ * e ∈ CFSG.pCore 2 ↥E := by
      rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥E)) ⟨c⁻¹ * e, h2⟩
    refine ⟨j, ?_⟩
    have hj' : (c⁻¹ * e) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hmk : (QuotientGroup.mk e : ↥E ⧸ C) = QuotientGroup.mk (c⁻¹ * e) := by
      rw [QuotientGroup.eq]
      have : e⁻¹ * (c⁻¹ * e) ∈ C := by
        have := (inferInstance : C.Normal).conj_mem c⁻¹ (C.inv_mem hc) e⁻¹
        simpa [mul_assoc] using this
      exact this
    rw [hmk, ← QuotientGroup.mk_pow, hj']
    rfl
  have htop : C = ⊤ := hshort.1 C hq
  exact Group.isPerfect_def.mpr (by rw [← hC]; exact htop)

theorem perfect_of_isLin2TypeGF [Finite Γ] (hmult : SL2EvenMultiplierTrivial) {E : Subgroup Γ}
    {n : ℕ} (hn : 3 ≤ n) (hshort : IsShort2 E) (h : IsLin2TypeGF E n) :
    ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E := by
  classical
  have hperf : Group.IsPerfect ↥E := isPerfect_of_isLin2TypeGF (by omega) hshort h
  obtain ⟨α, hαs, hαk, -⟩ := h
  set U : Subgroup ↥E := shortU ↥E with hU
  have hUnorm : U.Normal := by
    rw [hU]
    unfold shortU
    infer_instance
  have hUQ : U ≤ CFSG.pCore 2 ↥E := by
    have h1 : ⁅CFSG.pCore 2 ↥E, (⊤ : Subgroup ↥E)⁆ ≤ CFSG.pCore 2 ↥E :=
      Subgroup.commutator_le_left _ _
    exact h1
  let π : (↥E ⧸ U) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    QuotientGroup.lift U α (fun u hu => MonoidHom.mem_ker.1 (hαk ▸ hUQ hu))
  have hπmk : ∀ e : ↥E, π (QuotientGroup.mk e) = α e := fun e => rfl
  have hπs : Function.Surjective π := by
    intro A
    obtain ⟨e, he⟩ := hαs A
    exact ⟨QuotientGroup.mk e, by rw [hπmk, he]⟩
  have hπk : ∀ x : ↥E ⧸ U, x ∈ π.ker → ∃ q ∈ CFSG.pCore 2 ↥E, x = QuotientGroup.mk q := by
    intro x hx
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨e, ?_, rfl⟩
    rw [← hαk, MonoidHom.mem_ker, ← hπmk]
    exact hx
  have hcen : π.ker ≤ Subgroup.center (↥E ⧸ U) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := hπk x hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : ⁅q⁻¹, e⁻¹⁆ ∈ U :=
      Subgroup.commutator_mem_commutator ((CFSG.pCore 2 ↥E).inv_mem hq) (Subgroup.mem_top _)
    have h2 : (e * q)⁻¹ * (q * e) = ⁅q⁻¹, e⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact h1
  have hp2 : IsPGroup 2 ↥π.ker := by
    intro x
    obtain ⟨q, hq, hxq⟩ := hπk x.1 x.2
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥E)) ⟨q, hq⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : q ^ 2 ^ k = 1 := congrArg Subtype.val hk
    show (x.1) ^ 2 ^ k = 1
    rw [hxq, ← QuotientGroup.mk_pow, hk']
    rfl
  have hperfQ : Group.IsPerfect (↥E ⧸ U) := inferInstance
  have hker := hmult n hn (↥E ⧸ U) π hπs hcen hp2 hperfQ
  have hQU : CFSG.pCore 2 ↥E ≤ U := by
    intro q hq
    have h1 : (QuotientGroup.mk q : ↥E ⧸ U) ∈ π.ker := by
      rw [MonoidHom.mem_ker, hπmk, ← MonoidHom.mem_ker, hαk]
      exact hq
    rw [hker, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff q).1 h1
  have hQeq : (CFSG.pCore 2 ↥E).map E.subtype = pCoreOf 2 E := by
    rw [← CFSG.CGT.PushingUpLit.oTwoIn_eq_map, oTwoIn_eq_pCoreOf]
  rw [← map_shortU_eq_commutator E, ← hQeq]
  congr 1
  exact le_antisymm hUQ hQU

end CFSG.CGT.PushingUpLit.BHS6
