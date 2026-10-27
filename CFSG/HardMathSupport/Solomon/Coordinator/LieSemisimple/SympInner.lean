module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.CentralQuotient
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section DerivedJoin

variable {G : Type*} [Group G]

private def dsub (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => ⁅dsub H n, dsub H n⁆

private theorem commutator_le_self' (K : Subgroup G) : ⁅K, K⁆ ≤ K := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

private theorem dsub_anti (H : Subgroup G) : Antitone (dsub H) :=
  antitone_nat_of_succ_le fun n => commutator_le_self' (dsub H n)

private theorem dsub_le_self (H : Subgroup G) (n : ℕ) : dsub H n ≤ H := dsub_anti H (Nat.zero_le n)

private theorem map_subtype_derivedSeries (H : Subgroup G) (n : ℕ) :
    (derivedSeries ↥H n).map H.subtype = dsub H n := by
  induction n with
  | zero => rw [derivedSeries_zero, dsub, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih => rw [derivedSeries_succ, dsub, Subgroup.map_commutator, ih]

private theorem dsub_iSup {ι : Type*} (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (n : ℕ) :
    dsub (⨆ i, A i) n = ⨆ i, dsub (A i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dsub, ih]
    exact CFSG.RankThree.PartOne.KCUnitary.commutator_iSup_commuting (fun i => dsub (A i) n)
      (fun i j hij a ha b hb => hc i j hij a (dsub_le_self _ n ha) b (dsub_le_self _ n hb))

private theorem isSolvable_quotient_of_orbit_family {ι : Type*} [Finite ι] (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (P : ι → Prop)
    (hP : ∀ i, ¬ P i → Group.IsSolvable ↥(A i)) {C N : Subgroup G} (hCA : ⨆ i, A i = C)
    (hN : ∀ i, P i → ⁅A i, A i⁆ ≤ N) [(N.subgroupOf C).Normal] :
    Group.IsSolvable (↥C ⧸ N.subgroupOf C) := by
  classical
  subst hCA
  have hk : ∀ i, ∃ k : ℕ, ¬ P i → dsub (A i) k = ⊥ := by
    intro i
    by_cases hi : P i
    · exact ⟨0, fun h => absurd hi h⟩
    · obtain ⟨k, hk⟩ := (hP i hi).solvable
      refine ⟨k, fun _ => ?_⟩
      rw [← map_subtype_derivedSeries, hk, Subgroup.map_bot]
  choose k hk using hk
  cases nonempty_fintype ι
  refine ⟨⟨Finset.univ.sup k + 1, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (N.subgroupOf (⨆ i, A i))),
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', Subgroup.subgroupOf,
    ← Subgroup.map_le_iff_le_comap, map_subtype_derivedSeries, dsub_iSup A hc]
  refine iSup_le fun i => ?_
  by_cases hi : P i
  · exact (dsub_anti (A i) (Nat.le_add_left 1 _)).trans (hN i hi)
  · have h1 : dsub (A i) (Finset.univ.sup k + 1) ≤ dsub (A i) (k i) :=
      dsub_anti (A i) ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))
    exact (h1.trans (hk i hi).le).trans bot_le

end DerivedJoin

section Assembly

variable {X T : Type*} [Group X] [Group T]

private theorem fixSubgroup_conj_eq_centralizer (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem conj_mem_iSup' {ι : Type*} {C : Subgroup X} (F : ι → Subgroup X)
    (hF : ∀ i, ∀ c ∈ C, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i) :
    ∀ c ∈ C, ∀ g ∈ ⨆ i, F i, c * g * c⁻¹ ∈ ⨆ i, F i := by
  intro c hc g hg
  refine Subgroup.iSup_induction F (C := fun x => c * x * c⁻¹ ∈ ⨆ i, F i) hg
    (fun i x hx => Subgroup.mem_iSup_of_mem i (hF i c hc x hx)) (by simp) fun x y hx hy => ?_
  have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hx hy

theorem perfectInLayer_conj_of_orbit_family (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (x : X) {ι : Type*} [Finite ι] (A : ι → Subgroup X)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b)
    (hjoin : ⨆ i, A i = Subgroup.centralizer ({x} : Set X))
    (htame : ∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i)) :
    PerfectInLayer (MulAut.conj (π x)) := by
  classical
  have hfix : ⨆ i, A i = fixSubgroup (MulAut.conj x) := by
    rw [hjoin, fixSubgroup_conj_eq_centralizer]
  have hnormA : ∀ i, ∀ c ∈ ⨆ j, A j, ∀ g ∈ A i, c * g * c⁻¹ ∈ A i := by
    intro i c hc'
    refine Subgroup.iSup_induction A (C := fun c => ∀ g ∈ A i, c * g * c⁻¹ ∈ A i) hc' ?_ ?_ ?_
    · intro j y hy g hg
      by_cases hji : j = i
      · subst hji
        exact (A j).mul_mem ((A j).mul_mem hy hg) ((A j).inv_mem hy)
      · rw [(hc j i hji y hy g hg).eq, mul_inv_cancel_right]
        exact hg
    · intro g hg
      simpa using hg
    · intro u v hu hv g hg
      have e : u * v * g * (u * v)⁻¹ = u * (v * g * v⁻¹) * u⁻¹ := by group
      rw [e]
      exact hu _ (hv g hg)
  have hnormD : ∀ i, ∀ c ∈ ⨆ j, A j, ∀ g ∈ ⁅A i, A i⁆, c * g * c⁻¹ ∈ ⁅A i, A i⁆ := by
    intro i c hc' g hg
    have hmap : (A i).map (MulAut.conj c).toMonoidHom ≤ A i := by
      rintro _ ⟨y, hy, rfl⟩
      exact hnormA i c hc' y hy
    have h1 : (⁅A i, A i⁆).map (MulAut.conj c).toMonoidHom ≤ ⁅A i, A i⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmap hmap
    exact h1 ⟨g, hg, rfl⟩
  let F : {i : ι // CFSG.IsQuasisimple ↥⁅A i, A i⁆} → Subgroup X := fun i => ⁅A i.1, A i.1⁆
  have hFn : ∀ i, ∀ c ∈ fixSubgroup (MulAut.conj x), ∀ g ∈ F i, c * g * c⁻¹ ∈ F i :=
    fun i c hc' g hg => hnormD i.1 c (hfix ▸ hc') g hg
  have hNn := conj_mem_iSup' (C := fixSubgroup (MulAut.conj x)) F hFn
  haveI : ((⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn
  haveI hsol : Group.IsSolvable (↥(fixSubgroup (MulAut.conj x)) ⧸
      (⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x))) := by
    refine isSolvable_quotient_of_orbit_family A hc (fun i => CFSG.IsQuasisimple ↥⁅A i, A i⁆)
      (fun i hi => (htame i).resolve_left hi) hfix fun i hi => ?_
    exact le_iSup F ⟨i, hi⟩
  refine perfectInLayer_of_centralQuotient π hπ hker (MulAut.conj x) (MulAut.conj (π x))
    (fun g => by simp [MulAut.conj_apply]) F
    (fun i => (commutator_le_self' _).trans ((le_iSup A i.1).trans hfix.le)) hFn (fun i => i.2)
    (QuotientGroup.mk' ((⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x)))) fun g hg => ?_
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hg

end Assembly

section Tame

private def IsTame (G : Type*) [Group G] : Prop :=
  CFSG.IsQuasisimple ↥(commutator G) ∨ Group.IsSolvable G

private theorem isTame_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (h : IsTame H) :
    IsTame G := by
  rcases h with hq | hs
  · left
    have hmap : (commutator G).map e.toMonoidHom = commutator H := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.surjective]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (((commutator G).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).symm hq
  · right
    haveI := hs
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem isTame_of_isQuasisimple {G : Type*} [Group G] (h : CFSG.IsQuasisimple G) :
    IsTame G := by
  left
  have h1 : commutator G = ⊤ := Group.isPerfect_def.mp h.1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((MulEquiv.subgroupCongr h1).trans Subgroup.topEquiv).symm h

private theorem isTame_of_ker {G A : Type*} [Group G] [CommGroup A] (D : G →* A)
    (hq : CFSG.IsQuasisimple ↥D.ker) : IsTame G := by
  left
  have hle : commutator G ≤ D.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hge : D.ker ≤ commutator G := by
    have h1 := Subgroup.isPerfect_iff.mp hq.1
    calc D.ker = ⁅D.ker, D.ker⁆ := h1.symm
      _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator G := (_root_.commutator_def G).symm
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr (le_antisymm hge hle)) hq

private theorem isQuasisimple_commutator_subgroup_iff {X : Type*} [Group X] (H : Subgroup X) :
    CFSG.IsQuasisimple ↥(commutator ↥H) ↔ CFSG.IsQuasisimple ↥⁅H, H⁆ := by
  let e : ↥(commutator ↥H) ≃* ↥⁅H, H⁆ :=
    ((commutator ↥H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator H))
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm⟩

private theorem isTame_subgroup {X : Type*} [Group X] {H : Subgroup X} (h : IsTame ↥H) :
    CFSG.IsQuasisimple ↥⁅H, H⁆ ∨ Group.IsSolvable ↥H :=
  h.imp (isQuasisimple_commutator_subgroup_iff H).mp id

private theorem card_primeFactors_two_three (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 ^ a * 3 ^ b).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow ha Nat.prime_two, Nat.primeFactors_prime_pow hb Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

private theorem isSolvable_of_card_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G :=
  isSolvable_of_card_primeFactors_le_two (h ▸ card_primeFactors_two_three a b ha hb)

private theorem isTame_generalLinearGroup {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h4 : ∃ s : Finset E, s.card = 4) :
    IsTame (LinearMap.GeneralLinearGroup E W) := by
  by_cases hm : 2 ≤ Module.finrank E W
  · exact isTame_of_ker (Units.map (LinearMap.det : Module.End E W →* E))
      (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_ker_det hm (Or.inr h4))
  · right
    refine Group.isSolvable_of_comm fun a b => Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    exact (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (by omega) _ _).eq

private theorem finite_generalLinearGroup {ℓ f' : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ f' E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] : Finite (LinearMap.GeneralLinearGroup E W) := by
  have := hE.finite
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  exact Finite.of_injective _ Units.val_injective

private theorem isTame_sesqUnitaryGroup {ℓ f' : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ f' E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) : IsTame ↥(sesqUnitaryGroup Hf) := by
  have hq2 : 2 ≤ ℓ ^ f' := by
    have := Nat.one_lt_pow (by have := hE.one_le; omega : f' ≠ 0) hE.prime.one_lt
    omega
  haveI := finite_generalLinearGroup hE (W := W)
  by_cases hm : 2 ≤ Module.finrank E W
  · obtain ⟨hcard, -, -, -, hker, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
      rfl (by omega : 1 ≤ Module.finrank E W)
    by_cases hq : (Module.finrank E W = 2 → 4 ≤ ℓ ^ f') ∧ (Module.finrank E W = 3 → 3 ≤ ℓ ^ f')
    · refine isTame_of_ker (CFSG.LinearGroups.unitaryDet Hf) ?_
      rw [hker]
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm
        (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf
          hHfl hm hq)
    · right
      have hexc : (Module.finrank E W = 2 ∧ ℓ ^ f' = 2) ∨ (Module.finrank E W = 2 ∧ ℓ ^ f' = 3) ∨
          (Module.finrank E W = 3 ∧ ℓ ^ f' = 2) := by
        by_contra hn
        push_neg at hn
        obtain ⟨h1, h2, h3⟩ := hn
        refine hq ⟨fun h2' => ?_, fun h3' => ?_⟩
        · by_contra hlt
          rcases (show ℓ ^ f' = 2 ∨ ℓ ^ f' = 3 by omega) with hQ | hQ
          · exact h1 h2' hQ
          · exact h2 h2' hQ
        · by_contra hlt
          exact h3 h3' (by omega)
      rcases hexc with ⟨hm2, hQ⟩ | ⟨hm2, hQ⟩ | ⟨hm3, hQ⟩
      · rw [hm2, hQ] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
        have h18 : Nat.card ↥(sesqUnitaryGroup Hf) = 18 := by exact_mod_cast hcard.trans e
        exact isSolvable_of_card_two_three (a := 1) (b := 2) (by norm_num) (by norm_num)
          (by rw [h18]; norm_num)
      · rw [hm2, hQ] at hcard
        have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 96 := by decide +kernel
        have h96 : Nat.card ↥(sesqUnitaryGroup Hf) = 96 := by exact_mod_cast hcard.trans e
        exact isSolvable_of_card_two_three (a := 5) (b := 1) (by norm_num) (by norm_num)
          (by rw [h96]; norm_num)
      · rw [hm3, hQ] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
        have h648 : Nat.card ↥(sesqUnitaryGroup Hf) = 648 := by exact_mod_cast hcard.trans e
        exact isSolvable_of_card_two_three (a := 3) (b := 4) (by norm_num) (by norm_num)
          (by rw [h648]; norm_num)
  · right
    refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
    have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W)
      (by omega) ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
      ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
    simpa [Subgroup.coe_mul, Units.val_mul] using this

private theorem isTame_statedSp {s : ℕ} (hs : 1 ≤ s) {K : Type} [Field K] [Finite K] :
    IsTame (StatedSp s K) := by
  by_cases hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨
      (Nat.card K = 2 ∧ 3 ≤ s)
  · exact isTame_of_isQuasisimple (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs hq)
  · have hK2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
    have hK4 : Nat.card K < 4 := by
      by_contra h
      exact hq (Or.inl (Or.inr (by omega)))
    have h3 : Nat.card K = 3 → s < 2 := fun h => by
      by_contra h'
      exact hq (Or.inr (Or.inl ⟨h, by omega⟩))
    have h2 : Nat.card K = 2 → s < 3 := fun h => by
      by_contra h'
      exact hq (Or.inr (Or.inr ⟨h, by omega⟩))
    have hcard := SymplecticFlag.card_statedSp (K := K) s
    rcases (show Nat.card K = 2 ∨ Nat.card K = 3 by omega) with hK | hK
    · rcases (show s = 1 ∨ s = 2 by have := h2 hK; omega) with rfl | rfl
      · right
        refine isSolvable_of_card_two_three (a := 1) (b := 1) (by norm_num) (by norm_num) ?_
        rw [hcard, hK]
        norm_num [Finset.Icc_self]
      · left
        have hd : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
        obtain ⟨E⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hK
          (CFSG.RankThree.Classical.spForm_isAlt (r := 2) (K := K))
          (CFSG.RankThree.Classical.spForm_nondegenerate (r := 2) (K := K)) hd
        let e₀ : StatedSp 2 K ≃* sesqUnitaryGroup (CFSG.RankThree.Classical.spForm 2 K) :=
          (MonoidHom.ofInjective
            (CFSG.RankThree.Classical.spLin_injective (r := 2) (K := K))).trans
            (MulEquiv.subgroupCongr (CFSG.RankThree.Classical.range_spLin (r := 2) (K := K)))
        exact (CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour (e₀.trans E)).1
    · have hs1 : s = 1 := by have := h3 hK; omega
      subst hs1
      right
      refine isSolvable_of_card_two_three (a := 3) (b := 1) (by norm_num) (by norm_num) ?_
      rw [hcard, hK]
      norm_num [Finset.Icc_self]

end Tame

private theorem isTame_sesqUnitaryGroup_alt {K : Type} [Field K] [Finite K] {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Nontrivial W]
    {B : LinearMap.BilinForm K W} (hB : B.IsAlt) (hn : B.Nondegenerate) :
    IsTame ↥(sesqUnitaryGroup B) := by
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  have hs1 : 1 ≤ s := by
    have := Module.finrank_pos (R := K) (M := W)
    omega
  exact isTame_of_mulEquiv e (isTame_statedSp hs1)

section Blocks

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {K : Type} [Field K]

private theorem exists_finset_card_four_of_paired {ℓ f p : ℕ} (hp3 : 3 ≤ p) (hq : 2 ≤ ℓ ^ f)
    {x : StatedSp r K} {h : primaryFactors (spEnd x)} (hP : SpPairedBlock ℓ f p x h) :
    ∃ s : Finset (AdjoinRoot (h : K[X])), s.card = 4 := by
  have hdeg : 1 ≤ (h : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
  have hN : ℓ ^ f ≤ (ℓ ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
  have hle := Nat.le_of_dvd (by omega) hP.dvd
  have hcard : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
    rw [hP.card_field]
    omega
  have : Finite (AdjoinRoot (h : K[X])) := Nat.finite_of_card_ne_zero (by omega)
  exact exists_finset_card_four_of_card hcard

private theorem isTame_spSupported_of_factor [Finite K] {ℓ f p : ℕ} (hp3 : 3 ≤ p) (hq : 2 ≤ ℓ ^ f)
    {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks ℓ f p x a)
    (h : primaryFactors (spEnd x)) :
    IsTame ↥(spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO]
    by_cases h1 : (h : K[X]) = X - 1
    · obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      have : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
      exact isTame_of_mulEquiv φ (isTame_sesqUnitaryGroup_alt
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate)
    · obtain ⟨d, -, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      exact isTame_of_mulEquiv φ (isTame_sesqUnitaryGroup hE hHf hHfl)
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ, -, -⟩ := hP.factor
    exact isTame_of_mulEquiv φ
      (isTame_generalLinearGroup (exists_finset_card_four_of_paired hp3 hq hP))

private theorem isTame_spSupported [Finite K] {ℓ f p : ℕ} (hp3 : 3 ≤ p) (hq : 2 ≤ ℓ ^ f)
    {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks ℓ f p x a)
    (O : reciprocalOrbits (spEnd x)) : IsTame ↥(spSupported x (O : Set K[X])) := by
  obtain ⟨O, h, hh, rfl⟩ := O
  exact isTame_spSupported_of_factor hp3 hq hsq blocks ⟨h, hh⟩

end Blocks

section Main

open Polynomial

variable {r : ℕ} {K : Type} [Field K]

theorem perfectInLayer_conj_sp {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 1 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (x : StatedSp r K)
    (hx : x ^ p = 1) : PerfectInLayer (MulAut.conj (SymplecticFlag.proj r K x)) := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  have hq : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have : Fact p.Prime := ⟨hp⟩
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  by_cases hx1 : x = 1
  · subst hx1
    refine perfectInLayer_conj_of_orbit_family (SymplecticFlag.proj r K)
      SymplecticHigher.proj_surjective hZc 1 (fun _ : Unit => (⊤ : Subgroup (StatedSp r K)))
      (fun i j hij => absurd (Subsingleton.elim i j) hij) ?_ fun _ => ?_
    · ext g
      simp [Subgroup.mem_centralizer_iff]
    · exact isTame_subgroup (isTame_of_mulEquiv Subgroup.topEquiv (isTame_statedSp hr))
  · have hZp : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) p := by
      rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
      exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _)
        ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have ha1 : SymplecticFlag.proj r K x ≠ 1 := fun h =>
      hx1 (CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime (a := 1) (b := 0)
        (SymplecticFlag.proj r K) hZc hZp (by rwa [pow_one]) (by simp)
        (by rw [h, map_one]))
    have ha : orderOf (SymplecticFlag.proj r K x) = p :=
      orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
    have hxp : orderOf x = p := orderOf_eq_prime hx hx1
    have blocks := (CFSG.RankThree.Classical.symplectic_cross_prime_primary_centralizer_blocks hℓ
      hf hK hp hp2 hpℓ hr _ ha).2 x rfl hxp
    have hpK : (p : K) ≠ 0 := by
      have := Fintype.ofFinite K
      have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
      have : Fact ℓ.Prime := ⟨hℓ⟩
      have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) hcardK
      intro h
      rw [CharP.cast_eq_zero_iff K ℓ] at h
      exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
    have hsq := (CFSG.RankThree.Classical.altPrimaryData_spLin hpK hx).squarefree
    haveI : Finite (CFSG.RankThree.Classical.reciprocalOrbits (CFSG.RankThree.Classical.spEnd x)) :=
      (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
    obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
    exact perfectInLayer_conj_of_orbit_family (SymplecticFlag.proj r K)
      SymplecticHigher.proj_surjective hZc x
      (fun O : CFSG.RankThree.Classical.reciprocalOrbits (CFSG.RankThree.Classical.spEnd x) =>
        CFSG.RankThree.Classical.spSupported x (O : Set K[X]))
      (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
      hjoin fun O => isTame_subgroup (isTame_spSupported hp3 hq hsq blocks O)

theorem quasisimple_or_solvable_spSupported [Finite K] {ℓ f p : ℕ} (hp3 : 3 ≤ p)
    (hq : 2 ≤ ℓ ^ f) {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsq : Squarefree (minpoly K (CFSG.RankThree.Classical.spEnd x)))
    (blocks : CFSG.RankThree.Classical.SpPrimaryBlocks ℓ f p x a)
    (O : CFSG.RankThree.Classical.reciprocalOrbits (CFSG.RankThree.Classical.spEnd x)) :
    CFSG.IsQuasisimple ↥⁅CFSG.RankThree.Classical.spSupported x (O : Set K[X]),
        CFSG.RankThree.Classical.spSupported x (O : Set K[X])⁆ ∨
      Group.IsSolvable ↥(CFSG.RankThree.Classical.spSupported x (O : Set K[X])) :=
  isTame_subgroup (isTame_spSupported hp3 hq hsq blocks O)

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
