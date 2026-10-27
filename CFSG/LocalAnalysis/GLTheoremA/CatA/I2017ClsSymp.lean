module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsInn
import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusLinearTransport
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxSymplectic
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore
import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017Cls

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

private theorem card_alt_eight_sp : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
  rw [Nat.card_perm, Nat.card_fin] at h
  have h8 : (8 : ℕ).factorial = 40320 := by decide
  omega

private theorem le_six_of_two_pow_dvd_sp {t : ℕ} (h : 2 ^ t ∣ 20160) : t ≤ 6 := by
  rw [show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num] at h
  have h64 : 2 ^ t ∣ 2 ^ 6 :=
    Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left t (Nat.coprime_two_left.mpr (by norm_num : Odd 315))) h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h64

private theorem ker_id_le_center (X : Type*) [Group X] :
    (MonoidHom.id X).ker ≤ Subgroup.center X := fun g hg => by
  rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hg
  rw [hg]
  exact Subgroup.one_mem _

private theorem two_pow_dvd_card_centerQuotient_su_sp {E : Type} [Field E] [Finite E] {m f : ℕ}
    (hm : 3 ≤ m) (hf : 1 ≤ f) (hne : (m, 2 ^ f) ≠ (3, 2)) (hE : Nat.card E = (2 ^ f) ^ 2)
    {T : Type*} [Group T] (g : ↥(StatedSU m (2 ^ f) E) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(StatedSU m (2 ^ f) E))
    (hperf : commutator ↥(StatedSU m (2 ^ f) E) = ⊤) :
    2 ^ (f * (m * (m - 1) / 2)) ∣ Nat.card (T ⧸ Subgroup.center T) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := f) hE
  have hUF : UnitaryFieldData 2 f E := CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hE hf
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := E) (p := 2)
    (f := f) hE hm hne
  have hZ : Nat.card (Subgroup.center ↥(StatedSU m (2 ^ f) E)) = Nat.gcd m (2 ^ f + 1) := by
    rw [hQ.2]
    exact CFSG.LocalAnalysis.RankFourTheoremC.card_scalars_statedSU (K := E) (r := 2)
      (f := f) hE (by omega)
  have hZodd : Odd (Nat.card (Subgroup.center ↥(StatedSU m (2 ^ f) E))) := by
    rw [hZ]
    refine Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right _ _)
    obtain ⟨k, hk⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ k, by ring⟩
  have hsplit := KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  have hdvd : 2 ^ (f * (m * (m - 1) / 2)) ∣
      Nat.card (T ⧸ Subgroup.center T) * Nat.card (Subgroup.center ↥(StatedSU m (2 ^ f) E)) := by
    rw [← hsplit, KD264Lie.card_statedSU_eq_nat hUF (by omega), ← pow_mul]
    exact dvd_mul_right _ _
  exact Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hZodd)) hdvd

private theorem sl_not_alt_eight {E : Type} [Field E] [Fintype E] {m e : ℕ} (hm : 2 ≤ m)
    (he : 2 ≤ e) (hE : Fintype.card E = 2 ^ e) {X : Type} [Group X]
    (g : Matrix.SpecialLinearGroup (Fin m) E →* X) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E))
    (eX : X ⧸ Subgroup.center X ≃* ↥(alternatingGroup (Fin 8))) : False := by
  classical
  have h4 : 4 ≤ Fintype.card E := by
    rw [hE]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hperf := (slFactorFacts_holds E m hm (fun _ => h4)).perfect
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) E) := Group.isPerfect_def.mpr hperf
  have hE' : Nat.card E = 2 ^ e := by rw [Nat.card_eq_fintype_card, hE]
  have hcardQ : Nat.card (X ⧸ Subgroup.center X) = 20160 := by
    rw [Nat.card_congr eX.toEquiv, card_alt_eight_sp]
  have h2 := KD264Lie.pow_dvd_card_centerQuotient_of_surjective_specialLinear (by omega)
    (by omega) hE' g hg hker hperf
  rw [hcardQ] at h2
  have hb := le_six_of_two_pow_dvd_sp h2
  have hm3 : m ≤ 3 := by
    by_contra hc
    have h12 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h6 : 6 ≤ m * (m - 1) / 2 := by omega
    have h12' : 2 * 6 ≤ e * (m * (m - 1) / 2) := Nat.mul_le_mul he h6
    omega
  rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl
  ·
    norm_num at hb
    have hsplit :=
      KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
    rw [hcardQ, LinearFlag.card_SL_eq (K := E) (n := 2) (by norm_num), hE'] at hsplit
    have hz : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) ≤ 2 := by
      rw [Nat.card_congr
        (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv]
      exact (card_rootsOfUnity (k := Fintype.card (Fin 2)) (R := E)).trans_eq
        (Fintype.card_fin 2)
    generalize Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) = z at hsplit hz
    interval_cases e <;> norm_num [Finset.Icc_self] at hsplit <;> omega
  ·
    have he2 : e = 2 := by
      norm_num at hb
      omega
    subst he2
    exact CFSG.HardMathSupport.Solomon.Coordinator.false_of_projectiveSL_alt_eight (F := E)
      (by rw [hE']; norm_num)
      (((QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 3 E)).trans
        (CFSG.ComponentClassification.PerfectCentralQuotient.equivalence g hg hker)).trans eX)

private theorem su_not_alt_eight {E : Type} [Field E] [Fintype E] {m Q f : ℕ}
    (hQ : Q = 2 ^ f) (hm : 3 ≤ m) (hf : 1 ≤ f) (hne : (m, Q) ≠ (3, 2))
    (hE : Fintype.card E = Q ^ 2) {X : Type} [Group X] (g : ↥(StatedSU m Q E) →* X)
    (hg : Function.Surjective g) (hker : g.ker ≤ Subgroup.center ↥(StatedSU m Q E))
    (eX : X ⧸ Subgroup.center X ≃* ↥(alternatingGroup (Fin 8))) : False := by
  classical
  subst hQ
  have hperf := (suFactorFacts_holds E m (2 ^ f) hE hm hne).perfect
  have hE' : Nat.card E = (2 ^ f) ^ 2 := by rw [Nat.card_eq_fintype_card, hE]
  have hcardQ : Nat.card (X ⧸ Subgroup.center X) = 20160 := by
    rw [Nat.card_congr eX.toEquiv, card_alt_eight_sp]
  have h2 := two_pow_dvd_card_centerQuotient_su_sp hm hf hne hE' g hg hker hperf
  rw [hcardQ] at h2
  have hb := le_six_of_two_pow_dvd_sp h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := f) hE'
  have hUF : UnitaryFieldData 2 f E := CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hE' hf
  have hsplit := KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  rw [hcardQ] at hsplit
  generalize Nat.card (Subgroup.center ↥(StatedSU m (2 ^ f) E)) = z at hsplit
  have hm4 : m ≤ 4 := by
    by_contra hc
    have h20 : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h10 : 10 ≤ m * (m - 1) / 2 := by omega
    have h10' : 1 * 10 ≤ f * (m * (m - 1) / 2) := Nat.mul_le_mul hf h10
    omega
  rcases (show m = 3 ∨ m = 4 by omega) with rfl | rfl
  ·
    have hf2 : f = 2 := by
      have hf1 : f ≠ 1 := by
        rintro rfl
        exact hne rfl
      norm_num at hb
      omega
    subst hf2
    have hval : Nat.card ↥(StatedSU 3 (2 ^ 2) E) = 62400 := by
      rw [KD264Lie.card_statedSU_eq_nat hUF (by norm_num)]
      decide
    rw [hval] at hsplit
    omega
  ·
    have hf1 : f = 1 := by
      norm_num at hb
      omega
    subst hf1
    have hval : Nat.card ↥(StatedSU 4 (2 ^ 1) E) = 25920 := by
      rw [KD264Lie.card_statedSU_eq_nat hUF (by norm_num)]
      decide
    rw [hval] at hsplit
    omega

section Generic

variable {G : Type*} [Group G]

private theorem commutator_le_self_sp (A : Subgroup G) : ⁅A, A⁆ ≤ A := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

private theorem map_commutator_mulEquiv_sp {A B : Type*} [Group A] [Group B] (φ : A ≃* B) :
    (commutator A).map φ.toMonoidHom = commutator B := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective]

private theorem range_eq_commutator_of_perfect_sp {X B Ab : Type*} [Group X] [Group B]
    [CommGroup Ab] (θ : X →* B) (hX : commutator X = ⊤) (D : B →* Ab) (hD : D.ker ≤ θ.range) :
    θ.range = commutator B := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← hX, _root_.commutator_def, Subgroup.map_commutator,
      _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · refine le_trans ?_ hD
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

private theorem range_comp_eq_commutator_sp {A : Subgroup G} {B X : Type*} [Group B] [Group X]
    (φ : A ≃* B) (θ : X →* B) (hθ : θ.range = commutator B) :
    (A.subtype.comp (φ.symm.toMonoidHom.comp θ)).range = ⁅A, A⁆ := by
  have h1 : (φ.symm.toMonoidHom.comp θ).range = commutator ↥A := by
    rw [MonoidHom.range_comp, hθ]
    exact map_commutator_mulEquiv_sp φ.symm
  rw [MonoidHom.range_comp, h1]
  exact Subgroup.map_subtype_commutator A

private theorem not_isSolvable_of_isQuasisimple_commutator_sp {H : Subgroup G}
    (hQ : CFSG.IsQuasisimple ↥⁅H, H⁆) : ¬ Group.IsSolvable ↥H := by
  intro hs
  haveI := hs
  have hle : ⁅H, H⁆ ≤ H := commutator_le_self_sp H
  haveI : Group.IsSolvable ↥⁅H, H⁆ :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  haveI : Group.IsPerfect ↥⁅H, H⁆ := hQ.1
  haveI : Nontrivial ↥⁅H, H⁆ := by
    obtain ⟨a, b, hab⟩ := hQ.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [h])⟩
  exact Group.IsPerfect.not_isSolvable ↥⁅H, H⁆ inferInstance

private theorem isSolvable_gl_of_le_one_sp {E : Type*} [Field E] {m : ℕ} (hm : m ≤ 1) :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) E) := by
  refine Group.isSolvable_of_comm fun a b => Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · exact Matrix.ext fun i => i.elim0
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one,
      Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact mul_comm _ _

end Generic

private abbrev PerfNotA8 (X : Type) (inst : Group X) : Prop :=
  letI := inst
  commutator X = ⊤ ∧ IsEmpty ((X ⧸ Subgroup.center X) ≃* ↥(alternatingGroup (Fin 8)))

variable {r : ℕ} {K : Type} [Field K]

private theorem isLieFactorOf_of_card_lt [Finite K] {A : Subgroup (StatedSp r K)}
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) (hA : Nat.card A < 20160) :
    IsLieFactorOf PerfNotA8 ⁅A, A⁆ := by
  refine ⟨↥⁅A, A⁆, inferInstance, inferInstance, ⁅A, A⁆.subtype, Subtype.val_injective,
    Subgroup.range_subtype _, Group.isPerfect_def.mp hQ.1, ⟨fun e => ?_⟩⟩
  have h1 := Nat.card_congr e.toEquiv
  rw [card_alt_eight_sp] at h1
  have h2 : Nat.card (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) ≤ Nat.card ↥⁅A, A⁆ :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have h3 : Nat.card ↥⁅A, A⁆ ≤ Nat.card A := Subgroup.card_le_of_le (commutator_le_self_sp A)
  omega

private theorem sp_good [Finite K] (hK : Nat.card K = 2) {A : Subgroup (StatedSp r K)} {s : ℕ}
    (φ : A ≃* StatedSp s K) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    IsLieFactorOf PerfNotA8 ⁅A, A⁆ := by
  classical
  haveI := Fintype.ofFinite K
  have hcardSp := SymplecticFlag.card_statedSp (K := K) s
  rw [hK] at hcardSp
  by_cases hs : s ≤ 2
  · refine isLieFactorOf_of_card_lt hQ ?_
    rw [Nat.card_congr φ.toEquiv, hcardSp]
    interval_cases s <;> decide
  · have hs3 : 3 ≤ s := by omega
    have hcK : Fintype.card K = 2 := by rw [Fintype.card_eq_nat_card, hK]
    have hne : (s, Fintype.card K) ≠ (2, 2) := by
      rw [hcK]
      intro h
      have h1 := congrArg Prod.fst h
      simp only at h1
      omega
    have hX := spFactorFacts_holds K s (by omega) hne
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hcK]; norm_num)
    have hZ : Subgroup.center ↥(StatedSp s K) = ⊥ := by
      rw [CFSG.LieType.Universal.Symplectic.center_eq,
        CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
    have hθ : (MonoidHom.id ↥(StatedSp s K)).range = commutator ↥(StatedSp s K) := by
      rw [MonoidHom.range_eq_top.2 Function.surjective_id, hX.perfect]
    refine ⟨↥(StatedSp s K), inferInstance, inferInstance,
      A.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.id _)),
      Subtype.val_injective.comp (φ.symm.injective.comp Function.injective_id),
      range_comp_eq_commutator_sp φ _ hθ, hX.perfect, ⟨fun e => ?_⟩⟩
    have hsplit := KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hX.perfect
      (MonoidHom.id _) Function.surjective_id (ker_id_le_center _)
    rw [Nat.card_congr e.toEquiv, card_alt_eight_sp, hZ, Subgroup.card_bot, mul_one,
      hcardSp] at hsplit
    have hdvd : 2 ^ (s ^ 2) ∣ 20160 := ⟨_, hsplit.symm⟩
    have h6 := le_six_of_two_pow_dvd_sp hdvd
    have h9 : 3 ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hs3 2
    exact absurd (h9.trans h6) (by norm_num)

private theorem gl_good {E : Type} [Field E] [Fintype E] {e : ℕ} (he : 2 ≤ e)
    (hE : Fintype.card E = 2 ^ e) {m : ℕ} {A : Subgroup (StatedSp r K)}
    (φ : A ≃* Matrix.GeneralLinearGroup (Fin m) E) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    IsLieFactorOf PerfNotA8 ⁅A, A⁆ := by
  classical
  have hm : 2 ≤ m := by
    by_contra hlt
    haveI := isSolvable_gl_of_le_one_sp (E := E) (not_le.1 hlt |> Nat.lt_succ_iff.1)
    exact not_isSolvable_of_isQuasisimple_commutator_sp hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  have h4 : 4 ≤ Fintype.card E := by
    rw [hE]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hX := slFactorFacts_holds E m hm (fun _ => h4)
  let θ : Matrix.SpecialLinearGroup (Fin m) E →* Matrix.GeneralLinearGroup (Fin m) E :=
    Matrix.SpecialLinearGroup.toGL
  have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin m) E) := by
    refine range_eq_commutator_of_perfect_sp θ hX.perfect
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) E →* Eˣ) fun g hg => ?_
    rw [MonoidHom.mem_ker] at hg
    have hdet : (g : Matrix (Fin m) (Fin m) E).det = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  exact ⟨Matrix.SpecialLinearGroup (Fin m) E, inferInstance, inferInstance,
    A.subtype.comp (φ.symm.toMonoidHom.comp θ),
    Subtype.val_injective.comp (φ.symm.injective.comp Matrix.SpecialLinearGroup.toGL_injective),
    range_comp_eq_commutator_sp φ θ hθ, hX.perfect,
    ⟨fun e' => sl_not_alt_eight hm he hE (MonoidHom.id _) Function.surjective_id
      (ker_id_le_center _) e'⟩⟩

private theorem exists_range_of_special_equiv_sp {ℓ g : ℕ} {G : Type*} [Group G] {E : Type}
    [Field E] (hE : UnitaryFieldData ℓ g E) {V : Type*} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (hm1 : 1 ≤ Module.finrank E V) {A : Subgroup G}
    (φ : A ≃* sesqUnitaryGroup Hf) {X : Type} [Group X] (hXp : commutator X = ⊤)
    (e : ↥(sesqSpecialUnitaryGroup Hf) ≃* X) :
    ∃ ψ : X →* G, Function.Injective ψ ∧ ψ.range = ⁅A, A⁆ := by
  obtain ⟨-, -, -, -, hker, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl hm1
  let θ : X →* ↥(sesqUnitaryGroup Hf) :=
    (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf)).comp e.symm.toMonoidHom
  have hθi : Function.Injective θ :=
    (Subgroup.inclusion_injective (sesqSpecialUnitaryGroup_le Hf)).comp e.symm.injective
  have hθ : θ.range = commutator ↥(sesqUnitaryGroup Hf) := by
    refine range_eq_commutator_of_perfect_sp θ hXp (CFSG.LinearGroups.unitaryDet Hf)
      fun u hu => ?_
    rw [hker] at hu
    exact ⟨e ⟨u, hu⟩, Subtype.ext (by simp [θ])⟩
  exact ⟨A.subtype.comp (φ.symm.toMonoidHom.comp θ),
    Subtype.val_injective.comp (φ.symm.injective.comp hθi), range_comp_eq_commutator_sp φ θ hθ⟩

open CFSG.RankThree.CentralLift CFSG.RankThree.Classical CFSG.ClassicalGroups.UnitaryFlag in
private theorem gu_good [Finite K] {g : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 g E)
    {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) {m : ℕ}
    (b : Module.Basis (Fin m) E V) (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0)
    {A : Subgroup (StatedSp r K)} (φ : A ≃* sesqUnitaryGroup Hf)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : IsLieFactorOf PerfNotA8 ⁅A, A⁆ := by
  classical
  have hfin : Module.finrank E V = m := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  haveI := hE.finite
  haveI := Fintype.ofFinite E
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := hE.charP
  have hg : 1 ≤ g := hE.one_le
  have hEcard : Fintype.card E = (2 ^ g) ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_eq_sq
  haveI : Finite ↥hE.fixedField := inferInstance
  haveI : Fintype ↥hE.fixedField := Fintype.ofFinite _
  have hFcard : Fintype.card ↥hE.fixedField = 2 ^ g := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_fixedField
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hsolv : Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
      refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
      have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := V)
        (by omega) ((a : LinearMap.GeneralLinearGroup E V) : Module.End E V)
        ((b : LinearMap.GeneralLinearGroup E V) : Module.End E V)).eq
      simpa [Subgroup.coe_mul, Units.val_mul] using this
    exact not_isSolvable_of_isQuasisimple_commutator_sp hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  by_cases hsmall : m ≤ 3 ∧ 2 ^ g = 2
  ·
    obtain ⟨hm3, hq⟩ := hsmall
    obtain ⟨hcard, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl hfin (by omega)
    have hA : Nat.card A < 20160 := by
      rw [Nat.card_congr φ.toEquiv]
      rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl
      · rw [hq] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
        have h18 : Nat.card ↥(sesqUnitaryGroup Hf) = 18 := by exact_mod_cast hcard.trans e
        omega
      · rw [hq] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
        have h648 : Nat.card ↥(sesqUnitaryGroup Hf) = 648 := by exact_mod_cast hcard.trans e
        omega
    exact isLieFactorOf_of_card_lt hQ hA
  · rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    ·
      have hg2 : 2 ≤ g := by
        by_contra hlt
        apply hsmall
        refine ⟨by omega, ?_⟩
        rw [show g = 1 by omega]
        norm_num
      have hq4 : 4 ≤ 2 ^ g := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hfin
      have hX := slFactorFacts_holds ↥hE.fixedField 2 le_rfl (fun _ => by rw [hFcard]; exact hq4)
      obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv_sp hE hHf hHfl (by omega) φ
        hX.perfect e
      exact ⟨Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField, inferInstance, inferInstance, ψ,
        hψi, hψ, hX.perfect, ⟨fun e' => sl_not_alt_eight le_rfl hg2 hFcard (MonoidHom.id _)
          Function.surjective_id (ker_id_le_center _) e'⟩⟩
    ·
      have hnq : (m, 2 ^ g) ≠ (3, 2) := by
        intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only at h1 h2
        exact hsmall ⟨by omega, h2⟩
      have hX := suFactorFacts_holds E m (2 ^ g) hEcard hm3 hnq
      obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
        (G := (1 : Matrix (Fin m) (Fin m) E)) (fun i j => by rw [hb i j, Matrix.one_apply])
      have hSUeq : StatedSU m (2 ^ g) E = gramSU hE (1 : Matrix (Fin m) (Fin m) E) :=
        unitarySU_eq_gramSU hE m
      let e' : ↥(sesqSpecialUnitaryGroup Hf) ≃* ↥(StatedSU m (2 ^ g) E) :=
        e.trans (MulEquiv.subgroupCongr hSUeq.symm)
      obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv_sp hE hHf hHfl (by omega) φ
        hX.perfect e'
      exact ⟨↥(StatedSU m (2 ^ g) E), inferInstance, inferInstance, ψ, hψi, hψ, hX.perfect,
        ⟨fun e'' => su_not_alt_eight rfl hm3 hg hnq hEcard (MonoidHom.id _)
          Function.surjective_id (ker_id_le_center _) e''⟩⟩

section Blocks

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

private theorem orbit_good [Finite K] (hK : Nat.card K = 2) {x : StatedSp r K}
    {a : StatedProj (StatedSp r K)} (blocks : SpPrimaryBlocks 2 1 3 x a)
    (h : primaryFactors (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆) :
    IsLieFactorOf PerfNotA8 ⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆ := by
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO] at hQ ⊢
    by_cases h1 : (h : K[X]) = X - 1
    · obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      obtain ⟨s, -, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      exact sp_good hK (φ.trans e) hQ
    · obtain ⟨d, -, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, -⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      exact gu_good hE hHf hHfl e he φ hQ
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ⟩ := hP.matrixFactor
    haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    haveI := Fintype.ofFinite (AdjoinRoot (h : K[X]))
    have hdeg : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    have hEc : Fintype.card (AdjoinRoot (h : K[X])) = 2 ^ (h : K[X]).natDegree := by
      rw [Fintype.card_eq_nat_card, hP.card_field, pow_one]
    have he2 : 2 ≤ (h : K[X]).natDegree := by
      by_contra hlt
      have h1 : (h : K[X]).natDegree = 1 := by omega
      have h3 := hP.dvd
      rw [h1] at h3
      norm_num at h3
    exact gl_good he2 hEc φ hQ

private theorem false_of_component_conj_sp [Finite K] (hK : Nat.card K = 2) (hr : 1 ≤ r)
    (x : StatedSp r K) (hx : x ^ 3 = 1) (hx1 : SymplecticFlag.proj r K x ≠ 1)
    (J : Subgroup (StatedProj (StatedSp r K)))
    (hJ : IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (MulAut.conj (SymplecticFlag.proj r K x))))
    (eJ : ↥J ⧸ Subgroup.center ↥J ≃* ↥(alternatingGroup (Fin 8))) : False := by
  classical
  haveI := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [Fintype.card_eq_nat_card, hK2])
  have ha : orderOf (SymplecticFlag.proj r K x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hx, map_one]) hx1
  have hxp : orderOf x = 3 := orderOf_eq_prime hx (fun h => hx1 (by rw [h, map_one]))
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two le_rfl hK2
    Nat.prime_three (by norm_num) (by norm_num) hr _ ha).2 x rfl hxp
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    norm_num at h
  have hsq := (altPrimaryData_spLin (p := 3) hpK hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  obtain ⟨X, inst, -, ⟨hXp, hXe⟩, f, hf, hfk⟩ :=
    components_of_orbit_family_lieFactor (P := PerfNotA8) x
      (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
      (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
      hjoin (fun O => CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported
        (by norm_num) (by norm_num) hsq blocks O)
      (fun O hQ => by
        obtain ⟨O, h, hh, rfl⟩ := O
        exact orbit_good hK blocks ⟨h, hh⟩ hQ) J hJ
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hXp f hf hfk
  exact hXe.false (e.trans eJ)

end Blocks

theorem sympTwoNoA8_holds : SympTwoNoA8 := by
  intro n d hd _ _ β hmem hβ3 hβ1 hA8
  classical
  have hS : KD264Lie.isSymplecticIdx d.1 := by
    rw [hd]
    exact Or.inr rfl
  obtain ⟨r, hr, hne, hcard, ⟨eP⟩⟩ := KD264Lie.exists_mulEquiv_statedProj_of_isSymplecticIdx hS
  haveI : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  have hfs : KD264Lie.fieldSize d.1 = 2 := by
    rw [hd]
    show gfTwoPP.card = 2
    rw [TauCeti.PrimePower.card_def]
    rfl
  have hK : Nat.card ↥d.fixedField = 2 := hcard.trans hfs
  have hr2 : r ≠ 2 := fun h => hne ⟨h, hfs⟩
  let θ : (TauCeti.CFSGIndex.lie d).Group ≃* StatedProj (StatedSp r ↥d.fixedField) := eP.symm
  let β' : MulAut (StatedProj (StatedSp r ↥d.fixedField)) := θ.symm.trans (β.trans θ)
  have hβ'mem : β' ∈ innAutDerived (StatedProj (StatedSp r ↥d.fixedField)) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ).2 hmem
  have hβ'3 : β' ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr θ) β 3
    rw [hβ3, map_one] at h3
    exact h3.symm
  have hβ'1 : β' ≠ 1 := by
    intro h1
    apply hβ1
    exact (MulAut.congr θ).injective (by rw [map_one]; exact h1)
  obtain ⟨t, ht⟩ := KD264Lie.mem_inner_of_mem_innAutDerived_statedSp (f := 1) Nat.prime_three
    (by norm_num) Nat.prime_two le_rfl (by rw [hK]; norm_num) hr (fun h => hr2 h.1) hβ'mem hβ'3
  have hZ : Subgroup.center (StatedProj (StatedSp r ↥d.fixedField)) = ⊥ := by
    obtain ⟨hsimple, hperf⟩ :=
      CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := ↥d.fixedField) hr
        (fun h => hr2 h.1)
    haveI := hsimple
    have hnc : ∃ u v : StatedProj (StatedSp r ↥d.fixedField), u * v ≠ v * u := by
      by_contra h
      push Not at h
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun u v => h u v⟩⟩
    exact CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc
  have ht3 : t ^ 3 = 1 :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ (by rw [map_pow, ht, hβ'3, map_one])
  obtain ⟨x, hx, hx3⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
      (r := r) (K := ↥d.fixedField) (by omega) Nat.prime_three (by norm_num) ht3
  have hβeq : β' = MulAut.conj (SymplecticFlag.proj r ↥d.fixedField x) := by rw [← ht, ← hx]
  have hx1 : SymplecticFlag.proj r ↥d.fixedField x ≠ 1 := by
    intro h1
    apply hβ'1
    rw [hβeq, h1, map_one]
  obtain ⟨J, -, hJc, ⟨eJ⟩⟩ := hA8
  have hfix := CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup θ β
  have hJ' : IsComponentOf (J.map θ.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (MulAut.conj (SymplecticFlag.proj r ↥d.fixedField x))) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map θ hJc
    rw [← hβeq]
    exact hfix ▸ h1
  have eJK : ↥J ≃* ↥(J.map θ.toMonoidHom) := J.equivMapOfInjective θ.toMonoidHom θ.injective
  have eJ' : ↥(J.map θ.toMonoidHom) ⧸ Subgroup.center ↥(J.map θ.toMonoidHom) ≃*
      ↥(alternatingGroup (Fin 8)) :=
    (QuotientGroup.congr _ _ eJK (Subgroup.map_center_eq eJK)).symm.trans eJ
  exact false_of_component_conj_sp hK (by omega) x hx3 hx1 _ hJ' eJ'

end CFSG.LocalAnalysis.GLTheoremA.I2017Cls

end
