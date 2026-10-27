module

public import CFSG.GH74.Generic.BProg.B2.ShapeGenS45
public import CFSG.GH74.Generic.BProg.B2.GenLocL5Out
public import CFSG.GH74.Generic.BProg.B2.GenLocL4Lin
import CFSG.GH74.Generic.BProg.B2.GenLocDiagU
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicExc

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.LocalAnalysis.ComponentInitial

namespace ShapeGenS13

section Gen

variable {X : Type} [Group X]

@[expose] def conjOn (B : Subgroup X) : B →* MulAut X := (MulAut.conj : X →* MulAut X).comp B.subtype

theorem conjOn_apply (B : Subgroup X) (b : B) (x : X) : conjOn B b x = (b : X) * x * (b : X)⁻¹ := rfl

theorem shapeGen_of_gammaAct {B : Subgroup X}
    (hnc : ∀ E : Subgroup ↥B, pRank 2 ↥B - 1 ≤ pRank 2 ↥E → ∃ b ∈ E, (b : X) ∉ center X)
    (hγ : gammaAct (conjOn B) = ⊤) :
    (⨆ (b : X) (_ : b ∈ B ∧ b ∉ center X), centralizer ({b} : Set X)) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← hγ, gammaAct]
  refine iSup₂_le fun E hE => ?_
  obtain ⟨b, hbE, hbZ⟩ := hnc E hE
  refine le_iSup₂_of_le (b : X) ⟨b.2, hbZ⟩ ?_
  intro x hx
  have hfix := (GenLocBasic.mem_fixedIn_map (conjOn B) E x).1 hx b hbE
  rw [conjOn_apply, mul_inv_eq_iff_eq_mul] at hfix
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hfix.symm

theorem center_trivial_of_conj_injective
    (h : Function.Injective (MulAut.conj : X →* MulAut X)) :
    ∀ z : X, (∀ g : X, g * z = z * g) → z = 1 := by
  intro z hz
  apply h
  rw [map_one]
  ext g
  rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul, hz g]

theorem center_trivial_of_equiv {Y : Type} [Group Y] (e : X ≃* Y)
    (h : ∀ z : Y, (∀ g : Y, g * z = z * g) → z = 1) : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1 := by
  intro z hz
  apply e.injective
  rw [map_one]
  apply h
  intro g
  have := congrArg e (hz (e.symm g))
  simpa using this

end Gen

section S3

theorem conj_injective_projectiveSL3 {F : Type} [Field F] [Finite F] :
    Function.Injective (MulAut.conj : LinearFlag.projectiveSL 3 F →*
      MulAut (LinearFlag.projectiveSL 3 F)) := by
  let e := CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F
  have hs0 := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by norm_num)
    (Or.inl (by norm_num))).2.1
  have hs : IsSimpleGroup (LinearFlag.projectiveSL 3 F) := e.symm.isSimpleGroup
  have hp0 := CFSG.LinearGroups.linear_projective_perfect (K := F) (n := 3) (by norm_num)
    (Or.inl (by norm_num))
  have hperf : Group.IsPerfect (LinearFlag.projectiveSL 3 F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact GenLocL5Out.conj_injective_of_simple_perfect hs hperf

theorem conj_injective_statedSU3 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) :
    Function.Injective (MulAut.conj : StatedProj (StatedSU 3 (p ^ f) K) →*
      MulAut (StatedProj (StatedSU 3 (p ^ f) K))) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hq2 : p ^ f ≠ 2 := GenLocDiagU.pow_ne_two hp hp2 hK
  have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := fun h => hq2 (by simpa using congrArg Prod.snd h)
  have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 3
    (by norm_num) hnq
  have hP : Group.IsPerfect (StatedSU 3 (p ^ f) K) := by
    have h := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) (n := 3)
      (by norm_num) fun _ => CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hK hq2
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 3] at h
    exact h
  have hperf : Group.IsPerfect (StatedProj (StatedSU 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact GenLocL5Out.conj_injective_of_simple_perfect hs hperf

theorem conj_injective_of_qShape3 {J : Type} [Group J] (h : QShape3 J) :
    Function.Injective (MulAut.conj : J →* MulAut J) := by
  obtain ⟨p, f, hp, hp2, -, hm | hm⟩ := h
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hm
    let ψ : J ≃* LinearFlag.projectiveSL 3 F :=
      e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
    exact GenLocBasic.conj_injective_of_center_trivial (center_trivial_of_equiv ψ
      (center_trivial_of_conj_injective conj_injective_projectiveSL3))
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := GenLocL5Out.stated_PSU hm
    exact GenLocBasic.conj_injective_of_center_trivial (center_trivial_of_equiv e
      (center_trivial_of_conj_injective (conj_injective_statedSU3 hp hp2 hK)))

theorem genInner_projectiveSL3 {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) : GenLocL5Out.GenInner (LinearFlag.projectiveSL 3 F) := by
  have hK2 : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
  intro A _ _ α hA hin
  exact gammaAct_projectiveSL_of_inner_odd' (by decide) hK2 conj_injective_projectiveSL3 hA.1 α
    fun a => hin ⟨a, rfl⟩

theorem genInner_statedSU3 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) : GenLocL5Out.GenInner (StatedProj (StatedSU 3 (p ^ f) K)) := by
  intro A _ _ α hA hin
  exact gammaAct_projectiveSU_of_inner_odd' hp hp2 hK (by decide)
    (conj_injective_statedSU3 hp hp2 hK) hA.1 α fun a => hin ⟨a, rfl⟩

theorem genInner_of_qShape3 {J : Type} [Group J] (h : QShape3 J) : GenLocL5Out.GenInner J := by
  obtain ⟨p, f, hp, hp2, -, hm | hm⟩ := h
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hm
    let ψ : J ≃* LinearFlag.projectiveSL 3 F :=
      e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
    exact GenLocL5Out.GenInner.of_mulEquiv ψ.symm (genInner_projectiveSL3 hp hp2 hF)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := GenLocL5Out.stated_PSU hm
    exact GenLocL5Out.GenInner.of_mulEquiv e.symm (genInner_statedSU3 hp hp2 hK)

theorem exists_ne_one_of_one_le_pRank {Y : Type} [Group Y] [Finite Y] {E : Subgroup Y}
    (h : 1 ≤ pRank 2 ↥E) : ∃ b ∈ E, b ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
  have hEA : CFSG.IsElementaryAbelian 2 ↥E :=
    WeakSigGen.isElementaryAbelian_of_forall (fun u hu v hv => by rw [hcon u hu, hcon v hv])
      (fun u hu => by rw [hcon u hu, mul_one])
  have : pRank 2 ↥E = 0 := by
    have hc : Nat.card ↥E = 2 ^ 0 := by rw [hbot, Subgroup.card_bot]; rfl
    exact CFSG.pRank_eq_of_card_eq_pow one_lt_two hc
  omega

theorem gammaAct_conjOn_qShape3 {Kt : Type} [Group Kt] [Finite Kt] (hKt : QShape3 Kt)
    {B : Subgroup Kt} (hB : CFSG.IsElementaryAbelian 2 ↥B) (hcard : Nat.card ↥B = 4) :
    gammaAct (conjOn B) = ⊤ := by
  have hGI := genInner_of_qShape3 hKt
  have hrank : pRank 2 ↥B = 2 := by
    have h1 := WeakSigGen.card_eq_two_pow_pRank hB
    rw [hcard] at h1
    have h2 : 2 ^ pRank 2 ↥B = 2 ^ 2 := by rw [← h1]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  exact hGI ↥B (conjOn B) ⟨hB, Or.inl hrank⟩ (by rintro _ ⟨b, rfl⟩; exact ⟨b.1, rfl⟩)

theorem shapeGen_3 : ShapeGenFor QShape3 4 := by
  intro Kt _ _ hKt B hB hcard
  have hinj := conj_injective_of_qShape3 hKt
  have hZ := center_trivial_of_conj_injective hinj
  have hrank : pRank 2 ↥B = 2 := by
    have h1 := WeakSigGen.card_eq_two_pow_pRank hB
    rw [hcard] at h1
    have h2 : 2 ^ pRank 2 ↥B = 2 ^ 2 := by rw [← h1]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  refine shapeGen_of_gammaAct (fun E hE => ?_) (gammaAct_conjOn_qShape3 hKt hB hcard)
  obtain ⟨b, hbE, hb1⟩ := exists_ne_one_of_one_le_pRank (E := E) (by omega)
  refine ⟨b, hbE, fun hbZ => hb1 ?_⟩
  exact Subtype.ext (hZ (b : Kt) (Subgroup.mem_center_iff.1 hbZ))

end S3

section S1

open Matrix

theorem gammaAct_eq_top_of_equiv {J J' : Type} [Group J] [Group J'] {A : Type} [Group A]
    (ψ : J ≃* J') (α : A →* MulAut J) (α' : A →* MulAut J')
    (hc : ∀ a x, α' a (ψ x) = ψ (α a x)) (h : gammaAct α' = ⊤) : gammaAct α = ⊤ := by
  have h2 := GenLocBasic.gammaAct_map_equiv ψ α α' hc
  have h4 : (gammaAct α).map ψ.toMonoidHom = ⊤ := h2.symm.trans h
  have h5 := Subgroup.comap_map_eq_self_of_injective (f := ψ.toMonoidHom) ψ.injective (gammaAct α)
  rw [h4, Subgroup.comap_top] at h5
  exact h5.symm

theorem gammaAct_conj_sl4 {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) {A : Type}
    [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (β : A →* Matrix.SpecialLinearGroup (Fin 4) F) :
    gammaAct ((MulAut.conj : Matrix.SpecialLinearGroup (Fin 4) F →*
      MulAut (Matrix.SpecialLinearGroup (Fin 4) F)).comp β) = ⊤ := by
  have hEA := hA.1
  have hsq : ∀ a : A, a * a = 1 := fun a => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a
  refine GenLocL4Inner.gammaAct_of_commuting_squares hF hA _
    (fun a => Matrix.SpecialLinearGroup.toGL (β a)) ?_ ?_ ?_
  · intro a g
    simp [MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul, ← map_inv]
  · intro a b
    simp only [← map_mul]
    rw [mul_comm' a b]
  · intro a
    refine ⟨1, one_ne_zero, ?_⟩
    have h1 : β a * β a = 1 := by rw [← map_mul, hsq a, map_one]
    have h2 : (Matrix.SpecialLinearGroup.toGL (β a) * Matrix.SpecialLinearGroup.toGL (β a)) = 1 := by
      rw [← map_mul, h1, map_one]
    have h3 := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) h2
    simpa using h3

theorem exists_noncentral_of_card {Kt : Type} [Group Kt] [Finite Kt] {B : Subgroup Kt}
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hZ : Nat.card ↥(center Kt) < 2 ^ (pRank 2 ↥B - 1))
    (E : Subgroup ↥B) (hE : pRank 2 ↥B - 1 ≤ pRank 2 ↥E) : ∃ b ∈ E, (b : Kt) ∉ center Kt := by
  by_contra hcon
  push Not at hcon
  have hBc := hB.1
  have hEA : CFSG.IsElementaryAbelian 2 ↥E :=
    WeakSigGen.isElementaryAbelian_of_forall (fun u _ v _ => mul_comm' u v)
      (fun u _ => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hB u)
  have hcard : Nat.card ↥E = 2 ^ pRank 2 ↥E := WeakSigGen.card_eq_two_pow_pRank hEA
  have hle : Nat.card ↥E ≤ Nat.card ↥(center Kt) := by
    have h1 : E.map B.subtype ≤ center Kt := by
      rintro _ ⟨b, hb, rfl⟩
      exact hcon b hb
    have h2 := Subgroup.card_le_of_le h1
    rwa [Subgroup.card_map_of_injective B.subtype_injective] at h2
  have h3 : 2 ^ (pRank 2 ↥B - 1) ≤ 2 ^ pRank 2 ↥E := Nat.pow_le_pow_right two_pos hE
  omega

theorem gammaAct_conjOn_stated_sl4 {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    {Kt : Type} [Group Kt] [Finite Kt] (e : Kt ≃* CFSG.Assembly.LowTwoRank.StatedSL 4 F)
    {B : Subgroup Kt} (hB : CFSG.IsElementaryAbelian 2 ↥B) :
    gammaAct (conjOn B) = ⊤ := by
  let ψ : Kt ≃* Matrix.SpecialLinearGroup (Fin 4) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 F).symm
  let β : ↥B →* Matrix.SpecialLinearGroup (Fin 4) F := ψ.toMonoidHom.comp B.subtype
  have h1 := gammaAct_conj_sl4 hF hB β
  exact gammaAct_eq_top_of_equiv ψ (conjOn B)
    ((MulAut.conj : Matrix.SpecialLinearGroup (Fin 4) F →*
      MulAut (Matrix.SpecialLinearGroup (Fin 4) F)).comp β) (fun a x => by
        simp [β, conjOn_apply, MulAut.conj_apply]) h1

theorem card_center_le_two_of_frame {Kt : Type} [Group Kt] {z : Kt}
    (hc : ∀ g : Kt, g ∈ center Kt ↔ g = 1 ∨ g = z) : Nat.card ↥(center Kt) ≤ 2 := by
  have hset : ((center Kt : Subgroup Kt) : Set Kt) = {1, z} := by
    ext g
    simp [hc g]
  have h1 : Nat.card ↥(center Kt) = Set.ncard ((center Kt : Subgroup Kt) : Set Kt) :=
    Nat.card_coe_set_eq _
  rw [h1, hset]
  exact (Set.ncard_insert_le _ _).trans (by simp)

@[expose] def GenConjSU4 : Prop :=
  ∀ (q : ℕ) (F : Type) [Field F] [Finite F], Nat.card F = q ^ 2 → q % 4 = 1 →
    ∀ (Kt : Type) [Group Kt] [Finite Kt],
      Nonempty (Kt ≃* CFSG.Assembly.LowTwoRank.StatedSU 4 q F) →
        ∀ B : Subgroup Kt, CFSG.IsElementaryAbelian 2 ↥B → Nat.card ↥B = 8 →
          gammaAct (conjOn B) = ⊤

end S1

end ShapeGenS13

@[expose] def GenConj (Pr : ∀ (Kt : Type) [Group Kt], Prop) (n : ℕ) : Prop :=
  ∀ (Kt : Type) [Group Kt] [Finite Kt], Pr Kt → ∀ B : Subgroup Kt, CFSG.IsElementaryAbelian 2 ↥B →
    Nat.card ↥B = n → gammaAct (ShapeGenS13.conjOn B) = ⊤

namespace ShapeGenS13

theorem genConj_1 (hU : GenConjSU4) : GenConj QShape1 8 := by
  intro Kt _ _ hKt B hB hcard
  rcases hKt with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · exact gammaAct_conjOn_stated_sl4 (GenLocL4Lin.ringChar_ne_two hF) e hB
  · exact hU q F hF hq Kt ⟨e⟩ B hB hcard

theorem shapeGen_1 (hU : GenConjSU4) : ShapeGenFor QShape1 8 := by
  intro Kt _ _ hKt B hB hcard
  obtain ⟨z, -, -, -, hc, -⟩ := CFSG.GH74.L5U5.IsSL4Model.exists_q8_frame hKt
  have hZ := card_center_le_two_of_frame hc
  have hrank : pRank 2 ↥B = 3 := by
    have h1 := WeakSigGen.card_eq_two_pow_pRank hB
    rw [hcard] at h1
    have h2 : 2 ^ pRank 2 ↥B = 2 ^ 3 := by rw [← h1]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  exact shapeGen_of_gammaAct (exists_noncentral_of_card hB (by rw [hrank]; omega))
    (genConj_1 hU Kt hKt B hB hcard)

end ShapeGenS13

end CFSG.GH74.Generic.BProg.B2
