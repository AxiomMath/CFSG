module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311e
public import CFSG.RankThree.PartOne.SEITZ2.G2Outer
import CFSG.RankThree.PartOne.SEITZ2.G2F2Main
import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Untwisted
public import CFSG.RankThree.PartOne.SEITZ2.ReeOuter
public import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256e2
public import CFSG.LieType.SeitzGeneration.OuterSUData
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2323b2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311e

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
open CFSG.RankThree.PartOne.CTP

section RootElements

open CFSG.Blueprint CFSG.Blueprint.Chevalley


theorem xOp_pow_eq (τ : Tag) {R : Type*} [CommRing R] (i : Fin τ.rank) (c : R) (n : ℕ) :
    xOp τ R i c ^ n = xOp τ R i (n * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, xOp_zero]
  | succ n ih => rw [pow_succ, ih, xOp_mul_xOp (upTransport τ), Nat.cast_succ, add_mul, one_mul]

theorem yOp_pow_eq (τ : Tag) {R : Type*} [CommRing R] (i : Fin τ.rank) (c : R) (n : ℕ) :
    yOp τ R i c ^ n = yOp τ R i (n * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, yOp_zero]
  | succ n ih => rw [pow_succ, ih, yOp_mul_yOp (downTransport τ), Nat.cast_succ, add_mul, one_mul]

theorem closure_pow_ringChar_adjointGroup (τ : Tag) (K : Type) [Field K] :
    Subgroup.closure {g : adjointGroup τ K | g ^ ringChar K = 1} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  have key : ∀ (x : ModGL τ K) (hx : x ∈ Subgroup.closure {g : ModGL τ K | ∃ (i : Fin τ.rank) (c : K),
      (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
        (g : Module.End K (RootModule τ K)) = yOp τ K i c}),
      (⟨x, hx⟩ : adjointGroup τ K) ∈ Subgroup.closure {g : adjointGroup τ K | g ^ ringChar K = 1} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ?_
      show (⟨x, Subgroup.subset_closure hx⟩ : adjointGroup τ K) ^ ringChar K = 1
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      obtain ⟨i, c, h | h⟩ := hx
      · rw [h, xOp_pow_eq, ringChar.Nat.cast_ringChar, zero_mul, xOp_zero]
      · rw [h, yOp_pow_eq, ringChar.Nat.cast_ringChar, zero_mul, yOp_zero]
    | one => exact one_mem _
    | mul x y _ _ ihx ihy => exact mul_mem ihx ihy
    | inv x _ ih => exact inv_mem ih
  exact key g hg

end RootElements

theorem fixedSubgroup_le_closure_of_conj {K : Type*} [Group K] {n : ℕ} {α β c : MulAut K}
    (h : c * α * c⁻¹ = β)
    (hβ : fixedSubgroup β ≤ Subgroup.closure {x | β x = x ∧ x ^ n = 1}) :
    fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ x ^ n = 1} := by
  have hα : α = c⁻¹ * β * c := by rw [← h]; group
  intro x hx
  have hx' : c x ∈ fixedSubgroup β := by
    have h1 : α x = x := hx
    show β (c x) = c x
    rw [← h]
    simp [MulAut.mul_apply, h1]
  have h1 := Subgroup.mem_map_of_mem c⁻¹.toMonoidHom (hβ hx')
  rw [MonoidHom.map_closure] at h1
  have h2 : c⁻¹.toMonoidHom (c x) = x := by simp
  rw [h2] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨y, ⟨hy, hyn⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hα]
    simp [MulAut.mul_apply, hy]
  · rw [← map_pow, hyn, map_one]

theorem exists_noncomm_of_conj_injective {P : Type*} [Group P] [Nontrivial P]
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) : ∃ a b : P, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := exists_ne (1 : P)
  apply ha
  apply hinj
  ext y
  rw [MulAut.conj_apply, map_one, MulAut.one_apply, hcon a y, mul_inv_cancel_right]

section G2Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.SEITZ2


theorem g2Fixed_le_closure {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    g2Fixed σ ≤ Subgroup.closure {x : adjointGroup .G2 K |
      entrywiseAdjointAut .G2 σ x = x ∧ x ^ ringChar K = 1} := by
  have hchar : ringChar (fixSubfield σ) = ringChar K := by
    have : CharP (fixSubfield σ) (ringChar K) := inferInstance
    exact ringChar.eq _ _
  intro y hy
  have hz : g2FixedEquiv σ ⟨y, hy⟩ ∈ Subgroup.closure {z : adjointGroup .G2 (fixSubfield σ) |
      z ^ ringChar (fixSubfield σ) = 1} := by
    rw [closure_pow_ringChar_adjointGroup]
    exact Subgroup.mem_top _
  have h1 : (⟨y, hy⟩ : ↥(g2Fixed σ)) ∈ (Subgroup.closure {z : adjointGroup .G2 (fixSubfield σ) |
      z ^ ringChar (fixSubfield σ) = 1}).map (g2FixedEquiv σ).symm.toMonoidHom := ⟨_, hz, by simp⟩
  rw [MonoidHom.map_closure] at h1
  have h2 := Subgroup.mem_map_of_mem (g2Fixed σ).subtype h1
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · have hmem : (((g2FixedEquiv σ).symm z : ↥(g2Fixed σ)) : adjointGroup .G2 K) ∈
        fixedSubgroup (entrywiseAdjointAut .G2 σ) := by
      rw [fixedSubgroup_entrywise_eq]
      exact ((g2FixedEquiv σ).symm z).2
    exact hmem
  · have hz' : z ^ ringChar K = 1 := by rw [← hchar]; exact hz
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [← Subgroup.coe_pow, ← map_pow, hz', map_one, Subgroup.coe_one]


theorem uniPlaneGen_outer_G2_even {f p : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) [IsSimpleGroup (adjointGroup .G2 K)] (hp : p.Prime) (hp5 : 5 ≤ p)
    (E : Subgroup (MulAut (adjointGroup .G2 K))) [CFSG.IsElementaryAbelian p E]
    (hc : Nat.card E = p ^ 2) (hout : ¬ ∀ φ ∈ E, ∃ g, φ = MulAut.conj g) :
    UniPlaneGen (ringChar K) E := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj := CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup (τ := .G2) (K := K)
  have hnab : ∃ a b : adjointGroup .G2 K, a * b ≠ b * a := exists_noncomm_of_conj_injective hinj
  have hd : FieldAutData (adjointGroup .G2 K) p :=
    fieldAutData_G2 (subfieldPairG2_of_f2 subfieldPairG2F2) hp hp5 hf hK
  have hfix : ∀ τ : MulAut (adjointGroup .G2 K), IsOuterOfOrder p τ →
      fixedSubgroup τ ≤ Subgroup.closure {x | τ x = x ∧ x ^ ringChar K = 1} := by
    intro τ hτ
    obtain ⟨h, σ, -, hh⟩ := exists_conj_entrywise hp hf hK τ hτ
    refine fixedSubgroup_le_closure_of_conj hh ?_
    rw [fixedSubgroup_entrywise_eq]
    exact g2Fixed_le_closure σ
  exact uniPlaneGen_of_fieldAutData hnab hp hd hfix E hc hout


theorem uniSeitzPlanes_G2_outer_even :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsG2Index d.1 ∧ d.1.characteristic = 2 ∧ 5 ≤ p := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, ⟨q, rfl⟩, hq2, hp5⟩
  have : Fact p.Prime := ⟨hp⟩
  have hq2' : q.p = 2 := by simpa using hq2
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hK' : Nat.card K = 2 ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def, hq2']
  have hchar : ringChar K = q.p := by
    rw [hq2']
    have : CharP K 2 := charP_two_of_card hK'
    exact ringChar.eq K 2
  have hf : 2 ≤ q.exponent := by
    have h3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    rw [TauCeti.PrimePower.card_def, hq2'] at h3
    by_contra hlt
    have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [h1] at h3
    norm_num at h3
  obtain ⟨-, hsimple⟩ := finite_isSimpleGroup_cat_G2 hv
  have : IsSimpleGroup (adjointGroup .G2 K) := MulEquiv.isSimpleGroup e.symm
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have h := uniPlaneGen_outer_G2_even hf hK' hp hp5 (E.map (MulAut.congr e).toMonoidHom) hc' hout'
  rw [hchar] at h
  have h' := (uniPlaneGen_map_congr e _ E).1 h
  simpa using h'

end G2Even

section FieldAutDataDvd

theorem uniPlaneGen_of_fieldAutData_dvd {K : Type} [Group K] [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a)
    {p r : ℕ} (hp : p.Prime) (hd : FieldAutData K p)
    (hfix : ∀ τ : MulAut K, IsOuterOfOrder p τ → p ∣ Nat.card (fixedSubgroup τ) →
      fixedSubgroup τ ≤ Subgroup.closure {x | τ x = x ∧ ∃ n : ℕ, x ^ (r ^ n) = 1})
    (E : Subgroup (MulAut K)) [hE : CFSG.IsElementaryAbelian p E] (hEc : Nat.card E = p ^ 2)
    (hout : ¬ ∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) : UniPlaneGen r E := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj := conj_injective_of_simple hnab
  obtain ⟨k, hk1, hkE⟩ := hd.out_rank E hE hEc
  push Not at hout
  obtain ⟨σ, hσE, hσinn⟩ := hout
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hσ1 : σ ≠ 1 := fun h => hσinn 1 (by rw [h, map_one])
  have hσp : σ ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian σ hσE
  have hσo : IsOuterOfOrder p σ := ⟨orderOf_eq_prime hσp hσ1, hσinn⟩
  have hkp : k ^ p = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ hkE
  have hcomm : σ * MulAut.conj k = MulAut.conj k * σ := hcommE σ hσE _ hkE
  have hστE : σ * MulAut.conj k ∈ E := E.mul_mem hσE hkE
  have hστ1 : σ * MulAut.conj k ≠ 1 := by
    intro h
    apply hσinn k⁻¹
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left h
  have hστp : (σ * MulAut.conj k) ^ p = 1 := by
    rw [(show Commute σ (MulAut.conj k) from hcomm).mul_pow, hσp, ← map_pow, hkp, map_one, one_mul]
  have hστo : IsOuterOfOrder p (σ * MulAut.conj k) := by
    refine ⟨orderOf_eq_prime hστp hστ1, fun g h => hσinn (g * k⁻¹) ?_⟩
    rw [map_mul, map_inv, ← h, mul_assoc, mul_inv_cancel, mul_one]
  have hσk : σ k = k := apply_eq_of_commute_conj hinj hcomm
  have hkP : k ∈ fixedSubgroup σ := hσk
  have hord : orderOf k = p := (orderOf_eq_prime hkp hk1 : orderOf k = p)
  have hpdvd : p ∣ Nat.card (fixedSubgroup σ) := by
    have h1 : orderOf (⟨k, hkP⟩ : fixedSubgroup σ) ∣ Nat.card (fixedSubgroup σ) :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hord] at h1
  have hkP' : k ∈ fixedSubgroup (σ * MulAut.conj k) := by
    show (σ * MulAut.conj k) k = k
    rw [MulAut.mul_apply, MulAut.conj_apply, mul_inv_cancel_right, hσk]
  have hpdvd' : p ∣ Nat.card (fixedSubgroup (σ * MulAut.conj k)) := by
    have h1 : orderOf (⟨k, hkP'⟩ : fixedSubgroup (σ * MulAut.conj k)) ∣
        Nat.card (fixedSubgroup (σ * MulAut.conj k)) := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hord] at h1
  have hne : fixedSubgroup σ ≠ fixedSubgroup (σ * MulAut.conj k) := by
    intro heq
    apply hk1
    refine hd.center σ hσo hpdvd k hkP fun y hy => ?_
    have hy' : y ∈ fixedSubgroup (σ * MulAut.conj k) := heq ▸ hy
    have h1 : σ y = y := hy
    have h2 : (σ * MulAut.conj k) y = y := hy'
    have h3 : σ (k * y * k⁻¹) = k * y * k⁻¹ := by
      rw [map_mul, map_mul, map_inv, hσk, h1]
    have h4 : σ (k * y * k⁻¹) = y := by
      simpa [MulAut.mul_apply, MulAut.conj_apply] using h2
    rw [h4] at h3
    calc k * y = k * y * k⁻¹ * k := by group
      _ = y * k := by rw [← h3]
  rcases hd.gen σ _ hσo hστo hne with hg | hsmall
  · rw [UniPlaneGen, eq_top_iff, ← hg, Subgroup.closure_le]
    rintro x (hx | hx)
    · refine ((Subgroup.closure_le _).2 ?_) (hfix σ hσo hpdvd hx)
      rintro y ⟨hy, n, hyr⟩
      exact mem_uniPlaneClosure hσE hσ1 hy hyr
    · refine ((Subgroup.closure_le _).2 ?_) (hfix _ hστo hpdvd' hx)
      rintro y ⟨hy, n, hyr⟩
      exact mem_uniPlaneClosure hστE hστ1 hy hyr
  · exact absurd hpdvd hsmall

theorem closure_pow_two_le_closure_two_pow {K : Type*} [Group K] (α : MulAut K) :
    Subgroup.closure {x | α x = x ∧ x ^ 2 = 1} ≤
      Subgroup.closure {x | α x = x ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1} :=
  Subgroup.closure_mono fun _ ⟨h1, h2⟩ => ⟨h1, 1, by rw [pow_one]; exact h2⟩

theorem fixedSubgroup_le_closure_pow_of_conj {K : Type*} [Group K] {r : ℕ} {α β c : MulAut K}
    (h : c * α * c⁻¹ = β)
    (hβ : fixedSubgroup β ≤ Subgroup.closure {x | β x = x ∧ ∃ n : ℕ, x ^ (r ^ n) = 1}) :
    fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ ∃ n : ℕ, x ^ (r ^ n) = 1} := by
  have hα : α = c⁻¹ * β * c := by rw [← h]; group
  intro x hx
  have hx' : c x ∈ fixedSubgroup β := by
    have h1 : α x = x := hx
    show β (c x) = c x
    rw [← h]
    simp [MulAut.mul_apply, h1]
  have h1 := Subgroup.mem_map_of_mem c⁻¹.toMonoidHom (hβ hx')
  rw [MonoidHom.map_closure] at h1
  have h2 : c⁻¹.toMonoidHom (c x) = x := by simp
  rw [h2] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨y, ⟨hy, n, hyn⟩, rfl⟩
  refine ⟨?_, n, ?_⟩
  · rw [hα]
    simp [MulAut.mul_apply, hy]
  · rw [← map_pow, hyn, map_one]

theorem closure_pow_two_eq_top_of_simple {F : Type*} [Group F] [Finite F] [IsSimpleGroup F]
    (hna : ∃ a b : F, a * b ≠ b * a) : Subgroup.closure {x : F | x ^ 2 = 1} = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Inputs2323b.normal_closure_pow_eq_one F 2
  have h2 : 2 ∣ Nat.card F := by
    have hev : Even (Nat.card F) := by
      by_contra h
      have hodd : Odd (Nat.card F) := Nat.not_even_iff_odd.mp h
      obtain ⟨a, b, hab⟩ := hna
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr (CFSG.FeitThompson.isSolvable_of_odd_natCard F hodd) a b)
    exact even_iff_two_dvd.mp hev
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure {x : F | x ^ 2 = 1}) with h | h
  · exfalso
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hmem : x ∈ Subgroup.closure {x : F | x ^ 2 = 1} :=
      Subgroup.subset_closure (show x ^ 2 = 1 by rw [← hx, pow_orderOf_eq_one])
    rw [h, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hx
    omega
  · exact h

noncomputable def card_fixedSubgroup_conj_equiv {K : Type*} [Group K] (c α : MulAut K) :
    fixedSubgroup α ≃ fixedSubgroup (c * α * c⁻¹) where
  toFun x := ⟨c x, by
    show (c * α * c⁻¹) (c x) = c x
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [show α x = x from x.2]⟩
  invFun y := ⟨c⁻¹ y, by
    have hy : (c * α * c⁻¹) y = y := y.2
    show α (c⁻¹ y) = c⁻¹ y
    simp only [MulAut.mul_apply, MulAut.inv_apply] at hy ⊢
    apply c.injective
    rw [MulEquiv.apply_symm_apply]
    exact hy⟩
  left_inv x := Subtype.ext (by simp [MulAut.inv_apply])
  right_inv y := Subtype.ext (by simp [MulAut.inv_apply])

theorem fixedSubgroup_le_closure_of_simple {K : Type*} [Group K] {α : MulAut K}
    [Finite (fixedSubgroup α)] [IsSimpleGroup (fixedSubgroup α)]
    (hna : ∃ a b : fixedSubgroup α, a * b ≠ b * a) :
    fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ x ^ 2 = 1} := by
  intro y hy
  have h1 : (⟨y, hy⟩ : fixedSubgroup α) ∈ Subgroup.closure {x : fixedSubgroup α | x ^ 2 = 1} := by
    rw [closure_pow_two_eq_top_of_simple hna]
    exact Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem (fixedSubgroup α).subtype h1
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨z.2, ?_⟩
  have hz' : z ^ 2 = 1 := hz
  simp only [Subgroup.coe_subtype]
  rw [← Subgroup.coe_pow, hz', Subgroup.coe_one]

theorem closure_two_pow_eq_top_of_derived {Γ : Type*} [Group Γ] [Finite Γ]
    [IsSimpleGroup (commutator Γ)] (hna : ∃ a b : commutator Γ, a * b ≠ b * a)
    (h2 : IsPGroup 2 (Γ ⧸ commutator Γ)) :
    Subgroup.closure {x : Γ | ∃ n : ℕ, x ^ (2 ^ n) = 1} = ⊤ := by
  classical
  set N := Subgroup.closure {x : Γ | ∃ n : ℕ, x ^ (2 ^ n) = 1} with hN
  have hD : commutator Γ ≤ N := by
    intro y hy
    have h1 : (⟨y, hy⟩ : commutator Γ) ∈ Subgroup.closure {x : commutator Γ | x ^ 2 = 1} := by
      rw [closure_pow_two_eq_top_of_simple hna]
      exact Subgroup.mem_top _
    have h3 := Subgroup.mem_map_of_mem (commutator Γ).subtype h1
    rw [MonoidHom.map_closure] at h3
    refine Subgroup.closure_mono ?_ h3
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨1, ?_⟩
    have hz' : z ^ 2 = 1 := hz
    rw [pow_one]
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_pow, hz', Subgroup.coe_one]
  rw [eq_top_iff]
  intro g _
  obtain ⟨k, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hu : (g ^ m) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
  have hv : (g ^ (2 ^ k)) ^ m = 1 := by
    rw [← pow_mul, ← hom, pow_orderOf_eq_one]
  have hvD : g ^ (2 ^ k) ∈ commutator Γ := by
    obtain ⟨s, hs⟩ := h2 (QuotientGroup.mk (g ^ (2 ^ k)))
    have hs' : (QuotientGroup.mk (g ^ (2 ^ k)) : Γ ⧸ commutator Γ) ^ (2 ^ s) = 1 := hs
    have hm' : (QuotientGroup.mk (g ^ (2 ^ k)) : Γ ⧸ commutator Γ) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, hv, QuotientGroup.mk_one]
    have hcop : Nat.Coprime (2 ^ s) m := Nat.Coprime.pow_left s (Nat.coprime_two_left.2 hm)
    have hone : (QuotientGroup.mk (g ^ (2 ^ k)) : Γ ⧸ commutator Γ) = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hs', hm'⟩
      rwa [hcop.gcd_eq_one, pow_one] at h1
    exact (QuotientGroup.eq_one_iff _).1 hone
  have hcop : Nat.Coprime m (2 ^ k) := (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)).symm
  have hgcd : (Nat.gcd m (2 ^ k) : ℤ) = m * Nat.gcdA m (2 ^ k) + 2 ^ k * Nat.gcdB m (2 ^ k) :=
    Nat.gcd_eq_gcd_ab m (2 ^ k)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hgcd
  have hg : g = (g ^ m) ^ Nat.gcdA m (2 ^ k) * (g ^ (2 ^ k)) ^ Nat.gcdB m (2 ^ k) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    push_cast
    rw [← hgcd, zpow_one]
  rw [hg]
  exact mul_mem (zpow_mem (Subgroup.subset_closure
    (show g ^ m ∈ {x : Γ | ∃ n : ℕ, x ^ (2 ^ n) = 1} from ⟨k, hu⟩)) _) (zpow_mem (hD hvD) _)

theorem fixedSubgroup_le_closure_of_closure_two {K : Type*} [Group K] {α : MulAut K}
    (h : Subgroup.closure {x : fixedSubgroup α | ∃ n : ℕ, x ^ (2 ^ n) = 1} = ⊤) :
    fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1} := by
  intro y hy
  have h1 : (⟨y, hy⟩ : fixedSubgroup α) ∈ Subgroup.closure {x : fixedSubgroup α | ∃ n : ℕ, x ^ (2 ^ n) = 1} := by
    rw [h]
    exact Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem (fixedSubgroup α).subtype h1
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨z, ⟨n, hz⟩, rfl⟩
  refine ⟨z.2, n, ?_⟩
  simp only [Subgroup.coe_subtype]
  rw [← Subgroup.coe_pow, hz, Subgroup.coe_one]

end FieldAutDataDvd

section UnitaryOuterEven

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP

theorem fixedSubgroup_primeFormFieldHom_le_closure_even {f p n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hp : p.Prime) (hp5 : 5 ≤ p) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ 2 ^ f = 2))
    (hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n))
    (hdvd : p ∣ Nat.card (fixedSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ))) :
    fixedSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) ≤
      Subgroup.closure {x | primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ x = x ∧ x ^ 2 = 1} := by
  have hfin := h.finite
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, -, -, -, -, -, -, hsimp, h72⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσ n hn hne hZ
  have hFeq : fixedSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) =
      fieldFixedPSU h n σ :=
    Subgroup.ext fun _ => Iff.rfl
  by_cases hq₀ : n = 3 ∧ 2 ^ (f / p) = 2
  · exfalso
    obtain ⟨hcard, -⟩ := h72 hq₀ (by omega)
    rw [hFeq, hcard] at hdvd
    have h72' : p ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact hdvd
    rcases (Nat.Prime.dvd_mul hp).1 h72' with h3 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
      omega
  · obtain ⟨hs, hnc, -⟩ := hsimp hq₀
    have : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      Finite.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    rw [hFeq] at hdvd ⊢
    have : IsSimpleGroup (fixedSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) := hs
    have hna : ∃ a b : fixedSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ),
        a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact hnc hcon
    rw [← hFeq]
    exact fixedSubgroup_le_closure_of_simple hna

theorem uniPlaneGen_outer_su_model_even {d : TauCeti.ValidLieTypeIndex}
    {ℓ n f p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ = 2)
    (e : Cat d ≃* primeFormP h (idGram K n)) (hn3 : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ InnerPlane d p E) : UniPlaneGen ℓ E := by
  classical
  subst hℓ2
  have : Fact p.Prime := ⟨hp⟩
  have hfin := h.finite
  have : CharP K 2 := h.charP
  have hp2 : p ≠ 2 := by omega
  have hpℓ : p ≠ 2 := hp2
  have : IsSimpleGroup (primeFormP h (idGram K n)) := isSimpleGroup_primeFormP_one h hn3 hne
  have hnab : ∃ a b : primeFormP h (idGram K n), a * b ≠ b * a := by
    have hnc := not_commute_primeFormP_one h hn3 hne
    push Not at hnc
    exact hnc
  have hd : FieldAutData (primeFormP h (idGram K n)) p :=
    fieldAutData_primeFormP_odd
      (subfieldPairSUOdd CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds)
      hn3 h hne hp hp2 hpℓ hg
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact hg
  have hfix : ∀ α : MulAut (primeFormP h (idGram K n)), IsOuterOfOrder p α →
      p ∣ Nat.card (fixedSubgroup α) →
        fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1} := by
    intro α hα hαdvd
    obtain ⟨hord, hout'⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    have hσ1 : primeFormFieldFactor h hC hn3 hne α ≠ 1 := by
      intro h1
      have hD : α ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [← ker_primeFormFieldFactor h hC hn3 hne]
        exact h1
      obtain ⟨g, hgk⟩ := pElement_mem_inner_of_not_dvd_gcd h hn3 hne hp hg hD hαp
      exact hout' g hgk.symm
    have hσp : (primeFormFieldFactor h hC hn3 hne α) ^ p = 1 := by
      rw [← map_pow, hαp, map_one]
    have hσord : orderOf (primeFormFieldFactor h hC hn3 hne α) = p := orderOf_eq_prime hσp hσ1
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne hp hp2 hpℓ
        α hord _ rfl hσord
    set c := (primeFormConjHom h _ M)⁻¹ with hcdef
    have hconj : c * α * c⁻¹ =
        primeFormFieldHom h (isPrimeFormGram_one (n := n)) (primeFormFieldFactor h hC hn3 hne α) := by
      rw [hcdef, inv_inv]
      exact hM
    have hcard : Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup
        (primeFormFieldHom h (isPrimeFormGram_one (n := n)) (primeFormFieldFactor h hC hn3 hne α))) := by
      rw [← hconj]
      exact Nat.card_congr (card_fixedSubgroup_conj_equiv c α)
    have key := fixedSubgroup_le_closure_of_conj (n := 2) hconj
      (fixedSubgroup_primeFormFieldHom_le_closure_even h hp hp5 hσord hn3 hne hZ (hcard ▸ hαdvd))
    exact key.trans (closure_pow_two_le_closure_two_pow α)
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout'' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h'
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h' φ hφ).imp fun g hg => hg.symm
  exact (uniPlaneGen_map_congr e _ E).1 (uniPlaneGen_of_fieldAutData_dvd hnab hp hd hfix _ hc' hout'')

theorem uniSeitzPlanes_unitary_outer_even :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsUnitaryIndex' d.1 ∧ CentralPrimeFree p d.1 ∧
      d.1.characteristic = 2 ∧ 5 ≤ p := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, ⟨m, q, hd⟩, hlift, hch, hp5⟩
  subst hd
  obtain ⟨hℓ, hf, hn3, hne, F, _, hU, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv
        (MulEquiv.refl (Cat ⟨.twistedA m q, hv⟩)))
  have h := uniPlaneGen_outer_su_model_even hU (by simpa using hch) θ hn3 hne hp hp5 (by
      intro hdv
      apply hlift
      rw [TauCeti.PrimePower.card_def]
      exact ⟨hdv.trans (Nat.gcd_dvd_right _ _), hdv.trans (Nat.gcd_dvd_left _ _)⟩) hE hc hout
  simpa using h

end UnitaryOuterEven

section ReeF4Parabolic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

@[expose] def uniCentSetIn {G : Type*} [Group G] (N A : Subgroup G) (r : ℕ) : Set G :=
  {g | g ∈ N ∧ ∃ x ∈ A, x ≠ 1 ∧ g * x = x * g ∧ ∃ n : ℕ, g ^ (r ^ n) = 1}

theorem iSup_inf_centralizer_le_closure {G : Type*} [Group G] {N A W : Subgroup G} (hWN : W ≤ N)
    (hW2 : IsPGroup 2 W) :
    (⨆ x ∈ A, ⨆ (_ : x ≠ 1), W ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      Subgroup.closure (uniCentSetIn N A 2) := by
  refine iSup₂_le fun x hx => iSup_le fun hx1 => fun g hg => ?_
  obtain ⟨hgW, hgc⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgc
  obtain ⟨n, hn⟩ := hW2 ⟨g, hgW⟩
  refine Subgroup.subset_closure ⟨hWN hgW, x, hx, hx1, hgc, n, ?_⟩
  simpa using congrArg Subtype.val hn

theorem reeGamma_le_closure_of_le_levi
    [IsSimpleGroup ↥(F4.reeGamma K a)] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (j : Fin F4.fixedOrbitCount) {A : Subgroup (ModGL F4.tag K)}
    [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A)
    (hAL : A ≤ F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a) :
    F4.reeGamma K a ≤ Subgroup.closure (uniCentSetIn (F4.reeGamma K a) A 2) := by
  have := finite_modGL (τ := F4.tag) (K := K)
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  set n := canonicalRep (coxeterSystem F4.tag) K w₀ with hn
  have hnΓ : n ∈ F4.reeGamma K a := (canonicalRep_longest_mem_reeFixedMonomial hw₀).2
  set V := F4.reeFixedOrbitComplementUnipotent K a j with hV
  set V' := V.map (MulAut.conj n⁻¹).toMonoidHom with hV'
  set L := F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a with hL
  obtain ⟨i, hij⟩ : ∃ i : Fin F4.fixedOrbitCount, i ≠ j := by
    have : ∀ j : Fin F4.fixedOrbitCount, ∃ i : Fin F4.fixedOrbitCount, i ≠ j := by decide
    exact this j
  have hVΓ : V ≤ F4.reeGamma K a := inf_le_right
  have hV'Γ : V' ≤ F4.reeGamma K a := by
    rintro _ ⟨v, hv, rfl⟩
    exact mul_mem (mul_mem (inv_mem hnΓ) (hVΓ hv)) (by simpa using hnΓ)
  have hBP := (reeFixedBorel_lt_reeLocalParabolic (K := K) (a := a) (t := F4) j).le
  have hLP : L ≤ F4.reeLocalParabolic K a j :=
    sup_le (reeLocalBlock_le j) (reeFixedTorus_le_reeFixedBorel.trans hBP)
  have hLV : L ≤ Subgroup.normalizer (V : Set (ModGL F4.tag K)) :=
    hLP.trans (reeLocalParabolic_le_normalizer_complement j)
  have hnL : L.map (MulAut.conj n).toMonoidHom ≤
      Subgroup.normalizer (V : Set (ModGL F4.tag K)) := by
    rw [hL, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [reeLocalBlock, Subgroup.map_sup, map_conj_reeFixedOrbitUnipotent_longest hw₀,
        map_conj_reeFixedOrbitNegUnipotent_longest hw₀, sup_comm]
      exact (reeLocalBlock_le j).trans (reeLocalParabolic_le_normalizer_complement j)
    · rw [map_conj_reeFixedTorus hw₀]
      exact reeFixedTorus_le_normalizer_complement j
  have hLV' : L ≤ Subgroup.normalizer (V' : Set (ModGL F4.tag K)) := fun l hl =>
    mem_normalizer_map_conj_inv (hnL ⟨l, hl, rfl⟩)
  have hV2 : IsPGroup 2 V := isPGroup_reeFixedOrbitComplementUnipotent j
  have hV'2 : IsPGroup 2 V' := hV2.map _
  have hpV : ¬ p ∣ Nat.card V := not_dvd_card_of_isPGroup (Ne.symm hp2) hV2
  have hpV' : ¬ p ∣ Nat.card V' := not_dvd_card_of_isPGroup (Ne.symm hp2) hV'2
  have h1 := le_iSup_inf_centralizer_of_coprime (C := V) hcard hpV (hAL.trans hLV) le_rfl
  have h2 := le_iSup_inf_centralizer_of_coprime (C := V') hcard hpV' (hAL.trans hLV') le_rfl
  have hXV : ∀ k, k ≠ j → F4.reeFixedOrbitUnipotent K a k ≤ V := fun k hk =>
    inf_le_inf_right _ (rootSpan_mono (fixedOrbitRoots_subset_complement_of_ne F4 hk))
  have hYV' : ∀ k, k ≠ j → F4.reeFixedOrbitNegUnipotent K a k ≤ V' := by
    intro k hk y hy
    refine ⟨n * y * n⁻¹, hXV k hk ?_, ?_⟩
    · rw [← map_conj_reeFixedOrbitNegUnipotent_longest hw₀ k]
      exact ⟨y, hy, rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hMW : ∀ k, k ≠ j → F4.reeLocalBlock K a k ≤ V ⊔ V' := fun k hk =>
    sup_le ((hXV k hk).trans le_sup_left) ((hYV' k hk).trans le_sup_right)
  have hMN : ∀ k, F4.reeLocalBlock K a k ≤
      Subgroup.normalizer ((V ⊔ V' : Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) := by
    intro k
    by_cases hk : k = j
    · subst hk
      exact fun m hm => mem_normalizer_sup_of_mem (hLV (Subgroup.mem_sup_left hm))
        (hLV' (Subgroup.mem_sup_left hm))
    · exact (hMW k hk).trans Subgroup.le_normalizer
  have hΓN : F4.reeGamma K a ≤
      Subgroup.normalizer ((V ⊔ V' : Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) := by
    rw [large_Ree_simple_pair_generation a K hK]
    exact sup_le (hMN _) (hMN _)
  have hWΓ : V ⊔ V' ≤ F4.reeGamma K a := sup_le hVΓ hV'Γ
  have hWnorm : ((V ⊔ V').subgroupOf (F4.reeGamma K a)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWΓ).2 hΓN
  have hV1 : V ≠ ⊥ := by
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (t := F4) (K := K) (a := a) i
    intro hbot
    apply hu1
    have := hXV i hij hu
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have hWtop : F4.reeGamma K a ≤ V ⊔ V' := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((V ⊔ V').subgroupOf (F4.reeGamma K a))
      with h | h
    · exfalso
      have hW : V ⊔ V' = ⊥ := (Subgroup.subgroupOf_eq_bot.1 h).eq_bot_of_le hWΓ
      exact hV1 (eq_bot_iff.2 (le_sup_left.trans hW.le))
    · exact Subgroup.subgroupOf_eq_top.1 h
  exact hWtop.trans (sup_le (h1.trans (iSup_inf_centralizer_le_closure hVΓ hV2))
    (h2.trans (iSup_inf_centralizer_le_closure hV'Γ hV'2)))

theorem le_closure_uniCentSetIn_of_map_conj {G : Type*} [Group G] {N A : Subgroup G} {c : G} (hc : c ∈ N)
    {r : ℕ} (h : N ≤ Subgroup.closure (uniCentSetIn N (A.map (MulAut.conj c).toMonoidHom) r)) :
    N ≤ Subgroup.closure (uniCentSetIn N A r) := by
  have hle : Subgroup.closure (uniCentSetIn N (A.map (MulAut.conj c).toMonoidHom) r) ≤
      (Subgroup.closure (uniCentSetIn N A r)).comap (MulAut.conj c⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro g ⟨hgN, _, ⟨x, hx, rfl⟩, hx1, hgx, n, hn⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
    refine Subgroup.subset_closure ⟨?_, x, hx, hx1', ?_, n, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact mul_mem (mul_mem (inv_mem hc) hgN) hc
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hgx ⊢
      calc c⁻¹ * g * c * x = c⁻¹ * (g * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * g) * c := by rw [hgx]
        _ = x * (c⁻¹ * g * c) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [show c⁻¹ * g * c = (MulAut.conj c⁻¹) g by simp [MulAut.conj_apply], ← map_pow, hn, map_one]
  intro g hg
  have hmem := hle (h (mul_mem (mul_mem hc hg) (inv_mem hc)))
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmem
  have e : c⁻¹ * (c * g * c⁻¹) * c⁻¹⁻¹ = g := by group
  rwa [e] at hmem

theorem uniRootInvariantGeneration_reeGamma
    [IsSimpleGroup ↥(F4.reeGamma K a)] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (A R : Subgroup (ModGL F4.tag K)) (hAΓ : A ≤ F4.reeGamma K a)
    (hA : IsElementaryAbelian p ↥A) (hcard : p ^ 2 ≤ Nat.card A) (hRΓ : R ≤ F4.reeGamma K a)
    (hRp : IsPGroup 2 ↥R) (hR : R ≠ ⊥) (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL F4.tag K))) :
    F4.reeGamma K a ≤ Subgroup.closure (uniCentSetIn (F4.reeGamma K a) A 2) := by
  have := hA
  have := finite_modGL (τ := F4.tag) (K := K)
  obtain ⟨g, hgΓ, j, hAj⟩ := exists_conj_le_reeLocalParabolic hK hAΓ hRΓ hR hRp hAR
  have hA1p : IsPGroup p (A.map (MulAut.conj g).toMonoidHom) :=
    (IsElementaryAbelian.isPGroup p A).map _
  obtain ⟨y, hyP, hyA⟩ := exists_conj_le_levi j hp2 hAj hA1p
  have hxΓ : y * g ∈ F4.reeGamma K a := mul_mem (Subgroup.mem_inf.1 hyP).1 hgΓ
  have hmap : A.map (MulAut.conj (y * g)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  have hAx : A.map (MulAut.conj (y * g)).toMonoidHom ≤
      F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a := hmap ▸ hyA
  have : IsElementaryAbelian p (A.map (MulAut.conj (y * g)).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hcard' : p ^ 2 ≤ Nat.card (A.map (MulAut.conj (y * g)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (y * g)).injective]
    exact hcard
  exact le_closure_uniCentSetIn_of_map_conj hxΓ (reeGamma_le_closure_of_le_levi hK hp2 j hcard' hAx)

end ReeF4Parabolic

theorem uniPlaneGen_of_native {C G : Type*} [Group C] [Group G] {N : Subgroup G} (e : C ≃* N)
    (hZ : Subgroup.center N = ⊥) {r p : ℕ}
    (hgen : ∀ A R : Subgroup G, A ≤ N → IsElementaryAbelian p ↥A → p ^ 2 ≤ Nat.card A → R ≤ N →
      IsPGroup r ↥R → R ≠ ⊥ → A ≤ Subgroup.normalizer (R : Set G) →
      N ≤ Subgroup.closure (uniCentSetIn N A r))
    {E : Subgroup (MulAut C)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hin : E ≤ (MulAut.conj : C →* MulAut C).range)
    (hR : ∃ R : Subgroup C, R ≠ ⊥ ∧ IsPGroup r ↥R ∧ ∀ ε ∈ E, R.map ε.toMonoidHom = R) :
    UniPlaneGen r E := by
  obtain ⟨R, hR1, hRp, hRn⟩ := hR
  have hconj : Function.Injective (MulAut.conj : C →* MulAut C) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hmem : e c ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro n
      obtain ⟨c', rfl⟩ := e.surjective n
      rw [← map_mul, ← map_mul]
      congr 1
      have h1 := DFunLike.congr_fun hc c'
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact e.injective (hmem.trans (map_one e).symm)
  set E₀ : Subgroup C := E.comap (MulAut.conj : C →* MulAut C) with hE₀
  have hEmap : E₀.map (MulAut.conj : C →* MulAut C) = E := Subgroup.map_comap_eq_self hin
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [← hcard, ← hEmap, Subgroup.card_map_of_injective hconj]
  have hE₀el : IsElemAbelian p E₀ := isElemAbelian_comap_of_injective _ hconj hE
  let ι : C →* G := N.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιN : ∀ c, ι c ∈ N := fun c => (e c).2
  set A : Subgroup G := E₀.map ι with hA
  set R' : Subgroup G := R.map ι with hR'
  have hAN : A ≤ N := by
    rintro _ ⟨c, -, rfl⟩
    exact hιN c
  have hR'N : R' ≤ N := by
    rintro _ ⟨c, -, rfl⟩
    exact hιN c
  have hAel : IsElementaryAbelian p ↥A :=
    isElementaryAbelian_of_isElemAbelian (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀el ι)
  have hAcard : p ^ 2 ≤ Nat.card A := by
    rw [hA, Subgroup.card_map_of_injective hι, hE₀card]
  have hR'p : IsPGroup r ↥R' :=
    hRp.of_surjective (ι.subgroupMap R) (ι.subgroupMap_surjective R)
  have hR'1 : R' ≠ ⊥ := fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective R hι).mp h)
  have hnormC : ∀ c ∈ E₀, ∀ x : C, x ∈ R ↔ c * x * c⁻¹ ∈ R := by
    intro c hc x
    have hRc : R.map (MulAut.conj c).toMonoidHom = R := hRn _ hc
    constructor
    · intro hx
      rw [← hRc]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hRc] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        have h2 : c * y * c⁻¹ = c * x * c⁻¹ := hyx
        simpa using h2
      rw [← this]
      exact hy
  have hAnorm : A ≤ Subgroup.normalizer (R' : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨c * x * c⁻¹, (hnormC c hc x).mp hx, by simp [map_mul]⟩
    · rintro ⟨y, hy, hyh⟩
      refine ⟨c⁻¹ * y * c, ?_, ?_⟩
      · have := (hnormC c⁻¹ (E₀.inv_mem hc) y).mp hy
        simpa using this
      · have h2 : ι y = ι c * h * (ι c)⁻¹ := hyh
        have h3 : h = (ι c)⁻¹ * ι y * ι c := by
          rw [h2]
          group
        rw [h3]
        simp [map_mul, map_inv]
  have hgenA := hgen A R' hAN hAel hAcard hR'N hR'p hR'1 hAnorm
  have hle : Subgroup.closure (uniCentSetIn N A r) ≤ (uniPlaneClosure r E).map ι := by
    rw [Subgroup.closure_le]
    rintro g ⟨hgN, _, ⟨x₀, hx₀, rfl⟩, hx1, hgx, n, hn⟩
    obtain ⟨c, hc⟩ : ∃ c : C, ι c = g := ⟨e.symm ⟨g, hgN⟩, by simp [ι]⟩
    refine ⟨c, ?_, hc⟩
    have hx₀1 : x₀ ≠ 1 := fun h => hx1 (by rw [h, map_one])
    refine mem_uniPlaneClosure (e := MulAut.conj x₀) (hx₀ : MulAut.conj x₀ ∈ E) ?_ ?_ (n := n) ?_
    · intro h1
      exact hx₀1 (hconj (by rw [h1, map_one]))
    · have hcx : c * x₀ = x₀ * c := by
        apply hι
        rw [map_mul, map_mul, hc]
        exact hgx
      rw [MulAut.conj_apply, ← hcx, mul_inv_cancel_right]
    · apply hι
      rw [map_pow, hc, hn, map_one]
  rw [UniPlaneGen, eq_top_iff]
  intro c _
  obtain ⟨c', hc', hcc'⟩ := hle (hgenA (hιN c))
  exact (hι hcc') ▸ hc'

section ReeF4Cat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag


theorem uniSeitzPlanes_reeF4_parabolic :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ IsReeF4Index d.1 ∧ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, ⟨m, rfl⟩, R, hR1, hRp, hRn⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, _, hm1, hX, hsimple, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  have : IsSimpleGroup ↥(F4.reeGamma X m) := MulEquiv.isSimpleGroup e.symm
  have h := uniPlaneGen_of_native e (large_Ree_fixed_group_center_trivial m X hX)
    (fun A R hAΓ hA hcard hRΓ hRp hR hAR =>
      uniRootInvariantGeneration_reeGamma hX hp2 A R hAΓ hA hcard hRΓ hRp hR hAR)
    hE hc hin ⟨R, hR1, by simpa using hRp, hRn⟩
  simpa using h

end ReeF4Cat

section ReeF4Outer

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ2


theorem closure_two_pow_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.closure {y : H | ∃ n : ℕ, y ^ (2 ^ n) = 1} = ⊤) :
    Subgroup.closure {x : G | ∃ n : ℕ, x ^ (2 ^ n) = 1} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : e x ∈ Subgroup.closure {y : H | ∃ n : ℕ, y ^ (2 ^ n) = 1} := by
    rw [h]
    exact Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem e.symm.toMonoidHom h1
  rw [MonoidHom.map_closure] at h2
  have h3 : e.symm.toMonoidHom (e x) = x := by simp
  rw [h3] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨y, ⟨n, hy⟩, rfl⟩
  exact ⟨n, by rw [← map_pow, hy, map_one]⟩

theorem fixedSubgroup_reeGammaFieldAut_le_closure {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {β : K ≃+* K}
    (hβ : orderOf β = p) :
    fixedSubgroup (F4.reeGammaFieldAut K a β) ≤
      Subgroup.closure {x | F4.reeGammaFieldAut K a β x = x ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1} := by
  obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ := CFSG.RankThree.PartOne.Sec66T.reeF4_fixed_data_odd hK hp hp2 hβ
  haveI := hchar
  have : Finite (ModGL F4.tag K) := finite_modGL
  have : Finite (ModGL F4.tag (fixSubfield β)) := finite_modGL
  have hfs : fixedSubgroup (F4.reeGammaFieldAut K a β) =
      CFSG.RankThree.PartOne.Sec66T.fixSub (F4.reeGammaFieldAut K a β) :=
    Subgroup.ext fun _ => Iff.rfl
  let eC' : fixedSubgroup (F4.reeGammaFieldAut K a β) ≃* F4.reeGamma (fixSubfield β) b :=
    (MulEquiv.subgroupCongr hfs).trans eC
  refine fixedSubgroup_le_closure_of_closure_two (closure_two_pow_eq_top_of_mulEquiv eC' ?_)
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  ·
    have hk2 : Nat.card (fixSubfield β) = 2 := by rw [hbcard]; norm_num
    refine closure_two_pow_eq_top_of_mulEquiv (reeFixedEquivReeGamma (fixSubfield β) 0).symm ?_
    have : Finite (reeFixed F4 (fixSubfield β) 0) := Subtype.finite
    have hsD : IsSimpleGroup (commutator (reeFixed F4 (fixSubfield β) 0)) :=
      CFSG.Sporadic.Schreier.Tits.commutator_reeFixed_simple hk2
    have hZD := CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot hk2
    have hnaD : ∃ x y : commutator (reeFixed F4 (fixSubfield β) 0), x * y ≠ y * x :=
      exists_noncomm_of_conj_injective (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot hZD)
    exact closure_two_pow_eq_top_of_derived hnaD (isPGroup_reeFixed_quotient (t := F4) rfl hk2)
  ·
    have hs : IsSimpleGroup (F4.reeGamma (fixSubfield β) b) :=
      CFSG.RankThree.PartOne.Sec66T.isSimpleGroup_reeGamma_F4' hb1 hbcard
    have hZ := large_Ree_fixed_group_center_trivial b (fixSubfield β) hbcard
    have hna0 : ∃ x y : F4.reeGamma (fixSubfield β) b, x * y ≠ y * x :=
      exists_noncomm_of_conj_injective (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot hZ)
    rw [eq_top_iff, ← closure_pow_two_eq_top_of_simple hna0]
    exact Subgroup.closure_mono fun x hx => ⟨1, by rw [pow_one]; exact hx⟩

theorem uniPlaneGen_outer_reeF4 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) [IsSimpleGroup ↥(F4.reeGamma K a)] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (E : Subgroup (MulAut ↥(F4.reeGamma K a)))
    [CFSG.IsElementaryAbelian p E] (hc : Nat.card E = p ^ 2) (hout : ¬ ∀ φ ∈ E, ∃ g, φ = MulAut.conj g) :
    UniPlaneGen 2 E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hZ := large_Ree_fixed_group_center_trivial a K hK
  have hnab : ∃ x y : F4.reeGamma K a, x * y ≠ y * x :=
    exists_noncomm_of_conj_injective (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot hZ)
  have hd : FieldAutData (F4.reeGamma K a) p :=
    fieldAutData_reeF4 CFSG.RankThree.PartOne.SEITZRF.subfieldPairReeF4_holds hp hp5 ha hK
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  have hfix : ∀ α : MulAut (F4.reeGamma K a), IsOuterOfOrder p α → p ∣ Nat.card (fixedSubgroup α) →
      fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1} := by
    intro α hα _
    obtain ⟨hord, hout'⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α
    let Θ : MulAut (F4.reeGamma K a) →* (K ≃+* K) :=
      SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
    have hΨα : Ψ ⟨x, β⟩ = α := by rw [hΨ x β]; exact hxβ.symm
    have hΘα : Θ α = β := by
      show SemidirectProduct.rightHom (Ψ.symm α) = β
      rw [← hΨα, MulEquiv.symm_apply_apply]
      rfl
    have hβp : β ^ p = 1 := by rw [← hΘα, ← map_pow, hαp, map_one]
    have hone : F4.reeGammaFieldAut K a 1 = 1 := by
      rw [← reeGammaFieldAutHom_apply, map_one]
    have hβ1 : β ≠ 1 := by
      intro h
      apply hout' x
      rw [h, hone, mul_one] at hxβ
      exact hxβ
    have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
    obtain ⟨g, hg⟩ := RF4.largeRee_fieldAut_coset_conj a hK hp β hβord α hαp ⟨x, hxβ⟩
    have hconj : (MulAut.conj g)⁻¹ * α * (MulAut.conj g)⁻¹⁻¹ = F4.reeGammaFieldAut K a β := by
      rw [hg]
      group
    exact fixedSubgroup_le_closure_pow_of_conj hconj
      (fixedSubgroup_reeGammaFieldAut_le_closure hK hp hp2 hβord)
  exact uniPlaneGen_of_fieldAutData_dvd hnab hp hd hfix E hc hout


theorem uniSeitzPlanes_reeF4_outer :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsReeF4Index d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, hp5, m, rfl⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, _, hm1, hX, hsimple, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  have : IsSimpleGroup ↥(F4.reeGamma X m) := MulEquiv.isSimpleGroup e.symm
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have h := (uniPlaneGen_map_congr e _ E).1 (uniPlaneGen_outer_reeF4 hm1 hX hp hp5 _ hc' hout')
  simpa using h

end ReeF4Outer

section LinearNonCpf

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

section GLBasic

variable {F : Type} [Field F] [Finite F] {n : ℕ}

@[expose] def IsScal (g : GL (Fin n) F) : Prop := ∃ c : F, (g : Matrix (Fin n) (Fin n) F) = c • 1

theorem conjAut_eq_one_iff_isScal (hn : 3 ≤ n) (A : GL (Fin n) F) :
    conjAut n F A = 1 ↔ IsScal A := by
  rw [CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    rw [GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hu := A.isUnit
      rw [show (A : Matrix (Fin n) (Fin n) F) = 0 by rw [hc, zero_smul]] at hu
      have : Nontrivial (Matrix (Fin n) (Fin n) F) := by
        haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
        infer_instance
      exact not_isUnit_zero hu
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, hc]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

theorem IsScal.exists_ne_zero (hn : 0 < n) {g : GL (Fin n) F} (hg : IsScal g) :
    ∃ c : F, c ≠ 0 ∧ (g : Matrix (Fin n) (Fin n) F) = c • 1 := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, ?_, hc⟩
  rintro rfl
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) F => M * ((g⁻¹ : GL (Fin n) F) :
    Matrix (Fin n) (Fin n) F)) hc
  simp only [Units.mul_inv, zero_smul, Matrix.zero_mul] at h1
  have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  simp at h2

end GLBasic

section HeisInvolution

variable {F : Type} [Field F] [Finite F] {n : ℕ}

open Polynomial Module in
theorem eq_one_of_commute_heis [CharP F 2] {p : ℕ} (hp : p.Prime) (hn : n = p)
    (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p) {a b t : GL (Fin n) F} (hbp : IsScal (b ^ p))
    (hab : IsScal ⁅a, b⁆) (hnc : a * b ≠ b * a) (htb : t * b = b * t) (ht2 : t ^ 2 = 1) :
    t = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := hn ▸ hp.pos
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  set A : Matrix (Fin n) (Fin n) F := (a : Matrix (Fin n) (Fin n) F) with hA
  set B : Matrix (Fin n) (Fin n) F := (b : Matrix (Fin n) (Fin n) F) with hB
  set T : Matrix (Fin n) (Fin n) F := (t : Matrix (Fin n) (Fin n) F) with hT
  obtain ⟨c, hc⟩ := hab
  obtain ⟨β, hβ0, hβ⟩ := hbp.exists_ne_zero hn0
  have hBp : B ^ p = β • 1 := by rw [hB, ← Units.val_pow_eq_pow_val, hβ]
  have hrel : A * B = c • (B * A) := by
    have h1 : (⁅a, b⁆ : GL (Fin n) F) * (b * a) = a * b := by
      simp only [commutatorElement_def]; group
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul] at h2
    exact h2.symm
  have hTB : T * B = B * T := by rw [hT, hB, ← Units.val_mul, htb, Units.val_mul]
  have hT2 : T * T = 1 := by
    rw [hT, ← Units.val_mul, ← pow_two, ht2, Units.val_one]
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hnc
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hrel, one_smul]
  have hpowA : ∀ k : ℕ, A * B ^ k = c ^ k • (B ^ k * A) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc A * B ^ (k + 1) = (A * B ^ k) * B := by rw [pow_succ, Matrix.mul_assoc]
        _ = c ^ k • (B ^ k * (A * B)) := by rw [ih, Matrix.smul_mul, Matrix.mul_assoc]
        _ = c ^ (k + 1) • (B ^ (k + 1) * A) := by
            rw [hrel, Matrix.mul_smul, smul_smul, pow_succ c k, pow_succ B k, Matrix.mul_assoc]
  have hA0 : A ≠ 0 := by
    intro h0
    have hu := a.isUnit
    rw [show (a : Matrix (Fin n) (Fin n) F) = 0 from h0] at hu
    have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
    exact not_isUnit_zero hu
  have hcp : c ^ p = 1 := by
    have h1 := hpowA p
    rw [hBp, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at h1
    have h2 : (β * (1 - c ^ p)) • A = 0 := by
      rw [mul_sub, mul_one, sub_smul, h1, mul_comm, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 hβ0
      · exact (sub_eq_zero.1 h4).symm
    · exact absurd h3 hA0
  have hcprim : IsPrimitiveRoot c⁻¹ p := by
    have h1 : c⁻¹ ^ p = 1 := by rw [inv_pow, hcp, inv_one]
    have h2 : c⁻¹ ≠ 1 := fun h => hc1 (by rw [← inv_inv c, h, inv_one])
    have := orderOf_eq_prime h1 h2
    rw [← this]
    exact IsPrimitiveRoot.orderOf _
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hcp
    exact zero_ne_one hcp
  have hrel' : B * A = c⁻¹ • (A * B) := by
    rw [hrel, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hpowB : ∀ k : ℕ, B * A ^ k = c⁻¹ ^ k • (A ^ k * B) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc B * A ^ (k + 1) = (B * A ^ k) * A := by rw [pow_succ, Matrix.mul_assoc]
        _ = c⁻¹ ^ k • (A ^ k * (B * A)) := by rw [ih, Matrix.smul_mul, Matrix.mul_assoc]
        _ = c⁻¹ ^ (k + 1) • (A ^ (k + 1) * B) := by
            rw [hrel', Matrix.mul_smul, smul_smul, pow_succ c⁻¹ k, pow_succ A k, Matrix.mul_assoc]
  have hfinV : Module.finrank F (Fin n → F) = p := by rw [Module.finrank_fin_fun, hn]
  by_cases hsplit : ∃ s : F, s ^ p = β
  ·
    obtain ⟨s, hs⟩ := hsplit
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hs
      exact hβ0 hs.symm
    set B' : Matrix (Fin n) (Fin n) F := s⁻¹ • B with hB'def
    have hB' : B' ^ p = 1 := by
      rw [hB'def, _root_.smul_pow, hBp, smul_smul, inv_pow, hs, inv_mul_cancel₀ hβ0, one_smul]
    obtain ⟨μ, v, hμp, hv0, hB'v⟩ := exists_eigenvector_of_pow_eq_one hp.pos hζ hn0 hB'
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hμp
      exact zero_ne_one hμp
    let u : Fin p → (Fin n → F) := fun k => (A ^ (k : ℕ)).mulVec v
    let lam : Fin p → F := fun k => μ * c⁻¹ ^ (k : ℕ)
    have hlam : Function.Injective lam := by
      intro i j hij
      have h1 : c⁻¹ ^ (i : ℕ) = c⁻¹ ^ (j : ℕ) := mul_left_cancel₀ hμ0 hij
      exact Fin.ext (hcprim.pow_inj i.2 j.2 h1)
    have hBu : ∀ k : Fin p, B'.mulVec (u k) = lam k • u k := by
      intro k
      show (s⁻¹ • B).mulVec ((A ^ (k : ℕ)).mulVec v) = (μ * c⁻¹ ^ (k : ℕ)) • (A ^ (k : ℕ)).mulVec v
      calc (s⁻¹ • B).mulVec ((A ^ (k : ℕ)).mulVec v) = (s⁻¹ • (B * A ^ (k : ℕ))).mulVec v := by
            rw [Matrix.mulVec_mulVec, Matrix.smul_mul]
        _ = (c⁻¹ ^ (k : ℕ) • (A ^ (k : ℕ) * B')).mulVec v := by
            congr 1
            rw [hpowB, hB'def, Matrix.mul_smul]
            exact smul_comm _ _ _
        _ = (μ * c⁻¹ ^ (k : ℕ)) • (A ^ (k : ℕ)).mulVec v := by
            rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hB'v, Matrix.mulVec_smul, smul_smul,
              mul_comm]
    have hu0 : ∀ k : Fin p, u k ≠ 0 := by
      intro k h0
      apply hv0
      have h1 : ((a ^ (k : ℕ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = A ^ (k : ℕ) := by
        rw [Units.val_pow_eq_pow_val]
      have h2 := congrArg (fun w => (((a ^ (k : ℕ))⁻¹ : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F).mulVec w) h0
      simp only [u, Matrix.mulVec_zero] at h2
      rw [← h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec] at h2
      exact h2
    have hli : LinearIndependent F u := by
      refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B') lam hlam u fun k => ?_
      refine Module.End.hasEigenvector_iff.2 ⟨?_, hu0 k⟩
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact hBu k
    have : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
    have hcard : Fintype.card (Fin p) = Module.finrank F (Fin n → F) := by
      rw [Fintype.card_fin, hfinV]
    let 𝔅 : Basis (Fin p) F (Fin n → F) := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have h𝔅 : ∀ k, 𝔅 k = u k := fun k => by
      simp [𝔅, coe_basisOfLinearIndependentOfCardEqFinrank]
    have heig : ∀ (k : Fin p) (w : Fin n → F), B'.mulVec w = lam k • w → ∃ σ : F, w = σ • u k := by
      intro k w hw
      obtain ⟨r, hr⟩ : ∃ r : Fin p → F, r = 𝔅.repr w := ⟨_, rfl⟩
      have hw' : w = ∑ j, r j • u j := by
        rw [hr]
        conv_lhs => rw [← 𝔅.sum_repr w]
        simp only [h𝔅]
      have h1 : ∑ j, (r j * (lam j - lam k)) • u j = 0 := by
        have h2 : B'.mulVec w - lam k • w = 0 := by rw [hw, sub_self]
        rw [hw', Matrix.mulVec_sum, Finset.smul_sum, ← Finset.sum_sub_distrib] at h2
        rw [← h2]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.mulVec_smul, hBu j]
        module
      have h3 := Fintype.linearIndependent_iff.1 hli _ h1
      refine ⟨r k, ?_⟩
      rw [hw', Finset.sum_eq_single k]
      · intro j _ hjk
        have h4 := h3 j
        rcases mul_eq_zero.1 h4 with h5 | h5
        · rw [h5, zero_smul]
        · exact absurd (hlam (sub_eq_zero.1 h5)) hjk
      · intro h; exact absurd (Finset.mem_univ k) h
    have hTB' : T * B' = B' * T := by
      rw [hB'def, Matrix.mul_smul, Matrix.smul_mul, hTB]
    have hTu : ∀ k : Fin p, T.mulVec (u k) = u k := by
      intro k
      have hw : B'.mulVec (T.mulVec (u k)) = lam k • T.mulVec (u k) := by
        rw [Matrix.mulVec_mulVec, ← hTB', ← Matrix.mulVec_mulVec, hBu k, Matrix.mulVec_smul]
      obtain ⟨σ, h1⟩ := heig k _ hw
      have h2 : T.mulVec (T.mulVec (u k)) = u k := by
        rw [Matrix.mulVec_mulVec, hT2, Matrix.one_mulVec]
      rw [h1, Matrix.mulVec_smul, h1, smul_smul] at h2
      have h3 : (σ * σ - 1) • u k = 0 := by rw [sub_smul, h2, one_smul, sub_self]
      have h4 : σ * σ = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (hu0 k))
      have h5 : (σ - 1) * (σ - 1) = 0 := by linear_combination h4 - σ * h2F + h2F
      have h6 : σ = 1 := sub_eq_zero.1 (mul_self_eq_zero.1 h5)
      rw [h1, h6, one_smul]
    have hTone : T = 1 := by
      have h1 : Matrix.toLin' T = Matrix.toLin' 1 := 𝔅.ext fun k => by
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h𝔅, hTu k, Matrix.one_mulVec]
      exact Matrix.toLin'.injective h1
    exact Units.ext (by rw [Units.val_one]; exact hTone)
  ·
    push Not at hsplit
    have hirr : Irreducible (X ^ p - C β : F[X]) := X_pow_sub_C_irreducible_of_prime hp hsplit
    set N : Matrix (Fin n) (Fin n) F := T - 1 with hN
    let Cs : Submodule F (Fin n → F) := LinearMap.ker (Matrix.toLin' N)
    have hmemC : ∀ w, w ∈ Cs ↔ T.mulVec w = w := fun w => by
      simp [Cs, LinearMap.mem_ker, Matrix.toLin'_apply, hN, Matrix.sub_mulVec, sub_eq_zero]
    have hBC : ∀ w ∈ Cs, Matrix.toLin' B w ∈ Cs := by
      intro w hw
      rw [hmemC] at hw ⊢
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hTB, ← Matrix.mulVec_mulVec, hw]
    have hN2 : N * N = 0 := by
      have hTT : T + T = 0 := by rw [← two_smul F T, h2F, zero_smul]
      have h11 : (1 : Matrix (Fin n) (Fin n) F) + 1 = 0 := by
        rw [← two_smul F (1 : Matrix (Fin n) (Fin n) F), h2F, zero_smul]
      calc N * N = (1 + 1) - (T + T) := by
            rw [hN, sub_mul, mul_sub, mul_sub, hT2, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul]
            abel
        _ = 0 := by rw [hTT, h11, sub_zero]
    have hCne : Cs ≠ ⊥ := by
      intro h0
      have hinj : Function.Injective (Matrix.toLin' N) := by
        rw [← LinearMap.ker_eq_bot]
        exact h0
      have hz : Matrix.toLin' N ∘ₗ Matrix.toLin' N = 0 := by
        rw [← Matrix.toLin'_mul, hN2, map_zero]
      have : Nontrivial (Fin n → F) := by
        have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
        infer_instance
      obtain ⟨w, hw0⟩ := exists_ne (0 : Fin n → F)
      apply hw0
      apply hinj
      apply hinj
      rw [map_zero, map_zero, ← LinearMap.comp_apply, hz, LinearMap.zero_apply]
    have hCnt : Nontrivial Cs := Submodule.nontrivial_iff_ne_bot.2 hCne
    set bC : Module.End F Cs := (Matrix.toLin' B).restrict hBC with hbC
    have haeval : aeval bC (X ^ p - C β : F[X]) = 0 := by
      rw [map_sub, map_pow, aeval_X, aeval_C, hbC, Module.End.pow_restrict]
      refine LinearMap.ext fun x => Subtype.ext ?_
      obtain ⟨w, hw⟩ := x
      simp only [LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.zero_apply,
        Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_zero, LinearMap.restrict_coe_apply]
      rw [← Matrix.toLin'_pow, hBp, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec,
        sub_self]
    have hmin : (X ^ p - C β : F[X]) = minpoly F bC :=
      minpoly.eq_of_irreducible_of_monic hirr haeval (monic_X_pow_sub_C β hp.ne_zero)
    have hdeg : p ≤ Module.finrank F Cs := by
      have h1 := LinearMap.minpoly_dvd_charpoly bC
      have h2 := Polynomial.natDegree_le_of_dvd h1 (LinearMap.charpoly_monic bC).ne_zero
      rw [← hmin, natDegree_X_pow_sub_C, LinearMap.charpoly_natDegree] at h2
      exact h2
    have htop : Cs = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have := Submodule.finrank_le Cs
      omega
    have hTone : T = 1 := by
      rw [Matrix.ext_iff_mulVec]
      intro w
      rw [Matrix.one_mulVec]
      exact (hmemC w).1 (htop ▸ Submodule.mem_top)
    exact Units.ext (by rw [Units.val_one]; exact hTone)

end HeisInvolution

section InnDiag

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem pow_card_sub_one_of_mem_scalars {z : Matrix.SpecialLinearGroup (Fin n) F}
    (hz : z ∈ scalars n F) : z ^ (Nat.card F - 1) = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hz
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hc, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
    ← Units.val_pow_eq_pow_val, ← Nat.card_units, pow_card_eq_one', Units.val_one, map_one]

theorem odd_natCard_sub_one_of_charTwo [CharP F 2] : Odd (Nat.card F - 1) := by
  have := Fintype.ofFinite F
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hk]
  have h1 : 1 ≤ 2 ^ (k : ℕ) := Nat.one_le_two_pow
  exact Nat.Even.sub_odd h1 (Nat.even_pow.2 ⟨even_two, k.ne_zero⟩) odd_one

theorem exists_gl_involution_of_fixed [CharP F 2] {b : GL (Fin n) F} {s : projectiveSL n F}
    (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1) (hfix : conjAut n F b s = s) :
    ∃ t : GL (Fin n) F, t ≠ 1 ∧ t ^ 2 = 1 ∧ t * b = b * t := by
  obtain ⟨g₀, rfl⟩ := proj_surjective n F s
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.card F - 1 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ := odd_natCard_sub_one_of_charTwo (F := F)
  have hmk : m = 2 * k + 1 := hm.trans hk
  have hsq : g₀ ^ 2 ∈ scalars n F := by
    rw [← proj_eq_one_iff, map_pow]; exact hs2
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = g₀ ^ m := ⟨_, rfl⟩
  have hg₁2 : g₁ ^ 2 = 1 := by
    rw [hg₁, ← pow_mul, mul_comm, pow_mul, hm, pow_card_sub_one_of_mem_scalars hsq]
  have hpg₁ : proj n F g₁ = proj n F g₀ := by
    rw [hg₁, map_pow, hmk, pow_succ, pow_mul, hs2, one_pow, one_mul]
  have hg₁1 : g₁ ≠ 1 := fun h => hs1 (by rw [← hpg₁, h, map_one])
  obtain ⟨w, hw⟩ : ∃ w, w = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F b g₁ :=
    ⟨_, rfl⟩
  have hpw : proj n F w = proj n F g₁ := by
    rw [hw, ← conjAut_proj, hpg₁, hfix]
  have hz : w⁻¹ * g₁ ∈ scalars n F := proj_eq_proj_iff.1 hpw
  have hw2 : w ^ 2 = 1 := by rw [hw, ← map_pow, hg₁2, map_one]
  have hzc : ∀ g, Commute (w⁻¹ * g₁) g := fun g => by
    have := (scalars_eq_center n F) ▸ hz
    exact (Subgroup.mem_center_iff.1 this g).symm
  have hz2 : (w⁻¹ * g₁) ^ 2 = 1 := by
    have h1 : (w⁻¹ * g₁) ^ 2 = w⁻¹ ^ 2 * g₁ ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      calc w⁻¹ * g₁ * (w⁻¹ * g₁) = w⁻¹ * (g₁ * (w⁻¹ * g₁)) := by simp only [mul_assoc]
        _ = w⁻¹ * ((w⁻¹ * g₁) * g₁) := by rw [← (hzc g₁).eq]
        _ = w⁻¹ * w⁻¹ * (g₁ * g₁) := by simp only [mul_assoc]
    rw [h1, hg₁2, inv_pow, hw2, inv_one, one_mul]
  have hzm : (w⁻¹ * g₁) ^ m = 1 := by rw [hm]; exact pow_card_sub_one_of_mem_scalars hz
  have hz1 : w⁻¹ * g₁ = 1 := by
    have : (w⁻¹ * g₁) ^ m = (w⁻¹ * g₁) := by
      rw [hmk, pow_succ, pow_mul, hz2, one_pow, one_mul]
    rw [← this, hzm]
  have hwg : w = g₁ := by
    have := congrArg (fun x => w * x) hz1
    simpa using this.symm
  refine ⟨Matrix.SpecialLinearGroup.toGL g₁, fun h => hg₁1 ?_, ?_, ?_⟩
  · exact Matrix.SpecialLinearGroup.toGL_injective (by rw [h, map_one])
  · rw [← map_pow, hg₁2, map_one]
  · apply Units.ext
    have hm' : (b : Matrix (Fin n) (Fin n) F) * g₁ * ((b⁻¹ : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = g₁ := by
      rw [← coe_slConjugation, ← hw, hwg]
    have hbinv : ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    show ((Matrix.SpecialLinearGroup.toGL g₁ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * b =
      b * ((Matrix.SpecialLinearGroup.toGL g₁ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    change (g₁ : Matrix (Fin n) (Fin n) F) * b = b * g₁
    calc (g₁ : Matrix (Fin n) (Fin n) F) * b
        = ((b : Matrix (Fin n) (Fin n) F) * g₁ * ((b⁻¹ : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) F)) * b := by rw [hm']
      _ = b * g₁ := by rw [Matrix.mul_assoc, hbinv, Matrix.mul_one]

theorem uniPlaneGen_psl_nonCpf [CharP F 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card F = 2 ^ f) (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ n)
    (hpq : p ∣ Nat.card F - 1) {E : Subgroup (MulAut (projectiveSL n F))}
    (hE : CFSG.Open.IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hns : ∃ e ∈ E, e ≠ 1 ∧ ¬ IsSolvable ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup e)) :
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.UniPlaneGen 2 E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  rcases Inputs256e.uniPlaneGen_or_heis Nat.prime_two hf hK hn hp hp2 hp2 hpn hpq hE hc with
    h | ⟨hD, hnp, A, B, hA, hB, hAB⟩
  · exact h
  exfalso
  have hζ := exists_primitiveRoot_of_dvd_card_sub_one hp hpq
  obtain ⟨e₁, he₁E, he₁1, hns⟩ := hns
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero 2 hp.ne_zero)
  have hord : orderOf e₁ = p := orderOf_eq_prime (hE.2 _ he₁E) he₁1
  obtain ⟨e₂, he₂E, he₂⟩ : ∃ e₂ ∈ E, e₂ ∉ Subgroup.zpowers e₁ := by
    by_contra h
    push Not at h
    have hle : E ≤ Subgroup.zpowers e₁ := fun x hx => h x hx
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hord, hc] at this
    have h1 := hp.one_lt
    nlinarith
  have hcomm₁₂ : Commute e₁ e₂ :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨e₁, he₁E⟩ ⟨e₂, he₂E⟩)
  obtain ⟨hel, hcard⟩ := Inputs256e.sup_zpowers_facts hp hcomm₁₂ (hE.2 _ he₁E) (hE.2 _ he₂E) he₁1 he₂
  have hle : Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ ≤ E :=
    sup_le (Subgroup.zpowers_le.2 he₁E) (Subgroup.zpowers_le.2 he₂E)
  have hgen : Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ = E :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hc])
  obtain ⟨b, rfl⟩ := mem_linearAutGroup_iff.mp (hD he₁E)
  obtain ⟨a, rfl⟩ := mem_linearAutGroup_iff.mp (hD he₂E)
  have hnc : a * b ≠ b * a := fun h => hAB (Inputs256e.lifts_commute_of_commute hn hgen h.symm hA hB)
  have hbp : IsScal (b ^ p) := by
    rw [← conjAut_eq_one_iff_isScal hn, map_pow]; exact hE.2 _ he₁E
  have hab : IsScal ⁅a, b⁆ := by
    rw [← conjAut_eq_one_iff_isScal hn, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hcomm₁₂.symm.eq
  apply hns
  by_contra hsolv
  have h2 : 2 ∣ Nat.card ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (conjAut n F b)) := by
    by_contra hodd
    exact hsolv (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hs1 : (s : projectiveSL n F) ≠ 1 := by
    intro h
    have : s = 1 := Subtype.ext h
    rw [this, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hs2 : (s : projectiveSL n F) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hs, pow_orderOf_eq_one, Subgroup.coe_one]
  have hfix : conjAut n F b (s : projectiveSL n F) = s :=
    CFSG.RankThree.PartOne.CTP.mem_fixedSubgroup.1 s.2
  obtain ⟨t, ht1, ht2, htb⟩ := exists_gl_involution_of_fixed hs1 hs2 hfix
  exact ht1 (eq_one_of_commute_heis hp hnp hζ hbp hab hnc htb ht2)

end InnDiag

end LinearNonCpf

section LinearNonCpfCat

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem isSolvable_fixedSubgroup_of_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (ε : MulAut G) (h : IsSolvable ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (MulAut.congr e ε))) :
    IsSolvable ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup ε) := by
  let ψ : CFSG.RankThree.PartOne.CTP.fixedSubgroup ε →* CFSG.RankThree.PartOne.CTP.fixedSubgroup (MulAut.congr e ε) :=
    { toFun := fun x => ⟨e (x : G), by
        rw [CFSG.RankThree.PartOne.CTP.mem_fixedSubgroup]
        change e (ε (e.symm (e (x : G)))) = e (x : G)
        rw [MulEquiv.symm_apply_apply, CFSG.RankThree.PartOne.CTP.mem_fixedSubgroup.1 x.2]⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' := fun x y => Subtype.ext (map_mul e (x : G) (y : G)) }
  exact @Group.isSolvable_of_isSolvable_injective _ _ _ _ ψ
    (fun x y hxy => Subtype.ext (e.injective (congrArg Subtype.val hxy))) h

theorem uniSeitzPlanes_linear_nonCpf :
    UniSeitzPlanes fun d p E => IsLinearIndex d.1 ∧ d.1.characteristic = 2 ∧ 5 ≤ p ∧
      ¬ CentralPrimeFree p d.1 ∧
        ∃ e ∈ E, e ≠ 1 ∧ ¬ IsSolvable ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup e) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨⟨m, q, hd⟩, hch, hp5, hncpf, hns⟩
  subst hd
  have hq2 : q.p = 2 := by simpa using hch
  have hlift : p ∣ q.card - 1 ∧ p ∣ m + 1 := by simpa [CentralPrimeFree] using hncpf
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let e : Cat ⟨.A m q, hv⟩ ≃* projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hKq : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', hq2]
  have : CharP (GaloisField q.p q.exponent) 2 := by
    rw [← hq2]; infer_instance
  have hm5 : 5 ≤ m + 1 := hp5.trans (Nat.le_of_dvd (by omega) hlift.2)
  have hE'el : IsElemAbelian p (E.map (MulAut.congr e).toMonoidHom) := isElemAbelian_map_congr e hE
  have hE'c : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := (card_map_congr e E).trans hc
  have hns' : ∃ ε ∈ E.map (MulAut.congr e).toMonoidHom, ε ≠ 1 ∧
      ¬ IsSolvable ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup ε) := by
    obtain ⟨ε, hεE, hε1, hεs⟩ := hns
    refine ⟨MulAut.congr e ε, ⟨ε, hεE, rfl⟩, fun h => hε1 ?_, fun hs => hεs ?_⟩
    · exact (MulAut.congr e).injective (h.trans (map_one _).symm)
    · exact isSolvable_fixedSubgroup_of_congr e ε hs
  have h := uniPlaneGen_psl_nonCpf q.exponent_pos hKq (by omega) hp hp5 hlift.2
    (by rw [hcardF]; exact hlift.1) hE'el hE'c hns'
  have h' := (uniPlaneGen_map_congr e _ E).1 h
  simpa [hq2] using h'

variable {X : Type} [Group X] [Finite X]

theorem isSolvable_inf_centralizer_of_fixed {Q : Type*} [Group Q] {K : Subgroup X}
    (θ : (↥K ⧸ Subgroup.center ↥K) ≃* Q) {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X))
    (h : IsSolvable ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup ((MulAut.congr θ) (Inputs2323b.centerQuotAct K ⟨b, hb⟩)))) :
    IsSolvable ↥(K ⊓ Subgroup.centralizer ({b} : Set X)) := by
  set ε := (MulAut.congr θ) (Inputs2323b.centerQuotAct K ⟨b, hb⟩) with hε
  have hK1 : ∀ k : ↥(K ⊓ Subgroup.centralizer ({b} : Set X)), (k : X) ∈ K := fun k =>
    (Subgroup.mem_inf.1 k.2).1
  have hmem : ∀ k : ↥(K ⊓ Subgroup.centralizer ({b} : Set X)),
      θ (QuotientGroup.mk (⟨k, hK1 k⟩ : ↥K)) ∈ CFSG.RankThree.PartOne.CTP.fixedSubgroup ε := by
    intro k
    rw [CFSG.RankThree.PartOne.CTP.mem_fixedSubgroup, hε]
    change θ (Inputs2323b.centerQuotAct K ⟨b, hb⟩ (θ.symm (θ (QuotientGroup.mk (⟨k, hK1 k⟩ : ↥K))))) =
      θ (QuotientGroup.mk (⟨k, hK1 k⟩ : ↥K))
    rw [MulEquiv.symm_apply_apply, Inputs2323b.centerQuotAct_mk]
    congr 2
    apply Subtype.ext
    show b * (k : X) * b⁻¹ = k
    have hc : (k : X) * b = b * k :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 k.2).2
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  let φ : ↥(K ⊓ Subgroup.centralizer ({b} : Set X)) →* ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup ε) :=
    { toFun := fun k => ⟨_, hmem k⟩
      map_one' := Subtype.ext (by
        show θ (QuotientGroup.mk (1 : ↥K)) = 1
        rw [QuotientGroup.mk_one, map_one])
      map_mul' := fun x y => Subtype.ext (by
        show θ (QuotientGroup.mk ((⟨x, hK1 x⟩ : ↥K) * ⟨y, hK1 y⟩)) =
          θ (QuotientGroup.mk ⟨x, hK1 x⟩) * θ (QuotientGroup.mk ⟨y, hK1 y⟩)
        rw [QuotientGroup.mk_mul, map_mul]) }
  have hker : ∀ x y : ↥φ.ker, x * y = y * x := by
    intro x y
    have hx : (⟨(x : X), hK1 x⟩ : ↥K) ∈ Subgroup.center ↥K := by
      have h1 : φ x = 1 := x.2
      have h2 : θ (QuotientGroup.mk (⟨(x : X), hK1 x⟩ : ↥K)) = 1 := congrArg Subtype.val h1
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h2
      exact h2
    have h3 := Subgroup.mem_center_iff.1 hx ⟨(y : X), hK1 y⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg Subtype.val h3).symm
  exact Group.isSolvable_of_ker_le_range (hG' := isSolvable_of_comm hker) (hG'' := h)
    φ.ker.subtype φ (by rw [Subgroup.range_subtype])

theorem input23_11TwoOn_of_uniSeitzPlanes_ns
    {S : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (MulAut (Cat d)) → Prop}
    (hU : UniSeitzPlanes S) {R : ℕ → TauCeti.LieTypeIndex → Prop}
    (hRS : ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → 5 ≤ p → R p d.1 →
      d.1.characteristic = 2 → ∀ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E →
        Nat.card E = p ^ 2 → (∃ e ∈ E, e ≠ 1 ∧ ¬ IsSolvable ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup e)) → S d p E) :
    Inputs2323b.Input23_11TwoOn R := by
  intro p hp hp5 X _ _ K B hK d hR hchar he hBel hBc hBN hfaith hexc hns
  obtain ⟨θ⟩ := he
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hEel, hEcard⟩ := Inputs2323b.isElemAbelian_card_map_centerQuotAct hK hBel hBc hBN hfaith θ
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1 := by
    rintro (⟨hp3, -⟩ | ⟨hp5', hd⟩)
    · omega
    · apply hexc hp5'
      rcases hd with hd | hd
      · exact Or.inl ⟨d, hd, ⟨θ⟩⟩
      · exact Or.inr (Or.inr ⟨d, hd, ⟨θ⟩⟩)
  have hpd : p ≠ d.1.characteristic := by rw [hchar]; exact hp2
  have hnsE : ∃ e ∈ (B.subgroupOf (Subgroup.normalizer (K : Set X))).map
      ((MulAut.congr θ).toMonoidHom.comp (Inputs2323b.centerQuotAct K)), e ≠ 1 ∧
        ¬ IsSolvable ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup e) := by
    obtain ⟨b, hbB, hb1, hbs⟩ := hns
    have hbN : b ∈ Subgroup.normalizer (K : Set X) := hBN hbB
    refine ⟨(MulAut.congr θ) (Inputs2323b.centerQuotAct K ⟨b, hbN⟩),
      ⟨⟨b, hbN⟩, Subgroup.mem_subgroupOf.2 hbB, rfl⟩, ?_, fun hs => hbs ?_⟩
    · intro h1
      apply hb1
      have h2 : Inputs2323b.centerQuotAct K ⟨b, hbN⟩ = 1 := by
        rwa [MulEquiv.map_eq_one_iff] at h1
      have h3 : K.normalizerMonoidHom ⟨b, hbN⟩ = 1 :=
        quotientCenterAut'_injective hK.1 (by rw [map_one]; exact h2)
      have h4 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (K : Set X))) ∈ K.normalizerMonoidHom.ker := h3
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h4
      have h5 : b ∈ B ⊓ Subgroup.centralizer (K : Set X) := ⟨hbB, h4⟩
      rw [hfaith] at h5
      exact h5
    · exact isSolvable_inf_centralizer_of_fixed θ hbN hs
  have hgen := hU d p hp hp2 hpd hex _ hEel hEcard (hRS d p hp hp5 hR hchar _ hEel hEcard hnsE)
  rw [hchar] at hgen
  exact Inputs2323b.eq_iSup_oPrimeResidualOf_of_uniPlaneGen hK hBN hp hp2 hBel.2 θ hgen

theorem input23_11TwoOn_linear_nonCpf :
    Inputs2323b.Input23_11TwoOn fun p d => d.characteristic = 2 ∧ ¬ CentralPrimeFree p d ∧
      IsLinearIndex d :=
  input23_11TwoOn_of_uniSeitzPlanes_ns uniSeitzPlanes_linear_nonCpf fun _ _ _ hp5 hR hch _ _ _ hns =>
    ⟨hR.2.2, hch, hp5, hR.2.1, hns⟩

theorem input23_11TwoNonCpf_of_unitary
    (h : Inputs2323b.Input23_11TwoOn fun p d => d.characteristic = 2 ∧ ¬ CentralPrimeFree p d ∧
      IsUnitaryIndex' d) : Inputs2323b.Input23_11TwoNonCpf := by
  refine Inputs2323b.Input23_11TwoOn.mono (fun p d hd => ?_)
    (Inputs2323b.input23_11TwoOn_or input23_11TwoOn_linear_nonCpf h)
  obtain ⟨hc, hcpf⟩ := hd
  cases d with
  | A m q => exact Or.inl ⟨hc, hcpf, ⟨m, q, rfl⟩⟩
  | twistedA m q => exact Or.inr ⟨hc, hcpf, ⟨m, q, rfl⟩⟩
  | _ => exact absurd trivial hcpf

end LinearNonCpfCat

@[expose] def Input23_11TwoRest2 : Prop :=
  Inputs2311c.UniSeitzPlanes (fun d p E => d.1.characteristic = 2 ∧ 5 ≤ p ∧ CentralPrimeFree p d.1 ∧
      InnerPlane d p E ∧
      (IsChevalleyExcIndex d.1 ∨ (IsReeF4Index d.1 ∧ ¬ (p = 5 ∧ d.1 = TauCeti.LieTypeIndex.reeF4 2))) ∧
        ¬ NormalizesRSubgroup d E) ∧
    Inputs2323b.Input23_11TwoOn fun p d => d.characteristic = 2 ∧ ¬ CentralPrimeFree p d ∧
      IsUnitaryIndex' d

@[expose] def Input23_23NRest2 : Prop :=
  Input23_11TwoRest2 ∧ Inputs2323b.Input14_1BadRest

section Assembly


theorem uni23_11TwoCpfRest_of_rest2
    (hTor : ∀ {ℓ f n p : ℕ} {K : Type} [Field K] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K),
      p.Prime → p ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
      ∀ (E : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1))),
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
        Subgroup.closure {g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1) |
          ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} = ⊤)
    (hNS : ∀ {ℓ f p n : ℕ} {K : Type} [Field K] (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K),
      p.Prime → 5 ≤ p → p ≠ ℓ → ¬ p ∣ ℓ ^ f + 1 → ¬ p ∣ ℓ ^ f - 1 → 3 ≤ n →
      ∀ (E : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K n)),
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
        Subgroup.closure {g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K n |
          ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} = ⊤)
    (hSpOut : UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsSymplecticIndex d.1)
    (hOrthOut : UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsOrthogonalIndex d.1)
    (hF4E78Out : UniSeitzPlanes fun d p E =>
      ¬ InnerPlane d p E ∧ (IsF4Index d.1 ∨ IsE7Index d.1 ∨ IsE8Index d.1))
    (hE6Out : UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsE6Index d.1 ∧ 5 ≤ p)
    (hTwE6Out : UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsTwistedE6Index d.1)
    (hD4Out : UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsTrialityIndex d.1)
    (h : Input23_11TwoRest2) : Inputs2323b.Uni23_11TwoCpfRest := by
  have hSp := UniSeitzPlanes.of_cover (S := fun d p E => 5 ≤ p ∧ IsSymplecticIndex d.1)
    (fun d p _ _ E ⟨hp5, hsp⟩ => by
      by_cases hin : InnerPlane d p E
      · exact Or.inl ⟨hin, hp5, hsp⟩
      · exact Or.inr ⟨hin, hsp⟩) uniSeitzPlanes_symplectic_inner_five hSpOut
  have hU := UniSeitzPlanes.of_cover (S := fun d p E => d.1.characteristic = 2 ∧ 5 ≤ p ∧
      IsUnitaryIndex' d.1 ∧ CentralPrimeFree p d.1)
    (fun d p _ _ E ⟨hc, hp5, hu, hcpf⟩ => by
      by_cases hin : InnerPlane d p E
      · exact Or.inl ⟨hin, hp5, hu, hcpf⟩
      · exact Or.inr ⟨hin, hu, hcpf, hc, hp5⟩)
    (uniSeitzPlanes_unitary_inner_five hTor hNS) uniSeitzPlanes_unitary_outer_even
  have hOut := UniSeitzPlanes.of_cover (S := fun d p E => ¬ InnerPlane d p E ∧ d.1.characteristic = 2 ∧ 5 ≤ p ∧
      (IsOrthogonalIndex d.1 ∨ IsChevalleyExcIndex d.1 ∨ IsReeF4Index d.1))
    (fun d p _ _ E ⟨hout, hc, hp5, hfam⟩ => by
      rcases hfam with ho | ((hG | hF | hE6 | hE7 | hE8) | (hD4 | hTw)) | hR4
      · exact Or.inl ⟨hout, hp5, ho⟩
      · exact Or.inr (Or.inl ⟨hout, hG, hc, hp5⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hout, Or.inl hF⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hout, hE6, hp5⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨hout, Or.inr (Or.inl hE7)⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hout, Or.inr (Or.inr hE8)⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hout, hp5, hD4⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hout, hp5, hTw⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hout, hp5, hR4⟩))))))
    hOrthOut (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_G2_outer_even
      (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) hF4E78Out
        (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) hE6Out
          (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) hTwE6Out
            (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) hD4Out uniSeitzPlanes_reeF4_outer)))))
  have hPar := UniSeitzPlanes.of_cover (S := fun d p E => InnerPlane d p E ∧
      (IsChevalleyExcIndex d.1 ∨ IsReeF4Index d.1) ∧ NormalizesRSubgroup d E)
    (fun d p _ _ E ⟨hin, hfam, hR⟩ => by
      rcases hfam with hx | hx
      · exact Or.inl ⟨hin, hx, hR⟩
      · exact Or.inr ⟨hin, hx, hR⟩) uniSeitzPlanes_excParabolic uniSeitzPlanes_reeF4_parabolic
  refine UniSeitzPlanes.of_cover (fun d p hp hp2 E hE => ?_)
    (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) hSp
      (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) hU
        (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) hOut
          (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) hPar orthSq_uniSeitzPlanes_orthogonal)))) h.1
  obtain ⟨hc, hp5, hcpf, hlin, hsz, hti, hexc⟩ := hE
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have key : ∀ (hfam : IsOrthogonalIndex d ∨ IsChevalleyExcIndex d ∨
      (IsReeF4Index d ∧ ¬ (p = 5 ∧ d = TauCeti.LieTypeIndex.reeF4 2))),
      (5 ≤ p ∧ IsSymplecticIndex d ∨ (d.characteristic = 2 ∧ 5 ≤ p ∧ IsUnitaryIndex' d ∧
        CentralPrimeFree p d) ∨ (¬ InnerPlane ⟨d, hv⟩ p E ∧ d.characteristic = 2 ∧ 5 ≤ p ∧
          (IsOrthogonalIndex d ∨ IsChevalleyExcIndex d ∨ IsReeF4Index d)) ∨
        (InnerPlane ⟨d, hv⟩ p E ∧ (IsChevalleyExcIndex d ∨ IsReeF4Index d) ∧
          NormalizesRSubgroup ⟨d, hv⟩ E) ∨
        (InnerPlane ⟨d, hv⟩ p E ∧ 5 ≤ p ∧ IsOrthogonalIndex d)) ∨
      (d.characteristic = 2 ∧ 5 ≤ p ∧ CentralPrimeFree p d ∧ InnerPlane ⟨d, hv⟩ p E ∧
        (IsChevalleyExcIndex d ∨ (IsReeF4Index d ∧ ¬ (p = 5 ∧ d = TauCeti.LieTypeIndex.reeF4 2))) ∧
          ¬ NormalizesRSubgroup ⟨d, hv⟩ E) := by
    intro hfam
    by_cases hin : InnerPlane ⟨d, hv⟩ p E
    · rcases hfam with ho | hx | hx
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨hin, hp5, ho⟩))))
      · by_cases hR : NormalizesRSubgroup ⟨d, hv⟩ E
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hin, Or.inl hx, hR⟩))))
        · exact Or.inr ⟨hc, hp5, hcpf, hin, Or.inl hx, hR⟩
      · by_cases hR : NormalizesRSubgroup ⟨d, hv⟩ E
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hin, Or.inr hx.1, hR⟩))))
        · exact Or.inr ⟨hc, hp5, hcpf, hin, Or.inr hx, hR⟩
    · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨hin, hc, hp5, ?_⟩)))
      rcases hfam with ho | hx | hx
      · exact Or.inl ho
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx.1)
  cases d with
  | A r q => exact absurd ⟨r, q, rfl⟩ hlin
  | twistedA r q => exact Or.inl (Or.inr (Or.inl ⟨hc, hp5, ⟨r, q, rfl⟩, hcpf⟩))
  | B r q =>
    have hq2 : q.p = 2 := by simpa using hc
    have hsp : IsSymplecticIndex (.B r q) := by
      rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
      · exact Or.inl ⟨q, rfl⟩
      · exact Or.inr (Or.inl ⟨r, q, rfl, hr3, hq2⟩)
    exact Or.inl (Or.inl ⟨hp5, hsp⟩)
  | C r q =>
    have hq2 : q.p = 2 := by simpa using hc
    exact absurd hq2 hrange.2
  | D r q => exact key (Or.inl (Or.inr (Or.inl ⟨r, q, rfl⟩)))
  | twistedD r q => exact key (Or.inl (Or.inr (Or.inr ⟨r, q, rfl⟩)))
  | E6 q => exact key (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))))
  | E7 q => exact key (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))))))
  | E8 q => exact key (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩)))))))
  | F4 q => exact key (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl ⟨q, rfl⟩)))))
  | G2 q => exact key (Or.inr (Or.inl (Or.inl (Or.inl ⟨q, rfl⟩))))
  | twistedE6 q => exact key (Or.inr (Or.inl (Or.inr (Or.inr ⟨q, rfl⟩))))
  | trialityD4 q => exact key (Or.inr (Or.inl (Or.inr (Or.inl ⟨q, rfl⟩))))
  | suzuki m => exact absurd rfl (hsz m)
  | reeG2 m => simp at hc
  | reeF4 m => exact key (Or.inr (Or.inr ⟨⟨m, rfl⟩, hexc⟩))
  | tits => exact absurd rfl hti

theorem input23_11TwoRest_of_rest2
    (hTor : ∀ {ℓ f n p : ℕ} {K : Type} [Field K] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K),
      p.Prime → p ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
      ∀ (E : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1))),
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
        Subgroup.closure {g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1) |
          ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} = ⊤)
    (hNS : ∀ {ℓ f p n : ℕ} {K : Type} [Field K] (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K),
      p.Prime → 5 ≤ p → p ≠ ℓ → ¬ p ∣ ℓ ^ f + 1 → ¬ p ∣ ℓ ^ f - 1 → 3 ≤ n →
      ∀ (E : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K n)),
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
        Subgroup.closure {g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K n |
          ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} = ⊤)
    (hSpOut : UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsSymplecticIndex d.1)
    (hOrthOut : UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsOrthogonalIndex d.1)
    (hF4E78Out : UniSeitzPlanes fun d p E =>
      ¬ InnerPlane d p E ∧ (IsF4Index d.1 ∨ IsE7Index d.1 ∨ IsE8Index d.1))
    (hE6Out : UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsE6Index d.1 ∧ 5 ≤ p)
    (hTwE6Out : UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsTwistedE6Index d.1)
    (hD4Out : UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsTrialityIndex d.1)
    (h : Input23_11TwoRest2) : Inputs2323b.Input23_11TwoRest :=
  Inputs2323b.input23_11TwoRest_of_uni
    (uni23_11TwoCpfRest_of_rest2 hTor hNS hSpOut hOrthOut hF4E78Out hE6Out hTwE6Out hD4Out h)
    (input23_11TwoNonCpf_of_unitary h.2)

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311e
