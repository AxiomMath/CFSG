module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.Arith
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Group
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicSpecial
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

section Symplectic

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K]

theorem charP_two_of_card_eight (hK : Nat.card K = 8) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 3) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)

theorem center_statedSp_eq_bot_of_charP_two [CharP K 2] (n : ℕ) :
    Subgroup.center (StatedSp n K) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]

theorem three_dvd_card_statedSp_eight (hK : Nat.card K = 8) {s : ℕ} (hs : 1 ≤ s) :
    3 ∣ Nat.card (StatedSp s K) := by
  rw [SymplecticFlag.card_statedSp, hK]
  refine Dvd.dvd.mul_left ?_ _
  have h1 : 1 ∈ Finset.Icc 1 s := Finset.mem_Icc.2 ⟨le_rfl, hs⟩
  exact (by norm_num : 3 ∣ 8 ^ (2 * 1) - 1).trans
    (Finset.dvd_prod_of_mem (fun j => 8 ^ (2 * j) - 1) h1)

theorem noNormalPPrime_three_statedSp_eight (hK : Nat.card K = 8) (s : ℕ) :
    NoNormalPPrime 3 (⊤ : Subgroup (StatedSp s K)) := by
  have : CharP K 2 := charP_two_of_card_eight hK
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · intro N _ _ _
    haveI : Subsingleton (StatedSp 0 K) :=
      ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => by
        rcases i with i | i <;> exact i.elim0))⟩
    exact Subgroup.eq_bot_of_subsingleton N
  · have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs
      (Or.inl (Or.inr (by rw [hK]; norm_num)))
    intro N _ hNn hNc
    haveI hNnorm : N.Normal := ⟨fun x hx g => by simpa using hNn g (Subgroup.mem_top g) x hx⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNnorm with htop | hcen
    · exfalso
      have h3 : 3 ∣ Nat.card N := by
        rw [htop, Subgroup.card_top]
        exact three_dvd_card_statedSp_eight hK hs
      exact absurd (Nat.Coprime.eq_one_of_dvd hNc h3) (by norm_num)
    · rw [center_statedSp_eq_bot_of_charP_two s] at hcen
      exact le_bot_iff.1 hcen

theorem noNormalPPrime_three_sesqUnitaryGroup_alt_eight (hK : Nat.card K = 8) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {B : LinearMap.BilinForm K W}
    (hB : B.IsAlt) (hn : B.Nondegenerate) :
    NoNormalPPrime 3 (⊤ : Subgroup (sesqUnitaryGroup B)) := by
  obtain ⟨s, -, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  exact W2.noNormalPPrime_top_of_mulEquiv e (noNormalPPrime_three_statedSp_eight hK s)

end Symplectic

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix CFSG.RankThree.PartOne

variable {f : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 f E) (hf : 2 ^ f = 8)
  {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
  {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)

include hf hHf hHfl in
theorem card_sesqSpecialUnitaryGroup_int_eight {n : ℕ} (hn : Module.finrank E W = n)
    (hn1 : 1 ≤ n) :
    (Nat.card (sesqSpecialUnitaryGroup Hf) : ℤ) =
      8 ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, ((8 : ℤ) ^ i - (-1) ^ i) := by
  have := (CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl hn hn1).2.1
  rw [hf] at this
  simpa using this

include hf hHf hHfl in
theorem three_dvd_card_sesqSpecialUnitaryGroup_eight {n : ℕ} (hn : Module.finrank E W = n)
    (hn2 : 2 ≤ n) : 3 ∣ Nat.card (sesqSpecialUnitaryGroup Hf) := by
  have h := card_sesqSpecialUnitaryGroup_int_eight hE hf hHf hHfl hn (by omega)
  have h3 : (3 : ℤ) ∣ (Nat.card (sesqSpecialUnitaryGroup Hf) : ℤ) := by
    rw [h]
    refine Dvd.dvd.mul_left ?_ _
    have h2 : (2 : ℕ) ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨le_rfl, hn2⟩
    exact (by norm_num : (3 : ℤ) ∣ (8 : ℤ) ^ 2 - (-1) ^ 2).trans
      (Finset.dvd_prod_of_mem (fun i : ℕ => (8 : ℤ) ^ i - (-1) ^ i) h2)
  exact_mod_cast h3

include hf hHf hHfl in
theorem pow_nine_eq_one_of_central (hm : 2 ≤ Module.finrank E W)
    {x : LinearMap.GeneralLinearGroup E W} (hx : x ∈ sesqSpecialUnitaryGroup Hf)
    (hc : ∀ δ ∈ sesqSpecialUnitaryGroup Hf, δ * x = x * δ) : x ^ 9 = 1 := by
  have hq2 : 2 ≤ 2 ^ f := by rw [hf]; norm_num
  obtain ⟨c, hcx⟩ := KCUnitary.exists_smul_of_commute_special_unitary hE hHf hHfl hm hq2
    (x : Module.End E W) (fun δ hδ => by
      have := congrArg (fun g : LinearMap.GeneralLinearGroup E W => (g : Module.End E W)) (hc δ hδ)
      exact (by simpa using this : (δ : Module.End E W) * x = x * δ).symm)
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hHf hHfl
  let w₀ : W := e ⟨0, by omega⟩
  have hw₀ : Hf w₀ w₀ = 1 := by simp [w₀, he]
  have hu := mem_sesqUnitaryGroup.1 (sesqSpecialUnitaryGroup_le Hf hx) w₀ w₀
  change Hf ((x : Module.End E W) w₀) ((x : Module.End E W) w₀) = Hf w₀ w₀ at hu
  have hcc : Hf (c • w₀) (c • w₀) = hE.bar c * (c * Hf w₀ w₀) := by
    simp [LinearMap.map_smulₛₗ]
    ring
  rw [hcx w₀, hcc, hw₀] at hu
  simp only [mul_one] at hu
  have hbar : hE.bar c = c ^ 8 := by rw [hE.bar_apply, hf]
  have hc9 : c ^ 9 = 1 := by
    rw [hbar] at hu
    calc c ^ 9 = c ^ 8 * c := by ring
      _ = 1 := hu
  have hpow : ∀ n : ℕ, ∀ w, ((x ^ n : LinearMap.GeneralLinearGroup E W) : Module.End E W) w =
      c ^ n • w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih, map_smul, hcx, smul_smul, pow_succ]
  refine Units.ext (LinearMap.ext fun w => ?_)
  rw [hpow 9 w, hc9, one_smul]
  rfl

include hf hHf hHfl in
theorem noNormalPPrime_three_sesqSpecialUnitaryGroup_eight :
    NoNormalPPrime 3 (sesqSpecialUnitaryGroup Hf) := by
  classical
  by_cases h1 : Module.finrank E W ≤ 1
  · intro N hNS _ _
    refine (Subgroup.eq_bot_iff_forall N).2 fun x hx => ?_
    exact KCSpIsotypic.eq_one_of_det_eq_one_of_finrank_le_one h1 x
      (mem_sesqSpecialUnitaryGroup.1 (hNS hx)).2
  have h2 : 2 ≤ Module.finrank E W := by omega
  have hq := KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl h2
    ⟨fun _ => by rw [hf]; norm_num, fun _ => by rw [hf]; norm_num⟩
  intro N hNS hNn hNc
  set N0 : Subgroup ↥(sesqSpecialUnitaryGroup Hf) := N.subgroupOf (sesqSpecialUnitaryGroup Hf)
    with hN0
  have hN0n : N0.Normal := ⟨fun x hx g => by
    rw [hN0, Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hNn g g.2 x hx⟩
  have hcard : Nat.card N0 = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNS).toEquiv
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN0n with htop | hcen
  · exfalso
    have h3 : 3 ∣ Nat.card N := by
      rw [← hcard, htop, Subgroup.card_top]
      exact three_dvd_card_sesqSpecialUnitaryGroup_eight hE hf hHf hHfl rfl h2
    exact absurd (Nat.Coprime.eq_one_of_dvd hNc h3) (by norm_num)
  · refine (Subgroup.eq_bot_iff_forall N).2 fun x hx => ?_
    have hxS : x ∈ sesqSpecialUnitaryGroup Hf := hNS hx
    have hxc : (⟨x, hxS⟩ : ↥(sesqSpecialUnitaryGroup Hf)) ∈ Subgroup.center _ :=
      hcen (Subgroup.mem_subgroupOf.2 hx)
    rw [Subgroup.mem_center_iff] at hxc
    have hx9 := pow_nine_eq_one_of_central hE hf hHf hHfl h2 hxS
      (fun δ hδ => congrArg Subtype.val (hxc ⟨δ, hδ⟩))
    have hdvd9 : orderOf x ∣ 3 ^ 2 := by
      norm_num
      exact orderOf_dvd_of_pow_eq_one hx9
    have hdvdN : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
    have hcop : Nat.Coprime (orderOf x) (3 ^ 2) :=
      Nat.Coprime.pow_right 2 (Nat.Coprime.coprime_dvd_left hdvdN hNc.symm)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd9)

include hf hHf hHfl in
theorem noNormalPPrime_three_sesqUnitaryGroup_eight :
    NoNormalPPrime 3 (⊤ : Subgroup (sesqUnitaryGroup Hf)) := by
  classical
  by_cases h0 : Module.finrank E W = 0
  · have : Subsingleton W := Module.finrank_zero_iff.1 h0
    intro N _ _ _
    haveI : Subsingleton (sesqUnitaryGroup Hf) :=
      ⟨fun a b => Subtype.ext (Units.ext (LinearMap.ext fun w => Subsingleton.elim _ _))⟩
    exact Subgroup.eq_bot_of_subsingleton N
  have hn1 : 1 ≤ Module.finrank E W := Nat.one_le_iff_ne_zero.2 h0
  obtain ⟨-, -, -, hcard, hker, -⟩ :=
    CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl hn1
  refine W2.noNormalPPrime_top_of_ker (CFSG.LinearGroups.unitaryDet Hf) ⟨2, ?_⟩ ?_
  · rw [hcard, hf]
    norm_num
  · rw [hker, ← W2.noNormalPPrime_map_iff (sesqUnitaryGroup Hf).subtype
      (sesqUnitaryGroup Hf).subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 (sesqSpecialUnitaryGroup_le Hf)]
    exact noNormalPPrime_three_sesqSpecialUnitaryGroup_eight hE hf hHf hHfl

end Unitary

end CFSG.HardMathSupport.Dickson.Bal207

end
