module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Group
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicSpecial

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.RankThree.PartOne

section Irreducible

variable {f : ℕ} {E : Type} [Field E]

theorem eq_top_of_invariant_gramSU (hE : UnitaryFieldData 2 f E) (hf : 2 ^ f = 2) {m : ℕ}
    (hm : 2 ≤ m) (F : Submodule E (Fin m → E))
    (hF : ∀ A ∈ gramSU hE (1 : Matrix (Fin m) (Fin m) E), ∀ v ∈ F,
      (A : Matrix (Fin m) (Fin m) E) *ᵥ v ∈ F)
    {v : Fin m → E} (hv : v ∈ F) (hv0 : v ≠ 0) : F = ⊤ := by
  classical
  have h2 : (2 : E) = 0 := by
    have := hE.charP
    exact CharP.cast_eq_zero E 2
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  obtain ⟨j, hji⟩ : ∃ j : Fin m, j ≠ i := by
    by_cases h0 : i = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, fun h => by rw [h0] at h; exact absurd (congrArg Fin.val h) (by simp)⟩
    · exact ⟨⟨0, by omega⟩, fun h => h0 h.symm⟩
  have hij : i ≠ j := hji.symm
  obtain ⟨c, hc, hc2⟩ := KCUnitary.exists_norm_one_sq_ne_one hE (by rw [hf])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact zero_ne_one hc
  have hci : hE.bar c⁻¹ * c⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hc, inv_one]
  obtain ⟨A₁, hA₁, hA₁g⟩ := unitLambdaDiag_mem hE hc hij
  obtain ⟨A₂, hA₂, hA₂g⟩ := unitLambdaDiag_mem hE hci hij
  have hw₁ := F.sub_mem (hF A₁ hA₁g v hv) hv
  have hw₂ := F.sub_mem (hF A₂ hA₂g v hv) hv
  rw [hA₁] at hw₁
  rw [hA₂] at hw₂
  set κ : E := (c - 1) * (c - 1) - (c⁻¹ - 1) * (c⁻¹ - 1) with hκ
  have hκ0 : κ ≠ 0 := by
    intro h0
    have h3 : (c - c⁻¹) * (c + c⁻¹) = 0 := by
      have : (c - c⁻¹) * (c + c⁻¹ - 2) = κ := by rw [hκ]; ring
      rw [h2, sub_zero] at this
      rw [this, h0]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · apply hc2
      have : c = c⁻¹ := sub_eq_zero.1 h4
      calc c ^ 2 = c * c := sq c
        _ = c * c⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel₀ hc0
    · apply hc2
      have h5 : c * (c + c⁻¹) = 0 := by rw [h4, mul_zero]
      have h6 : c ^ 2 + 1 = 0 := by
        have : c * (c + c⁻¹) = c ^ 2 + 1 := by field_simp
        rw [← this, h5]
      have h7 : (1 : E) + 1 = 0 := by
        have : (2 : E) = 1 + 1 := by norm_num
        rw [← this, h2]
      calc c ^ 2 = c ^ 2 + 1 - 1 := by ring
        _ = -1 := by rw [h6]; ring
        _ = 1 := by
          have := eq_neg_of_add_eq_zero_left h7
          exact this.symm
  have hu : (c - 1) • ((diagonal (unitLambdaDiag c i j)) *ᵥ v - v) -
      (c⁻¹ - 1) • ((diagonal (unitLambdaDiag c⁻¹ i j)) *ᵥ v - v) =
        (κ * v i) • Pi.single i (1 : E) := by
    funext r
    simp only [Pi.sub_apply, Pi.smul_apply, mulVec_diagonal, smul_eq_mul, unitLambdaDiag]
    by_cases hri : r = i
    · subst hri
      simp [hκ]
      ring
    · by_cases hrj : r = j
      · subst hrj
        simp [hri]
        ring
      · simp [hri, hrj]
  have hmem : (κ * v i) • (Pi.single i (1 : E) : Fin m → E) ∈ F := by
    rw [← hu]
    exact F.sub_mem (F.smul_mem _ hw₁) (F.smul_mem _ hw₂)
  have hei : (Pi.single i (1 : E) : Fin m → E) ∈ F := by
    have := F.smul_mem (κ * v i)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hκ0 hi), one_smul] at this
  have hek : ∀ k : Fin m, (Pi.single k (1 : E) : Fin m → E) ∈ F := by
    intro k
    by_cases hk : k = i
    · rw [hk]; exact hei
    · obtain ⟨M, hM, hMg⟩ := unitSignedSwapMatrix_mem hE (Ne.symm hk)
      have := hF M hMg _ hei
      rw [hM, unitSignedSwapMatrix_mulVec] at this
      convert this using 1
      funext r
      simp only [unitSignedSwap]
      by_cases hrk : r = k
      · subst hrk
        simp [hk]
      · have : Equiv.swap i k r ≠ i := by
          intro h
          apply hrk
          have := (Equiv.swap_apply_eq_iff.1 h)
          simpa [Equiv.swap_apply_left] using this
        simp [hrk, Pi.single_apply, this]
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine F.sum_mem fun k _ => ?_
  have : (Pi.single k (w k) : Fin m → E) = w k • Pi.single k (1 : E) := by
    funext r
    simp [Pi.single_apply]
  rw [this]
  exact F.smul_mem _ (hek k)

theorem noNormalPPrime_three_gramSU (hE : UnitaryFieldData 2 f E) (hf : 2 ^ f = 2) {m : ℕ}
    (hm : 2 ≤ m)
    (hord : Nat.card (gramSU hE (1 : Matrix (Fin m) (Fin m) E)) ∣ 2 ^ 3 * 3 ^ 3) :
    NoNormalPPrime 3 (gramSU hE (1 : Matrix (Fin m) (Fin m) E)) := by
  classical
  intro N hNS hNn hNc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card N ∣ 2 ^ 3 * 3 ^ 3 := (Subgroup.card_dvd_of_le hNS).trans hord
  have hN2 : Nat.card N ∣ 2 ^ 3 :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right 3 hNc.symm) hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hN2
  have hpg : IsPGroup 2 N := IsPGroup.of_card hj
  letI : MulAction N (Fin m → E) := MulAction.compHom (Fin m → E)
    ((Matrix.GeneralLinearGroup.toLin : GL (Fin m) E ≃* _).toMonoidHom.comp N.subtype)
  have hsmul : ∀ (n : N) (v : Fin m → E),
      n • v = ((n : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ v := fun n v => rfl
  have : Finite E := hE.finite
  have hcardE : Nat.card E = 4 := by
    rw [hE.card, pow_mul', hf]
    norm_num
  have hpα : 2 ∣ Nat.card (Fin m → E) := by
    rw [Nat.card_pi]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    rw [hcardE]
    exact dvd_pow (by norm_num : 2 ∣ 4) (by omega)
  have h0 : (0 : Fin m → E) ∈ MulAction.fixedPoints N (Fin m → E) := fun n =>
    (hsmul n 0).trans (mulVec_zero _)
  obtain ⟨b, hb, hb0⟩ := hpg.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin m → E) hpα h0
  let F : Submodule E (Fin m → E) :=
    { carrier := {v | ∀ n : N, ((n : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ v = v}
      add_mem' := fun {a b} ha hb n => by rw [mulVec_add, ha n, hb n]
      zero_mem' := fun n => by simp
      smul_mem' := fun c v hv n => by rw [mulVec_smul, hv n] }
  have hbF : b ∈ F := fun n => by rw [← hsmul]; exact hb n
  have hFtop : F = ⊤ := by
    refine eq_top_of_invariant_gramSU hE hf hm F ?_ hbF (Ne.symm hb0)
    intro A hA v hv n
    obtain ⟨n, hn⟩ := n
    have hn' : (A⁻¹ * n * A⁻¹⁻¹ : GL (Fin m) E) ∈ N :=
      hNn A⁻¹ ((gramSU hE (1 : Matrix (Fin m) (Fin m) E)).inv_mem hA) n hn
    have h1 : (n : Matrix (Fin m) (Fin m) E) * (A : Matrix (Fin m) (Fin m) E) =
        (A : Matrix (Fin m) (Fin m) E) *
          ((A⁻¹ * n * A⁻¹⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    show (n : Matrix (Fin m) (Fin m) E) *ᵥ ((A : Matrix (Fin m) (Fin m) E) *ᵥ v) =
      (A : Matrix (Fin m) (Fin m) E) *ᵥ v
    rw [mulVec_mulVec, h1, ← mulVec_mulVec]
    have := hv ⟨_, hn'⟩
    simp only at this
    rw [this]
  refine (Subgroup.eq_bot_iff_forall N).2 fun n hn => ?_
  have hall : ∀ v : Fin m → E, ((n : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ v = v := by
    intro v
    have : v ∈ F := by rw [hFtop]; trivial
    exact this ⟨n, hn⟩
  apply Units.ext
  ext r s
  have := congrFun (hall (Pi.single s 1)) r
  simpa [mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

end Irreducible

section Abstract

variable {f : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 f E) (hf : 2 ^ f = 2)
  {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
  {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)

include hf hHf hHfl in
theorem card_sesqSpecialUnitaryGroup_int {n : ℕ} (hn : Module.finrank E W = n) (hn1 : 1 ≤ n) :
    (Nat.card (sesqSpecialUnitaryGroup Hf) : ℤ) =
      2 ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, ((2 : ℤ) ^ i - (-1) ^ i) := by
  have := (CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl hn hn1).2.1
  rw [hf] at this
  simpa using this

include hf hHf hHfl in
theorem card_sesqSpecialUnitaryGroup_dvd (hm : Module.finrank E W = 2 ∨ Module.finrank E W = 3) :
    Nat.card (sesqSpecialUnitaryGroup Hf) ∣ 2 ^ 3 * 3 ^ 3 := by
  rcases hm with hm | hm
  · have := card_sesqSpecialUnitaryGroup_int hE hf hHf hHfl hm (by norm_num)
    have h6 : Nat.card (sesqSpecialUnitaryGroup Hf) = 6 := by
      have : (Nat.card (sesqSpecialUnitaryGroup Hf) : ℤ) = 6 := by
        rw [this]; decide
      exact_mod_cast this
    rw [h6]; norm_num
  · have := card_sesqSpecialUnitaryGroup_int hE hf hHf hHfl hm (by norm_num)
    have h216 : Nat.card (sesqSpecialUnitaryGroup Hf) = 216 := by
      have : (Nat.card (sesqSpecialUnitaryGroup Hf) : ℤ) = 216 := by
        rw [this]; decide
      exact_mod_cast this
    rw [h216]; norm_num

include hf hHf hHfl in
theorem three_dvd_card_sesqSpecialUnitaryGroup {n : ℕ} (hn : Module.finrank E W = n)
    (hn2 : 2 ≤ n) : 3 ∣ Nat.card (sesqSpecialUnitaryGroup Hf) := by
  have h := card_sesqSpecialUnitaryGroup_int hE hf hHf hHfl hn (by omega)
  have h3 : (3 : ℤ) ∣ (Nat.card (sesqSpecialUnitaryGroup Hf) : ℤ) := by
    rw [h]
    refine Dvd.dvd.mul_left ?_ _
    have h2 : (2 : ℕ) ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨le_rfl, hn2⟩
    exact (by norm_num : (3 : ℤ) ∣ (2 : ℤ) ^ 2 - (-1) ^ 2).trans
      (Finset.dvd_prod_of_mem (fun i : ℕ => (2 : ℤ) ^ i - (-1) ^ i) h2)
  exact_mod_cast h3

include hf hHf hHfl in
theorem pow_three_eq_one_of_central (hm : 2 ≤ Module.finrank E W)
    {x : LinearMap.GeneralLinearGroup E W} (hx : x ∈ sesqSpecialUnitaryGroup Hf)
    (hc : ∀ δ ∈ sesqSpecialUnitaryGroup Hf, δ * x = x * δ) : x ^ 3 = 1 := by
  have hq2 : 2 ≤ 2 ^ f := by rw [hf]
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
  have hbar : hE.bar c = c ^ 2 := by rw [hE.bar_apply, hf]
  have hc3 : c ^ 3 = 1 := by
    rw [hbar] at hu
    calc c ^ 3 = c ^ 2 * c := by ring
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
  rw [hpow 3 w, hc3, one_smul]
  rfl

include hf hHf hHfl in
theorem noNormalPPrime_three_sesqSpecial_of_four_le (h4 : 4 ≤ Module.finrank E W) :
    NoNormalPPrime 3 (sesqSpecialUnitaryGroup Hf) := by
  have hq := KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl (by omega)
    ⟨fun h => by omega, fun h => by omega⟩
  intro N hNS hNn hNc
  set N0 : Subgroup ↥(sesqSpecialUnitaryGroup Hf) := N.subgroupOf (sesqSpecialUnitaryGroup Hf)
    with hN0
  have hN0n : N0.Normal := ⟨fun x hx g => by
    rw [hN0, Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hNn g g.2 x hx⟩
  have hcard : Nat.card N0 = Nat.card N := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNS).toEquiv
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN0n with htop | hcen
  · exfalso
    have h3 : 3 ∣ Nat.card N := by
      rw [← hcard, htop, Subgroup.card_top]
      exact three_dvd_card_sesqSpecialUnitaryGroup hE hf hHf hHfl rfl (by omega)
    exact absurd (Nat.Coprime.eq_one_of_dvd hNc h3) (by norm_num)
  · refine (Subgroup.eq_bot_iff_forall N).2 fun x hx => ?_
    have hxS : x ∈ sesqSpecialUnitaryGroup Hf := hNS hx
    have hxc : (⟨x, hxS⟩ : ↥(sesqSpecialUnitaryGroup Hf)) ∈ Subgroup.center _ :=
      hcen (Subgroup.mem_subgroupOf.2 hx)
    rw [Subgroup.mem_center_iff] at hxc
    have hx3 := pow_three_eq_one_of_central hE hf hHf hHfl (by omega) hxS
      (fun δ hδ => congrArg Subtype.val (hxc ⟨δ, hδ⟩))
    have hdvd3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have hdvdN : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
    have h1 : orderOf x = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvdN hNc.symm) hdvd3
    exact orderOf_eq_one_iff.1 h1

include hf hHf hHfl in
theorem noNormalPPrime_three_sesqSpecialUnitaryGroup :
    NoNormalPPrime 3 (sesqSpecialUnitaryGroup Hf) := by
  classical
  by_cases h1 : Module.finrank E W ≤ 1
  · intro N hNS _ _
    refine (Subgroup.eq_bot_iff_forall N).2 fun x hx => ?_
    exact KCSpIsotypic.eq_one_of_det_eq_one_of_finrank_le_one h1 x
      (mem_sesqSpecialUnitaryGroup.1 (hNS hx)).2
  by_cases h4 : 4 ≤ Module.finrank E W
  · exact noNormalPPrime_three_sesqSpecial_of_four_le hE hf hHf hHfl h4
  have hm23 : Module.finrank E W = 2 ∨ Module.finrank E W = 3 := by omega
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hHf hHfl
  have heG : ∀ i j, Hf (e i) (e j) =
      (1 : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E) i j := fun i j => by
    rw [he, Matrix.one_apply]
  obtain ⟨ψ⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE e heG
  have hord : Nat.card (gramSU hE (1 : Matrix (Fin (Module.finrank E W))
      (Fin (Module.finrank E W)) E)) ∣ 2 ^ 3 * 3 ^ 3 := by
    rw [← Nat.card_congr ψ.toEquiv]
    exact card_sesqSpecialUnitaryGroup_dvd hE hf hHf hHfl hm23
  have hgram := noNormalPPrime_three_gramSU hE hf (by omega) hord
  rw [← noNormalPPrime_top_iff] at hgram ⊢
  exact noNormalPPrime_top_of_mulEquiv ψ hgram

include hf hHf hHfl in
theorem noNormalPPrime_three_sesqUnitaryGroup :
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
  refine noNormalPPrime_top_of_ker (CFSG.LinearGroups.unitaryDet Hf) ⟨1, ?_⟩ ?_
  · rw [hcard, hf]
    norm_num
  · rw [hker, ← noNormalPPrime_map_iff (sesqUnitaryGroup Hf).subtype
      (sesqUnitaryGroup Hf).subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 (sesqSpecialUnitaryGroup_le Hf)]
    exact noNormalPPrime_three_sesqSpecialUnitaryGroup hE hf hHf hHfl

end Abstract

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
