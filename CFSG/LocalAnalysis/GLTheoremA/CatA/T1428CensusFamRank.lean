module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CtxHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcRankInn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem exists_elemAbelian_ge_27_of_commuting {X : Type} [Group X] [Finite X] {x₁ x₂ x₃ : X}
    (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃) (c23 : Commute x₂ x₃)
    (hind : ∀ e₁ e₂ e₃ : ℤ, x₁ ^ e₁ * x₂ ^ e₂ * x₃ ^ e₃ = 1 →
      (3 : ℤ) ∣ e₁ ∧ (3 : ℤ) ∣ e₂ ∧ (3 : ℤ) ∣ e₃) :
    ∃ Ω : Subgroup X, IsElemAbelian 3 Ω ∧ 27 ≤ Nat.card Ω := by
  classical
  let θf : (Fin 3 → ℤ) → X := fun n => x₁ ^ n 0 * x₂ ^ n 1 * x₃ ^ n 2
  have hθmul : ∀ n m : Fin 3 → ℤ, θf (n + m) = θf n * θf m := by
    intro n m
    simp only [θf, Pi.add_apply, zpow_add]
    have h1 : Commute (x₃ ^ n 2) (x₁ ^ m 0) := (c13.zpow_zpow (m 0) (n 2)).symm
    have h2 : Commute (x₂ ^ n 1) (x₁ ^ m 0) := (c12.zpow_zpow (m 0) (n 1)).symm
    have h3 : Commute (x₃ ^ n 2) (x₂ ^ m 1) := (c23.zpow_zpow (m 1) (n 2)).symm
    calc x₁ ^ n 0 * x₁ ^ m 0 * (x₂ ^ n 1 * x₂ ^ m 1) * (x₃ ^ n 2 * x₃ ^ m 2)
        = x₁ ^ n 0 * (x₁ ^ m 0 * x₂ ^ n 1) * x₂ ^ m 1 * x₃ ^ n 2 * x₃ ^ m 2 := by group
      _ = x₁ ^ n 0 * (x₂ ^ n 1 * x₁ ^ m 0) * x₂ ^ m 1 * x₃ ^ n 2 * x₃ ^ m 2 := by rw [h2.eq]
      _ = x₁ ^ n 0 * x₂ ^ n 1 * x₁ ^ m 0 * (x₂ ^ m 1 * x₃ ^ n 2) * x₃ ^ m 2 := by group
      _ = x₁ ^ n 0 * x₂ ^ n 1 * x₁ ^ m 0 * (x₃ ^ n 2 * x₂ ^ m 1) * x₃ ^ m 2 := by rw [h3.eq]
      _ = x₁ ^ n 0 * x₂ ^ n 1 * (x₁ ^ m 0 * x₃ ^ n 2) * x₂ ^ m 1 * x₃ ^ m 2 := by group
      _ = x₁ ^ n 0 * x₂ ^ n 1 * (x₃ ^ n 2 * x₁ ^ m 0) * x₂ ^ m 1 * x₃ ^ m 2 := by rw [h1.eq]
      _ = x₁ ^ n 0 * x₂ ^ n 1 * x₃ ^ n 2 * (x₁ ^ m 0 * x₂ ^ m 1 * x₃ ^ m 2) := by group
  let θ : Multiplicative (Fin 3 → ℤ) →* X :=
    { toFun := fun n => θf (Multiplicative.toAdd n)
      map_one' := by simp [θf]
      map_mul' := fun a b => hθmul _ _ }
  have hθ : ∀ n : Fin 3 → ℤ, θ (Multiplicative.ofAdd n) = x₁ ^ n 0 * x₂ ^ n 1 * x₃ ^ n 2 :=
    fun _ => rfl
  set A := θ.range with hA
  have hAc : ∀ a b : A, a * b = b * a := by
    rintro ⟨_, n, rfl⟩ ⟨_, m, rfl⟩
    apply Subtype.ext
    change θ n * θ m = θ m * θ n
    rw [← map_mul, ← map_mul, mul_comm n m]
  let pw : A →* A :=
    { toFun := fun a => a ^ 3
      map_one' := one_pow _
      map_mul' := fun a b => (show Commute a b from hAc a b).mul_pow 3 }
  have hθ3 : ∀ n : Fin 3 → ℤ, θ (Multiplicative.ofAdd n) ^ 3 =
      θ (Multiplicative.ofAdd ((3 : ℤ) • n)) := by
    intro n
    rw [← map_pow]
    congr 1
  let emb : (Fin 3 → Fin 3) → A ⧸ pw.range := fun e =>
    ((⟨θ (Multiplicative.ofAdd fun i => ((e i : ℕ) : ℤ)), ⟨_, rfl⟩⟩ : A) : A ⧸ pw.range)
  have hemb : Function.Injective emb := by
    intro e e' hee
    simp only [emb, QuotientGroup.eq] at hee
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := hee
    have hn' := congrArg Subtype.val hn
    simp only [pw, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_pow, Subgroup.coe_mul,
      Subgroup.coe_inv] at hn'
    obtain ⟨n, rfl⟩ := Multiplicative.ofAdd.surjective n
    rw [hθ3, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add] at hn'
    have h1 : θ (Multiplicative.ofAdd ((3 : ℤ) • n - (-(fun i => ((e i : ℕ) : ℤ)) +
        fun i => ((e' i : ℕ) : ℤ)))) = 1 := by
      rw [sub_eq_add_neg, ofAdd_add, map_mul, hn', ofAdd_neg, map_inv, mul_inv_cancel]
    rw [hθ] at h1
    obtain ⟨d0, d1, d2⟩ := hind _ _ _ h1
    funext i
    apply Fin.ext
    have key : ∀ j : Fin 3, (3 : ℤ) ∣ (3 : ℤ) * n j - (-((e j : ℕ) : ℤ) + ((e' j : ℕ) : ℤ)) := by
      intro j
      fin_cases j
      · simpa using d0
      · simpa using d1
      · simpa using d2
    have hi := key i
    have hi' : (3 : ℤ) ∣ ((e' i : ℕ) : ℤ) - ((e i : ℕ) : ℤ) := by
      have h3 : (3 : ℤ) ∣ (3 : ℤ) * n i := dvd_mul_right 3 _
      have := dvd_sub h3 hi
      simpa [sub_sub_cancel_left, sub_eq_add_neg, add_comm] using this
    have he := (e i).isLt
    have he' := (e' i).isLt
    omega
  have hquot : 27 ≤ Nat.card (A ⧸ pw.range) := by
    have h := Nat.card_le_card_of_injective emb hemb
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h
    norm_num at h
    exact h
  have hker : Nat.card pw.ker = Nat.card (A ⧸ pw.range) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup pw.ker
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup pw.range
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange pw).toEquiv] at h1
    have hpos : 0 < Nat.card pw.range := Nat.card_pos
    rw [h1, mul_comm] at h2
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  set Ω := pw.ker.map A.subtype with hΩ
  have hΩcard : Nat.card Ω = Nat.card pw.ker := by
    rw [hΩ, Subgroup.card_map_of_injective A.subtype_injective]
  have hΩexp : ∀ x ∈ Ω, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : a ^ 3 = 1 := ha
    simpa using congrArg Subtype.val h1
  have hΩel : IsElemAbelian 3 Ω := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, hΩexp⟩
    obtain ⟨a', -, ha'⟩ := a.2
    obtain ⟨b', -, hb'⟩ := b.2
    apply Subtype.ext
    change (a : X) * b = b * a
    rw [← ha', ← hb']
    exact congrArg Subtype.val (hAc a' b')
  exact ⟨Ω, hΩel, by rw [hΩcard, hker]; exact hquot⟩

private theorem mk_eq_one_of_commute_three {X : Type*} [Group X] {J : Subgroup X} {z : X}
    (hz : z ∈ J) (hc : ∀ y ∈ J, z * y = y * z) :
    ((⟨z, hz⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact (hc y y.2).symm

private theorem exists_elemAbelian_ge_27_of_components {X : Type} [Group X] [Finite X]
    {C J₁ J₂ J₃ : Subgroup X} (h1 : IsComponentOf J₁ C) (h2 : IsComponentOf J₂ C)
    (h3 : IsComponentOf J₃ C) (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃)
    {x₁ : ↥J₁} {x₂ : ↥J₂} {x₃ : ↥J₃}
    (hx₁ : orderOf (x₁ : ↥J₁ ⧸ Subgroup.center ↥J₁) = 3)
    (hx₂ : orderOf (x₂ : ↥J₂ ⧸ Subgroup.center ↥J₂) = 3)
    (hx₃ : orderOf (x₃ : ↥J₃ ⧸ Subgroup.center ↥J₃) = 3) :
    ∃ Ω : Subgroup X, IsElemAbelian 3 Ω ∧ 27 ≤ Nat.card Ω := by
  have hcomm : ∀ {A B : Subgroup X}, IsComponentOf A C → IsComponentOf B C → A ≠ B →
      ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro A B hA hB hAB a ha b hb
    exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hA hB hAB ha hb
  have c12 : Commute (x₁ : X) x₂ := hcomm h1 h2 h12 _ x₁.2 _ x₂.2
  have c13 : Commute (x₁ : X) x₃ := hcomm h1 h3 h13 _ x₁.2 _ x₃.2
  have c23 : Commute (x₂ : X) x₃ := hcomm h2 h3 h23 _ x₂.2 _ x₃.2
  have hdiv : ∀ {J : Subgroup X} {x : ↥J}, orderOf (x : ↥J ⧸ Subgroup.center ↥J) = 3 →
      ∀ e : ℤ, (∀ y ∈ J, (x : X) ^ e * y = y * (x : X) ^ e) → (3 : ℤ) ∣ e := by
    intro J x hx e hc
    have hz := mk_eq_one_of_commute_three (J := J) (z := (x : X) ^ e) (zpow_mem x.2 e) hc
    have hz' : ((x ^ e : ↥J) : ↥J ⧸ Subgroup.center ↥J) = 1 := by
      rw [← hz]
      congr 1
    rw [QuotientGroup.mk_zpow] at hz'
    have := orderOf_dvd_iff_zpow_eq_one.mpr hz'
    rwa [hx] at this
  refine exists_elemAbelian_ge_27_of_commuting c12 c13 c23 fun e₁ e₂ e₃ he => ⟨?_, ?_, ?_⟩
  ·
    refine hdiv hx₁ e₁ fun y hy => ?_
    have heq : (x₁ : X) ^ e₁ = ((x₂ : X) ^ e₂ * (x₃ : X) ^ e₃)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact he)
    rw [heq]
    have hy2 : (x₂ : X) ^ e₂ * y = y * (x₂ : X) ^ e₂ :=
      (hcomm h1 h2 h12 y hy _ (zpow_mem x₂.2 e₂)).symm
    have hy3 : (x₃ : X) ^ e₃ * y = y * (x₃ : X) ^ e₃ :=
      (hcomm h1 h3 h13 y hy _ (zpow_mem x₃.2 e₃)).symm
    have hc : Commute ((x₂ : X) ^ e₂ * (x₃ : X) ^ e₃) y :=
      (show Commute _ y from hy2).mul_left hy3
    exact hc.inv_left.eq
  ·
    refine hdiv hx₂ e₂ fun y hy => ?_
    have heq : (x₂ : X) ^ e₂ = ((x₁ : X) ^ e₁)⁻¹ * ((x₃ : X) ^ e₃)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact eq_inv_of_mul_eq_one_right (by rw [← mul_assoc]; exact he)
    rw [heq]
    have hy1 : (x₁ : X) ^ e₁ * y = y * (x₁ : X) ^ e₁ :=
      hcomm h1 h2 h12 _ (zpow_mem x₁.2 e₁) y hy
    have hy3 : (x₃ : X) ^ e₃ * y = y * (x₃ : X) ^ e₃ :=
      (hcomm h2 h3 h23 y hy _ (zpow_mem x₃.2 e₃)).symm
    exact ((show Commute _ y from hy1).inv_left.mul_left
      (show Commute _ y from hy3).inv_left).eq
  ·
    refine hdiv hx₃ e₃ fun y hy => ?_
    have heq : (x₃ : X) ^ e₃ = ((x₁ : X) ^ e₁ * (x₂ : X) ^ e₂)⁻¹ :=
      eq_inv_of_mul_eq_one_right he
    rw [heq]
    have hy1 : (x₁ : X) ^ e₁ * y = y * (x₁ : X) ^ e₁ :=
      hcomm h1 h3 h13 _ (zpow_mem x₁.2 e₁) y hy
    have hy2 : (x₂ : X) ^ e₂ * y = y * (x₂ : X) ^ e₂ :=
      hcomm h2 h3 h23 _ (zpow_mem x₂.2 e₂) y hy
    exact ((show Commute _ y from hy1).mul_left (show Commute _ y from hy2)).inv_left.eq

private theorem exists_orderOf_three_of_dvd {X : Type} [Group X] [Finite X] (J : Subgroup X)
    (h : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    ∃ x : ↥J, orderOf (x : ↥J ⧸ Subgroup.center ↥J) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨x, hy⟩

section Certified

set_option linter.unusedSectionVars false


private theorem three_dvd_card_of_catalogIs_isL2n {G : Type} [Group G] [Finite G] {r : ℕ}
    (h : catalogIs G (S10.isL2n r)) : 3 ∣ Nat.card G := by
  rcases CatDistinct.data_isL2n CatDistinct.ctx_holds h with h60 | ⟨hk, hcard, -⟩
  · rw [h60]
    norm_num
  · rw [hcard, CatDistinct.orderA_one_eq hk]
    refine Dvd.dvd.mul_left ?_ _
    have h4 : (2 ^ r) ^ 2 = 4 ^ r := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4]
    have h1 : 4 ^ r ≡ 1 [MOD 3] := by
      have := (show 4 ≡ 1 [MOD 3] by decide).pow r
      simpa using this
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 h1.symm

private theorem censusBody_of_rankLE2 (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (hrk : CFSG.LieType.SeitzGeneration.RankLE2 3 (TauCeti.CFSGIndex.lie d).Group) :
    CensusBody d := by
  intro η _ _ _ r _ _ J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  exfalso
  obtain ⟨x₁, hx₁⟩ := exists_orderOf_three_of_dvd J₁ (three_dvd_card_of_catalogIs_isL2n hL1)
  obtain ⟨x₂, hx₂⟩ := exists_orderOf_three_of_dvd J₂ (three_dvd_card_of_catalogIs_isL2n hL2)
  obtain ⟨x₃, hx₃⟩ := exists_orderOf_three_of_dvd J₃ (three_dvd_card_of_catalogIs_isL2n hL3)
  obtain ⟨Ω, hΩ, hcard⟩ :=
    exists_elemAbelian_ge_27_of_components hJ₁ hJ₂ hJ₃ h12 h13 h23 hx₁ hx₂ hx₃
  have h9 := hrk Ω hΩ
  norm_num at h9
  omega

theorem censusBodyG2 : CensusBodyG2 := by
  intro q hv hq
  haveI := (CFSG.Assembly.lie_finite_simple ⟨TauCeti.LieTypeIndex.G2 q, hv⟩).1
  exact censusBody_of_rankLE2 _
    (K1419E.l3u3Rank_g2 q hv hq (MulEquiv.refl _)).2

theorem censusBodyTriD4 : CensusBodyTriD4 := by
  intro q hv hq
  haveI := (CFSG.Assembly.lie_finite_simple ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩).1
  exact censusBody_of_rankLE2 _
    (K1419E.l3u3Rank_triD4 q hv hq (MulEquiv.refl _)).2

theorem censusBodyReeF4 : CensusBodyReeF4 := by
  intro m hv
  haveI := (CFSG.Assembly.lie_finite_simple ⟨TauCeti.LieTypeIndex.reeF4 m, hv⟩).1
  exact censusBody_of_rankLE2 _
    (K1419E.l3u3Rank_reeF4 hv (MulEquiv.refl _)).2

end Certified

end CFSG.LocalAnalysis.GLTheoremA.T1428
