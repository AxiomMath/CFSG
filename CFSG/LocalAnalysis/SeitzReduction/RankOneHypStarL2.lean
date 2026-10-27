module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarOuter
public import CFSG.LocalAnalysis.SteinbergBNLinearTwoOuterInvolutionRigidity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.GMS78BasicLinear
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped Pointwise

theorem eq_one_or_eq_sq_of_mem_sup_zpowers {G : Type*} [Group G] {E : Subgroup G} {u : G}
    (hEodd : Odd (Nat.card E)) (hEu : ∀ e ∈ E, u * e * u⁻¹ ∈ E) (hu2 : orderOf (u ^ 2) = 2)
    {g : G} (hg : g ∈ E ⊔ zpowers u) (hg2 : g ^ 2 = 1) (hgu : g * u ^ 2 = u ^ 2 * g) :
    g = 1 ∨ g = u ^ 2 := by
  classical
  have hE2 : ∀ y ∈ E, y ^ 2 = 1 → y = 1 := by
    intro y hy hy2
    have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    have h2 : orderOf y ∣ Nat.card E := Subgroup.orderOf_dvd_natCard E hy
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h2
      exact absurd (Odd.of_dvd_nat hEodd h2) (by decide)
  set x := u ^ 2 with hx
  have hx2 : x ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one x
  have hu4 : u ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, ← hx, hx2]
  have hpow : ∀ n : ℕ, ∀ e ∈ E, u ^ n * e * (u ^ n)⁻¹ ∈ E := by
    intro n
    induction n with
    | zero => intro e he; simpa using he
    | succ n ih =>
      intro e he
      have h1 : u ^ (n + 1) * e * (u ^ (n + 1))⁻¹ = u ^ n * (u * e * u⁻¹) * (u ^ n)⁻¹ := by
        rw [pow_succ]; group
      rw [h1]
      exact ih _ (hEu e he)
  have huN : u ∈ normalizer (E : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨hEu h, fun hh => ?_⟩
    have hu3 : u⁻¹ = u ^ 3 := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ]
      exact hu4
    have key : h = u ^ 3 * (u * h * u⁻¹) * (u ^ 3)⁻¹ := by rw [← hu3]; group
    rw [key]
    exact hpow 3 _ hh
  have hset := coe_mul_of_right_le_normalizer_left E (zpowers u) (zpowers_le.mpr huN)
  have hg' : g ∈ (E : Set G) * (zpowers u : Set G) := by rw [← hset]; exact hg
  rw [Set.mem_mul] at hg'
  obtain ⟨e, he, w, hw, rfl⟩ := hg'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  have he' : u ^ k * e * (u ^ k)⁻¹ ∈ E := (mem_normalizer_iff.mp (zpow_mem huN k) e).mp he
  have hxz : ∀ m : ℤ, x ^ m = u ^ (2 * m) := fun m => by
    rw [hx, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat]
  have hxk : x ^ k ∈ E := by
    have h1 : (e * (u ^ k * e * (u ^ k)⁻¹)) * x ^ k = e * u ^ k * (e * u ^ k) := by
      rw [hxz, two_mul, zpow_add]; group
    rw [← sq, hg2] at h1
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_mem (mul_mem he he')
  have hxk1 : x ^ k = 1 := by
    refine hE2 _ hxk ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  obtain ⟨j, rfl⟩ : (2 : ℤ) ∣ k := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hxk1
    rwa [hu2, Nat.cast_ofNat] at this
  have hukx : u ^ (2 * j) = x ^ j := (hxz j).symm
  have hxj : x ^ j = 1 ∨ x ^ j = x := by
    rw [← zpow_mod_orderOf, hu2, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one j with h | h
    · left; rw [h, zpow_zero]
    · right; rw [h, zpow_one]
  rw [hukx] at hg2 hgu ⊢
  rcases hxj with h | h
  · rw [h, mul_one] at hg2 ⊢
    exact Or.inl (hE2 e he hg2)
  · rw [h] at hg2 hgu ⊢
    have hc : Commute e x := by
      have h1 : e * x * x = x * e * x := by rw [hgu, mul_assoc]
      exact mul_right_cancel h1
    have he2 : e ^ 2 = 1 := by
      rw [hc.mul_pow, hx2, mul_one] at hg2
      exact hg2
    rw [hE2 e he he2, one_mul]
    exact Or.inr rfl

open CFSG.Open CFSG.ComponentClassification.AschbacherToolkit.Bender in
open scoped MatrixGroups in
theorem hypOneStar_inner_of_psl2 {D : Type} [Group D] [Finite D]
    {f : ℕ} (hf : 3 ≤ f) (e : D ≃* PSL(2, GaloisField 2 f)) {z : D} {u : MulAut D}
    (hx : orderOf (MulAut.conj z) = 2) (hu : u ^ 2 = MulAut.conj z) {E : Subgroup (MulAut D)}
    (hEodd : Odd (Nat.card E)) (hEu : ∀ e ∈ E, u * e * u⁻¹ ∈ E) :
    ∃ c : D, MulAut.conj c * MulAut.conj z = MulAut.conj z * MulAut.conj c ∧
      MulAut.conj c * u * (MulAut.conj c)⁻¹ ∉ E ⊔ zpowers u := by
  classical
  have hf2 : 2 ≤ f := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ι : D →* MulAut D := MulAut.conj with hι
  have hB : fusionBenderBorel D (2 ^ f) 1 :=
    (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f
      hf2).map_mulEquiv e.symm
  have hsimple : IsSimpleGroup D :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (Or.inl ⟨f, hf2, ⟨e⟩⟩)
  have hinj : ∀ c : D, ι c = 1 → c = 1 := by
    obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 D))
    obtain ⟨hSE₀, -, -, -⟩ := benderBorel_sylowCenter hB P₀
    have hcen : center D = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center D) with h | h
      · exact h
      · exfalso
        apply hSE₀.1
        rw [eq_top_iff]
        intro g _
        rw [mem_normalizer_iff]
        intro y
        have hg : g ∈ center D := h ▸ mem_top g
        have hgy : g * y * g⁻¹ = y := by
          rw [← mem_center_iff.mp hg y, mul_inv_cancel_right]
        rw [hgy]
    intro c hc
    have hcc : c ∈ center D := by
      rw [mem_center_iff]
      intro g
      have h1 : c * g * c⁻¹ = g := by
        have := congrArg (fun φ : MulAut D => φ g) hc
        simpa only [hι, MulAut.conj_apply, MulAut.one_apply] using this
      calc g * c = c * g * c⁻¹ * c := by rw [h1]
        _ = c * g := by group
    rw [hcen, mem_bot] at hcc
    exact hcc
  have hx1 : ι z ≠ 1 := by
    intro h
    rw [hι] at h
    rw [h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hz1 : z ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hz2 : z ^ 2 = 1 := hinj _ (by rw [map_pow, hι, ← hx]; exact pow_orderOf_eq_one _)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq, hz2])
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  obtain ⟨P, hP⟩ := (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_zpowers, hzord, pow_one] : Nat.card (zpowers z) = 2 ^ 1)).exists_le_sylow
  have hzP : z ∈ (P : Subgroup D) := hP (mem_zpowers z)
  obtain ⟨hsq, hcomm⟩ := CFSG.ComponentClassification.GMS78.sylow_elem_of_psl2 hf2 e P
  obtain ⟨hSE, -, -, hPcard⟩ := benderBorel_sylowCenter hB P
  have hcard : Nat.card (Sylow 2 D) = Nat.card (P : Subgroup D) + 1 := by
    rw [card_sylow_eq_of_mulEquiv e 2, CFSG.Walter.psl2_even_card_sylow (by omega), hPcard,
      pow_one]
  have hxu : ι z * u = u * ι z := by
    rw [hι, ← hu]
    exact ((Commute.refl u).pow_left 2).eq
  have huz : u z = z := by
    have h1 : ι (u z) = ι z := by
      rw [hι, mulAut_conj_apply_eq, ← hι, ← hxu, mul_inv_cancel_right]
    have h2 : ι (u z * z⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj _ h2)
  have hPu : u • P = P := by
    by_contra hne
    have hz' : z ∈ ((u • P : Sylow 2 D) : Subgroup D) := by
      rw [Omega.mem_smul_iff]
      have h1 : u⁻¹ z = z := by rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, huz]
      rw [h1]
      exact hzP
    exact hz1 (Omega.eq_one_of_mem_of_mem hSE hne hzP hz')
  have huP : ∀ r ∈ (P : Subgroup D), u r ∈ (P : Subgroup D) := by
    intro r hr
    have h1 : u r ∈ ((u • P : Sylow 2 D) : Subgroup D) := by
      rw [Omega.mem_smul_iff, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      exact hr
    rwa [hPu] at h1
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hu2 : orderOf (u ^ 2) = 2 := by rw [hu]; exact hx
  have hψ : ∀ c ∈ (P : Subgroup D), c * (u c)⁻¹ = 1 ∨ c * (u c)⁻¹ = z := by
    intro c hc
    have hwP : c * (u c)⁻¹ ∈ (P : Subgroup D) := mul_mem hc (inv_mem (huP c hc))
    have hg : ι (c * (u c)⁻¹) ∈ E ⊔ zpowers u := by
      have h1 : ι (c * (u c)⁻¹) = ι c * u * (ι c)⁻¹ * u⁻¹ := by
        rw [map_mul, map_inv, hι, mulAut_conj_apply_eq]
        group
      rw [h1]
      refine mul_mem (hcon c ?_) (inv_mem ((le_sup_right : zpowers u ≤ E ⊔ zpowers u)
        (mem_zpowers u)))
      rw [hι, ← map_mul, ← map_mul, hcomm c hc z hzP]
    have hg2 : ι (c * (u c)⁻¹) ^ 2 = 1 := by rw [← map_pow, hsq _ hwP, map_one]
    have hgu : ι (c * (u c)⁻¹) * u ^ 2 = u ^ 2 * ι (c * (u c)⁻¹) := by
      rw [hu, hι, ← map_mul, ← map_mul, hcomm _ hwP z hzP]
    rcases eq_one_or_eq_sq_of_mem_sup_zpowers hEodd hEu hu2 hg hg2 hgu with h | h
    · exact Or.inl (hinj _ h)
    · right
      rw [hu] at h
      have h2 : ι (c * (u c)⁻¹ * z⁻¹) = 1 := by rw [map_mul, map_inv, h, hι, mul_inv_cancel]
      exact mul_inv_eq_one.mp (hinj _ h2)
  have hmove : ∀ r ∈ (P : Subgroup D), u r ≠ r → u r = z * r := by
    intro r hr hur
    rcases hψ r hr with h | h
    · exact absurd (mul_inv_eq_one.mp h).symm hur
    · have h1 : (u r)⁻¹ = r⁻¹ * z := by rw [← h]; group
      rw [← inv_inv (u r), h1, mul_inv_rev, inv_inv, hzinv]
  by_cases hfixall : ∀ c ∈ (P : Subgroup D), u c = c
  ·
    obtain ⟨r, hr, hur⟩ := Omega.exists_eq_conj_of_abelian hSE hcard hcomm u hfixall
    apply hx1
    rw [hι, ← hu, hur, ← map_pow, hsq r hr, map_one]
  push Not at hfixall
  obtain ⟨p, hp, hup⟩ := hfixall
  have hup' : u p = z * p := hmove p hp hup
  set α : MulAut D := u * ι p with hα
  have hαapp : ∀ r ∈ (P : Subgroup D), α r = u r := by
    intro r hr
    rw [hα, MulAut.mul_apply, hι, MulAut.conj_apply, hcomm p hp r hr, mul_inv_cancel_right]
  have hαR : ∀ r ∈ (P : Subgroup D), α r ∈ (P : Subgroup D) := fun r hr => by
    rw [hαapp r hr]
    exact huP r hr
  have hαα : α * α = 1 := by
    have h1 : ι p * u = u * ι (u⁻¹ p) := by
      rw [hι, mulAut_conj_apply_eq u⁻¹ p]
      group
    have hu_inv_p : u⁻¹ p = z * p := by
      rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, map_mul, huz, hup', ← mul_assoc, ← sq, hz2,
        one_mul]
    have h2 : z * (z * p * p) = 1 := by
      rw [← mul_assoc, ← mul_assoc, ← sq, hz2, one_mul, ← sq, hsq p hp]
    calc α * α = u * (ι p * u) * ι p := by rw [hα]; group
      _ = u * (u * ι (u⁻¹ p)) * ι p := by rw [h1]
      _ = u ^ 2 * ι (u⁻¹ p * p) := by rw [map_mul, sq]; simp only [mul_assoc]
      _ = 1 := by rw [hu, hu_inv_p, hι, ← map_mul, h2, map_one]
  have hαout : ¬ ∃ y, α = MulAut.conj y := by
    rintro ⟨y, hy⟩
    have hu' : u = ι (y * p⁻¹) := by
      rw [map_mul, map_inv, hι, ← hy, hα, mul_inv_cancel_right]
    have hw2 : (y * p⁻¹) ^ 2 = z := by
      have h1 : ι ((y * p⁻¹) ^ 2 * z⁻¹) = 1 := by
        rw [map_mul, map_pow, ← hu', hu, map_inv, hι, mul_inv_cancel]
      exact mul_inv_eq_one.mp (hinj _ h1)
    have hw4 : (y * p⁻¹) ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hw2, hz2]
    obtain ⟨Q, hQ⟩ := (IsPGroup.of_card_dvd_pow (p := 2) (n := 2)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hw4 :
        Nat.card (zpowers (y * p⁻¹)) ∣ 2 ^ 2)).exists_le_sylow
    have h1 := (CFSG.ComponentClassification.GMS78.sylow_elem_of_psl2 hf2 e Q).1 _
      (hQ (mem_zpowers (y * p⁻¹)))
    rw [hw2] at h1
    exact hz1 h1
  have hC := CFSG.ComponentClassification.GMS78.card_fix_sq_le_of_not_inner_psl2 hf2 e α hαα
    hαout P hαR
  have hfixp : ∀ r ∈ (P : Subgroup D), u r ≠ r → α (r * p⁻¹) = r * p⁻¹ := by
    intro r hr hur
    have hrp : r * p⁻¹ ∈ (P : Subgroup D) := mul_mem hr (inv_mem hp)
    rw [hαapp _ hrp]
    have hc : z * (r * p⁻¹) = r * p⁻¹ * z := hcomm z hzP _ hrp
    calc u (r * p⁻¹) = u r * (u p)⁻¹ := by rw [map_mul, map_inv]
      _ = z * (r * p⁻¹) * z⁻¹ := by rw [hmove r hr hur, hup']; group
      _ = r * p⁻¹ := by rw [hc]; group
  have hlow : Nat.card (P : Subgroup D) ≤ Nat.card {r : (P : Subgroup D) // α r = r} * 2 := by
    let φ : ↥(P : Subgroup D) → {r : (P : Subgroup D) // α r = r} × Bool := fun r =>
      if h : u r = r then (⟨r, by rw [hαapp r r.2]; exact h⟩, true)
      else (⟨⟨r * p⁻¹, mul_mem r.2 (inv_mem hp)⟩, hfixp r r.2 h⟩, false)
    have hφ : Function.Injective φ := by
      intro r r' hrr'
      simp only [φ] at hrr'
      split_ifs at hrr' with h h'
      · simp only [Prod.mk.injEq, Subtype.mk.injEq, and_true] at hrr'
        exact hrr'
      · simp at hrr'
      · simp at hrr'
      · simp only [Prod.mk.injEq, Subtype.mk.injEq, and_true] at hrr'
        exact Subtype.ext (mul_right_cancel hrr')
    calc Nat.card (P : Subgroup D) ≤ Nat.card ({r : (P : Subgroup D) // α r = r} × Bool) :=
          Nat.card_le_card_of_injective φ hφ
      _ = Nat.card {r : (P : Subgroup D) // α r = r} * 2 := by
          rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  have hP8 : 8 ≤ Nat.card (P : Subgroup D) := by
    rw [hPcard, pow_one]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  nlinarith [Nat.mul_le_mul hlow hlow]

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.ComponentClassification.CatalogueBLinearTwoFixed in
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (linear_two_automorphism_semilinear_isomorphism even_linear_two_involution_normal_forms
    coordinateD_eq_G) in
theorem exists_fixed_simple_of_outer_psl2 {D : Type} [Group D] {f : ℕ} (hf : 3 ≤ f)
    (hD : StatedClassicalModel D .PSL 2 2 f) (α : MulAut D) (hα : orderOf α = 2)
    (hαout : α ∉ (MulAut.conj : D →* MulAut D).range) :
    ∃ J : Subgroup D, (∀ d : D, α d = d ↔ d ∈ J) ∧ IsSimpleGroup J ∧
      (∃ a b : J, a * b ≠ b * a) ∧
      ∀ P : Subgroup (MulAut D), IsPGroup 2 P → (∀ β ∈ P, ∀ j ∈ J, β j = j) →
        Nat.card P ≤ 2 := by
  classical
  obtain ⟨-, -, -, J', hαJ', -, -, hJ'nab, -, -, hJ'2⟩ :=
    CFSG.LocalAnalysis.even_linear_two_outer_involution_perfect_fixed_rigidity hf hD α hα hαout
  let F : Subgroup D :=
    { carrier := {d | α d = d}
      mul_mem' := fun {a b} (ha : α a = a) (hb : α b = b) => by
        show α (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := map_one α
      inv_mem' := fun {a} (ha : α a = a) => by
        show α a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hmemF : ∀ d : D, d ∈ F ↔ α d = d := fun d => Iff.rfl
  refine ⟨F, fun d => (hmemF d).symm, ?_, ?_, ?_⟩
  rotate_left
  ·
    by_contra hab
    push Not at hab
    apply hJ'nab
    intro a b
    have h1 := hab ⟨a, hαJ' a a.2⟩ ⟨b, hαJ' b b.2⟩
    have h2 : (a : D) * b = b * a := congrArg Subtype.val h1
    exact Subtype.ext h2
  ·
    intro P hP2 hPfix
    exact hJ'2 P (fun β hβ j hj => hPfix β hβ j (hαJ' j hj)) hP2
  obtain ⟨⟨-, hf1, -⟩, K, _, _, hK, ⟨eD⟩⟩ := hD
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf1 hK
  let φ : D ≃* coordinateG K :=
    eD.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans (pslEquivCoordinateG K))
  obtain ⟨c, hc, hcG, -⟩ := linear_two_automorphism_semilinear_isomorphism K
  let Φ : MulAut D ≃* coordinateE K := (MulAut.congr φ).trans c.symm
  have hΦ : ∀ (β : MulAut D) (d : D),
      ((φ (β d) : coordinateG K) : Equiv.Perm (Omega K)) =
        (Φ β : Equiv.Perm (Omega K)) * φ d * (Φ β : Equiv.Perm (Omega K))⁻¹ := by
    intro β d
    have h := hc (Φ β) (φ d)
    rw [show c (Φ β) = MulAut.congr φ β from c.apply_symm_apply _] at h
    rw [← h, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  set a : Equiv.Perm (Omega K) := (Φ α : Equiv.Perm (Omega K)) with ha
  have haE : a ∈ coordinateE K := (Φ α).2
  have ha2 : orderOf a = 2 := by
    rw [ha, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hα]
  have haG : a ∉ coordinateG K := by
    intro haG
    apply hαout
    have h1 : Φ α = ⟨a, ((coordinateG_le_D K).trans (coordinateD_le_E K)) haG⟩ := rfl
    have h2 : MulAut.congr φ α = MulAut.conj (⟨a, haG⟩ : coordinateG K) := by
      have h3 := hcG ⟨a, haG⟩
      rw [← h1] at h3
      rw [← h3]
      exact (c.apply_symm_apply _).symm
    refine ⟨φ.symm ⟨a, haG⟩, ?_⟩
    apply (MulAut.congr φ).injective
    rw [h2, CFSG.LocalAnalysis.mulAutCongr_conj_eq, φ.apply_symm_apply]
  have hNF := (even_linear_two_involution_normal_forms (K := K) hf1 hK).2.2.2.2.2.2.2.2.2 a haE
    ha2
  rcases hNF with ⟨haG', -⟩ | ⟨-, -, σ, hσ1, hσσ, -, -, -, ⟨h, hhG, hah⟩, -⟩
  · exact absurd haG' haG
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  set k : Subfield K := fixedField K σ with hk
  have hKk : Nat.card K = Nat.card k ^ 2 := card_eq_fixedField_card_sq K σ hσ2
  have hk4 : 4 ≤ Nat.card k := by
    have h8 : 8 ≤ Nat.card K := by
      rw [hK]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hev : Even (Nat.card k ^ 2) := by
      rw [← hKk, hK]
      exact (Nat.even_pow' (by omega)).mpr even_two
    have hev' : Even (Nat.card k) := (Nat.even_pow' (by norm_num)).mp hev
    rw [hKk] at h8
    by_contra hlt
    push Not at hlt
    obtain ⟨m, hm⟩ := hev'
    have hle : Nat.card k ≤ 2 := by omega
    have h4 : Nat.card k ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hle 2
    omega
  have : CharP k 2 := k.subtype.charP Subtype.val_injective 2
  have hDG : coordinateD K = coordinateG K := coordinateD_eq_G
  have hDGk : coordinateD k = coordinateG k := coordinateD_eq_G
  obtain ⟨s4, hs4⟩ := CFSG.LocalAnalysis.exists_finset_card_four hk4
  obtain ⟨-, hsimp, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := k) (n := 2) le_rfl
    (Or.inr ⟨s4, hs4⟩)
  let ρ : D →* Equiv.Perm (Omega K) :=
    (MulAut.conj h⁻¹).toMonoidHom.comp ((coordinateG K).subtype.comp φ.toMonoidHom)
  have hρ : ∀ d, ρ d = h⁻¹ * (φ d : Equiv.Perm (Omega K)) * h := fun d => by
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      Subgroup.coe_subtype]
  have hρinj : Function.Injective ρ := by
    intro d d' hdd
    rw [hρ, hρ] at hdd
    have h1 : (φ d : Equiv.Perm (Omega K)) = φ d' := mul_left_cancel (mul_right_cancel hdd)
    exact φ.injective (Subtype.ext h1)
  have hmap : F.map ρ = coordinateD K ⊓ Subgroup.centralizer {fieldExtension K σ} := by
    ext g
    constructor
    · rintro ⟨d, hd, rfl⟩
      have hd' : α d = d := hd
      rw [hρ, Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [hDG]
        exact mul_mem (mul_mem (inv_mem hhG) (φ d).2) hhG
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hΦ α d
        rw [hd', ← ha, hah] at h1
        have h2 : (fieldExtension K σ) * (h⁻¹ * (φ d : Equiv.Perm (Omega K)) * h) =
            (h⁻¹ * (φ d : Equiv.Perm (Omega K)) * h) * fieldExtension K σ := by
          calc (fieldExtension K σ) * (h⁻¹ * (φ d : Equiv.Perm (Omega K)) * h)
              = h⁻¹ * ((h * fieldExtension K σ * h⁻¹) * (φ d : Equiv.Perm (Omega K)) *
                  (h * fieldExtension K σ * h⁻¹)⁻¹) * h * fieldExtension K σ := by group
            _ = (h⁻¹ * (φ d : Equiv.Perm (Omega K)) * h) * fieldExtension K σ := by rw [← h1]
        exact h2.symm
    · intro hg
      rw [Subgroup.mem_inf] at hg
      obtain ⟨hgD, hgc⟩ := hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hgc
      rw [hDG] at hgD
      have hgG : h * g * h⁻¹ ∈ coordinateG K := mul_mem (mul_mem hhG hgD) (inv_mem hhG)
      refine ⟨φ.symm ⟨h * g * h⁻¹, hgG⟩, ?_, ?_⟩
      · show α (φ.symm ⟨h * g * h⁻¹, hgG⟩) = φ.symm ⟨h * g * h⁻¹, hgG⟩
        apply φ.injective
        apply Subtype.ext
        rw [hΦ, ← ha, hah, φ.apply_symm_apply]
        show h * fieldExtension K σ * h⁻¹ * (h * g * h⁻¹) * (h * fieldExtension K σ * h⁻¹)⁻¹ =
          h * g * h⁻¹
        calc h * fieldExtension K σ * h⁻¹ * (h * g * h⁻¹) * (h * fieldExtension K σ * h⁻¹)⁻¹
            = h * (fieldExtension K σ * g) * (fieldExtension K σ)⁻¹ * h⁻¹ := by group
          _ = h * (g * fieldExtension K σ) * (fieldExtension K σ)⁻¹ * h⁻¹ := by rw [hgc]
          _ = h * g * h⁻¹ := by group
      · rw [hρ, φ.apply_symm_apply]
        show h⁻¹ * (h * g * h⁻¹) * h = g
        group
  let eF : F ≃* ↥(coordinateD K ⊓ Subgroup.centralizer {fieldExtension K σ}) :=
    (F.equivMapOfInjective ρ hρinj).trans (MulEquiv.subgroupCongr hmap)
  let ek : ↥(coordinateD k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    (MulEquiv.subgroupCongr hDGk).trans (pslEquivCoordinateG k).symm
  exact (eF.trans ((subfieldCoordinateEquivDCentralizer K σ hσ2).symm.trans ek)).isSimpleGroup

open CFSG.Assembly.LowTwoRank in
theorem hypothesisOneStar_of_statedPSL2 {D : Type} [Group D]
    [Finite D] {f : ℕ} (hf : 3 ≤ f) (hD : StatedClassicalModel D .PSL 2 2 f) :
    HypothesisOneStar D := by
  intro x u hx hu E _hEC hEodd hEu hEinn
  by_cases hxin : x ∈ (MulAut.conj : D →* MulAut D).range
  · obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hxin
    obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psl2_of_stated hD
    exact hypOneStar_inner_of_psl2 hf e hx hu hEodd hEu
  · obtain ⟨J, hJfix, hJs, hJnab, hJ2⟩ := exists_fixed_simple_of_outer_psl2 hf hD x hx hxin
    exact hypOneStar_exists_of_simple_fixed hx hu J hJfix hJs hJnab hJ2 hEodd hEu hEinn

end CFSG.SeitzReduction.RankOne
