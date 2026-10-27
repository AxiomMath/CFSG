module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueField

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.OuterAutomorphisms

section General

variable {G : Type*} [Group G]

theorem commutator_sup_eq_sup_of_perfect {A B : Subgroup G} (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) :
    ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (sup_le ?_ ?_)
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · calc A = ⁅A, A⁆ := hA.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc B = ⁅B, B⁆ := hB.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem card_sup_eq_mul_of_le_centralizer {A B : Subgroup G} (hAB : B ≤ centralizer (A : Set G))
    (hdisj : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hAN : A ≤ normalizer (B : Set G) :=
    (le_centralizer_iff.1 hAB).trans (centralizer_le_normalizer _)
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : A × B => (⟨(p.1 : G) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ :
      (A ⊔ B : Subgroup G))) ⟨fun p p' h => ?_, fun x => ?_⟩)).symm
  · have h' : (p.1 : G) * p.2 = p'.1 * p'.2 := congrArg Subtype.val h
    have hmem : (p'.1 : G)⁻¹ * p.1 ∈ A ⊓ B := by
      refine mem_inf.2 ⟨mul_mem (inv_mem p'.1.2) p.1.2, ?_⟩
      have e : (p'.1 : G)⁻¹ * p.1 = p'.2 * (p.2 : G)⁻¹ := by
        calc (p'.1 : G)⁻¹ * p.1 = (p'.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
          _ = (p'.1 : G)⁻¹ * (p'.1 * p'.2) * (p.2 : G)⁻¹ := by rw [h']
          _ = p'.2 * (p.2 : G)⁻¹ := by group
      rw [e]
      exact mul_mem p'.2.2 (inv_mem p.2.2)
    rw [hdisj, mem_bot] at hmem
    have h1 : (p.1 : G) = p'.1 := by
      calc (p.1 : G) = p'.1 * ((p'.1 : G)⁻¹ * p.1) := by group
        _ = p'.1 := by rw [hmem, mul_one]
    have h2 : (p.2 : G) = p'.2 := by
      have := h'
      rw [h1] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · have hx : (x : G) ∈ ((A ⊔ B : Subgroup G) : Set G) := x.2
    rw [coe_mul_of_left_le_normalizer_right A B hAN] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

theorem isPGroup_sup_of_le_centralizer {p : ℕ} {A B : Subgroup G}
    (hAB : B ≤ centralizer (A : Set G)) (hA : IsPGroup p A) (hB : IsPGroup p B) :
    IsPGroup p (A ⊔ B : Subgroup G) :=
  IsPGroup.to_sup_of_normal_right' hA hB
    ((le_centralizer_iff.1 hAB).trans (centralizer_le_normalizer _))

end General

theorem ordF4_sq_eq (x : ℕ) (hx : 1 ≤ x) :
    CFSG.Open.ordF4 (x ^ 2) = CFSG.Open.ordF4 x *
      (x ^ 24 * (x ^ 12 + 1) * (x ^ 8 + 1) * (x ^ 6 + 1) * (x ^ 2 + 1)) := by
  have h : ∀ k, 1 ≤ x ^ k := fun k => Nat.one_le_pow _ _ hx
  have h' : ∀ k, 1 ≤ (x ^ 2) ^ k := fun k => Nat.one_le_pow _ _ (h 2)
  unfold CFSG.Open.ordF4
  zify [h 12, h 8, h 6, h 2, h' 12, h' 8, h' 6, h' 2]
  ring

theorem not_sq_ordF4_dvd_ordF4_sq {e : ℕ} (he : 1 ≤ e) :
    ¬ CFSG.Open.ordF4 (2 ^ e) ^ 2 ∣ CFSG.Open.ordF4 ((2 ^ e) ^ 2) := by
  intro h
  set x := 2 ^ e with hxdef
  have hx1 : 1 ≤ x := Nat.one_le_two_pow
  have hx2 : 2 ≤ x := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  set R := x ^ 24 * (x ^ 12 + 1) * (x ^ 8 + 1) * (x ^ 6 + 1) * (x ^ 2 + 1) with hRdef
  rw [ordF4_sq_eq x hx1, sq] at h
  have hpos : 0 < CFSG.Open.ordF4 x := by
    have hk : ∀ k, 0 < k → 1 ≤ x ^ k - 1 := fun k hk => by
      have : 2 ≤ x ^ k := le_trans hx2 (Nat.le_self_pow (by omega) x)
      omega
    unfold CFSG.Open.ordF4
    have := hk 12 (by norm_num)
    have := hk 8 (by norm_num)
    have := hk 6 (by norm_num)
    have := hk 2 (by norm_num)
    positivity
  have hdvd : CFSG.Open.ordF4 x ∣ R := Nat.dvd_of_mul_dvd_mul_left hpos h
  have hx3 : ((x : ℕ) : ZMod 3) ^ 2 = 1 := by
    rw [hxdef, Nat.cast_pow, ← pow_mul, mul_comm, pow_mul]
    have : ((2 : ℕ) : ZMod 3) ^ 2 = 1 := by decide
    rw [this, one_pow]
  have h3 : 3 ∣ CFSG.Open.ordF4 x := by
    have hsq : 3 ∣ x ^ 2 - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hx1), Nat.cast_pow,
        Nat.cast_one, hx3, sub_self]
    unfold CFSG.Open.ordF4
    exact Dvd.dvd.mul_left hsq _
  have hR : ¬ 3 ∣ R := by
    rw [← ZMod.natCast_eq_zero_iff, hRdef]
    have e24 : ((x : ℕ) : ZMod 3) ^ 24 = 1 := by
      rw [show 24 = 2 * 12 by norm_num, pow_mul, hx3, one_pow]
    have e12 : ((x : ℕ) : ZMod 3) ^ 12 = 1 := by
      rw [show 12 = 2 * 6 by norm_num, pow_mul, hx3, one_pow]
    have e8 : ((x : ℕ) : ZMod 3) ^ 8 = 1 := by
      rw [show 8 = 2 * 4 by norm_num, pow_mul, hx3, one_pow]
    have e6 : ((x : ℕ) : ZMod 3) ^ 6 = 1 := by
      rw [show 6 = 2 * 3 by norm_num, pow_mul, hx3, one_pow]
    push_cast
    rw [e24, e12, e8, e6, hx3]
    decide
  exact hR (h3.trans hdvd)

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G]
  in
theorem inf_eq_bot_of_le_centralizer_F4 {M₁ M₂ : Subgroup G} {K₁ : Type} [Field K₁] [Finite K₁]
    (e₁ : M₁ ≃* adjointGroup .F4 K₁) (h₁₂ : M₂ ≤ centralizer (M₁ : Set G)) : M₁ ⊓ M₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hcen : (⟨x, (mem_inf.1 hx).1⟩ : M₁) ∈ center M₁ := Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext ((mem_centralizer_iff.1 (h₁₂ (mem_inf.1 hx).2)) y y.2)
  have h1 : e₁ ⟨x, (mem_inf.1 hx).1⟩ ∈ center (adjointGroup .F4 K₁) :=
    (MulEquivClass.apply_mem_center_iff e₁).2 hcen
  rw [center_adjointGroup_eq_bot, mem_bot, MulEquiv.map_eq_one_iff] at h1
  exact mem_bot.2 (congrArg Subtype.val h1)

theorem inf_centralizer_eq_of_swap_F4 (hset : StandardSetting G L) {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M₁ M₂ : Subgroup G} {K₁ : Type}
    [Field K₁] (hK₁ : Nat.card K₁ = 2 ^ f) (e₁ : M₁ ≃* adjointGroup .F4 K₁)
    (h₁₂ : M₂ ≤ centralizer (M₁ : Set G)) (hswap : M₁.map (MulAut.conj t).toMonoidHom = M₂) :
    (M₁ ⊔ M₂) ⊓ centralizer ({t} : Set G) = L := by
  have := finite_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK₁
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨φ, hφinj, hφ⟩ :=
    exists_injective_eq_range_of_swap h₁₂ (inf_eq_bot_of_le_centralizer_F4 e₁ h₁₂) ht2 hswap
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  have : Group.IsPerfect (adjointGroup .F4 K₁) := CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 K₁
  have hrange : (φ.comp e₁.symm.toMonoidHom).range = φ.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e₁.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e₁ x, by simp⟩
  have hperf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [← hrange]
    exact commutator_monoidHom_range_eq_of_isPerfect _
  rw [hφ]
  refine Subgroup.eq_of_le_of_card_ge
    (std_perfect_le hset hOut htC ht hperf (hφ ▸ inf_le_right)) ?_
  rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_congr e₁.toEquiv,
    Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK, hK₁]

omit [Finite G]
  in
theorem exists_perfect_twoSubgroup_of_inner_F4 {t : G} (ht : orderOf t = 2) {M : Subgroup G}
    {f : ℕ} (hf : 2 ≤ f) {K₁ : Type} [Field K₁] (hK₁ : Nat.card K₁ = 2 ^ f)
    (e₁ : M ≃* adjointGroup .F4 K₁) (hin : ∃ m ∈ M, ∀ x ∈ M, t * x * t⁻¹ = m * x * m⁻¹) :
    ∃ P Q : Subgroup G, ⁅P, P⁆ = P ∧ P ≤ centralizer ({t} : Set G) ∧ P ≤ M ∧ Q ≤ P ∧
      IsPGroup 2 Q ∧ Nat.card Q = 2 ^ (20 * f) := by
  have := finite_of_natCard_eq_two_pow hK₁
  have := charP_two_of_natCard_eq_two_pow hK₁
  obtain ⟨m₀, hm₀M, hm₀⟩ := hin
  obtain ⟨w, hwM, hw2, hwC⟩ := exists_involution_centralizer_le_of_inner ht e₁ hm₀M hm₀
  have hq : 4 ≤ Nat.card K₁ := by
    rw [hK₁]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hw' : orderOf (e₁ ⟨w, hwM⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hw2]
  obtain ⟨P, Q, hP, hPw, hQP, hQ, hQcard⟩ := exists_perfect_twoSubgroup_le_centralizer_F4 hq hw'
  set φ : adjointGroup .F4 K₁ →* G := M.subtype.comp e₁.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := M.subtype_injective.comp e₁.symm.injective
  have hφw : φ (e₁ ⟨w, hwM⟩) = w := by simp [hφ]
  refine ⟨P.map φ, Q.map φ, by rw [← map_commutator, hP], ?_, ?_, map_mono hQP, hQ.map φ, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hpw := mem_centralizer_singleton_iff.1 (hPw hp)
    have hpw' : φ p * w = w * φ p := by
      rw [← hφw, ← map_mul, ← map_mul, hpw]
    exact mem_centralizer_singleton_iff.2 (hwC _ (e₁.symm p).2 hpw')
  · rintro _ ⟨p, -, rfl⟩
    exact (e₁.symm p).2
  · rw [Subgroup.card_map_of_injective hφinj, hQcard, hK₁, ← pow_mul, mul_comm]

theorem false_of_inner_inner_F4 (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M₁ M₂ : Subgroup G}
    {K₁ K₂ : Type} [Field K₁] [Field K₂] (hK₁ : Nat.card K₁ = 2 ^ f) (hK₂ : Nat.card K₂ = 2 ^ f)
    (e₁ : M₁ ≃* adjointGroup .F4 K₁) (e₂ : M₂ ≃* adjointGroup .F4 K₂)
    (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (hin₁ : ∃ m ∈ M₁, ∀ x ∈ M₁, t * x * t⁻¹ = m * x * m⁻¹)
    (hin₂ : ∃ m ∈ M₂, ∀ x ∈ M₂, t * x * t⁻¹ = m * x * m⁻¹) : False := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK₁
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  obtain ⟨P₁, Q₁, hP₁, hP₁t, hP₁M, hQ₁P, hQ₁, hQ₁c⟩ :=
    exists_perfect_twoSubgroup_of_inner_F4 ht hf hK₁ e₁ hin₁
  obtain ⟨P₂, Q₂, hP₂, hP₂t, hP₂M, hQ₂P, hQ₂, hQ₂c⟩ :=
    exists_perfect_twoSubgroup_of_inner_F4 ht hf hK₂ e₂ hin₂
  have hPL : P₁ ⊔ P₂ ≤ L :=
    std_perfect_le hset hOut htC ht (commutator_sup_eq_sup_of_perfect hP₁ hP₂) (sup_le hP₁t hP₂t)
  have hQ₁₂ : Q₂ ≤ centralizer (Q₁ : Set G) := fun y hy =>
    (Subgroup.centralizer_le fun x hx => (hQ₁P.trans hP₁M) hx) (h₁₂ ((hQ₂P.trans hP₂M) hy))
  have hdisj : Q₁ ⊓ Q₂ = ⊥ := le_bot_iff.1 ((inf_le_inf (hQ₁P.trans hP₁M)
    (hQ₂P.trans hP₂M)).trans (inf_eq_bot_of_le_centralizer_F4 e₁ h₁₂).le)
  have hle := natCard_le_of_le_of_isPGroup_two_F4 e
    ((sup_le_sup hQ₁P hQ₂P).trans hPL) (isPGroup_sup_of_le_centralizer hQ₁₂ hQ₁ hQ₂)
  rw [card_sup_eq_mul_of_le_centralizer hQ₁₂ hdisj, hQ₁c, hQ₂c, hK, ← pow_add, ← pow_mul] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
  omega

omit [Finite G] in
theorem perfect_card_inf_centralizer_of_outer_F4 {t : G} (ht : orderOf t = 2) {M : Subgroup G}
    {e' : ℕ} {K₁ : Type} [Field K₁] (hK₁ : Nat.card K₁ = 2 ^ (2 * e'))
    (e₁ : M ≃* adjointGroup .F4 K₁) (htM : t ∈ normalizer (M : Set G))
    (hout : ¬ ∃ m ∈ M, ∀ x ∈ M, t * x * t⁻¹ = m * x * m⁻¹) :
    ⁅M ⊓ centralizer ({t} : Set G), M ⊓ centralizer ({t} : Set G)⁆ =
        M ⊓ centralizer ({t} : Set G) ∧
      Nat.card (M ⊓ centralizer ({t} : Set G) : Subgroup G) = CFSG.Open.ordF4 (2 ^ e') := by
  set α := normalizerMulAut e₁ ⟨t, htM⟩ with hα
  have hα2 : α ^ 2 = 1 := by
    have h1 : (⟨t, htM⟩ : normalizer (M : Set G)) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← ht, pow_orderOf_eq_one]; rfl)
    rw [hα, ← map_pow, h1, map_one]
  have hαo : α ∉ (MulAut.conj : adjointGroup .F4 K₁ →* MulAut (adjointGroup .F4 K₁)).range := by
    rintro ⟨c, hc⟩
    refine hout ⟨(e₁.symm c : G), (e₁.symm c).2, fun x hx => ?_⟩
    have h := coe_symm_normalizerMulAut_apply e₁ ⟨t, htM⟩ (e₁ ⟨x, hx⟩)
    rw [← hα, ← hc] at h
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h
    exact h.symm
  obtain ⟨hperf, hcard⟩ := eqLocus_perfect_card_of_outer_F4 hK₁ α hα2 hαo
  have hP := inf_centralizer_eq_map_eqLocus e₁ htM
  refine ⟨?_, ?_⟩
  · rw [hP, ← map_commutator, hperf]
  · have hinj : Function.Injective (M.subtype.comp e₁.symm.toMonoidHom) :=
      M.subtype_injective.comp e₁.symm.injective
    rw [hP, card_map_of_injective hinj, hcard]

theorem false_of_outer_inner_F4_even (hset : StandardSetting G L) {e' : ℕ} (he : 1 ≤ e')
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ (2 * e')) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M₁ M₂ : Subgroup G}
    {K₁ K₂ : Type} [Field K₁] [Field K₂] (hK₁ : Nat.card K₁ = 2 ^ (2 * e'))
    (hK₂ : Nat.card K₂ = 2 ^ (2 * e')) (e₁ : M₁ ≃* adjointGroup .F4 K₁)
    (e₂ : M₂ ≃* adjointGroup .F4 K₂) (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (htM₁ : t ∈ normalizer (M₁ : Set G))
    (hout₁ : ¬ ∃ m ∈ M₁, ∀ x ∈ M₁, t * x * t⁻¹ = m * x * m⁻¹)
    (hin₂ : ∃ m ∈ M₂, ∀ x ∈ M₂, t * x * t⁻¹ = m * x * m⁻¹) : False := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  set C₁ := M₁ ⊓ centralizer ({t} : Set G) with hC₁
  obtain ⟨hC₁perf, hC₁card⟩ := perfect_card_inf_centralizer_of_outer_F4 ht hK₁ e₁ htM₁ hout₁
  obtain ⟨P₂, Q₂, hP₂, hP₂t, hP₂M, hQ₂P, hQ₂, hQ₂c⟩ :=
    exists_perfect_twoSubgroup_of_inner_F4 ht (by omega : 2 ≤ 2 * e') hK₂ e₂ hin₂
  have hdvd : 2 ^ (e' * 24) ∣ Nat.card C₁ := by
    obtain ⟨r, -, hr⟩ := (CFSG.Timmesfeld.Orders.profile_ordF4 he).two
    rw [hC₁card, hr]
    exact Dvd.intro r rfl
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  set S' := S.map C₁.subtype with hS'
  have hS'card : Nat.card S' = 2 ^ (e' * 24) := by
    rw [hS', card_map_of_injective C₁.subtype_injective, hS]
  have hS'2 : IsPGroup 2 S' := IsPGroup.of_card hS'card
  have hS'C₁ : S' ≤ C₁ := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hS'M₁ : S' ≤ M₁ := hS'C₁.trans inf_le_left
  have hPL : C₁ ⊔ P₂ ≤ L := std_perfect_le hset hOut htC ht
    (commutator_sup_eq_sup_of_perfect hC₁perf hP₂) (sup_le inf_le_right hP₂t)
  have hQ₁₂ : Q₂ ≤ centralizer (S' : Set G) := fun y hy =>
    (Subgroup.centralizer_le fun x hx => hS'M₁ hx) (h₁₂ ((hQ₂P.trans hP₂M) hy))
  have hdisj : S' ⊓ Q₂ = ⊥ := le_bot_iff.1 ((inf_le_inf hS'M₁ (hQ₂P.trans hP₂M)).trans
    (inf_eq_bot_of_le_centralizer_F4 e₁ h₁₂).le)
  have hle := natCard_le_of_le_of_isPGroup_two_F4 e ((sup_le_sup hS'C₁ hQ₂P).trans hPL)
    (isPGroup_sup_of_le_centralizer hQ₁₂ hS'2 hQ₂)
  rw [card_sup_eq_mul_of_le_centralizer hQ₁₂ hdisj, hS'card, hQ₂c, hK, ← pow_add,
    ← pow_mul] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
  omega

theorem false_of_outer_outer_F4_even (hset : StandardSetting G L) {e' : ℕ} (he : 1 ≤ e')
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ (2 * e')) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M₁ M₂ : Subgroup G}
    {K₁ K₂ : Type} [Field K₁] [Field K₂] (hK₁ : Nat.card K₁ = 2 ^ (2 * e'))
    (hK₂ : Nat.card K₂ = 2 ^ (2 * e')) (e₁ : M₁ ≃* adjointGroup .F4 K₁)
    (e₂ : M₂ ≃* adjointGroup .F4 K₂) (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (htM₁ : t ∈ normalizer (M₁ : Set G))
    (hout₁ : ¬ ∃ m ∈ M₁, ∀ x ∈ M₁, t * x * t⁻¹ = m * x * m⁻¹)
    (htM₂ : t ∈ normalizer (M₂ : Set G))
    (hout₂ : ¬ ∃ m ∈ M₂, ∀ x ∈ M₂, t * x * t⁻¹ = m * x * m⁻¹) : False := by
  have := finite_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK₁
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  set C₁ := M₁ ⊓ centralizer ({t} : Set G) with hC₁
  set C₂ := M₂ ⊓ centralizer ({t} : Set G) with hC₂
  obtain ⟨hC₁perf, hC₁card⟩ := perfect_card_inf_centralizer_of_outer_F4 ht hK₁ e₁ htM₁ hout₁
  obtain ⟨hC₂perf, hC₂card⟩ := perfect_card_inf_centralizer_of_outer_F4 ht hK₂ e₂ htM₂ hout₂
  have hPL : C₁ ⊔ C₂ ≤ L := std_perfect_le hset hOut htC ht
    (commutator_sup_eq_sup_of_perfect hC₁perf hC₂perf) (sup_le inf_le_right inf_le_right)
  have h12 : C₂ ≤ centralizer (C₁ : Set G) := fun y hy =>
    (Subgroup.centralizer_le fun x hx => (inf_le_left : C₁ ≤ M₁) hx)
      (h₁₂ ((inf_le_left : C₂ ≤ M₂) hy))
  have hdisj : C₁ ⊓ C₂ = ⊥ := le_bot_iff.1 ((inf_le_inf (inf_le_left : C₁ ≤ M₁)
    (inf_le_left : C₂ ≤ M₂)).trans (inf_eq_bot_of_le_centralizer_F4 e₁ h₁₂).le)
  have hdvd := Subgroup.card_dvd_of_le hPL
  rw [card_sup_eq_mul_of_le_centralizer h12 hdisj, hC₁card, hC₂card, Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK,
    show (2 : ℕ) ^ (2 * e') = (2 ^ e') ^ 2 by rw [← pow_mul, mul_comm], ← sq] at hdvd
  exact not_sq_ordF4_dvd_ordF4_sq he hdvd

end Standard

end CFSG.SeitzReduction.F4Pilot
