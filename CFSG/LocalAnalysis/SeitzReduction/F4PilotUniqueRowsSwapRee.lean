module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwap
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapF4

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag reeFixed)
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def reeOrderF4 (q : ℕ) : ℕ :=
  q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)

theorem ordF4_eq_reeOrderF4_mul (q : ℕ) (hq : 1 ≤ q) :
    CFSG.Open.ordF4 q = reeOrderF4 q *
      (q ^ 12 * (q ^ 6 - 1) * (q ^ 4 + 1) * (q ^ 3 - 1) * (q + 1)) := by
  have h : ∀ k, 1 ≤ q ^ k := fun k => Nat.one_le_pow _ _ hq
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  unfold CFSG.Open.ordF4 reeOrderF4
  zify [h 12, h 8, h 6, h 2, h 3, hq, h2, h4, (by omega : 1 ≤ q ^ 2 - q + 1)]
  ring

theorem two_pow_dvd_reeOrderF4 (f : ℕ) : 2 ^ (12 * f) ∣ reeOrderF4 (2 ^ f) := by
  unfold reeOrderF4
  rw [show (2 : ℕ) ^ (12 * f) = (2 ^ f) ^ 12 by rw [← pow_mul, mul_comm]]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (Dvd.dvd.mul_right (dvd_refl _) _) _) _) _) _

theorem not_sq_reeOrder_dvd_ordF4 (m : ℕ) :
    ¬ reeOrderF4 (2 ^ (2 * m + 1)) ^ 2 ∣ CFSG.Open.ordF4 (2 ^ (2 * m + 1)) := by
  intro h
  set q := 2 ^ (2 * m + 1) with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  set S := q ^ 12 * (q ^ 6 - 1) * (q ^ 4 + 1) * (q ^ 3 - 1) * (q + 1) with hS
  rw [ordF4_eq_reeOrderF4_mul q hq1, sq] at h
  have hpos : 0 < reeOrderF4 q := by
    have hq2 : 2 ≤ q := by
      rw [hqdef, pow_succ]
      have : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
      omega
    have h2 : q < q ^ 2 := by nlinarith
    have h4 : q ^ 2 < q ^ 4 := by
      have : q ^ 4 = q ^ 2 * q ^ 2 := by ring
      nlinarith
    unfold reeOrderF4
    have : 0 < q - 1 := by omega
    have : 0 < q ^ 2 - q + 1 := by omega
    have : 0 < q ^ 4 - q ^ 2 + 1 := by omega
    positivity
  have hdvd : reeOrderF4 q ∣ S := Nat.dvd_of_mul_dvd_mul_left hpos h
  have hq5 : ((q : ℕ) : ZMod 5) = 2 ∨ ((q : ℕ) : ZMod 5) = 3 := by
    rw [hqdef, Nat.cast_pow, pow_succ, pow_mul]
    have h4 : ((2 : ℕ) : ZMod 5) ^ 2 = -1 := by decide
    rw [h4]
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · left
      rw [show k + k = 2 * k by ring, pow_mul, neg_one_sq, one_pow, one_mul]
      rfl
    · right
      rw [pow_succ, show 2 * k = 2 * k by rfl, pow_mul, neg_one_sq, one_pow, one_mul]
      decide
  have h5N : 5 ∣ reeOrderF4 q := by
    have hsq : 5 ∣ q ^ 2 + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rcases hq5 with h | h <;> rw [h] <;> decide
    unfold reeOrderF4
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow hsq (by norm_num)) _)
      _) _
  have h5S : ¬ 5 ∣ S := by
    have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
    have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
    rw [← ZMod.natCast_eq_zero_iff, hS]
    push_cast [Nat.cast_sub hq3, Nat.cast_sub hq6]
    rcases hq5 with h | h <;> rw [h] <;> decide
  exact h5S (h5N.trans hdvd)

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}


omit [Finite G]
  in
theorem perfect_card_inf_centralizer_of_outer_F4_odd {t : G} (ht : orderOf t = 2)
    {M : Subgroup G} {m : ℕ} (hm : 1 ≤ m) {K₁ : Type} [Field K₁]
    (hK₁ : Nat.card K₁ = 2 ^ (2 * m + 1)) (e₁ : M ≃* adjointGroup .F4 K₁)
    (htM : t ∈ normalizer (M : Set G))
    (hout : ¬ ∃ x ∈ M, ∀ y ∈ M, t * y * t⁻¹ = x * y * x⁻¹) :
    ⁅M ⊓ centralizer ({t} : Set G), M ⊓ centralizer ({t} : Set G)⁆ =
        M ⊓ centralizer ({t} : Set G) ∧
      Nat.card (M ⊓ centralizer ({t} : Set G) : Subgroup G) = reeOrderF4 (2 ^ (2 * m + 1)) := by
  have := finite_of_natCard_eq_two_pow hK₁
  have hc2 := charP_two_of_natCard_eq_two_pow hK₁
  have hc : CharP K₁ ReeTag.F4.prime := hc2
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
  obtain ⟨ψ, -, -, hodd, hfix, -⟩ :=
    even_F4_all_outer_involutions_canonical (f := 2 * m + 1) (by omega) K₁ hK₁ α hα2 hαo
  obtain ⟨hree, -⟩ := hodd m rfl
  have hΓ : (ReeTag.F4.finiteExceptionalAut K₁ ^ (2 * m + 1)).toMonoidHom.eqLocus
      (MonoidHom.id _) = reeFixed ReeTag.F4 K₁ m := by
    rw [hree, CFSG.LieType.Ree.ReeTag.finiteReeAut_eq_reeAut]
    rfl
  have hK' : Nat.card K₁ = ReeTag.F4.prime ^ (2 * m + 1) := hK₁
  have hΓperf : ⁅reeFixed ReeTag.F4 K₁ m, reeFixed ReeTag.F4 K₁ m⁆ = reeFixed ReeTag.F4 K₁ m :=
    Subgroup.isPerfect_iff.1 ⟨CFSG.LieType.Simplicity.commutator_reeFixed_F4 m hm hK'⟩
  have hΓcard : Nat.card (reeFixed ReeTag.F4 K₁ m) = reeOrderF4 (2 ^ (2 * m + 1)) := by
    have h1 := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      m K₁ hK₁).1
    rw [CFSG.LieType.Ree.ReeTag.reeGamma_eq_reeFixedGroup,
      CFSG.LieType.Ree.reeFixedGroup_eq_map_reeFixed,
      card_map_of_injective (adjointGroup ReeTag.F4.tag K₁).subtype_injective] at h1
    exact h1
  let ψ' : MulAut (adjointGroup .F4 K₁) := ψ
  let Γ : Subgroup (adjointGroup .F4 K₁) := reeFixed ReeTag.F4 K₁ m
  have hfix' : (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ'.toMonoidHom = Γ :=
    hfix.trans hΓ
  have hΓperf' : ⁅Γ, Γ⁆ = Γ := hΓperf
  have hΓcard' : Nat.card Γ = reeOrderF4 (2 ^ (2 * m + 1)) := hΓcard
  have hαperf : ⁅α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .F4 K₁)),
      α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .F4 K₁))⁆ =
      α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .F4 K₁)) := by
    apply Subgroup.map_injective (f := ψ'.toMonoidHom) ψ'.injective
    rw [map_commutator, hfix', hΓperf']
  have hαcard : Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .F4 K₁))) =
      reeOrderF4 (2 ^ (2 * m + 1)) := by
    rw [← card_map_of_injective (f := ψ'.toMonoidHom) ψ'.injective, hfix', hΓcard']
  have hP := inf_centralizer_eq_map_eqLocus e₁ htM
  have hinj : Function.Injective (M.subtype.comp e₁.symm.toMonoidHom) :=
    M.subtype_injective.comp e₁.symm.injective
  refine ⟨?_, ?_⟩
  · rw [hP, ← map_commutator, hαperf]
  · rw [hP, card_map_of_injective hinj, hαcard]

theorem false_of_outer_inner_F4_odd (hset : StandardSetting G L) {m : ℕ} (hm : 1 ≤ m)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ (2 * m + 1)) (e : L ≃* adjointGroup .F4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M₁ M₂ : Subgroup G}
    {K₁ K₂ : Type} [Field K₁] [Field K₂] (hK₁ : Nat.card K₁ = 2 ^ (2 * m + 1))
    (hK₂ : Nat.card K₂ = 2 ^ (2 * m + 1)) (e₁ : M₁ ≃* adjointGroup .F4 K₁)
    (e₂ : M₂ ≃* adjointGroup .F4 K₂) (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (htM₁ : t ∈ normalizer (M₁ : Set G))
    (hout₁ : ¬ ∃ x ∈ M₁, ∀ y ∈ M₁, t * y * t⁻¹ = x * y * x⁻¹)
    (hin₂ : ∃ x ∈ M₂, ∀ y ∈ M₂, t * y * t⁻¹ = x * y * x⁻¹) : False := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  set C₁ := M₁ ⊓ centralizer ({t} : Set G) with hC₁
  obtain ⟨hC₁perf, hC₁card⟩ := perfect_card_inf_centralizer_of_outer_F4_odd ht hm hK₁ e₁ htM₁ hout₁
  obtain ⟨P₂, Q₂, hP₂, hP₂t, hP₂M, hQ₂P, hQ₂, hQ₂c⟩ :=
    exists_perfect_twoSubgroup_of_inner_F4 ht (by omega : 2 ≤ 2 * m + 1) hK₂ e₂ hin₂
  have hdvd : 2 ^ (12 * (2 * m + 1)) ∣ Nat.card C₁ := by
    rw [hC₁card]
    exact two_pow_dvd_reeOrderF4 _
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  set S' := S.map C₁.subtype with hS'
  have hS'card : Nat.card S' = 2 ^ (12 * (2 * m + 1)) := by
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

theorem false_of_outer_outer_F4_odd (hset : StandardSetting G L) {m : ℕ} (hm : 1 ≤ m)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ (2 * m + 1)) (e : L ≃* adjointGroup .F4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M₁ M₂ : Subgroup G}
    {K₁ K₂ : Type} [Field K₁] [Field K₂] (hK₁ : Nat.card K₁ = 2 ^ (2 * m + 1))
    (hK₂ : Nat.card K₂ = 2 ^ (2 * m + 1)) (e₁ : M₁ ≃* adjointGroup .F4 K₁)
    (e₂ : M₂ ≃* adjointGroup .F4 K₂) (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (htM₁ : t ∈ normalizer (M₁ : Set G))
    (hout₁ : ¬ ∃ x ∈ M₁, ∀ y ∈ M₁, t * y * t⁻¹ = x * y * x⁻¹)
    (htM₂ : t ∈ normalizer (M₂ : Set G))
    (hout₂ : ¬ ∃ x ∈ M₂, ∀ y ∈ M₂, t * y * t⁻¹ = x * y * x⁻¹) : False := by
  have := finite_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK₁
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  set C₁ := M₁ ⊓ centralizer ({t} : Set G) with hC₁
  set C₂ := M₂ ⊓ centralizer ({t} : Set G) with hC₂
  obtain ⟨hC₁perf, hC₁card⟩ := perfect_card_inf_centralizer_of_outer_F4_odd ht hm hK₁ e₁ htM₁ hout₁
  obtain ⟨hC₂perf, hC₂card⟩ := perfect_card_inf_centralizer_of_outer_F4_odd ht hm hK₂ e₂ htM₂ hout₂
  have hPL : C₁ ⊔ C₂ ≤ L := std_perfect_le hset hOut htC ht
    (commutator_sup_eq_sup_of_perfect hC₁perf hC₂perf) (sup_le inf_le_right inf_le_right)
  have h12 : C₂ ≤ centralizer (C₁ : Set G) := fun y hy =>
    (Subgroup.centralizer_le fun x hx => (inf_le_left : C₁ ≤ M₁) hx)
      (h₁₂ ((inf_le_left : C₂ ≤ M₂) hy))
  have hdisj : C₁ ⊓ C₂ = ⊥ := le_bot_iff.1 ((inf_le_inf (inf_le_left : C₁ ≤ M₁)
    (inf_le_left : C₂ ≤ M₂)).trans (inf_eq_bot_of_le_centralizer_F4 e₁ h₁₂).le)
  have hdvd := Subgroup.card_dvd_of_le hPL
  rw [card_sup_eq_mul_of_le_centralizer h12 hdisj, hC₁card, hC₂card, Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK, ← sq] at hdvd
  exact not_sq_reeOrder_dvd_ordF4 m hdvd

theorem false_of_mem_normalizer_both_F4 (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M₁ M₂ : Subgroup G}
    {K₁ K₂ : Type} [Field K₁] [Field K₂] (hK₁ : Nat.card K₁ = 2 ^ f)
    (hK₂ : Nat.card K₂ = 2 ^ f) (e₁ : M₁ ≃* adjointGroup .F4 K₁)
    (e₂ : M₂ ≃* adjointGroup .F4 K₂) (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (htM₁ : t ∈ normalizer (M₁ : Set G)) (htM₂ : t ∈ normalizer (M₂ : Set G)) : False := by
  have h₂₁ : M₁ ≤ centralizer (M₂ : Set G) := le_centralizer_iff.1 h₁₂
  by_cases hin₁ : ∃ x ∈ M₁, ∀ y ∈ M₁, t * y * t⁻¹ = x * y * x⁻¹
  · by_cases hin₂ : ∃ x ∈ M₂, ∀ y ∈ M₂, t * y * t⁻¹ = x * y * x⁻¹
    · exact false_of_inner_inner_F4 hset hf hK e htC ht hK₁ hK₂ e₁ e₂ h₁₂ hin₁ hin₂
    · rcases Nat.even_or_odd' f with ⟨e', rfl | rfl⟩
      · exact false_of_outer_inner_F4_even hset (by omega) hK e htC ht hK₂ hK₁ e₂ e₁ h₂₁ htM₂
          hin₂ hin₁
      · exact false_of_outer_inner_F4_odd hset (by omega) hK e htC ht hK₂ hK₁ e₂ e₁ h₂₁ htM₂
          hin₂ hin₁
  · by_cases hin₂ : ∃ x ∈ M₂, ∀ y ∈ M₂, t * y * t⁻¹ = x * y * x⁻¹
    · rcases Nat.even_or_odd' f with ⟨e', rfl | rfl⟩
      · exact false_of_outer_inner_F4_even hset (by omega) hK e htC ht hK₁ hK₂ e₁ e₂ h₁₂ htM₁
          hin₁ hin₂
      · exact false_of_outer_inner_F4_odd hset (by omega) hK e htC ht hK₁ hK₂ e₁ e₂ h₁₂ htM₁
          hin₁ hin₂
    · rcases Nat.even_or_odd' f with ⟨e', rfl | rfl⟩
      · exact false_of_outer_outer_F4_even hset (by omega) hK e htC ht hK₁ hK₂ e₁ e₂ h₁₂ htM₁
          hin₁ htM₂ hin₂
      · exact false_of_outer_outer_F4_odd hset (by omega) hK e htC ht hK₁ hK₂ e₁ e₂ h₁₂ htM₁
          hin₁ htM₂ hin₂

theorem swap_and_inf_centralizer_eq_of_mem_normalizer_F4 (hset : StandardSetting G L) {f : ℕ}
    (hf : 2 ≤ f) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M₁ M₂ : Subgroup G}
    {K₁ K₂ : Type} [Field K₁] [Field K₂] (hK₁ : Nat.card K₁ = 2 ^ f)
    (hK₂ : Nat.card K₂ = 2 ^ f) (e₁ : M₁ ≃* adjointGroup .F4 K₁)
    (e₂ : M₂ ≃* adjointGroup .F4 K₂) (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (htM : t ∈ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G)) :
    M₁.map (MulAut.conj t).toMonoidHom = M₂ ∧ (M₁ ⊔ M₂) ⊓ centralizer ({t} : Set G) = L := by
  have := finite_of_natCard_eq_two_pow hK₁
  have := finite_of_natCard_eq_two_pow hK₂
  have hf1 : 1 ≤ f := by omega
  have hs₁ : IsSimpleGroup M₁ := isSimpleGroup_of_mulEquiv_adjointGroup_F4 hf1 hK₁ e₁
  have hs₂ : IsSimpleGroup M₂ := isSimpleGroup_of_mulEquiv_adjointGroup_F4 hf1 hK₂ e₂
  have hna₁ := exists_mul_ne_mul_of_mulEquiv_adjointGroup_F4 e₁
  have hna₂ := exists_mul_ne_mul_of_mulEquiv_adjointGroup_F4 e₂
  have h₂₁ : M₁ ≤ centralizer (M₂ : Set G) := le_centralizer_iff.1 h₁₂
  rcases map_conj_eq_or_eq_of_isSimpleGroup h₁₂ hs₁ hs₂ hna₁ htM with h | h
  · exfalso
    have htM₁ : t ∈ normalizer (M₁ : Set G) := mem_normalizer_iff_map_conj_toMonoidHom.2 h
    have htM' : t ∈ normalizer ((M₂ ⊔ M₁ : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact htM
    have htM₂ : t ∈ normalizer (M₂ : Set G) := by
      rcases map_conj_eq_or_eq_of_isSimpleGroup h₂₁ hs₂ hs₁ hna₂ htM' with h' | h'
      · exact mem_normalizer_iff_map_conj_toMonoidHom.2 h'
      · exact absurd (map_conj_toMonoidHom_inj.1 (h.trans h'.symm))
          (ne_of_le_centralizer_of_exists_ne h₁₂ hna₁)
    exact false_of_mem_normalizer_both_F4 hset hf hK e htC ht hK₁ hK₂ e₁ e₂ h₁₂ htM₁ htM₂
  · exact ⟨h, inf_centralizer_eq_of_swap_F4 hset hK e htC ht hK₁ e₁ h₁₂ h⟩

end Standard

end CFSG.SeitzReduction.F4Pilot
