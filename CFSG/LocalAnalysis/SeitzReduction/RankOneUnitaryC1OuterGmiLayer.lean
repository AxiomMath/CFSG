module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiCore
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiCat
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.Open
open scoped MatrixGroups commutatorElement

@[expose] def gmiOmega {X : Type} [Group X] (Q : Sylow 2 X) : Subgroup X :=
  Subgroup.closure {x | x ∈ (Q : Subgroup X) ⊓ goldschmidtLayer X ∧ x ^ 2 = 1}

theorem gmi_card_inf_centralizer {X : Type} [Group X] (K : Subgroup X) :
    Nat.card (K ⊓ centralizer (K : Set X) : Subgroup X) = Nat.card (Subgroup.center K) := by
  rw [CFSG.GroupTheory.inf_centralizer_eq_map_center,
    Subgroup.card_map_of_injective K.subtype_injective]

structure GmiLayerHyp (X : Type) [Group X] [Finite X] (f : ℕ) (Q : Sylow 2 X)
    (J F A₁ K₀ Dv : Subgroup X) (v e : X) (τ : MulAut X) : Prop where
  odd : CFSG.oddCore X = ⊥
  gen : CFSG.Open.pCore 2 X ⊔ goldschmidtLayer X = ⊤
  J_eq : J = CFSG.Open.pCore 2 X ⊔ gmiOmega Q
  type : ∀ K : Subgroup X, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K)
  J_comm : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a
  F_le : F ≤ J
  F_sq : ∀ x ∈ F, x ^ 2 = 1
  card_F : Nat.card F = (2 ^ f) ^ 2
  two_le : 2 ≤ f
  even : Even f
  v_mem : v ∈ J
  v_comm : ∀ y : X, v * y = y * v
  v_not_mem : v ∉ F
  v_sq : v ^ 2 = 1
  L4 : ∀ Y : Subgroup X, Y ≤ Q → (∀ y ∈ Y, ∀ a ∈ F ⊔ zpowers v, y * a = a * y) →
    Nat.card Y ≤ 2 * Nat.card (Y ⊓ (F ⊔ zpowers v) : Subgroup X)
  L6 : Nat.card (Q : Subgroup X) ≤ 8 * f * (2 ^ f) ^ 2
  K₀_iso : Nonempty (K₀ ≃* PSL(2, GaloisField 2 f))
  K₀_simple : ∀ N : Subgroup X, N ≤ K₀ → (∀ k ∈ K₀, ∀ x ∈ N, k * x * k⁻¹ ∈ N) →
    N = ⊥ ∨ N = K₀
  K₀_perfect : K₀ ≤ ⁅K₀, K₀⁆
  card_K₀ : Nat.card K₀ = 2 ^ f * ((2 ^ f) ^ 2 - 1)
  A₁_le_K₀ : A₁ ≤ K₀
  A₁_le_F : A₁ ≤ F
  card_A₁ : Nat.card A₁ = 2 ^ f
  e_mem : e ∈ K₀
  e_F : ∀ x ∈ F, e * x * e⁻¹ ∈ F
  e_fix : ∀ x ∈ F, e * x * e⁻¹ = x → x = 1
  τ_inv : ∀ x, τ (τ x) = x
  τ_K₀ : ∀ x ∈ K₀, τ x = x
  τ_F : ∀ x ∈ F, τ x ∈ F
  τ_Q : ∀ x ∈ (Q : Subgroup X), τ x ∈ (Q : Subgroup X)
  τ_move : ∃ x ∈ F, τ x ≠ x
  D_le : Dv ≤ K₀
  D_odd : Odd (Nat.card Dv)
  D_τ : ∀ x ∈ Dv, τ x = x
  D_F : ∀ d ∈ Dv, ∀ x ∈ F, d * x * d⁻¹ ∈ F

namespace GmiLayerHyp

variable {X : Type} [Group X] [Finite X] {f : ℕ} {Q : Sylow 2 X} {J F A₁ K₀ Dv : Subgroup X}
  {v e : X} {τ : MulAut X} (h : GmiLayerHyp X f Q J F A₁ K₀ Dv v e τ)
include h

theorem layer_eq : goldschmidtLayer X = CFSG.layer X :=
  CFSG.ComponentClassification.AschbacherTheorem3.goldschmidtLayer_eq_layer X

theorem layer_normal : (CFSG.layer X).Normal := by
  have := CFSG.LocalCores.layer_characteristic (G := X)
  infer_instance

theorem pCore_comm_layer {z y : X} (hz : z ∈ CFSG.Open.pCore 2 X) (hy : y ∈ CFSG.layer X) :
    z * y = y * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzF : z ∈ fittingSubgroup X := by
    exact CFSG.pCore_le_fitting X 2 hz
  have hc : ⁅z, y⁆ ∈ ⁅fittingSubgroup X, CFSG.layer X⁆ :=
    Subgroup.commutator_mem_commutator hzF hy
  rw [CFSG.LocalCores.fitting_layer_commute (G := X)] at hc
  have h1 : z * y * z⁻¹ * y⁻¹ = 1 := by
    rw [← commutatorElement_def]
    exact Subgroup.mem_bot.mp hc
  calc z * y = (z * y * z⁻¹ * y⁻¹) * (y * z) := by group
    _ = y * z := by rw [h1, one_mul]

theorem exists_mul (x : X) : ∃ z ∈ CFSG.Open.pCore 2 X, ∃ y ∈ CFSG.layer X, z * y = x := by
  have hx : x ∈ CFSG.Open.pCore 2 X ⊔ CFSG.layer X := by
    rw [← h.layer_eq, h.gen]
    exact mem_top x
  exact ncyc_exists_mul_of_mem_sup (fun z _ => gmi_top_le_normalizer h.layer_normal (mem_top z)) hx

theorem pCore_le_J : CFSG.Open.pCore 2 X ≤ J := h.J_eq ▸ le_sup_left

theorem omega_le_J : gmiOmega Q ≤ J := h.J_eq ▸ le_sup_right

theorem pCore_comm {z : X} (hz : z ∈ CFSG.Open.pCore 2 X) (y : X) : z * y = y * z := by
  obtain ⟨z', hz', y', hy', rfl⟩ := h.exists_mul y
  have h1 : z * z' = z' * z := h.J_comm z (h.pCore_le_J hz) z' (h.pCore_le_J hz')
  have h2 : z * y' = y' * z := h.pCore_comm_layer hz hy'
  calc z * (z' * y') = (z * z') * y' := (mul_assoc _ _ _).symm
    _ = z' * (z * y') := by rw [h1, mul_assoc]
    _ = z' * y' * z := by rw [h2, mul_assoc]

theorem exists_pow_eq_one_of_central {z : X} (hz : ∀ y : X, z * y = y * z) :
    ∃ k : ℕ, z ^ 2 ^ k = 1 := by
  obtain ⟨a, m, hm, hdec⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  set y := z ^ 2 ^ a with hy
  have hym : y ^ m = 1 := by rw [hy, ← pow_mul, ← hdec, pow_orderOf_eq_one]
  have hyodd : Odd (orderOf y) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hym)
  have hyc : ∀ g : X, g * y = y * g := fun g => by
    rw [hy]
    exact ((Commute.pow_left (hz g) (2 ^ a))).eq.symm
  have hN : (zpowers y).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [show g * x * g⁻¹ = x by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      rw [((Commute.zpow_left (hyc g).symm k)).eq.symm, mul_inv_cancel_right]]
    exact hx
  have hodd : Odd (Nat.card (zpowers y)) := by rw [Nat.card_zpowers]; exact hyodd
  have hle : zpowers y ≤ CFSG.oddCore X := le_sSup ⟨hN, hodd⟩
  rw [h.odd] at hle
  exact ⟨a, Subgroup.mem_bot.mp (hle (mem_zpowers y))⟩

theorem component_normal {K : Subgroup X} (hK : CFSG.IsComponent K) : K.Normal := by
  have hE : CFSG.layer X ≤ normalizer (K : Set X) := CFSG.LocalCores.layer_le_normalizer hK
  have hP : CFSG.Open.pCore 2 X ≤ normalizer (K : Set X) := fun z hz =>
    mem_normalizer_iff.mpr fun k => by rw [h.pCore_comm hz k, mul_inv_cancel_right]
  rw [← normalizer_eq_top_iff, eq_top_iff, ← h.gen, h.layer_eq]
  exact sup_le hP hE

theorem sup_centralizer {K : Subgroup X} (hK : CFSG.IsComponent K) :
    K ⊔ centralizer (K : Set X) = ⊤ := by
  have hE : CFSG.layer X ≤ K ⊔ centralizer (K : Set X) := by
    refine sSup_le fun K₂ hK₂ => ?_
    rcases CFSG.LocalCores.distinct_components_commute hK₂ hK with rfl | hne
    · exact le_sup_left
    · exact le_sup_of_le_right (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hne)
  have hP : CFSG.Open.pCore 2 X ≤ centralizer (K : Set X) := fun z hz =>
    mem_centralizer_iff.mpr fun k _ => (h.pCore_comm hz k).symm
  rw [eq_top_iff, ← h.gen, h.layer_eq]
  exact sup_le (hP.trans le_sup_right) hE

theorem centralizer_normal {K : Subgroup X} (hK : CFSG.IsComponent K) :
    (centralizer (K : Set X)).Normal := by
  have := h.component_normal hK
  infer_instance

theorem comm_of_mem_inf {K : Subgroup X} (hK : CFSG.IsComponent K) {z : X}
    (hz : z ∈ K ⊓ centralizer (K : Set X)) (y : X) : z * y = y * z := by
  have hy : y ∈ K ⊔ centralizer (K : Set X) := by rw [h.sup_centralizer hK]; exact mem_top y
  obtain ⟨k, hk, c, hc, rfl⟩ := ncyc_exists_mul_of_mem_sup
    (fun k _ => gmi_top_le_normalizer (h.centralizer_normal hK) (mem_top k)) hy
  obtain ⟨hzK, hzC⟩ := mem_inf.mp hz
  have h1 : z * k = k * z := (mem_centralizer_iff.mp hzC k hk).symm
  have h2 : z * c = c * z := mem_centralizer_iff.mp hc z hzK
  calc z * (k * c) = k * (z * c) := by rw [← mul_assoc, h1, mul_assoc]
    _ = k * c * z := by rw [h2, mul_assoc]

theorem center_isPGroup {K : Subgroup X} (hK : CFSG.IsComponent K) :
    IsPGroup 2 (Subgroup.center K) := by
  intro g
  have hz : ((g : K) : X) ∈ K ⊓ centralizer (K : Set X) := by
    refine mem_inf.mpr ⟨(g : K).2, mem_centralizer_iff.mpr fun k hk => ?_⟩
    have := Subgroup.mem_center_iff.mp g.2 ⟨k, hk⟩
    exact congrArg Subtype.val this
  obtain ⟨n, hn⟩ := h.exists_pow_eq_one_of_central (h.comm_of_mem_inf hK hz)
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  simpa using hn

theorem commutator_le_layer : ⁅(⊤ : Subgroup X), ⊤⁆ ≤ CFSG.layer X := by
  have key1 : ∀ {z y b : X}, (∀ x, z * x = x * z) → ⁅z * y, b⁆ = ⁅y, b⁆ := by
    intro z y b hz
    rw [commutatorElement_def, commutatorElement_def]
    calc z * y * b * (z * y)⁻¹ * b⁻¹ = z * (y * b * y⁻¹) * z⁻¹ * b⁻¹ := by group
      _ = (y * b * y⁻¹) * z * z⁻¹ * b⁻¹ := by rw [hz]
      _ = y * b * y⁻¹ * b⁻¹ := by group
  have key2 : ∀ {z y a : X}, (∀ x, z * x = x * z) → ⁅a, z * y⁆ = ⁅a, y⁆ := by
    intro z y a hz
    rw [commutatorElement_def, commutatorElement_def]
    calc a * (z * y) * a⁻¹ * (z * y)⁻¹ = (a * z) * y * a⁻¹ * y⁻¹ * z⁻¹ := by group
      _ = z * a * y * a⁻¹ * y⁻¹ * z⁻¹ := by rw [← hz a]
      _ = z * (a * y * a⁻¹ * y⁻¹) * z⁻¹ := by group
      _ = (a * y * a⁻¹ * y⁻¹) * z * z⁻¹ := by rw [hz]
      _ = a * y * a⁻¹ * y⁻¹ := by group
  rw [Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨z₁, hz₁, y₁, hy₁, rfl⟩ := h.exists_mul a
  obtain ⟨z₂, hz₂, y₂, hy₂, rfl⟩ := h.exists_mul b
  rw [key1 (h.pCore_comm hz₁), key2 (h.pCore_comm hz₂), commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hy₁ hy₂) (inv_mem hy₁)) (inv_mem hy₂)

theorem K₀_le_layer : K₀ ≤ CFSG.layer X :=
  h.K₀_perfect.trans ((Subgroup.commutator_mono le_top le_top).trans h.commutator_le_layer)

theorem F_le_layer : F ≤ CFSG.layer X :=
  gmi_le_of_fixedPointFree (h.K₀_le_layer h.e_mem)
    (fun x _ n hn => h.layer_normal.conj_mem n hn x) h.e_F h.e_fix

theorem omega_le_layer : gmiOmega Q ≤ CFSG.layer X := by
  rw [gmiOmega, Subgroup.closure_le]
  rintro x ⟨hx, -⟩
  rw [← h.layer_eq]
  exact (mem_inf.mp hx).2

theorem omega_le_Q : gmiOmega Q ≤ (Q : Subgroup X) := by
  rw [gmiOmega, Subgroup.closure_le]
  rintro x ⟨hx, -⟩
  exact (mem_inf.mp hx).1

theorem omega_sq {x : X} (hx : x ∈ gmiOmega Q) : x ^ 2 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => exact one_pow 2
  | mul a b ha hb iha ihb =>
    have hab : Commute a b := h.J_comm a (h.omega_le_J ha) b (h.omega_le_J hb)
    rw [hab.mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem mem_omega {x : X} (hxQ : x ∈ (Q : Subgroup X)) (hxE : x ∈ CFSG.layer X)
    (hx2 : x ^ 2 = 1) : x ∈ gmiOmega Q :=
  subset_closure ⟨mem_inf.mpr ⟨hxQ, h.layer_eq ▸ hxE⟩, hx2⟩

theorem pCore_le_Q : CFSG.Open.pCore 2 X ≤ (Q : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  have hsup := hp.to_sup_of_normal_left Q.isPGroup'
  have heq := Q.is_maximal' hsup le_sup_right
  rw [← heq]
  exact le_sup_left

theorem J_le_Q : J ≤ (Q : Subgroup X) := h.J_eq ▸ sup_le h.pCore_le_Q h.omega_le_Q

theorem F_le_omega : F ≤ gmiOmega Q := fun x hx =>
  h.mem_omega (h.J_le_Q (h.F_le hx)) (h.F_le_layer hx) (h.F_sq x hx)

theorem isSylowOf_inf {K : Subgroup X} (hK : CFSG.IsComponent K) :
    IsSylowOf 2 ((Q : Subgroup X) ⊓ K) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (gmi_isSylowOf_top Q).inf_of_le_normalizer le_top
    (gmi_top_le_normalizer (h.component_normal hK))

theorem exists_mul_of_mem_Q {K : Subgroup X} (hK : CFSG.IsComponent K) {x : X}
    (hx : x ∈ (Q : Subgroup X)) :
    ∃ a ∈ (Q : Subgroup X) ⊓ K, ∃ b ∈ (Q : Subgroup X) ⊓ centralizer (K : Set X), a * b = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact gmi_exists_mul_of_sylow (gmi_isSylowOf_top Q) (h.component_normal hK)
    (h.centralizer_normal hK) (h.sup_centralizer hK) hx

theorem not_K₀_le_centralizer (hC4 : GmiCatFourInput) {K : Subgroup X}
    (hK : CFSG.IsComponent K) : ¬ K₀ ≤ centralizer (K : Set X) := by
  intro hK₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCn := h.centralizer_normal hK
  have hFC : F ≤ centralizer (K : Set X) :=
    gmi_le_of_fixedPointFree (hK₀ h.e_mem) (fun x _ n hn => hCn.conj_mem n hn x) h.e_F h.e_fix
  have hvC : v ∈ centralizer (K : Set X) := mem_centralizer_iff.mpr fun k _ => (h.v_comm k).symm
  have hAC : F ⊔ zpowers v ≤ centralizer (K : Set X) := sup_le hFC (zpowers_le.mpr hvC)
  set T := (Q : Subgroup X) ⊓ K with hT
  have hTS := h.isSylowOf_inf hK
  have hTc : ∀ y ∈ T, ∀ a ∈ F ⊔ zpowers v, y * a = a * y := fun y hy a ha =>
    mem_centralizer_iff.mp (hAC ha) y (mem_inf.mp hy).2
  have h1 := h.L4 T inf_le_left hTc
  have hle2 : T ⊓ (F ⊔ zpowers v) ≤ K ⊓ centralizer (K : Set X) := fun x hx =>
    mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hx).1).2, hAC (mem_inf.mp hx).2⟩
  have h2 := Subgroup.card_le_of_le hle2
  rw [gmi_card_inf_centralizer] at h2
  have h4 := hC4 _ (h.type K ((CFSG.isComponent_iff_open K).mp hK))
  have hKcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  obtain ⟨c, hc⟩ := (h.center_isPGroup hK).exists_card_eq
  have hdvd : 2 ^ (c + 2) ∣ Nat.card K := by
    have h4' : 2 ^ 2 ∣ Nat.card (K ⧸ Subgroup.center K) := by norm_num; exact h4
    rw [hKcard, hc, pow_add, mul_comm (2 ^ c)]
    exact Nat.mul_dvd_mul_right h4' _
  have hTdvd : 2 ^ (c + 2) ∣ Nat.card T := by
    rw [hTS.card_eq]
    refine pow_dvd_pow 2 ?_
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  have hle := Nat.le_of_dvd Nat.card_pos hTdvd
  rw [hc] at h2
  rw [pow_add] at hle
  have hpos : 0 < 2 ^ c := pow_pos (by norm_num) c
  omega

theorem K₀_inf_centralizer (hC4 : GmiCatFourInput) {K : Subgroup X} (hK : CFSG.IsComponent K) :
    K₀ ⊓ centralizer (K : Set X) = ⊥ := by
  have hCn := h.centralizer_normal hK
  refine (h.K₀_simple _ inf_le_left fun k hk x hx =>
    mem_inf.mpr ⟨mul_mem (mul_mem hk (mem_inf.mp hx).1) (inv_mem hk),
      hCn.conj_mem x (mem_inf.mp hx).2 k⟩).resolve_right fun heq => ?_
  exact h.not_K₀_le_centralizer hC4 hK (by rw [← heq]; exact inf_le_right)

theorem card_K₀_dvd (hC4 : GmiCatFourInput) {K : Subgroup X} (hK : CFSG.IsComponent K) :
    Nat.card K₀ ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have hCn := h.centralizer_normal hK
  set C := centralizer (K : Set X) with hC
  have hK₀C := h.K₀_inf_centralizer hC4 hK
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer (A := C)
    (B := K₀) (fun x _ => gmi_top_le_normalizer hCn (mem_top x))
  rw [inf_comm, hK₀C, Subgroup.card_bot, mul_one] at h1
  have h2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer (A := C)
    (B := K) (fun x _ => gmi_top_le_normalizer hCn (mem_top x))
  rw [sup_comm, h.sup_centralizer hK, Subgroup.card_top, inf_comm, gmi_card_inf_centralizer] at h2
  have h3 : Nat.card (C ⊔ K₀ : Subgroup X) ∣ Nat.card X := Subgroup.card_subgroup_dvd_card _
  rw [h1] at h3
  have hKcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hZpos : 0 < Nat.card (Subgroup.center K) := Nat.card_pos
  have h4 : Nat.card C * (Nat.card K₀ * Nat.card (Subgroup.center K)) ∣
      Nat.card C * (Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center K)) := by
    rw [← hKcard, ← h2, ← mul_assoc]
    exact Nat.mul_dvd_mul_right h3 _
  exact Nat.dvd_of_mul_dvd_mul_right hZpos (Nat.dvd_of_mul_dvd_mul_left hCpos h4)

end GmiLayerHyp

end CFSG.SeitzReduction.RankOne
