module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneProjectiveEightLayerChain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint
open CFSG.ComponentClassification.GMS78.Finkelstein (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Conj

variable {G : Type} [Group G]

theorem coe_normalizerMonoidHom_pow_apply (H : Subgroup G) {g : G}
    (hg : g ∈ normalizer (H : Set G)) (k : ℕ) (u : H) :
    (((H.normalizerMonoidHom ⟨g, hg⟩ ^ k) u : H) : G) = g ^ k * u * (g ^ k)⁻¹ := by
  rw [← map_pow, Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

end Conj

namespace LinearPushChain

variable {G : Type} [Group G] {t d : G} {T A : Subgroup G} {f m : ℕ} {C : ℕ → Subgroup G}

theorem truncate (h : LinearPushChain t d T A f (m + 1) C) : LinearPushChain t d T A f m C := by
  refine ⟨h.zero, h.base, fun j hj => h.mono j (by omega), fun j hj => h.card j (by omega),
    fun j hj => h.normal j (by omega), fun j hj => h.layer_sq j (by omega),
    fun j hj => h.layer_comm j (by omega), fun j hj => h.t_norm j (by omega),
    fun ht => h.t_not_mem (h.mono (m + 1) le_rfl ht), fun j h1 hj => h.comm_t j h1 (by omega),
    fun j h1 hj => h.comm_t_ker j h1 (by omega), fun j h1 hj => h.comm_t_onto j h1 (by omega),
    ?_, h.d_comm, h.d_order, fun j hj => h.d_norm j (by omega), h.d_reg,
    fun j hj => h.T_norm j (by omega)⟩
  refine le_antisymm ?_ ?_
  · rw [← h.centralizer_t]
    exact inf_le_inf_right _ (h.mono (m + 1) le_rfl)
  · have h1 : A ≤ C (m + 1) := h.base ▸ h.le_of_le (by omega) (by omega)
    have h2 : A ≤ centralizer ({t} : Set G) := h.centralizer_t ▸ inf_le_right
    exact le_inf h1 h2

theorem base_le (h : LinearPushChain t d T A f m C) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ m + 1) :
    A ≤ C j :=
  h.base ▸ h.le_of_le hj1 hj

theorem base_le_centralizer (h : LinearPushChain t d T A f m C) :
    A ≤ centralizer ({t} : Set G) :=
  h.centralizer_t ▸ inf_le_right

theorem mem_base_of_commute (h : LinearPushChain t d T A f m C) {j : ℕ} (hj : j ≤ m + 1)
    {x : G} (hx : x ∈ C j) (hxt : x * t = t * x) : x ∈ A := by
  rw [← h.centralizer_t]
  refine mem_inf.mpr ⟨h.le_of_le hj le_rfl hx, mem_centralizer_iff.mpr fun y hy => ?_⟩
  rw [Set.mem_singleton_iff.mp hy]
  exact hxt.symm

variable [Finite G]

theorem inv_of_one_le (h : LinearPushChain t d T A f m C) (hm : 1 ≤ m) (htt : t * t = 1) :
    ∀ c ∈ C m, t * c * t⁻¹ = c⁻¹ :=
  inv_of_forall_conj_eq_mul htt (h.exists_conj_eq_mul hm)

theorem comm_of_one_le (h : LinearPushChain t d T A f m C) (hm : 1 ≤ m) (htt : t * t = 1) :
    ∀ a ∈ C m, ∀ b ∈ C m, a * b = b * a :=
  comm_of_forall_conj_eq_inv (h.inv_of_one_le hm htt)

theorem mem_iff_pow_of_le (h : LinearPushChain t d T A f m C) (hm : 1 ≤ m) (htt : t * t = 1) :
    ∀ j ≤ m, ∀ x ∈ C m, x ∈ C j ↔ x ^ 2 ^ j = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact h.truncate.mem_iff_pow_two_pow_eq_one (h.inv_of_one_le hm htt)

theorem normalizer_le_of_one_le (h : LinearPushChain t d T A f m C) (hm : 1 ≤ m)
    (htt : t * t = 1) : normalizer (C m : Set G) ≤ pushNormalizer C (m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact h.truncate.normalizer_le_pushNormalizer (h.inv_of_one_le hm htt)

theorem mem_base_of_sq_eq_one (h : LinearPushChain t d T A f m C) (hm : 1 ≤ m)
    (htt : t * t = 1) {x : G} (hx : x ∈ C m) (hxx : x * x = 1) : x ∈ A := by
  have h1 := (h.mem_iff_pow_of_le hm htt 1 hm x hx).mpr (by rw [pow_one, sq]; exact hxx)
  rwa [h.base] at h1

theorem exists_sq_eq_of_two_le (h : LinearPushChain t d T A f m C) (hm : 2 ≤ m)
    (htt : t * t = 1) : ∀ a ∈ A, ∃ x ∈ C m, x * x = a := by
  intro a ha
  obtain ⟨x, hx, hxa⟩ := h.comm_t_onto 1 le_rfl (by omega) a (h.base ▸ ha)
  rw [Nat.sub_self, h.zero, mem_bot, inv_mul_eq_one] at hxa
  have hxm : x ∈ C m := h.le_of_le (by omega) (by omega) hx
  have hinv := h.inv_of_one_le (by omega) htt x hxm
  refine ⟨x, hxm, ?_⟩
  rw [hxa]
  have h1 : t * x⁻¹ * t⁻¹ = x := by
    rw [show t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group, hinv, inv_inv]
  calc x * x = x * (t * x⁻¹ * t⁻¹) := by rw [h1]
    _ = x * t * x⁻¹ * t⁻¹ := by group


omit [Finite G] in
theorem mem_fixSubgroup_iff (h : LinearPushChain t d T A f m C) {j : ℕ} (hj : j ≤ m + 1)
    (u : C j) :
    u ∈ fixSubgroup ((C j).normalizerMonoidHom ⟨t, h.t_norm j hj⟩) ↔ (u : G) ∈ A := by
  rw [mem_fixSubgroup]
  constructor
  · intro hu
    have h1 := congrArg Subtype.val hu
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    exact h.mem_base_of_commute hj u.2 (by
      calc (u : G) * t = t * u * t⁻¹ * t := by rw [h1]
        _ = t * u := by group)
  · intro hu
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hc := mem_centralizer_iff.mp (h.base_le_centralizer hu) t (Set.mem_singleton t)
    show t * (u : G) * t⁻¹ = u
    rw [hc]
    group

omit [Finite G] in
theorem exists_base_ne_one (h : LinearPushChain t d T A f m C) (hf : 1 ≤ f) :
    ∃ a ∈ A, a ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hAb : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hcon
  have h1 := h.card 1 (by omega)
  rw [h.base, hAb, card_bot, mul_one] at h1
  have h2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

omit [Finite G] in
theorem eq_of_conj_eq_of_le (h : LinearPushChain t d T A f m C)
    (hdfix : ∀ k : ℕ, ∀ a ∈ A, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1)
    {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) {k k' : ℕ} (hkk : k ≤ k') (hk' : k' < 2 ^ f - 1)
    (h1 : d ^ k * a * (d ^ k)⁻¹ = b) (h2 : d ^ k' * a * (d ^ k')⁻¹ = b) : k = k' := by
  have hbA : b ∈ A := by
    rw [← h1]
    have hdA : d ^ k ∈ normalizer (A : Set G) := pow_mem (h.base ▸ h.d_norm 1 (by omega)) k
    exact (mem_normalizer_iff.mp hdA a).mp ha
  have hb1 : b ≠ 1 := by
    rw [← h1]
    intro e
    apply ha1
    have : a = (d ^ k)⁻¹ * (d ^ k * a * (d ^ k)⁻¹) * d ^ k := by group
    rw [this, e]
    group
  have hsplit : d ^ k' = d ^ (k' - k) * d ^ k := by rw [← pow_add, Nat.sub_add_cancel hkk]
  have hfix : d ^ (k' - k) * b * (d ^ (k' - k))⁻¹ = b := by
    rw [← h1]
    calc d ^ (k' - k) * (d ^ k * a * (d ^ k)⁻¹) * (d ^ (k' - k))⁻¹
        = (d ^ (k' - k) * d ^ k) * a * (d ^ (k' - k) * d ^ k)⁻¹ := by group
      _ = d ^ k' * a * (d ^ k')⁻¹ := by rw [← hsplit]
      _ = _ := by rw [h2, h1]
  have h3 := hdfix (k' - k) b hbA hb1 hfix
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [h.d_order] at h4
  rcases Nat.eq_zero_or_pos (k' - k) with h5 | h5
  · omega
  · exact absurd (Nat.le_of_dvd h5 h4) (by omega)

omit [Finite G] in
theorem finkHyp (h : LinearPushChain t d T A f m C) (hf : 2 ≤ f) (htt : t * t = 1)
    (hdfix : ∀ k : ℕ, ∀ a ∈ A, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ m + 1) :
    Finkelstein.Hyp (C j) f ((C j).normalizerMonoidHom ⟨t, h.t_norm j hj⟩)
      ((C j).normalizerMonoidHom ⟨d, h.d_norm j hj⟩) := by
  set τ := (C j).normalizerMonoidHom ⟨t, h.t_norm j hj⟩ with hτ
  set δ := (C j).normalizerMonoidHom ⟨d, h.d_norm j hj⟩ with hδ
  have hτa : ∀ u : C j, ((τ u : C j) : G) = t * u * t⁻¹ := fun u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ u
  have hδa : ∀ (k : ℕ) (u : C j), (((δ ^ k) u : C j) : G) = d ^ k * u * (d ^ k)⁻¹ :=
    fun k u => coe_normalizerMonoidHom_pow_apply _ _ k u
  have hpos : 0 < 2 ^ f - 1 := by
    have : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  refine ⟨IsPGroup.of_card (h.card j hj), hf, ?_, ?_, ?_, ?_⟩
  ·
    refine MulEquiv.ext fun u => Subtype.ext ?_
    show (((τ ^ 2) u : C j) : G) = u
    rw [sq, MulAut.mul_apply, hτa, hτa]
    calc t * (t * ↑u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
      _ = u := by rw [htt]; group
  ·
    have hdt : (⟨t, h.t_norm j hj⟩ : normalizer (C j : Set G)) * ⟨d, h.d_norm j hj⟩ =
        ⟨d, h.d_norm j hj⟩ * ⟨t, h.t_norm j hj⟩ := Subtype.ext h.d_comm.symm
    rw [hτ, hδ, ← map_mul, ← map_mul, hdt]
  ·
    rw [orderOf_eq_iff hpos]
    refine ⟨MulEquiv.ext fun u => Subtype.ext ?_, fun k hk hk0 h1 => ?_⟩
    · show (((δ ^ (2 ^ f - 1)) u : C j) : G) = u
      rw [hδa, ← h.d_order, pow_orderOf_eq_one]
      group
    · obtain ⟨a, ha, ha1⟩ := h.exists_base_ne_one (by omega)
      have h2 : (((δ ^ k) ⟨a, h.base_le hj1 hj ha⟩ : C j) : G) = a := by rw [h1]; rfl
      rw [hδa] at h2
      have h4 := orderOf_dvd_of_pow_eq_one (hdfix k a ha ha1 h2)
      rw [h.d_order] at h4
      exact absurd (Nat.le_of_dvd hk0 h4) (by omega)
  ·
    intro a b ha hb ha1 hb1
    have haA : (a : G) ∈ A := (h.mem_fixSubgroup_iff hj a).mp ha
    have hbA : (b : G) ∈ A := (h.mem_fixSubgroup_iff hj b).mp hb
    have ha1' : (a : G) ≠ 1 := fun e => ha1 (Subtype.ext e)
    have hb1' : (b : G) ≠ 1 := fun e => hb1 (Subtype.ext e)
    obtain ⟨k, hk⟩ := h.d_reg a haA b hbA ha1' hb1'
    have hk0 : d ^ (k % (2 ^ f - 1)) * a * (d ^ (k % (2 ^ f - 1)))⁻¹ = b := by
      rw [← h.d_order, pow_mod_orderOf, hk]
    refine ⟨k % (2 ^ f - 1), ⟨Nat.mod_lt _ hpos, Subtype.ext (by rw [hδa]; exact hk0)⟩, ?_⟩
    rintro k' ⟨hk', hk'b⟩
    have hk'b' : d ^ k' * a * (d ^ k')⁻¹ = b := by rw [← hδa, hk'b]
    rcases le_total k' (k % (2 ^ f - 1)) with hle | hle
    · exact h.eq_of_conj_eq_of_le hdfix haA ha1' hle (Nat.mod_lt _ hpos) hk'b' hk0
    · exact (h.eq_of_conj_eq_of_le hdfix haA ha1' hle hk' hk0 hk'b').symm

theorem commute_base (h : LinearPushChain t d T A f m C) (hf : 2 ≤ f) (htt : t * t = 1)
    (hdfix : ∀ k : ℕ, ∀ a ∈ A, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ m + 1) : ∀ x ∈ C j, ∀ a ∈ A, x * a = a * x := by
  intro x hx a ha
  have hH := h.finkHyp hf htt hdfix hj1 hj
  have hfix := (h.mem_fixSubgroup_iff hj ⟨a, h.base_le hj1 hj ha⟩).mpr ha
  exact congrArg Subtype.val (hH.mem_center_of_mem_fix hfix ⟨x, hx⟩)

omit [Finite G] in
theorem commutator_sup_le (h : LinearPushChain t d T A f m C) (hm : 1 ≤ m) (htt : t * t = 1) :
    ⁅C (m + 1) ⊔ zpowers t, C (m + 1) ⊔ zpowers t⁆ ≤ C m := by
  have htU : zpowers t ≤ normalizer (C (m + 1) : Set G) := zpowers_le.mpr (h.t_norm (m + 1) le_rfl)
  have hUN : ∀ u ∈ C (m + 1), ∀ n ∈ C m, u * n * u⁻¹ ∈ C m := fun u hu n hn =>
    (mem_normalizer_iff.mp (h.normal m le_rfl hu) n).mp hn
  have hc1 : ∀ u ∈ C (m + 1), ∀ u' ∈ C (m + 1), u * u' * u⁻¹ * u'⁻¹ ∈ C m :=
    h.layer_comm m le_rfl
  have hc2 : ∀ u ∈ C (m + 1), u * t * u⁻¹ * t⁻¹ ∈ C m := h.comm_t m hm le_rfl
  have hc3 : ∀ u₁ ∈ C (m + 1), ∀ u₂ ∈ C (m + 1), u₁ * (u₂ * t) * u₁⁻¹ * (u₂ * t)⁻¹ ∈ C m := by
    intro u₁ hu₁ u₂ hu₂
    have e : u₁ * (u₂ * t) * u₁⁻¹ * (u₂ * t)⁻¹ =
        (u₁ * u₂ * u₁⁻¹ * u₂⁻¹) * (u₂ * (u₁ * t * u₁⁻¹ * t⁻¹) * u₂⁻¹) := by group
    rw [e]
    exact mul_mem (hc1 u₁ hu₁ u₂ hu₂) (hUN u₂ hu₂ _ (hc2 u₁ hu₁))
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨u₁, hu₁, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htU ha <;>
    obtain ⟨u₂, hu₂, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htU hb
  · exact hc1 u₁ hu₁ u₂ hu₂
  · exact hc3 u₁ hu₁ u₂ hu₂
  · have h1 := inv_mem (hc3 u₂ hu₂ u₁ hu₁)
    rw [commutatorElement_def]
    convert h1 using 1
    group
  ·
    have hv : u₂ * u₁⁻¹ ∈ C (m + 1) := mul_mem hu₂ (inv_mem hu₁)
    have hct : t * (u₂ * u₁⁻¹) * t⁻¹ * (u₂ * u₁⁻¹)⁻¹ ∈ C m := by
      have := inv_mem (hc2 _ hv)
      convert this using 1
      group
    have e : ⁅u₁ * t, u₂ * t⁆ = (u₁ * (t * (u₂ * u₁⁻¹) * t⁻¹ * (u₂ * u₁⁻¹)⁻¹) * u₁⁻¹) *
        (u₁ * u₂ * u₁⁻¹ * u₂⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hUN u₁ hu₁ _ hct) (hc1 u₁ hu₁ u₂ hu₂)

omit [Finite G] in
theorem le_commutator_sup (h : LinearPushChain t d T A f m C) :
    C m ≤ ⁅C (m + 1) ⊔ zpowers t, C (m + 1) ⊔ zpowers t⁆ := by
  suffices H : ∀ j ≤ m, C j ≤ ⁅C (m + 1) ⊔ zpowers t, C (m + 1) ⊔ zpowers t⁆ from H m le_rfl
  intro j
  induction j with
  | zero => intro _; rw [h.zero]; exact bot_le
  | succ j ih =>
    intro hj u hu
    obtain ⟨x, hx, hxu⟩ := h.comm_t_onto (j + 1) (by omega) hj u hu
    rw [Nat.add_sub_cancel] at hxu
    have hxC : x ∈ C (m + 1) ⊔ zpowers t := mem_sup_left (h.le_of_le (by omega) le_rfl hx)
    have htC : t ∈ C (m + 1) ⊔ zpowers t := mem_sup_right (mem_zpowers t)
    have hcomm : x * t * x⁻¹ * t⁻¹ ∈ ⁅C (m + 1) ⊔ zpowers t, C (m + 1) ⊔ zpowers t⁆ := by
      have := commutator_mem_commutator hxC htC
      rwa [commutatorElement_def] at this
    have e : u = (x * t * x⁻¹ * t⁻¹) * (u⁻¹ * (x * t * x⁻¹ * t⁻¹))⁻¹ := by group
    rw [e]
    exact mul_mem hcomm (inv_mem (ih (by omega) hxu))

omit [Finite G] in
theorem commutator_sup_eq (h : LinearPushChain t d T A f m C) (hm : 1 ≤ m) (htt : t * t = 1) :
    ⁅C (m + 1) ⊔ zpowers t, C (m + 1) ⊔ zpowers t⁆ = C m :=
  le_antisymm (h.commutator_sup_le hm htt) h.le_commutator_sup

omit [Finite G] in
theorem mem_normalizer_of_mem_normalizer_sup (h : LinearPushChain t d T A f m C) (hm : 1 ≤ m)
    (htt : t * t = 1) {z : G} (hz : z ∈ normalizer ((C (m + 1) ⊔ zpowers t : Subgroup G) : Set G)) :
    z ∈ normalizer (C m : Set G) := by
  rw [← SteinbergBV.map_conj_eq_self_iff] at hz ⊢
  rw [← h.commutator_sup_eq hm htt, map_commutator, hz]

end LinearPushChain

end CFSG.SeitzReduction.RankOne
