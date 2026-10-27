module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EModel
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum.Prime

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

theorem exists_sylow_normalized_of_not_dvd' {G : Type*} [Group G] [Finite G] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (L B : Subgroup G) (hBp : IsPGroup p B) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hcop : ¬ p ∣ Nat.card L) :
    ∃ Q : Subgroup G, Q ≤ L ∧ IsPGroup q Q ∧
      (∀ n : ℕ, q ^ n ∣ Nat.card L → q ^ n ∣ Nat.card Q) ∧
        B ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  let φ : B →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBL)
  let _ : MulDistribMulAction B L := MulDistribMulAction.compHom L φ
  let _ : MulAction B (Sylow q L) := Sylow.pointwiseMulAction
  have hcard : ¬ p ∣ Nat.card (Sylow q L) := by
    intro h
    obtain ⟨Q₁⟩ : Nonempty (Sylow q L) := inferInstance
    exact hcop (h.trans (Q₁.card_dvd_index.trans (Q₁ : Subgroup L).index_dvd_card))
  obtain ⟨Q₀, hQ₀⟩ := hBp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q L) hcard
  refine ⟨(Q₀ : Subgroup L).map L.subtype, Subgroup.map_subtype_le _, Q₀.isPGroup'.map _,
    fun n hn => ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective L)]
    exact Q₀.pow_dvd_card_of_pow_dvd_card hn
  · rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have hfix : (⟨b, hb⟩ : B) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
    have hmem : (⟨b, hb⟩ : B) • y ∈ (Q₀ : Subgroup L) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : B) (Q₀ : Subgroup L) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change (((L.normalizerMonoidHom) (Subgroup.inclusion hBL ⟨b, hb⟩)) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl

namespace Datum
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (D : Datum V)

theorem kl (hK : D.HasKa) {X : Subgroup (V ≃ₗ[ZMod 3] V)} (hXW : X ≤ D.W)
    (hXodd : Odd (Nat.card X)) (hXQ : ∀ q ∈ D.Q, ∀ x ∈ X, q * x * q⁻¹ ∈ X)
    {a : V} (ha : a ∈ D.A) (ha0 : a ≠ 0) {x : V ≃ₗ[ZMod 3] V} (hx : x ∈ X) (hxa : x a = a) :
    ∀ q ∈ D.Q, q * x = x * q := by
  intro q hq
  obtain ⟨S, hS, hSn⟩ := hK a ha ha0
  have hxS : ∀ q ∈ D.Q, x * q * x⁻¹ ∈ S := fun q hq =>
    hSn x (hXW hx) (Or.inl hxa) q (hS.Q_le hq)
  have hc : x * q * x⁻¹ * q⁻¹ ∈ X ⊓ S := by
    refine ⟨?_, S.mul_mem (hxS q hq) (S.inv_mem (hS.Q_le hq))⟩
    have : x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) := by group
    rw [this]
    exact X.mul_mem hx (hXQ q hq _ (X.inv_mem hx))
  have hZ : X ⊓ S = ⊥ := by
    refine D.planeQ.odd_normalized (X ⊓ S) (fun z hz f hf => hS.mem_F z hz.2 f hf)
      (fun z hz hzf => hS.faith z hz.2 hzf) ?_ ?_
    · exact Odd.of_dvd_nat hXodd (Subgroup.card_dvd_of_le inf_le_left)
    · intro q hq z hz
      exact ⟨hXQ q hq z hz.1, S.mul_mem (S.mul_mem (hS.Q_le hq) hz.2) (S.inv_mem (hS.Q_le hq))⟩
  rw [hZ, Subgroup.mem_bot] at hc
  have h1 : x * q * x⁻¹ = q := by
    have := mul_inv_eq_one.1 hc
    exact this
  calc q * x = (x * q * x⁻¹) * x := by rw [h1]
    _ = x * q := by group

@[expose] def Unip (y : V ≃ₗ[ZMod 3] V) : Prop := (∀ f ∈ D.F, y f = f) ∧ ∀ v, y v - v ∈ D.F

variable {D}

theorem Unip.add_F {y : V ≃ₗ[ZMod 3] V} (hy : D.Unip y) (v : V) {w : V} (hw : w ∈ D.F) :
    y (v + w) - (v + w) = y v - v := by
  rw [map_add, hy.1 w hw]; abel

theorem Unip.mul {y z : V ≃ₗ[ZMod 3] V} (hy : D.Unip y) (hz : D.Unip z) : D.Unip (y * z) := by
  refine ⟨fun f hf => by simp [hz.1 f hf, hy.1 f hf], fun v => ?_⟩
  have h1 : (y * z) v - v = (y (z v) - z v) + (z v - v) := by simp
  rw [h1]; exact D.F.add_mem (hy.2 _) (hz.2 v)

theorem Q_sub_mem {q : V ≃ₗ[ZMod 3] V} (hq : q ∈ D.Q) (v : V) : q v - v ∈ D.F := by
  obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
  have : q (a + f) - (a + f) = q f - f := by rw [map_add, D.Q_fix_A q hq a ha]; abel
  rw [this]
  exact D.F.sub_mem (D.planeQ.mem q hq f hf) hf

theorem Unip.conj_apply {y : V ≃ₗ[ZMod 3] V} (hy : D.Unip y) {q : V ≃ₗ[ZMod 3] V} (hq : q ∈ D.Q)
    (v : V) : (q * y * q⁻¹) v = v + q (y v - v) := by
  have hq' : q⁻¹ ∈ D.Q := D.Q.inv_mem hq
  have hu : q⁻¹ v - v ∈ D.F := Q_sub_mem hq' v
  have h1 : y (q⁻¹ v) - q⁻¹ v = y v - v := by
    have := hy.add_F v hu
    simpa using this
  have h2 : (q * y * q⁻¹) v = q (y (q⁻¹ v)) := rfl
  rw [h2]
  have h3 : y (q⁻¹ v) = q⁻¹ v + (y v - v) := by
    rw [← h1]; abel
  rw [h3, map_add]
  have : q (q⁻¹ v) = v := by
    simp
  rw [this]

theorem Unip.conj {y : V ≃ₗ[ZMod 3] V} (hy : D.Unip y) {q : V ≃ₗ[ZMod 3] V} (hq : q ∈ D.Q) :
    D.Unip (q * y * q⁻¹) := by
  refine ⟨fun f hf => ?_, fun v => ?_⟩
  · rw [hy.conj_apply hq, hy.1 f hf]; simp
  · rw [hy.conj_apply hq]
    simp only [add_sub_cancel_left]
    exact D.planeQ.mem q hq _ (hy.2 v)

theorem unip_prod_apply {y : V ≃ₗ[ZMod 3] V} (hy : D.Unip y) {q1 q2 : V ≃ₗ[ZMod 3] V}
    (hq1 : q1 ∈ D.Q) (hq2 : q2 ∈ D.Q) (v : V) :
    (y * (q1 * y * q1⁻¹) * (q2 * y * q2⁻¹)) v = v + q2 (y v - v) + q1 (y v - v) + (y v - v) := by
  have hF : ∀ w ∈ D.F, q1 w ∈ D.F ∧ q2 w ∈ D.F := fun w hw =>
    ⟨D.planeQ.mem q1 hq1 w hw, D.planeQ.mem q2 hq2 w hw⟩
  have hh : y v - v ∈ D.F := hy.2 v
  have e1 : (q2 * y * q2⁻¹) v = v + q2 (y v - v) := hy.conj_apply hq2 v
  have hw2 : q2 (y v - v) ∈ D.F := (hF _ hh).2
  have e2 : (q1 * y * q1⁻¹) (v + q2 (y v - v)) = v + q2 (y v - v) + q1 (y v - v) := by
    rw [hy.conj_apply hq1, hy.add_F v hw2]
  have hw3 : q2 (y v - v) + q1 (y v - v) ∈ D.F := D.F.add_mem hw2 (hF _ hh).1
  have e3 : y (v + q2 (y v - v) + q1 (y v - v)) =
      v + q2 (y v - v) + q1 (y v - v) + (y v - v) := by
    rw [add_assoc]
    have h4 := hy.add_F v hw3
    rw [sub_eq_iff_eq_add.mp h4]; abel
  show y ((q1 * y * q1⁻¹) ((q2 * y * q2⁻¹) v)) = _
  rw [e1, e2, e3]

theorem lemmaH {X : Subgroup (V ≃ₗ[ZMod 3] V)} (hXQ : ∀ q ∈ D.Q, ∀ x ∈ X, q * x * q⁻¹ ∈ X)
    {y : V ≃ₗ[ZMod 3] V} (hyX : y ∈ X) (hy : D.Unip y) (hy1 : y ≠ 1) :
    ∃ y' ∈ X, D.Unip y' ∧ y' ≠ 1 ∧ ∃ a ∈ D.A, a ≠ 0 ∧ y' a = a := by
  by_cases hfix : ∃ a ∈ D.A, a ≠ 0 ∧ y a = a
  · exact ⟨y, hyX, hy, hy1, hfix⟩
  push Not at hfix
  let φ : D.A → D.F := fun a => ⟨y a - a, hy.2 a⟩
  have hφinj : Function.Injective φ := by
    intro a a' h
    have h1 : y a - a = y a' - a' := congrArg Subtype.val h
    by_contra hne
    have hne' : (a : V) - a' ≠ 0 := fun h0 => hne (Subtype.ext (sub_eq_zero.1 h0))
    have := hfix _ (D.A.sub_mem a.2 a'.2) hne'
    apply this
    rw [map_sub]
    calc (y a : V) - y a' = (y a - a) - (y a' - a') + (a - a') := by abel
      _ = a - a' := by rw [h1, sub_self, zero_add]
  have hφbij : Function.Bijective φ :=
    hφinj.bijective_of_nat_card_le (by rw [D.card_A, D.card_F])
  obtain ⟨q1, hq1, q2, hq2, ⟨f0, hf0F, hf0ne, hf0⟩, ⟨f1, hf1F, hf1⟩⟩ := D.planeQ.zd
  obtain ⟨a0, ha0⟩ := hφbij.2 ⟨f0, hf0F⟩
  obtain ⟨a1, ha1⟩ := hφbij.2 ⟨f1, hf1F⟩
  have ha0' : y a0 - a0 = f0 := congrArg Subtype.val ha0
  have ha1' : y a1 - a1 = f1 := congrArg Subtype.val ha1
  have hy' : D.Unip (y * (q1 * y * q1⁻¹) * (q2 * y * q2⁻¹)) :=
    (hy.mul (hy.conj hq1)).mul (hy.conj hq2)
  refine ⟨y * (q1 * y * q1⁻¹) * (q2 * y * q2⁻¹), ?_, hy', ?_, a0, a0.2, ?_, ?_⟩
  · exact X.mul_mem (X.mul_mem hyX (hXQ q1 hq1 y hyX)) (hXQ q2 hq2 y hyX)
  · intro h1
    have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e a1) h1
    simp only [unip_prod_apply hy hq1 hq2, ha1', LinearEquiv.coe_one, id_eq] at this
    apply hf1
    apply add_left_cancel (a := (a1 : V))
    rw [add_zero]
    calc (a1 : V) + (f1 + q1 f1 + q2 f1) = a1 + q2 f1 + q1 f1 + f1 := by abel
      _ = a1 := this
  · intro h0
    apply hf0ne
    have h1 := ha0'
    rw [h0, map_zero, sub_zero] at h1
    exact h1.symm
  · rw [unip_prod_apply hy hq1 hq2, ha0']
    calc (a0 : V) + q2 f0 + q1 f0 + f0 = a0 + (f0 + q1 f0 + q2 f0) := by abel
      _ = a0 := by rw [hf0, add_zero]

theorem eq_one_of_unip_comm_t {y : V ≃ₗ[ZMod 3] V} (hy : D.Unip y) (hc : D.t * y = y * D.t) :
    y = 1 := by
  ext v
  obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
  have hc' : ∀ w, D.t (y w) = y (D.t w) := fun w => by
    have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e w) hc
    simpa using this
  have h1 : y (a + f) - (a + f) = y a - a := by
    have := hy.add_F a hf
    exact this
  have h2 : y (D.t (a + f)) - D.t (a + f) = y a - a := by
    rw [D.t_apply ha hf, sub_eq_add_neg]
    have := hy.add_F a (D.F.neg_mem hf)
    rw [← sub_eq_add_neg]
    simpa [sub_eq_add_neg] using this
  have h3 : D.t (y a - a) = -(y a - a) := D.t_neg_F _ (hy.2 a)
  have h4 : D.t (y (a + f)) = y (D.t (a + f)) := hc' _
  have h5 : y (a + f) = (a + f) + (y a - a) := by
    rw [← h1]; abel
  have h6 : y (D.t (a + f)) = D.t (a + f) + (y a - a) := by
    rw [← h2]; abel
  rw [h5, map_add, h3, h6] at h4
  have h7 : y a - a = -(y a - a) := (add_left_cancel h4).symm
  have h8 : y a - a = 0 := eq_zero_of_eq_neg h7
  rw [h5, h8]; simp

theorem inv_apply_of_fix {x : V ≃ₗ[ZMod 3] V} {f : V} (h : x f = f) : x⁻¹ f = f := by
  have : x⁻¹ (x f) = f := by
    simp
  rw [h] at this; exact this

theorem unip_comm {x q : V ≃ₗ[ZMod 3] V} (hx : ∀ f ∈ D.F, x f = f) (hq : q ∈ D.Q) :
    D.Unip (x * q * x⁻¹ * q⁻¹) := by
  have hq' : q⁻¹ ∈ D.Q := D.Q.inv_mem hq
  have hxi : ∀ f ∈ D.F, x⁻¹ f = f := fun f hf => inv_apply_of_fix (hx f hf)
  have hqq : ∀ v, q (q⁻¹ v) = v := fun v => by
    simp
  have hxx : ∀ v, x (x⁻¹ v) = v := fun v => by
    simp
  refine ⟨fun f hf => ?_, fun v => ?_⟩
  · have hf1 : q⁻¹ f ∈ D.F := D.planeQ.mem _ hq' f hf
    show x (q (x⁻¹ (q⁻¹ f))) = f
    rw [hxi _ hf1, hqq, hx f hf]
  · have hf1 : q⁻¹ v - v ∈ D.F := Q_sub_mem hq' v
    have hf2 : q (x⁻¹ v) - x⁻¹ v ∈ D.F := Q_sub_mem hq _
    have hf3 : q (q⁻¹ v - v) ∈ D.F := D.planeQ.mem _ hq _ hf1
    have e1 : (x * q * x⁻¹ * q⁻¹) v = x (q (x⁻¹ (q⁻¹ v))) := rfl
    have h1 : q⁻¹ v = v + (q⁻¹ v - v) := by abel
    have h2 : q (x⁻¹ v) = x⁻¹ v + (q (x⁻¹ v) - x⁻¹ v) := by abel
    have e3 : x (q (x⁻¹ (q⁻¹ v))) = v + (q (x⁻¹ v) - x⁻¹ v) + q (q⁻¹ v - v) := by
      calc x (q (x⁻¹ (q⁻¹ v))) = x (q (x⁻¹ (v + (q⁻¹ v - v)))) := by rw [← h1]
        _ = x (q (x⁻¹ v + (q⁻¹ v - v))) := by rw [map_add, hxi _ hf1]
        _ = x (q (x⁻¹ v) + q (q⁻¹ v - v)) := by rw [map_add]
        _ = x (x⁻¹ v + (q (x⁻¹ v) - x⁻¹ v) + q (q⁻¹ v - v)) := by rw [← h2]
        _ = x (x⁻¹ v) + x (q (x⁻¹ v) - x⁻¹ v) + x (q (q⁻¹ v - v)) := by rw [map_add, map_add]
        _ = v + (q (x⁻¹ v) - x⁻¹ v) + q (q⁻¹ v - v) := by rw [hxx, hx _ hf2, hx _ hf3]
    rw [e1, e3]
    have : v + (q (x⁻¹ v) - x⁻¹ v) + q (q⁻¹ v - v) - v = (q (x⁻¹ v) - x⁻¹ v) + q (q⁻¹ v - v) := by abel
    rw [this]
    exact D.F.add_mem hf2 hf3

theorem three_case (hK : D.HasKa) {X : Subgroup (V ≃ₗ[ZMod 3] V)} (hXW : X ≤ D.W)
    (hX3 : IsPGroup 3 X) (hXQ : ∀ q ∈ D.Q, ∀ x ∈ X, q * x * q⁻¹ ∈ X) :
    ∀ x ∈ X, ∀ q ∈ D.Q, q * x = x * q := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0, q0, hq0, hne⟩ := hcon
  have hXodd : Odd (Nat.card X) := by
    obtain ⟨k, hk⟩ := hX3.exists_card_eq
    rw [hk]; exact Odd.pow (by decide)
  obtain ⟨v, hvfix, hv0⟩ : ∃ v : V, (∀ x ∈ X, x v = v) ∧ v ≠ 0 := by
    have hp : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have h3 : 3 ∣ Nat.card V := by rw [D.card_V]; norm_num
    have hfp : (0 : V) ∈ MulAction.fixedPoints X V := by
      intro x; exact map_zero _
    obtain ⟨b, hb, hb0⟩ := hX3.exists_fixed_point_of_prime_dvd_card_of_fixed_point V h3 hfp
    refine ⟨b, fun x hx => ?_, fun h0 => hb0 h0.symm⟩
    exact hb ⟨x, hx⟩
  have hX_t : ∀ x ∈ X, D.t * x * D.t⁻¹ ∈ X := fun x hx => hXQ D.t D.t_mem x hx
  have htinv : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right D.t_mul_self
  have hclosed : ∀ y ∈ fixSub X, D.t y ∈ fixSub X := by
    intro y hy x hx
    have h1 : D.t * x * D.t⁻¹ ∈ X := hX_t x hx
    have h2 : (D.t * x * D.t⁻¹) y = y := hy _ h1
    rw [htinv] at h2
    have h3 : D.t (x (D.t y)) = y := h2
    calc x (D.t y) = D.t (D.t (x (D.t y))) := (D.t_t _).symm
      _ = D.t y := by rw [h3]
  obtain ⟨a, haX, haA, f, hfX, hfF, hv⟩ := D.split_of_t_closed (fixSub X) hclosed
    (show v ∈ fixSub X from hvfix)
  by_cases ha0 : a = 0
  ·
    have hf0 : f ≠ 0 := by
      intro hf0; apply hv0; rw [hv, ha0, hf0]; simp
    have hQcl : ∀ q ∈ D.Q, ∀ y ∈ fixSub X, q y ∈ fixSub X := by
      intro q hq y hy x hx
      have h1 : q⁻¹ * x * q⁻¹⁻¹ ∈ X := hXQ q⁻¹ (D.Q.inv_mem hq) x hx
      have h2 : (q⁻¹ * x * q⁻¹⁻¹) y = y := hy _ h1
      have h3 : q⁻¹ (x (q y)) = y := by simpa using h2
      calc x (q y) = q (q⁻¹ (x (q y))) := by simp
        _ = q y := by rw [h3]
    have hXF : ∀ x ∈ X, ∀ f ∈ D.F, x f = f := fun x hx g hg =>
      D.F_le_of_Q_closed (fixSub X) hQcl (f := f) hfX hfF hf0 g hg x hx
    set y0 := x0 * q0 * x0⁻¹ * q0⁻¹ with hy0
    have hy0X : y0 ∈ X := by
      have : y0 = x0 * (q0 * x0⁻¹ * q0⁻¹) := by rw [hy0]; group
      rw [this]; exact X.mul_mem hx0 (hXQ q0 hq0 _ (X.inv_mem hx0))
    have hy01 : y0 ≠ 1 := by
      intro h1
      apply hne
      have : x0 * q0 * x0⁻¹ = q0 := mul_inv_eq_one.1 h1
      calc q0 * x0 = (x0 * q0 * x0⁻¹) * x0 := by rw [this]
        _ = x0 * q0 := by group
    obtain ⟨y', hy'X, hy'u, hy'1, a', ha'A, ha'0, ha'fix⟩ :=
      lemmaH hXQ hy0X (unip_comm (hXF x0 hx0) hq0) hy01
    have hcomm := D.kl hK hXW hXodd hXQ ha'A ha'0 hy'X ha'fix D.t D.t_mem
    exact hy'1 (eq_one_of_unip_comm_t hy'u hcomm)
  · exact hne (D.kl hK hXW hXodd hXQ haA ha0 hx0 (haX x0 hx0) q0 hq0)

theorem card_aut_four (hV : Nat.card V = 81) : Nat.card (V ≃ₗ[ZMod 3] V) = 24261120 := by
  have hfr : Module.finrank (ZMod 3) V = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [hV, Nat.card_zmod] at h
    have : (3:ℕ)^4 = 3 ^ Module.finrank (ZMod 3) V := by simpa using h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) this).symm
  let b := Module.finBasisOfFinrankEq (ZMod 3) V hfr
  let e : (V ≃ₗ[ZMod 3] V) ≃* GL (Fin 4) (ZMod 3) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) V).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp [Fin.prod_univ_four, ZMod.card]

theorem five_case {R : Subgroup (V ≃ₗ[ZMod 3] V)} (hRQ : ∀ q ∈ D.Q, ∀ x ∈ R, q * x * q⁻¹ ∈ R)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hR : IsPGroup r R) : R = ⊥ := by
  have := Fact.mk hr
  by_contra hRne
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hRne
    rw [← Subgroup.card_eq_one, hk]; simp
  have hdvd : Nat.card R ∣ 24261120 := by
    rw [← card_aut_four (D.card_V)]
    exact Subgroup.card_subgroup_dvd_card R
  have hrdvd : r ∣ 24261120 := by
    refine dvd_trans ?_ hdvd
    rw [hk]; exact dvd_pow_self r hk0
  have hr513 : r = 5 ∨ r = 13 := by
    have h' : r ∣ 2 ^ 9 * 3 ^ 6 * 5 * 13 := by norm_num; exact hrdvd
    rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
    · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hr).1 h2 with h3 | h3
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h3)) hr2
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h3)) hr3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h2)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1)
  have hk1 : k = 1 := by
    by_contra hk1
    have hk2 : 2 ≤ k := by omega
    have h2 : r ^ 2 ∣ 24261120 := by
      refine dvd_trans ?_ (hk ▸ hdvd)
      exact pow_dvd_pow r hk2
    rcases hr513 with rfl | rfl <;> norm_num at h2
  have hcard : Nat.card R = r := by rw [hk, hk1, pow_one]
  have hcyc : IsCyclic R := isCyclic_of_prime_card hcard
  have hQN : D.Q ≤ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V)) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hRQ q hq x hx, fun hx => ?_⟩
    have := hRQ q⁻¹ (D.Q.inv_mem hq) _ hx
    simpa [mul_assoc] using this
  let ψ : D.Q →* MulAut R := R.normalizerMonoidHom.comp (Subgroup.inclusion hQN)
  have hcomm : ∀ σ τ : MulAut R, σ * τ = τ * σ := by
    intro σ τ
    apply (IsCyclic.mulAutMulEquiv R).injective
    rw [map_mul, map_mul, mul_comm]
  have hψt : ψ ⟨D.t, D.t_mem⟩ = 1 := by
    obtain ⟨i, hi, j, hj, hij⟩ := D.exists_ij
    have h1 : ψ ⟨i, hi⟩ * ψ ⟨j, hj⟩ = ψ ⟨D.t, D.t_mem⟩ * (ψ ⟨j, hj⟩ * ψ ⟨i, hi⟩) := by
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hij
    rw [hcomm (ψ ⟨i, hi⟩) (ψ ⟨j, hj⟩)] at h1
    have h2 : (ψ ⟨D.t, D.t_mem⟩ * (ψ ⟨j, hj⟩ * ψ ⟨i, hi⟩)) = 1 * (ψ ⟨j, hj⟩ * ψ ⟨i, hi⟩) := by
      rw [← h1]; group
    exact mul_right_cancel (b := ψ ⟨j, hj⟩ * ψ ⟨i, hi⟩) (by simpa using h2)
  have htR : ∀ x ∈ R, D.t * x = x * D.t := by
    intro x hx
    have h1 := congrArg (fun σ : MulAut R => ((σ ⟨x, hx⟩ : R) : V ≃ₗ[ZMod 3] V)) hψt
    simp only [ψ, MonoidHom.comp_apply] at h1
    have h2 : D.t * x * D.t⁻¹ = x := by
      simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h1
    calc D.t * x = (D.t * x * D.t⁻¹) * D.t := by group
      _ = x * D.t := by rw [h2]
  have hRA : ∀ x ∈ R, ∀ a ∈ D.A, x a ∈ D.A := fun x hx => (D.t_comm_preserves (htR x hx).symm).1
  have hRF : ∀ x ∈ R, ∀ f ∈ D.F, x f ∈ D.F := fun x hx => (D.t_comm_preserves (htR x hx).symm).2
  have hgcd : Nat.gcd r 48 = 1 := by rcases hr513 with rfl | rfl <;> decide
  have hAF : ∀ x ∈ R, x = 1 := by
    intro x hx
    have hxr : (⟨x, hx⟩ : R) ^ r = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have hA1 : resHom D.A R hRA ⟨x, hx⟩ = 1 := by
      have h1 : (resHom D.A R hRA ⟨x, hx⟩) ^ r = 1 := by rw [← map_pow, hxr, map_one]
      have h2 : (resHom D.A R hRA ⟨x, hx⟩) ^ 48 = 1 := by
        rw [← plane_card_aut D.card_A]; exact pow_card_eq_one'
      have := pow_gcd_eq_one.2 ⟨h1, h2⟩
      rwa [hgcd, pow_one] at this
    have hF1 : resHom D.F R hRF ⟨x, hx⟩ = 1 := by
      have h1 : (resHom D.F R hRF ⟨x, hx⟩) ^ r = 1 := by rw [← map_pow, hxr, map_one]
      have h2 : (resHom D.F R hRF ⟨x, hx⟩) ^ 48 = 1 := by
        rw [← plane_card_aut D.card_F]; exact pow_card_eq_one'
      have := pow_gcd_eq_one.2 ⟨h1, h2⟩
      rwa [hgcd, pow_one] at this
    ext v
    obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
    have hxa : x a = a := by
      have := congrArg (fun e : D.A ≃ₗ[ZMod 3] D.A => ((e ⟨a, ha⟩ : D.A) : V)) hA1
      simpa using this
    have hxf : x f = f := by
      have := congrArg (fun e : D.F ≃ₗ[ZMod 3] D.F => ((e ⟨f, hf⟩ : D.F) : V)) hF1
      simpa using this
    simp [map_add, hxa, hxf]
  apply hRne
  rw [Subgroup.eq_bot_iff_forall]
  exact hAF

theorem card_Q : Nat.card D.Q = 8 := by
  rw [Nat.card_congr D.planeQ.quat.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem lemma64_pairwise (hK : D.HasKa) {X : Subgroup (V ≃ₗ[ZMod 3] V)} (hXW : X ≤ D.W)
    (hXodd : Odd (Nat.card X)) (hXQ : ∀ q ∈ D.Q, ∀ x ∈ X, q * x * q⁻¹ ∈ X) :
    ∀ x ∈ X, ∀ q ∈ D.Q, q * x = x * q := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 D.Q := by
    apply IsPGroup.of_card (n := 3)
    rw [D.card_Q]; norm_num
  have hQN : D.Q ≤ Subgroup.normalizer (X : Set (V ≃ₗ[ZMod 3] V)) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hXQ q hq x hx, fun hx => ?_⟩
    have := hXQ q⁻¹ (D.Q.inv_mem hq) _ hx
    simpa [mul_assoc] using this
  have hcop : ¬ 2 ∣ Nat.card X := by
    intro h; exact (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h)
  have hsyl : ∀ r : ℕ, ∃ R : Subgroup (V ≃ₗ[ZMod 3] V), r.Prime → (R ≤ X ∧ IsPGroup r R ∧
      (∀ n : ℕ, r ^ n ∣ Nat.card X → r ^ n ∣ Nat.card R) ∧
        D.Q ≤ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V))) := by
    intro r
    by_cases hr : r.Prime
    · have := Fact.mk hr
      obtain ⟨R, hR1, hR2, hR3, hR4⟩ :=
        exists_sylow_normalized_of_not_dvd' (p := 2) (q := r) X D.Q hQ2 hQN hcop
      exact ⟨R, fun _ => ⟨hR1, hR2, hR3, hR4⟩⟩
    · exact ⟨⊥, fun h => absurd h hr⟩
  choose R hR using hsyl
  have hcomm : ∀ r : ℕ, r.Prime → r ∣ Nat.card X → ∀ x ∈ R r, ∀ q ∈ D.Q, q * x = x * q := by
    intro r hr hrdvd
    obtain ⟨hR1, hR2, hR3, hR4⟩ := hR r hr
    have hRQ : ∀ q ∈ D.Q, ∀ x ∈ R r, q * x * q⁻¹ ∈ R r := fun q hq x hx =>
      (Subgroup.mem_normalizer_iff.1 (hR4 hq) x).1 hx
    by_cases h3 : r = 3
    · subst h3
      exact D.three_case hK (hR1.trans hXW) hR2 hRQ
    · have hr2 : r ≠ 2 := by
        rintro rfl; exact hcop hrdvd
      have := D.five_case hRQ hr hr2 h3 hR2
      intro x hx q hq
      rw [this, Subgroup.mem_bot] at hx
      subst hx; simp
  set Y : Subgroup (V ≃ₗ[ZMod 3] V) := ⨆ r ∈ (Nat.card X).primeFactors, R r with hY
  have hYX : Y ≤ X := iSup₂_le fun r hr => (hR r (Nat.prime_of_mem_primeFactors hr)).1
  have hYdvd : Nat.card X ∣ Nat.card Y := by
    have hn0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
    rw [← Nat.factorization_prime_le_iff_dvd hn0 Nat.card_pos.ne']
    intro p hp
    by_cases hpd : p ∣ Nat.card X
    · have hpmem : p ∈ (Nat.card X).primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpd, hn0⟩
      have h1 : p ^ (Nat.card X).factorization p ∣ Nat.card X := Nat.ordProj_dvd _ _
      have h2 := (hR p hp).2.2.1 _ h1
      have h3 : Nat.card (R p) ∣ Nat.card Y :=
        Subgroup.card_dvd_of_le (le_iSup₂ (f := fun r (_ : r ∈ (Nat.card X).primeFactors) => R r) p hpmem)
      exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (h2.trans h3)
    · rw [Nat.factorization_eq_zero_of_not_dvd hpd]; exact Nat.zero_le _
  have hYeq : Y = X := by
    apply Subgroup.eq_of_le_of_card_ge hYX
    exact Nat.le_of_dvd Nat.card_pos hYdvd
  intro x hx q hq
  have hxY : x ∈ Y := hYeq ▸ hx
  have hYc : Y ≤ Subgroup.centralizer (D.Q : Set (V ≃ₗ[ZMod 3] V)) := by
    refine iSup₂_le fun r hr y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hcomm r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr) y hy q hq
  exact (Subgroup.mem_centralizer_iff.1 (hYc hxY)) q hq

theorem lemma64_abs (hK : D.HasKa) : D.Lemma64Concl := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hle : sSup D.NWQ2 ≤ Subgroup.centralizer (D.Q : Set (V ≃ₗ[ZMod 3] V)) :=
    sSup_le fun X hX x hx => by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact D.lemma64_pairwise hK hX.1 hX.2.1 hX.2.2 x hx q hq
  exact (Subgroup.mem_centralizer_iff.1 (hle hs) q hq).symm

end Datum
end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E
