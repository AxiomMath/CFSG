module

public import CFSG.CGT.Foote81L6.Normalizer.Lemma8
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin

structure Lemma11Hyp {V X : Type*} [CommGroup V] [Group X] (ρ : X →* MulAut V)
    (d₀ d₁ x₀ x₁ τ : X) (b₀ b₁ : V) : Prop where
  injective : Function.Injective ρ
  sq_eq_one : ∀ v : V, v * v = 1
  card_eq : Nat.card V = 2 ^ 6
  tv₀ : IsTransvectionWith (ρ d₀) b₀
  tv₁ : IsTransvectionWith (ρ d₁) b₁
  ne_one₀ : ρ d₀ ≠ 1
  ne_one₁ : ρ d₁ ≠ 1
  ne : b₀ ≠ b₁
  orderOf₀ : orderOf x₀ = 3
  orderOf₁ : orderOf x₁ = 3
  comm : x₀ * x₁ = x₁ * x₀
  core_eq : pPrimeCore 2 X = Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁
  inv₀ : d₀ * x₀ * d₀⁻¹ = x₀⁻¹
  inv₁ : d₁ * x₁ * d₁⁻¹ = x₁⁻¹
  comm₀₁ : d₀ * x₁ = x₁ * d₀
  comm₁₀ : d₁ * x₀ = x₀ * d₁
  conj : τ * d₀ * τ⁻¹ = d₁

variable {V : Type*} [CommGroup V]

theorem commV_of_inverted [Finite V] (hV : ∀ v : V, v * v = 1) {t : MulAut V} {b : V}
    (ht : IsTransvectionWith t b) (ht1 : t ≠ 1) {x : MulAut V} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (htx : t * x * t⁻¹ = x⁻¹) :
    Nat.card (commV (Subgroup.zpowers x)) = 4 ∧ b ∈ commV (Subgroup.zpowers x) ∧
      (∀ c ∈ fixV (Subgroup.zpowers x), t c = c) ∧
      (∀ v ∈ commV (Subgroup.zpowers x), v = 1 ∨ v = b ∨ v = x b ∨ v = x (x b)) ∧
      (x b ≠ b ∧ x (x b) ≠ b ∧ x (x b) ≠ x b ∧ x b ≠ 1 ∧ x (x b) ≠ 1) ∧
      t (x b) = x b * b ∧ t (x (x b)) = x (x b) * b := by
  have hV' : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  obtain ⟨hb, hfix, hcard, -⟩ := B1.inverted_by_transvection hV' ht ht1 (r := 3) (by decide)
    hx3 hx1 htx
  rw [← commV_eq_commSub] at hb hcard
  obtain ⟨hmem, hxb, hxxb, hxxb', hxb1, hxxb1⟩ := mem_commV_zpowers hV hx3 hcard hb ht.1
  have htb : t b = b := B1.tv_fix ht ht1
  have hx3' : ∀ v : V, x (x (x v)) = v := by
    intro v
    have := congrArg (fun f : MulAut V => f v) hx3
    simpa [pow_succ, MulAut.mul_apply] using this
  have htx' : ∀ v : V, t (x v) = x (x (t v)) := by
    intro v
    have h1 : t * x = x⁻¹ * t := by
      calc t * x = t * x * t⁻¹ * t := by group
        _ = x⁻¹ * t := by rw [htx]
    have h2 := congrArg (fun f : MulAut V => f v) h1
    simp only [MulAut.mul_apply] at h2
    rw [h2]
    have h3 : x⁻¹ (t v) = x (x (x (x⁻¹ (t v)))) := (hx3' _).symm
    rw [h3, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have ht1' : t (x b) = x b * b := by
    rcases ht.2 (x b) with h | h
    · exfalso
      rw [htx', htb] at h
      exact hxxb' h
    · exact h
  have ht2' : t (x (x b)) = x (x b) * b := by
    rcases ht.2 (x (x b)) with h | h
    · exfalso
      rw [htx', htx', htb, hx3'] at h
      exact hxxb' h.symm
    · exact h
  exact ⟨hcard, hb, hfix, hmem, ⟨hxb, hxxb, hxxb', hxb1, hxxb1⟩, ht1', ht2'⟩

theorem exists_zpow_mul_zpow_of_mem_sup {X : Type*} [Group X] {x₀ x₁ : X}
    (hc : x₀ * x₁ = x₁ * x₀) {o : X} (ho : o ∈ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁) :
    ∃ a b : ℤ, o = x₀ ^ a * x₁ ^ b := by
  have hcomm : Commute x₀ x₁ := hc
  let P : Subgroup X :=
    { carrier := {g | ∃ a b : ℤ, g = x₀ ^ a * x₁ ^ b}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
        refine ⟨a + c, b + d, ?_⟩
        rw [zpow_add, zpow_add]
        calc x₀ ^ a * x₁ ^ b * (x₀ ^ c * x₁ ^ d) = x₀ ^ a * (x₁ ^ b * x₀ ^ c) * x₁ ^ d := by group
          _ = x₀ ^ a * (x₀ ^ c * x₁ ^ b) * x₁ ^ d := by rw [(hcomm.zpow_zpow c b).eq]
          _ = x₀ ^ a * x₀ ^ c * (x₁ ^ b * x₁ ^ d) := by group
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        refine ⟨-a, -b, ?_⟩
        rw [mul_inv_rev, zpow_neg, zpow_neg]
        exact ((hcomm.zpow_zpow a b).inv_inv).eq.symm }
  have hle : Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁ ≤ P :=
    sup_le (Subgroup.zpowers_le.mpr ⟨1, 0, by simp⟩) (Subgroup.zpowers_le.mpr ⟨0, 1, by simp⟩)
  exact hle ho

theorem mem_zpowers_of_inverted_of_mem_sup {X : Type*} [Group X] {x y d : X}
    (hc : x * y = y * x) (hy3 : y ^ 3 = 1) (hdx : d * x * d⁻¹ = x⁻¹) (hdy : y * d = d * y)
    {o : X} (ho : o ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) (hinv : d * o * d⁻¹ = o⁻¹) :
    o ∈ Subgroup.zpowers x := by
  obtain ⟨a, b, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hc ho
  have hcomm : Commute x y := hc
  have hdy' : d * y * d⁻¹ = y := by rw [← hdy]; group
  have hconj : ∀ (z : X) (j : ℤ), d * z ^ j * d⁻¹ = (d * z * d⁻¹) ^ j := fun z j => by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  have e1 : d * (x ^ a * y ^ b) * d⁻¹ = x ^ (-a) * y ^ b := by
    calc d * (x ^ a * y ^ b) * d⁻¹ = (d * x ^ a * d⁻¹) * (d * y ^ b * d⁻¹) := by group
      _ = x ^ (-a) * y ^ b := by rw [hconj, hconj, hdx, hdy', inv_zpow, zpow_neg]
  have e2 : (x ^ a * y ^ b)⁻¹ = x ^ (-a) * y ^ (-b) := by
    rw [mul_inv_rev, zpow_neg, zpow_neg]
    exact ((hcomm.zpow_zpow a b).inv_inv).eq.symm
  rw [e1, e2] at hinv
  have hb : y ^ b = 1 := eq_one_of_zpow_eq_zpow_neg hy3 (mul_left_cancel hinv)
  rw [hb, mul_one]
  exact Subgroup.zpow_mem_zpowers x a

namespace Lemma11Hyp

variable [Finite V] {X : Type*} [Group X] [Finite X] {ρ : X →* MulAut V} {d₀ d₁ x₀ x₁ τ : X}
  {b₀ b₁ : V}

theorem pow_three₀ (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) : (ρ x₀) ^ 3 = 1 := by
  rw [← map_pow, ← h.orderOf₀, pow_orderOf_eq_one, map_one]

theorem pow_three₁ (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) : (ρ x₁) ^ 3 = 1 := by
  rw [← map_pow, ← h.orderOf₁, pow_orderOf_eq_one, map_one]

theorem ne_one_x₀ (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) : ρ x₀ ≠ 1 := fun h1 => by
  have : x₀ = 1 := h.injective (h1.trans (map_one ρ).symm)
  have h3 := h.orderOf₀
  rw [this, orderOf_one] at h3
  exact absurd h3 (by decide)

theorem ne_one_x₁ (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) : ρ x₁ ≠ 1 := fun h1 => by
  have : x₁ = 1 := h.injective (h1.trans (map_one ρ).symm)
  have h3 := h.orderOf₁
  rw [this, orderOf_one] at h3
  exact absurd h3 (by decide)

private theorem conj_ρ {g x y : X} (hgx : g * x * g⁻¹ = y) : ρ g * ρ x * (ρ g)⁻¹ = ρ y := by
  rw [← map_inv, ← map_mul, ← map_mul, hgx]

theorem comm₀_facts (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    Nat.card (commV (Subgroup.zpowers (ρ x₀))) = 4 ∧ b₀ ∈ commV (Subgroup.zpowers (ρ x₀)) ∧
      (∀ c ∈ fixV (Subgroup.zpowers (ρ x₀)), ρ d₀ c = c) ∧
      (∀ v ∈ commV (Subgroup.zpowers (ρ x₀)),
        v = 1 ∨ v = b₀ ∨ v = ρ x₀ b₀ ∨ v = ρ x₀ (ρ x₀ b₀)) ∧
      (ρ x₀ b₀ ≠ b₀ ∧ ρ x₀ (ρ x₀ b₀) ≠ b₀ ∧ ρ x₀ (ρ x₀ b₀) ≠ ρ x₀ b₀ ∧ ρ x₀ b₀ ≠ 1 ∧
        ρ x₀ (ρ x₀ b₀) ≠ 1) ∧
      ρ d₀ (ρ x₀ b₀) = ρ x₀ b₀ * b₀ ∧ ρ d₀ (ρ x₀ (ρ x₀ b₀)) = ρ x₀ (ρ x₀ b₀) * b₀ :=
  commV_of_inverted h.sq_eq_one h.tv₀ h.ne_one₀ h.pow_three₀ h.ne_one_x₀
    (by rw [conj_ρ h.inv₀, map_inv])

theorem comm₁_facts (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    Nat.card (commV (Subgroup.zpowers (ρ x₁))) = 4 ∧ b₁ ∈ commV (Subgroup.zpowers (ρ x₁)) ∧
      (∀ c ∈ fixV (Subgroup.zpowers (ρ x₁)), ρ d₁ c = c) ∧
      (∀ v ∈ commV (Subgroup.zpowers (ρ x₁)),
        v = 1 ∨ v = b₁ ∨ v = ρ x₁ b₁ ∨ v = ρ x₁ (ρ x₁ b₁)) ∧
      (ρ x₁ b₁ ≠ b₁ ∧ ρ x₁ (ρ x₁ b₁) ≠ b₁ ∧ ρ x₁ (ρ x₁ b₁) ≠ ρ x₁ b₁ ∧ ρ x₁ b₁ ≠ 1 ∧
        ρ x₁ (ρ x₁ b₁) ≠ 1) ∧
      ρ d₁ (ρ x₁ b₁) = ρ x₁ b₁ * b₁ ∧ ρ d₁ (ρ x₁ (ρ x₁ b₁)) = ρ x₁ (ρ x₁ b₁) * b₁ :=
  commV_of_inverted h.sq_eq_one h.tv₁ h.ne_one₁ h.pow_three₁ h.ne_one_x₁
    (by rw [conj_ρ h.inv₁, map_inv])

private theorem comm_apply (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) (v : V) :
    ρ x₀ (ρ x₁ v) = ρ x₁ (ρ x₀ v) := by
  have := congrArg (fun f : MulAut V => f v) (show ρ x₀ * ρ x₁ = ρ x₁ * ρ x₀ by
    rw [← map_mul, ← map_mul, h.comm])
  simpa only [MulAut.mul_apply] using this

theorem fix_comm₁ (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    ∀ u ∈ commV (Subgroup.zpowers (ρ x₁)), ρ x₀ u = u := by
  have hb : ρ x₀ b₁ = b₁ := B1.tv_comm_centre h.tv₁ h.ne_one₁ (by
    rw [← map_mul, ← map_mul, h.comm₁₀])
  obtain ⟨-, -, -, hmem, -⟩ := h.comm₁_facts
  intro u hu
  rcases hmem u hu with rfl | rfl | rfl | rfl
  · exact map_one _
  · exact hb
  · rw [comm_apply h, hb]
  · rw [comm_apply h, comm_apply h, hb]

theorem fix_comm₀ (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    ∀ u ∈ commV (Subgroup.zpowers (ρ x₀)), ρ x₁ u = u := by
  have hb : ρ x₁ b₀ = b₀ := B1.tv_comm_centre h.tv₀ h.ne_one₀ (by
    rw [← map_mul, ← map_mul, h.comm₀₁])
  obtain ⟨-, -, -, hmem, -⟩ := h.comm₀_facts
  intro u hu
  rcases hmem u hu with rfl | rfl | rfl | rfl
  · exact map_one _
  · exact hb
  · rw [← comm_apply h, hb]
  · rw [← comm_apply h, ← comm_apply h, hb]

theorem comm_inf_comm (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    commV (Subgroup.zpowers (ρ x₀)) ⊓ commV (Subgroup.zpowers (ρ x₁)) = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨hu₀, hu₁⟩
  have hfix : u ∈ fixV (Subgroup.zpowers (ρ x₀)) :=
    mem_fixV_zpowers_iff_apply.mpr (h.fix_comm₁ u hu₁)
  have : u ∈ commV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₀)) := ⟨hu₀, hfix⟩
  rwa [commV_zpowers_inf_eq h.sq_eq_one h.pow_three₀] at this

private theorem card_sup_of_inf {U W : Subgroup V} (hUW : U ⊓ W = ⊥) :
    Nat.card (U ⊔ W : Subgroup V) = Nat.card U * Nat.card W :=
  CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U W
    (by rw [CommGroup.normalizer_eq_top]; exact le_top) (disjoint_iff.mpr hUW)

private theorem fix_decomp (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    (fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁))) ⊔
        commV (Subgroup.zpowers (ρ x₁)) = fixV (Subgroup.zpowers (ρ x₀)) ∧
      (fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁))) ⊓
        commV (Subgroup.zpowers (ρ x₁)) = ⊥ ∧
      Nat.card (fixV (Subgroup.zpowers (ρ x₀))) = 16 := by
  set C₀ := fixV (Subgroup.zpowers (ρ x₀)) with hC₀
  set C₁ := fixV (Subgroup.zpowers (ρ x₁)) with hC₁
  set U₀ := commV (Subgroup.zpowers (ρ x₀)) with hU₀
  set U₁ := commV (Subgroup.zpowers (ρ x₁)) with hU₁
  have hV' : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact h.sq_eq_one v
  have hcard₀ : Nat.card C₀ = 16 := by
    have h1 := card_sup_of_inf (commV_zpowers_inf_eq h.sq_eq_one h.pow_three₀)
    rw [commV_zpowers_sup_eq h.sq_eq_one h.pow_three₀, Subgroup.card_top, h.card_eq,
      h.comm₀_facts.1, ← hC₀] at h1
    norm_num at h1
    omega
  have hinv : ∀ y ∈ Subgroup.zpowers (ρ x₁), ∀ m ∈ C₀, y m ∈ C₀ := by
    intro y hy m hm
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute (ρ x₀) (ρ x₁) := by
      show ρ x₀ * ρ x₁ = ρ x₁ * ρ x₀
      rw [← map_mul, ← map_mul, h.comm]
    refine mem_fixV_zpowers_iff_apply.mpr ?_
    have hm' : ρ x₀ m = m := mem_fixV_zpowers_iff_apply.mp hm
    have := congrArg (fun f : MulAut V => f m) (hc.zpow_right n).eq
    simp only [MulAut.mul_apply] at this
    rw [this, hm']
  have hU₁C₀ : U₁ ≤ C₀ := fun u hu => mem_fixV_zpowers_iff_apply.mpr (h.fix_comm₁ u hu)
  have hodd : Odd (Nat.card (Subgroup.zpowers (ρ x₁))) := by
    rw [Nat.card_zpowers, orderOf_injective ρ h.injective, h.orderOf₁]
    decide
  obtain ⟨hsup, hinf⟩ := B1.coprime_decomp hV' hodd hinv
  have hle : commSub C₀ (Subgroup.zpowers (ρ x₁)) ≤ U₁ := by
    rw [hU₁, commV_eq_commSub]
    exact Subgroup.closure_mono fun c ⟨y, hy, w, _, hc⟩ => ⟨y, hy, w, trivial, hc⟩
  have hU₁C₁ : U₁ ⊓ C₁ = ⊥ := commV_zpowers_inf_eq h.sq_eq_one h.pow_three₁
  have hge : U₁ ≤ commSub C₀ (Subgroup.zpowers (ρ x₁)) := by
    intro u hu
    have huC₀ : u ∈ (C₀ ⊓ C₁) ⊔ commSub C₀ (Subgroup.zpowers (ρ x₁)) := by
      rw [hsup]; exact hU₁C₀ hu
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp huC₀
    have haU₁ : a ∈ U₁ := by
      have : a = a * c * c⁻¹ := by group
      rw [this]
      exact U₁.mul_mem hu (U₁.inv_mem (hle hc))
    have : a ∈ U₁ ⊓ C₁ := ⟨haU₁, ha.2⟩
    rw [hU₁C₁, Subgroup.mem_bot] at this
    rw [this, one_mul]
    exact hc
  have heq : commSub C₀ (Subgroup.zpowers (ρ x₁)) = U₁ := le_antisymm hle hge
  rw [heq] at hsup hinf
  exact ⟨hsup, hinf, hcard₀⟩

theorem mem_fix_iff (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) {v : V} :
    v ∈ fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁)) ↔
      ∀ o ∈ pPrimeCore 2 X, ρ o v = v := by
  constructor
  · rintro ⟨h0, h1⟩ o ho
    let S : Subgroup X := (MulAction.stabilizer (MulAut V) v).comap ρ
    have hle : Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁ ≤ S := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact mem_fixV_zpowers_iff_apply.mp h0
      · exact mem_fixV_zpowers_iff_apply.mp h1
    rw [h.core_eq] at ho
    exact hle ho
  · intro hv
    have hx₀ : x₀ ∈ pPrimeCore 2 X := by
      rw [h.core_eq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x₀)
    have hx₁ : x₁ ∈ pPrimeCore 2 X := by
      rw [h.core_eq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x₁)
    exact ⟨mem_fixV_zpowers_iff_apply.mpr (hv x₀ hx₀), mem_fixV_zpowers_iff_apply.mpr (hv x₁ hx₁)⟩

theorem card_fix (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    Nat.card (fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁)) : Subgroup V) = 4 := by
  obtain ⟨hsup, hinf, hcard⟩ := h.fix_decomp
  have h1 := card_sup_of_inf hinf
  rw [hsup, hcard, h.comm₁_facts.1] at h1
  omega

theorem fix_inf_eq (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    (fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁))) ⊓
      (commV (Subgroup.zpowers (ρ x₀)) ⊔ commV (Subgroup.zpowers (ρ x₁))) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨⟨hv₀, hv₁⟩, hvU⟩
  obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := Subgroup.mem_sup.mp hvU
  have hx₀ : ρ x₀ (u₀ * u₁) = u₀ * u₁ := mem_fixV_zpowers_iff_apply.mp hv₀
  rw [map_mul, h.fix_comm₁ u₁ hu₁] at hx₀
  have hu₀' : ρ x₀ u₀ = u₀ := mul_right_cancel hx₀
  have h1 : u₀ ∈ commV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₀)) :=
    ⟨hu₀, mem_fixV_zpowers_iff_apply.mpr hu₀'⟩
  rw [commV_zpowers_inf_eq h.sq_eq_one h.pow_three₀, Subgroup.mem_bot] at h1
  rw [h1, one_mul] at hv₁ ⊢
  have h2 : u₁ ∈ commV (Subgroup.zpowers (ρ x₁)) ⊓ fixV (Subgroup.zpowers (ρ x₁)) := ⟨hu₁, hv₁⟩
  rwa [commV_zpowers_inf_eq h.sq_eq_one h.pow_three₁] at h2

theorem fix_sup_eq (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    (fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁))) ⊔
      commV (Subgroup.zpowers (ρ x₀)) ⊔ commV (Subgroup.zpowers (ρ x₁)) = ⊤ := by
  obtain ⟨hsup, -, -⟩ := h.fix_decomp
  have h1 := commV_zpowers_sup_eq h.sq_eq_one h.pow_three₀
  rw [← hsup] at h1
  rw [← h1, sup_comm (commV _) (_ ⊔ _), sup_assoc, sup_assoc, sup_comm (commV (Subgroup.zpowers (ρ x₁)))]

theorem d₀_fix (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    ∀ v ∈ fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁)), ρ d₀ v = v :=
  fun v hv => h.comm₀_facts.2.2.1 v hv.1

theorem d₁_fix (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    ∀ v ∈ fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁)), ρ d₁ v = v :=
  fun v hv => h.comm₁_facts.2.2.1 v hv.2

theorem fix_invariant (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) (g : X) :
    ∀ v ∈ fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁)),
      ρ g v ∈ fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁)) := by
  intro v hv
  rw [h.mem_fix_iff] at hv ⊢
  intro o ho
  have hconj : g⁻¹ * o * g ∈ pPrimeCore 2 X := by
    have := (inferInstance : (pPrimeCore 2 X).Normal).conj_mem o ho g⁻¹
    rwa [inv_inv] at this
  have e : ρ o (ρ g v) = ρ g (ρ (g⁻¹ * o * g) v) := by
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  rw [e, hv _ hconj]

theorem d₀_apply (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) {u : V}
    (hu : u ∈ commV (Subgroup.zpowers (ρ x₀))) (hu1 : u ≠ 1) (hub : u ≠ b₀) :
    ρ d₀ u = u * b₀ := by
  obtain ⟨-, -, -, hmem, -, h1, h2⟩ := h.comm₀_facts
  rcases hmem u hu with rfl | rfl | rfl | rfl
  · exact absurd rfl hu1
  · exact absurd rfl hub
  · exact h1
  · exact h2

theorem d₁_apply (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) {u : V}
    (hu : u ∈ commV (Subgroup.zpowers (ρ x₁))) (hu1 : u ≠ 1) (hub : u ≠ b₁) :
    ρ d₁ u = u * b₁ := by
  obtain ⟨-, -, -, hmem, -, h1, h2⟩ := h.comm₁_facts
  rcases hmem u hu with rfl | rfl | rfl | rfl
  · exact absurd rfl hu1
  · exact absurd rfl hub
  · exact h1
  · exact h2

theorem exists_conj₀ (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) {u : V}
    (hu : u ∈ commV (Subgroup.zpowers (ρ x₀))) (hu1 : u ≠ 1) :
    ∃ g ∈ Subgroup.zpowers x₀, ρ g b₀ = u := by
  obtain ⟨-, -, -, hmem, -⟩ := h.comm₀_facts
  rcases hmem u hu with rfl | rfl | rfl | rfl
  · exact absurd rfl hu1
  · exact ⟨1, Subgroup.one_mem _, by rw [map_one, MulAut.one_apply]⟩
  · exact ⟨x₀, Subgroup.mem_zpowers x₀, rfl⟩
  · exact ⟨x₀ * x₀, Subgroup.mul_mem _ (Subgroup.mem_zpowers x₀) (Subgroup.mem_zpowers x₀),
      by rw [map_mul, MulAut.mul_apply]⟩

theorem exists_conj₁ (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) {u : V}
    (hu : u ∈ commV (Subgroup.zpowers (ρ x₁))) (hu1 : u ≠ 1) :
    ∃ g ∈ Subgroup.zpowers x₁, ρ g b₁ = u := by
  obtain ⟨-, -, -, hmem, -⟩ := h.comm₁_facts
  rcases hmem u hu with rfl | rfl | rfl | rfl
  · exact absurd rfl hu1
  · exact ⟨1, Subgroup.one_mem _, by rw [map_one, MulAut.one_apply]⟩
  · exact ⟨x₁, Subgroup.mem_zpowers x₁, rfl⟩
  · exact ⟨x₁ * x₁, Subgroup.mul_mem _ (Subgroup.mem_zpowers x₁) (Subgroup.mem_zpowers x₁),
      by rw [map_mul, MulAut.mul_apply]⟩

theorem exists_conj_mul (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) {u₀ u₁ : V}
    (hu₀ : u₀ ∈ commV (Subgroup.zpowers (ρ x₀))) (hu₀1 : u₀ ≠ 1)
    (hu₁ : u₁ ∈ commV (Subgroup.zpowers (ρ x₁))) (hu₁1 : u₁ ≠ 1) :
    ∃ g ∈ pPrimeCore 2 X, ρ g (b₀ * b₁) = u₀ * u₁ := by
  obtain ⟨g₀, hg₀, hg₀b⟩ := h.exists_conj₀ hu₀ hu₀1
  obtain ⟨g₁, hg₁, hg₁b⟩ := h.exists_conj₁ hu₁ hu₁1
  have hb₀ : ρ g₁ b₀ = b₀ := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₁
    rw [map_zpow]
    exact B1.zpowers_fix (h.fix_comm₀ b₀ h.comm₀_facts.2.1) _ (Subgroup.zpow_mem_zpowers _ n)
  have hu₁' : ρ g₀ u₁ = u₁ := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₀
    rw [map_zpow]
    exact B1.zpowers_fix (h.fix_comm₁ u₁ hu₁) _ (Subgroup.zpow_mem_zpowers _ n)
  refine ⟨g₀ * g₁, ?_, ?_⟩
  · rw [h.core_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg₀) (Subgroup.mem_sup_right hg₁)
  · rw [map_mul ρ g₀ g₁, MulAut.mul_apply, map_mul (ρ g₁) b₀ b₁, hb₀, hg₁b,
      map_mul (ρ g₀) b₀ u₁, hg₀b, hu₁']

theorem mem_zpowers₁_of_inverted (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) {o : X}
    (ho : o ∈ pPrimeCore 2 X) (hinv : d₁ * o * d₁⁻¹ = o⁻¹) : o ∈ Subgroup.zpowers x₁ := by
  rw [h.core_eq, sup_comm] at ho
  have hx₀3 : x₀ ^ 3 = 1 := by rw [← h.orderOf₀]; exact pow_orderOf_eq_one x₀
  exact mem_zpowers_of_inverted_of_mem_sup h.comm.symm hx₀3 h.inv₁ h.comm₁₀.symm ho hinv

theorem mem_zpowers₀_of_inverted (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) {o : X}
    (ho : o ∈ pPrimeCore 2 X) (hinv : d₀ * o * d₀⁻¹ = o⁻¹) : o ∈ Subgroup.zpowers x₀ := by
  rw [h.core_eq] at ho
  have hx₁3 : x₁ ^ 3 = 1 := by rw [← h.orderOf₁]; exact pow_orderOf_eq_one x₁
  exact mem_zpowers_of_inverted_of_mem_sup h.comm hx₁3 h.inv₀ h.comm₀₁.symm ho hinv

theorem conj_mem_zpowers (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    τ * x₀ * τ⁻¹ ∈ Subgroup.zpowers x₁ ∧ τ⁻¹ * x₁ * τ ∈ Subgroup.zpowers x₀ := by
  have hO := (inferInstance : (pPrimeCore 2 X).Normal)
  have hx₀ : x₀ ∈ pPrimeCore 2 X := by
    rw [h.core_eq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x₀)
  have hx₁ : x₁ ∈ pPrimeCore 2 X := by
    rw [h.core_eq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x₁)
  constructor
  · apply h.mem_zpowers₁_of_inverted (hO.conj_mem x₀ hx₀ τ)
    rw [← h.conj]
    calc τ * d₀ * τ⁻¹ * (τ * x₀ * τ⁻¹) * (τ * d₀ * τ⁻¹)⁻¹ = τ * (d₀ * x₀ * d₀⁻¹) * τ⁻¹ := by
          group
      _ = (τ * x₀ * τ⁻¹)⁻¹ := by rw [h.inv₀]; group
  · have hτ : τ⁻¹ * x₁ * τ ∈ pPrimeCore 2 X := by
      have := hO.conj_mem x₁ hx₁ τ⁻¹
      rwa [inv_inv] at this
    apply h.mem_zpowers₀_of_inverted hτ
    have hd₀ : d₀ = τ⁻¹ * d₁ * τ := by rw [← h.conj]; group
    rw [hd₀]
    calc τ⁻¹ * d₁ * τ * (τ⁻¹ * x₁ * τ) * (τ⁻¹ * d₁ * τ)⁻¹ = τ⁻¹ * (d₁ * x₁ * d₁⁻¹) * τ := by
          group
      _ = (τ⁻¹ * x₁ * τ)⁻¹ := by rw [h.inv₁]; group

private theorem apply_mem_commV_of_conj {g x y : X} (hg : g * x * g⁻¹ ∈ Subgroup.zpowers y) :
    ∀ v ∈ commV (Subgroup.zpowers (ρ x)), ρ g v ∈ commV (Subgroup.zpowers (ρ y)) := by
  intro v hv
  rw [commV_eq_commSub] at hv ⊢
  refine B1.commSub_smul_mem (M := ⊤) (M' := ⊤) (ρ g) (fun z hz => ?_)
    (fun _ _ => Subgroup.mem_top _) v hv
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hg
  have e : ρ g * ρ x ^ n * (ρ g)⁻¹ = (ρ (g * x * g⁻¹)) ^ n := by
    rw [map_mul, map_mul, map_inv, ← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  rw [e, ← hm, map_zpow, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers _ _

theorem map_comm_eq (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    (commV (Subgroup.zpowers (ρ x₀))).map (ρ τ).toMonoidHom = commV (Subgroup.zpowers (ρ x₁)) := by
  obtain ⟨h₀, h₁⟩ := h.conj_mem_zpowers
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact apply_mem_commV_of_conj h₀ u hu
  · intro u hu
    have h₁' : τ⁻¹ * x₁ * τ⁻¹⁻¹ ∈ Subgroup.zpowers x₀ := by rwa [inv_inv]
    refine ⟨ρ τ⁻¹ u, apply_mem_commV_of_conj h₁' u hu, ?_⟩
    show ρ τ (ρ τ⁻¹ u) = u
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem fix_inf_closure_eq (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    (fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁))) ⊓
      Subgroup.closure ({b₀, b₁} : Set V) = ⊥ := by
  have hle : Subgroup.closure ({b₀, b₁} : Set V) ≤
      commV (Subgroup.zpowers (ρ x₀)) ⊔ commV (Subgroup.zpowers (ρ x₁)) := by
    rw [Subgroup.closure_le]
    rintro v (rfl | rfl)
    · exact Subgroup.mem_sup_left h.comm₀_facts.2.1
    · exact Subgroup.mem_sup_right h.comm₁_facts.2.1
  rw [eq_bot_iff, ← h.fix_inf_eq]
  exact inf_le_inf_left _ hle

end Lemma11Hyp

end CFSG.CGT.Foote81L6.Normalizer
