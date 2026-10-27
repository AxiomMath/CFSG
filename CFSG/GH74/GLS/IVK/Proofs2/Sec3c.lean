module

public import CFSG.GH74.GLS.IVK.Proofs2.Sec3Fac
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

open Subgroup CFSG CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.IVK.Proofs2

section Sec3c

variable {H : Type} [Group H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem twist_conj {z w x : H} (hxx : x * x = z) (hwx : w * x * w⁻¹ = x⁻¹) :
    x * w * x⁻¹ = z * w := by
  have h1 : w * x⁻¹ * w⁻¹ = x := by
    calc w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [hwx]
      _ = x := inv_inv x
  calc x * w * x⁻¹ = x * (w * x⁻¹ * w⁻¹) * w := by group
    _ = x * x * w := by rw [h1]
    _ = z * w := by rw [hxx]

theorem FactorFacts.conj_to_w (h : ProdSL2 H K₁ K₂ F₁ F₂) {z w : H} (hz : z ∈ K₁ ⊓ K₂)
    (f : FactorFacts K₁ K₂ z w) {a : H} (ha : a ∈ K₁) (hsq : (a * w) * (a * w) ∈ K₂) :
    ∃ g ∈ K₁, a * w = g * w * g⁻¹ := by
  obtain ⟨k, hk, h1 | h1⟩ := f.conj a ha hsq
  · exact ⟨k, hk, h1⟩
  · obtain ⟨x, hx, hxx, hwx⟩ := f.twist
    refine ⟨k * x, K₁.mul_mem hk hx, ?_⟩
    have hxw := twist_conj hxx hwx
    have hzk : Commute z k := (h.comm k hk z hz.2).symm
    rw [h1]
    calc z * (k * w * k⁻¹) = k * (z * w) * k⁻¹ := by
          have := hzk.eq
          calc z * (k * w * k⁻¹) = (z * k) * w * k⁻¹ := by group
            _ = (k * z) * w * k⁻¹ := by rw [this]
            _ = k * (z * w) * k⁻¹ := by group
      _ = k * (x * w * x⁻¹) * k⁻¹ := by rw [hxw]
      _ = (k * x) * w * (k * x)⁻¹ := by group

theorem prodSL2_invol_conj_w (h : ProdSL2 H K₁ K₂ F₁ F₂) {z w : H} (hz : z ∈ K₁ ⊓ K₂)
    (hw2 : w * w = 1) (hw₁ : ∀ x ∈ K₁, w * x * w⁻¹ ∈ K₁) (hw₂ : ∀ x ∈ K₂, w * x * w⁻¹ ∈ K₂)
    (f₁ : FactorFacts K₁ K₂ z w) (f₂ : FactorFacts K₂ K₁ z w) {x : H}
    (hx : ∃ k ∈ K₁ ⊔ K₂, x = k * w) (hx2 : x * x = 1) :
    ∃ g ∈ K₁ ⊔ K₂, g * w * g⁻¹ = x := by
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_sup_iff k).1 hk
  set a' := w * a * w⁻¹ with ha'
  set b' := w * b * w⁻¹ with hb'
  have ha'K : a' ∈ K₁ := hw₁ a ha
  have hb'K : b' ∈ K₂ := hw₂ b hb
  have h1 : (a * b * w) * (a * b * w) = (a * a') * (b * b') := by
    calc (a * b * w) * (a * b * w) = a * b * (w * a * w⁻¹) * (w * b * w⁻¹) * (w * w) := by group
      _ = a * b * a' * b' := by rw [hw2, mul_one]
      _ = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← h.comm a' ha'K b hb]
      _ = (a * a') * (b * b') := by group
  have h2 : a * a' = (b * b')⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← h1]; exact hx2)
  have haa'₂ : a * a' ∈ K₂ := by rw [h2]; exact K₂.inv_mem (K₂.mul_mem hb hb'K)
  have hbb'₁ : b * b' ∈ K₁ := by
    have : b * b' = (a * a')⁻¹ := by rw [h2, inv_inv]
    rw [this]; exact K₁.inv_mem (K₁.mul_mem ha ha'K)
  have hsq₁ : (a * w) * (a * w) ∈ K₂ := by
    have : (a * w) * (a * w) = a * a' := by
      calc (a * w) * (a * w) = a * (w * a * w⁻¹) * (w * w) := by group
        _ = a * a' := by rw [hw2, mul_one]
    rw [this]; exact haa'₂
  have hsq₂ : (b * w) * (b * w) ∈ K₁ := by
    have : (b * w) * (b * w) = b * b' := by
      calc (b * w) * (b * w) = b * (w * b * w⁻¹) * (w * w) := by group
        _ = b * b' := by rw [hw2, mul_one]
    rw [this]; exact hbb'₁
  obtain ⟨g₁, hg₁, hag₁⟩ := f₁.conj_to_w h hz ha hsq₁
  obtain ⟨g₂, hg₂, hbg₂⟩ := f₂.conj_to_w h.symm (by rwa [inf_comm] at hz) hb hsq₂
  refine ⟨g₁ * g₂, Subgroup.mul_mem_sup hg₁ hg₂, ?_⟩
  have hcg : g₁ * g₂ = g₂ * g₁ := h.comm g₁ hg₁ g₂ hg₂
  have hag : a * g₂ = g₂ * a := h.comm a ha g₂ hg₂
  calc (g₁ * g₂) * w * (g₁ * g₂)⁻¹ = (g₂ * g₁) * w * (g₂ * g₁)⁻¹ := by rw [hcg]
    _ = g₂ * (g₁ * w * g₁⁻¹) * g₂⁻¹ := by group
    _ = g₂ * (a * w) * g₂⁻¹ := by rw [hag₁]
    _ = (g₂ * a) * w * g₂⁻¹ := by group
    _ = (a * g₂) * w * g₂⁻¹ := by rw [hag]
    _ = a * (g₂ * w * g₂⁻¹) := by group
    _ = a * (b * w) := by rw [hbg₂]
    _ = a * b * w := by group

theorem prodSL2_invol_conj (h : ProdSL2 H K₁ K₂ F₁ F₂) {z w : H} (hz : z ∈ K₁ ⊓ K₂)
    (hw2 : w * w = 1) (hw₁ : ∀ x ∈ K₁, w * x * w⁻¹ ∈ K₁) (hw₂ : ∀ x ∈ K₂, w * x * w⁻¹ ∈ K₂)
    (f₁ : FactorFacts K₁ K₂ z w) (f₂ : FactorFacts K₂ K₁ z w) {x y : H}
    (hx : ∃ k ∈ K₁ ⊔ K₂, x = k * w) (hy : ∃ k ∈ K₁ ⊔ K₂, y = k * w)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) : ConjUnder (K₁ ⊔ K₂) x y := by
  obtain ⟨gx, hgx, hgx'⟩ := prodSL2_invol_conj_w h hz hw2 hw₁ hw₂ f₁ f₂ hx
    (CFSG.GH74.GLS.IVK.Proofs2.mul_self_eq_one_of_orderOf_eq_two hx2)
  obtain ⟨gy, hgy, hgy'⟩ := prodSL2_invol_conj_w h hz hw2 hw₁ hw₂ f₁ f₂ hy
    (CFSG.GH74.GLS.IVK.Proofs2.mul_self_eq_one_of_orderOf_eq_two hy2)
  refine ⟨gy * gx⁻¹, (K₁ ⊔ K₂).mul_mem hgy ((K₁ ⊔ K₂).inv_mem hgx), ?_⟩
  rw [← hgx', ← hgy']
  group

end Sec3c

section Sec3cCard

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem card_sylow_two_of_four_mul_odd {G : Type*} [Group G] [Finite G] {m : ℕ} (hm : Odd m)
    (hcard : Nat.card G = 4 * m) (S : Sylow 2 G) : Nat.card S = 4 := by
  have h := Sylow.card_eq_multiplicity S
  rw [hcard] at h
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  have hfac : (4 * m).factorization 2 = 2 := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply, h4,
      Nat.Prime.factorization_pow Nat.prime_two]
    have : m.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd))
    simp [this]
  rw [hfac] at h
  simpa using h

theorem prodSL2_card_centralizer_w (h : ProdSL2 H K₁ K₂ F₁ F₂) {z w : H} (hz : z ∈ K₁ ⊓ K₂)
    (hz1 : z ≠ 1) (hw₁ : ∀ x ∈ K₁, w * x * w⁻¹ ∈ K₁)
    (hw₂ : ∀ x ∈ K₂, w * x * w⁻¹ ∈ K₂)
    (f₁ : FactorFacts K₁ K₂ z w) (f₂ : FactorFacts K₂ K₁ z w) :
    ∃ m : ℕ, Odd m ∧ Nat.card ↥(Subgroup.centralizer ({w} : Set H) ⊓ (K₁ ⊔ K₂)) = 4 * m := by
  obtain ⟨S₁, hS₁, m₁, hm₁, hc₁⟩ := f₁.card
  obtain ⟨S₂, hS₂, m₂, hm₂, hc₂⟩ := f₂.card
  obtain ⟨x₁, hx₁, hx₁z, hwx₁⟩ := f₁.twist
  obtain ⟨hint, hzo⟩ := h.inter_eq hz hz1
  have hzz : z * z = 1 := CFSG.GH74.GLS.IVK.Proofs2.mul_self_eq_one_of_orderOf_eq_two hzo
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hwz : w * z = z * w := w_comm_z h hz hz1 hw₁ hw₂
  have hwzw : w * z * w⁻¹ = z := by
    calc w * z * w⁻¹ = (z * w) * w⁻¹ := by rw [hwz]
      _ = z := by group
  have hS₁le : S₁ ≤ K₁ := fun a ha => ((hS₁ a).1 ha).1
  have hS₂le : S₂ ≤ K₂ := fun a ha => ((hS₂ a).1 ha).1
  have hcommS : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b = b * a :=
    fun a ha b hb => h.comm a (hS₁le ha) b (hS₂le hb)
  obtain ⟨hcardS, hsetS⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute S₁ S₂ hcommS
  have hzS₁ : z ∈ S₁ := (hS₁ z).2 ⟨hz.1, by
    have : w * z * w⁻¹ * z⁻¹ = 1 := by rw [hwzw]; group
    rw [this]; exact K₂.one_mem⟩
  have hzS₂ : z ∈ S₂ := (hS₂ z).2 ⟨hz.2, by
    have : w * z * w⁻¹ * z⁻¹ = 1 := by rw [hwzw]; group
    rw [this]; exact K₁.one_mem⟩
  have hinfS : S₁ ⊓ S₂ = K₁ ⊓ K₂ := by
    apply le_antisymm (inf_le_inf hS₁le hS₂le)
    rw [hint, Subgroup.zpowers_le]
    exact ⟨hzS₁, hzS₂⟩
  have hcard2 : Nat.card ↥(S₁ ⊓ S₂) = 2 := by rw [hinfS]; exact h.card_inter
  set S := S₁ ⊔ S₂ with hS
  set C := Subgroup.centralizer ({w} : Set H) ⊓ (K₁ ⊔ K₂) with hC
  have hScard : Nat.card S = 8 * (m₁ * m₂) := by
    rw [hcard2, hc₁, hc₂] at hcardS
    nlinarith
  have hSK : S ≤ K₁ ⊔ K₂ := sup_le (hS₁le.trans le_sup_left) (hS₂le.trans le_sup_right)
  have hcomm_mem : ∀ s ∈ S, w * s * w⁻¹ * s⁻¹ = 1 ∨ w * s * w⁻¹ * s⁻¹ = z := by
    intro s hs
    have : s ∈ (S₁ : Set H) * (S₂ : Set H) := by rw [← hsetS]; exact hs
    obtain ⟨a, ha, b, hb, rfl⟩ := this
    have haK : a ∈ K₁ := hS₁le ha
    have hbK : b ∈ K₂ := hS₂le hb
    have h1 : w * a * w⁻¹ * a⁻¹ ∈ K₁ ⊓ K₂ :=
      ⟨K₁.mul_mem (hw₁ a haK) (K₁.inv_mem haK), ((hS₁ a).1 ha).2⟩
    have h2 : w * b * w⁻¹ * b⁻¹ ∈ K₁ ⊓ K₂ :=
      ⟨((hS₂ b).1 hb).2, K₂.mul_mem (hw₂ b hbK) (K₂.inv_mem hbK)⟩
    have hc1 := h.inter_cases hz hz1 _ h1
    have hc2 := h.inter_cases hz hz1 _ h2
    have hcom : (w * b * w⁻¹ * b⁻¹) * a⁻¹ = a⁻¹ * (w * b * w⁻¹ * b⁻¹) := by
      rcases hc2 with h2' | h2'
      · rw [h2']; simp
      · rw [h2']; exact (h.comm a⁻¹ (K₁.inv_mem haK) z hz.2).symm
    have hexp : w * (a * b) * w⁻¹ * (a * b)⁻¹ =
        (w * a * w⁻¹ * a⁻¹) * (w * b * w⁻¹ * b⁻¹) := by
      calc w * (a * b) * w⁻¹ * (a * b)⁻¹
          = (w * a * w⁻¹) * ((w * b * w⁻¹ * b⁻¹) * a⁻¹) := by group
        _ = (w * a * w⁻¹) * (a⁻¹ * (w * b * w⁻¹ * b⁻¹)) := by rw [hcom]
        _ = (w * a * w⁻¹ * a⁻¹) * (w * b * w⁻¹ * b⁻¹) := by group
    rw [hexp]
    rcases hc1 with h1' | h1' <;> rcases hc2 with h2' | h2'
    · left; rw [h1', h2']; group
    · right; rw [h1', h2']; group
    · right; rw [h1', h2']; group
    · left; rw [h1', h2']; exact hzz
  have hCS : C ≤ S := by
    intro c hc
    obtain ⟨hcw, hcK⟩ := hc
    obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_sup_iff c).1 hcK
    have hcw' : (a * b) * w = w * (a * b) := Subgroup.mem_centralizer_singleton_iff.mp hcw
    have ha'K : w * a * w⁻¹ ∈ K₁ := hw₁ a ha
    have hb'K : w * b * w⁻¹ ∈ K₂ := hw₂ b hb
    have hab : (w * a * w⁻¹) * (w * b * w⁻¹) = a * b := by
      calc (w * a * w⁻¹) * (w * b * w⁻¹) = w * (a * b) * w⁻¹ := by group
        _ = a * b := by rw [← hcw']; group
    have he : a⁻¹ * (w * a * w⁻¹) = b * (w * b * w⁻¹)⁻¹ := by
      calc a⁻¹ * (w * a * w⁻¹)
          = a⁻¹ * ((w * a * w⁻¹) * (w * b * w⁻¹)) * (w * b * w⁻¹)⁻¹ := by group
        _ = a⁻¹ * (a * b) * (w * b * w⁻¹)⁻¹ := by rw [hab]
        _ = b * (w * b * w⁻¹)⁻¹ := by group
    have heK : a⁻¹ * (w * a * w⁻¹) ∈ K₁ ⊓ K₂ :=
      ⟨K₁.mul_mem (K₁.inv_mem ha) ha'K, by rw [he]; exact K₂.mul_mem hb (K₂.inv_mem hb'K)⟩
    have hecomm : ∀ y ∈ K₁, (a⁻¹ * (w * a * w⁻¹)) * y = y * (a⁻¹ * (w * a * w⁻¹)) := by
      intro y hy
      rcases h.inter_cases hz hz1 _ heK with h' | h'
      · rw [h']; simp
      · rw [h']; exact (h.comm y hy z hz.2).symm
    have haS : a ∈ S₁ := by
      refine (hS₁ a).2 ⟨ha, ?_⟩
      have hea := hecomm a ha
      have : w * a * w⁻¹ * a⁻¹ = a⁻¹ * (w * a * w⁻¹) := by
        calc w * a * w⁻¹ * a⁻¹ = (a * (a⁻¹ * (w * a * w⁻¹))) * a⁻¹ := by group
          _ = ((a⁻¹ * (w * a * w⁻¹)) * a) * a⁻¹ := by rw [hea]
          _ = a⁻¹ * (w * a * w⁻¹) := by group
      rw [this]; exact heK.2
    have hbS : b ∈ S₂ := by
      refine (hS₂ b).2 ⟨hb, ?_⟩
      have : w * b * w⁻¹ * b⁻¹ = (a⁻¹ * (w * a * w⁻¹))⁻¹ := by
        rw [he]; group
      rw [this]; exact K₁.inv_mem heK.1
    exact Subgroup.mul_mem_sup haS hbS
  have hx₁S₁ : x₁ ∈ S₁ := (hS₁ x₁).2 ⟨hx₁, by
    have h1 : x₁⁻¹ * x₁⁻¹ = z := by
      calc x₁⁻¹ * x₁⁻¹ = (x₁ * x₁)⁻¹ := by group
        _ = z⁻¹ := by rw [hx₁z]
        _ = z := hzi
    have : w * x₁ * w⁻¹ * x₁⁻¹ = z := by rw [hwx₁, h1]
    rw [this]; exact hz.2⟩
  have hx₁S : x₁ ∈ S := Subgroup.mem_sup_left hx₁S₁
  have hmemC : ∀ s ∈ S, (s ∈ C ↔ w * s * w⁻¹ * s⁻¹ = 1) := by
    intro s hs
    constructor
    · rintro ⟨hsw, -⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp hsw
      calc w * s * w⁻¹ * s⁻¹ = (s * w) * w⁻¹ * s⁻¹ := by rw [this]
        _ = 1 := by group
    · intro h1
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hSK hs⟩
      calc s * w = (w * s * w⁻¹ * s⁻¹) * (s * w) := by rw [h1, one_mul]
        _ = w * s := by group
  have hmul : ∀ s ∈ S, w * (s * x₁) * w⁻¹ * (s * x₁)⁻¹ = z * (w * s * w⁻¹ * s⁻¹) := by
    intro s hs
    have hzs : Commute z s := h.z_comm hz (hSK hs)
    have hzw : Commute z w := hwz.symm
    have hzc : Commute z (w * s * w⁻¹) := (hzw.mul_right hzs).mul_right hzw.inv_right
    have h1 : x₁⁻¹ * x₁⁻¹ = z := by
      calc x₁⁻¹ * x₁⁻¹ = (x₁ * x₁)⁻¹ := by group
        _ = z⁻¹ := by rw [hx₁z]
        _ = z := hzi
    calc w * (s * x₁) * w⁻¹ * (s * x₁)⁻¹
        = (w * s * w⁻¹) * (w * x₁ * w⁻¹) * x₁⁻¹ * s⁻¹ := by group
      _ = (w * s * w⁻¹) * (x₁⁻¹ * x₁⁻¹) * s⁻¹ := by rw [hwx₁]; group
      _ = (w * s * w⁻¹) * z * s⁻¹ := by rw [h1]
      _ = z * (w * s * w⁻¹) * s⁻¹ := by rw [hzc.eq.symm]
      _ = z * (w * s * w⁻¹ * s⁻¹) := by group
  have hidx : (C.subgroupOf S).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x₁, hx₁S⟩, fun b => ?_⟩
    have hbS : (b : H) ∈ S := b.2
    have hbx : ((b : H) * x₁) ∈ S := S.mul_mem hbS hx₁S
    show Xor (((b : H) * x₁) ∈ C) ((b : H) ∈ C)
    rw [hmemC _ hbx, hmemC _ hbS, hmul _ hbS]
    rcases hcomm_mem b hbS with h' | h'
    · rw [h']
      right
      refine ⟨rfl, ?_⟩
      simpa using hz1
    · rw [h']
      left
      refine ⟨hzz, ?_⟩
      exact hz1
  have hcardN : Nat.card (C.subgroupOf S) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCS).toEquiv
  have h3 := Subgroup.card_mul_index (C.subgroupOf S)
  rw [hidx, hcardN, hScard] at h3
  exact ⟨m₁ * m₂, hm₁.mul hm₂, by linarith⟩

end Sec3cCard

section Sec3Final

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem factorFacts_of_diag
    (h : ProdSL2 H K₁ K₂ F₁ F₂) {z w : H} (hz : z ∈ K₁ ⊓ K₂)
    (hz1 : z ≠ 1) (hw2 : w * w = 1) (hd : IsDiagInv K₁ K₂ F₁ F₂ w) :
    FactorFacts K₁ K₂ z w ∧ FactorFacts K₂ K₁ z w := by
  have := h.finite₁
  have := h.symm.finite₁
  have hz' : z ∈ K₂ ⊓ K₁ := by rwa [inf_comm] at hz
  obtain ⟨hw₁, hw₂, ⟨hN₁, ⟨θ₂⟩⟩, ⟨hN₂, ⟨θ₁⟩⟩⟩ := hd
  have := hN₁
  have := hN₂
  obtain ⟨Q₁⟩ := QuotData.of_equiv K₂ (K₁ ⊔ K₂ ⊔ Subgroup.zpowers w) θ₁
  obtain ⟨Q₂⟩ := QuotData.of_equiv K₁ (K₁ ⊔ K₂ ⊔ Subgroup.zpowers w) θ₂
  refine ⟨factorFacts h (odd_card_left h hz hz1) hz hz1 hw2 hw₁ hw₂ rfl Q₁, ?_⟩
  exact factorFacts h.symm (odd_card_left h.symm hz' hz1) hz' hz1 hw2 hw₂ hw₁
    (by rw [sup_comm K₂ K₁]) Q₂

theorem prodSL2_exists_z (h : ProdSL2 H K₁ K₂ F₁ F₂) : ∃ z ∈ K₁ ⊓ K₂, z ≠ 1 := by
  have hn : Nontrivial ↥(K₁ ⊓ K₂) := by
    rw [← Finite.one_lt_card_iff_nontrivial, h.card_inter]; norm_num
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥(K₁ ⊓ K₂))
  exact ⟨a, a.2, fun h1 => ha (Subtype.ext h1)⟩

theorem ivk_3_1c : IVK_3_1c := by
  intro F₁ F₂ _ _ H _ _ K₁ K₂ h T w _ hw2 hd
  have hww : w * w = 1 := CFSG.GH74.GLS.IVK.Proofs2.mul_self_eq_one_of_orderOf_eq_two hw2
  obtain ⟨z, hz, hz1⟩ := prodSL2_exists_z h
  obtain ⟨f₁, f₂⟩ := factorFacts_of_diag h hz hz1 hww hd
  obtain ⟨hw₁, hw₂, -⟩ := hd
  refine ⟨?_, ?_⟩
  · intro x y hx hy hx2 hy2
    exact prodSL2_invol_conj h hz hww hw₁ hw₂ f₁ f₂ hx hy hx2 hy2
  · intro S
    obtain ⟨m, hm, hcard⟩ := prodSL2_card_centralizer_w h hz hz1 hw₁ hw₂ f₁ f₂
    exact card_sylow_two_of_four_mul_odd hm hcard S

end Sec3Final

end CFSG.GH74.GLS.IVK.Proofs2
