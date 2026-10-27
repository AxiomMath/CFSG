module

public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.Basic
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55.I336

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem not_dvd_card_of_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T N : Subgroup G}
    (hT : IsPGroup 2 T) (h : N ≤ T) : ¬ p ∣ Nat.card N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (hT.to_le h).exists_card_eq
  rw [hk]
  intro hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))

theorem commute_of_fixed_coset {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A T T₀ Z : Subgroup G}
    {t : G} (hA : IsPGroup p A) (hT : IsPGroup 2 T) (hT₀T : T₀ ≤ T)
    (hAT₀ : A ≤ Subgroup.normalizer (T₀ : Set G)) (htT : t ∈ T)
    (hAt : ∀ a ∈ A, a * t * a⁻¹ = t)
    (hZc : ∀ c ∈ Z, ∀ g ∈ T, g * c = c * g) (hZA : ∀ c ∈ Z, ∀ a ∈ A, a * c * a⁻¹ = c)
    (hcl : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ Z)
    (hfix : ∀ x ∈ T₀, x ∈ Subgroup.centralizer (A : Set G) → x * t = t * x) :
    ∀ x ∈ T₀, x * t = t * x := by
  set N : Subgroup G := T₀ ⊓ Subgroup.centralizer ({t} : Set G) with hN
  have hAt' : ∀ a ∈ A, a⁻¹ * t = t * a⁻¹ := by
    intro a ha
    have h := hAt a⁻¹ (A.inv_mem ha)
    rw [inv_inv] at h
    calc a⁻¹ * t = (a⁻¹ * t * a) * a⁻¹ := by group
      _ = t * a⁻¹ := by rw [h]
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := by
    refine le_normalizer_of_forall_mem fun a ha n hn => ?_
    obtain ⟨hnT₀, hnc⟩ := hn
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hAT₀ ha) n).mp hnT₀, ?_⟩
    have hnc := Subgroup.mem_centralizer_singleton_iff.mp hnc
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 : a * t = t * a := by
      have := hAt a ha
      calc a * t = a * t * a⁻¹ * a := by group
        _ = t * a := by rw [this]
    symm
    calc t * (a * n * a⁻¹) = (t * a) * n * a⁻¹ := by group
      _ = (a * t) * n * a⁻¹ := by rw [h1]
      _ = a * (t * n) * a⁻¹ := by group
      _ = a * (n * t) * a⁻¹ := by rw [hnc]
      _ = a * n * (t * a⁻¹) := by group
      _ = a * n * (a⁻¹ * t) := by rw [hAt' a ha]
      _ = a * n * a⁻¹ * t := by group
  have hNp : ¬ p ∣ Nat.card N := not_dvd_card_of_le hp hp2 hT (inf_le_left.trans hT₀T)
  intro x hx
  have hxT : x ∈ T := hT₀T hx
  have hconj : ∀ a ∈ A, a * x * a⁻¹ ∈ T₀ := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hAT₀ ha) x).mp hx
  have hcomm_aux : ∀ y ∈ T, ∀ c ∈ Z, y⁻¹ * c = c * y⁻¹ := by
    intro y hy c hc
    exact hZc c hc y⁻¹ (T.inv_mem hy)
  have hy : ∀ a ∈ A, x⁻¹ * (a * x * a⁻¹) ∈ N := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨T₀.mul_mem (T₀.inv_mem hx) (hconj a ha), ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    set x' := a * x * a⁻¹ with hx'
    have hx'T : x' ∈ T := hT₀T (hconj a ha)
    set c₁ := ⁅x, t⁆ with hc₁
    have hc₁Z : c₁ ∈ Z := hcl x hxT t htT
    have hc₂ : ⁅x', t⁆ = c₁ := by
      calc ⁅x', t⁆ = x' * t * x'⁻¹ * t⁻¹ := rfl
        _ = (a * x * a⁻¹) * (a * t * a⁻¹) * (a * x * a⁻¹)⁻¹ * (a * t * a⁻¹)⁻¹ := by
            rw [hAt a ha]
        _ = a * (x * t * x⁻¹ * t⁻¹) * a⁻¹ := by group
        _ = c₁ := hZA c₁ hc₁Z a ha
    have e1 : x * t = c₁ * (t * x) := by
      rw [hc₁]; simp only [commutatorElement_def]; group
    have e2 : x' * t = c₁ * (t * x') := by
      rw [← hc₂]; simp only [commutatorElement_def]; group
    have hcx : c₁ * x⁻¹ = x⁻¹ * c₁ := (hcomm_aux x hxT c₁ hc₁Z).symm
    have e3 : t * x⁻¹ = c₁ * (x⁻¹ * t) := by
      calc t * x⁻¹ = x⁻¹ * (x * t) * x⁻¹ := by group
        _ = x⁻¹ * (c₁ * (t * x)) * x⁻¹ := by rw [e1]
        _ = (x⁻¹ * c₁) * t := by group
        _ = (c₁ * x⁻¹) * t := by rw [hcx]
        _ = c₁ * (x⁻¹ * t) := by group
    symm
    calc t * (x⁻¹ * x') = (t * x⁻¹) * x' := by group
      _ = c₁ * (x⁻¹ * t) * x' := by rw [e3]
      _ = (c₁ * x⁻¹) * t * x' := by group
      _ = (x⁻¹ * c₁) * t * x' := by rw [hcx]
      _ = x⁻¹ * (c₁ * (t * x')) := by group
      _ = x⁻¹ * (x' * t) := by rw [← e2]
      _ = x⁻¹ * x' * t := by group
  obtain ⟨n, hnN, hn⟩ := exists_fixed_mem_coset hp hA hAN hNp hy
  have hxnT₀ : x * n ∈ T₀ := T₀.mul_mem hx hnN.1
  have h1 : (x * n) * t = t * (x * n) := hfix _ hxnT₀ hn
  have h2 : n * t = t * n := Subgroup.mem_centralizer_singleton_iff.mp hnN.2
  have hc1 : Commute (x * n) t := h1
  have hc2 : Commute n t := h2
  have := hc1.mul_left hc2.inv_left
  have e : x * n * n⁻¹ = x := by group
  rw [e] at this
  exact this

theorem comm_of_mem_zpowers {y g a : G} (h : y * g = g * y) (ha : a ∈ Subgroup.zpowers y) :
    a * g = g * a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact (Commute.zpow_left (show Commute y g from h) k).eq

theorem card_sup_zpowers {A : Subgroup G} {y : G} (hy : orderOf y = 2)
    (hyc : ∀ a ∈ A, a * y = y * a) (hyA : y ∉ A) :
    Nat.card ↥(A ⊔ Subgroup.zpowers y) = 2 * Nat.card A := by
  have hB : Subgroup.zpowers y ≤ Subgroup.normalizer (A : Set G) := by
    refine le_normalizer_of_forall_mem fun g hg a ha => ?_
    have h1 : g * a = a * g := comm_of_mem_zpowers (hyc a ha).symm hg
    rw [h1, mul_inv_cancel_right]
    exact ha
  have hcardB : Nat.card (Subgroup.zpowers y) = 2 := by rw [Nat.card_zpowers, hy]
  have hdvd : Nat.card ↥(A ⊓ Subgroup.zpowers y) ∣ 2 :=
    hcardB ▸ Subgroup.card_dvd_of_le inf_le_right
  have hne2 : Nat.card ↥(A ⊓ Subgroup.zpowers y) ≠ 2 := by
    intro h2
    have h3 : A ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcardB, h2])
    apply hyA
    have : y ∈ A ⊓ Subgroup.zpowers y := by rw [h3]; exact Subgroup.mem_zpowers y
    exact this.1
  have hinf : Nat.card ↥(A ⊓ Subgroup.zpowers y) = 1 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_right hne2
  have h := card_sup_mul_card_inf_of_le_normalizer hB
  rw [hinf, hcardB, mul_one] at h
  rw [h, mul_comm]

theorem elemAbelian_eight_aux {u v z a b : G} (hz : orderOf z = 2) (hu2 : u ^ 2 = 1)
    (hv2 : v ^ 2 = 1) (hzu : z * u = u * z) (hzv : z * v = v * z) (huv : u * v = v * u)
    (hza : z * a = a * z) (hau : a * u = z * (u * a)) (hzb : z * b = b * z)
    (hub : u * b = b * u) (hbv : b * v = z * (v * b)) :
    IsElemAbelian 2 (Subgroup.zpowers z ⊔ Subgroup.zpowers u ⊔ Subgroup.zpowers v) ∧
      Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers u ⊔ Subgroup.zpowers v) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hcancel : ∀ w : G, z * w = w → False := by
    intro w h
    apply hz1
    have : z * w = 1 * w := by rw [h, one_mul]
    exact mul_right_cancel this
  have hun : u ∉ Subgroup.zpowers z := by
    intro hmem
    have h1 : u * a = a * u := comm_of_mem_zpowers (y := z) (g := a) hza hmem
    rw [h1] at hau
    exact hcancel _ hau.symm
  have hu1 : u ≠ 1 := fun h => hun (h ▸ Subgroup.one_mem _)
  have huord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have hW₂ : Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers u) = 4 := by
    rw [card_sup_zpowers huord (fun x hx => comm_of_mem_zpowers hzu hx) hun, Nat.card_zpowers, hz]
  have hW₂c : ∀ x ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers u, x * b = b * x := by
    have : Subgroup.zpowers z ⊔ Subgroup.zpowers u ≤ Subgroup.centralizer ({b} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hzb))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hub))
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hx)
  have hvn : v ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers u := by
    intro hmem
    have h1 := hW₂c v hmem
    rw [h1] at hbv
    exact hcancel _ hbv.symm
  have hv1 : v ≠ 1 := fun h => hvn (h ▸ Subgroup.one_mem _)
  have hvord : orderOf v = 2 := orderOf_eq_prime hv2 hv1
  have hW₂v : ∀ x ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers u, x * v = v * x := by
    have : Subgroup.zpowers z ⊔ Subgroup.zpowers u ≤ Subgroup.centralizer ({v} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hzv))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr huv))
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hx)
  refine ⟨?_, ?_⟩
  · refine IsElemAbelian.sup_of_commute (IsElemAbelian.sup_of_commute
      (isElemAbelian_zpowers hz2) (isElemAbelian_zpowers hu2) ?_) (isElemAbelian_zpowers hv2) ?_
    · intro x hx y hy
      exact comm_of_mem_zpowers (y := z) (g := y) (a := x)
        (comm_of_mem_zpowers (y := u) (g := z) (a := y) hzu.symm hy).symm hx
    · intro x hx y hy
      exact comm_of_mem_zpowers (y := v) (g := x) (a := y) (hW₂v x hx).symm hy |>.symm
  · rw [card_sup_zpowers hvord hW₂v hvn, hW₂]

theorem elemAbelian_eight {i₀ j₀ i₁ j₁ z : G} (hz : orderOf z = 2)
    (hi₀ : i₀ ^ 2 = z) (hj₀ : j₀ ^ 2 = z) (hij₀ : i₀ * j₀ = z * (j₀ * i₀))
    (hi₁ : i₁ ^ 2 = z) (hj₁ : j₁ ^ 2 = z) (hij₁ : i₁ * j₁ = z * (j₁ * i₁))
    (hzi₀ : z * i₀ = i₀ * z) (hzj₀ : z * j₀ = j₀ * z) (hzi₁ : z * i₁ = i₁ * z)
    (hzj₁ : z * j₁ = j₁ * z)
    (hii : i₀ * i₁ = i₁ * i₀) (hij : i₀ * j₁ = j₁ * i₀) (hji : j₀ * i₁ = i₁ * j₀)
    (hjj : j₀ * j₁ = j₁ * j₀) :
    IsElemAbelian 2 (Subgroup.zpowers z ⊔ Subgroup.zpowers (i₀ * i₁) ⊔
        Subgroup.zpowers (j₀ * j₁)) ∧
      Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers (i₀ * i₁) ⊔
        Subgroup.zpowers (j₀ * j₁)) = 8 := by
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hji₀ : j₀ * i₀ = z * (i₀ * j₀) := by
    rw [hij₀, ← mul_assoc, hzz, one_mul]
  refine elemAbelian_eight_aux (a := j₀) (b := i₀) hz ?_ ?_ ?_ ?_ ?_ hzj₀ ?_ hzi₀ ?_ ?_
  · calc (i₀ * i₁) ^ 2 = i₀ * (i₁ * i₀) * i₁ := by rw [pow_two]; group
      _ = i₀ * (i₀ * i₁) * i₁ := by rw [hii]
      _ = i₀ ^ 2 * i₁ ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hi₀, hi₁, hzz]
  · calc (j₀ * j₁) ^ 2 = j₀ * (j₁ * j₀) * j₁ := by rw [pow_two]; group
      _ = j₀ * (j₀ * j₁) * j₁ := by rw [hjj]
      _ = j₀ ^ 2 * j₁ ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hj₀, hj₁, hzz]
  · calc z * (i₀ * i₁) = (z * i₀) * i₁ := by group
      _ = i₀ * z * i₁ := by rw [hzi₀]
      _ = i₀ * (z * i₁) := by group
      _ = i₀ * (i₁ * z) := by rw [hzi₁]
      _ = i₀ * i₁ * z := by group
  · calc z * (j₀ * j₁) = (z * j₀) * j₁ := by group
      _ = j₀ * z * j₁ := by rw [hzj₀]
      _ = j₀ * (z * j₁) := by group
      _ = j₀ * (j₁ * z) := by rw [hzj₁]
      _ = j₀ * j₁ * z := by group
  ·
    have hzc : (j₀ * i₀) * z = z * (j₀ * i₀) := by
      calc (j₀ * i₀) * z = j₀ * (i₀ * z) := by group
        _ = j₀ * (z * i₀) := by rw [hzi₀]
        _ = (j₀ * z) * i₀ := by group
        _ = (z * j₀) * i₀ := by rw [hzj₀]
        _ = z * (j₀ * i₀) := by group
    calc i₀ * i₁ * (j₀ * j₁) = i₀ * (i₁ * j₀) * j₁ := by group
      _ = i₀ * (j₀ * i₁) * j₁ := by rw [hji]
      _ = (i₀ * j₀) * (i₁ * j₁) := by group
      _ = (z * (j₀ * i₀)) * (z * (j₁ * i₁)) := by rw [hij₀, hij₁]
      _ = z * (((j₀ * i₀) * z) * (j₁ * i₁)) := by group
      _ = z * ((z * (j₀ * i₀)) * (j₁ * i₁)) := by rw [hzc]
      _ = (z * z) * (j₀ * (i₀ * j₁) * i₁) := by group
      _ = j₀ * (j₁ * i₀) * i₁ := by rw [hzz, one_mul, hij]
      _ = j₀ * j₁ * (i₀ * i₁) := by group
  ·
    calc j₀ * (i₀ * i₁) = (j₀ * i₀) * i₁ := by group
      _ = (z * (i₀ * j₀)) * i₁ := by rw [hji₀]
      _ = z * (i₀ * (j₀ * i₁)) := by group
      _ = z * (i₀ * (i₁ * j₀)) := by rw [hji]
      _ = z * (i₀ * i₁ * j₀) := by group
  ·
    calc i₀ * i₁ * i₀ = i₀ * (i₁ * i₀) := by group
      _ = i₀ * (i₀ * i₁) := by rw [hii]
  ·
    calc i₀ * (j₀ * j₁) = (i₀ * j₀) * j₁ := by group
      _ = (z * (j₀ * i₀)) * j₁ := by rw [hij₀]
      _ = z * (j₀ * (i₀ * j₁)) := by group
      _ = z * (j₀ * (j₁ * i₀)) := by rw [hij]
      _ = z * (j₀ * j₁ * i₀) := by group

end CFSG.LocalAnalysis.GLTheoremA.P55.I336
