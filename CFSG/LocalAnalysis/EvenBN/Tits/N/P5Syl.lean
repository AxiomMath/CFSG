module

public import CFSG.Open.FusionDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_fixed_coset_of_two_dvd_relIndex {C W : Subgroup Γ} {t : Γ} (ht2 : t * t = 1)
    (htW : ∀ x ∈ W, t * x * t⁻¹ ∈ W) (htC : ∀ x ∈ C, t * x * t⁻¹ ∈ C) (h2 : 2 ∣ W.relIndex C) :
    ∃ g ∈ C, g ∉ W ∧ (t * g * t⁻¹)⁻¹ * g ∈ W := by
  let f : C → C := fun g => ⟨t * g * t⁻¹, htC g g.2⟩
  have hf : ∀ g : C, (f g : Γ) = t * g * t⁻¹ := fun g => rfl
  let F : C ⧸ W.subgroupOf C → C ⧸ W.subgroupOf C := Quotient.map' f (fun a b hab => by
    rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hab ⊢
    convert htW _ hab using 1
    rw [coe_mul, coe_inv, hf, hf, coe_mul, coe_inv]
    group)
  have hFmk : ∀ g : C, F (g : C ⧸ W.subgroupOf C) = (f g : C ⧸ W.subgroupOf C) := fun g => rfl
  have hF : Function.Involutive F := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hFmk, hFmk]
    congr 1
    ext
    rw [hf, hf]
    calc t * (t * (g : Γ) * t⁻¹) * t⁻¹ = (t * t) * g * (t * t)⁻¹ := by group
      _ = g := by rw [ht2]; group
  haveI : Fintype (C ⧸ W.subgroupOf C) := Fintype.ofFinite _
  have h2' : 2 ∣ Fintype.card (C ⧸ W.subgroupOf C) := by
    rw [Fintype.card_eq_nat_card]; exact h2
  have hσ : (hF.toPerm F) ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    exact Equiv.ext fun x => hF x
  have h1 : (hF.toPerm F) ((1 : C) : C ⧸ W.subgroupOf C) = ((1 : C) : C ⧸ W.subgroupOf C) := by
    rw [Function.Involutive.coe_toPerm, hFmk]
    congr 1
    ext
    rw [hf]
    simp
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' h2' hσ h1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
  rw [Function.Involutive.coe_toPerm, hFmk, QuotientGroup.eq, mem_subgroupOf] at hb
  refine ⟨g, g.2, fun hg => hb1 ?_, ?_⟩
  · rw [QuotientGroup.eq, mem_subgroupOf]
    simpa using hg
  · simpa [hf] using hb

theorem fusionIsSylowIn_centralizer_of_trans {Hs W : Subgroup Γ} {t : Γ}
    (hWHs : W ≤ Hs) (hWab : IsElemAbelian 2 W) (htHs : t ∈ Hs) (ht2 : t * t = 1)
    (htn : t ∈ normalizer (W : Set Γ))
    (hcent : ∀ c ∈ Hs, c ∈ centralizer (W : Set Γ) → c * t = t * c → c ∈ W)
    (htrans : ∀ q ∈ Hs, q ∈ centralizer (W : Set Γ) → (∃ w ∈ W, q * t * q⁻¹ = w * t) →
      ∃ w ∈ W, w * t * w⁻¹ = q * t * q⁻¹) :
    fusionIsSylowIn 2 W (centralizer (W : Set Γ) ⊓ Hs) := by
  have hWC : W ≤ centralizer (W : Set Γ) := le_centralizer_iff_isMulCommutative.mpr hWab.1
  have hWp : IsPGroup 2 W := fun g => ⟨1, Subtype.ext (by simpa using hWab.2 g g.2)⟩
  refine ⟨le_inf hWC hWHs, hWp, fun P hPC hP hWP => ?_⟩
  by_contra hne
  have htW : ∀ x ∈ W, t * x * t⁻¹ ∈ W := fun x hx => (mem_set_normalizer_iff.mp htn x).mp hx
  have htC : ∀ x ∈ centralizer (W : Set Γ) ⊓ Hs, t * x * t⁻¹ ∈ centralizer (W : Set Γ) ⊓ Hs := by
    intro x hx
    rw [mem_inf] at hx ⊢
    refine ⟨?_, mul_mem (mul_mem htHs hx.2) (inv_mem htHs)⟩
    rw [mem_centralizer_iff]
    intro h hh
    have h' : t⁻¹ * h * t ∈ W := (mem_set_normalizer_iff''.mp htn h).mp hh
    have hc := mem_centralizer_iff.mp hx.1 _ h'
    calc h * (t * x * t⁻¹) = t * ((t⁻¹ * h * t) * x) * t⁻¹ := by group
      _ = t * (x * (t⁻¹ * h * t)) * t⁻¹ := by rw [hc]
      _ = t * x * t⁻¹ * h := by group
  have h2 : 2 ∣ W.relIndex (centralizer (W : Set Γ) ⊓ Hs) := by
    obtain ⟨n, hn⟩ := hP.index (W.subgroupOf P)
    have hn' : W.relIndex P = 2 ^ n := hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (le_antisymm (relIndex_eq_one.mp (by rw [hn', pow_zero])) hWP)
    calc 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
      _ = W.relIndex P := hn'.symm
      _ ∣ _ := Dvd.intro _ (relIndex_mul_relIndex _ _ _ hWP hPC)
  obtain ⟨g, hgC, hgW, hg⟩ := exists_fixed_coset_of_two_dvd_relIndex ht2 htW htC h2
  rw [mem_inf] at hgC
  have hq : g⁻¹ * t * g⁻¹⁻¹ * t⁻¹ ∈ W := by
    convert inv_mem hg using 1
    group
  obtain ⟨w, hwW, hwt⟩ := htrans g⁻¹ (inv_mem hgC.2) (inv_mem hgC.1) ⟨_, hq, by group⟩
  have hc : w⁻¹ * g⁻¹ ∈ W := by
    refine hcent _ (mul_mem (inv_mem (hWHs hwW)) (inv_mem hgC.2))
      (mul_mem (inv_mem (hWC hwW)) (inv_mem hgC.1)) ?_
    calc w⁻¹ * g⁻¹ * t = w⁻¹ * (g⁻¹ * t * g⁻¹⁻¹) * g⁻¹ := by group
      _ = w⁻¹ * (w * t * w⁻¹) * g⁻¹ := by rw [hwt]
      _ = t * (w⁻¹ * g⁻¹) := by group
  apply hgW
  simpa using inv_mem (mul_mem hwW hc)

theorem exists_mul_centralizer_of_commutator_mem {Hs W : Subgroup Γ} {t k : Γ}
    (hWab : IsElemAbelian 2 W) (ht2 : t * t = 1)
    (hsyl : fusionIsSylowIn 2 W (centralizer (W : Set Γ) ⊓ Hs))
    (hcomm : ∀ u ∈ W, t * u * t⁻¹ = u → ∃ w ∈ W, u = w * (t * w * t⁻¹))
    (hk : k * t * k⁻¹ * t⁻¹ ∈ centralizer (W : Set Γ) ⊓ Hs) :
    ∃ m ∈ centralizer (W : Set Γ) ⊓ Hs, (m⁻¹ * k) * t = t * (m⁻¹ * k) := by
  obtain ⟨c, hc⟩ : ∃ c, c = k * t * k⁻¹ * t⁻¹ := ⟨_, rfl⟩
  rw [← hc] at hk
  have hct : c * t = k * t * k⁻¹ := by rw [hc]; group
  have h1 : c * t * (c * t) = 1 := by
    rw [hct]
    calc k * t * k⁻¹ * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hinv : t * c * t⁻¹ = c⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right ht2]
    calc t * c * t = c⁻¹ * (c * t * (c * t)) := by group
      _ = c⁻¹ := by rw [h1, mul_one]
  have hpow : ∀ j : ℤ, t * c ^ j * t⁻¹ = (c ^ j)⁻¹ := fun j => by
    rw [← conj_zpow, hinv, inv_zpow]
  obtain ⟨a, o, ho, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ a) o
  rw [(Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr ho)).gcd_eq_one, Nat.cast_one] at hbez
  have hord : ∀ j : ℤ, c ^ (((2 ^ a * o : ℕ) : ℤ) * j) = 1 := fun j =>
    orderOf_dvd_iff_zpow_eq_one.mp (by rw [hn]; exact Dvd.intro _ rfl)
  obtain ⟨e₂, he₂⟩ : ∃ e : ℤ, e = (o : ℤ) * Nat.gcdB (2 ^ a) o := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ : ∃ e : ℤ, e = ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) o := ⟨_, rfl⟩
  have hdecomp : c = c ^ e' * c ^ e₂ := by
    rw [← zpow_add, he', he₂, ← hbez, zpow_one]
  have hc₂2 : (c ^ e₂) ^ (2 ^ a) = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    have : e₂ * ((2 ^ a : ℕ) : ℤ) = ((2 ^ a * o : ℕ) : ℤ) * Nat.gcdB (2 ^ a) o := by
      rw [he₂]; push_cast; ring
    rw [this, hord]
  have hc₂C : c ^ e₂ ∈ centralizer (W : Set Γ) ⊓ Hs := zpow_mem hk _
  have hzp : IsPGroup 2 (zpowers (c ^ e₂)) := IsPGroup.of_card_dvd_pow (n := a)
    (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hc₂2)
  have hle : zpowers (c ^ e₂) ≤ normalizer (W : Set Γ) :=
    zpowers_le.mpr (centralizer_le_normalizer _ (mem_inf.mp hc₂C).1)
  have heq := hsyl.2.2 _ (sup_le (zpowers_le.mpr hc₂C) hsyl.1)
    (IsPGroup.to_sup_of_normal_right' hzp hsyl.2.1 hle) le_sup_right
  have hc₂W : c ^ e₂ ∈ W := by
    rw [← heq]
    exact mem_sup_left (mem_zpowers _)
  have hc₂inv : (c ^ e₂)⁻¹ = c ^ e₂ :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hWab.2 _ hc₂W)
  obtain ⟨w₁, hw₁W, hw₁⟩ := hcomm _ hc₂W (by rw [hpow, hc₂inv])
  have hw₁inv : w₁⁻¹ = w₁ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hWab.2 _ hw₁W)
  obtain ⟨r, hr⟩ := ho
  have hp₁ : c ^ (e' * (r + 1)) * c ^ (e' * (r + 1)) = c ^ e' := by
    rw [← zpow_add]
    have : e' * (r + 1) + e' * (r + 1) = ((2 ^ a * o : ℕ) : ℤ) * Nat.gcdA (2 ^ a) o + e' := by
      rw [he', hr]; push_cast; ring
    rw [this, zpow_add, hord, one_mul]
  have hp₁t : c ^ (e' * (r + 1)) * t * (c ^ (e' * (r + 1)))⁻¹ = c ^ e' * t := by
    calc c ^ (e' * (r + 1)) * t * (c ^ (e' * (r + 1)))⁻¹
        = c ^ (e' * (r + 1)) * (t * c ^ (e' * (r + 1)) * t⁻¹)⁻¹ * t := by group
      _ = c ^ (e' * (r + 1)) * (c ^ (e' * (r + 1)))⁻¹⁻¹ * t := by rw [hpow]
      _ = c ^ e' * t := by rw [inv_inv, hp₁]
  have hw₁c' : w₁ * c ^ e' = c ^ e' * w₁ :=
    mem_centralizer_iff.mp (mem_inf.mp (zpow_mem hk e')).1 w₁ hw₁W
  refine ⟨w₁ * c ^ (e' * (r + 1)), mul_mem (hsyl.1 hw₁W) (zpow_mem hk _), ?_⟩
  have key : w₁ * c ^ (e' * (r + 1)) * t * (w₁ * c ^ (e' * (r + 1)))⁻¹ = k * t * k⁻¹ := by
    calc w₁ * c ^ (e' * (r + 1)) * t * (w₁ * c ^ (e' * (r + 1)))⁻¹
        = w₁ * (c ^ (e' * (r + 1)) * t * (c ^ (e' * (r + 1)))⁻¹) * w₁⁻¹ := by group
      _ = (w₁ * c ^ e') * t * w₁⁻¹ := by rw [hp₁t]; group
      _ = (c ^ e' * w₁) * t * w₁⁻¹ := by rw [hw₁c']
      _ = c ^ e' * (w₁ * (t * w₁⁻¹ * t⁻¹)) * t := by group
      _ = c ^ e' * c ^ e₂ * t := by rw [hw₁inv, ← hw₁]
      _ = k * t * k⁻¹ := by rw [← hdecomp, hct]
  generalize w₁ * c ^ (e' * (r + 1)) = m at key ⊢
  calc m⁻¹ * k * t = m⁻¹ * (k * t * k⁻¹) * k := by group
    _ = m⁻¹ * (m * t * m⁻¹) * k := by rw [key]
    _ = t * (m⁻¹ * k) := by group

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
