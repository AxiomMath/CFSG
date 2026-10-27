module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineE

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

@[expose] def fiveClosure (M : Subgroup X) (s z : X) : Subgroup X :=
  closure {y | y ∈ M ∧ y ∈ centralizer ({s} : Set X) ∧ y ∈ centralizer ({z} : Set X) ∧
    ∃ k : ℕ, orderOf y = 5 ^ k}

theorem fiveClosure_le (M : Subgroup X) (s z : X) :
    fiveClosure M s z ≤ M ⊓ centralizer ({s} : Set X) ⊓ centralizer ({z} : Set X) :=
  closure_le _ |>.mpr fun _ hy => mem_inf.mpr ⟨mem_inf.mpr ⟨hy.1, hy.2.1⟩, hy.2.2.1⟩

theorem mem_normalizer_fiveClosure {M : Subgroup X} {s z c : X} (hcM : c ∈ M)
    (hcs : c ∈ centralizer ({s} : Set X)) (hcz : c ∈ centralizer ({z} : Set X)) :
    c ∈ normalizer (fiveClosure M s z : Set X) := by
  have key : ∀ d : X, d ∈ M → d ∈ centralizer ({s} : Set X) → d ∈ centralizer ({z} : Set X) →
      ∀ y ∈ fiveClosure M s z, d * y * d⁻¹ ∈ fiveClosure M s z := by
    intro d hdM hds hdz y hy
    have h1 : (fiveClosure M s z).map (MulAut.conj d).toMonoidHom ≤ fiveClosure M s z := by
      rw [fiveClosure, MonoidHom.map_closure]
      refine closure_mono ?_
      rintro _ ⟨w, ⟨hwM, hws, hwz, k, hwk⟩, rfl⟩
      refine ⟨mul_mem (mul_mem hdM hwM) (inv_mem hdM),
        mul_mem (mul_mem hds hws) (inv_mem hds), mul_mem (mul_mem hdz hwz) (inv_mem hdz), k, ?_⟩
      show orderOf ((MulAut.conj d).toMonoidHom w) = 5 ^ k
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hwk]
    exact h1 ⟨y, hy, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact key c hcM hcs hcz y
  · intro hy
    have h1 := key c⁻¹ (inv_mem hcM) (inv_mem hcs) (inv_mem hcz) _ hy
    rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at h1

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.mem_image_fiveClosure (hρ : IsPermAction θ ρ) [Finite X] (hr : 4 ≤ r)
    {s z : X} (hsN : s ∈ normalizer (M : Set X)) (hs2 : IsPGroup 2 (zpowers s))
    (hzN : z ∈ normalizer (M : Set X)) (hz2 : z * z = 1) (hsz : s * z = z * s)
    {b : alternatingGroup (Fin r)} (hb5 : b ^ 5 = 1)
    (hbs : (b : Perm (Fin r)) * ρ ⟨s, hsN⟩ = ρ ⟨s, hsN⟩ * b)
    (hbz : (b : Perm (Fin r)) * ρ ⟨z, hzN⟩ = ρ ⟨z, hzN⟩ * b) :
    (b : Perm (Fin r)) ∈ ((fiveClosure M s z).subgroupOf (normalizer (M : Set X))).map ρ := by
  classical
  obtain ⟨x₀, hx₀s, hx₀z, hx₀θ⟩ := hρ.exists_lift_of_two_two hsN hs2 hzN hz2 hsz hbs hbz
  have ho0 : orderOf (x₀ : X) ≠ 0 := (orderOf_pos (x₀ : X)).ne'
  obtain ⟨k, m, hm5, ho⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho0 5 (by norm_num)
  set y : X := (x₀ : X) ^ m with hydef
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ho
    exact ho0 ho
  have hyo : orderOf y = 5 ^ k := by
    rw [hydef, orderOf_pow, ho, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hyM : y ∈ M := pow_mem x₀.2 m
  have hy5 : y ∈ fiveClosure M s z :=
    subset_closure ⟨hyM, pow_mem hx₀s m, pow_mem hx₀z m, k, hyo⟩
  have hρy : ρ ⟨y, le_normalizer hyM⟩ = (b : Perm (Fin r)) ^ m := by
    have h1 := hρ.apply_of_mem hr ⟨y, hyM⟩
    have h2 : ((⟨y, hyM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
        ((x₀ ^ m : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) := by
      congr 1
    rw [h1, h2, QuotientGroup.mk_pow, map_pow, hx₀θ, Subgroup.coe_pow]
  have hbo : orderOf (b : Perm (Fin r)) ∣ 5 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hb5
  have hgcd : m.gcd (orderOf (b : Perm (Fin r))) = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hbo with h | h
    · rw [h, Nat.gcd_one_right]
    · rw [h]
      exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm5))
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (mem_zpowers_pow_iff.mpr hgcd)
  have hmem : ρ ⟨y, le_normalizer hyM⟩ ∈
      ((fiveClosure M s z).subgroupOf (normalizer (M : Set X))).map ρ :=
    ⟨⟨y, le_normalizer hyM⟩, mem_subgroupOf.mpr hy5, rfl⟩
  rw [← hj, ← hρy]
  exact zpow_mem hmem j

theorem IsPermAction.fixAlt_le_image_fiveClosure (hρ : IsPermAction θ ρ) [Finite X] (hr : 5 ≤ r)
    {s z : X} (hsN : s ∈ normalizer (M : Set X)) (hs2 : IsPGroup 2 (zpowers s))
    (hzN : z ∈ normalizer (M : Set X)) (hz2 : z * z = 1) (hsz : s * z = z * s)
    (hzK : z ∈ UnbalancedLayer.coreActionKernel M)
    (h5 : 5 ≤ r - (ρ ⟨s, hsN⟩).support.card) :
    ∀ c ∈ fixAlt (ρ ⟨s, hsN⟩), (c : Perm (Fin r)) ∈
      ((fiveClosure M s z).subgroupOf (normalizer (M : Set X))).map ρ := by
  classical
  set σ := ρ ⟨s, hsN⟩ with hσdef
  set R := ((fiveClosure M s z).subgroupOf (normalizer (M : Set X))).map ρ with hRdef
  have hρz : ρ ⟨z, hzN⟩ = 1 := hρ.eq_one_of_mem_coreActionKernel (by omega) hzK
  have hcom : ∀ c ∈ fixAlt σ, (c : Perm (Fin r)) * σ = σ * c := by
    intro c hc
    have hd : Perm.Disjoint (c : Perm (Fin r)) σ := by
      rw [Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
      intro x hx hxσ
      exact (Finset.mem_compl.mp ((mem_fixAlt.mp hc) hx)) hxσ
    exact hd.commute.eq
  have hcomz : ∀ c : alternatingGroup (Fin r), (c : Perm (Fin r)) * ρ ⟨z, hzN⟩ =
      ρ ⟨z, hzN⟩ * c := fun c => by rw [hρz, mul_one, one_mul]
  set R' : Subgroup ↥(fixAlt σ) :=
    R.comap ((alternatingGroup (Fin r)).subtype.comp (fixAlt σ).subtype) with hR'def
  have hR'n : R'.Normal := by
    refine ⟨fun x hx c => ?_⟩
    obtain ⟨yc, hycs, hycz, hycθ⟩ := hρ.exists_lift_of_two_two hsN hs2 hzN hz2 hsz
      (hcom c c.2) (hcomz c)
    have hycN := mem_normalizer_fiveClosure (s := s) (z := z) yc.2 hycs hycz
    obtain ⟨w, hw, hwx⟩ := hx
    have hw5 : (w : X) ∈ fiveClosure M s z := mem_subgroupOf.mp hw
    have h1 : (yc : X) * w * (yc : X)⁻¹ ∈ fiveClosure M s z :=
      (mem_normalizer_iff.mp hycN w).mp hw5
    have hycρ : ρ ⟨yc, le_normalizer yc.2⟩ = ((c : alternatingGroup (Fin r)) : Perm (Fin r)) := by
      rw [hρ.apply_of_mem (by omega) yc, hycθ]
    refine ⟨⟨yc, le_normalizer yc.2⟩ * w * ⟨yc, le_normalizer yc.2⟩⁻¹, mem_subgroupOf.mpr h1, ?_⟩
    rw [map_mul, map_mul, map_inv, hwx, hycρ]
    rfl
  have hcard : 5 ∣ Nat.card (fixAlt σ) := by
    rw [card_fixAlt (by omega)]
    have h1 : 5 ∣ (r - σ.support.card).factorial := Nat.dvd_factorial (by norm_num) h5
    have h2 : 2 ∣ (r - σ.support.card).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    obtain ⟨q, hq⟩ := h1
    omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' 5 hcard
  have hb₀5 : ((b₀ : alternatingGroup (Fin r))) ^ 5 = 1 := by
    rw [← Subgroup.orderOf_coe] at hb₀
    rw [← hb₀]
    exact pow_orderOf_eq_one _
  have hb₀R : b₀ ∈ R' :=
    hρ.mem_image_fiveClosure (by omega) hsN hs2 hzN hz2 hsz hb₀5 (hcom b₀ b₀.2) (hcomz b₀)
  have hR'top : R' = ⊤ := by
    have : IsSimpleGroup ↥(fixAlt σ) := isSimpleGroup_fixAlt h5
    rcases hR'n.eq_bot_or_eq_top with h | h
    · exfalso
      rw [h, mem_bot] at hb₀R
      rw [hb₀R, orderOf_one] at hb₀
      exact absurd hb₀ (by norm_num)
    · exact h
  intro c hc
  have h1 : (⟨c, hc⟩ : ↥(fixAlt σ)) ∈ R' := by rw [hR'top]; exact mem_top _
  exact h1

end CFSG.ComponentClassification.SolMax
