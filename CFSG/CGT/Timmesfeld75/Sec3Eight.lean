module

public import CFSG.CGT.Timmesfeld75.Sec3EightMain

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G]

theorem exists_pair_orderOf_four_aux {F : Set G} (hFsq : ∀ x ∈ F, x * x = 1)
    (hFconj : ∀ x ∈ F, ∀ y ∈ F, x * y * x⁻¹ ∈ F) :
    ∀ k : ℕ, 2 ≤ k → ∀ x ∈ F, ∀ y ∈ F, orderOf (x * y) = 2 ^ k →
      ∃ x' ∈ F, ∃ y' ∈ F, orderOf (x' * y') = 4 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro x hx y hy h
    exact ⟨x, hx, y, hy, by rw [h]; norm_num⟩
  | succ k hk2 ih =>
    intro x hx y hy h
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hFsq x hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hFsq y hy)
    have hy₁ : x * y * x⁻¹ ∈ F := hFconj x hx y hy
    have hyx : y * x = (x * y)⁻¹ := by rw [mul_inv_rev, hxi, hyi]
    have hprod : y * (x * y * x⁻¹) = (y * x) ^ 2 := by
      rw [hxi, pow_two]
      group
    have hord : orderOf (y * (x * y * x⁻¹)) = 2 ^ k := by
      rw [hprod, orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), hyx, orderOf_inv, h,
        Nat.gcd_eq_right (dvd_pow_self 2 (Nat.succ_ne_zero k)), pow_succ,
        Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    exact ih y hy _ hy₁ hord

theorem exists_pair_orderOf_four {S : Subgroup G} (hS : IsPGroup 2 S) {F : Set G}
    (hFS : ∀ x ∈ F, x ∈ S) (hFsq : ∀ x ∈ F, x * x = 1)
    (hFconj : ∀ x ∈ F, ∀ y ∈ F, x * y * x⁻¹ ∈ F) {x y : G} (hx : x ∈ F) (hy : y ∈ F)
    (hxy : x * y ≠ y * x) : ∃ x' ∈ F, ∃ y' ∈ F, orderOf (x' * y') = 4 := by
  have hxyS : x * y ∈ S := S.mul_mem (hFS x hx) (hFS y hy)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).1 hS ⟨x * y, hxyS⟩
  have hk' : orderOf (x * y) = 2 ^ k := by
    rw [← Subgroup.orderOf_mk (x * y) hxyS]
    exact hk
  have hk2 : 2 ≤ k := by
    by_contra hlt
    apply hxy
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with h0 | h1
    · rw [h0, pow_zero] at hk'
      have h1 : x * y = 1 := orderOf_eq_one_iff.1 hk'
      rw [h1]
      exact ((mul_eq_one_comm).1 h1).symm
    · rw [h1, pow_one] at hk'
      have h2 : (x * y) ^ 2 = 1 := by
        rw [← hk']
        exact pow_orderOf_eq_one _
      have h3 : x * y * (x * y) = 1 := by rw [← pow_two]; exact h2
      calc x * y = x * (x * y * (x * y)) * y := by rw [h3]; group
        _ = (x * x) * y * x * (y * y) := by group
        _ = y * x := by rw [hFsq x hx, hFsq y hy]; group
  exact exists_pair_orderOf_four_aux hFsq hFconj k hk2 x hx y hy hk'

theorem section3Eight [Finite G] [IsSimpleGroup G] (h214 : Lemma214)
    (hInv : InvolutionClassInput) (hSz : Section3SzInput) (hnab : ∃ a b : G, a * b ≠ b * a)
    {T T₁ : Subgroup G} (hS : Sec3 T T₁) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (T : Set G))
    (hSL : S ≤ Subgroup.normalizer (normIn T T₁ : Set G)) (hL₁S : normIn T₁ T ≤ S) :
    IsElemAbelian 2 (⨆ s : S, conjSubgroup (s : G) (normIn T₁ T)) := by
  set F : Set G := {x | ∃ s ∈ S, x ∈ conjSubgroup s (normIn T₁ T)} with hF
  have hFS : ∀ x ∈ F, x ∈ S := by
    rintro x ⟨s, hs, hx⟩
    obtain ⟨e, he, rfl⟩ := mem_conjSubgroup_iff_exists.1 hx
    exact S.mul_mem (S.mul_mem hs (hL₁S he)) (S.inv_mem hs)
  have hFsq : ∀ x ∈ F, x * x = 1 := by
    rintro x ⟨s, hs, hx⟩
    obtain ⟨e, he, rfl⟩ := mem_conjSubgroup_iff_exists.1 hx
    have hee : e * e = 1 := elemAbelian_mul_self hS.cfg.wc₁.1 (mem_normIn.1 he).1
    calc s * e * s⁻¹ * (s * e * s⁻¹) = s * (e * e) * s⁻¹ := by group
      _ = 1 := by rw [hee]; group
  have hFconjS : ∀ c ∈ S, ∀ y ∈ F, c * y * c⁻¹ ∈ F := by
    rintro c hc y ⟨s, hs, hy⟩
    refine ⟨c * s, S.mul_mem hc hs, ?_⟩
    rw [← conjSubgroup_conjSubgroup]
    exact conj_mem_conjSubgroup c hy
  have hFconj : ∀ x ∈ F, ∀ y ∈ F, x * y * x⁻¹ ∈ F := fun x hx y hy =>
    hFconjS x (hFS x hx) y hy
  have hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
    intro x hx y hy
    by_contra hxy
    obtain ⟨a₀, ha₀, b₀, hb₀, hord⟩ := exists_pair_orderOf_four hS2 hFS hFsq hFconj hx hy hxy
    obtain ⟨s, hs, hbs⟩ := hb₀
    have hb : s⁻¹ * b₀ * s ∈ normIn T₁ T := mem_conjSubgroup.1 hbs
    have ha : s⁻¹ * a₀ * s⁻¹⁻¹ ∈ F := hFconjS s⁻¹ (S.inv_mem hs) a₀ ha₀
    rw [inv_inv] at ha
    have hab : orderOf (s⁻¹ * a₀ * s * (s⁻¹ * b₀ * s)) = 4 := by
      have := MulEquiv.orderOf_eq (MulAut.conj s⁻¹) (a₀ * b₀)
      rw [hord] at this
      rw [← this]
      simp only [MulAut.conj_apply, inv_inv]
      congr 1
      group
    obtain ⟨h, hhS, hah⟩ := ha
    have hbb : s⁻¹ * b₀ * s * (s⁻¹ * b₀ * s) = 1 := by
      have := hFsq _ (hFconjS s⁻¹ (S.inv_mem hs) b₀ ⟨s, hs, hbs⟩)
      rw [inv_inv] at this
      exact this
    have ha1 : s⁻¹ * a₀ * s ≠ 1 := by
      intro ha1
      rw [ha1, one_mul] at hab
      have h2 : orderOf (s⁻¹ * b₀ * s) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hbb)
      rw [hab] at h2
      omega
    obtain ⟨e, he, hae⟩ := mem_conjSubgroup_iff_exists.1 hah
    have he1 : e ≠ 1 := by
      intro he1
      apply ha1
      rw [hae, he1]
      group
    have hL : IsLElt T T₁ (s⁻¹ * a₀ * s) := by
      rw [hae]
      exact (hS.isLElt_of_mem_normIn he he1).conj (hSN hhS) (hSL hhS)
    have hS' : Sec38Hyp T T₁ S (s⁻¹ * a₀ * s) (s⁻¹ * b₀ * s) :=
      ⟨hS, hS2, hL₁S, hFS _ ⟨h, hhS, hah⟩, hL, hb, hab⟩
    exact hS'.false_of_inputs h214 hInv hSz hnab
  refine isElemAbelian_iSup_of_comm (fun s : S => conjSubgroup (s : G) (normIn T₁ T)) ?_ ?_
  · intro s x hx
    have hxF : x ∈ F := ⟨s, s.2, hx⟩
    rw [pow_two]
    exact hFsq x hxF
  · intro s s' x hx y hy
    exact hcomm x ⟨s, s.2, hx⟩ y ⟨s', s'.2, hy⟩

end CFSG.CGT.Timmesfeld75
