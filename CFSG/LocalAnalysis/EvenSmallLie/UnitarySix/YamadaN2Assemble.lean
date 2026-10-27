module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2SL3

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped commutatorElement

variable {Γ : Type*} [Group Γ] {M : Type*} [Group M]

theorem two_mem_of_mul {X K : Subgroup Γ} (hKc : K ≤ Subgroup.center Γ)
    (hKo : Odd (Nat.card K)) {x m k : Γ} (hm : m ∈ X) (hk : k ∈ K) (hx : x = m * k)
    (hx2 : x * x = 1) : x ∈ X := by
  have hkc : ∀ g : Γ, g * k = k * g := fun g => (Subgroup.mem_center_iff.mp (hKc hk) g)
  have e : m * m * (k * k) = 1 := by
    rw [← hx2, hx, show m * k * (m * k) = m * (k * m) * k by group, ← hkc m]
    group
  have hkk : k * k ∈ X := by
    rw [eq_inv_of_mul_eq_one_right e]; exact inv_mem (mul_mem hm hm)
  have hodd : Odd (orderOf k) := Odd.of_dvd_nat hKo (Subgroup.orderOf_dvd_natCard K hk)
  obtain ⟨r, hr⟩ := hodd
  have hkr : k = (k * k) ^ (r + 1) := by
    have h1 : k ^ (2 * r + 1) = 1 := by rw [← hr]; exact pow_orderOf_eq_one k
    calc k = k * k ^ (2 * r + 1) := by rw [h1, mul_one]
      _ = (k * k) ^ (r + 1) := by rw [← sq, ← pow_mul, ← pow_succ']; ring_nf
  rw [hx]
  exact mul_mem hm (hkr ▸ Subgroup.pow_mem _ hkk _)

theorem mem_sup_of_commute {X Y : Subgroup Γ} (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {g : Γ}
    (hg : g ∈ X ⊔ Y) : ∃ a ∈ X, ∃ b ∈ Y, g = a * b := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, one_mem _, by rw [mul_one]⟩
    · exact ⟨1, one_mem _, x, hx, by rw [one_mul]⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, by rw [mul_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
    rw [mul_assoc a, ← mul_assoc b, ← hXY a' ha' b hb]
    group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
    rw [_root_.mul_inv_rev]
    have := hXY a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
    exact this.symm

theorem omegaI_pow_three : omegaI ^ 3 = 1 := Subtype.ext (by
  rw [coe_omegaI_pow, coe_SL3_one]
  ext i j
  by_cases h : i = j
  · subst h; rw [diagonal_apply_eq, one_apply_eq]; exact f4_ext rfl
  · rw [diagonal_apply_ne _ h, one_apply_ne h])

theorem isTwoElt_map_st3 (φ : SL3 →* Γ) (a b : Fin 3) (c : F4) : IsTwoElt (φ (st3 a b c)) :=
  isTwoElt_of_sq (by rw [← map_mul, st3, stT_mul_self, map_one])

section Assemble

variable (τ : Γ →* Γ) (f : Γ →* M) (T : M) (ψ θ : SL3 →* Γ)
  (hττ : ∀ g, τ (τ g) = g) (hKc : f.ker ≤ Subgroup.center Γ) (hKo : Odd (Nat.card f.ker))
  (hKfix : ∀ g ∈ f.ker, τ g = g → g = 1) (hfτ : ∀ γ, f (τ γ) = T * f γ * T⁻¹)
  (hcomm : ∀ a b, f (ψ a) * (T * f (ψ b) * T⁻¹) = (T * f (ψ b) * T⁻¹) * f (ψ a))
  (hsc : ∀ a b, f (ψ a) = T * f (ψ b) * T⁻¹ → a ∈ Subgroup.zpowers omegaI)
  (hθ : ∀ g, f (θ g) = f (ψ g) * (T * f (ψ g) * T⁻¹)) (hτθ : ∀ g, τ (θ g) = θ g)

include hKc hKo hfτ hcomm in
theorem commute_ψ (a b : SL3) : Commute (ψ a) (τ (ψ b)) := by
  have hst : ∀ (i j : Fin 3) (c : F4) (k l : Fin 3) (c' : F4),
      Commute (ψ (st3 i j c)) (τ (ψ (st3 k l c'))) := by
    intro i j c k l c'
    refine commute_of_isTwoElt hKc hKo (isTwoElt_map_st3 ψ i j c) ?_ ?_
    · obtain ⟨n, hn⟩ := isTwoElt_map_st3 ψ k l c'
      exact ⟨n, by rw [← map_pow, hn, map_one]⟩
    · rw [MonoidHom.mem_ker, map_commutatorElement, hfτ, commutatorElement_eq_one_iff_commute]
      exact hcomm _ _
  have h1 : ∀ b : SL3, ∀ (k l : Fin 3) (c' : F4), Commute (ψ b) (τ (ψ (st3 k l c'))) := by
    intro b k l c'
    have hb : b ∈ Subgroup.closure (Set.range fun p : Fin 3 × Fin 3 × F4 =>
        stT (F := F4) (m := 2) (by norm_num) p.1 p.2.1 p.2.2) := by
      rw [closure_stT]; exact Subgroup.mem_top b
    induction hb using Subgroup.closure_induction with
    | mem x hx => obtain ⟨⟨i, j, c⟩, rfl⟩ := hx; exact hst i j c k l c'
    | one => rw [map_one]; exact Commute.one_left _
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_left hy
    | inv x _ hx => rw [map_inv]; exact hx.inv_left
  have hb : b ∈ Subgroup.closure (Set.range fun p : Fin 3 × Fin 3 × F4 =>
      stT (F := F4) (m := 2) (by norm_num) p.1 p.2.1 p.2.2) := by
    rw [closure_stT]; exact Subgroup.mem_top b
  induction hb using Subgroup.closure_induction with
  | mem x hx => obtain ⟨⟨i, j, c⟩, rfl⟩ := hx; exact h1 a i j c
  | one => rw [map_one, map_one]; exact Commute.one_right _
  | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact hx.mul_right hy
  | inv x _ hx => rw [map_inv, map_inv]; exact hx.inv_right

include hττ hKc hKo hKfix hfτ hcomm hθ hτθ in
theorem theta_eq (g : SL3) : θ g = ψ g * τ (ψ g) := by
  have hc := commute_ψ τ f T ψ hKc hKo hfτ hcomm g g
  set k := (ψ g * τ (ψ g))⁻¹ * θ g with hk
  have hkK : k ∈ f.ker := by
    rw [MonoidHom.mem_ker, hk, map_mul, map_inv, map_mul, hfτ, hθ, inv_mul_cancel]
  have hkτ : τ k = k := by
    rw [hk, map_mul, map_inv, map_mul, hττ, hτθ, ← hc.eq]
  have := hKfix k hkK hkτ
  rw [hk, inv_mul_eq_one] at this
  exact this.symm

include hsc hfτ in
theorem inter_le : ψ.range ⊓ ψ.range.map τ ≤ Subgroup.zpowers (ψ omegaI) := by
  rintro x ⟨⟨a, rfl⟩, ⟨_, ⟨b, rfl⟩, hb⟩⟩
  have hf : f (ψ a) = T * f (ψ b) * T⁻¹ := by rw [← hfτ, hb]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hsc a b hf)
  rw [← hn, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ _

include hsc hfτ in
theorem card_inter_dvd [Finite Γ] : Nat.card (ψ.range ⊓ ψ.range.map τ : Subgroup Γ) ∣ 3 := by
  refine (Subgroup.card_dvd_of_le (inter_le τ f T ψ hfτ hsc)).trans ?_
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, omegaI_pow_three, map_one])

include hsc in
theorem ker_le_center : ψ.ker ≤ Subgroup.center SL3 := by
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  refine zpowers_omegaI_le_center (hsc a 1 ?_)
  rw [ha, map_one, map_one, map_one, mul_one, mul_inv_cancel]

include hττ hKc hKo hKfix hfτ hcomm hsc hθ hτθ in
theorem fixed_mem {γ : Γ} (hγ : γ ∈ ψ.range ⊔ ψ.range.map τ) (hτγ : τ γ = γ) :
    γ ∈ θ.range := by
  have hXY : ∀ x ∈ ψ.range, ∀ y ∈ ψ.range.map τ, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact (commute_ψ τ f T ψ hKc hKo hfτ hcomm a b).eq
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨_, ⟨b, rfl⟩, rfl⟩, rfl⟩ := mem_sup_of_commute hXY hγ
  have hba := (commute_ψ τ f T ψ hKc hKo hfτ hcomm b a).eq
  have hτγ' : τ (ψ a) * ψ b = ψ a * τ (ψ b) := by rw [← hτγ, map_mul, hττ]
  have h1 : ψ (a⁻¹ * b) = τ (ψ (b * a⁻¹)) := by
    simp only [map_mul, map_inv]
    have : ψ b * τ (ψ a) = ψ a * τ (ψ b) := by rw [hba, hτγ']
    calc (ψ a)⁻¹ * ψ b = (ψ a)⁻¹ * (ψ b * τ (ψ a)) * (τ (ψ a))⁻¹ := by group
      _ = (ψ a)⁻¹ * (ψ a * τ (ψ b)) * (τ (ψ a))⁻¹ := by rw [this]
      _ = τ (ψ b) * (τ (ψ a))⁻¹ := by group
  have hζ : a⁻¹ * b ∈ Subgroup.zpowers omegaI := hsc (a⁻¹ * b) (b * a⁻¹) (by rw [h1, hfτ])
  set ζ := a⁻¹ * b with hζdef
  have hb : b = a * ζ := by rw [hζdef]; group
  have hthe := theta_eq τ f T ψ θ hττ hKc hKo hKfix hfτ hcomm hθ hτθ
  have key : ψ a * τ (ψ b) = θ a * τ (ψ ζ) := by
    rw [hb, map_mul, map_mul, ← mul_assoc, ← hthe]
  have hy : τ (ψ ζ) = ψ ζ := by
    have e := hτγ
    rw [key, map_mul, hτθ, hττ] at e
    exact (mul_left_cancel e).symm
  have hθζ : θ ζ = ψ ζ * ψ ζ := by rw [hthe, hy]
  have hζ3 : ζ ^ 3 = 1 := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hζ
    rw [← hn, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
      omegaI_pow_three, _root_.one_zpow]
  have hy3 : ψ ζ ^ 3 = 1 := by rw [← map_pow, hζ3, map_one]
  have hyθ : ψ ζ = θ (ζ ^ 2) := by
    rw [map_pow, hθζ, ← sq, ← pow_mul]
    calc ψ ζ = ψ ζ ^ 3 * ψ ζ := by rw [hy3, one_mul]
      _ = ψ ζ ^ (2 * 2) := by rw [← pow_succ]
  rw [key, hy, hyθ, ← map_mul]
  exact ⟨_, rfl⟩

include hKc hKo hKfix hfτ hcomm hθ hττ hτθ in
theorem sup_eq_top {S : Set Γ} (hS : Subgroup.closure S = ⊤)
    (hgen : ∀ s ∈ S, s ∈ θ.range ∨
      (s * s = 1 ∧ ∃ a b, f s = f (ψ a) * (T * f (ψ b) * T⁻¹))) :
    ψ.range ⊔ ψ.range.map τ = ⊤ := by
  rw [eq_top_iff, ← hS, Subgroup.closure_le]
  intro s hs
  rcases hgen s hs with ⟨g, rfl⟩ | ⟨hs2, a, b, hfs⟩
  · rw [theta_eq τ f T ψ θ hττ hKc hKo hKfix hfτ hcomm hθ hτθ]
    exact mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right ⟨ψ g, ⟨g, rfl⟩, rfl⟩)
  · set m := ψ a * τ (ψ b) with hm
    have hmX : m ∈ ψ.range ⊔ ψ.range.map τ :=
      mul_mem (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right ⟨ψ b, ⟨b, rfl⟩, rfl⟩)
    have hk : m⁻¹ * s ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hm, map_mul, hfτ, hfs, inv_mul_cancel]
    exact two_mem_of_mul hKc hKo hmX hk (by group) hs2

include hττ hKc hKo hKfix hfτ hcomm hsc hθ hτθ in
theorem concl_of_assemble [Finite Γ] {S : Set Γ} (hS : Subgroup.closure S = ⊤)
    (hgen : ∀ s ∈ S, s ∈ θ.range ∨
      (s * s = 1 ∧ ∃ a b, f s = f (ψ a) * (T * f (ψ b) * T⁻¹))) :
    (∀ γ, τ γ = γ → γ ∈ θ.range) ∧ ∃ X : Subgroup Γ, X ⊔ X.map τ = ⊤ ∧ ⁅X, X.map τ⁆ = ⊥ ∧
      Nat.card (X ⊓ X.map τ : Subgroup Γ) ∣ 3 ∧ ∃ ψ' : SL3 →* X, Function.Surjective ψ' ∧
        ψ'.ker ≤ Subgroup.center SL3 ∧ ∀ g, θ g = (ψ' g : Γ) * τ (ψ' g) := by
  have htop := sup_eq_top τ f T ψ θ hττ hKc hKo hKfix hfτ hcomm hθ hτθ hS hgen
  refine ⟨fun γ hγ => fixed_mem τ f T ψ θ hττ hKc hKo hKfix hfτ hcomm hsc hθ hτθ
    (by rw [htop]; exact Subgroup.mem_top γ) hγ, ψ.range, htop, ?_,
    card_inter_dvd τ f T ψ hfτ hsc, ψ.rangeRestrict, ψ.rangeRestrict_surjective, ?_,
    fun g => theta_eq τ f T ψ θ hττ hKc hKo hKfix hfτ hcomm hθ hτθ g⟩
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact (commute_ψ τ f T ψ hKc hKo hfτ hcomm a b).eq.symm
  · rw [MonoidHom.ker_rangeRestrict]
    exact ker_le_center f T ψ hsc

include hcomm in
theorem exists_Q_of_mem_closure {S₀ : Set Γ}
    (hS₀ : ∀ s ∈ S₀, ∃ a b, f s = f (ψ a) * (T * f (ψ b) * T⁻¹)) {γ : Γ}
    (hγ : γ ∈ Subgroup.closure S₀) : ∃ a b, f γ = f (ψ a) * (T * f (ψ b) * T⁻¹) := by
  induction hγ using Subgroup.closure_induction with
  | mem x hx => exact hS₀ x hx
  | one => exact ⟨1, 1, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, hab⟩ := hx
    obtain ⟨a', b', hab'⟩ := hy
    refine ⟨a * a', b * b', ?_⟩
    rw [map_mul, hab, hab', map_mul, map_mul, map_mul, map_mul]
    have hc := hcomm a' b
    calc f (ψ a) * (T * f (ψ b) * T⁻¹) * (f (ψ a') * (T * f (ψ b') * T⁻¹))
        = f (ψ a) * ((T * f (ψ b) * T⁻¹) * f (ψ a')) * (T * f (ψ b') * T⁻¹) := by group
      _ = f (ψ a) * (f (ψ a') * (T * f (ψ b) * T⁻¹)) * (T * f (ψ b') * T⁻¹) := by rw [hc]
      _ = f (ψ a) * f (ψ a') * (T * (f (ψ b) * f (ψ b')) * T⁻¹) := by group
  | inv x _ hx =>
    obtain ⟨a, b, hab⟩ := hx
    refine ⟨a⁻¹, b⁻¹, ?_⟩
    rw [map_inv, hab, map_inv, map_inv, map_inv, map_inv]
    have hc := hcomm a⁻¹ b⁻¹
    rw [map_inv, map_inv, map_inv, map_inv] at hc
    calc (f (ψ a) * (T * f (ψ b) * T⁻¹))⁻¹ = (T * (f (ψ b))⁻¹ * T⁻¹) * (f (ψ a))⁻¹ := by group
      _ = (f (ψ a))⁻¹ * (T * (f (ψ b))⁻¹ * T⁻¹) := hc.symm

end Assemble



theorem closure_range_union {G : Type*} [Group G] (θ : SL3 →* G) (D : Subgroup G)
    (h : θ.range ⊔ D = ⊤) : Subgroup.closure (Set.range θ ∪ (D : Set G)) = ⊤ := by
  rw [eq_top_iff, ← h]
  refine sup_le ?_ ?_
  · rintro _ ⟨g, rfl⟩; exact Subgroup.subset_closure (Or.inl ⟨g, rfl⟩)
  · intro x hx; exact Subgroup.subset_closure (Or.inr hx)

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
