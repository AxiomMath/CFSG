module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Open

namespace CoverThree

theorem eq_one_of_sq_of_cube {G : Type*} [Group G] {ζ : G} (h2 : ζ ^ 2 = 1) (h3 : ζ ^ 3 = 1) :
    ζ = 1 := by
  calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
    _ = 1 := by rw [h2, h3, inv_one, mul_one]

theorem mem_normalizer_closure_pair {G : Type*} [Group G] [Finite G] {x u v : G}
    (hu : x * u * x⁻¹ ∈ Subgroup.closure ({u, v} : Set G))
    (hv : x * v * x⁻¹ ∈ Subgroup.closure ({u, v} : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.closure ({u, v} : Set G) : Set G) := by
  have hle : Subgroup.closure ({u, v} : Set G) ≤
      (Subgroup.closure ({u, v} : Set G)).comap (MulAut.conj x).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hu
    · exact hv
  have hmap : (Subgroup.closure ({u, v} : Set G)).map (MulAut.conj x).toMonoidHom =
      Subgroup.closure ({u, v} : Set G) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.mpr hle) ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hle hh, fun hh => ?_⟩
  rw [← hmap] at hh
  obtain ⟨h', hh', he⟩ := hh
  have : h' = h := by
    simpa [MulAut.conj_apply] using he
  rwa [← this]

variable {K X : Type} [Group K] [Group X] {f : K →* X}

theorem eq_of_map_eq_of_sq_eq_one (hker : f.ker ≤ Subgroup.center K)
    (h3 : ∀ ζ ∈ f.ker, ζ ^ 3 = 1) {x y : K} (hxy : f x = f y) (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) : x = y := by
  have hζ : x⁻¹ * y ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hc : Commute x (x⁻¹ * y) := Subgroup.mem_center_iff.mp (hker hζ) x
  have h2 : (x⁻¹ * y) ^ 2 = 1 := by
    have h := hc.mul_pow 2
    rw [mul_inv_cancel_left, hy, hx, one_mul] at h
    exact h.symm
  exact inv_mul_eq_one.mp (eq_one_of_sq_of_cube h2 (h3 _ hζ))

theorem exists_preimage_sq_eq_one (hf : Function.Surjective f) (h3 : ∀ ζ ∈ f.ker, ζ ^ 3 = 1)
    {q : X} (hq : q ^ 2 = 1) : ∃ x : K, f x = q ∧ x ^ 2 = 1 := by
  obtain ⟨x, rfl⟩ := hf q
  have hk : x ^ 2 ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow, hq]
  refine ⟨x ^ 3, ?_, ?_⟩
  · rw [map_pow, pow_succ, hq, one_mul]
  · calc (x ^ 3) ^ 2 = (x ^ 2) ^ 3 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := h3 _ hk

theorem pow_three_eq_one_of_inv (hker : f.ker ≤ Subgroup.center K)
    (h3 : ∀ ζ ∈ f.ker, ζ ^ 3 = 1) {a g : K} (ha : f a ^ 3 = 1)
    (hg : f g * f a * (f g)⁻¹ = (f a)⁻¹) : a ^ 3 = 1 := by
  have hk : a ^ 3 ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow, ha]
  have hζ : a * (g * a * g⁻¹) ∈ f.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, hg, mul_inv_cancel]
  have hgag : g * a * g⁻¹ = a⁻¹ * (a * (g * a * g⁻¹)) := (inv_mul_cancel_left a _).symm
  have hcomm : Commute a⁻¹ (a * (g * a * g⁻¹)) := Subgroup.mem_center_iff.mp (hker hζ) a⁻¹
  have hconj : g * a ^ 3 * g⁻¹ = (a ^ 3)⁻¹ := by
    rw [← conj_pow, hgag, hcomm.mul_pow, h3 _ hζ, mul_one, inv_pow]
  have hcen : g * a ^ 3 * g⁻¹ = a ^ 3 := by
    rw [Subgroup.mem_center_iff.mp (hker hk) g, mul_inv_cancel_right]
  have h2 : (a ^ 3) ^ 2 = 1 := by
    rw [sq]
    calc a ^ 3 * a ^ 3 = a ^ 3 * (a ^ 3)⁻¹ := by rw [← hconj, hcen]
      _ = 1 := mul_inv_cancel _
  exact eq_one_of_sq_of_cube h2 (h3 _ hk)

theorem commute_of_conj (hker : f.ker ≤ Subgroup.center K) (h3 : ∀ ζ ∈ f.ker, ζ ^ 3 = 1)
    {a b g : K} (hab : f a * f b = f b * f a) (hga : f g * f a * (f g)⁻¹ = f a)
    (hgb : f g * f b * (f g)⁻¹ = (f b)⁻¹) : a * b = b * a := by
  obtain ⟨c, hc⟩ : ∃ c : K, c = a * b * (b * a)⁻¹ := ⟨_, rfl⟩
  obtain ⟨ζ₁, hζ₁⟩ : ∃ ζ : K, ζ = a⁻¹ * (g * a * g⁻¹) := ⟨_, rfl⟩
  obtain ⟨ζ₂, hζ₂⟩ : ∃ ζ : K, ζ = b * (g * b * g⁻¹) := ⟨_, rfl⟩
  have hck : c ∈ f.ker := by
    simp only [hc, MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  have hζ₁k : ζ₁ ∈ f.ker := by
    simp only [hζ₁, MonoidHom.mem_ker, map_mul, map_inv, hga, inv_mul_cancel]
  have hζ₂k : ζ₂ ∈ f.ker := by
    simp only [hζ₂, MonoidHom.mem_ker, map_mul, map_inv, hgb, mul_inv_cancel]
  have zc : ∀ y, y * c = c * y := Subgroup.mem_center_iff.mp (hker hck)
  have z1 : ∀ y, y * ζ₁ = ζ₁ * y := Subgroup.mem_center_iff.mp (hker hζ₁k)
  have z2 : ∀ y, y * ζ₂ = ζ₂ * y := Subgroup.mem_center_iff.mp (hker hζ₂k)
  have hcab : a * b = c * (b * a) := by rw [hc, inv_mul_cancel_right]
  have hgag : g * a * g⁻¹ = a * ζ₁ := by rw [hζ₁, mul_inv_cancel_left]
  have hgbg : g * b * g⁻¹ = b⁻¹ * ζ₂ := by rw [hζ₂, inv_mul_cancel_left]
  have key : (a * ζ₁) * (b⁻¹ * ζ₂) = c * ((b⁻¹ * ζ₂) * (a * ζ₁)) := by
    rw [← hgag, ← hgbg]
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (c * (b * a)) * g⁻¹ := by rw [hcab]
      _ = c * (g * b * g⁻¹ * (g * a * g⁻¹)) := by rw [← mul_assoc g c, zc g]; group
  have hL : (a * ζ₁) * (b⁻¹ * ζ₂) = (a * b⁻¹) * (ζ₁ * ζ₂) := by
    rw [mul_assoc a ζ₁, ← mul_assoc ζ₁ b⁻¹, ← z1 b⁻¹]
    group
  have hR : c * ((b⁻¹ * ζ₂) * (a * ζ₁)) = (c * (b⁻¹ * a)) * (ζ₁ * ζ₂) := by
    rw [mul_assoc b⁻¹ ζ₂, ← mul_assoc ζ₂ a, ← z2 a, mul_assoc a ζ₂ ζ₁, z1 ζ₂]
    group
  have h1 : a * b⁻¹ = c * (b⁻¹ * a) := mul_right_cancel (hL.symm.trans (key.trans hR))
  have h2 : b⁻¹ * a = c * (a * b⁻¹) := by
    calc b⁻¹ * a = b⁻¹ * (a * b) * b⁻¹ := by group
      _ = b⁻¹ * (c * (b * a)) * b⁻¹ := by rw [hcab]
      _ = c * (a * b⁻¹) := by rw [← mul_assoc b⁻¹ c, zc b⁻¹]; group
  have hcc : c * c * (a * b⁻¹) = 1 * (a * b⁻¹) := by
    calc c * c * (a * b⁻¹) = c * (c * (a * b⁻¹)) := mul_assoc _ _ _
      _ = c * (b⁻¹ * a) := by rw [← h2]
      _ = a * b⁻¹ := h1.symm
      _ = 1 * (a * b⁻¹) := (one_mul _).symm
  have hc1 : c = 1 := eq_one_of_sq_of_cube (by rw [sq]; exact mul_right_cancel hcc) (h3 c hck)
  rw [hcab, hc1, one_mul]

theorem exists_e27 [Finite K] (hf : Function.Surjective f) (hker : f.ker = Subgroup.center K)
    (hZ : Nat.card (Subgroup.center K) = 3) {q₁ q₂ a b g₁ g₂ : X}
    (hq₁ : q₁ ^ 2 = 1) (hq₂ : q₂ ^ 2 = 1) (hq : q₁ * q₂ = q₂ * q₁) (hq₁1 : q₁ ≠ 1)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a)
    (hdist : ∀ i j k l : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) →
      i = k ∧ j = l)
    (haq : ∀ q ∈ ({q₁, q₂} : Set X), a * q * a⁻¹ ∈ ({q₁, q₂, q₁ * q₂} : Set X))
    (hbq : ∀ q ∈ ({q₁, q₂} : Set X), b * q * b⁻¹ ∈ ({q₁, q₂, q₁ * q₂} : Set X))
    (hg₁ : g₁ * a * g₁⁻¹ = a⁻¹) (hg₂a : g₂ * a * g₂⁻¹ = a) (hg₂b : g₂ * b * g₂⁻¹ = b⁻¹) :
    ∃ Q E : Subgroup K, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ E ≤ Subgroup.normalizer (Q : Set K) ∧
      IsElemAbelian 3 E ∧ 27 ≤ Nat.card E := by
  have hkerZ : f.ker ≤ Subgroup.center K := hker.le
  have h3 : ∀ ζ ∈ f.ker, ζ ^ 3 = 1 := by
    intro ζ hζ
    rw [hker] at hζ
    have := pow_card_eq_one' (G := ↥(Subgroup.center K)) (x := ⟨ζ, hζ⟩)
    rw [hZ] at this
    exact congrArg Subtype.val this
  obtain ⟨Q1, rfl, hQ1s⟩ := exists_preimage_sq_eq_one hf h3 hq₁
  obtain ⟨Q2, rfl, hQ2s⟩ := exists_preimage_sq_eq_one hf h3 hq₂
  obtain ⟨A, rfl⟩ := hf a
  obtain ⟨B, rfl⟩ := hf b
  obtain ⟨G1, rfl⟩ := hf g₁
  obtain ⟨G2, rfl⟩ := hf g₂
  have hA3 : A ^ 3 = 1 := pow_three_eq_one_of_inv hkerZ h3 ha hg₁
  have hB3 : B ^ 3 = 1 := pow_three_eq_one_of_inv hkerZ h3 hb hg₂b
  have hAB : A * B = B * A := commute_of_conj hkerZ h3 hab hg₂a hg₂b
  have hsq : ∀ x : K, x ^ 2 = 1 → ∀ y : K, (y * x * y⁻¹) ^ 2 = 1 := fun x hx y => by
    rw [conj_pow, hx, mul_one, mul_inv_cancel]
  have hQ12 : Q1 * Q2 = Q2 * Q1 := by
    have h : Q1 * Q2 * Q1⁻¹ = Q2 :=
      eq_of_map_eq_of_sq_eq_one hkerZ h3
        (by rw [map_mul, map_mul, map_inv, hq, mul_inv_cancel_right]) (hsq Q2 hQ2s Q1) hQ2s
    exact mul_inv_eq_iff_eq_mul.mp h
  have hQQs : (Q1 * Q2) ^ 2 = 1 := by
    rw [(show Commute Q1 Q2 from hQ12).mul_pow, hQ1s, hQ2s, one_mul]
  have hQel : IsElemAbelian 2 (Subgroup.closure ({Q1, Q2} : Set K)) := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · intro x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact hQ12
      · exact hQ12.symm
      · rfl
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hQ1s
      · exact hQ2s
  have hQp : IsPGroup 2 (Subgroup.closure ({Q1, Q2} : Set K)) := fun x =>
    ⟨1, Subtype.ext (by simpa using hQel.2 x x.2)⟩
  have hQne : Subgroup.closure ({Q1, Q2} : Set K) ≠ ⊥ := by
    intro h
    have hm : Q1 ∈ Subgroup.closure ({Q1, Q2} : Set K) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    rw [h, Subgroup.mem_bot] at hm
    exact hq₁1 (by rw [hm, map_one])
  have hconjMem : ∀ x : K, f x * f Q1 * (f x)⁻¹ ∈ ({f Q1, f Q2, f Q1 * f Q2} : Set X) →
      x * Q1 * x⁻¹ ∈ Subgroup.closure ({Q1, Q2} : Set K) := by
    intro x hx
    have hsx := hsq Q1 hQ1s x
    have hfx : f (x * Q1 * x⁻¹) = f x * f Q1 * (f x)⁻¹ := by rw [map_mul, map_mul, map_inv]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [eq_of_map_eq_of_sq_eq_one hkerZ h3 (hfx.trans hx) hsx hQ1s]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [eq_of_map_eq_of_sq_eq_one hkerZ h3 (hfx.trans hx) hsx hQ2s]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [eq_of_map_eq_of_sq_eq_one hkerZ h3 ((hfx.trans hx).trans (map_mul f Q1 Q2).symm) hsx
        hQQs]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hconjMem2 : ∀ x : K, f x * f Q2 * (f x)⁻¹ ∈ ({f Q1, f Q2, f Q1 * f Q2} : Set X) →
      x * Q2 * x⁻¹ ∈ Subgroup.closure ({Q1, Q2} : Set K) := by
    intro x hx
    have hsx := hsq Q2 hQ2s x
    have hfx : f (x * Q2 * x⁻¹) = f x * f Q2 * (f x)⁻¹ := by rw [map_mul, map_mul, map_inv]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [eq_of_map_eq_of_sq_eq_one hkerZ h3 (hfx.trans hx) hsx hQ1s]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [eq_of_map_eq_of_sq_eq_one hkerZ h3 (hfx.trans hx) hsx hQ2s]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [eq_of_map_eq_of_sq_eq_one hkerZ h3 ((hfx.trans hx).trans (map_mul f Q1 Q2).symm) hsx
        hQQs]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hAN : A ∈ Subgroup.normalizer (Subgroup.closure ({Q1, Q2} : Set K) : Set K) :=
    mem_normalizer_closure_pair (hconjMem A (haq _ (Set.mem_insert _ _)))
      (hconjMem2 A (haq _ (Set.mem_insert_of_mem _ rfl)))
  have hBN : B ∈ Subgroup.normalizer (Subgroup.closure ({Q1, Q2} : Set K) : Set K) :=
    mem_normalizer_closure_pair (hconjMem B (hbq _ (Set.mem_insert _ _)))
      (hconjMem2 B (hbq _ (Set.mem_insert_of_mem _ rfl)))
  have hcen : ∀ z ∈ Subgroup.center K, ∀ y : K, y * z = z * y := fun z hz =>
    Subgroup.mem_center_iff.mp hz
  have hS3 : ∀ x ∈ (insert A (insert B (Subgroup.center K : Set K))), x ^ 3 = 1 := by
    intro x hx
    rcases hx with rfl | rfl | hx
    · exact hA3
    · exact hB3
    · exact h3 x (hker ▸ hx)
  have hScomm : ∀ x ∈ (insert A (insert B (Subgroup.center K : Set K))),
      ∀ y ∈ (insert A (insert B (Subgroup.center K : Set K))), x * y = y * x := by
    intro x hx y hy
    rcases hy with rfl | rfl | hy
    · rcases hx with rfl | rfl | hx
      · rfl
      · exact hAB.symm
      · exact (hcen x hx _).symm
    · rcases hx with rfl | rfl | hx
      · exact hAB
      · rfl
      · exact (hcen x hx _).symm
    · exact hcen y hy x
  have hEel : IsElemAbelian 3 (Subgroup.closure (insert A (insert B
      (Subgroup.center K : Set K)))) := IsElemAbelian.closure_of_commute hScomm hS3
  have hEN : Subgroup.closure (insert A (insert B (Subgroup.center K : Set K))) ≤
      Subgroup.normalizer (Subgroup.closure ({Q1, Q2} : Set K) : Set K) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | rfl | hx
    · exact hAN
    · exact hBN
    · exact Subgroup.center_le_normalizer _ hx
  have hmemE : ∀ (i j : ℕ) (z : ↥(Subgroup.center K)), A ^ i * B ^ j * (z : K) ∈
      Subgroup.closure (insert A (insert B (Subgroup.center K : Set K))) := by
    intro i j z
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ?_ _)
      (Subgroup.pow_mem _ ?_ _)) ?_
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ z.2))
  let F : Fin 3 × Fin 3 × ↥(Subgroup.center K) →
      ↥(Subgroup.closure (insert A (insert B (Subgroup.center K : Set K)))) :=
    fun p => ⟨A ^ (p.1 : ℕ) * B ^ (p.2.1 : ℕ) * (p.2.2 : K), hmemE _ _ _⟩
  have hFinj : Function.Injective F := by
    rintro ⟨i, j, z⟩ ⟨k, l, z'⟩ h
    have h' : A ^ (i : ℕ) * B ^ (j : ℕ) * (z : K) = A ^ (k : ℕ) * B ^ (l : ℕ) * (z' : K) :=
      congrArg Subtype.val h
    have hz : f z = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact z.2
    have hz' : f z' = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact z'.2
    have hf' := congrArg f h'
    simp only [map_mul, map_pow, hz, hz', mul_one] at hf'
    obtain ⟨rfl, rfl⟩ := hdist i j k l hf'
    exact Prod.ext rfl (Prod.ext rfl (Subtype.ext (mul_left_cancel h')))
  have hdom : Nat.card (Fin 3 × Fin 3 × ↥(Subgroup.center K)) = 27 := by
    rw [Nat.card_prod, Nat.card_prod, hZ]
    simp
  refine ⟨_, _, hQne, hQp, hEN, hEel, ?_⟩
  rw [← hdom]
  exact Nat.card_le_card_of_injective F hFinj

end CoverThree

theorem KConf.false_of_threeCover {K X : Type} [Group K] [Finite K] [Group X]
    {L V MK : Subgroup K} (hK : KConf K L V MK) (e : K ⧸ Subgroup.center K ≃* X)
    (hZ : Nat.card (Subgroup.center K) = 3) {q₁ q₂ a b g₁ g₂ : X}
    (hq₁ : q₁ ^ 2 = 1) (hq₂ : q₂ ^ 2 = 1) (hq : q₁ * q₂ = q₂ * q₁) (hq₁1 : q₁ ≠ 1)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a)
    (hdist : ∀ i j k l : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) →
      i = k ∧ j = l)
    (haq : ∀ q ∈ ({q₁, q₂} : Set X), a * q * a⁻¹ ∈ ({q₁, q₂, q₁ * q₂} : Set X))
    (hbq : ∀ q ∈ ({q₁, q₂} : Set X), b * q * b⁻¹ ∈ ({q₁, q₂, q₁ * q₂} : Set X))
    (hg₁ : g₁ * a * g₁⁻¹ = a⁻¹) (hg₂a : g₂ * a * g₂⁻¹ = a) (hg₂b : g₂ * b * g₂⁻¹ = b⁻¹) :
    False := by
  let f : K →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨Q, E, hQ, hQp, hEN, hEel, hE⟩ := CoverThree.exists_e27 hf hker hZ hq₁ hq₂ hq hq₁1 ha
    hb hab hdist haq hbq hg₁ hg₂a hg₂b
  have h := hK.card_le Q hQ hQp 3 Nat.prime_three (by norm_num) E hEN hEel
  norm_num at h
  omega

end CFSG.SectionRank.QTK.Insp443

end
