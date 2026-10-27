module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem conj_mul_conj (n c a : G) : n * c * a * (n * c)⁻¹ = n * (c * a * c⁻¹) * n⁻¹ := by
  group

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

theorem mem_normalizer_closure [Finite G] {s : Set G} {g : G}
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s) :
    g ∈ Subgroup.normalizer ((Subgroup.closure s : Subgroup G) : Set G) := by
  have hle : (Subgroup.closure s).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure s := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro x hx
    exact h x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

theorem mem_normalizer_zpowers_iff [Finite G] {b g : G} :
    g ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) ↔ g * b * g⁻¹ ∈ Subgroup.zpowers b := by
  constructor
  · intro h
    exact (Subgroup.mem_normalizer_iff.1 h b).1 (Subgroup.mem_zpowers b)
  · intro h
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have : g * b ^ k * g⁻¹ = (g * b * g⁻¹) ^ k := conj_zpow.symm
    rw [this]
    exact Subgroup.zpow_mem _ h k

theorem normalizer_map_conj (g : G) (H : Subgroup G) :
    Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)).symm

theorem card_normalizer_map_conj (g : G) (H : Subgroup G) :
    Nat.card (Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
      Nat.card (Subgroup.normalizer (H : Set G)) := by
  rw [normalizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem centralizer_map_conj (g : G) (H : Subgroup G) :
    Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_map, SetLike.mem_coe,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro h
    refine ⟨g⁻¹ * x * g, fun y hy => ?_, by group⟩
    have := h (g * y * g⁻¹) ⟨y, hy, rfl⟩
    have h2 : y * (g⁻¹ * x * g) = g⁻¹ * (g * y * g⁻¹ * x) * g := by group
    have h3 : g⁻¹ * x * g * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
    rw [h2, h3, this]
  · rintro ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩
    have := hz y hy
    have h2 : g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
    have h3 : g * z * g⁻¹ * (g * y * g⁻¹) = g * (z * y) * g⁻¹ := by group
    rw [h2, h3, this]

theorem card_centralizer_map_conj (g : G) (H : Subgroup G) :
    Nat.card (Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
      Nat.card (Subgroup.centralizer (H : Set G)) := by
  rw [centralizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem map_conj_map_conj (a b : G) (H : Subgroup G) :
    (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      H.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_map_conj_inv (g : G) (H : Subgroup G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [map_conj_map_conj, inv_mul_cancel]
  ext x
  simp [Subgroup.mem_map]

theorem map_conj_zpowers (g x : G) :
    (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (g * x * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem exists_zpowers_eq_of_card_eq_prime [Finite G] {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (h : Nat.card P = p) : ∃ x : G, P = Subgroup.zpowers x ∧ orderOf x = p := by
  have hne : P ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, h]
    exact hp.one_lt
  obtain ⟨⟨x, hxP⟩, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hx1 : x ≠ 1 := fun h1 => hx (Subtype.ext h1)
  have hord : orderOf x = p := by
    have hdvd : orderOf x ∣ p := h ▸ Subgroup.orderOf_dvd_natCard P hxP
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hx1
    · exact h1
  refine ⟨x, (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxP) ?_).symm, hord⟩
  rw [Nat.card_zpowers, hord, h]

theorem exists_conj_of_isPGroup [Finite G] (p : ℕ) [Fact p.Prime] {B B₀ : Subgroup G}
    (hB : IsPGroup p B) (hB₀ : IsPGroup p B₀) (hi : ¬ p ∣ B.index) (hi₀ : ¬ p ∣ B₀.index) :
    ∃ g : G, B₀.map (MulAut.conj g).toMonoidHom = B := by
  let P : Sylow p G := hB.toSylow hi
  let P₀ : Sylow p G := hB₀.toSylow hi₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
  refine ⟨g, ?_⟩
  have h := congrArg (fun Q : Sylow p G => (Q : Subgroup G)) hg
  simp only [Sylow.coe_subgroup_smul] at h
  exact h

theorem mem_zpowers_five_iff {b : G} (hb : orderOf b = 5) (y : G) :
    y ∈ Subgroup.zpowers b ↔ y = 1 ∨ y = b ∨ y = b * b ∨ y = b * b * b ∨ y = b * b * b * b := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    have hk : b ^ k = b ^ (k % (5 : ℤ)) := by
      have := zpow_mod_orderOf b k
      rw [hb] at this
      exact this.symm
    rw [hk]
    have h5 : k % (5 : ℤ) = 0 ∨ k % (5 : ℤ) = 1 ∨ k % (5 : ℤ) = 2 ∨ k % (5 : ℤ) = 3 ∨
        k % (5 : ℤ) = 4 := by omega
    rcases h5 with h5 | h5 | h5 | h5 | h5 <;> rw [h5]
    · left; simp
    · right; left; simp
    · right; right; left; simp [sq]
    · right; right; right; left
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]; simp [pow_succ]
    · right; right; right; right
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]; simp [pow_succ]
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_zpowers _)
        (Subgroup.mem_zpowers _)) (Subgroup.mem_zpowers _)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_zpowers _)
        (Subgroup.mem_zpowers _)) (Subgroup.mem_zpowers _)) (Subgroup.mem_zpowers _)

theorem mem_zpowers_four_iff {b : G} (hb : orderOf b = 4) (y : G) :
    y ∈ Subgroup.zpowers b ↔ y = 1 ∨ y = b ∨ y = b * b ∨ y = b * b * b := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    have hk : b ^ k = b ^ (k % (4 : ℤ)) := by
      have := zpow_mod_orderOf b k
      rw [hb] at this
      exact this.symm
    rw [hk]
    have h4 : k % (4 : ℤ) = 0 ∨ k % (4 : ℤ) = 1 ∨ k % (4 : ℤ) = 2 ∨ k % (4 : ℤ) = 3 := by omega
    rcases h4 with h4 | h4 | h4 | h4 <;> rw [h4]
    · left; simp
    · right; left; simp
    · right; right; left; simp [sq]
    · right; right; right
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]; simp [pow_succ]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_zpowers _)
        (Subgroup.mem_zpowers _)) (Subgroup.mem_zpowers _)

theorem centralizer_zpowers_eq (b : G) :
    Subgroup.centralizer (Subgroup.zpowers b : Set G) = Subgroup.centralizer ({b} : Set G) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
    forall_eq]
  constructor
  · intro h
    exact h b (Subgroup.mem_zpowers b)
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_left (show Commute b x from h) k)).eq


theorem exists_map_conj_le_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P₀ : Sylow p G)
    {E : Subgroup G} (hE : IsPGroup p E) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ (P₀ : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P₀
  refine ⟨g, ?_⟩
  have h := congrArg (fun R : Sylow p G => (R : Subgroup G)) hg
  simp only [Sylow.coe_subgroup_smul] at h
  rw [← h]
  exact Subgroup.map_mono hQ

end CFSG.GroupTheory
