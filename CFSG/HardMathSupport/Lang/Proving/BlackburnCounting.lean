module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.HardMathSupport.Lang.Proving

variable {G : Type*} [Group G]

@[expose] def cmap (x y : G) : G := y⁻¹ * x⁻¹ * y * x

theorem cmap_apply (x y : G) : cmap x y = y⁻¹ * x⁻¹ * y * x := rfl

lemma cmap_eq (x y : G) : cmap x y = y⁻¹ * x⁻¹ * y * x := by simp only [cmap]

lemma cmap_mul (x a b : G) : cmap x (a * b) = (b⁻¹ * cmap x a * b) * cmap x b := by
  simp only [cmap]; group

lemma cmap_inv (x y : G) : cmap x y⁻¹ = y * (cmap x y)⁻¹ * y⁻¹ := by
  simp only [cmap]; group

lemma cmap_one (x : G) : cmap x 1 = 1 := by
  simp [cmap]

def cSub (x : G) (H : Subgroup G) (K : Subgroup G) [K.Normal] : Subgroup G where
  carrier := {y | y ∈ H ∧ cmap x y ∈ K}
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    rw [cmap_mul]
    refine K.mul_mem ?_ hcb
    have := Subgroup.Normal.conj_mem (inferInstance : K.Normal) (cmap x a) hca b⁻¹
    simpa using this
  one_mem' := ⟨H.one_mem, by rw [cmap_one]; exact K.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, hca⟩
    refine ⟨H.inv_mem ha, ?_⟩
    rw [cmap_inv]
    exact Subgroup.Normal.conj_mem (inferInstance : K.Normal) _ (K.inv_mem hca) a

lemma mem_cSub {x : G} {H K : Subgroup G} [K.Normal] {y : G} :
    y ∈ cSub x H K ↔ y ∈ H ∧ cmap x y ∈ K := Iff.rfl

lemma mk_cmap_mul (K K' : Subgroup G) [K'.Normal]
    (hK' : ∀ k ∈ K, ∀ g : G, g⁻¹ * k * g * k⁻¹ ∈ K') (x a b : G) (ha : cmap x a ∈ K) :
    (QuotientGroup.mk (cmap x (a * b)) : G ⧸ K')
      = QuotientGroup.mk (cmap x a) * QuotientGroup.mk (cmap x b) := by
  have h1 : (QuotientGroup.mk (b⁻¹ * cmap x a * b) : G ⧸ K')
      = QuotientGroup.mk (cmap x a) := by
    rw [QuotientGroup.eq]
    have := hK' (cmap x a)⁻¹ (K.inv_mem ha) b
    simpa [mul_assoc, mul_inv_rev] using this
  rw [cmap_mul, QuotientGroup.mk_mul, h1]

def cHom (x : G) (H K K' : Subgroup G) [K.Normal] [K'.Normal]
    (hK' : ∀ k ∈ K, ∀ g : G, g⁻¹ * k * g * k⁻¹ ∈ K') :
    cSub x H K →* G ⧸ K' :=
  MonoidHom.mk' (fun y => QuotientGroup.mk (cmap x y.1))
    (fun a b => mk_cmap_mul K K' hK' x a.1 b.1 a.2.2)

lemma cHom_range_le (x : G) (H K K' : Subgroup G) [K.Normal] [K'.Normal]
    (hK' : ∀ k ∈ K, ∀ g : G, g⁻¹ * k * g * k⁻¹ ∈ K') :
    (cHom x H K K' hK').range ≤ K.map (QuotientGroup.mk' K') := by
  rintro _ ⟨y, rfl⟩
  exact ⟨cmap x y.1, y.2.2, rfl⟩

def cKerEquiv (x : G) (H K K' : Subgroup G) [K.Normal] [K'.Normal] (hKK : K' ≤ K)
    (hK' : ∀ k ∈ K, ∀ g : G, g⁻¹ * k * g * k⁻¹ ∈ K') :
    (cHom x H K K' hK').ker ≃ cSub x H K' where
  toFun a := ⟨a.1.1, a.1.2.1, (QuotientGroup.eq_one_iff _).1 a.2⟩
  invFun b := ⟨⟨b.1, b.2.1, hKK b.2.2⟩, (QuotientGroup.eq_one_iff _).2 b.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_cSub_le_three_mul [Finite G] (x : G) (H K K' : Subgroup G) [K.Normal] [K'.Normal]
    (hKK : K' ≤ K) (hK' : ∀ k ∈ K, ∀ g : G, g⁻¹ * k * g * k⁻¹ ∈ K')
    (hfac : Nat.card (K.map (QuotientGroup.mk' K')) ≤ 3) :
    Nat.card (cSub x H K) ≤ 3 * Nat.card (cSub x H K') := by
  have hidx := Subgroup.card_mul_index (cHom x H K K' hK').ker
  have hker := Subgroup.index_ker (cHom x H K K' hK')
  have hrange : Nat.card (cHom x H K K' hK').range ≤ 3 :=
    le_trans (Subgroup.card_le_of_le (cHom_range_le x H K K' hK')) hfac
  have hkc : Nat.card (cHom x H K K' hK').ker = Nat.card (cSub x H K') :=
    Nat.card_congr (cKerEquiv x H K K' hKK hK')
  rw [← hidx, hker, hkc, mul_comm 3]
  exact Nat.mul_le_mul_left _ hrange

open scoped commutatorElement

instance lcs_normal' (G : Type*) [Group G] (k : ℕ) :
    ((⊤ : Subgroup G).lowerCentralSeries k).Normal :=
  Subgroup.lowerCentralSeries_normal (⊤ : Subgroup G) k

lemma lcs_comm_mem (G : Type*) [Group G] (k : ℕ) {g u : G}
    (hu : u ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    g⁻¹ * u * g * u⁻¹ ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
  have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top g⁻¹) hu
  rw [commutatorElement_def] at h
  simpa using h

lemma mem_cSub_bot {x y : G} {H : Subgroup G} :
    y ∈ cSub x H ⊥ ↔ y ∈ H ∧ x * y = y * x := by
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    have h' : cmap x y = 1 := (Subgroup.mem_bot).1 h
    have e : y * x = x * (y * (y⁻¹ * x⁻¹ * y * x)) := by group
    rw [← cmap, h', mul_one] at e
    exact e.symm
  · rintro ⟨hy, h⟩
    refine ⟨hy, Subgroup.mem_bot.2 ?_⟩
    have hyx : y * x = x * y := h.symm
    have : cmap x y = y⁻¹ * (x⁻¹ * (y * x)) := by simp [cmap, mul_assoc]
    rw [this, hyx]
    group

theorem card_cSub_le_pow_mul [Finite G] (x : G) (H : Subgroup G) (k j : ℕ)
    (hfac : ∀ l, k ≤ l → l < k + j →
      Nat.card (((⊤ : Subgroup G).lowerCentralSeries l).map
        (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (l + 1)))) ≤ 3) :
    Nat.card (cSub x H ((⊤ : Subgroup G).lowerCentralSeries k))
      ≤ 3 ^ j * Nat.card (cSub x H ((⊤ : Subgroup G).lowerCentralSeries (k + j))) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hKK : (⊤ : Subgroup G).lowerCentralSeries (k + j + 1)
        ≤ (⊤ : Subgroup G).lowerCentralSeries (k + j) :=
      Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (Nat.le_succ _)
    have hK' : ∀ u ∈ (⊤ : Subgroup G).lowerCentralSeries (k + j), ∀ g : G,
        g⁻¹ * u * g * u⁻¹ ∈ (⊤ : Subgroup G).lowerCentralSeries (k + j + 1) :=
      fun u hu g => lcs_comm_mem G (k + j) hu
    have step := card_cSub_le_three_mul x H ((⊤ : Subgroup G).lowerCentralSeries (k + j))
      ((⊤ : Subgroup G).lowerCentralSeries (k + j + 1)) hKK hK'
      (hfac (k + j) (by omega) (by omega))
    have ih' := ih (fun l h1 h2 => hfac l h1 (by omega))
    calc Nat.card (cSub x H ((⊤ : Subgroup G).lowerCentralSeries k))
        ≤ 3 ^ j * Nat.card (cSub x H ((⊤ : Subgroup G).lowerCentralSeries (k + j))) := ih'
      _ ≤ 3 ^ j * (3 * Nat.card (cSub x H ((⊤ : Subgroup G).lowerCentralSeries (k + j + 1)))) :=
          Nat.mul_le_mul_left _ step
      _ = 3 ^ (j + 1) * Nat.card (cSub x H ((⊤ : Subgroup G).lowerCentralSeries (k + (j + 1)))) := by
          rw [pow_succ, show k + (j + 1) = k + j + 1 by omega]; ring

theorem card_le_pow_mul_centralizer [Finite G] (x : G) (H : Subgroup G) (k N : ℕ) (hkN : k ≤ N)
    (hN : (⊤ : Subgroup G).lowerCentralSeries N = ⊥)
    (hfac : ∀ l, k ≤ l → l < N →
      Nat.card (((⊤ : Subgroup G).lowerCentralSeries l).map
        (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (l + 1)))) ≤ 3)
    (hH : ∀ y ∈ H, cmap x y ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    Nat.card H ≤ 3 ^ (N - k) * Nat.card (cSub x H ⊥) := by
  have hH' : cSub x H ((⊤ : Subgroup G).lowerCentralSeries k) = H :=
    le_antisymm (fun y hy => hy.1) (fun y hy => ⟨hy, hH y hy⟩)
  have hbot : cSub x H ((⊤ : Subgroup G).lowerCentralSeries N) = cSub x H ⊥ := by
    ext y
    simp only [mem_cSub, hN]
  have key := card_cSub_le_pow_mul x H k (N - k) (by
    intro l h1 h2; exact hfac l h1 (by omega))
  rw [Nat.add_sub_of_le hkN, hbot, hH'] at key
  exact key

theorem card_map_mk'_eq_index (K K' : Subgroup G) [K'.Normal] :
    Nat.card (K.map (QuotientGroup.mk' K')) = (K'.subgroupOf K).index := by
  let φ : K →* G ⧸ K' := (QuotientGroup.mk' K').comp K.subtype
  have hker : φ.ker = K'.subgroupOf K := by
    ext k
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hr : φ.range = K.map (QuotientGroup.mk' K') := by
    simp [φ, MonoidHom.range_comp]
  rw [← hr, ← hker, Subgroup.index_ker]

theorem card_le_pow_mul_centralizer_of_index [Finite G] (x : G) (H : Subgroup G) (k N : ℕ)
    (hkN : k ≤ N) (hN : (⊤ : Subgroup G).lowerCentralSeries N = ⊥)
    (hidx : ∀ l, k ≤ l → l < N →
      (((⊤ : Subgroup G).lowerCentralSeries (l + 1)).subgroupOf
        ((⊤ : Subgroup G).lowerCentralSeries l)).index ≤ 3)
    (hH : ∀ y ∈ H, cmap x y ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    Nat.card H ≤ 3 ^ (N - k) * Nat.card (cSub x H ⊥) :=
  card_le_pow_mul_centralizer x H k N hkN hN
    (fun l h1 h2 => by rw [card_map_mk'_eq_index]; exact hidx l h1 h2) hH

end CFSG.HardMathSupport.Lang.Proving
