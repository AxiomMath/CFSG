module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

section ConjOrbit

variable {G : Type*} [Group G]

def conjOrbit (H : Subgroup G) (a : G) : Set G :=
  {y | ∃ h ∈ H, h * a * h⁻¹ = y}

theorem mem_conjOrbit {H : Subgroup G} {a y : G} :
    y ∈ conjOrbit H a ↔ ∃ h ∈ H, h * a * h⁻¹ = y := Iff.rfl

theorem conjOrbit_mono {H K : Subgroup G} (hHK : H ≤ K) (a : G) :
    conjOrbit H a ⊆ conjOrbit K a :=
  fun _ ⟨h, hh, hy⟩ => ⟨h, hHK hh, hy⟩

theorem conjOrbit_eq_of_mem {H : Subgroup G} {a y : G} (hy : y ∈ conjOrbit H a) :
    conjOrbit H y = conjOrbit H a := by
  obtain ⟨h, hh, rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * h, H.mul_mem hk hh, by group⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m * h⁻¹, H.mul_mem hm (H.inv_mem hh), by group⟩

theorem ncard_range_conj_mul_card {Γ : Type*} [Group Γ] (f : Γ →* G) (a : G) :
    (Set.range fun γ : Γ => f γ * a * (f γ)⁻¹).ncard *
      Nat.card {γ : Γ // f γ * a * (f γ)⁻¹ = a} = Nat.card Γ := by
  letI : MulAction Γ G :=
    { smul := fun γ x => f γ * x * (f γ)⁻¹
      one_smul := fun x => by
        show f 1 * x * (f 1)⁻¹ = x
        simp
      mul_smul := fun γ δ x => by
        show f (γ * δ) * x * (f (γ * δ))⁻¹ = f γ * (f δ * x * (f δ)⁻¹) * (f γ)⁻¹
        simp [mul_assoc] }
  have h : (MulAction.orbit Γ a).ncard * Nat.card (MulAction.stabilizer Γ a) = Nat.card Γ := by
    rw [← MulAction.index_stabilizer, mul_comm]
    exact Subgroup.card_mul_index _
  exact h

theorem ncard_conjOrbit_mul_card (H : Subgroup G) (a : G) :
    (conjOrbit H a).ncard * Nat.card (H ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) =
      Nat.card H := by
  have h := ncard_range_conj_mul_card H.subtype a
  have hrange : conjOrbit H a = Set.range fun γ : H => H.subtype γ * a * (H.subtype γ)⁻¹ := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ, γ.2, rfl⟩
  have key : ∀ x : G, x ∈ Subgroup.centralizer ({a} : Set G) ↔ x * a * x⁻¹ = a := fun x => by
    rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hcard : Nat.card {γ : H // H.subtype γ * a * (H.subtype γ)⁻¹ = a} =
      Nat.card (H ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
    Nat.card_congr
      { toFun := fun γ => ⟨γ.1, Subgroup.mem_inf.2 ⟨γ.1.2, (key _).2 γ.2⟩⟩
        invFun := fun t =>
          ⟨⟨t.1, (Subgroup.mem_inf.1 t.2).1⟩, (key _).1 (Subgroup.mem_inf.1 t.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hrange, ← hcard]
  exact h

end ConjOrbit

theorem no_extra_fusion {G : Type*} [Group G] [Finite G]
    (N E P : Subgroup G) (e y₁ : G)
    (hNE : ∀ n ∈ N, ∀ x ∈ E, n * x * n⁻¹ ∈ E)
    (hPE : ∀ p ∈ P, ∀ x ∈ E, p * x * p⁻¹ ∈ E)
    (hP : Nat.card P = 2 ^ 11) (hG : ¬ 2 ^ 12 ∣ Nat.card G)
    (heE : e ∈ E) (hN : Nat.card N = 3072)
    (hCe : Nat.card (N ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) = 384)
    (hCy : Nat.card (N ⊓ Subgroup.centralizer ({y₁} : Set G) : Subgroup G) = 128)
    (hCL : ∀ g : G, g * e = e * g → (∀ x ∈ E, g * x * g⁻¹ ∈ E) → g ∈ N)
    (hX : ∀ y ∈ E, IsConj e y →
      (∃ n ∈ N, n * e * n⁻¹ = y) ∨ (∃ n ∈ N, n * y₁ * n⁻¹ = y)) : False := by
  obtain ⟨L, hNL, hPL, hLE⟩ : ∃ L : Subgroup G, N ≤ L ∧ P ≤ L ∧
      ∀ l ∈ L, ∀ x ∈ E, l * x * l⁻¹ ∈ E :=
    ⟨Subgroup.normalizer (E : Set G), Subgroup.le_normalizer_iff.2 hNE,
      Subgroup.le_normalizer_iff.2 hPE, Subgroup.le_normalizer_iff.1 le_rfl⟩
  have hCL' : L ⊓ Subgroup.centralizer ({e} : Set G) = N ⊓ Subgroup.centralizer ({e} : Set G) := by
    refine le_antisymm (fun g hg => ?_) (inf_le_inf_right _ hNL)
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hg
    exact Subgroup.mem_inf.2
      ⟨hCL g hg.2 (hLE g hg.1), Subgroup.mem_centralizer_singleton_iff.2 hg.2⟩
  have hLcard := ncard_conjOrbit_mul_card L e
  rw [hCL', hCe] at hLcard
  have hNe := ncard_conjOrbit_mul_card N e
  rw [hCe, hN] at hNe
  have hNy := ncard_conjOrbit_mul_card N y₁
  rw [hCy, hN] at hNy
  have h8 : (conjOrbit N e).ncard = 8 := by omega
  have h24 : (conjOrbit N y₁).ncard = 24 := by omega
  have h2L : 2 ^ 11 ∣ Nat.card L := by
    have := Subgroup.card_dvd_of_le hPL
    rwa [hP] at this
  have hLG : Nat.card L ∣ Nat.card G := Subgroup.card_subgroup_dvd_card L
  have hNK : conjOrbit N e ⊆ conjOrbit L e := conjOrbit_mono hNL e
  by_cases hcase : conjOrbit L e ⊆ conjOrbit N e
  ·
    have hK : (conjOrbit L e).ncard = 8 := by
      have h1 := Set.ncard_le_ncard hcase
      have h2 := Set.ncard_le_ncard hNK
      omega
    rw [hK] at hLcard
    omega
  ·
    obtain ⟨y, hyK, hyN⟩ := Set.not_subset.1 hcase
    have hyE : y ∈ E := by
      obtain ⟨l, hl, hly⟩ := hyK
      exact hly ▸ hLE l hl e heE
    have hyconj : IsConj e y := by
      obtain ⟨l, -, hly⟩ := hyK
      exact isConj_iff.2 ⟨l, hly⟩
    have hy₁ : y ∈ conjOrbit N y₁ := by
      rcases hX y hyE hyconj with ⟨n, hn, hny⟩ | ⟨n, hn, hny⟩
      · exact absurd ⟨n, hn, hny⟩ hyN
      · exact ⟨n, hn, hny⟩
    have hNy' : conjOrbit N y₁ ⊆ conjOrbit L e := by
      rw [← conjOrbit_eq_of_mem hy₁, ← conjOrbit_eq_of_mem hyK]
      exact conjOrbit_mono hNL y
    have hunion : conjOrbit L e = conjOrbit N e ∪ conjOrbit N y₁ := by
      refine Set.Subset.antisymm (fun z hz => ?_) (Set.union_subset hNK hNy')
      obtain ⟨m, hm, hmz⟩ := hz
      have hzE : z ∈ E := hmz ▸ hLE m hm e heE
      rcases hX z hzE (isConj_iff.2 ⟨m, hmz⟩) with ⟨n, hn, hnz⟩ | ⟨n, hn, hnz⟩
      · exact Or.inl ⟨n, hn, hnz⟩
      · exact Or.inr ⟨n, hn, hnz⟩
    have hdisj : Disjoint (conjOrbit N e) (conjOrbit N y₁) := by
      rw [Set.disjoint_left]
      intro z hz hz'
      have heq := (conjOrbit_eq_of_mem hz).symm.trans (conjOrbit_eq_of_mem hz')
      rw [heq] at h8
      omega
    have hK : (conjOrbit L e).ncard = 32 := by
      rw [hunion, Set.ncard_union_eq hdisj, h8, h24]
    rw [hK] at hLcard
    exact hG (Dvd.dvd.trans ⟨3, by omega⟩ hLG)

end CFSG.EvenSporadicStandard.M12Std.Yosh
