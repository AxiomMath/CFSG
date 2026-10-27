module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma48
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools

namespace L415

theorem card_le_of_fiber {G β : Type*} [Group G] [Finite G] [DecidableEq β] {A K : Subgroup G}
    (f : G → β) (hf : ∀ a ∈ A, ∀ a' ∈ A, f a = f a' → a⁻¹ * a' ∈ K) (s : Finset β)
    (hs : ∀ a ∈ A, f a ∈ s) : Nat.card A ≤ Nat.card ↥(A ⊓ K) * s.card := by
  classical
  have : Fintype ↥A := Fintype.ofFinite _
  set g : ↥A → β := fun a => f a with hg
  have : Fintype ↥((A ⊓ K : Subgroup G) : Set G) := Fintype.ofFinite _
  have hcardAK : ((((A ⊓ K : Subgroup G) : Set G)).toFinset).card = Nat.card ↥(A ⊓ K) := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    rfl
  have hfib : ∀ b ∈ (Finset.univ : Finset ↥A).image g,
      ((Finset.univ : Finset ↥A).filter fun a => g a = b).card ≤ Nat.card ↥(A ⊓ K) := by
    intro b hb
    obtain ⟨a₀, -, ha₀⟩ := Finset.mem_image.mp hb
    rw [← hcardAK]
    refine Finset.card_le_card_of_injOn (fun a : ↥A => (a₀ : G)⁻¹ * a) ?_ ?_
    · intro a ha
      have ha' : g a = b := (Finset.mem_filter.mp ha).2
      rw [Finset.mem_coe, Set.mem_toFinset, SetLike.mem_coe]
      exact mem_inf.mpr ⟨mul_mem (inv_mem a₀.2) a.2, hf a₀ a₀.2 a a.2 (ha₀.trans ha'.symm)⟩
    · intro a _ a' _ h
      exact Subtype.ext (mul_left_cancel h)
  have h1 := Finset.card_le_mul_card_image (Finset.univ : Finset ↥A) _ hfib
  have h2 : ((Finset.univ : Finset ↥A).image g).card ≤ s.card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    exact hs a a.2
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  calc Nat.card A ≤ Nat.card ↥(A ⊓ K) * ((Finset.univ : Finset ↥A).image g).card := h1
    _ ≤ Nat.card ↥(A ⊓ K) * s.card := Nat.mul_le_mul_left _ h2

theorem card_le_of_commutator {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {t z : G} (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    (hc : ∀ a ∈ A, a⁻¹ * (t * a * t⁻¹) = 1 ∨ a⁻¹ * (t * a * t⁻¹) = z) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ centralizer {t}) := by
  classical
  have h1 := card_le_of_fiber (A := A) (K := centralizer {t})
    (fun a => a⁻¹ * (t * a * t⁻¹)) (fun a ha a' ha' h => by
      have hta := htA a ha
      have h2 : t * a' * t⁻¹ = a' * a⁻¹ * (t * a * t⁻¹) := by
        calc t * a' * t⁻¹ = a' * (a'⁻¹ * (t * a' * t⁻¹)) := by group
          _ = a' * (a⁻¹ * (t * a * t⁻¹)) := by rw [← h]
          _ = a' * a⁻¹ * (t * a * t⁻¹) := by group
      have h3 : (t * a * t⁻¹)⁻¹ * (a' * a⁻¹) * (t * a * t⁻¹) = a' * a⁻¹ := by
        have := hAc _ (inv_mem hta) _ (mul_mem ha' (inv_mem ha))
        calc (t * a * t⁻¹)⁻¹ * (a' * a⁻¹) * (t * a * t⁻¹) =
            (a' * a⁻¹) * (t * a * t⁻¹)⁻¹ * (t * a * t⁻¹) := by rw [this]
          _ = a' * a⁻¹ := by group
      have h4 : a⁻¹ * a' = a' * a⁻¹ := hAc _ (inv_mem ha) _ ha'
      have h5 : t * (a⁻¹ * a') * t⁻¹ = a⁻¹ * a' := by
        calc t * (a⁻¹ * a') * t⁻¹ = (t * a * t⁻¹)⁻¹ * (t * a' * t⁻¹) := by group
          _ = (t * a * t⁻¹)⁻¹ * (a' * a⁻¹ * (t * a * t⁻¹)) := by rw [h2]
          _ = (t * a * t⁻¹)⁻¹ * (a' * a⁻¹) * (t * a * t⁻¹) := by group
          _ = a' * a⁻¹ := h3
          _ = a⁻¹ * a' := h4.symm
      rw [mem_centralizer_singleton_iff]
      calc a⁻¹ * a' * t = (t * (a⁻¹ * a') * t⁻¹) * t := by rw [h5]
        _ = t * (a⁻¹ * a') := by group)
    ({1, z} : Finset G) (fun a ha => by
      rcases hc a ha with h | h <;> simp [h])
  calc Nat.card A ≤ Nat.card ↥(A ⊓ centralizer {t}) * ({1, z} : Finset G).card := h1
    _ ≤ Nat.card ↥(A ⊓ centralizer {t}) * 2 := Nat.mul_le_mul_left _ Finset.card_le_two
    _ = 2 * Nat.card ↥(A ⊓ centralizer {t}) := mul_comm _ _

theorem exists_normal_four {G : Type*} [Group G] [Finite G] {P Y : Subgroup G}
    (hP : IsPGroup 2 P) (hYP : Y ≤ P) (hYn : ∀ g ∈ P, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) {z : G}
    (hzc : ∀ g ∈ P, g * z = z * g) (hYz : ¬ Y ≤ zpowers z) :
    ∃ e ∈ Y, e ∉ zpowers z ∧ ∀ g ∈ P, g * e * g⁻¹ * e⁻¹ ∈ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (zpowers z).subgroupOf P with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ zpowers z := hn
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn'
    have hgz : Commute (g : G) z := hzc g g.2
    show ((g * n * g⁻¹ : ↥P) : G) ∈ zpowers z
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hk, (hgz.zpow_right k).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers z) k⟩
  have hG' : IsPGroup 2 (↥P ⧸ N) := hP.to_quotient N
  have : Group.IsNilpotent (↥P ⧸ N) := hG'.isNilpotent
  set Yb := (Y.subgroupOf P).map (QuotientGroup.mk' N) with hYb
  have hYbn : Yb.Normal := by
    have hYn' : (Y.subgroupOf P).Normal := ⟨fun y hy g => hYn g g.2 y hy⟩
    exact hYn'.map _ (QuotientGroup.mk'_surjective N)
  have hYb1 : Yb ≠ ⊥ := by
    intro h1
    apply hYz
    intro y hy
    have h2 : QuotientGroup.mk' N (⟨y, hYP hy⟩ : ↥P) ∈ Yb := ⟨⟨y, hYP hy⟩, hy, rfl⟩
    rw [h1, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  obtain ⟨⟨eb, heY, heZ⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hYb1)
  obtain ⟨e', he'Y, rfl⟩ := heY
  refine ⟨e', he'Y, fun h1 => he1 ?_, fun g hg => ?_⟩
  · apply Subtype.ext
    show QuotientGroup.mk' N e' = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h1
  · have h2 := (mem_center_iff.mp heZ) (QuotientGroup.mk' N ⟨g, hg⟩)
    have h3 : QuotientGroup.mk' N (⟨g, hg⟩ * e' * (⟨g, hg⟩)⁻¹ * e'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3

end L415

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem le_X_of_elem_centralizer [Finite X] (hσ : Setup42 h hS w z) {F : Subgroup X}
    (hFt : F ≤ centralizer {t}) (hF2 : ∀ x ∈ F, x ^ 2 = 1)
    (hFT : ∀ g ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w, ∀ x ∈ F, g * x * g⁻¹ ∈ F) :
    F ≤ closure {t, w ^ (orderOf w / 2), z} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFp : IsPGroup 2 F := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hF2 x x.2)⟩
  have hTp : IsPGroup 2 ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) := hS.isPGroup.to_le hσ.T_le
  have hTN : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ normalizer (F : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hFT g hg x hx
    · intro hx
      have h1 := hFT g⁻¹ (inv_mem hg) _ hx
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1
  have hsup := hFp.to_sup_of_normal_left' hTp hTN
  have hle : F ⊔ (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ≤ centralizer {t} :=
    sup_le hFt (hσ.T_le.trans hS.le)
  obtain ⟨S', hS', hle'⟩ := exists_isSylowOf_ge hsup hle
  have h1 := (hσ.sylow_transport hS' (le_sup_right.trans hle')).2.2.2
  exact h1 F (le_sup_left.trans hle')
    (fun g hg x hx => hFT g (mem_sup_left (mem_sup_right hg)) x hx) hF2

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
