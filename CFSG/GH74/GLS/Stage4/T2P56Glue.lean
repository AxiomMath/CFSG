module

public import CFSG.GH74.GLS.Stage4.T2P56Syl
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank

section Decomp

theorem exists_two_odd_decomp {G : Type*} [Group G] [Finite G] (c : G) :
    ∃ a b : G, c = a * b ∧ a * b = b * a ∧ TwoElt a ∧ Odd (orderOf b) ∧
      a ∈ Subgroup.zpowers c ∧ b ∈ Subgroup.zpowers c := by
  have hn : orderOf c ≠ 0 := (orderOf_pos c).ne'
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * ((2 ^ k : ℕ) : ℤ) + v * (m : ℤ) = 1 := by
    obtain ⟨u, v, h⟩ := Nat.isCoprime_iff_coprime.2 hcop
    exact ⟨u, v, by exact_mod_cast h⟩
  have hcn : c ^ (2 ^ k * m) = 1 := by rw [← hnm]; exact pow_orderOf_eq_one c
  have hcnz : ∀ w : ℤ, (c ^ (2 ^ k * m)) ^ w = 1 := fun w => by rw [hcn]; exact one_zpow w
  refine ⟨c ^ (v * (m : ℤ)), c ^ (u * ((2 ^ k : ℕ) : ℤ)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← zpow_add, add_comm, huv, zpow_one]
  · rw [← zpow_add, ← zpow_add, add_comm]
  · refine ⟨k, ?_⟩
    rw [← zpow_natCast, ← zpow_mul]
    have : v * (m : ℤ) * ((2 ^ k : ℕ) : ℤ) = ((2 ^ k * m : ℕ) : ℤ) * v := by push_cast; ring
    rw [this, zpow_mul, zpow_natCast]
    exact hcnz v
  · have h1 : (c ^ (u * ((2 ^ k : ℕ) : ℤ))) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : u * ((2 ^ k : ℕ) : ℤ) * (m : ℤ) = ((2 ^ k * m : ℕ) : ℤ) * u := by push_cast; ring
      rw [this, zpow_mul, zpow_natCast]
      exact hcnz u
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)
  · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _
  · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _

end Decomp

section Norm

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2Ctx_all_normK
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hLoc : Ch6Loc5 N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁)
    (hq₂ : N.q₂ = q₂) {c : G} (hc : c * z = z * c) :
    (∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁) ∧ (∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂) := by
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨a, b, hab, -, ha2, hbodd, haz, hbz⟩ := exists_two_odd_decomp c
  have hcomm : ∀ w : G, w ∈ Subgroup.zpowers c → w * z = z * w := by
    intro w hw
    obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact ((Commute.zpow_left (show Commute c z from hc) r)).eq
  have haz' : a * z = z * a := hcomm a haz
  have hbz' : b * z = z * b := hcomm b hbz
  have haC : a ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := twoElt_mem_residual haz' ha2
  obtain ⟨hn₁, hn₂⟩ := t2C_C₁_normalizes hRem hSet.comm
  obtain ⟨hb₁, hb₂⟩ := t2Ctx_odd_normK ctx hbz' hbodd
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have : c * x * c⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by rw [hab]; group
    rw [this]; exact hn₁ a haC _ (hb₁ x hx)
  · have : c * x * c⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by rw [hab]; group
    rw [this]; exact hn₂ a haC _ (hb₂ x hx)

end Norm

section Transport

theorem isLnEps_of_equiv {n : ℕ} {K K' : Type} [Group K] [Group K'] {ε : ℤ} {q : ℕ} (e : K ≃* K')
    (h : IsLnEps n K ε q) : IsLnEps n K' ε q := by
  rcases h with ⟨h1, F, i1, i2, hF, ⟨f⟩⟩ | ⟨h1, F, i1, i2, hF, ⟨f⟩⟩
  · exact Or.inl ⟨h1, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨h1, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩

theorem isSLnEps_of_equiv {n : ℕ} {K K' : Type} [Group K] [Group K'] {ε : ℤ} {q : ℕ} (e : K ≃* K')
    (h : IsSLnEps n K ε q) : IsSLnEps n K' ε q := by
  rcases h with ⟨h1, F, i1, i2, hF, ⟨f⟩⟩ | ⟨h1, F, i1, i2, hF, ⟨f⟩⟩
  · exact Or.inl ⟨h1, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨h1, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩

end Transport

section Star

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hstar_of_local (X : Subgroup G) {y z u : G} (hzX : z ∈ X) (huX : u ∈ X)
    (hXy : ∀ x ∈ X, x * y = y * x) (hXy' : ∀ g : G, g * y = y * g → g ∈ X)
    (hloc : ∀ B : Subgroup G, (∀ b ∈ B, b * y = y * b) →
      (∀ g : G, g * y = y * g → ∀ b ∈ B, g * b * g⁻¹ ∈ B) → Odd (Nat.card B) →
        ∀ b ∈ B, b * z = z * b → b * u = u * b)
    (N : Subgroup ↥X) (hN : Odd (Nat.card N)) :
    ∀ B : Subgroup ↥X, B.Normal → B ≤ N → ∀ b ∈ B,
      b * (⟨z, hzX⟩ : ↥X) = ⟨z, hzX⟩ * b → b * (⟨u, huX⟩ : ↥X) = ⟨u, huX⟩ * b := by
  intro B hBn hBN b hb hbz
  have hBodd : Odd (Nat.card ↥(B.map X.subtype)) := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact Odd.of_dvd_nat hN (Subgroup.card_dvd_of_le hBN)
  have := hloc (B.map X.subtype) (by rintro _ ⟨b', hb', rfl⟩; exact hXy _ b'.2)
    (by
      intro g hg _ ⟨b', hb', hb'e⟩
      refine ⟨⟨g, hXy' g hg⟩ * b' * ⟨g, hXy' g hg⟩⁻¹, hBn.conj_mem b' hb' _, ?_⟩
      rw [← hb'e]; rfl)
    hBodd (b : G) ⟨b, hb, rfl⟩ (congrArg Subtype.val hbz)
  exact Subtype.ext this

end Star

end CFSG.GH74.GLS.Stage4.Rest
