module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBNorm1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma48

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

theorem exists_mem_normalizer_sq_mem {X : Type*} [Group X] [Finite X] {W : Subgroup X}
    (hW2 : IsPGroup 2 W) (hWX : ¬ IsSylowOf 2 W ⊤) :
    ∃ y ∈ normalizer (W : Set X), y ∉ W ∧ y ^ 2 ∈ W ∧ IsPGroup 2 ↥(W ⊔ zpowers y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hWQ⟩ := exists_isSylowOf_ge hW2 (le_top : W ≤ ⊤)
  have hWQ' : W ≠ Q := fun h => hWX (h ▸ hQ)
  have hlt : W.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hWQ' (le_antisymm hWQ fun x hx => ?_)
    have : (⟨x, hx⟩ : Q) ∈ W.subgroupOf Q := h ▸ mem_top _
    exact this
  have : Group.IsNilpotent Q := hQ.isPGroup.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt
  obtain ⟨y₀, hy₀N, hy₀W⟩ := IsConcreteLE.exists_of_lt hnc
  have hy₀N' : (y₀ : X) ∈ normalizer (W : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact (mem_normalizer_iff.mp hy₀N ⟨x, hWQ hx⟩).mp (show (⟨x, hWQ hx⟩ : Q) ∈ W.subgroupOf Q
        from hx)
    · intro hx
      have hxQ : x ∈ Q := by
        have h1 : (y₀ : X)⁻¹ * (y₀ * x * (y₀ : X)⁻¹) * y₀ ∈ Q :=
          mul_mem (mul_mem (inv_mem y₀.2) (hWQ hx)) y₀.2
        rwa [show (y₀ : X)⁻¹ * (y₀ * x * (y₀ : X)⁻¹) * y₀ = x by group] at h1
      exact (mem_normalizer_iff.mp hy₀N ⟨x, hxQ⟩).mpr hx
  have hy₀W' : (y₀ : X) ∉ W := hy₀W
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ.isPGroup) y₀
  have hex : ∃ i : ℕ, (y₀ : X) ^ (2 ^ i) ∈ W := by
    refine ⟨k, ?_⟩
    have h : orderOf (y₀ : X) = 2 ^ k := by rw [Subgroup.orderOf_coe, hk]
    rw [← h, pow_orderOf_eq_one]
    exact one_mem _
  classical
  set i := Nat.find hex with hi
  have hiW : (y₀ : X) ^ (2 ^ i) ∈ W := Nat.find_spec hex
  have hi0 : i ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hiW
    exact hy₀W' hiW
  have hprev : (y₀ : X) ^ (2 ^ (i - 1)) ∉ W := Nat.find_min hex (by omega)
  refine ⟨(y₀ : X) ^ (2 ^ (i - 1)), pow_mem hy₀N' _, hprev, ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi0)]
    exact hiW
  · exact hQ.isPGroup.to_le (sup_le hWQ (zpowers_le.mpr (pow_mem y₀.2 _)))

theorem index_dvd_card_of_forall_stabilizer {G α : Type*} [Group G] [MulAction G α]
    [Finite α] {K : Subgroup G} (hK : ∀ a : α, MulAction.stabilizer G a = K) :
    K.index ∣ Nat.card α := by
  classical
  let Ω := MulAction.orbitRel.Quotient G α
  have e1 : α ≃ Σ ω : Ω, G ⧸ MulAction.stabilizer G ω.out :=
    MulAction.selfEquivSigmaOrbitsQuotientStabilizer G α
  have e2 : (Σ ω : Ω, G ⧸ MulAction.stabilizer G ω.out) ≃ Σ _ω : Ω, G ⧸ K :=
    Equiv.sigmaCongrRight fun ω => Subgroup.quotientEquivOfEq (hK ω.out)
  have e3 : (Σ _ω : Ω, G ⧸ K) ≃ Ω × (G ⧸ K) := Equiv.sigmaEquivProd _ _
  have : Finite Ω := Quotient.finite _
  rw [Nat.card_congr ((e1.trans e2).trans e3), Nat.card_prod]
  exact dvd_mul_left _ _

section CModZ

variable {G : Type*} [Group G]

@[expose] def cModZ (V : Subgroup G) : Subgroup G where
  carrier := {v | v ∈ V ∧ ∀ a ∈ ⁅V, V⁆, ⁅v, a⁆ ∈ zW V}
  mul_mem' := by
    rintro x y ⟨hxV, hx⟩ ⟨hyV, hy⟩
    refine ⟨mul_mem hxV hyV, fun a ha => ?_⟩
    have hya := hy a ha
    have hxa := hx a ha
    have hc : x * ⁅y, a⁆ * x⁻¹ = ⁅y, a⁆ := by
      have := mem_centralizer_iff.mp (mem_inf.mp hya).2 x hxV
      calc x * ⁅y, a⁆ * x⁻¹ = ⁅y, a⁆ * x * x⁻¹ := by rw [this]
        _ = ⁅y, a⁆ := by group
    have : ⁅x * y, a⁆ = (x * ⁅y, a⁆ * x⁻¹) * ⁅x, a⁆ := by
      simp only [commutatorElement_def]
      group
    rw [this, hc]
    exact mul_mem hya hxa
  one_mem' := ⟨one_mem V, fun a _ => by rw [commutatorElement_def]; simp⟩
  inv_mem' := by
    rintro x ⟨hxV, hx⟩
    refine ⟨inv_mem hxV, fun a ha => ?_⟩
    have hxa := hx a ha
    have hc : x⁻¹ * ⁅x, a⁆⁻¹ * x = ⁅x, a⁆⁻¹ := by
      have := mem_centralizer_iff.mp (mem_inf.mp (inv_mem hxa)).2 x⁻¹ (inv_mem hxV)
      calc x⁻¹ * ⁅x, a⁆⁻¹ * x = ⁅x, a⁆⁻¹ * x⁻¹ * x := by rw [this]
        _ = ⁅x, a⁆⁻¹ := by group
    have : ⁅x⁻¹, a⁆ = x⁻¹ * ⁅x, a⁆⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [this, hc]
    exact inv_mem hxa

theorem cModZ_le (V : Subgroup G) : cModZ V ≤ V := fun _ h => h.1

theorem conj_mem_cModZ {N V : Subgroup G} (hV : ∀ y ∈ N, ∀ x ∈ V, y * x * y⁻¹ ∈ V) :
    ∀ y ∈ N, ∀ x ∈ cModZ V, y * x * y⁻¹ ∈ cModZ V := by
  have hZ : ∀ y ∈ N, ∀ x ∈ zW V, y * x * y⁻¹ ∈ zW V :=
    conj_mem_inf' hV (conj_mem_centralizer' hV)
  have hD : ∀ y ∈ N, ∀ x ∈ ⁅V, V⁆, y * x * y⁻¹ ∈ ⁅V, V⁆ := conj_mem_commutator' hV hV
  intro y hy x ⟨hxV, hx⟩
  refine ⟨hV y hy x hxV, fun a ha => ?_⟩
  have ha' : y⁻¹ * a * y⁻¹⁻¹ ∈ ⁅V, V⁆ := hD y⁻¹ (inv_mem hy) a ha
  rw [inv_inv] at ha'
  have h1 := hZ y hy _ (hx _ ha')
  have : ⁅y * x * y⁻¹, a⁆ = y * ⁅x, y⁻¹ * a * y⁆ * y⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [this]
  exact h1

end CModZ

end CFSG.ComponentClassification.HarrisLit.EndB
