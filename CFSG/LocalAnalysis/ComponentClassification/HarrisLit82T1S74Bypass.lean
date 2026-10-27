module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup

section Bypass

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem le_pPrimeCore_of_normal_of_odd {N : Subgroup Y} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ pPrimeCore 2 Y :=
  le_sSup ⟨hN, Nat.coprime_two_left.mpr hodd⟩

theorem le_pPrimeCore_of_sup_eq_top {C₀ K₀ : Subgroup Y} (hY : pPrimeCore 2 Y ⊔ C₀ = ⊤)
    (hK₀ : ∀ c ∈ C₀, ∀ k ∈ K₀, c * k * c⁻¹ ∈ K₀) (hodd : Odd (Nat.card K₀)) :
    K₀ ≤ pPrimeCore 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (K₀.map (QuotientGroup.mk' (pPrimeCore 2 Y))).Normal := by
    constructor
    rintro _ ⟨k, hk, rfl⟩ g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 Y) g
    have hy : y ∈ ((pPrimeCore 2 Y ⊔ C₀ : Subgroup Y) : Set Y) := by
      rw [hY]
      exact mem_top y
    rw [normal_mul] at hy
    obtain ⟨o, ho, c, hc, rfl⟩ := hy
    refine ⟨c * k * c⁻¹, hK₀ c hc k hk, ?_⟩
    have hπo : QuotientGroup.mk' (pPrimeCore 2 Y) o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    simp only [map_mul, map_inv, hπo, one_mul]
  have hodd' : Odd (Nat.card (K₀.map (QuotientGroup.mk' (pPrimeCore 2 Y)))) :=
    Odd.of_dvd_nat hodd (card_map_dvd K₀ _)
  have hle := le_pPrimeCore_of_normal_of_odd hnorm hodd'
  rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2, le_bot_iff, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] at hle
  exact hle

theorem sup_eq_top_of_sup_eq_top {C₀ K₀ M : Subgroup Y} (hY : pPrimeCore 2 Y ⊔ C₀ = ⊤)
    (hK₀ : ∀ c ∈ C₀, ∀ k ∈ K₀, c * k * c⁻¹ ∈ K₀) (hodd : Odd (Nat.card K₀))
    (hC₀ : C₀ ≤ K₀ ⊔ M) : pPrimeCore 2 Y ⊔ M = ⊤ := by
  have hK := le_pPrimeCore_of_sup_eq_top hY hK₀ hodd
  rw [eq_top_iff, ← hY]
  exact sup_le le_sup_left (hC₀.trans (sup_le (hK.trans le_sup_left) le_sup_right))

end Bypass

theorem exists_conj_of_sylow_le {G : Type} [Group G] [Finite G] {z : G} {L : Subgroup G}
    (hLH : L ≤ centralizer ({z} : Set G))
    (hconj : ∀ x ∈ centralizer ({z} : Set G), (∃ g : G, g * z * g⁻¹ = x) ↔
      (x ∈ L ∧ orderOf x = 2))
    (S : Sylow 2 G) (hSL : (S : Subgroup G) ≤ L) {x : G} (hx : orderOf x = 2) :
    ∃ g : G, g * z * g⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨T, hQT⟩ := hQ.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S T
  have h := hQT (mem_zpowers x)
  rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at h
  have hy : g⁻¹ * x * g ∈ (S : Subgroup G) := by
    simpa [MulAut.smul_def, mul_assoc] using h
  have hyL := hSL hy
  have hyo : orderOf (g⁻¹ * x * g) = 2 := by
    have : g⁻¹ * x * g = MulAut.conj g⁻¹ x := by
      rw [MulAut.conj_apply, inv_inv]
    rw [this, MulEquiv.orderOf_eq, hx]
  obtain ⟨h₁, hh₁⟩ := (hconj _ (hLH hyL)).mpr ⟨hyL, hyo⟩
  refine ⟨g * h₁, ?_⟩
  calc g * h₁ * z * (g * h₁)⁻¹ = g * (h₁ * z * h₁⁻¹) * g⁻¹ := by group
    _ = x := by rw [hh₁]; group

end CFSG.ComponentClassification.HarrisLit.T1.S74
