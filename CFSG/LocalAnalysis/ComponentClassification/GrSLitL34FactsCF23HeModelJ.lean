module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeModel
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover
public import CFSG.Sporadic.HeldB.InnerClass

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem hj_isSimpleGroup_S : IsSimpleGroup ↥PSL3Four.S := by
  obtain ⟨θ, -⟩ := PSL3Four.exact_model.2.1
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) PSL3Four.F4) :=
    BenderSuzuki.External.huppert_II_6_13 3 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  exact (θ.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3
      PSL3Four.F4))).isSimpleGroup

theorem pow_eq_pow_mod_two {g : Equiv.Perm (Fin 8330)} (hg : g * g = 1) (p : ℕ) :
    g ^ p = g ^ (p % 2) := by
  conv_lhs => rw [← Nat.div_add_mod p 2, pow_add, pow_mul, sq, hg, one_pow, one_mul]

section Sigma


theorem sigma_mem_S (c : Cover) : sigma c ∈ PSL3Four.S := range_sigma ▸ ⟨c, rfl⟩

theorem map_sigma_cases {N : Subgroup Cover} (hN : N.Normal) :
    N ≤ sigma.ker ∨ ∀ c : Cover, ∃ n ∈ N, c⁻¹ * n ∈ sigma.ker := by
  have := hj_isSimpleGroup_S
  set K : Subgroup ↥PSL3Four.S := (N.map sigma).subgroupOf PSL3Four.S with hK
  have hKn : K.Normal := by
    constructor
    intro k hk s
    rw [mem_subgroupOf] at hk ⊢
    obtain ⟨n, hn, hnk⟩ := hk
    have hs : (s : Equiv.Perm (Fin 42)) ∈ sigma.range := by
      rw [range_sigma]
      exact s.2
    obtain ⟨c, hc⟩ := hs
    refine ⟨c * n * c⁻¹, hN.conj_mem n hn c, ?_⟩
    simp only [map_mul, map_inv, hc, hnk, Subgroup.coe_mul, Subgroup.coe_inv]
  have := hKn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hbot | htop
  · left
    intro n hn
    have h1 : (⟨sigma n, sigma_mem_S n⟩ : ↥PSL3Four.S) ∈ K := by
      rw [mem_subgroupOf]
      exact ⟨n, hn, rfl⟩
    rw [hbot, mem_bot] at h1
    exact congrArg Subtype.val h1
  · right
    intro c
    have h1 : (⟨sigma c, sigma_mem_S c⟩ : ↥PSL3Four.S) ∈ K := htop ▸ mem_top _
    rw [mem_subgroupOf] at h1
    obtain ⟨n, hn, hnc⟩ := h1
    exact ⟨n, hn, by rw [MonoidHom.mem_ker, map_mul, map_inv, hnc, inv_mul_cancel]⟩

theorem card_cover : Nat.card Cover = 967680 := by
  have h := Subgroup.card_ker_mul_card_range sigma
  rw [range_sigma, PSL3Four.card_S, ← range_zHom,
    ← Nat.card_congr (MonoidHom.ofInjective zHom_injective).toEquiv] at h
  have hcard : Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ×
      Multiplicative (ZMod 3)) = 48 := by simp
  rw [hcard] at h
  omega

end Sigma

section Ker


theorem hjAP_eq : hjLam (PresentedGroup.of 0) = hjAP := by
  rw [hjLam_of]
  rfl

theorem hjBP_eq : hjLam (PresentedGroup.of 1) = hjBP := by
  rw [hjLam_of]
  rfl

theorem ker_hjLam_le_ker_sigma :
    hjLam.ker ≤ sigma.ker := by
  rcases map_sigma_cases hjLam.normal_ker with h | hall
  · exact h
  exfalso
  obtain ⟨n₀, hn₀, hz₀⟩ := hall (PresentedGroup.of 0)
  obtain ⟨n₁, hn₁, hz₁⟩ := hall (PresentedGroup.of 1)
  set z₀ := (PresentedGroup.of 0 : Cover)⁻¹ * n₀ with hz₀def
  set z₁' := (PresentedGroup.of 1 : Cover)⁻¹ * n₁ with hz₁def
  have e₀ : hjAP = hjLam z₀⁻¹ := by
    rw [← hjAP_eq, hz₀def, mul_inv_rev, inv_inv, map_mul, map_inv, (MonoidHom.mem_ker).1 hn₀,
      inv_one, one_mul]
  have e₁ : hjBP = hjLam z₁'⁻¹ := by
    rw [← hjBP_eq, hz₁def, mul_inv_rev, inv_inv, map_mul, map_inv, (MonoidHom.mem_ker).1 hn₁,
      inv_one, one_mul]
  have hc : z₀⁻¹ * z₁'⁻¹ = z₁'⁻¹ * z₀⁻¹ :=
    (mem_center_iff.1 (inv_mem (ker_sigma_le_center hz₀)) z₁'⁻¹).symm
  apply hjAB_ne
  rw [e₀, e₁, ← map_mul, hc, map_mul]


theorem hjZP_comm_t : hjZP * heGenPerm 0 = heGenPerm 0 * hjZP := by
  have h := congrArg hjLam (mem_center_iff.1 z₁_mem_center z₂)
  rw [map_mul, map_mul, hjLam_z₂] at h
  exact h.symm

theorem hjLam_zHom (d : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ×
    Multiplicative (ZMod 3)) :
    hjLam (zHom d) = hjZP ^ d.1.toAdd.val * heGenPerm 0 ^ d.2.1.toAdd.val := by
  rw [zHom_apply, map_mul, map_mul, map_pow, map_pow, map_pow, hjLam_z₂, hjLam_z₃, one_pow,
    mul_one]

theorem hjLam_zHom_eq_one_iff
    (d : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 3)) :
    hjLam (zHom d) = 1 ↔ d.1.toAdd.val % 2 = 0 ∧ d.2.1.toAdd.val % 2 = 0 := by
  have ht : heGenPerm 0 * heGenPerm 0 = 1 := by rw [← sq]; exact heGen0_sq
  rw [hjLam_zHom, pow_eq_pow_mod_two hjZP_mul_self, pow_eq_pow_mod_two ht]
  rcases Nat.mod_two_eq_zero_or_one d.1.toAdd.val with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one d.2.1.toAdd.val with h2 | h2 <;>
    simp only [h1, h2, pow_zero, pow_one, one_mul, mul_one, and_true, one_ne_zero, and_false,
      iff_false]
  · exact heA0_ne_one
  · exact hjZP_ne_one
  · intro h
    apply hjZP_ne_t
    calc hjZP = hjZP * heGenPerm 0 * heGenPerm 0 := by rw [mul_assoc, ht, mul_one]
      _ = heGenPerm 0 := by rw [h, one_mul]


theorem ker_hjLam_eq : hjLam.ker = (hjLam.comp zHom).ker.map zHom := by
  apply le_antisymm
  · intro c hc
    have hc' := ker_hjLam_le_ker_sigma hc
    rw [← range_zHom] at hc'
    obtain ⟨d, rfl⟩ := hc'
    exact ⟨d, hc, rfl⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact hd


theorem card_ker_hjLam : Nat.card hjLam.ker = 12 := by
  rw [ker_hjLam_eq, Subgroup.card_map_of_injective zHom_injective]
  have hset : ∀ d, d ∈ (hjLam.comp zHom).ker ↔
      (d.1.toAdd.val % 2 = 0 ∧ d.2.1.toAdd.val % 2 = 0) := fun d => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hjLam_zHom_eq_one_iff]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hset), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

theorem card_hjJ : Nat.card hjJ = 80640 := by
  have h := Subgroup.card_ker_mul_card_range hjLam
  rw [card_ker_hjLam, card_cover] at h
  rw [hjJ]
  omega

theorem index_hjJ :
    (hjJ.subgroupOf (centralizerIn heP (heGenPerm 0))).index = 2 := by
  have h := (hjJ.subgroupOf (centralizerIn heP (heGenPerm 0))).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hjJ_le).toEquiv, card_hjJ,
    card_heP_cent0] at h
  omega

end Ker

end CFSG.ComponentClassification.GSThmB.CF23L34
