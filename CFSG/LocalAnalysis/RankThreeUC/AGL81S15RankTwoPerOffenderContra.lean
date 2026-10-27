module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderCount
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderFinish
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSemi
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerDef

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

private theorem exists_sq_one_conjAgree {G : Type*} [Group G] {L : Subgroup G} {b l : G} (hl : l ∈ L)
    (hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1) (hb : b * b = 1)
    (h : ConjAgree L b l) : ∃ l' ∈ L, ConjAgree L b l' ∧ l' * l' = 1 :=
  exists_involutory_lift hZ hb hl h

private theorem NatQuot.exists_rho_eq_of_conjAgree {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    [CharP F 2] {r : ℕ} (N : NatQuot ρ L F r) (hS : NatSchur N.Mat)
    (hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1)
    (hIcomm : ∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2)
      {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x})
    {k l : G} (hl : l ∈ L) (hk2 : k * k = 1) (hkI : ∀ v ∈ N.I, ρ k v ∈ N.I)
    (h : ConjAgree L k l) : ∃ l' ∈ L, ∀ v ∈ N.I, ρ k v = ρ l' v := by
  obtain ⟨l', hl', hconj, hl'2⟩ := exists_sq_one_conjAgree hl hZ hk2 h
  have hki : k * l'⁻¹ = l'⁻¹ * k := by
    have h2 : k * l'⁻¹ * k⁻¹ = l'⁻¹ := by
      calc k * l'⁻¹ * k⁻¹ = (k * l' * k⁻¹)⁻¹ := by group
        _ = l'⁻¹ := by rw [hconj.self hl']
    calc k * l'⁻¹ = (k * l'⁻¹ * k⁻¹) * k := by group
      _ = l'⁻¹ * k := by rw [h2]
  have hc_comm : ∀ x ∈ L, (l'⁻¹ * k) * x = x * (l'⁻¹ * k) := by
    intro x hx
    have hcx : (l'⁻¹ * k) * x * (l'⁻¹ * k)⁻¹ = x := by
      calc l'⁻¹ * k * x * (l'⁻¹ * k)⁻¹
          = l'⁻¹ * (k * x * k⁻¹) * l' := by group
        _ = l'⁻¹ * (l' * x * l'⁻¹) * l' := by rw [hconj x hx]
        _ = x := by group
    calc (l'⁻¹ * k) * x = ((l'⁻¹ * k) * x * (l'⁻¹ * k)⁻¹) * (l'⁻¹ * k) := by group
      _ = x * (l'⁻¹ * k) := by rw [hcx]
  have hcI : ∀ v ∈ N.I, ρ (l'⁻¹ * k) v ∈ N.I := by
    intro v hv
    have h := N.inv l'⁻¹ (L.inv_mem hl') (ρ k v) (hkI v hv)
    simpa only [map_mul, Module.End.mul_apply] using h
  have hcc : (l'⁻¹ * k) * (l'⁻¹ * k) = 1 := by
    calc l'⁻¹ * k * (l'⁻¹ * k) = l'⁻¹ * (k * l'⁻¹) * k := by group
      _ = l'⁻¹ * (l'⁻¹ * k) * k := by rw [hki]
      _ = (l'⁻¹ * l'⁻¹) * (k * k) := by group
      _ = (l' * l')⁻¹ * (k * k) := by rw [mul_inv_rev]
      _ = 1 := by rw [hl'2, hk2]; simp
  have hc2v : ∀ v ∈ N.I, ρ (l'⁻¹ * k) (ρ (l'⁻¹ * k) v) = v := by
    intro v hv
    rw [← Module.End.mul_apply, ← map_mul, hcc, map_one, Module.End.one_apply]
  have hfix := NatQuot.rho_eq_of_commute_sq N hS hIcomm (l'⁻¹ * k) hc_comm hcI hc2v
  refine ⟨l', hl', fun v hv => ?_⟩
  have hk_eq : k = l' * (l'⁻¹ * k) := by group
  rw [hk_eq, map_mul, Module.End.mul_apply, hfix v hv]

private theorem exists_index_two_complement {G : Type*} [Group G] [Finite G] {A K : Subgroup G}
    (hKA : K ≤ A) (hrel : K.relIndex A ≤ 2) (hne : ¬ A ≤ K) :
    ∃ a ∈ A, a ∉ K ∧ Nat.card A = 2 * Nat.card K ∧ ∀ g ∈ A, g ∈ K ∨ a * g ∈ K := by
  have hcard : K.relIndex A * Nat.card K = Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := K) (K := A)
    rwa [inf_eq_left.mpr hKA] at h
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hrel0 : K.relIndex A ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcard
    exact hApos.ne' hcard.symm
  have hrel1 : K.relIndex A ≠ 1 := fun h1 => hne (Subgroup.relIndex_eq_one.mp h1)
  have hrel2 : K.relIndex A = 2 := by omega
  obtain ⟨a, haA, haK, hgen'⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp hrel2
  refine ⟨a, haA, haK, ?_, ?_⟩
  · rw [← hcard, hrel2]
  · intro g hg
    rcases hgen' g hg with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem NatQuot.forall_conjAgree_of_bestOffender {G : Type} [Group G] [Finite G] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) G V}
    (hfaith : Function.Injective ρ) {L : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2]
    {n r : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (hr : 2 ≤ r) (hr6 : r ≤ 6)
    (N : NatQuot ρ L F r) (hperf : PerfStab N.Mat) (hS : NatSchur N.Mat) (hO : NatOut N.Mat)
    (hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1)
    (hIcomm : ∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2)
      {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x})
    {A : Subgroup G} (hbest : IsBestOffenderOn ρ A ⊤)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hAI : ∀ a ∈ A, ∀ v ∈ N.I, ρ a v ∈ N.I)
    (hrel : (innerPart L A).relIndex A ≤ 2) :
    ∀ a ∈ A, ∃ l ∈ L, ConjAgree L a l := by
  intro a ha
  by_contra hnot
  let K : Subgroup G := innerPart L A
  have hKA : K ≤ A := innerPart_le L A
  have hne : ¬ A ≤ K := by
    intro hAK
    have : a ∈ innerPart L A := hAK ha
    exact hnot (mem_innerPart.mp this).2
  obtain ⟨a', ha'A, ha'K, hidx, hgen⟩ := exists_index_two_complement hKA hrel hne
  have hB2 : ∀ b ∈ A, b * b = 1 := fun b hb =>
    hfaith (by
      rw [map_one]
      exact LinearMap.ext fun v => (hbest.1 b hb b hb).2 v Submodule.mem_top)
  have hIK : ∀ k ∈ K, ∀ v ∈ N.I, ρ k v ∈ N.I := fun k hk => hAI k (hKA hk)
  have hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v := by
    intro k hk
    obtain ⟨hkA, l, hl, hconj⟩ := mem_innerPart.mp hk
    exact NatQuot.exists_rho_eq_of_conjAgree N hS hZ hIcomm hl (hB2 k hkA) (hAI k hkA) hconj
  have hgN : ∀ l ∈ L, a' * l * a'⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp (hAN ha'A) l).mp hl
  have hgN' : ∀ l ∈ L, a'⁻¹ * l * a' ∈ L := by
    intro l hl
    have h := (Subgroup.mem_normalizer_iff.mp (hAN (A.inv_mem ha'A)) l).mp hl
    simpa using h
  have hgI : ∀ v ∈ N.I, ρ a' v ∈ N.I := hAI a' ha'A
  have hg2 : ∀ v ∈ N.I, ρ a' (ρ a' v) = v := fun v _ => rho_rho_eq_of_isBestOffenderOn hbest ha'A v
  obtain ⟨T, σ, hTπ, hT2, hTσ⟩ := NatQuot.exists_semilinear_psi N hS hgN hgN' hgI hg2
  by_cases hσ : ∃ c : F, σ c ≠ c
  · have hσ2 : ∀ c : F, σ (σ c) = c :=
      ringEquiv_involutive_of_semilinear_involution (by omega : 0 < r) T hT2 σ hTσ
    obtain ⟨hn2, E, hE, hEcomm, hEcard⟩ :=
      NatQuot.exists_elemAbelian_of_swap hn hF (by omega : 0 < r) N hperf hbest hKA ha'A hgen
        hidx hIK (hAI a' ha'A) hKL hσ T hTσ hTπ
    have hF4 : Nat.card F = 4 := by rw [hF, hn2]; norm_num
    have hle : Nat.card E ≤ 2 ^ (r ^ 2 / 4) :=
      card_le_of_elemAbelian_commute_semilinear hF4 hσ hσ2 T hTσ hT2 E hE hEcomm
    have hp : 2 ^ (2 * r - 2) ≤ 2 ^ (r ^ 2 / 4) := hEcard.trans hle
    have hexp : 2 * r - 2 ≤ r ^ 2 / 4 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hp
    interval_cases r <;> norm_num at hexp
  · have hσ' : ∀ c : F, σ c = c := by
      intro c
      by_contra hc
      exact hσ ⟨c, hc⟩
    have hTlin : ∀ (c : F) (u : Fin r → F), T (c • u) = c • T u := by
      intro c u
      rw [hTσ, hσ' c]
    obtain ⟨l₀, hl₀, hAgree⟩ :=
      NatQuot.acts_as_L_of_linear N hO hIcomm hgN hgI hg2 T hTπ hTlin
    exact ha'K (show a' ∈ K from mem_innerPart.mpr ⟨ha'A, l₀, hl₀, hAgree.2⟩)

end CFSG.LocalAnalysis.RankThreeUC.S15

end
