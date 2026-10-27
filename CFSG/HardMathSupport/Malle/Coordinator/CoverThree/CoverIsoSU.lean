module

public import CFSG.GH74.GLS.LU.Local.L3Cover
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.HopfCompat
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThree

open CFSG.GH74.GLS.LU.Local CFSG.RankThree.PerfectCover CFSG.Assembly.LowTwoRank

theorem exists_mulEquiv_su3_of_cover_compat
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {p n : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p ^ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = (p ^ n) ^ 2)
    (h9 : 9 ∣ p ^ n + 1)
    (ρ : K →* StatedProj (StatedSU 3 (p ^ n) F)) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.center K) (hz : 3 ∣ Nat.card (Subgroup.center K)) :
    ∃ ψ : ↥(StatedSU 3 (p ^ n) F) ≃* K, ∀ g, ρ (ψ g) =
      QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ n) F)) g := by
  classical
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at h5
    · exact hpos
  have : Fact p.Prime := ⟨hp⟩
  have hcardM := card_hopfMultiplier_psu_three hGA
    (lieModel_psu_three hp h5 hF (MulEquiv.refl (StatedProj (StatedSU 3 (p ^ n) F))))
  have : Finite (hopfMultiplier (StatedProj (StatedSU 3 (p ^ n) F))) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcardM]
      exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
  have hS₀ : Group.IsPerfect (StatedSU 3 (p ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF le_rfl (fun h => by
      simp only [Prod.mk.injEq, true_and] at h
      omega)
  let p₀ : ↥(StatedSU 3 (p ^ n) F) →* StatedProj (StatedSU 3 (p ^ n) F) :=
    QuotientGroup.mk' _
  have hp₀ : Function.Surjective p₀ := QuotientGroup.mk'_surjective _
  have hk₀ : p₀.ker = (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ n) F) :=
    QuotientGroup.ker_mk' _
  have hk₀c : p₀.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ n) F) := by
    rw [hk₀]
    exact CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 3 (p ^ n)
  have hcardk : Nat.card p₀.ker = 3 := by
    rw [hk₀, card_scalars_statedSU_three hp hn hF]
    exact Nat.gcd_eq_left (dvd_trans (by norm_num : 3 ∣ 9) h9)
  obtain ⟨α, hα, hαρ⟩ := exists_surjective_compat_of_card_hopfMultiplier_le hS₀ inferInstance p₀
    hp₀ hk₀c ρ hρ hker.le (by rw [hcardM, hcardk]; exact Nat.gcd_le_left _ (by norm_num))
  have hρα : Function.Surjective (ρ.comp α) := hρ.comp hα
  have hNcard : Nat.card (ρ.comp α).ker = 3 := by
    have h1 := (ρ.comp α).ker.card_mul_index
    have h2 := p₀.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hρα, Subgroup.card_top] at h1
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hp₀, Subgroup.card_top] at h2
    have hpos : 0 < Nat.card (StatedProj (StatedSU 3 (p ^ n) F)) := Nat.card_pos
    have h3 : Nat.card (ρ.comp α).ker * Nat.card (StatedProj (StatedSU 3 (p ^ n) F)) =
        3 * Nat.card (StatedProj (StatedSU 3 (p ^ n) F)) := by rw [h1, ← h2, hcardk]
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  have hkerle : α.ker ≤ (ρ.comp α).ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  have hbot : α.ker = ⊥ := by
    by_contra hne
    have hdvd : Nat.card α.ker ∣ 3 := by
      have := Subgroup.card_dvd_of_le hkerle
      rwa [hNcard] at this
    have hne1 : Nat.card α.ker ≠ 1 := fun h => hne ((Subgroup.card_eq_one).mp h)
    have h3 : Nat.card α.ker = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne1
    have hker_eq : α.ker = (ρ.comp α).ker :=
      Subgroup.eq_of_le_of_card_ge hkerle (by rw [h3, hNcard])
    have hZ : Subgroup.center K = ⊥ := by
      rw [eq_bot_iff]
      intro z hzK
      obtain ⟨g, rfl⟩ := hα z
      have h1 : ρ (α g) = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hzK
      have : g ∈ α.ker := hker_eq ▸ (MonoidHom.mem_ker.mpr (by simpa using h1))
      rw [MonoidHom.mem_ker.mp this]
      exact Subgroup.one_mem _
    rw [hZ] at hz
    simp at hz
  exact ⟨MulEquiv.ofBijective α ⟨(MonoidHom.ker_eq_bot_iff α).mp hbot, hα⟩, hαρ⟩


theorem exists_mulEquiv_su3_of_cover
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {p n : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p ^ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = (p ^ n) ^ 2)
    (h9 : 9 ∣ p ^ n + 1)
    (ρ : K →* StatedProj (StatedSU 3 (p ^ n) F)) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.center K) (hz : 3 ∣ Nat.card (Subgroup.center K)) :
    Nonempty (↥(StatedSU 3 (p ^ n) F) ≃* K) := by
  obtain ⟨ψ, -⟩ := exists_mulEquiv_su3_of_cover_compat hGA hp h5 hF h9 ρ hρ hker hz
  exact ⟨ψ⟩

end CFSG.HardMathSupport.Malle.Coordinator.CoverThree
