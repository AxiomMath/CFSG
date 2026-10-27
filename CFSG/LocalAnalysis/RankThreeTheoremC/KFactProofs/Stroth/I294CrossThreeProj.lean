module

public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open

theorem le_pRank_centralizer_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] {H : Subgroup (GL ι K)} {A : Type*} [Group A] {k : ℕ}
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ 3 = 1) (hA : Nat.card A = 3 ^ k)
    (φ : A →* GL ι K) (hφ : Function.Injective φ) (hH : ∀ a, φ a ∈ H)
    (hsc : ∀ a, φ a ∈ StatedScalars ι K → a = 1) (g : H)
    (hg : ∀ a, (g : GL ι K) * φ a = φ a * (g : GL ι K)) :
    k ≤ pRank 3 (Subgroup.centralizer
      ({(QuotientGroup.mk g : StatedProj H)} : Set (StatedProj H))) := by
  let ψ : A →* StatedProj H :=
    (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)).comp (φ.codRestrict H hH)
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ha
    exact (Subgroup.mem_bot).2 (hsc a ha)
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hcomm hpow hA ψ hψ ?_
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  show ψ a * (QuotientGroup.mk g : StatedProj H) = (QuotientGroup.mk g : StatedProj H) * ψ a
  show QuotientGroup.mk (φ.codRestrict H hH a) * (QuotientGroup.mk g : StatedProj H) =
    (QuotientGroup.mk g : StatedProj H) * QuotientGroup.mk (φ.codRestrict H hH a)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hg a).symm

theorem exists_lift_pow_three {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {H : Subgroup (GL ι K)} {N : ℕ} (hN : Nat.Coprime 3 N)
    (hZ : ∀ z ∈ (StatedScalars ι K).subgroupOf H, z ^ N = 1) {x : StatedProj H}
    (hx : x ^ 3 = 1) : ∃ g : H, g ^ 3 = 1 ∧ (QuotientGroup.mk g : StatedProj H) = x := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective x
  have h3 : g₀ ^ 3 ∈ (StatedScalars ι K).subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hx
  have hN' : (g₀ ^ 3) ^ N = 1 := hZ _ h3
  obtain ⟨N', -, hN'3⟩ := Nat.exists_mul_mod_eq_one_of_coprime hN.symm (by norm_num : 1 < 3)
  refine ⟨g₀ ^ (N * N'), ?_, ?_⟩
  · calc (g₀ ^ (N * N')) ^ 3 = ((g₀ ^ 3) ^ N) ^ N' := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring
      _ = 1 := by rw [hN', one_pow]
  · rw [QuotientGroup.mk_pow, pow_eq_pow_mod _ hx, hN'3, pow_one]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
