module

public import CFSG.Open.RankThreeDefs
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

private theorem finish65_fusionIsSylowIn_conj {G : Type} [Group G] {f : ℕ} {S O : Subgroup G}
    (hS : fusionIsSylowIn f S O) {h : G} (hh : h ∈ normalizer (O : Set G)) :
    fusionIsSylowIn f (S.map (MulAut.conj h).toMonoidHom) O := by
  obtain ⟨hSO, hSp, hmax⟩ := hS
  refine ⟨?_, hSp.map _, fun P hPO hPp hTP => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (mem_normalizer_iff.mp hh s).mp (hSO hs)
  · have hh' : h⁻¹ ∈ normalizer (O : Set G) := inv_mem hh
    have h1 : S ≤ P.map (MulAut.conj h⁻¹).toMonoidHom := fun s hs =>
      ⟨h * s * h⁻¹, hTP ⟨s, hs, rfl⟩, by simp [mul_assoc]⟩
    have h2 : P.map (MulAut.conj h⁻¹).toMonoidHom ≤ O := by
      rintro _ ⟨p, hp, rfl⟩
      exact (mem_normalizer_iff.mp hh' p).mp (hPO hp)
    have h3 := hmax _ h2 (hPp.map _) h1
    refine le_antisymm (fun x hx => ?_) hTP
    have hx' : h⁻¹ * x * h ∈ S := by
      rw [← h3]
      exact ⟨x, hx, by simp⟩
    exact ⟨h⁻¹ * x * h, hx', by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem finish65_mem_normalizer_of_map_eq {G : Type} [Group G] {S : Subgroup G} {c h : G}
    (hTc : S.map (MulAut.conj h).toMonoidHom = S.map (MulAut.conj c).toMonoidHom) :
    c⁻¹ * h ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx1 : h * x * h⁻¹ ∈ S.map (MulAut.conj c).toMonoidHom := by
      rw [← hTc]
      exact ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hsx⟩ := hx1
    have hsx' : c * s * c⁻¹ = h * x * h⁻¹ := hsx
    have : c⁻¹ * h * x * (c⁻¹ * h)⁻¹ = s := by
      calc c⁻¹ * h * x * (c⁻¹ * h)⁻¹ = c⁻¹ * (h * x * h⁻¹) * c := by group
        _ = c⁻¹ * (c * s * c⁻¹) * c := by rw [hsx']
        _ = s := by group
    rw [this]
    exact hs
  · intro hx
    have hx1 : h * x * h⁻¹ ∈ S.map (MulAut.conj c).toMonoidHom :=
      ⟨c⁻¹ * h * x * (c⁻¹ * h)⁻¹, hx, by
        show c * (c⁻¹ * h * x * (c⁻¹ * h)⁻¹) * c⁻¹ = h * x * h⁻¹
        group⟩
    rw [← hTc] at hx1
    obtain ⟨s, hs, hsx⟩ := hx1
    have hsx' : h * s * h⁻¹ = h * x * h⁻¹ := hsx
    have : s = x := mul_left_cancel (mul_right_cancel hsx')
    rwa [← this]

private theorem finish65_le_of_normalizer_le {G : Type} [Group G] [Finite G] {M H O S : Subgroup G}
    {f : ℕ} (hf : f.Prime) (hO3 : ¬ 3 ∣ Nat.card O) (hHO : H ≤ normalizer (O : Set G))
    (hOM : O ≤ M) (hS : fusionIsSylowIn f S O) (hSM : normalizer (S : Set G) ≤ M) : H ≤ M := by
  intro h hh
  have hT := finish65_fusionIsSylowIn_conj hS (hHO hh)
  have hbot3 : IsPGroup 3 (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨c, hc, hTc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    Nat.prime_three hf hbot3 hO3 bot_le hS hT bot_le bot_le
  have hn := finish65_mem_normalizer_of_map_eq hTc
  have := M.mul_mem (hOM (mem_inf.mp hc).1) (hSM hn)
  simpa using this

set_option linter.unusedVariables false in
theorem normalizer_le_of_enlarged {G : Type} [Group G] [Finite G] {M B F E : Subgroup G}
    {f : ℕ} (hf : f.Prime) (hf3 : f ≠ 3) (hB : IsPGroup 3 B) (hF : IsPGroup f F)
    (hmax : ∀ F' : Subgroup G, F' ≤ M → IsPGroup f F' → F' ≠ ⊥ → B ≤ normalizer (F' : Set G) →
      Nat.card F < Nat.card F' → normalizer (F' : Set G) ≤ M)
    (hBF : B ≤ normalizer (F : Set G))
    (hOM : rankThreePrimeCore 3 (normalizer (F : Set G)) ≤ M) (hFE : F < E) (hE : IsPGroup f E)
    (hBE : B ≤ normalizer (E : Set G))
    (hEO : E ≤ rankThreePrimeCore 3 (normalizer (F : Set G))) :
    normalizer (F : Set G) ≤ M := by
  obtain ⟨-, hHO, hO3⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 (normalizer (F : Set G))
  have hO3' : ¬ 3 ∣ Nat.card (rankThreePrimeCore 3 (normalizer (F : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO3
  obtain ⟨S, hSsyl, hES, hBS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three hf hB hO3' (hBF.trans hHO) hEO hE hBE
  have hS1 : S ≠ ⊥ := bot_lt_iff_ne_bot.mp ((bot_le.trans_lt hFE).trans_le hES)
  have hcard : Nat.card F < Nat.card S :=
    (Subgroup.card_lt_of_lt hFE).trans_le (Subgroup.card_le_of_le hES)
  have hN : normalizer (S : Set G) ≤ M := hmax S (hSsyl.1.trans hOM) hSsyl.2.1 hS1 hBS hcard
  exact finish65_le_of_normalizer_le hf hO3' hHO hOM hSsyl hN

end CFSG.LocalAnalysis.RankThreeTheoremC
