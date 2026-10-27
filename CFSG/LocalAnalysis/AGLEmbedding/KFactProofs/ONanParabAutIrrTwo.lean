module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXY
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrPow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrQuot
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrRank

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

@[expose] def TwoHub (Y : Type) [Group Y] : Prop :=
  ∀ (S₀ : Sylow 2 Y) (J : Subgroup Y), Subgroup.normalizer (S₀ : Set Y) ≤ J →
    ∀ r : ℕ, r.Prime → 5 ≤ r → ∀ g ∈ J, (∃ a : ℕ, g ^ r ^ a = 1) → g ∈ perfectJoin J

theorem false_of_two {Y : Type} [Group Y] [Finite Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) (TH : TwoHub Y)
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr5 : 5 ≤ r)
    (R1 : OutPTwoGen Y p) (Rr : OutPInner Y r)
    (S₀ : Sylow 2 Y) {J : Subgroup Y} (hJ : Subgroup.normalizer (S₀ : Set Y) ≤ J)
    (hcyc : PerfectCyclicSylow p J) {U Z : Subgroup (MulAut Y)} {y : MulAut Y}
    (hU : IsPGroup p U) (hZ : Z = ⁅U, U⁆) (hirr : IrrAct y U Z) (hrel : p ^ 3 ≤ Z.relIndex U)
    (hpow : ∀ u ∈ U, u ^ p ∈ Z) (hyU : y ∈ Subgroup.normalizer (U : Set (MulAut Y)))
    (hUJ : U ≤ Subgroup.normalizer
      ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)))
    (hyJ : y ∈ Subgroup.normalizer
      ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)))
    (hyr : ∃ a : ℕ, y ^ r ^ a = 1) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hrank : NeedsThree U Z :=
    needsThree_of_relIndex (hZ ▸ Subgroup.commutator_le_self U) hZ.ge hpow hrel
  set cj : Y →* MulAut Y := MulAut.conj with hcj
  obtain ⟨a, ha⟩ := hyr
  have hSJ : (S₀ : Subgroup Y) ≤ J := fun x hx => hJ (Subgroup.le_normalizer hx)
  have hyin : y ∈ inn Y := by
    have hP : IsPGroup r (Subgroup.zpowers y) := by
      have : Fact r.Prime := ⟨hr⟩
      rintro ⟨_, k, rfl⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
    exact Rr _ hP (Subgroup.mem_zpowers y)
  obtain ⟨g, rfl⟩ := hyin
  have hUI : U ≤ inn Y := by
    obtain ⟨a₁, ha₁, b₁, hb₁, hgen⟩ := R1 U hU
    have hyI : (cj g) ∈ Subgroup.normalizer (inn Y : Set (MulAut Y)) := by
      rw [Subgroup.mem_normalizer_iff]
      exact fun x => ⟨fun hx => (inn_normal (Y := Y)).conj_mem x hx (cj g), fun hx => by
        simpa [mul_assoc] using (inn_normal (Y := Y)).conj_mem _ hx (cj g)⁻¹⟩
    exact le_of_two_generated hU hZ hirr hrank hyU hyI ha₁ hb₁ hgen
  have hgn : g ∈ Subgroup.normalizer (J : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    exact iff_of_mem_normalizer_map_conj hinj hyJ
  have hgJ : g ∈ J := mem_of_mem_normalizer S₀ hSJ hJ hgn
  have hgr : g ^ r ^ a = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact ha
  have hgP : g ∈ perfectJoin J := TH S₀ J hJ r hr hr5 g hgJ ⟨a, hgr⟩
  set N : Subgroup (MulAut Y) := (perfectJoin J).map cj with hN
  have hNle : N ≤ perfectJoin (J.map cj) := map_perfectJoin_le cj le_rfl
  have hcycN : ∀ A : Subgroup (MulAut Y), A ≤ N → IsPGroup p A → IsCyclic A :=
    fun A hA hAp => isCyclic_of_le_perfectJoin_map cj hinj hcyc (hA.trans hNle) hAp
  have hyN : cj g ∈ Subgroup.normalizer (N : Set (MulAut Y)) := by
    refine mem_normalizer_map_conj_of_iff (J := perfectJoin J) (fun x => ?_)
    show x ∈ perfectJoin J ↔ g * x * g⁻¹ ∈ perfectJoin J
    refine ⟨fun hx => conj_mem_perfectJoin hgJ hx, fun hx => ?_⟩
    simpa [mul_assoc] using conj_mem_perfectJoin (J.inv_mem hgJ) hx
  have hpowN : ∀ u ∈ U, ∃ k : ℕ, cj g * u * (cj g)⁻¹ * (u ^ k)⁻¹ ∈ N := by
    intro u hu
    obtain ⟨x, rfl⟩ := hUI hu
    have hxn : x ∈ Subgroup.normalizer (J : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      exact iff_of_mem_normalizer_map_conj hinj (hUJ hu)
    have hxJ : x ∈ J := mem_of_mem_normalizer S₀ hSJ hJ hxn
    refine ⟨1, ⟨g * x * g⁻¹ * x⁻¹, ?_, ?_⟩⟩
    · have h1 : g * x * g⁻¹ * x⁻¹ = g * (x * g⁻¹ * x⁻¹) := by group
      rw [h1]
      exact mul_mem hgP (conj_mem_perfectJoin hxJ (inv_mem hgP))
    · simp [hcj, map_mul, map_inv]
  exact core hU hZ hirr hrank hyU hyN (fun A _ _ => by assumption) hcycN hpowN

end CFSG.AGLEmbedding.ParabAutIrr
