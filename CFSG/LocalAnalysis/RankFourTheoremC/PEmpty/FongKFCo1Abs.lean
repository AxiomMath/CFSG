module

public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFCo1

open Subgroup

variable {p : ℕ}

theorem mem_normalizer_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) :
    f n ∈ Subgroup.normalizer ((S.map f : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro h
  constructor
  · intro hh
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hh
    refine Subgroup.mem_map.2 ⟨n * s * n⁻¹, (hn s).1 hs, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · intro hh
    obtain ⟨s', hs', hs'e⟩ := Subgroup.mem_map.1 hh
    have hh' : h = f (n⁻¹ * s' * n) := by
      rw [map_mul, map_mul, map_inv, hs'e]
      simp [mul_assoc]
    rw [hh']
    refine Subgroup.mem_map.2 ⟨n⁻¹ * s' * n, ?_, rfl⟩
    refine (hn (n⁻¹ * s' * n)).2 ?_
    simpa [mul_assoc] using hs'

theorem le_of_normalizers_generate [Fact p.Prime] {Z C : Type} [Group Z] [Finite Z] [Group C]
    [Finite C] {L : Subgroup Z} (φ : L ≃* C) {P : Subgroup Z} (hPL : P ≤ L)
    (hPp : IsPGroup p P) (hidx : ¬ p ∣ (P.subgroupOf L).index) {Y : Subgroup Z}
    (hY : ∀ S : Subgroup Z, S ≤ P → 2 ≤ CFSG.Open.pRank p S →
      Subgroup.normalizer (S : Set Z) ≤ Y)
    {P₀ : Subgroup C} (hP₀ : IsPGroup p P₀) {ι : Type} (S : ι → Subgroup C)
    (hSP : ∀ i, S i ≤ P₀)
    (hSr : ∀ i, ∃ E : Subgroup C, E ≤ S i ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2)
    (N : ι → Set C) (hN : ∀ i, ∀ n ∈ N i, n ∈ Subgroup.normalizer (S i : Set C))
    (hgen : Subgroup.closure (⋃ i, N i) = ⊤) : L ≤ Y := by
  classical
  have hQp : IsPGroup p (P.subgroupOf L) := hPp.comap_subtype
  let Q' : Subgroup C := (P.subgroupOf L).map (φ : L →* C)
  have hQ'p : IsPGroup p Q' := hQp.map (φ : L →* C)
  have hQ'idx : ¬ p ∣ Q'.index := by
    have : Q'.index = (P.subgroupOf L).index := Subgroup.index_map_equiv (P.subgroupOf L) φ
    rwa [this]
  let Qs : Sylow p C := hQ'p.toSylow hQ'idx
  obtain ⟨R, hR⟩ := hP₀.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Qs R
  have hmem : ∀ x ∈ P₀, g⁻¹ * x * g ∈ Q' := by
    intro x hx
    have hxR : x ∈ (R : Subgroup C) := hR hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxR
    obtain ⟨q, hq, hqx⟩ := hxR
    have : g⁻¹ * x * g = q := by
      rw [← hqx]
      simp [MulAut.smul_def, mul_assoc]
    rw [this]
    exact hq
  let ψ : C →* Z := L.subtype.comp ((φ.symm : C →* L).comp (MulAut.conj g⁻¹).toMonoidHom)
  have hψ : ∀ x : C, ψ x = ((φ.symm (g⁻¹ * x * g) : L) : Z) := by
    intro x
    simp [ψ, MulAut.conj_apply, mul_assoc]
  have hψinj : Function.Injective ψ := by
    intro a b hab
    rw [hψ, hψ] at hab
    have h1 := φ.symm.injective (Subtype.ext hab)
    have h2 : g⁻¹ * a * g = g⁻¹ * b * g := h1
    simpa using h2
  have hψP : ∀ x ∈ P₀, ψ x ∈ P := by
    intro x hx
    obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.1 (hmem x hx)
    rw [hψ]
    have : φ.symm (g⁻¹ * x * g) = q := by
      rw [← hqe]
      exact φ.symm_apply_apply q
    rw [this]
    exact Subgroup.mem_subgroupOf.1 hq
  let T : ι → Subgroup Z := fun i => (S i).map ψ
  have hTP : ∀ i, T i ≤ P := by
    intro i z hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hz
    exact hψP s (hSP i hs)
  have hTr : ∀ i, 2 ≤ CFSG.Open.pRank p (T i) := by
    intro i
    obtain ⟨E, hES, hEel, hEc⟩ := hSr i
    refine CFSG.GH74.Uniqueness.SU.SU1.le_pRank (Fact.out : p.Prime).one_lt
      (Subgroup.map_mono hES : E.map ψ ≤ T i) (CFSG.Open.IsElemAbelian.map hEel ψ) (k := 2) ?_
    rw [Subgroup.card_map_of_injective hψinj, hEc]
  have hnorm : ∀ i, ∀ n ∈ N i, ψ n ∈ Y := by
    intro i n hn
    exact hY (T i) (hTP i) (hTr i) (mem_normalizer_map ψ (hN i n hn))
  have hall : ∀ c : C, ψ c ∈ Y := by
    have : (⊤ : Subgroup C) ≤ Y.comap ψ := by
      rw [← hgen, Subgroup.closure_le]
      intro n hn
      obtain ⟨i, hni⟩ := Set.mem_iUnion.1 hn
      exact hnorm i n hni
    intro c
    exact this (Subgroup.mem_top c)
  intro l hl
  have : ψ (g * φ ⟨l, hl⟩ * g⁻¹) = l := by
    rw [hψ]
    simp [mul_assoc]
  rw [← this]
  exact hall _


end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFCo1
