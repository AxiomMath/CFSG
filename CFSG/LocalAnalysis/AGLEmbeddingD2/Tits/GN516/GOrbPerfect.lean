module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Perf

variable {G G' : Type*} [Group G] [Group G']

@[expose] def perfRad (X : Subgroup G) : Subgroup G :=
  ⨆ (Q : Subgroup G) (_ : Q ≤ X ∧ ⁅Q, Q⁆ = Q), Q

theorem perfRad_le (X : Subgroup G) : perfRad X ≤ X :=
  iSup₂_le fun _ hQ => hQ.1

theorem le_perfRad {Q X : Subgroup G} (hQX : Q ≤ X) (hQ : ⁅Q, Q⁆ = Q) : Q ≤ perfRad X :=
  le_iSup₂_of_le Q ⟨hQX, hQ⟩ le_rfl

theorem commutator_perfRad (X : Subgroup G) : ⁅perfRad X, perfRad X⁆ = perfRad X := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    show g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ perfRad X
    exact (perfRad X).mul_mem ((perfRad X).mul_mem ((perfRad X).mul_mem hg₁ hg₂)
      ((perfRad X).inv_mem hg₁)) ((perfRad X).inv_mem hg₂)
  · refine iSup₂_le fun Q hQ => ?_
    have hQP : Q ≤ perfRad X := le_perfRad hQ.1 hQ.2
    calc Q = ⁅Q, Q⁆ := hQ.2.symm
      _ ≤ ⁅perfRad X, perfRad X⁆ := Subgroup.commutator_mono hQP hQP

private theorem map_perfRad_le (f : G →* G') (Y : Subgroup G) :
    (perfRad Y).map f ≤ perfRad (Y.map f) := by
  have hperf : ⁅(perfRad Y).map f, (perfRad Y).map f⁆ = (perfRad Y).map f := by
    rw [← Subgroup.map_commutator, commutator_perfRad]
  exact le_perfRad (Subgroup.map_mono (f := f) (perfRad_le Y)) hperf

theorem map_perfRad (e : G ≃* G') (X : Subgroup G) :
    (perfRad X).map e.toMonoidHom = perfRad (X.map e.toMonoidHom) := by
  have hgf : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  have hfg : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' := by
    ext x
    simp
  refine le_antisymm (map_perfRad_le e.toMonoidHom X) ?_
  have h2 : (perfRad (X.map e.toMonoidHom)).map e.symm.toMonoidHom ≤ perfRad X := by
    have h := map_perfRad_le e.symm.toMonoidHom (X.map e.toMonoidHom)
    rwa [Subgroup.map_map, hgf, Subgroup.map_id] at h
  calc perfRad (X.map e.toMonoidHom)
      = ((perfRad (X.map e.toMonoidHom)).map e.symm.toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_map, hfg, Subgroup.map_id]
    _ ≤ (perfRad X).map e.toMonoidHom := Subgroup.map_mono h2

private theorem eq_bot_of_perfect_of_isSolvable {H : Type*} [Group H] [Group.IsSolvable H]
    {P : Subgroup H} (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, derivedSeries H n = ⊥ := Group.IsSolvable.solvable
  have key : ∀ k : ℕ, P ≤ derivedSeries H k := by
    intro k
    induction k with
    | zero =>
      rw [derivedSeries_zero]
      exact le_top
    | succ k ih =>
      rw [derivedSeries_succ]
      calc P = ⁅P, P⁆ := hP.symm
        _ ≤ ⁅derivedSeries H k, derivedSeries H k⁆ := Subgroup.commutator_mono ih ih
  have hPn := key n
  rw [hn] at hPn
  exact le_bot_iff.mp hPn

private theorem le_of_perfect_of_pgroup_sup {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {K N P : Subgroup H} [K.Normal] (hN : IsPGroup p N) (hNK : N ⊔ K = ⊤)
    (hP : ⁅P, P⁆ = P) : P ≤ K := by
  have hKbot : K.map (QuotientGroup.mk' K) = ⊥ :=
    (Subgroup.map_eq_bot_iff K).mpr (QuotientGroup.ker_mk' K).ge
  have hmap : N.map (QuotientGroup.mk' K) = ⊤ := by
    calc N.map (QuotientGroup.mk' K) = N.map (QuotientGroup.mk' K) ⊔ ⊥ := (sup_bot_eq _).symm
      _ = N.map (QuotientGroup.mk' K) ⊔ K.map (QuotientGroup.mk' K) := by rw [hKbot]
      _ = (N ⊔ K).map (QuotientGroup.mk' K) := (Subgroup.map_sup _ _ _).symm
      _ = (⊤ : Subgroup H).map (QuotientGroup.mk' K) := by rw [hNK]
      _ = ⊤ := Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)
  have hsurj : Function.Surjective ((QuotientGroup.mk' K).comp N.subtype) := by
    intro y
    have hy : y ∈ N.map (QuotientGroup.mk' K) := by
      rw [hmap]
      exact Subgroup.mem_top y
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hpq : IsPGroup p (H ⧸ K) := hN.of_surjective _ hsurj
  haveI := IsPGroup.isNilpotent hpq
  have hperf : ⁅P.map (QuotientGroup.mk' K), P.map (QuotientGroup.mk' K)⁆
      = P.map (QuotientGroup.mk' K) := by
    rw [← Subgroup.map_commutator, hP]
  have hbot := eq_bot_of_perfect_of_isSolvable hperf
  have hle : P ≤ (QuotientGroup.mk' K).ker := (Subgroup.map_eq_bot_iff P).mp hbot
  rwa [QuotientGroup.ker_mk'] at hle

theorem le_of_perfect_of_le_sup [Finite G] {p : ℕ} [Fact p.Prime] {Q A N : Subgroup G}
    (hQ : ⁅Q, Q⁆ = Q) (hle : Q ≤ A ⊔ N) (hNA : N ≤ Subgroup.normalizer (A : Set G))
    (hN : IsPGroup p N) : Q ≤ A := by
  have hAB : A ≤ A ⊔ N := le_sup_left
  have hNB : N ≤ A ⊔ N := le_sup_right
  have hBN : A ⊔ N ≤ Subgroup.normalizer (A : Set G) :=
    sup_le Subgroup.le_normalizer hNA
  haveI : (A.subgroupOf (A ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mpr hBN
  have hNK : N.subgroupOf (A ⊔ N) ⊔ A.subgroupOf (A ⊔ N) = ⊤ := by
    have h := Subgroup.subgroupOf_sup hAB hNB
    rw [Subgroup.subgroupOf_self] at h
    exact (sup_comm _ _).trans h.symm
  have hN' : IsPGroup p (N.subgroupOf (A ⊔ N)) := hN.comap_subtype (K := A ⊔ N)
  have hQ' : ⁅Q.subgroupOf (A ⊔ N), Q.subgroupOf (A ⊔ N)⁆ = Q.subgroupOf (A ⊔ N) := by
    refine Subgroup.map_injective (f := (A ⊔ N).subtype) Subtype.val_injective ?_
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hle, hQ]
  intro x hx
  have hxB : x ∈ A ⊔ N := hle hx
  have hmem : (⟨x, hxB⟩ : ↥(A ⊔ N)) ∈ Q.subgroupOf (A ⊔ N) := hx
  exact le_of_perfect_of_pgroup_sup hN' hNK hQ' hmem

theorem perfRad_le_of_le_sup [Finite G] {p : ℕ} [Fact p.Prime] {X A N : Subgroup G}
    (hle : X ≤ A ⊔ N) (hNA : N ≤ Subgroup.normalizer (A : Set G)) (hN : IsPGroup p N) :
    perfRad X ≤ A :=
  le_of_perfect_of_le_sup (commutator_perfRad X) ((perfRad_le X).trans hle) hNA hN

end CFSG.AGLEmbeddingD2.Tits.GN516.Perf
