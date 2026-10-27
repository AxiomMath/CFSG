module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthT
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthC
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthD

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open Polynomial Module Matrix CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.Classical2

section Perfect

private theorem exists_derivedSeries_succ_eq (G : Type*) [Group G] [Finite G] :
    ∃ k : ℕ, derivedSeries G (k + 1) = derivedSeries G k := by
  by_contra h
  push Not at h
  have hlt : ∀ k, Nat.card (derivedSeries G (k + 1)) < Nat.card (derivedSeries G k) := by
    intro k
    have hle : derivedSeries G (k + 1) ≤ derivedSeries G k := by
      rw [derivedSeries_succ]
      exact Subgroup.commutator_le_left _ _
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (h k))
  have hbound : ∀ k, Nat.card (derivedSeries G k) + k ≤ Nat.card G := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hlt k
      omega
  have h1 := hbound (Nat.card G + 1)
  have h2 : 0 < Nat.card (derivedSeries G (Nat.card G + 1)) := Nat.card_pos
  omega

private theorem exists_isPerfect_ne_bot {G : Type*} [Group G] [Finite G]
    (h : ¬ Group.IsSolvable G) : ∃ D : Subgroup G, Group.IsPerfect ↥D ∧ D ≠ ⊥ := by
  obtain ⟨k, hk⟩ := exists_derivedSeries_succ_eq G
  refine ⟨derivedSeries G k, ?_, fun hbot => h ⟨⟨k, hbot⟩⟩⟩
  rw [Subgroup.isPerfect_iff, ← derivedSeries_succ, hk]

end Perfect

section Plane

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] {Q : QuadraticForm K (Fin n → K)}
  {E0 : Subgroup (SpecialLinearGroup (Fin n) K)} [Fintype E0] [IsMulCommutative E0]

local notation "ρ₀" => planeRep E0

theorem orthBlockConcl_of_plane [Finite K] [CharP K 2] (hP : IsPlane p E0) (hpK : (p : K) ≠ 0)
    (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {R : Subgroup ((Fin n → K) ≃ₗ[K] (Fin n → K))}
    [Group.IsPerfect ↥R] (hR : R ≠ ⊥) (hRO : R ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hRc : ∀ g ∈ R, ∀ e : ↥E0, Commute (g : (Fin n → K) →ₗ[K] (Fin n → K)) (act ρ₀ e))
    {â : ↥E0} (hâ1 : â ≠ 1) : OrthBlockConcl Q E0 p â := by
  obtain ⟨M₁, hM₁, hM₁0, hâM₁⟩ := exists_active_not_mem hP hpK hâ1
  obtain ⟨c₁, hc₁M₁, hc₁1⟩ := RankThree.PartOne.KCLinPlane.exists_ne_one_mem E0 hM₁ hP
  have hex : ∀ L : Subgroup ↥E0, ∃ c : ↥E0, L ∈ lines p E0 → ∃ L' ∈ lines p E0, L' ≠ L ∧
      projLine ρ₀ L' ≠ 0 ∧ c ∈ L' ∧ c ≠ 1 := by
    intro L
    by_cases hL : L ∈ lines p E0
    · obtain ⟨b, hbL, hb1⟩ := RankThree.PartOne.KCLinPlane.exists_ne_one_mem E0 hL hP
      obtain ⟨L', hL', hL'0, hbL'⟩ := exists_active_not_mem hP hpK hb1
      obtain ⟨c, hcL', hc1⟩ := RankThree.PartOne.KCLinPlane.exists_ne_one_mem E0 hL' hP
      refine ⟨c, fun _ => ⟨L', hL', fun h => hbL' ?_, hL'0, hcL', hc1⟩⟩
      rw [h]
      exact hbL
    · exact ⟨1, fun h => absurd h hL⟩
  choose cL hcL using hex
  have hcLL : ∀ L ∈ lines p E0, cL L ∉ L := by
    intro L hL hmem
    obtain ⟨L', hL', hL'L, -, hcL', hc1⟩ := hcL L hL
    have h : cL L ∈ L' ⊓ L := ⟨hcL', hmem⟩
    rw [hP.inf_eq_bot (mem_lines.mp hL') (mem_lines.mp hL) hL'L, Subgroup.mem_bot] at h
    exact hc1 h
  rcases orth_exists_good_piece hP hpK hEQ hreg hR hRO hRc hM₁ hâM₁ hc₁M₁ hc₁1 cL hcLL with
    hns | ⟨L, hL, h, hh, hX, hns⟩
  · exact orthBlockConcl_of_fixed hP hpK hEQ hreg hp2 hpq hM₁ hM₁0 hâM₁ hc₁M₁ hc₁1 hns
  · obtain ⟨L', hL', hL'L, hL'0, hcL', hc1⟩ := hcL L hL
    exact orthBlockConcl_of_piece hP hpK hEQ hreg hp2 hpq hâ1 hL hL' hL'L hL'0 hcL' hc1 hh hX hns

end Plane

section Main

variable {n : ℕ} {K : Type} [Field K]

private theorem act_orthToSL {Q : QuadraticForm K (Fin n → K)} {A : Subgroup ↥(orthDerived Q)}
    {g : ↥(orthDerived Q)} (hg : g ∈ A) :
    act (planeRep (A.map (orthToSL Q))) ⟨orthToSL Q g, Subgroup.mem_map_of_mem _ hg⟩ =
      ((g : (Fin n → K) ≃ₗ[K] (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K)) :=
  toLin'_orthToSL Q g

theorem innerBlockAt_orthDerived [Finite K] [CharP K 2] (Q : QuadraticForm K (Fin n → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) : InnerBlockAt p ↥(orthDerived Q) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  intro A a hA hAc haA ha1 hns
  have hpK : (p : K) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := hpq
    have h1 : ((Nat.card K + 1 : ℕ) : K) = 0 := by rw [hm, Nat.cast_mul, h0, zero_mul]
    rw [Nat.cast_add, Nat.cast_one, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero,
      zero_add] at h1
    exact one_ne_zero h1
  have hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0 := fun v hv => hQ.1 v hv
  have : Finite ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
    Finite.of_injective (fun g : (Fin n → K) ≃ₗ[K] (Fin n → K) => (g : (Fin n → K) → Fin n → K))
      DFunLike.coe_injective
  have hΩO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _
  haveI : IsMulCommutative ↥(A.map (orthToSL Q)) := ⟨⟨fun x y => by
    obtain ⟨x', hx', hx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨y', hy', hy⟩ := Subgroup.mem_map.mp y.2
    have hc := congrArg Subtype.val (hA.1.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul]
    exact congrArg _ hc⟩⟩
  letI : Fintype ↥(A.map (orthToSL Q)) := Fintype.ofFinite _
  have hP : IsPlane p ↥(A.map (orthToSL Q)) :=
    { prime := hp
      card := by rw [Subgroup.card_map_of_injective (orthToSL_injective Q), hAc]
      pow := fun x => by
        obtain ⟨x', hx', hx⟩ := Subgroup.mem_map.mp x.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hx, ← map_pow, hA.2 x' hx', map_one, Subgroup.coe_one] }
  have hEQ : ∀ e : ↥(A.map (orthToSL Q)), ∀ v,
      Q (act (planeRep (A.map (orthToSL Q))) e v) = Q v := by
    intro e v
    obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp e.2
    have he : e = ⟨orthToSL Q g, Subgroup.mem_map_of_mem _ hg⟩ := Subtype.ext hge.symm
    rw [he, act_orthToSL hg]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hΩO g.2) v
  obtain ⟨D, hDp, hD⟩ := exists_isPerfect_ne_bot hns
  haveI := hDp
  set f : ↥(Subgroup.centralizer (A : Set ↥(orthDerived Q))) →* (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (orthDerived Q).subtype.comp (Subgroup.centralizer (A : Set ↥(orthDerived Q))).subtype
    with hf
  have hinj : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext h)
  haveI : Group.IsPerfect ↥(D.map f) := Group.IsPerfect.map _
  have hR0 : D.map f ≠ ⊥ := fun h => hD ((Subgroup.map_eq_bot_iff_of_injective D hinj).mp h)
  have hRO : D.map f ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨d, -, rfl⟩
    exact hΩO d.1.2
  have hRc : ∀ g ∈ D.map f, ∀ e : ↥(A.map (orthToSL Q)),
      Commute (g : (Fin n → K) →ₗ[K] (Fin n → K)) (act (planeRep (A.map (orthToSL Q))) e) := by
    rintro _ ⟨d, -, rfl⟩ e
    obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp e.2
    have he : e = ⟨orthToSL Q g, Subgroup.mem_map_of_mem _ hg⟩ := Subtype.ext hge.symm
    rw [he, act_orthToSL hg]
    have hc : g * d.1 = d.1 * g := Subgroup.mem_centralizer_iff.mp d.2 g hg
    refine LinearMap.ext fun v => ?_
    have := DFunLike.congr_fun (congrArg Subtype.val hc) v
    exact this.symm
  have hâ1 : (⟨orthToSL Q a, Subgroup.mem_map_of_mem _ haA⟩ : ↥(A.map (orthToSL Q))) ≠ 1 :=
    fun h1 => ha1 (orthToSL_injective Q (by
      rw [map_one]
      exact congrArg Subtype.val h1))
  exact innerBlock_of_orthBlockConcl haA
    (orthBlockConcl_of_plane hP hpK hEQ hreg hp2 hpq hR0 hRO hRc hâ1)

end Main

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
