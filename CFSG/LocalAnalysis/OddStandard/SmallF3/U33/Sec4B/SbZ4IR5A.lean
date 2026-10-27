module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR3A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]

private theorem z4i_le_of_map_eq (hN : Odd (Nat.card N)) {P A B : Subgroup X}
    (hP : IsPGroup 2 P) (hA : A ≤ P) (hB : B ≤ P) (h : A.map (z4iπ N) = B.map (z4iπ N)) :
    A ≤ B := by
  intro x hx
  have hxmap : z4iπ N x ∈ B.map (z4iπ N) := by
    rw [← h]
    exact ⟨x, hx, rfl⟩
  obtain ⟨b, hb, hbx⟩ := hxmap
  have hb' : b = x := z4iπ_injOn N hN hP (hB hb) (hA hx) hbx
  rwa [← hb']

theorem z4i_eq_of_map_eq (hN : Odd (Nat.card N)) {P A B : Subgroup X} (hP : IsPGroup 2 P)
    (hA : A ≤ P) (hB : B ≤ P) (h : A.map (z4iπ N) = B.map (z4iπ N)) : A = B :=
  le_antisymm (z4i_le_of_map_eq N hN hP hA hB h) (z4i_le_of_map_eq N hN hP hB hA h.symm)

theorem z4i_map_ne_one (hN : Odd (Nat.card N)) {a : X} (ha : a * a = 1) (ha1 : a ≠ 1) :
    z4iπ N a ≠ 1 := by
  intro h
  have hmemN : a ∈ N := by
    rw [← z4iπ_ker N]
    exact MonoidHom.mem_ker.2 h
  have ha2 : a ^ 2 = 1 := by rw [pow_two]; exact ha
  have hord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hdvd : orderOf a ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hmemN
  rw [hord] at hdvd
  exact hN.not_two_dvd_nat hdvd

theorem z4i_exists_conj_of_map_eq (hN : Odd (Nat.card N)) {a b : X} (ha : a * a = 1)
    (ha1 : a ≠ 1) (hb : b * b = 1) (h : z4iπ N a = z4iπ N b) : ∃ g : X, a = g * b * g⁻¹ := by
  have ha2 : a ^ 2 = 1 := by rw [pow_two]; exact ha
  have horda : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hb1 : b ≠ 1 := fun hb1 => z4i_map_ne_one N hN ha ha1 (by rw [h, hb1, map_one])
  have hb2 : b ^ 2 = 1 := by rw [pow_two]; exact hb
  have hordb : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  obtain ⟨m, -, hm⟩ :=
    CFSG.RankThree.OddKernel.isConj_of_mk_eq N hN horda hordb h
  refine ⟨m⁻¹, ?_⟩
  calc a = m⁻¹ * (m * a * m⁻¹) * m := by group
    _ = m⁻¹ * b * m := by rw [hm]
    _ = m⁻¹ * b * (m⁻¹)⁻¹ := by group

theorem z4i_exists_lift_max (hN : Odd (Nat.card N)) {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    {W : Subgroup (X ⧸ N)} (hW : IsPGroup 2 W) (hQW : Q.map (z4iπ N) ≤ W)
    (hmax : ∀ P'' : Subgroup (X ⧸ N), IsPGroup 2 P'' → W ≤ P'' → P'' = W) :
    ∃ P : Subgroup X, IsPGroup 2 P ∧ Q ≤ P ∧ P.map (z4iπ N) = W ∧
      ∀ P'' : Subgroup X, IsPGroup 2 P'' → P ≤ P'' → P'' ≤ P := by
  have hker : Odd (Nat.card (z4iπ N).ker) := by rw [z4iπ_ker]; exact hN
  obtain ⟨P, hP, hQP, hPW, -⟩ :=
    z4i_lift_two_ge (z4iπ N) (z4iπ_surjective N) hker hQ hW hQW
  refine ⟨P, hP, hQP, hPW, ?_⟩
  intro P'' hP'' hle
  have hmap2 : IsPGroup 2 (P''.map (z4iπ N)) := hP''.map (z4iπ N)
  have hWle : W ≤ P''.map (z4iπ N) := by
    rw [← hPW]
    exact Subgroup.map_mono hle
  have hP''W : P''.map (z4iπ N) = W := hmax _ hmap2 hWle
  have hcard : Nat.card P'' = Nat.card P := by
    rw [(z4i_card_map N hN hP'').symm, hP''W, hPW.symm, z4i_card_map N hN hP]
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).ge

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
