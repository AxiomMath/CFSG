module

public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG.Certificates.RawSchreierDatum

theorem transversal_getD_spec {n : ℕ} (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount) (x : Fin n) (hx : x ∈ Q.orbitPoints i) :
    Q.transversal? i x = some ((Q.transversal? i x).getD 1) ∧
      (Q.transversal? i x).getD 1 ∈ Q.levelSubgroup i.val ∧
      (Q.transversal? i x).getD 1 (Q.base.get i) = x := by
  obtain ⟨t, ht, htH, _, htx⟩ := Q.orbitPoint_transversal i x hx
  simpa only [ht, Option.getD_some] using And.intro ht (And.intro htH htx)

@[expose] def levelOrbitTransversal {n : ℕ} (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount)
    (x : MulAction.orbit (Q.levelSubgroup i.val) (Q.base.get i)) : Q.levelSubgroup i.val :=
  ⟨(Q.transversal? i x.val).getD 1,
    (Q.transversal_getD_spec i x.val (by
      rw [Q.orbitPoints_eq_orbit i]
      exact x.property)).2.1⟩

theorem levelOrbitTransversal_val {n : ℕ} (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount)
    (x : MulAction.orbit (Q.levelSubgroup i.val) (Q.base.get i)) :
    (Q.levelOrbitTransversal i x : Equiv.Perm (Fin n)) =
      (Q.transversal? i x.val).getD 1 := rfl

theorem levelOrbitTransversal_smul {n : ℕ} (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount)
    (x : MulAction.orbit (Q.levelSubgroup i.val) (Q.base.get i)) :
    Q.levelOrbitTransversal i x • Q.base.get i = (x : Fin n) :=
  (Q.transversal_getD_spec i x.val (by
    rw [Q.orbitPoints_eq_orbit i]
    exact x.property)).2.2

theorem levelOrbitTransversal_root {n : ℕ} (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount) :
    Q.levelOrbitTransversal i ⟨Q.base.get i, MulAction.mem_orbit_self _⟩ = 1 := by
  apply Subtype.ext
  simp only [levelOrbitTransversal, Q.transversal_root i, Option.getD_some, Subgroup.coe_one]

theorem checked_schreier_mem_next {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (i : Fin Q.baseCount) (x : Fin n)
    (tx : Equiv.Perm (Fin n)) (htx : Q.transversal? i x = some tx)
    (s : Equiv.Perm (Fin n)) (hs : s ∈ Q.levelSteps i.val) :
    ∃ ty, Q.transversal? i (s x) = some ty ∧
      ty⁻¹ * s * tx ∈ Q.levelSubgroup (i.val + 1) := by
  obtain ⟨ty, hty, hsift⟩ := ((validSchreier_iff Q).1 hQ).2.2.2 i x tx htx s hs
  refine ⟨ty, hty, Q.sift_mem_levelSubgroup (i.val + 1) (ty⁻¹ * s * tx) ?_⟩
  simpa only [sift] using hsift

theorem schreier_step_mem_levelSteps {n : ℕ} (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount) (s : Q.levelSubgroup i.val)
    (hs : s ∈ (Q.levelSubgroup i.val).subtype ⁻¹' {g | g ∈ Q.levelGenerators i.val} ∪
      (fun g : Q.levelSubgroup i.val => g⁻¹) ''
        ((Q.levelSubgroup i.val).subtype ⁻¹' {g | g ∈ Q.levelGenerators i.val})) :
    (s : Equiv.Perm (Fin n)) ∈ Q.levelSteps i.val := by
  rcases hs with hs | ⟨u, hu, rfl⟩
  · exact List.mem_append_left _ hs
  · exact List.mem_append_right _ (List.mem_map_of_mem hu)

theorem schreier_generator_mem_next {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (i : Fin Q.baseCount) (g : Equiv.Perm (Fin n))
    (hg : g ∈ (Q.levelSubgroup i.val).subtype ''
      schreierGeneratorSet (Q.base.get i)
        ((Q.levelSubgroup i.val).subtype ⁻¹' {s | s ∈ Q.levelGenerators i.val})
        (Q.levelOrbitTransversal i)) : g ∈ Q.levelSubgroup (i.val + 1) := by
  obtain ⟨u, ⟨x, s, hs, hu⟩, rfl⟩ := hg
  let tx : Equiv.Perm (Fin n) := (Q.transversal? i x.val).getD 1
  have htx : Q.transversal? i x.val = some tx :=
    (Q.transversal_getD_spec i x.val (by
      rw [Q.orbitPoints_eq_orbit i]
      exact x.property)).1
  obtain ⟨ty, hty, hmem⟩ := Q.checked_schreier_mem_next hQ i x.val tx htx s
    (Q.schreier_step_mem_levelSteps i s hs)
  rw [hu]
  change ((Q.transversal? i ((s : Equiv.Perm (Fin n)) x.val)).getD 1)⁻¹ *
    (s : Equiv.Perm (Fin n)) * (Q.transversal? i x.val).getD 1 ∈
      Q.levelSubgroup (i.val + 1)
  simpa only [hty, Option.getD_some] using hmem

theorem levelSubgroup_succ_eq_stabilizer {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (i : Fin Q.baseCount) :
    Q.levelSubgroup (i.val + 1) =
      Q.levelSubgroup i.val ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i) := by
  apply le_antisymm (Q.levelSubgroup_succ_le_stabilizer i)
  change Subgroup.closure {s | s ∈ Q.levelGenerators i.val} ⊓
    MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i) ≤ Q.levelSubgroup (i.val + 1)
  rw [← schreier_generated_stabilizer_generators (Q.base.get i)
    {s | s ∈ Q.levelGenerators i.val} (Q.levelOrbitTransversal i)
    (Q.levelOrbitTransversal_smul i) (Q.levelOrbitTransversal_root i)]
  exact (Subgroup.closure_le _).2 (Q.schreier_generator_mem_next hQ i)

theorem base_take_succ {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Q.base.toList.take (i.val + 1) = Q.base.toList.take i.val ++ [Q.base.get i] := by
  rw [List.take_succ_eq_append_getElem (by simp)]
  simp [Vector.getElem_toList, Vector.get]

theorem mem_levelSubgroup_iff {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (i : ℕ) (hi : i ≤ Q.baseCount) (g : Equiv.Perm (Fin n)) :
    g ∈ Q.levelSubgroup i ↔ g ∈ Q.originalSubgroup ∧
      ∀ b ∈ Q.base.toList.take i, g b = b := by
  induction i with
  | zero => simp [Q.levelSubgroup_zero_eq_original hQ]
  | succ i ih =>
    let j : Fin Q.baseCount := ⟨i, by omega⟩
    rw [Q.levelSubgroup_succ_eq_stabilizer hQ j]
    simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    rw [ih (by omega), Q.base_take_succ j]
    constructor
    · rintro ⟨⟨hg, hfix⟩, hlast⟩
      refine ⟨hg, ?_⟩
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hfix b hb
      · have hb' : b = Q.base.get j := by simpa using hb
        simpa only [hb'] using hlast
    · rintro ⟨hg, hfix⟩
      exact ⟨⟨hg, fun b hb => hfix b (List.mem_append_left _ hb)⟩,
        hfix (Q.base.get j) (by simp)⟩

theorem levelSubgroup_eq_pointwise_stabilizer {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (i : ℕ) (hi : i ≤ Q.baseCount) :
    Q.levelSubgroup i = Q.originalSubgroup ⊓
      fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList.take i} := by
  ext g
  simp only [Subgroup.mem_inf, mem_fixingSubgroup_iff, Set.mem_ofPred_eq, Equiv.Perm.smul_def]
  exact Q.mem_levelSubgroup_iff hQ i hi g

end CFSG.Certificates.RawSchreierDatum
