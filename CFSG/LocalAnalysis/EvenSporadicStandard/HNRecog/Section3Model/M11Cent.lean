module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.M11Data
public import CFSG.CharacterTheory.Semidihedral.FourPointUniversal

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Equiv Equiv.Perm CFSG.Holt.SmallGroups CFSG.Semidihedral.FourPointPresentation

open scoped Pointwise


@[expose] def m11zG : ↥CFSG.Open.M11 := ⟨m11z, (m11z_facts.1 |> mem_m11Stab.mp).1⟩

private theorem m11z_fixed_iff (x : Fin 11) :
    m11z x = x ↔ x = 0 ∨ x = 1 ∨ x = 2 := by
  revert x
  decide +kernel

private def m11Sub : Set.powersetCard (Fin 11) 3 :=
  Set.powersetCard.ofCard (s := ({0, 1, 2} : Finset (Fin 11))) (by decide)

private theorem map_normalWord {P Q : Type*} [Group P] [Group Q] (φ : P →* Q)
    (a b c z : P) (i : Fin 2 × Fin 6 × Fin 4) :
    φ (normalWord a b c z i) = normalWord (φ a) (φ b) (φ c) (φ z) i := by
  obtain ⟨e, j, k⟩ := i
  fin_cases e <;> fin_cases j <;> fin_cases k <;>
    simp [normalWord, parabolicWord, cosetWord, map_mul, map_pow]

private theorem normalWord_mem_closure {P : Type*} [Group P] (a b c z : P)
    (i : Fin 2 × Fin 6 × Fin 4) :
    normalWord a b c z i ∈ Subgroup.closure ({a, b, c, z} : Set P) := by
  let S : Subgroup P := Subgroup.closure ({a, b, c, z} : Set P)
  have ha : a ∈ S := Subgroup.subset_closure (by simp)
  have hb : b ∈ S := Subgroup.subset_closure (by simp)
  have hc : c ∈ S := Subgroup.subset_closure (by simp)
  have hz : z ∈ S := Subgroup.subset_closure (by simp)
  show normalWord a b c z i ∈ S
  obtain ⟨e, j, k⟩ := i
  fin_cases e <;> fin_cases j <;> fin_cases k <;>
    simp only [normalWord, parabolicWord, cosetWord, pow_zero, pow_one, one_mul, mul_one] <;>
    repeat' (first
      | exact S.one_mem
      | exact ha | exact hb | exact hc | exact hz
      | apply S.mul_mem)

theorem m11_card_centralizer_z_le :
    Nat.card ↥(Subgroup.centralizer ({m11zG} : Set ↥CFSG.Open.M11)) ≤ 48 := by
  haveI : MulAction.IsPretransitive ↥CFSG.Open.M11 (Set.powersetCard (Fin 11) 3) :=
    Set.powersetCard.isPretransitive_of_isMultiplyPretransitive ↥CFSG.Open.M11
      m11_isMultiplyPretransitive_three
  have hmap : ∀ (g : ↥CFSG.Open.M11),
      g ∈ Subgroup.centralizer ({m11zG} : Set ↥CFSG.Open.M11) →
      ∀ b ∈ (m11Sub : Finset (Fin 11)), g • b ∈ (m11Sub : Finset (Fin 11)) := by
    intro g hg b hb
    have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by simpa [m11Sub] using hb
    have hzfix : m11z 0 = 0 ∧ m11z 1 = 1 ∧ m11z 2 = 2 :=
      ⟨(mem_m11Stab.mp m11z_facts.1).2.1, (mem_m11Stab.mp m11z_facts.1).2.2.1,
        (mem_m11Stab.mp m11z_facts.1).2.2.2⟩
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hfix : m11zG • b = b := by
      rcases hb' with rfl | rfl | rfl
      · simpa only [m11zG, Subgroup.smul_def, Perm.smul_def] using hzfix.1
      · simpa only [m11zG, Subgroup.smul_def, Perm.smul_def] using hzfix.2.1
      · simpa only [m11zG, Subgroup.smul_def, Perm.smul_def] using hzfix.2.2
    have hgb : m11zG • (g • b) = g • b := by
      have h := congrArg (fun x : ↥CFSG.Open.M11 => x • b) hcomm
      simpa only [mul_smul, hfix] using h.symm
    have hzgb : m11z (g • b) = g • b := by
      simpa only [m11zG, Subgroup.smul_def, Perm.smul_def] using hgb
    simpa [m11Sub] using (m11z_fixed_iff (g • b)).mp hzgb
  have hle : Subgroup.centralizer ({m11zG} : Set ↥CFSG.Open.M11) ≤
      MulAction.stabilizer ↥CFSG.Open.M11 m11Sub := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g • (m11Sub : Finset (Fin 11)) = (m11Sub : Finset (Fin 11))
    apply Finset.ext
    intro x
    constructor
    · intro hx
      rw [Finset.mem_smul_finset] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hmap g hg y hy
    · intro hx
      rw [Finset.mem_smul_finset]
      exact ⟨g⁻¹ • x, hmap g⁻¹ (Subgroup.inv_mem _ hg) x hx, by simp⟩
  have hindex : (MulAction.stabilizer ↥CFSG.Open.M11 m11Sub).index = 165 := by
    rw [MulAction.index_stabilizer_of_transitive ↥CFSG.Open.M11 m11Sub,
      Set.powersetCard.card, Nat.card_fin]
    decide
  have hcardstab : Nat.card ↥(MulAction.stabilizer ↥CFSG.Open.M11 m11Sub) = 48 := by
    have h := Subgroup.card_mul_index (MulAction.stabilizer ↥CFSG.Open.M11 m11Sub)
    rw [hindex, card_m11] at h
    omega
  calc Nat.card ↥(Subgroup.centralizer ({m11zG} : Set ↥CFSG.Open.M11))
      ≤ Nat.card ↥(MulAction.stabilizer ↥CFSG.Open.M11 m11Sub) :=
        Nat.card_mono (Set.toFinite _) hle
    _ = 48 := hcardstab

theorem m11_centralizer_z_equiv :
    Nonempty (↥(Subgroup.centralizer ({m11zG} : Set ↥CFSG.Open.M11)) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  let H : Subgroup ↥CFSG.Open.M11 := Subgroup.centralizer ({m11zG} : Set ↥CFSG.Open.M11)
  let A : ↥CFSG.Open.M11 := ⟨m11a1, m11a1_mem⟩
  let B : ↥CFSG.Open.M11 := ⟨m11b1, m11b1_mem⟩
  let C : ↥CFSG.Open.M11 := ⟨m11c1, m11c1_mem⟩
  let Z : ↥CFSG.Open.M11 := m11zG
  have hA : A ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext m11_comm_z.1
  have hB : B ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext m11_comm_z.2.1
  have hC : C ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext m11_comm_z.2.2
  have hZ : Z ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let A' : ↥H := ⟨A, hA⟩
  let B' : ↥H := ⟨B, hB⟩
  let C' : ↥H := ⟨C, hC⟩
  let Z' : ↥H := ⟨Z, hZ⟩
  let K : Subgroup ↥H := Subgroup.closure ({A', B', C', Z'} : Set ↥H)
  have hrel : Relations A' B' C' Z' :=
    { central := by
        rw [Subgroup.mem_center_iff]
        intro x
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp x.2
      a_sq := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [A', A, pow_two] using m11_sq_one.1
      b_sq := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [B', B, pow_two] using m11_sq_one.2.1
      c_sq := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [C', C, pow_two] using m11_sq_one.2.2.1
      z_sq := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [Z', Z, m11zG, pow_two] using m11_sq_one.2.2.2.2
      ab_cube := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [A', B', A, B] using m11_relations.1
      bc_cube := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [B', C', B, C] using m11_relations.2.1
      ac_sq := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [A', C', Z', A, C, Z, m11zG] using m11_relations.2.2 }
  have hKmem : ∀ i : Fin 2 × Fin 6 × Fin 4, normalWord A' B' C' Z' i ∈ K :=
    fun i => normalWord_mem_closure A' B' C' Z' i
  let f : Fin 2 × Fin 6 × Fin 4 → ↥K :=
    fun i => ⟨normalWord A' B' C' Z' i, hKmem i⟩
  have hf : Function.Injective f := by
    intro i j hij
    let φ : ↥H →* Perm (Fin 11) :=
      (Subgroup.subtype CFSG.Open.M11).comp (Subgroup.subtype H)
    have hperm : φ (normalWord A' B' C' Z' i) = φ (normalWord A' B' C' Z' j) := by
      have h1 := congrArg (fun x : ↥K => φ (x : ↥H)) hij
      simpa [f] using h1
    rw [map_normalWord φ A' B' C' Z' i, map_normalWord φ A' B' C' Z' j] at hperm
    have hφA : φ A' = m11a1 := by simp [φ, A', A]
    have hφB : φ B' = m11b1 := by simp [φ, B', B]
    have hφC : φ C' = m11c1 := by simp [φ, C', C]
    have hφZ : φ Z' = m11z := by simp [φ, Z', Z, m11zG]
    rw [hφA, hφB, hφC, hφZ] at hperm
    exact m11_normalWord_images_inj i j
      ⟨congrArg (fun σ : Perm (Fin 11) => σ 0) hperm,
        congrArg (fun σ : Perm (Fin 11) => σ 1) hperm,
        congrArg (fun σ : Perm (Fin 11) => σ 2) hperm,
        congrArg (fun σ : Perm (Fin 11) => σ 3) hperm⟩
  have h48le : 48 ≤ Nat.card ↥K := by
    have hcard48 : Nat.card (Fin 2 × Fin 6 × Fin 4) = 48 := by
      rw [Nat.card_prod, Nat.card_prod, Nat.card_fin, Nat.card_fin, Nat.card_fin]
    have := Nat.card_le_card_of_injective f hf
    omega
  have hHle : Nat.card ↥H ≤ 48 := m11_card_centralizer_z_le
  have hKle : Nat.card ↥K ≤ Nat.card ↥H :=
    Nat.card_le_card_of_injective (fun x : ↥K => (x.1 : ↥H))
      (fun a b hab => Subtype.ext hab)
  have hKcard : Nat.card ↥K = 48 := le_antisymm (le_trans hKle hHle) h48le
  have hHcard : Nat.card ↥H = 48 := le_antisymm hHle (le_trans h48le hKle)
  have hgen : K = ⊤ := Subgroup.eq_top_of_card_eq K (by rw [hKcard, hHcard])
  obtain ⟨θ, -⟩ :=
    CFSG.Semidihedral.FourPointUniversal.exists_matrix_equiv hrel hgen hHcard
  exact ⟨θ⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
