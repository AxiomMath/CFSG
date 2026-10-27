module

public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Census.Witness46

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

theorem not_all_sylow_three_cyclic_of_four {G : Type} [Group G] [Finite G]
    (E : Subgroup G) (hE : IsPGroup 3 E) (x₁ x₂ x₃ x₄ : G)
    (h₁ : x₁ ∈ E) (h₂ : x₂ ∈ E) (h₃ : x₃ ∈ E) (h₄ : x₄ ∈ E)
    (c₁ : x₁ ^ 3 = 1) (c₂ : x₂ ^ 3 = 1) (c₃ : x₃ ^ 3 = 1) (c₄ : x₄ ^ 3 = 1)
    (n₁ : x₁ ≠ 1) (n₂ : x₂ ≠ 1) (n₃ : x₃ ≠ 1) (n₄ : x₄ ≠ 1)
    (d₁₂ : x₁ ≠ x₂) (d₁₃ : x₁ ≠ x₃) (d₁₄ : x₁ ≠ x₄) (d₂₃ : x₂ ≠ x₃) (d₂₄ : x₂ ≠ x₄) (d₃₄ : x₃ ≠ x₄) :
    ¬ ∀ Q : Sylow 3 G, IsCyclic ↥(↑Q : Subgroup G) := by
  intro hall
  classical
  obtain ⟨Q, hEQ⟩ := IsPGroup.exists_le_sylow (P := E) hE
  have hc := hall Q
  haveI : Fintype ↥(↑Q : Subgroup G) := Fintype.ofFinite _
  let y₁ : ↥(↑Q : Subgroup G) := ⟨x₁, hEQ h₁⟩
  let y₂ : ↥(↑Q : Subgroup G) := ⟨x₂, hEQ h₂⟩
  let y₃ : ↥(↑Q : Subgroup G) := ⟨x₃, hEQ h₃⟩
  let y₄ : ↥(↑Q : Subgroup G) := ⟨x₄, hEQ h₄⟩
  have hy : ∀ i : ↥(↑Q : Subgroup G), i ^ 3 = 1 ↔ ((i : G) ^ 3 = 1) := fun i => by
    constructor
    · intro hi; simpa using congrArg Subtype.val hi
    · intro hi; exact Subtype.ext (by simpa using hi)
  let S5 : Finset ↥(↑Q : Subgroup G) := {1, y₁, y₂, y₃, y₄}
  have hS5 : S5 ⊆ Finset.univ.filter (fun a : ↥(↑Q : Subgroup G) => a ^ 3 = 1) := by
    intro a ha
    simp only [S5, Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · simp
    · exact (hy _).mpr c₁
    · exact (hy _).mpr c₂
    · exact (hy _).mpr c₃
    · exact (hy _).mpr c₄
  have hne : ∀ a b : ↥(↑Q : Subgroup G), (a : G) ≠ (b : G) → a ≠ b := fun a b h hab => h (congrArg Subtype.val hab)
  have f12 : y₁ ≠ y₂ := hne _ _ d₁₂
  have f13 : y₁ ≠ y₃ := hne _ _ d₁₃
  have f14 : y₁ ≠ y₄ := hne _ _ d₁₄
  have f23 : y₂ ≠ y₃ := hne _ _ d₂₃
  have f24 : y₂ ≠ y₄ := hne _ _ d₂₄
  have f34 : y₃ ≠ y₄ := hne _ _ d₃₄
  have g1 : (1 : ↥(↑Q : Subgroup G)) ≠ y₁ := hne _ _ (fun h => n₁ h.symm)
  have g2 : (1 : ↥(↑Q : Subgroup G)) ≠ y₂ := hne _ _ (fun h => n₂ h.symm)
  have g3 : (1 : ↥(↑Q : Subgroup G)) ≠ y₃ := hne _ _ (fun h => n₃ h.symm)
  have g4 : (1 : ↥(↑Q : Subgroup G)) ≠ y₄ := hne _ _ (fun h => n₄ h.symm)
  have hcard : S5.card = 5 := by
    simp only [S5]
    simp [Finset.card_insert_of_notMem, f12, f13, f14, f23, f24, f34, g1, g2, g3, g4,
      Ne.symm f12, Ne.symm f13, Ne.symm f14, Ne.symm f23, Ne.symm f24, Ne.symm f34,
      Ne.symm g1, Ne.symm g2, Ne.symm g3, Ne.symm g4]
  have hle := Finset.card_le_card hS5
  have h3 := IsCyclic.card_pow_eq_one_le (α := ↥(↑Q : Subgroup G)) (n := 3) (by norm_num)
  omega

theorem isPGroup_three_closure {G : Type} [Group G] (x y : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : x * y = y * x) : IsPGroup 3 (Subgroup.closure ({x, y} : Set G)) := by
  set S : Set G := {x, y} with hS
  have hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact hxy
    · exact hxy.symm
    · rfl
  have hC : Subgroup.closure S ≤ Subgroup.centralizer S := by
    refine (Subgroup.closure_le _).mpr ?_
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    exact hSc t ht s hs
  have hcomm : ∀ g ∈ Subgroup.closure S, ∀ h ∈ Subgroup.closure S, Commute g h := by
    intro g hg h hh
    have hh' := Subgroup.closure_le_centralizer_centralizer S hh
    rw [Subgroup.mem_centralizer_iff] at hh'
    exact hh' g (hC hg)
  have key : ∀ g ∈ Subgroup.closure S, g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem z hz =>
      rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    | one => simp
    | mul a b ha hb iha ihb =>
      rw [(hcomm a ha b hb).mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by simpa using key g.1 g.2)⟩

def cyc3a : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

def cyc3b : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 3 4 * Equiv.swap 4 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem cyc3a_cube : cyc3a ^ 3 = 1 := by
  apply Subtype.ext
  simp only [cyc3a, Subgroup.coe_pow, Subgroup.coe_one]
  decide

theorem cyc3b_cube : cyc3b ^ 3 = 1 := by
  apply Subtype.ext
  simp only [cyc3b, Subgroup.coe_pow, Subgroup.coe_one]
  decide

theorem cyc3_comm : cyc3a * cyc3b = cyc3b * cyc3a := by
  apply Subtype.ext
  simp only [cyc3a, cyc3b, Subgroup.coe_mul]
  decide

theorem cyc3a_ne_one : cyc3a ≠ 1 := by
  intro h
  have : (cyc3a : Equiv.Perm (Fin 6)) 0 = 0 := by rw [h]; rfl
  revert this
  simp only [cyc3a, Subgroup.coe_mul]
  decide

theorem cyc3b_ne_one : cyc3b ≠ 1 := by
  intro h
  have : (cyc3b : Equiv.Perm (Fin 6)) 3 = 3 := by rw [h]; rfl
  revert this
  simp only [cyc3b, Subgroup.coe_mul]
  decide

theorem cyc3_distinct : cyc3a ≠ cyc3a ^ 2 ∧ cyc3a ≠ cyc3b ∧ cyc3a ≠ cyc3b ^ 2 ∧
    cyc3a ^ 2 ≠ cyc3b ∧ cyc3a ^ 2 ≠ cyc3b ^ 2 ∧ cyc3b ≠ cyc3b ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> apply_fun (fun g : alternatingGroup (Fin 6) =>
    ((g : Equiv.Perm (Fin 6)) 0, (g : Equiv.Perm (Fin 6)) 3)) at h <;> revert h <;>
    simp only [cyc3a, cyc3b, pow_two, Subgroup.coe_mul] <;> decide

theorem nonempty_alt6_of_catalogIs_isA6 {S : Type} [Group S] (hS : catalogIs S S8.isA6) :
    Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  cases i with
  | cyclic p hp => rcases hi with h | h <;> exact (show False from h).elim
  | alternating n hn =>
    rcases hi with h | h
    · have h6 : n = 6 := h
      subst h6
      exact ⟨e⟩
    · exact (show False from h).elim
  | sporadic s => rcases hi with h | h <;> exact (show False from h).elim
  | lie j =>
    rcases hi with h | h
    · exact (show False from h).elim
    · rcases j with ⟨d, hv⟩
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · exact (show False from h).elim
        · have h9 : q.card = 9 := h
          obtain ⟨p, f, hpp, hf⟩ := q
          have hpf : p ^ f = 3 ^ 2 := by
            have hc := TauCeti.PrimePower.card_def (⟨p, f, hpp, hf⟩ : TauCeti.PrimePower)
            simp only at hc
            rw [← hc]
            exact h9
          obtain ⟨hp3, hf2⟩ := Nat.Prime.pow_inj' hpp Nat.prime_three hf.ne' (by norm_num) hpf
          subst hp3
          subst hf2
          haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
          have eP := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨3, 2, hpp, hf⟩ hv
          have hcard : Nat.card (GaloisField 3 2) = 9 := by
            rw [GaloisField.card 3 2 (by norm_num)]
            norm_num
          obtain ⟨e2⟩ := CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine hcard
          exact ⟨e.trans (eP.trans e2)⟩
        · exact (show False from h).elim
      | _ => exact (show False from h).elim

theorem cyc3a2_cube : (cyc3a ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, cyc3a_cube, one_pow]

theorem cyc3b2_cube : (cyc3b ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, cyc3b_cube, one_pow]

theorem cyc3a2_ne_one : cyc3a ^ 2 ≠ 1 := by
  intro h
  apply cyc3a_ne_one
  calc cyc3a = cyc3a ^ 3 * (cyc3a ^ 2)⁻¹ := by group
    _ = 1 := by rw [cyc3a_cube, h, inv_one, mul_one]

theorem cyc3b2_ne_one : cyc3b ^ 2 ≠ 1 := by
  intro h
  apply cyc3b_ne_one
  calc cyc3b = cyc3b ^ 3 * (cyc3b ^ 2)⁻¹ := by group
    _ = 1 := by rw [cyc3b_cube, h, inv_one, mul_one]

theorem not_all_sylow_three_cyclic_of_isA6 {S : Type} [Group S] [Finite S]
    (hS : catalogIs S S8.isA6) : ¬ ∀ Q : Sylow 3 S, IsCyclic ↥(↑Q : Subgroup S) := by
  obtain ⟨e⟩ := nonempty_alt6_of_catalogIs_isA6 hS
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := cyc3_distinct
  have hE := isPGroup_three_closure cyc3a cyc3b cyc3a_cube cyc3b_cube cyc3_comm
  have hES := hE.map e.symm.toMonoidHom
  have hmA : cyc3a ∈ Subgroup.closure ({cyc3a, cyc3b} : Set (alternatingGroup (Fin 6))) :=
    Subgroup.subset_closure (by simp)
  have hmB : cyc3b ∈ Subgroup.closure ({cyc3a, cyc3b} : Set (alternatingGroup (Fin 6))) :=
    Subgroup.subset_closure (by simp)
  have hinj : ∀ g : alternatingGroup (Fin 6), e.symm g = 1 → g = 1 :=
    fun g h => (map_eq_one_iff e.symm e.symm.injective).mp h
  refine not_all_sylow_three_cyclic_of_four _ hES (e.symm cyc3a) (e.symm (cyc3a ^ 2))
    (e.symm cyc3b) (e.symm (cyc3b ^ 2)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Subgroup.mem_map_of_mem _ hmA
  · exact Subgroup.mem_map_of_mem _ (Subgroup.pow_mem _ hmA 2)
  · exact Subgroup.mem_map_of_mem _ hmB
  · exact Subgroup.mem_map_of_mem _ (Subgroup.pow_mem _ hmB 2)
  · rw [← map_pow, cyc3a_cube, map_one]
  · rw [← map_pow, cyc3a2_cube, map_one]
  · rw [← map_pow, cyc3b_cube, map_one]
  · rw [← map_pow, cyc3b2_cube, map_one]
  · intro h; exact cyc3a_ne_one (hinj _ h)
  · intro h; exact cyc3a2_ne_one (hinj _ h)
  · intro h; exact cyc3b_ne_one (hinj _ h)
  · intro h; exact cyc3b2_ne_one (hinj _ h)
  · intro h; exact d1 (e.symm.injective h)
  · intro h; exact d2 (e.symm.injective h)
  · intro h; exact d3 (e.symm.injective h)
  · intro h; exact d4 (e.symm.injective h)
  · intro h; exact d5 (e.symm.injective h)
  · intro h; exact d6 (e.symm.injective h)

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

end
