module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.Balance.BootstrapTriple
public import CFSG.ClassicalInvolution.Balance.PassTwoConj
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureDefs

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem card_closure_pair_le_four [Finite G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : Nat.card (Subgroup.closure ({x, y} : Set G)) ≤ 4 := by
  classical
  have c : y * x = x * y := hxy.symm
  have s1' : ∀ b, x * (x * b) = b := fun b => by rw [← mul_assoc, hx, one_mul]
  have c' : ∀ b, y * (x * b) = x * (y * b) := fun b => by rw [← mul_assoc, c, mul_assoc]
  have i1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have i2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have key : ∀ g (hg : g ∈ Subgroup.closure ({x, y} : Set G)),
      g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
    intro g hg
    refine Subgroup.closure_induction
      (p := fun g _ => g = 1 ∨ g = x ∨ g = y ∨ g = x * y) ?_ ?_ ?_ ?_ hg
    · intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with hu | hu <;> subst hu <;> simp
    · simp
    · rintro a b - - (ha | ha | ha | ha) (hb | hb | hb | hb) <;> subst ha <;> subst hb <;>
        simp [mul_assoc, hx, hy, s1', c, c']
    · rintro a - (ha | ha | ha | ha) <;> subst ha <;> simp [i1, i2, c]
  have hsub : (Subgroup.closure ({x, y} : Set G) : Set G) ⊆ ({1, x, y, x * y} : Finset G) := by
    intro g hg
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] using key g hg
  calc Nat.card (Subgroup.closure ({x, y} : Set G))
      = Nat.card ((Subgroup.closure ({x, y} : Set G) : Set G)) := rfl
    _ ≤ Nat.card (({1, x, y, x * y} : Finset G) : Set G) := Nat.card_mono (Set.toFinite _) hsub
    _ = Finset.card ({1, x, y, x * y} : Finset G) := Nat.card_eq_finsetCard _
    _ ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp

theorem exists_exactTriple_of_indepTriple [Finite G] {Ω : Set (Subgroup G)}
    (h : IndepTriple p f Ω) :
    ∃ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G), ExactTriple K₁ K₂ K₃ z₁ z₂ z₃ ∧
      z₁ * z₂ ≠ z₃ ∧ K₁ ∈ Ω ∧ K₂ ∈ Ω ∧ K₃ ∈ Ω ∧ IsClassicalMember p f K₁ z₁ ∧
        IsClassicalMember p f K₂ z₂ ∧ IsClassicalMember p f K₃ z₃ := by
  obtain ⟨K, z, hK, hcomm, hel, hcard⟩ := h
  have hc : ∀ i, IsCentralInvolution (K i) (z i) := fun i => (hK i).2.isCentralInvolution
  have hzz : ∀ i j, z i * z j = z j * z i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · exact hcomm i j hij (z i) (hc i).mem (z j) (hc j).mem
  have hle4 : ∀ x y : G, x * x = 1 → y * y = 1 → x * y = y * x →
      Set.range z ⊆ ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) → False := by
    intro x y hx hy hxy hsub
    have h1 : Subgroup.closure (Set.range z) ≤ Subgroup.closure ({x, y} : Set G) :=
      (Subgroup.closure_le _).mpr hsub
    have h2 := Subgroup.card_le_of_le h1
    have h3 := card_closure_pair_le_four hx hy hxy
    omega
  have hne : ∀ i j, i ≠ j → z i ≠ z j := by
    intro i j hij hz
    have key : ∀ (k : Fin 3), (∀ l, l = i ∨ l = j ∨ l = k) →
        Set.range z ⊆ ((Subgroup.closure ({z i, z k} : Set G) : Subgroup G) : Set G) := by
      intro k hk
      rintro _ ⟨l, rfl⟩
      rcases hk l with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · rw [← hz]; exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    have hexk : ∀ a b : Fin 3, a ≠ b → ∃ k : Fin 3, ∀ l, l = a ∨ l = b ∨ l = k := by decide
    obtain ⟨k, hk⟩ := hexk i j hij
    exact hle4 (z i) (z k) (hc i).sq (hc k).sq (hzz i k) (key k hk)
  have hind : z 0 * z 1 ≠ z 2 := by
    intro hd
    refine hle4 (z 0) (z 1) (hc 0).sq (hc 1).sq (hzz 0 1) ?_
    rintro _ ⟨l, rfl⟩
    fin_cases l
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · show z 2 ∈ ((Subgroup.closure ({z 0, z 1} : Set G) : Subgroup G) : Set G)
      rw [← hd]
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have T : ExactTriple (K 0) (K 1) (K 2) (z 0) (z 1) (z 2) :=
    { mem₁ := (hc 0).mem
      mem₂ := (hc 1).mem
      mem₃ := (hc 2).mem
      central₁ := fun k hk => ((hc 0).central k hk).symm
      central₂ := fun k hk => ((hc 1).central k hk).symm
      central₃ := fun k hk => ((hc 2).central k hk).symm
      sq₁ := (hc 0).sq
      sq₂ := (hc 1).sq
      sq₃ := (hc 2).sq
      ne_one₁ := (hc 0).ne_one
      ne_one₂ := (hc 1).ne_one
      ne_one₃ := (hc 2).ne_one
      comm₁₂ := hcomm 0 1 (by decide)
      comm₁₃ := hcomm 0 2 (by decide)
      comm₂₃ := hcomm 1 2 (by decide)
      ne₁₂ := hne 0 1 (by decide)
      ne₁₃ := hne 0 2 (by decide)
      ne₂₃ := hne 1 2 (by decide) }
  exact ⟨K 0, K 1, K 2, z 0, z 1, z 2, T, hind, (hK 0).1, (hK 1).1, (hK 2).1, (hK 0).2, (hK 1).2,
    (hK 2).2⟩

theorem omegaConnected_of_deltaConnected {Ω : Set (Subgroup G)}
    (h : CFSG.ClassicalInvolution.RouteD.DeltaConnected Ω) :
    CFSG.ClassicalInvolution.Generic.DeltaClosure.OmegaConnected Ω := by
  intro L hL L' hL'
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).mp
    (h.preconnected ⟨L, hL⟩ ⟨L', hL'⟩)
  refine Relation.ReflTransGen.lift
    (p := fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) (fun v : ↥Ω => (v : Subgroup G))
    (fun a b hab => ?_) _ _ hr
  obtain ⟨-, hcomm⟩ := CFSG.ClassicalInvolution.Models.commGraph_adj.mp hab
  exact ⟨b.2, hcomm⟩

end CFSG.ClassicalInvolution.Balance.Bootstrap
