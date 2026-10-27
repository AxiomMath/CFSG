module

public import CFSG.Fischer.Classification.SRG.Conference

public section

namespace CFSG.GroupTheory.TransitiveDegree36

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

def OrbitalRel (G : Type*) [Group G] [MulAction G X] (x : X) (A : Set X) (u v : X) : Prop :=
  ∃ g : G, g • x = u ∧ g⁻¹ • v ∈ A

section Orbital

variable {x : X} {A : Set X}

theorem orbitalRel_iff (hA : ∀ s ∈ stabilizer G x, ∀ y ∈ A, s • y ∈ A) {g : G} {u : X}
    (hg : g • x = u) (v : X) : OrbitalRel G x A u v ↔ g⁻¹ • v ∈ A := by
  constructor
  · rintro ⟨h, hh, hv⟩
    have hs : g⁻¹ * h ∈ stabilizer G x := by
      rw [mem_stabilizer_iff, mul_smul, hh, ← hg, inv_smul_smul]
    have := hA _ hs _ hv
    rwa [mul_smul, smul_inv_smul] at this
  · exact fun hv => ⟨g, hg, hv⟩

theorem orbitalRel_base (hA : ∀ s ∈ stabilizer G x, ∀ y ∈ A, s • y ∈ A) (v : X) :
    OrbitalRel G x A x v ↔ v ∈ A := by
  rw [orbitalRel_iff hA (one_smul G x), inv_one, one_smul]

theorem orbitalRel_smul (k : G) {u v : X} :
    OrbitalRel G x A (k • u) (k • v) ↔ OrbitalRel G x A u v := by
  constructor
  · rintro ⟨g, hg, hv⟩
    refine ⟨k⁻¹ * g, by rw [mul_smul, hg, inv_smul_smul], ?_⟩
    rw [mul_inv_rev, inv_inv, mul_smul]
    exact hv
  · rintro ⟨g, hg, hv⟩
    refine ⟨k * g, by rw [mul_smul, hg], ?_⟩
    rw [mul_inv_rev, mul_smul, inv_smul_smul]
    exact hv

theorem not_orbitalRel_self (hA : ∀ s ∈ stabilizer G x, ∀ y ∈ A, s • y ∈ A) (hxA : x ∉ A)
    [IsPretransitive G X] (u : X) : ¬OrbitalRel G x A u u := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G x u
  rw [orbitalRel_iff hA rfl, inv_smul_smul]
  exact hxA

theorem card_outNeighbors_eq (hA : ∀ s ∈ stabilizer G x, ∀ y ∈ A, s • y ∈ A)
    [IsPretransitive G X] (u : X) : Nat.card {v // OrbitalRel G x A u v} = Nat.card A := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G x u
  exact Nat.card_congr
    (Equiv.subtypeEquiv (MulAction.toPerm g⁻¹) fun v => orbitalRel_iff hA rfl v)

theorem card_inNeighbors_eq [Finite X] [IsPretransitive G X]
    (hA : ∀ s ∈ stabilizer G x, ∀ y ∈ A, s • y ∈ A) :
    Nat.card {u // OrbitalRel G x A u x} = Nat.card A := by
  classical
  have := Fintype.ofFinite X
  have hin : ∀ v : X,
      Nat.card {u // OrbitalRel G x A u v} = Nat.card {u // OrbitalRel G x A u x} := by
    intro v
    obtain ⟨g, rfl⟩ := exists_smul_eq G x v
    refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g⁻¹) fun u => ?_)
    change _ ↔ OrbitalRel G x A (g⁻¹ • u) x
    rw [← orbitalRel_smul g (u := g⁻¹ • u) (v := x), smul_inv_smul]
  have hsum : ∑ u : X, Nat.card {v // OrbitalRel G x A u v} =
      ∑ v : X, Nat.card {u // OrbitalRel G x A u v} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    exact Finset.sum_comm
  simp only [card_outNeighbors_eq hA, hin, Finset.sum_const, smul_eq_mul,
    Finset.card_univ] at hsum
  have hpos : 0 < Fintype.card X := Fintype.card_pos_iff.2 ⟨x⟩
  exact (Nat.eq_of_mul_eq_mul_left hpos hsum).symm

theorem orbitalRel_symm [Finite X] [IsPretransitive G X]
    (hA : ∀ s ∈ stabilizer G x, ∀ y ∈ A, s • y ∈ A) (hxA : x ∉ A) {B : Set X}
    (hcover : ∀ y, y = x ∨ y ∈ A ∨ y ∈ B)
    (hBorb : ∀ y ∈ B, ∀ z ∈ B, ∃ s ∈ stabilizer G x, s • y = z)
    (hAB : Nat.card A < Nat.card B) {u v : X} (huv : OrbitalRel G x A u v) :
    OrbitalRel G x A v u := by
  set S : Set X := {u | OrbitalRel G x A u x} with hSdef
  have hSinv : ∀ s ∈ stabilizer G x, ∀ y ∈ S, s • y ∈ S := by
    intro s hs y hy
    have h := (orbitalRel_smul s (u := y) (v := x)).2 hy
    rw [mem_stabilizer_iff.1 hs] at h
    exact h
  have hcardS : Nat.card S = Nat.card A := card_inNeighbors_eq hA
  have hSB : ∀ y ∈ S, y ∉ B := by
    intro y hyS hyB
    have hBS : B ⊆ S := by
      intro z hz
      obtain ⟨s, hs, rfl⟩ := hBorb y hyB z hz
      exact hSinv s hs y hyS
    have : Nat.card B ≤ Nat.card S := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hBS (Set.toFinite S)
    omega
  have hSA : S ⊆ A := by
    intro y hy
    rcases hcover y with rfl | hyA | hyB
    · exact absurd hy (not_orbitalRel_self hA hxA y)
    · exact hyA
    · exact absurd hyB (hSB y hy)
  have hSeq : S = A := Set.eq_of_subset_of_ncard_le hSA (by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcardS]) (Set.toFinite A)
  obtain ⟨g, rfl⟩ := exists_smul_eq G x u
  have h1 : OrbitalRel G x A x (g⁻¹ • v) := by
    rw [← orbitalRel_smul g (u := x) (v := g⁻¹ • v), smul_inv_smul]
    exact huv
  have h2 : g⁻¹ • v ∈ S := hSeq ▸ (orbitalRel_base hA _).1 h1
  have h3 := (orbitalRel_smul g).2 h2
  rwa [smul_inv_smul] at h3

end Orbital

theorem subdegrees_one_seven_twentyeight_obstruction [Finite X] (hX : Nat.card X = 36)
    [IsPretransitive G X] (x : X) (A B : Set X) (hA : A.ncard = 7) (hB : B.ncard = 28) :
    Set.range (fun y => orbit (stabilizer G x) y) ≠ {{x}, A, B} := by
  classical
  intro horb
  have := Fintype.ofFinite X
  have hmem : ∀ y, orbit (stabilizer G x) y ∈ ({{x}, A, B} : Set (Set X)) := fun y =>
    horb ▸ Set.mem_range_self y
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, orbit (stabilizer G x) a₀ = A := by
    have : A ∈ Set.range (fun y => orbit (stabilizer G x) y) := by simp [horb]
    exact this
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, orbit (stabilizer G x) b₀ = B := by
    have : B ∈ Set.range (fun y => orbit (stabilizer G x) y) := by simp [horb]
    exact this
  have horbx : orbit (stabilizer G x) x = {x} := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact mem_stabilizer_iff.1 s.2
    · intro hy
      rw [Set.mem_singleton_iff.1 hy]
      exact mem_orbit_self x
  have hxA : x ∉ A := by
    intro hx
    rw [← ha₀] at hx
    have := (orbit_eq_iff.2 hx).trans ha₀
    rw [horbx] at this
    rw [← this, Set.ncard_singleton] at hA
    omega
  have hxB : x ∉ B := by
    intro hx
    rw [← hb₀] at hx
    have := (orbit_eq_iff.2 hx).trans hb₀
    rw [horbx] at this
    rw [← this, Set.ncard_singleton] at hB
    omega
  have hcover : ∀ y, y = x ∨ y ∈ A ∨ y ∈ B := by
    intro y
    rcases hmem y with h | h | h
    · left
      have : y ∈ orbit (stabilizer G x) y := mem_orbit_self y
      rw [h] at this
      exact this
    · right; left
      rw [← h]
      exact mem_orbit_self y
    · right; right
      rw [← Set.mem_singleton_iff.1 h]
      exact mem_orbit_self y
  have hAinv : ∀ s ∈ stabilizer G x, ∀ y ∈ A, s • y ∈ A := by
    intro s hs y hy
    rw [← ha₀] at hy ⊢
    obtain ⟨t, rfl⟩ := hy
    exact ⟨⟨s, hs⟩ * t, mul_smul _ _ _⟩
  have horbit : ∀ {C : Set X} {c₀ : X}, orbit (stabilizer G x) c₀ = C →
      ∀ y ∈ C, ∃ s ∈ stabilizer G x, s • c₀ = y := by
    intro C c₀ hC y hy
    rw [← hC] at hy
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, t.2, rfl⟩
  have hBorb : ∀ y ∈ B, ∀ z ∈ B, ∃ s ∈ stabilizer G x, s • y = z := by
    intro y hy z hz
    obtain ⟨s, hs, rfl⟩ := horbit hb₀ y hy
    obtain ⟨t, ht, rfl⟩ := horbit hb₀ z hz
    exact ⟨t * s⁻¹, mul_mem ht (inv_mem hs), by rw [mul_smul, inv_smul_smul]⟩
  have hAB : Nat.card A < Nat.card B := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, hA, hB]
    norm_num
  let Γ : SimpleGraph X :=
    { Adj := OrbitalRel G x A
      symm := ⟨fun _ _ h => orbitalRel_symm hAinv hxA hcover hBorb hAB h⟩
      loopless := ⟨fun u h => not_orbitalRel_self hAinv hxA u h⟩ }
  have hadj : ∀ u v, Γ.Adj u v ↔ OrbitalRel G x A u v := fun _ _ => Iff.rfl
  have hcommon : ∀ (k : G) (v w : X),
      Fintype.card (Γ.commonNeighbors (k • v) (k • w)) = Fintype.card (Γ.commonNeighbors v w) := by
    intro k v w
    refine Fintype.card_congr (Equiv.subtypeEquiv (MulAction.toPerm k⁻¹) fun z => ?_)
    change z ∈ Γ.commonNeighbors (k • v) (k • w) ↔ k⁻¹ • z ∈ Γ.commonNeighbors v w
    rw [SimpleGraph.mem_commonNeighbors, SimpleGraph.mem_commonNeighbors, hadj, hadj, hadj, hadj,
      ← orbitalRel_smul k (u := v), ← orbitalRel_smul k (u := w), smul_inv_smul]
  have hedge : ∀ v w, Γ.Adj v w → ∃ k : G, k • x = v ∧ k • a₀ = w := by
    intro v w hvw
    obtain ⟨g, hg, hw⟩ := hvw
    obtain ⟨s, hs, hsa⟩ := horbit ha₀ _ hw
    refine ⟨g * s, by rw [mul_smul, mem_stabilizer_iff.1 hs, hg], ?_⟩
    rw [mul_smul, hsa, smul_inv_smul]
  have hnonedge : ∀ v w, v ≠ w → ¬Γ.Adj v w → ∃ k : G, k • x = v ∧ k • b₀ = w := by
    intro v w hvw hnadj
    obtain ⟨g, rfl⟩ := exists_smul_eq G x v
    have hw : g⁻¹ • w ∈ B := by
      rcases hcover (g⁻¹ • w) with h | h | h
      · exact absurd (by rw [← h, smul_inv_smul]) hvw
      · exact absurd ((orbitalRel_iff hAinv rfl w).2 h) hnadj
      · exact h
    obtain ⟨s, hs, hsb⟩ := horbit hb₀ _ hw
    refine ⟨g * s, by rw [mul_smul, mem_stabilizer_iff.1 hs], ?_⟩
    rw [mul_smul, hsb, smul_inv_smul]
  have hdeg : ∀ v, Γ.degree v = 7 := by
    intro v
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    have := card_outNeighbors_eq hAinv (G := G) v
    rw [Nat.card_coe_set_eq, hA] at this
    exact this
  have hsrg : Γ.IsSRGWith 36 7 (Fintype.card (Γ.commonNeighbors x a₀))
      (Fintype.card (Γ.commonNeighbors x b₀)) := by
    refine ⟨by rw [← Nat.card_eq_fintype_card, hX], hdeg, ?_, ?_⟩
    · intro v w hvw
      obtain ⟨k, rfl, rfl⟩ := hedge v w hvw
      exact hcommon k x a₀
    · intro v w hvw hnadj
      obtain ⟨k, rfl, rfl⟩ := hnonedge v w hvw hnadj
      exact hcommon k x b₀
  set ℓ := Fintype.card (Γ.commonNeighbors x a₀)
  set μ := Fintype.card (Γ.commonNeighbors x b₀)
  have hxa : Γ.Adj x a₀ := (orbitalRel_base hAinv a₀).2 (ha₀ ▸ mem_orbit_self a₀)
  have hℓ : ℓ < 7 := hdeg x ▸ hxa.card_commonNeighbors_lt_degree
  have hparam := hsrg.param_eq Γ (by norm_num)
  have hcases : (ℓ = 6 ∧ μ = 0) ∨ (ℓ = 2 ∧ μ = 1) := by omega
  rcases hcases with ⟨h6, h0⟩ | ⟨h2, h1⟩
  · obtain ⟨f, g, hfg, htr⟩ := hsrg.exists_multiplicities_of_roots (by norm_num) (r := 7) (s := -1)
      (by norm_num) (by rw [h6, h0]; norm_num) (by rw [h0]; norm_num)
    omega
  · obtain ⟨f, g, hfg, htr⟩ := hsrg.exists_multiplicities_of_roots (by norm_num) (r := 3) (s := -2)
      (by norm_num) (by rw [h2, h1]; norm_num) (by rw [h1]; norm_num)
    omega

theorem transitive_degree36_subdegrees_obstruction {X : Type*} [Finite X] (hX : Nat.card X = 36)
    (K : Subgroup (Equiv.Perm X)) [IsPretransitive K X] (x : X) (A B : Set X)
    (hA : A.ncard = 7) (hB : B.ncard = 28) :
    Set.range (fun y => orbit (stabilizer K x) y) ≠ {{x}, A, B} :=
  subdegrees_one_seven_twentyeight_obstruction hX x A B hA hB

end CFSG.GroupTheory.TransitiveDegree36
