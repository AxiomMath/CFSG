module

public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycles
public import CFSG.ClassicalInvolution.Phan.Geometry.Cycles

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary Module

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ}

@[expose] def IsGeomWalk (σ : K ≃+* K) (W : Submodule K (Fin m → K)) {x : ↥(nsPts σ W)}
    (c : (collGraph σ W).Walk x x) : Prop :=
  ∃ A : Submodule K (Fin m → K), A ≤ W ∧ Nondeg σ A ∧ 2 ≤ finrank K A ∧
    finrank K A < finrank K W ∧ ∀ v ∈ c.support, v.1 ≤ A

@[expose] def geomWalks (σ : K ≃+* K) (W : Submodule K (Fin m → K)) (x : ↥(nsPts σ W)) :
    Set ((collGraph σ W).Walk x x) :=
  {c | IsGeomWalk σ W c}

variable {W : Submodule K (Fin m → K)}

theorem mem_geomWalks {x : ↥(nsPts σ W)} {c : (collGraph σ W).Walk x x} :
    c ∈ geomWalks σ W x ↔ IsGeomWalk σ W c := Iff.rfl

theorem isGeomWalk_of_le {x : ↥(nsPts σ W)} {c : (collGraph σ W).Walk x x}
    {A : Submodule K (Fin m → K)} (hAW : A ≤ W) (hA : Nondeg σ A) (h2 : 2 ≤ finrank K A)
    (hlt : finrank K A < finrank K W) (hv : ∀ v ∈ c.support, v.1 ≤ A) : IsGeomWalk σ W c :=
  ⟨A, hAW, hA, h2, hlt, hv⟩

theorem isGeomWalk_of_finrank_eq_two {x : ↥(nsPts σ W)} {c : (collGraph σ W).Walk x x}
    {A : Submodule K (Fin m → K)} (hAW : A ≤ W) (hA : Nondeg σ A) (h2 : finrank K A = 2)
    (hlt : finrank K A < finrank K W) (hv : ∀ v ∈ c.support, v.1 ≤ A) : IsGeomWalk σ W c :=
  isGeomWalk_of_le hAW hA h2.ge hlt hv

theorem isGeomWalk_of_finrank_eq_three {x : ↥(nsPts σ W)} {c : (collGraph σ W).Walk x x}
    {A : Submodule K (Fin m → K)} (hAW : A ≤ W) (hA : Nondeg σ A) (h3 : finrank K A = 3)
    (hlt : finrank K A < finrank K W) (hv : ∀ v ∈ c.support, v.1 ≤ A) : IsGeomWalk σ W c :=
  isGeomWalk_of_le hAW hA (by omega) hlt hv

theorem IsGeomWalk.reverse {x : ↥(nsPts σ W)} {c : (collGraph σ W).Walk x x}
    (h : IsGeomWalk σ W c) : IsGeomWalk σ W c.reverse := by
  obtain ⟨A, hAW, hA, h2, hlt, hv⟩ := h
  exact ⟨A, hAW, hA, h2, hlt, fun v hv' => hv v (by simpa using hv')⟩

theorem geomWalks_reverse (x : ↥(nsPts σ W)) {c : (collGraph σ W).Walk x x}
    (h : c ∈ geomWalks σ W x) : c.reverse ∈ geomWalks σ W x :=
  IsGeomWalk.reverse h

theorem two_le_finrank_of_adj {x y : ↥(nsPts σ W)} (h : (collGraph σ W).Adj x y)
    {Y : Submodule K (Fin m → K)} (hx : x.1 ≤ Y) (hy : y.1 ≤ Y) : 2 ≤ finrank K Y := by
  have h2 := finrank_sup_of_ne_pts x.2.2.1 y.2.2.1 h.1
  rw [← h2]
  exact Submodule.finrank_mono (sup_le hx hy)

theorem isGeomWalk_of_inProperNondeg {x : ↥(nsPts σ W)} {c : (collGraph σ W).Walk x x}
    {S : Set (Submodule K (Fin m → K))} (hS : InProperNondeg σ W S)
    (hv : ∀ v ∈ c.support, v.1 ∈ S)
    (hadj : ∃ y z : ↥(nsPts σ W), (collGraph σ W).Adj y z ∧ y.1 ∈ S ∧ z.1 ∈ S) :
    IsGeomWalk σ W c := by
  obtain ⟨A, hAW, hA, hlt, hAS⟩ := hS
  obtain ⟨y, z, hyz, hy, hz⟩ := hadj
  exact ⟨A, hAW, hA, two_le_finrank_of_adj hyz (hAS _ hy) (hAS _ hz), hlt,
    fun v hv' => hAS _ (hv v hv')⟩

theorem isGeomWalk_triangle {x y z : ↥(nsPts σ W)} (hxy : (collGraph σ W).Adj x y)
    (hyz : (collGraph σ W).Adj y z) (hzx : (collGraph σ W).Adj z x)
    (h : InProperNondeg σ W {x.1, y.1, z.1}) :
    IsGeomWalk σ W (.cons hxy (.cons hyz (.cons hzx .nil)) : (collGraph σ W).Walk x x) := by
  refine isGeomWalk_of_inProperNondeg h ?_ ⟨x, y, hxy, by simp, by simp⟩
  intro v hv
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> simp

section Decomp

variable (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
include hσ hK

theorem coneTriangles_geomWalks (hq : 4 ≤ q) (hW : Nondeg σ W) (hd : 4 ≤ finrank K W) :
    ConeTriangles (geomWalks σ W) := by
  intro a b c hab hbc hca
  obtain ⟨e, he, hae, hbe, hce, h₁, h₂, h₃⟩ := exists_cone_point_triangle_of_four_le hσ hK hq hW hd
    a.2 b.2 c.2 hab (hca.symm) hbc
  let e' : ↥(nsPts σ W) := ⟨e, he⟩
  have hae' : (collGraph σ W).Adj a e' := hae
  have hbe' : (collGraph σ W).Adj b e' := hbe
  have hce' : (collGraph σ W).Adj c e' := hce
  refine ⟨e', hae', hbe', hce', ?_, ?_, ?_⟩
  · exact cycleHomotopic_of_mem _ (isGeomWalk_triangle hab hbe' hae'.symm h₁)
  · exact cycleHomotopic_of_mem _ (isGeomWalk_triangle hbc hce' hbe'.symm h₃)
  · exact cycleHomotopic_of_mem _
      (isGeomWalk_triangle hca hae' hce'.symm (by rwa [Set.insert_comm] at h₂))

theorem commonNeighbour4_collGraph (hq : 4 ≤ q) (hW : Nondeg σ W) (hd : 4 ≤ finrank K W) :
    CommonNeighbour4 (G := collGraph σ W) := by
  intro a b c d hab hbc hcd hda
  obtain ⟨e, he, hOa, hOb, hce, hde⟩ := exists_orth_collinear_two hσ hK hq hW hd a.2 b.2 hab
    c.2 d.2
  exact ⟨⟨e, he⟩, IsCollinear.of_orth hσ a.2 he (hOa.symm hσ),
    IsCollinear.of_orth hσ b.2 he (hOb.symm hσ), hce, hde⟩

theorem apexPentagon_collGraph (hq : 4 ≤ q) (hW : Nondeg σ W) (hd : 4 ≤ finrank K W) :
    ApexPentagon (G := collGraph σ W) := by
  intro a c d hcd
  obtain ⟨f, hf, hOc, hOd, haf⟩ := exists_orth_collinear_one hσ hK (by omega) hW hd c.2 d.2 hcd
    a.2
  exact ⟨⟨f, hf⟩, IsCollinear.of_orth hσ hf c.2 hOc, IsCollinear.of_orth hσ hf d.2 hOd, haf⟩

theorem collinear_decomp (hq : 4 ≤ q) (hW : Nondeg σ W) (hd : 4 ≤ finrank K W)
    {x : ↥(nsPts σ W)} (w : (collGraph σ W).Walk x x) :
    CycleHomotopic (geomWalks σ W) w .nil :=
  cycleTrivial_of_cycles_le_five (geomWalks σ W)
    (collGraph_connected hσ hK (by omega) hW (by omega))
    (collGraph_ediam_le_two hσ hK (by omega) hW (by omega))
    (coneTriangles_geomWalks hσ hK hq hW hd) (commonNeighbour4_collGraph hσ hK hq hW hd)
    (apexPentagon_collGraph hσ hK hq hW hd) x w

theorem collinear_homotopic (hq : 4 ≤ q) (hW : Nondeg σ W) (hd : 4 ≤ finrank K W)
    {x y : ↥(nsPts σ W)} (p r : (collGraph σ W).Walk x y) :
    CycleHomotopic (geomWalks σ W) p r :=
  (cycleTrivial_iff_homotopic (geomWalks σ W)).1
    (fun _ w => collinear_decomp hσ hK hq hW hd w) x y p r

end Decomp

end CFSG.ClassicalInvolution.Phan
