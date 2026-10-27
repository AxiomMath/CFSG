module

public import CFSG.GH74.BNPair.Geometry
public import CFSG.GH74.BNPair.RootGroups
public import CFSG.GH74.BNPair.PathFixer

public section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem action_injective : Function.Injective D.action := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h : g⁻¹ = 1 := D.faithful g⁻¹ (fun v hv => by
    have := congrArg (fun σ : Equiv.Perm D.Vertex => (σ ⟨v, hv⟩ : Set X)) hg
    simpa [action, rankTwoAction] using this)
  simpa using h

theorem action_mem_graphAut (g : X) : D.action g ∈ graphAut D.graph :=
  fun u v => rankTwoAction_adj g u v

theorem exists_extension {π : List D.Vertex} (hπ : IsGLSPath D.graph π) (hlen : π.length = n + 1) :
    ∃ l : List D.Vertex, IsGLSPath D.graph l ∧ l.length = n + 2 ∧ π <+: l := by
  have hn := D.three_le
  obtain ⟨L, a, b, rfl⟩ : ∃ (L : List D.Vertex) (a b : D.Vertex), π = L ++ [a, b] := by
    rcases List.eq_nil_or_concat π with rfl | ⟨L', b, rfl⟩
    · simp at hlen
    · rcases List.eq_nil_or_concat L' with rfl | ⟨L, a, rfl⟩
      · simp at hlen; omega
      · exact ⟨L, a, b, by simp⟩
  obtain ⟨y, hy, hya⟩ : ∃ y, D.graph.Adj b y ∧ y ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsub : D.graph.neighborSet b ⊆ {a} := fun y hy => hcon y hy
    have h1 := Set.encard_le_encard hsub
    have h2 := D.lemma30_6_iv b
    simp only [Set.encard_singleton] at h1
    have : (3 : ℕ∞) ≤ 1 := h2.trans h1
    exact absurd this (by norm_num)
  refine ⟨L ++ [a, b, y], ?_, by simp at hlen ⊢; omega, ⟨[y], by simp⟩⟩
  have hπ' : IsGLSPath D.graph ((L ++ [a]) ++ [b]) := by simpa using hπ
  have := isGLSPath_concat (G := D.graph) (l := L ++ [a]) (y := b) (x := y)
  have hc := this.2 ⟨hπ', hy, fun w hw hwy => hya (by
    have : w = a := by simpa using hw.symm
    rw [← hwy, this])⟩
  simpa using hc

theorem pathFixer_eq_map_root {π : List D.Vertex} {r : ℤ} (hπ : IsGLSPath D.graph π)
    (hlen : π.length = n + 1)
    (hfix : ∀ x ∈ D.root r, ∀ v ∈ interiorVertices π, ∀ w, D.graph.Adj v w → D.action x w = w)
    (htrans : ∀ l l' : List D.Vertex, IsGLSPath D.graph l → IsGLSPath D.graph l' →
      l.length = n + 2 → l'.length = n + 2 → π <+: l → π <+: l' →
        ∃ x ∈ D.root r, l.map (D.action x) = l') :
    pathFixer D.graph π = (D.root r).map D.action := by
  have hn := D.three_le
  ext σ
  constructor
  · intro hσ
    have hσg : σ ∈ graphAut D.graph := (mem_pathFixer_iff.1 hσ).1
    have hσfix := pathFixer_fixes hπ hn hlen hσ
    obtain ⟨l, hl, hl2, hpre⟩ := D.exists_extension hπ hlen
    have hl' : IsGLSPath D.graph (l.map σ) :=
      IsGLSPath.map (G := D.graph) (g := σ) (fun v w => hσg v w) hl
    have hmapπ : π.map σ = π := by
      conv_rhs => rw [← List.map_id π]
      exact List.map_congr_left hσfix
    have hpre' : π <+: l.map σ := by
      have := hpre.map σ
      rwa [hmapπ] at this
    obtain ⟨x, hx, hxl⟩ := htrans l (l.map σ) hl hl' hl2 (by simpa using hl2) hpre hpre'
    have hρx : D.action x ∈ pathFixer D.graph π :=
      mem_pathFixer_iff.2 ⟨D.action_mem_graphAut x, hfix x hx⟩
    have hmem : (D.action x)⁻¹ * σ ∈ pathFixer D.graph π := mul_mem (inv_mem hρx) hσ
    have hall : ∀ v ∈ l, ((D.action x)⁻¹ * σ) v = v := by
      intro v hv
      have := List.map_inj_left.1 (hxl) v hv
      simp only [Equiv.Perm.mul_apply]
      rw [← this]
      simp
    have h1 : (D.action x)⁻¹ * σ = 1 :=
      D.polyHyp.eq_one_of_fix hl hlen hl2 hpre
        (g := (D.action x)⁻¹ * σ) (fun v w => (mem_pathFixer_iff.1 hmem).1 v w) hall
        (mem_pathFixer_iff.1 hmem).2
    exact ⟨x, hx, inv_mul_eq_one.1 h1⟩
  · rintro ⟨x, hx, rfl⟩
    exact mem_pathFixer_iff.2 ⟨D.action_mem_graphAut x, hfix x hx⟩

theorem exists_conj_root_one_or_n {i : ℤ} (hi : IsRoot n i) :
    ∃ m : D.N, conjBy (m : X) (D.root 1) = D.root i ∨ conjBy (m : X) (D.root n) = D.root i := by
  have hn := D.three_le
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective D.w₁
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective D.w₂
  obtain ⟨a1, a2, a3⟩ := D.roots.action₁ m₁ hm₁
  obtain ⟨b1, b2, b3⟩ := D.roots.action₂ m₂ hm₂
  have trans : ∀ (m m' : D.N) (j0 j j' : ℤ), conjBy (m : X) (D.root j0) = D.root j →
      conjBy (m' : X) (D.root j) = D.root j' →
        conjBy ((m * m' : D.N) : X) (D.root j0) = D.root j' := by
    intro m m' j0 j j' h h'
    rw [Subgroup.coe_mul, conjBy_mul, h, h']
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (∃ m : D.N, conjBy (m : X) (D.root 1) = D.root (k : ℤ) ∨
        conjBy (m : X) (D.root n) = D.root (k : ℤ)) ∧
      (∃ m : D.N, conjBy (m : X) (D.root 1) = D.root (-(k : ℤ)) ∨
        conjBy (m : X) (D.root n) = D.root (-(k : ℤ))) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk1 hkn
      by_cases hk : k = 1
      · subst hk
        refine ⟨⟨1, Or.inl ?_⟩, ⟨m₁, Or.inl ?_⟩⟩
        · simp [conjBy_one]
        · simpa using a1
      by_cases hk2 : k = 2
      · subst hk2
        have h4 := a3 (n : ℤ) (by omega) le_rfl
        refine ⟨⟨m₁, Or.inr ?_⟩, ⟨m₂ * m₁, Or.inr ?_⟩⟩
        · simpa using h4.1
        · refine trans m₂ m₁ n (-(n : ℤ)) (-((2 : ℕ) : ℤ)) b1 ?_
          simpa using h4.2
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
        obtain ⟨⟨m, hm⟩, ⟨m', hm'⟩⟩ := ih (j + 1) (by omega) (by omega) (by omega)
        have hb := b3 ((j + 1 : ℕ) : ℤ) (by omega) (by omega)
        have ha := a3 ((n : ℤ) - ((j + 1 : ℕ) : ℤ)) (by omega) (by omega)
        have e1 : (n : ℤ) + 2 - ((n : ℤ) - ((j + 1 : ℕ) : ℤ)) = ((j + 3 : ℕ) : ℤ) := by
          push_cast; ring
        rw [e1] at ha
        have ha2 := ha.2
        refine ⟨?_, ?_⟩
        · rcases hm with hm | hm
          · exact ⟨m * m₂ * m₁, Or.inl (trans _ _ 1 _ _ (trans _ _ 1 _ _ hm hb.1) ha.1)⟩
          · exact ⟨m * m₂ * m₁, Or.inr (trans _ _ (n : ℤ) _ _ (trans _ _ (n : ℤ) _ _ hm hb.1) ha.1)⟩
        · rcases hm' with hm' | hm'
          · exact ⟨m' * m₂ * m₁, Or.inl (trans _ _ 1 _ _ (trans _ _ 1 _ _ hm' hb.2) ha2)⟩
          · exact ⟨m' * m₂ * m₁, Or.inr (trans _ _ (n : ℤ) _ _ (trans _ _ (n : ℤ) _ _ hm' hb.2) ha2)⟩
  obtain ⟨hi0, hin⟩ := hi
  rcases lt_or_gt_of_ne hi0 with hneg | hpos
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = -i := ⟨(-i).toNat, by omega⟩
    have := (key k (by omega) (by omega)).2
    rw [hk, neg_neg] at this
    exact this
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = i := ⟨i.toNat, by omega⟩
    have := (key k (by omega) (by omega)).1
    rw [hk] at this
    exact this

theorem isTypeOne_or_isTypeTwo (v : D.Vertex) : D.IsTypeOne v ∨ D.IsTypeTwo v := by
  cases h : vtype D.B D.N D.w₁ D.w₂ v
  · exact Or.inr ((D.isTypeTwo_iff v).2 h)
  · exact Or.inl ((D.isTypeOne_iff v).2 h)

theorem map_xplus_eq (h9 : Lemma30_9.{u}) :
    D.Xplus.map D.action = pathFixerSpan D.graph n := by
  obtain ⟨π₁, π₂, hπ₁, hπ₂, hl₁, hl₂, ⟨a₁, ha₁, hta₁⟩, ⟨a₂, ha₂, hta₂⟩, hfix₂, htrans₂, hfix₁,
    htrans₁⟩ := h9 X n D
  have hn := D.three_le
  have hA₂ := D.pathFixer_eq_map_root hπ₂ hl₂ hfix₂ htrans₂
  have hA₁ := D.pathFixer_eq_map_root hπ₁ hl₁ hfix₁ htrans₁
  apply le_antisymm
  ·
    rw [Subgroup.map_le_iff_le_comap]
    unfold Xplus
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨m, hm⟩ := D.exists_conj_root_one_or_n hi
    have hconj : ∀ (j : ℤ) (π : List D.Vertex), IsGLSPath D.graph π → π.length = n + 1 →
        pathFixer D.graph π = (D.root j).map D.action → conjBy (m : X) (D.root j) = D.root i →
          D.action x ∈ pathFixerSpan D.graph n := by
      intro j π hπ hlen hA hmj
      have hxm : (m : X) * x * (m : X)⁻¹ ∈ D.root j := by
        have : x ∈ conjBy (m : X) (D.root j) := by rw [hmj]; exact hxi
        exact mem_conjBy_iff.1 this
      have hy : D.action ((m : X) * x * (m : X)⁻¹) ∈ pathFixer D.graph π := by
        rw [hA]
        exact ⟨_, hxm, rfl⟩
      refine mem_pathFixerSpan_of_map (σ := D.action ((m : X)⁻¹)) (D.action_mem_graphAut _) hπ hlen
        (τ := D.action x) ?_
      have : (D.action ((m : X)⁻¹))⁻¹ * D.action x * D.action ((m : X)⁻¹) =
          D.action ((m : X) * x * (m : X)⁻¹) := by
        simp [map_mul, map_inv, mul_assoc]
      rw [this]
      exact hy
    rcases hm with hm | hm
    · exact hconj 1 π₁ hπ₁ hl₁ hA₁ hm
    · exact hconj n π₂ hπ₂ hl₂ hA₂ hm
  ·
    unfold pathFixerSpan
    rw [Subgroup.closure_le]
    intro τ hτ
    obtain ⟨l, hl, hτl⟩ := Set.mem_iUnion₂.1 hτ
    obtain ⟨hl, hlen⟩ := hl
    have hne : l ≠ [] := by
      rintro rfl
      simp at hlen
    obtain ⟨u, hu⟩ : ∃ u, l.head? = some u := ⟨l.head hne, List.head?_eq_some_head hne⟩
    have hmain : ∀ (j : ℤ) (π : List D.Vertex), pathFixer D.graph π = (D.root j).map D.action →
        IsRoot n j → (∃ g : X, π.map (D.action g) = l) →
          τ ∈ (Subgroup.map D.action D.Xplus : Set _) := by
      intro j π hA hj ⟨g, hg⟩
      have hτ' : τ ∈ pathFixer D.graph (π.map (D.action g)) := by
        rw [hg]; exact hτl
      rw [mem_pathFixer_map (D.action_mem_graphAut g)] at hτ'
      rw [hA] at hτ'
      obtain ⟨x, hx, hxτ⟩ := hτ'
      refine ⟨g * x * g⁻¹, D.xplus_normal.conj_mem x (D.root_le_xplus hj hx) g, ?_⟩
      have : D.action (g * x * g⁻¹) = τ := by
        rw [map_mul, map_mul, map_inv, hxτ]
        group
      exact this
    rcases D.isTypeOne_or_isTypeTwo u with hu1 | hu2
    · obtain ⟨g, hg⟩ := lemma30_8 X n D n le_rfl π₁ l hπ₁ hl hl₁ hlen (by
        intro a b ha hb
        rw [ha₁] at ha
        rw [hu] at hb
        cases ha
        cases hb
        exact ⟨fun _ => hu1, fun _ => hta₁⟩)
      exact hmain 1 π₁ hA₁ ⟨by norm_num, by simp; omega⟩ ⟨g, hg⟩
    · obtain ⟨g, hg⟩ := lemma30_8 X n D n le_rfl π₂ l hπ₂ hl hl₂ hlen (by
        intro a b ha hb
        rw [ha₂] at ha
        rw [hu] at hb
        cases ha
        cases hb
        have h1 : ¬ D.IsTypeOne a₂ := by
          rw [D.isTypeOne_iff]; rw [D.isTypeTwo_iff] at hta₂; simp [hta₂]
        have h2 : ¬ D.IsTypeOne u := by
          rw [D.isTypeOne_iff]; rw [D.isTypeTwo_iff] at hu2; simp [hu2]
        exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩)
      exact hmain n π₂ hA₂ ⟨by omega, by simp⟩ ⟨g, hg⟩

end RankTwoSystem

@[expose] def CoordIso : Prop :=
  ∀ (X X' : Type u) [Group X] [Group X'] (n : ℕ) (D : RankTwoSystem X n) (D' : RankTwoSystem X' n)
    (φ : D.U ≃* D'.U),
    (∀ i : ℤ, 1 ≤ i → i ≤ n → ∀ x : D.U, (x : X) ∈ D.root i ↔ ((φ x : D'.U) : X') ∈ D'.root i) →
      Nonempty (D.graph ≃g D'.graph)

theorem theorem30_4_of_lemma30_9_of_coordIso (h9 : Lemma30_9.{u}) (hc : CoordIso.{u}) :
    Theorem30_4.{u} := by
  intro X X' _ _ n D D' φ hφ
  obtain ⟨e⟩ := hc X X' n D D' φ hφ
  have h1 := D.map_xplus_eq h9
  have h2 := D'.map_xplus_eq h9
  have h3 := pathFixerSpan_map_iso e n
  exact ⟨(((D.Xplus.equivMapOfInjective D.action D.action_injective).trans
    (MulEquiv.subgroupCongr h1)).trans
    ((MulEquiv.subgroupMap (Equiv.permCongrHom e.toEquiv) _).trans
      (MulEquiv.subgroupCongr h3))).trans
    ((MulEquiv.subgroupCongr h2).symm.trans
      (D'.Xplus.equivMapOfInjective D'.action D'.action_injective).symm)⟩

end CFSG.GH74.BNPair
