module

public import CFSG.CGT.PushingUpLit.CGT6.RouteCAlt
public import CFSG.CGT.PushingUpLit.CGT6.EmbThree
public import CFSG.CGT.PushingUpLit.CGT6.RouteCLin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.SectionRank.Ccomm
open scoped Matrix

section Central

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem Emb5Cfg.lift_of_central (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1) {y d t : MulAut V}
    (hY : Y = Subgroup.zpowers y) (hgen : Subgroup.zpowers d ⊔ Y ⊔ Subgroup.zpowers t = G)
    (hyd : y * d = d * y) (hyt : y * t = t * y) : ∃ X, Lift5 G Y X := by
  have hyc : ∀ g ∈ G, g * y = y * g := by
    intro g hg
    have hGc : G ≤ Subgroup.centralizer ({y} : Set (MulAut V)) := by
      rw [← hgen]
      refine sup_le (sup_le ?_ ?_) ?_
      · refine Subgroup.zpowers_le.mpr ?_
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hyd
      · rw [hY]
        refine Subgroup.zpowers_le.mpr ?_
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        rfl
      · refine Subgroup.zpowers_le.mpr ?_
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hyt
    exact (Subgroup.mem_centralizer_iff.mp (hGc hg) y rfl).symm
  have hYG : Y ≤ G := by
    rw [← hgen]
    exact le_sup_of_le_left le_sup_right
  have hnorm : G ≤ Subgroup.normalizer (Y : Set (MulAut V)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hcg : Commute g y := hyc g hg
    have hgx : ∀ m : ℤ, g * y ^ m * g⁻¹ = y ^ m := fun m => by
      have h2 : Commute g (y ^ m) := hcg.zpow_right m
      rw [h2.eq]
      group
    have hgx' : ∀ m : ℤ, g⁻¹ * y ^ m * g = y ^ m := fun m => by
      have h2 : Commute g⁻¹ (y ^ m) := (hcg.zpow_right m).inv_left
      rw [h2.eq]
      group
    constructor
    · intro hx
      rw [hY] at hx ⊢
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [hgx m]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) m
    · intro hx
      rw [hY] at hx ⊢
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hx' : x = y ^ m := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * y ^ m * g := by rw [← hm]
          _ = y ^ m := hgx' m
      rw [hx']
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) m
  have hsub : (Y.subgroupOf G).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hYG).2 hnorm).isSubnormal
  exact ⟨Y, Lift5.of_subnormal hV cfg.adm.h3 cfg.adm.h4 hYG hsub⟩

end Central


section Coord

variable {V : Type} [CommGroup V] {n : ℕ}

theorem elemAutEquivGL_trans (e : V ≃* Multiplicative (Fin n → ZMod 2))
    (A : MulAut (Multiplicative (Fin n → ZMod 2))) (x : MulAut V) :
    elemAutEquivGL (e.trans A) x =
      mulAutEquivGL n A * elemAutEquivGL e x * (mulAutEquivGL n A)⁻¹ := by
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun u => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  obtain ⟨v, rfl⟩ := exists_coord_eq (e.trans A) u
  have hc : coord (e.trans A) v =
      (mulAutEquivGL n A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ coord e v := by
    have := mulAutEquivGL_mulVec n A (coord e v)
    rw [this]
    simp [coord]
  rw [mulVec_coord, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hc, Matrix.mulVec_mulVec (M := ((mulAutEquivGL n A)⁻¹ : GL (Fin n) (ZMod 2)).val),
    Units.inv_mul, Matrix.one_mulVec, mulVec_coord]
  simp only [coord, MulEquiv.trans_apply]
  rw [mulAutEquivGL_mulVec n A, ofAdd_toAdd]

theorem exists_coord_of_conj (e : V ≃* Multiplicative (Fin n → ZMod 2)) (y d t : MulAut V)
    {P : (Matrix (Fin n) (Fin n) (ZMod 2) × Matrix (Fin n) (Fin n) (ZMod 2) ×
      Matrix (Fin n) (Fin n) (ZMod 2)) → Prop}
    (h : ∃ g₀ : GL (Fin n) (ZMod 2),
      P (((g₀ * elemAutEquivGL e y * g₀⁻¹ : GL (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)),
        ((g₀ * elemAutEquivGL e d * g₀⁻¹ : GL (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)),
        ((g₀ * elemAutEquivGL e t * g₀⁻¹ : GL (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)))) :
    ∃ e' : V ≃* Multiplicative (Fin n → ZMod 2),
      P (((elemAutEquivGL e' y : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)),
        ((elemAutEquivGL e' d : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)),
        ((elemAutEquivGL e' t : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) := by
  obtain ⟨g₀, hg⟩ := h
  refine ⟨e.trans ((mulAutEquivGL n).symm g₀), ?_⟩
  rw [elemAutEquivGL_trans, elemAutEquivGL_trans, elemAutEquivGL_trans]
  simpa using hg

end Coord


section Reach

variable {k : ℕ}

@[expose] def reachN (gens : List (Equiv.Perm (Fin k))) (i : Fin k) : ℕ → Finset (Fin k)
  | 0 => {i}
  | m + 1 => reachN gens i m ∪
      gens.foldr (fun (g : Equiv.Perm (Fin k)) acc =>
        (reachN gens i m).image (g : Fin k → Fin k) ∪ acc) ∅

theorem mem_foldr_image {gens : List (Equiv.Perm (Fin k))} {S : Finset (Fin k)} {j : Fin k}
    (h : j ∈ gens.foldr (fun (g : Equiv.Perm (Fin k)) acc => S.image (g : Fin k → Fin k) ∪ acc) ∅) :
    ∃ g ∈ gens, ∃ j' ∈ S, g j' = j := by
  induction gens with
  | nil => simp at h
  | cons g gs ih =>
    simp only [List.foldr_cons, Finset.mem_union, Finset.mem_image] at h
    rcases h with ⟨j', hj', rfl⟩ | h
    · exact ⟨g, List.mem_cons_self, j', hj', rfl⟩
    · obtain ⟨g', hg', j', hj', rfl⟩ := ih h
      exact ⟨g', List.mem_cons_of_mem _ hg', j', hj', rfl⟩

theorem reachN_sound (gens : List (Equiv.Perm (Fin k))) (i : Fin k) (m : ℕ) {j : Fin k}
    (h : j ∈ reachN gens i m) :
    ∃ p ∈ Subgroup.closure {g | g ∈ gens}, p i = j := by
  induction m generalizing j with
  | zero =>
    simp only [reachN, Finset.mem_singleton] at h
    exact ⟨1, Subgroup.one_mem _, by rw [h]; rfl⟩
  | succ m ih =>
    simp only [reachN, Finset.mem_union] at h
    rcases h with h | h
    · exact ih h
    · obtain ⟨g, hg, j', hj', rfl⟩ := mem_foldr_image h
      obtain ⟨p, hp, hpi⟩ := ih hj'
      exact ⟨g * p, Subgroup.mul_mem _ (Subgroup.subset_closure hg) hp, by simp [hpi]⟩

theorem transitive_of_reachN (gens : List (Equiv.Perm (Fin k))) (i₀ : Fin k)
    (h : reachN gens i₀ k = Finset.univ) (i j : Fin k) :
    ∃ p ∈ Subgroup.closure {g | g ∈ gens}, p i = j := by
  obtain ⟨pi, hpi, hpi'⟩ := reachN_sound gens i₀ k (h ▸ Finset.mem_univ i)
  obtain ⟨pj, hpj, hpj'⟩ := reachN_sound gens i₀ k (h ▸ Finset.mem_univ j)
  exact ⟨pj * pi⁻¹, Subgroup.mul_mem _ hpj (Subgroup.inv_mem _ hpi), by
    rw [Equiv.Perm.mul_apply, ← hpi']
    simp [hpj']⟩

end Reach


section Mat

variable {V : Type} [CommGroup V] {n : ℕ}

noncomputable def AltData.ofMatrix (e : V ≃* Multiplicative (Fin n → ZMod 2))
    {y d t : MulAut V} {a : ℕ} (w₀ : Fin (2 * a + 1) → (Fin n → ZMod 2))
    (hinj : Function.Injective w₀)
    (hspan : ∀ u : Fin n → ZMod 2, ∃ s : Finset (Fin (2 * a + 1)), ∑ i ∈ s, w₀ i = u)
    (x₁ x₂ x₃ : Fin (2 * a + 1)) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (pd pe : Equiv.Perm (Fin (2 * a + 1)))
    (hy : ∀ i, (elemAutEquivGL e y : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w₀ i =
      w₀ ((Equiv.swap x₁ x₂ * Equiv.swap x₁ x₃) i))
    (hd : ∀ i, (elemAutEquivGL e d : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w₀ i = w₀ (pd i))
    (he : ∀ i, ((elemAutEquivGL e t : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (elemAutEquivGL e d : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (elemAutEquivGL e t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ w₀ i = w₀ (pe i))
    (ht : ∀ i, ∃ j, (elemAutEquivGL e t : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w₀ i = w₀ j)
    (hreach : reachN [Equiv.swap x₁ x₂ * Equiv.swap x₁ x₃, pd, pe] ⟨0, by omega⟩ (2 * a + 1) =
      Finset.univ)
    (hfix : ∀ u : Fin n → ZMod 2,
      (elemAutEquivGL e y : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u = u →
      (elemAutEquivGL e d : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u = u →
      ((elemAutEquivGL e t : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (elemAutEquivGL e d : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (elemAutEquivGL e t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ u = u → u = 0)
    (ht2 : t ^ 2 = 1) (hne : w₀ ⟨0, by omega⟩ ≠ 0) : AltData y d t a := by
  classical
  let w : Fin (2 * a + 1) → V := fun i => e.symm (Multiplicative.ofAdd (w₀ i))
  have hw : ∀ i, coord e (w i) = w₀ i := fun i => by simp [w, coord]
  have hwinj : Function.Injective w := fun i j h => hinj (by rw [← hw i, ← hw j, h])
  have hcoord0 : coord e (1 : V) = 0 := by simp [coord]
  have hmat : ∀ x : MulAut V, ∀ v : V,
      (elemAutEquivGL e x : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ coord e v = coord e (x v) :=
    fun x v => mulVec_coord e x v
  refine
    { w := w, injective := hwinj, span := ?_,
      py := Equiv.swap x₁ x₂ * Equiv.swap x₁ x₃, pd := pd, pe := pe,
      hpy := fun i => coord_injective e (by rw [← hmat, hw, hy, hw]),
      hpd := fun i => coord_injective e (by rw [← hmat, hw, hd, hw]),
      hpe := fun i => coord_injective e (by
        have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht2)
        rw [htinv, MulAut.mul_apply, MulAut.mul_apply, ← hmat t, ← hmat d, ← hmat t, hw,
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, he i, hw]),
      hpt := fun i => ?_,
      three := Equiv.Perm.isThreeCycle_swap_mul_swap_same h12 h13 h23,
      trans := ?_, fix := ?_, ne_one := ?_ }
  · rw [eq_top_iff]
    intro v _
    obtain ⟨s, hs⟩ := hspan (coord e v)
    have : v = ∏ i ∈ s, w i := by
      apply coord_injective e
      rw [← hs]
      simp only [coord, map_prod, toAdd_prod, hw]
    rw [this]
    exact Subgroup.prod_mem _ fun i _ => Subgroup.subset_closure ⟨i, rfl⟩
  · obtain ⟨j, hj⟩ := ht i
    exact ⟨j, coord_injective e (by rw [← hmat, hw, hj, hw])⟩
  · intro i j
    have := transitive_of_reachN [Equiv.swap x₁ x₂ * Equiv.swap x₁ x₃, pd, pe] ⟨0, by omega⟩
      hreach i j
    have hset : {g | g ∈ [Equiv.swap x₁ x₂ * Equiv.swap x₁ x₃, pd, pe]} =
        ({Equiv.swap x₁ x₂ * Equiv.swap x₁ x₃, pd, pe} :
          Set (Equiv.Perm (Fin (2 * a + 1)))) := by
      ext g
      simp
    rwa [hset] at this
  · intro v hyv hdv htv
    apply coord_injective e
    rw [hcoord0]
    refine hfix _ ?_ ?_ ?_
    · rw [hmat, hyv]
    · rw [hmat, hdv]
    · have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht2)
      have h1 : t (d (t v)) = v := by
        have := htv
        rw [htinv] at this
        simpa [MulAut.mul_apply] using this
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmat t v, hmat d (t v),
        hmat t (d (t v)), h1]
  · intro h
    apply hne
    have := congrArg (coord e) h
    rw [hw, hcoord0] at this
    exact this

end Mat

end CFSG.CGT.PushingUpLit.CGT6
