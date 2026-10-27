module

public import CFSG.LieType.Universal.SymplecticExtras.Unipotent
import all CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.LieType.Universal.Symplectic.SpExtras

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  TauCeti.GLSymplecticFin

variable {n : ℕ} {F : Type} [Field F]

noncomputable def corootHom (k : Fin n) : Fˣ →* (Fin n → Fˣ) where
  toFun c := corootVec n F k c
  map_one' := by
    funext a
    simp [corootVec]
  map_mul' c d := by
    funext a
    simp only [corootVec, Pi.mul_apply]
    split_ifs <;> simp [mul_comm]

theorem mem_torus_iff {k : Fin n} {x : StatedSp n F} :
    x ∈ torus n F k ↔ ∃ c : Fˣ, x = equivStatedSp n F (diagonal (corootVec n F k c)) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hle : Subgroup.closure (Set.range fun c : Fˣ => diagonal (R := F) (corootVec n F k c)) ≤
        (diagonal.comp (corootHom (F := F) k)).range :=
      Subgroup.closure_le _ |>.mpr fun z ⟨c, hc⟩ => ⟨c, hc⟩
    obtain ⟨c, rfl⟩ := hle hy
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact diagonal_mem_torus n F k c

theorem exists_diagonal_of_mem_iSup_torus {x : StatedSp n F} (hx : x ∈ ⨆ i, torus n F i) :
    ∃ t : Fin n → Fˣ, x = equivStatedSp n F (diagonal t) := by
  refine Subgroup.iSup_induction _ hx (C := fun x => ∃ t : Fin n → Fˣ,
    x = equivStatedSp n F (diagonal t)) (fun k y hy => ?_) ⟨1, by rw [map_one, map_one]⟩ ?_
  · obtain ⟨c, rfl⟩ := mem_torus_iff.1 hy
    exact ⟨_, rfl⟩
  · rintro y z ⟨t, rfl⟩ ⟨t', rfl⟩
    exact ⟨t * t', by rw [map_mul, map_mul]⟩

theorem torus_commute (i j : Fin n) (h : StatedSp n F) (hh : h ∈ torus n F i)
    (h' : StatedSp n F) (hh' : h' ∈ torus n F j) : Commute h h' := by
  obtain ⟨c, rfl⟩ := mem_torus_iff.1 hh
  obtain ⟨d, rfl⟩ := mem_torus_iff.1 hh'
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm]

noncomputable def prefixProd (k : Fin n) : (Fin n → Fˣ) →* Fˣ where
  toFun t := ∏ a ∈ Finset.univ.filter (fun a : Fin n => a.val ≤ k.val), t a
  map_one' := by simp
  map_mul' t t' := by simp [Finset.prod_mul_distrib]

theorem corootVec_eq_mul (j : Fin n) (c : Fˣ) :
    corootVec n F j c = Pi.mulSingle j c *
      (if h : j.val + 1 < n then Pi.mulSingle ⟨j.val + 1, h⟩ c⁻¹ else 1) := by
  funext a
  simp only [corootVec, Pi.mul_apply, Pi.mulSingle_apply]
  by_cases h : j.val + 1 < n
  · rw [dite_eq_left h]
    simp only [Pi.mulSingle_apply, Fin.ext_iff]
    split_ifs <;> first | (simp; done) | (exfalso; omega)
  · rw [dite_eq_right h]
    simp only [Pi.one_apply, mul_one, Fin.ext_iff]
    split_ifs <;> first | (simp; done) | (exfalso; omega)

theorem prefixProd_corootVec (j k : Fin n) (c : Fˣ) :
    prefixProd k (corootVec n F j c) = if j = k then c else 1 := by
  rw [corootVec_eq_mul, map_mul]
  have hsingle : ∀ (i : Fin n) (d : Fˣ), prefixProd k (Pi.mulSingle i d) =
      if i.val ≤ k.val then d else 1 := by
    intro i d
    change ∏ a ∈ Finset.univ.filter (fun a : Fin n => a.val ≤ k.val), Pi.mulSingle i d a = _
    rw [Finset.prod_pi_mulSingle']
    simp
  rw [hsingle]
  by_cases h : j.val + 1 < n
  · rw [dite_eq_left h, hsingle]
    simp only
    rcases lt_trichotomy j.val k.val with hjk | hjk | hjk
    · rw [ite_eq_left hjk.le, ite_eq_left (by omega), ite_eq_right (Fin.ne_of_val_ne hjk.ne),
        mul_inv_cancel]
    · rw [ite_eq_left hjk.le, ite_eq_right (by omega), ite_eq_left (Fin.ext hjk), mul_one]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (Fin.ne_of_val_ne hjk.ne'), mul_one]
  · rw [dite_eq_right h, map_one, mul_one]
    have hk := k.2
    rcases eq_or_ne j k with rfl | hjk
    · rw [ite_eq_left le_rfl, ite_eq_left rfl]
    · have : k.val < j.val := by
        have := Fin.val_ne_of_ne hjk
        omega
      rw [ite_eq_right (by omega), ite_eq_right hjk]

theorem torus_iSupIndep : iSupIndep (torus n F) := by
  intro k
  rw [Subgroup.disjoint_def]
  intro x hxk hx
  obtain ⟨c, rfl⟩ := mem_torus_iff.1 hxk
  have hP : ∃ t : Fin n → Fˣ, equivStatedSp n F (diagonal (corootVec n F k c)) =
      equivStatedSp n F (diagonal t) ∧ prefixProd k t = 1 := by
    rw [iSup_subtype'] at hx
    refine Subgroup.iSup_induction _ hx (C := fun x => ∃ t : Fin n → Fˣ,
      x = equivStatedSp n F (diagonal t) ∧ prefixProd k t = 1) (fun j y hy => ?_)
      ⟨1, by rw [map_one, map_one], map_one _⟩ ?_
    · obtain ⟨d, rfl⟩ := mem_torus_iff.1 hy
      exact ⟨_, rfl, by rw [prefixProd_corootVec, ite_eq_right j.2]⟩
    · rintro y z ⟨t, rfl, ht⟩ ⟨t', rfl, ht'⟩
      exact ⟨t * t', by rw [map_mul, map_mul], by rw [map_mul, ht, ht', mul_one]⟩
  obtain ⟨t, ht, ht1⟩ := hP
  have := diagonal_injective ((equivStatedSp n F).injective ht)
  rw [← this, prefixProd_corootVec, ite_eq_left rfl] at ht1
  subst ht1
  change equivStatedSp n F (diagonal (corootHom k 1)) = 1
  rw [map_one, map_one, map_one]

theorem torus_inf_posPart :
    (⨆ i, torus n F i) ⊓
      (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartanC n) ∅ ∧ 0 < ht γ}, rootGroup n F γ) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxt, hxp⟩
  rw [Subgroup.mem_bot]
  obtain ⟨t, rfl⟩ := exists_diagonal_of_mem_iSup_torus hxt
  have hpos := idBelow_of_mem_iSup 1 _ (fun γ hγ => ⟨hγ.1, by have := hγ.2; omega⟩) hxp
  apply mat_injective
  rw [map_one, mat_equiv_diagonal]
  ext a b
  by_cases hab : a = b
  · subst hab
    have := hpos a a (by simp)
    rwa [mat_equiv_diagonal] at this
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]

end CFSG.LieType.Universal.Symplectic.SpExtras
