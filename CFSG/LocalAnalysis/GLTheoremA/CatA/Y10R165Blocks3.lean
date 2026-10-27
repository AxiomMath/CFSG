module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks2

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open CFSG.RankThree.LocalRank (natCast_card_subgroup_ne_zero)
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  exists_coe_add_of_isCompl)
open scoped DirectSum BigOperators

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
variable {p : ℕ}

private theorem zpow_eq_pow_toNat {G : Type*} [Group G] {x : G} {q : ℕ} (hq : 0 < q) (hx : x ^ q = 1)
    (n : ℤ) : x ^ n = x ^ (n % (q : ℤ)).toNat := by
  rw [zpow_eq_zpow_emod n (by rw [zpow_natCast]; exact hx), ← zpow_natCast]
  congr 1
  rw [Int.toNat_of_nonneg (Int.emod_nonneg n (by exact_mod_cast hq.ne'))]

theorem pow_blockEnd_eq_one (hp : p.Prime) (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A)
    (D : Hyperplane A p) : ((t D : V ≃ₗ[F] V) ^ p) = 1 := by
  have h := map_pow A.subtype (t D) p
  rw [pow_eq_one A hA (t D), map_one] at h
  exact h.symm

theorem exists_mul_pow_of_mem_sup_zpowers (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (a : ↥A) (D : Hyperplane A p) :
    ∃ (d : ↥A) (n : ℕ), d ∈ D.1 ∧ a = d * (t D) ^ n := by
  haveI : IsMulCommutative ↥A := hA.1
  letI : CommGroup ↥A := { (inferInstance : Group ↥A) with mul_comm := fun a b => mul_comm' a b }
  have htop : D.1 ⊔ Subgroup.zpowers (t D) = ⊤ := by
    refine HyperBlocks.sup_zpowers_eq hp le_top ?_ (Subgroup.mem_top (t D)) (ht D)
    rw [Subgroup.relIndex_top_right]
    exact D.2
  have ha : a ∈ D.1 ⊔ Subgroup.zpowers (t D) := by rw [htop]; exact Subgroup.mem_top a
  obtain ⟨d, hd, u, hu, hdu⟩ := Subgroup.mem_sup.mp ha
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu
  refine ⟨d, (n % (p : ℤ)).toNat, hd, ?_⟩
  rw [← hdu, show u = (t D) ^ n from hn.symm,
    zpow_eq_pow_toNat (G := ↥A) (x := t D) hp.pos (pow_eq_one A hA (t D)) n]

theorem pow_blockEnd_apply_eq (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D : Hyperplane A p} {d : ↥A}
    (hd : d ∈ D.1) (n : ℕ) {w : V} (hw : w ∈ blockSpace A D.1) :
    (((d * (t D) ^ n : ↥A)) : V ≃ₗ[F] V) w = ((t D : V ≃ₗ[F] V) ^ n) w := by
  haveI : IsMulCommutative ↥A := hA.1
  have h1 : (((d * (t D) ^ n : ↥A)) : V ≃ₗ[F] V)
      = (d : V ≃ₗ[F] V) * (((t D) ^ n : ↥A) : V ≃ₗ[F] V) := map_mul A.subtype d ((t D) ^ n)
  have h2 : (((t D) ^ n : ↥A) : V ≃ₗ[F] V) = (t D : V ≃ₗ[F] V) ^ n := map_pow A.subtype (t D) n
  have h3 : (d : V ≃ₗ[F] V) (((t D : V ≃ₗ[F] V) ^ n) w) = ((t D : V ≃ₗ[F] V) ^ n) w := by
    have hcomm : (d : V ≃ₗ[F] V) * ((t D : V ≃ₗ[F] V) ^ n)
        = ((t D : V ≃ₗ[F] V) ^ n) * (d : V ≃ₗ[F] V) := by
      have hdn : ((d * (t D) ^ n : ↥A)) = ((t D) ^ n * d : ↥A) := by
        rw [mul_comm' d ((t D) ^ n)]
      calc (d : V ≃ₗ[F] V) * ((t D : V ≃ₗ[F] V) ^ n)
          = (d : V ≃ₗ[F] V) * ((((t D) ^ n : ↥A)) : V ≃ₗ[F] V) := by rw [h2]
        _ = (((d * (t D) ^ n : ↥A)) : V ≃ₗ[F] V) := (map_mul A.subtype d ((t D) ^ n)).symm
        _ = ((((t D) ^ n * d : ↥A)) : V ≃ₗ[F] V) := by rw [hdn]
        _ = ((((t D) ^ n : ↥A)) : V ≃ₗ[F] V) * (d : V ≃ₗ[F] V) := map_mul A.subtype _ d
        _ = ((t D : V ≃ₗ[F] V) ^ n) * (d : V ≃ₗ[F] V) := by rw [h2]
    calc (d : V ≃ₗ[F] V) (((t D : V ≃ₗ[F] V) ^ n) w)
        = ((d : V ≃ₗ[F] V) * ((t D : V ≃ₗ[F] V) ^ n)) w := (LinearEquiv.mul_apply ..).symm
      _ = (((t D : V ≃ₗ[F] V) ^ n) * (d : V ≃ₗ[F] V)) w := by rw [hcomm]
      _ = ((t D : V ≃ₗ[F] V) ^ n) ((d : V ≃ₗ[F] V) w) := LinearEquiv.mul_apply ..
      _ = ((t D : V ≃ₗ[F] V) ^ n) w := by rw [(mem_blockSpace A).mp hw |>.1 d hd]
  rw [h1, h2]
  change (d : V ≃ₗ[F] V) (((t D : V ≃ₗ[F] V) ^ n) w) = ((t D : V ≃ₗ[F] V) ^ n) w
  exact h3

abbrev blockEndOf (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) (a : ↥A)
    (D : Hyperplane A p) : V ≃ₗ[F] V :=
  glue (isCompl_blockSpace_ker A hp hpF hA D)
    (restrictEquiv (blockSpace A D.1) (a : V ≃ₗ[F] V)
      (fun u hu => blockSpace_invariant A hp hpF hA hu)
      (fun u hu => blockSpace_invariant A hp hpF hA (a := a⁻¹) hu)) 1

theorem blockEndOf_apply_mem (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (a : ↥A) (D : Hyperplane A p) {u : V} (hu : u ∈ blockSpace A D.1) :
    blockEndOf A hp hpF hA a D u = (a : V ≃ₗ[F] V) u := by
  have h := glue_apply (isCompl_blockSpace_ker A hp hpF hA D)
    (restrictEquiv (blockSpace A D.1) (a : V ≃ₗ[F] V)
      (fun u hu => blockSpace_invariant A hp hpF hA hu)
      (fun u hu => blockSpace_invariant A hp hpF hA (a := a⁻¹) hu)) 1
    (⟨u, hu⟩ : ↥(blockSpace A D.1))
    (⟨0, Submodule.zero_mem _⟩ : ↥(LinearMap.ker (projBlock A hp hpF hA D)))
  simpa using h

theorem blockEndOf_apply_of_ker (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (a : ↥A) (D : Hyperplane A p) {r : V} (hr : r ∈ LinearMap.ker (projBlock A hp hpF hA D)) :
    blockEndOf A hp hpF hA a D r = r := by
  have h := glue_apply (isCompl_blockSpace_ker A hp hpF hA D)
    (restrictEquiv (blockSpace A D.1) (a : V ≃ₗ[F] V)
      (fun u hu => blockSpace_invariant A hp hpF hA hu)
      (fun u hu => blockSpace_invariant A hp hpF hA (a := a⁻¹) hu)) 1
    (⟨0, Submodule.zero_mem _⟩ : ↥(blockSpace A D.1))
    (⟨r, hr⟩ : ↥(LinearMap.ker (projBlock A hp hpF hA D)))
  simpa using h

theorem blockEndOf_apply_fixed (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (a : ↥A) (D : Hyperplane A p) {c : V} (hc : c ∈ fixedSpaceOf A) :
    blockEndOf A hp hpF hA a D c = c :=
  blockEndOf_apply_of_ker A hp hpF hA a D (by
    rw [LinearMap.mem_ker]; exact projBlock_apply_fixed A hp hpF hA D hc)

theorem blockEndOf_apply_of_mem_block (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (a : ↥A) {D E : Hyperplane A p} (hDE : E ≠ D) {v : V} (hv : v ∈ blockSpace A E.1) :
    blockEndOf A hp hpF hA a D v = v :=
  blockEndOf_apply_of_ker A hp hpF hA a D (by
    rw [LinearMap.mem_ker]; exact projBlock_apply_of_mem_block A hp hpF hA hDE hv)

theorem blockEnd_apply_eq (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) (v : V) :
    blockEnd A hp hpF hA t ht D v
      = v + ((t D : V ≃ₗ[F] V) (projBlock A hp hpF hA D v) - projBlock A hp hpF hA D v) := by
  obtain ⟨u, r, hcu, rfl⟩ :=
    exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
  have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
    rw [LinearMap.mem_ker]; exact r.2
  have h1 : projBlock A hp hpF hA D ((u : V) + (r : V)) = projBlock A hp hpF hA D (u : V) := by
    rw [map_add, projBlock_apply_of_mem A hp hpF hA D u.2, LinearMap.mem_ker.mp hr, add_zero]
  rw [map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
    blockEnd_apply_of_ker A hp hpF hA t ht D hr, h1, projBlock_apply_of_mem A hp hpF hA D u.2]
  abel

theorem blockEndOf_apply_eq (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (a : ↥A) (D : Hyperplane A p) (v : V) :
    blockEndOf A hp hpF hA a D v
      = v + ((a : V ≃ₗ[F] V) (projBlock A hp hpF hA D v) - projBlock A hp hpF hA D v) := by
  obtain ⟨u, r, hcu, rfl⟩ :=
    exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
  have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
    rw [LinearMap.mem_ker]; exact r.2
  have h1 : projBlock A hp hpF hA D ((u : V) + (r : V)) = projBlock A hp hpF hA D (u : V) := by
    rw [map_add, projBlock_apply_of_mem A hp hpF hA D u.2, LinearMap.mem_ker.mp hr, add_zero]
  rw [map_add, blockEndOf_apply_mem A hp hpF hA a D u.2,
    blockEndOf_apply_of_ker A hp hpF hA a D hr, h1, projBlock_apply_of_mem A hp hpF hA D u.2]
  abel

theorem projBlock_apply_blockEndOf (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (a : ↥A) {D E : Hyperplane A p} (hDE : E ≠ D) (v : V) :
    projBlock A hp hpF hA D (blockEndOf A hp hpF hA a E v) = projBlock A hp hpF hA D v := by
  rw [blockEndOf_apply_eq, map_add, map_sub,
    projBlock_apply_of_mem_block A hp hpF hA hDE
      (blockSpace_invariant A hp hpF hA (projBlock_apply_mem A hp hpF hA E v)),
    projBlock_apply_of_mem_block A hp hpF hA hDE (projBlock_apply_mem A hp hpF hA E v)]
  abel

theorem blockEndOf_commute (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (a b : ↥A) {D E : Hyperplane A p} (hDE : E ≠ D) :
    Commute (blockEndOf A hp hpF hA a D) (blockEndOf A hp hpF hA b E) := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    blockEndOf_apply_eq A hp hpF hA a D (blockEndOf A hp hpF hA b E v),
    blockEndOf_apply_eq A hp hpF hA b E (blockEndOf A hp hpF hA a D v),
    projBlock_apply_blockEndOf A hp hpF hA b hDE v,
    projBlock_apply_blockEndOf A hp hpF hA a (Ne.symm hDE) v,
    blockEndOf_apply_eq A hp hpF hA b E v, blockEndOf_apply_eq A hp hpF hA a D v]
  abel

theorem blockEndOf_eq_zpow_blockEnd (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {a : ↥A} {D : Hyperplane A p} {d : ↥A} (hd : d ∈ D.1) (n : ℕ)
    (ha : a = d * (t D) ^ n) :
    blockEndOf A hp hpF hA a D = (blockEnd A hp hpF hA t ht D) ^ n := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, r, hcu, rfl⟩ :=
    exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
  have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
    rw [LinearMap.mem_ker]; exact r.2
  rw [blockEnd_pow_apply A hp hpF hA t ht D n u.2 hr, map_add,
    blockEndOf_apply_mem A hp hpF hA a D u.2, blockEndOf_apply_of_ker A hp hpF hA a D hr,
    ha, pow_blockEnd_apply_eq A hp hpF hA t ht hd n u.2]

theorem noncommProd_blockEndOf_apply_fixed (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (a : ↥A) {c : V} (hc : c ∈ fixedSpaceOf A)
    (s : Finset (Hyperplane A p))
    (comm : (s : Set (Hyperplane A p)).Pairwise (Function.onFun Commute (fun D => blockEndOf A hp hpF hA a D))) :
    (s.noncommProd (fun D => blockEndOf A hp hpF hA a D) comm) c = c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.noncommProd_insert_of_notMem s b _ comm hb, LinearEquiv.mul_apply,
      ih (fun x hx y hy hxy => comm (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy) hxy),
      blockEndOf_apply_fixed A hp hpF hA a b hc]

theorem noncommProd_blockEndOf_apply_of_forall_ne (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (a : ↥A) (D : Hyperplane A p) {w : V}
    (hw : w ∈ blockSpace A D.1) (s : Finset (Hyperplane A p))
    (comm : (s : Set (Hyperplane A p)).Pairwise (Function.onFun Commute
      (fun E => blockEndOf A hp hpF hA a E)))
    (hne : ∀ E ∈ s, E ≠ D) :
    (s.noncommProd (fun E => blockEndOf A hp hpF hA a E) comm) w = w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.noncommProd_insert_of_notMem s b _ comm hb, LinearEquiv.mul_apply,
      ih (fun x hx y hy hxy => comm (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy) hxy)
        (fun E hE => hne E (Finset.mem_insert_of_mem hE)),
      blockEndOf_apply_of_mem_block A hp hpF hA a
        (Ne.symm (hne b (Finset.mem_insert_self b s))) hw]

theorem noncommProd_blockEndOf_apply_mem (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (a : ↥A) (D : Hyperplane A p) {w : V}
    (hw : w ∈ blockSpace A D.1) (s : Finset (Hyperplane A p))
    (comm : (s : Set (Hyperplane A p)).Pairwise (Function.onFun Commute
      (fun E => blockEndOf A hp hpF hA a E)))
    (hs : D ∈ s) :
    (s.noncommProd (fun E => blockEndOf A hp hpF hA a E) comm) w = (a : V ≃ₗ[F] V) w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs (by simp)
  | insert b s' hb ih =>
    rw [Finset.noncommProd_insert_of_notMem s' b _ comm hb, LinearEquiv.mul_apply]
    have hcomm' : (s' : Set (Hyperplane A p)).Pairwise (Function.onFun Commute
        (fun E => blockEndOf A hp hpF hA a E)) :=
      fun x hx y hy hxy => comm (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy) hxy
    by_cases hbD : b = D
    · subst hbD
      rw [noncommProd_blockEndOf_apply_of_forall_ne A hp hpF hA a b hw s' hcomm'
          (fun E hE => by rintro rfl; exact hb hE),
        blockEndOf_apply_mem A hp hpF hA a b hw]
    · have hDs' : D ∈ s' := by
        rcases Finset.mem_insert.mp hs with h | h
        · exact absurd h.symm hbD
        · exact h
      rw [ih hcomm' hDs',
        blockEndOf_apply_of_mem_block A hp hpF hA a (D := b) (E := D) (fun h => hbD h.symm)
          (blockSpace_invariant A hp hpF hA hw)]

theorem noncommProd_blockEndOf_eq (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (a : ↥A) (comm : ((Finset.univ : Finset (Hyperplane A p)) : Set (Hyperplane A p)).Pairwise
      (Function.onFun Commute (fun D => blockEndOf A hp hpF hA a D))) :
    (Finset.univ.noncommProd (fun D => blockEndOf A hp hpF hA a D) comm) = (a : V ≃ₗ[F] V) := by
  classical
  have hK : fixedSpaceOf A ⊔ (⨆ D : Hyperplane A p, blockSpace A D.1) ≤
      LinearMap.ker ((Finset.univ.noncommProd (fun D => blockEndOf A hp hpF hA a D) comm :
        V ≃ₗ[F] V).toLinearMap - (a : V →ₗ[F] V)) := by
    refine sup_le ?_ (iSup_le fun D => ?_)
    · intro c hc
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      rw [show (a : V →ₗ[F] V) c = c from (mem_fixedSpaceOf A).mp hc a]
      exact noncommProd_blockEndOf_apply_fixed A hp hpF hA a hc Finset.univ comm
    · intro w hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      simpa only [LinearEquiv.coe_toLinearMap] using
        noncommProd_blockEndOf_apply_mem A hp hpF hA a D hw Finset.univ comm (Finset.mem_univ D)
  have htop := sup_fixedSpaceOf_iSup_blockSpace A hp hpF hA
  have hKtop : (⊤ : Submodule F V) ≤ LinearMap.ker
      ((Finset.univ.noncommProd (fun D => blockEndOf A hp hpF hA a D) comm :
        V ≃ₗ[F] V).toLinearMap - (a : V →ₗ[F] V)) := htop ▸ hK
  refine LinearEquiv.ext fun v => ?_
  have hv := hKtop (Submodule.mem_top : v ∈ (⊤ : Submodule F V))
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearEquiv.coe_toLinearMap]
    using hv

theorem mem_closure_blockEnd (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (a : ↥A) :
    (a : V ≃ₗ[F] V) ∈ Subgroup.closure (Set.range (blockEnd A hp hpF hA t ht)) := by
  classical
  choose d n hd hn using exists_mul_pow_of_mem_sup_zpowers A hp hpF hA t ht a
  have commOf : ((Finset.univ : Finset (Hyperplane A p)) : Set (Hyperplane A p)).Pairwise
      (Function.onFun Commute (fun D => blockEndOf A hp hpF hA a D)) :=
    fun D _ E _ hne => blockEndOf_commute A hp hpF hA a a (Ne.symm hne)
  have commPow : ((Finset.univ : Finset (Hyperplane A p)) : Set (Hyperplane A p)).Pairwise
      (Function.onFun Commute (fun D => blockEnd A hp hpF hA t ht D ^ n D)) :=
    fun D _ E _ hne =>
      (blockEndOf_commute A hp hpF hA (t D) (t E) (Ne.symm hne)).pow_pow (n D) (n E)
  have hprod : (Finset.univ.noncommProd (fun D => blockEndOf A hp hpF hA a D) commOf)
      = Finset.univ.noncommProd (fun D => blockEnd A hp hpF hA t ht D ^ n D) commPow :=
    (Finset.noncommProd_congr rfl (fun D _ =>
      (blockEndOf_eq_zpow_blockEnd A hp hpF hA t ht (a := a) (D := D) (d := d D) (hd := hd D)
        (n := n D) (ha := hn D)).symm) commPow).symm
  rw [← noncommProd_blockEndOf_eq A hp hpF hA a commOf, hprod]
  exact Subgroup.noncommProd_mem (Subgroup.closure (Set.range (blockEnd A hp hpF hA t ht)))
    (t := Finset.univ) commPow (fun D _ => Subgroup.pow_mem _
      (Subgroup.subset_closure (k := Set.range (blockEnd A hp hpF hA t ht)) ⟨D, rfl⟩) _)

theorem le_closure_blockEnd (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) :
    (A : Set (V ≃ₗ[F] V)) ⊆
      Subgroup.closure (Set.range (blockEnd A hp hpF hA t ht)) :=
  fun _ ha => mem_closure_blockEnd A hp hpF hA t ht ⟨_, ha⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

