
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Leaf
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeSplit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeDefs
public import CFSG.Sporadic.Co1Block.Perm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import Certificates.Data.ExceptionalSL3

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.ElemThree CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  Timmesfeld.Co1Leaf
open CFSG.Sporadic.Co1Schreier.Native (Rows mul one inv pow act wf)
open Matrix

noncomputable abbrev xL : List ℕ := CFSG.Sporadic.Co1Block.certVecs.toList

theorem certVecs_size : CFSG.Sporadic.Co1Block.certVecs.size = 98280 := by
  unfold CFSG.Sporadic.Co1Block.certVecs CFSG.Monster.B.Co2.Native.hexTable
  simp

theorem mem_xL {x : ℕ} (hx : x ∈ xL) :
    ∃ i : Fin 98280, CFSG.Sporadic.Co1Block.certVecs[i.val]! = x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < 98280 := by rw [Array.length_toList, certVecs_size] at hi; exact hi
  refine ⟨⟨i, hi'⟩, ?_⟩
  simp [Array.length_toList ▸ hi]

theorem certVecs_mem_xL (i : Fin 98280) : CFSG.Sporadic.Co1Block.certVecs[i.val]! ∈ xL := by
  have hi : i.val < CFSG.Sporadic.Co1Block.certVecs.size := by rw [certVecs_size]; exact i.isLt
  rw [getElem!_pos CFSG.Sporadic.Co1Block.certVecs i.val hi]
  exact Array.getElem_mem_toList hi

theorem xL_lt : ∀ x ∈ xL, x < 2 ^ 24 := by
  intro x hx
  obtain ⟨i, rfl⟩ := mem_xL hx
  exact CFSG.Sporadic.Co1Block.certVecs_lt i.isLt

theorem xL_maps
    (g : ↥GA) :
    ∀ x ∈ xL, ∃ y ∈ xL, (((g : GL24) : M24)) *ᵥ toVecD 24 x = toVecD 24 y := by
  intro x hx
  obtain ⟨i, rfl⟩ := mem_xL hx
  refine ⟨CFSG.Sporadic.Co1Block.certVecs[(CFSG.Sporadic.Co1Block.certRhoHom g i).val]!,
    certVecs_mem_xL _, ?_⟩
  have := CFSG.Sporadic.Co1Block.certVec_rho g i
  simp only [CFSG.Sporadic.Co1Block.certVec] at this
  exact this.symm

theorem finite_GA : Finite ↥GA :=
  Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)

theorem wf_iff (X : Rows) : wf X = true ↔ X.size = 24 ∧ ∀ x ∈ X, x < 2 ^ 24 := by
  simp only [CFSG.Sporadic.Co1Schreier.Native.wf, Bool.and_eq_true, beq_iff_eq]
  refine and_congr_right fun _ => ?_
  rw [Array.all_eq_true_iff_forall_mem]
  simp

theorem wf_mul {X Y : Rows} (hX : wf X = true) (hY : wf Y = true) : wf (mul X Y) = true := by
  rw [wf_iff] at hX hY ⊢
  refine ⟨by simp [CFSG.Sporadic.Co1Schreier.Native.mul, mulRows, hX.1], fun x hx => ?_⟩
  simp only [CFSG.Sporadic.Co1Schreier.Native.mul, mulRows, Array.mem_map] at hx
  obtain ⟨r, -, rfl⟩ := hx
  exact vecMulN_lt Y hY.2 r

theorem wf_one : wf (one ()) = true := by
  rw [wf_iff]
  refine ⟨by simp [CFSG.Sporadic.Co1Schreier.Native.one, idRows], fun x hx => ?_⟩
  simp only [CFSG.Sporadic.Co1Schreier.Native.one, idRows, Array.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by norm_num) i.isLt

theorem wf_pow {X : Rows} (hX : wf X = true) (e : ℕ) : wf (pow X e) = true := by
  induction e with
  | zero => exact wf_one
  | succ e ih => exact wf_mul ih hX

theorem wf_eltR {gs : List Rows} (hgs : ∀ g ∈ gs, wf g = true) (e : List ℕ) :
    wf (eltR gs e) = true := by
  unfold eltR
  have key : ∀ (l : List (Rows × ℕ)) (acc : Rows), (∀ ge ∈ l, wf ge.1 = true) → wf acc = true →
      wf (l.foldl (fun acc ge => mul acc (pow ge.1 ge.2)) acc) = true := by
    intro l
    induction l with
    | nil => intro acc _ h; exact h
    | cons ge l ih =>
      intro acc hl hacc
      rw [List.foldl_cons]
      exact ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (wf_mul hacc (wf_pow (hl ge List.mem_cons_self) _))
  exact key _ _ (fun ge hge => hgs _ (List.of_mem_zip hge).1) wf_one

def RowsRep (gs : List Rows) (fs : List ↥GA) : Prop :=
  List.Forall₂ (fun R (f : ↥GA) => MRep R (f : GL24)) gs fs

theorem mrep_eltR {gs : List Rows} {fs : List ↥GA} (h : RowsRep gs fs) (b : List ℕ) :
    MRep (eltR gs b) (eltG fs b : GL24) := by
  unfold eltR eltG
  have key : ∀ (gs : List Rows) (fs : List ↥GA), RowsRep gs fs → ∀ (b : List ℕ) (accR : Rows)
      (accG : ↥GA), MRep accR (accG : GL24) →
      MRep ((gs.zip b).foldl (fun acc ge => mul acc (pow ge.1 ge.2)) accR)
        (((fs.zip b).foldl (fun acc fb => acc * fb.1 ^ fb.2) accG : ↥GA) : GL24) := by
    intro gs fs h
    induction h with
    | nil => intro b accR accG hacc; simpa using hacc
    | cons hab _ ih =>
      intro b accR accG hacc
      cases b with
      | nil => simpa using hacc
      | cons k b =>
        simp only [List.zip_cons_cons, List.foldl_cons]
        refine ih b _ _ ?_
        rw [Subgroup.coe_mul, Subgroup.coe_pow]
        exact hacc.mul (hab.pow k)
  exact key gs fs h b _ _ (by rw [OneMemClass.coe_one]; exact MRep.one)

theorem RowsRep.length_eq {gs : List Rows} {fs : List ↥GA} (h : RowsRep gs fs) :
    gs.length = fs.length :=
  List.Forall₂.length_eq h

noncomputable def fnOf (fs : List ↥GA) : Fin fs.length → ↥GA := fun i => fs.get i

theorem eltG_eq_prod (fs : List ↥GA) (b : List ℕ) :
    eltG fs b = ((fs.zip b).map fun p => p.1 ^ p.2).prod := by
  unfold eltG
  suffices H : ∀ (l : List (↥GA × ℕ)) (acc : ↥GA),
      l.foldl (fun acc fb => acc * fb.1 ^ fb.2) acc = acc * (l.map fun p => p.1 ^ p.2).prod by
    rw [H, one_mul]
  intro l
  induction l with
  | nil => intro acc; rw [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | cons p l ih => intro acc; rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

theorem vecProd_eq_eltG (fs : List ↥GA) {b : List ℕ} (hlen : b.length = fs.length)
    (hb : ∀ x ∈ b, x < 3) : Co3T.vecProd (fnOf fs) (listVec fs.length b) = eltG fs b := by
  rw [eltG_eq_prod]
  unfold Co3T.vecProd
  congr 1
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    have hi : i < fs.length := by simpa using h1
    have hib : i < b.length := hlen ▸ hi
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_zip, fnOf, listVec,
      List.get_eq_getElem, Fin.cast_mk]
    congr 1
    rw [List.getD_eq_getElem _ _ hib, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (hb _ (List.getElem_mem hib))

theorem vecList_lt {k : ℕ} (a : Fin k → ZMod 3) : ∀ x ∈ vecList a, x < 3 := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact ZMod.val_lt (a i)

structure SplitData (A : List Rows) (fsA : List ↥GA) : Prop where
  rep : RowsRep A fsA
  wf : ∀ g ∈ A, wf g = true
  comm : ∀ f ∈ fsA, ∀ f' ∈ fsA, f * f' = f' * f
  cube : ∀ f ∈ fsA, f ^ 3 = 1
  nodup : ((expVecs 3 A.length).map (eltR A)).Nodup

namespace SplitData

variable {A : List Rows} {fsA : List ↥GA} (hS : SplitData A fsA)
include hS

theorem fn_comm : ∀ i j, Commute (fnOf fsA i) (fnOf fsA j) := fun _ _ =>
  hS.comm _ (List.get_mem _ _) _ (List.get_mem _ _)

theorem fn_cube : ∀ i, fnOf fsA i ^ 3 = 1 := fun _ => hS.cube _ (List.get_mem _ _)

noncomputable def φ : Multiplicative (Fin fsA.length → ZMod 3) →* ↥GA :=
  Co3T.vecProdHom (fnOf fsA) hS.fn_comm hS.fn_cube

theorem φ_apply (a : Fin fsA.length → ZMod 3) :
    hS.φ (Multiplicative.ofAdd a) = eltG fsA (vecList a) := by
  rw [φ, Co3T.vecProdHom_apply, ← vecProd_eq_eltG fsA (vecList_length a) (vecList_lt a),
    listVec_vecList]

theorem φ_injective : Function.Injective hS.φ := by
  intro x y hxy
  have hx := hS.φ_apply (Multiplicative.toAdd x)
  have hy := hS.φ_apply (Multiplicative.toAdd y)
  simp only [ofAdd_toAdd] at hx hy
  rw [hx, hy] at hxy
  have hrx := mrep_eltR hS.rep (vecList (Multiplicative.toAdd x))
  have hry := mrep_eltR hS.rep (vecList (Multiplicative.toAdd y))
  rw [hxy] at hrx
  have hrows := rowsMatrix_injective_of_wf (wf_eltR hS.wf _) (wf_eltR hS.wf _)
    (hrx.trans hry.symm)
  have hlen : A.length = fsA.length := hS.rep.length_eq
  have hmx : vecList (Multiplicative.toAdd x) ∈ expVecs 3 A.length := by
    rw [hlen]; exact vecList_mem_expVecs _
  have hmy : vecList (Multiplicative.toAdd y) ∈ expVecs 3 A.length := by
    rw [hlen]; exact vecList_mem_expVecs _
  have hv := List.inj_on_of_nodup_map hS.nodup hmx hmy hrows
  have := congrArg (listVec fsA.length) hv
  rw [listVec_vecList, listVec_vecList] at this
  exact Multiplicative.toAdd.injective this

noncomputable def T : Subgroup ↥GA := hS.φ.range

theorem T_comm : ∀ x ∈ hS.T, ∀ y ∈ hS.T, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem T_pow_three : ∀ x ∈ hS.T, x ^ 3 = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_pow]
  have : a ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, show ((3 : ℕ) : ZMod 3) = 0 from rfl,
      zero_mul]
  rw [this, map_one]

theorem T_elemAbelian : IsElemAbelian 3 hS.T :=
  ⟨⟨⟨fun x y => Subtype.ext (hS.T_comm x x.2 y y.2)⟩⟩, hS.T_pow_three⟩

theorem mem_T (i : Fin fsA.length) : fsA.get i ∈ hS.T := by
  refine ⟨Multiplicative.ofAdd (Pi.single i 1), ?_⟩
  rw [φ, Co3T.vecProdHom_apply, vecProd_single]
  rfl

theorem T_ne_bot (hk : 0 < fsA.length) : hS.T ≠ ⊥ := by
  intro h
  have hmem := hS.mem_T ⟨0, hk⟩
  rw [h, Subgroup.mem_bot] at hmem
  have h1 : hS.φ (Multiplicative.ofAdd (Pi.single ⟨0, hk⟩ 1)) = hS.φ 1 := by
    rw [map_one, φ, Co3T.vecProdHom_apply, vecProd_single]
    exact hmem
  have := congrArg (fun m => (Multiplicative.toAdd m) ⟨0, hk⟩) (hS.φ_injective h1)
  simp at this

end SplitData

theorem comm_eltG {n : ↥GA} {fs : List ↥GA} (h : ∀ f ∈ fs, n * f = f * n) (b : List ℕ) :
    n * eltG fs b = eltG fs b * n := by
  rw [eltG_eq_prod]
  have key : ∀ l : List ↥GA, (∀ x ∈ l, n * x = x * n) → n * l.prod = l.prod * n := by
    intro l
    induction l with
    | nil => intro _; rw [List.prod_nil, mul_one, one_mul]
    | cons x l ih =>
      intro hl
      rw [List.prod_cons, ← mul_assoc, hl x List.mem_cons_self, mul_assoc,
        ih fun y hy => hl y (List.mem_cons_of_mem _ hy), mul_assoc]
  refine key _ fun x hx => ?_
  obtain ⟨⟨f, e⟩, hfe, rfl⟩ := List.mem_map.1 hx
  have hf := h f (List.of_mem_zip hfe).1
  clear hx hfe
  induction e with
  | zero => rw [pow_zero, mul_one, one_mul]
  | succ e ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hf, mul_assoc]

def Good (F : List ↥GA) : Prop :=
  GLAPPrimeCoreOf 3 (Subgroup.centralizer {x | x ∈ F}) = ⊥

theorem centralizer_append (F F' : List ↥GA) :
    Subgroup.centralizer {x | x ∈ F} ⊓ Subgroup.centralizer {x | x ∈ F'} =
      Subgroup.centralizer {x | x ∈ F ++ F'} := by
  ext n
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_ofPred_eq, List.mem_append]
  constructor
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · exact h1 x hx
    · exact h2 x hx
  · intro h
    exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩

theorem set_kerBasis_eq {fsA : List ↥GA} {fl : List ℕ} (hfl : fl ∈ normVecs 3 fsA.length) :
    {x | ∃ b ∈ kerBasis 3 fl, x = Co3T.vecProd (fnOf fsA) (listVec fsA.length b)} =
      {x | x ∈ (kerBasis 3 fl).map (eltG fsA)} := by
  obtain ⟨hlen, -, -, -⟩ := normVecs_pivot hfl
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨j, -, -, rfl⟩ := mem_kerBasis hb
    exact ⟨_, hb, (vecProd_eq_eltG fsA (by rw [kerVec_length, hlen]) (kerVec_lt fl j)).symm⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨j, -, -, rfl⟩ := mem_kerBasis hb
    exact ⟨_, hb, (vecProd_eq_eltG fsA (by rw [kerVec_length, hlen]) (kerVec_lt fl j)).symm⟩

theorem SplitData.T_eq_closure {A : List Rows} {fsA : List ↥GA} (hS : SplitData A fsA) :
    hS.T = Subgroup.closure {x | x ∈ fsA} := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    have ha : hS.φ a = eltG fsA (vecList (Multiplicative.toAdd a)) := by
      rw [← hS.φ_apply, ofAdd_toAdd]
    rw [ha, eltG_eq_prod]
    refine Subgroup.list_prod_mem (K := Subgroup.closure {x | x ∈ fsA}) fun x hx => ?_
    obtain ⟨⟨f, e⟩, hfe, rfl⟩ := List.mem_map.1 hx
    have hf : f ∈ ({x | x ∈ fsA} : Set ↥GA) := (List.of_mem_zip hfe).1
    exact Subgroup.pow_mem _ (Subgroup.subset_closure hf) _
  · rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨i, rfl⟩ := List.get_of_mem hx
    exact hS.mem_T i

theorem centralizer_singleton_eq (R : ↥GA) :
    Subgroup.centralizer {x | x ∈ [R]} = Subgroup.centralizer ({R} : Set ↥GA) := by
  congr 1
  ext x
  simp

theorem aGA_length : aGA.length = 6 := by simp [aGA]

theorem nodup_expVecs (p : ℕ) : ∀ r, (expVecs p r).Nodup
  | 0 => List.nodup_singleton _
  | r + 1 => by
    rw [expVecs, List.nodup_flatMap]
    refine ⟨fun e _ => List.Nodup.map (fun k k' h => by simpa using h) List.nodup_range, ?_⟩
    refine (nodup_expVecs p r).imp fun {a b} hne x hx hx' => hne ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨k', -, h⟩ := List.mem_map.1 hx'
    exact (List.append_inj' h rfl).1.symm

theorem exists_six_of_length {l : List ℕ} (h : l.length = 6) :
    ∃ x0 x1 x2 x3 x4 x5, l = [x0, x1, x2, x3, x4, x5] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, l⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at h <;>
    first | omega | exact ⟨_, _, _, _, _, _, rfl⟩

noncomputable def aE (i : ℕ) (hi : i < 6) : ↥GA :=
  ⟨a ⟨i, hi⟩, A_le_GA (Subgroup.subset_closure (Set.mem_union_left _ (a_mem_E _)))⟩

theorem aGA_eq_aE : aGA = [aE 0 (by norm_num), aE 1 (by norm_num), aE 2 (by norm_num),
    aE 3 (by norm_num), aE 4 (by norm_num), aE 5 (by norm_num)] := rfl

theorem eltG_six_mul (g0 g1 g2 g3 g4 g5 : ↥GA) (x0 x1 x2 x3 x4 x5 : ℕ) :
    eltG [g0, g1, g2, g3, g4, g5] [x0, x1, x2, x3, x4, x5] =
      g0 ^ x0 * g1 ^ x1 * g2 ^ x2 * g3 ^ x3 * g4 ^ x4 * g5 ^ x5 := by
  simp only [eltG, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
    one_mul]

theorem coe_eltG_aGA (x0 x1 x2 x3 x4 x5 : ℕ) :
    (eltG aGA [x0, x1, x2, x3, x4, x5] : GL24) =
      a 0 ^ x0 * a 1 ^ x1 * a 2 ^ x2 * a 3 ^ x3 * a 4 ^ x4 * a 5 ^ x5 := by
  rw [aGA_eq_aE, eltG_six_mul]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  rfl

theorem eProd_eq_six (b : Fin 6 → ZMod 3) :
    eProd b = a 0 ^ (b 0).val * a 1 ^ (b 1).val * a 2 ^ (b 2).val * a 3 ^ (b 3).val *
      a 4 ^ (b 4).val * a 5 ^ (b 5).val := by
  simp only [eProd, List.finRange_succ, List.finRange_zero, List.map_cons, List.map_map,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

section E

theorem aGens_rep : RowsRep (Native.aGens ()) aGA := by
  unfold Native.aGens aGA RowsRep
  have h1 : (List.range 6).map Native.aRows =
      (List.finRange 6).map fun i => Native.aRows i.val := by
    simp [List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, List.range_succ]
  rw [h1, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun i _ => a_rep i

theorem eltG_aGA_inj {x y : List ℕ} (hx : x ∈ expVecs 3 6) (hy : y ∈ expVecs 3 6)
    (h : eltG aGA x = eltG aGA y) : x = y := by
  obtain ⟨hlx, hx3⟩ := mem_expVecs_iff.1 hx
  obtain ⟨hly, hy3⟩ := mem_expVecs_iff.1 hy
  obtain ⟨x0, x1, x2, x3, x4, x5, rfl⟩ := exists_six_of_length hlx
  obtain ⟨y0, y1, y2, y3, y4, y5, rfl⟩ := exists_six_of_length hly
  have hx0 := hx3 x0 (by simp)
  have hx1 := hx3 x1 (by simp)
  have hx2 := hx3 x2 (by simp)
  have hx3' := hx3 x3 (by simp)
  have hx4 := hx3 x4 (by simp)
  have hx5 := hx3 x5 (by simp)
  have hy0 := hy3 y0 (by simp)
  have hy1 := hy3 y1 (by simp)
  have hy2 := hy3 y2 (by simp)
  have hy3' := hy3 y3 (by simp)
  have hy4 := hy3 y4 (by simp)
  have hy5 := hy3 y5 (by simp)
  have e := congrArg Subtype.val h
  rw [coe_eltG_aGA, coe_eltG_aGA] at e
  have ex : eProd ![(x0 : ZMod 3), x1, x2, x3, x4, x5] =
      a 0 ^ x0 * a 1 ^ x1 * a 2 ^ x2 * a 3 ^ x3 * a 4 ^ x4 * a 5 ^ x5 := by
    rw [eProd_eq_six]
    simp only [Matrix.cons_val, ZMod.val_natCast, Nat.mod_eq_of_lt hx0, Nat.mod_eq_of_lt hx1,
      Nat.mod_eq_of_lt hx2, Nat.mod_eq_of_lt hx3', Nat.mod_eq_of_lt hx4, Nat.mod_eq_of_lt hx5]
  have ey : eProd ![(y0 : ZMod 3), y1, y2, y3, y4, y5] =
      a 0 ^ y0 * a 1 ^ y1 * a 2 ^ y2 * a 3 ^ y3 * a 4 ^ y4 * a 5 ^ y5 := by
    rw [eProd_eq_six]
    simp only [Matrix.cons_val, ZMod.val_natCast, Nat.mod_eq_of_lt hy0, Nat.mod_eq_of_lt hy1,
      Nat.mod_eq_of_lt hy2, Nat.mod_eq_of_lt hy3', Nat.mod_eq_of_lt hy4, Nat.mod_eq_of_lt hy5]
  have hb := @eHom_injective (Multiplicative.ofAdd ![(x0 : ZMod 3), x1, x2, x3, x4, x5])
    (Multiplicative.ofAdd ![(y0 : ZMod 3), y1, y2, y3, y4, y5]) (ex.trans (e.trans ey.symm))
  have hv : ∀ i : Fin 6, (![(x0 : ZMod 3), x1, x2, x3, x4, x5] i).val =
      (![(y0 : ZMod 3), y1, y2, y3, y4, y5] i).val := fun i =>
    congrArg (fun m => (Multiplicative.toAdd m i).val) hb
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  simp only [Matrix.cons_val, ZMod.val_natCast] at h0 h1 h2 h3 h4 h5
  simp only [List.cons.injEq, and_true]
  omega

theorem eSplit : SplitData (Native.aGens ()) aGA where
  rep := aGens_rep
  wf := by
    have hc := CFSG.Sporadic.Co1Schreier.e_check
    unfold CFSG.Sporadic.Co1Schreier.Native.eCheck at hc
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    intro g hg
    rw [Native.aGens, List.mem_map] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    have e : CFSG.Sporadic.Co1Schreier.Native.eRows (Pi.single (⟨i, List.mem_range.1 hi⟩ : Fin 6) 1)
        = Native.aRows i := beq_iff_eq.1 (hc.2 ⟨i, List.mem_range.1 hi⟩ (List.mem_finRange _))
    rw [← e]
    exact hc.1.1 _ (Finset.mem_univ _)
  comm := by
    intro f hf f' hf'
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hf
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hf'
    exact Subtype.ext (a_comm i j).eq
  cube := by
    intro f hf
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hf
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact a_pow_three i
  nodup := by
    have hlen : (Native.aGens ()).length = 6 := by simp [Native.aGens]
    rw [hlen]
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (nodup_expVecs 3 6)
    have h1 := mrep_eltR aGens_rep x
    have h2 := mrep_eltR aGens_rep y
    rw [hxy] at h1
    exact eltG_aGA_inj hx hy (Subtype.ext (h1.eq h2))

end E

theorem factorization_card_GA :
    (Nat.card ↥(⊤ : Subgroup ↥GA)).factorization 3 = 9 := by
  rw [Subgroup.card_top, card_GA_eq,
    show (4157776806543360000 : ℕ) = 3 ^ 9 * 211236945920000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem good_conj (h s : ↥GA) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({h * s * h⁻¹} : Set ↥GA)) = ⊥ ↔
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set ↥GA)) = ⊥ :=
  @gLAPPrimeCoreOf_centralizer_conj 3 ↥GA (Subgroup.toGroup GA) h s

theorem orderOf_conj_GA (g s : ↥GA) : orderOf (g * s * g⁻¹) = orderOf s := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [conj_pow]
  constructor
  · intro h
    have e : s ^ n = g⁻¹ * (g * s ^ n * g⁻¹) * g := by group
    rw [e, h]
    group
  · intro h
    rw [h]
    group

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

end
