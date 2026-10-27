module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3F2
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Setup.X3E

open Finset

@[expose] def Inv {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M] (g : Bool → (M →ₗ[ZMod 2] M))
    (U : Submodule (ZMod 2) M) : Prop :=
  ∀ b, ∀ u ∈ U, g b u ∈ U

@[expose] def IrredPair {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (g : Bool → (M →ₗ[ZMod 2] M)) : Prop :=
  ∀ U : Submodule (ZMod 2) M, Inv g U → U = ⊥ ∨ U = ⊤

theorem wmap_mem {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M] {g : Bool → (M →ₗ[ZMod 2] M)}
    {U : Submodule (ZMod 2) M} (hU : Inv g U) : ∀ (w : List Bool) (u : M), u ∈ U →
      (wmap g w) u ∈ U
  | [], u, hu => hu
  | b :: w, u, hu => by
    rw [wmap_cons]
    exact hU b _ (wmap_mem hU w u hu)

theorem norton_sem {d : ℕ} (g : Bool → (Vec d →ₗ[ZMod 2] Vec d)) (a : Vec d →ₗ[ZMod 2] Vec d)
    (ha : ∀ U : Submodule (ZMod 2) (Vec d), Inv g U → ∀ u ∈ U, a u ∈ U)
    (hN1 : ∀ v : Vec d, a v = 0 → v ≠ 0 → ∀ U : Submodule (ZMod 2) (Vec d), Inv g U → v ∈ U →
      U = ⊤)
    (ψ : Vec d →ₗ[ZMod 2] ZMod 2) (hψa : ∀ v, ψ (a v) = 0)
    (hN2 : ∀ U : Submodule (ZMod 2) (Vec d), Inv g U → (∀ u ∈ U, ψ u = 0) → U = ⊥) :
    IrredPair g := by
  intro U hU
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  by_contra htop
  have hinj : ∀ u ∈ U, a u = 0 → u = 0 := by
    intro u hu h0
    by_contra hne
    exact htop (hN1 u h0 hne U hU hu)
  have hsurj : ∀ u ∈ U, ∃ u' ∈ U, a u' = u := by
    intro u hu
    let f : U → U := fun u => ⟨a u, ha U hU u u.2⟩
    have hf : Function.Injective f := by
      intro u u' h
      have h1 : a (u : Vec d) = a (u' : Vec d) := congrArg Subtype.val h
      have h2 : a ((u : Vec d) - u') = 0 := by rw [map_sub, h1]; exact sub_self _
      have h3 := hinj _ (U.sub_mem u.2 u'.2) h2
      exact Subtype.ext (sub_eq_zero.mp h3)
    obtain ⟨u', hu'⟩ := (Finite.injective_iff_surjective.mp hf) ⟨u, hu⟩
    exact ⟨u', u'.2, congrArg Subtype.val hu'⟩
  have hψU : ∀ u ∈ U, ψ u = 0 := by
    intro u hu
    obtain ⟨u', -, rfl⟩ := hsurj u hu
    exact hψa u'
  exact hbot (hN2 U hU hψU)

theorem eq_top_of_basis_mem {d : ℕ} {U : Submodule (ZMod 2) (Vec d)}
    (h : ∀ k : Fin d, (Pi.single k (1 : ZMod 2) : Vec d) ∈ U) : U = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have : v = ∑ k, v k • (Pi.single k (1 : ZMod 2) : Vec d) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact U.sum_mem fun k _ => U.smul_mem _ (h k)

theorem linearMap_ext_basis {d : ℕ} {N : Type*} [AddCommMonoid N] [Module (ZMod 2) N]
    {f f' : Vec d →ₗ[ZMod 2] N} (h : ∀ k : Fin d, f (Pi.single k 1) = f' (Pi.single k 1)) :
    f = f' := by
  apply LinearMap.pi_ext
  intro k x
  have hx : (Pi.single k x : Vec d) = x • (Pi.single k (1 : ZMod 2) : Vec d) := by
    funext j; by_cases hj : j = k <;> simp [hj]
  rw [hx, map_smul, map_smul, h k]

theorem lin_eq_of_cols {d : ℕ} (f : Vec d →ₗ[ZMod 2] Vec d) (cols : List ℕ)
    (h : ∀ k : Fin d, toVec d (cols.getD k.val 0) = f (Pi.single k 1)) : lin d cols = f := by
  apply linearMap_ext_basis
  intro k
  rw [← h k, lin_apply]
  simp [Pi.single_apply]

theorem wapp_lt {d : ℕ} {cols : Bool → List ℕ} (h : ∀ b, ∀ j < d, (cols b).getD j 0 < 2 ^ d)
    (w : List Bool) {v : ℕ} (hv : v < 2 ^ d) : wapp d cols w v < 2 ^ d := by
  induction w with
  | nil => exact hv
  | cons b w ih =>
    unfold wapp at ih ⊢
    simp only [List.foldr_cons]
    exact papply_lt (h b) _

@[expose] def aColsOf (d : ℕ) (cols : Bool → List ℕ) (aW : List (List Bool)) : List ℕ :=
  (List.range d).map fun k => aW.foldl (fun acc w => acc ^^^ wapp d cols w (1 <<< k)) 0

@[expose] def xorSelW (d : ℕ) (cols : Bool → List ℕ) (gw : List (List Bool)) (t c : ℕ) : ℕ :=
  (List.range gw.length).foldl
    (fun acc l => if c.testBit l then acc ^^^ wapp d cols (gw.getD l []) t else acc) 0

@[expose] def kerCertOK (d : ℕ) (cols : Bool → List ℕ) (aCols : List ℕ)
    (e : ℕ × List (List Bool) × List ℕ) : Bool :=
  decide (0 < e.1) && decide (e.1 < 2 ^ d) && (papply d aCols e.1 == 0) && e.2.2.length == d &&
    (List.range d).all fun k => xorSelW d cols e.2.1 e.1 (e.2.2.getD k 0) == 1 <<< k

@[expose] def rowAt (d : ℕ) (cols : Bool → List ℕ) (psi : ℕ) (dw : List (List Bool)) (l : ℕ) : ℕ :=
  ofBits d fun k => dotb d psi (wapp d cols (dw.getD l []) (1 <<< k))

@[expose] def mkAt (d : ℕ) (cols : Bool → List ℕ) (psi : ℕ) (dw : List (List Bool)) (k : ℕ) : ℕ :=
  ofBits d fun l => (rowAt d cols psi dw l).testBit k

@[expose] def nortonOK (d : ℕ) (cols : Bool → List ℕ) (aW : List (List Bool))
    (kers : List (ℕ × List (List Bool) × List ℕ)) (psi : ℕ) (dw : List (List Bool))
    (rCols minv : List ℕ) : Bool :=
  ((0 :: kers.map (·.1)).all fun x => (0 :: kers.map (·.1)).all fun y =>
      (0 :: kers.map (·.1)).contains (x ^^^ y)) &&
    (List.range d).all (fun k => (0 :: kers.map (·.1)).contains
      ((1 <<< k) ^^^ papply d rCols ((aColsOf d cols aW).getD k 0))) &&
    kers.all (kerCertOK d cols (aColsOf d cols aW)) &&
    (List.range d).all (fun k => !(dotb d psi ((aColsOf d cols aW).getD k 0))) &&
    (List.range d).all (fun k => papply d minv (mkAt d cols psi dw k) == 1 <<< k)

theorem lin_single (d : ℕ) (cols : List ℕ) (k : Fin d) :
    lin d cols (Pi.single k 1) = toVec d (cols.getD k.val 0) := by
  rw [lin_apply]
  simp [Pi.single_apply]

theorem fnl_single (d ψ : ℕ) (k : Fin d) : fnl d ψ (Pi.single k 1) = toVec d ψ k := by
  rw [fnl_apply]
  simp [Pi.single_apply]

theorem list_sum_apply {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module (ZMod 2) M]
    [Module (ZMod 2) N] (L : List (M →ₗ[ZMod 2] N)) (v : M) :
    (L.sum) v = (L.map fun f => f v).sum := by
  induction L with
  | nil => rfl
  | cons f L ih => simp [List.sum_cons, ih]

theorem toVec_foldl_xor (d : ℕ) {α : Type*} (f : α → ℕ) (l : List α) (init : ℕ) :
    toVec d (l.foldl (fun acc a => acc ^^^ f a) init) = toVec d init + (l.map fun a => toVec d (f a)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, toVec_xor, List.map_cons, List.sum_cons]
    abel

theorem one_shiftLeft_lt {d k : ℕ} (hk : k < d) : 1 <<< k < 2 ^ d := by
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by norm_num) hk

theorem aColsOf_lt {d : ℕ} {cols : Bool → List ℕ} (h : ∀ b, ∀ j < d, (cols b).getD j 0 < 2 ^ d)
    (aW : List (List Bool)) : ∀ j < d, (aColsOf d cols aW).getD j 0 < 2 ^ d := by
  intro j hj
  unfold aColsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some]
  suffices hs : ∀ (l : List (List Bool)) (init : ℕ), init < 2 ^ d →
      l.foldl (fun acc w => acc ^^^ wapp d cols w (1 <<< j)) init < 2 ^ d from
    hs aW 0 (by positivity)
  intro l
  induction l with
  | nil => intro init hi; simpa using hi
  | cons w l ih =>
    intro init hi
    rw [List.foldl_cons]
    exact ih _ (Nat.xor_lt_two_pow hi (wapp_lt h w (one_shiftLeft_lt hj)))

theorem aColsOf_eq {d : ℕ} {cols : Bool → List ℕ} (aW : List (List Bool)) :
    lin d (aColsOf d cols aW) = (aW.map (wmap (fun b => lin d (cols b)))).sum := by
  apply lin_eq_of_cols
  intro k
  unfold aColsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range k.isLt]
  simp only [Option.map_some, Option.getD_some]
  rw [toVec_foldl_xor, toVec_zero, zero_add, list_sum_apply, List.map_map]
  congr 1
  apply List.map_congr_left
  intro w _
  simp only [Function.comp]
  rw [toVec_wapp, toVec_one_shiftLeft d k k.isLt]

theorem toVec_xorSelW (d : ℕ) (cols : Bool → List ℕ) (gw : List (List Bool)) (t c : ℕ) :
    toVec d (xorSelW d cols gw t c) = ∑ l ∈ range gw.length,
      if c.testBit l then (wmap (fun b => lin d (cols b)) (gw.getD l [])) (toVec d t) else 0 := by
  unfold xorSelW
  rw [foldl_xor_toVec d (fun l => c.testBit l = true) (fun l => wapp d cols (gw.getD l []) t),
    toVec_zero, zero_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [toVec_wapp]

theorem ker_subset {d : ℕ} {cols : Bool → List ℕ} {aW : List (List Bool)} {rCols : List ℕ}
    {kerAll : List ℕ} (h0 : 0 ∈ kerAll)
    (hclos : ∀ x ∈ kerAll, ∀ y ∈ kerAll, (x ^^^ y) ∈ kerAll)
    (hθ : ∀ k : Fin d, ((1 <<< k.val) ^^^ papply d rCols ((aColsOf d cols aW).getD k.val 0)) ∈ kerAll)
    (v : Vec d) (hv : lin d (aColsOf d cols aW) v = 0) : ∃ t ∈ kerAll, toVec d t = v := by
  have hexp : v = ∑ k, v k • (Pi.single k (1 : ZMod 2) : Vec d) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hθv : v = ∑ k, v k • toVec d ((1 <<< k.val) ^^^
      papply d rCols ((aColsOf d cols aW).getD k.val 0)) := by
    have h1 : v + lin d rCols (lin d (aColsOf d cols aW) v) = v := by rw [hv, map_zero, add_zero]
    have h2 : ∀ k : Fin d, (Pi.single k (1 : ZMod 2) : Vec d) +
        lin d rCols (lin d (aColsOf d cols aW) (Pi.single k 1)) =
        toVec d ((1 <<< k.val) ^^^ papply d rCols ((aColsOf d cols aW).getD k.val 0)) := by
      intro k
      rw [lin_single, ← toVec_papply, ← toVec_one_shiftLeft d k.val k.isLt, ← toVec_xor]
    let θ : Vec d →ₗ[ZMod 2] Vec d :=
      LinearMap.id + (lin d rCols).comp (lin d (aColsOf d cols aW))
    have h3 : θ v = ∑ k, v k • θ (Pi.single k 1) := by
      conv_lhs => rw [hexp]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
    have h4 : θ v = v := h1
    have h5 : ∀ k : Fin d, θ (Pi.single k 1) = (Pi.single k (1 : ZMod 2) : Vec d) +
        lin d rCols (lin d (aColsOf d cols aW) (Pi.single k 1)) := fun k => rfl
    rw [h4] at h3
    refine h3.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [h5, h2]
  rw [hθv]
  apply Finset.sum_induction _ (fun x => ∃ t ∈ kerAll, toVec d t = x)
  · rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    exact ⟨t ^^^ t', hclos t ht t' ht', toVec_xor d t t'⟩
  · exact ⟨0, h0, toVec_zero d⟩
  · intro k _
    have hk : v k = 0 ∨ v k = 1 := by
      generalize v k = c
      revert c; decide
    rcases hk with hk | hk
    · exact ⟨0, h0, by rw [hk, zero_smul, toVec_zero]⟩
    · exact ⟨_, hθ k, by rw [hk, one_smul]⟩

theorem nortonOK_sound {d : ℕ} {cols : Bool → List ℕ} {aW : List (List Bool)}
    {kers : List (ℕ × List (List Bool) × List ℕ)} {psi : ℕ} {dw : List (List Bool)}
    {rCols minv : List ℕ} (h : nortonOK d cols aW kers psi dw rCols minv = true) :
    IrredPair (fun b => lin d (cols b)) := by
  unfold nortonOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hA, hB⟩, hK2⟩, hK3⟩, hK5⟩ := h
  rw [List.all_eq_true] at hA hB hK2 hK3 hK5
  set g : Bool → (Vec d →ₗ[ZMod 2] Vec d) := fun b => lin d (cols b) with hg
  apply norton_sem g (lin d (aColsOf d cols aW)) _ _ (fnl d psi) _ _
  · intro U hU u hu
    rw [aColsOf_eq, list_sum_apply]
    apply list_sum_mem
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    rw [List.mem_map] at hf
    obtain ⟨w, -, rfl⟩ := hf
    exact wmap_mem hU w u hu
  · intro v hv0 hv U hU hvU
    obtain ⟨t, htk, htv⟩ := ker_subset (cols := cols) (aW := aW) (rCols := rCols)
      (kerAll := 0 :: kers.map (·.1)) (by simp)
      (fun x hx y hy => by
        have := hA x hx
        rw [List.all_eq_true] at this
        simpa using this y hy)
      (fun k => by
        have := hB k.val (List.mem_range.mpr k.isLt)
        simpa using this) v hv0
    have ht0 : t ≠ 0 := by rintro rfl; exact hv (htv ▸ toVec_zero d)
    obtain ⟨e, he, het⟩ : ∃ e ∈ kers, e.1 = t := by
      simpa [ht0] using htk
    have hcert := hK2 e he
    unfold kerCertOK at hcert
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hcert
    obtain ⟨-, hgen⟩ := hcert
    apply eq_top_of_basis_mem
    intro k
    rw [← toVec_one_shiftLeft d k k.isLt, ← hgen k k.isLt, toVec_xorSelW]
    apply Submodule.sum_mem
    intro l _
    split_ifs
    · rw [het, htv]
      exact wmap_mem hU _ _ hvU
    · exact U.zero_mem
  · intro v
    have : (fnl d psi).comp (lin d (aColsOf d cols aW)) = 0 := by
      apply linearMap_ext_basis
      intro k
      simp only [LinearMap.comp_apply, LinearMap.zero_apply]
      rw [lin_single, ← dotb_cast]
      have h3 := hK3 k.val (List.mem_range.mpr k.isLt)
      simp only [Bool.not_eq_true'] at h3
      rw [h3]
      rfl
    exact LinearMap.congr_fun this v
  · intro U hU hψU
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨t, ht, rfl⟩ := exists_toVec u
    rw [Submodule.mem_bot]
    have hrow : ∀ l, fnl d (rowAt d cols psi dw l) (toVec d t) = 0 := by
      intro l
      have : fnl d (rowAt d cols psi dw l) = (fnl d psi).comp (wmap g (dw.getD l [])) := by
        apply linearMap_ext_basis
        intro k
        rw [fnl_single]
        unfold rowAt
        rw [toVec_ofBits]
        simp only [LinearMap.comp_apply]
        rw [← toVec_one_shiftLeft d k k.isLt, ← toVec_wapp, ← dotb_cast]
      rw [this]
      exact hψU _ (wmap_mem hU _ _ hu)
    have hM : ∑ k, toVec d t k • toVec d (mkAt d cols psi dw k) = 0 := by
      funext l
      rw [Finset.sum_apply]
      have := hrow l.val
      rw [fnl_apply] at this
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold mkAt
      rw [toVec_ofBits, mul_comm]
      unfold rowAt
      simp [toVec_apply, ofBits_testBit]
    have hu0 : toVec d t = ∑ k, toVec d t k • (Pi.single k (1 : ZMod 2) : Vec d) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hbasis : ∀ k : Fin d, lin d minv (toVec d (mkAt d cols psi dw k)) = Pi.single k 1 := by
      intro k
      have := hK5 k.val (List.mem_range.mpr k.isLt)
      rw [beq_iff_eq] at this
      rw [← toVec_papply, this, toVec_one_shiftLeft d k.val k.isLt]
    calc toVec d t = ∑ k, toVec d t k • (Pi.single k (1 : ZMod 2) : Vec d) := hu0
      _ = ∑ k, toVec d t k • lin d minv (toVec d (mkAt d cols psi dw k)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hbasis]
      _ = lin d minv (∑ k, toVec d t k • toVec d (mkAt d cols psi dw k)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_smul]
      _ = 0 := by rw [hM, map_zero]

end CFSG.QuasithinUnique.Setup.X3E
