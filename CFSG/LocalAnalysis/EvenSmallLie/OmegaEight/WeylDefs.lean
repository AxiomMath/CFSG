module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhCaseOne
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernel
public import CFSG.Monster.B.Co2.PermArr

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def vecD (i j : ℕ) (a b : ℤ) : List ℤ :=
  (List.range 8).map fun k => if k = i then a else if k = j then b else 0

@[expose] def rootsD : List (List ℤ) :=
  (List.range 8).flatMap fun i => ((List.range 8).filter (i < ·)).flatMap fun j =>
    [vecD i j 2 2, vecD i j 2 (-2), vecD i j (-2) 2, vecD i j (-2) (-2)]

@[expose] def rootsS : List (List ℤ) :=
  ((List.range 256).filter fun m => framePop m % 2 = 0).map fun m =>
    (List.range 8).map fun k => if m.testBit k then -1 else 1

@[expose] def rootList : List (List ℤ) := rootsD ++ rootsS

@[expose] def rootVec (i : ℕ) : List ℤ := rootList.getD i []

@[expose] def rootIdx (v : List ℤ) : ℕ := rootList.idxOf v

@[expose] def dotZ (u v : List ℤ) : ℤ := (List.zipWith (· * ·) u v).sum

@[expose] def reflVec (r x : List ℤ) : List ℤ := List.zipWith (fun a b => a - dotZ x r / 4 * b) x r

@[expose] def reflArr (r : ℕ) : Array ℕ :=
  Array.ofFn (n := 240) fun i => rootIdx (reflVec (rootVec r) (rootVec i.val))

@[expose] def refl (r : ℕ) : Equiv.Perm (Fin 240) := permOfArr 240 (reflArr r)

@[expose] def negArr : Array ℕ := Array.ofFn (n := 240) fun i => rootIdx ((rootVec i.val).map (-·))

@[expose] def zPerm : Equiv.Perm (Fin 240) := permOfArr 240 negArr

@[expose] def wE8 : Subgroup (Equiv.Perm (Fin 240)) := closure {g | ∃ r < 240, refl r = g}

@[expose] def wPlus : Subgroup (Equiv.Perm (Fin 240)) := wE8 ⊓ alternatingGroup (Fin 240)

@[expose] def permArr (σ : Equiv.Perm (Fin 8)) : Array ℕ :=
  Array.ofFn (n := 240) fun i =>
    rootIdx ((List.finRange 8).map fun k => (rootVec i.val).getD (σ.symm k : ℕ) 0)

@[expose] def permMat (σ : Equiv.Perm (Fin 8)) : Equiv.Perm (Fin 240) := permOfArr 240 (permArr σ)

@[expose] def signArr (v : FrameVec) : Array ℕ :=
  Array.ofFn (n := 240) fun i =>
    rootIdx ((List.finRange 8).map fun k =>
      if v k = 1 then -(rootVec i.val).getD k 0 else (rootVec i.val).getD k 0)

@[expose] def signPerm (v : FrameVec) : Equiv.Perm (Fin 240) := permOfArr 240 (signArr v)

@[expose] def frameRoot (i : Fin 8) : ℕ := rootIdx (vecD (2 * (i / 2)) (2 * (i / 2) + 1) 2
  (if (i : ℕ) % 2 = 0 then -2 else 2))

@[expose] def frameArr (v : FrameVec) : Array ℕ :=
  Array.ofFn (n := 240) fun i =>
    rootIdx ((List.finRange 8).foldl (fun x k => if v k = 1 then reflVec (rootVec (frameRoot k)) x
      else x) (rootVec i.val))

@[expose] def frameElt (v : FrameVec) : Equiv.Perm (Fin 240) := permOfArr 240 (frameArr v)

@[expose] def eSub : Subgroup (Equiv.Perm (Fin 240)) :=
  closure (signPerm '' (evenSub : Set FrameVec))

@[expose] def e1Sub : Subgroup (Equiv.Perm (Fin 240)) := closure (Set.range frameElt)

@[expose] def e1PlusSub : Subgroup (Equiv.Perm (Fin 240)) :=
  closure (frameElt '' (evenSub : Set FrameVec))

@[expose] def pPlusGens : List (Equiv.Perm (Fin 8)) :=
  [Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 4 5 * Equiv.swap 6 7, Equiv.swap 4 6 * Equiv.swap 5 7,
    Equiv.swap 0 1 * Equiv.swap 4 5,
    Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7]

@[expose] def tPlusSub : Subgroup (Equiv.Perm (Fin 240)) :=
  closure (signPerm '' (evenSub : Set FrameVec) ∪ {g | ∃ σ ∈ pPlusGens, permMat σ = g})

@[expose] def tSub : Subgroup (Equiv.Perm (Fin 240)) :=
  closure (signPerm '' (evenSub : Set FrameVec) ∪
    {g | ∃ σ ∈ Equiv.swap 0 1 :: pPlusGens, permMat σ = g})

@[expose] def vec2 (i j : Fin 8) : FrameVec := frameE i + frameE j

@[expose] def uSub : Subgroup (Equiv.Perm (Fin 240)) :=
  closure {signPerm (vec2 0 1 + vec2 2 3), signPerm (vec2 4 5 + vec2 6 7)}

@[expose] def uPrimeSub : Subgroup (Equiv.Perm (Fin 240)) :=
  closure {signPerm (vec2 0 1), signPerm (vec2 0 2) * permMat (Equiv.swap 0 1 * Equiv.swap 2 3),
    signPerm (vec2 0 4) * permMat (Equiv.swap 0 1 * Equiv.swap 4 5),
    signPerm (vec2 0 6) * permMat (Equiv.swap 0 1 * Equiv.swap 6 7)}

@[expose] def sZero : Equiv.Perm (Fin 240) := refl (frameRoot 0)

@[expose] def xPlane : Equiv.Perm (Fin 240) := signPerm (vec2 0 1 + vec2 2 3)

structure WeylModel : Prop where
  card_wE8 : Nat.card wE8 = 696729600
  card_wPlus : Nat.card wPlus = 348364800
  refl_mem : ∀ r < 240, refl r ∈ wE8
  sZero_mem : sZero ∈ wE8
  sZero_not_mem : sZero ∉ wPlus
  sZero_sq : sZero * sZero = 1
  zPerm_mem : zPerm ∈ wPlus
  zPerm_ne_one : zPerm ≠ 1
  zPerm_sq : zPerm * zPerm = 1
  zPerm_comm : ∀ w ∈ wE8, w * zPerm = zPerm * w
  commutator_eq : ⁅wE8, wE8⁆ = wPlus
  perfect : commutator wPlus = ⊤
  centralizer_wPlus : ∀ w ∈ wE8, (∀ x ∈ wPlus, w * x = x * w) → w = 1 ∨ w = zPerm
  mem_center : ∀ x : wPlus, x ∈ center wPlus ↔ (x : Equiv.Perm (Fin 240)) = 1 ∨ x = zPerm
  card_center : Nat.card (center wPlus) = 2
  lieModel : CFSG.Blueprint.LieModel (wPlus ⧸ center wPlus) .POmegaPlus 4 2 1
  sq_eq_zPerm : ∀ w ∈ wE8, w * w = zPerm → w ∈ wPlus
  doubleCover : ∀ (L : Type) [Group L], commutator L = ⊤ → Nat.card (center L) = 2 →
    CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1 →
      ∃ θ : L ≃* wPlus, (center L).map θ.toMonoidHom = center wPlus

structure WeylAut : Prop where
  conj : ∀ φ : MulAut wPlus, ∃ w ∈ wE8, ∀ x : wPlus,
    ((φ x : wPlus) : Equiv.Perm (Fin 240)) = w * x * w⁻¹
  card_mulAut : Nat.card (MulAut wPlus) = 348364800
  foursGroup : FoursGroupCondition wPlus

structure WeylCoords : Prop where
  signPerm_add : ∀ v ∈ evenSub, ∀ w ∈ evenSub, signPerm (v + w) = signPerm v * signPerm w
  signPerm_inj : ∀ v ∈ evenSub, ∀ w ∈ evenSub, signPerm v = signPerm w → v = w
  mem_eSub : ∀ g, g ∈ eSub ↔ ∃ v ∈ evenSub, signPerm v = g
  signPerm_frameZ : signPerm frameZ = zPerm
  frameElt_add : ∀ v w, frameElt (v + w) = frameElt v * frameElt w
  frameElt_injective : Function.Injective frameElt
  mem_e1Sub : ∀ g, g ∈ e1Sub ↔ ∃ v, frameElt v = g
  mem_e1PlusSub : ∀ g, g ∈ e1PlusSub ↔ ∃ v ∈ evenSub, frameElt v = g
  e1PlusSub_eq : e1PlusSub = e1Sub ⊓ wPlus
  frameElt_frameZ : frameElt frameZ = zPerm
  frameElt_frameE : ∀ i, frameElt (frameE i) = refl (frameRoot i)
  sZero_eq : sZero = frameElt (frameE 0) ∧ sZero = permMat (Equiv.swap 0 1)
  signPerm_pair : ∀ i : Fin 8, (i : ℕ) % 2 = 0 → signPerm (vec2 i (i + 1)) = frameElt (vec2 i (i + 1))
  eSub_le : eSub ≤ wPlus
  e1Sub_le : e1Sub ≤ wE8

structure WeylSylow : Prop where
  tSub_le : tSub ≤ wE8
  tPlusSub_eq : tPlusSub = tSub ⊓ wPlus
  card_tSub : Nat.card tSub = 2 ^ 14
  card_tPlusSub : Nat.card tPlusSub = 2 ^ 13
  eSub_le : eSub ≤ tPlusSub
  e1Sub_le : e1Sub ≤ tSub
  e1PlusSub_le : e1PlusSub ≤ tPlusSub
  center_tSub : ∀ x ∈ tSub, (∀ y ∈ tSub, x * y = y * x) → x = 1 ∨ x = zPerm
  center_tPlusSub : ∀ x ∈ tPlusSub, (∀ y ∈ tPlusSub, x * y = y * x) → x = 1 ∨ x = zPerm
  centralizer_eSub : ∀ w ∈ wE8, (∀ e ∈ eSub, w * e = e * w) → w ∈ eSub
  centralizer_e1Sub : ∀ w ∈ wE8, (∀ e ∈ e1Sub, w * e = e * w) → w ∈ e1Sub
  centralizer_e1PlusSub : ∀ w ∈ wE8, (∀ e ∈ e1PlusSub, w * e = e * w) → w ∈ e1Sub
  uPrimeSub_le : uPrimeSub ≤ tPlusSub
  centralizer_uPrimeSub : ∀ t ∈ tSub, (∀ u ∈ uPrimeSub, t * u = u * t) → t ∈ uPrimeSub

structure WeylAbelian : Prop where
  abelian_tPlus : ∀ B : Subgroup (Equiv.Perm (Fin 240)), B ≤ tPlusSub →
    (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → 2 ^ 7 ≤ Nat.card B →
      B = eSub ∨ B = e1PlusSub ∨ B = uPrimeSub
  abelian_t : ∀ B : Subgroup (Equiv.Perm (Fin 240)), B ≤ tSub →
    (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → 2 ^ 8 ≤ Nat.card B → B = e1Sub
  card_eSub : Nat.card eSub = 2 ^ 7
  card_e1Sub : Nat.card e1Sub = 2 ^ 8
  card_e1PlusSub : Nat.card e1PlusSub = 2 ^ 7
  card_uPrimeSub : Nat.card uPrimeSub = 2 ^ 7
  sq_eSub : ∀ e ∈ eSub, e * e = 1
  sq_e1Sub : ∀ e ∈ e1Sub, e * e = 1
  comm_e1Sub : ∀ a ∈ e1Sub, ∀ b ∈ e1Sub, a * b = b * a
  comm_uPrimeSub : ∀ a ∈ uPrimeSub, ∀ b ∈ uPrimeSub, a * b = b * a
  not_sq_uPrimeSub : ∃ u ∈ uPrimeSub, u * u ≠ 1
  e1PlusSub_ne_eSub : e1PlusSub ≠ eSub

structure WeylNormalizers : Prop where
  normalizer_eSub : ∀ w ∈ wE8, w ∈ normalizer (eSub : Set (Equiv.Perm (Fin 240))) →
    ∃ σ : Equiv.Perm (Fin 8), (∀ v ∈ evenSub, w * signPerm v * w⁻¹ = signPerm (permVec σ v)) ∧
      (w ∈ wPlus ↔ σ ∈ alternatingGroup (Fin 8))
  permMat_mem : ∀ σ : Equiv.Perm (Fin 8), permMat σ ∈ wE8 ∧
    permMat σ ∈ normalizer (eSub : Set (Equiv.Perm (Fin 240))) ∧
      ∀ v ∈ evenSub, permMat σ * signPerm v * (permMat σ)⁻¹ = signPerm (permVec σ v)
  permMat_mem_wPlus : ∀ σ : Equiv.Perm (Fin 8), permMat σ ∈ wPlus ↔ σ ∈ alternatingGroup (Fin 8)
  card_normalizer_eSub : Nat.card (wE8 ⊓ normalizer (eSub : Set (Equiv.Perm (Fin 240))) :
    Subgroup (Equiv.Perm (Fin 240))) = 2 ^ 7 * 40320
  card_normalizer_eSub_plus : Nat.card (wPlus ⊓ normalizer (eSub : Set (Equiv.Perm (Fin 240))) :
    Subgroup (Equiv.Perm (Fin 240))) = 2 ^ 7 * 20160
  normalizer_e1Sub : ∀ w ∈ wE8, w ∈ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) →
    ∃ σ ∈ frameAut, ∀ v, w * frameElt v * w⁻¹ = frameElt (permVec σ v)
  frameAut_realized : ∀ σ ∈ frameAut, ∃ w ∈ wPlus, ∀ v, w * frameElt v * w⁻¹ = frameElt (permVec σ v)
  normalizer_e1PlusSub : ∀ w ∈ wE8, (w ∈ normalizer (e1PlusSub : Set (Equiv.Perm (Fin 240))) ↔
    w ∈ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))))
  card_normalizer_e1Sub : Nat.card (wE8 ⊓ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) :
    Subgroup (Equiv.Perm (Fin 240))) = 2 ^ 8 * 1344
  card_normalizer_e1Sub_plus : Nat.card (wPlus ⊓ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) :
    Subgroup (Equiv.Perm (Fin 240))) = 2 ^ 7 * 1344

structure WeylInvolutions : Prop where
  conj_e1Sub : ∀ x ∈ wE8, x * x = 1 → ∃ g ∈ wE8, g * x * g⁻¹ ∈ e1Sub
  conj_e1PlusSub : ∀ x ∈ wPlus, x * x = 1 → ∃ g ∈ wPlus, g * x * g⁻¹ ∈ e1PlusSub
  frame_conj_eSub : ∀ v ∈ evenSub, (frameWt v = 2 ∨ frameWt v = 6 ∨ ∃ B ∈ frameBlocks,
    v = blockVec B) → ∃ g ∈ wPlus, ∃ u ∈ evenSub, u ≠ frameZ ∧ g * frameElt v * g⁻¹ = signPerm u
  xPlane_eq : xPlane = frameElt (blockVec {0, 1, 2, 3})
  plane_conj : ∀ B ∈ frameBlocks, ∃ g ∈ wPlus, g * frameElt (blockVec B) * g⁻¹ = xPlane

structure WeylUArg : Prop where
  uSub_le_eSub : uSub ≤ eSub
  uSub_le_e1Sub : uSub ≤ e1Sub
  card_uSub : Nat.card uSub = 4
  zPerm_mem : zPerm ∈ uSub
  xPlane_mem : xPlane ∈ uSub
  normal : ∀ t ∈ tSub, ∀ u ∈ uSub, t * u * t⁻¹ ∈ uSub
  unique : ∀ V : Subgroup (Equiv.Perm (Fin 240)), V ≤ tSub → Nat.card V = 4 →
    (∀ v ∈ V, v * v = 1) → (∀ t ∈ tSub, ∀ v ∈ V, t * v * t⁻¹ ∈ V) → V = uSub
  centralizer_iff : ∀ t ∈ tSub, t * xPlane = xPlane * t ↔ ∀ u ∈ uSub, t * u = u * t
  card_cT : Nat.card (tSub ⊓ centralizer {xPlane} : Subgroup (Equiv.Perm (Fin 240))) = 2 ^ 13
  e1Sub_le : e1Sub ≤ centralizer {xPlane}
  center_cT : ∀ c ∈ tSub ⊓ centralizer {xPlane}, ((∀ d ∈ tSub ⊓ centralizer {xPlane},
    c * d = d * c) ↔ c ∈ uSub)
  center_mod : ∀ c ∈ tSub ⊓ centralizer {xPlane}, ((∀ d ∈ tSub ⊓ centralizer {xPlane},
    c * d * c⁻¹ * d⁻¹ ∈ e1Sub) ↔ c ∈ e1Sub ⊔ closure {signPerm (vec2 0 2), signPerm (vec2 4 6)})
  comm_02 : ∀ g, (∃ e ∈ e1Sub, g = e * signPerm (vec2 0 2) * e⁻¹ * (signPerm (vec2 0 2))⁻¹) ↔
    g ∈ closure {signPerm (vec2 0 1), signPerm (vec2 2 3)}
  comm_46 : ∀ g, (∃ e ∈ e1Sub, g = e * signPerm (vec2 4 6) * e⁻¹ * (signPerm (vec2 4 6))⁻¹) ↔
    g ∈ closure {signPerm (vec2 4 5), signPerm (vec2 6 7)}
  comm_0246 : ∀ g, (∃ e ∈ e1Sub, g = e * signPerm (vec2 0 2 + vec2 4 6) * e⁻¹ *
    (signPerm (vec2 0 2 + vec2 4 6))⁻¹) ↔ g ∈ closure {signPerm (vec2 0 1), signPerm (vec2 2 3),
      signPerm (vec2 4 5), signPerm (vec2 6 7)}
  inf_uSub : ∀ g ∈ uSub, (g ∈ closure {signPerm (vec2 0 1), signPerm (vec2 2 3)} ↔
    g = 1 ∨ g = xPlane)

structure WeylPackage : Prop where
  model : WeylModel
  aut : WeylAut
  coords : WeylCoords
  sylow : WeylSylow
  abelian : WeylAbelian
  normalizers : WeylNormalizers
  involutions : WeylInvolutions
  uArg : WeylUArg

end CFSG.EvenSmallLie.OmegaEight.Weyl
