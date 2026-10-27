module

public import Certificates.Data.Kernel.HatChkK
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.HatChkK

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Quasithin.H13.Ch4.HatChk

theorem memA_keysOf (n : ℕ) (ps : List ℕ) (c : ArrCert) (t : Array ℕ) :
    memA n ps c (keysOf n ps c) t = memL n ps c.pts t := by
  apply Bool.eq_iff_iff.2
  rw [memA_iff, memL, List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hk, he⟩
    refine ⟨c.pts[j]!, ?_, ?_⟩
    · rw [getElem!_pos c.pts j hj, Array.mem_toList_iff]
      exact Array.getElem_mem hj
    · rw [keysOf, map_getElem! _ _ hj] at hk
      rw [hk, he]
      simp
  · rintro ⟨p, hp, h⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    have hj' : j < c.pts.size := by simpa using hj
    rw [Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨j, hj', ?_, ?_⟩
    · rw [keysOf, map_getElem! _ _ hj', getElem!_pos c.pts j hj', ← h.1]
      simp
    · rw [getElem!_pos c.pts j hj']
      simpa using h.2

theorem coverOK_eq (n m : ℕ) (ps : List ℕ) (c₁ c₂ : ArrCert) (cls : Array ℕ) :
    coverOK n m ps c₁ c₂ cls = coverOKL n m ps c₁.pts c₂.pts cls := by
  unfold coverOK coverOKL
  simp only [memA_keysOf]

theorem greedyCover_eq (n : ℕ) (ps : List ℕ) (c₁ c₂ : ArrCert) :
    greedyCover n ps c₁ c₂ = greedyCoverL n ps c₁.pts c₂.pts := by
  unfold greedyCover greedyCoverL
  simp only [memA_keysOf]

theorem forIn_id {α β : Type} {l : List α} {init : β} (f : α → β → Id (ForInStep β))
    (g : β → α → β) (h : ∀ a b, f a b = pure (.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  have e : f = fun a b => pure (.yield (g b a)) := funext fun a => funext fun b => h a b
  subst e
  exact List.forIn_pure_yield_eq_foldl _ _

theorem greedyCoverL_eq (n : ℕ) (ps : List ℕ) (P₁ P₂ : Array (Array ℕ)) :
    greedyCoverL n ps P₁ P₂ =
      greedyF P₁.size (fun i => memL n ps P₂ P₁[i]!) (fun i j => cmA n P₁[i]! P₁[j]!) := by
  unfold greedyCoverL greedyF
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_id _ (gOut (fun i => memL n ps P₂ P₁[i]!) (fun i j => cmA n P₁[i]! P₁[j]!))]
  · simp
  · intro i st
    unfold gOut
    split
    · rw [forIn_id _ (gIn (fun i j => cmA n P₁[i]! P₁[j]!) i)]
      · simp only [pure_bind]
        split <;> rename_i hc <;> simp only [hc, ↓reduceIte]
      · intro k s
        unfold gIn
        rw [Array.all_toList]
        split <;> rfl
    · rfl

theorem coverOKL_eq (n m : ℕ) (ps : List ℕ) (P₁ P₂ : Array (Array ℕ)) (cls : Array ℕ) :
    coverOKL n m ps P₁ P₂ cls = coverF P₁.size m (fun i => (P₁.map fun t => memL n ps P₂ t)[i]!)
      (fun i => cls[i]!) (fun i j => cmA n P₁[i]! P₁[j]!) := rfl

section Packed

open CFSG.KC.Enum (pg pcomp)
open CFSG.KS (mask)
open CFSG.KS.Raw (unpack szOK)
open CFSG.KC.Misc.ArrEnum (permB pp_of_permB permB_of_pp comp_unpack' eqA_unpack')
open CFSG.KC.BfsPin (PP eqA_unpack pts_toList)
open CFSG.KC.B3S3K (any_range_congr)

variable {n w : ℕ} (hw : szOK n w = true)

omit hw in
theorem fpfA_unpack (p : ℕ) : fpfA n (unpack n w p) = fpfK n w p := by
  apply Bool.eq_iff_iff.2
  rw [fpfA, allLt_iff, fpfK, List.all_eq_true]
  simp only [List.mem_range]
  refine forall₂_congr fun i hi => ?_
  rw [CFSG.KS.Raw.Orb.unpack_get hi]
  by_cases e : pg w (mask w) p i = i
  · simp [e]
  · have e2 : Nat.beq (pg w (mask w) p i) i = false :=
      Bool.eq_false_iff.2 fun h2 => e (Nat.eq_of_beq_eq_true h2)
    simp [e, e2]

include hw

theorem permB_pcomp {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    permB n w (pcomp n w (mask w) p q) = true :=
  permB_of_pp ((pp_of_permB hw hp).mul (pp_of_permB hw hq))

theorem cmA_unpack {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    cmA n (unpack n w p) (unpack n w q) = cmK n w p q := by
  unfold cmA cmK
  rw [comp_unpack' hw hp hq, comp_unpack' hw hq hp,
    eqA_unpack' hw (permB_pcomp hw hp hq) (permB_pcomp hw hq hp)]

theorem centralA_unpack {gs : Array (Array ℕ)} {ng : ℕ} {G : ℕ → ℕ}
    (hg : CFSG.KC.B3S3K.BindA n w gs ng G) (hG : ∀ k < ng, permB n w (G k) = true) {t : ℕ}
    (ht : permB n w t = true) :
    centralA n gs (unpack n w t) = (List.range ng).all fun k => cmK n w (G k) t := by
  apply Bool.eq_iff_iff.2
  rw [centralA, allLt_iff, List.all_eq_true, hg.1]
  simp only [List.mem_range]
  refine forall₂_congr fun k hk => ?_
  rw [hg.2 k hk, cmA_unpack hw (hG k hk) ht]

theorem memL_unpack {ps : List ℕ} {N : ℕ} {T : ℕ → ℕ} (hT : ∀ j < N, permB n w (T j) = true)
    {t : ℕ} (ht : permB n w t = true) :
    memL n ps (Array.ofFn (n := N) fun i => unpack n w (T i.val)) (unpack n w t) =
      (List.range N).any fun j => Nat.beq t (T j) := by
  unfold memL
  rw [pts_toList (fun j => unpack n w (T j)), List.any_map]
  apply any_range_congr
  intro j hj
  simp only [Function.comp]
  rw [eqA_unpack (pp_of_permB hw ht).1 (pp_of_permB hw (hT j hj)).1]
  cases h : Nat.beq t (T j)
  · simp
  · rw [Nat.eq_of_beq_eq_true h]
    simp

theorem fpfPairOK_unpack {gs : Array (Array ℕ)} {ng N : ℕ} {G T : ℕ → ℕ} {c : ArrCert}
    (hg : CFSG.KC.B3S3K.BindA n w gs ng G) (hG : ∀ k < ng, permB n w (G k) = true)
    (hN : c.pts.size = N) (hc : ∀ j < N, c.pts[j]! = unpack n w (T j))
    (hT : ∀ j < N, permB n w (T j) = true) {r : ℕ} (hr : permB n w r = true) :
    fpfPairOK n gs c (unpack n w r) = (List.range N).all fun j => fpfPairK n w ng G r (T j) := by
  apply Bool.eq_iff_iff.2
  rw [fpfPairOK, allLt_iff, List.all_eq_true, hN]
  simp only [List.mem_range]
  refine forall₂_congr fun j hj => ?_
  rw [hc j hj, centralA_unpack hw hg hG (hT j hj), fpfA_unpack, eqA_unpack' hw (hT j hj) hr,
    comp_unpack' hw hr (hT j hj), fpfA_unpack]
  rfl

end Packed

end CFSG.KC.HatChkK

end
