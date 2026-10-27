module

public import CFSG.Certificates.Kernel.BabyMonster.DyConjAlg
public import CFSG.Certificates.Kernel.BabyMonster.FixSound
public import CFSG.Certificates.Kernel.BabyMonster.DyConjOrd

public section

namespace CFSG.KC.BM.Ln

open CFSG.KC.BM CFSG.KC.BM.Fix
open scoped Matrix

abbrev Letter := List ℕ × ℕ × ℕ

theorem intRep_prod {B : Matrix (Fin 4371) (Fin 4371) ℚ} :
    ∀ {L : List Letter} {S : List (Matrix (Fin 4371) (Fin 4371) (ZMod 2))},
      List.Forall₂ (fun l s => IntRep (Cn B (mkMat l.2.2)) s) L S →
      IntRep ((L.map fun l => Cn B (mkMat l.2.2)).prod) S.prod
  | [], [], _ => IntRep.one
  | _ :: _, _ :: _, List.Forall₂.cons h hs => (h.mul (intRep_prod hs)).congr rfl rfl

theorem derive_x {B : Matrix (Fin 4371) (Fin 4371) ℚ} (hB : IsUnit B.det) {Ly Lx : Letter}
    {Lu : List Letter} (hM : ∀ l ∈ (Ly :: Lu) ++ [Lx], MonoOK l.1 l.2.2 l.2.1)
    (hlab : cjRel ((Ly :: Lu).map (·.1)) ((Ly :: Lu).map (·.2.1)) ((Lu ++ [Lx]).map (·.1))
      ((Lu ++ [Lx]).map (·.2.1)) = true)
    {Sy Sx : Matrix (Fin 4371) (Fin 4371) (ZMod 2)} {Su : List (Matrix (Fin 4371) (Fin 4371) (ZMod 2))}
    (hu : List.Forall₂ (fun l s => IntRep (Cn B (mkMat l.2.2)) s) Lu Su)
    (hy : IntRep (Cn B (mkMat Ly.2.2)) Sy) (hS : Sy * Su.prod = Su.prod * Sx) :
    IntRep (Cn B (mkMat Lx.2.2)) Sx := by
  have hrel := cjRel_sound (fun l hl => hM l (by simp at hl ⊢; tauto))
    (fun l hl => hM l (by simp at hl ⊢; tauto)) hlab
  rw [List.map_cons, List.prod_cons, List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.mul_one] at hrel
  obtain ⟨k, hk, hU⟩ := word_pow_eq_one (L := Lu) (fun l hl => hM l (by simp; tauto))
  refine transfer_x hB hrel hk hU ?_ hy hS
  rw [Cn_prod hB, List.map_map]
  exact intRep_prod hu

theorem derive_y {B : Matrix (Fin 4371) (Fin 4371) ℚ} (hB : IsUnit B.det) {Ly Lx : Letter}
    {Lu : List Letter} (hM : ∀ l ∈ (Ly :: Lu) ++ [Lx], MonoOK l.1 l.2.2 l.2.1)
    (hlab : cjRel ((Ly :: Lu).map (·.1)) ((Ly :: Lu).map (·.2.1)) ((Lu ++ [Lx]).map (·.1))
      ((Lu ++ [Lx]).map (·.2.1)) = true)
    {Sy Sx : Matrix (Fin 4371) (Fin 4371) (ZMod 2)} {Su : List (Matrix (Fin 4371) (Fin 4371) (ZMod 2))}
    (hu : List.Forall₂ (fun l s => IntRep (Cn B (mkMat l.2.2)) s) Lu Su)
    (hx : IntRep (Cn B (mkMat Lx.2.2)) Sx) (hS : Sy * Su.prod = Su.prod * Sx) :
    IntRep (Cn B (mkMat Ly.2.2)) Sy := by
  have hrel := cjRel_sound (fun l hl => hM l (by simp at hl ⊢; tauto))
    (fun l hl => hM l (by simp at hl ⊢; tauto)) hlab
  rw [List.map_cons, List.prod_cons, List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.mul_one] at hrel
  obtain ⟨k, hk, hU⟩ := word_pow_eq_one (L := Lu) (fun l hl => hM l (by simp; tauto))
  refine transfer_y hB hrel hk hU ?_ hx hS
  rw [Cn_prod hB, List.map_map]
  exact intRep_prod hu

theorem allBlocksN_of {R : List (List ℕ)} {S : List ℕ} :
    ∀ (s : ℕ), R.length + s = 69 → S.length + s = 69 →
      (∀ t < R.length, blockOKn 4371 (R.getD t []) (S.getD t 0) (s + t) = true) → AllBlocksN R S s := by
  induction R generalizing S with
  | nil =>
    intro s hR hS _
    rcases S with _ | ⟨x, S⟩
    · exact AllBlocksN.nil s
    · simp at hR hS
      omega
  | cons blk R ih =>
    intro s hR hS h
    rcases S with _ | ⟨T, S⟩
    · simp at hR hS
      omega
    · refine AllBlocksN.cons blk T s R S ?_ (ih (Nat.succ s) (by simp at hR; omega) (by simp at hS; omega)
        (fun t ht => ?_))
      · have := h 0 (by simp)
        simpa using this
      · have := h (t + 1) (by simp; omega)
        simp only [List.getD_cons_succ] at this
        rw [show s + (t + 1) = Nat.succ s + t by omega] at this
        exact this

theorem allStripsN_refl (Ws : List (List ℕ)) :
    ∀ A : List ℕ, AllStripsN Ws A (A.map (mulWn 4371 Ws))
  | [] => AllStripsN.nil
  | a :: A => AllStripsN.cons a _ A _ (Nat.beq_refl _) (allStripsN_refl Ws A)

theorem nthLL_getD : ∀ (L : List (List ℕ)) (i : ℕ), nthLL L i = L.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => nthLL_getD L i

theorem rows_eq_strips {R : List (List ℕ)} {S : List ℕ} (hb : ∀ s < 69, cjBlk R S s = true)
    (hR : R.length = 69) (hwf : wfMatn 4371 S = true) :
    CFSG.KC.BSeed.rowsMat 4371 (Lat.recOf R) = stripMatn S := by
  refine rowsMat_eq_stripMatn (allBlocksN_of 0 (by omega) (by rw [(SL.wf_bit hwf).1]) fun t ht => ?_) hwf
  have := hb t (by omega)
  unfold cjBlk at this
  rw [nthLL_getD, Dy.nthN_eq, show 0 + t = t by omega] at *
  exact this

theorem foldl_mul_eq (a : Matrix (Fin 4371) (Fin 4371) (ZMod 2)) :
    ∀ L : List (Matrix (Fin 4371) (Fin 4371) (ZMod 2)), L.foldl (· * ·) a = a * L.prod
  | [] => by simp
  | b :: L => by rw [List.foldl_cons, foldl_mul_eq (a * b) L, List.prod_cons, Matrix.mul_assoc]

theorem strip_rel {Sy Sx S1 : List ℕ} {Us : List (List ℕ)}
    (hwf : ∀ W ∈ Sy :: S1 :: (Us ++ [Sx]), wfMatn 4371 W = true)
    (h : AllStripsN (S1 :: Us) Sy (S1.map (mulWn 4371 (Us ++ [Sx])))) :
    stripMatn Sy * ((S1 :: Us).map stripMatn).prod = ((S1 :: Us).map stripMatn).prod * stripMatn Sx := by
  have h1 := stripMatn_mul_of_allStrips (fun W hW => hwf W (by simp at hW ⊢; tauto))
    (hwf Sy (by simp)) h
  have h2 := stripMatn_mul_of_allStrips (Ws := Us ++ [Sx]) (A := S1) (fun W hW => hwf W (by simp at hW ⊢; tauto))
    (hwf S1 (by simp)) (allStripsN_refl _ S1)
  rw [foldl_mul_eq] at h1 h2
  rw [h1, ← h2, List.map_cons, List.prod_cons, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.mul_assoc]

end CFSG.KC.BM.Ln

end
