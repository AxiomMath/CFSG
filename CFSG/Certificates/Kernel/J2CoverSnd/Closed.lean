
module

public import CFSG.Certificates.Kernel.Child3Reps
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelNative
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.SporSch.ConjClosureSpec

public section

namespace CFSG.KC.J2Cover.Snd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover

theorem pg_inv_left {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) (h : pcomp n w (mask w) p q = pidn n w) :
    ∀ i < n, pg w (mask w) q (pg w (mask w) p i) = i := by
  obtain ⟨hn, hw, -, hpr⟩ := PF.canon_facts hp
  obtain ⟨-, -, -, hqr⟩ := PF.canon_facts hq
  have hn32 : n < 2 ^ 32 := by omega
  have hpq : ∀ j < n, pg w (mask w) p (pg w (mask w) q j) = j := fun j hj => by
    have e : pg w (mask w) (pcomp n w (mask w) p q) j = pg w (mask w) (pidn n w) j := by rw [h]
    rwa [PF.pg_pcomp hn32 hj, PF.pg_pidn hn hw hj] at e
  let F : Fin n → Fin n := fun j => ⟨pg w (mask w) p j, hpr j j.2⟩
  have hF : Function.Surjective F := fun j =>
    ⟨⟨pg w (mask w) q j, hqr j j.2⟩, Fin.ext (hpq j j.2)⟩
  have hFi : Function.Injective F := Finite.injective_iff_surjective.2 hF
  intro i hi
  exact congrArg Fin.val (hFi (a₁ := ⟨pg w (mask w) q (pg w (mask w) p i), hqr _ (hpr i hi)⟩)
    (a₂ := ⟨i, hi⟩) (Fin.ext (hpq _ (hpr i hi))))

theorem cj_cj {n w l X : Nat} {GP GIP : Nat → Nat}
    (hP : canonK n w (mask w) (n * w) (GP l) = true)
    (hI : canonK n w (mask w) (n * w) (GIP l) = true) (hX : canonK n w (mask w) (n * w) X = true)
    (hIP : ∀ i < n, pg w (mask w) (GIP l) (pg w (mask w) (GP l) i) = i) :
    cj n w GIP GP l (cj n w GP GIP l X) = X := by
  obtain ⟨hn, hw, hX0, hXr⟩ := PF.canon_facts hX
  obtain ⟨-, -, -, hPr⟩ := PF.canon_facts hP
  obtain ⟨-, -, -, hIr⟩ := PF.canon_facts hI
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  unfold cj
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) hX0 fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hPr i hi), PF.pg_pcomp hn32 (hPr i hi),
    PF.pg_pcomp hn32 (hIr _ (hPr i hi)), hIP i hi, hIP _ (hXr i hi)]

theorem closedOK_of_rec {n w g N cap : Nat} {GP GIP CI E P L K S SI : Nat → Nat}
    {CS OFF : List Nat} {gens gensInv : Array Table}
    (hg : gens.size = g ∧ gensInv.size = g ∧ ∀ l < g, gens[l]! = arrTable n (unpack n w (GP l)) ∧
      gensInv[l]! = arrTable n (unpack n w (GIP l)))
    (hgc : ∀ l < g, canonK n w (mask w) (n * w) (GP l) = true ∧
      canonK n w (mask w) (n * w) (GIP l) = true)
    (hinv : ∀ l < g, pcomp n w (mask w) (GP l) (GIP l) = pidn n w)
    (hoff : offOK CS OFF N = true)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K S SI N cap j = true)
    (hpos : ∀ c ∈ CS, 0 < c) (hn : n = 315) :
    ∀ i < CS.length, CFSG.ComponentClassification.J2Cover.Kernel.closedOK gens gensInv
      (conjClosure n gens gensInv (arrTable n (unpack n w (E (lget OFF i)))) cap).1 = true := by
  subst hn
  intro i hi
  rw [closure_rep hg hgc hoff h hpos hi]
  have CI' := fun k (hk : k < lget CS i) => ci_eq hoff h hi hk
  have F := fun k (hk : k < lget CS i) => repK_facts (h _ (CI' k hk).1)
  have hcan : ∀ k < lget CS i, canonK 315 w (mask w) (315 * w) (E (lget OFF i + k)) = true :=
    fun k hk => (F k hk).canon
  have hn32 : (315 : Nat) < 2 ^ 32 := by decide
  have hcl : ∀ k (hk : k < lget CS i), ∀ l < g, K (g * (lget OFF i + k) + l) < lget CS i ∧
      E (lget OFF i + K (g * (lget OFF i + k) + l)) = cj 315 w GP GIP l (E (lget OFF i + k)) := by
    intro k hk l hl
    have C := (F k hk).close l hl
    rw [(CI' k hk).2] at C
    exact ⟨C.1, C.2.1⟩
  unfold CFSG.ComponentClassification.J2Cover.Kernel.closedOK
  dsimp only
  rw [List.all_eq_true]
  intro x hx
  rw [Array.toList_ofFn, List.mem_ofFn] at hx
  obtain ⟨⟨k, hk⟩, rfl⟩ := hx
  dsimp only
  rw [List.all_eq_true]
  intro l hl
  rw [List.mem_range, hg.1] at hl
  rw [Bool.and_eq_true, List.any_eq_true, List.any_eq_true, (hg.2.2 l hl).1, (hg.2.2 l hl).2]
  have hPc := (hgc l hl).1
  have hIc := (hgc l hl).2
  have hPr := (PF.canon_facts hPc).2.2.2
  have hIr := (PF.canon_facts hIc).2.2.2
  have hXr := (PF.canon_facts (hcan k hk)).2.2.2
  have hIP := pg_inv_left hPc hIc (hinv l hl)
  constructor
  · refine ⟨arrTable 315 (unpack 315 w (E (lget OFF i + K (g * (lget OFF i + k) + l)))), ?_, ?_⟩
    · rw [Array.toList_ofFn, List.mem_ofFn]
      exact ⟨⟨_, (hcl k hk l hl).1⟩, rfl⟩
    · have e : conjT 315 (arrTable 315 (unpack 315 w (GP l)))
          (arrTable 315 (unpack 315 w (GIP l))) (arrTable 315 (unpack 315 w (E (lget OFF i + k)))) =
          arrTable 315 (unpack 315 w (E (lget OFF i + K (g * (lget OFF i + k) + l)))) := by
        rw [(hcl k hk l hl).2]
        exact conjT_tabP hn32 hXr hIr
      rw [e]
      exact CFSG.KS.SporSch.ClsSpec.tblEq_self _
  · let τ : Fin (lget CS i) → Fin (lget CS i) := fun a =>
      ⟨K (g * (lget OFF i + a.val) + l), (hcl a.val a.2 l hl).1⟩
    have hτ : Function.Injective τ := by
      intro a b e
      have e' : K (g * (lget OFF i + a.val) + l) = K (g * (lget OFF i + b.val) + l) :=
        congrArg Fin.val e
      have h1 := (hcl a.val a.2 l hl).2
      have h2 := (hcl b.val b.2 l hl).2
      rw [e'] at h1
      have h4 := congrArg (cj 315 w GIP GP l) (h1.symm.trans h2)
      rw [cj_cj hPc hIc (hcan a.val a.2) hIP, cj_cj hPc hIc (hcan b.val b.2) hIP] at h4
      have := E_inj h (CI' a.val a.2).1 (CI' b.val b.2).1 h4
      exact Fin.ext (by omega)
    obtain ⟨⟨k', hk'⟩, e⟩ := Finite.surjective_of_injective hτ ⟨k, hk⟩
    have ek : K (g * (lget OFF i + k') + l) = k := congrArg Fin.val e
    have h1 := (hcl k' hk' l hl).2
    rw [ek] at h1
    refine ⟨arrTable 315 (unpack 315 w (E (lget OFF i + k'))), ?_, ?_⟩
    · rw [Array.toList_ofFn, List.mem_ofFn]
      exact ⟨⟨k', hk'⟩, rfl⟩
    · have e2 : conjT 315 (arrTable 315 (unpack 315 w (GIP l)))
          (arrTable 315 (unpack 315 w (GP l))) (arrTable 315 (unpack 315 w (E (lget OFF i + k)))) =
          arrTable 315 (unpack 315 w (E (lget OFF i + k'))) := by
        refine (conjT_tabP (GP := GIP) (GIP := GP) (l := l) hn32 hXr hPr).trans ?_
        rw [h1, cj_cj hPc hIc (hcan k' hk') hIP]
      rw [e2]
      exact CFSG.KS.SporSch.ClsSpec.tblEq_self _

end CFSG.KC.J2Cover.Snd

end
