module

public import CFSG.GF2Type.SmithTypeE.L6.E23Four
public import CFSG.GF2Type.SmithTypeE.L6.ModCert
public import Certificates.Certificate38653

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod
open CFSG.SmithE (applyCols)
open CFSG.LargeExtraspecial.SMod20 (V decode decode_xor eq_of_decode_eq)
open CFSG.LargeExtraspecial.S14.SMG (code_lt)

theorem word0Check_holds {i j : Nat} (hi : i < 1395)
    (hj : j < 1395) (h₀ : InE 0 i) (h : InE 0 j) :
    ∃ w : List Nat, (∀ r ∈ w, r < 1953 ∧ mfPairKind 0 r = 0) ∧ e4fApplyWord w (wt i) = wt j :=
  Certificates.certificate38653.1 i hi j hj h₀ h

theorem plane0Check_holds {l : Nat} (hl : l < 1953)
    (hk : mfPairKind 0 l = 2) :
    ∃ i < 1395, InE 0 i ∧ applyCols (tvCols l) (wt i) = wt i ∧ ¬ InE l i :=
  Certificates.certificate38653.2 l hl hk

section Conv


theorem inEV_of_inE {k i : Nat} (hk : k < 1953) (h : InE k i) : InEV (tvEquiv k) (wtV i) := by
  obtain ⟨c, -, hc⟩ := h
  refine ⟨decode c, ?_⟩
  rw [wtV, ← hc, decode_xor, tvEquiv_decode hk]

theorem inE_of_inEV {k i : Nat} (hk : k < 1953) (hi : i < 1395)
    (h : InEV (tvEquiv k) (wtV i)) : InE k i := by
  obtain ⟨x, hx⟩ := h
  have hxc : decode (CFSG.LargeExtraspecial.S14.SMG.code x) = x := decode_code x
  have hc : CFSG.LargeExtraspecial.S14.SMG.code x < 2 ^ 20 := code_lt x
  refine ⟨_, hc, eq_of_decode_eq (Nat.xor_lt_two_pow (n := 20) (applyCols_tv_lt hk _) hc)
    (wt_lt' hi) ?_⟩
  rw [decode_xor, ← tvEquiv_decode hk, hxc]
  exact hx.symm

end Conv

section Words


theorem applyWord_lt {w : List Nat} (hw : ∀ r ∈ w, r < 1953) {c : Nat} (hc : c < 2 ^ 20) :
    applyWord w c < 2 ^ 20 := by
  induction w with
  | nil => exact hc
  | cons r w _ => exact applyCols_tv_lt (hw r List.mem_cons_self) _

end Words

section Base


theorem creach_word (w : List Nat) (hw : ∀ r ∈ w, r < 1953 ∧ mfPairKind 0 r = 0) (c : Nat) :
    CReach (tvE 0) (decode c) (decode (e4fApplyWord w c)) := by
  induction w with
  | nil => exact CReach.refl _ _
  | cons r w ih =>
    obtain ⟨hr, hk⟩ := hw r List.mem_cons_self
    have ih' := ih fun r' hr' => hw r' (List.mem_cons_of_mem _ hr')
    have e : decode (e4fApplyWord (r :: w) c) = tvE ⟨r, hr⟩ (decode (e4fApplyWord w c)) := by
      show decode (applyCols (tvCols r) (e4fApplyWord w c)) = tvEquiv r (decode _)
      rw [tvEquiv_decode hr]
    rw [e]
    exact CReach.cons ⟨r, hr⟩ ((pair0_kind ⟨r, hr⟩).1 hk).symm ih'

theorem creach_pair {i₀ i : Nat} (hi₀ : i₀ < 1395) (hi : i < 1395) (h₀ : InE 0 i₀)
    (h : InE 0 i) : CReach (tvE 0) (wtV i₀) (wtV i) := by
  obtain ⟨w, hw, he⟩ := word0Check_holds hi₀ hi h₀ h
  have := creach_word w hw (wt i₀)
  rw [he] at this
  exact this

end Base

section Word


theorem rhoMod_wtV_inv_smul (g : T6) (i : Fin 1395) :
    rhoMod g (wtV ((g⁻¹ • i : Fin 1395) : Nat)) = wtV i := by
  rw [rhoMod_wtV, smul_inv_smul]

theorem word_general {k i₀ i : Nat} (hk : k < 1953) (hi₀ : i₀ < 1395) (hi : i < 1395)
    (h₀ : InE k i₀) (h : InE k i) :
    ∃ w : List Nat, (∀ r ∈ w, r < 1953 ∧ ∀ c < 2 ^ 20,
      applyCols (tvCols r) (applyCols (tvCols k) c) =
        applyCols (tvCols k) (applyCols (tvCols r) c)) ∧ applyWord w (wt i₀) = wt i := by
  obtain ⟨g, hg⟩ := exists_T6_zero ⟨k, hk⟩
  set j₀ : Fin 1395 := g⁻¹ • (⟨i₀, hi₀⟩ : Fin 1395) with hj₀
  set j : Fin 1395 := g⁻¹ • (⟨i, hi⟩ : Fin 1395) with hj
  have e₀ : rhoMod g (wtV j₀.val) = wtV i₀ := rhoMod_wtV_inv_smul g ⟨i₀, hi₀⟩
  have e₁ : rhoMod g (wtV j.val) = wtV i := rhoMod_wtV_inv_smul g ⟨i, hi⟩
  have hV₀ : InEV (tvE 0) (wtV j₀.val) := by
    have h1 : InEV (tvE ((g : Equiv.Perm (Fin 1953)) 0)) (rhoMod g (wtV j₀.val)) := by
      rw [e₀, hg]
      exact inEV_of_inE hk h₀
    exact (inEV_tvE_smul g 0 _).mp h1
  have hV₁ : InEV (tvE 0) (wtV j.val) := by
    have h1 : InEV (tvE ((g : Equiv.Perm (Fin 1953)) 0)) (rhoMod g (wtV j.val)) := by
      rw [e₁, hg]
      exact inEV_of_inE hk h
    exact (inEV_tvE_smul g 0 _).mp h1
  have hR := (creach_pair j₀.2 j.2 (inE_of_inEV (by norm_num) j₀.2 hV₀)
    (inE_of_inEV (by norm_num) j.2 hV₁)).smul g
  rw [e₀, e₁, hg] at hR
  obtain ⟨w', hw', hw'e⟩ := hR
  refine ⟨w'.map Fin.val, fun r hr => ?_, ?_⟩
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    exact ⟨r'.2, comm_code_of_relC r'.2 hk (hw' r' hr')⟩
  · have key : ∀ (w : List (Fin 1953)) (c : Nat), decode (applyWord (w.map Fin.val) c) =
        wordF w (decode c) := by
      intro w c
      induction w with
      | nil => rfl
      | cons r w ih =>
        simp only [List.map_cons, applyWord, wordF]
        rw [← ih]
        exact (tvEquiv_decode r.2 _).symm
    have hlt : ∀ r ∈ w'.map Fin.val, r < 1953 := by
      intro r hr
      obtain ⟨r', -, rfl⟩ := List.mem_map.mp hr
      exact r'.2
    refine eq_of_decode_eq (applyWord_lt hlt (wt_lt' hi₀)) (wt_lt' hi) ?_
    rw [key]
    exact hw'e

end Word

@[expose] def PlaneV (a b : V ≃ₗ[ZMod 2] V) : Prop :=
  ∃ i : Fin 1395, InEV a (wtV i.val) ∧ b (wtV i.val) = wtV i.val ∧ ¬ InEV b (wtV i.val)

section Plane


theorem planeV_base (l : Fin 1953) (hk : mfPairKind 0 l.val = 2) : PlaneV (tvE 0) (tvE l) := by
  obtain ⟨i, hi, h0, hfix, hn⟩ := plane0Check_holds l.2 hk
  refine ⟨⟨i, hi⟩, inEV_of_inE (by norm_num) h0, ?_, fun hmem => hn (inE_of_inEV l.2 hi hmem)⟩
  change tvEquiv l.val (decode (wt i)) = decode (wt i)
  rw [tvEquiv_decode l.2, hfix]

theorem planeV_smul (g : T6) {k l : Fin 1953} (h : PlaneV (tvE k) (tvE l)) :
    PlaneV (tvE ((g : Equiv.Perm (Fin 1953)) k)) (tvE ((g : Equiv.Perm (Fin 1953)) l)) := by
  obtain ⟨i, h1, h2, h3⟩ := h
  refine ⟨g • i, ?_, ?_, ?_⟩
  · rw [← rhoMod_wtV]
    exact (inEV_tvE_smul g k _).mpr h1
  · rw [← rhoMod_wtV]
    exact (tvE_fix_smul g l _).mpr h2
  · rw [← rhoMod_wtV]
    exact fun h => h3 ((inEV_tvE_smul g l _).mp h)

theorem plane_general {k l : Nat} (hk : k < 1953) (hl : l < 1953) (_hkl : k ≠ l)
    (hC : ¬ ∀ c < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) c) =
      applyCols (tvCols l) (applyCols (tvCols k) c))
    (hB : ¬ ∀ c < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c))) :
    ∃ i < 1395, InE k i ∧ applyCols (tvCols l) (wt i) = wt i ∧ ¬ InE l i := by
  obtain ⟨g, hg⟩ := exists_T6_zero ⟨k, hk⟩
  obtain ⟨l', hl'⟩ : ∃ l' : Fin 1953, (g : Equiv.Perm (Fin 1953)) l' = ⟨l, hl⟩ :=
    ⟨(g : Equiv.Perm (Fin 1953))⁻¹ ⟨l, hl⟩, by simp⟩
  have hkind := kind_two_of_not g l' (by
      rw [hg, hl']
      exact fun h => hC (comm_code_of_relC hk hl h))
    (by
      rw [hg, hl']
      exact fun h => hB (braid_code_of_relB hk hl h))
  have hP := planeV_smul g (planeV_base l' hkind)
  rw [hg, hl'] at hP
  obtain ⟨i, h1, h2, h3⟩ := hP
  refine ⟨i.val, i.2, inE_of_inEV hk i.2 h1, ?_, fun hE => h3 (inEV_of_inE hl hE)⟩
  have h2' : tvEquiv l (decode (wt i.val)) = decode (wt i.val) := h2
  rw [tvEquiv_decode hl] at h2'
  exact eq_of_decode_eq (applyCols_tv_lt hl _) (wt_lt' i.2) h2'

end Plane

theorem e23FourFacts :
    E23FourFacts where
  tv_invol := fun hr _ hc => tv_invol_code hr hc
  word := fun hk hi₀ hi h₀ h => word_general hk hi₀ hi h₀ h
  plane := fun hk hl hkl hC hB => plane_general hk hl hkl hC hB

end CFSG.GF2Type.SmithTypeE.L6
