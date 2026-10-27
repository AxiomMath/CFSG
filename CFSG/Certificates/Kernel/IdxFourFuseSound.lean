module

public import Certificates.Data.Kernel.IdxFourFuseK
public import CFSG.Certificates.Kernel.IdxFourSiftSound
public import CFSG.Certificates.Kernel.IdxFourChainCard
public import CFSG.GF2Type.Smith1979.GammaU.Violation

public section

namespace CFSG.KC.IF4F

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.GF2Type.Smith1979.GammaU

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

section Chain

variable {SP SI : Nat} {T O PS B : List Nat} {TL WD : List (List Nat)}
  {TR R : List (List (List Nat))} {j0 n : Nat}

theorem lvlGrp_eq_genGrp {gs : List (Array Nat)} (htl : TL.getD 0 [] = List.range j0)
    (hlen : gs.length = j0) (hr : ∀ j < j0, rowsP (look SP j) = gs.getD j #[]) :
    lvlGrp SP TL 0 = Viol.genGrp gs := by
  rw [lvlGrp, Viol.genGrp, htl]
  congr 1
  ext U
  simp only [Viol.GenSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, hg, hU⟩
    rw [List.mem_range] at hg
    have hg' : g < gs.length := by rw [hlen]; exact hg
    refine ⟨gs[g], List.getElem_mem hg', fun v => ?_⟩
    rw [hU v, linP_eq_of_rowsP (hr g hg), getD_of_lt _ hg']
  · rintro ⟨r, hr', hU⟩
    obtain ⟨g, hg, rfl⟩ := List.getElem_of_mem hr'
    have hg' : g < j0 := by rw [← hlen]; exact hg
    refine ⟨g, List.mem_range.2 hg', fun v => ?_⟩
    rw [hU v, linP_eq_of_rowsP (hr g hg'), getD_of_lt _ hg]

theorem eltP_eq (q : Nat) :
    eltP T O q =
      mulP (look (T.getD 0 0) (q / O.getD 1 0)) (look (T.getD 1 0) (q % O.getD 1 0)) := by
  simp only [eltP, nthD_eq]
  rfl

theorem exists_mem_eltP (hC : TreeHyp SP SI T O PS B TL WD TR 2 j0 n) :
    ∀ q < O.getD 0 0 * O.getD 1 0, ∃ U ∈ lvlGrp SP TL 0, IsP U (eltP T O q) := by
  intro q hq
  have h1 : 0 < O.getD 1 0 := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hq; omega
  obtain ⟨U, hU, hUP⟩ := hC.exists_tr (i := 0) (by omega) (q / O.getD 1 0)
    ((Nat.div_lt_iff_lt_mul h1).2 hq)
  obtain ⟨V, hV, hVP⟩ := hC.exists_tr (i := 1) (by omega) (q % O.getD 1 0) (Nat.mod_lt _ h1)
  exact ⟨U * V, Subgroup.mul_mem _ hU hV, by rw [eltP_eq]; exact hUP.mul hVP⟩

theorem exists_eltP (hC : ChainHyp SP SI T O PS B TL WD TR R 2 j0 n) {U : GL}
    (hU : U ∈ lvlGrp SP TL 0) : ∃ q < O.getD 0 0 * O.getD 1 0, IsP U (eltP T O q) := by
  obtain ⟨x, hx, V, hV, h, hh, rfl⟩ := hC.surj (i := 0) (by omega) hU
  obtain ⟨y, hy, V', hV', h', hh', rfl⟩ := hC.surj (i := 1) (by omega) hh
  have hb : lvlGrp SP TL (1 + 1) = ⊥ := hC.lvlGrp_eq_bot
  rw [hb, Subgroup.mem_bot] at hh'
  subst hh'
  refine ⟨x * O.getD 1 0 + y, ?_, ?_⟩
  · have : (x + 1) * O.getD 1 0 ≤ O.getD 0 0 * O.getD 1 0 := Nat.mul_le_mul_right _ hx
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · have h1 : 0 < O.getD 1 0 := by omega
    rw [eltP_eq, Nat.add_comm, Nat.add_mul_div_right _ _ h1, Nat.div_eq_of_lt hy, Nat.zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy, mul_one]
    exact hV.mul hV'

end Chain

theorem fld_zero (h : Nat) : fld h 0 = h &&& 4095 := by
  change (h >>> 0) &&& 4095 = h &&& 4095
  rw [Nat.shiftRight_zero]

theorem mulPk_congr : ∀ (k : Nat) {g h g' h' : Nat},
    (∀ j < k, ap12 g (fld h j) = ap12 g' (fld h' j)) → mulPk k g h = mulPk k g' h'
  | 0, _, _, _, _, _ => rfl
  | k + 1, g, h, g', h', hf => by
    change (ap12 g (h &&& 4095) ||| mulPk k g (h >>> 12) <<< 12) =
      (ap12 g' (h' &&& 4095) ||| mulPk k g' (h' >>> 12) <<< 12)
    have h0 := hf 0 (Nat.succ_pos k)
    rw [fld_zero, fld_zero] at h0
    rw [h0, mulPk_congr k (g := g) (h := h >>> 12) (g' := g') (h' := h' >>> 12) (fun j hj => by
      rw [fld_shiftRight, fld_shiftRight]
      exact hf (j + 1) (by omega))]

theorem linP_single (m : Nat) (j : Fin 12) : linP m (Pi.single j 1) = vecOf (fld m j) := by
  rw [linP_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem mulP_eq_of_isP {U : GL} {g h g' h' : Nat} (h1 : IsP U (mulP g h))
    (h2 : IsP U (mulP g' h')) : mulP g h = mulP g' h' := by
  refine mulPk_congr 12 fun j hj => ?_
  have e := (h1 (Pi.single ⟨j, hj⟩ 1)).symm.trans (h2 (Pi.single ⟨j, hj⟩ 1))
  rw [linP_single, linP_single, fld_mulP, fld_mulP] at e
  exact vecOf_inj (ap12_lt _ _) (ap12_lt _ _) e

theorem mulP_idP : mulP idP idP = idP := by decide +kernel

theorem mulP_self_eq_idP {s : GL} {x : Nat} (hs : IsP s x) (h2 : s * s = 1) :
    mulP x x = idP := by
  have a := hs.mul hs
  rw [h2] at a
  have b : IsP 1 (mulP idP idP) := by rw [mulP_idP]; exact IsP.one
  rw [← mulP_idP]
  exact mulP_eq_of_isP a b

section
variable {T O ET EO : List Nat} {Q : Nat} {L : List Nat} {W : List (List Nat)}

theorem fullOK_spec {s : Nat} : ∀ {w : List Nat}, fullOK ET EO Q L s w = true →
    ∃ m f as, f < 4 ∧ pathOK EO as = true ∧
      mulP (mulP (pathP ET as) (look Q f)) s = mulP (subP L m) (mulP (pathP ET as) (look Q f))
  | [], h => absurd (h : false = true) Bool.false_ne_true
  | [_], h => absurd (h : false = true) Bool.false_ne_true
  | m :: f :: as, h => by
    change (Nat.blt f 4 && pathOK EO as &&
      conjOK (mulP (pathP ET as) (look Q f)) s (subP L m)) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq, conjOK, Nat.beq_eq] at h
    exact ⟨m, f, as, h.1.1, h.1.2, h.2⟩

theorem recW_zero {s : Nat} {w : List Nat} (h : recW T O ET EO Q L W s w = true)
    (h0 : w.getD 0 0 = 0) : fullOK ET EO Q L s (w.drop 1) = true := by
  unfold recW at h
  have hb : Nat.beq (nthD 0 w 0) 0 = true := by rw [nthD_eq, h0]; rfl
  rwa [hb, cond_true, dropN_eq] at h

theorem recW_ne {s : Nat} {w : List Nat} (h : recW T O ET EO Q L W s w = true)
    (h0 : w.getD 0 0 ≠ 0) :
    w.getD 1 0 < O.getD 0 0 * O.getD 1 0 ∧ w.getD 2 0 < O.getD 0 0 * O.getD 1 0 ∧
      (W.getD (w.getD 1 0) []).getD 0 0 = 0 ∧
      mulP (eltP T O (w.getD 2 0)) (eltP T O (w.getD 1 0)) =
        mulP s (eltP T O (w.getD 2 0)) := by
  unfold recW at h
  have hb : Nat.beq (nthD 0 w 0) 0 = false := by
    rw [nthD_eq]
    cases h' : Nat.beq (w.getD 0 0) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h') h0
  rw [hb, cond_false] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, nthD_eq, conjOK, Nat.mul_eq] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem witOK_spec {q : Nat} (h : witOK T O ET EO Q L W q = true)
    (hsq : mulP (eltP T O q) (eltP T O q) = idP) :
    recW T O ET EO Q L W (eltP T O q) (W.getD q []) = true := by
  unfold witOK sqOK at h
  rwa [hsq, Nat.beq_refl, cond_true, nthD_eq] at h

theorem fuseBlk_spec {c : Nat} (h : fuseBlk T O ET EO Q L W c = true) :
    ∀ j < 32, witOK T O ET EO Q L W (32 * c + j) = true := by
  unfold fuseBlk at h
  exact (allBelow_iff _ _).1 h

theorem conj_of_witOK {S M Lg : Subgroup GL}
    (hS : ∀ q < O.getD 0 0 * O.getD 1 0, ∃ U ∈ S, IsP U (eltP T O q))
    (hpath : ∀ as, pathOK EO as = true → ∃ P ∈ M, IsP P (pathP ET as))
    (hQ : ∀ f < 4, ∃ U ∈ M, IsP U (look Q f)) (hL : ∀ g ∈ L, ∃ U ∈ Lg, IsP U g)
    (hSM : S ≤ M) (hwit : ∀ q < O.getD 0 0 * O.getD 1 0, witOK T O ET EO Q L W q = true)
    {q : Nat} (hq : q < O.getD 0 0 * O.getD 1 0) {s : GL} (hs : IsP s (eltP T O q))
    (h2 : s * s = 1) : ∃ h ∈ M, h * s * h⁻¹ ∈ Lg := by
  have full : ∀ {x : Nat} {w : List Nat} {t : GL}, fullOK ET EO Q L x w = true → IsP t x →
      ∃ h ∈ M, h * t * h⁻¹ ∈ Lg := by
    intro x w t hw ht
    obtain ⟨m, f, as, hf, hp, heq⟩ := fullOK_spec hw
    obtain ⟨P, hP, hPP⟩ := hpath as hp
    obtain ⟨F, hF, hFP⟩ := hQ f hf
    obtain ⟨l, hl, hlP⟩ := exists_subP (K := Lg) L hL m
    have hH := hPP.mul hFP
    have e : P * F * t = l * (P * F) :=
      IsP.inj (hH.mul ht) (by rw [heq]; exact hlP.mul hH)
    refine ⟨P * F, M.mul_mem hP hF, ?_⟩
    rw [e, mul_inv_cancel_right]
    exact hl
  have hr := witOK_spec (hwit q hq) (mulP_self_eq_idP hs h2)
  by_cases h0 : (W.getD q []).getD 0 0 = 0
  · exact full (recW_zero hr h0) hs
  · obtain ⟨hp, hc, hW, heq⟩ := recW_ne hr h0
    obtain ⟨Sp, -, hSpP⟩ := hS _ hp
    obtain ⟨C, hC, hCP⟩ := hS _ hc
    have e : C * Sp = s * C := IsP.inj (hCP.mul hSpP) (by rw [heq]; exact hs.mul hCP)
    have e2 : Sp = C⁻¹ * s * C := by rw [mul_assoc, ← e, inv_mul_cancel_left]
    have hSp2 : Sp * Sp = 1 := by
      rw [e2]
      calc C⁻¹ * s * C * (C⁻¹ * s * C) = C⁻¹ * (s * s) * C := by group
        _ = 1 := by rw [h2, mul_one, inv_mul_cancel]
    have hrp := witOK_spec (hwit _ hp) (mulP_self_eq_idP hSpP hSp2)
    obtain ⟨h, hh, hhl⟩ := full (recW_zero hrp hW) hSpP
    refine ⟨h * C⁻¹, M.mul_mem hh (M.inv_mem (hSM hC)), ?_⟩
    have : h * C⁻¹ * s * (h * C⁻¹)⁻¹ = h * Sp * h⁻¹ := by rw [e2]; group
    rw [this]
    exact hhl

end

end CFSG.KC.IF4F

end
