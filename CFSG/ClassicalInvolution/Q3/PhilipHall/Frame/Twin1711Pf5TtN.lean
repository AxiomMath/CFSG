module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5OvrSem
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtClsLt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Cls
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Aut
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Fix
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Misc
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf3Sp0Aut

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open CFSG.Monster.B.Co2 PkG CovK CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic

set_option linter.unusedSectionVars false


theorem hout_Y : ∀ α : MulAut ↥ySub, ∃ g : ↥ySub, α = MulAut.conj g := by
  have hLie : CFSG.Blueprint.LieModel ModSp0 .PSp 3 2 1 :=
    Or.inl ⟨by decide, CFSG.Sporadic.Schreier.Co3.co3X36_classicalModel⟩
  have : Finite ModSp0 := inferInstance
  exact autInner_cover CovK.qYc CovK.qYc_surjective CovK.qYc_ker_central CovK.Y_perfect
    CFSG.Sporadic.Schreier.Co3.co3X36_center (Sp0Aut.autInner_of_lieModel_PSp hLie)

theorem q8_sq_eq_one : ∀ q : QuaternionGroup 2, q * q = 1 → q = 1 ∨ q = QuaternionGroup.a 2 := by
  decide

theorem qY_a2 : Sp6Cover.qY (QuaternionGroup.a 2) = Sp6Cover.tY := by
  rw [qY_a]
  show iY ^ 2 = tY
  exact iY_sq

theorem tY_unique : IsUniqueInvolution RY Sp6Cover.tY := by
  refine ⟨tY_mem, tY_ne_one, tY_mul_tY, ?_⟩
  intro y hy hy2
  obtain ⟨q, rfl⟩ := hy
  have h1 : q * q = 1 := by
    apply qY_injective
    rw [map_mul, hy2, map_one]
  rcases q8_sq_eq_one q h1 with rfl | rfl
  · left; exact map_one _
  · right; exact qY_a2

theorem RY_norm : ∀ s ∈ Sp0Core.TT Sp6Cover.tY, conjSub s RY = RY := by
  intro s hs
  have hs' : s ∈ Subgroup.centralizer ({Sp6Cover.tY} : Set ↥ySub) := mem_TT_iff.1 hs
  have hsi : s⁻¹ ∈ Subgroup.centralizer ({Sp6Cover.tY} : Set ↥ySub) :=
    (Subgroup.centralizer _).inv_mem hs'
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have := conj_mem_RY hs' h
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rwa [e] at this
  · intro h
    have := conj_mem_RY hsi h
    have e : s⁻¹ * x * s⁻¹⁻¹ = s⁻¹ * x * s := by group
    rwa [e] at this

theorem mem_tT_of_comm {g : ↥ySub} (h : g * Sp6Cover.tY = Sp6Cover.tY * g) : g ∈ tT := by
  rw [tT, Subgroup.mem_centralizer_singleton_iff]
  exact h

theorem hfix1_Y : Nat.card ↥(fixSet (⊤ : Subgroup ↥ySub) ({RY} : Set (Subgroup ↥ySub))) ≤ 96 := by
  have h := fixSet_top_card_le hout_Y ClsK.zY ClsK.zY_ne_one ClsK.zY_central ({RY} : Set (Subgroup ↥ySub))
    ((rowsT.filter fun r => decide (2 ≤ r.getD 1 0)).map elt) (by
      intro g hg
      have hi : g * iY = iY * g := hg iY ⟨RY, rfl, iY_mem⟩
      have hj : g * jY = jY * g := hg jY ⟨RY, rfl, jY_mem⟩
      have ht : g * Sp6Cover.tY = Sp6Cover.tY * g := hg Sp6Cover.tY ⟨RY, rfl, tY_mem⟩
      obtain ⟨r, hr, rfl⟩ := exists_row (mem_tT_of_comm ht)
      refine List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, ?_⟩, rfl⟩
      simpa using cc_flag hr (congrArg Subtype.val hi) (congrArg Subtype.val hj))
  have hl : ((rowsT.filter fun r => decide (2 ≤ r.getD 1 0)).map elt).length = 192 := by
    rw [List.length_map]
    exact rowsT_cntC2
  omega

theorem hfix2_Y : Nat.card ↥(fixSet (⊤ : Subgroup ↥ySub)
    ({RY, conjSub eE RY} : Set (Subgroup ↥ySub))) ≤ 8 := by
  have h := fixSet_top_card_le hout_Y ClsK.zY ClsK.zY_ne_one ClsK.zY_central
    ({RY, conjSub eE RY} : Set (Subgroup ↥ySub))
    ((rowsT.filter fun r => r.getD 1 0 == 4).map elt) (by
      intro g hg
      have hi : g * iY = iY * g := hg iY ⟨RY, by simp, iY_mem⟩
      have hj : g * jY = jY * g := hg jY ⟨RY, by simp, jY_mem⟩
      have ht : g * Sp6Cover.tY = Sp6Cover.tY * g := hg Sp6Cover.tY ⟨RY, by simp, tY_mem⟩
      have hi' : g * (eE * iY * eE⁻¹) = (eE * iY * eE⁻¹) * g :=
        hg _ ⟨conjSub eE RY, by simp, conj_mem_conjSub iY_mem⟩
      have hj' : g * (eE * jY * eE⁻¹) = (eE * jY * eE⁻¹) * g :=
        hg _ ⟨conjSub eE RY, by simp, conj_mem_conjSub jY_mem⟩
      obtain ⟨r, hr, rfl⟩ := exists_row (mem_tT_of_comm ht)
      refine List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, ?_⟩, rfl⟩
      simpa using cc_flag4 hr (congrArg Subtype.val hi) (congrArg Subtype.val hj)
        (congrArg Subtype.val hi') (congrArg Subtype.val hj'))
  have hl : ((rowsT.filter fun r => r.getD 1 0 == 4).map elt).length = 16 := by
    rw [List.length_map]
    exact rowsT_cntC4
  omega

theorem badLink : bad1c = bad1w.map (List.map (· + 6)) ∧ bad2c = bad2w.map (List.map (· + 6)) := by
  decide +kernel

theorem badLen : bad1c.length = bad1h.length ∧ bad2c.length = bad2h.length := by decide +kernel

theorem bad_letters : ∀ w ∈ bad1w ++ bad2w, ∀ l ∈ w, l < 6 := by decide +kernel

theorem bad_conj_aux {c h : List ℕ} (hc : ∀ l ∈ c, l < 6)
    (hp : ((c.map (· + 6)).all (fun x => decide (6 ≤ x ∧ x < 12)) &&
      comp 256 240 (comp 256 240 (evalW 256 240 GLO h) (GLO.getD 12 (one 256 240)))
        (evalW 256 240 GLO (invWO h)) == evalW 256 240 GLO (c.map (· + 6))) = true) :
    ∃ g : ↥ySub, g * Sp6Cover.tY * g⁻¹ = xw c := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have h1 := prepWO h
  have h2 := prepWO (invWO h)
  have e2 : permW LGO (invWO h) = (permW LGO h)⁻¹ := permW_invW LGO hIO h
  rw [e2] at h2
  have h3 := (h1.comp (by norm_num : 0 < 256) (prepLO 12)).comp (by norm_num : 0 < 256) h2
  rw [hp.2] at h3
  have h4 := prepWO (c.map (· + 6))
  rw [permW_shiftL c hc] at h4
  have := PkG.Rep.unique h3 h4
  rw [LGO_12] at this
  exact ⟨⟨permW LGO h, permW_mem LGO LGO_mem h⟩, Subtype.ext this⟩

theorem bad_sem1 {bw : List ℕ} (hb : bw ∈ bad1w) :
    (∃ g : ↥ySub, g * Sp6Cover.tY * g⁻¹ = xw bw) ∧ xw bw ≠ Sp6Cover.tY := by
  have hlt : ∀ l ∈ bw, l < 6 := bad_letters bw (List.mem_append_left _ hb)
  have hbc : bw.map (· + 6) ∈ bad1c := by rw [badLink.1]; exact List.mem_map_of_mem hb
  have hall := badChkO_true
  simp only [badChkO, List.all_append, Bool.and_eq_true] at hall
  obtain ⟨h, -, hp⟩ := exists_of_zip_all hall.1 badLen.1 hbc
  refine ⟨bad_conj_aux (h := h) hlt (by simpa using hp), ?_⟩
  · intro heq
    have hne := badNeChk_true
    simp only [badNeChk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hne
    have hv : evalW 64 48 base48 bw ∈ BadP1 := by rw [← BadP1_eq]; exact List.mem_map_of_mem hb
    apply hne.1 _ hv
    have h1 := resW bw
    have h2 : (xw bw : Equiv.Perm (Fin 240)) = Sp6Cover.tP := congrArg Subtype.val heq
    rw [xw_val] at h2
    rw [h2] at h1
    exact h1.digits_unique res_t

theorem bad_sem2 {bw : List ℕ} (hb : bw ∈ bad2w) :
    (∃ g : ↥ySub, g * Sp6Cover.tY * g⁻¹ = xw bw) ∧ xw bw ≠ Sp6Cover.tY ∧
      xw bw ≠ eE * Sp6Cover.tY * eE⁻¹ := by
  have hlt : ∀ l ∈ bw, l < 6 := bad_letters bw (List.mem_append_right _ hb)
  have hbc : bw.map (· + 6) ∈ bad2c := by rw [badLink.2]; exact List.mem_map_of_mem hb
  have hall := badChkO_true
  simp only [badChkO, List.all_append, Bool.and_eq_true] at hall
  obtain ⟨h, -, hp⟩ := exists_of_zip_all hall.2 badLen.2 hbc
  have hv : evalW 64 48 base48 bw ∈ BadP2 := by rw [← BadP2_eq]; exact List.mem_map_of_mem hb
  have hne := badNeChk_true
  simp only [badNeChk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hne
  refine ⟨bad_conj_aux (h := h) hlt (by simpa using hp), ?_, ?_⟩
  · intro heq
    apply (hne.2 _ hv).1
    have h1 := resW bw
    have h2 : (xw bw : Equiv.Perm (Fin 240)) = Sp6Cover.tP := congrArg Subtype.val heq
    rw [xw_val] at h2
    rw [h2] at h1
    exact h1.digits_unique res_t
  · intro heq
    apply (hne.2 _ hv).2
    have h1 := resW bw
    have h2 : (xw bw : Equiv.Perm (Fin 240)) = eP * Sp6Cover.tP * eP⁻¹ := congrArg Subtype.val heq
    rw [xw_val] at h2
    rw [h2] at h1
    have h3 : eP * Sp6Cover.tP * eP⁻¹ = permW CG (spW.getD 10 []) := by
      rw [permW_sp10, ← LGO_12, ← LGO_21, ← LGO_22, LGO_etz]
    rw [h3] at h1
    exact h1.digits_unique (res_sp 10)

theorem xw_nil : xw [] = 1 := Subtype.ext (by simp [xw_val, permW_nil])

theorem xw_append (a b : List ℕ) : xw (a ++ b) = xw a * xw b :=
  Subtype.ext (by simp [xw_val, permW_append])

theorem xw_sp0 : xw (spW.getD 0 []) = Sp6Cover.tY := Subtype.ext permW_sp0

theorem xw_sp1 : xw (spW.getD 1 []) = iY := Subtype.ext permW_sp1

theorem xw_sp3 : xw (spW.getD 3 []) = jY := Subtype.ext permW_sp3

theorem L0_mem_RY : ∀ e, xw (L0w.getD e []) ∈ RY := by
  intro e
  by_cases he : e < 8
  · have hmem : L0w.getD e [] ∈ L0w := by
      rw [List.getD_eq_getElem _ _ (by simpa [L0w] using he)]
      exact List.getElem_mem _
    generalize L0w.getD e [] = w at hmem ⊢
    simp only [L0w, List.mem_cons, List.not_mem_nil, or_false] at hmem
    have h0 : xw (spW.getD 0 []) ∈ RY := by rw [xw_sp0]; exact tY_mem
    have h1 : xw (spW.getD 1 []) ∈ RY := by rw [xw_sp1]; exact iY_mem
    have h3 : xw (spW.getD 3 []) ∈ RY := by rw [xw_sp3]; exact jY_mem
    rcases hmem with h | h | h | h | h | h | h | h <;> rw [h]
    · rw [xw_nil]; exact RY.one_mem
    · exact h0
    · exact h1
    · rw [xw_append]; exact RY.mul_mem h1 h0
    · exact h3
    · rw [xw_append]; exact RY.mul_mem h3 h0
    · rw [xw_append]; exact RY.mul_mem h1 h3
    · rw [xw_append, xw_append]; exact RY.mul_mem (RY.mul_mem h1 h3) h0
  · rw [getD_default' L0w e [] (by simp [L0w]; omega), xw_nil]
    exact RY.one_mem

theorem res_L0 (e : ℕ) : ResRep (L0P.getD e (one 64 48)) (xw (L0w.getD e [])) := by
  have h := resW (L0w.getD e [])
  have : L0P.getD e (one 64 48) = evalW 64 48 base48 (L0w.getD e []) := by
    rw [← L0P_eq]
    exact getD_map' (evalW 64 48 base48) L0w e []
  rw [this]
  exact h

theorem res_rep (k : ℕ) : ResRep (repP.getD k (one 64 48)) (xw (repW.getD k [])) := by
  have h := resW (repW.getD k [])
  have : repP.getD k (one 64 48) = evalW 64 48 base48 (repW.getD k []) := by
    rw [← repP_eq]
    exact getD_map' (evalW 64 48 base48) repW k []
  rw [this]
  exact h

theorem res_repI (k : ℕ) : ResRep (repIP.getD k (one 64 48)) (xw (repW.getD k []))⁻¹ := by
  have h := resW (invW6 (repW.getD k []))
  have hlt : ∀ l ∈ repW.getD k [], l < 6 := by
    have : (repW.all fun w => w.all fun l => decide (l < 6)) = true := by decide +kernel
    by_cases hk : k < repW.length
    · have hm : repW.getD k [] ∈ repW := by
        rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
      intro l hl
      simpa using List.all_eq_true.1 (List.all_eq_true.1 this _ hm) l hl
    · rw [getD_default' _ _ _ (by omega)]; simp
  rw [permW_inv6 _ hlt] at h
  have : repIP.getD k (one 64 48) = evalW 64 48 base48 (invW6 (repW.getD k [])) := by
    rw [← repIP_eq]
    exact getD_map' (fun w => evalW 64 48 base48 (invW6 w)) repW k []
  rw [this]
  exact h

theorem rowOk_letters {r : List ℕ} (hr : r ∈ rowsT) : ∀ l ∈ rowG r ++ rowW r, l < 6 := by
  have h := rows_sound.1 r hr
  simp only [rowOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem row_conj {r : List ℕ} (hr : r ∈ rowsT) :
    xw (rowG r) * elt r * (xw (rowG r))⁻¹ = xw (repW.getD (r.getD 2 0) []) := by
  have hlet := rowOk_letters hr
  have hG : ∀ l ∈ rowG r, l < 6 := fun l hl => hlet l (List.mem_append_left _ hl)
  have hok := rows_sound.1 r hr
  simp only [rowOk, Bool.and_eq_true, beq_iff_eq] at hok
  have h1 := resW (rowG r)
  have h2 := res_elt r
  have h3 := resW (invW6 (rowG r))
  rw [permW_inv6 _ hG] at h3
  have h4 := h1.comp (h2.comp h3)
  rw [hok.2] at h4
  have h5 := res_rep (r.getD 2 0)
  have hT1 : xw (rowG r) * elt r * (xw (rowG r))⁻¹ ∈ tT :=
    (tT).mul_mem ((tT).mul_mem (xw_mem _) (xw_mem _)) ((tT).inv_mem (xw_mem _))
  refine res_inj hT1 (xw_mem _) (p := repP.getD (r.getD 2 0) (one 64 48)) ?_ h5
  have : ((xw (rowG r) * elt r * (xw (rowG r))⁻¹ : ↥ySub) : Equiv.Perm (Fin 240)) =
      permW CG (rowG r) * ((elt r : ↥ySub) : Equiv.Perm (Fin 240)) * (permW CG (rowG r))⁻¹ := rfl
  rw [this, mul_assoc]
  exact h4

section NBound

variable {N : Subgroup ↥ySub} (hNT : N ≤ tT)
  (hNn : (N.subgroupOf (Sp0Core.TT Sp6Cover.tY)).Normal)

include hNT hNn in
theorem conj_mem_N {g x : ↥ySub} (hg : g ∈ tT) (hx : x ∈ N) : g * x * g⁻¹ ∈ N := by
  have := hNn.conj_mem ⟨x, mem_TT_iff.2 (hNT hx)⟩ (Subgroup.mem_subgroupOf.2 hx)
    ⟨g, mem_TT_iff.2 hg⟩
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

include hNT hNn in
theorem fold_elt (k : ℕ) {u : ↥ySub} (hu : u ∈ N) (hu' : u = xw (repW.getD k [])) :
    ∀ (L : List (List ℕ × Bool)), (∀ f ∈ L, ∀ l ∈ f.1, l < 6) → ∀ (acc : ℕ) (A : ↥ySub),
      A ∈ N → ResRep acc (A : Equiv.Perm (Fin 240)) →
      ∃ Z : ↥ySub, Z ∈ N ∧ ResRep (L.foldl (fun z f => comp 64 48 z
        (if f.2 then comp 64 48 (evalW 64 48 base48 f.1) (comp 64 48 (repP.getD k (one 64 48))
            (evalW 64 48 base48 (invW6 f.1)))
          else comp 64 48 (evalW 64 48 base48 f.1) (comp 64 48 (repIP.getD k (one 64 48))
            (evalW 64 48 base48 (invW6 f.1))))) acc) (Z : Equiv.Perm (Fin 240))
  | [], _, acc, A, hA, hR => ⟨A, hA, hR⟩
  | f :: L, hL, acc, A, hA, hR => by
    have hf : ∀ l ∈ f.1, l < 6 := hL f (List.mem_cons_self ..)
    have hres1 := resW f.1
    have hres2 := resW (invW6 f.1)
    rw [permW_inv6 _ hf] at hres2
    by_cases hs : f.2 = true
    · have hF : xw f.1 * u * (xw f.1)⁻¹ ∈ N := conj_mem_N hNT hNn (xw_mem _) hu
      have hRF := hres1.comp ((hu' ▸ res_rep k : ResRep (repP.getD k (one 64 48))
        (u : Equiv.Perm (Fin 240))).comp hres2)
      have := fold_elt k hu hu' L (fun f' hf' => hL f' (List.mem_cons_of_mem _ hf')) _
        (A * (xw f.1 * u * (xw f.1)⁻¹)) (N.mul_mem hA hF)
        (hR.comp (by
          have e : ((xw f.1 * u * (xw f.1)⁻¹ : ↥ySub) : Equiv.Perm (Fin 240)) =
              permW CG f.1 * (u * (permW CG f.1)⁻¹) := by
            show permW CG f.1 * (u : Equiv.Perm (Fin 240)) * (permW CG f.1)⁻¹ = _
            rw [mul_assoc]
          rw [e]
          exact hRF))
      simpa [hs] using this
    · have hs' : f.2 = false := by simpa using hs
      have hF : xw f.1 * u⁻¹ * (xw f.1)⁻¹ ∈ N := conj_mem_N hNT hNn (xw_mem _) (N.inv_mem hu)
      have hiu : ResRep (repIP.getD k (one 64 48)) ((u⁻¹ : ↥ySub) : Equiv.Perm (Fin 240)) := by
        have := res_repI k
        rw [← hu'] at this
        exact this
      have hRF := hres1.comp (hiu.comp hres2)
      have := fold_elt k hu hu' L (fun f' hf' => hL f' (List.mem_cons_of_mem _ hf')) _
        (A * (xw f.1 * u⁻¹ * (xw f.1)⁻¹)) (N.mul_mem hA hF)
        (hR.comp (by
          have e : ((xw f.1 * u⁻¹ * (xw f.1)⁻¹ : ↥ySub) : Equiv.Perm (Fin 240)) =
              permW CG f.1 * ((u⁻¹ : ↥ySub) * (permW CG f.1)⁻¹) := by
            show permW CG f.1 * ((u⁻¹ : ↥ySub) : Equiv.Perm (Fin 240)) * (permW CG f.1)⁻¹ = _
            rw [mul_assoc]
          rw [e]
          exact hRF))
      simpa [hs'] using this

include hNT hNn in
theorem witVal_elt (hNR : RY ≤ N) (k : ℕ) {u : ↥ySub} (hu : u ∈ N) (hu' : u = xw (repW.getD k []))
    (wd : List (List ℕ × Bool) × ℕ) (hW : ∀ f ∈ wd.1, ∀ l ∈ f.1, l < 6) :
    ∃ Z : ↥ySub, Z ∈ N ∧ ResRep (witVal k wd) (Z : Equiv.Perm (Fin 240)) := by
  obtain ⟨Z, hZ, hRZ⟩ := fold_elt hNT hNn k hu hu' wd.1 hW (one 64 48) 1 N.one_mem ResRep.one
  exact ⟨Z * xw (L0w.getD wd.2 []), N.mul_mem hZ (hNR (L0_mem_RY _)), hRZ.comp (res_L0 _)⟩

include hNT hNn in
theorem N_sub_rows (hNR : RY ≤ N) (Sf : List ℕ) (Wd : List (List (List ℕ × Bool) × ℕ))
    (Bw : List (List ℕ)) (BP : List ℕ) (hBP : Bw.map (evalW 64 48 base48) = BP)
    (hwit : ∀ k, k < 51 → Sf.getD k 0 = 1 ∨
      BP.contains (witVal k (Wd.getD k ([], 0))) = true)
    (hW : ∀ k < 51, ∀ f ∈ (Wd.getD k ([], 0)).1, ∀ l ∈ f.1, l < 6)
    (hbad : ∀ bw ∈ Bw, xw bw ∈ N → False) :
    ∀ x ∈ N, ∃ r ∈ rowsT, elt r = x ∧ Sf.getD (r.getD 2 0) 0 = 1 := by
  intro x hx
  obtain ⟨r, hr, hrx⟩ := exists_row (hNT hx)
  refine ⟨r, hr, hrx, ?_⟩
  by_contra hS
  have hk := cls_lt r hr
  have hwk := (hwit _ hk).resolve_left hS
  have hu : xw (repW.getD (r.getD 2 0) []) ∈ N := by
    rw [← row_conj hr, hrx]
    exact conj_mem_N hNT hNn (xw_mem _) hx
  obtain ⟨Z, hZ, hRZ⟩ := witVal_elt hNT hNn hNR (r.getD 2 0) hu rfl _ (hW _ hk)
  have hmem := List.mem_of_elem_eq_true hwk
  rw [← hBP] at hmem
  obtain ⟨bw, hbw, hbwv⟩ := List.mem_map.1 hmem
  have hres := resW bw
  rw [hbwv] at hres
  have hZeq : Z = xw bw := res_inj (hNT hZ) (xw_mem bw) hRZ hres
  exact hbad bw hbw (hZeq ▸ hZ)

end NBound

theorem tT_card : Nat.card ↥(Sp0Core.TT Sp6Cover.tY) = 4608 := by
  have : Sp0Core.TT Sp6Cover.tY = tT := by
    ext x; exact mem_TT_iff
  rw [this]
  exact card_centralizer_tY

theorem relIndex_big {N : Subgroup ↥ySub} (hNT : N ≤ Sp0Core.TT Sp6Cover.tY) {n b : ℕ}
    (hN : Nat.card ↥N ≤ n) (hb : b * n < 4608) : b < N.relIndex (Sp0Core.TT Sp6Cover.tY) := by
  have h := Subgroup.relIndex_mul_card (H := N) (K := Sp0Core.TT Sp6Cover.tY)
  rw [inf_of_le_left hNT, tT_card] at h
  by_contra hle
  push Not at hle
  have := Nat.mul_le_mul hle hN
  omega

theorem hidx1_Y : ∀ N : Subgroup ↥ySub, RY ≤ N → N ≤ Sp0Core.TT Sp6Cover.tY →
    (N.subgroupOf (Sp0Core.TT Sp6Cover.tY)).Normal →
    (∀ x : ↥ySub, x * Sp6Cover.tY * x⁻¹ ∈ N → x * Sp6Cover.tY * x⁻¹ = Sp6Cover.tY) →
    96 < N.relIndex (Sp0Core.TT Sp6Cover.tY) := by
  intro N hNR hNT hNn hinv
  have hNT' : N ≤ tT := fun x hx => mem_TT_iff.1 (hNT hx)
  have hsub := N_sub_rows hNT' hNn hNR S1f W1d bad1w BadP1 BadP1_eq (by
      intro k hk
      have h := List.all_eq_true.1 witChk1_true k (List.mem_range.2 hk)
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      exact h) W1d_letters (by
      intro bw hbw hbn
      obtain ⟨⟨h, hh⟩, hne⟩ := bad_sem1 hbw
      apply hne
      rw [← hh] at hbn ⊢
      exact hinv h hbn)
  refine relIndex_big hNT (n := 8) ?_ (by norm_num)
  have hl : ((rowsT.filter fun r => S1f.getD (r.getD 2 0) 0 == 1).map elt).length = 8 := by
    rw [List.length_map]
    exact rowsT_cnt1
  rw [← hl]
  refine card_le_of_subset_list N _ fun x hx => ?_
  obtain ⟨r, hr, hrx, hf⟩ := hsub x hx
  exact List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by simpa using hf⟩, hrx⟩

theorem hidx2_Y : ∀ N : Subgroup ↥ySub, RY ≤ N → N ≤ Sp0Core.TT Sp6Cover.tY →
    (N.subgroupOf (Sp0Core.TT Sp6Cover.tY)).Normal →
    (∀ x : ↥ySub, x * Sp6Cover.tY * x⁻¹ ∈ N → x * Sp6Cover.tY * x⁻¹ = Sp6Cover.tY ∨
      x * Sp6Cover.tY * x⁻¹ = eE * Sp6Cover.tY * eE⁻¹) →
    8 < N.relIndex (Sp0Core.TT Sp6Cover.tY) := by
  intro N hNR hNT hNn hinv
  have hNT' : N ≤ tT := fun x hx => mem_TT_iff.1 (hNT hx)
  have hsub := N_sub_rows hNT' hNn hNR S2f W2d bad2w BadP2 BadP2_eq (by
      intro k hk
      have h := List.all_eq_true.1 witChk2_true k (List.mem_range.2 hk)
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      exact h) W2d_letters (by
      intro bw hbw hbn
      obtain ⟨⟨h, hh⟩, hne, hne'⟩ := bad_sem2 hbw
      rw [← hh] at hbn
      rcases hinv h hbn with h1 | h1
      · exact hne (hh.symm.trans h1)
      · exact hne' (hh.symm.trans h1))
  refine relIndex_big hNT (n := 368) ?_ (by norm_num)
  have hl : ((rowsT.filter fun r => S2f.getD (r.getD 2 0) 0 == 1).map elt).length = 368 := by
    rw [List.length_map]
    exact rowsT_cnt2
  rw [← hl]
  refine card_le_of_subset_list N _ fun x hx => ?_
  obtain ⟨r, hr, hrx, hf⟩ := hsub x hx
  exact List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by simpa using hf⟩, hrx⟩


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
