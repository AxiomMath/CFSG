module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5OvrChk0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5OvrChk1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5OvrChk2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5OvrChk3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5OvrChk4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5OvrChk5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtSem
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf3Sp0Core

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open CFSG.Monster.B.Co2 PkG CovK CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData

set_option linter.unusedSectionVars false


@[expose] noncomputable def eE : ↥ySub := ⟨eP, LGO_mem 23⟩

@[expose] def OmS : Set (Equiv.Perm (Fin 240)) := {s | ∃ p ∈ OM, PkG.Rep 256 240 p s}

theorem LGO_d {l : ℕ} (hl : l < 3) : LGO l = permOfArr 240 yS[l]! := by
  rw [LGO_base (by omega)]
  have : GO l = GBase l := by simp [GO, show l < 6 by omega]
  rw [this]
  simp [GBase, hl]

theorem LGO_dinv {l : ℕ} (hl : l < 3) : LGO (l + 3) = (permOfArr 240 yS[l]!)⁻¹ := by
  rw [LGO_base (by omega)]
  have : GO (l + 3) = GBase (l + 3) := by simp [GO, show l + 3 < 6 by omega]
  rw [this]
  have h1 : ¬ (l + 3 < 3) := by omega
  have h2 : l + 3 < 6 := by omega
  simp [GBase, h1, h2]

theorem om_closed_mem {p : ℕ} (hp : p ∈ OM) {l : ℕ} (hl : l < 6) :
    OM.contains (comp 256 240 (comp 256 240 (GLO.getD l (one 256 240)) p)
      (GLO.getD (invO l) (one 256 240))) = true := by
  have key : ∀ ps : List ℕ, omClosedSlice ps = true → p ∈ ps →
      OM.contains (comp 256 240 (comp 256 240 (GLO.getD l (one 256 240)) p)
        (GLO.getD (invO l) (one 256 240))) = true := fun ps h hpp =>
    List.all_eq_true.1 (List.all_eq_true.1 h p hpp) l (List.mem_range.2 hl)
  simp only [OM, List.mem_cons, List.mem_append, or_assoc] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp
  · exact key _ clos_head_true (by rw [hp]; exact List.mem_cons_self ..)
  · exact key _ clos_head_true (by rw [hp]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact key _ clos0_true hp
  · exact key _ clos1_true hp
  · exact key _ clos2_true hp
  · exact key _ clos3_true hp
  · exact key _ clos4_true hp
  · exact key _ clos5_true hp

theorem om_conj {l : ℕ} (hl : l < 6) {s : Equiv.Perm (Fin 240)} (hs : s ∈ OmS) :
    LGO l * s * (LGO l)⁻¹ ∈ OmS := by
  obtain ⟨p, hp, hps⟩ := hs
  refine ⟨_, List.mem_of_elem_eq_true (om_closed_mem hp hl), ?_⟩
  have := ((prepLO l).comp (by norm_num : 0 < 256) hps).comp (by norm_num : 0 < 256) (prepLO (invO l))
  rwa [hIO] at this

theorem om_stab {h : Equiv.Perm (Fin 240)} (hh : h ∈ ySub) :
    ∀ s ∈ OmS, h * s * h⁻¹ ∈ OmS ∧ h⁻¹ * s * h ∈ OmS := by
  rw [ySub_eq_closure] at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    intro s hs
    have h1 := om_conj (l := i) (by omega) hs
    have h2 := om_conj (l := i + 3) (by omega) hs
    rw [LGO_d hi] at h1
    rw [LGO_dinv hi, inv_inv] at h2
    exact ⟨h1, h2⟩
  | one => intro s hs; simpa using hs
  | mul x y _ _ ihx ihy =>
    intro s hs
    have e1 : x * y * s * (x * y)⁻¹ = x * (y * s * y⁻¹) * x⁻¹ := by group
    have e2 : (x * y)⁻¹ * s * (x * y) = y⁻¹ * (x⁻¹ * s * x) * y := by group
    refine ⟨?_, ?_⟩
    · rw [e1]; exact (ihx _ (ihy s hs).1).1
    · rw [e2]; exact (ihy _ (ihx s hs).2).2
  | inv x _ ih =>
    intro s hs
    exact ⟨by simpa using (ih s hs).2, by simpa using (ih s hs).1⟩

theorem tP_omS : Sp6Cover.tP ∈ OmS := by
  refine ⟨GLO.getD 12 (one 256 240), by unfold OM; exact List.mem_cons_self .., ?_⟩
  rw [← LGO_12]
  exact prepLO 12

theorem invO_m : ∀ i, i < 5 → invO (25 + i) = 30 + i := by decide +kernel

theorem MT_get {i : ℕ} (hi : i < 5) : MT.getD i (one 256 240) =
    comp 256 240 (comp 256 240 (GLO.getD (25 + i) (one 256 240)) (GLO.getD 12 (one 256 240)))
      (GLO.getD (30 + i) (one 256 240)) := by
  rw [← MT_eq]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem rec_sem {ss : List ℕ} {rs : List (List ℕ)} (h : recsChk ss rs = true) {p : ℕ} (hp : p ∈ ss)
    {s : Equiv.Perm (Fin 240)} (hps : PkG.Rep 256 240 p s) :
    ∃ (w : List ℕ) (i : ℕ), (∀ l ∈ w, l < 6) ∧ i < 5 ∧
      s = permW CG w * (LGO (25 + i) * Sp6Cover.tP * (LGO (25 + i))⁻¹) * (permW CG w)⁻¹ := by
  simp only [recsChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hp
  have hk' : k < rs.length := hlen ▸ hk
  have hmem : (ss[k], rs[k]) ∈ ss.zip rs := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by simp [hk, hk'], by simp⟩
  have hok := List.all_eq_true.1 hall _ hmem
  simp only [recOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hi, hlt⟩, hcomp⟩ := hok
  set r := rs[k] with hr
  set w := r.tail with hw
  set i := r.headD 0 with hi'
  have hlt' : ∀ l ∈ w, l < 6 := fun l hl => by simpa using hlt l hl
  have hc := prepWO (w.map (· + 6))
  rw [permW_shiftL w hlt'] at hc
  have hMT : PkG.Rep 256 240 (MT.getD i (one 256 240)) (LGO (25 + i) * Sp6Cover.tP * (LGO (25 + i))⁻¹) := by
    rw [MT_get hi]
    have a := ((prepLO (25 + i)).comp (by norm_num : 0 < 256) (prepLO 12)).comp
      (by norm_num : 0 < 256) (prepLO (30 + i))
    have e : LGO (30 + i) = (LGO (25 + i))⁻¹ := by
      rw [← invO_m i hi]; exact hIO _
    rw [e, LGO_12] at a
    exact a
  have hci := prepWO (invWO (w.map (· + 6)))
  have e2 : permW LGO (invWO (w.map (· + 6))) = (permW LGO (w.map (· + 6)))⁻¹ := permW_invW LGO hIO _
  rw [e2, permW_shiftL w hlt'] at hci
  have hprod := (hc.comp (by norm_num : 0 < 256) hMT).comp (by norm_num : 0 < 256) hci
  rw [hcomp] at hprod
  exact ⟨w, i, hlt', hi, PkG.Rep.unique hps hprod⟩

theorem omS_cases {s : Equiv.Perm (Fin 240)} (hs : s ∈ OmS) :
    s = Sp6Cover.tP ∨ s = eP * Sp6Cover.tP * eP⁻¹ ∨
      ∃ (w : List ℕ) (i : ℕ), (∀ l ∈ w, l < 6) ∧ i < 5 ∧
        s = permW CG w * (LGO (25 + i) * Sp6Cover.tP * (LGO (25 + i))⁻¹) * (permW CG w)⁻¹ := by
  obtain ⟨p, hp, hps⟩ := hs
  simp only [OM, List.mem_cons, List.mem_append, or_assoc] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp
  · left
    rw [hp] at hps
    exact PkG.Rep.unique hps (by rw [← LGO_12]; exact prepLO 12)
  · right; left
    rw [hp] at hps
    have := PkG.Rep.unique hps (prepLO 22)
    rw [this, ← LGO_etz, LGO_12]
  · right; right; exact rec_sem recs0_true hp hps
  · right; right; exact rec_sem recs1_true hp hps
  · right; right; exact rec_sem recs2_true hp hps
  · right; right; exact rec_sem recs3_true hp hps
  · right; right; exact rec_sem recs4_true hp hps
  · right; right; exact rec_sem recs5_true hp hps

@[expose] noncomputable def hO (w : List ℕ) : ↥ySub := ⟨permW LGO w, permW_mem LGO LGO_mem w⟩

theorem hO_cons (l : ℕ) (w : List ℕ) : hO (l :: w) = hO [l] * hO w :=
  Subtype.ext (by
    show permW LGO (l :: w) = permW LGO [l] * permW LGO w
    rw [permW_cons, permW_single])

theorem hO_mem_of_letters {K : Subgroup ↥ySub} {w : List ℕ} (h : ∀ l ∈ w, hO [l] ∈ K) :
    hO w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [hO_cons]
    exact K.mul_mem (h l (List.mem_cons_self ..))
      (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

theorem genWd_sem {i k : ℕ} (hi : i < 5) (hk : k < 3) :
    (∀ l ∈ genWd.getD (3 * i + k) [], (6 ≤ l ∧ l < 12) ∨ l = 25 + i ∨ l = 30 + i) ∧
      permW LGO (genWd.getD (3 * i + k) []) = LGO k := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 genChkO_true i (List.mem_range.2 hi)) k
    (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  refine ⟨fun l hl => or_assoc.1 (h.1 l hl), ?_⟩
  have h1 := prepWO (genWd.getD (3 * i + k) [])
  rw [h.2] at h1
  exact PkG.Rep.unique h1 (prepLO k)

theorem dY_eq_hO {i k : ℕ} (hi : i < 5) (hk : k < 3) : dY k hk = hO (genWd.getD (3 * i + k) []) := by
  apply Subtype.ext
  show dP k = permW LGO _
  rw [(genWd_sem hi hk).2, LGO_d hk]

theorem mem_TT_iff {x : ↥ySub} : x ∈ Sp0Core.TT Sp6Cover.tY ↔ x ∈ tT := by
  simp [Sp0Core.TT, tT]

theorem hO_single_mem_TT {l : ℕ} (hl : 6 ≤ l ∧ l < 12) :
    hO [l] ∈ Sp0Core.TT Sp6Cover.tY := by
  rw [Sp0Core.TT, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine ⟨Subgroup.mem_top _, Subtype.ext ?_⟩
  show permW LGO [l] * Sp6Cover.tP = Sp6Cover.tP * permW LGO [l]
  rw [permW_single, LGO_base hl.2]
  have : GO l = CG (l - 6) := by
    have : ¬ (l < 6) := by omega
    simp [GO, this]
  rw [this]
  exact CG_comm_t _

theorem hover_Y : ∀ S : Subgroup ↥ySub, Sp0Core.TT Sp6Cover.tY ≤ S → S ≠ ⊤ →
    ∀ g ∈ S, g ∈ Sp0Core.TT Sp6Cover.tY ∨ ∃ s ∈ Sp0Core.TT Sp6Cover.tY, g = eE * s := by
  intro S hTS hSne g hg
  have hs : (g : Equiv.Perm (Fin 240)) * Sp6Cover.tP * (g : Equiv.Perm (Fin 240))⁻¹ ∈ OmS :=
    (om_stab g.2 _ tP_omS).1
  have hTT : ∀ x : ↥ySub, x ∈ Sp0Core.TT Sp6Cover.tY ↔ x * Sp6Cover.tY = Sp6Cover.tY * x := by
    intro x
    simp [Sp0Core.TT, Subgroup.mem_centralizer_singleton_iff]
  rcases omS_cases hs with h | h | ⟨w, i, hw, hi, h⟩
  · left
    rw [hTT]
    apply Subtype.ext
    show (g : Equiv.Perm (Fin 240)) * Sp6Cover.tP = Sp6Cover.tP * g
    calc (g : Equiv.Perm (Fin 240)) * Sp6Cover.tP = (g * Sp6Cover.tP * (g : Equiv.Perm (Fin 240))⁻¹) * g := by
          group
      _ = Sp6Cover.tP * g := by rw [h]
  · right
    refine ⟨eE⁻¹ * g, ?_, by group⟩
    rw [hTT]
    apply Subtype.ext
    show ((eP)⁻¹ * (g : Equiv.Perm (Fin 240))) * Sp6Cover.tP = Sp6Cover.tP * ((eP)⁻¹ * g)
    calc (eP)⁻¹ * (g : Equiv.Perm (Fin 240)) * Sp6Cover.tP =
        (eP)⁻¹ * (g * Sp6Cover.tP * (g : Equiv.Perm (Fin 240))⁻¹) * g := by group
      _ = Sp6Cover.tP * ((eP)⁻¹ * g) := by rw [h]; group
  · exfalso
    apply hSne
    set c : ↥ySub := xw w with hc
    set m : ↥ySub := ⟨LGO (25 + i), LGO_mem _⟩ with hm
    have hcT : c ∈ Sp0Core.TT Sp6Cover.tY := mem_TT_iff.2 (xw_mem w)
    have hu : (c * m)⁻¹ * g ∈ Sp0Core.TT Sp6Cover.tY := by
      rw [hTT]
      apply Subtype.ext
      show ((permW CG w * LGO (25 + i))⁻¹ * (g : Equiv.Perm (Fin 240))) * Sp6Cover.tP =
        Sp6Cover.tP * ((permW CG w * LGO (25 + i))⁻¹ * g)
      have h' : (g : Equiv.Perm (Fin 240)) * Sp6Cover.tP * (g : Equiv.Perm (Fin 240))⁻¹ =
          (permW CG w * LGO (25 + i)) * Sp6Cover.tP * (permW CG w * LGO (25 + i))⁻¹ := by
        rw [h]; group
      calc (permW CG w * LGO (25 + i))⁻¹ * (g : Equiv.Perm (Fin 240)) * Sp6Cover.tP =
          (permW CG w * LGO (25 + i))⁻¹ *
            ((g : Equiv.Perm (Fin 240)) * Sp6Cover.tP * (g : Equiv.Perm (Fin 240))⁻¹) * g := by group
        _ = Sp6Cover.tP * ((permW CG w * LGO (25 + i))⁻¹ * g) := by rw [h']; group
    have hmS : m ∈ S := by
      have e : m = c⁻¹ * g * ((c * m)⁻¹ * g)⁻¹ := by group
      rw [e]
      exact S.mul_mem (S.mul_mem (S.inv_mem (hTS hcT)) hg) (S.inv_mem (hTS hu))
    apply eq_top_of_dY
    intro k hk
    rw [dY_eq_hO hi hk]
    apply hO_mem_of_letters
    intro l hl
    rcases (genWd_sem hi hk).1 l hl with hl' | rfl | rfl
    · exact hTS (hO_single_mem_TT hl')
    · have : hO [25 + i] = m := Subtype.ext (by show permW LGO [25 + i] = _; rw [permW_single])
      rw [this]; exact hmS
    · have e : hO [30 + i] = m⁻¹ := by
        apply Subtype.ext
        show permW LGO [30 + i] = (LGO (25 + i))⁻¹
        rw [permW_single, ← invO_m i hi]
        exact hIO _
      rw [e]; exact S.inv_mem hmS

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
