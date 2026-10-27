module

public import Certificates.Data.Kernel.GMS78Ru
public import CFSG.Certificates.Kernel.GMS78RuGen
import CFSG.Certificates.Kernel.GMS78RuSoundS

public section

namespace CFSG.KC.GMS

open CFSG.GMS78Ru

theorem q0_sound (mt : Array (Fin 8)) (qt : List (Fin 8))
    (sd : List ((Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List (Fin 8 × Fin 8 × Fin 8)))
    {QT SD : Nat} (hM : bindMul mt = true) (hQ : bindQ qt QT = true) (hS : bindSD sd SD = true)
    (h : kQ0 QT SD = true) : Gen.q0Check mt qt sd = true := by
  obtain ⟨hsl, hsk⟩ := Snd.bindSD_spec hS
  obtain ⟨hql, hqk⟩ := Snd.bindFin8_iff hQ
  unfold kQ0 at h
  rw [Snd.allN_iff] at h
  unfold Gen.q0Check
  rw [List.all_eq_true]
  intro d hd
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hd
  have hR := h k (by lomega)
  have hrec := hsk k hk
  generalize sd[k] = d at hrec ⊢
  obtain ⟨t, X, Xi⟩ := d
  obtain ⟨h1, -, -, -, h5, h6⟩ := Snd.sdRec_spec hrec
  obtain ⟨f0, f1, -, -⟩ := Snd.fget_rec h1
  unfold q0Rec at hR
  rw [Snd.allN_iff] at hR
  rw [List.all_eq_true]
  intro m hm
  rw [List.mem_range] at hm
  have hm' := hR m hm
  simp only [Snd.nat_beq_eq, Snd.nat_shiftRight_eq, beq_iff_eq] at hm'
  rw [f0, f1, Snd.xiK_eq h5 h6] at hm'
  rw [beq_iff_eq, Fin.ext_iff, Snd.sqN_packV hM, hm', Gen.qC,
    List.getD_eq_getElem _ _ (by lomega), hqk m (by lomega)]

theorem c1_sound (mt : Array (Fin 8)) {WT : Nat → Nat} (hM : bindMul mt = true)
    (hP : pairsOK = true) (h : ∀ c, 1 ≤ c → c < 8 → kC1 c (WT c) = true) :
    Gen.c1Check mt = true := by
  unfold Gen.c1Check
  rw [List.all_eq_true]
  intro c _
  rw [Bool.or_eq_true]
  rcases Nat.eq_zero_or_pos c.val with hc0 | hc0
  · left; rw [Snd.fin_beq_val, hc0]; rfl
  right
  rw [List.all_eq_true]; intro e _
  rw [List.all_eq_true]; intro p _
  rw [List.all_eq_true]; intro q _
  rw [Bool.or_eq_true]
  cases hcan : canon p q
  · left; rfl
  right
  rw [Snd.canon_eq] at hcan
  obtain ⟨k, hk, hkp, hkq⟩ := Snd.pairsOK_spec hP p.isLt q.isLt hcan
  have hC := h c.val hc0 c.isLt
  unfold kC1 at hC
  rw [Snd.allN_iff] at hC
  have hC' := hC e.val e.isLt
  rw [Snd.allN_iff] at hC'
  have hpar := hC' k (by lomega)
  rw [hkp, hkq] at hpar
  generalize KLie.CT.fget (WT c.val) _ _ = WS at hpar
  unfold c1Par at hpar
  rw [Snd.notB_eq, Bool.not_eq_true', Snd.nat_beq_eq, beq_eq_false_iff_ne] at hpar
  have hsteps := Snd.foldK_steps
    (P := fun i s => c1Need c.val e.val (wK p.val q.val i) = true →
      c1Wit c.val e.val p.val q.val (wK p.val q.val i) (KLie.CT.fget WS (s - 1) 24) = true)
    (Snd.c1Step_zero _ _ _ _ _) (fun _ _ hs => Snd.c1Step_spec hs) 256 1 hpar
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Snd.exists_wPt hx
  have hpk := Snd.packV_wPt p q hi
  simp only [Bool.or_eq_true, Snd.fin_beq_val, beq_iff_eq, bne_iff_ne, ne_eq]
  by_cases hneed : c1Need c.val e.val (wK p.val q.val i) = true
  · right
    obtain ⟨s', hs'⟩ := hsteps i hi
    obtain ⟨w1, w2, w3, hind⟩ := Snd.c1Wit_spec (hs' hneed)
    have hj : ∀ j, KLie.CT.fget (KLie.CT.fget WS (s' - 1) 24) j 8 < 256 :=
      fun j => Snd.fget_lt _ _ 8
    obtain ⟨hq1, hq2, hq21⟩ := Snd.indep3K_spec hind
    rw [← hpk] at w1 w2 w3
    rw [← Snd.packV_wPt p q (hj 0)] at w1 hind hq1
    rw [← Snd.packV_wPt p q (hj 1)] at w2 hind hq2 hq21
    rw [← Snd.packV_wPt p q (hj 2)] at w3 hind
    rw [← Snd.packV_wPt p q (hj 0)] at hq21
    rw [← Snd.commN_packV hM] at w1 w2 w3
    rw [← Snd.sqN_packV hM, ← Snd.sqN_packV hM, ← Snd.sqN_packV hM, ← Snd.indep3_eq] at hind
    rw [← Snd.sqN_packV hM] at hq1 hq2 hq21
    rw [← Snd.sqN_packV hM] at hq21
    unfold Gen.spanAt
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    refine ⟨_, Snd.wPt_mem p q, Fin.ext w1, ⟨fun h0 => hq1 (by rw [h0]; rfl), ?_⟩⟩
    refine ⟨_, Snd.wPt_mem p q, Fin.ext w2, ⟨⟨fun h0 => hq2 (by rw [h0]; rfl),
      fun h0 => hq21 (by rw [h0])⟩, ?_⟩⟩
    exact ⟨_, Snd.wPt_mem p q, Fin.ext w3, hind⟩
  · left
    rw [Snd.c1Need_iff, ← hpk, Snd.fget_packV0, Snd.fget_packV1, ← Snd.sqN_packV hM] at hneed
    by_cases h1 : (Snd.wPt p q i).1.val = 0
    · exact Or.inl (Or.inl h1)
    by_cases h2 : (Snd.wPt p q i).2.1.val = 0
    · exact Or.inl (Or.inr h2)
    exact Or.inr (fun h3 => hneed ⟨h1, h2, by rw [h3]; rfl⟩)

theorem c2_sound (mt : Array (Fin 8)) (sl : List (Fin 8 × Fin 8 × Fin 8 × Fin 8))
    (hM : bindMul mt = true) (hP : pairsOK = true) (hS : bindSpec sl = true)
    (h : ∀ c, 1 ≤ c → c < 8 → kC2 c = true) : Gen.c2Check mt sl = true := by
  unfold Gen.c2Check
  rw [List.all_eq_true]
  intro c _
  rw [Bool.or_eq_true]
  rcases Nat.eq_zero_or_pos c.val with hc0 | hc0
  · left; rw [Snd.fin_beq_val, hc0]; rfl
  right
  rw [List.all_eq_true]; intro e _
  rw [List.all_eq_true]; intro p _
  rw [List.all_eq_true]; intro q _
  rw [Bool.or_eq_true, Bool.or_eq_true]
  cases hcan : canon p q
  · left; left; rfl
  rw [Snd.canon_eq] at hcan
  obtain ⟨k, hk, hkp, hkq⟩ := Snd.pairsOK_spec hP p.isLt q.isLt hcan
  have hC := h c.val hc0 c.isLt
  unfold kC2 at hC
  rw [Snd.allN_iff] at hC
  have hC' := hC e.val e.isLt
  rw [Snd.allN_iff] at hC'
  have hpar := hC' k (by lomega)
  rw [hkp, hkq] at hpar
  unfold c2Par at hpar
  rw [Snd.orB_eq, Bool.or_eq_true] at hpar
  rcases hpar with hsp | hin
  · left; right
    exact Snd.specK_spec (t := (c, e, p, q)) hS hsp
  right
  rw [List.all_eq_true]
  intro x hx
  rw [List.all_eq_true]
  intro y hy
  rw [List.mem_filter] at hx hy
  obtain ⟨hxW, hxz⟩ := hx
  obtain ⟨hyW, hyz⟩ := hy
  obtain ⟨i, hi, rfl⟩ := Snd.exists_wPt hxW
  obtain ⟨j, hj, rfl⟩ := Snd.exists_wPt hyW
  have hpi := Snd.packV_wPt p q hi
  have hpj := Snd.packV_wPt p q hj
  have hzi : (zMask c.val e.val p.val q.val).testBit i = true := by
    rw [Snd.zMask_testBit, ← hpi, Snd.allNZK_packV, ← Snd.sqN_packV hM]
    simp only [Bool.and_eq_true, beq_iff_eq] at hxz
    exact ⟨hi, hxz.1, by rw [hxz.2]; rfl⟩
  have hzj : (zMask c.val e.val p.val q.val).testBit j = true := by
    rw [Snd.zMask_testBit, ← hpj, Snd.allNZK_packV, ← Snd.sqN_packV hM]
    simp only [Bool.and_eq_true, beq_iff_eq] at hyz
    exact ⟨hj, hyz.1, by rw [hyz.2]; rfl⟩
  have hpair := Snd.c2Pair_spec (Snd.c2Inner_spec hin i hi j hj hzi hzj)
  rw [← hpi, ← hpj] at hpair
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true']
  rcases hpair with h1 | h1 | h1 | ⟨l, hl, hl'⟩
  · exact Or.inl (Or.inl (Or.inl (Snd.packV_inj h1)))
  · refine Or.inl (Or.inl (Or.inr fun h0 => h1 ?_))
    rw [← Snd.commN_packV hM, h0]; rfl
  · refine Or.inl (Or.inr ?_)
    rw [← Snd.packV_addV, Snd.allNZK_packV] at h1
    exact h1
  · right
    obtain ⟨z, hz, hzl⟩ := Snd.lineK_mem p q hl
    rw [← hzl, ← Snd.commN_packV hM, ← Snd.commN_packV hM] at hl'
    rw [List.all_eq_false]
    refine ⟨z, hz, ?_⟩
    simp only [beq_iff_eq]
    intro e'
    apply hl'
    rw [Bool.eq_iff_iff] at e'
    simp only [beq_iff_eq] at e'
    apply propext
    rw [Fin.ext_iff, Fin.ext_iff] at e'
    exact e'

theorem c3_sound (mt : Array (Fin 8)) (hM : bindMul mt = true) (hMul : mulOK = true)
    (hP : pairsOK = true) (h : ∀ c < 8, ∀ k < 7, c3Pair c k = true) : Gen.c3Check mt = true :=
  Snd.c3Check_of hM hMul hP h

theorem s_sound (mt : Array (Fin 8))
    (sd : List ((Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List (Fin 8 × Fin 8 × Fin 8)))
    (sl : List (Fin 8 × Fin 8 × Fin 8 × Fin 8)) (il gl : List CFSG.GMS78RuSim.Lin8)
    {SD INV INVL : Nat} (hM : bindMul mt = true)
    (hMul : mulOK = true) (hS : bindSD sd SD = true) (hSp : bindSpec sl = true)
    (h0 : kS0 SD INV = true) (h1 : ∀ d < 7, kS1 INV (CFSG.KLie.CT.fget SD d 160) = true)
    (h2a : kS2a INV INVL = true) (h2b : kS2b INVL = true) (hil : Gen.invListOK il = true)
    (hgl : Gen.glOK gl = true) :
    Gen.s0Check sd sl = true ∧ Gen.s1Check mt sd = true ∧
      Gen.s2aCheckG il = true ∧ Gen.s2bCheckG il gl = true :=
  ⟨Snd.s0Check_of hS hSp h0, Snd.s1Check_of hM hMul hS h0 h1, Snd.s2aCheck_of h0 h2a hil,
    Snd.s2bCheck_of h2b hil hgl⟩

end CFSG.KC.GMS

end
