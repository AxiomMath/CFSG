module

public import CFSG.Certificates.Kernel.J4Q.RepVOrbB
import CFSG.Certificates.Kernel.J4Q.VOrbBFS
import CFSG.Certificates.Kernel.J4Q.VOrbTree

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.Native CFSG.KC.LQT.Syl

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private theorem getN_eq' (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], i => by
    rw [List.getD_nil]
    rfl
  | _ :: _, 0 => rfl
  | m :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact getN_eq' d l i

theorem vorbit_pts_iff (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {mats : Array (Array V2)}
    {Ms : List Nat} (_hs : mats.size = Ms.length)
    (_hM : ∀ g, WfA (mats[g]?.getD (idRows ())) ∧ encR (mats[g]?.getD (idRows ())) = getN one Ms g)
    {w : V2} (_hw : w.wf = true) {cap bits : Nat} (_hcap : cap < 2 ^ bits)
    (_h32 : 4 * 2 ^ bits < 2 ^ 32)
    {Rs : List (List Nat)} (_hR : Rs = Ms.map (rowsOfJ rm)) {B : Nat} (_hB : Ms.length * B ≤ 131072)
    (_hB1 : 0 < B)
    {chs : List (List Nat)} {p0s : List Nat} {SPch : List (List Nat)}
    (_hlen : chs.flatten.length + 1 = cap)
    (_hchs : ∀ i, i + 1 < chs.length → (chs.getD i []).length = B)
    (_hlast : ∀ ch ∈ chs, ch.length ≤ B)
    (_htree : ∀ i < chs.length, vtB rm (rep 1 128 B) Ms (vptsK rm (v2N w) chs.flatten)
      (chs.getD i []) (p0s.getD i 0) (1 + B * i) = true)
    (_hsinc : sincK SPch.flatten 0 = true) (_hsl : SPch.flatten.length = cap)
    (_hspl : ∀ sc ∈ SPch, sc.length ≤ 131072)
    (_hin : ∀ pc ∈ pchK rm (v2N w) chs, inSK pc SPch.flatten = true)
    (_hsp : ∀ sc ∈ SPch, spInK sc (pchK rm (v2N w) chs) = true)
    (_hcl : ∀ pc ∈ pchK rm (v2N w) chs, clB rm (rep 1 128 B) Ms pc SPch.flatten = true) :
    ∀ v, v ∈ (vorbit (mats.map frTable) w cap bits).pts ↔
      v.wf = true ∧ v2N v ∈ vptsK rm (v2N w) chs.flatten := by
  have hok := vorbit_soundB _hK _hs _hM _hw _hcap _h32 _hR _hB _hB1 _hlen _hchs _hlast _htree
    _hsinc _hsl _hspl _hin _hsp _hcl
  have hrm : rm = 2 ^ 112 - 1 := (consts_c _hK).2
  set ts := mats.map frTable with hts
  set A := vptsK rm (v2N w) chs.flatten with hA
  have hAP : (pchK rm (v2N w) chs).flatten = A := by
    simp only [pchK, List.flatten_cons, List.singleton_append, hA, vptsK, List.map_flatten]
  have hRl : Rs.length = Ms.length := by rw [_hR, List.length_map]
  have hact : ∀ v : V2, v.wf = true → ∀ g < ts.size,
      v2N (frApply ts[g]! v) = vecLJ (v2N v) (Rs.getD g []) := by
    intro v hv g hg
    have hgm : g < mats.size := by rw [hts, Array.size_map] at hg; exact hg
    have hget : ts[g]! = frTable mats[g] := by
      rw [getElem!_pos ts g hg]
      simp only [hts, Array.getElem_map]
    have hMg := _hM g
    rw [Array.getElem?_eq_getElem hgm, Option.getD_some] at hMg
    rw [hget]
    have hMs : Ms.getD g one = Ms[g]'(by omega) := List.getD_eq_getElem _ _ (by omega)
    have hRs : Rs.getD g [] = rowsOfJ rm (Ms[g]'(by omega)) := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp only [_hR, List.getElem_map]
    rw [v2N_frApply _hK hMg.1 hv, hMg.2, getN_eq', hMs, hRs, vecLJ_rowsOfJ]
  have hpts := VOrbTree.checked_points_spec (Pch := pchK rm (v2N w) chs) (cap := cap)
    (by rw [hAP, hA, vptsK, List.length_cons, List.length_map, _hlen]) _hsl _hsinc _hsp
  rw [hAP] at hpts
  have hAl : A.length = cap := by
    rw [hA, vptsK, List.length_cons, List.length_map, _hlen]
  have hmem := VOrbTree.checked_membership _hin _hsp
  rw [hAP] at hmem
  have hclA : ∀ x ∈ A, ∀ g < Ms.length, vecLJ x (Rs.getD g []) ∈ A := by
    intro x hx g hg
    rw [← hAP] at hx
    obtain ⟨pc, hpc, hx⟩ := List.mem_flatten.1 hx
    have hlen : pc.length ≤ B := by
      simp only [pchK, List.mem_cons, List.mem_map] at hpc
      rcases hpc with rfl | ⟨ch, hch, rfl⟩
      · rw [List.length_singleton]
        exact _hB1
      · rw [List.length_map]
        exact _hlast ch hch
    have hRs : Rs.getD g [] = rowsOfJ rm (Ms[g]'hg) := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp only [_hR, List.getElem_map]
    rw [hRs, vecLJ_rowsOfJ]
    exact (hmem _).2 (clB_sound hrm hlen (_hcl pc hpc) x hx _ (List.getElem_mem _))
  have htsz : ts.size = Ms.length := by rw [hts, Array.size_map, _hs]
  generalize vorbit ts w cap bits = O at hok ⊢
  unfold vorbOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨hsz, -⟩, -⟩, -⟩, hroot⟩, hat⟩ := hok
  have hroot' : O.pts[0]! = w := V2.beq_iff.1 hroot
  have hat' : ∀ q < cap, (O.pts[q]!.wf = true ∧ vfind O.pts O.slots O.bits O.pts[q]! = q + 1) ∧
      (∀ g < ts.size, frApply ts[g]! O.pts[q]! ∈ O.pts) ∧
      (q = 0 ∨ O.par[q]! < q ∧ O.lab[q]! < ts.size ∧
        frApply ts[O.lab[q]!]! O.pts[O.par[q]!]! = O.pts[q]!) := by
    intro q hq
    have h := hat q hq
    unfold vorbAt at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨h1, fun g hg => ?_, ?_⟩
    · obtain ⟨⟨he0, hes⟩, heq⟩ := h2 g hg
      rw [← V2.beq_iff.1 heq]
      exact VOrbBFS.get!_mem (by omega)
    · rcases h3 with h3 | ⟨⟨h4, h5⟩, h6⟩
      · exact Or.inl h3
      · exact Or.inr ⟨h4, h5, V2.beq_iff.1 h6⟩
  have hfwd : ∀ q < cap, v2N O.pts[q]! ∈ A := by
    intro q
    induction q using Nat.strong_induction_on with
    | _ q ih =>
      intro hq
      rcases (hat' q hq).2.2 with h0 | ⟨hpq, hlab, heq⟩
      · subst h0
        rw [hroot', hA, vptsK]
        exact List.mem_cons_self
      · rw [← heq, hact _ (hat' _ (by omega)).1.1 _ hlab]
        exact hclA _ (ih _ hpq (by omega)) _ (by omega)
  have hnd : (O.pts.toList.map v2N).Nodup := by
    refine List.Nodup.map (fun a b h => VOrbBFS.v2N_inj h) ?_
    rw [List.nodup_iff_injective_get]
    intro i j hij
    have hi : i.1 < O.pts.size := by simp
    have hj : j.1 < O.pts.size := by simp
    apply Fin.ext
    have e : O.pts[i.1]! = O.pts[j.1]! := by
      rw [getElem!_pos O.pts i.1 hi, getElem!_pos O.pts j.1 hj]
      simpa [List.get_eq_getElem, Array.getElem_toList] using hij
    have h1 := (hat' i.1 (by omega)).1.2
    have h2 := (hat' j.1 (by omega)).1.2
    rw [e, h2] at h1
    omega
  have hsub : O.pts.toList.map v2N ⊆ A := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := VOrbBFS.exists_get! (Array.mem_toList_iff.1 hu)
    exact hfwd i (by omega)
  have hperm := (List.subperm_of_subset hnd hsub).perm_of_length_le
    (by rw [List.length_map, @Array.length_toList _ O.pts, hsz, hAl])
  intro v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := VOrbBFS.exists_get! hv
    exact ⟨(hat' i (by omega)).1.1, hfwd i (by omega)⟩
  · rintro ⟨-, hv⟩
    obtain ⟨u, hu, huv⟩ := List.mem_map.1 (hperm.symm.subset hv)
    rw [← VOrbBFS.v2N_inj huv]
    exact Array.mem_toList_iff.1 hu

end CFSG.KC.J4Q

end
