module

public import CFSG.Certificates.Kernel.SporLatDc2Base
public import CFSG.Certificates.Kernel.SporLatDc2Count

public section

namespace CFSG.KC.SLD2

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F
open CFSG.KC.SLDc (sortedLt cntB anyB headL lookC cntB_eq_length_filter)
open MulAction

namespace Dc2SoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] (P : Dc2SoundCtx Γ n)

@[expose] def xr (r : Rec1) : PtL n := P.elt r.u • P.Λl

@[expose] def meets (y : PtL n) (j : ℕ) : Prop :=
  ∃ q ∈ y.val, inO (P.D.bo.getD j default) q = true

theorem rec1_facts {r : Rec1} (hr : rec1OK P.C P.D r = true) : (∀ l ∈ r.u, l < P.C.nl) ∧
    r.key = r.mode :: headL (r.cl.ord.map (lookC r.cl.B r.cl.C)) ∧
    (r.mode = 0 → modeEOK P.C P.D (P.xr r).val r.m r.cl = true) ∧
    (∀ i, r.mode = i + 1 →
      modeBOK P.C P.D i (P.D.bo.getD i default) (P.xr r).val r.m r.cl = true) := by
  unfold rec1OK at hr
  simp only [Bool.and_eq_true, isW_iff, beq_iff_eq] at hr
  obtain ⟨⟨hu, hk⟩, hm⟩ := hr
  have hx : (P.xr r).val = lw P.C r.u P.C.Λ := P.smul_lw hu P.Λl
  refine ⟨hu, hk, fun h0 => ?_, fun i hi => ?_⟩
  · rw [hx]
    rw [h0] at hm
    exact hm
  · rw [hx]
    rw [hi] at hm
    exact hm

theorem missOK_spec {x : PtL n} {i : ℕ} (h : missOK P.D x.val i = true) :
    ∀ j < i, ¬ P.meets x j := by
  rintro j hj ⟨q, hq, hi⟩
  unfold missOK at h
  have e := List.all_eq_true.1 h j (List.mem_range.2 hj)
  rw [Nat.beq_eq, cntB_eq_zero_iff] at e
  rw [e q hq] at hi
  exact Bool.false_ne_true hi

theorem modeE_facts {x : PtL n} {m : ℕ} {Cl : Clos} (h : modeEOK P.C P.D x.val m Cl = true) :
    (∀ j < P.D.bo.length, ¬ P.meets x j) ∧
    clOK P.C P.D (sLet P.C) x.val (fun _ => true) Cl = true ∧ m = Cl.C.flatten.length := by
  unfold modeEOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨P.missOK_spec h.1.1, h.1.2, h.2⟩

theorem modeB_facts {i : ℕ} {x : PtL n} {m : ℕ} {Cl : Clos}
    (h : modeBOK P.C P.D i (P.D.bo.getD i default) x.val m Cl = true) :
    i < P.D.bo.length ∧ (∀ j < i, ¬ P.meets x j) ∧
    0 < cntB (inO (P.D.bo.getD i default)) x.val ∧
    clOK P.C P.D (P.D.bo.getD i default).kg x.val
      (fun y => anyB (Nat.beq (P.D.bo.getD i default).qs) y) Cl = true ∧
    (∀ q ∈ x.val, inO (P.D.bo.getD i default) q = true → ∃ w, (∀ l ∈ w, l < P.C.ns) ∧
      wordF P.C.L w q = (P.D.bo.getD i default).qs ∧ ∃ j, atOK P.C Cl x.val w j = true) ∧
    m * cntB (inO (P.D.bo.getD i default)) x.val =
      (P.D.bo.getD i default).osz * Cl.C.flatten.length := by
  unfold modeBOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, P.missOK_spec h2, h3, h4, fun q hq hqi => ?_, h6⟩
  obtain ⟨hlen, hall⟩ := all2_spec h5
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_filter.2 ⟨hq, hqi⟩)
  have e := hall k hk (by rw [← hlen]; exact hk)
  simp only [Bool.and_eq_true, isS_iff, Nat.beq_eq] at e
  exact ⟨_, e.1.1, e.1.2, _, e.2⟩

theorem meets_of_pos {x : PtL n} {i : ℕ} (h : 0 < cntB (inO (P.D.bo.getD i default)) x.val) :
    P.meets x i := by
  by_contra hn
  have e : cntB (inO (P.D.bo.getD i default)) x.val = 0 := by
    rw [cntB_eq_zero_iff]
    intro q hq
    by_contra hq'
    exact hn ⟨q, hq, by simpa using hq'⟩
  omega

theorem borb_of_mode {r : Rec1} (hr : rec1OK P.C P.D r = true) {i : ℕ} (hi : r.mode = i + 1) :
    borbOK P.C P.D (P.D.bo.getD i default) = true :=
  P.parts.2.1 i (P.modeB_facts ((P.rec1_facts hr).2.2.2 i hi)).1

theorem cl_facts {r : Rec1} (hr : rec1OK P.C P.D r = true) :
    (r.cl.ord.map (lookC r.cl.B r.cl.C)).Perm r.cl.C.flatten ∧
    sortedLt (r.cl.ord.map (lookC r.cl.B r.cl.C)) = true ∧ r.cl.C.flatten.Nodup ∧
    0 < r.cl.C.flatten.length ∧ ∀ y ∈ r.cl.C.flatten, ∃ z : PtL n, z.val = y := by
  have key : ∀ {G : List (List ℕ)} {Pr : List ℕ → Bool}, (∀ w ∈ G, ∀ l ∈ w, l < P.C.ns) →
      clOK P.C P.D G (P.xr r).val Pr r.cl = true →
      (r.cl.ord.map (lookC r.cl.B r.cl.C)).Perm r.cl.C.flatten ∧
      sortedLt (r.cl.ord.map (lookC r.cl.B r.cl.C)) = true ∧ r.cl.C.flatten.Nodup ∧
      0 < r.cl.C.flatten.length ∧ ∀ y ∈ r.cl.C.flatten, ∃ z : PtL n, z.val = y := by
    intro G Pr hG h
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := P.clOK_sound hG (P.xr r) h
    refine ⟨h1, h2, h3, h4, fun y hy => ?_⟩
    obtain ⟨k, -, w, -, -, -, rfl⟩ := h5 y hy
    exact ⟨_, rfl⟩
  rcases hm : r.mode with _ | i
  · exact key P.sLet_lt (P.modeE_facts ((P.rec1_facts hr).2.2.1 hm)).2.1
  · have hf := P.borb_facts (P.borb_of_mode hr hm)
    exact key (fun w hw => (hf.2.2.2.2.1 w hw).1)
      (P.modeB_facts ((P.rec1_facts hr).2.2.2 i hm)).2.2.2.1

theorem clSet_mode0 {r : Rec1} (hr : rec1OK P.C P.D r = true) (h0 : r.mode = 0) :
    clSet n r.cl = orbit P.S (P.xr r) := by
  obtain ⟨-, hcl, -⟩ := P.modeE_facts ((P.rec1_facts hr).2.2.1 h0)
  obtain ⟨-, -, -, hpos, hreach, hclosed⟩ := P.clOK_sound P.sLet_lt (P.xr r) hcl
  rw [P.closure_sLet] at hreach hclosed
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk, w, -, hw, -, e⟩ := hreach _ hy
    refine ⟨⟨k * P.elt w, P.S.mul_mem hk (P.elt_mem_S hw)⟩, PtL.ext ?_⟩
    show ((k * P.elt w) • P.xr r).val = y.val
    rw [mul_smul, e]
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨k, hk, w, -, hw, -, e⟩ := hreach _ (List.getElem_mem hpos)
    have h1 : (k • P.elt w • P.xr r).val ∈ r.cl.C.flatten := e ▸ List.getElem_mem hpos
    have h2 := hclosed (g * (k * P.elt w)⁻¹)
      (P.S.mul_mem hg (P.S.inv_mem (P.S.mul_mem hk (P.elt_mem_S hw)))) _ h1
    rw [← mul_smul k, ← mul_smul, inv_mul_cancel_right] at h2
    exact h2

theorem clSet_modeB {r : Rec1} (hr : rec1OK P.C P.D r = true) {i : ℕ} (hi : r.mode = i + 1) :
    clSet n r.cl = {y ∈ orbit P.S (P.xr r) | (P.D.bo.getD i default).qs ∈ y.val} := by
  obtain ⟨-, -, -, hcl, hst, -⟩ := P.modeB_facts ((P.rec1_facts hr).2.2.2 i hi)
  have hb := P.borb_of_mode hr hi
  have hf := P.borb_facts hb
  obtain ⟨-, -, -, -, hreach, hclosed⟩ :=
    P.clOK_sound (fun w hw => (hf.2.2.2.2.1 w hw).1) (P.xr r) hcl
  rw [P.closure_kg hb] at hreach hclosed
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk, w, -, hw, hp, e⟩ := hreach _ hy
    rw [Subgroup.mem_inf, mem_stabilizer_iff] at hk
    refine ⟨⟨⟨k * P.elt w, P.S.mul_mem hk.2 (P.elt_mem_S hw)⟩, PtL.ext ?_⟩, ?_⟩
    · show ((k * P.elt w) • P.xr r).val = y.val
      rw [mul_smul, e]
    · rw [e]
      have hq : (P.qsF hb).val ∈ (P.elt w • P.xr r).val := (anyB_beq_iff _ _).1 hp
      have h1 := (mem_smul_iff k (P.elt w • P.xr r) (P.qsF hb)).2 hq
      rw [hk.1] at h1
      exact h1
  · rintro ⟨⟨⟨g, hg⟩, rfl⟩, hq⟩
    change (P.qsF hb).val ∈ (g • P.xr r).val at hq
    have hqx : (g⁻¹ • P.qsF hb).val ∈ (P.xr r).val := by
      have h1 := (mem_smul_iff g⁻¹ (g • P.xr r) (P.qsF hb)).2 hq
      rwa [inv_smul_smul] at h1
    have hqO := P.inO_smul hb (P.S.inv_mem hg) (P.qsF hb) hf.2.2.1
    obtain ⟨w, hw, hwq, j, hj⟩ := hst _ hqx hqO
    have hwl : ∀ l ∈ w, l < P.C.nl := fun l hl =>
      lt_of_lt_of_le (hw l hl) (le_trans P.ns_le P.nf_le)
    have hmem := P.atOK_mem (P.chunks_of_clOK hcl) hwl hj
    have hwq' : P.elt w • (g⁻¹ • P.qsF hb) = P.qsF hb := by
      apply Fin.ext
      rw [← act_eq, (P.act_wordF w hwl _ (g⁻¹ • P.qsF hb).isLt).1, hwq]
      rfl
    have hk : g * (P.elt w)⁻¹ ∈ stabilizer Γ (P.qsF hb) ⊓ P.S := by
      rw [Subgroup.mem_inf, mem_stabilizer_iff]
      refine ⟨?_, P.S.mul_mem hg (P.S.inv_mem (P.elt_mem_S hw))⟩
      rw [mul_smul, ← hwq', inv_smul_smul, smul_inv_smul]
      exact hwq'.symm
    have h2 := hclosed _ hk _ hmem
    rw [← mul_smul, inv_mul_cancel_right] at h2
    exact h2

theorem ncard_orbit_xr {r : Rec1} (hr : rec1OK P.C P.D r = true) :
    (orbit P.S (P.xr r)).ncard = r.m := by
  obtain ⟨-, -, hnd, -, hv⟩ := P.cl_facts hr
  have hcard := ncard_clSet hnd hv
  rcases hm : r.mode with _ | i
  · rw [← P.clSet_mode0 hr hm, hcard]
    exact (P.modeE_facts ((P.rec1_facts hr).2.2.1 hm)).2.2.symm
  · obtain ⟨-, -, hpos, -, -, hmc⟩ := P.modeB_facts ((P.rec1_facts hr).2.2.2 i hm)
    have hb := P.borb_of_mode hr hm
    have hc := orbit_count P.S (P.qsF hb) (P.xr r)
    have e1 : {y ∈ orbit P.S (P.xr r) | (P.qsF hb).val ∈ y.val} = clSet n r.cl :=
      (P.clSet_modeB hr hm).symm
    have e2 : {q ∈ orbit P.S (P.qsF hb) | q.val ∈ (P.xr r).val}.ncard =
        cntB (inO (P.D.bo.getD i default)) (P.xr r).val := by
      rw [P.orbit_qs hb, cntB_eq_length_filter,
        length_filter_eq_ncard _ (P.xr r) (nodup_smul (L := P.Λl) P.Λ_nodup)]
      rfl
    rw [P.ncard_orbit_qs hb, e1, hcard, e2] at hc
    exact Nat.eq_of_mul_eq_mul_right hpos (hc.trans hmc.symm)

end Dc2SoundCtx

end CFSG.KC.SLD2

end
