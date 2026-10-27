module

public import CFSG.Certificates.Kernel.SporLatDcImgs

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

namespace DcSoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

variable (P : DcSoundCtx Γ n)

theorem lab_lab {x : List ℕ} (hx : PtValid n x) (g h : Γ) :
    lab n ptLab (lab n ptLab x h) g = lab n ptLab x (g * h) :=
  (lab_mul (A := ptLab) (Δ := x) hlaw hx g h).symm

private theorem Sx_shift {x : List ℕ} (hx : PtValid n x) {g : Γ} (hg : g ∈ P.S)
    {M : List ℕ} (hM : M ∈ P.Sx x) : lab n ptLab M g ∈ P.Sx x := by
  rw [mem_Sx] at hM ⊢
  obtain ⟨s, hs, rfl⟩ := hM
  exact ⟨g * s, P.S.mul_mem hg hs, lab_lab hx g s⟩

private theorem Sx_shift_inv {x : List ℕ} (hx : PtValid n x) {g : Γ} (hg : g ∈ P.S)
    {M : List ℕ} (hM : M ∈ P.Sx x) :
    lab n ptLab (lab n ptLab M g) g⁻¹ = M := by
  rw [mem_Sx] at hM
  obtain ⟨s, hs, rfl⟩ := hM
  rw [lab_lab hx g s, lab_lab hx g⁻¹ (g * s), inv_mul_cancel_left]

private theorem Sx_shift_inv' {x : List ℕ} (hx : PtValid n x) {g : Γ} (hg : g ∈ P.S)
    {M : List ℕ} (hM : M ∈ P.Sx x) :
    lab n ptLab (lab n ptLab M g⁻¹) g = M := by
  rw [mem_Sx] at hM
  obtain ⟨s, hs, rfl⟩ := hM
  rw [lab_lab hx g⁻¹ s, lab_lab hx g (g⁻¹ * s), mul_inv_cancel_left]

private theorem card_filter_shift {x : List ℕ} (hx : PtValid n x) {g : Γ} (hg : g ∈ P.S)
    {j p : ℕ} (hp : p < n) (hgp : act n g⁻¹ p = P.D.obase.getD j 0) :
    ((P.Sx x).filter (fun M => p ∈ M)).card =
      ((P.Sx x).filter (fun M => P.D.obase.getD j 0 ∈ M)).card := by
  have hg' : g⁻¹ ∈ P.S := P.S.inv_mem hg
  refine Finset.card_bij (fun M _ => lab n ptLab M g⁻¹) ?_ ?_ ?_
  · intro M hM
    rw [Finset.mem_filter] at hM ⊢
    refine ⟨Sx_shift P hx hg' hM.1, ?_⟩
    rw [← List.mem_toFinset, lab_toFinset, Finset.mem_image]
    exact ⟨p, List.mem_toFinset.mpr hM.2, hgp⟩
  · intro M1 hM1 M2 hM2 he
    rw [Finset.mem_filter] at hM1 hM2
    have h1 := Sx_shift_inv' P hx hg hM1.1
    have h2 := Sx_shift_inv' P hx hg hM2.1
    rw [← h1, ← h2, he]
  · intro M' hM'
    rw [Finset.mem_filter] at hM'
    refine ⟨lab n ptLab M' g, ?_, Sx_shift_inv P hx hg hM'.1⟩
    rw [Finset.mem_filter]
    refine ⟨Sx_shift P hx hg hM'.1, ?_⟩
    rw [← List.mem_toFinset, lab_toFinset, Finset.mem_image]
    refine ⟨P.D.obase.getD j 0, List.mem_toFinset.mpr hM'.2, ?_⟩
    rw [← hgp, ← act_mul _ _ hp, mul_inv_cancel, act_one hp]

private theorem card_filter_of_mem_Oj {x : List ℕ} (hx : PtValid n x) {j : ℕ}
    (hj : j < P.D.obase.length) {p : ℕ} (hp : p ∈ P.Oj j) :
    ((P.Sx x).filter (fun M => p ∈ M)).card =
      ((P.Sx x).filter (fun M => P.D.obase.getD j 0 ∈ M)).card := by
  rw [mem_Oj] at hp
  obtain ⟨hpn, hpo⟩ := hp
  obtain ⟨s, hs, hsp⟩ := reach_base P (dp P.D p) p hpn rfl
  have hsp' : act n s (P.D.obase.getD (oid P.D p) 0) = p := hsp
  rw [hpo] at hsp'
  have hj' : j < P.D.obase.length := by
    rw [← hpo]
    exact ptOK_oid_lt P hpn
  refine card_filter_shift P hx (g := s) hs hpn ?_
  rw [← hsp', ← act_mul _ _ (obase_lt P hj'), inv_mul_cancel, act_one (obase_lt P hj')]

theorem filter_eq_inter_Oj {x : List ℕ} {M : List ℕ} (hx : PtValid n x) (hM : M ∈ P.Sx x)
    (j : ℕ) : M.toFinset.filter (fun p => oid P.D p = j) = M.toFinset ∩ P.Oj j := by
  ext p
  rw [Finset.mem_filter, Finset.mem_inter, mem_Oj]
  constructor
  · rintro ⟨hp, ho⟩
    exact ⟨hp, Sx_lt P (fun q hq => hx.2 q hq) hM p (List.mem_toFinset.mp hp), ho⟩
  · rintro ⟨hp, -, ho⟩
    exact ⟨hp, ho⟩

private noncomputable def pairSet (x : List ℕ) (j : ℕ) : Finset (List ℕ × ℕ) :=
  (P.Sx x).biUnion (fun M => (M.toFinset.filter (fun p => oid P.D p = j)).image (fun p => (M, p)))

private theorem pairSet_mem_iff {x : List ℕ} {j : ℕ} {a : List ℕ × ℕ} :
    a ∈ P.pairSet x j ↔ a.1 ∈ P.Sx x ∧ a.2 ∈ a.1.toFinset ∧ oid P.D a.2 = j := by
  rw [pairSet, Finset.mem_biUnion]
  constructor
  · rintro ⟨M, hM, ha⟩
    rw [Finset.mem_image] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    rw [Finset.mem_filter] at hp
    exact ⟨hM, hp.1, hp.2⟩
  · rintro ⟨hM, hp, ho⟩
    refine ⟨a.1, hM, ?_⟩
    rw [Finset.mem_image]
    exact ⟨a.2, Finset.mem_filter.mpr ⟨hp, ho⟩, rfl⟩

private theorem pairSet_card₁ {x : List ℕ} (hx : PtValid n x) (hnd : x.Nodup) (j : ℕ)
    (hj : j < P.D.obase.length) :
    (P.pairSet x j).card = (P.Sx x).card * cntO P.D x j := by
  rw [pairSet, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun M hM => ?_), Finset.sum_const, smul_eq_mul]
    rw [Finset.card_image_of_injOn]
    · rw [filter_eq_inter_Oj P hx hM, card_Sx_inter P (fun p hp => hx.2 p hp) hnd hM]
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
      exact (Prod.mk.inj hab).2
  · intro M1 hM1 M2 hM2 hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq] at ha1 ha2
    obtain ⟨p, -, rfl⟩ := ha1
    obtain ⟨p', -, h2⟩ := ha2
    exact hne (Prod.mk.inj h2).1.symm

private theorem pairSet_fst {x : List ℕ} (hx : PtValid n x) {j : ℕ}
    (hj : j < P.D.obase.length) :
    Set.MapsTo (fun a : List ℕ × ℕ => a.2) (↑(P.pairSet x j) : Set (List ℕ × ℕ))
      (↑(P.Oj j) : Set ℕ) := by
  rintro ⟨M, p⟩ hp
  have hp' : (M, p) ∈ P.pairSet x j := hp
  rw [pairSet_mem_iff] at hp'
  change p ∈ P.Oj j
  rw [mem_Oj]
  have hpM : p ∈ M := List.mem_toFinset.mp (by simpa using hp'.2.1)
  exact ⟨Sx_lt P (fun q hq => hx.2 q hq) hp'.1 p hpM, hp'.2.2⟩

private theorem pairSet_card₂ {x : List ℕ} (hx : PtValid n x) (hnd : x.Nodup) {j : ℕ}
    (hj : j < P.D.obase.length) (h0 : 0 < (P.D.K.getD j []).length)
    (hpaths : pathsOK P.C P.D x j = true) :
    (P.pairSet x j).card = P.D.osz.getD j 0 * (imgs P.C P.D x j).length := by
  rw [Finset.card_eq_sum_card_fiberwise (pairSet_fst P hx hj)]
  have hterm : ∀ p ∈ P.Oj j, ((P.pairSet x j).filter (fun a => a.2 = p)).card =
      (imgs P.C P.D x j).length := by
    intro p hp
    have himg : ((P.pairSet x j).filter (fun a => a.2 = p)).image Prod.fst =
        (P.Sx x).filter (fun M => p ∈ M) := by
      ext M
      constructor
      · intro hM
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hM
        rw [Finset.mem_filter] at ha
        have hp' : (a.1, a.2) ∈ P.pairSet x j := ha.1
        rw [pairSet_mem_iff] at hp'
        rw [ha.2] at hp'
        exact Finset.mem_filter.mpr ⟨hp'.1, List.mem_toFinset.mp hp'.2.1⟩
      · intro hM
        rw [Finset.mem_filter] at hM
        refine Finset.mem_image.mpr ⟨(M, p), ?_, rfl⟩
        rw [Finset.mem_filter]
        have hpiff := pairSet_mem_iff (P := P) (x := x) (j := j) (a := (M, p))
        exact ⟨hpiff.mpr ⟨hM.1, List.mem_toFinset.mpr hM.2, (mem_Oj P).mp hp |>.2⟩, rfl⟩
    have hcard : ((P.pairSet x j).filter (fun a => a.2 = p)).card =
        ((P.Sx x).filter (fun M => p ∈ M)).card := by
      rw [← himg, Finset.card_image_of_injOn]
      rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Prod.fst, Prod.mk.injEq] at ha hb hab ⊢
      exact ⟨hab, ha.2.trans hb.2.symm⟩
    rw [hcard, card_filter_of_mem_Oj P hx hj hp,
      ← imgs_length P hj h0 (fun p hp => hx.2 p hp) hpaths]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Oj_card P hj]

private theorem card_mul {x : List ℕ} (hx : PtValid n x) (hnd : x.Nodup) {j : ℕ}
    (hj : j < P.D.obase.length) (h0 : 0 < (P.D.K.getD j []).length)
    (hpaths : pathsOK P.C P.D x j = true) :
    (P.Sx x).card * cntO P.D x j = P.D.osz.getD j 0 * (imgs P.C P.D x j).length := by
  rw [← pairSet_card₁ P hx hnd j hj, pairSet_card₂ P hx hnd hj h0 hpaths]

theorem isW_lt {w : List ℕ} (h : isW P.C w = true) : ∀ l ∈ w, l < 2 + P.C.ns := by
  intro l hl
  have h1 := (List.all_eq_true.mp h) l hl
  rwa [Nat.blt_eq] at h1

private theorem delta_nodup : P.C.Δ.Nodup :=
  List.Pairwise.imp (fun {_ _} h => ne_of_lt h) (delta_pair P)

theorem repOK_parts {r : Rep} (hr : repOK P.C P.D r) :
    isW P.C r.w = true ∧ Rep.lab r = labF (wordF P.C.L r.w) P.C.Δ := by
  unfold repOK at hr
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hr
  refine ⟨hr.1.1.1, ?_⟩
  simpa using hr.1.1.2

theorem rep_lab_eq {r : Rep} (hr : repOK P.C P.D r) :
    Rep.lab r = lab n ptLab P.C.Δ (evalElt P.els r.w) := by
  obtain ⟨hisW, hlab⟩ := repOK_parts P hr
  rw [hlab, P.labF_eq_lab (isW_lt P hisW)]

private theorem rep_lab_lt {r : Rep} (hr : repOK P.C P.D r) : ∀ p ∈ Rep.lab r, p < n := by
  rw [rep_lab_eq P hr]
  exact lab_lt (fun p hp => delta_lt P hp) _

theorem rep_lab_valid {r : Rep} (hr : repOK P.C P.D r) : PtValid n (Rep.lab r) := by
  rw [rep_lab_eq P hr]
  exact lab_valid (fun p hp => delta_lt P hp) _

theorem rep_lab_nodup {r : Rep} (hr : repOK P.C P.D r) : (Rep.lab r).Nodup := by
  rw [rep_lab_eq P hr]
  exact lab_nodup (fun p hp => delta_lt P hp) (delta_nodup P) _

theorem m_eq_card {r : Rep} (hr : repOK P.C P.D r) :
    Rep.m r = (P.Sx (Rep.lab r)).card := by
  have hr0 : repOK P.C P.D r = true := hr
  obtain ⟨hisW, hlab⟩ := repOK_parts P hr
  unfold repOK at hr
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hr
  have horb := hr.1.2
  unfold orbR at horb
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at horb
  obtain ⟨⟨⟨⟨⟨hj, hcnt⟩, harg⟩, hpaths⟩, -⟩, hsize⟩ := horb
  have hj' : Rep.j r < P.D.obase.length := by rwa [Nat.blt_eq] at hj
  have hcnt' : 0 < cntO P.D (Rep.lab r) (Rep.j r) := by rwa [Nat.blt_eq] at hcnt
  have hK0 : 0 < (P.D.K.getD (Rep.j r) []).length := by
    unfold argOK at harg
    rw [Bool.and_eq_true] at harg
    have := harg.1
    rwa [Nat.blt_eq] at this
  have hsz : (imgs P.C P.D (Rep.lab r) (Rep.j r)).length * P.D.osz.getD (Rep.j r) 0 =
      cntO P.D (Rep.lab r) (Rep.j r) * Rep.m r := by
    unfold sizeKey at hsize
    rw [Bool.and_eq_true] at hsize
    have := hsize.1
    rwa [Nat.beq_eq] at this
  have h1 := card_mul P (rep_lab_valid P hr0) (rep_lab_nodup P hr0) hj' hK0 hpaths
  have hosz : 0 < P.D.osz.getD (Rep.j r) 0 := osz_pos P hj'
  have h2 : (P.Sx (Rep.lab r)).card *
        (cntO P.D (Rep.lab r) (Rep.j r) * P.D.osz.getD (Rep.j r) 0) =
      Rep.m r * (cntO P.D (Rep.lab r) (Rep.j r) * P.D.osz.getD (Rep.j r) 0) := by
    calc (P.Sx (Rep.lab r)).card * (cntO P.D (Rep.lab r) (Rep.j r) * P.D.osz.getD (Rep.j r) 0)
        = ((P.Sx (Rep.lab r)).card * cntO P.D (Rep.lab r) (Rep.j r)) *
            P.D.osz.getD (Rep.j r) 0 := by ring
      _ = (P.D.osz.getD (Rep.j r) 0 * (imgs P.C P.D (Rep.lab r) (Rep.j r)).length) *
            P.D.osz.getD (Rep.j r) 0 := by rw [h1]
      _ = P.D.osz.getD (Rep.j r) 0 *
            ((imgs P.C P.D (Rep.lab r) (Rep.j r)).length * P.D.osz.getD (Rep.j r) 0) := by ring
      _ = P.D.osz.getD (Rep.j r) 0 * (cntO P.D (Rep.lab r) (Rep.j r) * Rep.m r) := by rw [hsz]
      _ = Rep.m r * (cntO P.D (Rep.lab r) (Rep.j r) * P.D.osz.getD (Rep.j r) 0) := by ring
  exact (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hcnt' hosz) h2).symm

end DcSoundCtx

end CFSG.KC.SLDc

end
