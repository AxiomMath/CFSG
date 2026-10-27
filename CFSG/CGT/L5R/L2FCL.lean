module

public import CFSG.CGT.L5R.L2FDL
public import CFSG.CGT.L5R.L2FAL

public section

namespace CFSG.CGT.L5R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.CGT.M24R

@[expose] def AdmL (u : Fin 2 → N8) : Prop :=
  (∀ l r : List (Fin 2), wv2 dL l = wv2 dL r → wv2 u l = wv2 u r) ∧
    (∀ w, wv2 dL w ≠ 1 → wv2 u w ≠ 1) ∧ (∀ w, wv2 dL w ∈ T8 → wv2 u w ∈ B8L) ∧
    (∀ w, wv2 dL w ∈ B8L → wv2 u w ∈ T8) ∧
    (∀ m : N8, m * wv2 u z1DW * m⁻¹ ∈ T8 ∨
      Nat.card ↥(T8 ⊓ Subgroup.centralizer ({m * wv2 u z1DW * m⁻¹} : Set N8)) ≠ 4) ∧
    ∀ m n : N8, n * bL 0 * n⁻¹ ≠ m * wv2 u z2DW * m⁻¹

theorem AdmL.conj (hT : T8.Normal) {u : Fin 2 → N8} (h : AdmL u) {e : N8} (he : e ∈ DL) :
    AdmL fun k => e * u k * e⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun l r hlr => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun m => ?_,
    fun m n => ?_⟩
  · rw [wv2_conj, wv2_conj, h1 l r hlr]
  · rw [wv2_conj]
    intro h
    exact h2 w hw (by simpa using h)
  · rw [wv2_conj]
    exact (Subgroup.mem_normalizer_iff.1 he _).1 (h3 w hw)
  · rw [wv2_conj]
    exact hT.conj_mem _ (h4 w hw) e
  · have e1 : m * wv2 (fun k => e * u k * e⁻¹) z1DW * m⁻¹ =
        (m * e) * wv2 u z1DW * (m * e)⁻¹ := by rw [wv2_conj]; group
    rw [e1]
    exact h5 (m * e)
  · have e1 : m * wv2 (fun k => e * u k * e⁻¹) z2DW * m⁻¹ =
        (m * e) * wv2 u z2DW * (m * e)⁻¹ := by rw [wv2_conj]; group
    rw [e1]
    exact h6 (m * e) n

section FC


theorem fcCheckL_spec :
    stage0L (mkCtx ()) (dListL (mkCtx ())) (thT2 0) ((mkCtx ()).tab rep2Code) = true ∧
    stage1L (mkCtx ()) (dListL (mkCtx ())) (conjMap (mkCtx ()) (mkCtx ()).codes (betaT 0))
      (thT2 0) ((mkCtx ()).tab rep2Code) = true := by
  have h := Certificates.certificate21196.2.2.2.2.2.2
  simp only [fcCheckL, Bool.and_eq_true] at h
  exact h

variable (hcard : Nat.card N8 = 322560)
include hcard

theorem goodL_of_adm {fm : Array ℕ} {u : Fin 2 → N8} (hu : AdmL u) {U : Fin 2 → Table}
    (hU : ∀ k, IsTab (U k) (u k)) : goodL (mkCtx ()) fm U = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hu
  have hev := evT2_isTab hU
  simp only [goodL, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.not_eq_true', Bool.or_eq_true]
  refine ⟨⟨⟨⟨fun p hp => ?_, fun i => ⟨?_, ?_⟩⟩, fun i => ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
  · exact ((hev p.1).beq_iff hcard (hev p.2) (evT2_size _ _) (evT2_size _ _)).2
      (h1 _ _ (relDW_holds hcard p hp))
  · rw [Bool.eq_false_iff]
    intro h
    exact h2 _ (aDW_spec hcard i).1 (((hev _).beq_iff hcard IsTab.one (evT2_size _ _)
      idT_size).1 h)
  · exact (isB8_iff hcard (hev _) (evT2_size _ _)).2 (h3 _ (aDW_spec hcard i).2)
  · rw [Bool.eq_false_iff]
    intro h
    exact h2 _ (bDW_spec hcard i).1 (((hev _).beq_iff hcard IsTab.one (evT2_size _ _)
      idT_size).1 h)
  · exact (isTt_iff hcard (hev _) (evT2_size _ _)).2 (h4 _ (bDW_spec hcard i).2)
  · rcases h5 1 with h | h
    · left
      exact (isTt_iff hcard (hev _) (evT2_size _ _)).2 (by simpa using h)
    · right
      rw [Bool.eq_false_iff, commCount_eq hcard (hev _)]
      intro h'
      exact h (by simpa using beq_iff_eq.1 h')
  · rw [Bool.eq_false_iff]
    intro h
    obtain ⟨n, hn⟩ := conjVia_sound hcard (isTab_betaT 0) (hev _) h
    exact h6 1 n (by simpa using hn)

theorem viaD_sound {fm : Array ℕ} {R V : Table} {r v : N8} (hR : IsTab R r) (hV : IsTab V v)
    (h : viaD (mkCtx ()) fm R V = true) : ∃ e ∈ DL, e * v * e⁻¹ = r := by
  simp only [viaD, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlt, hD⟩, heq⟩ := h
  have hE := isTab_tab hlt
  refine ⟨_, (normB8_iff hcard hE).1 hD, ?_⟩
  have e := ((hE.mul hV).beq_iff hcard (hR.mul hE) (compT_size _ _) (compT_size _ _)).1 heq
  rw [e, mul_inv_cancel_right]

theorem stage0_sound {v : N8} (hv : v ∈ DL) (h1 : v ≠ 1) (h7 : wv2 (fun _ => v) sevenW = 1) :
    ∃ e ∈ DL, e * v * e⁻¹ = thL 0 ∨ e * v * e⁻¹ = el rep2Code := by
  obtain ⟨c, hc, rfl⟩ := el_of_mem_DL hcard hv
  have hV := isTab_tab (mem_codes.1 ((mem_dListL_iff hcard).1 hc).1).1
  have h0 := fcCheckL_spec.1
  simp only [stage0L, List.all_eq_true] at h0
  have hk := h0 c hc
  have hid : ((mkCtx ()).tab c == idT 16) = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact h1 ((hV.beq_iff hcard IsTab.one (tab_size c) idT_size).1 h)
  have h7' : (evT2 (fun _ => (mkCtx ()).tab c) sevenW == idT 16) = true :=
    ((evT2_isTab (u := fun _ => el c) (fun _ => hV) sevenW).beq_iff hcard IsTab.one
      (evT2_size _ _) idT_size).2 h7
  rw [hid, h7'] at hk
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hk
  rcases hk with h | h
  · obtain ⟨e, he, hev⟩ := viaD_sound hcard (isTab_thT2 0) hV h
    exact ⟨e, he, Or.inl hev⟩
  · obtain ⟨e, he, hev⟩ := viaD_sound hcard (isTab_tab (by unfold rep2Code; norm_num)) hV h
    exact ⟨e, he, Or.inr hev⟩

theorem stage1_sound {r v : N8} (hr : r = thL 0 ∨ r = el rep2Code) (hv : v ∈ DL)
    (hu : AdmL ![r, v]) : r = thL 0 ∧ ∃ k : ℕ, thL 0 ^ k * v * (thL 0 ^ k)⁻¹ = thL 1 := by
  obtain ⟨c, hc, rfl⟩ := el_of_mem_DL hcard hv
  have hV := isTab_tab (mem_codes.1 ((mem_dListL_iff hcard).1 hc).1).1
  have h0 := fcCheckL_spec.2
  simp only [stage1L, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h0
  have key : ∀ {R : Table}, IsTab R r → R.size = 16 → (∀ v ∈ dListL (mkCtx ()), (!(goodL (mkCtx ())
      (conjMap (mkCtx ()) (mkCtx ()).codes (betaT 0)) ![R, (mkCtx ()).tab v]) ||
      (R == thT2 0 && (List.range 7).any fun k => compT 16 (powT 16 k (thT2 0))
        ((mkCtx ()).tab v) == compT 16 (thT2 1) (powT 16 k (thT2 0)))) = true) →
      r = thL 0 ∧ ∃ k : ℕ, thL 0 ^ k * el c * (thL 0 ^ k)⁻¹ = thL 1 := by
    intro R hR hRs hall
    have hg : goodL (mkCtx ()) (conjMap (mkCtx ()) (mkCtx ()).codes (betaT 0))
        ![R, (mkCtx ()).tab c] = true := by
      refine goodL_of_adm hcard hu fun k => ?_
      fin_cases k
      · exact hR
      · exact hV
    have hk := hall c hc
    rw [hg] at hk
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.any_eq_true,
      List.mem_range] at hk
    obtain ⟨hR1, k, -, hk⟩ := hk
    have hpow : IsTab (powT 16 k (thT2 0)) (thL 0 ^ k) := by
      unfold IsTab
      rw [map_pow]
      exact Rep.powT (by norm_num) (isTab_thT2 0) k
    refine ⟨(hR.beq_iff hcard (isTab_thT2 0) hRs (wTab_size _)).1 hR1, k, ?_⟩
    · have e := ((hpow.mul hV).beq_iff hcard ((isTab_thT2 1).mul hpow) (compT_size _ _)
        (compT_size _ _)).1 hk
      rw [e, mul_inv_cancel_right]
  rcases hr with rfl | rfl
  · exact key (isTab_thT2 0) (wTab_size _) h0.1
  · exact key (isTab_tab (by unfold rep2Code; norm_num)) (tab_size _) h0.2

end FC

end CFSG.CGT.L5R
