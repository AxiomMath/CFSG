module

public import CFSG.Certificates.Kernel.SporLatDc2Fib

public section

namespace CFSG.KC.SLD2

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F
open CFSG.KC.SLDc (chunksOK_pos)
open MulAction

namespace Dc2SoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] (P : Dc2SoundCtx Γ n)

theorem lev2_facts {u : List ℕ} {e : Rec2} (hu : ∀ l ∈ u, l < P.C.nl)
    (h : lev2OK P.C P.D u e = true) :
    (∀ ts ∈ e.1, (∀ l ∈ ts.1, l < P.C.nf) ∧ (∀ l ∈ ts.2, l < P.C.ns) ∧
      P.elt u * P.elt ts.1 = P.elt ts.2 * P.elt u) ∧
    (∀ i < P.C.N2, fdep P.D e.2 i = 0 ∨ (fgen P.D e.2 i < e.1.length ∧
      fdep P.D e.2 (idxW P.D (e.1.getD (fgen P.D e.2 i) default).1 i) + 1 = fdep P.D e.2 i)) := by
  unfold lev2OK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun ts hts => ?_, fun i hi => ?_⟩
  · have e := List.all_eq_true.1 h1 ts hts
    simp only [Bool.and_eq_true, isF_iff, isS_iff, List.all_eq_true, Nat.beq_eq] at e
    obtain ⟨⟨ht, hs⟩, hsep⟩ := e
    refine ⟨ht, hs, ?_⟩
    have hl1 : ∀ l ∈ u ++ ts.1, l < P.C.nl := by
      intro l hl
      rcases List.mem_append.1 hl with hl | hl
      · exact hu l hl
      · exact lt_of_lt_of_le (ht l hl) P.nf_le
    have hl2 : ∀ l ∈ ts.2 ++ u, l < P.C.nl := by
      intro l hl
      rcases List.mem_append.1 hl with hl | hl
      · exact lt_of_lt_of_le (hs l hl) (le_trans P.ns_le P.nf_le)
      · exact hu l hl
    rw [← P.elt_append, ← P.elt_append]
    exact P.eq_of_sep hl1 hl2 hsep
  · have e := List.all_eq_true.1 h2 i (List.mem_range.2 hi)
    simp only [Bool.or_eq_true, Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq] at e
    exact e

theorem root_of_dep0 {c : ℕ} (hc : c < P.D.R1.length) {i : ℕ} (hi : i < P.C.N2)
    (h0 : fdep P.D (P.D.R2.getD c default).2 i = 0) :
    ∃ t ∈ P.D.roots.flatten, t.c = c ∧ t.ρ = i := by
  have e := P.parts.2.2.2.2.2.2.2
  unfold rootIdxOK at e
  rw [beq_iff_eq] at e
  have hmem : (c, i) ∈ (List.range P.D.R1.length).flatMap (dep0 P.C P.D) := by
    refine List.mem_flatMap.2 ⟨c, List.mem_range.2 hc, ?_⟩
    refine List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, ?_⟩, rfl⟩
    show Nat.beq (fdep P.D (P.D.R2.getD c default).2 i) 0 = true
    rw [h0]
    rfl
  rw [← e] at hmem
  obtain ⟨t, ht, he⟩ := List.mem_map.1 hmem
  simp only [Prod.mk.injEq] at he
  exact ⟨t, ht, he.1, he.2⟩

theorem idxW_spec {t : List ℕ} (ht : ∀ l ∈ t, l < P.C.nf) (z : PrL n) {i : ℕ} (hi : i < P.C.N2)
    (hz : P.D.fC.flatten.getD i [] = z.val) :
    idxW P.D t i < P.C.N2 ∧ P.D.fC.flatten.getD (idxW P.D t i) [] = (P.elt t • z).val := by
  induction t with
  | nil => exact ⟨hi, by rw [P.elt_nil, one_smul]; exact hz⟩
  | cons l t ih =>
    obtain ⟨h1, h2⟩ := ih fun l' hl' => ht l' (List.mem_cons_of_mem _ hl')
    have hl := ht l List.mem_cons_self
    obtain ⟨h3, h4⟩ := P.fRow_spec hl _ h1
    refine ⟨h3, ?_⟩
    rw [P.elt_cons, mul_smul, P.smul_fAct hl, ← h2]
    exact h4

theorem forest {c : ℕ} (hc : c < P.D.R1.length) :
    ∀ i < P.C.N2, ∀ z : PrL n, P.D.fC.flatten.getD i [] = z.val →
      ∃ T ∈ P.H, ∃ t ∈ P.D.roots.flatten, t.c = c ∧
        P.D.fC.flatten.getD t.ρ [] = (T⁻¹ • z).val ∧
        P.elt (P.D.R1.getD c default).u * T * (P.elt (P.D.R1.getD c default).u)⁻¹ ∈ P.S := by
  obtain ⟨hgen, hdep⟩ :=
    P.lev2_facts (P.rec1_facts (P.parts.2.2.1 c hc)).1 (P.parts.2.2.2.2.2.1 c hc)
  suffices ∀ d, ∀ i < P.C.N2, fdep P.D (P.D.R2.getD c default).2 i = d → ∀ z : PrL n,
      P.D.fC.flatten.getD i [] = z.val → ∃ T ∈ P.H, ∃ t ∈ P.D.roots.flatten, t.c = c ∧
        P.D.fC.flatten.getD t.ρ [] = (T⁻¹ • z).val ∧
        P.elt (P.D.R1.getD c default).u * T * (P.elt (P.D.R1.getD c default).u)⁻¹ ∈ P.S from
    fun i hi z hz => this _ i hi rfl z hz
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hi hd z hz
    rcases hdep i hi with h0 | ⟨hg, hd'⟩
    · obtain ⟨t, ht, htc, rfl⟩ := P.root_of_dep0 hc hi h0
      refine ⟨1, P.H.one_mem, t, ht, htc, by rw [inv_one, one_smul]; exact hz, ?_⟩
      rw [mul_one, mul_inv_cancel]
      exact P.S.one_mem
    · have hts : (P.D.R2.getD c default).1.getD (fgen P.D (P.D.R2.getD c default).2 i) default ∈
          (P.D.R2.getD c default).1 := by
        rw [List.getD_eq_getElem _ _ hg]
        exact List.getElem_mem hg
      obtain ⟨ht1, ht2, hconj⟩ := hgen _ hts
      obtain ⟨hi', hz'⟩ := P.idxW_spec ht1 z hi hz
      obtain ⟨T', hT', t, ht, htc, hρ, hS'⟩ := ih _ (by omega) _ hi' rfl _ hz'
      refine ⟨(P.elt _)⁻¹ * T', P.H.mul_mem (P.H.inv_mem (P.elt_mem_H ht1)) hT', t, ht, htc, ?_, ?_⟩
      · rw [hρ, mul_inv_rev, inv_inv, mul_smul]
      · have hσ := eq_mul_inv_of_mul_eq hconj.symm
        have e : P.elt (P.D.R1.getD c default).u * ((P.elt
            ((P.D.R2.getD c default).1.getD (fgen P.D (P.D.R2.getD c default).2 i) default).1)⁻¹ *
            T') * (P.elt (P.D.R1.getD c default).u)⁻¹ =
            (P.elt (P.D.R1.getD c default).u * P.elt
            ((P.D.R2.getD c default).1.getD (fgen P.D (P.D.R2.getD c default).2 i) default).1 *
            (P.elt (P.D.R1.getD c default).u)⁻¹)⁻¹ *
            (P.elt (P.D.R1.getD c default).u * T' * (P.elt (P.D.R1.getD c default).u)⁻¹) := by
          group
        rw [e, ← hσ]
        exact P.S.mul_mem (P.S.inv_mem (P.elt_mem_S ht2)) hS'

theorem rootOK_of_mem {t : Root} (ht : t ∈ P.D.roots.flatten) : rootOK P.C P.D t = true := by
  obtain ⟨bl, hbl, htb⟩ := List.mem_flatten.1 ht
  obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hbl
  have e := P.parts.2.2.2.2.2.2.1 b hb
  unfold rootsOK at e
  rw [List.getD_eq_getElem _ _ hb] at e
  exact List.all_eq_true.1 e t htb

theorem root_facts {t : Root} (ht : t ∈ P.D.roots.flatten) :
    (∀ l ∈ t.φ, l < P.C.nf) ∧ (P.elt t.φ • P.Δl).val = P.D.fC.flatten.getD t.ρ [] ∧
    witOK P.C ((P.D.R1.getD t.c default).u ++ t.φ) t.s t.l t.p = true := by
  have e := P.rootOK_of_mem ht
  unfold rootOK at e
  simp only [Bool.and_eq_true, isF_iff, Nat.beq_eq] at e
  obtain ⟨⟨h1, h2⟩, h3⟩ := e
  refine ⟨h1, ?_, h3⟩
  obtain ⟨hC, hhead, hlen, -⟩ := P.fRest_facts
  have hpos : 0 < P.C.N2 := hlen ▸ (chunksOK_pos hC).2
  have h0 : P.D.fC.flatten.getD 0 [] = P.Δl.val := by
    rw [← List.headD_eq_getD, hhead]
    rfl
  rw [← h2, (P.idxW_spec h1 P.Δl hpos h0).2]

theorem cover (g : Γ) : ∃ t ∈ P.D.roots.flatten, t.c < P.D.R1.length ∧ ∃ s₁ ∈ P.S, ∃ s₂ ∈ P.S,
    g = s₁ * P.elt ((P.D.R1.getD t.c default).u ++ t.φ) * s₂ := by
  obtain ⟨hU, hstab, hstabΔ⟩ := P.count
  have hg : g • P.Λl ∈ P.U1 P.D.R1 := hU ▸ mem_orbit P.Λl g
  obtain ⟨r, hr, ⟨⟨s, hs⟩, hsx⟩⟩ := hg
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hr
  obtain ⟨u, hu⟩ : ∃ u, (P.D.R1.getD c default).u = u := ⟨_, rfl⟩
  have hsx' : s • P.elt u • P.Λl = g • P.Λl := by
    rw [← hu, List.getD_eq_getElem _ _ hc]
    exact hsx
  have hh : (P.elt u)⁻¹ * s⁻¹ * g ∈ P.H := by
    rw [← hstab, mem_stabilizer_iff, mul_smul, mul_smul, ← hsx', inv_smul_smul, inv_smul_smul]
  have hz : (((P.elt u)⁻¹ * s⁻¹ * g) • P.Δl).val ∈ P.D.fC.flatten := by
    have e : ((P.elt u)⁻¹ * s⁻¹ * g) • P.Δl ∈ orbit P.H P.Δl := ⟨⟨_, hh⟩, rfl⟩
    rw [P.orbit_H_Δ] at e
    exact e
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hz
  obtain ⟨-, -, hlen, -⟩ := P.fRest_facts
  obtain ⟨T, hT, t, ht, htc, hρ, hTS⟩ := P.forest hc i (by omega)
    (((P.elt u)⁻¹ * s⁻¹ * g) • P.Δl) (by rw [List.getD_eq_getElem _ _ hi, e])
  rw [hu] at hTS
  obtain ⟨hφ, hφΔ, -⟩ := P.root_facts ht
  have e2 : T⁻¹ • ((P.elt u)⁻¹ * s⁻¹ * g) • P.Δl = P.elt t.φ • P.Δl :=
    PrL.ext (hρ.symm.trans hφΔ.symm)
  have hs₂ : (P.elt t.φ)⁻¹ * T⁻¹ * ((P.elt u)⁻¹ * s⁻¹ * g) ∈ P.S := by
    rw [← hstabΔ, Subgroup.mem_inf, mem_stabilizer_iff]
    refine ⟨?_, P.H.mul_mem (P.H.mul_mem (P.H.inv_mem (P.elt_mem_H hφ)) (P.H.inv_mem hT)) hh⟩
    rw [mul_smul, mul_smul, e2, inv_smul_smul]
  refine ⟨t, ht, by rw [htc]; exact hc, s * (P.elt u * T * (P.elt u)⁻¹), P.S.mul_mem hs hTS, _,
    hs₂, ?_⟩
  rw [htc, hu, P.elt_append]
  group

end Dc2SoundCtx

end CFSG.KC.SLD2

end
