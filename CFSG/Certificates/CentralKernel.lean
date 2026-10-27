module

public import CFSG.Certificates.CentralizerPresented
public import CFSG.Certificates.CosetTableRelations

public section

namespace CFSG.CosetTable

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

section Core

variable {G : Type*} [Group G] {gen : ℕ → G} {H : Subgroup G} {P : Params}

theorem exists_live_rel (hP : Good gen H P)
    (hgen : Subgroup.closure (gen '' Set.Iio P.L) = ⊤) {st : St} (h : SInv P.L gen H st)
    (hc : st.complete P.L = true) (g : G) :
    ∃ c, st.live c = true ∧ Rel P.L gen H st.par 1 g c := by
  unfold St.complete at hc
  rw [Bool.and_eq_true, allBelow_iff] at hc
  obtain ⟨h1, hrow⟩ := hc
  have hlive : ∀ c, st.live c = true → 0 < c ∧ c < st.next := by
    intro c hc
    simp only [St.live, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hc.1.2⟩
  have hstep : ∀ c, st.live c = true → ∀ x < P.L, st.live (st.tab.getD (c * P.L + x) 0) = true ∧
      Rel P.L gen H st.par c (gen x) (st.tab.getD (c * P.L + x) 0) := by
    intro c hc x hx
    have hr := hrow c (hlive c hc).2
    simp only [hc, Bool.not_true, Bool.false_or, allBelow_iff] at hr
    have hl := hr x hx
    refine ⟨hl, ?_⟩
    have hne : st.tab.getD (c * P.L + x) 0 ≠ 0 := by
      have := (hlive _ hl).1; omega
    have := h.tab_rel _ hne
    obtain ⟨dd, mm⟩ := div_mod_letter (c := c) hx
    rwa [dd, mm] at this
  have hg : g ∈ Subgroup.closure (gen '' Set.Iio P.L) := hgen ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨1, h1, Rel.refl _ _⟩
  | mul_right g _ y hy ih =>
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨c, hc, hr⟩ := ih
    obtain ⟨hl, hr'⟩ := hstep c hc x hx
    exact ⟨_, hl, hr.trans hr'⟩
  | mul_inv_cancel g _ y hy ih =>
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨c, hc, hr⟩ := ih
    obtain ⟨hl, hr'⟩ := hstep c hc _ (hP.inv_lt x hx)
    exact ⟨_, hl, (hr.trans hr').of_eq (by rw [hP.gen_inv x hx])⟩

theorem mem_conj_of_fixAll (hP : Good gen H P)
    (hgen : Subgroup.closure (gen '' Set.Iio P.L) = ⊤) {st : St} (h : SInv P.L gen H st)
    (hc : st.complete P.L = true) (w : List ℕ) (hw : ∀ y ∈ w, y < P.L)
    (hfix : ∀ c, st.live c = true → walkRoot P.L st.tab st.fwd st.next c w = some c) (g : G) :
    g * evalWord gen w * g⁻¹ ∈ H := by
  obtain ⟨c, hc', hr⟩ := exists_live_rel hP hgen h hc g
  have hlive : c < st.next := by
    simp only [St.live, Bool.and_eq_true, decide_eq_true_eq] at hc'
    exact hc'.1.2
  have hwc := walkRoot_spec h st.next w c c hw hlive (hfix c hc')
  rw [rel_iff, Inv.rep_one h, one_mul] at hr
  rw [rel_iff] at hwc
  have := H.mul_mem (H.mul_mem hr hwc) (H.inv_mem hr)
  convert this using 1
  group

theorem mem_center_of_conj_mem {x : G} {H : Subgroup G} (hH : H ≤ Subgroup.centralizer {x})
    (hN : Subgroup.normalClosure {x} = ⊤) {W : G} (hW : ∀ g : G, g * W * g⁻¹ ∈ H) :
    W ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ Subgroup.normalClosure ({x} : Set G) := hN ▸ Subgroup.mem_top y
  have hcl : Subgroup.normalClosure ({x} : Set G) ≤ Subgroup.centralizer ({W} : Set G) := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro z hz
    rw [Group.mem_conjugatesOfSet_iff] at hz
    obtain ⟨a', ha', hconj⟩ := hz
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    have h1 := hH (hW g⁻¹)
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    calc g * a' * g⁻¹ * W = g * (a' * (g⁻¹ * W * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * W * g) * a') * g⁻¹ := by
        have := h1
        simp only [inv_inv] at this
        rw [← this]
      _ = W * (g * a' * g⁻¹) := by group
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcl hy)

end Core

section Presented

variable {m : ℕ}

@[expose] def fixCheckHLT (P : Params) (cap n : ℕ) (us : List (List ℕ)) : Bool :=
  let st := enumerateHLT P cap
  (!st.overflow && st.complete P.L && st.liveCount == n) &&
    (List.range st.next).all fun c =>
      !st.live c || us.all fun w => walkRoot P.L st.tab st.fwd st.next c w == some c

theorem checkHLT_of_fixCheckHLT {P : Params} {cap n : ℕ} {us : List (List ℕ)}
    (h : fixCheckHLT P cap n us = true) : checkHLT P cap n = true := by
  unfold fixCheckHLT at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  unfold checkHLT
  simpa only [Bool.and_eq_true] using h1

theorem central_of_fixCheckHLT (ws : List (List (Fin m × Bool))) {i : ℕ} (hi : i < m)
    (cw : List (List ℕ))
    (hcw : ∀ s ∈ cw, Commute (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (2 * i))
      (evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) s))
    (hlet : ∀ s ∈ cw, ∀ c ∈ s, c < 2 * m) {cap n cap₂ : ℕ} (us : List (List (Fin m × Bool)))
    (h1 : fixCheckHLT (mkParams (2 * m) (invArr m) (codes ws) cw) cap n (codes us) = true)
    (h2 : check (presParams (ws ++ [genWord m i]) []) cap₂ 1 = true) :
    ∀ u ∈ us, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u) ∈ Subgroup.center (PG m ws) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set gen := presLetter rels
  set x : PG m ws := PresentedGroup.of ⟨i, hi⟩
  have hx : gen (2 * i) = x := presLetter_two_mul hi
  set H : Subgroup (PG m ws) := Subgroup.closure {g | ∃ s ∈ cw, g = evalWord gen s}
  have hH : H ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have := hcw s hs
    rw [hx] at this
    exact this.eq.symm
  have hg := goodParams ws [] H (by simp)
  have hgood : Good gen H (mkParams (2 * m) (invArr m) (codes ws) cw) := by
    refine ⟨hg.inv_lt, hg.gen_inv, ?_, ?_, ?_⟩
    · intro x' p hp
      exact hg.scans x' p (by simpa [presParams, mkParams] using hp)
    · intro p hp
      obtain ⟨hp1, hp2⟩ := mem_subs hp
      exact ⟨hp1, hlet _ hp2, Subgroup.subset_closure ⟨_, hp2, rfl⟩⟩
    · intro p hp
      exact hg.rels p (by simpa [presParams, mkParams] using hp)
  have hgen : Subgroup.closure (gen '' Set.Iio (mkParams (2 * m) (invArr m) (codes ws) cw).L) =
      ⊤ := by
    have := closure_presLetter rels
    simpa [mkParams] using this
  obtain ⟨f2, c2⟩ := card_le_of_check_trivial (ws ++ [genWord m i]) h2
  have hN : Subgroup.normalClosure {x} = ⊤ := by
    apply eq_top_of_card_le_one (us := [genWord m i]) _ _ f2 c2
    intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    exact Subgroup.closure_le_normalClosure (mk_genWord_mem hi)
  have hc := checkHLT_of_fixCheckHLT h1
  unfold fixCheckHLT at h1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨hov, hcomplete⟩, -⟩, hwalk⟩ := h1
  have hinv := enumerateHLT_inv hgood cap
  intro u hu
  have hcode : u.map letterCode ∈ codes us := List.mem_map_of_mem hu
  apply mem_center_of_conj_mem hH hN (W := PresentedGroup.mk rels (FreeGroup.mk u))
  have hu' : PresentedGroup.mk rels (FreeGroup.mk u) = evalWord gen (u.map letterCode) := by
    rw [evalWord_presLetter]
  rw [hu']
  intro g
  refine mem_conj_of_fixAll hgood hgen hinv hcomplete _ ?_ ?_ g
  · intro y hy
    have := letters_codes hcode y hy
    simpa [mkParams] using this
  · intro c hcl
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq] at hwalk
    have hlt : c < (enumerateHLT (mkParams (2 * m) (invArr m) (codes ws) cw) cap).next := by
      simp only [St.live, Bool.and_eq_true, decide_eq_true_eq] at hcl
      exact hcl.1.2
    rcases hwalk c hlt with hn | hw
    · rw [hcl] at hn; exact absurd hn (by simp)
    · exact hw (u.map letterCode) hcode

end Presented

end CFSG.CosetTable
