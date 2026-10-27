module

public import Certificates.Data.G2ThreeMaxCheck

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert

open CFSG.Monster.B.TwoA.Census Certificates.G2ThreeMax


@[expose] def wordElem {G : Type*} [Group G] (gens : ℕ → G) (w : List ℕ) : G := (w.map gens).prod

section Stage

variable {G X : Type*} [Group G] [MulAction G X]

theorem tab_spec {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root : ℕ} {c : NatCert}
    (h : natCertOK act ngen valid root c = true) {dec : ℕ → X} {gens : ℕ → G}
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a)
    {k : ℕ} (hk : k < ngen) {i : ℕ} (hi : i < c.pts.size) :
    tabOf c k i < c.pts.size ∧ dec c.pts[tabOf c k i]! = gens k • dec c.pts[i]! := by
  obtain ⟨hj, e⟩ := natCertOK_edge h hi hk
  refine ⟨hj, ?_⟩
  unfold tabOf
  rw [e, hact k hk _ (natCertOK_valid h hi)]

theorem word_spec {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root : ℕ} {c : NatCert}
    (h : natCertOK act ngen valid root c = true) {dec : ℕ → X} {gens : ℕ → G}
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a) (w : List ℕ)
    (hw : ∀ k ∈ w, k < ngen) :
    ∀ i < c.pts.size, applyW c w i < c.pts.size ∧
      dec c.pts[applyW c w i]! = wordElem gens w • dec c.pts[i]! := by
  induction w with
  | nil => intro i hi; simpa [applyW, wordElem] using hi
  | cons k w ih =>
    intro i hi
    have hk : k < ngen := hw k (by simp)
    obtain ⟨h1, h2⟩ := ih (fun x hx => hw x (by simp [hx])) i hi
    obtain ⟨h3, h4⟩ := tab_spec h hact hk h1
    refine ⟨?_, ?_⟩
    · simpa [applyW] using h3
    · have e : applyW c (k :: w) i = tabOf c k (applyW c w i) := rfl
      have hwe : wordElem gens (k :: w) = gens k * wordElem gens w := by simp [wordElem]
      rw [e, h4, h2, hwe, mul_smul]

theorem orbit_mem_of_natCertOK {act : ℕ → ℕ → ℕ} {ngen N root : ℕ} {c : NatCert} {d : ℕ → X}
    {gs : ℕ → G} (h : natCertOK act ngen (fun u => decide (u < N)) root c = true)
    (hact : ∀ k < ngen, ∀ a < N, d (act k a) = gs k • d a) {i : ℕ} (hi : i ∈ c.pts.toList) :
    ∃ m ∈ Subgroup.closure (gs '' {k | k < ngen}), d i = m • d root := by
  have h' := orbit_of_natCertOK h (dec := d) (gens := gs)
    (fun k hk a ha => hact k hk a (by simpa using ha))
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hi
  have hj' : j < c.pts.size := by simpa using hj
  have hmem : d c.pts[j]! ∈ MulAction.orbit (Subgroup.closure (gs '' {k | k < ngen})) (d root) := by
    rw [h']
    exact ⟨j, hj', rfl⟩
  obtain ⟨⟨m, hm⟩, hmx⟩ := hmem
  refine ⟨m, hm, ?_⟩
  have hmx' : m • d root = d c.pts[j]! := hmx
  have hi' : c.pts.toList[j] = c.pts[j]! := by simp [getElem!_pos c.pts j hj']
  rw [hi']
  exact hmx'.symm

theorem isCoatom_stabilizer_of_cover {G X : Type*} [Group G] [MulAction G X] (x₀ : X)
    (hnt : ∃ g : G, g • x₀ ≠ x₀) (Hs : Subgroup G) (hHs : Hs ≤ MulAction.stabilizer G x₀)
    (reps : Set G)
    (hcov : ∀ g : G, g • x₀ ≠ x₀ → ∃ r ∈ reps, ∃ h ∈ Hs, g • x₀ = (h * r) • x₀)
    (htrans : ∀ r ∈ reps, ∀ g : G, ∃ m ∈ Subgroup.closure ((Hs : Set G) ∪ {r}), g • x₀ = m • x₀) :
    IsCoatom (MulAction.stabilizer G x₀) := by
  refine ⟨?_, fun M hM => ?_⟩
  · intro h
    obtain ⟨g, hg⟩ := hnt
    apply hg
    have : g ∈ MulAction.stabilizer G x₀ := by rw [h]; exact Subgroup.mem_top g
    exact this
  · obtain ⟨m, hmM, hmS⟩ := IsConcreteLE.exists_of_lt hM
    have hm : m • x₀ ≠ x₀ := fun h => hmS h
    obtain ⟨r, hr, h, hh, hmr⟩ := hcov m hm
    have hs : (h * r)⁻¹ * m ∈ MulAction.stabilizer G x₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hmr, inv_smul_smul]
    have hsM : (h * r)⁻¹ * m ∈ M := hM.le hs
    have h1 : h * r ∈ M := by
      have : h * r = m * ((h * r)⁻¹ * m)⁻¹ := by group
      rw [this]
      exact M.mul_mem hmM (M.inv_mem hsM)
    have hhM : h ∈ M := hM.le (hHs hh)
    have hrM : r ∈ M := by
      have : r = h⁻¹ * (h * r) := by group
      rw [this]
      exact M.mul_mem (M.inv_mem hhM) h1
    have hcl : Subgroup.closure ((Hs : Set G) ∪ {r}) ≤ M := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact hM.le (hHs hx)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hrM
    rw [Subgroup.eq_top_iff']
    intro g
    obtain ⟨m', hm', hgm'⟩ := htrans r hr g
    have hs' : m'⁻¹ * g ∈ MulAction.stabilizer G x₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hgm', inv_smul_smul]
    have h2 : m'⁻¹ * g ∈ M := hM.le hs'
    have : g = m' * (m'⁻¹ * g) := by group
    rw [this]
    exact M.mul_mem (hcl hm') h2


theorem permArr_get (c : NatCert) (w : List ℕ) {a : ℕ} (ha : a < c.pts.size) :
    (permArr c w)[a]! = applyW c w a := by
  unfold permArr
  rw [getElem!_pos _ a (by simpa using ha)]
  simp

theorem hpOf_get (inp : Input) (c₁ : NatCert) {s : ℕ} (hs : s < inp.stab.length) :
    (hpOf inp c₁)[s]! = permArr c₁ (inp.stab[s]!) := by
  unfold hpOf
  simp [hs]

theorem hpOf_size (inp : Input) (c₁ : NatCert) : (hpOf inp c₁).size = inp.stab.length := by
  simp [hpOf]


theorem coatom_of_checks {G X : Type*} [Group G] [MulAction G X]
    (inp : Input) (x₀ : X) (gens : ℕ → G)
    (hgen : Subgroup.closure (gens '' {k | k < 8}) = ⊤)
    (dec : ℕ → X) (hroot : dec (encode (wordArr inp.base)) = x₀)
    (hact : ∀ k < 8, ∀ a, dec (actOf (colsInvArr inp.sigma) k a) = gens k • dec a)
    (hnt : ∃ g : G, g • x₀ ≠ x₀) (hcheck : primCheck inp = true) :
    IsCoatom (MulAction.stabilizer G x₀) := by
  classical
  unfold primCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨hσ, -⟩, h1⟩, -⟩, hst⟩, hor⟩, htr⟩ := hcheck
  set c₁ := stage1 inp with hc₁
  set hp := hpOf inp c₁ with hhp
  set orbs := orbitSearch (hAct hp) hp.size c₁.pts.size with horbs
  clear_value orbs hp c₁
  simp only [okStage1, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨hc, -⟩ := h1
  simp only [okStab, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hst
  simp only [okOrbs, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hor
  obtain ⟨hor1, hor2⟩ := hor
  simp only [okTrans, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at htr
  have hNpos : 0 < c₁.pts.size := natCertOK_pos hc
  set N := c₁.pts.size with hN
  set d : ℕ → X := fun i => dec c₁.pts[i]! with hd
  have hd0 : d 0 = x₀ := by
    simp only [hd]
    rw [natCertOK_root hc]
    exact hroot
  have hword : ∀ w : List ℕ, (∀ k ∈ w, k < 8) → ∀ i < N,
      applyW c₁ w i < N ∧ d (applyW c₁ w i) = wordElem gens w • d i :=
    fun w hw => word_spec hc (fun k hk a _ => hact k hk a) w hw
  have hα : ∀ g : G, ∃ i < N, d i = g • x₀ := by
    intro g
    have h' := orbit_of_natCertOK hc (dec := dec) (gens := gens) (fun k hk a _ => hact k hk a)
    have hmem : g • dec (encode (wordArr inp.base)) ∈ MulAction.orbit
        (Subgroup.closure (gens '' {k | k < 8})) (dec (encode (wordArr inp.base))) :=
      ⟨⟨g, by rw [hgen]; exact Subgroup.mem_top g⟩, rfl⟩
    rw [h'] at hmem
    obtain ⟨i, hi, hie⟩ := hmem
    refine ⟨i, hi, ?_⟩
    rw [← hroot]
    exact hie
  have hp_size : hp.size = inp.stab.length := by rw [hhp]; exact hpOf_size inp c₁
  have hp_get : ∀ s < inp.stab.length, ∀ a < N, (hp[s]!)[a]! = applyW c₁ (inp.stab[s]!) a := by
    intro s hs a ha
    rw [hhp, hpOf_get inp c₁ hs, permArr_get c₁ _ ha]
  have hstab_w : ∀ s < inp.stab.length, (∀ k ∈ inp.stab[s]!, k < 8) ∧
      applyW c₁ (inp.stab[s]!) 0 = 0 := by
    intro s hs
    apply hst
    rw [getElem!_pos inp.stab s hs]
    exact List.getElem_mem hs
  set hgens : ℕ → G := fun s => wordElem gens (inp.stab[s]!) with hhgens
  have hact₂ : ∀ s < hp.size, ∀ a < N, d (hAct hp s a) = hgens s • d a := by
    intro s hs a ha
    have hs' : s < inp.stab.length := hp_size ▸ hs
    obtain ⟨hw8, -⟩ := hstab_w s hs'
    have := (hword _ hw8 a ha).2
    unfold hAct
    rw [hp_get s hs' a ha]
    exact this
  let H' : Subgroup G := Subgroup.closure (hgens '' {s | s < hp.size})
  have hH'le : H' ≤ MulAction.stabilizer G x₀ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    have hs' : s < inp.stab.length := hp_size ▸ hs
    obtain ⟨hw8, h0⟩ := hstab_w s hs'
    have := (hword _ hw8 0 hNpos).2
    rw [h0, hd0] at this
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact this.symm
  have hcover : ∀ i < N, ∃ t ∈ orbs, ∃ h ∈ H', d i = h • d t.1 := by
    intro i hi
    have hmem : i ∈ List.range N := List.mem_range.2 hi
    rw [← hor2] at hmem
    have hmem' := (List.mergeSort_perm _ _).mem_iff.1 hmem
    obtain ⟨t, ht, hit⟩ := List.mem_flatMap.1 hmem'
    obtain ⟨m, hm, hmx⟩ := orbit_mem_of_natCertOK (hor1 t ht) hact₂ hit
    exact ⟨t, ht, m, hm, hmx⟩
  have hrep : ∀ t ∈ orbs, t.1 ≠ 0 → (∀ k ∈ pathWord c₁ N t.1, k < 8) ∧
      applyW c₁ (pathWord c₁ N t.1) 0 = t.1 ∧ ∀ i < N, ∃ m ∈ Subgroup.closure
        ((H' : Set G) ∪ {wordElem gens (pathWord c₁ N t.1)}), d i = m • d 0 := by
    intro t ht ht0
    have hchk := (htr t ht).resolve_left ht0
    simp only [checkRep, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨hw8, happ⟩, hnat⟩, hsort⟩ := hchk
    set w := pathWord c₁ N t.1 with hw
    set rp := permArr c₁ w with hrp
    set c₃ := natBfs (repAct hp rp) (hp.size + 1) 0 N with hc₃
    clear_value c₃
    refine ⟨hw8, happ, ?_⟩
    set gs₃ : ℕ → G := fun s => if s < hp.size then hgens s else wordElem gens w with hgs₃
    have hact₃ : ∀ k < hp.size + 1, ∀ a < N, d (repAct hp rp k a) = gs₃ k • d a := by
      intro k hk a ha
      by_cases hkp : k < hp.size
      · simp only [repAct, hkp, ite_true, gs₃]
        exact hact₂ k hkp a ha
      · simp only [repAct, hkp, ite_false, gs₃]
        rw [hrp, permArr_get c₁ w ha]
        exact (hword w hw8 a ha).2
    intro i hi
    have hmem : i ∈ List.range N := List.mem_range.2 hi
    rw [← hsort] at hmem
    have hmem' := (List.mergeSort_perm _ _).mem_iff.1 hmem
    obtain ⟨m, hm, hmx⟩ := orbit_mem_of_natCertOK hnat hact₃ hmem'
    refine ⟨m, ?_, hmx⟩
    refine Subgroup.closure_mono ?_ hm
    rintro _ ⟨k, hk, rfl⟩
    by_cases hkp : k < hp.size
    · left
      simp only [gs₃, hkp, ite_true]
      exact Subgroup.subset_closure ⟨k, hkp, rfl⟩
    · right
      simp only [gs₃, hkp, ite_false]
      rfl
  refine isCoatom_stabilizer_of_cover x₀ hnt H' hH'le
    {g | ∃ t ∈ orbs, t.1 ≠ 0 ∧ g = wordElem gens (pathWord c₁ N t.1)} ?_ ?_
  · intro g hg
    obtain ⟨i, hi, hie⟩ := hα g
    obtain ⟨t, ht, h, hh, hdi⟩ := hcover i hi
    by_cases ht0 : t.1 = 0
    · exfalso
      apply hg
      have h1 : h • x₀ = x₀ := hH'le hh
      rw [← hie, hdi, ht0, hd0, h1]
    · obtain ⟨hw8, hwa, -⟩ := hrep t ht ht0
      refine ⟨wordElem gens (pathWord c₁ N t.1), ⟨t, ht, ht0, rfl⟩, h, hh, ?_⟩
      have h1 := (hword _ hw8 0 hNpos).2
      rw [hwa, hd0] at h1
      rw [← hie, hdi, h1, mul_smul]
  · rintro r ⟨t, ht, ht0, rfl⟩ g
    obtain ⟨-, -, hall⟩ := hrep t ht ht0
    obtain ⟨i, hi, hie⟩ := hα g
    obtain ⟨m, hm, hmx⟩ := hall i hi
    exact ⟨m, hm, by rw [← hie, hmx, hd0]⟩

end Stage


end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert
