module

public import CFSG.Fischer.Uniq.PolarFacts

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X}

theorem LocalPoints.mem_muSet_iff_perp {f d c : X} (Lf : LocalPoints polarModel E f)
    (hdf : d ∈ LocalClass E f) (hcf : c ∈ LocalClass E f) (hcd : c * d ≠ d * c)
    (g : LocalClass E f) :
    (g : X) ∈ muSet E d c ↔ perp (Lf.χ g) (Lf.χ ⟨d, hdf⟩) ∧ perp (Lf.χ g) (Lf.χ ⟨c, hcf⟩) := by
  have hab : ¬ perp (Lf.χ ⟨c, hcf⟩) (Lf.χ ⟨d, hdf⟩) := fun h =>
    hcd ((Lf.comm ⟨c, hcf⟩ ⟨d, hdf⟩).2 h)
  constructor
  · rintro ⟨hgd, hgc⟩
    exact ⟨(Lf.comm g ⟨d, hdf⟩).1 hgd.2.2, (Lf.comm g ⟨c, hcf⟩).1 hgc.2.2⟩
  · rintro ⟨h1, h2⟩
    have hgd : (g : X) ≠ d := by
      intro h
      have : g = ⟨d, hdf⟩ := Subtype.ext h
      rw [this] at h2
      exact hab ((Lf.comm ⟨c, hcf⟩ ⟨d, hdf⟩).1 ((Lf.comm ⟨d, hdf⟩ ⟨c, hcf⟩).2 h2).symm)
    have hgc : (g : X) ≠ c := by
      intro h
      have : g = ⟨c, hcf⟩ := Subtype.ext h
      rw [this] at h1
      exact hab h1
    exact ⟨⟨g.2.1, hgd, (Lf.comm g ⟨d, hdf⟩).2 h1⟩, ⟨g.2.1, hgc, (Lf.comm g ⟨c, hcf⟩).2 h2⟩⟩

theorem Pair.isClosedHyperoval_muImg (hPF : PolarFacts) (hP : Pair X E) {d c : X} (hd : d ∈ E)
    (hc : c ∈ E) (hcd : c * d ≠ d * c) (L : LocalPoints polarModel E d)
    (hloc : ∀ f ∈ E, Nonempty (LocalPoints polarModel E f)) :
    IsClosedHyperoval (L.muImg c) := by
  set O := L.muImg c with hO
  have hsub : ∀ x ∈ O, tvP x '' O ⊆ O := by
    rintro x ⟨s, hs, rfl⟩ _ ⟨y, ⟨s', hs', rfl⟩, rfl⟩
    have hm : (s : X) * s' * s ∈ muSet E d c := Pair.mul_mul_mem_muSet hP ⟨s.2, hs⟩ ⟨s'.2, hs'⟩
    exact ⟨⟨_, hm.1⟩, hm.2, L.tau s s' hm.1⟩
  refine ⟨fun Λ hΛ => ?_, fun x hx => le_antisymm (hsub x hx) fun y hy =>
    ⟨tvP x y, hsub x hx ⟨y, hy, rfl⟩, tvP_tvP x y⟩⟩
  by_cases hne : (Λ ∩ O).Nonempty
  swap
  · left
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty]
  right
  obtain ⟨p, hpΛ, hpO⟩ := hne
  set f : LocalClass E d := L.χ.symm p with hf
  have hfp : L.χ f = p := Equiv.apply_symm_apply _ _
  have hfc : (f : X) ∈ LocalClass E c := L.mem_muImg.1 hpO
  have hdf : d ∈ LocalClass E f := ⟨hd, f.2.2.1.symm, f.2.2.2.symm⟩
  have hcf : c ∈ LocalClass E f := ⟨hc, hfc.2.1.symm, hfc.2.2.symm⟩
  obtain ⟨Lf⟩ := hloc f f.2.1
  set a := Lf.χ ⟨d, hdf⟩
  set b := Lf.χ ⟨c, hcf⟩
  have hab : ¬ perp a b := fun h => hcd ((Lf.comm ⟨d, hdf⟩ ⟨c, hcf⟩).2 h).symm
  have hcomm : ∀ g : LocalClass E d, perp p (L.χ g) ↔ (f : X) * g = g * f := by
    intro g
    rw [← hfp]
    exact (L.comm f g).symm
  have hstar : ∀ Λ', IsLine Λ' → p ∈ Λ' → ∀ z ∈ Λ' ∩ O, z ≠ p →
      ((L.χ.symm z : X) ∈ LocalClass E f ∧ (L.χ.symm z : X) ∈ muSet E d c) := by
    rintro Λ' hΛ' hpΛ' z ⟨hzΛ, hzO⟩ hzp
    have hperp : perp p z := hPF.line_perp Λ' hΛ' p hpΛ' z hzΛ
    have h1 := (hcomm (L.χ.symm z)).1 (by rw [Equiv.apply_symm_apply]; exact hperp)
    refine ⟨⟨(L.χ.symm z).2.1, fun h => hzp ?_, h1.symm⟩, ⟨(L.χ.symm z).2, L.mem_muImg.1 hzO⟩⟩
    have : L.χ.symm z = f := Subtype.ext h
    rw [← hfp, ← this, Equiv.apply_symm_apply]
  have hmost : ∀ Λ', IsLine Λ' → p ∈ Λ' → ∀ z₁ ∈ Λ' ∩ O, ∀ z₂ ∈ Λ' ∩ O, z₁ ≠ p → z₂ ≠ p →
      z₁ = z₂ := by
    intro Λ' hΛ' hpΛ' z₁ hz₁ z₂ hz₂ hz₁p hz₂p
    by_contra h12
    obtain ⟨hg₁f, hg₁mu⟩ := hstar Λ' hΛ' hpΛ' z₁ hz₁ hz₁p
    obtain ⟨hg₂f, hg₂mu⟩ := hstar Λ' hΛ' hpΛ' z₂ hz₂ hz₂p
    have hpz₁ : perp p z₁ := hPF.line_perp Λ' hΛ' p hpΛ' z₁ hz₁.1
    have hpz₂ : perp p z₂ := hPF.line_perp Λ' hΛ' p hpΛ' z₂ hz₂.1
    have htw := hPF.twins_of_line p z₁ z₂ hpz₁ hpz₂ hz₁p hz₂p h12
      ⟨Λ', hΛ', hpΛ', hz₁.1, hz₂.1⟩
    set g₁ : LocalClass E f := ⟨_, hg₁f⟩
    set g₂ : LocalClass E f := ⟨_, hg₂f⟩
    have hx := (Lf.mem_muSet_iff_perp hdf hcf hcd g₁).1 hg₁mu
    have hy := (Lf.mem_muSet_iff_perp hdf hcf hcd g₂).1 hg₂mu
    have hxy : Lf.χ g₁ ≠ Lf.χ g₂ := by
      intro h
      apply h12
      have := congrArg Subtype.val (Lf.χ.injective h)
      have h' : L.χ.symm z₁ = L.χ.symm z₂ := Subtype.ext this
      exact L.χ.symm.injective h'
    have hz₁₂ : perp z₁ z₂ := hPF.line_perp Λ' hΛ' z₁ hz₁.1 z₂ hz₂.1
    have hg₁₂ : (g₁ : X) * g₂ = g₂ * g₁ := by
      have := (L.comm (L.χ.symm z₁) (L.χ.symm z₂)).2
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact this hz₁₂
    obtain ⟨w, ⟨hwa, hwb⟩, hw⟩ :=
      hPF.twinFree a b hab (Lf.χ g₁) (Lf.χ g₂) hx hy hxy ((Lf.comm g₁ g₂).1 hg₁₂)
    set h : LocalClass E f := Lf.χ.symm w
    have hhw : Lf.χ h = w := Equiv.apply_symm_apply _ _
    have hhmu : (h : X) ∈ muSet E d c :=
      (Lf.mem_muSet_iff_perp hdf hcf hcd h).2 (by rw [hhw]; exact ⟨hwa, hwb⟩)
    set h' : LocalClass E d := ⟨h, hhmu.1⟩
    have hpw : perp p (L.χ h') := (hcomm h').2 h.2.2.2.symm
    have hwp : L.χ h' ≠ p := by
      intro e
      have : h' = f := by rw [← hfp] at e; exact L.χ.injective e
      exact h.2.2.1 (congrArg Subtype.val this)
    have htw' := htw (L.χ h') hpw hwp
    have e₁ : perp (L.χ h') z₁ ↔ (h : X) * g₁ = g₁ * h := by
      have := L.comm h' (L.χ.symm z₁)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    have e₂ : perp (L.χ h') z₂ ↔ (h : X) * g₂ = g₂ * h := by
      have := L.comm h' (L.χ.symm z₂)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    have f₁ : perp w (Lf.χ g₁) ↔ (h : X) * g₁ = g₁ * h := by
      rw [← hhw]; exact (Lf.comm h g₁).symm
    have f₂ : perp w (Lf.χ g₂) ↔ (h : X) * g₂ = g₂ * h := by
      rw [← hhw]; exact (Lf.comm h g₂).symm
    exact hw (by rw [f₁, f₂, ← e₁, ← e₂]; exact htw')
  set T : Set (Fin 693) :=
    {z | (L.χ.symm z : X) ∈ LocalClass E f ∧ (L.χ.symm z : X) ∈ muSet E d c}
  have hTO : ∀ z ∈ T, z ∈ O ∧ z ≠ p ∧ perp p z := by
    rintro z ⟨hzf, hzmu⟩
    refine ⟨L.mem_muImg.2 hzmu.2, fun hzp => hzf.2.1 ?_, ?_⟩
    · rw [hzp]
    · rw [← Equiv.apply_symm_apply L.χ z]
      exact (hcomm _).2 hzf.2.2.symm
  have hTcard : T.ncard = 45 := by
    rw [← hPF.ncard_perp_perp a b hab]
    refine Set.ncard_congr (fun z hz => Lf.χ ⟨L.χ.symm z, hz.1⟩) (fun z hz => ?_)
      (fun z z' hz hz' e => ?_) (fun w hw => ?_)
    · exact (Lf.mem_muSet_iff_perp hdf hcf hcd _).1 hz.2
    · have := congrArg Subtype.val (Lf.χ.injective e)
      exact L.χ.symm.injective (Subtype.ext this)
    · set g := Lf.χ.symm w with hg
      have hgmu : (g : X) ∈ muSet E d c :=
        (Lf.mem_muSet_iff_perp hdf hcf hcd g).2 (by rw [hg, Equiv.apply_symm_apply]; exact hw)
      have hz : ((L.χ.symm (L.χ ⟨g, hgmu.1⟩)) : X) = g := by rw [Equiv.symm_apply_apply]
      refine ⟨L.χ ⟨g, hgmu.1⟩, ⟨by rw [hz]; exact g.2, by rw [hz]; exact hgmu⟩, ?_⟩
      calc Lf.χ ⟨_, _⟩ = Lf.χ g := congrArg Lf.χ (Subtype.ext hz)
        _ = w := Equiv.apply_symm_apply _ _
  have hinj : Set.InjOn (fun z => lineThru p z) T := by
    intro z hz z' hz' e
    simp only at e
    have hΛz := hPF.isLine_lineThru p z (hTO z hz).2.1.symm (hTO z hz).2.2
    exact hmost (lineThru p z) hΛz (hPF.left_mem_lineThru p z) z
      ⟨hPF.right_mem_lineThru p z, (hTO z hz).1⟩ z'
      ⟨by rw [e]; exact hPF.right_mem_lineThru p z', (hTO z' hz').1⟩ (hTO z hz).2.1
      (hTO z' hz').2.1
  have himage : (fun z => lineThru p z) '' T = {Λ' | IsLine Λ' ∧ p ∈ Λ'} := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨hPF.isLine_lineThru p z (hTO z hz).2.1.symm (hTO z hz).2.2,
        hPF.left_mem_lineThru p z⟩
    · rw [hinj.ncard_image, hTcard, hPF.ncard_lines_through p]
  have hΛmem : Λ ∈ (fun z => lineThru p z) '' T := by
    rw [himage]; exact ⟨hΛ, hpΛ⟩
  obtain ⟨q, hqT, hqΛ⟩ := hΛmem
  simp only at hqΛ
  obtain ⟨hqO, hqp, -⟩ := hTO q hqT
  have hqΛ' : q ∈ Λ := by rw [← hqΛ]; exact hPF.right_mem_lineThru p q
  have hΛO : Λ ∩ O = {p, q} := by
    ext z
    constructor
    · intro hz
      by_cases hzp : z = p
      · exact Or.inl hzp
      · exact Or.inr (hmost Λ hΛ hpΛ z hz q ⟨hqΛ', hqO⟩ hzp hqp)
    · rintro (rfl | rfl)
      · exact ⟨hpΛ, hpO⟩
      · exact ⟨hqΛ', hqO⟩
  rw [hΛO, Set.ncard_pair hqp.symm]

end CFSG.Fischer
