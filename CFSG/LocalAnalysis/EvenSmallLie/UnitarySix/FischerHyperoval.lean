module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerPoints
public import CFSG.Fischer.Polar.Facts
public import Certificates.Certificate3146

public section

namespace CFSG.EvenSmallLie.UnitarySix.Fischer

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

theorem domOK_eq :
    domOK 1 = true ∧ domOK 2 = true ∧ domOK 3 = true :=
  Certificates.certificate3146

theorem exists_perp_of_notMem_hypRoot
    (i : Fin 3) {q : Fin 693}
    (hq : q ∉ hypRoot i) :
    ∃ x ∈ hypRoot i, perp q x := by
  have hd : domOK (i.val + 1) = true := by
    fin_cases i
    exacts [domOK_eq.1, domOK_eq.2.1, domOK_eq.2.2]
  have h1 := List.all_eq_true.1 hd q.val (List.mem_range.2 q.2)
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact absurd (by rw [← flagSet_rootFlags]; exact h1) hq
  · obtain ⟨x, hx, hx'⟩ := List.any_eq_true.1 h1
    rw [Bool.and_eq_true, beq_iff_eq] at hx'
    refine ⟨⟨x, List.mem_range.1 hx⟩, by rw [← flagSet_rootFlags]; exact hx'.1, ?_⟩
    rw [← tvP_apply_eq_self_iff]
    exact Fin.ext (by rw [tvP_val]; exact hx'.2)

theorem exists_perp_of_isClosedHyperoval
    {O : Set (Fin 693)}
    (hO : IsClosedHyperoval O)
    (hne : O.Nonempty) {q : Fin 693} (hq : q ∉ O) : ∃ x ∈ O, perp q x := by
  obtain ⟨i, g, hg, rfl⟩ := polarFacts.exists_mem_hypOrbit O hO hne
  have hq' : g⁻¹ q ∉ hypRoot i := fun h => hq ⟨g⁻¹ q, h, perm_apply_inv_self g q⟩
  obtain ⟨x, hx, hpx⟩ := exists_perp_of_notMem_hypRoot i hq'
  refine ⟨g x, ⟨x, hx, rfl⟩, ?_⟩
  rw [← perp_apply_of_mem hg, perm_apply_inv_self] at hpx
  exact hpx

section Hyperoval

variable {G : Type} [Group G] {D : Set G}

theorem isClosedHyperoval_muImg_of_conj
    (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    (hD2 : ∀ x ∈ D, x * x = 1) {d c : G} (hd : d ∈ D) (hc : c ∈ D) (hcd : c * d ≠ d * c)
    (L : LocalPoints polarModel D d)
    (hloc : ∀ f ∈ D, Nonempty (LocalPoints polarModel D f)) :
    IsClosedHyperoval (L.muImg c) := by
  have hPF := polarFacts
  set O := L.muImg c with hO
  have hsub : ∀ x ∈ O, tvP x '' O ⊆ O := by
    rintro x ⟨s, hs, rfl⟩ _ ⟨y, ⟨s', hs', rfl⟩, rfl⟩
    have hm : (s : G) * s' * s ∈ muSet D d c :=
      ⟨mul_mul_mem_localClass hDinv hD2 s.2 s'.2, mul_mul_mem_localClass hDinv hD2 hs hs'⟩
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
  set f : LocalClass D d := L.χ.symm p with hf
  have hfp : L.χ f = p := Equiv.apply_symm_apply _ _
  have hfc : (f : G) ∈ LocalClass D c := L.mem_muImg.1 hpO
  have hdf : d ∈ LocalClass D f := ⟨hd, f.2.2.1.symm, f.2.2.2.symm⟩
  have hcf : c ∈ LocalClass D f := ⟨hc, hfc.2.1.symm, hfc.2.2.symm⟩
  obtain ⟨Lf⟩ := hloc f f.2.1
  set a := Lf.χ ⟨d, hdf⟩
  set b := Lf.χ ⟨c, hcf⟩
  have hab : ¬ perp a b := fun h => hcd ((Lf.comm ⟨d, hdf⟩ ⟨c, hcf⟩).2 h).symm
  have hcomm : ∀ g : LocalClass D d, perp p (L.χ g) ↔ (f : G) * g = g * f := by
    intro g
    rw [← hfp]
    exact (L.comm f g).symm
  have hstar : ∀ Λ', IsLine Λ' → p ∈ Λ' → ∀ z ∈ Λ' ∩ O, z ≠ p →
      ((L.χ.symm z : G) ∈ LocalClass D f ∧ (L.χ.symm z : G) ∈ muSet D d c) := by
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
    set g₁ : LocalClass D f := ⟨_, hg₁f⟩
    set g₂ : LocalClass D f := ⟨_, hg₂f⟩
    have hx := (Lf.mem_muSet_iff_perp hdf hcf hcd g₁).1 hg₁mu
    have hy := (Lf.mem_muSet_iff_perp hdf hcf hcd g₂).1 hg₂mu
    have hxy : Lf.χ g₁ ≠ Lf.χ g₂ := by
      intro h
      apply h12
      have := congrArg Subtype.val (Lf.χ.injective h)
      have h' : L.χ.symm z₁ = L.χ.symm z₂ := Subtype.ext this
      exact L.χ.symm.injective h'
    have hz₁₂ : perp z₁ z₂ := hPF.line_perp Λ' hΛ' z₁ hz₁.1 z₂ hz₂.1
    have hg₁₂ : (g₁ : G) * g₂ = g₂ * g₁ := by
      have := (L.comm (L.χ.symm z₁) (L.χ.symm z₂)).2
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact this hz₁₂
    obtain ⟨w, ⟨hwa, hwb⟩, hw⟩ :=
      hPF.twinFree a b hab (Lf.χ g₁) (Lf.χ g₂) hx hy hxy ((Lf.comm g₁ g₂).1 hg₁₂)
    set h : LocalClass D f := Lf.χ.symm w
    have hhw : Lf.χ h = w := Equiv.apply_symm_apply _ _
    have hhmu : (h : G) ∈ muSet D d c :=
      (Lf.mem_muSet_iff_perp hdf hcf hcd h).2 (by rw [hhw]; exact ⟨hwa, hwb⟩)
    set h' : LocalClass D d := ⟨h, hhmu.1⟩
    have hpw : perp p (L.χ h') := (hcomm h').2 h.2.2.2.symm
    have hwp : L.χ h' ≠ p := by
      intro e
      have : h' = f := by rw [← hfp] at e; exact L.χ.injective e
      exact h.2.2.1 (congrArg Subtype.val this)
    have htw' := htw (L.χ h') hpw hwp
    have e₁ : perp (L.χ h') z₁ ↔ (h : G) * g₁ = g₁ * h := by
      have := L.comm h' (L.χ.symm z₁)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    have e₂ : perp (L.χ h') z₂ ↔ (h : G) * g₂ = g₂ * h := by
      have := L.comm h' (L.χ.symm z₂)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    have f₁ : perp w (Lf.χ g₁) ↔ (h : G) * g₁ = g₁ * h := by
      rw [← hhw]; exact (Lf.comm h g₁).symm
    have f₂ : perp w (Lf.χ g₂) ↔ (h : G) * g₂ = g₂ * h := by
      rw [← hhw]; exact (Lf.comm h g₂).symm
    exact hw (by rw [f₁, f₂, ← e₁, ← e₂]; exact htw')
  set T : Set (Fin 693) :=
    {z | (L.χ.symm z : G) ∈ LocalClass D f ∧ (L.χ.symm z : G) ∈ muSet D d c}
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
      have hgmu : (g : G) ∈ muSet D d c :=
        (Lf.mem_muSet_iff_perp hdf hcf hcd g).2 (by rw [hg, Equiv.apply_symm_apply]; exact hw)
      have hz : ((L.χ.symm (L.χ ⟨g, hgmu.1⟩)) : G) = g := by rw [Equiv.symm_apply_apply]
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

end Hyperoval

theorem FischerHyp.hii
    {G : Type} [Group G] {t : G}
    {L E : Subgroup G}
    {p : L →* Equiv.Perm (Fin 693)} (h : FischerHyp t L E p) :
    ∀ b ∈ LocalClass (tClass t) t, ∀ a ∈ tClass t, a * t ≠ t * a →
      a ∈ LocalClass (tClass t) b → ∀ c ∈ LocalClass (tClass t) t,
        ∃ f ∈ LocalClass (tClass t) a ∩ LocalClass (tClass t) t, f * c = c * f := by
  intro b hb a ha hat hab c hc
  set Lt := h.localPoints
  have hO := isClosedHyperoval_muImg_of_conj (tClass_inv t)
    (fun _ hx => mul_self_of_mem_tClass h.orderOf_t hx) (self_mem_tClass t) ha hat Lt
    h.nonempty_localPoints
  have hne : (Lt.muImg a).Nonempty :=
    ⟨Lt.χ ⟨b, hb⟩, ⟨b, hb⟩, ⟨hb.1, fun e => hab.2.1 e.symm, hab.2.2.symm⟩, rfl⟩
  by_cases hcO : Lt.χ ⟨c, hc⟩ ∈ Lt.muImg a
  · obtain ⟨s, hs, hsc⟩ := hcO
    have hsc' : s = ⟨c, hc⟩ := Lt.χ.injective hsc
    have hsc'' : (s : G) = c := congrArg Subtype.val hsc'
    exact ⟨c, ⟨hsc'' ▸ hs, hc⟩, rfl⟩
  · obtain ⟨x, ⟨s, hs, rfl⟩, hpx⟩ := exists_perp_of_isClosedHyperoval hO hne hcO
    exact ⟨s, ⟨hs, s.2⟩, (Lt.comm s ⟨c, hc⟩).2 (perp_comm.1 hpx)⟩

end CFSG.EvenSmallLie.UnitarySix.Fischer
