module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClLam4Kill
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClLam4Move
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClTwoMove

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.Quasithin CFSG.AGLEmbedding CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique


theorem eightTenNodeColourFourLam4SmallMove : EightTenNodeColourFourLam4SmallMove := by
  intro G _ _ X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hunm hcnt hiff' hT hfix hnoD hmv
  classical
  exfalso
  obtain ⟨hSL, hA', hLs, hpS, hkerP, hsh⟩ := theta_node_data hX hA hL hm e hNS
  obtain ⟨π, hπ, hkerπ, hAd, hequiv, hker⟩ := hNS
  have hS2 : IsPGroup 2 S := hA'.twoRadical.isPGroup
  have hP := pre_of_theta hS2 (le_sup_right : S ≤ L ⊔ S) θ hsh
  set W : Subgroup (Perm (Fin m)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  set Sstar : Subgroup (Perm (Fin m)) := (S.subgroupOf (L ⊔ S)).map θ with hSstar
  obtain ⟨hσ1, hσ2, hg, hc, hcol, hdbl⟩ := hbd
  have hbd' : BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c := ⟨hσ1, hσ2, hg, hc, hcol, hdbl⟩
  have hAJ : A ≤ thompsonJ S :=
    le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hAm
  have hEW : (A.subgroupOf (L ⊔ S)).map θ ≤ W := Subgroup.map_mono (Subgroup.comap_mono hAJ)
  have hJS : thompsonJ S ≤ S := iSup_le fun A => iSup_le fun hA => hA.1
  have hWS : W ≤ Sstar := Subgroup.map_mono (Subgroup.comap_mono hJS)
  have hiffP : ∀ y, Classif.partner hP.twoGroup y = y ↔ c y = true := by
    intro y
    rw [← hiff' y]
    constructor
    · intro h z hz1 hz2
      have := Classif.partner_eq_of_swap_mem hP.twoGroup hz1 hz2
      rw [h] at this
      exact hz1 this
    · intro h
      by_contra hne
      obtain ⟨z, hz1, hz2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
      exact h z hz1 hz2
  have hex : ∃ z, Classif.partner hP.twoGroup z = z := by
    obtain ⟨z, hz⟩ := hunm
    refine ⟨z, ?_⟩
    by_contra hne
    obtain ⟨y, hy1, hy2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
    exact hz y hy1 hy2
  have hsw : ∀ y, swap y (σ y) ∉ W ↔ c y = true := by
    intro y
    constructor
    · intro h
      exact (hcol y).2 fun h' => h (hEW h')
    · intro h hmem
      exact (hiff' y).2 h (σ y) (Ne.symm (hσ1 y)) hmem
  have hWsw : ∀ y, c y = false → swap y (σ y) ∈ W := by
    intro y hy
    by_contra h
    have := (hsw y).1 h
    rw [hy] at this; exact absurd this (by simp)
  obtain ⟨z, hz⟩ := Finset.card_pos.1 (by omega : 0 < (Finset.univ.filter fun y : Fin m => c y = true).card)
  have hcz : c z = true := by simpa using hz
  have hother : ∀ y' : Fin m, ∃ w, c w = true ∧ w ≠ y' ∧ w ≠ σ y' := by
    intro y'
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ.filter fun w : Fin m => c w = true) ⊆ {y', σ y'} := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h1 : w = y'
      · exact Or.inl h1
      · exact Or.inr (hno w hw h1)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_le_two (a := y') (b := σ y')
    omega
  obtain ⟨y, hcy, hyz, hyσz⟩ := hother z
  have hΛset := true_class_of_four σ hσ1 hσ2 c hc hT hcz hcy hyz hyσz
  have hnoDW : ∀ z y : Fin m, c z = true → c y = true → y ≠ z → y ≠ σ z →
      swap z y * swap (σ z) (σ y) ∉ W := fun z y h1 h2 h3 h4 hmem => hnoD z y h1 h2 h3 h4 (hWS hmem)
  have hle : W ≤ pairPres σ hσ1 hσ2 :=
    le_trans hP.sup (iSup_le fun i =>
      hP.le_pairPres_of_blockData_four (i₀ := ⟨A, hAm⟩) hbd' hiffP hT hcz hcy hyz hyσz hnoDW i)
  have hD : ∀ x y, y ≠ x → y ≠ σ x → swap x (σ x) ∉ W → swap y (σ y) ∉ W →
      swap x (σ x) * swap y (σ y) ∈ W := by
    intro x y hyx hyσ hx' hy'
    have hcx := (hsw x).1 hx'
    have hcy := (hsw y).1 hy'
    exact hEW (hdbl (Subgroup.subset_closure ⟨x, y, hyx, hyσ, hcy.trans hcx.symm, rfl⟩))
  have hflip : ∀ y, ∃ w ∈ W, w y = σ y := by
    intro y
    by_cases hy : c y = false
    · exact ⟨_, hWsw y hy, swap_apply_left _ _⟩
    · have hyt : c y = true := by simpa using hy
      obtain ⟨z', hz', hzy, hzσ⟩ := hother y
      have hz'' : swap y (σ y) * swap z' (σ z') ∈ W :=
        hD y z' hzy hzσ ((hsw y).2 hyt) ((hsw z').2 hz')
      refine ⟨_, hz'', ?_⟩
      have hyz' : y ≠ z' := hzy.symm
      have hyσz' : y ≠ σ z' := fun h => hzσ (by rw [h, hσ2])
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hyz' hyσz', swap_apply_left]
  have hσcomm : ∀ h ∈ Subgroup.normalizer (W : Set (Perm (Fin m))), ∀ y, h (σ y) = σ (h y) :=
    fun h hh y => comm_sigma_of_normalizer hle hflip hh y
  let U : Subgroup (Perm (Fin m)) := pairPres σ hσ1 hσ2 ⊓ alternatingGroup (Fin m)
  have hUN : U ≤ Subgroup.normalizer (W : Set (Perm (Fin m))) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have h1 := pairPres_comm hu.1 (hle hw)
      have : u * w * u⁻¹ = w := by rw [h1]; group
      rw [this]; exact hw
    · intro hw'
      have h1 := pairPres_comm ((pairPres σ hσ1 hσ2).inv_mem hu.1) (hle hw')
      have : u⁻¹ * (u * w * u⁻¹) * u = w := by group
      rw [← this, h1]
      simpa using hw'
  have hU2 : IsPGroup 2 U := by
    rintro ⟨u, hu⟩
    refine ⟨1, Subtype.ext ?_⟩
    show u ^ 2 ^ 1 = 1
    simpa [pow_two] using sq_eq_one_of_pair hσ1 hσ2 (g := u) hu.1
  have hUr : U ≤ θ.range := by
    intro u hu
    obtain ⟨l, hl⟩ := hAd u hu.2
    exact ⟨⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩, hl⟩
  have hUnorm : ∀ h ∈ Subgroup.normalizer (W : Set (Perm (Fin m))), h ∈ θ.range →
      ∀ u ∈ U, h * u * h⁻¹ ∈ U := by
    intro h hh _ u hu
    exact ⟨conj_mem_pairPres (hσcomm h hh) hu.1, Subgroup.Normal.conj_mem inferInstance u hu.2 h⟩
  have hUS : U ≤ Sstar :=
    le_theta_S_of_normal_two hA' (le_sup_right : S ≤ L ⊔ S) θ hθS W rfl U hUN hU2 hUr hUnorm
  have hU : ∀ g ∈ pairPres σ hσ1 hσ2, g ∈ alternatingGroup (Fin m) → g ∈ Sstar :=
    fun g hg ha => hUS ⟨hg, ha⟩
  have hnormW : ∀ s ∈ Sstar, ∀ w ∈ W, s * w * s⁻¹ ∈ W := by
    rintro _ ⟨s', hs', rfl⟩ w hw
    have hh := theta_mem_normalizer_W θ s' (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.1 hs'))
    exact ((Subgroup.mem_normalizer_iff.1 hh) w).1 hw
  obtain ⟨p, hp⟩ : ∃ p : Fin m, c p = false := by
    by_contra h
    push Not at h
    have hall : (Finset.univ.filter fun y : Fin m => c y = true) = Finset.univ := by
      ext y; simp [h y]
    have := Finset.card_univ (α := Fin m)
    rw [← hall, hT] at this
    simp only [Fintype.card_fin] at this
    omega
  have htsw : ∀ y, c y = true → swap y (σ y) ∈ Sstar := by
    intro y hy
    have hpp : swap p (σ p) ∈ Sstar := hWS (hWsw p hp)
    have hpair : swap p (σ p) * swap y (σ y) ∈ Sstar := by
      refine hU _ ((pairPres σ hσ1 hσ2).mul_mem (swap_mem_pairPres hσ1 hσ2 p)
        (swap_mem_pairPres hσ1 hσ2 y)) ?_
      rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (hσ1 p).symm, sign_swap (hσ1 y).symm]
      decide
    have := Sstar.mul_mem hpp hpair
    rwa [← mul_assoc, swap_mul_self, one_mul] at this
  have hFix : ∀ s ∈ Sstar, ∀ y, c y = false → s y = y ∨ s y = σ y := by
    rintro _ ⟨s', hs', rfl⟩ y hy
    have hs'S : (s' : G) ∈ S := Subgroup.mem_subgroupOf.1 hs'
    have hpσ : Classif.partner hP.twoGroup y = σ y :=
      (Classif.partner_eq_of_swap_mem hP.twoGroup (hσ1 y).symm (hWsw y hy)).symm.symm
    have hne : Classif.partner hP.twoGroup y ≠ y := by rw [hpσ]; exact hσ1 y
    have hiso : IsIsoPair W y (σ y) := by
      refine ⟨(hσ1 y).symm, hWsw y hy, fun w hw => ?_⟩
      have := hP.blockTrivial_of_unmatched hex w hw y hne
      rwa [hpσ] at this
    exact hfix y (σ y) hiso s' hs'S
  have hD1 : swap z (σ z) * swap y (σ y) ∈ W := hD z y hyz hyσz ((hsw z).2 hcz) ((hsw y).2 hcy)
  obtain ⟨z', y'', hz', hy'', h1, h2, hmem⟩ :=
    exists_D_of_move σ hσ1 hσ2 c hc Sstar W hWS hle hWsw hnormW z y hcz hcy hyz hyσz hD1 hΛset htsw
      hFix hmv
  exact hnoD z' y'' hz' hy'' h1 h2 hmem

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
