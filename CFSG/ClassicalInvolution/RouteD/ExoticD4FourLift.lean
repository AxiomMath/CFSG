module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourInvolution
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourPair
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Lift

theorem locMk_inj_of_member (hex : ExactMembers Ω) {x : G} {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) {a b : ↥(locLayer Ω x)} (ha : (a : G) ∈ L)
    (hb : (b : G) ∈ L) (h : locMk Ω x a = locMk Ω x b) : a = b := by
  have hLY := le_centralizingLayer hL
  let e := Subgroup.subgroupOfEquivOfLe hLY
  have hO : classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x)) = ⊥ := by
    have h1 : Subgroup.map e.toMonoidHom
        (classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x))) =
        classicalInvolutionOddCore ↥L := CFSG.ComponentClassification.OddCore.equiv_invariant e
    rw [hex L hL.1] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hinf := Generic.inf_oddCore_eq_bot hO
  have hmem : a⁻¹ * b ∈ (L.subgroupOf (locLayer Ω x)) ⊓
      classicalInvolutionOddCore ↥(locLayer Ω x) :=
    ⟨(L.subgroupOf (locLayer Ω x)).mul_mem ((L.subgroupOf (locLayer Ω x)).inv_mem
      (Subgroup.mem_subgroupOf.mpr ha)) (Subgroup.mem_subgroupOf.mpr hb), QuotientGroup.eq.mp h⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

omit [Finite G] in
theorem exists_lift_of_corr {w : G} {D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)}
    {i : Fin D.card} {T : Subgroup G}
    {R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hR : Corr Ω w D i T R) {u : (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hu : u ∈ R) : ∃ (y : G) (hy : y ∈ locLayer Ω w), y ∈ T ∧
      locMk Ω w ⟨y, hy⟩ = D.hom i u := by
  have hmem : D.hom i u ∈ locImg Ω w T := hR.2.2 ▸ ⟨u, hu, rfl⟩
  obtain ⟨y', hy', hyu⟩ := hmem
  exact ⟨y', y'.2, Subgroup.mem_subgroupOf.mp hy', hyu⟩

omit [Finite G] in
theorem elem_central_of_lift {w : G} {D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)}
    {i : Fin D.card} {T : Subgroup G}
    {R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hR : Corr Ω w D i T R) {y : G} (hy : y ∈ locLayer Ω w)
    {u : (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hu : D.hom i u = locMk Ω w ⟨y, hy⟩) (hc : ∀ g ∈ T, y * g = g * y) :
    ∀ r ∈ R, u * r = r * u := by
  have hRperf : ⁅R, R⁆ = R := le_antisymm
    (Subgroup.commutator_le.mpr fun _ hx _ hy =>
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy))
    (hperf R hR.2.1)
  have hcent : u ∈ Subgroup.centralizer (R : Set _) :=
    Models.Transfer.mem_centralizer_of_map (D.ker_le_center i) hRperf (g := u) (by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [← hR.2.2] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      rw [hu]
      show locMk Ω w g * locMk Ω w ⟨y, hy⟩ = locMk Ω w ⟨y, hy⟩ * locMk Ω w g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (hc g (Subgroup.mem_subgroupOf.mp hg)).symm)
  intro r hr
  exact (Subgroup.mem_centralizer_iff.mp hcent r hr).symm

omit [Finite G] in
theorem mul_self_of_isClassicalMember {L : Subgroup G} {z₀ : G} (h : IsClassicalMember p f L z₀) :
    z₀ * z₀ = 1 := by
  have h3 : z₀ ^ 2 = 1 := by
    rw [← h.orderOf_eq_two]
    exact pow_orderOf_eq_one _
  simpa [pow_two] using h3

theorem eq_one_of_mem_oddCore_of_sq {Y : Type} [Group Y] [Finite Y] {g : Y}
    (hg : g ∈ classicalInvolutionOddCore Y) (h : g * g = 1) : g = 1 := by
  have hord : orderOf (⟨g, hg⟩ : classicalInvolutionOddCore Y) = 1 := by
    have h2 : orderOf (⟨g, hg⟩ : classicalInvolutionOddCore Y) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using h))
    have h3 := orderOf_dvd_natCard (⟨g, hg⟩ : classicalInvolutionOddCore Y)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h4 | h4
    · exact h4
    · rw [h4] at h3
      exact absurd (even_iff_two_dvd.mpr h3)
        (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp hord)

omit [Finite G] in
theorem le_iSup_of_model_generates (hΩ : InClass p f Ω) {w : G} (hP1 : LocalOddCentral Ω {w})
    {D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)} {i : Fin D.card} {ι : Type}
    (T : ι → Subgroup G)
    (R : ι → Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K)
    (hT : ∀ a, Corr Ω w D i (T a) (R a)) (hgen : (⨆ a, R a) = ⊤) {L : Subgroup G}
    (hL : L ∈ compMembers Ω w D i) : L ≤ ⨆ a, T a := by
  classical
  set Y := locLayer Ω w with hY
  set B : Subgroup ↥Y := ⨆ a, (T a).subgroupOf Y with hB
  have hmapB : B.map (locMk Ω w) = ⨆ a, locImg Ω w (T a) := by
    rw [hB, Subgroup.map_iSup]
    rfl
  have hrange : (D.hom i).range = ⨆ a, locImg Ω w (T a) := by
    have : ∀ a, locImg Ω w (T a) = (R a).map (D.hom i) := fun a => (hT a).2.2
    simp only [this]
    rw [← Subgroup.map_iSup, hgen, MonoidHom.range_eq_map]
  have hLB : L.subgroupOf Y ≤ B ⊔ classicalInvolutionOddCore ↥Y := by
    intro a ha
    have h1 : locMk Ω w a ∈ (D.hom i).range := hL.2 ⟨a, ha, rfl⟩
    rw [hrange, ← hmapB] at h1
    have h2 := Subgroup.comap_map_eq (locMk Ω w) B ▸ (show a ∈ Subgroup.comap (locMk Ω w)
      (B.map (locMk Ω w)) from h1)
    rw [QuotientGroup.ker_mk'] at h2
    exact h2
  have hBle := le_of_perfect_of_le_sup_center hP1 (subgroupOf_le_commutator hΩ hL.1) hLB
  intro l hl
  have hlY : l ∈ Y := le_centralizingLayer hL.1 hl
  have h3 : (⟨l, hlY⟩ : ↥Y) ∈ B := hBle (Subgroup.mem_subgroupOf.mpr hl)
  have h4 : l ∈ B.map Y.subtype := ⟨⟨l, hlY⟩, h3, rfl⟩
  rw [hB, Subgroup.map_iSup] at h4
  have hle : (⨆ a, ((T a).subgroupOf Y).map Y.subtype) ≤ ⨆ a, T a := iSup_mono fun a => by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hy
  exact hle h4

end Lift

section Main

variable [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem exists_lift_data (hnab : ∃ x y : G, x * y ≠ y * x) (S : RouteDSetup p f K z)
    (hloc : LocalShapeT p f 4 .POmegaPlus 4 (conjClass K) z) {N₀ M : Subgroup G}
    (hN₀ : N₀ ∈ conjClass K) (hM : M ∈ outerSet (conjClass K) N₀) {z₀ : G}
    (hz₀ : IsClassicalMember p f N₀ z₀) :
    ∃ (Ta Tb : Subgroup G) (ya yb : G) (P : Subgroup G) (x : G),
      Ta ∈ conjClass K ∧ Tb ∈ conjClass K ∧
      cnbhd (conjClass K) Ta = cnbhd (conjClass K) N₀ ∧
      cnbhd (conjClass K) Tb = cnbhd (conjClass K) N₀ ∧ Ta ≠ N₀ ∧ Tb ≠ N₀ ∧ Ta ≠ Tb ∧
      ya ∈ Ta ∧ yb ∈ Tb ∧ ya * ya = z₀ ∧ yb * yb = z₀ ∧
      (¬ ∀ g ∈ Ta, ya * g = g * ya) ∧ (¬ ∀ g ∈ Tb, yb * g = g * yb) ∧ ya * yb ≠ 1 ∧
      P ∈ conjClass K ∧ x ∈ P ∧ (∀ g ∈ P, g * (ya * yb) = (ya * yb) * g) ∧
      (x * z₀ * x⁻¹ * z₀⁻¹) ^ 4 = 1 ∧ x * z₀ * x⁻¹ * z₀⁻¹ ≠ 1 := by
  classical
  set Ω := conjClass K with hΩdef
  have hΩ : InClass p f Ω := S.inClass
  have hex : ExactMembers Ω := S.exact
  have hf : 0 < f := routeD_f_pos S
  have hMΩ : M ∈ Ω := hM.1.1
  obtain ⟨w, hw, hP1, D, i₁, hcard, ht, hr, hrest⟩ := exists_D4At S hloc hMΩ
  have hout := outerSet_eq_compMembers S.odd hf S.five hΩ hex hw hMΩ hP1
    (single_class_of_mem hMΩ) D ht hr hrest
  have hq4 : 4 ≤ p ^ f := by
    have := S.five
    omega
  have hperf := D.fundPerfect S.odd hq4
    (trialityD4_vacuous D (by decide : StatedLieTag.POmegaPlus ≠ .trialityD4) ht hrest) i₁
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      exact absurd h (by decide)
  let 𝒯 : Set (Subgroup G) := {T | T ∈ Ω ∧ cnbhd Ω T = cnbhd Ω N₀}
  have h𝒯 : 𝒯.ncard = 4 := ncard_twins_of_shape S hloc hN₀
  have hN₀𝒯 : N₀ ∈ 𝒯 := ⟨hN₀, rfl⟩
  have h3 : (𝒯 \ {N₀}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem hN₀𝒯, h𝒯]
  obtain ⟨T₂, T₃, T₄, h23, h24, h34, hset⟩ := Set.ncard_eq_three.mp h3
  have hT : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) → T ∈ 𝒯 ∧ T ≠ N₀ := by
    intro T hT
    have : T ∈ 𝒯 \ {N₀} := by
      rw [hset]
      rcases hT with rfl | rfl | rfl <;> simp
    exact ⟨this.1, this.2⟩
  have hcomm𝒯 : ∀ {T T' : Subgroup G}, T ∈ 𝒯 → T' ∈ 𝒯 → T ≠ T' → Commutes T T' := by
    intro T T' hT hT' hne
    have : T ∈ cnbhd Ω T' := by
      rw [hT'.2, ← hT.2]
      exact self_mem_cnbhd hT.1
    exact this.2.resolve_left hne
  have hout' : ∀ T ∈ 𝒯, T ∈ compMembers Ω w D i₁ := by
    intro T hT
    rw [← hout]
    have hMT : M ∈ outerSet Ω T := by
      rw [outerSet_eq_of_cnbhd_eq hT.2]
      exact hM
    exact mem_outerSet_symm hT.1 hMT
  have hT₂ := hT T₂ (Or.inl rfl)
  have hT₃ := hT T₃ (Or.inr (Or.inl rfl))
  have hT₄ := hT T₄ (Or.inr (Or.inr rfl))
  obtain ⟨R₁, hR₁⟩ := exists_corr_left hΩ hex D (hout' N₀ hN₀𝒯)
  obtain ⟨R₂, hR₂⟩ := exists_corr_left hΩ hex D (hout' T₂ hT₂.1)
  obtain ⟨R₃, hR₃⟩ := exists_corr_left hΩ hex D (hout' T₃ hT₃.1)
  obtain ⟨R₄, hR₄⟩ := exists_corr_left hΩ hex D (hout' T₄ hT₄.1)
  have hR12 : R₁ ≠ R₂ := fun h => hT₂.2 (corr_unique_right hΩ hP1 hR₂ (h ▸ hR₁))
  have hR13 : R₁ ≠ R₃ := fun h => hT₃.2 (corr_unique_right hΩ hP1 hR₃ (h ▸ hR₁))
  have hR14 : R₁ ≠ R₄ := fun h => hT₄.2 (corr_unique_right hΩ hP1 hR₄ (h ▸ hR₁))
  have hR23 : R₂ ≠ R₃ := fun h => h23 (corr_unique_right hΩ hP1 hR₂ (h ▸ hR₃))
  have hR24 : R₂ ≠ R₄ := fun h => h24 (corr_unique_right hΩ hP1 hR₂ (h ▸ hR₄))
  have hR34 : R₃ ≠ R₄ := fun h => h34 (corr_unique_right hΩ hP1 hR₃ (h ▸ hR₄))
  have c12 : Commutes R₁ R₂ :=
    (corr_commutes hΩ hP1 hperf hR₁ hR₂).mp (hcomm𝒯 hN₀𝒯 hT₂.1 hT₂.2.symm)
  have c13 : Commutes R₁ R₃ :=
    (corr_commutes hΩ hP1 hperf hR₁ hR₃).mp (hcomm𝒯 hN₀𝒯 hT₃.1 hT₃.2.symm)
  have c14 : Commutes R₁ R₄ :=
    (corr_commutes hΩ hP1 hperf hR₁ hR₄).mp (hcomm𝒯 hN₀𝒯 hT₄.1 hT₄.2.symm)
  have hz₀Y : z₀ ∈ locLayer Ω w := le_centralizingLayer hR₁.1 hz₀.mem
  obtain ⟨c, hcR, hcz, hcimg, hc1⟩ := exists_central_preimage hperf hR₁ hz₀ hz₀Y
  have hcp := exists_clique_partner_of_eq S.odd S.five ht hr hexp (D.admissible i₁) hR₁.2.1
    hR₂.2.1 hR₃.2.1 hR₄.2.1 hR12 hR13 hR14 hR23 hR24 hR34 c12 c13 c14 hcR hcz hc1
  unfold CliquePartner at hcp
  obtain ⟨Ra, Rb, hRa, hRb, hab, ua, hua, ub, hub, Pm, hPm, xm, hxm, hcom, hsqa, hsqb, hnca,
    hncb, hnc, ht4, htnc⟩ := hcp
  have hsel : ∀ {R : Subgroup (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K},
      (R = R₂ ∨ R = R₃ ∨ R = R₄) → ∃ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) ∧ Corr Ω w D i₁ T R := by
    rintro R (rfl | rfl | rfl)
    · exact ⟨T₂, Or.inl rfl, hR₂⟩
    · exact ⟨T₃, Or.inr (Or.inl rfl), hR₃⟩
    · exact ⟨T₄, Or.inr (Or.inr rfl), hR₄⟩
  obtain ⟨Ta, hTa, hRaTa⟩ := hsel hRa
  obtain ⟨Tb, hTb, hRbTb⟩ := hsel hRb
  have hTab : Ta ≠ Tb := fun h => hab (corr_unique_left hperf hRaTa (h ▸ hRbTb))
  obtain ⟨hTa𝒯, hTaN⟩ := hT Ta hTa
  obtain ⟨hTb𝒯, hTbN⟩ := hT Tb hTb
  obtain ⟨ya, hyaY, hyaT, hya⟩ := exists_lift_of_corr hRaTa hua
  obtain ⟨yb, hybY, hybT, hyb⟩ := exists_lift_of_corr hRbTb hub
  have hz₀a : IsClassicalMember p f Ta z₀ :=
    isClassicalMember_of_twin hnab S hloc hN₀ hTa𝒯.1 hTa𝒯.2 hz₀
  have hz₀b : IsClassicalMember p f Tb z₀ :=
    isClassicalMember_of_twin hnab S hloc hN₀ hTb𝒯.1 hTb𝒯.2 hz₀
  obtain ⟨ca, hcaR, hcaz, hcaimg, hca1⟩ := exists_central_preimage hperf hRaTa hz₀a hz₀Y
  obtain ⟨cb, hcbR, hcbz, hcbimg, hcb1⟩ := exists_central_preimage hperf hRbTb hz₀b hz₀Y
  have hsqya : ya * ya = z₀ := by
    have h1 : locMk Ω w (⟨ya, hyaY⟩ * ⟨ya, hyaY⟩) = locMk Ω w ⟨z₀, hz₀Y⟩ := by
      rw [map_mul, hya, ← map_mul, hsqa ca hcaR hcaz hca1, hcaimg]
    have := locMk_inj_of_member hex hRaTa.1 (a := ⟨ya, hyaY⟩ * ⟨ya, hyaY⟩) (b := ⟨z₀, hz₀Y⟩)
      (Subgroup.mul_mem _ hyaT hyaT) hz₀a.mem h1
    exact congrArg Subtype.val this
  have hsqyb : yb * yb = z₀ := by
    have h1 : locMk Ω w (⟨yb, hybY⟩ * ⟨yb, hybY⟩) = locMk Ω w ⟨z₀, hz₀Y⟩ := by
      rw [map_mul, hyb, ← map_mul, hsqb cb hcbR hcbz hcb1, hcbimg]
    have := locMk_inj_of_member hex hRbTb.1 (a := ⟨yb, hybY⟩ * ⟨yb, hybY⟩) (b := ⟨z₀, hz₀Y⟩)
      (Subgroup.mul_mem _ hybT hybT) hz₀b.mem h1
    exact congrArg Subtype.val this
  have hyaYb : ya * yb ∈ locLayer Ω w := (locLayer Ω w).mul_mem hyaY hybY
  have himg : locMk Ω w ⟨ya * yb, hyaYb⟩ = D.hom i₁ (ua * ub) := by
    rw [map_mul, ← hya, ← hyb]
    exact map_mul (locMk Ω w) ⟨ya, hyaY⟩ ⟨yb, hybY⟩
  have hne1 : ya * yb ≠ 1 := by
    intro h1
    apply hnc
    apply D.ker_le_center i₁
    rw [MonoidHom.mem_ker, ← himg]
    have : (⟨ya * yb, hyaYb⟩ : ↥(locLayer Ω w)) = 1 := Subtype.ext h1
    rw [this, map_one]
  have hsc := fundamentalSingleClass_of_ne D i₁ (by rw [ht]; decide) (by rw [ht]; decide)
  obtain ⟨P, hPcorr⟩ := exists_corr_right hΩ D hsc hPm
  obtain ⟨x', hx'Y, hx'P, hx'⟩ := exists_lift_of_corr hPcorr hxm
  have hPcomm : ∀ g ∈ P, g * (ya * yb) = (ya * yb) * g := by
    refine commutes_elem_of_commutes_locImg hΩ hP1 hPcorr.1 hyaYb ?_
    intro w' hw'
    rw [hPcorr.2.2] at hw'
    obtain ⟨r, hr, rfl⟩ := hw'
    rw [himg, ← map_mul, ← map_mul, hcom r hr]
  set X : ↥(locLayer Ω w) := ⟨x', hx'Y⟩ with hX
  set Z₀ : ↥(locLayer Ω w) := ⟨z₀, hz₀Y⟩ with hZ₀
  have hlocT : locMk Ω w (X * Z₀ * X⁻¹ * Z₀⁻¹) = D.hom i₁ (xm * c * xm⁻¹ * c⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv, map_inv,
      hcimg]
    rw [hX, hx']
  have hTne : x' * z₀ * x'⁻¹ * z₀⁻¹ ≠ 1 := by
    intro h1
    apply htnc
    apply D.ker_le_center i₁
    rw [MonoidHom.mem_ker, ← hlocT]
    have : X * Z₀ * X⁻¹ * Z₀⁻¹ = 1 := Subtype.ext h1
    rw [this, map_one]
  have hT4 : (x' * z₀ * x'⁻¹ * z₀⁻¹) ^ 4 = 1 := by
    set T' : ↥(locLayer Ω w) := X * Z₀ * X⁻¹ * Z₀⁻¹ with hT'
    have hmk : locMk Ω w (T' ^ 4) = 1 := by
      rw [map_pow, hT', hlocT, ← map_pow, ht4, map_one]
    have hO : T' ^ 4 ∈ classicalInvolutionOddCore ↥(locLayer Ω w) :=
      (QuotientGroup.eq_one_iff _).mp hmk
    have hcent : T' ^ 4 ∈ Subgroup.center ↥(locLayer Ω w) := hP1 hO
    have hZ2 : Z₀ * Z₀ = 1 := Subtype.ext (mul_self_of_isClassicalMember hz₀)
    have hZi : Z₀⁻¹ = Z₀ := inv_eq_of_mul_eq_one_right hZ2
    have hinv : Z₀ * T' * Z₀⁻¹ = T'⁻¹ := by
      rw [hT']
      simp only [mul_inv_rev, inv_inv, hZi, mul_assoc, hZ2, mul_one]
    have hsq : T' ^ 4 * T' ^ 4 = 1 := by
      have h1 : Z₀ * T' ^ 4 * Z₀⁻¹ = (T' ^ 4)⁻¹ := by
        rw [← conj_pow, hinv, inv_pow]
      have h2 : Z₀ * T' ^ 4 * Z₀⁻¹ = T' ^ 4 := by
        rw [Subgroup.mem_center_iff.mp hcent Z₀]
        group
      rw [h2] at h1
      exact mul_eq_one_iff_eq_inv.mpr h1
    have := eq_one_of_mem_oddCore_of_sq hO hsq
    exact congrArg Subtype.val this
  refine ⟨Ta, Tb, ya, yb, P, x', hTa𝒯.1, hTb𝒯.1, hTa𝒯.2, hTb𝒯.2, hTaN, hTbN, hTab, hyaT,
    hybT, hsqya, hsqyb, ?_, ?_, hne1, hPcorr.1.1, hx'P, hPcomm, hT4, hTne⟩
  · exact fun hc => hnca (elem_central_of_lift hperf hRaTa hyaY hya.symm hc)
  · exact fun hc => hncb (elem_central_of_lift hperf hRbTb hybY hyb.symm hc)

end Main

end CFSG.ClassicalInvolution.RouteD.Exotic
