module

public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinA
public import CFSG.ClassicalInvolution.RouteD.TwinYP1Layer
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Local
public import CFSG.ClassicalInvolution.RouteD.TwinYElement

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.Assembly.LowTwoRank
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.RouteD.Gaps (eq_of_map_eq_of_central)
open scoped commutatorElement

section Perfect

theorem commutator_self_le {X : Type*} [Group X] (R : Subgroup X) : ⁅R, R⁆ ≤ R :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)

theorem commutes_of_commutators_mem_center {H : Type*} [Group H] {L : Subgroup H}
    (hperf : ⁅L, L⁆ = L) {u : H} (h : ∀ ℓ ∈ L, ⁅u, ℓ⁆ ∈ Subgroup.center H) :
    ∀ ℓ ∈ L, u * ℓ = ℓ * u := by
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  let φ : ↥L →* ↥(Subgroup.center H) :=
    { toFun := fun s => ⟨⁅u, (s : H)⁆, h s s.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun s t => by
        apply Subtype.ext
        have hs := Subgroup.mem_center_iff.mp (h t t.2) (s : H)
        simp only [Subgroup.coe_mul, commutatorElement_def]
        have hs' : (s : H) * (u * t * u⁻¹ * (t : H)⁻¹) = (u * t * u⁻¹ * (t : H)⁻¹) * s := by
          simpa [commutatorElement_def] using hs
        calc u * ((s : H) * t) * u⁻¹ * ((s : H) * t)⁻¹
            = (u * s * u⁻¹ * (s : H)⁻¹) * ((s : H) * (u * t * u⁻¹ * (t : H)⁻¹) * (s : H)⁻¹) := by
              group
          _ = (u * s * u⁻¹ * (s : H)⁻¹) * (u * t * u⁻¹ * (t : H)⁻¹) := by
            congr 1
            rw [hs']
            group }
  have hker : commutator ↥L ≤ φ.ker := Abelianization.commutator_subset_ker φ
  intro ℓ hℓ
  have hmem : (⟨ℓ, hℓ⟩ : ↥L) ∈ commutator ↥L := by
    rw [Group.IsPerfect.commutator_eq_top]
    trivial
  have h1 : φ ⟨ℓ, hℓ⟩ = 1 := hker hmem
  have h2 : ⁅u, ℓ⁆ = 1 := congrArg Subtype.val h1
  rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
  exact h2

theorem central_of_map_central {X Y : Type*} [Group X] [Group Y] (ψ : X →* Y)
    (hker : ψ.ker ≤ Subgroup.center X) {R : Subgroup X} (hperf : ⁅R, R⁆ = R) {r : X}
    (hr : r ∈ R) (hc : ∀ s ∈ R, ψ r * ψ s = ψ s * ψ r) : ∀ s ∈ R, r * s = s * r := by
  have : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hperf
  have key : (⟨r, hr⟩ : ↥R) ∈ Subgroup.center ↥R := by
    refine mem_center_of_comm_mem_center fun t => ?_
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    have h1 : ψ ⁅r, (t : X)⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hc t t.2)
    have h2 : ⁅r, (t : X)⁆ ∈ Subgroup.center X := hker (MonoidHom.mem_ker.mpr h1)
    have := Subgroup.mem_center_iff.mp h2 (u : X)
    have e : ((⁅(⟨r, hr⟩ : ↥R), t⁆ : ↥R) : X) = ⁅r, (t : X)⁆ := by
      simp [commutatorElement_def]
    simp only [Subgroup.coe_mul, e]
    exact this
  intro s hs
  have := Subgroup.mem_center_iff.mp key ⟨s, hs⟩
  exact congrArg Subtype.val this.symm

end Perfect

section Model

variable (p f : ℕ) [Fact p.Prime]


@[expose] def TwinProductCentral (tY : StatedLieTag) (nY : ℕ) : Prop :=
  ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
    ∀ R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      R ≠ R' → Commutes R R' →
      (∀ S ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
        (S = R ∨ Commutes S R) ↔ (S = R' ∨ Commutes S R')) →
      ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ≠ 1 →
      ∀ r' ∈ R', (∀ s ∈ R', r' * s = s * r') → r' ≠ 1 →
        r * r' ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K

end Model

section Local

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K T : Subgroup G} {z w : G} {tY : StatedLieTag} {nY : ℕ}


structure TwinLocal (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (z : G) (tY : StatedLieTag) (nY : ℕ) where
  hΩ : InClass p f Ω
  hex : ExactMembers Ω
  hP1 : LocalOddCentral Ω {z}
  rf : TwinRowFacts p f tY nY
  d : ShapeDictT2 p f tY nY Ω z

theorem exists_central_lift_loc (L₀ : TwinLocal p f Ω z tY nY) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) {wL : G} (hw : IsClassicalMember p f L wL)
    {R : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω z L = R.map L₀.d.ψ) :
    ∃ hY : wL ∈ locLayer Ω z, ∃ r ∈ R, (∀ s ∈ R, r * s = s * r) ∧ r ≠ 1 ∧
      locElt Ω z wL hY = L₀.d.ψ r := by
  obtain ⟨hY, ha, -, ha1, hac⟩ := G2D4.image_involution_facts hL hw
  refine ⟨hY, ?_⟩
  rw [hLR] at ha hac
  obtain ⟨r, hrR, hr⟩ := ha
  have hperf : ⁅R, R⁆ = R := le_antisymm (commutator_self_le R) (L₀.rf.perf R hR)
  refine ⟨r, hrR, ?_, ?_, by unfold locElt; exact hr.symm⟩
  · refine central_of_map_central L₀.d.ψ L₀.d.ker_le hperf hrR fun s hs => ?_
    rw [hr]
    exact hac _ ⟨s, hs, rfl⟩
  · rintro rfl
    apply ha1
    rw [← hr, map_one]

section Core

variable (L₀ : TwinLocal p f Ω z tY nY) (hFT : FalseTwinPure Ω K T z w)
  (hcls : IsClassicalMember p f K z) (hclsT : IsClassicalMember p f T w)

include L₀ hFT hcls hclsT

theorem u_central (hmf : TwinProductCentral p f tY nY) {g₀ : G}
    (hM : conjSub g₀ K ∈ centralizingMembers Ω {z}) (hMK : conjSub g₀ K ≠ K)
    (hMT : conjSub g₀ K ≠ T) :
    ∀ y ∈ locLayer Ω z, g₀ * (z * w) * g₀⁻¹ * y = y * (g₀ * (z * w) * g₀⁻¹) := by
  have hM₂ := hFT.M₂_mem hM hMK hMT
  have hM₂K := hFT.M₂_ne_K hMT
  have hM₂T := hFT.M₂_ne_T hMK
  have hMc : IsClassicalMember p f (conjSub g₀ K) (g₀ * z * g₀⁻¹) := hcls.conj g₀
  have hM₂c : IsClassicalMember p f (conjSub g₀ T) (g₀ * w * g₀⁻¹) := hclsT.conj g₀
  obtain ⟨R, hR, hMR⟩ := big_of_ne L₀.hΩ L₀.hex L₀.hP1 L₀.rf L₀.d hFT.K_mem hFT.T_mem hFT.hKT
    hFT.commK hFT.commT hM hMK hMT
  obtain ⟨R₂, hR₂, hM₂R⟩ := big_of_ne L₀.hΩ L₀.hex L₀.hP1 L₀.rf L₀.d hFT.K_mem hFT.T_mem
    hFT.hKT hFT.commK hFT.commT hM₂ hM₂K hM₂T
  obtain ⟨hzY, r, hrR, hrc, hr1, hr⟩ := exists_central_lift_loc L₀ hM hMc hR hMR
  obtain ⟨hwY, r₂, hr₂R, hr₂c, hr₂1, hr₂⟩ := exists_central_lift_loc L₀ hM₂ hM₂c hR₂ hM₂R
  have hRR₂ : R ≠ R₂ := by
    intro e
    rw [e] at hMR
    exact hFT.M₂_ne_M (locImg_injOn L₀.hΩ L₀.hP1 hM₂ hM (hM₂R.trans hMR.symm))
  have hcomm : Commutes R R₂ :=
    (commutes_iff_fund L₀.hΩ L₀.hP1 L₀.rf L₀.d hM hM₂ hR hMR hM₂R).mp hFT.commutes_M_M₂
  have hnbhd : ∀ S ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      (S = R ∨ Commutes S R) ↔ (S = R₂ ∨ Commutes S R₂) := by
    intro S hS
    by_cases hSR : S = R
    · subst hSR
      exact ⟨fun _ => Or.inr hcomm, fun _ => Or.inl rfl⟩
    by_cases hSR₂ : S = R₂
    · subst hSR₂
      exact ⟨fun _ => Or.inl rfl, fun _ => Or.inr hcomm.symm⟩
    obtain ⟨L, hL, hLS⟩ := mem_locFamily_iff.mp (L₀.d.mem_fam S hS)
    have hLM : L ≠ conjSub g₀ K := by
      rintro rfl
      exact hSR (eq_of_map_eq_of_central L₀.d.ψ L₀.d.ker_le (L₀.rf.perf S hS)
        (L₀.rf.perf R hR) (hLS.symm.trans hMR))
    have hLM₂ : L ≠ conjSub g₀ T := by
      rintro rfl
      exact hSR₂ (eq_of_map_eq_of_central L₀.d.ψ L₀.d.ker_le (L₀.rf.perf S hS)
        (L₀.rf.perf R₂ hR₂) (hLS.symm.trans hM₂R))
    have h1 := commutes_iff_fund L₀.hΩ L₀.hP1 L₀.rf L₀.d hL hM hS hLS hMR
    have h2 := commutes_iff_fund L₀.hΩ L₀.hP1 L₀.rf L₀.d hL hM₂ hS hLS hM₂R
    have h3 := hFT.graphTwin hL hLM hLM₂
    simp only [hSR, hSR₂, false_or]
    rw [← h1, ← h2]
    exact h3
  have hcen : r * r₂ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K :=
    hmf R hR R₂ hR₂ hRR₂ hcomm hnbhd r hrR hrc hr1 r₂ hr₂R hr₂c hr₂1
  have hUY : (g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹) ∈ locLayer Ω z :=
    (locLayer Ω z).mul_mem hzY hwY
  have hŪ : locElt Ω z ((g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹)) hUY = L₀.d.ψ (r * r₂) := by
    rw [← locElt_mul hzY hwY, hr, hr₂, map_mul]
  have hLcomm : ∀ L ∈ centralizingMembers Ω {z}, ∀ ℓ ∈ L,
      (g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹) * ℓ = ℓ * ((g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹)) := by
    intro L hL ℓ hℓ
    have hzM : g₀ * z * g₀⁻¹ ∈ conjSub g₀ K := conj_mem_conjSub hFT.hz.mem
    have hwM : g₀ * w * g₀⁻¹ ∈ conjSub g₀ T := conj_mem_conjSub hFT.hw.mem
    have fin : ∀ (a b : G), ℓ * a = a * ℓ → ℓ * b = b * ℓ → a * b * ℓ = ℓ * (a * b) := by
      intro a b ha hb
      calc a * b * ℓ = a * (b * ℓ) := by group
        _ = a * (ℓ * b) := by rw [hb]
        _ = (a * ℓ) * b := by group
        _ = (ℓ * a) * b := by rw [ha]
        _ = ℓ * (a * b) := by group
    by_cases hLK : L = K
    · subst hLK
      exact fin _ _ (hFT.commK _ hM hMK ℓ hℓ _ hzM) (hFT.commK _ hM₂ hM₂K ℓ hℓ _ hwM)
    by_cases hLT : L = T
    · subst hLT
      exact fin _ _ (hFT.commT _ hM hMT ℓ hℓ _ hzM) (hFT.commT _ hM₂ hM₂T ℓ hℓ _ hwM)
    obtain ⟨S, hS, hLS⟩ := big_of_ne L₀.hΩ L₀.hex L₀.hP1 L₀.rf L₀.d hFT.K_mem hFT.T_mem hFT.hKT
      hFT.commK hFT.commT hL hLK hLT
    obtain ⟨zL, hzL⟩ := L₀.hΩ.classical L hL.1
    have hLY : L ≤ locLayer Ω z := le_centralizingLayer hL
    have hperf : ⁅L.subgroupOf (locLayer Ω z), L.subgroupOf (locLayer Ω z)⁆ =
        L.subgroupOf (locLayer Ω z) :=
      commutator_eq_of_isClassicalMember (hzL.subgroupOf p f hLY)
    have hZall : ∀ ℓ' ∈ L.subgroupOf (locLayer Ω z),
        ⁅(⟨(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹), hUY⟩ : ↥(locLayer Ω z)), ℓ'⁆ ∈
          Subgroup.center ↥(locLayer Ω z) := by
      intro ℓ' hℓ'
      have hℓ'L : (ℓ' : G) ∈ L := Subgroup.mem_subgroupOf.mp hℓ'
      have himg : locElt Ω z (ℓ' : G) ℓ'.2 ∈ locImg Ω z L := locElt_mem_locImg hLY hℓ'L
      rw [hLS] at himg
      obtain ⟨s, hsS, hs⟩ := himg
      have hcomm' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z))
            ⟨(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹), hUY⟩ *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ℓ' =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ℓ' *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z))
            ⟨(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹), hUY⟩ := by
        have e1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z))
            ⟨(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹), hUY⟩ = L₀.d.ψ (r * r₂) := hŪ
        have e2 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ℓ' =
            L₀.d.ψ s := hs.symm
        rw [e1, e2, ← map_mul, ← map_mul]
        congr 1
        exact (Subgroup.mem_center_iff.mp hcen s).symm
      have hker : ⁅(⟨(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹), hUY⟩ : ↥(locLayer Ω z)), ℓ'⁆ ∈
          classicalInvolutionOddCore ↥(locLayer Ω z) := by
        have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z))
            ⁅(⟨(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹), hUY⟩ : ↥(locLayer Ω z)), ℓ'⁆ = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm'
        exact (QuotientGroup.eq_one_iff _).mp h1
      exact L₀.hP1 hker
    have key := commutes_of_commutators_mem_center hperf hZall
    have := key ⟨ℓ, hLY hℓ⟩ (Subgroup.mem_subgroupOf.mpr hℓ)
    exact congrArg Subtype.val this
  have hle : locLayer Ω z ≤ Subgroup.centralizer
      ({(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹)} : Set G) := by
    refine iSup₂_le fun L hL ℓ hℓ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hLcomm L hL ℓ hℓ).symm
  intro y hy
  have hy' := Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have e : g₀ * (z * w) * g₀⁻¹ = (g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹) := by group
  rw [e]
  exact hy'.symm

end Core

section Claims

variable (L₀ : TwinLocal p f Ω z tY nY) (hFT : FalseTwinPure Ω K T z w)
  (hcls : IsClassicalMember p f K z) (hclsT : IsClassicalMember p f T w)

include L₀ hFT hcls hclsT

theorem claimA (hmf : TwinProductCentral p f tY nY) :
    ∃ ε : G, ∀ g₁ : G, conjSub g₁ K ∈ centralizingMembers Ω {z} → conjSub g₁ K ≠ K →
      conjSub g₁ K ≠ T → g₁ * (z * w) * g₁⁻¹ = ε := by
  obtain ⟨J, hJ, hJK, hJT⟩ := exists_big_member L₀.hΩ L₀.hP1 L₀.rf L₀.d hFT.commK hFT.commT
  obtain ⟨g₀, rfl⟩ := hFT.trans J hJ.1
  refine ⟨g₀ * (z * w) * g₀⁻¹, fun g₁ h1 h1K h1T => ?_⟩
  obtain ⟨y, hyY, hy⟩ := link_big L₀.hΩ L₀.hex L₀.hP1 L₀.rf L₀.d hFT.K_mem hFT.T_mem hFT.hKT
    hFT.commK hFT.commT hJ hJK hJT h1 h1K h1T
  have hconj : conjSub (y * g₀) K = conjSub g₁ K := by
    rw [conjSub_mul]
    exact hy
  have hu := u_central L₀ hFT hcls hclsT hmf hJ hJK hJT y hyY
  rw [← hFT.conj_zw_eq hconj]
  calc y * g₀ * (z * w) * (y * g₀)⁻¹ = y * (g₀ * (z * w) * g₀⁻¹) * y⁻¹ := by group
    _ = (g₀ * (z * w) * g₀⁻¹ * y) * y⁻¹ := by rw [← hu]
    _ = g₀ * (z * w) * g₀⁻¹ := by group

theorem exists_member : ∃ g₀ : G, conjSub g₀ K ∈ centralizingMembers Ω {z} ∧
    conjSub g₀ K ≠ K ∧ conjSub g₀ K ≠ T := by
  obtain ⟨J, hJ, hJK, hJT⟩ := exists_big_member L₀.hΩ L₀.hP1 L₀.rf L₀.d hFT.commK hFT.commT
  obtain ⟨g₀, rfl⟩ := hFT.trans J hJ.1
  exact ⟨g₀, hJ, hJK, hJT⟩

end Claims

end Local

end CFSG.ClassicalInvolution.Asc77.S28
