module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Abs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoP
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLT237

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL


section Cov

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y}

theorem e_mem_orb (Z : Subgroup Y) (t e : Y) : e ∈ p23Orb Z t e :=
  ⟨1, Subgroup.one_mem _, by group⟩

theorem piE_e_ne_one (hc : P23Cfg n Y R S t K' W u e g) :
    ZTwo.piE hc ⟨e, p23_e_mem_rLayer hc⟩ ≠ 1 := by
  intro h
  have h1 : e ∈ oddCoreOf (rLayer (Om R) e) := (ZTwo.piE_eq_one_iff hc _).mp h
  exact hc.data.he1 (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h1
    (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.he2))

theorem omegaOneCenter_of_cover (hc : P23Cfg n Y R S t K' W u e g)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) :
    OmegaOneCenter (rLayer (Om R) e) e := by
  intro z hz hcen hsq
  by_cases h1 : ZTwo.piE hc ⟨z, hz⟩ = 1
  · exact Or.inl ((ZTwo.piE_eq_one_iff hc _).mp h1)
  · right
    have heE : e ∈ rLayer (Om R) e := p23_e_mem_rLayer hc
    have hEC : rLayer (Om R) e ≤ Subgroup.centralizer ({e} : Set Y) := F7C.rLayer_le_centralizer e
    have hzc : ZTwo.piE hc ⟨z, hz⟩ ∈ Subgroup.center (SecQ R e) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := ZTwo.piE_surjective hc q
      have h2 : ZTwo.piE hc (⟨z, hz⟩ * y * ⟨z, hz⟩⁻¹ * y⁻¹) = 1 :=
        (ZTwo.piE_eq_one_iff hc _).mpr (hcen y y.2)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
      exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)).symm
    have hec : ZTwo.piE hc ⟨e, heE⟩ ∈ Subgroup.center (SecQ R e) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨a, rfl⟩ := ZTwo.piE_surjective hc q
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (a : Y) * e = e * (a : Y)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hEC a.2)
    have hz2 : ZTwo.piE hc ⟨z, hz⟩ * ZTwo.piE hc ⟨z, hz⟩ = 1 := by
      rw [← map_mul]
      exact (ZTwo.piE_eq_one_iff hc _).mpr hsq
    have h4 := D.eq_of_central_involutions hzc hec hz2 h1 (piE_e_ne_one hc)
    exact (ZTwo.piE_eq_iff hc ⟨e, heE⟩ ⟨z, hz⟩).mp h4.symm

theorem omegaOneCenter_orbit (hc : P23Cfg n Y R S t K' W u e g)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {c : Y} (hcO : c ∈ p23Orb Z t e) :
    OmegaOneCenter (rLayer (Om R) c) c := by
  obtain ⟨m, -, rfl⟩ := hcO
  have h := (omegaOneCenter_of_cover hc D).conj m
  rwa [← rLayer_conj (R := R) m e] at h

theorem not_centModE_orbit (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {y : Y} (hy : y ∈ p23Orb Z t e)
    (hye : y ≠ e) : ¬ CentModE R e y := by
  intro hcm
  obtain ⟨m, hm, rfl⟩ := hy
  have hyZ : m * e * m⁻¹ ∈ Z := hZ.orb_le ⟨m, hm, rfl⟩
  have hyC : m * e * m⁻¹ ∈ Subgroup.centralizer ({e} : Set Y) := hZ.le_cent hZ.he hyZ
  have hy2 : (m * e * m⁻¹) * (m * e * m⁻¹) = 1 := hZ.sq _ hyZ
  have hΩ := ZTwo.hΩ_of hc
  refine ZTwo.false_of_trivial hc D hyC hy2 hye ?_
  intro q
  obtain ⟨x, rfl⟩ := ZTwo.piE_surjective hc q
  have hcx : (m * e * m⁻¹) * (x : Y) * (m * e * m⁻¹)⁻¹ ∈ rLayer (Om R) e := by
    have := conj_mem_conjSub (n := m * e * m⁻¹) x.2
    rwa [conjSub_rLayer_eq hΩ hyC] at this
  rw [ZTwo.secAut_piE hc hyC x hcx, ZTwo.piE_eq_iff hc]
  have h1 := hcm ((x : Y)⁻¹) ((rLayer (Om R) e).inv_mem x.2)
  have h2 : (((m * e * m⁻¹) * (x : Y) * (m * e * m⁻¹)⁻¹)⁻¹ * (x : Y)) =
      (m * e * m⁻¹) * (x : Y)⁻¹ * (m * e * m⁻¹)⁻¹ * ((x : Y)⁻¹)⁻¹ := by group
  show (((m * e * m⁻¹) * (x : Y) * (m * e * m⁻¹)⁻¹)⁻¹ * (x : Y)) ∈ oddCoreOf (rLayer (Om R) e)
  rw [h2]
  exact h1

theorem centModE_of_central (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    {c₁ c₂ : Y} (hc₁ : c₁ ∈ p23Orb Z t e) (hVc₁ : V ≤ aSub R Z c₁) (hc₂ : c₂ ∈ Z)
    (hc₂X : c₂ ∈ rLayerSub (Om R) V)
    (hcen : QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨c₂, hc₂X⟩ ∈
      Subgroup.center (SecQuot (rLayerSub (Om R) V))) : CentModE R c₁ c₂ := by
  have hΩ : HypOmegaGen (Om R) := ZTwo.hΩ_of hc
  obtain ⟨-, hE₀E, hE₀X, hcov⟩ := LemL.p23_cover_V hc hZ hVZ hc₁ hVc₁
  have hc₁Z : c₁ ∈ Z := hZ.orb_le hc₁
  have hA : c₂ ∈ Subgroup.centralizer ((V ⊔ Subgroup.zpowers c₁ : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hZ.comm h ((sup_le hVZ (Subgroup.zpowers_le.mpr hc₁Z)) hh) c₂ hc₂
  have hN := F7L.mem_normalizer_rLayerSub hΩ hA
  exact centMod_of_central_cover hE₀E hE₀X hcov hc₂X hcen
    (fun y hy => (Subgroup.mem_normalizer_iff.mp hN y).mp hy)
    (fun o ho => F7C.conj_mem_oddCoreOf_rLayer hΩ (hZ.le_cent hc₁Z hc₂) ho)

theorem not_central_f (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {f : Y} (hf : f ∈ p23Orb Z t e)
    (hfe : f ≠ e) (hVe : V ≤ aSub R Z e) (hfX : f ∈ rLayerSub (Om R) V) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨f, hfX⟩ ∉
      Subgroup.center (SecQuot (rLayerSub (Om R) V)) := fun hcen =>
  not_centModE_orbit hc hZ D hf hfe
    (centModE_of_central hc hZ hVZ (e_mem_orb Z t e) hVe (hZ.orb_le hf) hfX hcen)

theorem not_central_e (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {f : Y} (hf : f ∈ p23Orb Z t e)
    (hfe : f ≠ e) (hVf : V ≤ aSub R Z f) (heX : e ∈ rLayerSub (Om R) V) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨e, heX⟩ ∉
      Subgroup.center (SecQuot (rLayerSub (Om R) V)) := by
  intro hcen
  have hcm : CentModE R f e := centModE_of_central hc hZ hVZ hf hVf hZ.he heX hcen
  obtain ⟨m, hm, rfl⟩ := hf
  have hm' : m⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.normalizer (Z : Set Y) :=
    Subgroup.inv_mem _ hm
  have hcm' : CentModE R e (m⁻¹ * e * m⁻¹⁻¹) := by
    have := (centModE_conj (R := R) m⁻¹ (m * e * m⁻¹) e).mpr hcm
    rwa [show m⁻¹ * (m * e * m⁻¹) * m⁻¹⁻¹ = e by group] at this
  refine not_centModE_orbit hc hZ D (y := m⁻¹ * e * m⁻¹⁻¹) ⟨m⁻¹, hm', rfl⟩ ?_ hcm'
  intro h
  apply hfe
  calc m * e * m⁻¹ = m * (m⁻¹ * e * m⁻¹⁻¹) * m⁻¹ := by rw [h]
    _ = e := by group

theorem mk_sq (hZ : P23ZData t u e Z) {c : Y} (hcZ : c ∈ Z) {X : Subgroup Y} (hcX : c ∈ X) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨c, hcX⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨c, hcX⟩ = 1 := by
  rw [← map_mul]
  have : (⟨c, hcX⟩ * ⟨c, hcX⟩ : ↥X) = 1 := Subtype.ext (hZ.sq c hcZ)
  rw [this, map_one]

theorem mem_Ea_self (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    {c : Y} (hcO : c ∈ p23Orb Z t e) (hVc : V ≤ aSub R Z c) (hcX : c ∈ rLayerSub (Om R) V) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨c, hcX⟩ ∈
      Ea (p23SecFamV R V)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨c, hcX⟩) := by
  obtain ⟨-, hE₀E, hE₀X, hcov⟩ := LemL.p23_cover_V hc hZ hVZ hcO hVc
  rw [LemL.Ea_eq_secImage hc hZ hcO hcX]
  have hcE₀ : c ∈ rLayerSub (Om R) (V ⊔ Subgroup.zpowers c) := by
    refine F7C.mem_rLayerSub_of_cover ?_ (p23_mem_rLayer_self hc hcO)
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one
        (hZ.sq c (hZ.orb_le hcO)))
    rw [inf_eq_right.mpr hE₀E]
    exact hcov
  exact ⟨⟨c, hcX⟩, Subgroup.mem_subgroupOf.mpr hcE₀, rfl⟩

theorem not_isSolvable_Ea (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {c : Y} (hcO : c ∈ p23Orb Z t e)
    (hVc : V ≤ aSub R Z c) (hcX : c ∈ rLayerSub (Om R) V) :
    ¬ Group.IsSolvable ↥(Ea (p23SecFamV R V)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨c, hcX⟩)) := by
  obtain ⟨-, hE₀E, hE₀X, hcov⟩ := LemL.p23_cover_V hc hZ hVZ hcO hVc
  rw [LemL.Ea_eq_secImage hc hZ hcO hcX]
  obtain ⟨π, hπs, hπO⟩ : ∃ π : ↥(rLayer (Om R) c) →* SecQ R e, Function.Surjective π ∧
      classicalInvolutionOddCore ↥(rLayer (Om R) c) ≤ π.ker := by
    obtain ⟨m, -, hcm⟩ := hcO
    have hEc : rLayer (Om R) c = conjSub m (rLayer (Om R) e) := by
      rw [hcm]
      exact rLayer_conj m e
    have hmem : ∀ x : Y, x ∈ rLayer (Om R) c ↔ m⁻¹ * x * m ∈ rLayer (Om R) e := fun x => by
      rw [hEc, mem_conjSub_iff]
    have hOc : ∀ x : Y, x ∈ oddCoreOf (rLayer (Om R) c) ↔
        m⁻¹ * x * m ∈ oddCoreOf (rLayer (Om R) e) := fun x => by
      rw [hEc, Asc77.Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff]
    refine ⟨MonoidHom.mk' (fun x : ↥(rLayer (Om R) c) =>
        ZTwo.piE hc ⟨m⁻¹ * (x : Y) * m, (hmem _).mp x.2⟩) ?_, ?_, ?_⟩
    · intro x y
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      show m⁻¹ * ((x : Y) * (y : Y)) * m = (m⁻¹ * (x : Y) * m) * (m⁻¹ * (y : Y) * m)
      group
    · intro q
      obtain ⟨x, rfl⟩ := ZTwo.piE_surjective hc q
      have hx : m * (x : Y) * m⁻¹ ∈ rLayer (Om R) c := (hmem _).mpr (by
        rw [show m⁻¹ * (m * (x : Y) * m⁻¹) * m = (x : Y) by group]
        exact x.2)
      refine ⟨⟨m * (x : Y) * m⁻¹, hx⟩, ?_⟩
      show ZTwo.piE hc ⟨m⁻¹ * (m * (x : Y) * m⁻¹) * m, _⟩ = ZTwo.piE hc x
      congr 1
      apply Subtype.ext
      show m⁻¹ * (m * (x : Y) * m⁻¹) * m = (x : Y)
      group
    · intro x hx
      rw [MonoidHom.mem_ker]
      show ZTwo.piE hc ⟨m⁻¹ * (x : Y) * m, _⟩ = 1
      rw [ZTwo.piE_eq_one_iff]
      exact (hOc _).mp ((ZTwo.mem_oddCore_iff_val _ x).mp hx)
  obtain ⟨σ, hσ⟩ := exists_surj_secImage_of_cover hE₀X hE₀E hcov π hπs hπO
  intro hs
  haveI := D.perfect
  haveI : Nontrivial (SecQ R e) := ⟨⟨_, 1, piE_e_ne_one hc⟩⟩
  haveI := hs
  exact Group.IsPerfect.not_isSolvable (SecQ R e) (Group.isSolvable_of_surjective hσ)

theorem central_Ea (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {c : Y} (hcO : c ∈ p23Orb Z t e)
    (hVc : V ≤ aSub R Z c) (hcX : c ∈ rLayerSub (Om R) V)
    (hcen : QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨c, hcX⟩ ∈
      Subgroup.center (SecQuot (rLayerSub (Om R) V)) → False) :
    ∀ z ∈ Subgroup.center (SecQuot (rLayerSub (Om R) V)),
      z ∈ Ea (p23SecFamV R V)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨c, hcX⟩) → z = 1 := by
  obtain ⟨-, hE₀E, hE₀X, hcov⟩ := LemL.p23_cover_V hc hZ hVZ hcO hVc
  have hcovV : rLayer (Om R) c ≤ oddCoreOf (rLayer (Om R) c) ⊔
      (rLayer (Om R) c ⊓ rLayerSub (Om R) V) :=
    hcov.trans (sup_le_sup_left (le_inf hE₀E hE₀X) _)
  have hbot := LemL.central_inf_eq_bot hcX (hZ.sq c (hZ.orb_le hcO)) hcovV
    (omegaOneCenter_orbit hc D hcO) hcen
  intro z hz hzE
  rw [LemL.Ea_eq_secImage hc hZ hcO hcX] at hzE
  have hz' : z ∈ secImage (rLayerSub (Om R) V) (rLayer (Om R) c ⊓ rLayerSub (Om R) V) := by
    obtain ⟨x, hx, rfl⟩ := hzE
    exact ⟨x, Subgroup.mem_subgroupOf.mpr ⟨hE₀E (Subgroup.mem_subgroupOf.mp hx),
      hE₀X (Subgroup.mem_subgroupOf.mp hx)⟩, rfl⟩
  have hmem : z ∈ secImage (rLayerSub (Om R) V) (rLayer (Om R) c ⊓ rLayerSub (Om R) V) ⊓
      Subgroup.center (SecQuot (rLayerSub (Om R) V)) := ⟨hz', hz⟩
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

end Cov

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
