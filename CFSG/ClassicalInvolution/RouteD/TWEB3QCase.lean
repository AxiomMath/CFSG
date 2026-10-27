module

public import CFSG.ClassicalInvolution.RouteD.TWEB3PCase
public import CFSG.ClassicalInvolution.RouteD.TWEB3QClass
public import CFSG.ClassicalInvolution.RouteD.TWEB3QDet
public import CFSG.ClassicalInvolution.RouteD.TWEB3QSqrt
public import CFSG.ClassicalInvolution.RouteD.TWEB3QLay
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.TWE.B6 CFSG.ClassicalInvolution.RouteD.TWE.B4
open QuadraticMap

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Num

variable {p f : ℕ} [Fact p.Prime]

theorem exists_sqrt_neg_one_of_one (hf : f ≠ 0) (h : p ^ f % 4 = 1) :
    ∃ i : (GaloisField p f)ˣ, i * i = -1 := by
  let _ : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hsq : IsSquare (-1 : GaloisField p f) := by
    rw [FiniteField.isSquare_neg_one_iff (F := GaloisField p f), ← Nat.card_eq_fintype_card,
      hcard]
    omega
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hc.symm)⟩

end Num

section LocAut

variable {G : Type} [Group G]

theorem locAut_mul_self_eq {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {w d s : G}
    (hdw : d * w * d⁻¹ = w) (hsw : s * w * s⁻¹ = w) (hds : d * d = s) (a : locQuot Ω w) :
    locAut hΩ hdw (locAut hΩ hdw a) = locAut hΩ hsw a := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
  show locMk Ω w (layerAut hΩ hdw (layerAut hΩ hdw y)) = locMk Ω w (layerAut hΩ hsw y)
  congr 1
  apply Subtype.ext
  show d * (d * (y : G) * d⁻¹) * d⁻¹ = s * (y : G) * s⁻¹
  rw [← hds]
  group

end LocAut

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


theorem twinYPatternAtL_b3_of_one_mod_four (hq1 : p ^ f % 4 = 1) :
    TwinYPatternAtL p f .POmegaOdd 3 (@PartnerPatternBPair p f 3 _) := by
  intro G _ _ _ hnab K z S hshape T e J J' w e' β s hcfg hP1 hP1' hty hty'
  classical
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hΩ : InClass p f (𝒞 K) := S.inClass
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd
  obtain ⟨c⟩ := TCtx.nonempty_odd (le_refl 3) S.odd S.five S.inClass S.exact hKΩ S.cls S.p1
    hshape
  have hf : f ≠ 0 := by
    rintro rfl
    have := c.hq
    simp at this
  obtain ⟨u₁, hu₁⟩ := exists_sqrt_neg_one_of_one (p := p) hf hq1
  have hT := hcfg.twin
  have hTz : T ∈ centralizingMembers (𝒞 K) {z} := hT.mem
  have hTQ := twin_locImg_le c hT
  have hJz := hcfg.mem_J
  have hJ'z := hcfg.mem_J'
  have hJL : IsLayerMember c J := ⟨hJz, hcfg.J_ne_K, fun hle =>
    hcfg.J_ne_T (c.eq_of_locImg_le_Q₁ hJz hTz hle hTQ)⟩
  have hJ'L : IsLayerMember c J' := ⟨hJ'z, hcfg.J'_ne_K, fun hle =>
    hcfg.J'_ne_T (c.eq_of_locImg_le_Q₁ hJ'z hTz hle hTQ)⟩
  obtain ⟨RM, hRM, hJR⟩ := hJL.exists_fund
  obtain ⟨RM', hRM', hJ'R⟩ := hJ'L.exists_fund
  have ht := hcfg.clsβ
  obtain ⟨W₀, hW₀⟩ := id hcfg.linear
  have htz : s * z * s⁻¹ = z := partner_involution_commutes c.hp2 c.hz ht hcfg.linear
  have h2t : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [ht.orderOf_eq_two, pow_two] at this
  have hKt : conjSub s K = K := conjSub_eq_of_standardPair h2 hW₀ ht.mem ht.orderOf_eq_two
  have hadm : StatedLieAdmissible .POmegaOdd 3 p f := ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf,
    le_refl 3, c.hp2⟩
  have hodd : Odd (Nat.card (GaloisField p f)) := c.hodd
  have cq := centralQuot_odd (m := 3) c.hp2 (le_refl 3) c.hq
  obtain ⟨FM, -, -, hFM, hFM', -, -, -, -, -, -, -, -, -, -⟩ := twin_datum_b3 c hJz hJ'z
    hcfg.clsJ hcfg.clsJ' e' hcfg.twinJ.ne.symm hRM hJR hRM' hJ'R
  have htwin : ∀ i j, IsFundamental (quadOdd 3 (GaloisField p f))
      (RM.map (spinAction (quadOdd 3 (GaloisField p f)))) i →
      IsFundamental (quadOdd 3 (GaloisField p f))
        (RM'.map (spinAction (quadOdd 3 (GaloisField p f)))) j → i = j := by
    intro i j hi hj
    rw [hFM] at hi
    rw [hFM'] at hj
    rw [IsFundamental.involution_unique hodd hi (IsFundamental.of_frame FM),
      IsFundamental.involution_unique hodd hj (IsFundamental.of_frame_swap FM)]
  have hne : RM' ≠ RM := fun h =>
    hcfg.twinJ.ne (c.eq_of_locImg_eq hJ'z hJz (by rw [hJ'R, hJR, h]))
  let θ : spinGroup (quadOdd 3 (GaloisField p f)) →* locQuot (𝒞 K) z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range c htz h2t hKt (range_le_iSup_fund_odd (by omega) hadm c.hY.std c.d.ψ) k'
  have hfixσ : ∀ {L : Subgroup G} {R : Subgroup (spinGroup (quadOdd 3 (GaloisField p f)))},
      L ∈ centralizingMembers (𝒞 K) {z} → locImg (𝒞 K) z L = R.map θ → Commutes β L →
      ∀ r ∈ R, σ (θ r) = θ r := fun hL hLR hβL r hr =>
    (locAut_fixed_iff hΩ c.hP1 htz hL).mp (fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hβL s ht.mem n hn).symm) _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  obtain ⟨x, α, g₀, -, -, hαθ, hg₀O, hg₀2, hconj, -⟩ := lift_b3 c.hp2 c.hq θ c.d.ker_le σ hσ2 hσr
    hRM hRM' hne htwin (hfixσ hJz hJR hcfg.comm_J) (hfixσ hJ'z hJ'R hcfg.comm_J')
  have hcommg : ∀ {R : Subgroup (spinGroup (quadOdd 3 (GaloisField p f)))},
      R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p f)) →
      (∀ r ∈ R, σ (θ r) = θ r) →
      ∀ l ∈ R.map (spinAction (quadOdd 3 (GaloisField p f))), g₀ * l = l * g₀ :=
    fun hR hfix => commute_of_fixed θ c.d.ker_le σ α hαθ (cq.perf _ hR) hfix hconj
  obtain ⟨d, hdβ, hdd, hdz, hKd⟩ := exists_sqrt_partner h2 hu₁ hW₀ c.hz.mem c.hz.orderOf_eq_two
    ht.mem ht.orderOf_eq_two
  let σd := locAut hΩ.conjInvariant hdz
  have hσdd : ∀ y, σd (σd y) = σ y := fun y => locAut_mul_self_eq hΩ.conjInvariant hdz htz hdd y
  have hσdr : ∀ k', σd (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range_of_unit c hdz hKd (range_le_iSup_fund_odd (by omega) hadm c.hY.std c.d.ψ) k'
  have hfixd : ∀ {L : Subgroup G} {R : Subgroup (spinGroup (quadOdd 3 (GaloisField p f)))},
      L ∈ centralizingMembers (𝒞 K) {z} → locImg (𝒞 K) z L = R.map θ → Commutes β L →
      ∀ r ∈ R, σd (θ r) = θ r := fun hL hLR hβL r hr =>
    (locAut_fixed_iff hΩ c.hP1 hdz hL).mp (fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hβL d hdβ n hn).symm) _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  have hiMf : IsFundamental (quadOdd 3 (GaloisField p f))
      (RM.map (spinAction (quadOdd 3 (GaloisField p f)))) (FM.La (-1)) := by
    rw [hFM]
    exact IsFundamental.of_frame FM
  obtain ⟨εM, hεM, hgM⟩ := sign_of_commute h2 hiMf hg₀O hg₀2
    (hcommg hRM (hfixσ hJz hJR hcfg.comm_J))
  have hgM' : ∀ x ∈ FM.span, g₀ x = εM • x := fun x hx =>
    hgM x (by rw [negSpace_La_neg_one h2]; exact hx)
  obtain ⟨h, αd, hhO, hhspan, hαdψ', hhconj⟩ := exists_isometry_sqrt_b3 c.hp2 c.hq θ c.d.ker_le σ
    σd hσ2 hσdd hσr hσdr FM hFM hFM' (hfixd hJz hJR hcfg.comm_J) (hfixd hJ'z hJ'R hcfg.comm_J')
  have hdet := det_of_sq_b3 c.hp2 c.hq θ c.d.ker_le σ σd hσdd FM hhO hhspan hαdψ' hhconj α hαθ
    hg₀O hconj hεM hgM'
  have hKJ : Commutes K J := hT.comm_K J hJz hcfg.J_ne_K
  have hKJ' : Commutes K J' := hT.comm_K J' hJ'z hcfg.J'_ne_K
  have hKu : K ∈ centralizingMembers (𝒞 K) {e'.u} := e'.mem_centralizingMembers_u hKΩ hKJ hKJ'
  obtain ⟨N₁, hN₁, N₂, hN₂, hKN₁, hKN₂, hβN₁, hβN₂, hne₁₂⟩ := exists_leaf_b3 S.odd S.five hΩ
    S.exact hP1' hty' hKu hcfg.memβ S.cls ht hcfg.linear
  obtain ⟨N₀, hN₀u, hKN₀, hβN₀, hN₀T⟩ : ∃ N ∈ centralizingMembers (𝒞 K) {e'.u},
      Commutes K N ∧ (∃ W, LinearBlockStandardPair (GaloisField p f) W β N) ∧ N ≠ T := by
    by_cases h : N₁ = T
    · exact ⟨N₂, hN₂, hKN₂, hβN₂, fun h' => hne₁₂ (h.trans h'.symm)⟩
    · exact ⟨N₁, hN₁, hKN₁, hβN₁, h⟩
  have hN₀z : N₀ ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hN₀u.1 c.hz.mem (commutes_symm hKN₀)
  have hN₀K : N₀ ≠ K := fun h => not_commutes_self_of_mem hΩ hKΩ (by rw [h] at hKN₀; exact hKN₀)
  have hN₀L : IsLayerMember c N₀ := ⟨hN₀z, hN₀K, fun hle =>
    hN₀T (c.eq_of_locImg_le_Q₁ hN₀z hTz hle hTQ)⟩
  obtain ⟨RN, hRN, hN₀R⟩ := hN₀L.exists_fund
  obtain ⟨W₁, hW₁⟩ := hβN₀
  have hβN₀' : ∃ W, LinearBlockStandardPair (GaloisField p f) W N₀ β :=
    ⟨W₁, linearBlockStandardPair_symm hW₁⟩
  obtain ⟨W₂, hW₂⟩ := hβN₀'
  have hN₀t : conjSub s N₀ = N₀ :=
    conjSub_eq_of_standardPair h2 hW₂ ht.mem ht.orderOf_eq_two
  obtain ⟨x₁, hx₁N, hx₁1, hx₁p, hx₁inv⟩ :=
    TWS7.exists_inverted_unipotent (p := p) h2 hW₂ ht.mem ht.orderOf_eq_two
  obtain ⟨hαN, x₀, hx₀N, hx₀1, hx₀p, hx₀α⟩ :=
    unip_data_b3 c htz hN₀z hRN hN₀R hN₀t hx₁N hx₁1 hx₁p hx₁inv hαθ
  have hnormN : ∀ l ∈ RN.map (spinAction (quadOdd 3 (GaloisField p f))),
      g₀ * l * g₀ ∈ RN.map (spinAction (quadOdd 3 (GaloisField p f))) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨α y, hαN y hy, ?_⟩
    refine LinearEquiv.ext fun v => ?_
    have e1 : g₀ (g₀ v) = v := by simpa using LinearEquiv.congr_fun hg₀2 v
    have := hconj y (g₀ v)
    rw [e1] at this
    exact this
  have hx₀inv : ∀ v, g₀ (spinAction (quadOdd 3 (GaloisField p f)) x₀ v) =
      (spinAction (quadOdd 3 (GaloisField p f)) x₀).symm (g₀ v) := by
    intro v
    have h1 := hconj x₀ v
    rw [hx₀α, map_inv] at h1
    exact h1.symm
  obtain ⟨x', hRNeq, hscal⟩ := class_spin_b3_det c.hp2 c.hq cq hg₀O hg₀2 hεM hdet hRN FM hgM'
    hnormN hx₀N hx₀1 hx₀p hx₀inv
  have hn2 : locImg (𝒞 K) z N₀ =
      ((rootSL2 (oddFrame 3 (GaloisField p f)).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false).map (MulAut.conj x').toMonoidHom).map c.d.ψ := by
    rw [hN₀R, hRNeq]
  exact pattern_b3 c htz hN₀u.1 hKN₀ ⟨W₁, hW₁⟩ hn2 hαθ hg₀O hconj
    (by rcases hεM with rfl | rfl <;> norm_num) hscal


theorem twinYPatternAtL_b3 :
    TwinYPatternAtL p f .POmegaOdd 3 (@PartnerPatternBPair p f 3 _) := by
  by_cases hp2 : p = 2
  · intro G _ _ _ hnab K z S
    exact absurd hp2 S.odd
  · exact twinYPatternAtL_b3_of_one hp2 twinYPatternAtL_b3_of_one_mod_four

end Main

end CFSG.ClassicalInvolution.RouteD.TWE.B3
