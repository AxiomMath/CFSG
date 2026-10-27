module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigN
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTri

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Sp62Rec
  CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section CentralMod

variable {X : Type*} [Group X] [Finite X]

theorem comm_of_comm_quot {O : Subgroup X} [O.Normal] (hOc : O ≤ Subgroup.center X)
    (hOodd : Odd (Nat.card O)) {a : X} (ha : a * a = 1)
    (h : ∀ y : X ⧸ O, QuotientGroup.mk' O a * y = y * QuotientGroup.mk' O a) :
    ∀ y : X, a * y = y * a := by
  refine comm_of_central_mod_odd hOc hOodd ha fun y => ?_
  have h1 : QuotientGroup.mk' O (a * y * a⁻¹ * y⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h (QuotientGroup.mk' O y)]
    group
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem exists_lift_three_quot {O : Subgroup X} [O.Normal] (hOc : O ≤ Subgroup.center X) {t : X}
    (ht : t * t = 1) {c : X ⧸ O} {m : ℕ} (hc : c ^ 3 ^ m = 1)
    (hct : c * QuotientGroup.mk' O t = QuotientGroup.mk' O t * c) :
    ∃ x : X, QuotientGroup.mk' O x = c ∧ (∃ m' : ℕ, x ^ 3 ^ m' = 1) ∧ x * t = t * x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O c
  have hker : (QuotientGroup.mk' O).ker ≤ Subgroup.center X := by
    rw [QuotientGroup.ker_mk']
    exact hOc
  exact exists_lift_three (QuotientGroup.mk' O) hker ht hc hct

end CentralMod

section Generic

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

theorem exists_three_of_twinE4 (mv : E4ModelMove) (F : LemL.Q8Pre G Φ) {K : Subgroup G} (hK : K ∈ Φ)
    {t : G} (ht : IsUniqueInvolution K t) (hno : ¬ TightInO2 t) (hE : TwinE4 G) {a : G}
    (ha2 : a * a = 1) (haK : ∀ x ∈ K, a * x = x * a) (ha : ¬ ∀ y : G, a * y = y * a)
    (hat : ¬ ∀ y : G, (a * t) * y = y * (a * t)) :
    ∃ c : G, (∃ m : ℕ, c ^ 3 ^ m = 1) ∧ c * t = t * c ∧ c * a ≠ a * c := by
  obtain ⟨Q, hQ, f, hfs, hker, hM⟩ := hE
  have hN2 : IsPGroup 2 ↥f.ker := hker
  have hzN : ∀ J ∈ Φ, ∀ u : G, IsUniqueInvolution J u → u ∉ f.ker := by
    intro J hJ u hu huN
    obtain ⟨g, rfl⟩ := F.trans K hK J hJ
    have hu' : g * t * g⁻¹ = u := (ht.conj g).eq hu
    apply hno
    refine ⟨f.ker, inferInstance, hN2, ?_⟩
    have h3 := (inferInstance : f.ker.Normal).conj_mem u huN g⁻¹
    rw [← hu'] at h3
    simpa [mul_assoc] using h3
  have hmeet : ∀ J ∈ Φ, J ⊓ f.ker = ⊥ := fun J hJ => TwinDisc.ExitE4.inf_eq_bot F.two F.hyp hzN hJ
  have hNc : f.ker ≤ Subgroup.center G :=
    TwinDisc.ExitE4.center_of_meet F.hyp F.two F.gen hN2 hmeet
  let e : (G ⧸ f.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hfs
  have hMq : CFSG.Blueprint.LieModel (G ⧸ f.ker) .PSp 3 2 1 ∨
      CFSG.Blueprint.LieModel (G ⧸ f.ker) .POmegaPlus 4 2 1 :=
    hM.imp (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
      (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  have hnab := TwinDisc.ExitE4.exists_noncomm F.hyp F.two hK
  have hinvK : IsUniqueInvolution (K.map (QuotientGroup.mk' f.ker)) (QuotientGroup.mk' f.ker t) :=
    AscQuot.isUniqueInvolution_map_mk (hmeet K hK) ht
  have hq8K : Nonempty (↥(K.map (QuotientGroup.mk' f.ker)) ≃* QuaternionGroup 2) := by
    obtain ⟨eK⟩ := F.q8 K hK
    exact ⟨(AscQuot.quotRestrictEquiv (hmeet K hK)).symm.trans eK⟩
  have htw : ∀ c ∈ Subgroup.centralizer ({QuotientGroup.mk' f.ker t} : Set (G ⧸ f.ker)),
      conjSub c (K.map (QuotientGroup.mk' f.ker)) = K.map (QuotientGroup.mk' f.ker) ∨
        ∀ x ∈ K.map (QuotientGroup.mk' f.ker), ∀ y ∈ conjSub c (K.map (QuotientGroup.mk' f.ker)),
          x * y = y * x := by
    intro cb hcb
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective f.ker cb
    have hc' : QuotientGroup.mk' f.ker c * QuotientGroup.mk' f.ker t =
        QuotientGroup.mk' f.ker t * QuotientGroup.mk' f.ker c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcb
    have hq : t⁻¹ * (c * t * c⁻¹) ∈ f.ker := by
      have h0 : QuotientGroup.mk' f.ker (t⁻¹ * (c * t * c⁻¹)) = 1 := by
        simp only [map_mul, map_inv]
        rw [hc', mul_inv_cancel_right, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    have hcen : ∀ y : G, y * (t⁻¹ * (c * t * c⁻¹)) = (t⁻¹ * (c * t * c⁻¹)) * y :=
      Subgroup.mem_center_iff.mp (hNc hq)
    rcases TwinDisc.ExitE4.twin_clause_central F.hyp F.two hK ht hnab rfl hcen with h | h
    · left
      rw [← AscQuot.map_conjSub, h]
    · right
      rintro _ ⟨x, hx, rfl⟩ y hy
      rw [← AscQuot.map_conjSub] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_mul, ← map_mul, h x hx y' hy']
  have hπa : QuotientGroup.mk' f.ker a ≠ 1 := fun h =>
    ha fun y => (Subgroup.mem_center_iff.mp (hNc ((QuotientGroup.eq_one_iff _).mp h)) y).symm
  have hπat : QuotientGroup.mk' f.ker a ≠ QuotientGroup.mk' f.ker t := by
    intro h
    have h0 : QuotientGroup.mk' f.ker (a * t) = 1 := by
      rw [map_mul, h, ← map_mul, ht.sq, map_one]
    exact hat fun y =>
      (Subgroup.mem_center_iff.mp (hNc ((QuotientGroup.eq_one_iff _).mp h0)) y).symm
  have hsq : QuotientGroup.mk' f.ker a * QuotientGroup.mk' f.ker a = 1 := by
    rw [← map_mul, ha2, map_one]
  have hcomm : ∀ x ∈ K.map (QuotientGroup.mk' f.ker),
      QuotientGroup.mk' f.ker a * x = x * QuotientGroup.mk' f.ker a := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, haK x hx]
  obtain ⟨c, hc3, hcs, hca⟩ := mv (G ⧸ f.ker) hMq _ _ hq8K hinvK htw (QuotientGroup.mk' f.ker a)
    hsq hπa hπat hcomm
  obtain ⟨x, hxy, hx3, hxt⟩ := exists_lift_three_quot hNc ht.sq (m := 1) (by simpa using hc3) hcs
  refine ⟨x, hx3, hxt, fun h => hca ?_⟩
  rw [← hxy, ← map_mul, ← map_mul, h]

end Generic


section Branch

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g x : Y}

namespace ZCtx

variable (H : ZCtx n Y R S t K' W u e g x)
include H

theorem q8Pre_sec (hT : Thm4RTwinBelow 3 n) (hoc : classicalInvolutionOddCore ↥(p23XE R e x) ≤
      Subgroup.center ↥(p23XE R e x)) :
    LemL.Q8Pre (SecQuot (p23XE R e x))
      (SectionThmD.secClass (p23XE R e x) (tightCore R)) := by
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK2 : IsPGroup 2 (tightCore R) := H.two _ hK
  have hKN : tightCore R ≤ p23XE R e x := H.K_le_N
  have hAe : AEmpty (Om R) (tightCore R) := (CoreData.of_S H.cfg.std.perp.core).aEmpty
  have hΩX := hypOmegaGen_conjClass_section H.hΩ hK hKN
  have hAJ := aEmpty_conjClass_section H.hΩ H.two hK hAe hKN
  have hJ2 : IsPGroup 2 ((tightCore R).subgroupOf (p23XE R e x)) := hK2.comap_subtype
  have hmem : ∀ L ∈ CoreAssembly.conjClass ((tightCore R).subgroupOf (p23XE R e x)),
      IsPGroup 2 L := by
    rintro _ ⟨g, rfl⟩
    exact isPGroup_conjSub g hJ2
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥(p23XE R e x))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(p23XE R e x)
  have hfam : quotFamily (CoreAssembly.conjClass ((tightCore R).subgroupOf (p23XE R e x)))
      (classicalInvolutionOddCore ↥(p23XE R e x)) =
      SectionThmD.secClass (p23XE R e x) (tightCore R) :=
    image_conjClass (N := classicalInvolutionOddCore ↥(p23XE R e x))
      ((tightCore R).subgroupOf (p23XE R e x))
  have hq := OddQuot.hypOmegaGen_quotFamily hΩX hmem hNodd
  have hAall := aEmpty_forall_of_transitive hΩX.conjInvariant (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) hAJ
  have hAq := OddQuot.aEmpty_quotFamily hΩX hmem hNodd hAall
  rw [hfam] at hq hAq
  refine ⟨hq, SectionThmD.isPGroup_of_mem_secClass hK2, ?_, hAq,
    SectionThmD.pSpan_secClass hKN (H.gen_N hT hoc), SectionThmD.secClass_trans,
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥(p23XE R e x)⟩
  rintro _ ⟨g, rfl⟩
  obtain ⟨e8⟩ := H.q8_of_mem hK
  exact ⟨(Twin1711.conjSubEquiv (secImage (p23XE R e x) (tightCore R)) g).symm.trans
    ((SectionThmD.secImageEquiv hKN hK2).trans e8)⟩

theorem x0_of_twinE4 (mv : E4ModelMove) (hT : Thm4RTwinBelow 3 n) (hA : MFA)
    (he : ¬ ∀ y ∈ p23XE R e x, e * y = y * e)
    (het : ¬ ∀ y ∈ p23XE R e x, (e * t) * y = y * (e * t))
    (hno : ¬ TightInO2 (secInv (p23XE R e x) ⟨t, H.t_mem_N⟩))
    (h : TwinE4 (SecQuot (p23XE R e x))) :
    ∃ x₀ ∈ p23XE R e x, x₀ * t = t * x₀ ∧ IsPGroup 3 (Subgroup.zpowers x₀) ∧
      x₀ * e * x₀⁻¹ ≠ e := by
  set N := p23XE R e x
  have hoc : classicalInvolutionOddCore ↥N ≤ Subgroup.center ↥N := H.oc hA
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥N)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥N
  have hF := H.q8Pre_sec hT hoc
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hKN : tightCore R ≤ N := H.K_le_N
  have hz : IsUniqueInvolution (secImage N (tightCore R)) (secInv N ⟨t, H.t_mem_N⟩) :=
    SectionThmD.isUniqueInvolution_secImage hKN (H.two _ hK) H.hz
  have hKcls : secImage N (tightCore R) ∈ SectionThmD.secClass N (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  set φ : ↥N →* SecQuot N := QuotientGroup.mk' (classicalInvolutionOddCore ↥N)
  set e₁ : ↥N := ⟨e, H.e_mem_N⟩
  set t₁ : ↥N := ⟨t, H.t_mem_N⟩
  have hee : e * e = 1 := H.cfg.data.he2
  have heC : e ∈ Subgroup.centralizer ({t} : Set Y) := by
    obtain ⟨c, -, rfl⟩ := H.eO2
    exact c.2
  have hte : t * e = e * t := (Subgroup.mem_centralizer_singleton_iff.mp heC).symm
  have he₁2 : e₁ * e₁ = 1 := Subtype.ext hee
  have ht₁2 : t₁ * t₁ = 1 := Subtype.ext H.hz.sq
  have het₁ : (e₁ * t₁) * (e₁ * t₁) = 1 := by
    refine Subtype.ext ?_
    show (e * t) * (e * t) = 1
    calc (e * t) * (e * t) = e * (t * e) * t := by group
      _ = e * (e * t) * t := by rw [hte]
      _ = (e * e) * (t * t) := by group
      _ = 1 := by rw [hee, H.hz.sq, one_mul]
  have hcen : ∀ {b : ↥N}, b * b = 1 → (∀ y : SecQuot N, φ b * y = y * φ b) →
      ∀ y : ↥N, b * y = y * b := fun hb2 hb =>
    comm_of_comm_quot hoc hodd hb2 hb
  obtain ⟨c, ⟨m, hc3⟩, hct, hca⟩ := exists_three_of_twinE4 mv hF hKcls hz hno h (a := φ e₁)
    (by rw [← map_mul, he₁2, map_one])
    (by
      rintro _ ⟨k, hk, rfl⟩
      have hke : e * (k : Y) = (k : Y) * e :=
        (Subgroup.mem_centralizer_singleton_iff.mp
          (H.K_le_Ce (Subgroup.mem_subgroupOf.mp hk))).symm
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext hke))
    (fun hall => he fun y hy => congrArg Subtype.val (hcen he₁2 hall ⟨y, hy⟩))
    (fun hall => het fun y hy => congrArg Subtype.val (hcen het₁ (by
      intro z
      rw [map_mul]
      exact hall z) ⟨y, hy⟩))
  obtain ⟨x₁, hxy, ⟨m', hm'⟩, hxt⟩ := exists_lift_three_quot hoc ht₁2 hc3 hct
  refine ⟨(x₁ : Y), x₁.2, congrArg Subtype.val hxt,
    isPGroup_three_zpowers (m := m') (by simpa using congrArg Subtype.val hm'), fun hxe => hca ?_⟩
  have hxe' : x₁ * e₁ = e₁ * x₁ := by
    refine Subtype.ext ?_
    show (x₁ : Y) * e = e * (x₁ : Y)
    calc (x₁ : Y) * e = ((x₁ : Y) * e * (x₁ : Y)⁻¹) * (x₁ : Y) := by group
      _ = e * (x₁ : Y) := by rw [hxe]
  rw [← hxy, ← map_mul, ← map_mul, hxe']

end ZCtx

end Branch

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig
