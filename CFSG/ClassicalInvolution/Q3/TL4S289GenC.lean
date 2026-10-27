module

public import CFSG.ClassicalInvolution.Q3.TL4S289GenA
public import CFSG.ClassicalInvolution.Q3.TL4S289GenCS4
public import CFSG.ClassicalInvolution.Q3.TL4S289Z
public import CFSG.ClassicalInvolution.Q3.TL4E3S3NBG
public import CFSG.ClassicalInvolution.Q3.Q3AM289Shape
public import CFSG.ClassicalInvolution.Q3.TL4E3C269G9Fin
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenL3
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenU3
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenM12

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

namespace S289G

section Gen

variable {X : Type} [Group X]

theorem mul_comm_of_mem_omegaStarNbr [Finite X] {Φ : Set (Subgroup X)} (hΩ : HypOmegaGen Φ)
    {L L' : Subgroup X} (hst : L' ∈ omegaStarNbr Φ L) {a b : X} (ha : IsUniqueInvolution L a)
    (hb : IsUniqueInvolution L' b) : a * b = b * a := by
  obtain ⟨-, -, U, hU, hUK, hUN⟩ := hst
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hbN : b ∈ Subgroup.normalizer (L : Set X) :=
    hUN (T3.mem_of_isPGroup hb hUK (Sec6Gen.isPGroup_of_mem_USet hΩ hU) (by omega))
  have h1 := ha.conj_eq (mem_normalizer_iff_conjSub_eq.mp hbN)
  calc a * b = (b * a * b⁻¹) * b := by rw [h1]
    _ = b * a := by group

theorem sup_centralizer_conj {a b : X}
    (h : Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({b} : Set X) = ⊤) (g : X) :
    Subgroup.centralizer ({g * a * g⁻¹} : Set X) ⊔
      Subgroup.centralizer ({g * b * g⁻¹} : Set X) = ⊤ := by
  have key : ∀ c : X, (Subgroup.centralizer ({c} : Set X)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ({g * c * g⁻¹} : Set X) := by
    rintro c _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    show g * y * g⁻¹ * (g * c * g⁻¹) = g * c * g⁻¹ * (g * y * g⁻¹)
    calc g * y * g⁻¹ * (g * c * g⁻¹) = g * (y * c) * g⁻¹ := by group
      _ = g * (c * y) * g⁻¹ := by rw [hy]
      _ = g * c * g⁻¹ * (g * y * g⁻¹) := by group
  rw [eq_top_iff]
  intro x _
  have hx : g⁻¹ * x * g ∈ Subgroup.centralizer ({a} : Set X) ⊔
      Subgroup.centralizer ({b} : Set X) := by
    rw [h]
    exact Subgroup.mem_top _
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  rw [Subgroup.map_sup] at h1
  have h2 := sup_le_sup (key a) (key b) h1
  rwa [show (MulAut.conj g).toMonoidHom (g⁻¹ * x * g) = x by
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group] at h2

end Gen

section Link


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem noGNbr_of_linkTrans (hL : TightLargeHypR 3 n Y R S t) (htr : LinkTrans R t)
    (hA : ¬ TriNbrAll R t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    NoGNbr R t J := by
  have h := TightLargeHypR.typeRFam hL
  obtain ⟨J₀, hJ₀, hbad⟩ := exists_noGNbr_of_not_triNbrAll hA
  obtain ⟨gb, hgb⟩ := htr _ (subgroupOf_mem_linkRestrict (t := t) hJ₀) _
    (subgroupOf_mem_linkRestrict (t := t) hJ)
  rw [Generic.conjSub_subgroupOf] at hgb
  have hle : conjSub (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J₀) ≤ linkGrp R t := by
    have h1 := conjSub_mono (n := (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t))
      (le_linkGrp (t := t) hJ₀)
    rwa [conjSub_eq_self_of_mem gb.2] at h1
  have h1 := Subgroup.subgroupOf_inj.mp hgb
  rw [inf_of_le_left hle, inf_of_le_left (le_linkGrp (t := t) hJ)] at h1
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective
    (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
  have hg₀C : (g₀ : Y) ∈ Subgroup.centralizer ({t} : Set Y) := layerY_le_centralizer g₀.2
  have h2 : secImg (CoreAssembly.conjClass (tightCore R)) t (conjSub (g₀ : Y) J₀) =
      secImg (CoreAssembly.conjClass (tightCore R)) t J := by
    rw [← conjSub_secImg]
    show conjSub (QuotientGroup.mk g₀) _ = _
    rw [hg₀]
    exact h1
  have hJ₀g := conjSub_mem_omegaNbr_core hL hJ₀ hg₀C
  obtain ⟨ν, -, hJeq⟩ := exists_conj_of_secImg_eq h (xMem_of_mem_omegaNbr_core hL hJ₀g)
    (xMem_of_mem_omegaNbr_core hL hJ) h2
  have hc : (ν : Y) * g₀ ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mul_mem _ (layerY_le_centralizer ν.2) hg₀C
  rw [hJeq, ← conjSub_mul]
  exact noGNbr_conj hL hbad hc

theorem mul_mem_center_link (hL : TightLargeHypR 3 n Y R S t) (htr : LinkTrans R t)
    (hA : ¬ TriNbrAll R t) :
    ∀ M ∈ linkFam R t, ∀ N ∈ omegaNbr (linkFam R t) M, ∀ m n' : ↥(linkGrp R t),
      IsUniqueInvolution M m → IsUniqueInvolution N n' →
        m * n' ∈ Subgroup.center ↥(linkGrp R t) := by
  intro M hM N hN m n' hm hn'
  have hNΦ := hN.1
  obtain ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩ := hM
  obtain ⟨_, ⟨K, hK, rfl⟩, -, rfl⟩ := hNΦ
  have h := TightLargeHypR.typeRFam hL
  have hd := hL.datum
  have hJx := xMem_of_mem_omegaNbr_core hL hJ
  have hKx := xMem_of_mem_omegaNbr_core hL hK
  have hnbr := omegaNbr_secFam_of_link hL hJ hK hN
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hd.hypOmegaGen hJ.1
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hd.hypOmegaGen hK.1
  have ha := isUniqueInvolution_secImg h hJx hu
  have hb := isUniqueInvolution_secImg h hKx hw
  have hc := isUniqueInvolution_secImg h (xMem_core hL) hd.isUniqueInvolution_core
  have e := mul_eq_of_noGNbr hL hJ (noGNbr_of_linkTrans hL htr hA hJ) hK hnbr ha hb hc
  have hm' : (m : SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t))
        ⟨u, mem_layerY_of_isUniqueInvolution h hJx hu⟩ :=
    congrArg Subtype.val (hm.eq (isUniqueInvolution_subgroupOf ha (le_linkGrp hJ)))
  have hn'' : (n' : SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t))
        ⟨w, mem_layerY_of_isUniqueInvolution h hKx hw⟩ :=
    congrArg Subtype.val (hn'.eq (isUniqueInvolution_subgroupOf hb (le_linkGrp hK)))
  set c : SecQuot (CoreAssembly.conjClass (tightCore R)) t := QuotientGroup.mk'
    (classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t))
    ⟨t, mem_layerY_of_isUniqueInvolution h (xMem_core hL) hd.isUniqueInvolution_core⟩ with hcdef
  have hcZ : ∀ z : SecQuot (CoreAssembly.conjClass (tightCore R)) t, c * z = z * c := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) z
    rw [hcdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (layerY_le_centralizer y.2)).symm
  have key : ((m * n' : ↥(linkGrp R t)) : SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      c := by
    rw [Subgroup.coe_mul, hm', hn'', e, ← mul_assoc, ← hcZ, mul_assoc, ha.sq, mul_one]
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  have e1 : ((x * (m * n') : ↥(linkGrp R t)) : SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      (x : SecQuot (CoreAssembly.conjClass (tightCore R)) t) * c := by
    rw [Subgroup.coe_mul, key]
  have e2 : ((m * n' * x : ↥(linkGrp R t)) : SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      c * (x : SecQuot (CoreAssembly.conjClass (tightCore R)) t) := by
    rw [Subgroup.coe_mul, key]
  rw [e1, e2]
  exact (hcZ _).symm

end Link

section S3


theorem linkModelFacts_of_lieS3 {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (h : SecIdLieS3 Φ) : Q3T8.Asc77.LinkModelFacts X := by
  obtain ⟨c, hc, ψ, hsurj, hker⟩ : ∃ c : CompData, (c = CompData.model .PSU 3 ∨
      c = CompData.model .G2 0 ∨ c = CompData.model .trialityD4 0) ∧
      ∃ ψ : c.G →* X, Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center c.G := by
    rcases h with ⟨ψ, h1, h2, -⟩ | ⟨ψ, h1, h2, -⟩ | ⟨ψ, h1, h2, -⟩
    · exact ⟨_, Or.inl rfl, ψ, h1, h2⟩
    · exact ⟨_, Or.inr (Or.inl rfl), ψ, h1, h2⟩
    · exact ⟨_, Or.inr (Or.inr rfl), ψ, h1, h2⟩
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (Q3T8.Asc77.center_eq_bot_of_rows hc).le
  refine Q3T8.Asc77.LinkModelFacts.of_mulEquiv (MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm ?_
  rcases hc with rfl | rfl | rfl
  · exact Q3T8.Asc77.linkModelFacts_psu3_model
  · exact Q3T8.Asc77.linkModelFacts_of_gen
      (Q3T8.Asc77.involutionsConj_of_rows (Or.inr (Or.inl rfl)))
      (Q3W.EX.genFact3_g2 (show CFSG.Assembly.LowTwoRank.StatedLieAdmissible .G2 0 3 1 from
        ⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩))
  · exact Q3T8.Asc77.linkModelFacts_of_gen
      (Q3T8.Asc77.involutionsConj_of_rows (Or.inr (Or.inr rfl)))
      (Q3W.EX.genFact3_td4 (show CFSG.Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 0 3 1
        from ⟨Nat.prime_three, le_rfl, rfl⟩))

theorem starFrameGenAll_of_lieS3 {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') (hid : SecIdMuS3S4Id Φ)
    (hN : SecIdStarNbrId3) (hS3 : SecIdLieS3 Φ) {L : Subgroup X} (hL : L ∈ Φ) :
    StarFrameGenAll Φ L := by
  have hLMF := linkModelFacts_of_lieS3 hS3
  obtain ⟨L', hL'Φ, hst, hn⟩ := hN X Φ h hO hgen htr hid L hL
  obtain ⟨b, hb⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL'Φ
  refine StarFrameGenAll.of_pair hst hn hb fun a ha => ?_
  have hne : a ≠ b := fun e => hst.2.1 (h.noTwins L hL L' ⟨hL'Φ, a, ha, e ▸ hb⟩)
  exact hLMF.2 a b ha.sq ha.ne_one hb.sq hb.ne_one hne
    (mul_comm_of_mem_omegaStarNbr h.hyp hst ha hb)

end S3

section Exit


theorem starFrameGenAll_of_exitS3 {n : ℕ} {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (h6 : Thm6RBelow 3 n) (hX : Nat.card X < n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') (hid : SecIdMuS3S4Id Φ)
    (hN : SecIdStarNbrId3) (hE : SecIdExitS3 Φ) {L : Subgroup X} (hL : L ∈ Φ) :
    StarFrameGenAll Φ L := by
  obtain ⟨-, -, R, S, z, hm, heq, hO2, hout⟩ := hE
  obtain ⟨L', hL'Φ, hst, hn⟩ := hN X Φ h hO hgen htr hid L hL
  obtain ⟨b, hb⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL'Φ
  refine StarFrameGenAll.of_pair hst hn hb fun a ha => ?_
  have hz := hm.datum.isUniqueInvolution_core
  have hLc : ∃ g : X, conjSub g (tightCore R) = L := by
    have h1 : L ∈ CoreAssembly.conjClass (tightCore R) := by rw [heq]; exact hL
    exact h1
  have hL'c : ∃ g : X, conjSub g (tightCore R) = L' := by
    have h1 : L' ∈ CoreAssembly.conjClass (tightCore R) := by rw [heq]; exact hL'Φ
    exact h1
  obtain ⟨g, hg⟩ := hLc
  obtain ⟨g', hg'⟩ := hL'c
  have hag : a = g * z * g⁻¹ := ha.eq (hg ▸ hz.conj g)
  have hbg : b = g' * z * g'⁻¹ := hb.eq (hg' ▸ hz.conj g')
  have hab := mul_comm_of_mem_omegaStarNbr h.hyp hst ha hb
  have hne : a ≠ b := fun e => hst.2.1 (h.noTwins L hL L' ⟨hL'Φ, a, ha, e ▸ hb⟩)
  have hex : TightEx X R S z := by
    rcases hout with ⟨h3, -⟩ | hM12
    · exact Or.inr (Or.inl ⟨hm.edgeless, h3⟩)
    · obtain ⟨e⟩ := hM12
      refine Or.inr (Or.inr (Or.inl ⟨hm.edgeless, e.toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center X)), ?_, ?_⟩))
      · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
      · have hk : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker =
            Subgroup.center X := by
          ext x
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
            MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        rw [hk]
        exact TC.Thin.isPGroup_center_of_oddCore hO
  set s := g⁻¹ * b * g with hs
  have hzs : z * s = s * z := by
    have e1 : z = g⁻¹ * a * g := by rw [hag]; group
    rw [hs, e1]
    calc g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
      _ = g⁻¹ * (b * a) * g := by rw [hab]
      _ = g⁻¹ * b * g * (g⁻¹ * a * g) := by group
  have hsz : s ≠ z := fun e => hne (by rw [hag, ← e, hs]; group)
  have hsconj : ∃ k : X, s = k * z * k⁻¹ := ⟨g⁻¹ * g', by rw [hs, hbg]; group⟩
  have hgen' := E3S3NBG.sup_centralizer_of_edgeless_exit e3C269L2_proved e3S3GenL3_proved
    e3S3GenU3_proved e3S3GenM12_proved modelM12Acts3_proved secIdE4Edge_proved h6 hX hm.datum
    (tightClsR_three_iff.mp hm.cls) hex hm.edgeless hO2 hzs hsz hsconj
  have h2 := sup_centralizer_conj hgen' g
  rw [← hag, show g * s * g⁻¹ = b by rw [hs]; group] at h2
  rw [eq_top_iff, ← h2]
  exact le_sup_left

end Exit

section Main


variable {n : ℕ}

theorem tightStar289FrameGenR_of (hN : SecIdStarNbrId3) (hS4 : SecIdStarGenS4)
    (h6 : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      TightLargeHypR 3 n Y R S t → Thm6RBelow 3 n) :
    TightStar289FrameGenR n := by
  intro Y _ _ R S t hL _ hA hcase J hJ
  have hΦ := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  have hO := oddCore_linkGrp_eq_bot hL
  have hgen := omegaGen_linkRestrict (R := R) (t := t)
  have h284 := mul_mem_center_link hL hcase.1 hA
  have hJ' := subgroupOf_mem_linkRestrict (t := t) hJ
  rcases hcase.2.2 with hS3 | hS4' | hEx | hE8 | hE64 | hSp6 | hWN
  · exact starFrameGenAll_of_lieS3 hΦ hO hgen hcase.1 hcase.2 hN hS3 hJ'
  · exact hS4 _ _ hΦ hO hgen hcase.1 hcase.2.1 hS4' h284 _ hJ'
  · exact starFrameGenAll_of_exitS3 (h6 Y R S t hL) (S289.natCard_linkGrp_lt hL) hΦ hO hgen
      hcase.1 hcase.2 hN hEx hJ'
  · exact starFrameGenAll_of_dstarConnected hΦ hgen hE8.2 h284 hJ'
  · exact starFrameGenAll_of_dstarConnected hΦ hgen hE64.2 h284 hJ'
  · exact starFrameGenAll_of_dstarConnected hΦ hgen hSp6.2.2 h284 hJ'
  · exact starFrameGenAll_of_dstarConnected hΦ hgen hWN.2.2 h284 hJ'

theorem tightStar289GenR_of (hN : SecIdStarNbrId3) (hS4 : SecIdStarGenS4)
    (h6 : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      TightLargeHypR 3 n Y R S t → Thm6RBelow 3 n) :
    TightStar289GenR 3 n :=
  tightStar289GenR_of_frameGen hN (tightStar289FrameGenR_of hN hS4 h6)

end Main

end S289G

end CFSG.ClassicalInvolution.Q3.TL4
