module

public import CFSG.ClassicalInvolution.Q3.Q3T8AF04
public import CFSG.ClassicalInvolution.Q3.Q3T8AFZ

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3T8.AF
open scoped commutatorElement

section Helpers


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

noncomputable abbrev layerHom (Ω : Set (Subgroup G)) (z : G) :
    ↥(Q3NL.exactLayer3 Ω z) →* Q3T7.layerQuot3 Ω z :=
  QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω z))

theorem exists_mul_mem_centralizer {Y O : Subgroup G} (hodd : Odd (Nat.card O))
    (hYn : ∀ y ∈ Y, ∀ o ∈ O, y * o * y⁻¹ ∈ O) {c y : G} (hc : c ∈ Y) (hc2 : c * c = 1)
    (hcomm : ⁅y, c⁆ ∈ O) :
    ∃ o ∈ O, o⁻¹ * y ∈ Subgroup.centralizer ({c} : Set G) := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hc'2 : (y * c * y⁻¹) * (y * c * y⁻¹) = 1 := by
    calc y * c * y⁻¹ * (y * c * y⁻¹) = y * (c * c) * y⁻¹ := by group
      _ = 1 := by rw [hc2]; group
  have h1 : c⁻¹ * (y * c * y⁻¹) ∈ O := by
    have h2 := hYn c⁻¹ (Y.inv_mem hc) _ hcomm
    rw [commutatorElement_def] at h2
    convert h2 using 1
    group
  obtain ⟨o, ho, hoe⟩ := exists_conj_of_inv_mul_mem hc2 hc'2 hodd h1
  refine ⟨o, ho, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : (o⁻¹ * y) * c * (o⁻¹ * y)⁻¹ = c := by
    calc (o⁻¹ * y) * c * (o⁻¹ * y)⁻¹ = o⁻¹ * (y * c * y⁻¹) * o := by group
      _ = o⁻¹ * (o * c * o⁻¹) * o := by rw [hoe]
      _ = c := by group
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem isUniqueInvolution_layerImg3 {z : G} {A : Subgroup G} {tA : G}
    (hA : A ∈ Q3NL.tqMembers3 Ω z) (htA : IsUniqueInvolution A tA) :
    ∃ h : tA ∈ Q3NL.exactLayer3 Ω z,
      IsUniqueInvolution (Layer.layerImg3 Ω z A) (layerHom Ω z ⟨tA, h⟩) := by
  have hodd := Layer.odd_natCard_oddCore_exactLayer3 (Ω := Ω) (x := z)
  have hAL := Layer.isUniqueInvolution_exactCore3 hA.2.1 htA
  have hAY := isUniqueInvolution_subgroupOf hAL (Q3NL.exactCore3_le_exactLayer3 hA)
  have hAb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _) hAY
  exact ⟨Q3NL.exactCore3_le_exactLayer3 hA hAL.mem, hAb⟩

theorem layerImg3_conj_Y {z : G} {K : Subgroup G} (y : ↥(Q3NL.exactLayer3 Ω z)) :
    Layer.layerImg3 Ω z (conjSub (y : G) K) =
      conjSub (layerHom Ω z y) (Layer.layerImg3 Ω z K) := by
  have hyc : (y : G) ∈ T8.cenZ z := Layer.exactLayer3_le_cenZ Ω z y.2
  unfold Layer.layerImg3
  rw [← Layer.exactCore3_conj_cen hyc, ← conjSub_subgroupOf, AscQuot.map_conjSub]

theorem comm_mem_oddCoreOf_iff {z : G} (y c : ↥(Q3NL.exactLayer3 Ω z)) :
    ⁅(y : G), (c : G)⁆ ∈ oddCoreOf (Q3NL.exactLayer3 Ω z) ↔
      layerHom Ω z y * layerHom Ω z c = layerHom Ω z c * layerHom Ω z y := by
  constructor
  · intro h
    obtain ⟨k, hk, hke⟩ := h
    have hk' : k = ⁅y, c⁆ := Subtype.ext hke
    have h1 : layerHom Ω z ⁅y, c⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hk' ▸ hk)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · intro h
    have h1 : layerHom Ω z ⁅y, c⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨_, h2, by simp [commutatorElement_def]⟩

end Helpers

section Pure


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exactLayer3_le_normalizer_alpha [IsSimpleGroup G] {K₀ : Subgroup G}
    (hs : Q3.Disc3.AscStand3 Ω K₀) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    {K A B : Subgroup G} {z tA tB : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hA : A ∈ omegaNbr Ω K) (hB : B ∈ omegaNbr Ω K) (htA : IsUniqueInvolution A tA)
    (htB : IsUniqueInvolution B tB) (hAB : B ∈ omegaNbr Ω A)
    (hind : tB ∉ Subgroup.closure ({z, tA} : Set G))
    (hgen : ∀ (h₁ : tA ∈ Q3NL.exactLayer3 Ω z) (h₂ : tB ∈ Q3NL.exactLayer3 Ω z),
      Subgroup.centralizer ({layerHom Ω z ⟨tA, h₁⟩} : Set (Q3T7.layerQuot3 Ω z)) ⊔
        Subgroup.centralizer ({layerHom Ω z ⟨tB, h₂⟩} : Set (Q3T7.layerQuot3 Ω z)) ⊔
        Subgroup.centralizer ({layerHom Ω z ⟨tA, h₁⟩ * layerHom Ω z ⟨tB, h₂⟩} :
          Set (Q3T7.layerQuot3 Ω z)) = ⊤) :
    Q3NL.exactLayer3 Ω z ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({tA, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaMod Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hs.hyp
  set Y : Subgroup G := Q3NL.exactLayer3 Ω z with hY
  set α₀ : Subgroup G := alphaOf (Subgroup.closure ({tA, z} : Set G)) with hα₀
  obtain ⟨hbal, -⟩ := alpha_of_triangle hs hnt hK hz htA htB hA hB hAB hind
  have hOA : oddCoreOf Y ≤ Subgroup.normalizer (α₀ : Set G) :=
    oddCore_le_normalizer_alpha hs hnt hK hz hA hB htA htB hAB hind
  have hodd : Odd (Nat.card (oddCoreOf Y)) := oddCoreOf_odd_natCard Y
  have hOY : oddCoreOf Y ≤ Y := oddCoreOf_le_self Y
  have hYn : ∀ y ∈ Y, ∀ o ∈ oddCoreOf Y, y * o * y⁻¹ ∈ oddCoreOf Y := fun y hy o ho =>
    T7R.conj_mem_oddCoreOf hy ho
  have hABc : tA * tB = tB * tA := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ htA hAB htB
  have hzA : z * tA = tA * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hA htA
  have hzB : z * tB = tB * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hB htB
  have htAY : tA ∈ Y := Q3NL.exactCore3_le_exactLayer3
    (mem_tqMembers3_of_omegaNbr hΩ hnt hz hA htA)
    ⟨htA.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzA.symm⟩
  have htBY : tB ∈ Y := Q3NL.exactCore3_le_exactLayer3
    (mem_tqMembers3_of_omegaNbr hΩ hnt hz hB htB)
    ⟨htB.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzB.symm⟩
  have hkey : ∀ c : G, c ∈ Y → c * c = 1 →
      alphaOf (Subgroup.closure ({c, z} : Set G)) = α₀ →
      ∀ y ∈ Y, ⁅y, c⁆ ∈ oddCoreOf Y → y ∈ Subgroup.normalizer (α₀ : Set G) := by
    intro c hcY hc2 hαc y hyY hcomm
    obtain ⟨o, ho, hy'⟩ := exists_mul_mem_centralizer hodd hYn hcY hc2 hcomm
    have hy'Y : o⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem (hOY ho)) hyY
    have hyz : o⁻¹ * y ∈ Subgroup.centralizer ({z} : Set G) :=
      Q3NL.exactLayer3_le_centralizer Ω z hy'Y
    have hcent : o⁻¹ * y ∈
        Subgroup.centralizer ((Subgroup.closure ({c, z} : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      rintro h (rfl | rfl)
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hy').symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hyz).symm
    have hmem : o⁻¹ * y ∈ Subgroup.normalizer (α₀ : Set G) :=
      T8T.centralizer_le_normalizer_of_alphaOf_eq hαc hcent
    have e : y = o * (o⁻¹ * y) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hOA ho) hmem
  have htBz : tB ≠ z := fun h => hB.2.1 (hnt K hK B ⟨hB.1, z, hz, h ▸ htB⟩)
  have htAB1 : tA * tB ≠ 1 := fun h => by
    have : tB = tA := by
      have h1 : tA⁻¹ = tB := inv_eq_of_mul_eq_one_right h
      rw [← h1]
      exact inv_eq_of_mul_eq_one_right htA.sq
    exact hind (this ▸ Subgroup.subset_closure (by simp))
  have htABz : tA * tB ≠ z := fun h => by
    have : tB = tA * z := by
      have h1 : tB = tA⁻¹ * z := by rw [← h]; group
      rwa [inv_eq_of_mul_eq_one_right htA.sq] at h1
    exact hind (this ▸ Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hc₃2 : (tA * tB) * (tA * tB) = 1 := by
    calc tA * tB * (tA * tB) = tA * (tB * tA) * tB := by group
      _ = tA * (tA * tB) * tB := by rw [← hABc]
      _ = (tA * tA) * (tB * tB) := by group
      _ = 1 := by rw [htA.sq, htB.sq, one_mul]
  have hc₃Y : tA * tB ∈ Y := Y.mul_mem htAY htBY
  have hz₃ : (tA * tB) * z = z * (tA * tB) := by
    calc tA * tB * z = tA * (tB * z) := by group
      _ = tA * (z * tB) := by rw [hzB]
      _ = (tA * z) * tB := by group
      _ = (z * tA) * tB := by rw [hzA]
      _ = z * (tA * tB) := by group
  have hle₂ : Subgroup.closure ({tB, z} : Set G) ≤ Subgroup.closure ({z, tA, tB} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hle₃ : Subgroup.closure ({tA * tB, z} : Set G) ≤
      Subgroup.closure ({z, tA, tB} : Set G) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
  have hα₂ : alphaOf (Subgroup.closure ({tB, z} : Set G)) = α₀ :=
    hbal _ hle₂ (T7A.isElemAbelian2_closure_pair htB.sq hz.sq htB.ne_one hz.ne_one htBz hzB.symm)
  have hα₃ : alphaOf (Subgroup.closure ({tA * tB, z} : Set G)) = α₀ :=
    hbal _ hle₃ (T7A.isElemAbelian2_closure_pair hc₃2 hz.sq htAB1 hz.ne_one htABz hz₃)
  set S : Subgroup ↥Y := (Subgroup.normalizer (α₀ : Set G)).subgroupOf Y with hS
  have hC : ∀ (c : G) (hcY : c ∈ Y), c * c = 1 →
      alphaOf (Subgroup.closure ({c, z} : Set G)) = α₀ →
      Subgroup.centralizer ({layerHom Ω z ⟨c, hcY⟩} : Set (Q3T7.layerQuot3 Ω z)) ≤
        S.map (layerHom Ω z) := by
    intro c hcY hc2 hαc w hw
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ w
    refine ⟨y, ?_, rfl⟩
    have hcomm := (comm_mem_oddCoreOf_iff y ⟨c, hcY⟩).mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hw)
    exact hkey c hcY hc2 hαc y y.2 hcomm
  have htop : (⊤ : Subgroup (Q3T7.layerQuot3 Ω z)) ≤ S.map (layerHom Ω z) := by
    rw [← hgen htAY htBY]
    refine sup_le (sup_le (hC tA htAY htA.sq rfl) (hC tB htBY htB.sq hα₂)) ?_
    have e : layerHom Ω z ⟨tA * tB, hc₃Y⟩ =
        layerHom Ω z ⟨tA, htAY⟩ * layerHom Ω z ⟨tB, htBY⟩ := by
      rw [← map_mul]
      rfl
    rw [← e]
    exact hC (tA * tB) hc₃Y hc₃2 hα₃
  intro y hy
  obtain ⟨s, hs, hsy⟩ := htop (Subgroup.mem_top (layerHom Ω z ⟨y, hy⟩))
  have h1 : s⁻¹ * ⟨y, hy⟩ ∈ classicalInvolutionOddCore ↥Y := QuotientGroup.eq.mp hsy
  have h2 : ((s⁻¹ * ⟨y, hy⟩ : ↥Y) : G) ∈ oddCoreOf Y := ⟨_, h1, rfl⟩
  have h3 : (s : G) ∈ Subgroup.normalizer (α₀ : Set G) := Subgroup.mem_subgroupOf.mp hs
  have e : y = (s : G) * ((s⁻¹ * ⟨y, hy⟩ : ↥Y) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem _ h3 (hOA h2)

end Pure

section Main



theorem pureLinkConst3_of_zFacts (hZ : ZLinkFacts3) : PureLinkConst3 := by
  intro G _ _ _ Ω K hs hnt z hz A B tA tB hA hB hAB htA htB hind ι D hpure J hJ tJ htJ
  have hΩ : HypOmegaMod Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hs.hyp
  have hK : K ∈ Ω := hs.mem
  have hx : z * z = 1 := hz.sq
  have hAt := mem_tqMembers3_of_omegaNbr hΩ hnt hz hA htA
  have hBt := mem_tqMembers3_of_omegaNbr hΩ hnt hz hB htB
  have hJt := mem_tqMembers3_of_omegaNbr hΩ hnt hz hJ htJ
  have hne : (Q3NL.tqMembers3 Ω z).Nonempty := ⟨A, hAt⟩
  have hL : Layer.LayerHyp Ω z := Layer.LayerHyp.of_stand3 hs hx hne
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hx
  have hΨ : HypOmegaModU (.sl2 3 1) (Q3T7.layerFam3 Ω z) :=
    Q3T7.hypOmegaModU_layerFam3 hs hc2 hne
  have hntΨ := Layer.noTwins_layerFam3 hL hnt
  have hXA := xMem_of_omegaNbr hΩ hnt hz hA htA
  have hXB := xMem_of_omegaNbr hΩ hnt hz hB htB
  have hcAB : tA * tB = tB * tA := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ htA hAB htB
  have htne : tA ≠ tB := fun h => hind (h ▸ Subgroup.subset_closure (by simp))
  have himg : Layer.layerImg3 Ω z A ≠ Layer.layerImg3 Ω z B :=
    Layer.layerImg3_ne_of_involutions hL hXA hXB htA htB hcAB htne
  have hzA : z * tA = tA * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hA htA
  have hztq : z ∈ trivialOnQuot B := hXB.trivialOnQuot3 hΩ hx
  have htAtq : tA ∈ trivialOnQuot B :=
    (xMem_of_omegaNbr hΩ hnt htA hAB htB).trivialOnQuot3 hΩ htA.sq
  have hVtq : Subgroup.closure ({z, tA} : Set G) ≤ trivialOnQuot B := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hztq
    · exact htAtq
  have htAz : tA ≠ z := fun h => hA.2.1 (hnt K hK A ⟨hA.1, z, hz, h ▸ htA⟩)
  have hVab : IsElemAbelian2 (Subgroup.closure ({z, tA} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hz.sq htA.sq hz.ne_one htA.ne_one (Ne.symm htAz) hzA
  have hV2 : IsPGroup 2 ↥(Subgroup.closure ({z, tA} : Set G)) :=
    isPGroup_two_of_sq_eq_one hVab.2
  have hVcomm : ⁅Subgroup.closure ({z, tA} : Set G), B⁆ ≤ oddCoreOf B :=
    Subgroup.commutator_le.mpr fun a ha x hx => (hVtq ha).2 x hx
  obtain ⟨R, hR, hRc⟩ := AscE184Sect.exists_isSylow2In_centralizer hV2 hVcomm
  have hRcl : ∀ r ∈ R, z * r = r * z ∧ tA * r = r * tA := by
    intro r hr
    have h := hRc hr
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff] at h
    exact ⟨h z (by simp), h tA (by simp)⟩
  have hRz : R ≤ T8.cenZ z := by
    rw [T8.cenZ_eq_centralizer]
    exact fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hRcl r hr).1.symm
  have hRtA : R ≤ Subgroup.centralizer ({tA} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRcl r hr).2.symm
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hB.1 hR
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
  have hRN : R ≤ Subgroup.normalizer (A : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hA.1 hB.1 hAB.2.1.symm htA hR.1 hR.2.1
      (by omega) hRtA
  have hadj : Layer.layerImg3 Ω z B ∈
      omegaNbr (Q3T7.layerFam3 Ω z) (Layer.layerImg3 Ω z A) :=
    Layer.layerImg3_omegaNbr hAt hBt hR hRz hRN himg
  obtain ⟨iA, RA, hRA, hAR⟩ := D.fundamental _ (Layer.layerImg3_mem hAt)
  obtain ⟨iB, RB, hRB, hBR⟩ := D.fundamental _ (Layer.layerImg3_mem hBt)
  have hiB : iB = iA := hpure B hB iB iA RB RA hBR hAR
  subst hiB
  obtain ⟨hgenZ, hconjZ⟩ := hZ (Q3T7.layerQuot3 Ω z) (Q3T7.layerFam3 Ω z) ι D hΨ hntΨ _ _
    (Layer.layerImg3_mem hAt) hadj iB RA RB hRA hRB hAR hBR
  obtain ⟨h₁, hu⟩ := isUniqueInvolution_layerImg3 hAt htA
  obtain ⟨h₂, hv⟩ := isUniqueInvolution_layerImg3 hBt htB
  set u := layerHom Ω z ⟨tA, h₁⟩ with hu_def
  set v := layerHom Ω z ⟨tB, h₂⟩ with hv_def
  have hZtop : Subgroup.centralizer ({u} : Set (Q3T7.layerQuot3 Ω z)) ⊔
      Subgroup.centralizer ({v} : Set (Q3T7.layerQuot3 Ω z)) ⊔
      Subgroup.centralizer ({u * v} : Set (Q3T7.layerQuot3 Ω z)) = ⊤ := by
    rw [eq_top_iff, ← D.generate]
    refine iSup_le fun j => ?_
    by_cases hj : j = iB
    · subst hj
      exact hgenZ u v hu hv
    · have huA : u ∈ RA.map (D.hom iB) := hAR ▸ hu.mem
      obtain ⟨r, -, hr⟩ := huA
      rintro _ ⟨r', rfl⟩
      refine Subgroup.mem_sup_left (Subgroup.mem_sup_left ?_)
      rw [Subgroup.mem_centralizer_singleton_iff, ← hr]
      exact (D.commute iB j (Ne.symm hj) r r').symm
  have hD1 := exactLayer3_le_normalizer_alpha hs hnt hK hz hA hB htA htB hAB hind
    (fun _ _ => hZtop)
  obtain ⟨iJ, RJ, hRJ, hJR⟩ := D.fundamental _ (Layer.layerImg3_mem hJt)
  have hiJ : iJ = iB := hpure J hJ iJ iB RJ RA hJR hAR
  subst hiJ
  obtain ⟨g, hg⟩ := hconjZ _ (Layer.layerImg3_mem hJt) RJ hRJ hJR
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hyz : (y : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Q3NL.exactLayer3_le_centralizer Ω z y.2
  have hyA : conjSub (y : G) A ∈ Q3NL.tqMembers3 Ω z :=
    Q3NL.conjSub_mem_tqMembers3 hΩ.conjInvariant hyz hAt
  have himgeq : Layer.layerImg3 Ω z (conjSub (y : G) A) = Layer.layerImg3 Ω z J := by
    rw [layerImg3_conj_Y, hg]
  obtain ⟨n, hn, hnJ⟩ := Layer.exists_oddCore_conj_of_layerImg3_eq hL hyA hJt himgeq
  have hnY : n ∈ Q3NL.exactLayer3 Ω z := oddCoreOf_le_self _ hn
  have hgY : n * (y : G) ∈ Q3NL.exactLayer3 Ω z :=
    (Q3NL.exactLayer3 Ω z).mul_mem hnY y.2
  have hJeq : J = conjSub (n * (y : G)) A := by rw [conjSub_mul]; exact hnJ.symm
  have htJeq : tJ = (n * (y : G)) * tA * (n * (y : G))⁻¹ := by
    have : IsUniqueInvolution J ((n * (y : G)) * tA * (n * (y : G))⁻¹) :=
      hJeq ▸ htA.conj (n * (y : G))
    exact htJ.eq this
  have hgz : (n * (y : G)) * z * (n * (y : G))⁻¹ = z := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp
      (Q3NL.exactLayer3_le_centralizer Ω z hgY)
    rw [mul_inv_eq_iff_eq_mul]
    exact h
  have hF : Subgroup.closure ({tJ, z} : Set G) =
      conjSub (n * (y : G)) (Subgroup.closure ({tA, z} : Set G)) := by
    rw [conjSub_closure_pair, hgz, htJeq]
  rw [hF, alphaOf_conjSub]
  exact mem_normalizer_iff_conjSub_eq.mp (hD1 hgY)

end Main

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
