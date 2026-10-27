module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264A
public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4B

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight

section Normal

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {r n : ℕ}

theorem normal_of_not_conj_of_mul_mem_center (h4 : Thm4RBelow r n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) (hgen : omegaGen Φ = ⊤)
    {A B : Subgroup Q} (hA : A ∈ Φ) (hB : B ∈ Φ) {x y : Q} (hx : IsUniqueInvolution A x)
    (hy : IsUniqueInvolution B y) (hxy : x * y ∈ Subgroup.center Q)
    (hnc : ¬ ∃ g : Q, conjSub g A = B) : A.Normal := by
  have hcl := h.hyp.conjInvariant
  have key : ∀ L ∈ Φ, ∀ l ∈ L, conjSub l A = A := by
    intro L hL l hl
    by_cases hc : ∃ g ∈ omegaGen Φ, conjSub g A = L
    · obtain ⟨g, -, rfl⟩ := hc
      have hnc' : ¬ ∃ g' ∈ omegaGen Φ, conjSub g' (conjSub g A) = B := by
        rintro ⟨g', -, hg'⟩
        exact hnc ⟨g' * g, by rw [conjSub_mul]; exact hg'⟩
      have hcomm := Vtx.commutes_of_not_conj h4 h hO hn (hcl g A hA) hB hnc'
      have hly : l * y = y * l := hcomm l hl y hy.mem
      have hlx : l * x * l⁻¹ = x := by
        have hc1 : l * (x * y) = (x * y) * l := Subgroup.mem_center_iff.mp hxy l
        have hly' : l * y⁻¹ = y⁻¹ * l := by
          calc l * y⁻¹ = y⁻¹ * (y * l) * y⁻¹ := by group
            _ = y⁻¹ * (l * y) * y⁻¹ := by rw [hly]
            _ = y⁻¹ * l := by group
        calc l * x * l⁻¹ = (l * (x * y)) * y⁻¹ * l⁻¹ := by group
          _ = (x * y) * (l * y⁻¹) * l⁻¹ := by rw [hc1]; group
          _ = (x * y) * (y⁻¹ * l) * l⁻¹ := by rw [hly']
          _ = x := by group
      have hxc : IsUniqueInvolution (conjSub l A) x := by
        have := hx.conj l
        rwa [hlx] at this
      exact h.noTwins A hA (conjSub l A) ⟨hcl l A hA, x, hx, hxc⟩
    · have hcomm := Vtx.commutes_of_not_conj h4 h hO hn hA hL hc
      exact Vtx.conjSub_eq_of_forall_commute fun a ha => (hcomm a ha l hl).symm
  have hN : omegaGen Φ ≤ Subgroup.normalizer (A : Set Q) :=
    iSup₂_le fun L hL l hl => mem_normalizer_iff_conjSub_eq.mpr (key L hL l hl)
  rw [hgen, top_le_iff] at hN
  exact Subgroup.normalizer_eq_top_iff.mp hN

end Normal

section Sec

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

omit [Finite G] in
theorem secImg_conjSub_eq_map (hcl : ConjInvariant Ω) {c : G}
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) (L : Subgroup G) :
    secImg Ω x (conjSub c L) = (secImg Ω x L).map (secAct hcl hc).toMonoidHom := by
  have hcY := mem_normalizer_layerY hcl hc
  have hact : ∀ (y : ↥(layerY Ω x)) (hyc : c * (y : G) * c⁻¹ ∈ layerY Ω x),
      (secAct hcl hc).toMonoidHom (QuotientGroup.mk' _ y) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨c * (y : G) * c⁻¹, hyc⟩ := by
    intro y hyc
    simp only [MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    exact s26Act_mk (layerY Ω x) ⟨c, hcY⟩ y ⟨c * (y : G) * c⁻¹, hyc⟩ rfl
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ coreAt x (conjSub c L) := Subgroup.mem_subgroupOf.mp hy
    rw [← conjSub_coreAt x hc, mem_conjSub_iff] at hy'
    have hyY : c⁻¹ * (y : G) * c ∈ layerY Ω x := by
      have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hcY)
        (y : G)).mp y.2
      simpa using h1
    refine ⟨QuotientGroup.mk' _ ⟨c⁻¹ * (y : G) * c, hyY⟩,
      ⟨⟨c⁻¹ * (y : G) * c, hyY⟩, Subgroup.mem_subgroupOf.mpr hy', rfl⟩, ?_⟩
    have hyc : c * ((⟨c⁻¹ * (y : G) * c, hyY⟩ : ↥(layerY Ω x)) : G) * c⁻¹ ∈ layerY Ω x := by
      simp [mul_assoc]
    rw [hact _ hyc]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]
  · rintro ⟨w', ⟨y, hy, rfl⟩, rfl⟩
    have hyc : c * (y : G) * c⁻¹ ∈ layerY Ω x := (Subgroup.mem_normalizer_iff.mp hcY (y : G)).mp y.2
    refine ⟨⟨c * (y : G) * c⁻¹, hyc⟩, ?_, (hact y hyc).symm⟩
    have hy' : (y : G) ∈ coreAt x L := Subgroup.mem_subgroupOf.mp hy
    show ((⟨c * (y : G) * c⁻¹, hyc⟩ : ↥(layerY Ω x)) : G) ∈ coreAt x (conjSub c L)
    rw [← conjSub_coreAt x hc]
    exact conj_mem_conjSub hy'

end Sec

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.secImg_normal_of_not_conj (h4 : Thm4RBelow r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hnc : ¬ SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t)) :
    (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)).Normal ∧
      (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J).Normal := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΦ := h.secFam (x := z * t)
  have hO := secQuot_oddCore_eq_bot (Ω := Ω) (x := z * t)
  have hn := hs.natCard_secQuot_lt
  have hgen := omegaGen_secFam (Ω := Ω) (x := z * t)
  have hK := secImg_mem hs.xMem_K
  have hJ := secImg_mem hs.xMem_J
  have hzb := isUniqueInvolution_secImg h hs.xMem_K hs.hz
  have htb := isUniqueInvolution_secImg h hs.xMem_J hs.ht
  have hzt := Q3CL.T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht
  have hcen : ∀ w (hw : w ∈ layerY Ω (z * t)), w = z * t →
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨w, hw⟩ :
        SecQuot Ω (z * t)) ∈ Subgroup.center (SecQuot Ω (z * t)) :=
    fun w hw hwx => mk_mem_center_secQuot hw hwx
  have hzt' : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t)))
      ⟨z, mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz⟩ : SecQuot Ω (z * t)) *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t)))
        ⟨t, mem_layerY_of_isUniqueInvolution h hs.xMem_J hs.ht⟩ ∈
      Subgroup.center (SecQuot Ω (z * t)) := by
    rw [← map_mul]
    exact hcen _ _ rfl
  have htz' : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t)))
      ⟨t, mem_layerY_of_isUniqueInvolution h hs.xMem_J hs.ht⟩ : SecQuot Ω (z * t)) *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t)))
        ⟨z, mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz⟩ ∈
      Subgroup.center (SecQuot Ω (z * t)) := by
    rw [← map_mul]
    exact hcen _ _ hzt.symm
  have hnc' : ¬ ∃ g : SecQuot Ω (z * t),
      conjSub g (secImg Ω (z * t) J) = secImg Ω (z * t) (tightCore Rd) := by
    rintro ⟨g, hg⟩
    exact hnc ⟨g⁻¹, by rw [← hg, conjSub_inv_conjSub]⟩
  exact ⟨normal_of_not_conj_of_mul_mem_center h4 hΦ hO hn hgen hK hJ hzb htb hzt' hnc,
    normal_of_not_conj_of_mul_mem_center h4 hΦ hO hn hgen hJ hK htb hzb htz' hnc'⟩

theorem TightStd8R.c264One_of_pair (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hKN : (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)).Normal)
    (hpair : ∀ M ∈ secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t), M.Normal →
      M = secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ∨
        M = secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J) :
    C264One (CoreAssembly.conjClass (tightCore Rd)) z t := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have h := TightLargeHypR.typeRFam hs.large
  have hcl := hs.hyp.conjInvariant
  set O := oddCoreOf (layerY Ω (z * t)) with hOdef
  set H : Subgroup Y := Subgroup.closure ({z * t, z} : Set Y) ⊔ O with hHdef
  have hzY := mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz
  have htY := mem_layerY_of_isUniqueInvolution h hs.xMem_J hs.ht
  have hcH : Subgroup.closure ({z * t, z} : Set Y) ≤ H := le_sup_left
  have hOH : O ≤ H := le_sup_right
  have hzH : z ∈ H := hcH (Subgroup.subset_closure (by simp))
  have haH : z * t ∈ H := hcH (Subgroup.subset_closure (by simp))
  have htH : t ∈ H := by
    have e : t = z⁻¹ * (z * t) := by group
    rw [e]
    exact H.mul_mem (H.inv_mem hzH) haH
  intro c hc
  have hcY := mem_normalizer_layerY hcl hc
  have hcO : c ∈ Subgroup.normalizer (O : Set Y) := mem_normalizer_oddCore_of_mem_normalizer hcY
  have hKc : XMem Ω (z * t) (conjSub c K) := XMem.conj' hcl hs.xMem_K hc
  have himg := secImg_conjSub_eq_map hcl hc K
  have hNc : (secImg Ω (z * t) (conjSub c K)).Normal := by
    rw [himg]
    exact hKN.map _ (secAct hcl hc).surjective
  have hczc : IsUniqueInvolution (conjSub c K) (c * z * c⁻¹) := hs.hz.conj c
  have hczY := mem_layerY_of_isUniqueInvolution h hKc hczc
  have hb := isUniqueInvolution_secImg h hKc hczc
  have hczH : c * z * c⁻¹ ∈ H := by
    have hlift : ∀ {w : Y} (hw : w ∈ layerY Ω (z * t)), w ∈ H →
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t)))
          ⟨c * z * c⁻¹, hczY⟩ : SecQuot Ω (z * t)) =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨w, hw⟩ →
        c * z * c⁻¹ ∈ H := by
      intro w hw hwH he
      have he' := QuotientGroup.eq.mp he
      have hmem : (c * z * c⁻¹)⁻¹ * w ∈ O :=
        ⟨_, he', by simp⟩
      have e : c * z * c⁻¹ = w * ((c * z * c⁻¹)⁻¹ * w)⁻¹ := by group
      rw [e]
      exact H.mul_mem hwH (H.inv_mem (hOH hmem))
    rcases hpair _ (secImg_mem hKc) hNc with e | e
    · rw [e] at hb
      exact hlift hzY hzH (hb.eq (isUniqueInvolution_secImg h hs.xMem_K hs.hz))
    · rw [e] at hb
      exact hlift htY htH (hb.eq (isUniqueInvolution_secImg h hs.xMem_J hs.ht))
  have hca : c * (z * t) * c⁻¹ = z * t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
    group
  have hle : conjSub c H ≤ H := by
    show H.map (MulAut.conj c).toMonoidHom ≤ H
    rw [Subgroup.map_sup, sup_le_iff]
    refine ⟨?_, ?_⟩
    · rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl
      · show c * (z * t) * c⁻¹ ∈ H
        rw [hca]
        exact haH
      · exact hczH
    · rintro _ ⟨w, hw, rfl⟩
      exact hOH ((Subgroup.mem_normalizer_iff.mp hcO w).mp hw)
  have heq : conjSub c H = H := by
    refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
    exact Nat.card_congr (H.equivMapOfInjective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).toEquiv
  exact mem_normalizer_iff_conjSub_eq.mpr heq

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
