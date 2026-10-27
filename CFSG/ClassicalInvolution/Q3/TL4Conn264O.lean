module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26YS
public import CFSG.ClassicalInvolution.Q3.TL4Conn264B
public import CFSG.ClassicalInvolution.Q3.TL4Conn264T
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Hyp

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (ThmDHyp)

section WSet

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem card_inf_of_wSet_eq (hD : ThmDHyp 3 Φ) {V : Subgroup X} (hW1 : WSet Φ = {V}) :
    ∀ L ∈ Φ, Nat.card ↥(L ⊓ V) = 4 := by
  intro L hL
  have hW : V ∈ WSet Φ := by rw [hW1]; rfl
  have hVn : ∀ g : X, conjSub g V = V := fun g => by
    have := WSet.conj hD.hyp.conjInvariant hW g
    rwa [hW1] at this
  have hLsyl : IsSylow2In L L := ⟨le_rfl, hD.two L hL, fun V' hVL _ hLV => le_antisymm hVL hLV⟩
  have hLD : L ∈ DSet Φ V :=
    ⟨mem_RSet_of_isSylow2In hL hLsyl, fun x _ => mem_normalizer_iff_conjSub_eq.mpr (hVn x)⟩
  obtain ⟨-, -, -, -, hcard⟩ := Q3CL.Thompson.inf_W_of_mem_D hD.hyp hW hLD hL hLsyl
  have h8 : Nat.card ↥L = 8 := by rw [hD.card L hL]; norm_num
  omega

end WSet

theorem card_inf_subgroupOf_le {Q : Type} [Group Q] [Finite Q] {X A : Subgroup Q}
    (V : Subgroup ↥X) : Nat.card ↥(A.subgroupOf X ⊓ V) ≤ Nat.card ↥(A ⊓ V.map X.subtype) := by
  rw [← Subgroup.card_map_of_injective X.subtype_injective]
  refine Subgroup.card_le_of_le ?_
  rintro _ ⟨y, ⟨hyA, hyV⟩, rfl⟩
  exact ⟨Subgroup.mem_subgroupOf.mp hyA, y, hyV, rfl⟩

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.c264One_of_conj (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hconj : ∀ c ∈ Subgroup.centralizer ({z * t} : Set Y),
      secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (conjSub c (tightCore Rd)) =
          secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ∨
        secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (conjSub c (tightCore Rd)) =
          secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J) :
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
    rcases hconj c hc with e | e
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

theorem TightStd8R.c264One_of_orb (h4 : Thm4RBelow 3 n) (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (h2K : IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)))
    (h2J : IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J))
    (honly : ∀ M ∈ secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t),
      M ≤ secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) →
        M = secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ∨
          M = secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J) :
    C264One (CoreAssembly.conjClass (tightCore Rd)) z t := by
  refine hs.c264One_of_conj fun c hc => ?_
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΦ := h.secFam (x := z * t)
  have hcl := hs.hyp.conjInvariant
  have hKc : XMem Ω (z * t) (conjSub c (tightCore Rd)) := XMem.conj' hcl hs.xMem_K hc
  have hMΦ := secImg_mem hKc
  by_cases hMX : secImg Ω (z * t) (conjSub c (tightCore Rd)) ≤ secOrb Ω (tightCore Rd) (z * t)
  · exact honly _ hMΦ hMX
  exfalso
  have hKΦ := secImg_mem hs.xMem_K
  have hJΦ := secImg_mem hs.xMem_J
  have hO := secQuot_oddCore_eq_bot (Ω := Ω) (x := z * t)
  have hn := hs.natCard_secQuot_lt
  have hnc : ¬ ∃ g ∈ omegaGen (secFam Ω (z * t)),
      conjSub g (secImg Ω (z * t) (conjSub c (tightCore Rd))) =
        secImg Ω (z * t) (tightCore Rd) := by
    rintro ⟨g, hg, e⟩
    apply hMX
    have e' : secImg Ω (z * t) (conjSub c (tightCore Rd)) =
        conjSub g⁻¹ (secImg Ω (z * t) (tightCore Rd)) := by
      rw [← e, conjSub_inv_conjSub]
    rw [e']
    exact Vtx.conjSub_le_orbGrp _ ⟨g⁻¹, (omegaGen _).inv_mem hg⟩
  obtain ⟨g₀, hg₀⟩ := hcj
  have hg₀G : g₀ ∈ omegaGen (secFam Ω (z * t)) := by
    rw [omegaGen_secFam]
    exact Subgroup.mem_top _
  have hncJ : ¬ ∃ g ∈ omegaGen (secFam Ω (z * t)),
      conjSub g (secImg Ω (z * t) (conjSub c (tightCore Rd))) = secImg Ω (z * t) J := by
    rintro ⟨g, hg, e⟩
    refine hnc ⟨g₀⁻¹ * g, (omegaGen _).mul_mem ((omegaGen _).inv_mem hg₀G) hg, ?_⟩
    rw [conjSub_mul, e, ← hg₀, conjSub_inv_conjSub]
  have hcK := Vtx.commutes_of_not_conj h4 hΦ hO hn hMΦ hKΦ hnc
  have hcJ := Vtx.commutes_of_not_conj h4 hΦ hO hn hMΦ hJΦ hncJ
  have hM2 : IsPGroup 2 ↥(secImg Ω (z * t) (conjSub c (tightCore Rd))) := by
    rw [secImg_conjSub_eq_map hcl hc]
    exact h2K.map _
  have hJN : secImg Ω (z * t) J ≤
      Subgroup.normalizer ((secImg Ω (z * t) (tightCore Rd) : Subgroup _) : Set _) := by
    obtain ⟨-, -, T', hT', hT'J, hT'N⟩ := hs.secImg_J_mem_omegaNbr
    have hT'syl : IsSylow2In T' (secImg Ω (z * t) J) :=
      Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΦ.hyp hJΦ hT' hT'J
    have hTJ : T' = secImg Ω (z * t) J :=
      (hT'syl.2.2 _ le_rfl h2J hT'syl.1).symm
    rw [← hTJ]
    exact hT'N
  have hJK2 : IsPGroup 2 ↥(secImg Ω (z * t) J ⊔ secImg Ω (z * t) (tightCore Rd)) :=
    h2J.to_sup_of_normal_right' h2K hJN
  have hMN : secImg Ω (z * t) (conjSub c (tightCore Rd)) ≤
      Subgroup.normalizer (((secImg Ω (z * t) J ⊔ secImg Ω (z * t) (tightCore Rd) :
        Subgroup _)) : Set _) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcJ a ha b hb
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcK a ha b hb
  have hP2 := hM2.to_sup_of_normal_right' hJK2 hMN
  have hcard : ∀ {B : Subgroup (SecQuot Ω (z * t))}, B ∈ secFam Ω (z * t) → IsPGroup 2 ↥B →
      B ≤ secImg Ω (z * t) (conjSub c (tightCore Rd)) ⊔
        (secImg Ω (z * t) J ⊔ secImg Ω (z * t) (tightCore Rd)) →
      2 < Nat.card ↥(B ⊓ (secImg Ω (z * t) (conjSub c (tightCore Rd)) ⊔
        (secImg Ω (z * t) J ⊔ secImg Ω (z * t) (tightCore Rd)))) := by
    intro B hB hB2 hBP
    rw [inf_eq_left.mpr hBP, LinkE2.card_of_isPGroup_typeR hΦ hB hB2]
    norm_num
  have hKM : secImg Ω (z * t) (tightCore Rd) ≠ secImg Ω (z * t) (conjSub c (tightCore Rd)) :=
    fun e => hMX (e ▸ Vtx.le_orbGrp _)
  have hJM : secImg Ω (z * t) J ≠ secImg Ω (z * t) (conjSub c (tightCore Rd)) := by
    intro e
    apply hMX
    rw [← e, ← hg₀]
    exact Vtx.conjSub_le_orbGrp _ ⟨g₀, hg₀G⟩
  have hKJ : secImg Ω (z * t) (tightCore Rd) ≠ secImg Ω (z * t) J :=
    hs.secImg_J_mem_omegaNbr.2.1.symm
  exact false_of_three_secImg_E4 hs.partIHypG hs.hW.1 hE hs.xMem_K hs.xMem_J hKc hKJ hKM hJM hP2
    (hcard hKΦ h2K (le_sup_right.trans le_sup_right))
    (hcard hJΦ h2J (le_sup_left.trans le_sup_right)) (hcard hMΦ hM2 le_sup_left)

theorem TightStd8R.c264One_of_wSet_secOrb (h4 : Thm4RBelow 3 n)
    (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))
    {V : Subgroup ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))}
    (hW1 : WSet (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) = {V}) :
    C264One (CoreAssembly.conjClass (tightCore Rd)) z t := by
  have hKX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) := Vtx.le_orbGrp _
  obtain ⟨g₀, hg₀⟩ := hcj
  have hJX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) := by
    rw [← hg₀]
    exact Vtx.conjSub_le_orbGrp _ ⟨g₀, by rw [omegaGen_secFam]; exact Subgroup.mem_top _⟩
  have hKΦ := secImg_mem hs.xMem_K
  have hJΦ := secImg_mem hs.xMem_J
  have h2 : ∀ {B : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t))},
      B ∈ secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t) →
      B ≤ secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) →
      IsPGroup 2 ↥B := fun hB hBX =>
    (hD.two _ ⟨_, hB, hBX, rfl⟩).of_equiv (Subgroup.subgroupOfEquivOfLe hBX)
  have hW : V ∈ WSet (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) := by
    rw [hW1]; rfl
  have hV2 : IsPGroup 2 ↥(V.map
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)).subtype) :=
    (Thompson.isPGroup_of_mem_WSet hW).map _
  have hc4 : ∀ {B : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t))},
      B ∈ secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t) →
      B ≤ secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) →
      2 < Nat.card ↥(B ⊓ V.map
        (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)).subtype) := by
    intro B hB hBX
    have h1 := card_inf_of_wSet_eq hD hW1 _ ⟨_, hB, hBX, rfl⟩
    have h2 := card_inf_subgroupOf_le (A := B) V
    omega
  refine hs.c264One_of_orb h4 hE ⟨g₀, hg₀⟩ (h2 hKΦ hKX) (h2 hJΦ hJX) fun M hM hMX => ?_
  by_contra hne
  rw [not_or] at hne
  obtain ⟨L, hL, rfl⟩ := mem_secFam_iff.mp hM
  exact false_of_three_secImg_E4 hs.partIHypG hs.hW.1 hE hs.xMem_K hs.xMem_J hL
    hs.secImg_J_mem_omegaNbr.2.1.symm (Ne.symm hne.1) (Ne.symm hne.2) hV2 (hc4 hKΦ hKX)
    (hc4 hJΦ hJX) (hc4 hM hMX)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
