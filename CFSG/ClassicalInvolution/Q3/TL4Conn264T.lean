module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264A
public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4B

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem ne_of_mem_omegaNbr)

section Sylow

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem false_of_three_meet_sylow_E4 (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)
    (hE : MuIsoE4 Ω W) (S₂ : Sylow 2 G) {L₁ L₂ L₃ : Subgroup G} (h₁ : L₁ ∈ Ω) (h₂ : L₂ ∈ Ω)
    (h₃ : L₃ ∈ Ω) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃)
    (hc₁ : 2 < Nat.card ↥(L₁ ⊓ (S₂ : Subgroup G)))
    (hc₂ : 2 < Nat.card ↥(L₂ ⊓ (S₂ : Subgroup G)))
    (hc₃ : 2 < Nat.card ↥(L₃ ⊓ (S₂ : Subgroup G))) : False := by
  classical
  have hΩ : HypOmegaGen Ω := hP.hyp
  obtain ⟨g, η₂, hη₂, hinv₂, hgW⟩ := exists_conj_eta hΩ.conjInvariant hW S₂
  have hη₂G : η₂ ∈ etaG Ω := ⟨S₂, hη₂, hinv₂⟩
  set W₂ : Subgroup G := ⨆ U ∈ η₂, U with hW₂def
  have hW₂ : W₂ ∈ WSet Ω := ⟨η₂, hη₂G, rfl⟩
  have hηS : ∀ V ∈ η₂, V ≤ (S₂ : Subgroup G) := fun V hV => (hη₂.1 hV).2
  have c₂ : Q3CL.Thompson.Ctx Ω W₂ := Q3CL.T8.ctxOf hP hW₂
  have hE₂ : MuIsoE4 Ω W₂ := by
    obtain ⟨φ⟩ := hE
    rw [← hgW]
    exact ⟨(muGroupConjEquivGen hΩ g W).symm.trans φ⟩
  have hrep : ∀ L ∈ Ω, 2 < Nat.card ↥(L ⊓ (S₂ : Subgroup G)) → ∃ ρ : Rep Ω W₂, ρ.K = L := by
    intro L hL hcard
    have h611 : L ⊓ W₂ ∈ η₂ := Sec6Gen.l6_11Gen G Ω hΩ S₂ η₂ hη₂G hηS L hL hcard
    have hV₀U : L ⊓ W₂ ∈ USet Ω := (hη₂.1 h611).1
    obtain ⟨zL, hzL⟩ := Sec6Gen.exists_uniqueInvolution hΩ hL
    have hV₀2 : IsPGroup 2 ↥(L ⊓ W₂) := Sec6Gen.isPGroup_of_mem_USet hΩ hV₀U
    have hV₀4 : 4 ≤ Nat.card ↥(L ⊓ W₂) := by
      obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hV₀U
      exact h4
    have hzLV : zL ∈ L ⊓ W₂ := T3.mem_of_isPGroup hzL inf_le_left hV₀2 (by omega)
    obtain ⟨ρL, hρL⟩ := exists_rep_of_involution_mem_gen c₂ hP.cls hL hzL hzLV.2
    exact ⟨ρL, hρL⟩
  obtain ⟨ρ₁, e₁⟩ := hrep L₁ h₁ hc₁
  obtain ⟨ρ₂, e₂⟩ := hrep L₂ h₂ hc₂
  obtain ⟨ρ₃, e₃⟩ := hrep L₃ h₃ hc₃
  exact no_three_reps_E4_gen hP hW₂ hE₂ ρ₁ ρ₂ ρ₃ (by rw [e₁, e₂]; exact h12)
    (by rw [e₁, e₃]; exact h13) (by rw [e₂, e₃]; exact h23)

end Sylow

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_isPGroup_map_eq {Pb : Subgroup (SecQuot Ω x)} (hPb : IsPGroup 2 ↥Pb) :
    ∃ P : Subgroup ↥(layerY Ω x), IsPGroup 2 ↥P ∧
      P.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) = Pb := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (T := ⊥)
    (P := Pb.comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))))
    IsPGroup.of_bot bot_le
  have hVb := isSylow2In_map_mk odd_natCard_oddCore_layerY hV
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hVb
  exact ⟨V, hV.2.1, (hVb.2.2 Pb le_rfl hPb hVb.1).symm⟩

theorem exists_conj_lt_card_inf (M : Subgroup G) {P : Subgroup ↥(layerY Ω x)}
    (hP : IsPGroup 2 ↥P) {k : ℕ}
    (hk : k < Nat.card ↥(secImg Ω x M ⊓
      P.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))))) :
    ∃ ν : ↥(layerY Ω x), ν ∈ classicalInvolutionOddCore ↥(layerY Ω x) ∧
      k < Nat.card ↥(conjSub (ν : G) M ⊓ P.map (layerY Ω x).subtype) := by
  set N := classicalInvolutionOddCore ↥(layerY Ω x) with hNdef
  set π := QuotientGroup.mk' N with hπ
  set C : Subgroup ↥(layerY Ω x) := (coreAt x M).subgroupOf (layerY Ω x) with hCdef
  set D : Subgroup ↥(layerY Ω x) := P ⊓ (secImg Ω x M).comap π with hDdef
  have hD2 : IsPGroup 2 ↥D := hP.to_le inf_le_left
  have hDC : D ≤ C ⊔ N := by
    intro d hd
    have h1 : d ∈ (C.map π).comap π := hd.2
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  obtain ⟨ν, hν, hνD⟩ := exists_conj_le_of_le_sup odd_natCard_oddCore_layerY hD2 hDC
  have hmap : D.map π = secImg Ω x M ⊓ P.map π := by
    apply le_antisymm
    · rintro _ ⟨d, ⟨hdP, hdM⟩, rfl⟩
      exact ⟨hdM, d, hdP, rfl⟩
    · rintro w ⟨hwM, d, hdP, rfl⟩
      exact ⟨d, ⟨hdP, hwM⟩, rfl⟩
  have hkD : k < Nat.card ↥D := by
    have h1 : Nat.card ↥(D.map π) ≤ Nat.card ↥D :=
      Nat.card_le_card_of_surjective _ (π.subgroupMap_surjective D)
    rw [hmap] at h1
    exact lt_of_lt_of_le hk h1
  refine ⟨ν⁻¹, N.inv_mem hν, lt_of_lt_of_le hkD ?_⟩
  have hle : D.map (layerY Ω x).subtype ≤ conjSub ((ν⁻¹ : ↥(layerY Ω x)) : G) M ⊓
      P.map (layerY Ω x).subtype := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨?_, d, hd.1, rfl⟩
    have h1 : ν * d * ν⁻¹ ∈ C := hνD (conj_mem_conjSub hd)
    have h2 : ((ν * d * ν⁻¹ : ↥(layerY Ω x)) : G) ∈ M :=
      coreAt_le x M (Subgroup.mem_subgroupOf.mp h1)
    show (d : G) ∈ conjSub ((ν⁻¹ : ↥(layerY Ω x)) : G) M
    rw [mem_conjSub_iff]
    simpa using h2
  calc Nat.card ↥D = Nat.card ↥(D.map (layerY Ω x).subtype) :=
        (Subgroup.card_map_of_injective (layerY Ω x).subtype_injective).symm
    _ ≤ _ := Subgroup.card_le_of_le hle

theorem false_of_three_secImg_E4 (hP : Q3CL.PartIHypG Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hE : MuIsoE4 Ω W) {M₁ M₂ M₃ : Subgroup G} (h₁ : XMem Ω x M₁) (h₂ : XMem Ω x M₂)
    (h₃ : XMem Ω x M₃) (h12 : secImg Ω x M₁ ≠ secImg Ω x M₂)
    (h13 : secImg Ω x M₁ ≠ secImg Ω x M₃) (h23 : secImg Ω x M₂ ≠ secImg Ω x M₃)
    {Pb : Subgroup (SecQuot Ω x)} (hPb : IsPGroup 2 ↥Pb)
    (hc₁ : 2 < Nat.card ↥(secImg Ω x M₁ ⊓ Pb)) (hc₂ : 2 < Nat.card ↥(secImg Ω x M₂ ⊓ Pb))
    (hc₃ : 2 < Nat.card ↥(secImg Ω x M₃ ⊓ Pb)) : False := by
  obtain ⟨P, hP2, rfl⟩ := exists_isPGroup_map_eq hPb
  obtain ⟨ν₁, hν₁, hk₁⟩ := exists_conj_lt_card_inf M₁ hP2 hc₁
  obtain ⟨ν₂, hν₂, hk₂⟩ := exists_conj_lt_card_inf M₂ hP2 hc₂
  obtain ⟨ν₃, hν₃, hk₃⟩ := exists_conj_lt_card_inf M₃ hP2 hc₃
  obtain ⟨S₂, hS₂⟩ := (hP2.map (layerY Ω x).subtype).exists_le_sylow
  have hcl := hP.hyp.conjInvariant
  have hne : ∀ {A B : Subgroup G} {ν μ : ↥(layerY Ω x)},
      ν ∈ classicalInvolutionOddCore ↥(layerY Ω x) →
      μ ∈ classicalInvolutionOddCore ↥(layerY Ω x) →
      secImg Ω x A ≠ secImg Ω x B → conjSub (ν : G) A ≠ conjSub (μ : G) B := by
    intro A B ν μ hν hμ hAB he
    apply hAB
    rw [← secImg_conj_of_mem hν A, he, secImg_conj_of_mem hμ B]
  have hcard : ∀ {A : Subgroup G}, 2 < Nat.card ↥(A ⊓ P.map (layerY Ω x).subtype) →
      2 < Nat.card ↥(A ⊓ (S₂ : Subgroup G)) := fun hA =>
    lt_of_lt_of_le hA (Subgroup.card_le_of_le (inf_le_inf_left _ hS₂))
  exact false_of_three_meet_sylow_E4 hP hW hE S₂ (hcl _ _ h₁.1) (hcl _ _ h₂.1) (hcl _ _ h₃.1)
    (hne hν₁ hν₂ h12) (hne hν₁ hν₃ h13) (hne hν₂ hν₃ h23) (hcard hk₁) (hcard hk₂) (hcard hk₃)

end Lift

section Cit3


variable {n : ℕ}

theorem tightC264Pair_proved : TightC264Pair n := by
  intro _ Y _ _ Rd Sd z J S R T W t hs _ hE hKN hJN M hM hMN
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  have h := TightLargeHypR.typeRFam hs.large
  obtain ⟨L, hL, rfl⟩ := mem_secFam_iff.mp hM
  have hKJ : secImg Ω (z * t) (tightCore Rd) ≠ secImg Ω (z * t) J :=
    secImg_ne h hs.xMem_K hs.xMem_J hs.hz hs.ht
      (Q3CL.T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht)
      (ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)
  by_contra hne
  rw [not_or] at hne
  set H : Subgroup (SecQuot Ω (z * t)) := secImg Ω (z * t) (tightCore Rd) ⊔
    secImg Ω (z * t) J ⊔ secImg Ω (z * t) L with hHdef
  obtain ⟨Pb, hPb, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := H) IsPGroup.of_bot bot_le
  have hcard : ∀ B ∈ secFam Ω (z * t), B.Normal → B ≤ H → 2 < Nat.card ↥(B ⊓ Pb) := by
    intro B hB hBN hBH
    have hsyl : IsSylow2In (Pb ⊓ B) B :=
      AscP1Nine3.isSylow2In_inf_of_le_normalizer' hPb hBH fun y _ => by
        rw [Subgroup.normalizer_eq_top_iff.mpr hBN]
        exact Subgroup.mem_top y
    obtain ⟨e⟩ : Nonempty (↥(Pb ⊓ B) ≃* QuaternionGroup 2) := h.secFam.quat B hB _ hsyl
    rw [inf_comm, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  exact false_of_three_secImg_E4 hs.partIHypG hs.hW.1 hE hs.xMem_K hs.xMem_J hL
    hKJ (Ne.symm hne.1) (Ne.symm hne.2) hPb.2.1
    (hcard _ (secImg_mem hs.xMem_K) hKN (le_sup_left.trans le_sup_left))
    (hcard _ (secImg_mem hs.xMem_J) hJN (le_sup_right.trans le_sup_left))
    (hcard _ hM hMN le_sup_right)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
