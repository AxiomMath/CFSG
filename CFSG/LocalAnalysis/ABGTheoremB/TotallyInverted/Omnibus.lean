module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusQuotient

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

namespace Omnibus

theorem conjSub_mem_signalizersPerm (hσ : σ.IsValid) (Δ : Data σ r) {m : G}
    (hm : m ∈ Subgroup.normalizer (σ.T : Set G)) {H R : Subgroup G}
    (hR : R ∈ signalizersPerm H σ.T σ.C r) :
    conjSub m R ∈ signalizersPerm (conjSub m H) σ.T σ.C r := by
  obtain ⟨⟨hRH, hRp, hTR, -⟩, hperm⟩ := hR
  exact mem_signalizersPerm hσ Δ (conjSub_mono hRH) (isPGroup_conjSub hRp)
    (le_normalizer_conjSub hTR hm) (conjSub_mul_comm (normalizer_T_le_M hm) hperm)

theorem conjSub_mem_maximals (hσ : σ.IsValid) (Δ : Data σ r) {m : G} {H R : Subgroup G}
    (hmH : m ∈ H) (hm : m ∈ Subgroup.normalizer (σ.T : Set G))
    (hR : R ∈ maximals (signalizersPerm H σ.T σ.C r)) :
    conjSub m R ∈ maximals (signalizersPerm H σ.T σ.C r) := by
  have hHm : conjSub m H = H := conjSub_eq_self_of_mem hmH
  have hm' : m⁻¹ ∈ Subgroup.normalizer (σ.T : Set G) := Subgroup.inv_mem _ hm
  refine ⟨hHm ▸ conjSub_mem_signalizersPerm hσ Δ hm hR.1, fun Z hZ hle => ?_⟩
  have hZ' := conjSub_mem_signalizersPerm hσ Δ hm' hZ
  rw [conjSub_eq_self_of_mem (H.inv_mem hmH)] at hZ'
  have hRZ : R ≤ conjSub m⁻¹ Z := by
    rw [← conjSub_le_conjSub_iff (g := m), conjSub_conjSub_inv]
    exact hle
  have := hR.2 _ hZ' hRZ
  rw [← this, conjSub_conjSub_inv]

theorem exists_eq_inf_oddCoreIn_sup (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (hI : OmnibusInputs Δ) {H U : Subgroup G} (hCH : σ.C ≤ H)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) (hO : oddCoreIn H ≠ ⊥) :
    ∃ j : Fin 3, U = (U ⊓ oddCoreIn H) ⊔ (U ⊓ σ.Ns j) := by
  obtain ⟨⟨⟨hUH, hUp, hTU, -⟩, -⟩, -⟩ := hU
  have hUodd := odd_card_of_isPGroup Δ.prime Δ.ne_two hUp
  obtain ⟨t, htT, ht1, ht⟩ := (centralizing_conjugate hσ hF Δ hI hCH hO).1 U hUH hUodd hTU
  obtain ⟨j, rfl⟩ := ((mem_T_iff hσ).mp htT).resolve_left ht1
  refine ⟨j, le_antisymm ?_ (sup_le inf_le_left inf_le_left)⟩
  have htU : σ.xs j ∈ Subgroup.normalizer (U : Set G) := hTU htT
  obtain ⟨hdec, -⟩ := odd_fixed_mul_inverted hUodd (xs_orderOf hσ j) htU
  intro u hu
  have hu' : u ∈ (U : Set G) := hu
  rw [hdec] at hu'
  obtain ⟨f, hf, v, hv, rfl⟩ := hu'
  obtain ⟨hvU, hvinv⟩ := OddInversion.mem_invertedSet.mp hv
  have hv2 : v ^ 2 ∈ oddCoreIn H := by
    have := ht v hvU
    rwa [show v * σ.xs j * v⁻¹ * (σ.xs j)⁻¹ = v * (σ.xs j * v⁻¹ * (σ.xs j)⁻¹) by group,
      show σ.xs j * v⁻¹ * (σ.xs j)⁻¹ = (σ.xs j * v * (σ.xs j)⁻¹)⁻¹ by group, hvinv, inv_inv,
      ← pow_two] at this
  have hvO : v ∈ oddCoreIn H := mem_of_sq_mem (odd_orderOf_of_mem hUodd hvU) hv2
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hf) (Subgroup.mem_sup_left ⟨hvU, hvO⟩)

theorem exists_conj_eq (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (hI : OmnibusInputs Δ) {H U U' : Subgroup G} (hCH : σ.C ≤ H)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r))
    (hU' : U' ∈ maximals (signalizersPerm H σ.T σ.C r)) (hO : oddCoreIn H ≠ ⊥) :
    ∃ m ∈ σ.M ⊓ H, conjSub m U' = U := by
  have hN := hI.nStructure
  have hX := oddCoreIn_sup_mem_maximals hσ Δ hN hCH hU
  have hX' := oddCoreIn_sup_mem_maximals hσ Δ hN hCH hU'
  obtain ⟨m, ⟨hmH, hmT⟩, hm⟩ := (centralizing_conjugate hσ hF Δ hI hCH hO).2 _ hX _ hX'
  have hU'' := conjSub_mem_maximals hσ Δ hmH hmT hU'
  have hU''X : conjSub m U' ≤ oddCoreIn H ⊔ U := by
    rw [← hm]
    exact conjSub_mono le_sup_right
  obtain ⟨hYodd, hTY, hYperm⟩ := oddCoreIn_sup_props hσ Δ hCH hU.1
  obtain ⟨c, ⟨hcC, hcH⟩, hc⟩ := exists_conj_of_le hσ Δ hN hCH
    (sup_le (oddCoreIn_le H) hU.1.1.1) hYodd hTY hYperm hU hU'' le_sup_right hU''X
  refine ⟨c * m, ⟨σ.M.mul_mem (C_le_M hcC) (normalizer_T_le_M hmT), H.mul_mem hcH hmH⟩, ?_⟩
  rw [conjSub_mul, hc]

theorem pCoreIn_sup_mem_maximals (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (hI : OmnibusInputs Δ) {H U : Subgroup G} (hCH : σ.C ≤ H)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) :
    pCoreIn r (U ⊔ σ.C) ∈ maximals (signalizers H σ.C r) := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  obtain ⟨⟨⟨hUH, hUp, hTU, -⟩, hperm⟩, hmax⟩ := id hU
  set V : Subgroup G := pCoreIn r (U ⊔ σ.C) with hVdef
  have hVmem : V ∈ signalizers H σ.C r := pCoreIn_sup_mem_signalizers Δ hCH hUH
  refine ⟨hVmem, fun Y hY hVY => ?_⟩
  obtain ⟨hYH, hYp, hCY, hYC⟩ := hY
  by_cases hV1 : V = ⊥
  ·
    have hUC : U ≤ σ.C := by
      have := eq_pCoreIn_sup_inf hσ Δ hCH hU
      rw [← hVdef, hV1, bot_sup_eq] at this
      rw [this]
      exact inf_le_right
    have hUY : U ≤ Subgroup.normalizer (Y : Set G) := hUC.trans hCY
    have hUYmem : U ⊔ Y ∈ signalizersPerm H σ.T σ.C r := by
      refine mem_signalizersPerm hσ Δ (sup_le hUH hYH)
        (IsPGroup.to_sup_of_normal_right' hUp hYp hUY)
        (fun t ht => mem_normalizer_sup (hTU ht) (hCY ((σ.T_le_C hσ) ht))) ?_
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUY, mul_assoc,
        ← mul_comm_of_le_normalizer hCY, ← mul_assoc, coe_mul_coe_of_le' hUC, ← mul_assoc,
        coe_mul_coe_of_le hUC]
    have hUYU := hmax _ hUYmem le_sup_left
    have hYU : Y ≤ U := hUYU ▸ le_sup_right
    have hY1 : Y = ⊥ := by
      rw [eq_bot_iff, ← hYC]
      exact le_inf le_rfl (hYU.trans hUC)
    rw [hY1, hV1]
  ·
    by_contra hne
    have hVY' : V ≠ Y := fun h => hne h.symm
    set H' : Subgroup G := H ⊓ Subgroup.normalizer (V : Set G) with hH'def
    have hCH' : σ.C ≤ H' := le_inf hCH hVmem.2.2.1
    have hUH' : U ≤ H' := le_inf hUH (le_sup_left.trans (le_normalizer_pCoreIn r _))
    have hUmax' : U ∈ maximals (signalizersPerm H' σ.T σ.C r) :=
      mem_maximals_of_le hU hUH' inf_le_left
    set V' : Subgroup G := Y ⊓ Subgroup.normalizer (V : Set G) with hV'def
    obtain ⟨y, hyY, hyN, hyV⟩ := exists_mem_normalizer_not_mem hYp hVY hVY'
    have hVV' : V ≤ V' := le_inf hVY Subgroup.le_normalizer
    have hyV' : y ∈ V' := ⟨hyY, hyN⟩
    have hCV' : σ.C ≤ Subgroup.normalizer (V' : Set G) := fun c hc =>
      mem_normalizer_inf (hCY hc) (mem_normalizer_normalizer (hVmem.2.2.1 hc))
    have hV'mem : V' ∈ signalizersPerm H' σ.T σ.C r :=
      mem_signalizersPerm hσ Δ (inf_le_inf_right _ hYH) (hYp.to_le inf_le_left)
        ((σ.T_le_C hσ).trans hCV') (mul_comm_of_le_normalizer hCV').symm
    obtain ⟨Us, hUs, hV'Us⟩ := exists_le_mem_maximals hV'mem
    have hO' : oddCoreIn H' ≠ ⊥ := by
      intro h
      apply hV1
      rw [eq_bot_iff, ← h]
      exact le_oddCoreIn (le_inf (hVmem.1) Subgroup.le_normalizer) inf_le_right
        (odd_card_of_isPGroup Δ.prime Δ.ne_two hVmem.2.1)
    obtain ⟨m, ⟨hmM, hmH'⟩, hm⟩ := exists_conj_eq hσ hF Δ hI hCH' hUmax' hUs hO'
    have hconj : conjSub m (pCoreIn r (Us ⊔ σ.C)) = V := by
      rw [← pCoreIn_conjSub, conjSub_sup, hm, conjSub_eq_self hmM]
    have hV'core : V' ≤ pCoreIn r (Us ⊔ σ.C) :=
      le_pCoreIn_sup_of_le hUs.1.2 hUs.1.1.2.1 hV'Us hCV'
    have hle : conjSub m V' ≤ V := hconj ▸ conjSub_mono hV'core
    have hcard : Nat.card V' ≤ Nat.card V := by
      rw [← card_conjSub m V']
      exact Subgroup.card_le_of_le hle
    have hVeq : V = V' := Subgroup.eq_of_le_of_card_ge hVV' hcard
    exact hyV (hVeq ▸ hyV')

theorem omnibusAt (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (hI : OmnibusInputs Δ) {H U : Subgroup G} (hCH : σ.C ≤ H)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) : OmnibusAt Δ H U := by
  obtain ⟨⟨⟨hUH, hUp, hTU, -⟩, hperm⟩, -⟩ := id hU
  have hUodd := odd_card_of_isPGroup Δ.prime Δ.ne_two hUp
  have hX := hasNormalPComplement_sup hσ Δ hUodd hTU hperm
  refine ⟨fun i => inf_Ns_mem_signalizersPerm hσ hU.1 i (inf_le_left.trans hUH),
    exists_comp hσ Δ hCH hU, ⟨U ⊓ σ.C, isSylowOf_inf_C hσ Δ hCH hU, inf_le_left⟩,
    exists_isSylowOf_oddCoreIn_le hσ Δ hI.nStructure hCH hU,
    fun _ => eq_pCoreIn_sup_inf hσ Δ hCH hU,
    fun hO => exists_eq_inf_oddCoreIn_sup hσ hF Δ hI hCH hU hO,
    fun hO U' hU' => exists_conj_eq hσ hF Δ hI hCH hU hU' hO, ⟨hX, ?_⟩,
    pCoreIn_sup_mem_maximals hσ hF Δ hI hCH hU,
    fun X hX hXU => le_pCoreIn_sup_of_le hperm hUp hXU hX.2.2.1⟩
  rw [Δ.W_eq]
  exact le_oddCoreIn_of_hasNormalPComplement hX
    ((oddCoreIn_le _).trans (inf_le_left.trans le_sup_right)) (odd_card_oddCoreIn _)

end Omnibus

theorem omnibus (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (hI : OmnibusInputs Δ) : Omnibus Δ :=
  fun _ hCH _ hU => Omnibus.omnibusAt hσ hF Δ hI hCH hU

end CFSG.ABGTheoremB.TotallyInverted
