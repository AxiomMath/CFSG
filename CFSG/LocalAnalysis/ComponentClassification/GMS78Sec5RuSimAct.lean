module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuHyp
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSimCert

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {a : ℕ} {y d : G}

theorem exists_conj_coords
    (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    {v : G → BinaryGaloisField (2 * a + 1)}
    {φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)}
    {c e : BinaryGaloisField (2 * a + 1)} {Λ : AddSubgroup (BinaryGaloisField (2 * a + 1))}
    (hC : RCoords L T R R₂ a v φ c e Λ) {g : G} (hg : g ∈ normalizer (R : Set G)) :
    ∃ (ρ : BinaryGaloisField (2 * a + 1) → BinaryGaloisField (2 * a + 1))
      (M : BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
        BinaryGaloisField (2 * a + 1) → BinaryGaloisField (2 * a + 1) ×
        BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1)),
      (∀ b ∈ gmsA L T, v (g * b * g⁻¹) = ρ (v b)) ∧
      (∀ x ∈ R, φ (g * x * g⁻¹) = M (φ x)) ∧
      (∀ s t, ρ (s + t) = ρ s + ρ t) ∧ (∀ s, ρ s = 0 → s = 0) ∧
      (∀ z, z.2.2 ∈ Λ → (M z).2.2 ∈ Λ) ∧
      (∀ z w, z.2.2 ∈ Λ → w.2.2 ∈ Λ → M (z + w) = M z + M w) ∧
      (∀ z, z.2.2 ∈ Λ → VLike.sqMap a c e (M z) = ρ (VLike.sqMap a c e z)) := by
  classical
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  have hAR : gmsA L T ≤ R := gmsA_le_T.trans hS.T_le
  have hgN := hS.normalizer_le_normalizer_gmsA hR₂ hg
  have hgA : ∀ b ∈ gmsA L T, g * b * g⁻¹ ∈ gmsA L T := fun b hb =>
    (mem_normalizer_iff.mp hgN b).mp hb
  have hgR' : ∀ x ∈ R, g * x * g⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hg x).mp hx
  have hv1 : v 1 = 0 := by
    have h := hC.v_mul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    linear_combination -h
  have hφ1 : φ 1 = 0 := (hC.ker 1 (one_mem _)).mpr (one_mem _)
  have hvinj : ∀ b ∈ gmsA L T, ∀ b' ∈ gmsA L T, v b = v b' → b = b' := by
    intro b hb b' hb' h
    have h1 : v (b * b'⁻¹) = 0 := by
      rw [hC.v_mul _ hb _ (inv_mem hb'), h, ← hC.v_mul _ hb' _ (inv_mem hb'), mul_inv_cancel,
        hv1]
    exact mul_inv_eq_one.mp (hC.v_inj _ (mul_mem hb (inv_mem hb')) h1)
  let ρ : BinaryGaloisField (2 * a + 1) → BinaryGaloisField (2 * a + 1) := fun s =>
    v (g * (hC.v_surj s).choose * g⁻¹)
  have hρ : ∀ b ∈ gmsA L T, v (g * b * g⁻¹) = ρ (v b) := by
    intro b hb
    have hspec := (hC.v_surj (v b)).choose_spec
    have h1 : (hC.v_surj (v b)).choose = b := hvinj _ hspec.1 _ hb hspec.2
    simp only [ρ, h1]
  have hρadd : ∀ s t, ρ (s + t) = ρ s + ρ t := by
    intro s t
    obtain ⟨b, hb, rfl⟩ := hC.v_surj s
    obtain ⟨b', hb', rfl⟩ := hC.v_surj t
    rw [← hC.v_mul _ hb _ hb', ← hρ _ (mul_mem hb hb'), ← hρ _ hb, ← hρ _ hb',
      ← hC.v_mul _ (hgA _ hb) _ (hgA _ hb')]
    congr 1
    group
  have hρinj : ∀ s, ρ s = 0 → s = 0 := by
    intro s hs
    obtain ⟨b, hb, rfl⟩ := hC.v_surj s
    rw [← hρ _ hb] at hs
    have h1 := hC.v_inj _ (hgA _ hb) hs
    have h2 : b = 1 := by
      have e1 : b = g⁻¹ * (g * b * g⁻¹) * g := by group
      rw [e1, h1]
      group
    rw [h2, hv1]
  have hwd : ∀ x ∈ R, ∀ x' ∈ R, φ x = φ x' → φ (g * x * g⁻¹) = φ (g * x' * g⁻¹) := by
    intro x hx x' hx' h
    have ha : x * x'⁻¹ ∈ gmsA L T := by
      rw [← hC.ker _ (mul_mem hx (inv_mem hx')), hC.mul _ hx _ (inv_mem hx'), h,
        ← hC.mul _ hx' _ (inv_mem hx'), mul_inv_cancel, hφ1]
    have e1 : g * x * g⁻¹ = (g * (x * x'⁻¹) * g⁻¹) * (g * x' * g⁻¹) := by group
    rw [e1, hC.mul _ (hAR (hgA _ ha)) _ (hgR' x' hx'), (hC.ker _ (hAR (hgA _ ha))).mpr (hgA _ ha),
      zero_add]
  let M : BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1) → BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) := fun z =>
    if hz : z.2.2 ∈ Λ then φ (g * (hC.surj z hz).choose * g⁻¹) else z
  have hM : ∀ x ∈ R, φ (g * x * g⁻¹) = M (φ x) := by
    intro x hx
    have hz := hC.mem x hx
    have hspec := (hC.surj (φ x) hz).choose_spec
    simp only [M, hz, ↓reduceDIte]
    exact (hwd _ hspec.1 _ hx hspec.2).symm
  refine ⟨ρ, M, hρ, hM, hρadd, hρinj, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hC.surj z hz
    rw [← hM x hx]
    exact hC.mem _ (hgR' x hx)
  · intro z w hz hw
    obtain ⟨x, hx, rfl⟩ := hC.surj z hz
    obtain ⟨x', hx', rfl⟩ := hC.surj w hw
    rw [← hC.mul _ hx _ hx', ← hM _ (mul_mem hx hx'), ← hM _ hx, ← hM _ hx',
      ← hC.mul _ (hgR' _ hx) _ (hgR' _ hx')]
    congr 1
    group
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hC.surj z hz
    have h2 := hS.sq_mem_gmsA_of_mem_R h34 hX hx
    rw [← hM _ hx, ← hC.sq _ (hgR' _ hx), ← hC.sq _ hx, ← hρ _ h2]
    congr 1
    rw [sq, sq]
    group

theorem exists_action
    (hS : SzR G L T R 1 y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G)))
    {v : G → BinaryGaloisField (2 * 1 + 1)}
    {φ : G → BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) ×
      BinaryGaloisField (2 * 1 + 1)}
    {c e : BinaryGaloisField (2 * 1 + 1)} {Λ : AddSubgroup (BinaryGaloisField (2 * 1 + 1))}
    (hC : RCoords L T R R₂ 1 v φ c e Λ) :
    ∃ dd ∈ steinData, (∀ t, RuCode.toGF t ∈ Λ ↔ t ∈ lamList dd.1.2.2.1 dd.1.2.2.2) ∧
      RuCode.toGF dd.1.1 = c ∧ RuCode.toGF dd.1.2.1 = e ∧
      ∀ g ∈ normalizer (R : Set G), ∃ r ∈ glList,
        (∀ b ∈ gmsA L T, ∀ t, v b = RuCode.toGF t →
          v (g * b * g⁻¹) = RuCode.toGF (linApply r t)) ∧
        (∀ x ∈ R, ∀ w, φ x = RuCode.toGF3 w →
          φ (g * x * g⁻¹) = RuCode.toGF3 (RuSimCode.nMap dd r w)) := by
  classical
  have h0 := ruSim0_check
  have hΛ4 : Nat.card Λ = 4 := by rw [hC.card, h4]
  obtain ⟨c', e', p, q, hc', he', hpq, hΛ, hsp⟩ := hS.exists_special h34 hR₂ h4 hNS hC
  obtain ⟨dd, hdd, hdd1⟩ : ∃ dd ∈ steinData, dd.1 = (c', e', p, q) := by
    have h1 := (RuSimCode.s0_parts h0).1
    rw [← h1] at hsp
    obtain ⟨dd, hdd, hdd1⟩ := List.mem_map.mp hsp
    exact ⟨dd, hdd, hdd1⟩
  obtain ⟨⟨c₀, e₀, p₀, q₀⟩, X₀, Xi₀⟩ := dd
  simp only [Prod.mk.injEq] at hdd1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hdd1
  refine ⟨_, hdd, hΛ, hc', he', fun g hg => ?_⟩
  set code := Function.surjInv RuCode.toGF_surjective with hcode
  have hcode1 : ∀ s, RuCode.toGF (code s) = s := Function.surjInv_eq RuCode.toGF_surjective
  set code3 := Function.surjInv RuCode.toGF3_surjective with hcode3
  have hcode3' : ∀ z, RuCode.toGF3 (code3 z) = z := Function.surjInv_eq RuCode.toGF3_surjective
  have hcode3'' : ∀ w, code3 (RuCode.toGF3 w) = w := fun w =>
    RuCode.toGF3_injective (hcode3' _)
  have hWΛ : ∀ z : BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) ×
      BinaryGaloisField (2 * 1 + 1), z.2.2 ∈ Λ ↔ code3 z ∈ wList p₀ q₀ := by
    intro z
    rw [RuCode.mem_wList, ← hΛ]
    conv_lhs => rw [← hcode3' z]
    rfl
  obtain ⟨ρ, M, hρ, hM, hρadd, hρinj, hMmem, hMadd, hMsq⟩ := hS.exists_conj_coords h34 hR₂ hC hg
  obtain ⟨ρ', M', hρ', hM', -, -, hM'mem, hM'add, hM'sq⟩ :=
    hS.exists_conj_coords h34 hR₂ hC (inv_mem hg)
  have hAR : gmsA L T ≤ R := gmsA_le_T.trans hS.T_le
  have hgN := hS.normalizer_le_normalizer_gmsA hR₂ hg
  have hρ'ρ : ∀ s, ρ' (ρ s) = s := by
    intro s
    obtain ⟨b, hb, rfl⟩ := hC.v_surj s
    have hgb : g * b * g⁻¹ ∈ gmsA L T := (mem_normalizer_iff.mp hgN b).mp hb
    rw [← hρ _ hb, ← hρ' _ hgb, show g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b by group]
  have hMM' : ∀ z, z.2.2 ∈ Λ → M (M' z) = z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hC.surj z hz
    have hgx : g⁻¹ * x * g⁻¹⁻¹ ∈ R := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    rw [← hM' _ hx, ← hM _ hgx, show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x by group]
  set f : Fin 8 → Fin 8 := fun t => code (ρ (RuCode.toGF t)) with hf
  have hfadd : ∀ s t, f (s ^^^ t) = f s ^^^ f t := by
    intro s t
    apply RuCode.toGF_injective
    simp only [hf, hcode1, RuCode.toGF_xor, hρadd]
  set r : Lin8 := (f 1, f 2, f 4) with hr
  have hfr : ∀ t, f t = linApply r t := RuSimCode.eq_linApply hfadd
  have hρr : ∀ t, ρ (RuCode.toGF t) = RuCode.toGF (linApply r t) := by
    intro t
    rw [← hfr, hf, hcode1]
  have hrinj : ∀ s t, linApply r s = linApply r t → s = t := by
    intro s t h
    apply RuCode.toGF_injective
    have h1 : ρ (RuCode.toGF s) = ρ (RuCode.toGF t) := by rw [hρr, hρr, h]
    have h2 : ρ (RuCode.toGF s + RuCode.toGF t) = 0 := by
      rw [hρadd, h1, CharTwo.add_self_eq_zero]
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg, CharTwo.neg_eq]; exact hρinj _ h2)
  have hrGL : r ∈ glList := RuSimCode.mem_glList.mpr (RuSimCode.indep3_of_injective hrinj)
  refine ⟨r, hrGL, fun b hb t hbt => by rw [hρ _ hb, hbt, hρr], ?_⟩
  set N : BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) ×
      BinaryGaloisField (2 * 1 + 1) → BinaryGaloisField (2 * 1 + 1) ×
      BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) := fun z =>
    RuCode.toGF3 (RuSimCode.nMap ((c₀, e₀, p₀, q₀), X₀, Xi₀) r (code3 z)) with hN
  have hNmem : ∀ z, z.2.2 ∈ Λ → (N z).2.2 ∈ Λ := by
    intro z _
    rw [hWΛ, hN, hcode3'']
    exact RuSimCode.nMap_mem h0 hdd r
  have hNadd : ∀ z w : BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) ×
      BinaryGaloisField (2 * 1 + 1), z.2.2 ∈ Λ → w.2.2 ∈ Λ → N (z + w) = N z + N w := by
    intro z w hz hw
    have e1 : code3 (z + w) = addV (code3 z) (code3 w) := by
      apply RuCode.toGF3_injective
      rw [RuCode.toGF3_addV, hcode3', hcode3', hcode3']
    simp only [hN]
    rw [e1, RuSimCode.nMap_addV h0 hdd r ((hWΛ z).mp hz) ((hWΛ w).mp hw), RuCode.toGF3_addV]
  have hNsq : ∀ z, z.2.2 ∈ Λ → VLike.sqMap 1 c e (N z) = ρ (VLike.sqMap 1 c e z) := by
    intro z hz
    simp only [hN]
    rw [← hc', ← he', RuCode.sqMap_toGF3, RuSimCode.sqN_nMap hdd hrGL ((hWΛ z).mp hz),
      ← hρr, ← RuCode.sqMap_toGF3, hcode3']
  have hF := VLike.eq_self_of_card_four hΛ4 c e (fun z => M' (N z))
    (fun z hz => hM'mem _ (hNmem z hz))
    (fun z w hz hw => by
      show M' (N (z + w)) = M' (N z) + M' (N w)
      rw [hNadd z w hz hw, hM'add _ _ (hNmem z hz) (hNmem w hw)])
    (fun z hz => by
      show VLike.sqMap 1 c e (M' (N z)) = VLike.sqMap 1 c e z
      rw [hM'sq _ (hNmem z hz), hNsq z hz, hρ'ρ])
  intro x hx w hxw
  have hz : (φ x).2.2 ∈ Λ := hC.mem x hx
  have h1 : M' (N (φ x)) = φ x := hF (φ x) hz
  rw [hM x hx, ← h1, hMM' _ (hNmem _ hz)]
  simp only [hN]
  rw [hxw, hcode3'']

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
