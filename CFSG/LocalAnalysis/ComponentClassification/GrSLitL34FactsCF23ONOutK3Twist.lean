module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Cent

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.ONOut

open CFSG.ONSchreier


theorem sigma_sigma (x : Pv) : sigmaPv (sigmaPv x) = x := by
  rw [← MulAut.mul_apply, sigmaPv_sq, MulAut.one_apply]

theorem sigma_mem_CM {k : Pv} (hk : k ∈ CM) : sigmaPv k ∈ CM := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
  calc sigmaPv k * zP = sigmaPv k * sigmaPv zP := by rw [sigmaPv_zP]
    _ = sigmaPv (k * zP) := (map_mul _ _ _).symm
    _ = sigmaPv (zP * k) := by rw [hk]
    _ = zP * sigmaPv k := by rw [map_mul, sigmaPv_zP]

abbrev TwSet : Type := {x : Pv // x ∈ CM ∧ x * sigmaPv x = 1}

theorem twist_mem {k x : Pv} (hk : k ∈ CM) (hx : x ∈ CM ∧ x * sigmaPv x = 1) :
    k * x * (sigmaPv k)⁻¹ ∈ CM ∧
      k * x * (sigmaPv k)⁻¹ * sigmaPv (k * x * (sigmaPv k)⁻¹) = 1 := by
  refine ⟨CM.mul_mem (CM.mul_mem hk hx.1) (CM.inv_mem (sigma_mem_CM hk)), ?_⟩
  have hσx : sigmaPv x = x⁻¹ := eq_inv_of_mul_eq_one_right hx.2
  rw [map_mul, map_mul, map_inv, sigma_sigma, hσx]
  group

@[expose, instance_reducible] def twistAction : MulAction CM TwSet where
  smul k x := ⟨(k : Pv) * x.1 * (sigmaPv (k : Pv))⁻¹, twist_mem k.2 x.2⟩
  one_smul x := Subtype.ext (by
    show (1 : Pv) * x.1 * (sigmaPv 1)⁻¹ = x.1
    rw [map_one, inv_one, one_mul, mul_one])
  mul_smul k₁ k₂ x := Subtype.ext (by
    show ((k₁ : Pv) * k₂) * x.1 * (sigmaPv ((k₁ : Pv) * k₂))⁻¹ =
      (k₁ : Pv) * ((k₂ : Pv) * x.1 * (sigmaPv (k₂ : Pv))⁻¹) * (sigmaPv (k₁ : Pv))⁻¹
    rw [map_mul]
    group)

theorem exists_twist {m : Pv} (hm : m ∈ CM) (h : m * sigmaPv m = 1) :
    ∃ k ∈ CM, m = k * (sigmaPv k)⁻¹ := by
  let _inst : MulAction CM TwSet := twistAction
  let t1 : TwSet := ⟨1, CM.one_mem, by rw [map_one, one_mul]⟩
  have hstab : Nat.card (MulAction.stabilizer CM t1) ≤ 120 := by
    have hfix : ∀ s : MulAction.stabilizer CM t1, sigmaPv ((s : CM) : Pv) = (s : CM) := by
      intro s
      have hs := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 s.2)
      change ((s : CM) : Pv) * 1 * (sigmaPv ((s : CM) : Pv))⁻¹ = 1 at hs
      rw [mul_one, mul_inv_eq_one] at hs
      exact hs.symm
    refine le_trans (Nat.card_le_card_of_injective
      (fun s => (⟨((s : CM) : Pv), (s : CM).2, hfix s⟩ :
        {x : Pv // x ∈ CM ∧ sigmaPv x = x})) ?_) card_cent_le
    intro a b hab
    have h' : ((a : CM) : Pv) = ((b : CM) : Pv) :=
      congrArg (fun x : {x : Pv // x ∈ CM ∧ sigmaPv x = x} => x.1) hab
    exact Subtype.ext (Subtype.ext h')
  have horb := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup CM t1)
  rw [Nat.card_prod, card_CM] at horb
  have hT : Nat.card TwSet ≤ 1344 := card_twist_le
  have hle : 1344 ≤ (MulAction.orbit CM t1).ncard := by
    rw [← Nat.card_coe_set_eq]
    by_contra hlt
    have := Nat.mul_le_mul (Nat.le_of_lt_succ (not_le.1 hlt)) hstab
    omega
  have huniv : MulAction.orbit CM t1 = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ]; omega)
      Set.finite_univ
  have hmem : (⟨m, hm, h⟩ : TwSet) ∈ MulAction.orbit CM t1 := huniv ▸ Set.mem_univ _
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, k.2, ?_⟩
  have e := congrArg Subtype.val hk
  change (k : Pv) * 1 * (sigmaPv (k : Pv))⁻¹ = m at e
  rw [mul_one] at e
  exact e.symm

end CFSG.ComponentClassification.SolMax.ONOut
