module

public import CFSG.LargeExtraspecial.AS35CS63Inn
public import CFSG.Sporadic.Schreier.PairJ2Pairs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld CFSG.ComponentClassification

namespace S63

@[expose] def J2CentInput : Prop :=
  ∀ (Y : Type) [Group Y], Blueprint.NativeSporadic.IsSporadic Y .J2 →
    ∀ (s : Y), orderOf s = 2 → ∀ N : Subgroup Y, N ≤ centralizer ({s} : Set Y) →
      (∀ c ∈ centralizer ({s} : Set Y), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → IsPGroup 2 N → s ∈ N →
        2 ^ 4 ≤ Nat.card N →
          Nat.card N = 2 ^ 5 ∧ N ≤ zpowers s ⊔ ⁅N, centralizer ({s} : Set Y)⁆ ∧
            centralizer (N : Set Y) ≤ N

variable {X : Type} [Group X] [Finite X] {ζ : X} {F : Subgroup X}

omit [Finite X] in
theorem exists_of_mem_sup_centralizer {τ : X} (hτ : τ ∈ F ⊔ centralizer (F : Set X)) :
    ∃ f ∈ F, f⁻¹ * τ ∈ centralizer (F : Set X) := by
  let S₁ : Subgroup X :=
    { carrier := {x | ∃ f ∈ F, f⁻¹ * x ∈ centralizer (F : Set X)}
      mul_mem' := by
        rintro x y ⟨f, hf, hfx⟩ ⟨g, hg, hgy⟩
        refine ⟨f * g, mul_mem hf hg, ?_⟩
        have e : (f * g)⁻¹ * (x * y) = (g⁻¹ * (f⁻¹ * x) * g) * (g⁻¹ * y) := by group
        rw [e]
        refine mul_mem ?_ hgy
        have h1 := mem_centralizer_iff.mp hfx g hg
        rw [show g⁻¹ * (f⁻¹ * x) * g = f⁻¹ * x by rw [mul_assoc, ← h1]; group]
        exact hfx
      one_mem' := ⟨1, one_mem _, by rw [inv_one, one_mul]; exact one_mem _⟩
      inv_mem' := by
        rintro x ⟨f, hf, hfx⟩
        refine ⟨f⁻¹, inv_mem hf, ?_⟩
        have h1 := mem_centralizer_iff.mp hfx f⁻¹ (inv_mem hf)
        have e : f⁻¹⁻¹ * x⁻¹ = f * (f⁻¹ * x)⁻¹ * f⁻¹ := by group
        rw [e]
        have h2 : f * (f⁻¹ * x)⁻¹ * f⁻¹ = (f⁻¹ * x)⁻¹ := by
          have h3 := mem_centralizer_iff.mp (inv_mem hfx) f⁻¹ (inv_mem hf)
          calc f * (f⁻¹ * x)⁻¹ * f⁻¹ = f * ((f⁻¹ * x)⁻¹ * f⁻¹) := by group
            _ = f * (f⁻¹ * (f⁻¹ * x)⁻¹) := by rw [h3]
            _ = (f⁻¹ * x)⁻¹ := by group
        rw [h2]
        exact inv_mem hfx }
  have hle : F ⊔ centralizer (F : Set X) ≤ S₁ :=
    sup_le (fun f hf => ⟨f, hf, by rw [inv_mul_cancel]; exact one_mem _⟩)
      (fun c hc => ⟨1, one_mem _, by rw [inv_one, one_mul]; exact hc⟩)
  exact hle hτ

omit [Finite X] in
theorem orderOf_piU_zeta (hC : SmithConf ζ F) (hs : IsSimpleGroup (UZ ζ)) :
    orderOf (piU ζ (zetaU ζ)) = 2 := by
  have hζ := not_mem_ZU_of_simple hs
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have h2 : zetaU ζ ^ 2 = 1 := by
      apply Subtype.ext
      change ζ ^ 2 = 1
      rw [← hC.hyp.orderOf_eq]
      exact pow_orderOf_eq_one ζ
    rw [h2, map_one]
  · intro h1
    apply hζ
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨zetaU ζ, h1, rfl⟩

theorem smithJ2Input_of (hJc : J2CentInput) :
    ∀ (X : Type) [Group X] [Finite X] (ζ : X) (F : Subgroup X), SmithConf ζ F →
      Blueprint.NativeSporadic.IsSporadic (UZ ζ) .J2 →
        F ≤ normalClosure ({ζ} : Set X) ∧ center ↥(normalClosure ({ζ} : Set X)) ≠ ⊥ := by
  intro X _ _ ζ F hC hJ2
  obtain ⟨e⟩ := hJ2
  have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .J2) := Sporadic.J2.isSimpleGroup_J2
  have hs : IsSimpleGroup (UZ ζ) := e.isSimpleGroup
  have hOut : Nat.card (OuterAutomorphisms.Outer (UZ ζ)) ≤ 2 := by
    rw [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]
    exact Sporadic.Schreier.AT_J2_Schreier.1
  have hF2 := hC.card_le_mul_card_Finn (k := 2) (fun H _ => (card_le_card_group H).trans hOut)
  have hιinj := hC.iota_injective (F := F) hs
  have hζF : ζ ∈ Finn ζ F := hC.zeta_mem_Finn
  have hιζ : SmithConf.iota (F := F) hs ⟨ζ, hζF⟩ = piU ζ (zetaU ζ) :=
    SmithConf.iota_of_mem_U hs ⟨ζ, hζF⟩ (zetaU ζ).2
  have hcardN : Nat.card (SmithConf.iota (F := F) hs).range = Nat.card (Finn ζ F) := by
    rw [MonoidHom.range_eq_map, card_map_of_injective hιinj, card_top]
  have hfz : ∀ f : ↥(Finn ζ F), (f : X) * ζ = ζ * f := fun f =>
    mem_centralizer_singleton_iff.mp (hC.hyp.le_centralizer (Finn_le ζ F f.2))
  have hNC : (SmithConf.iota (F := F) hs).range ≤ centralizer ({piU ζ (zetaU ζ)} : Set (UZ ζ)) := by
    rintro _ ⟨f, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (SmithConf.iota_comm_zeta hs f (hfz f))
  have hNn : ∀ c ∈ centralizer ({piU ζ (zetaU ζ)} : Set (UZ ζ)),
      ∀ n ∈ (SmithConf.iota (F := F) hs).range,
        c * n * c⁻¹ ∈ (SmithConf.iota (F := F) hs).range := by
    rintro c hc _ ⟨f, rfl⟩
    obtain ⟨u, rfl, hu⟩ := hC.exists_lift_of_comm hs (mem_centralizer_singleton_iff.mp hc)
    exact ⟨_, hC.iota_conj_mem hs hu f⟩
  have hF2grp : IsPGroup 2 ↥(Finn ζ F) := hC.hyp.extraspecial.1.to_le (Finn_le ζ F)
  have hN2 : IsPGroup 2 (SmithConf.iota (F := F) hs).range :=
    hF2grp.of_surjective _ (SmithConf.iota (F := F) hs).rangeRestrict_surjective
  have hsN : piU ζ (zetaU ζ) ∈ (SmithConf.iota (F := F) hs).range := ⟨_, hιζ⟩
  have hwidth := hC.hyp.width
  have hN16 : 2 ^ 4 ≤ Nat.card (SmithConf.iota (F := F) hs).range := by
    rw [hcardN]; omega
  obtain ⟨hN32, hNle, hCN⟩ := hJc (UZ ζ) ⟨e⟩ _ (orderOf_piU_zeta hC hs) _ hNC hNn hN2 hsN hN16
  obtain ⟨w, hw⟩ := exists_card_extraspecial hC.hyp.extraspecial
  have hFeq : Finn ζ F = F := by
    refine Subgroup.eq_of_le_of_card_ge (Finn_le ζ F) ?_
    rw [hcardN] at hN32
    rw [hN32]
    have h1 : 2 ^ 5 ≤ 2 ^ (1 + 2 * w) := hw ▸ hwidth
    have h2 : 2 ^ (1 + 2 * w) ≤ 2 ^ 6 := by rw [← hw]; omega
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
    have h5 : w = 2 := by omega
    rw [hw, h5]
  set H : Subgroup X := normalClosure ({ζ} : Set X) ⊓ Finn ζ F with hH
  have hle : zpowers (piU ζ (zetaU ζ)) ⊔
      ⁅(SmithConf.iota (F := F) hs).range, centralizer ({piU ζ (zetaU ζ)} : Set (UZ ζ))⁆ ≤
      (H.subgroupOf (Finn ζ F)).map (SmithConf.iota (F := F) hs) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact ⟨⟨ζ, hζF⟩, mem_subgroupOf.mpr ⟨(zetaU ζ).2, hζF⟩, hιζ⟩
    · rw [commutator_le]
      rintro _ ⟨f, rfl⟩ c hc
      obtain ⟨u, rfl, hu⟩ := hC.exists_lift_of_comm hs (mem_centralizer_singleton_iff.mp hc)
      have hgU : (f : X) * u * (f : X)⁻¹ * (u : X)⁻¹ ∈ normalClosure ({ζ} : Set X) :=
        mul_mem (normalClosure_normal.conj_mem _ u.2 _) (inv_mem u.2)
      have hgF : (f : X) * u * (f : X)⁻¹ * (u : X)⁻¹ ∈ Finn ζ F := by
        have h1 := hC.conj_mem_Finn u.2 hu (inv_mem f.2)
        rw [show (f : X) * u * (f : X)⁻¹ * (u : X)⁻¹ = f * ((u : X) * (f : X)⁻¹ * (u : X)⁻¹) by
          group]
        exact mul_mem f.2 h1
      refine ⟨⟨_, hgF⟩, mem_subgroupOf.mpr ⟨hgU, hgF⟩, ?_⟩
      rw [SmithConf.iota_of_mem_U hs ⟨_, hgF⟩ hgU, commutatorElement_def,
        SmithConf.iota_conj hs f u]
      rw [show (⟨(f : X) * u * (f : X)⁻¹ * (u : X)⁻¹, hgU⟩ : ↥(normalClosure ({ζ} : Set X)))
          = ⟨(f : X) * u * (f : X)⁻¹, normalClosure_normal.conj_mem _ u.2 _⟩ * u⁻¹ from rfl,
        map_mul, map_inv]
  have hFU : F ≤ normalClosure ({ζ} : Set X) := by
    intro f hf
    have hf' : f ∈ Finn ζ F := by rw [hFeq]; exact hf
    obtain ⟨g, hg, hgf⟩ := hle (hNle ⟨⟨f, hf'⟩, rfl⟩)
    replace hg := mem_subgroupOf.mp hg
    have := hιinj hgf
    rw [← show ((g : ↥(Finn ζ F)) : X) = f from congrArg Subtype.val this]
    exact hg.1
  refine ⟨hFU, fun hZ => ?_⟩
  have hπinj : Function.Injective (piU ζ) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  obtain ⟨τ, hτc, hτne⟩ := hC.nonIsolated
  obtain ⟨f, hf, hfc⟩ := exists_of_mem_sup_centralizer (hC.hyp.conj_mem_E τ hτc.2 hτc.1)
  have hτU := mem_normalClosure_of_isConj hτc.2
  have hcU : f⁻¹ * τ ∈ normalClosure ({ζ} : Set X) := mul_mem (inv_mem (hFU hf)) hτU
  have hπc : piU ζ ⟨f⁻¹ * τ, hcU⟩ ∈
      centralizer ((SmithConf.iota (F := F) hs).range : Set (UZ ζ)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    rw [SmithConf.iota_of_mem_U hs g (hFU (Finn_le ζ F g.2)), ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hfc g (Finn_le ζ F g.2))
  obtain ⟨g, hg⟩ := hCN hπc
  rw [SmithConf.iota_of_mem_U hs g (hFU (Finn_le ζ F g.2))] at hg
  have hcg : f⁻¹ * τ = g := congrArg Subtype.val (hπinj hg).symm
  have hτF : τ ∈ F := by
    rw [show τ = f * (f⁻¹ * τ) by group, hcg]
    exact mul_mem hf (Finn_le ζ F g.2)
  exact hτne (hC.hyp.conj_mem_F τ hτF hτc.2)

end S63

end CFSG.LargeExtraspecial
