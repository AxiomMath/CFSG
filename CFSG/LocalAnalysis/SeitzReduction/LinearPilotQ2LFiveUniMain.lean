module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylLang
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveUniNorm

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift)

theorem lFiveThompsonFieldQuotInput_holds :
    LFiveThompsonFieldQuotInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt _ c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀ u huS
    hu2
  set N := normalizer (W₁ : Set G) with hNdef
  set ν := QuotientGroup.mk' (W₁.subgroupOf N) with hν
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  set V₁ := modelToG e (pointRadical (K := K) c) with hV₁
  set s := ν ⟨t, htN⟩ with hsdef
  set Lb := (L₁.subgroupOf N).map ν with hLbdef
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨hLq, hLZ, -, -, hLs⟩ := leviBar_facts e hK htC hW₁c hLN htN
  have hs : orderOf s = 2 := orderOf_mk_wOne_eq_two e hK ht hW₁c hW₁2 hW₁t htN
  have hCs := centralizer_bar_le_sup e hK ht hW₁c hW₁2 hW₁t htN hLN
    (lFiveNormalizerPointRadicalInput G L hset K hK e t ht hKt c)
  obtain ⟨hKc, hLKc, -, hsKc, -, hmodel, hsN, hout⟩ := hfield
  have hsC : QuotientGroup.mk' (oddCore (seitzBar W₁)) s ∉
      centralizer (Kc : Set (seitzHat W₁)) := by
    intro hc
    apply hout
    have h1 : (⟨_, hsN⟩ : normalizer (Kc : Set (seitzHat W₁))) ∈ Kc.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hc
    exact ⟨1, by rw [map_one, MonoidHom.mem_ker.mp h1]⟩
  obtain ⟨-, -, hmap, hsNs, -, hKsm⟩ := exists_lift_field_of_le_sup hs hLs hLq hLZ hCs
    (fun X _ hX => oddSchurTrivial_of_lieModel_PSL_four_four hX) hKc hsN hsC hmodel
  set Ks := oddCoreLift Kc with hKsdef
  have hLp : ⁅Lb, Lb⁆ = Lb := isPerfect_iff.mp ⟨hLq.1⟩
  have hLK : Lb ≤ Ks := by
    refine F4Pilot.le_oddCoreLift_of_perfect hLp ?_
    have h1 := hLKc.le
    rw [seitzLeviHat_eq_map_map] at h1
    exact h1
  have hsKs : s ∉ Ks := by
    intro h
    apply hsKc
    rw [← hmap]
    exact mem_map_of_mem _ h
  obtain ⟨ψ₁⟩ := nonempty_modelToG_blockSL_compl_mulEquiv e c
  set φ : Matrix.SpecialLinearGroup (Fin 4) K →* seitzBar W₁ :=
    ν.comp ((Subgroup.inclusion hLN).comp ψ₁.symm.toMonoidHom) with hφdef
  have hφ : φ.range = Lb := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      ψ₁.symm.surjective, ← MonoidHom.range_eq_map, Subgroup.inclusion_range]
  obtain ⟨hS₀p, hS₀N, hS₀syl, -, Q₀, hQ₀L, hQ₀c, hQ₀S₀⟩ := hS₀
  have hS₀N' : S₀ ≤ N := hS₀N.trans (seitzTilde_le_normalizer W₁ Kc)
  set S := (S₀.subgroupOf N).map ν with hSdef
  have hSK : S ≤ Ks := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨_, hxK⟩ := mem_seitzTilde_iff.1 (hS₀N (mem_subgroupOf.1 hx))
    exact hxK
  have hS2 : IsPGroup 2 S := (hS₀p.comap_subtype (K := N)).map ν
  have hW2 : IsPGroup 2 ν.ker := by
    rw [hν, QuotientGroup.ker_mk']
    exact (IsPGroup.of_card hW₁c).comap_subtype
  have hmax : ∀ R : Subgroup (seitzBar W₁), IsPGroup 2 R → S ≤ R → R ≤ Ks → R = S := by
    intro R hR hSR hRK
    set R' : Subgroup G := (R.comap ν).map N.subtype with hR'
    have hR'2 : IsPGroup 2 R' := (hR.comap_of_ker_isPGroup ν hW2).map _
    have hS₀R' : S₀ ≤ R' := fun x hx =>
      ⟨⟨x, hS₀N' hx⟩, mem_comap.2 (hSR ⟨⟨x, hS₀N' hx⟩, mem_subgroupOf.2 hx, rfl⟩), rfl⟩
    have hR'Ñ : R' ≤ seitzTilde W₁ Kc := by
      rintro _ ⟨y, hy, rfl⟩
      exact mem_seitzTilde_iff.2 ⟨y.2, hRK (mem_comap.1 hy)⟩
    have hmul := Subgroup.relIndex_mul_relIndex S₀ R' (seitzTilde W₁ Kc) hS₀R' hR'Ñ
    obtain ⟨k, hk⟩ := hR'2.index (S₀.subgroupOf R')
    have h1 : S₀.relIndex R' = 2 ^ k := hk
    have hk0 : k = 0 := by
      by_contra hk0
      apply hS₀syl
      rw [← hmul, h1]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 hk0) _
    rw [hk0, pow_zero] at h1
    have hR'S₀ : R' ≤ S₀ := Subgroup.relIndex_eq_one.1 h1
    refine le_antisymm (fun r hr => ?_) hSR
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (W₁.subgroupOf N) r
    have hy : (y : G) ∈ R' := ⟨y, mem_comap.2 hr, rfl⟩
    exact ⟨y, mem_subgroupOf.2 (hR'S₀ hy), rfl⟩
  have hQ₀N : Q₀ ≤ N := hQ₀S₀.trans hS₀N'
  set Q := (Q₀.subgroupOf N).map ν with hQdef
  have hQS : Q ≤ S := map_mono (fun x hx => mem_subgroupOf.2 (hQ₀S₀ (mem_subgroupOf.1 hx)))
  have hQs : Q ≤ centralizer ({s} : Set (seitzBar W₁)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.1 htC) x (hQ₀L (mem_subgroupOf.1 hx))
  have hQc : 2 ^ 6 ≤ Nat.card Q := by
    set Q₀' := Q₀.subgroupOf N with hQ₀'
    let f : Q₀' →* seitzBar W₁ := ν.comp Q₀'.subtype
    have hfrange : f.range = Q := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hfrange] at h1
    have hQ₀'c : Nat.card Q₀' = 2 ^ 10 :=
      (Nat.card_congr (subgroupOfEquivOfLe hQ₀N).toEquiv).trans hQ₀c
    have hV₁c : Nat.card V₁ = 2 ^ 4 := card_modelToG_pointRadical hK e c
    have hker : Nat.card f.ker ≤ 2 ^ 4 := by
      rw [← hV₁c]
      refine Nat.card_le_card_of_injective (fun x => ⟨(((x : Q₀') : N) : G), ?_⟩) ?_
      · have hx1 : ν (x : Q₀') = 1 := x.2
        rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hx1
        have hxt : (((x : Q₀') : N) : G) ∈ centralizer ({t} : Set G) := by
          rw [mem_centralizer_singleton_iff]
          exact (mem_centralizer_iff.1 htC) _ (hQ₀L (mem_subgroupOf.1 (x : Q₀').2))
        have h2 : (((x : Q₀') : N) : G) ∈ W₁ ⊓ centralizer ({t} : Set G) := mem_inf.2 ⟨hx1, hxt⟩
        rw [hW₁t] at h2
        exact h2
      · intro a b hab
        have h := congrArg Subtype.val hab
        simp only at h
        exact Subtype.ext (Subtype.ext (Subtype.ext h))
    rw [hQ₀'c] at h1
    have h2 : 2 ^ 6 * 2 ^ 4 ≤ Nat.card Q * 2 ^ 4 := by
      calc 2 ^ 6 * 2 ^ 4 = Nat.card Q * Nat.card f.ker := by rw [← h1]; norm_num
        _ ≤ Nat.card Q * 2 ^ 4 := Nat.mul_le_mul_left _ hker
    exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
  have huN : u ∈ N := hS₀N' huS
  have hū : ν ⟨u, huN⟩ ∈ S := ⟨⟨u, huN⟩, mem_subgroupOf.2 huS, rfl⟩
  have hu2' : ν ⟨u, huN⟩ * s * (ν ⟨u, huN⟩ * s) = 1 := by
    rw [hsdef, ← map_mul, ← map_mul, hν, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hu2
  obtain ⟨v, hvS, hv⟩ := exists_inv_mul_mul_eq_one_of_fieldComponent hK hs hLs hLq hLZ hCs hsNs
    hsKs hLK hKsm φ hφ hSK hS2 hmax hQS hQs hQc hū hu2'
  obtain ⟨w, hw, rfl⟩ := hvS
  refine ⟨(w : G), mem_subgroupOf.1 hw, ?_⟩
  have h1 : ν (w⁻¹ * (⟨u, huN⟩ * ⟨t, htN⟩) * w * (⟨t, htN⟩ : N)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hv
  rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  simpa using h1

theorem lFiveThompsonFieldInput_holds :
    LFiveThompsonFieldInput :=
  lFiveThompsonFieldInput_of_quot lFiveThompsonFieldQuotInput_holds

end CFSG.SeitzReduction.LinearPilot
