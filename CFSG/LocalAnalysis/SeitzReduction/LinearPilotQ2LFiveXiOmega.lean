module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveUniMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveXiA
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveXiGen

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift)

theorem lFiveFieldSylowGenInput_holds :
    LFiveFieldSylowGenInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt _ c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀
  obtain ⟨hW₁Nt, -, -, -⟩ :=
    seitzTilde_fusion_facts hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
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
  have hW₁S₀ : W₁ ≤ S₀ := wOne_le_of_not_two_dvd_relIndex (IsPGroup.of_card hW₁c)
    (seitzTilde_le_normalizer W₁ Kc) hS₀p hS₀N hW₁Nt hS₀syl
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
  have hgen := le_closure_conj_involutions_of_fieldComponent hK hs hLs hLq hLZ hCs hsNs hsKs hLK
    hKsm φ hφ hSK hS2 hmax hQS hQs hQc
  set Ω := closure {x : G | x ∈ S₀ ∧ x * x = 1} with hΩ
  have hW₁Ω : W₁ ≤ Ω := fun w hw => subset_closure ⟨hW₁S₀ hw, hW₁2 w hw⟩
  have hker : ∀ a b : N, ν a = ν b → (a : G)⁻¹ * b ∈ W₁ := by
    intro a b hab
    have h1 : ν (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    simpa using h1
  have hVL : ∀ x : G, x ∈ V₁ → x ∈ L₁ → x = 1 := by
    intro x hxV hxL
    obtain ⟨a, ha, rfl⟩ := (mem_modelToG e).1 hxV
    obtain ⟨b, hb, hab⟩ := (mem_modelToG e).1 hxL
    have hab' : b = a := e.symm.injective (Subtype.ext hab)
    have hmem : a ∈ pointRadical (K := K) c ⊓ blockSL (K := K) ({c}ᶜ : Finset (Fin 5)) :=
      mem_inf.2 ⟨ha, hab' ▸ hb⟩
    rw [pointRadical_inf_blockSL_compl_eq_bot hK c, mem_bot] at hmem
    rw [hmem, map_one]
    rfl
  have hY : ∀ y ∈ {y : seitzBar W₁ | y ∈ S ∧ ∃ n ∈ Ks, ∃ q ∈ Lb, q * q = 1 ∧ y = n * q * n⁻¹},
      y ∈ (Ω.subgroupOf N).map ν := by
    rintro y ⟨hyS, n, -, q, hqL, hqq, rfl⟩
    obtain ⟨l, hlL, rfl⟩ := hqL
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (W₁.subgroupOf N) n
    have hlL' : (l : G) ∈ L₁ := mem_subgroupOf.1 hlL
    have hll : (l : G) * l = 1 := by
      have h1 : ((1 : N) : G)⁻¹ * ((l * l : N) : G) ∈ W₁ :=
        hker 1 (l * l) (by rw [map_one, map_mul, hqq])
      simp only [OneMemClass.coe_one, inv_one, one_mul, Subgroup.coe_mul] at h1
      have hlt : (l : G) * l ∈ centralizer ({t} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.1 htC) _ ((modelToG_le e _) (mul_mem hlL' hlL'))
      have h2 : (l : G) * l ∈ W₁ ⊓ centralizer ({t} : Set G) := mem_inf.2 ⟨h1, hlt⟩
      rw [hW₁t] at h2
      exact hVL _ h2 (mul_mem hlL' hlL')
    set z : N := m * l * m⁻¹ with hz
    have hνz : ν z = ν m * ν l * (ν m)⁻¹ := by rw [hz, map_mul, map_mul, map_inv]
    obtain ⟨x', hx'S, hx'⟩ := hyS
    have hzS₀ : (z : G) ∈ S₀ := by
      have h1 := hker x' z (by rw [hνz]; exact hx')
      have h2 : (z : G) = (x' : G) * ((x' : G)⁻¹ * z) := by group
      rw [h2]
      exact mul_mem (mem_subgroupOf.1 hx'S) (hW₁S₀ h1)
    have hzz : (z : G) * z = 1 := by
      have h1 : (z : G) * z = m * ((l : G) * l) * (m : G)⁻¹ := by
        simp only [hz, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h1, hll]
      group
    exact ⟨z, mem_subgroupOf.2 (subset_closure ⟨hzS₀, hzz⟩), hνz⟩
  intro x hx
  have hxN := hS₀N' hx
  have h1 : ν ⟨x, hxN⟩ ∈ S := ⟨⟨x, hxN⟩, mem_subgroupOf.2 hx, rfl⟩
  obtain ⟨ω, hωΩ, hω⟩ := ((closure_le _).2 hY) (hgen h1)
  have h2 := hker ω ⟨x, hxN⟩ hω
  have h3 : x = (ω : G) * ((ω : G)⁻¹ * x) := by group
  rw [h3]
  exact mul_mem (mem_subgroupOf.1 hωΩ) (hW₁Ω h2)

theorem lFiveFieldSylowNormalInput_holds :
    LFiveFieldSylowNormalInput :=
  lFiveFieldSylowNormalInput_of_gen lFiveThompsonFieldInput_holds lFiveFieldSylowGenInput_holds

end CFSG.SeitzReduction.LinearPilot
