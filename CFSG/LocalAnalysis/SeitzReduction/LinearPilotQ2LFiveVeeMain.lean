module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeSet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeBeta
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeCount
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeOmega

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.Fischer
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem eq_one_of_mem_levi_of_le_centralizer {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* projectiveSL 5 K) (c : Fin 5) {l : G}
    (hl : l ∈ modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))))
    (hV : modelToG e (pointRadical (K := K) c) ≤ centralizer ({l} : Set G)) : l = 1 := by
  obtain ⟨a, ha, hal⟩ := (mem_modelToG e).1 hl
  have ha1 : a = 1 := by
    refine eq_one_of_mem_blockSL_of_forall_conj_pointRadical hK c ha fun v hv => ?_
    have hv' : ((e.symm v : L) : G) ∈ centralizer ({l} : Set G) := hV (symm_mem_modelToG e hv)
    have hc := mem_centralizer_singleton_iff.1 hv'
    rw [← hal] at hc
    have hc' : e.symm v * e.symm a = e.symm a * e.symm v := Subtype.ext hc
    have hc'' := congrArg e hc'
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hc''
    rw [← hc'']
    group
  rw [← hal, ha1, map_one]
  rfl

theorem exists_wOne_coordinates
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc) :
    ∃ (ψ : seitzTilde W₁ Kc →* SpecialLinearGroup (Fin 4) F4) (β : W₁ → (Fin 4 → F4)),
      Function.Surjective ψ ∧ (∀ n, ψ n = 1 ↔ (n : G) ∈ W₁) ∧
      (∀ n m : seitzTilde W₁ Kc, (m : G) = t * n * t⁻¹ → ψ m = veeFrob (ψ n)) ∧
      Function.Bijective β ∧ (∀ v w : W₁, β (v * w) = β v + β w) ∧
      ((∀ (n : seitzTilde W₁ Kc) (w v : W₁), (v : G) = n * w * n⁻¹ →
          β v = (ψ n : Matrix (Fin 4) (Fin 4) F4) *ᵥ β w) ∨
        ∀ (n : seitzTilde W₁ Kc) (w v : W₁), (v : G) = n * w * n⁻¹ →
          β v = ((ψ n)⁻¹ : SpecialLinearGroup (Fin 4) F4)ᵀ *ᵥ β w) ∧
      ∀ w v : W₁, (v : G) = t * w * t⁻¹ → β v = veeFrobHom ∘ β w := by
  set N := normalizer (W₁ : Set G) with hNdef
  set ν := QuotientGroup.mk' (W₁.subgroupOf N) with hν
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  set V₁ := modelToG e (pointRadical (K := K) c) with hV₁
  set s := ν ⟨t, htN⟩ with hsdef
  set Lb := (L₁.subgroupOf N).map ν with hLbdef
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨hLq, hLZ, -, -, hLs⟩ := leviBar_facts e hK htC hW₁c hLN htN
  have hs : orderOf s = 2 := orderOf_mk_wOne_eq_two e hK ht hW₁c hW₁2 hW₁t htN
  have hCs := centralizer_bar_le_sup e hK ht hW₁c hW₁2 hW₁t htN hLN
    (lFiveNormalizerPointRadicalInput G L hset K hK e t ht hKt c)
  obtain ⟨-, htNt, htNNt, -⟩ :=
    seitzTilde_fusion_facts hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
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
  obtain ⟨ψ', hψ'θ, hψ'L⟩ := exists_mulEquiv_specialLinear_F4_of_lieModel_four_four hK hs hLs
    hLq hLZ hCs hsNs hsKs hLK hKsm φ hφ
  let _ : CommGroup W₁ :=
    { (inferInstance : Group W₁) with
      mul_comm := fun a b => Subtype.ext (mul_comm_of_forall_mul_self_eq_one hW₁2 a.2 b.2) }
  have hconj : ∀ (n : N) (w : W₁), (n : G) * w * (n : G)⁻¹ ∈ W₁ := fun n w =>
    (mem_normalizer_iff.1 n.2 w).1 w.2
  let cnjf : N → AddMonoid.End (Additive W₁) := fun n =>
    { toFun := fun x => Additive.ofMul ⟨(n : G) * ((Additive.toMul x : W₁) : G) * (n : G)⁻¹, hconj n _⟩
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp
      map_add' := fun x y => by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp only [toMul_add, toMul_ofMul, Subgroup.coe_mul]
        group }
  have hcnjf : ∀ n x, ((Additive.toMul (cnjf n x) : W₁) : G) =
      (n : G) * ((Additive.toMul x : W₁) : G) * (n : G)⁻¹ := fun n x => rfl
  let cnj : N →* AddMonoid.End (Additive W₁) :=
    { toFun := cnjf
      map_one' := by
        refine AddMonoidHom.ext fun x => ?_
        apply Additive.toMul.injective
        apply Subtype.ext
        change ((1 : N) : G) * ((Additive.toMul x : W₁) : G) * ((1 : N) : G)⁻¹ =
          ((Additive.toMul x : W₁) : G)
        simp
      map_mul' := fun n m => by
        refine AddMonoidHom.ext fun x => ?_
        apply Additive.toMul.injective
        apply Subtype.ext
        change ((n * m : N) : G) * ((Additive.toMul x : W₁) : G) * ((n * m : N) : G)⁻¹ =
          (n : G) * ((m : G) * ((Additive.toMul x : W₁) : G) * (m : G)⁻¹) * (n : G)⁻¹
        simp only [Subgroup.coe_mul]
        group }
  have hcnj : ∀ n x, ((Additive.toMul (cnj n x) : W₁) : G) =
      (n : G) * ((Additive.toMul x : W₁) : G) * (n : G)⁻¹ := fun n x => rfl
  have hker : W₁.subgroupOf N ≤ cnj.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    refine AddMonoidHom.ext fun x => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    have h1 := mul_comm_of_forall_mul_self_eq_one hW₁2 (mem_subgroupOf.1 hn) (Additive.toMul x).2
    change (n : G) * ((Additive.toMul x : W₁) : G) * (n : G)⁻¹ = ((Additive.toMul x : W₁) : G)
    rw [h1]
    group
  let ρbar : seitzBar W₁ →* AddMonoid.End (Additive W₁) := QuotientGroup.lift _ cnj hker
  let ρ : SpecialLinearGroup (Fin 4) F4 →* AddMonoid.End (Additive W₁) :=
    (ρbar.comp Ks.subtype).comp ψ'.symm.toMonoidHom
  have hρν : ∀ (n : N) (hn : ν n ∈ Ks), ρ (ψ' ⟨ν n, hn⟩) = cnj n := by
    intro n hn
    change ρbar ((ψ'.symm (ψ' ⟨ν n, hn⟩) : Ks) : seitzBar W₁) = cnj n
    rw [MulEquiv.symm_apply_apply]
    exact QuotientGroup.lift_mk' _ _ n
  have hfixcard : ∀ n : N, Nat.card {x : Additive W₁ // cnj n x = x} =
      Nat.card (W₁ ⊓ centralizer ({(n : G)} : Set G) : Subgroup G) := by
    intro n
    have hiff : ∀ x : Additive W₁, cnj n x = x ↔
        ((Additive.toMul x : W₁) : G) * n = n * (Additive.toMul x : W₁) := by
      intro x
      constructor
      · intro h
        have h1 := congrArg (fun y : Additive W₁ => ((Additive.toMul y : W₁) : G)) h
        simp only [hcnj] at h1
        calc ((Additive.toMul x : W₁) : G) * n = n * (Additive.toMul x : W₁) * (n : G)⁻¹ * n := by
              rw [h1]
          _ = n * (Additive.toMul x : W₁) := by group
      · intro h
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [hcnj, ← h]
        group
    refine Nat.card_congr
      { toFun := fun x => ⟨((Additive.toMul x.1 : W₁) : G), mem_inf.2 ⟨(Additive.toMul x.1).2,
          mem_centralizer_singleton_iff.2 ((hiff x.1).1 x.2)⟩⟩
        invFun := fun w => ⟨Additive.ofMul ⟨w.1, (mem_inf.1 w.2).1⟩, (hiff _).2
          (mem_centralizer_singleton_iff.1 (mem_inf.1 w.2).2)⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
  have hlift : ∀ x : SpecialLinearGroup (Fin 4) F4, veeFrob x = x →
      ∃ (l : N) (hl : ν l ∈ Ks), (l : G) ∈ L₁ ∧ ψ' ⟨ν l, hl⟩ = x := by
    intro x hx
    obtain ⟨l, hl, hlν⟩ := hψ'L x hx
    have hlK : ν l ∈ Ks := by rw [hlν]; exact (ψ'.symm x).2
    refine ⟨l, hlK, mem_subgroupOf.1 hl, ?_⟩
    have h1 : (⟨ν l, hlK⟩ : Ks) = ψ'.symm x := Subtype.ext hlν
    rw [h1, MulEquiv.apply_symm_apply]
  have hpowK : ∀ (l : N) (hl : ν l ∈ Ks) (k : ℕ), ν (l ^ k) ∈ Ks := fun l hl k => by
    rw [map_pow]; exact pow_mem hl k
  have hpow : ∀ (l : N) (hl : ν l ∈ Ks) (k : ℕ),
      ψ' ⟨ν (l ^ k), hpowK l hl k⟩ = ψ' ⟨ν l, hl⟩ ^ k := fun l hl k => by
    rw [← map_pow]
    congr 1
  have hL₁W : ∀ (l : N), (l : G) ∈ L₁ → ν l = 1 → l = 1 := by
    intro l hlL hl1
    rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hl1
    have hlt : (l : G) ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) _ (modelToG_le e _ hlL))
    have hlV : (l : G) ∈ V₁ := by rw [← hW₁t]; exact mem_inf.2 ⟨hl1, hlt⟩
    have h := modelToG_pointRadical_inf_eq_bot hK e c
    have h2 : (l : G) ∈ V₁ ⊓ L₁ := mem_inf.2 ⟨hlV, hlL⟩
    rw [h] at h2
    exact Subtype.ext h2
  have horder : ∀ (l : N) (hl : ν l ∈ Ks) (k : ℕ), (l : G) ∈ L₁ → ψ' ⟨ν l, hl⟩ ^ k = 1 →
      (l : G) ^ k = 1 := by
    intro l hl k hlL hk
    have h1 : ν (l ^ k) = 1 := by
      have h2 := hpow l hl k
      rw [hk] at h2
      have h3 : (⟨ν (l ^ k), hpowK l hl k⟩ : Ks) = 1 := ψ'.injective (by rw [h2, map_one])
      exact congrArg Subtype.val h3
    have h4 := hL₁W (l ^ k) (pow_mem hlL k) h1
    have h5 := congrArg Subtype.val h4
    simpa using h5
  have hV₁c : Nat.card V₁ = 16 := by rw [card_modelToG_pointRadical hK e c]; norm_num
  have hlVN : ∀ (l : G), l ∈ L₁ → l ∈ normalizer (V₁ : Set G) := by
    intro l hlL
    rw [← hW₁t]
    exact mem_normalizer_inf_of_mem_normalizer (hLN hlL)
      (mem_normalizer_centralizer_of_mul_comm ((mem_centralizer_iff.1 htC) _ (modelToG_le e _ hlL)))
  have hdelta : ∀ (l : G), l ∈ L₁ → Nat.card (W₁ ⊓ centralizer ({l} : Set G) : Subgroup G) ≤
      Nat.card (V₁ ⊓ centralizer ({l} : Set G) : Subgroup G) ^ 2 := by
    intro l hlL
    have hlt : l * t = t * l := (mem_centralizer_iff.1 htC) _ (modelToG_le e _ hlL)
    have h := card_inf_centralizer_le_sq_of_exponent_two hW₁2 ht2 htN hlt
    rwa [hW₁t] at h
  have hone : ∀ (l : N) (hl : ν l ∈ Ks), l = 1 → ψ' ⟨ν l, hl⟩ = 1 := by
    rintro l hl rfl
    have h2 : (⟨ν 1, hl⟩ : Ks) = 1 := Subtype.ext (map_one ν)
    rw [h2, map_one]
  obtain ⟨lB, hlBK, hlBL, hlBψ⟩ := hlift veeB veeFrob_veeB
  have hρB : ρ veeB = cnj lB := by rw [← hlBψ, hρν]
  have hB : Nat.card {x : Additive W₁ // ρ veeB x = x} ≤ 16 := by
    rw [hρB, hfixcard]
    have hl3 : (lB : G) ^ 3 = 1 := horder lB hlBK 3 hlBL (by rw [hlBψ, veeB_pow_three])
    have hnt : ¬ V₁ ≤ centralizer ({(lB : G)} : Set G) := by
      intro hle
      have h1 := eq_one_of_mem_levi_of_le_centralizer hK e c hlBL hle
      apply veeB_ne_one
      rw [← hlBψ]
      exact hone lB hlBK (Subtype.ext h1)
    have h4 := card_inf_centralizer_le_four_of_pow_three hV₁c (hlVN _ hlBL) hl3 hnt
    calc _ ≤ Nat.card (V₁ ⊓ centralizer ({(lB : G)} : Set G) : Subgroup G) ^ 2 := hdelta _ hlBL
      _ ≤ 4 ^ 2 := Nat.pow_le_pow_left h4 2
      _ = 16 := by norm_num
  obtain ⟨ζ, hζK, hζL, hζψ⟩ := hlift veeS veeFrob_veeS
  have hρC : ρ veeC = cnj (ζ ^ 5) := by
    rw [← veeS_pow_five, ← hζψ, ← hpow ζ hζK 5, hρν]
  have hζ15 : (ζ : G) ^ 15 = 1 := horder ζ hζK 15 hζL (by rw [hζψ, veeS_pow_fifteen])
  have hnt' : ∀ k : ℕ, ψ' ⟨ν ζ, hζK⟩ ^ k ≠ 1 → ¬ V₁ ≤ centralizer ({(ζ : G) ^ k} : Set G) := by
    intro k hk hle
    have h1 := eq_one_of_mem_levi_of_le_centralizer hK e c (pow_mem hζL k) hle
    apply hk
    rw [← hpow ζ hζK k]
    exact hone _ _ (Subtype.ext (by rw [Subgroup.coe_pow]; exact h1))
  have hV5 := inf_centralizer_eq_bot_of_pow_fifteen hV₁c (hlVN _ hζL) hζ15
    (hnt' 3 (by rw [hζψ]; exact veeS_pow_three_ne_one))
    (hnt' 5 (by rw [hζψ, veeS_pow_five]; exact veeC_ne_one))
  have hζ5L : ((ζ ^ 5 : N) : G) ∈ L₁ := by rw [Subgroup.coe_pow]; exact pow_mem hζL 5
  have hC : ∀ x : Additive W₁, ρ veeC x = x → x = 0 := by
    intro x hx
    rw [hρC] at hx
    have hW5 : Nat.card (W₁ ⊓ centralizer ({((ζ ^ 5 : N) : G)} : Set G) : Subgroup G) ≤ 1 := by
      have h1 := hdelta _ hζ5L
      rw [Subgroup.coe_pow, hV5, Subgroup.card_bot] at h1
      rw [Subgroup.coe_pow]
      simpa using h1
    have hmem : ((Additive.toMul x : W₁) : G) ∈
        W₁ ⊓ centralizer ({((ζ ^ 5 : N) : G)} : Set G) := by
      refine mem_inf.2 ⟨(Additive.toMul x).2, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := congrArg (fun y : Additive W₁ => ((Additive.toMul y : W₁) : G)) hx
      simp only [hcnj] at h1
      calc ((Additive.toMul x : W₁) : G) * ((ζ ^ 5 : N) : G) =
            ((ζ ^ 5 : N) : G) * (Additive.toMul x : W₁) * ((ζ ^ 5 : N) : G)⁻¹ *
              ((ζ ^ 5 : N) : G) := by rw [h1]
        _ = ((ζ ^ 5 : N) : G) * (Additive.toMul x : W₁) := by group
    have hbot := (Subgroup.card_le_one_iff_eq_bot _).1 hW5
    rw [hbot, mem_bot] at hmem
    apply Additive.toMul.injective
    exact Subtype.ext hmem
  have h2E : ∀ x : Additive W₁, x + x = 0 := fun x => by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hW₁2 _ (Additive.toMul x).2
  have hEc : Nat.card (Additive W₁) = 2 ^ 8 := hW₁c
  obtain ⟨ω, hω, hωρ, hsemi⟩ := exists_omega_of_fixed h2E hEc ρ hB hC
  have hρB1 : ρ veeB ≠ 1 := by
    intro h
    have h1 := hB
    rw [h] at h1
    have h2 : Nat.card {x : Additive W₁ // (1 : AddMonoid.End (Additive W₁)) x = x} = 2 ^ 8 :=
      (Nat.card_congr (Equiv.subtypeUnivEquiv fun x => rfl)).trans hEc
    rw [h2] at h1
    norm_num at h1
  have hρ : ∀ g, ρ g = 1 → g = 1 := eq_one_of_apply_eq_one ρ hρB1
  set t' : N := ⟨t, htN⟩ with ht'
  have ht'2 : t' * t' = 1 := Subtype.ext ht2
  let τ : Additive W₁ →+ Additive W₁ := cnj t'
  have hττ : ∀ x, τ (τ x) = x := fun x => by
    change (cnj t' * cnj t') x = x
    rw [← map_mul, ht'2, map_one]
    rfl
  have hτ : Function.Bijective τ := Function.Involutive.bijective hττ
  have hθν : ∀ (n : N) (hn : ν n ∈ Ks), ∃ hn' : ν (t' * n * t'⁻¹) ∈ Ks,
      Ks.normalizerMonoidHom ⟨s, hsNs⟩ ⟨ν n, hn⟩ = ⟨ν (t' * n * t'⁻¹), hn'⟩ := by
    intro n hn
    have h1 : ν (t' * n * t'⁻¹) = s * ν n * s⁻¹ := by rw [map_mul, map_mul, map_inv]
    have hmem : ν (t' * n * t'⁻¹) ∈ Ks := by rw [h1]; exact (mem_normalizer_iff.1 hsNs _).1 hn
    refine ⟨hmem, ?_⟩
    apply Subtype.ext
    rw [F4Pilot.coe_normalizerMonoidHom_mk_apply Ks hsNs]
    exact h1.symm
  have hτρ : ∀ g x, τ (ρ g x) = ρ (veeFrob g) (τ x) := by
    intro g x
    obtain ⟨k, rfl⟩ := ψ'.surjective g
    obtain ⟨n, hnk⟩ := QuotientGroup.mk'_surjective (W₁.subgroupOf N) (k : seitzBar W₁)
    have hnν : ν n = (k : seitzBar W₁) := hnk
    have hnK : ν n ∈ Ks := by rw [hnν]; exact k.2
    have hk : k = ⟨ν n, hnK⟩ := Subtype.ext hnν.symm
    obtain ⟨hn', hθ⟩ := hθν n hnK
    rw [hk, ← hψ'θ, hθ, hρν, hρν]
    change (cnj t' * cnj n) x = (cnj (t' * n * t'⁻¹) * cnj t') x
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have hτω : ∀ x, τ (ω x) = ω (ω (τ x)) := hsemi τ hτρ
  obtain ⟨β', hβ'ρ, hβ'τ⟩ := exists_addEquiv_of_omega h2E hEc ρ hρ ω hω hωρ τ hτ hτρ hτω
  have hNt : ∀ n : seitzTilde W₁ Kc, (n : G) ∈ N := fun n => (mem_seitzTilde_iff.1 n.2).1
  have hνK : ∀ n : seitzTilde W₁ Kc, ν ⟨n, hNt n⟩ ∈ Ks := fun n => (mem_seitzTilde_iff.1 n.2).2
  let νK : seitzTilde W₁ Kc →* Ks :=
    { toFun := fun n => ⟨ν ⟨n, hNt n⟩, hνK n⟩
      map_one' := Subtype.ext (map_one ν)
      map_mul' := fun n m => Subtype.ext (map_mul ν ⟨n, hNt n⟩ ⟨m, hNt m⟩) }
  let ψt : seitzTilde W₁ Kc →* SpecialLinearGroup (Fin 4) F4 := ψ'.toMonoidHom.comp νK
  have hψt : ∀ n : seitzTilde W₁ Kc, ψt n = ψ' ⟨ν ⟨n, hNt n⟩, hνK n⟩ := fun n => rfl
  have hρψt : ∀ n : seitzTilde W₁ Kc, ρ (ψt n) = cnj ⟨n, hNt n⟩ := fun n => by
    rw [hψt, hρν]
  refine ⟨ψt, fun w => β' (Additive.ofMul w), fun x => ?_, fun n => ?_, fun n m hm => ?_,
    β'.bijective.comp Additive.ofMul.bijective, fun v w => ?_, ?_, fun w v hv => ?_⟩
  ·
    obtain ⟨k, rfl⟩ := ψ'.surjective x
    obtain ⟨n, hnk⟩ := QuotientGroup.mk'_surjective (W₁.subgroupOf N) (k : seitzBar W₁)
    have hnν : ν n = (k : seitzBar W₁) := hnk
    have hnT : (n : G) ∈ seitzTilde W₁ Kc :=
      mem_seitzTilde_iff.2 ⟨n.2, by
        have h : (⟨(n : G), n.2⟩ : N) = n := rfl
        rw [h, ← hν, hnν]
        exact k.2⟩
    refine ⟨⟨n, hnT⟩, ?_⟩
    rw [hψt]
    congr 1
    exact Subtype.ext hnν
  ·
    rw [hψt]
    constructor
    · intro h
      have h1 : (⟨ν ⟨n, hNt n⟩, hνK n⟩ : Ks) = 1 := ψ'.injective (by rw [h, map_one])
      have h2 : ν ⟨n, hNt n⟩ = 1 := congrArg Subtype.val h1
      rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h2
      exact h2
    · intro h
      have h1 : ν ⟨n, hNt n⟩ = 1 := by
        rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
        exact h
      have h2 : (⟨ν ⟨n, hNt n⟩, hνK n⟩ : Ks) = 1 := Subtype.ext h1
      rw [h2, map_one]
  ·
    obtain ⟨hn', hθ⟩ := hθν ⟨n, hNt n⟩ (hνK n)
    rw [hψt, hψt, ← hψ'θ, hθ]
    congr 2
    congr 1
    apply Subtype.ext
    change (m : G) = t * n * t⁻¹
    exact hm
  ·
    change β' (Additive.ofMul (v * w)) = β' (Additive.ofMul v) + β' (Additive.ofMul w)
    rw [ofMul_mul, map_add]
  ·
    have hconjeq : ∀ (n : seitzTilde W₁ Kc) (w v : W₁), (v : G) = n * w * n⁻¹ →
        Additive.ofMul v = ρ (ψt n) (Additive.ofMul w) := by
      intro n w v hv
      rw [hρψt]
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hcnj]
      exact hv
    rcases hβ'ρ with h | h
    · refine Or.inl fun n w v hv => ?_
      change β' (Additive.ofMul v) = _
      rw [hconjeq n w v hv, h]
    · refine Or.inr fun n w v hv => ?_
      change β' (Additive.ofMul v) = _
      rw [hconjeq n w v hv, h]
  ·
    have h1 : Additive.ofMul v = τ (Additive.ofMul w) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (v : G) = t * w * t⁻¹
      exact hv
    change β' (Additive.ofMul v) = _
    rw [h1, hβ'τ]

end CFSG.SeitzReduction.LinearPilot
