module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGrCount

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem seitzTilde_fusion_facts
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc) :
    W₁ ≤ seitzTilde W₁ Kc ∧ t ∉ seitzTilde W₁ Kc ∧
      t ∈ normalizer (seitzTilde W₁ Kc : Set G) ∧
      ∀ g : G, g * t * g⁻¹ ∈ seitzTilde W₁ Kc ⊔ zpowers t →
        ∃ m ∈ seitzTilde W₁ Kc ⊔ zpowers t, g * t * g⁻¹ = m * t * m⁻¹ := by
  have hconj := not_conj_mem_seitzTilde hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  set N := normalizer (W₁ : Set G) with hNdef
  set ν := QuotientGroup.mk' (W₁.subgroupOf N) with hν
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  set s := ν ⟨t, htN⟩ with hsdef
  set Lb := (L₁.subgroupOf N).map ν with hLbdef
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
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
  obtain ⟨-, -, hLang⟩ :=
    facts_of_lieModel_four_four hK hs hLs hLq hLZ hCs hsNs hsKs hLK hKsm φ hφ
  set Nt := seitzTilde W₁ Kc with hNtdef
  have hmemNt : ∀ (g : G) (hg : g ∈ N), ν ⟨g, hg⟩ ∈ Ks → g ∈ Nt := fun g hg h =>
    mem_seitzTilde_iff.2 ⟨hg, h⟩
  have hNtmem : ∀ g ∈ Nt, ∃ hg : g ∈ N, ν ⟨g, hg⟩ ∈ Ks := fun g hg => mem_seitzTilde_iff.1 hg
  have hW₁Nt : W₁ ≤ Nt := fun w hw => hmemNt w (le_normalizer hw) (by
    have h1 : ν ⟨w, le_normalizer hw⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hw)
    rw [h1]
    exact one_mem _)
  have htNt : t ∉ Nt := fun h => by
    obtain ⟨hg, hgK⟩ := hNtmem t h
    exact hsKs hgK
  have hconjNt : ∀ g ∈ Nt, t * g * t⁻¹ ∈ Nt := by
    intro g hg
    obtain ⟨hgN, hgK⟩ := hNtmem g hg
    have hmem : t * g * t⁻¹ ∈ N := mul_mem (mul_mem htN hgN) (inv_mem htN)
    refine hmemNt _ hmem ?_
    have h1 : (⟨t * g * t⁻¹, hmem⟩ : N) = ⟨t, htN⟩ * ⟨g, hgN⟩ * (⟨t, htN⟩ : N)⁻¹ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 hsNs _).1 hgK
  have htNNt : t ∈ normalizer (Nt : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    refine ⟨hconjNt g, fun h => ?_⟩
    have h1 := hconjNt _ h
    have h2 : t * (t * g * t⁻¹) * t⁻¹ = g := by
      calc t * (t * g * t⁻¹) * t⁻¹ = (t * t) * g * (t * t)⁻¹ := by group
        _ = g := by rw [ht2]; group
    rwa [h2] at h1
  refine ⟨hW₁Nt, htNt, htNNt, ?_⟩
  have hMN : Nt ⊔ zpowers t ≤ N := sup_le (seitzTilde_le_normalizer W₁ Kc) ((zpowers_le).2 htN)
  have hsurj := tcomm_surjective_of_card hW₁2 ht2 htN
    (by rw [hW₁c, card_wOne_inf_centralizer e hK hW₁t]; norm_num)
  intro g hg
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htNNt hg with h | h
  · exact absurd (by simpa using h) (hconj g⁻¹)
  · have hyN : g * t * g⁻¹ ∈ N := hMN hg
    have hy2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hyi : (g * t * g⁻¹)⁻¹ = g * t * g⁻¹ := inv_eq_of_mul_eq_one_right hy2
    obtain ⟨hnN, hnK⟩ := hNtmem _ h
    have hinvn : s * ν ⟨g * t * g⁻¹ * t, hnN⟩ * s⁻¹ = (ν ⟨g * t * g⁻¹ * t, hnN⟩)⁻¹ := by
      have h1 : (⟨t, htN⟩ : N) * ⟨g * t * g⁻¹ * t, hnN⟩ * (⟨t, htN⟩ : N)⁻¹ =
          (⟨g * t * g⁻¹ * t, hnN⟩ : N)⁻¹ := by
        apply Subtype.ext
        change t * (g * t * g⁻¹ * t) * t⁻¹ = (g * t * g⁻¹ * t)⁻¹
        rw [mul_inv_rev, hyi, hti]
        calc t * (g * t * g⁻¹ * t) * t = t * (g * t * g⁻¹) * (t * t) := by group
          _ = t * (g * t * g⁻¹) := by rw [ht2, mul_one]
      rw [← map_mul, ← map_inv, ← map_mul, h1, map_inv]
    obtain ⟨k, hkK, hk⟩ := hLang _ hnK hinvn
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk'_surjective (W₁.subgroupOf N) k
    have hκNt : (κ : G) ∈ Nt := hmemNt _ κ.2 (by
      rw [show (⟨(κ : G), κ.2⟩ : N) = κ from rfl]
      rw [← hκ] at hkK
      exact hkK)
    have hw : (κ : G)⁻¹ * (g * t * g⁻¹) * κ * t⁻¹ ∈ W₁ := by
      have h1 : ν (κ⁻¹ * ⟨g * t * g⁻¹, hyN⟩ * κ * (⟨t, htN⟩ : N)⁻¹) = 1 := by
        have h2 : (⟨g * t * g⁻¹, hyN⟩ : N) = ⟨g * t * g⁻¹ * t, hnN⟩ * ⟨t, htN⟩ := by
          apply Subtype.ext
          change g * t * g⁻¹ = g * t * g⁻¹ * t * t
          rw [mul_assoc (g * t * g⁻¹) t t, ht2, mul_one]
        have h3 : ν ⟨g * t * g⁻¹, hyN⟩ = k * s * k⁻¹ := by rw [h2, map_mul, hk]
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h3, hκ, ← hsdef]
        group
      rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      simpa using h1
    have hwt : (κ : G)⁻¹ * (g * t * g⁻¹) * κ * t⁻¹ * t *
        ((κ : G)⁻¹ * (g * t * g⁻¹) * κ * t⁻¹ * t) = 1 := by
      calc (κ : G)⁻¹ * (g * t * g⁻¹) * κ * t⁻¹ * t *
            ((κ : G)⁻¹ * (g * t * g⁻¹) * κ * t⁻¹ * t) =
          (κ : G)⁻¹ * (g * t * g⁻¹ * (g * t * g⁻¹)) * κ := by group
        _ = 1 := by rw [hy2]; group
    obtain ⟨u, huW, hu⟩ := exists_conj_eq_of_mul_self_eq_one hW₁2 ht2 hsurj hw hwt
    refine ⟨(κ : G) * u, mem_sup_left (mul_mem hκNt (hW₁Nt huW)), ?_⟩
    have h1 : g * t * g⁻¹ = (κ : G) * ((κ : G)⁻¹ * (g * t * g⁻¹) * κ * t⁻¹ * t) * (κ : G)⁻¹ := by
      group
    rw [h1, hu]
    group

theorem card_centralizer_dvd_two_pow_twelve_mul (hset : SeitzSetting G L) {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    Nat.card (centralizer ({t} : Set G)) ∣ 2 ^ 12 * 9765 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have h1 := card_centralizer_dvd_two_mul_card_mulAut hset.2.2.2.1 e ht hKt
  have h2 := card_mulAut_projectiveSL_dvd (n := 5) (K := K) (by norm_num) (f := 1)
    (by rw [pow_one]; exact hK)
  rw [card_GL_five_of_card_two hK] at h2
  refine h1.trans ?_
  have h3 : 2 * (2 * 1 * 9999360) = 2 ^ 12 * 9765 := by norm_num
  rw [← h3]
  exact Nat.mul_dvd_mul_left 2 h2

theorem two_dvd_index_of_le_seitzTilde_sup_of_graph
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hgraph : ∃ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc)
    {T₀ : Subgroup G} (hT₀ : IsPGroup 2 T₀) (hT₀M : T₀ ≤ seitzTilde W₁ Kc ⊔ zpowers t) :
    2 ∣ T₀.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hfus⟩ :=
    seitzTilde_fusion_facts hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l hl)
  have hzt : zpowers t ≤ centralizer ({t} : Set G) :=
    (zpowers_le).2 (mem_centralizer_singleton_iff.2 rfl)
  have hzL : zpowers t ≤ centralizer (L : Set G) := (zpowers_le).2 htC
  have hLtc : Nat.card (L ⊔ zpowers t : Subgroup G) = 2 ^ 11 * 9765 := by
    rw [card_sup_eq_mul_of_le_centralizer_of_inf_eq_bot hzL
      (inf_zpowers_eq_bot hset.center_eq_bot htC ht), Nat.card_congr e.toEquiv,
      card_projectiveSL_five_of_card_two hK, Nat.card_zpowers, ht]
    norm_num
  have hmax11 : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ L ⊔ zpowers t → Nat.card P ≤ 2 ^ 11 :=
    fun P hP hPL => card_le_two_pow_of_isPGroup_of_dvd hP (by decide)
      (hLtc ▸ Subgroup.card_dvd_of_le hPL)
  obtain ⟨g₀, hg₀C, hg₀⟩ := hgraph
  have htNL : t ∈ normalizer (L : Set G) := cKind_mem_normalizer hLt
  have hg₀L : g₀ ∉ L ⊔ zpowers t := by
    intro h
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htNL h with h1 | h1
    · obtain ⟨x, -, hx⟩ := hg₀ g₀ h1
      exact hx rfl
    · obtain ⟨x, hxL, hx⟩ := hg₀ (g₀ * t) h1
      apply hx
      have hxt : x * t = t * x := (mem_centralizer_iff.1 htC) x hxL
      calc g₀ * x * g₀⁻¹ = g₀ * (x * t) * t⁻¹ * g₀⁻¹ := by group
        _ = g₀ * (t * x) * t⁻¹ * g₀⁻¹ := by rw [hxt]
        _ = g₀ * t * x * (g₀ * t)⁻¹ := by group
  have hLC : L ⊔ zpowers t ≤ centralizer ({t} : Set G) := sup_le hLt hzt
  have hcardlt := Subgroup.card_lt_of_lt (lt_of_le_of_ne hLC fun h => hg₀L (h ▸ hg₀C))
  have hdvd1 := Subgroup.card_dvd_of_le hLC
  rw [hLtc] at hdvd1 hcardlt
  obtain ⟨a, ha⟩ := hdvd1
  have ha2 : a ∣ 2 := by
    have h := card_centralizer_dvd_two_pow_twelve_mul hset hK e ht hKt
    rw [ha, show 2 ^ 12 * 9765 = 2 ^ 11 * 9765 * 2 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have ha1 : 2 ≤ a := by
    by_contra h
    have h1 : a ≤ 1 := by omega
    rw [ha] at hcardlt
    have h2 : 2 ^ 11 * 9765 * a ≤ 2 ^ 11 * 9765 :=
      (Nat.mul_le_mul_left _ h1).trans_eq (mul_one _)
    omega
  have haeq : a = 2 := le_antisymm (Nat.le_of_dvd (by norm_num) ha2) ha1
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := centralizer ({t} : Set G)) 2
    (n := 12) (by rw [ha, haeq]; norm_num)
  set R : Subgroup G := Q.map (centralizer ({t} : Set G)).subtype with hRdef
  have hRc : Nat.card R = 2 ^ 12 := by
    rw [hRdef, card_map_of_injective (centralizer ({t} : Set G)).subtype_injective, hQ]
  have hRp : IsPGroup 2 R := IsPGroup.of_card hRc
  have hRC : R ≤ centralizer ({t} : Set G) := map_subtype_le _
  have htR : t ∈ R := by
    by_contra htR
    have htCR : t ∈ centralizer (R : Set G) :=
      mem_centralizer_iff.2 fun r hr => mem_centralizer_singleton_iff.1 (hRC hr)
    have htNR : t ∈ normalizer (R : Set G) := Subgroup.centralizer_le_normalizer _ htCR
    have h1 := card_sup_zpowers_eq_two_mul htR htNR ht2
    have h2 := card_le_two_pow_twelve_of_isPGroup_of_le_centralizer hset hK e ht hKt
      (isPGroup_sup_zpowers hRp htR htNR ht2) (sup_le hRC hzt)
    rw [h1, hRc] at h2
    norm_num at h2
  by_contra hidx
  obtain ⟨S', hRS'⟩ := hRp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' (hT₀.toSylow hidx)
  have hconjR : ∀ r ∈ R, g * r * g⁻¹ ∈ T₀ := by
    intro r hr
    have h1 := Subgroup.smul_mem_pointwise_smul r (MulAut.conj g) (S' : Subgroup G) (hRS' hr)
    rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe] at h1
    exact h1
  obtain ⟨m, hmM, hm⟩ := hfus g (hT₀M (hconjR t htR))
  set b := m⁻¹ * g with hbdef
  have htb : t = b * t * b⁻¹ := by
    calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
      _ = m⁻¹ * (g * t * g⁻¹) * m := by rw [hm]
      _ = b * t * b⁻¹ := by rw [hbdef]; group
  have hMN : seitzTilde W₁ Kc ⊔ zpowers t ≤ normalizer (W₁ : Set G) :=
    sup_le (seitzTilde_le_normalizer W₁ Kc) ((zpowers_le).2 htN)
  have hA8 := lFiveNormalizerPointRadicalInput G L hset K hK e t ht hKt c
  set P : Subgroup G := R.map (MulAut.conj b).toMonoidHom with hPdef
  have hPc : Nat.card P = 2 ^ 12 := by
    rw [hPdef, card_map_of_injective (MulAut.conj b).injective, hRc]
  have hPL : P ≤ L ⊔ zpowers t := by
    rintro _ ⟨r, hr, rfl⟩
    change b * r * b⁻¹ ∈ L ⊔ zpowers t
    have hyM : b * r * b⁻¹ ∈ seitzTilde W₁ Kc ⊔ zpowers t := by
      have h1 : b * r * b⁻¹ = m⁻¹ * (g * r * g⁻¹) * m := by rw [hbdef]; group
      rw [h1]
      exact mul_mem (mul_mem (inv_mem hmM) (hT₀M (hconjR r hr))) hmM
    have hyC : b * r * b⁻¹ ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have hrt : r * t = t * r := mem_centralizer_singleton_iff.1 (hRC hr)
      have key : b * r * b⁻¹ * (b * t * b⁻¹) = (b * t * b⁻¹) * (b * r * b⁻¹) := by
        calc b * r * b⁻¹ * (b * t * b⁻¹) = b * (r * t) * b⁻¹ := by group
          _ = b * (t * r) * b⁻¹ := by rw [hrt]
          _ = (b * t * b⁻¹) * (b * r * b⁻¹) := by group
      rw [← htb] at key
      exact key
    have hyN : b * r * b⁻¹ ∈ normalizer (W₁ : Set G) := hMN hyM
    have hyV : b * r * b⁻¹ ∈ normalizer (modelToG e (pointRadical (K := K) c) : Set G) := by
      rw [← hW₁t, mem_normalizer_iff]
      intro v
      constructor
      · intro hv
        obtain ⟨hvW, hvC⟩ := mem_inf.1 hv
        exact mem_inf.2 ⟨(mem_normalizer_iff.1 hyN v).1 hvW,
          mul_mem (mul_mem hyC hvC) (inv_mem hyC)⟩
      · intro hv
        obtain ⟨hvW, hvC⟩ := mem_inf.1 hv
        refine mem_inf.2 ⟨(mem_normalizer_iff.1 hyN v).2 hvW, ?_⟩
        have h1 : v = (b * r * b⁻¹)⁻¹ * ((b * r * b⁻¹) * v * (b * r * b⁻¹)⁻¹) *
            (b * r * b⁻¹) := by group
        rw [h1]
        exact mul_mem (mul_mem (inv_mem hyC) hvC) hyC
    have h1 := hA8 (mem_inf.2 ⟨hyV, hyC⟩)
    exact (sup_le (sup_le ((modelToG_le e _).trans le_sup_left)
      ((modelToG_le e _).trans le_sup_left)) le_sup_right) h1
  have h2 := hmax11 P (hRp.map _) hPL
  rw [hPc] at h2
  norm_num at h2

end CFSG.SeitzReduction.LinearPilot
