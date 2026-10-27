module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveNSplit
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveNSylow
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveNCount
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveNIdent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveESwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGSchur

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift)

section Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_sup_zpowers_eq_two_of_not_mem {W : Subgroup G} {t : G} (htW : t ∉ W)
    (htN : t ∈ normalizer (W : Set G)) (htt : t * t = 1) :
    W.relIndex (W ⊔ zpowers t) = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨t, mem_sup_right (mem_zpowers t), fun b hb => ?_⟩
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers htt htN hb with h | h
  · refine Or.inr ⟨h, fun h' => htW ?_⟩
    have h1 : b⁻¹ * (b * t) = t := by group
    rw [← h1]
    exact mul_mem (inv_mem h) h'
  · refine Or.inl ⟨h, fun h' => htW ?_⟩
    have h1 : b⁻¹ * (b * t) = t := by group
    rw [← h1]
    exact mul_mem (inv_mem h') h

theorem false_of_conj_of_preimage {W : Subgroup G} (hW2 : ∀ w ∈ W, w * w = 1)
    (hWc : Nat.card W = 2 ^ 8)
    {R : Subgroup (seitzBar W)} (hR : IsPGroup 2 R) {t x g : G}
    (hxN : x ∈ normalizer (W : Set G)) (hxg : x = g⁻¹ * t * g) (hx : x * x = 1)
    (hRx : ∀ r ∈ R, r * QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨x, hxN⟩ =
      QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨x, hxN⟩ * r)
    {a : ℕ}
    (hcard : 2 ^ (a + 1) * Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) ≤
      2 ^ 8 * Nat.card R)
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ centralizer ({t} : Set G) →
      Nat.card Q ≤ 2 ^ a) : False := by
  set ν := QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) with hν
  set P : Subgroup G := (R.comap ν).map (normalizer (W : Set G)).subtype with hPdef
  have hWN : W ≤ normalizer (W : Set G) := le_normalizer
  have hPc : Nat.card P = 2 ^ 8 * Nat.card R := by
    rw [hPdef, card_map_of_injective (normalizer (W : Set G)).subtype_injective, hν,
      card_comap_mk_eq_mul, Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv, hWc]
  have hP : IsPGroup 2 P := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hR
    exact IsPGroup.of_card (n := 8 + m) (by rw [hPc, hm, pow_add])
  have hPW : ∀ y ∈ P, y * x * y⁻¹ * x⁻¹ ∈ W := by
    rintro _ ⟨y, hy, rfl⟩
    have hc : ν y * ν ⟨x, hxN⟩ = ν ⟨x, hxN⟩ * ν y := hRx _ (mem_comap.1 hy)
    have h1 : ν (y * ⟨x, hxN⟩ * y⁻¹ * (⟨x, hxN⟩ : normalizer (W : Set G))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    simpa using h1
  exact false_of_conj_of_card_le hW2 hxg hx hP hPW (hcard.trans hPc.symm.le) hmax

end Generic

section Inner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldTypeAtNOne_of_inner
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hinner : ∀ g ∈ centralizer ({t} : Set G), ∃ l ∈ L, ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    (hfield : LinearTwoFieldTypeAtNOne e t c W₁ htN) : False := by
  set N := normalizer (W₁ : Set G) with hNdef
  set ν := QuotientGroup.mk' (W₁.subgroupOf N) with hν
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  set V₁ := modelToG e (pointRadical (K := K) c) with hV₁
  set s := ν ⟨t, htN⟩ with hsdef
  set Lb := (L₁.subgroupOf N).map ν with hLbdef
  have hG : IsSimpleGroup G := hset.1
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hle := centralizer_le_sup_zpowers_of_inner hKt hinner
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l hl)
  have htL : t ∉ L := by
    intro h
    have h1 : t ∈ L ⊓ zpowers t := mem_inf.2 ⟨h, mem_zpowers t⟩
    rw [inf_zpowers_eq_bot hset.center_eq_bot htC ht, mem_bot] at h1
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)
  have hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P ≤ 2 ^ 11 := fun P hP hPt =>
    card_le_of_isPGroup_of_le_centralizer hset hK e ht htC hle hP hPt
  obtain ⟨hLq, hLZ, -, -, hLs⟩ := leviBar_facts e hK htC hW₁c hLN htN
  have hs : orderOf s = 2 := orderOf_mk_wOne_eq_two e hK ht hW₁c hW₁2 hW₁t htN
  have hCs := centralizer_bar_le_sup e hK ht hW₁c hW₁2 hW₁t htN hLN
    (lFiveNormalizerPointRadicalInput G L hset K hK e t ht hKt c)
  have hLp : ⁅Lb, Lb⁆ = Lb := isPerfect_iff.mp ⟨hLq.1⟩
  obtain ⟨Kc, hKc, hLKc, -, hsKc, -, hmodel, hsN, hout⟩ := hfield
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
  obtain ⟨hR12, hinv, hLang⟩ :=
    facts_of_lieModel_four_four hK hs hLs hLq hLZ hCs hsNs hsKs hLK hKsm φ hφ
  set Nt : Subgroup G := (Ks.comap ν).map N.subtype with hNtdef
  have hmemNt : ∀ (g : G) (hg : g ∈ N), ν ⟨g, hg⟩ ∈ Ks → g ∈ Nt := fun g hg h =>
    ⟨⟨g, hg⟩, h, rfl⟩
  have hNtmem : ∀ g ∈ Nt, ∃ hg : g ∈ N, ν ⟨g, hg⟩ ∈ Ks := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  have hNtN : Nt ≤ N := map_subtype_le _
  have hW₁Nt : W₁ ≤ Nt := fun w hw => hmemNt w (le_normalizer hw) (by
    have h1 : ν ⟨w, le_normalizer hw⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hw)
    rw [h1]
    exact one_mem _)
  have hL₁Nt : L₁ ≤ Nt := fun l hl =>
    hmemNt l (hLN hl) (hLK ⟨⟨l, hLN hl⟩, mem_subgroupOf.2 hl, rfl⟩)
  have hV₁W : V₁ ≤ W₁ := fun v hv => by
    have h : v ∈ W₁ ⊓ centralizer ({t} : Set G) := by rw [hW₁t]; exact hv
    exact (mem_inf.1 h).1
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
  have hconj : ∀ g : G, g⁻¹ * t * g ∉ Nt := by
    intro g hxNt
    have hx2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
      calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [ht2]; group
    obtain ⟨hxN, hxK⟩ := hNtmem _ hxNt
    by_cases hx1 : ν ⟨g⁻¹ * t * g, hxN⟩ = 1
    ·
      obtain ⟨R, -, hR2, hRc⟩ := hR12
      refine false_of_conj_of_preimage hW₁2 hW₁c hR2 hxN rfl hx2
        (fun r _ => by rw [hx1, mul_one, one_mul]) (a := 11) ?_ hmax
      calc 2 ^ (11 + 1) * Nat.card (W₁ ⊓ centralizer ({g⁻¹ * t * g} : Set G) : Subgroup G) ≤
            2 ^ 12 * 2 ^ 8 :=
          Nat.mul_le_mul_left _ (hW₁c ▸ Subgroup.card_le_of_le inf_le_left)
        _ = 2 ^ 8 * Nat.card R := by rw [hRc]; ring
    ·
      have hxb2 : ν ⟨g⁻¹ * t * g, hxN⟩ * ν ⟨g⁻¹ * t * g, hxN⟩ = 1 := by
        rw [← map_mul]
        have h1 : (⟨g⁻¹ * t * g, hxN⟩ : N) * ⟨g⁻¹ * t * g, hxN⟩ = 1 := Subtype.ext hx2
        rw [h1, map_one]
      obtain ⟨k, hkK, hkL, R, -, hRC, hR2, hRc⟩ := hinv _ hxK hxb2 hx1
      obtain ⟨κ, hκ⟩ := QuotientGroup.mk'_surjective (W₁.subgroupOf N) k
      have hx'N : (κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹ ∈ N :=
        mul_mem (mul_mem κ.2 hxN) (inv_mem κ.2)
      have hνx' : ν ⟨(κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹, hx'N⟩ =
          k * ν ⟨g⁻¹ * t * g, hxN⟩ * k⁻¹ := by
        have h1 : (⟨(κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹, hx'N⟩ : N) =
            κ * ⟨g⁻¹ * t * g, hxN⟩ * κ⁻¹ := Subtype.ext rfl
        rw [h1, map_mul, map_mul, map_inv]
        exact congrArg (fun z => z * ν ⟨g⁻¹ * t * g, hxN⟩ * z⁻¹) hκ
      obtain ⟨l', hl', hl'eq⟩ := hkL
      have hlL₁ : (l' : G) ∈ L₁ := mem_subgroupOf.1 hl'
      have hw₀ : (l' : G)⁻¹ * ((κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹) ∈ W₁ := by
        have h1 : ν (l'⁻¹ * ⟨(κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹, hx'N⟩) = 1 := by
          rw [map_mul, map_inv, hl'eq, hνx', inv_mul_cancel]
        rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
        simpa using h1
      have hl1 : (l' : G) ≠ 1 := by
        intro h1
        apply hx1
        have h2 : l' = 1 := Subtype.ext h1
        rw [h2, map_one] at hl'eq
        have h3 : ν ⟨g⁻¹ * t * g, hxN⟩ = k⁻¹ * (k * ν ⟨g⁻¹ * t * g, hxN⟩ * k⁻¹) * k := by group
        rw [h3, ← hl'eq]
        group
      have hlt : (l' : G) * t = t * l' := (mem_centralizer_iff.1 htC) _ (modelToG_le e _ hlL₁)
      have hCV : Nat.card (V₁ ⊓ centralizer ({(l' : G)} : Set G) : Subgroup G) ≤ 2 ^ 3 := by
        refine card_le_of_le_of_ne_of_card_eq_two_pow inf_le_left ?_
          (card_modelToG_pointRadical hK e c)
        intro heq
        apply hl1
        obtain ⟨a, ha, hal⟩ := (mem_modelToG e).1 hlL₁
        have ha1 : a = 1 := by
          refine eq_one_of_mem_blockSL_of_forall_conj_pointRadical hK c ha fun v hv => ?_
          have hv' : ((e.symm v : L) : G) ∈ V₁ ⊓ centralizer ({(l' : G)} : Set G) := by
            rw [heq]
            exact symm_mem_modelToG e hv
          have hc := mem_centralizer_singleton_iff.1 (mem_inf.1 hv').2
          rw [← hal] at hc
          have hc' : e.symm v * e.symm a = e.symm a * e.symm v := Subtype.ext hc
          have hc'' := congrArg e hc'
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hc''
          rw [← hc'']
          group
        rw [← hal, ha1, map_one]
        rfl
      have hCW : Nat.card (W₁ ⊓ centralizer
          ({(κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹} : Set G) : Subgroup G) ≤ 2 ^ 6 := by
        have h1 : W₁ ⊓ centralizer ({(κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹} : Set G) ≤
            W₁ ⊓ centralizer ({(l' : G)} : Set G) := by
          intro w hw
          obtain ⟨hwW, hwx⟩ := mem_inf.1 hw
          refine mem_inf.2 ⟨hwW, mem_centralizer_singleton_iff.2 ?_⟩
          have hwx' := mem_centralizer_singleton_iff.1 hwx
          set w₀ := (l' : G)⁻¹ * ((κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹) with hw₀def
          have hx'eq : (κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹ = l' * w₀ := by rw [hw₀def]; group
          have hww₀ : w * w₀ = w₀ * w := by
            have h2 := hW₁2 (w * w₀) (mul_mem hwW hw₀)
            have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hW₁2 w hwW)
            have hw₀i : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right (hW₁2 w₀ hw₀)
            calc w * w₀ = (w * w₀)⁻¹ := (inv_eq_of_mul_eq_one_right h2).symm
              _ = w₀ * w := by rw [mul_inv_rev, hwi, hw₀i]
          rw [hx'eq] at hwx'
          have h3 : w * l' * w₀ = l' * w * w₀ := by
            calc w * l' * w₀ = w * (l' * w₀) := by group
              _ = l' * w₀ * w := hwx'
              _ = l' * (w₀ * w) := by group
              _ = l' * (w * w₀) := by rw [hww₀]
              _ = l' * w * w₀ := by group
          exact mul_right_cancel h3
        have h2 := card_inf_centralizer_le_sq_of_exponent_two hW₁2 ht2 htN hlt
        rw [hW₁t] at h2
        calc Nat.card (W₁ ⊓ centralizer
              ({(κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹} : Set G) : Subgroup G) ≤
            Nat.card (W₁ ⊓ centralizer ({(l' : G)} : Set G) : Subgroup G) :=
              Subgroup.card_le_of_le h1
          _ ≤ (2 ^ 3) ^ 2 := h2.trans (Nat.pow_le_pow_left hCV 2)
          _ = 2 ^ 6 := by norm_num
      refine false_of_conj_of_preimage hW₁2 hW₁c hR2 hx'N (g := g * (κ : G)⁻¹) (by group) ?_
        (fun r hr => by rw [hνx']; exact mem_centralizer_singleton_iff.1 (hRC hr)) (a := 11)
        ?_ hmax
      · calc (κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹ * ((κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹) =
              (κ : G) * (g⁻¹ * t * g * (g⁻¹ * t * g)) * (κ : G)⁻¹ := by group
          _ = 1 := by rw [hx2]; group
      · calc 2 ^ (11 + 1) * Nat.card (W₁ ⊓ centralizer
              ({(κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹} : Set G) : Subgroup G) ≤ 2 ^ 12 * 2 ^ 6 :=
            Nat.mul_le_mul_left _ hCW
          _ = 2 ^ 8 * 2 ^ 10 := by norm_num
          _ ≤ 2 ^ 8 * Nat.card R := Nat.mul_le_mul_left _ hRc
  set M := Nt ⊔ zpowers t with hMdef
  have hMN : M ≤ N := sup_le hNtN ((zpowers_le).2 htN)
  have hsurj := tcomm_surjective_of_card hW₁2 ht2 htN
    (by rw [hW₁c, card_wOne_inf_centralizer e hK hW₁t]; norm_num)
  have hfus : ∀ g : G, g * t * g⁻¹ ∈ M → ∃ m ∈ M, g * t * g⁻¹ = m * t * m⁻¹ := by
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
  obtain ⟨Q₀, hQ₀le, hQ₀c⟩ := exists_two_subgroup_le_pointRadical_sup_levi (G := G) hK e c
  have hQ₀L : Q₀ ≤ L := hQ₀le.trans (sup_le (modelToG_le e _) (modelToG_le e _))
  have hQ₀Nt : Q₀ ≤ Nt := hQ₀le.trans (sup_le (hV₁W.trans hW₁Nt) hL₁Nt)
  have hzQ₀ : zpowers t ≤ centralizer (Q₀ : Set G) :=
    (zpowers_le).2 (Subgroup.centralizer_le hQ₀L htC)
  have hQ₀t : Q₀ ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff, ← inf_zpowers_eq_bot hset.center_eq_bot htC ht]
    exact inf_le_inf_right _ hQ₀L
  set Q := Q₀ ⊔ zpowers t with hQdef
  have hQc : Nat.card Q = 2 ^ 11 := by
    rw [hQdef, card_sup_eq_mul_of_le_centralizer_of_inf_eq_bot hzQ₀ hQ₀t, hQ₀c, Nat.card_zpowers,
      ht]
    norm_num
  have hQ : IsPGroup 2 Q := IsPGroup.of_card hQc
  have htQ : t ∈ Q := mem_sup_right (mem_zpowers t)
  have hQt : Q ≤ centralizer ({t} : Set G) := sup_le (hQ₀L.trans hLt)
    ((zpowers_le).2 (mem_centralizer_singleton_iff.2 rfl))
  have hQM : Q ≤ M := sup_le (hQ₀Nt.trans le_sup_left) le_sup_right
  have hQmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P ≤ Nat.card Q := fun P hP hPt => hQc ▸ hmax P hP hPt
  have htNQ₀ : t ∈ normalizer (Q₀ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (hzQ₀ (mem_zpowers t))
  have hQL : ∀ x ∈ Q, x ∈ L → x ∈ Q₀ := by
    intro x hxQ hxL
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htNQ₀ hxQ with h | h
    · exact h
    · exfalso
      apply htL
      have h1 : x⁻¹ * (x * t) = t := by group
      rw [← h1]
      exact mul_mem (inv_mem hxL) (hQ₀L h)
  have htNL : t ∈ normalizer (L : Set G) := cKind_mem_normalizer hLt
  have hNQ : ∀ y ∈ centralizer ({t} : Set G), y ∈ normalizer (Q : Set G) → y ∈ M := by
    intro y hyC hyN
    have hlNQ : ∀ l ∈ L, l ∈ normalizer (Q : Set G) → l ∈ Q₀ := by
      intro l hl hlN
      refine mem_of_mem_normalizer_of_card_eq hK e hQ₀L hQ₀c hl ?_
      rw [mem_normalizer_iff]
      intro q
      constructor
      · intro hq
        exact hQL _ ((mem_normalizer_iff.1 hlN q).1 (mem_sup_left hq))
          (mul_mem (mul_mem hl (hQ₀L hq)) (inv_mem hl))
      · intro hq
        have hqQ : q ∈ Q := (mem_normalizer_iff.1 hlN q).2 (mem_sup_left hq)
        have hqL : q ∈ L := by
          have h1 : l⁻¹ * (l * q * l⁻¹) * l = q := by group
          rw [← h1]
          exact mul_mem (mul_mem (inv_mem hl) (hQ₀L hq)) hl
        exact hQL q hqQ hqL
    have htNQ : t ∈ normalizer (Q : Set G) := le_normalizer htQ
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htNL (hle hyC) with h | h
    · exact hQM (mem_sup_left (hlNQ y h hyN))
    · have h1 := hQM (mem_sup_left (hlNQ _ h (mul_mem hyN htNQ)))
      have h2 : y = y * t * t⁻¹ := by group
      rw [h2]
      exact mul_mem h1 (inv_mem (mem_sup_right (mem_zpowers t)))
  have hG2 : 2 < Nat.card G := by
    have h1 := Subgroup.card_le_card_group L
    rw [Nat.card_congr e.toEquiv, card_projectiveSL_five_of_card_two hK] at h1
    omega
  exact false_of_simple_of_fusion_control hG2
    (relIndex_sup_zpowers_eq_two_of_not_mem htNt htNNt ht2) (mem_sup_right (mem_zpowers t)) htNt
    ht hconj htQ hQ hQt hQM hQmax hfus hNQ

end Inner

theorem lFiveFieldNOneInnerInput :
    LFiveFieldNOneInnerInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hinner c W₁ hW₁c hW₁2 hW₁t htN hLN hfield
  exact false_of_fieldTypeAtNOne_of_inner hset hK e ht hKt hinner c hW₁c hW₁2 hW₁t htN hLN hfield

theorem lFiveFieldNOneInput_of_graph
    (hG : LFiveFieldNOneGraphInput) : LFiveFieldNOneInput :=
  lFiveFieldNOneInput_of_inner_of_graph lFiveFieldNOneInnerInput hG

end CFSG.SeitzReduction.LinearPilot
