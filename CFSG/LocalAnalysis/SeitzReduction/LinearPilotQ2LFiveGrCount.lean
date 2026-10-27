module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGrIdent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveNInner

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift)

section Generic

variable {X : Type} [Group X]

theorem card_sup_zpowers_eq_two_mul {R : Subgroup X} {s : X} (hsR : s ∉ R)
    (hsN : s ∈ normalizer (R : Set X)) (hss : s * s = 1) :
    Nat.card (R ⊔ zpowers s : Subgroup X) = 2 * Nat.card R := by
  have h := Subgroup.relIndex_mul_card (H := R) (K := R ⊔ zpowers s)
  rw [relIndex_sup_zpowers_eq_two_of_not_mem hsR hsN hss, inf_of_le_left le_sup_left] at h
  exact h.symm

theorem isPGroup_sup_zpowers {R : Subgroup X} (hR : IsPGroup 2 R) [Finite R] {s : X}
    (hsR : s ∉ R) (hsN : s ∈ normalizer (R : Set X)) (hss : s * s = 1) :
    IsPGroup 2 (R ⊔ zpowers s : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hR
  exact IsPGroup.of_card (n := m + 1) (by
    rw [card_sup_zpowers_eq_two_mul hsR hsN hss, hm, pow_succ, mul_comm])

end Generic

section CentOrder

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_GL_five_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card (GL (Fin 5) K) = 9999360 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  classical
  rw [Matrix.card_GL_field, hq]
  decide

theorem card_le_two_pow_twelve_of_isPGroup_of_le_centralizer (hset : SeitzSetting G L)
    {K : Type} [Field K] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPt : P ≤ centralizer ({t} : Set G)) :
    Nat.card P ≤ 2 ^ 12 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have h1 := card_centralizer_dvd_two_mul_card_mulAut hset.2.2.2.1 e ht hKt
  have h2 := card_mulAut_projectiveSL_dvd (n := 5) (K := K) (by norm_num) (f := 1)
    (by rw [pow_one]; exact hK)
  rw [card_GL_five_of_card_two hK] at h2
  have hdvd : Nat.card P ∣ 2 ^ 12 * 9765 := by
    refine (Subgroup.card_dvd_of_le hPt).trans (h1.trans ?_)
    have h3 : 2 * (2 * 1 * 9999360) = 2 ^ 12 * 9765 := by norm_num
    rw [← h3]
    exact Nat.mul_dvd_mul_left 2 h2
  exact card_le_two_pow_of_isPGroup_of_dvd hP (by decide) hdvd

end CentOrder

section Tilde

variable {G : Type} [Group G]

@[expose] def IsFieldTypeComponentAtNOne {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (c : Fin n) (W₁ : Subgroup G)
    (htN : t ∈ normalizer (W₁ : Set G)) (Kc : Subgroup (seitzHat W₁)) : Prop :=
  IsComponent Kc ∧ seitzLeviHat e c W₁ < Kc ∧
    Kc.map (MulAut.conj (seitzHatMap W₁ ⟨t, htN⟩)).toMonoidHom = Kc ∧
    seitzHatMap W₁ ⟨t, htN⟩ ∉ Kc ∧ center Kc = ⊥ ∧ LieModel Kc .PSL (n - 1) 2 2 ∧
    ∃ hsN : seitzHatMap W₁ ⟨t, htN⟩ ∈ normalizer (Kc : Set (seitzHat W₁)),
      Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range

theorem linearTwoFieldTypeAtNOne_iff {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (c : Fin n) (W₁ : Subgroup G)
    (htN : t ∈ normalizer (W₁ : Set G)) :
    LinearTwoFieldTypeAtNOne e t c W₁ htN ↔
      ∃ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc :=
  Iff.rfl

@[expose] noncomputable def seitzTilde (W : Subgroup G) (Kc : Subgroup (seitzHat W)) :
    Subgroup G :=
  ((oddCoreLift Kc).comap (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))))).map
    (normalizer (W : Set G)).subtype

theorem mem_seitzTilde_iff {W : Subgroup G} {Kc : Subgroup (seitzHat W)} {g : G} :
    g ∈ seitzTilde W Kc ↔ ∃ hg : g ∈ normalizer (W : Set G),
      QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨g, hg⟩ ∈ oddCoreLift Kc := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem seitzTilde_le_normalizer (W : Subgroup G) (Kc : Subgroup (seitzHat W)) :
    seitzTilde W Kc ≤ normalizer (W : Set G) :=
  map_subtype_le _

end Tilde

section Count

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_conj_mem_seitzTilde
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc)
    (g : G) : g⁻¹ * t * g ∉ seitzTilde W₁ Kc := by
  set N := normalizer (W₁ : Set G) with hNdef
  set ν := QuotientGroup.mk' (W₁.subgroupOf N) with hν
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  set V₁ := modelToG e (pointRadical (K := K) c) with hV₁
  set s := ν ⟨t, htN⟩ with hsdef
  set Lb := (L₁.subgroupOf N).map ν with hLbdef
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P ≤ 2 ^ 12 := fun P hP hPt =>
    card_le_two_pow_twelve_of_isPGroup_of_le_centralizer hset hK e ht hKt hP hPt
  obtain ⟨hLq, hLZ, -, -, hLs⟩ := leviBar_facts e hK htC hW₁c hLN htN
  have hs : orderOf s = 2 := orderOf_mk_wOne_eq_two e hK ht hW₁c hW₁2 hW₁t htN
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
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
  obtain ⟨hR12, hinv⟩ :=
    facts_of_lieModel_four_four_of_fieldAut hK hs hLs hLq hLZ hCs hsNs hsKs hLK hKsm φ hφ
  intro hxNt
  have hx2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨hxN, hxK⟩ := mem_seitzTilde_iff.1 hxNt
  by_cases hx1 : ν ⟨g⁻¹ * t * g, hxN⟩ = 1
  ·
    obtain ⟨R, hRK, hR2, hRc, hsR⟩ := hR12
    have hsR' : s ∉ R := fun h => hsKs (hRK h)
    have hR'c := card_sup_zpowers_eq_two_mul hsR' hsR hs2
    refine false_of_conj_of_preimage hW₁2 hW₁c (isPGroup_sup_zpowers hR2 hsR' hsR hs2) hxN rfl
      hx2 (fun r _ => by rw [hx1, mul_one, one_mul]) (a := 12) ?_ hmax
    calc 2 ^ (12 + 1) * Nat.card (W₁ ⊓ centralizer ({g⁻¹ * t * g} : Set G) : Subgroup G) ≤
          2 ^ 13 * 2 ^ 8 :=
        Nat.mul_le_mul_left _ (hW₁c ▸ Subgroup.card_le_of_le inf_le_left)
      _ = 2 ^ 8 * Nat.card (R ⊔ zpowers s : Subgroup (seitzBar W₁)) := by rw [hR'c, hRc]; ring
  ·
    have hxb2 : ν ⟨g⁻¹ * t * g, hxN⟩ * ν ⟨g⁻¹ * t * g, hxN⟩ = 1 := by
      rw [← map_mul]
      have h1 : (⟨g⁻¹ * t * g, hxN⟩ : N) * ⟨g⁻¹ * t * g, hxN⟩ = 1 := Subtype.ext hx2
      rw [h1, map_one]
    obtain ⟨k, -, hkL, R, hRK, hRC, hR2, hRc, hsR⟩ := hinv _ hxK hxb2 hx1
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk'_surjective (W₁.subgroupOf N) k
    have hx'N : (κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹ ∈ N :=
      mul_mem (mul_mem κ.2 hxN) (inv_mem κ.2)
    have hνx' : ν ⟨(κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹, hx'N⟩ =
        k * ν ⟨g⁻¹ * t * g, hxN⟩ * k⁻¹ := by
      have h1 : (⟨(κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹, hx'N⟩ : N) =
          κ * ⟨g⁻¹ * t * g, hxN⟩ * κ⁻¹ := Subtype.ext rfl
      rw [h1, map_mul, map_mul, map_inv]
      exact congrArg (fun z => z * ν ⟨g⁻¹ * t * g, hxN⟩ * z⁻¹) hκ
    have hsx : s ∈ centralizer ({k * ν ⟨g⁻¹ * t * g, hxN⟩ * k⁻¹} : Set (seitzBar W₁)) :=
      mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (hLs hkL)).symm
    have hR'C : R ⊔ zpowers s ≤
        centralizer ({k * ν ⟨g⁻¹ * t * g, hxN⟩ * k⁻¹} : Set (seitzBar W₁)) :=
      sup_le hRC ((zpowers_le).2 hsx)
    have hsR' : s ∉ R := fun h => hsKs (hRK h)
    have hR'c := card_sup_zpowers_eq_two_mul hsR' hsR hs2
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
    refine false_of_conj_of_preimage hW₁2 hW₁c (isPGroup_sup_zpowers hR2 hsR' hsR hs2) hx'N
      (g := g * (κ : G)⁻¹) (by group) ?_
      (fun r hr => by rw [hνx']; exact mem_centralizer_singleton_iff.1 (hR'C hr)) (a := 12)
      ?_ hmax
    · calc (κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹ * ((κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹) =
            (κ : G) * (g⁻¹ * t * g * (g⁻¹ * t * g)) * (κ : G)⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    · calc 2 ^ (12 + 1) * Nat.card (W₁ ⊓ centralizer
            ({(κ : G) * (g⁻¹ * t * g) * (κ : G)⁻¹} : Set G) : Subgroup G) ≤ 2 ^ 13 * 2 ^ 6 :=
          Nat.mul_le_mul_left _ hCW
        _ = 2 ^ 8 * (2 * 2 ^ 10) := by norm_num
        _ ≤ 2 ^ 8 * Nat.card (R ⊔ zpowers s : Subgroup (seitzBar W₁)) := by
          rw [hR'c]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hRc)

end Count

end CFSG.SeitzReduction.LinearPilot
