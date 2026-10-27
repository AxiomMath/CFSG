module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseAClose
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseGen2

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open CFSG.OddStandard.Seitz77
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover (unipAll)
open CFSG.GH74.GLS.Bg.Thompson (IsExtremalIn)

theorem two_mul_lt_two_pow {f : ℕ} (hf : 3 ≤ f) : 2 * f < 2 ^ f := by
  induction f, hf using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]
    omega

theorem card_centralizer_conj_eq {G : Type} [Group G] (t x : G) :
    Nat.card ↥(centralizer ({x⁻¹ * t * x} : Set G)) = Nat.card ↥(centralizer ({t} : Set G)) := by
  have : centralizer ({x⁻¹ * t * x} : Set G) =
      (centralizer ({t} : Set G)).map (MulAut.conj x⁻¹).toMonoidHom := by
    ext z
    rw [mem_map_conj_iff, inv_inv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hz
      calc x * z * x⁻¹ * t = x * (z * (x⁻¹ * t * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * t * x) * z) * x⁻¹ := by rw [hz]
        _ = t * (x * z * x⁻¹) := by group
    · intro hz
      calc z * (x⁻¹ * t * x) = x⁻¹ * (x * z * x⁻¹ * t) * x := by group
        _ = x⁻¹ * (t * (x * z * x⁻¹)) * x := by rw [hz]
        _ = x⁻¹ * t * x * z := by group
  rw [this, card_map_conj]

theorem card_le_four_of_mul_self {M N : Type*} [Group M] [IsCyclic M] [Finite M] [Group N]
    [Finite N] (hN : Nat.card N = 2) (R : Subgroup (M × N)) (hR : ∀ r ∈ R, r * r = 1) :
    Nat.card R ≤ 4 := by
  have h1 : Nat.card (R.map (MonoidHom.fst M N)) ≤ 2 := by
    refine card_le_two_of_isCyclic _ ?_
    rintro _ ⟨r, hr, rfl⟩
    rw [sq, ← map_mul, hR r hr, map_one]
  have h2 : Nat.card R ≤ Nat.card ↥(R.map (MonoidHom.fst M N)) * Nat.card N := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun r => (⟨(r : M × N).1, ⟨r, r.2, rfl⟩⟩, (r : M × N).2)) ?_
    intro a b hab
    have h1 := congrArg (fun p => (p.1 : M)) hab
    have h2 := congrArg Prod.snd hab
    exact Subtype.ext (Prod.ext h1 h2)
  rw [hN] at h2
  omega

namespace CaseAData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ} {d : Datum A}
  {W : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2] (C : CaseAData d W F)

@[expose] noncomputable def χ : ↥(normalizer (C.S₀ : Set G)) →* RingAut F × Multiplicative (ZMod 2) :=
  (unipFieldHom.prod unipSwapHom).comp C.ρ

omit [Finite G] [Finite F] in
theorem χ_apply (x : ↥(normalizer (C.S₀ : Set G))) :
    C.χ x = (autField (C.ρ x), unipSwapHom (C.ρ x)) := rfl

theorem card_le_card_inf_mul (hψt : autField (C.ρ C.tN) ≠ 1) {T : Subgroup G}
    (hT : IsPGroup 2 T) (hST : C.S₁ ≤ T) (hTN : T ≤ normalizer (C.S₀ : Set G)) {H : Subgroup G}
    (hHT : H ≤ T) :
    Nat.card H ≤ Nat.card ↥(H ⊓ C.S₀) * Nat.card (C.χ.comp (inclusion (hHT.trans hTN))).range := by
  set χH := C.χ.comp (inclusion (hHT.trans hTN)) with hχH
  have hcard := Subgroup.card_ker_mul_card_range χH
  have hker : Nat.card χH.ker ≤ Nat.card ↥(H ⊓ C.S₀) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨((x : H) : G), (x : H).2, ?_⟩ : ↥(H ⊓ C.S₀))) ?_
    · obtain ⟨⟨x, hxH⟩, hxk⟩ := x
      have h1 := MonoidHom.mem_ker.1 hxk
      rw [hχH, MonoidHom.comp_apply, χ_apply, Prod.mk_eq_one] at h1
      exact (C.mem_S₀_iff hψt hT hST ⟨x, hTN (hHT hxH)⟩ (hHT hxH)).2
        ⟨h1.1, (unipSwapHom_eq_one_iff _).1 h1.2⟩
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
  rw [← hcard]
  exact Nat.mul_le_mul_right _ hker

theorem false_of_le_normalizer [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hf3 : 3 ≤ f) (hF' : FusionFacts A (2 ^ f)) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hsyl : ∀ Vj : Subgroup G, (Vj = V₁ ∨ Vj = V₂) →
      IsSylowOf 2 (Vj ⊔ zpowers d.t) (centralizer ((Vj ⊔ zpowers d.t : Subgroup G) : Set G)))
    (hW : Vi = V₁ ∨ Vi = V₂) (hWe : IsElemAbelian 2 W) (hWc : Nat.card W = (2 ^ f) ^ 4)
    (hcomm : ∀ v ∈ Vi, ∃ x ∈ W, d.t * x * d.t * x⁻¹ = v)
    (hF : Nat.card F = (2 ^ f) ^ 2) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hST : C.S₁ ≤ T) (hTN : T ≤ normalizer (C.S₀ : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := SylowSetting.of_datum d
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hψt := C.autField_ρ_t_ne_one hq2 hR hW hcomm
  have hF2 : Nat.card F = 2 ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
  obtain ⟨hcyc, hcardAut⟩ := ringAut_isCyclic_and_card (F := F) (n := 2 * f) (by omega) hF2
  have : Finite (RingAut F) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  let ψT : ↥T →* RingAut F := unipFieldHom.comp (C.ρ.comp (inclusion hTN))
  have htT : d.t ∈ T := hST C.t_mem_S₁
  obtain ⟨g, hgT, hψg, hext⟩ := exists_extremal_conj_mem_ker hnonab hT hTidx ψT htT
    d.t_mul_self hψt
  set y := g⁻¹ * d.t * g with hy
  have hy2 : y * y = 1 := by
    rw [hy]
    calc g⁻¹ * d.t * g * (g⁻¹ * d.t * g) = g⁻¹ * (d.t * d.t) * g := by group
      _ = 1 := by rw [d.t_mul_self]; group
  have hyconj : IsConj d.t y := isConj_iff.mpr ⟨g⁻¹, by rw [hy, inv_inv]⟩
  have hyS : y ∉ C.S₀ := fun hmem =>
    C.not_conj_mem_S₀ hf3 hF' hR hsyl hWc hWe hF hmem hy2 hyconj
  set yN : ↥(normalizer (C.S₀ : Set G)) := ⟨y, hTN hgT⟩ with hyN
  have hyψ : autField (C.ρ yN) = 1 := hψg
  have hysw : autSwap (C.ρ yN) = true := by
    by_contra hne
    have hfalse : autSwap (C.ρ yN) = false := by simpa using hne
    exact hyS ((C.mem_S₀_iff hψt hT hST yN hgT).2 ⟨hyψ, hfalse⟩)
  have hα2 : ∀ u, C.ρ yN (C.ρ yN u) = u := by
    intro u
    have hyN2 : yN * yN = 1 := Subtype.ext hy2
    have : C.ρ yN * C.ρ yN = 1 := by rw [← map_mul, hyN2, map_one]
    exact DFunLike.congr_fun this u
  have hfix := card_fix_le_of_swap (C.ρ yN) hα2 hysw hyψ
  have hCS : Nat.card ↥(C.S₀ ⊓ centralizer ({y} : Set G)) ≤ Nat.card F := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun s => (⟨C.e ⟨s.1, s.2.1⟩, ?_⟩ : ↥(fixSubgroup (C.ρ yN)))) ?_) hfix
    · show C.ρ yN (C.e ⟨s.1, s.2.1⟩) = C.e ⟨s.1, s.2.1⟩
      rw [C.ρ_apply]
      congr 1
      refine Subtype.ext ?_
      show y * s.1 * y⁻¹ = s.1
      rw [mul_inv_eq_iff_eq_mul]
      exact (mem_centralizer_singleton_iff.mp s.2.2).symm
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      have h2 := C.e.injective h1
      have h3 := congrArg Subtype.val h2
      exact Subtype.ext h3
  have hKT : T ⊓ centralizer ({y} : Set G) ≤ T := inf_le_left
  have hK := C.card_le_card_inf_mul hψt hT hST hTN hKT
  have hKS : T ⊓ centralizer ({y} : Set G) ⊓ C.S₀ ≤ C.S₀ ⊓ centralizer ({y} : Set G) :=
    fun x hx => ⟨hx.2, hx.1.2⟩
  have hrange : Nat.card (C.χ.comp (inclusion (hKT.trans hTN))).range ≤ 2 * f * 2 := by
    calc _ ≤ Nat.card (RingAut F × Multiplicative (ZMod 2)) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 2 * f * 2 := by
          rw [Nat.card_prod, hcardAut, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hCT : Nat.card ↥(T ⊓ centralizer ({y} : Set G)) ≤ (2 ^ f) ^ 2 * (2 * f * 2) :=
    hK.trans (Nat.mul_le_mul ((Subgroup.card_le_of_le hKS).trans (hCS.trans hF.le)) hrange)
  have hsyl : IsSylowOf 2 (T ⊓ centralizer ({y} : Set G)) (centralizer ({y} : Set G)) :=
    isSylowOf_iff.2 hext
  have hcardP : Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = Nat.card d.P := by
    rw [hsyl.card_eq, d.P_isSylow_centralizer.card_eq, hy, card_centralizer_conj_eq]
  have hP : 2 * (2 ^ f) ^ 3 ≤ Nat.card d.P := by
    have hVle : d.V ≤ d.P := inf_le_left
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hVle
    rw [hR.card] at hm
    have hne : d.V ≠ d.P := fun heq => by
      have : d.t ∈ d.V := heq ▸ d.t_mem_P
      exact hd.t_not_mem hF' this.2
    have hm1 : m ≠ 1 := fun h1 => hne (Subgroup.eq_of_le_of_card_ge hVle (by
      rw [hm, h1, mul_one, hR.card]))
    have hm0 : m ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hm
      exact (Nat.card_pos (α := d.P)).ne' hm
    rw [hm]
    have : 2 ≤ m := by omega
    calc 2 * (2 ^ f) ^ 3 = (2 ^ f) ^ 3 * 2 := by ring
      _ ≤ (2 ^ f) ^ 3 * m := Nat.mul_le_mul_left _ this
  have h1 : 2 * (2 ^ f) ^ 3 ≤ (2 ^ f) ^ 2 * (2 * f * 2) := hP.trans (hcardP ▸ hCT)
  have h2 : (2 ^ f) ^ 2 * (2 * 2 ^ f) ≤ (2 ^ f) ^ 2 * (2 * f * 2) := by
    have e : 2 * (2 ^ f) ^ 3 = (2 ^ f) ^ 2 * (2 * 2 ^ f) := by ring
    omega
  have h3 := Nat.le_of_mul_le_mul_left h2 (by positivity)
  have h4 := two_mul_lt_two_pow hf3
  omega

theorem card_le_of_centralizes (hψt : autField (C.ρ C.tN) ≠ 1) {T : Subgroup G}
    (hT : IsPGroup 2 T) (hST : C.S₁ ≤ T) (hTN : T ≤ normalizer (C.S₀ : Set G)) {b : G}
    (hbT : b ∈ T) (hbS : b ∉ C.S₀) {B : Subgroup G} (hBS : B ≤ C.S₀)
    (hB2 : ∀ x ∈ B, x * x = 1) (hBc : ∀ x ∈ B, b * x = x * b) : Nat.card B ≤ Nat.card F := by
  set bN : ↥(normalizer (C.S₀ : Set G)) := ⟨b, hTN hbT⟩ with hbN
  set α := C.ρ bN with hα
  have hfixB : ∀ x (hx : x ∈ B), α (C.e ⟨x, hBS hx⟩) = C.e ⟨x, hBS hx⟩ := by
    intro x hx
    rw [hα, C.ρ_apply]
    congr 1
    refine Subtype.ext ?_
    show b * x * b⁻¹ = x
    rw [hBc x hx, mul_inv_cancel_right]
  set B' : Subgroup (unipAll F) := (B.subgroupOf C.S₀).map C.e.toMonoidHom with hB'
  have hB'2 : ∀ g ∈ B', g * g = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul]
    have : s * s = 1 := Subtype.ext (hB2 _ hs)
    rw [this, map_one]
  have hcardB : Nat.card B = Nat.card B' := by
    rw [hB', Subgroup.card_map_of_injective C.e.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv).symm
  have hB'fix : B' ≤ fixSubgroup α := by
    rintro _ ⟨s, hs, rfl⟩
    exact hfixB s hs
  have key : ∀ R : Subgroup (unipAll F), B' ≤ R → Nat.card ↥(fixSubgroup α ⊓ R) ≤ Nat.card F →
      Nat.card B ≤ Nat.card F := fun R hR hfR => by
    rw [hcardB]
    exact (Subgroup.card_le_of_le (le_inf hB'fix hR)).trans hfR
  by_cases hsw : autSwap α = true
  · have hZ : ∀ R : Subgroup (unipAll F), fixSubgroup α ⊓ R ≤ radCenter F →
        Nat.card ↥(fixSubgroup α ⊓ R) ≤ Nat.card F := fun R hR =>
      (Subgroup.card_le_of_le hR).trans (card_radCenter (F := F)).le
    rcases le_radOne_or_le_radTwo B' hB'2 with hle | hle
    · exact key _ hle (hZ _ (fix_inf_radOne_le_radCenter α hsw))
    · exact key _ hle (hZ _ (fix_inf_radTwo_le_radCenter α hsw))
  · have hsw' : autSwap α = false := by simpa using hsw
    have hbS₁ : b ∈ C.S₁ :=
      C.mem_S₁_of_mem_normalizer hT hST hbT ((C.autSwap_ρ_eq_false_iff bN).1 hsw')
    have hf : autField α ≠ 1 := fun h1 => hbS (C.mem_S₀_of_autField_eq_one hψt hbS₁ h1)
    rcases le_radOne_or_le_radTwo B' hB'2 with hle | hle
    · exact key _ hle (card_fix_inf_radOne_le α hsw' hf)
    · exact key _ hle (card_fix_inf_radTwo_le α hsw' hf)

theorem le_normalizer_of_ne (hf3 : 3 ≤ f) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂) (hWe : IsElemAbelian 2 W)
    (hWc : Nat.card W = (2 ^ f) ^ 4) (hcomm : ∀ v ∈ Vi, ∃ x ∈ W, d.t * x * d.t * x⁻¹ = v)
    (hF : Nat.card F = (2 ^ f) ^ 2) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hST : C.S₁ ≤ T) (hne : C.S₁ ≠ T) : T ≤ normalizer (C.S₀ : Set G) := by
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hψt := C.autField_ρ_t_ne_one hq2 hR hW hcomm
  have hF2 : Nat.card F = 2 ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
  obtain ⟨hcyc, hcardAut⟩ := ringAut_isCyclic_and_card (F := F) (n := 2 * f) (by omega) hF2
  set q := 2 ^ f with hq
  have hq8 : 8 ≤ q := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  have hS₁N := C.S₁_le
  obtain ⟨δ, hδT, hδN, hδnot, hδsq⟩ := exists_normalizing_sq_mem hT hST hne
  set W' := W.map (MulAut.conj δ).toMonoidHom with hW'
  have hW'e : IsElemAbelian 2 W' := isElemAbelian_map_conj' hWe δ
  have hW'c : Nat.card W' = q ^ 4 := by rw [hW', card_map_conj, hWc]
  have hW'2 : ∀ x ∈ W', x * x = 1 := fun x hx => by rw [← sq]; exact hW'e.2 x hx
  have hW'S₁ : W' ≤ C.S₁ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hδN x).1 (C.S₀_le (C.W_le hx))
  have hW'ne : W' ≠ W := by
    intro heq
    apply hδnot
    refine C.mem_S₁_of_mem_normalizer hT hST hδT (Subgroup.mem_normalizer_fintype fun x hx => ?_)
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  have : IsCyclic (RingAut F) := hcyc
  have : Finite (RingAut F) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hZ2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hrange4 : ∀ (B : Subgroup G) (hBN : B ≤ normalizer (C.S₀ : Set G)),
      (∀ x ∈ B, x * x = 1) → Nat.card (C.χ.comp (inclusion hBN)).range ≤ 4 := by
    intro B hBN hB2
    refine card_le_four_of_mul_self hZ2 _ ?_
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hB2 _ x.2)
    rw [this, map_one]
  have hq4 : ¬ q ^ 4 ≤ q ^ 2 * 4 := by
    intro h1
    have h2 : q ^ 4 = q ^ 2 * q ^ 2 := by ring
    have h3 : 4 < q ^ 2 := by nlinarith
    have h4 : q ^ 2 * 4 < q ^ 2 * q ^ 2 := Nat.mul_lt_mul_of_pos_left h3 (by positivity)
    omega
  have hW'S₀ : W' ≤ C.S₀ := by
    by_contra hnot
    obtain ⟨s, hsW', hsS₀⟩ := Set.not_subset.mp hnot
    have hbound := C.card_le_of_centralizes hψt C.isPGroup_S₁ le_rfl hS₁N (hW'S₁ hsW') hsS₀
      (B := W' ⊓ C.S₀) inf_le_right (fun x hx => hW'2 x hx.1)
      (fun x hx => comm_of_isElemAbelian hW'e hsW' hx.1)
    have hcard := C.card_le_card_inf_mul hψt C.isPGroup_S₁ le_rfl hS₁N hW'S₁
    have hr := hrange4 W' (hW'S₁.trans hS₁N) hW'2
    rw [hW'c] at hcard
    exact hq4 (hcard.trans (Nat.mul_le_mul (hbound.trans hF.le) hr))
  set B' : Subgroup (unipAll F) := (W'.subgroupOf C.S₀).map C.e.toMonoidHom with hB'
  have hB'2 : ∀ g ∈ B', g * g = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul]
    have : s * s = 1 := Subtype.ext (hW'2 _ hs)
    rw [this, map_one]
  have hB'card : Nat.card B' = Nat.card F ^ 2 := by
    rw [hB', Subgroup.card_map_of_injective C.e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW'S₀).toEquiv, hW'c, hF]
    ring
  have hB'rad : B' = radTwo F := by
    rcases eq_radOne_or_radTwo_of_card hB'2 hB'card with h1 | h1
    · exfalso
      apply hW'ne
      refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [hWc, hW'c])
      have : C.e ⟨x, hW'S₀ hx⟩ ∈ B' := ⟨⟨x, hW'S₀ hx⟩, hx, rfl⟩
      rw [h1] at this
      exact (C.mem_W_iff _).2 this
    · exact h1
  have hmemW' : ∀ s : C.S₀, (s : G) ∈ W' ↔ C.e s ∈ radTwo F := by
    intro s
    rw [← hB'rad]
    constructor
    · intro hs
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s', hs', he⟩
      have h1 : s' = s := C.e.injective he
      rw [← h1]
      exact hs'
  have hδS₀ : δ ∈ normalizer (C.S₀ : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    set u := C.e ⟨s, hs⟩ with hu
    set r₁ : unipAll F := uelt (coordA u) 0 (coordC u - coordA u * coordB u) with hr₁
    set r₂ : unipAll F := uelt 0 (coordB u) 0 with hr₂
    have hr : r₁ * r₂ = u := by
      rw [hr₁, hr₂, uelt_mul]
      conv_rhs => rw [← uelt_coords u]
      congr 1 <;> ring
    have hr₁1 : r₁ ∈ radOne F := (mem_radOne _).2 (coordB_uelt _ _ _)
    have hr₂2 : r₂ ∈ radTwo F := (mem_radTwo _).2 (coordA_uelt _ _ _)
    have hs₁W : ((C.e.symm r₁ : C.S₀) : G) ∈ W := by
      rw [C.mem_W_iff, MulEquiv.apply_symm_apply]
      exact hr₁1
    have hs₂W' : ((C.e.symm r₂ : C.S₀) : G) ∈ W' := by
      rw [hmemW', MulEquiv.apply_symm_apply]
      exact hr₂2
    have hss : s = (C.e.symm r₁ : G) * (C.e.symm r₂ : G) := by
      have : (⟨s, hs⟩ : C.S₀) = C.e.symm r₁ * C.e.symm r₂ := by
        apply C.e.injective
        rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hr]
      exact congrArg Subtype.val this
    rw [hss, show δ * ((C.e.symm r₁ : G) * (C.e.symm r₂ : G)) * δ⁻¹ =
      (δ * (C.e.symm r₁ : G) * δ⁻¹) * (δ * (C.e.symm r₂ : G) * δ⁻¹) by group]
    refine C.S₀.mul_mem (hW'S₀ ⟨_, hs₁W, rfl⟩) (C.W_le ?_)
    obtain ⟨x, hx, hxe⟩ := hs₂W'
    rw [← hxe]
    show δ * (δ * x * δ⁻¹) * δ⁻¹ ∈ W
    rw [show δ * (δ * x * δ⁻¹) * δ⁻¹ = (δ * δ) * x * (δ * δ)⁻¹ by group]
    exact (mem_normalizer_iff.1 (C.S₁_le_normalizer hδsq) x).1 hx
  set Sh := extByElt C.S₁ δ hδN hδsq with hSh
  have hmemSh : ∀ x, x ∈ Sh ↔ x ∈ C.S₁ ∨ δ⁻¹ * x ∈ C.S₁ := fun x => mem_extByElt_iff
  have hS₁Sh : C.S₁ ≤ Sh := fun x hx => (hmemSh x).2 (Or.inl hx)
  have hShT : Sh ≤ T := by
    intro x hx
    rcases (hmemSh x).1 hx with h1 | h1
    · exact hST h1
    · have : x = δ * (δ⁻¹ * x) := by group
      rw [this]
      exact T.mul_mem hδT (hST h1)
  have hShp : IsPGroup 2 Sh := hT.to_le hShT
  have hShN : Sh ≤ normalizer (C.S₀ : Set G) := by
    intro x hx
    rcases (hmemSh x).1 hx with h1 | h1
    · exact hS₁N h1
    · have : x = δ * (δ⁻¹ * x) := by group
      rw [this]
      exact mul_mem hδS₀ (hS₁N h1)
  have helem : ∀ B : Subgroup G, B ≤ Sh → IsElemAbelian 2 B → Nat.card B = q ^ 4 →
      B = W ∨ B = W' := by
    intro B hBSh hBe hBc
    have hB2 : ∀ x ∈ B, x * x = 1 := fun x hx => by rw [← sq]; exact hBe.2 x hx
    have hBS₀ : B ≤ C.S₀ := by
      by_contra hnot
      obtain ⟨b, hbB, hbS⟩ := Set.not_subset.mp hnot
      have hbound := C.card_le_of_centralizes hψt hShp hS₁Sh hShN (hBSh hbB) hbS
        (B := B ⊓ C.S₀) inf_le_right (fun x hx => hB2 x hx.1)
        (fun x hx => comm_of_isElemAbelian hBe hbB hx.1)
      have hcard := C.card_le_card_inf_mul hψt hShp hS₁Sh hShN hBSh
      have hr := hrange4 B (hBSh.trans hShN) hB2
      rw [hBc] at hcard
      exact hq4 (hcard.trans (Nat.mul_le_mul (hbound.trans hF.le) hr))
    set E : Subgroup (unipAll F) := (B.subgroupOf C.S₀).map C.e.toMonoidHom with hE
    have hE2 : ∀ g ∈ E, g * g = 1 := by
      rintro _ ⟨s, hs, rfl⟩
      rw [← map_mul]
      have : s * s = 1 := Subtype.ext (hB2 _ hs)
      rw [this, map_one]
    have hEcard : Nat.card E = Nat.card F ^ 2 := by
      rw [hE, Subgroup.card_map_of_injective C.e.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS₀).toEquiv, hBc, hF]
      ring
    have hmemE : ∀ x (hx : x ∈ B), C.e ⟨x, hBS₀ hx⟩ ∈ E := fun x hx => ⟨⟨x, hBS₀ hx⟩, hx, rfl⟩
    rcases eq_radOne_or_radTwo_of_card hE2 hEcard with h1 | h1
    · left
      refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [hWc, hBc])
      have := hmemE x hx
      rw [h1] at this
      exact (C.mem_W_iff _).2 this
    · right
      refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [hW'c, hBc])
      have := hmemE x hx
      rw [h1] at this
      exact (hmemW' _).2 this
  have hShT_eq : Sh = T := by
    by_contra hne'
    obtain ⟨x, hxT, hxN, hxnot, -⟩ := exists_normalizing_sq_mem hT hShT hne'
    have hBSh : W.map (MulAut.conj x).toMonoidHom ≤ Sh := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hxN y).1 (hS₁Sh (C.S₀_le (C.W_le hy)))
    rcases helem _ hBSh (isElemAbelian_map_conj' hWe x) (by rw [card_map_conj, hWc]) with h1 | h1
    · apply hxnot
      refine hS₁Sh (C.mem_S₁_of_mem_normalizer hT hST hxT
        (Subgroup.mem_normalizer_fintype fun y hy => ?_))
      rw [← h1]
      exact ⟨y, hy, rfl⟩
    · apply hxnot
      have hdx : δ⁻¹ * x ∈ normalizer (W : Set G) := by
        refine Subgroup.mem_normalizer_fintype fun y hy => ?_
        have h2 : x * y * x⁻¹ ∈ W' := by
          rw [← h1]
          exact ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hze⟩ := h2
        have hze' : δ * z * δ⁻¹ = x * y * x⁻¹ := hze
        have e : δ⁻¹ * x * y * (δ⁻¹ * x)⁻¹ = z := by
          calc δ⁻¹ * x * y * (δ⁻¹ * x)⁻¹ = δ⁻¹ * (x * y * x⁻¹) * δ := by group
            _ = δ⁻¹ * (δ * z * δ⁻¹) * δ := by rw [hze']
            _ = z := by group
        rw [e]
        exact hz
      have hdxT : δ⁻¹ * x ∈ T := T.mul_mem (T.inv_mem hδT) hxT
      exact (hmemSh x).2 (Or.inr (C.mem_S₁_of_mem_normalizer hT hST hdxT hdx))
  rw [← hShT_eq]
  exact hShN

include C in
theorem false [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hf3 : 3 ≤ f)
    (hF' : FusionFacts A (2 ^ f)) {V₁ V₂ Vi : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hsyl : ∀ Vj : Subgroup G, (Vj = V₁ ∨ Vj = V₂) →
      IsSylowOf 2 (Vj ⊔ zpowers d.t) (centralizer ((Vj ⊔ zpowers d.t : Subgroup G) : Set G)))
    (hW : Vi = V₁ ∨ Vi = V₂) (hWe : IsElemAbelian 2 W) (hWc : Nat.card W = (2 ^ f) ^ 4)
    (hcomm : ∀ v ∈ Vi, ∃ x ∈ W, d.t * x * d.t * x⁻¹ = v)
    (hF : Nat.card F = (2 ^ f) ^ 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 C.S₁ := C.isPGroup_S₁
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hTp : IsPGroup 2 (Q : Subgroup G) := Q.isPGroup'
  have hTidx : ¬ 2 ∣ (Q : Subgroup G).index := Q.not_dvd_index
  by_cases hS : C.S₁ = Q
  · refine C.false_of_le_normalizer hnonab hf3 hF' hR hsyl hW hWe hWc hcomm hF hTp hTidx hQ ?_
    rw [← hS]
    exact C.S₁_le
  · exact C.false_of_le_normalizer hnonab hf3 hF' hR hsyl hW hWe hWc hcomm hF hTp hTidx hQ
      (C.le_normalizer_of_ne hf3 hR hW hWe hWc hcomm hF hTp hQ hS)

end CaseAData

end CFSG.LocalAnalysis.EvenBN.LinearThree
