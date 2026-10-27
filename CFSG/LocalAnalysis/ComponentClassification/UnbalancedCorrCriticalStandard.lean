module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCritical
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open scoped Pointwise

@[expose] def LayerGeneratedUniversalComponentStandard : Prop :=
  ∀ (F : Type) [Group F] [Finite F], SectionRank.IsKGroupCat F →
    ∀ L : Subgroup F, L ≤ layer F → IsQuasisimple ↥L →
      (∃ E : Subgroup F, E ≤ L ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4) →
      ∀ a : F, a ∈ centralizer (L : Set F) → orderOf a = 2 →
        (∀ t : F, t ∈ centralizer (L : Set F) → orderOf t = 2 →
          IsComponent (L.subgroupOf (centralizer ({t} : Set F)))) →
        ⁅⨆ e ∈ layer F, conjugate L e, zpowers a⁆ = ⨆ e ∈ layer F, conjugate L e →
        IsStandardSubgroup L

variable {G : Type} [Group G] [Finite G]

theorem exists_lex_max {𝔅 : Set (Subgroup G)} (hne : 𝔅.Nonempty) (f : Subgroup G → ℕ)
    (hf : ∀ C, f C ≤ Nat.card G) :
    ∃ B ∈ 𝔅, ∀ C ∈ 𝔅, Nat.card C < Nat.card B ∨ (Nat.card C = Nat.card B ∧ f C ≤ f B) := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
  obtain ⟨B, hB, hmax⟩ := Set.exists_max_image 𝔅
    (fun C => Nat.card C * (Nat.card G + 1) + f C) (Set.toFinite 𝔅) hne
  refine ⟨B, hB, fun C hC => ?_⟩
  have h1 := hmax C hC
  have hfB := hf B
  have hfC := hf C
  rcases lt_trichotomy (Nat.card C) (Nat.card B) with h | h | h
  · exact Or.inl h
  · right
    refine ⟨h, ?_⟩
    rw [h] at h1
    omega
  · exfalso
    have h2 : (Nat.card B + 1) * (Nat.card G + 1) ≤ Nat.card C * (Nat.card G + 1) :=
      Nat.mul_le_mul_right _ h
    have h3 : (Nat.card B + 1) * (Nat.card G + 1) =
        Nat.card B * (Nat.card G + 1) + Nat.card G + 1 := by ring
    omega

omit [Finite G] in
theorem le_of_perfect_of_le_sup_solvable {U Y K : Subgroup G}
    (hY : Y ≤ normalizer (U : Set G)) (hYs : Group.IsSolvable ↥Y) (hK : ⁅K, K⁆ = K)
    (hKle : K ≤ U ⊔ Y) : K ≤ U := by
  set Z := U ⊔ Y with hZdef
  have hUZ : U ≤ Z := le_sup_left
  have hZN : Z ≤ normalizer (U : Set G) := sup_le le_normalizer hY
  have hUn : (U.subgroupOf Z).Normal := (normal_subgroupOf_iff_le_normalizer hUZ).mpr hZN
  let f : ↥(Y.subgroupOf Z) →* ↥Z ⧸ U.subgroupOf Z :=
    (QuotientGroup.mk' _).comp (Y.subgroupOf Z).subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hz : (z : G) ∈ (U : Set G) * (Y : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left U Y hY]
      exact z.2
    obtain ⟨u, hu, y, hy, huy⟩ := Set.mem_mul.mp hz
    refine ⟨⟨⟨y, mem_sup_right hy⟩, hy⟩, ?_⟩
    show ((⟨y, mem_sup_right hy⟩ : Z) : ↥Z ⧸ U.subgroupOf Z) = (z : ↥Z ⧸ U.subgroupOf Z)
    rw [QuotientGroup.eq, mem_subgroupOf]
    show y⁻¹ * (z : G) ∈ U
    rw [← huy]
    have h1 := (mem_normalizer_iff.mp (inv_mem (hY hy)) u).mp hu
    rw [inv_inv] at h1
    rwa [← mul_assoc]
  let e : ↥(Y.subgroupOf Z) ≃* ↥Y := subgroupOfEquivOfLe le_sup_right
  have hYs' : Group.IsSolvable ↥(Y.subgroupOf Z) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hQs : Group.IsSolvable (↥Z ⧸ U.subgroupOf Z) := Group.isSolvable_of_surjective hf
  have hK'perf : ⁅(K.subgroupOf Z).map (QuotientGroup.mk' (U.subgroupOf Z)),
      (K.subgroupOf Z).map (QuotientGroup.mk' (U.subgroupOf Z))⁆ =
      (K.subgroupOf Z).map (QuotientGroup.mk' (U.subgroupOf Z)) := by
    rw [← map_commutator]
    congr 1
    apply map_injective Z.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hKle, hK]
  have hbot := eq_bot_of_commutator_eq_of_isSolvable hK'perf inferInstance
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro k hk
  exact hbot (show (⟨k, hKle hk⟩ : Z) ∈ K.subgroupOf Z from hk)

omit [Finite G] in
theorem isComponent_subgroupOf_conjugate {L C : Subgroup G} (g : G)
    (h : IsComponent (L.subgroupOf C)) :
    IsComponent ((conjugate L g).subgroupOf (conjugate C g)) := by
  let e : ↥C ≃* ↥(conjugate C g) :=
    C.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have h1 := LocalCores.isComponent_map_mulEquiv e h
  have h2 : (L.subgroupOf C).map e.toMonoidHom = (conjugate L g).subgroupOf (conjugate C g) := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      rw [mem_subgroupOf, UnbalancedLayer.mem_conjugate_iff]
      show g * (g⁻¹ * (c : G) * g⁻¹⁻¹) * g⁻¹ ∈ L
      rw [show g * (g⁻¹ * (c : G) * g⁻¹⁻¹) * g⁻¹ = c by group]
      exact hc
    · intro y hy
      rw [mem_subgroupOf, UnbalancedLayer.mem_conjugate_iff] at hy
      have hyC : g * (y : G) * g⁻¹ ∈ C := by
        have h3 := y.2
        rw [UnbalancedLayer.mem_conjugate_iff] at h3
        exact h3
      refine ⟨⟨g * (y : G) * g⁻¹, hyC⟩, hy, ?_⟩
      apply Subtype.ext
      show g⁻¹ * (g * (y : G) * g⁻¹) * g⁻¹⁻¹ = y
      group
  rwa [h2] at h1

omit [Finite G] in
theorem conjugate_zpowers (x g : G) : conjugate (zpowers x) g = zpowers (g⁻¹ * x * g) := by
  show (zpowers x).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [MonoidHom.map_zpowers]
  congr 1
  show g⁻¹ * x * g⁻¹⁻¹ = _
  rw [inv_inv]

theorem exists_four_of_two_le_pRank {Y : Type*} [Group Y] [Finite Y] (h : 2 ≤ pRank 2 Y) :
    ∃ E : Subgroup Y, IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := {r : ℕ | ∃ A : Subgroup Y, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} with hSdef
  have hne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : pRank 2 Y = 0 := by
      show sSup S = 0
      rw [hne, csSup_empty]; rfl
    omega
  have hbdd : BddAbove S := by
    refine ⟨Nat.card Y, ?_⟩
    rintro r ⟨A, -, hA⟩
    have h1 : r < 2 ^ r := Nat.lt_two_pow_self
    have h2 : Nat.card A ≤ Nat.card Y := Subgroup.card_le_card_group A
    omega
  obtain ⟨A, hA, hcard⟩ := Nat.sSup_mem hne hbdd
  set m := sSup S with hmdef
  have hm : 2 ≤ m := h
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2) (G := A)
    (by rw [hcard]; exact pow_dvd_pow 2 hm)
  have hFe : IsElementaryAbelian 2 F :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
        (hA.toIsMulCommutative.is_comm.comm (x : A) (y : A))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) (x : A)) }
  refine ⟨F.map A.subtype, IsElementaryAbelian.map _, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hF]
  norm_num

theorem pRank_two_congr {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y) :
    pRank 2 X = pRank 2 Y := CFSG.pRank_congr_of_mulEquiv e 2

theorem pRank_two_quotient_pPrimeCore (X : Type*) [Group X] [Finite X] :
    pRank 2 X = pRank 2 (X ⧸ pPrimeCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top,
    SectionRank.pRank_quotient_eq (pPrimeCore 2 X)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card)]

theorem critical_local_quotient_standard_component_producer_of_inputs
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hCTI : LayerGeneratedUniversalComponentStandard)
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {S P : Subgroup G} (hSX : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)))
    (hP : P = S ⊓ UnbalancedLayer.coreActionKernel J)
    (H R T X E V : Subgroup G → Subgroup G) (hH : ∀ B, H B = normalizer (B : Set G))
    (hR : ∀ B, R B = (pPrimeCore 2 ↥(H B)).map (H B).subtype)
    (hT : ∀ B, T B = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype)
    (hX : ∀ B, X B = T B ⊔ R B) (hE : ∀ B, E B = (pLayer ↥(H B) 2).map (H B).subtype)
    (hV : ∀ B, V B = ⨆ e ∈ E B, conjugate (T B) e) (d : Subgroup G → ℕ)
    (hd : ∀ W : Subgroup G,
      d W = Nat.card ((↥W ⧸ pPrimeCore 2 ↥W) ⧸ center (↥W ⧸ pPrimeCore 2 ↥W)))
    (hz : ∀ z : G, orderOf z = 2 → z ∈ P → z ∈ centralizer (S : Set G) →
      ∃ P₀ : Sylow 2 ↥(centralizer ({z} : Set G) ⊓ normalizer (X (zpowers z) : Set G)),
        (P₀ : Subgroup _) =
          S.subgroupOf (centralizer ({z} : Set G) ⊓ normalizer (X (zpowers z) : Set G)))
    (hb : ∃ b : G, orderOf b = 2 ∧ b ∈ P ∧ ∀ M : Subgroup G, ¬ UnbalancedGS.GSIsoCorr a J b M)
    (hJ2 : 2 ≤ pRank 2 ↥J) :
    ∃ B : Subgroup G, B ≠ ⊥ ∧ B ≤ P ∧ ∃ haH : a ∈ H B,
      let θ := QuotientGroup.mk' (criticalOddTwoCore ↥(H B))
      let ā := θ ⟨a, haH⟩
      let L := ((T B).subgroupOf (H B)).map θ
      let W := ((V B).subgroupOf (H B)).map θ
      ((criticalOddTwoCore ↥(H B)).map (H B).subtype = R B ⊔ B ∧ R B ⊓ B = ⊥ ∧
        ⁅R B, B⁆ = ⊥ ∧ orderOf ā = 2 ∧ V B = E B ∧ ⁅V B, zpowers a⁆ = V B ∧
        B ≤ H B ⊓ UnbalancedLayer.coreActionKernel (V B) ∧
        (∃ P₀ : Sylow 2 ↥(H B ⊓ UnbalancedLayer.coreActionKernel (V B)),
          (P₀ : Subgroup _) = B.subgroupOf (H B ⊓ UnbalancedLayer.coreActionKernel (V B))) ∧
        S ⊓ normalizer (B : Set G) ≤ normalizer (B : Set G) ⊓ normalizer (X B : Set G) ∧
        ∃ P₀ : Sylow 2 ↥(normalizer (B : Set G) ⊓ normalizer (X B : Set G)),
          (P₀ : Subgroup _) = (S ⊓ normalizer (B : Set G)).subgroupOf
            (normalizer (B : Set G) ⊓ normalizer (X B : Set G))) ∧
      (L ≤ centralizer ({ā} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) ∧
        IsComponent (L.subgroupOf (centralizer ({ā} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))))) ∧
        2 ≤ pRank 2 ↥L ∧ IsStandardSubgroup L) ∧
      ((∃ e : ↥L ⧸ center ↥L ≃* ↥J ⧸ CFSG.Open.fusionZStar ↥J,
          ∀ (x : ↥((T B).subgroupOf (H B))) (hx : ((x : ↥(H B)) : G) ∈ J),
            e ((θ.subgroupMap ((T B).subgroupOf (H B)) x : ↥L) : ↥L ⧸ center ↥L) =
              ((⟨_, hx⟩ : J) : J ⧸ CFSG.Open.fusionZStar ↥J)) ∧
        (⨆ e ∈ layer (↥(H B) ⧸ criticalOddTwoCore ↥(H B)), conjugate L e) = W ∧
        ⁅W, zpowers ā⁆ = W ∧
        V B ⊓ (criticalOddTwoCore ↥(H B)).map (H B).subtype =
          (CFSG.Open.fusionZStar ↥(V B)).map (V B).subtype) ∧
      ∀ C : Subgroup G, C ≠ ⊥ → C ≤ P →
        (Nat.card B < Nat.card C ∨ (Nat.card B = Nat.card C ∧
          Nat.card ↥(S ⊓ normalizer (B : Set G)) < Nat.card ↥(S ⊓ normalizer (C : Set G)))) →
        V C ≤ H C ∧ IsPComponent 2 ((V C).subgroupOf (H C)) ∧ conjugate (V C) a = V C ∧
          (T C : Set G) * ((pPrimeCore 2 ↥(V C)).map (V C).subtype : Set G) = V C ∧
          T C = UnbalancedGS.gsFixedLayer (V C) a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := by
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have h1 : IsPGroup 2 (S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :=
      hP₀ ▸ P₀.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hSX)
  obtain ⟨⟨B₀, hB₀1, hB₀P, hbad₀⟩, hA5⟩ :=
    critical_two_subgroup_full_layer_and_odd_two_core_of_inputs hS hU hheld hnonab hK ha hJa hJ
      hSX hSsyl hP H R T X E V hH hR hT hX hE hV d hd hz hb
  obtain ⟨B, ⟨hB1, hBP, hbad⟩, hmax⟩ := exists_lex_max
    (𝔅 := {C : Subgroup G | C ≠ ⊥ ∧ C ≤ P ∧ d J < d (V C)}) ⟨B₀, hB₀1, hB₀P, hbad₀⟩
    (fun C => Nat.card ↥(S ⊓ normalizer (C : Set G))) (fun C => Subgroup.card_le_card_group _)
  obtain ⟨⟨hQL, hQsyl⟩, hVEeq, hVa, hBD, hBsylD, hNeq, hRBbot, hRBc, haN, hZ, -, hlarger⟩ :=
    hA5 B hB1 hBP hbad fun C hC1 hCP hCbad => hmax C ⟨hC1, hCP, hCbad⟩
  have hA2 := actual_two_local_fixed_layer_orbits_of_inputs hS hU hheld hnonab hK ha hJa hJ hSX
    hSsyl hP H R T X E V hH hR hT hX hE hV d hd
  obtain ⟨⟨hHtop, hKH⟩, -, hsupT, ⟨eTJ, heTJ⟩, hTaH, hpcT, hTE, ⟨M, hMH, hM, hMa, hVM, hVE,
    hVEn, -⟩, hOX, -, hQact, hNV⟩ := hA2.1 B hB1 hBP
  have haN' : a ∈ normalizer (B : Set G) := by
    obtain ⟨-, h, -⟩ := two_local_layer_facts hS hnonab hK ha hJa hJ hSX hS2 hB1 (hBP.trans hP.le)
      (hT B)
    exact h
  have haH : a ∈ H B := (hH B).symm ▸ haN'
  refine ⟨B, hB1, hBP, haH, ?_⟩
  intro θ ā L W
  have hRf : ∀ C : Subgroup G, R C = (pPrimeCore 2 ↥(normalizer (C : Set G))).map
      (normalizer (C : Set G)).subtype := fun C => by rw [hR, hH]
  have hBP' : B ≤ S ⊓ UnbalancedLayer.coreActionKernel J := hBP.trans hP.le
  have hB2 : IsPGroup 2 B := hS2.to_le (hBP'.trans inf_le_left)
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hHB : H B = normalizer (B : Set G) := hH B
  have hBH : B ≤ H B := hHB ▸ le_normalizer
  have hEB : E B = (pLayer ↥(H B) 2).map (H B).subtype := hE B
  have hVE' : V B ≤ (pLayer ↥(H B) 2).map (H B).subtype := hEB ▸ hVE
  have hEV : (pLayer ↥(H B) 2).map (H B).subtype ≤ normalizer (V B : Set G) :=
    hEB ▸ (normal_subgroupOf_iff_le_normalizer hVE).mp hVEn
  have hVH : V B ≤ H B := hVE'.trans (map_subtype_le _)
  have hVsub : ((V B).subgroupOf (H B)).IsSubnormal := isSubnormal_of_le_pLayer hVE' hEV
  have hOV : (pPrimeCore 2 ↥(V B)).map (V B).subtype = V B ⊓ R B := by
    rw [hR B]
    exact map_pPrimeCore_eq_inf_of_subgroupOf hVH hVsub
  have hMaH : conjugate M a ≤ H B := by
    have h1 := hVH
    rw [hVM] at h1
    exact le_sup_right.trans h1
  have hRBH : R B ≤ H B := by rw [hR B]; exact map_subtype_le _
  have hHR : H B ≤ normalizer (R B : Set G) := by
    rw [hR B]
    exact nested_le_normalizer_map_pPrimeCore (H B)
  have hTB : T B ≤ J ⊓ centralizer (B : Set G) := by rw [hT B]; exact map_subtype_le _
  have hTJ : T B ≤ J := hTB.trans inf_le_left
  have hTH : T B ≤ H B := hTaH.trans inf_le_left
  have hBn : (B.subgroupOf (H B)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBH).mpr hHB.le
  have hB2' : IsPGroup 2 (B.subgroupOf (H B)) :=
    hB2.comap_of_injective (H B).subtype (H B).subtype_injective
  have hθker : θ.ker = pPrimeCore 2 ↥(H B) ⊔ B.subgroupOf (H B) := by
    rw [QuotientGroup.ker_mk']
    apply map_injective (H B).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hBH, hNeq, hR B]
  have ha'1 : (⟨a, haH⟩ : H B) ∉ criticalOddTwoCore ↥(H B) := fun h => haN ⟨_, h, rfl⟩
  have hā2 : orderOf ā = 2 := by
    apply orderOf_eq_prime
    · show θ ⟨a, haH⟩ ^ 2 = 1
      rw [← map_pow]
      have h1 : (⟨a, haH⟩ : H B) ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_two]
        exact haa)
      rw [h1, map_one]
    · intro h
      exact ha'1 ((QuotientGroup.eq_one_iff _).mp h)
  set A := (B ⊔ zpowers a).subgroupOf (H B) with hAdef
  have hza2 : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hzaB : zpowers a ≤ normalizer (B : Set G) := zpowers_le.mpr haN'
  have hBa2 : IsPGroup 2 (B ⊔ zpowers a : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hB2 hza2 hzaB
  have hBaH : B ⊔ zpowers a ≤ H B := sup_le hBH (hHB ▸ hzaB)
  have hA2 : IsPGroup 2 A := hBa2.comap_of_injective (H B).subtype (H B).subtype_injective
  have hA1 : A ≠ ⊥ := by
    obtain ⟨b, hb⟩ := ne_bot_iff_exists_ne_one.mp hB1
    refine ne_bot_iff_exists_ne_one.mpr ⟨⟨⟨b, hBH b.2⟩, mem_sup_left b.2⟩, ?_⟩
    intro h
    apply hb
    exact Subtype.ext (congrArg (fun z : A => ((z : H B) : G)) h)
  have hBA : B.subgroupOf (H B) ≤ A := fun x hx => mem_sup_left hx
  have hCA : centralizer ((B ⊔ zpowers a : Subgroup G) : Set G) =
      centralizer ({a} : Set G) ⊓ centralizer (B : Set G) := by
    rw [centralizer_sup_zpowers, inf_comm]
  have hTaB : T B ≤ centralizer ({a} : Set G) ⊓ centralizer (B : Set G) := fun t ht =>
    ⟨hJa (hTB ht).1, (hTB ht).2⟩
  have hTCA : T B ≤ centralizer ((B ⊔ zpowers a : Subgroup G) : Set G) := hCA ▸ hTaB
  have hNA : normalizer ((A : Subgroup (H B)) : Set (H B)) =
      (normalizer ((B ⊔ zpowers a : Subgroup G) : Set G) ⊓ H B).subgroupOf (H B) := by
    rw [hAdef, normalizer_subgroupOf_eq hBaH, inf_subgroupOf_right]
  have hTA : (T B).subgroupOf (H B) ≤ normalizer ((A : Subgroup (H B)) : Set (H B)) := by
    rw [hNA]
    intro t ht
    exact ⟨centralizer_le_normalizer' _ (hTCA ht), t.2⟩
  have hYZ : centralizer ((B ⊔ zpowers a : Subgroup G) : Set G) ≤
      normalizer ((B ⊔ zpowers a : Subgroup G) : Set G) ⊓ H B :=
    le_inf (centralizer_le_normalizer' _) (hCA.le.trans (inf_le_right.trans
      ((centralizer_le_normalizer' B).trans hHB.ge)))
  have hYZn : ((centralizer ((B ⊔ zpowers a : Subgroup G) : Set G)).subgroupOf
      (normalizer ((B ⊔ zpowers a : Subgroup G) : Set G) ⊓ H B)).Normal := by
    refine ⟨fun y hy z => ?_⟩
    have h1 := (centralizer_normal_normalizer (B ⊔ zpowers a)).conj_mem
      ⟨y, (mem_inf.mp y.2).1⟩ hy ⟨z, (mem_inf.mp z.2).1⟩
    exact h1
  have hpcB : IsPComponent 2 ((T B).subgroupOf
      (centralizer ({a} : Set G) ⊓ centralizer (B : Set G))) := by
    obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := two_local_layer_facts hS hnonab hK ha hJa hJ hSX hS2
      hB1 hBP' (hT B)
    exact h
  have hpcA : IsPComponent 2 ((T B).subgroupOf
      (normalizer ((B ⊔ zpowers a : Subgroup G) : Set G) ⊓ H B)) := by
    have h1 : IsPComponent 2 ((T B).subgroupOf
        (centralizer ((B ⊔ zpowers a : Subgroup G) : Set G))) := by
      rw [hCA]
      exact hpcB
    exact isPComponent_subgroupOf_of_isSubnormal hTCA hYZ hYZn.isSubnormal h1
  have hTApc : IsPComponent 2 (((T B).subgroupOf (H B)).subgroupOf
      (normalizer ((A : Subgroup (H B)) : Set (H B)))) := by
    rw [hNA, isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two]
    exact hpcA
  obtain ⟨-, -, -, -, -, -, hLN, hLcomp, hOcent, -, ⟨eZ, heZ⟩, hrank⟩ :=
    kGroup_odd_times_two_normalizer_component_transport_of_inputs hS hU hheld hKH
      (B.subgroupOf (H B)) hB2' θ (QuotientGroup.mk'_surjective _) hθker A hA2 hA1 hBA
      ((T B).subgroupOf (H B)) hTA hTApc
  have hza' : (zpowers a).subgroupOf (H B) = zpowers (⟨a, haH⟩ : H B) := by
    apply map_injective (H B).subtype_injective
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr haH), MonoidHom.map_zpowers]
    rfl
  have hθA : A.map θ = zpowers ā := by
    rw [hAdef, subgroupOf_sup hBH (zpowers_le.mpr haH), hza', Subgroup.map_sup,
      MonoidHom.map_zpowers]
    have hBθ : (B.subgroupOf (H B)).map θ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hθker]
      exact le_sup_right
    rw [hBθ, bot_sup_eq]
  have hNā : normalizer ((zpowers ā : Subgroup _) : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) =
      centralizer ({ā} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) :=
    normalizer_zpowers_eq_centralizer hā2
  rw [hθA, hNā] at hLN hLcomp
  have hT2 : 2 ≤ pRank 2 ↥((T B).subgroupOf (H B)) := by
    rw [pRank_two_congr (subgroupOfEquivOfLe hTH), pRank_two_quotient_pPrimeCore,
      pRank_two_congr eTJ, ← pRank_two_quotient_pPrimeCore]
    exact hJ2
  have hL2 : 2 ≤ pRank 2 ↥L := hrank hT2
  have hiso : ∃ e : ↥L ⧸ center ↥L ≃* ↥J ⧸ CFSG.Open.fusionZStar ↥J,
      ∀ (x : ↥((T B).subgroupOf (H B))) (hx : ((x : ↥(H B)) : G) ∈ J),
        e ((θ.subgroupMap ((T B).subgroupOf (H B)) x : ↥L) : ↥L ⧸ center ↥L) =
          ((⟨_, hx⟩ : J) : J ⧸ CFSG.Open.fusionZStar ↥J) := by
    let ι : ↥((T B).subgroupOf (H B)) ≃* ↥(T B) := subgroupOfEquivOfLe hTH
    obtain ⟨g₁, hg₁⟩ := exists_zstar_equiv ↥((T B).subgroupOf (H B))
    obtain ⟨g₂, hg₂⟩ := exists_centerQuotient_congr
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 ι)
    obtain ⟨g₃, hg₃⟩ := exists_centerQuotient_congr eTJ
    obtain ⟨g₄, hg₄⟩ := exists_zstar_equiv ↥J
    refine ⟨eZ.symm.trans (g₁.trans (g₂.trans (g₃.trans g₄.symm))), fun x hx => ?_⟩
    have h1 : eZ.symm ((θ.subgroupMap ((T B).subgroupOf (H B)) x : ↥L) : ↥L ⧸ center ↥L) =
        (x : ↥((T B).subgroupOf (H B)) ⧸ CFSG.Open.fusionZStar ↥((T B).subgroupOf (H B))) := by
      rw [MulEquiv.symm_apply_eq, heZ]
    simp only [MulEquiv.trans_apply]
    rw [h1, hg₁, hg₂, UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr_mk, hg₃,
      heTJ (ι x) ⟨_, hx⟩ rfl, MulEquiv.symm_apply_eq, hg₄]
  have hBbot : B.subgroupOf (H B) ≠ ⊥ := by
    intro h
    apply hB1
    have h1 := congrArg (Subgroup.map (H B).subtype) h
    rwa [map_subgroupOf_eq_of_le hBH, Subgroup.map_bot] at h1
  have hNBtop : normalizer ((B.subgroupOf (H B) : Subgroup (H B)) : Set (H B)) = ⊤ :=
    normalizer_eq_top_iff.mpr hBn
  have hcompθ : ∀ K : Subgroup G, K ≤ H B → IsPComponent 2 (K.subgroupOf (H B)) →
      IsComponent ((K.subgroupOf (H B)).map θ) := by
    intro K hKHB hKc
    have hKA : K.subgroupOf (H B) ≤ normalizer ((B.subgroupOf (H B) : Subgroup (H B)) :
        Set (H B)) := by
      rw [hNBtop]
      exact le_top
    have hKc' : IsPComponent 2 ((K.subgroupOf (H B)).subgroupOf
        (normalizer ((B.subgroupOf (H B) : Subgroup (H B)) : Set (H B)))) := by
      rw [hNBtop, ← subgroupOf_self (H B),
        isPComponent_subgroupOf_subgroupOf_iff' le_rfl 2 Nat.prime_two]
      exact hKc
    obtain ⟨-, -, -, -, -, -, -, hcomp, -⟩ :=
      kGroup_odd_times_two_normalizer_component_transport_of_inputs hS hU hheld hKH
        (B.subgroupOf (H B)) hB2' θ (QuotientGroup.mk'_surjective _) hθker
        (B.subgroupOf (H B)) hB2' hBbot le_rfl (K.subgroupOf (H B)) hKA hKc'
    have hBθ : (B.subgroupOf (H B)).map θ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hθker]
      exact le_sup_right
    rw [hBθ] at hcomp
    have htop : normalizer ((⊥ : Subgroup (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) :
        Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) = ⊤ :=
      normalizer_eq_top_iff.mpr inferInstance
    rw [htop] at hcomp
    have hq : IsQuasisimple ↥((K.subgroupOf (H B)).map θ) :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe le_top) hcomp.1
    obtain ⟨-, -, hs, -, -⟩ := id hKc
    exact ⟨hq, hs.map (QuotientGroup.mk'_surjective _)⟩
  have hWsup : W = ((M.subgroupOf (H B)).map θ) ⊔ (((conjugate M a).subgroupOf (H B)).map θ) := by
    show ((V B).subgroupOf (H B)).map θ = _
    rw [hVM, subgroupOf_sup hMH hMaH, Subgroup.map_sup]
  have hWlayer : W ≤ layer (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) := by
    rw [hWsup]
    exact sup_le (LocalCores.component_le_layer (hcompθ M hMH hM))
      (LocalCores.component_le_layer (hcompθ _ hMaH hMa))
  have hHV : H B ≤ normalizer (V B : Set G) := by
    rw [hVEeq, hEB]
    have : (pLayer ↥(H B) 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    intro h hh
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic (H B) (pLayer ↥(H B) 2)
      (le_normalizer hh)
  have hV'n : ((V B).subgroupOf (H B)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVH).mpr hHV
  have hWn : W.Normal := hV'n.map θ (QuotientGroup.mk'_surjective _)
  have hTV : T B ≤ V B := by
    obtain ⟨-, -, h, -, -, -⟩ := two_local_conj_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2
      hB1 hBP' (hT B) (hRf B) (hX B) (by rw [hE, hH]) (hV B)
    exact h
  have hLW : L ≤ W := map_mono (fun x hx => hTV hx)
  have hncl : (⨆ e ∈ layer (↥(H B) ⧸ criticalOddTwoCore ↥(H B)), conjugate L e) = W := by
    apply le_antisymm
    · refine iSup₂_le fun e _ => ?_
      have h1 : conjugate W e = W :=
        UnbalancedLayer.conjugate_eq_of_mem_normalizer (normalizer_eq_top_iff.mpr hWn ▸ mem_top e)
      rw [← h1]
      exact map_mono hLW
    ·
      have hVV : V B = ⨆ e ∈ V B, conjugate (T B) e := by
        conv_lhs => rw [hV B]
        rw [← hVEeq]
      rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      have hxV : ((x : H B) : G) ∈ V B := hx
      rw [hVV] at hxV
      set Y := ⨆ e ∈ layer (↥(H B) ⧸ criticalOddTwoCore ↥(H B)), conjugate L e with hYdef
      have hle : (⨆ e ∈ V B, conjugate (T B) e) ≤ (Y.comap θ).map (H B).subtype := by
        refine iSup₂_le fun e he => ?_
        intro y hy
        have hyH : y ∈ H B := by
          rw [UnbalancedLayer.mem_conjugate_iff] at hy
          have h1 := mul_mem (mul_mem (inv_mem (hVH he)) (hTH hy)) (hVH he)
          rwa [show e⁻¹ * (e * y * e⁻¹) * e = y by group] at h1
        refine ⟨⟨y, hyH⟩, ?_, rfl⟩
        show θ ⟨y, hyH⟩ ∈ Y
        have heW : θ ⟨e, hVH he⟩ ∈ layer (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) :=
          hWlayer (mem_map_of_mem θ (show (⟨e, hVH he⟩ : H B) ∈ (V B).subgroupOf (H B) from he))
        have hmem : θ ⟨y, hyH⟩ ∈ conjugate L (θ ⟨e, hVH he⟩) := by
          rw [UnbalancedLayer.mem_conjugate_iff]
          rw [UnbalancedLayer.mem_conjugate_iff] at hy
          have h1 : (⟨e, hVH he⟩ : H B) * ⟨y, hyH⟩ * (⟨e, hVH he⟩ : H B)⁻¹ =
              ⟨e * y * e⁻¹, hTH hy⟩ := rfl
          rw [← map_mul, ← map_inv, ← map_mul, h1]
          exact mem_map_of_mem θ (show (⟨e * y * e⁻¹, hTH hy⟩ : H B) ∈ (T B).subgroupOf (H B)
            from hy)
        exact (le_iSup₂ (f := fun e (_ : e ∈ layer (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) =>
          conjugate L e) _ heW) hmem
      obtain ⟨y, hy, hyx⟩ := hle hxV
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
  have hWa : ⁅W, zpowers ā⁆ = W := by
    have h1 : ⁅(V B).subgroupOf (H B), zpowers (⟨a, haH⟩ : H B)⁆ = (V B).subgroupOf (H B) := by
      apply map_injective (H B).subtype_injective
      rw [map_commutator, map_subgroupOf_eq_of_le hVH, MonoidHom.map_zpowers]
      exact hVa
    show ⁅((V B).subgroupOf (H B)).map θ, zpowers ā⁆ = ((V B).subgroupOf (H B)).map θ
    rw [← MonoidHom.map_zpowers, ← map_commutator, h1]
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥(H B)) with hπdef
  have hVsup : (V B).subgroupOf (H B) = (M ⊔ conjugate M a).subgroupOf (H B) := by rw [hVM]
  have hcommBot : ∀ {Y : Subgroup (↥(H B) ⧸ pPrimeCore 2 ↥(H B))}, Y.Normal →
      Group.IsSolvable ↥Y → ⁅((V B).subgroupOf (H B)).map π, Y⁆ = ⊥ := by
    intro Y hYn hYs
    rw [hVsup]
    exact commutator_map_sup_eq_bot_of_solvable hMH hM hMaH hMa hYn hYs
  have hTperf : ⁅T B, T B⁆ = T B := commutator_eq_of_isPComponent hTaH hpcT
  have hT'perf : ⁅(T B).subgroupOf (H B), (T B).subgroupOf (H B)⁆ = (T B).subgroupOf (H B) := by
    apply map_injective (H B).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hTH, hTperf]
  have hT₀U : ((T B).subgroupOf (H B)).map π ≤ ((V B).subgroupOf (H B)).map π :=
    map_mono (fun x hx => hTV hx)
  have hBbs : Group.IsSolvable ↥((B.subgroupOf (H B)).map π) := by
    have h1 : IsPGroup 2 ((B.subgroupOf (H B)).map π) := hB2'.map π
    have : Group.IsNilpotent ↥((B.subgroupOf (H B)).map π) := h1.isNilpotent
    infer_instance
  have hBbc := hcommBot (hBn.map π (QuotientGroup.mk'_surjective _)) hBbs
  have hBbN : (B.subgroupOf (H B)).map π ≤
      normalizer ((((T B).subgroupOf (H B)).map π : Subgroup _) : Set _) := by
    intro x hx
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := commutator_mem_commutator (hT₀U hy) hx
    rw [hBbc, mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have hRπ : (pPrimeCore 2 ↥(H B)).map π = ⊥ := by
    rw [hπdef, QuotientGroup.map_mk'_self]
  have hR'eq : (R B).subgroupOf (H B) = pPrimeCore 2 ↥(H B) := by
    rw [hR B]
    exact comap_map_eq_self_of_injective (H B).subtype_injective _
  have hX'eq : (X B).subgroupOf (H B) = (T B).subgroupOf (H B) ⊔ pPrimeCore 2 ↥(H B) := by
    rw [hX B, subgroupOf_sup hTH hRBH, hR'eq]
  have hRθ : (pPrimeCore 2 ↥(H B)).map θ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hθker]
    exact le_sup_left
  have hθX : ((X B).subgroupOf (H B)).map θ = L := by
    rw [hX'eq, Subgroup.map_sup, hRθ, sup_bot_eq]
  have hNL : (normalizer (((X B).subgroupOf (H B) : Subgroup (H B)) : Set (H B))).map θ =
      normalizer ((L : Subgroup _) : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) := by
    apply le_antisymm
    · rw [← hθX]
      exact le_normalizer_map θ
    · intro g hg
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ g
      refine ⟨h, ?_, rfl⟩
      have hY : L.comap θ = (X B).subgroupOf (H B) ⊔ B.subgroupOf (H B) := by
        rw [← hθX, comap_map_eq, hθker, hX'eq, sup_assoc, sup_left_idem, ← sup_assoc]
      have hhY : h ∈ normalizer ((((X B).subgroupOf (H B) ⊔ B.subgroupOf (H B) : Subgroup _)) :
          Set (H B)) := by
        rw [← hY, ← comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _)]
        exact hg
      have hThY : ((T B).subgroupOf (H B)).map (MulAut.conj h).toMonoidHom ≤
          (X B).subgroupOf (H B) ⊔ B.subgroupOf (H B) := by
        rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp hhY y).mp (mem_sup_left (hX'eq ▸ mem_sup_left hy))
      have hThperf : ⁅((T B).subgroupOf (H B)).map (MulAut.conj h).toMonoidHom,
          ((T B).subgroupOf (H B)).map (MulAut.conj h).toMonoidHom⁆ =
          ((T B).subgroupOf (H B)).map (MulAut.conj h).toMonoidHom := by
        rw [← map_commutator, hT'perf]
      have hπTh : (((T B).subgroupOf (H B)).map (MulAut.conj h).toMonoidHom).map π ≤
          ((T B).subgroupOf (H B)).map π := by
        apply le_of_perfect_of_le_sup_solvable hBbN hBbs
        · rw [← map_commutator, hThperf]
        · calc (((T B).subgroupOf (H B)).map (MulAut.conj h).toMonoidHom).map π
              ≤ ((X B).subgroupOf (H B) ⊔ B.subgroupOf (H B)).map π := map_mono hThY
            _ = ((T B).subgroupOf (H B)).map π ⊔ (B.subgroupOf (H B)).map π := by
              rw [Subgroup.map_sup, hX'eq, Subgroup.map_sup, hRπ, sup_bot_eq]
      have hThX : ((T B).subgroupOf (H B)).map (MulAut.conj h).toMonoidHom ≤
          (X B).subgroupOf (H B) := by
        intro y hy
        obtain ⟨z, hz, hzy⟩ := hπTh ⟨y, hy, rfl⟩
        have hr : z⁻¹ * y ∈ pPrimeCore 2 ↥(H B) := by
          rw [← QuotientGroup.eq]
          exact hzy
        rw [show y = z * (z⁻¹ * y) by group, hX'eq]
        exact mul_mem (mem_sup_left hz) (mem_sup_right hr)
      apply mem_normalizer_of_forall_conj_mem
      intro x hx
      have hmap : ((X B).subgroupOf (H B)).map (MulAut.conj h).toMonoidHom ≤
          (X B).subgroupOf (H B) := by
        conv_lhs => rw [hX'eq]
        rw [Subgroup.map_sup]
        refine sup_le hThX ?_
        rintro _ ⟨r, hr, rfl⟩
        rw [hX'eq]
        exact mem_sup_right ((inferInstance : (pPrimeCore 2 ↥(H B)).Normal).conj_mem r hr h)
      exact hmap ⟨x, hx, rfl⟩
  have hNdef : (criticalOddTwoCore ↥(H B)).map (H B).subtype ≤ H B := map_subtype_le _
  have hHN : H B ≤ normalizer (((criticalOddTwoCore ↥(H B)).map (H B).subtype : Subgroup G) :
      Set G) := by
    rw [← normal_subgroupOf_iff_le_normalizer hNdef,
      show ((criticalOddTwoCore ↥(H B)).map (H B).subtype).subgroupOf (H B) =
        criticalOddTwoCore ↥(H B) from comap_map_eq_self_of_injective (H B).subtype_injective _]
    infer_instance
  have hObs : Group.IsSolvable ↥(pCore 2 (↥(H B) ⧸ pPrimeCore 2 ↥(H B))) := by
    have : Group.IsNilpotent ↥(pCore 2 (↥(H B) ⧸ pPrimeCore 2 ↥(H B))) := pCore_isNilpotent
    infer_instance
  have hπK : (criticalOddTwoCore ↥(H B)).map π = pCore 2 (↥(H B) ⧸ pPrimeCore 2 ↥(H B)) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hOc : ⁅((V B).subgroupOf (H B)).map π, pCore 2 (↥(H B) ⧸ pPrimeCore 2 ↥(H B))⁆ = ⊥ :=
    hcommBot inferInstance hObs
  have hA3 := (nested_two_local_full_core_residual_identities_of_inputs hS hU hheld hnonab hK ha
    hJa hJ hSX hSsyl hP H R T X hH hR hT hX).1
  have hU3 : ∀ (t : G) (htQ : t ∈ S ⊓ normalizer (B : Set G)) (htH : t ∈ H B),
      θ ⟨t, htH⟩ ∈ centralizer ((L : Subgroup _) : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) →
      orderOf (θ ⟨t, htH⟩) = 2 →
      IsComponent (L.subgroupOf (centralizer ({θ ⟨t, htH⟩} :
        Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))))) := by
    intro t htQ htH htc ht2
    have htB : t ∉ B := by
      intro h
      have h1 : (⟨t, htH⟩ : H B) ∈ criticalOddTwoCore ↥(H B) := by
        have h2 : t ∈ (criticalOddTwoCore ↥(H B)).map (H B).subtype := by
          rw [hNeq]
          exact mem_sup_right h
        obtain ⟨y, hy, hyt⟩ := h2
        have hy' : y = ⟨t, htH⟩ := Subtype.ext hyt
        rwa [← hy']
      have h2 : θ ⟨t, htH⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
      rw [h2, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    have htT : t ∈ normalizer (T B : Set G) := by
      have h1 : t ∈ normalizer ((J ⊓ centralizer (B : Set G) : Subgroup G) : Set G) :=
        UnbalancedLayer.normalizer_inf_mem (hSX (mem_inf.mp htQ).1).2
          (CatalogueBPrimeJoin.normalizer_le_normalizer_centralizer B (mem_inf.mp htQ).2)
      rw [hT B]
      have : (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).Characteristic :=
        CatalogueBPrimeJoin.pLayer_characteristic
      exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _ h1
    have hcθ : ⁅L, zpowers (θ ⟨t, htH⟩)⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer, UnbalancedLayer.centralizer_zpowers_eq]
      intro x hx
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htc x hx)
    have hzt : (zpowers t).subgroupOf (H B) = zpowers (⟨t, htH⟩ : H B) := by
      apply map_injective (H B).subtype_injective
      rw [map_subgroupOf_eq_of_le (zpowers_le.mpr htH), MonoidHom.map_zpowers]
      rfl
    have hcK : ⁅(T B).subgroupOf (H B), zpowers (⟨t, htH⟩ : H B)⁆ ≤
        criticalOddTwoCore ↥(H B) := by
      have h1 : (⁅(T B).subgroupOf (H B), zpowers (⟨t, htH⟩ : H B)⁆).map θ = ⊥ := by
        rw [map_commutator, MonoidHom.map_zpowers]
        exact hcθ
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    have hT₀c : ⁅((T B).subgroupOf (H B)).map π, zpowers (π ⟨t, htH⟩)⁆ = ⊥ := by
      have hT₀perf : Group.IsPerfect ↥(((T B).subgroupOf (H B)).map π) :=
        Subgroup.isPerfect_iff.mpr (by rw [← map_commutator, hT'perf])
      apply LocalCores.perfect_double_commutator hT₀perf
      have h1 : ⁅((T B).subgroupOf (H B)).map π, zpowers (π ⟨t, htH⟩)⁆ ≤
          pCore 2 (↥(H B) ⧸ pPrimeCore 2 ↥(H B)) := by
        rw [← MonoidHom.map_zpowers, ← map_commutator, ← hπK]
        exact map_mono hcK
      rw [← le_bot_iff, ← hOc, commutator_comm]
      exact commutator_mono hT₀U h1
    have hTt : ⁅T B, zpowers t⁆ ≤ R B := by
      rw [hR B]
      apply commutator_le_of_map_eq_bot hTH (zpowers_le.mpr htH)
      rw [hzt, MonoidHom.map_zpowers]
      exact hT₀c
    have htP : t ∈ P := by
      have htriv : ∀ x ∈ X B, x⁻¹ * t⁻¹ * x * t ∈ (pPrimeCore 2 ↥(X B)).map (X B).subtype := by
        intro x hx
        rw [hX B, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right (T B) (R B)
          (hTH.trans hHR)] at hx
        obtain ⟨w, hw, r, hr, rfl⟩ := Set.mem_mul.mp hx
        rw [hOX]
        apply mem_sup_left
        have hcw : w⁻¹ * t⁻¹ * w * t ∈ R B := by
          have h1 := hTt (commutator_mem_commutator (inv_mem hw) (inv_mem (mem_zpowers t)))
          rwa [commutatorElement_def, inv_inv, inv_inv] at h1
        have htr : t⁻¹ * r * t ∈ R B := by
          have h1 := (mem_normalizer_iff.mp (inv_mem (hHR htH)) r).mp hr
          rwa [inv_inv] at h1
        rw [show (w * r)⁻¹ * t⁻¹ * (w * r) * t = r⁻¹ * (w⁻¹ * t⁻¹ * w * t) * (t⁻¹ * r * t) by
          group]
        exact mul_mem (mul_mem (inv_mem hr) hcw) htr
      have h1 := ((hQact t htQ).2.2).mp htriv
      exact (mem_inf.mp h1).1
    set Tt := B ⊔ zpowers t with hTtdef
    have hTtP : Tt ≤ P := sup_le hBP (zpowers_le.mpr htP)
    have hBTt : B < Tt := lt_of_le_of_ne le_sup_left fun h =>
      htB (h ▸ mem_sup_right (mem_zpowers t))
    have hTt1 : Tt ≠ ⊥ := fun h => hB1 (le_bot_iff.mp (h ▸ hBTt.le))
    obtain ⟨hVTH, hVTpc, -, hVTmul, -⟩ := hlarger Tt hTt1 hTtP (Or.inl (card_lt_of_lt hBTt))
    have hTt2 : IsPGroup 2 Tt := hS2.to_le (hTtP.trans (hP.le.trans inf_le_left))
    have hHT : H Tt = normalizer (Tt : Set G) := hH Tt
    have hTtHT : Tt ≤ H Tt := hHT ▸ le_normalizer
    have hTtn : (Tt.subgroupOf (H Tt)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hTtHT).mpr hHT.le
    have hTtb : Group.IsSolvable ↥((Tt.subgroupOf (H Tt)).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(H Tt)))) := by
      have h1 : IsPGroup 2
          ((Tt.subgroupOf (H Tt)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(H Tt)))) :=
        (hTt2.comap_of_injective (H Tt).subtype (H Tt).subtype_injective).map _
      have : Group.IsNilpotent ↥((Tt.subgroupOf (H Tt)).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(H Tt)))) := h1.isNilpotent
      infer_instance
    have hc1 := commutator_map_sup_eq_bot_of_solvable hVTH hVTpc hVTH hVTpc
      (hTtn.map _ (QuotientGroup.mk'_surjective _)) hTtb
    rw [sup_idem] at hc1
    have hc2 : ⁅V Tt, Tt⁆ ≤ R Tt := by
      rw [hR Tt]
      exact commutator_le_of_map_eq_bot hVTH hTtHT hc1
    have hc3 : ⁅V Tt, Tt⁆ ≤ Tt := by
      rw [commutator_comm]
      exact UnbalancedLayer.commutator_le_left_of_le_normalizer (hVTH.trans hHT.le)
    have hRTodd : Nat.Coprime 2 (Nat.card (R Tt)) := by
      rw [hR Tt, card_map_of_injective (subtype_injective _)]
      exact pPrimeCore_coprime_card
    have hRT : R Tt ⊓ Tt = ⊥ := by
      rw [inf_comm]
      exact inf_eq_bot_of_isPGroup_two hTt2 hRTodd
    have hVTc : ⁅V Tt, Tt⁆ = ⊥ := le_bot_iff.mp (hRT ▸ le_inf hc2 hc3)
    have hVTC : V Tt ≤ centralizer (Tt : Set G) := commutator_eq_bot_iff_le_centralizer.mp hVTc
    have hVTHB : V Tt ≤ H B := hVTC.trans ((centralizer_le hBTt.le).trans
      ((centralizer_le_normalizer' B).trans hHB.ge))
    have hTtH : Tt ≤ H B := sup_le hBH (zpowers_le.mpr htH)
    set At := Tt.subgroupOf (H B) with hAtdef
    have hAt2 : IsPGroup 2 At := hTt2.comap_of_injective _ (H B).subtype_injective
    have hAt1 : At ≠ ⊥ := by
      intro h
      apply hTt1
      have h1 := congrArg (Subgroup.map (H B).subtype) h
      rwa [map_subgroupOf_eq_of_le hTtH, Subgroup.map_bot] at h1
    have hBAt : B.subgroupOf (H B) ≤ At := fun x hx => mem_sup_left hx
    have hNAt : normalizer ((At : Subgroup (H B)) : Set (H B)) =
        (normalizer (Tt : Set G) ⊓ H B).subgroupOf (H B) := by
      rw [hAtdef, normalizer_subgroupOf_eq hTtH, inf_subgroupOf_right]
    have hMAt : (V Tt).subgroupOf (H B) ≤ normalizer ((At : Subgroup (H B)) : Set (H B)) := by
      rw [hNAt]
      intro x hx
      exact ⟨centralizer_le_normalizer' _ (hVTC hx), x.2⟩
    have hMAtpc : IsPComponent 2 (((V Tt).subgroupOf (H B)).subgroupOf
        (normalizer ((At : Subgroup (H B)) : Set (H B)))) := by
      rw [hNAt, isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two]
      exact isPComponent_subgroupOf_of_le
        (le_inf (hVTC.trans (centralizer_le_normalizer' _)) hVTHB) (hHT ▸ inf_le_left) hVTpc
    obtain ⟨-, -, -, -, -, -, -, hMcomp, hMO, -⟩ :=
      kGroup_odd_times_two_normalizer_component_transport_of_inputs hS hU hheld hKH
        (B.subgroupOf (H B)) hB2' θ (QuotientGroup.mk'_surjective _) hθker At hAt2 hAt1 hBAt
        ((V Tt).subgroupOf (H B)) hMAt hMAtpc
    have hθAt : At.map θ = zpowers (θ ⟨t, htH⟩) := by
      rw [hAtdef, hTtdef, subgroupOf_sup hBH (zpowers_le.mpr htH), hzt, Subgroup.map_sup,
        MonoidHom.map_zpowers]
      have hBθ : (B.subgroupOf (H B)).map θ = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, hθker]
        exact le_sup_right
      rw [hBθ, bot_sup_eq]
    rw [hθAt, normalizer_zpowers_eq_centralizer ht2] at hMcomp
    obtain ⟨hTTB, -, hXBT⟩ := hA3 B Tt hB1 hBTt.le hTtP
    have hTTV : T Tt ≤ V Tt := by
      obtain ⟨-, -, h, -, -, -⟩ := two_local_conj_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2
        hTt1 (hTtP.trans hP.le) (hT Tt) (hRf Tt) (hX Tt) (by rw [hE, hH]) (hV Tt)
      exact h
    have hNθ : ∀ Y : Subgroup G, Y ≤ (criticalOddTwoCore ↥(H B)).map (H B).subtype →
        (Y.subgroupOf (H B)).map θ = ⊥ := by
      intro Y hY
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hY (mem_subgroupOf.mp hy)
      rwa [← Subtype.ext hzy]
    have hθTT : ((T Tt).subgroupOf (H B)).map θ = L := by
      apply le_antisymm (map_mono (fun x hx => hTTB hx :
        (T Tt).subgroupOf (H B) ≤ (T B).subgroupOf (H B)))
      have h1 : T B ≤ T Tt ⊔ R B := hXBT ▸ (hX B ▸ le_sup_left)
      have hTTH : T Tt ≤ H B := hTTB.trans hTH
      calc L = ((T B).subgroupOf (H B)).map θ := rfl
        _ ≤ ((T Tt ⊔ R B).subgroupOf (H B)).map θ := map_mono (fun x hx => h1 hx)
        _ = ((T Tt).subgroupOf (H B)).map θ := by
          rw [subgroupOf_sup hTTH hRBH, Subgroup.map_sup,
            hNθ (R B) (hNeq ▸ le_sup_left), sup_bot_eq]
    have hθVT : ((V Tt).subgroupOf (H B)).map θ = L := by
      apply le_antisymm _ (hθTT ▸ map_mono (fun x hx => hTTV hx :
        (T Tt).subgroupOf (H B) ≤ (V Tt).subgroupOf (H B)))
      rw [← hθTT]
      set OV := (pPrimeCore 2 ↥(V Tt)).map (V Tt).subtype with hOVdef
      have hOVV : OV ≤ V Tt := map_subtype_le _
      have hTOV : T Tt ⊔ OV = V Tt := by
        apply le_antisymm (sup_le hTTV hOVV)
        intro v hv
        rw [← SetLike.mem_coe, ← hVTmul] at hv
        obtain ⟨x, hx, o, ho, rfl⟩ := Set.mem_mul.mp hv
        exact mul_mem (mem_sup_left hx) (mem_sup_right ho)
      have hOVodd : Nat.Coprime 2 (Nat.card OV) := by
        rw [hOVdef, card_map_of_injective (subtype_injective _)]
        exact pPrimeCore_coprime_card
      have hcOV : ⁅T Tt, OV⁆ ≤ (criticalOddTwoCore ↥(H B)).map (H B).subtype := by
        have hOVH : OV = ((pPrimeCore 2 ↥((V Tt).subgroupOf (H B))).map
            ((V Tt).subgroupOf (H B)).subtype).map (H B).subtype :=
          (pPrimeCore_map_subgroupOf 2 (V Tt) (H B) hVTHB).symm
        have hcen : (((pPrimeCore 2 ↥((V Tt).subgroupOf (H B))).map
            ((V Tt).subgroupOf (H B)).subtype)).map θ ≤
            centralizer ((((V Tt).subgroupOf (H B)).map θ : Subgroup _) : Set _) := by
          rintro _ ⟨o, ⟨o', ho', rfl⟩, rfl⟩
          rw [mem_centralizer_iff]
          rintro _ ⟨m, hm, rfl⟩
          have h1 := mem_center_iff.mp (hMO ⟨o', ho', rfl⟩) ⟨θ m, ⟨m, hm, rfl⟩⟩
          exact congrArg Subtype.val h1
        have hc0 : ⁅((V Tt).subgroupOf (H B)), (pPrimeCore 2 ↥((V Tt).subgroupOf (H B))).map
            ((V Tt).subgroupOf (H B)).subtype⁆ ≤ criticalOddTwoCore ↥(H B) := by
          have h1 : (⁅((V Tt).subgroupOf (H B)), (pPrimeCore 2 ↥((V Tt).subgroupOf (H B))).map
              ((V Tt).subgroupOf (H B)).subtype⁆).map θ = ⊥ := by
            rw [map_commutator, commutator_comm, commutator_eq_bot_iff_le_centralizer]
            exact hcen
          rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
        have h2 := map_mono (f := (H B).subtype) hc0
        rw [map_commutator, map_subgroupOf_eq_of_le hVTHB, ← hOVH] at h2
        exact (commutator_mono hTTV le_rfl).trans h2
      have hres := primeResidual_le_sup_of_commutator_le (hTTV.trans
        (nested_le_normalizer_map_pPrimeCore (V Tt))) hOVodd
        (hTOV.le.trans (hVTHB.trans hHN)) hcOV
      rw [hTOV] at hres
      have hVT2 : CatalogueBPrimeJoin.primeResidual 2 ↥(V Tt) = ⊤ :=
        ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 (V Tt) _ hVTH).mp hVTpc).2.1
      rw [hVT2, ← MonoidHom.range_eq_map, range_subtype] at hres
      have hTTH : T Tt ≤ H B := hTTB.trans hTH
      calc ((V Tt).subgroupOf (H B)).map θ
          ≤ ((T Tt ⊔ (criticalOddTwoCore ↥(H B)).map (H B).subtype).subgroupOf (H B)).map θ :=
            map_mono (fun x hx => hres hx)
        _ = ((T Tt).subgroupOf (H B)).map θ := by
          rw [subgroupOf_sup hTTH hNdef, Subgroup.map_sup, hNθ _ le_rfl, sup_bot_eq]
    rw [hθVT] at hMcomp
    exact hMcomp
  have hXH : X B ≤ H B := by rw [hX B]; exact sup_le hTH hRBH
  have huniv : ∀ u : ↥(H B) ⧸ criticalOddTwoCore ↥(H B),
      u ∈ centralizer ((L : Subgroup _) : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) →
      orderOf u = 2 →
      IsComponent (L.subgroupOf
        (centralizer ({u} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))))) := by
    intro u hu hu2
    have huN : u ∈ normalizer ((L : Subgroup _) : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) :=
      centralizer_le_normalizer L hu
    set Lh := normalizer (((X B).subgroupOf (H B) : Subgroup (H B)) : Set (H B)) with hLhdef
    set Y₁ := (zpowers u).comap θ ⊓ Lh with hY₁def
    let f : ↥Y₁ →* ↥(zpowers u) :=
      (θ.comp Y₁.subtype).codRestrict (zpowers u) (fun y => (mem_inf.mp y.2).1)
    have hf : Function.Surjective f := by
      rintro ⟨v, hv⟩
      have hvN : v ∈ normalizer ((L : Subgroup _) : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) :=
        (zpowers_le.mpr huN) hv
      rw [← hNL] at hvN
      obtain ⟨h, hh, rfl⟩ := hvN
      exact ⟨⟨h, mem_inf.mpr ⟨hv, hh⟩⟩, rfl⟩
    obtain ⟨S₁⟩ : Nonempty (Sylow 2 ↥Y₁) := inferInstance
    have hS₁ : (S₁ : Subgroup ↥Y₁).map f = ⊤ := by
      have h1 := Subgroup.index_map_dvd (H := (S₁ : Subgroup ↥Y₁)) hf
      have h2 : ¬ 2 ∣ (S₁ : Subgroup ↥Y₁).index := S₁.not_dvd_index
      have hU2 : IsPGroup 2 ↥(zpowers u) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
      obtain ⟨k, hk⟩ := hU2.index ((S₁ : Subgroup ↥Y₁).map f)
      rw [hk] at h1
      have hk0 : k = 0 := by
        by_contra hk0
        exact h2 (dvd_trans (dvd_pow_self 2 hk0) h1)
      rw [hk0, pow_zero] at hk
      exact Subgroup.index_eq_one.mp hk
    obtain ⟨s, hs, hsu⟩ : ∃ s : ↥Y₁, s ∈ (S₁ : Subgroup ↥Y₁) ∧ f s = ⟨u, mem_zpowers u⟩ := by
      have h1 : (⟨u, mem_zpowers u⟩ : ↥(zpowers u)) ∈ (S₁ : Subgroup ↥Y₁).map f := by
        rw [hS₁]
        exact mem_top _
      obtain ⟨s, hs, hsu⟩ := h1
      exact ⟨s, hs, hsu⟩
    set S₁G := ((S₁ : Subgroup ↥Y₁).map Y₁.subtype).map (H B).subtype with hS₁Gdef
    have hS₁G2 : IsPGroup 2 S₁G := (S₁.isPGroup'.map _).map _
    have hS₁GL : S₁G ≤ normalizer (B : Set G) ⊓ normalizer (X B : Set G) := by
      rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
      have hyLh : ((y : Y₁) : H B) ∈ Lh := (mem_inf.mp y.2).2
      exact mem_inf.mpr ⟨hHB ▸ ((y : Y₁) : H B).2,
        UnbalancedLayer.mem_normalizer_of_subgroupOf hXH hyLh⟩
    obtain ⟨c, hcL, hcQ⟩ := UnbalancedLayer.exists_conjugate_le_of_sylow hQsyl hS₁GL hS₁G2
    have hsS : (((s : Y₁) : H B) : G) ∈ S₁G := ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have htQ : c⁻¹ * (((s : Y₁) : H B) : G) * c ∈ S ⊓ normalizer (B : Set G) := by
      apply hcQ
      rw [UnbalancedLayer.mem_conjugate_iff]
      rwa [show c * (c⁻¹ * (((s : Y₁) : H B) : G) * c) * c⁻¹ = (((s : Y₁) : H B) : G) by group]
    have hcH : c ∈ H B := hHB ▸ (mem_inf.mp hcL).1
    have htH : c⁻¹ * (((s : Y₁) : H B) : G) * c ∈ H B :=
      mul_mem (mul_mem (inv_mem hcH) ((s : Y₁) : H B).2) hcH
    have hθs : θ ((s : Y₁) : H B) = u := congrArg Subtype.val hsu
    have hθt : θ ⟨c⁻¹ * (((s : Y₁) : H B) : G) * c, htH⟩ =
        (θ ⟨c, hcH⟩)⁻¹ * u * θ ⟨c, hcH⟩ := by
      have h1 : (⟨c⁻¹ * (((s : Y₁) : H B) : G) * c, htH⟩ : H B) =
          (⟨c, hcH⟩ : H B)⁻¹ * ((s : Y₁) : H B) * ⟨c, hcH⟩ := rfl
      rw [h1, map_mul, map_mul, map_inv, hθs]
    have hθcN : θ ⟨c, hcH⟩ ∈
        normalizer ((L : Subgroup _) : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) := by
      rw [← hNL]
      exact ⟨⟨c, hcH⟩, UnbalancedLayer.mem_normalizer_subgroupOf_of_mem (mem_inf.mp hcL).2, rfl⟩
    set d := θ ⟨c, hcH⟩ with hddef
    have hu₁c : θ ⟨c⁻¹ * (((s : Y₁) : H B) : G) * c, htH⟩ ∈
        centralizer ((L : Subgroup _) : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) := by
      rw [hθt, mem_centralizer_iff]
      intro x hx
      have hx' : d * x * d⁻¹ ∈ L := (mem_normalizer_iff.mp hθcN x).mp hx
      have h1 := mem_centralizer_iff.mp hu _ hx'
      calc x * (d⁻¹ * u * d) = d⁻¹ * ((d * x * d⁻¹) * u) * d := by group
        _ = d⁻¹ * (u * (d * x * d⁻¹)) * d := by rw [h1]
        _ = d⁻¹ * u * d * x := by group
    have hu₁2 : orderOf (θ ⟨c⁻¹ * (((s : Y₁) : H B) : G) * c, htH⟩) = 2 := by
      rw [hθt, ← hu2]
      have h1 := orderOf_injective (MulAut.conj d⁻¹).toMonoidHom (MulAut.conj d⁻¹).injective u
      rw [← h1]
      congr 1
      show d⁻¹ * u * d = d⁻¹ * u * d⁻¹⁻¹
      rw [inv_inv]
    have hcomp := hU3 _ htQ htH hu₁c hu₁2
    have hcomp' := isComponent_subgroupOf_conjugate d⁻¹ hcomp
    have hLd : conjugate L d⁻¹ = L :=
      UnbalancedLayer.conjugate_eq_of_mem_normalizer (inv_mem hθcN)
    have hCd : conjugate (centralizer ({θ ⟨c⁻¹ * (((s : Y₁) : H B) : G) * c, htH⟩} :
        Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B)))) d⁻¹ =
        centralizer ({u} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) := by
      rw [← UnbalancedLayer.centralizer_zpowers_eq, conjugate_centralizer, conjugate_zpowers,
        hθt, ← UnbalancedLayer.centralizer_zpowers_eq]
      congr 2
      group
    rw [hLd, hCd] at hcomp'
    exact hcomp'
  have hLq : IsQuasisimple ↥L :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hLN) hLcomp.1
  have hāc : ā ∈ centralizer ((L : Subgroup _) : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hLN hx)
  have hKF : SectionRank.IsKGroupCat (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) := hKH.quotient _
  obtain ⟨E4, hE4, hE4card⟩ := exists_four_of_two_le_pRank hL2
  have hstd : IsStandardSubgroup L := by
    refine hCTI _ hKF L (hLW.trans hWlayer) hLq ⟨E4.map L.subtype, map_subtype_le _,
      IsElementaryAbelian.map _, by rw [card_map_of_injective L.subtype_injective, hE4card]⟩
      ā hāc hā2 huniv ?_
    rw [hncl]
    exact hWa
  exact ⟨⟨hNeq, hRBbot, hRBc, hā2, hVEeq, hVa, hBD, hBsylD, hQL, hQsyl⟩,
    ⟨hLN, hLcomp, hL2, hstd⟩, ⟨hiso, hncl, hWa, hZ⟩, hlarger⟩

end CFSG.ComponentClassification.UnbalancedCorr
