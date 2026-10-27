module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolMirror
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.Sporadic.Recognition.ONMultiplierCert

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Blueprint.NativeSporadic (IsSporadic)

theorem isSporadic_pPrimeCore_of_fusionZStar_on
    {Λ : Type} [Group Λ] [Finite Λ] (hperf : Group.IsPerfect Λ)
    (h : IsSporadic (Λ ⧸ Open.fusionZStar Λ) .ONan) : IsSporadic (Λ ⧸ pPrimeCore 2 Λ) .ONan := by
  obtain ⟨eS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar Λ
  obtain ⟨f⟩ := h
  have hc : center (Λ ⧸ pPrimeCore 2 Λ) = ⊥ :=
    Sporadic.Recognition.ONMultiplier.center_eq_bot_of_certificate inferInstance
      (FooteLit.isPGroup_center_quotient_pPrimeCore Λ) (eS.trans f)
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc).symm).trans
    (eS.trans f)⟩

theorem center_eq_bot_of_isComponent_on
    {X : Type} [Group X] [Finite X] (hO : pPrimeCore 2 X = ⊥)
    {L : Subgroup X} (hL : IsComponent L) (hLON : IsSporadic (↥L ⧸ center ↥L) .ONan) :
    center ↥L = ⊥ := by
  obtain ⟨f⟩ := hLON
  exact Sporadic.Recognition.ONMultiplier.center_eq_bot_of_certificate hL.1.1
    (Sol78.center_isPGroup_two (pPrimeCore_eq_bot_of_isSubnormal hO hL.2)) f

structure ONanWConfig (G : Type) [Group G] [Finite G] (t : G) (P W : Subgroup G) : Prop where
  base : L34BaseSetting G
  order_two : orderOf t = 2
  le_centralizer : P ≤ centralizer ({t} : Set G)
  isPComponent : IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set G)))
  normal : (P.subgroupOf (centralizer ({t} : Set G))).Normal
  mirror : FooteLit.GSMirrorMaximal P
  isSporadic : IsSporadic (P ⧸ Open.fusionZStar P) .ONan
  odd : Odd (Nat.card W)
  ne_bot : W ≠ ⊥
  le_normalizer : normalizer (P : Set G) ≤ normalizer (W : Set G)
  wGroup_eq : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → IsElemTwo E → 8 ≤ Nat.card E →
    wGroup E = W

namespace ONanWConfig

variable {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G}

theorem gwTwoBalanced (hc : ONanWConfig G t P W) : GWTwoBalanced G :=
  gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hc.base.2.2.2.2.2.1

theorem centralizer_le (hc : ONanWConfig G t P W) :
    centralizer ({t} : Set G) ≤ normalizer (W : Set G) :=
  ((normal_subgroupOf_iff_le_normalizer hc.le_centralizer).mp hc.normal).trans
    hc.le_normalizer

theorem mem_normalizer (hc : ONanWConfig G t P W) : t ∈ normalizer (W : Set G) :=
  hc.centralizer_le (mem_centralizer_singleton_iff.mpr rfl)

theorem le_normalizer' (hc : ONanWConfig G t P W) : P ≤ normalizer (W : Set G) :=
  hc.le_centralizer.trans hc.centralizer_le

theorem normalizer_ne_top (hc : ONanWConfig G t P W) : normalizer (W : Set G) ≠ ⊤ := by
  intro hMt
  have hWn : W.Normal := ⟨fun n hn g => by
    have hg : g ∈ normalizer (W : Set G) := hMt ▸ mem_top g
    exact (mem_normalizer_iff.mp hg n).mp hn⟩
  have := hc.base.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
  · exact hc.ne_bot h
  · have h2 : 2 ∣ Nat.card W := by
      rw [h, card_top, ← hc.order_two]
      exact orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.mpr hc.odd) (even_iff_two_dvd.mpr h2)

theorem isKGroupCat (hc : ONanWConfig G t P W) :
    SectionRank.IsKGroupCat ↥(normalizer (W : Set G)) :=
  UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
    (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hc.base.2.2.1
    _ hc.normalizer_ne_top

theorem centralizer_le_normalizer (hc : ONanWConfig G t P W) :
    centralizer ({t} : Set G) ≤ normalizer (P : Set G) :=
  (normal_subgroupOf_iff_le_normalizer hc.le_centralizer).mp hc.normal

theorem isPerfect (hc : ONanWConfig G t P W) : Group.IsPerfect ↥P := by
  have := CatalogueBAlternating.pComponent_perfect hc.isPComponent
  exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hc.le_centralizer).toMonoidHom)
    (subgroupOfEquivOfLe hc.le_centralizer).surjective

theorem isSporadic_pPrimeCore
    (hc : ONanWConfig G t P W) : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan :=
  isSporadic_pPrimeCore_of_fusionZStar_on hc.isPerfect hc.isSporadic

end ONanWConfig

private theorem le_pPrimeCore_two_of_normal {X : Type*} [Group X] {K : Subgroup X} (hK : K.Normal)
    (hodd : Nat.Coprime 2 (Nat.card K)) : K ≤ pPrimeCore 2 X := by
  unfold pPrimeCore
  exact le_sSup ⟨hK, hodd⟩

private theorem inf_oddIn_le_oddIn {G : Type*} [Group G] [Finite G] {P M : Subgroup G}
    (hPM : P ≤ M) : P ⊓ oddIn M ≤ oddIn P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro c ⟨hcP, hcO⟩
  set K : Subgroup ↥P := (P ⊓ oddIn M).subgroupOf P with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk x => ?_⟩
    rw [hK, mem_subgroupOf] at hk ⊢
    obtain ⟨-, hkO⟩ := mem_inf.mp hk
    refine mem_inf.mpr ⟨(x * k * x⁻¹).2, ?_⟩
    obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp hkO
    have hyk' : (y : G) = k := hyk
    refine Subgroup.mem_map.mpr ⟨⟨(x : G), hPM x.2⟩ * y * ⟨(x : G), hPM x.2⟩⁻¹,
      (pPrimeCore_normal (p := 2) (G := ↥M)).conj_mem y hy _, ?_⟩
    simp [hyk']
  have hKodd : Nat.Coprime 2 (Nat.card K) := by
    have hcardK : Nat.card K = Nat.card ↥(P ⊓ oddIn M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hdvd : Nat.card K ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [hcardK]
      refine (Subgroup.card_dvd_of_le inf_le_right).trans ?_
      rw [oddIn, Subgroup.card_map_of_injective M.subtype_injective]
    exact Nat.Coprime.coprime_dvd_right hdvd (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have hcK : (⟨c, hcP⟩ : ↥P) ∈ K := by
    rw [hK, mem_subgroupOf]
    exact ⟨hcP, hcO⟩
  exact Subgroup.mem_map.mpr ⟨⟨c, hcP⟩, le_pPrimeCore_two_of_normal hKn hKodd hcK, rfl⟩

theorem commutator_mem_oddIn_of_centralizes
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G} (hc : ONanWConfig G t P W)
    (hM : M = normalizer (W : Set G)) (htM : t ∈ M)
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)}
    (hPL : (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤
      L ⊔ L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom)
    {v : G} (hvM : v ∈ M) (htv : t * v = v * t)
    (hvL : ∀ y ∈ L ⊔ L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom,
        QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨v, hvM⟩ * y =
          y * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨v, hvM⟩) :
    ∀ p ∈ P, p⁻¹ * v⁻¹ * p * v ∈ oddIn P := by
  intro p hp
  have hPM : P ≤ M := hM ▸ hc.le_normalizer'
  have hvN : v ∈ normalizer (P : Set G) :=
    hc.centralizer_le_normalizer (mem_centralizer_singleton_iff.mpr htv.symm)
  have hcP : p⁻¹ * v⁻¹ * p * v ∈ P := by
    have h1 : v⁻¹ * p * v⁻¹⁻¹ ∈ P := (mem_normalizer_iff.mp (inv_mem hvN) p).mp hp
    rw [inv_inv] at h1
    have h2 := mul_mem (inv_mem hp) h1
    rwa [← mul_assoc, ← mul_assoc] at h2
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set p' : ↥M := ⟨p, hPM hp⟩ with hp'
  set v' : ↥M := ⟨v, hvM⟩ with hv'
  have hpL : π p' ∈ L ⊔ L.map (MulAut.conj (π ⟨t, htM⟩)).toMonoidHom :=
    hPL (Subgroup.mem_map_of_mem _ (mem_subgroupOf.mpr hp))
  have hcomm := hvL _ hpL
  have hker : p'⁻¹ * v'⁻¹ * p' * v' ∈ pPrimeCore 2 ↥M := by
    have h2 : π (v'⁻¹ * p' * v') = π p' := by
      rw [map_mul, map_mul, map_inv, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    have h1 : π (p'⁻¹ * v'⁻¹ * p' * v') = 1 := by
      rw [show p'⁻¹ * v'⁻¹ * p' * v' = p'⁻¹ * (v'⁻¹ * p' * v') by group, map_mul, h2, map_inv,
        inv_mul_cancel]
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥M)]
    exact h1
  have hcO : p⁻¹ * v⁻¹ * p * v ∈ oddIn M :=
    Subgroup.mem_map.mpr ⟨_, hker, rfl⟩
  exact inf_oddIn_le_oddIn hPM ⟨hcP, hcO⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
