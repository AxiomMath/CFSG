module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerIsoCorrSylowGrowth
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondence

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have h := mem_normalizer_sSup (S := {A, B}) (g := g) (by rintro N (rfl | rfl) <;> assumption)
  rwa [sSup_pair] at h

theorem conjugate_eq_self_of_le_centralizer {T : Subgroup G} {a : G}
    (h : T ≤ centralizer ({a} : Set G)) : conjugate T a = T := by
  ext y
  rw [mem_conjugate_iff]
  constructor
  · intro hy
    have h1 := mem_centralizer_singleton_iff.mp (h hy)
    have h2 : a * y = a * (a * y * a⁻¹) := by
      calc a * y = a * y * a⁻¹ * a := by group
        _ = a * (a * y * a⁻¹) := h1
    rwa [← mul_left_cancel h2] at hy
  · intro hy
    have h1 := mem_centralizer_singleton_iff.mp (h hy)
    rwa [← h1, mul_inv_cancel_right]

theorem conjugate_iSup_conjugate_le {E T : Subgroup G} {g : G}
    (hg : ∀ e ∈ E, ∃ e' ∈ E, conjugate T (e * g) = conjugate T e') :
    conjugate (⨆ e ∈ E, conjugate T e) g ≤ ⨆ e ∈ E, conjugate T e := by
  rw [conjugate, Subgroup.map_iSup]
  refine iSup_le fun e => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun he => ?_
  obtain ⟨e', he', heq⟩ := hg e he
  show conjugate (conjugate T e) g ≤ _
  rw [conjugate_conjugate, heq]
  exact le_iSup₂_of_le e' he' le_rfl

theorem mem_normalizer_iSup_conjugate {E T : Subgroup G} {g : G}
    (h₁ : ∀ e ∈ E, ∃ e' ∈ E, conjugate T (e * g) = conjugate T e')
    (h₂ : ∀ e ∈ E, ∃ e' ∈ E, conjugate T (e * g⁻¹) = conjugate T e') :
    g ∈ normalizer ((⨆ e ∈ E, conjugate T e : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjugate_eq
  apply le_antisymm (conjugate_iSup_conjugate_le h₁)
  have h3 : conjugate (conjugate (⨆ e ∈ E, conjugate T e) g⁻¹) g ≤
      conjugate (⨆ e ∈ E, conjugate T e) g :=
    map_mono (conjugate_iSup_conjugate_le h₂)
  rwa [conjugate_conjugate, inv_mul_cancel, conjugate_one] at h3

theorem mem_normalizer_iSup_conjugate_of_mem {E T : Subgroup G} {g : G} (hg : g ∈ E) :
    g ∈ normalizer ((⨆ e ∈ E, conjugate T e : Subgroup G) : Set G) :=
  mem_normalizer_iSup_conjugate (fun e he => ⟨e * g, mul_mem he hg, rfl⟩)
    (fun e he => ⟨e * g⁻¹, mul_mem he (inv_mem hg), rfl⟩)

theorem mem_normalizer_iSup_conjugate_of_normalizer {E T : Subgroup G} {g : G}
    (hgE : g ∈ normalizer (E : Set G)) (hgT : g ∈ normalizer (T : Set G)) :
    g ∈ normalizer ((⨆ e ∈ E, conjugate T e : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (E : Set G) → g ∈ normalizer (T : Set G) →
      ∀ e ∈ E, ∃ e' ∈ E, conjugate T (e * g) = conjugate T e' := by
    intro g hgE hgT e he
    refine ⟨g⁻¹ * e * g, ?_, ?_⟩
    · have h1 := (mem_normalizer_iff.mp (inv_mem hgE) e).mp he
      rwa [inv_inv] at h1
    · rw [show e * g = g * (g⁻¹ * e * g) by group, ← conjugate_conjugate,
        conjugate_eq_of_mem_normalizer hgT]
  exact mem_normalizer_iSup_conjugate (key g hgE hgT) (key g⁻¹ (inv_mem hgE) (inv_mem hgT))

theorem eq_bot_of_perfect_of_comm {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) : P = ⊥ := by
  rw [← hP, commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact hc y hy x hx

theorem pLayer_two_isPerfect (X : Type*) [Group X] : ⁅pLayer X 2, pLayer X 2⁆ = pLayer X 2 := by
  apply le_antisymm (commutator_le_self _)
  apply sSup_le
  intro M hM
  have : Group.IsPerfect M := CatalogueBAlternating.pComponent_perfect hM
  rw [← Subgroup.commutator_eq_self (H := M)]
  exact commutator_mono (le_sSup hM) (le_sSup hM)

variable [Finite G]

theorem le_of_commutator_map_eq {X : Type*} [Group X] [Finite X] {U R : Subgroup X}
    (hU : IsPComponent 2 U) (hRU : R ≤ normalizer (U : Set X))
    (hUR : U ≤ normalizer (R : Set X))
    (h : ⁅U.map (QuotientGroup.mk' (pPrimeCore 2 X)), R.map (QuotientGroup.mk' (pPrimeCore 2 X))⁆ =
      U.map (QuotientGroup.mk' (pPrimeCore 2 X))) : U ≤ R := by
  obtain ⟨-, -, hUsub, -, -⟩ := id hU
  have hW := eq_of_le_of_map_eq hU (commutator_le_left_of_le_normalizer hRU)
    (commutator_isSubnormal hUsub hRU) (by rw [map_commutator, h])
  rw [← hW, commutator_comm]
  exact commutator_le_left_of_le_normalizer hUR

theorem correspondence_normal_closure {a b : G} {J L : Subgroup G}
    (h : UnbalancedGS.GSCorr a J b L) {E K T : Subgroup G}
    (hE : E = (pLayer ↥(centralizer ({b} : Set G)) 2).map (centralizer ({b} : Set G)).subtype)
    (hK : K = L ⊔ conjugate L a) (hT : T = UnbalancedGS.gsFixedLayer J b) :
    K ≤ E ∧ (K.subgroupOf E).Normal ∧ (⨆ e ∈ E, conjugate T e) = K ∧
      ∀ g ∈ centralizer ({b} : Set G) ⊓ normalizer (J : Set G),
        g ∈ normalizer (K : Set G) ∧
          (fun U => conjugate U g) '' {L, conjugate L a} = {L, conjugate L a} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hE hK hT
  have hcard := UnbalancingLocal.Correspondence.card_gsFixedLayer_quotient h
  have hcmp := UnbalancingLocal.correspondence_quotient_order_comparison h
  obtain ⟨hao, -, hab, hJa, hJ, hLb, hL, -, -, hfix⟩ := h
  set H := centralizer ({b} : Set G) with hHdef
  set E := (pLayer ↥H 2).map H.subtype with hEdef
  set T := UnbalancedGS.gsFixedLayer J b with hTdef
  have haa : a * a = 1 := by rw [← pow_two, ← hao, pow_orderOf_eq_one]
  have haH : a ∈ H := mem_centralizer_singleton_iff.mpr hab
  have hLaH : conjugate L a ≤ H := fun y hy => by
    rw [mem_conjugate_iff] at hy
    have h1 := mul_mem (mul_mem (inv_mem haH) (hLb hy)) haH
    rwa [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at h1
  have hKH : L ⊔ conjugate L a ≤ H := sup_le hLb hLaH
  have hL₂ : IsPComponent 2 ((conjugate L a).subgroupOf H) := by
    have h1 := isPComponent_conjugate hL (⟨a, haH⟩ : H)
    rwa [conjugate_subgroupOf_eq] at h1
  have hLsub : (L.subgroupOf H).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hL
    exact hs
  have hLasub : ((conjugate L a).subgroupOf H).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hL₂
    exact hs
  have hEN : ∀ X : Subgroup H, IsPComponent 2 X → pLayer H 2 ≤ normalizer (X : Set H) := by
    intro X hX
    apply sSup_le
    intro M hM
    by_cases hMX : X = M
    · rw [← hMX]
      exact le_normalizer
    · exact ((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two X M hX
        hM).2 hMX).1
  have hENG : ∀ X : Subgroup G, X ≤ H → IsPComponent 2 (X.subgroupOf H) →
      E ≤ normalizer (X : Set G) := by
    intro X hXH hX y hy
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    exact mem_normalizer_of_subgroupOf hXH (hEN _ hX hy')
  have hENK : E ≤ normalizer ((L ⊔ conjugate L a : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_sup (hENG L hLb hL hy) (hENG _ hLaH hL₂ hy)
  have hL₁E : L.subgroupOf H ≤ pLayer ↥H 2 := le_sSup hL
  have hL₂E : (conjugate L a).subgroupOf H ≤ pLayer ↥H 2 := le_sSup hL₂
  have hKE : L ⊔ conjugate L a ≤ E := by
    apply sup_le
    · intro y hy
      exact ⟨⟨y, hLb hy⟩, hL₁E (show (⟨y, hLb hy⟩ : H) ∈ L.subgroupOf H from hy), rfl⟩
    · intro y hy
      exact ⟨⟨y, hLaH hy⟩,
        hL₂E (show (⟨y, hLaH hy⟩ : H) ∈ (conjugate L a).subgroupOf H from hy), rfl⟩
  have hTKa : T ≤ (L ⊔ conjugate L a) ⊓ centralizer ({a} : Set G) := by
    rw [hfix]
    exact UnbalancedGS.gsFixedLayer_le_inf _ a
  have hTK : T ≤ L ⊔ conjugate L a := hTKa.trans inf_le_left
  have hTH : T ≤ H := hTK.trans hKH
  set S := ⨆ e ∈ E, conjugate T e with hSdef
  have hTS : T ≤ S := by
    have h1 : conjugate T 1 ≤ S := le_iSup₂_of_le (1 : G) (one_mem E) le_rfl
    rwa [conjugate_one] at h1
  have hSK : S ≤ L ⊔ conjugate L a := iSup₂_le fun e he => by
    rw [← conjugate_eq_of_mem_normalizer (hENK he)]
    exact map_mono hTK
  have hES : E ≤ normalizer (S : Set G) := fun g hg => mem_normalizer_iSup_conjugate_of_mem hg
  have hKS : L ⊔ conjugate L a ≤ normalizer (S : Set G) := hKE.trans hES
  have hHE : ∀ g ∈ H, g ∈ normalizer (E : Set G) := by
    intro g hg
    have : (pLayer ↥H 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic H (pLayer ↥H 2)
      (le_normalizer hg)
  have hSH : S ≤ H := hSK.trans hKH
  have hS₁L : S.subgroupOf H ≤ normalizer (L.subgroupOf H : Set H) := fun s hs =>
    mem_normalizer_subgroupOf_of_mem (hENG L hLb hL (hKE (hSK hs)))
  have hL₁S : L.subgroupOf H ≤ normalizer (S.subgroupOf H : Set H) := fun l hl =>
    mem_normalizer_subgroupOf_of_mem (hKS (le_sup_left (a := L) hl))
  have hT₁S₁ : T.subgroupOf H ≤ S.subgroupOf H := fun y hy => hTS hy
  have hTperf : ⁅T, T⁆ = T := by
    rw [hTdef, UnbalancedGS.gsFixedLayer, ← map_commutator, pLayer_two_isPerfect]
  have hT₁perf : ⁅T.subgroupOf H, T.subgroupOf H⁆ = T.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hTH, hTperf]
  have hJnt : Nontrivial (J ⧸ pPrimeCore 2 J) := by
    have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJ).2.2
    have : IsSimpleGroup ((J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J)) := hJq.2.1
    exact (QuotientGroup.mk'_surjective (center (J ⧸ pPrimeCore 2 J))).nontrivial
  have hTnt : (T.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have hTodd : Odd (Nat.card T) := by
      have h1 : Nat.card (T.subgroupOf H) ∣ Nat.card (pPrimeCore 2 H) := card_dvd_of_le hbot
      rw [Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv] at h1
      exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
    have htop : pPrimeCore 2 T = ⊤ := by
      apply eq_top_iff.mpr
      refine le_sSup ⟨inferInstance, ?_⟩
      rw [card_top]
      exact Nat.coprime_two_left.mpr hTodd
    have h1 : Nat.card (T ⧸ pPrimeCore 2 T) = 1 := by
      rw [← index_eq_card, htop, index_top]
    rw [hcard] at h1
    exact (Finite.one_lt_card_iff_nontrivial.mpr hJnt).ne' h1
  have hmain : ⁅(L.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)),
      (S.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H))⁆ =
      (L.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) := by
    set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
    have hle : ⁅(L.subgroupOf H).map π, (S.subgroupOf H).map π⁆ ≤ (L.subgroupOf H).map π :=
      commutator_le_left_of_le_normalizer ((map_mono hS₁L).trans (le_normalizer_map π))
    obtain ⟨Kc, hKc, -, hmapL, -⟩ := id hL
    have hAq : IsQuasisimple ↥((L.subgroupOf H).map π) := by
      rw [hmapL]
      exact hKc.1
    have hAperf : ⁅(L.subgroupOf H).map π, (L.subgroupOf H).map π⁆ = (L.subgroupOf H).map π :=
      Subgroup.isPerfect_iff.mp hAq.1
    by_cases hLa : conjugate L a = L
    ·
      have hSL : S.subgroupOf H ≤ L.subgroupOf H := fun y hy => by
        have := hSK hy
        rwa [hLa, sup_idem] at this
      have hnorm : (((S.subgroupOf H).map π).subgroupOf ((L.subgroupOf H).map π)).Normal := by
        rw [normal_subgroupOf_iff_le_normalizer (map_mono hSL)]
        exact (map_mono hL₁S).trans (le_normalizer_map π)
      rcases quasisimple_normal_subgroups hAq hnorm with htop | hcen
      · have hSLeq : (S.subgroupOf H).map π = (L.subgroupOf H).map π :=
          le_antisymm (map_mono hSL) ((subgroupOf_eq_top (H := (S.subgroupOf H).map π)
            (K := (L.subgroupOf H).map π)).mp htop)
        rw [hSLeq, hAperf]
      · exfalso
        apply hTnt
        apply eq_bot_of_perfect_of_comm (by rw [← map_commutator, hT₁perf])
        intro x hx y hy
        have hxS := map_mono hT₁S₁ hx
        have hyL : y ∈ (L.subgroupOf H).map π := map_mono (hT₁S₁.trans hSL) hy
        have hxc := hcen (show (⟨x, map_mono hSL hxS⟩ : ↥((L.subgroupOf H).map π)) ∈
          ((S.subgroupOf H).map π).subgroupOf ((L.subgroupOf H).map π) from hxS)
        have := congrArg Subtype.val ((mem_center_iff.mp hxc) ⟨y, hyL⟩)
        exact this.symm
    ·
      obtain ⟨α, hαk, -, hcomm, -, -, -, -, hmemT, -⟩ := hcmp.2.2.1 hLa haH
      have hαB : ∀ u : ↥(UnbalancingLocal.corrImage b L ⊔
          UnbalancingLocal.corrImage b (conjugate L a)),
          (u : UnbalancingLocal.CorrQuotient b) ∈ UnbalancingLocal.corrImage b L →
          ((α u : ↥(UnbalancingLocal.corrImage b L ⊔
            UnbalancingLocal.corrImage b (conjugate L a))) : UnbalancingLocal.CorrQuotient b) ∈
            UnbalancingLocal.corrImage b (conjugate L a) := by
        intro u hu
        rw [hαk u]
        obtain ⟨l, hl, hlu⟩ := mem_map.mp hu
        refine ⟨⟨a, haH⟩ * l * ⟨a, haH⟩⁻¹, ?_, ?_⟩
        · show ((⟨a, haH⟩ * l * ⟨a, haH⟩⁻¹ : H) : G) ∈ conjugate L a
          rw [mem_conjugate_iff]
          have hl' : (l : G) ∈ L := hl
          rwa [show a * ((⟨a, haH⟩ * l * ⟨a, haH⟩⁻¹ : H) : G) * a⁻¹ = (l : G) by
            simp only [coe_mul, coe_inv]
            rw [show a * (a * (l : G) * a⁻¹) * a⁻¹ = (a * a) * l * (a * a)⁻¹ by group, haa]
            group]
        · rw [map_mul, map_mul, map_inv, hlu]
          rfl
      apply le_antisymm hle
      calc (L.subgroupOf H).map π = ⁅(L.subgroupOf H).map π, (L.subgroupOf H).map π⁆ :=
            hAperf.symm
        _ ≤ ⁅(L.subgroupOf H).map π, (S.subgroupOf H).map π⁆ := by
          rw [commutator_le]
          intro v hv u hu
          have hu' : u ∈ UnbalancingLocal.corrImage b L ⊔
              UnbalancingLocal.corrImage b (conjugate L a) := le_sup_left (a :=
                UnbalancingLocal.corrImage b L) hu
          have hΔ : u * ((α ⟨u, hu'⟩ : ↥(UnbalancingLocal.corrImage b L ⊔
              UnbalancingLocal.corrImage b (conjugate L a))) : UnbalancingLocal.CorrQuotient b) ∈
              (T.subgroupOf H).map π := (hmemT _).mpr ⟨⟨u, hu'⟩, hu, rfl⟩
          have hw := hαB ⟨u, hu'⟩ hu
          set w := ((α ⟨u, hu'⟩ : ↥(UnbalancingLocal.corrImage b L ⊔
            UnbalancingLocal.corrImage b (conjugate L a))) : UnbalancingLocal.CorrQuotient b)
          have hvw : v * w = w * v := hcomm v hv w hw
          have hwv : w * v⁻¹ = v⁻¹ * w := by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hvw, inv_mul_cancel_left]
          have hid : ⁅v, u⁆ = ⁅v, u * w⁆ := by
            rw [commutatorElement_def, commutatorElement_def]
            calc v * u * v⁻¹ * u⁻¹ = v * u * (v⁻¹ * w) * w⁻¹ * u⁻¹ := by group
              _ = v * u * (w * v⁻¹) * w⁻¹ * u⁻¹ := by rw [hwv]
              _ = v * (u * w) * v⁻¹ * (u * w)⁻¹ := by group
          rw [hid]
          exact commutator_mem_commutator hv (map_mono hT₁S₁ hΔ)
  have hLS₁ := le_of_commutator_map_eq hL hS₁L hL₁S hmain
  have hLS : L ≤ S := fun y hy =>
    hLS₁ (show (⟨y, hLb hy⟩ : H) ∈ L.subgroupOf H from hy)
  have haT : a ∈ normalizer (T : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_le_centralizer (hTKa.trans inf_le_right))
  have haS : a ∈ normalizer (S : Set G) :=
    mem_normalizer_iSup_conjugate_of_normalizer (hHE a haH) haT
  have hLaS : conjugate L a ≤ S := by
    rw [← conjugate_eq_of_mem_normalizer haS]
    exact map_mono hLS
  have hSeq : S = L ⊔ conjugate L a := le_antisymm hSK (sup_le hLS hLaS)
  have hgK : ∀ g ∈ H ⊓ normalizer (J : Set G),
      g ∈ normalizer ((L ⊔ conjugate L a : Subgroup G) : Set G) := by
    intro g hg
    obtain ⟨hgH, hgJ⟩ := mem_inf.mp hg
    have : (pLayer ↥(J ⊓ H) 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    have hgT : g ∈ normalizer (T : Set G) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic (J ⊓ H) (pLayer ↥(J ⊓ H) 2)
        (normalizer_inf_mem hgJ (le_normalizer hgH))
    rw [← hSeq]
    exact mem_normalizer_iSup_conjugate_of_normalizer (hHE g hgH) hgT
  have hmaps : ∀ g ∈ H ⊓ normalizer (J : Set G), ∀ U ∈ ({L, conjugate L a} : Set (Subgroup G)),
      conjugate U g ∈ ({L, conjugate L a} : Set (Subgroup G)) := by
    intro g hg U hU
    have hgH : g ∈ H := (mem_inf.mp hg).1
    have hUH : U ≤ H := by
      rcases hU with rfl | rfl
      · exact hLb
      · exact hLaH
    have hUc : IsPComponent 2 (U.subgroupOf H) := by
      rcases hU with rfl | rfl
      · exact hL
      · exact hL₂
    have hUgH : conjugate U g ≤ H := fun y hy => by
      rw [mem_conjugate_iff] at hy
      have h1 := mul_mem (mul_mem (inv_mem hgH) (hUH hy)) hgH
      rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
    have hUg : IsPComponent 2 ((conjugate U g).subgroupOf H) := by
      have h1 := isPComponent_conjugate hUc (⟨g, hgH⟩ : H)
      rwa [conjugate_subgroupOf_eq] at h1
    have hUK : conjugate U g ≤ L ⊔ conjugate L a := by
      rw [← conjugate_eq_of_mem_normalizer (hgK g hg)]
      refine map_mono ?_
      rcases hU with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    have heq : ∀ X : Subgroup G, X ≤ H → IsPComponent 2 (X.subgroupOf H) → conjugate U g ≤ X →
        conjugate U g = X := by
      intro X hXH hX hle
      have h1 := CatalogueBPrimeJoin.eq_of_le 2 _ _ hUg hX (fun y hy => hle hy)
      rw [subgroupOf_inj, inf_of_le_left hUgH, inf_of_le_left hXH] at h1
      exact h1
    rcases le_or_le_of_le_sup hUgH hUg hLb hLaH hLsub hLasub hUK with hle | hle
    · exact Or.inl (heq L hLb hL hle)
    · exact Or.inr (heq _ hLaH hL₂ hle)
  refine ⟨hKE, (normal_subgroupOf_iff_le_normalizer hKE).mpr hENK, hSeq, fun g hg => ⟨hgK g hg, ?_⟩⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨U, hU, rfl⟩
    exact hmaps g hg U hU
  · intro U hU
    have hg' : g⁻¹ ∈ H ⊓ normalizer (J : Set G) := inv_mem hg
    refine ⟨conjugate U g⁻¹, hmaps g⁻¹ hg' U hU, ?_⟩
    show conjugate (conjugate U g⁻¹) g = U
    rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]

end CFSG.ComponentClassification.UnbalancedCorr
