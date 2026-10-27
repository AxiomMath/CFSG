module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6LambdaDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Bal
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Equiv
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Sylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Reduce
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Tools

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

private theorem l1_isPGroup_zpowers {G : Type} [Group G] {a : G} {k : ℕ}
    (ha : a ^ (2 ^ k) = 1) : IsPGroup 2 (zpowers a) := fun g => by
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp g.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    ha, one_zpow, OneMemClass.coe_one]

private theorem l1_centralizer_zpowers {G : Type} [Group G] (a : G) :
    centralizer (zpowers a : Set G) = centralizer ({a} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

private theorem l1_mk_eq_one_iff {X : Type} [Group X] {C : Subgroup X} (x : ↥C) :
    QuotientGroup.mk' (pPrimeCore 2 ↥C) x = 1 ↔ (x : X) ∈ oddCoreOf C := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨x', hx', hxx'⟩
    rw [show x = x' from (Subtype.ext hxx').symm]
    exact hx'

private theorem l1_center_eq_bot_of_simple {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
    exact hp IsSimpleGroup.prime_card

private theorem l1_center_eq_bot_of_mcl {Q : Type} [Group Q]
    (e : Q ≃* Blueprint.NativeSporadic.McL) : center Q = ⊥ := by
  have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.McL.isSimpleGroup_McL e
  refine l1_center_eq_bot_of_simple ?_
  rw [Nat.card_congr e.toEquiv, Sporadic.McL.card_McL]
  norm_num

private theorem l1_center_eq_bot_of_ly {Q : Type} [Group Q]
    (e : Q ≃* Blueprint.NativeSporadic.Ly) : center Q = ⊥ := by
  have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Ly.isSimpleGroup_Ly e
  refine l1_center_eq_bot_of_simple ?_
  rw [Nat.card_congr e.toEquiv, Sporadic.Ly.card_Ly']
  norm_num

private theorem l1_le_normalizer {X : Type} [Group X] [Finite X] {n : ℕ} {H L : Subgroup X}
    (hL : Sec6MComp X n H L) : Sec6M X n H ≤ normalizer (L : Set X) := by
  refine sSup_le fun L' (hL' : Sec6MComp X n H L') => ?_
  by_cases h : L' = L
  · rw [h]
    exact le_normalizer
  · have hne : L'.subgroupOf H ≠ L.subgroupOf H := by
      intro he
      apply h
      rw [Subgroup.subgroupOf_inj, inf_of_le_left hL'.1.1.1, inf_of_le_left hL.1.1.1] at he
      exact he
    obtain ⟨-, h2, -⟩ :=
      (ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
        Nat.prime_two _ _ hL'.1.1.2 hL.1.1.2).2 hne
    intro x hx
    have hxH : x ∈ H := hL'.1.1.1 hx
    have h3 : (⟨x, hxH⟩ : ↥H) ∈ normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
      h2 (show (⟨x, hxH⟩ : ↥H) ∈ L'.subgroupOf H from hx)
    rw [← Subgroup.subgroupOf_normalizer_eq hL.1.1.1] at h3
    exact h3

private theorem l1_exists_conj {X : Type} [Group X] [Finite X] {A N : Subgroup X}
    (hAN : A ≤ normalizer (N : Set X)) (hN : Odd (Nat.card N)) {x : X} (hx : x ∈ A ⊔ N) {j : ℕ}
    (hxj : x ^ (2 ^ j) = 1) : ∃ o ∈ N, ∃ a ∈ A, a ^ (2 ^ j) = 1 ∧ x = o * a * o⁻¹ := by
  set D : Subgroup X := normalizer (N : Set X) with hD
  have hND : N ≤ D := Subgroup.le_normalizer
  have hMn : (N.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hND).2 le_rfl
  have hxD : x ∈ D := (sup_le hAN hND) hx
  have hxAN : (⟨x, hxD⟩ : D) ∈ A.subgroupOf D ⊔ N.subgroupOf D := by
    rw [← Subgroup.subgroupOf_sup hAN hND]
    exact hx
  have hN' : Odd (Nat.card (N.subgroupOf D)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hND).toEquiv]
    exact hN
  obtain ⟨o, ho, a, ha, hak, hxa⟩ :=
    exists_conj_twoElt_of_mem_sup_odd (A := A.subgroupOf D) (N := N.subgroupOf D) hN' hxAN
      (j := j) (Subtype.ext hxj)
  exact ⟨(o : X), Subgroup.mem_subgroupOf.1 ho, (a : X), Subgroup.mem_subgroupOf.1 ha,
    congrArg Subtype.val hak, congrArg Subtype.val hxa⟩

private theorem l1_decomp {G : Type} [Group G] (W : Subgroup G) (s : Set (Subgroup G))
    (hs : s.Finite) :
    (∀ M ∈ s, ∀ z ∈ M, (∀ y ∈ M, z * y = y * z) → z = 1) →
    (∀ M ∈ s, ∀ M' ∈ s, M ≠ M' → M' ≤ centralizer (M : Set G)) →
    ∀ β ∈ sSup s, (∀ M ∈ s, ∀ z ∈ M, z * β = β * z → (∃ k : ℕ, z ^ (2 ^ k) = 1) → z ∈ W) →
    ∀ x ∈ sSup s, x * β = β * x → ∀ j : ℕ, x ^ (2 ^ j) = 1 → x ∈ W := by
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    intro _ _ β _ _ x hx _ _ _
    rw [sSup_empty, mem_bot] at hx
    rw [hx]
    exact W.one_mem
  | @insert M s hMs hs ih =>
    intro hZ hc β hβ hW x hx hxβ j hxj
    have hMmem : M ∈ insert M s := Set.mem_insert M s
    have hEC : sSup s ≤ centralizer (M : Set G) := sSup_le fun M' hM' =>
      hc M hMmem M' (Set.mem_insert_of_mem M hM') (fun h => hMs (h ▸ hM'))
    have hME : M ≤ normalizer ((sSup s : Subgroup G) : Set G) :=
      (le_centralizer_iff.mp hEC).trans (centralizer_le_normalizer _)
    have hdec : ∀ y ∈ sSup (insert M s), ∃ m ∈ M, ∃ e ∈ sSup s, m * e = y := by
      intro y hy
      rw [sSup_insert] at hy
      have hy' : y ∈ ((M ⊔ sSup s : Subgroup G) : Set G) := hy
      rw [coe_mul_of_left_le_normalizer_right _ _ hME] at hy'
      exact hy'
    have hme : ∀ m ∈ M, ∀ e ∈ sSup s, m * e = e * m := fun m hm e he =>
      mem_centralizer_iff.mp (hEC he) m hm
    have hME1 : ∀ z ∈ M, z ∈ sSup s → z = 1 := fun z hzM hzE =>
      hZ M hMmem z hzM fun y hy => (mem_centralizer_iff.mp (hEC hzE) y hy).symm
    obtain ⟨m', hm', e', he', rfl⟩ := hdec β hβ
    obtain ⟨m, hm, e, he, rfl⟩ := hdec x hx
    have h1 : m * m' * (e * e') = m' * m * (e' * e) := by
      have e1 : m * e * (m' * e') = m * m' * (e * e') := by
        calc m * e * (m' * e') = m * (e * m') * e' := by group
          _ = m * (m' * e) * e' := by rw [← hme m' hm' e he]
          _ = m * m' * (e * e') := by group
      have e2 : m' * e' * (m * e) = m' * m * (e' * e) := by
        calc m' * e' * (m * e) = m' * (e' * m) * e := by group
          _ = m' * (m * e') * e := by rw [← hme m hm e' he']
          _ = m' * m * (e' * e) := by group
      rw [← e1, ← e2]
      exact hxβ
    have hw : (m' * m)⁻¹ * (m * m') = 1 := by
      apply hME1
      · exact mul_mem (inv_mem (mul_mem hm' hm)) (mul_mem hm hm')
      · have h2 : (m' * m)⁻¹ * (m * m') = (e' * e) * (e * e')⁻¹ := by
          calc (m' * m)⁻¹ * (m * m') = (m' * m)⁻¹ * (m * m' * (e * e')) * (e * e')⁻¹ := by
                group
            _ = (m' * m)⁻¹ * (m' * m * (e' * e)) * (e * e')⁻¹ := by rw [h1]
            _ = (e' * e) * (e * e')⁻¹ := by group
        rw [h2]
        exact mul_mem (mul_mem he' he) (inv_mem (mul_mem he he'))
    have hmm' : m * m' = m' * m := (inv_mul_eq_one.mp hw).symm
    have hee' : e * e' = e' * e := by
      have h2 : m * m' * (e * e') = m * m' * (e' * e) := by rw [h1, hmm']
      exact mul_left_cancel h2
    have h3 : m ^ (2 ^ j) * e ^ (2 ^ j) = 1 := by
      rw [← (show Commute m e from hme m hm e he).mul_pow]
      exact hxj
    have hmj : m ^ (2 ^ j) = 1 := by
      apply hME1 _ (pow_mem hm _)
      rw [eq_inv_of_mul_eq_one_left h3]
      exact inv_mem (pow_mem he _)
    have hej : e ^ (2 ^ j) = 1 := by
      rw [hmj, one_mul] at h3
      exact h3
    have hmW : m ∈ W := by
      refine hW M hMmem m hm ?_ ⟨j, hmj⟩
      calc m * (m' * e') = m * m' * e' := by group
        _ = m' * m * e' := by rw [hmm']
        _ = m' * (m * e') := by group
        _ = m' * (e' * m) := by rw [hme m hm e' he']
        _ = m' * e' * m := by group
    have heW : e ∈ W := by
      refine ih (fun M'' hM'' => hZ M'' (Set.mem_insert_of_mem M hM''))
        (fun M₁ h₁ M₂ h₂ hne =>
          hc M₁ (Set.mem_insert_of_mem M h₁) M₂ (Set.mem_insert_of_mem M h₂) hne)
        e' he' ?_ e he hee' j hej
      intro M'' hM'' z hz hze' hz2
      refine hW M'' (Set.mem_insert_of_mem M hM'') z hz ?_ hz2
      have hzm' : z * m' = m' * z :=
        (mem_centralizer_iff.mp (hEC (le_sSup hM'' hz)) m' hm').symm
      calc z * (m' * e') = z * m' * e' := by group
        _ = m' * z * e' := by rw [hzm']
        _ = m' * (z * e') := by group
        _ = m' * (e' * z) := by rw [hze']
        _ = m' * e' * z := by group
    exact mul_mem hmW heW

private theorem l1_le_centralizer_layer {G : Type} [Group G] [Finite G]
    {𝓕 : Set (Subgroup G)} (h𝓕 : ∀ F ∈ 𝓕, IsComponent F) {β : G} (hβ : β ∈ sSup 𝓕)
    (hβ2 : β ^ 2 = 1) {P : Subgroup G} (hPodd : Odd (Nat.card P))
    (hPβ : P ≤ centralizer ({β} : Set G))
    (hPn : centralizer ({β} : Set G) ≤ normalizer (P : Set G))
    (hkey : ∀ F ∈ 𝓕, P ≤ normalizer (F : Set G) → P ≤ centralizer (F : Set G)) :
    P ≤ centralizer (layer G : Set G) := by
  rw [le_centralizer_iff, layer.eq_sSup]
  refine sSup_le fun F (hF : IsComponent F) => le_centralizer_iff.mp ?_
  have hother : ∀ K ∈ 𝓕, K ≠ F → K ≤ centralizer (F : Set G) := fun K hK hKF =>
    commutator_eq_bot_iff_le_centralizer.mp
      ((LocalCores.distinct_components_commute (h𝓕 K hK) hF).resolve_left hKF)
  by_cases hβF : β ∈ centralizer (F : Set G)
  ·
    have hFβ : F ≤ centralizer ({β} : Set G) := fun f hf =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hβF f hf)
    have hFc : IsComponent (F.subgroupOf (centralizer ({β} : Set G))) :=
      LocalCores.component_overgroup hF hFβ
    have hPnH : (P.subgroupOf (centralizer ({β} : Set G))).Normal :=
      (normal_subgroupOf_iff_le_normalizer hPβ).mpr hPn
    have hsolv : Group.IsSolvable ↥(P.subgroupOf (centralizer ({β} : Set G))) := by
      refine CFSG.FeitThompson.isSolvable_of_odd_natCard _ ?_
      rw [Nat.card_congr (subgroupOfEquivOfLe hPβ).toEquiv]
      exact hPodd
    have hcomm := (LocalCores.component_solvable_centralizer hsolv hPnH.isSubnormal).1 _ hFc
    intro p hp
    rw [mem_centralizer_iff]
    intro f hf
    have h1 := commutator_eq_bot_iff_le_centralizer.mp hcomm
      (show (⟨f, hFβ hf⟩ : centralizer ({β} : Set G)) ∈ F.subgroupOf _ from hf)
    have h2 := mem_centralizer_iff.mp h1 ⟨p, hPβ hp⟩ hp
    exact (congrArg Subtype.val h2).symm
  ·
    have hF𝓕 : F ∈ 𝓕 := by
      by_contra hn
      exact hβF ((sSup_le fun K hK => hother K hK fun h => hn (h ▸ hK)) hβ)
    refine hkey F hF𝓕 ?_
    have hEF : sSup {K | K ∈ 𝓕 ∧ K ≠ F} ≤ centralizer (F : Set G) :=
      sSup_le fun K hK => hother K hK.1 hK.2
    have hle : sSup 𝓕 ≤ F ⊔ sSup {K | K ∈ 𝓕 ∧ K ≠ F} := sSup_le fun K hK => by
      by_cases h : K = F
      · exact h ▸ le_sup_left
      · exact le_sup_of_le_right (le_sSup ⟨hK, h⟩)
    have hβFE : β ∈ ((F ⊔ sSup {K | K ∈ 𝓕 ∧ K ≠ F} : Subgroup G) : Set G) := hle hβ
    rw [coe_mul_of_left_le_normalizer_right _ _
      ((le_centralizer_iff.mp hEF).trans (centralizer_le_normalizer _))] at hβFE
    obtain ⟨c, hc, e, he, rfl⟩ := hβFE
    have heF : e ∈ centralizer (F : Set G) := hEF he
    have hce : c * e = e * c := mem_centralizer_iff.mp heF c hc
    have hcβ : c ∈ centralizer ({c * e} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc c * (c * e) = c * (e * c) := by rw [hce]
        _ = c * e * c := by group
    have hc2 : c ^ 2 ∈ centralizer (F : Set G) := by
      have h1 : c ^ 2 * e ^ 2 = 1 := by
        rw [← (show Commute c e from hce).mul_pow]
        exact hβ2
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (pow_mem heF 2)
    have hcZ : c ∉ centralizer (F : Set G) := fun h => hβF (mul_mem h heF)
    obtain ⟨m, hm, k, hk⟩ := exists_odd_pow_twoElt c
    have hcmZ : c ^ m ∉ centralizer (F : Set G) := by
      intro h
      obtain ⟨r, rfl⟩ := hm
      apply hcZ
      have hcr : c = ((c ^ 2) ^ r)⁻¹ * c ^ (2 * r + 1) := by
        rw [pow_succ c (2 * r), pow_mul c 2 r, inv_mul_cancel_left]
      rw [hcr]
      exact mul_mem (inv_mem (pow_mem hc2 r)) h
    exact le_normalizer_component_of_odd hPodd hPβ hPn hF (pow_mem hc m) (pow_mem hcβ m) hk
      hcmZ

private theorem l1_tTrick {X : Type} [Group X] [Finite X] {H D P V : Subgroup X} {t : X}
    (htH : t ∈ H) (ht2 : t * t = 1) (hVH : V ≤ H) (hDt : ∀ d ∈ D, d * t = t * d)
    (hPt : t ∈ normalizer (P : Set X)) (hPodd : Odd (Nat.card P)) (hVodd : Odd (Nat.card V))
    (hDV : D ≤ normalizer (V : Set X)) (hPV : ∀ c ∈ P, c * t = t * c → c ∈ V)
    (hF : IsComponent ((D.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H))))
    (hPF : (P.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) ≤
      normalizer (((D.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) :
        Subgroup (↥H ⧸ pPrimeCore 2 ↥H)) : Set (↥H ⧸ pPrimeCore 2 ↥H))) :
    (P.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) ≤
      centralizer (((D.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) :
        Subgroup (↥H ⧸ pPrimeCore 2 ↥H)) : Set (↥H ⧸ pPrimeCore 2 ↥H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  set F := (D.subgroupOf H).map π with hFdef
  set Vb := (V.subgroupOf H).map π with hVb
  obtain ⟨t', ht'⟩ : ∃ t' : ↥H, (t' : X) = t := ⟨⟨t, htH⟩, rfl⟩
  have htF : ∀ f ∈ F, π t' * f = f * π t' := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [coe_mul, coe_mul, ht']
    exact (hDt _ hd).symm
  have hFV : F ≤ normalizer (Vb : Set _) := by
    rintro _ ⟨d, hd, rfl⟩
    have hdV : (d : X) ∈ normalizer (V : Set X) := hDV hd
    have hdN : d ∈ normalizer ((V.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      rw [mem_normalizer_iff]
      intro h
      rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
      exact mem_normalizer_iff.mp hdV h
    exact le_normalizer_map π (mem_map_of_mem π hdN)
  have hVbodd : Odd (Nat.card Vb) := by
    refine Odd.of_dvd_nat ?_ (card_map_dvd _ π)
    rw [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv]
    exact hVodd
  have hFVb : ∀ z ∈ F, z ∈ Vb → z = 1 := by
    have hO : pPrimeCore 2 (↥H ⧸ pPrimeCore 2 ↥H) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
    have hRn : F ≤ normalizer ((F ⊓ Vb : Subgroup _) : Set _) := fun f hf =>
      mem_normalizer_inf (le_normalizer hf) (hFV hf)
    have hsub : (F ⊓ Vb).IsSubnormal :=
      Subgroup.IsSubnormal.step _ F inf_le_left hF.2
        ((normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hRn)
    have hodd : Odd (Nat.card ↥(F ⊓ Vb)) := hVbodd.of_dvd_nat (card_dvd_of_le inf_le_right)
    have h1 := ComponentClassification.UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hsub
    have htop : (⊤ : Subgroup ↥(F ⊓ Vb)) ≤ pPrimeCore 2 ↥(F ⊓ Vb) := by
      refine le_sSup ⟨inferInstance, ?_⟩
      simpa using Nat.coprime_two_left.mpr hodd
    intro z hzF hzV
    have hz : z ∈ (pPrimeCore 2 ↥(F ⊓ Vb)).map (F ⊓ Vb).subtype :=
      ⟨⟨z, hzF, hzV⟩, htop (mem_top _), rfl⟩
    rw [h1, hO] at hz
    exact mem_bot.mp hz.2
  have hVC : ∀ v ∈ Vb, v ∈ normalizer (F : Set _) → v ∈ centralizer (F : Set _) := by
    intro v hv hvN
    rw [mem_centralizer_iff]
    intro f hf
    have h1 : v * f * v⁻¹ ∈ F := (mem_normalizer_iff.mp hvN f).mp hf
    have h2 : f * v⁻¹ * f⁻¹ ∈ Vb := (mem_normalizer_iff.mp (hFV hf) v⁻¹).mp (inv_mem hv)
    have hz : v * f * v⁻¹ * f⁻¹ = 1 := by
      refine hFVb _ (mul_mem h1 (inv_mem hf)) ?_
      rw [show v * f * v⁻¹ * f⁻¹ = v * (f * v⁻¹ * f⁻¹) by group]
      exact mul_mem hv h2
    calc f * v = (v * f * v⁻¹ * f⁻¹)⁻¹ * (v * f) := by group
      _ = v * f := by rw [hz, inv_one, one_mul]
  rintro _ ⟨p, hp, rfl⟩
  have hpP : (p : X) ∈ P := hp
  have hpN : π p ∈ normalizer (F : Set _) := hPF (mem_map_of_mem π hp)
  have htt : t' * t' = 1 := Subtype.ext (by rw [coe_mul, ht', coe_one]; exact ht2)
  have htP : ∀ x : ↥H, (x : X) ∈ P → ((t' * x * t'⁻¹ : ↥H) : X) ∈ P := fun x hx => by
    rw [coe_mul, coe_mul, coe_inv, ht']
    exact (mem_normalizer_iff.mp hPt x).mp hx
  obtain ⟨k, hk⟩ : ∃ k : ↥H, k = p⁻¹ * (t' * p * t'⁻¹) := ⟨_, rfl⟩
  have hkP : (k : X) ∈ P := by
    rw [hk, coe_mul, coe_inv]
    exact mul_mem (inv_mem hpP) (htP p hpP)
  have hkF : π k ∈ centralizer (F : Set _) := by
    rw [mem_centralizer_iff]
    intro f hf
    have h1 : π t' * f = f * π t' := htF f hf
    have hf2 : π p * f * (π p)⁻¹ ∈ F := (mem_normalizer_iff.mp hpN f).mp hf
    have h2 : π t' * (π p * f * (π p)⁻¹) = π p * f * (π p)⁻¹ * π t' := htF _ hf2
    have h1' : f * (π t')⁻¹ = (π t')⁻¹ * f := by
      calc f * (π t')⁻¹ = (π t')⁻¹ * (π t' * f) * (π t')⁻¹ := by group
        _ = (π t')⁻¹ * (f * π t') * (π t')⁻¹ := by rw [h1]
        _ = (π t')⁻¹ * f := by group
    rw [hk, map_mul, map_inv, map_mul, map_mul, map_inv]
    calc f * ((π p)⁻¹ * (π t' * π p * (π t')⁻¹))
        = (π p)⁻¹ * (π p * f * (π p)⁻¹ * π t') * π p * (π t')⁻¹ := by group
      _ = (π p)⁻¹ * (π t' * (π p * f * (π p)⁻¹)) * π p * (π t')⁻¹ := by rw [h2]
      _ = (π p)⁻¹ * π t' * π p * (f * (π t')⁻¹) := by group
      _ = (π p)⁻¹ * π t' * π p * ((π t')⁻¹ * f) := by rw [h1']
      _ = (π p)⁻¹ * (π t' * π p * (π t')⁻¹) * f := by group
  have hkodd : Odd (orderOf k) := by
    rw [← Subgroup.orderOf_coe]
    exact hPodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard P hkP)
  obtain ⟨s, hs⟩ := hkodd
  obtain ⟨r, hr⟩ : ∃ r : ↥H, r = k ^ (s + 1) := ⟨_, rfl⟩
  have hrr : r * r = k := by
    rw [hr, ← pow_add, show s + 1 + (s + 1) = orderOf k + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hσ : t' * (t' * p * t'⁻¹) * t'⁻¹ = p := by
    calc t' * (t' * p * t'⁻¹) * t'⁻¹ = (t' * t') * p * (t' * t')⁻¹ := by group
      _ = p := by rw [htt, one_mul, inv_one, mul_one]
  have htk : t' * k * t'⁻¹ = k⁻¹ := by
    rw [hk]
    calc t' * (p⁻¹ * (t' * p * t'⁻¹)) * t'⁻¹
        = (t' * p * t'⁻¹)⁻¹ * (t' * (t' * p * t'⁻¹) * t'⁻¹) := by group
      _ = (t' * p * t'⁻¹)⁻¹ * p := by rw [hσ]
      _ = (p⁻¹ * (t' * p * t'⁻¹))⁻¹ := by group
  have htr : t' * r * t'⁻¹ = r⁻¹ := by
    rw [hr, ← conj_pow, htk, inv_pow]
  have hpk : t' * p * t'⁻¹ = p * k := by
    rw [hk]
    group
  obtain ⟨c, hc⟩ : ∃ c : ↥H, c = p * r := ⟨_, rfl⟩
  have htc : c * t' = t' * c := by
    have h1 : t' * c * t'⁻¹ = c := by
      rw [hc]
      calc t' * (p * r) * t'⁻¹ = (t' * p * t'⁻¹) * (t' * r * t'⁻¹) := by group
        _ = p * (r * r) * r⁻¹ := by rw [hpk, htr, hrr]
        _ = p * r := by group
    calc c * t' = (t' * c * t'⁻¹) * t' := by rw [h1]
      _ = t' * c := by group
  have hcP : (c : X) ∈ P := by
    rw [hc, coe_mul, hr, coe_pow]
    exact mul_mem hpP (pow_mem hkP _)
  have hcV : (c : X) ∈ V := by
    refine hPV _ hcP ?_
    have h1 := congrArg Subtype.val htc
    rw [coe_mul, coe_mul, ht'] at h1
    exact h1
  have hcC : π c ∈ centralizer (F : Set _) :=
    hVC _ (mem_map_of_mem π (show c ∈ V.subgroupOf H from hcV))
      (hPF (mem_map_of_mem π (show c ∈ P.subgroupOf H from hcP)))
  have hrC : π r ∈ centralizer (F : Set _) := by
    rw [hr, map_pow]
    exact pow_mem hkF _
  have hpc : p = c * r⁻¹ := by
    rw [hc]
    group
  rw [hpc, map_mul, map_inv]
  exact mul_mem hcC (inv_mem hrC)

private abbrev l1Pi (X : Type) [Group X] (n : ℕ) (t b : X) : Subgroup X :=
  ⨆ (L : Subgroup X) (_ : Sec6MComp X n (cen t) L), sec6Piece L b

private theorem l1_mem_sup
    {X : Type} [Group X] [Finite X] {n : ℕ} {t a b : X}
    (hb : b ∈ Sec6M X n (cen t)) (hb2 : b ^ 2 = 1) (ha : a ∈ Sec6M X n (cen t))
    (hab : a * b = b * a) {j : ℕ} (haj : a ^ (2 ^ j) = 1) :
    a ∈ l1Pi X n t b ⊔ (oddCoreOf (cen t) ⊓ cen b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := cen t with hCdef
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  have hMC : Sec6M X n C ≤ C := sSup_le fun L (hL : Sec6MComp X n C L) => hL.1.1.1
  have hPiC : l1Pi X n t b ≤ C :=
    iSup₂_le fun L hL => ((oTwoPrimeOf_le _).trans inf_le_left).trans hL.1.1.1
  have hPib : l1Pi X n t b ≤ cen b :=
    iSup₂_le fun L _ => (oTwoPrimeOf_le _).trans inf_le_right
  set 𝓜 : Set (Subgroup (↥C ⧸ pPrimeCore 2 ↥C)) :=
    {K | ∃ L, Sec6MComp X n C L ∧ (L.subgroupOf C).map π = K} with h𝓜def
  have h𝓜c : ∀ K ∈ 𝓜, IsComponent K := by
    rintro K ⟨L, hL, rfl⟩
    obtain ⟨-, K', hK', -, hmap, -⟩ := hL.1.1
    rw [hmap]
    exact hK'
  have h𝓜Z : ∀ K ∈ 𝓜, ∀ z ∈ K, (∀ y ∈ K, z * y = y * z) → z = 1 := by
    rintro K ⟨L, hL, rfl⟩ z hz hzc
    obtain ⟨hLC, -, -, hsub, -, -⟩ := hL.1.1
    obtain ⟨e, -⟩ :=
      ComponentClassification.UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal hLC
        hsub
    have hZ : center ↥((L.subgroupOf C).map π) = ⊥ := by
      rcases hL.1.2.1 with ⟨⟨eM⟩⟩ | ⟨⟨eL⟩⟩
      · exact l1_center_eq_bot_of_mcl (e.symm.trans eM)
      · exact l1_center_eq_bot_of_ly (e.symm.trans eL)
    have hzZ : (⟨z, hz⟩ : ↥((L.subgroupOf C).map π)) ∈ center _ := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2).symm
    rw [hZ, mem_bot] at hzZ
    exact congrArg Subtype.val hzZ
  have h𝓜comm : ∀ K ∈ 𝓜, ∀ K' ∈ 𝓜, K ≠ K' → K' ≤ centralizer (K : Set _) :=
    fun K hK K' hK' hne => commutator_eq_bot_iff_le_centralizer.mp
      ((LocalCores.distinct_components_commute (h𝓜c K' hK') (h𝓜c K hK)).resolve_left
        (Ne.symm hne))
  have hmem : ∀ x ∈ Sec6M X n C, ∀ hx : x ∈ C, π ⟨x, hx⟩ ∈ sSup 𝓜 := by
    intro x hxM hxC
    have hle : Sec6M X n C ≤ ((sSup 𝓜).comap π).map C.subtype :=
      sSup_le fun L (hL : Sec6MComp X n C L) y hy => by
        refine ⟨⟨y, hL.1.1.1 hy⟩, ?_, rfl⟩
        have hK : (L.subgroupOf C).map π ≤ sSup 𝓜 := le_sSup ⟨L, hL, rfl⟩
        exact hK (mem_map_of_mem π (show (⟨y, hL.1.1.1 hy⟩ : ↥C) ∈ L.subgroupOf C from hy))
    obtain ⟨y, hy, hyx⟩ := hle hxM
    have : y = ⟨x, hxC⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  have haC : a ∈ C := hMC ha
  have hbC : b ∈ C := hMC hb
  have haCb : a ∈ cen b := mem_centralizer_singleton_iff.mpr hab
  have habBar : π ⟨a, haC⟩ * π ⟨b, hbC⟩ = π ⟨b, hbC⟩ * π ⟨a, haC⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hab
  have haPow : π ⟨a, haC⟩ ^ (2 ^ j) = 1 := by
    rw [← map_pow, show (⟨a, haC⟩ : ↥C) ^ (2 ^ j) = 1 from Subtype.ext (by simpa using haj),
      map_one]
  set W := ((l1Pi X n t b).subgroupOf C).map π with hW
  have hWcond : ∀ K ∈ 𝓜, ∀ z ∈ K, z * π ⟨b, hbC⟩ = π ⟨b, hbC⟩ * z →
      (∃ k : ℕ, z ^ (2 ^ k) = 1) → z ∈ W := by
    rintro K ⟨L, hL, rfl⟩ _ ⟨y, hy, rfl⟩ hzb ⟨k, hk⟩
    have hyL : (y : X) ∈ L := hy
    obtain ⟨hLC, -, -, hsub, -, -⟩ := hL.1.1
    have hOL : oddCoreOf L ≤ oddCoreOf C := pPrimeCoreOf_le_oddCoreOf hLC hsub
    have hLO : L ⊓ oddCoreOf C ≤ oddCoreOf L :=
      le_oddCoreOf_of_normalized inf_le_left
        (fun l hl => mem_normalizer_inf (le_normalizer hl) (le_normalizer_oddCoreOf C (hLC hl)))
        ((odd_card_oddCoreOf C).of_dvd_nat (card_dvd_of_le inf_le_right))
    have hyk : (y : X) ^ (2 ^ k) ∈ oddCoreOf L := by
      refine hLO ⟨pow_mem hyL _, ?_⟩
      have h1 := (l1_mk_eq_one_iff (y ^ (2 ^ k))).mp (by rw [← hπ, map_pow]; exact hk)
      rwa [coe_pow] at h1
    obtain ⟨m, hm1, hm2⟩ :=
      exists_zpow_twoElt_of_pow_mem (Nat.coprime_two_left.mpr (odd_card_oddCoreOf L)) hyk
    have hy'L : (y : X) ^ m ∈ L := zpow_mem hyL m
    have hy'C : (y : X) ^ m ∈ C := hLC hy'L
    have hπy' : π ⟨(y : X) ^ m, hy'C⟩ = π y := by
      have h1 : π (y⁻¹ * ⟨(y : X) ^ m, hy'C⟩) = 1 := (l1_mk_eq_one_iff _).mpr (hOL hm2)
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1.symm
    have hbN : b ∈ normalizer (L : Set X) := l1_le_normalizer hL hb
    have hbO : b ∈ normalizer (pPrimeCoreOf 2 L : Set X) :=
      mem_normalizer_oddCoreOf_of_mem_normalizer hbN
    have hcomm : ⁅(y : X) ^ m, b⁆ ∈ pPrimeCoreOf 2 L := by
      refine hLO ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        have h1 : b * ((y : X) ^ m)⁻¹ * b⁻¹ ∈ L :=
          (mem_normalizer_iff.mp hbN _).mp (inv_mem hy'L)
        rw [show (y : X) ^ m * b * ((y : X) ^ m)⁻¹ * b⁻¹ =
          (y : X) ^ m * (b * ((y : X) ^ m)⁻¹ * b⁻¹) by group]
        exact mul_mem hy'L h1
      · have h1 : π (⟨(y : X) ^ m, hy'C⟩ * ⟨b, hbC⟩ * ⟨(y : X) ^ m, hy'C⟩⁻¹ * ⟨b, hbC⟩⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπy', hzb, mul_inv_cancel_right,
            mul_inv_cancel]
        have h2 := (l1_mk_eq_one_iff _).mp h1
        rw [commutatorElement_def]
        exact h2
    obtain ⟨c, hc, hck, hcy⟩ := exists_twoElt_centralizer_of_comm_mem hb2 hbO hy'L hcomm hm1
    have hcPi : c ∈ l1Pi X n t b := by
      have hcp : c ∈ sec6Piece L b := mem_oTwoPrimeOf hc k hck
      exact (le_iSup₂ (f := fun L (_ : Sec6MComp X n (cen t) L) => sec6Piece L b) L hL) hcp
    have hcC : c ∈ C := hPiC hcPi
    refine ⟨⟨c, hcC⟩, hcPi, ?_⟩
    rw [← hπy']
    have h1 : π ((⟨c, hcC⟩ : ↥C)⁻¹ * ⟨(y : X) ^ m, hy'C⟩) = 1 :=
      (l1_mk_eq_one_iff _).mpr (hOL hcy)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have haW : π ⟨a, haC⟩ ∈ W :=
    l1_decomp W 𝓜 (Set.toFinite 𝓜) h𝓜Z h𝓜comm _ (hmem b hb hbC) hWcond _ (hmem a ha haC) habBar
      j haPow
  obtain ⟨w, hw, hwa⟩ := haW
  have hwPi : (w : X) ∈ l1Pi X n t b := hw
  have h1 : π (w⁻¹ * ⟨a, haC⟩) = 1 := by rw [map_mul, map_inv, hwa, inv_mul_cancel]
  have h2 : (w : X)⁻¹ * a ∈ oddCoreOf C := (l1_mk_eq_one_iff _).mp h1
  have h3 : (w : X)⁻¹ * a ∈ cen b := mul_mem (inv_mem (hPib hwPi)) haCb
  rw [show a = (w : X) * ((w : X)⁻¹ * a) by group]
  exact mul_mem_sup hwPi ⟨h2, h3⟩

private theorem l1_claimA
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hU : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X, Sec6MComp X n (cen t) L →
      Sec6KComp X n (cen x) F → sec6Piece L x ≤ F → F = oddCoreOf F ⊔ sec6Piece L x)
    {a b : X} (hb : b ∈ Sec6M X n (cen t)) (hb2 : orderOf b = 2) (ha : a ∈ l1Pi X n t b)
    (ha2 : orderOf a = 2) :
    oddCoreOf (cen a) ⊓ cen b ≤ oddCoreOf (cen b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpiece : ∀ L, Sec6MComp X n (cen t) L → sec6Piece L b ≤ L ⊓ cen b :=
    fun L _ => oTwoPrimeOf_le _
  have hPib : l1Pi X n t b ≤ cen b := iSup₂_le fun L hL => (hpiece L hL).trans inf_le_right
  have hMt : Sec6M X n (cen t) ≤ cen t :=
    sSup_le fun L (hL : Sec6MComp X n (cen t) L) => hL.1.1.1
  have hPiM : l1Pi X n t b ≤ Sec6M X n (cen t) := iSup₂_le fun L hL =>
    (hpiece L hL).trans (inf_le_left.trans (le_sSup (s := {M | Sec6MComp X n (cen t) M}) hL))
  have haM : a ∈ Sec6M X n (cen t) := hPiM ha
  have hab : a ∈ cen b := hPib ha
  have hta : t ∈ cen a :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hMt haM)).symm
  have htb : t ∈ cen b :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hMt hb)).symm
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have ha22 : a ^ 2 = 1 := by
    rw [← ha2]
    exact pow_orderOf_eq_one a
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥(cen b)) with hπ
  set P := oddCoreOf (cen a) ⊓ cen b with hP
  have hPb : P ≤ cen b := inf_le_right
  have hPodd' : Odd (Nat.card P) :=
    (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
  set Pb := (P.subgroupOf (cen b)).map π with hPbdef
  have hPodd : Odd (Nat.card Pb) := by
    refine Odd.of_dvd_nat ?_ (card_map_dvd _ π)
    rw [Nat.card_congr (subgroupOfEquivOfLe hPb).toEquiv]
    exact hPodd'
  have hPβ : Pb ≤ centralizer ({π ⟨a, hab⟩} : Set _) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (oddCoreOf_le _ hq.1))
  have hPn : centralizer ({π ⟨a, hab⟩} : Set _) ≤ normalizer (Pb : Set _) := by
    have hN2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥(cen b)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
    have ha'2 : (⟨a, hab⟩ : ↥(cen b)) ^ (2 ^ 1) = 1 := Subtype.ext (by simpa using ha22)
    have hcent := Semidihedral.Local.map_centralizer_eq_of_coprime 2 (pPrimeCore 2 ↥(cen b))
      hN2 (zpowers ⟨a, hab⟩) (l1_isPGroup_zpowers ha'2)
    rw [← hπ, MonoidHom.map_zpowers, l1_centralizer_zpowers, l1_centralizer_zpowers] at hcent
    rw [← hcent]
    refine (map_mono ?_).trans (le_normalizer_map π)
    intro z hz
    have hza : (z : X) ∈ cen a := mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mem_centralizer_singleton_iff.mp hz))
    have hzP : (z : X) ∈ normalizer (P : Set X) :=
      mem_normalizer_inf (le_normalizer_oddCoreOf (cen a) hza) (le_normalizer z.2)
    rw [mem_normalizer_iff]
    intro h
    rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp hzP h
  set 𝓕 : Set (Subgroup (↥(cen b) ⧸ pPrimeCore 2 ↥(cen b))) :=
    {K | ∃ L, Sec6MComp X n (cen t) L ∧ ((sec6Piece L b).subgroupOf (cen b)).map π = K}
    with h𝓕def
  have h𝓕 : ∀ K ∈ 𝓕, IsComponent K := by
    rintro K ⟨L, hL, rfl⟩
    obtain ⟨F, hFK, hpF⟩ := hC.land b (mem_sup_left hb) hb2 L (Or.inr hL)
    have hFeq := hU b hb hb2 L F hL hFK hpF
    have hFc : IsPCompIn 2 (cen b) F := by
      rcases hFK with ⟨⟨u, hu⟩, -⟩ | ⟨hM, -⟩
      · exact hu.2.2.1
      · exact hM.1
    obtain ⟨hFb, K', hK', hsub, hmap, -⟩ := hFc
    have hOF : oddCoreOf F ≤ oddCoreOf (cen b) := pPrimeCoreOf_le_oddCoreOf hFb hsub
    have heq : ((sec6Piece L b).subgroupOf (cen b)).map π = (F.subgroupOf (cen b)).map π := by
      apply le_antisymm
      · exact map_mono fun x hx => hpF hx
      · rintro _ ⟨f, hf, rfl⟩
        have hfF : (f : X) ∈ ((sec6Piece L b ⊔ oddCoreOf F : Subgroup X) : Set X) := by
          rw [sup_comm, ← hFeq]
          exact hf
        rw [coe_mul_of_left_le_normalizer_right _ _
          (fun y hy => le_normalizer_oddCoreOf F (hpF hy))] at hfF
        obtain ⟨p, hp, o, ho, hpo⟩ := hfF
        have hpb : p ∈ cen b := (hpiece L hL hp).2
        have hob : o ∈ cen b := by
          have : o = p⁻¹ * f := by
            rw [← hpo]
            group
          rw [this]
          exact mul_mem (inv_mem hpb) f.2
        refine ⟨⟨p, hpb⟩, hp, ?_⟩
        have h1 : π ⟨o, hob⟩ = 1 := (l1_mk_eq_one_iff _).mpr (hOF ho)
        have h2 : f = ⟨p, hpb⟩ * ⟨o, hob⟩ := Subtype.ext hpo.symm
        rw [h2, map_mul, h1, mul_one]
    rw [heq, hmap]
    exact hK'
  have haBar : π ⟨a, hab⟩ ∈ sSup 𝓕 := by
    have hle : l1Pi X n t b ≤ ((sSup 𝓕).comap π).map (cen b).subtype :=
      iSup₂_le fun L hL y hy => by
        have hyb : y ∈ cen b := (hpiece L hL hy).2
        refine ⟨⟨y, hyb⟩, ?_, rfl⟩
        have hK : ((sec6Piece L b).subgroupOf (cen b)).map π ≤ sSup 𝓕 := le_sSup ⟨L, hL, rfl⟩
        exact hK (mem_map_of_mem π
          (show (⟨y, hyb⟩ : ↥(cen b)) ∈ (sec6Piece L b).subgroupOf (cen b) from hy))
    obtain ⟨y, hy, hya⟩ := hle ha
    have : y = ⟨a, hab⟩ := Subtype.ext hya
    rw [← this]
    exact hy
  have hβ2 : (π ⟨a, hab⟩) ^ 2 = 1 := by
    rw [← map_pow, show (⟨a, hab⟩ : ↥(cen b)) ^ 2 = 1 from Subtype.ext (by simpa using ha22),
      map_one]
  have hkey : ∀ F ∈ 𝓕, Pb ≤ normalizer (F : Set _) → Pb ≤ centralizer (F : Set _) := by
    rintro F ⟨L, hL, rfl⟩ hPF
    refine l1_tTrick (V := oddCoreOf (cen t) ⊓ cen b) htb ht2 inf_le_right ?_ ?_ hPodd' ?_ ?_ ?_
      (h𝓕 _ ⟨L, hL, rfl⟩) hPF
    · intro d hd
      exact mem_centralizer_singleton_iff.mp (hL.1.1.1 (hpiece L hL hd).1)
    · exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen a) hta) (le_normalizer htb)
    · exact (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
    · intro d hd
      have hd' := hpiece L hL hd
      exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen t) (hL.1.1.1 hd'.1))
        (le_normalizer hd'.2)
    · intro c hc hct
      refine ⟨?_, hc.2⟩
      have h1 : c ∈ oddCoreOf (cen t ⊓ cen a) := by
        refine le_oddCoreOf_of_normalized (N := oddCoreOf (cen a) ⊓ cen t) ?_ ?_ ?_
          ⟨hc.1, mem_centralizer_singleton_iff.mpr hct⟩
        · exact le_inf inf_le_right (inf_le_left.trans (oddCoreOf_le _))
        · intro y hy
          exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen a) hy.2) (le_normalizer hy.1)
        · exact (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
      exact sec6_lemmaT hS haM ha2 h1
  have hPE := l1_le_centralizer_layer h𝓕 haBar hβ2 hPodd hPβ hPn hkey
  have hP1 := eq_bot_of_odd_of_le_centralizer_layer (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    (k := 1) (by rwa [pow_one]) hPodd hPβ hPn hPE
  intro x hx
  have hxb : x ∈ cen b := hx.2
  have hxP : π ⟨x, hxb⟩ ∈ Pb :=
    mem_map_of_mem π (show (⟨x, hxb⟩ : ↥(cen b)) ∈ P.subgroupOf (cen b) from hx)
  rw [hP1, mem_bot] at hxP
  exact (l1_mk_eq_one_iff _).mp hxP

theorem sec6Lambda1At_of_ctrl
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (hC : Sec6CtrlAt X n t)
    (hU : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X, Sec6MComp X n (cen t) L →
      Sec6KComp X n (cen x) F → sec6Piece L x ≤ F → F = oddCoreOf F ⊔ sec6Piece L x) :
    Sec6Lambda1At X n t := by
  intro a ha b hb ha2 hb2 hab
  have hsq : ∀ {x : X}, orderOf x = 2 → x ^ 2 = 1 := fun hx => by
    rw [← hx]
    exact pow_orderOf_eq_one _
  have hmem := l1_mem_sup hb (hsq hb2) ha hab (j := 1) (by rw [pow_one]; exact hsq ha2)
  have hPiN : l1Pi X n t b ≤ normalizer ((oddCoreOf (cen t) ⊓ cen b : Subgroup X) : Set X) := by
    refine iSup₂_le fun L hL y hy => ?_
    have hy' : y ∈ L ⊓ cen b := oTwoPrimeOf_le _ hy
    exact mem_normalizer_inf (le_normalizer_oddCoreOf (cen t) (hL.1.1.1 hy'.1))
      (le_normalizer hy'.2)
  have hNodd : Odd (Nat.card ↥(oddCoreOf (cen t) ⊓ cen b)) :=
    (odd_card_oddCoreOf _).of_dvd_nat (card_dvd_of_le inf_le_left)
  obtain ⟨o, ho, a', ha', ha'2, rfl⟩ :=
    l1_exists_conj hPiN hNodd hmem (by rw [pow_one]; exact hsq ha2)
  have ha'1 : a' ≠ 1 := by
    rintro rfl
    simp at ha2
  have ha'o : orderOf a' = 2 := orderOf_eq_prime (by rwa [pow_one] at ha'2) ha'1
  have hA := l1_claimA hS hC hU hb hb2 ha' ha'o
  have hob : o ∈ cen b := ho.2
  intro x hx
  have h1 : oddCoreOf (cen (o * a' * o⁻¹)) =
      (oddCoreOf (cen a')).map (MulAut.conj o).toMonoidHom := by
    rw [oddCoreOf_map_mulEquiv', cen_map, MulAut.conj_apply]
  have hx1 : x ∈ (oddCoreOf (cen a')).map (MulAut.conj o).toMonoidHom := by
    rw [← h1]
    exact hx.1
  obtain ⟨x', hx', rfl⟩ := hx1
  have hx'b : x' ∈ cen b := by
    have h2 : o * x' * o⁻¹ ∈ cen b := hx.2
    have h3 : x' = o⁻¹ * (o * x' * o⁻¹) * o := by group
    rw [h3]
    exact mul_mem (mul_mem (inv_mem hob) h2) hob
  have h4 := hA ⟨hx', hx'b⟩
  exact (mem_normalizer_iff.mp (le_normalizer_oddCoreOf (cen b) hob) x').mp h4

end CFSG.OddStandard.Solomon75
