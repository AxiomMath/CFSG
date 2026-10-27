module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalKnown
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveFactor

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open scoped Pointwise

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal

open SectionSix SectionSix.BarTools

namespace RankOne

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem isElemAbelian_of_equiv {Y : Type} [Group Y] {P : Subgroup G} {Q : Subgroup Y}
    (e : P ≃* Q) (hQ : IsElemAbelian 2 Q) : IsElemAbelian 2 P := by
  refine ⟨⟨⟨fun a b => e.injective ?_⟩⟩, fun x hx => ?_⟩
  · rw [map_mul, map_mul]
    exact hQ.1.is_comm.comm _ _
  · have h1 : ((e ⟨x, hx⟩ : Q) : Y) ^ 2 = 1 := hQ.2 _ (e ⟨x, hx⟩).2
    have h2 : e (⟨x, hx⟩ ^ 2) = 1 := Subtype.ext (by rw [map_pow]; exact h1)
    have h3 : (⟨x, hx⟩ : P) ^ 2 = 1 := e.injective (h2.trans (map_one e).symm)
    exact congrArg Subtype.val h3

theorem pRank_bar_le {Y : Subgroup G} (hYH : Y ≤ Subgroup.normalizer (D : Set G))
    {k : ℕ} (hY : CFSG.Open.pRank 2 Y ≤ k) : CFSG.Open.pRank 2 (bar D Y) ≤ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEY, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) (bar D Y)
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hcard
  obtain ⟨V, hVY, hV2, hVE⟩ := lift_two_subgroup hYH hE2 hEY
  have hVH : V ≤ Subgroup.normalizer (D : Set G) := hVY.trans hYH
  have hVel : IsElemAbelian 2 V := by
    have e := barEquiv hV2 hVH
    rw [hVE] at e
    exact isElemAbelian_of_equiv e hE
  have hVcard : Nat.card V = 2 ^ CFSG.Open.pRank 2 (bar D Y) := by
    rw [← card_bar_of_isPGroup hV2 hVH, hVE, hcard]
  exact (CFSG.SectionRank.le_pRank (by norm_num) hVY hVel hVcard).trans hY

theorem quasisimple_of_rank_one (hyp : Hyp61 G D r Abar) (i : Fin r)
    (hr : CFSG.Open.pRank 2 (bar D (aschbacherThm5Preimage D (Abar i))) ≤ 1) :
    CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar i))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, K, hm, hK, hcomm, hKgen⟩ := bar_factor_components hyp i
  have hone : ∀ l l' : Fin m, l = l' := by
    intro l l'
    by_contra hll'
    obtain ⟨S, hS⟩ := exists_isSylowOf 2 (K l)
    obtain ⟨S', hS'⟩ := exists_isSylowOf 2 (K l')
    have hSS' : ∀ x ∈ S, ∀ y ∈ S', x * y = y * x := fun x hx y hy =>
      hcomm l l' hll' x (hS.le hx) y (hS'.le hy)
    have hR2 : IsPGroup 2 (S ⊔ S' : Subgroup (Bar D)) :=
      isPGroup_sup_of_commute hS.isPGroup hS'.isPGroup hSS'
    have hRle : S ⊔ S' ≤ bar D (aschbacherThm5Preimage D (Abar i)) :=
      sup_le (hS.le.trans (hK l).2) (hS'.le.trans (hK l').2)
    have hRr : CFSG.Open.pRank 2 (S ⊔ S' : Subgroup (Bar D)) ≤ 1 :=
      (CFSG.SectionRank.pRank_mono (by norm_num) hRle).trans hr
    have hRtype : IsCyclic (S ⊔ S' : Subgroup (Bar D)) ∨
        AschbacherTheorem3.IsDihedralTwoGroup (S ⊔ S') ∨
        AschbacherTheorem3.IsQuaternionTwoGroup (S ⊔ S') := by
      rcases cyclic_or_quaternion_of_pRank_le_one hR2 hRr with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have hSc := sylow_not_cyclic_of_perfect (component_perfect (hK l).1)
      (component_ne_bot (hK l).1) hS
    have hS'c := sylow_not_cyclic_of_perfect (component_perfect (hK l').1)
      (component_ne_bot (hK l').1) hS'
    have heq := commuting_noncyclic_eq hRtype le_sup_left le_sup_right hSc hS'c hSS'
    apply sylow_not_le_centralizer_of_perfect (component_perfect (hK l).1)
      (component_ne_bot (hK l).1) hS
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxS' : x ∈ S' := heq ▸ hx
    exact hcomm l l' hll' y hy x (hS'.le hxS')
  have hbar : bar D (aschbacherThm5Preimage D (Abar i)) = K ⟨0, hm⟩ := by
    rw [← hKgen]
    apply le_antisymm
    · exact iSup_le fun l => le_of_eq (by rw [hone l ⟨0, hm⟩])
    · exact le_iSup K ⟨0, hm⟩
  rw [hbar]
  exact (hK ⟨0, hm⟩).1.2.2

theorem eq_one_of_central_odd (hyp : Hyp61 G D r Abar) (i : Fin r) {w : Bar D}
    (hwA : w ∈ bar D (aschbacherThm5Preimage D (Abar i)))
    (hwC : w ∈ Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar i)) : Set (Bar D)))
    (hodd : Odd (orderOf w)) : w = 1 := by
  set P := Subgroup.zpowers w with hPdef
  have hPD : P ≤ bar D D :=
    Subgroup.zpowers_le.mpr (bar_mono D (preimage_le D _) hwA)
  have hwD : bar D D ≤ Subgroup.centralizer ({w} : Set (Bar D)) := by
    rw [bar_D_eq_range, MonoidHom.range_eq_map, ← hyp.hgen, Subgroup.map_iSup]
    refine iSup_le fun j => ?_
    rw [map_quotientEmbedding]
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hji : j = i
    · subst hji
      exact (Subgroup.mem_centralizer_iff.mp hwC) y hy
    · exact (Subgroup.mem_centralizer_iff.mp
        (Strong.bar_factor_le_centralizer hyp (Ne.symm hji) hy) w hwA).symm
  have hDP : bar D D ≤ Subgroup.normalizer (P : Set (Bar D)) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro x ⟨k, rfl⟩
    have hyw : Commute y w := Subgroup.mem_centralizer_singleton_iff.mp (hwD hy)
    exact ((hyw.zpow_right k).eq).symm
  have hPodd : Odd (Nat.card P) := by rw [hPdef, Nat.card_zpowers]; exact hodd
  have hle := AschbacherTheorem3.le_map_oddCore hPD hDP hPodd
  rw [oddCore_bar_D, Subgroup.map_bot, le_bot_iff] at hle
  have hw : w ∈ P := Subgroup.mem_zpowers w
  rw [hle, Subgroup.mem_bot] at hw
  exact hw

theorem central_isTwoElement (hyp : Hyp61 G D r Abar) (i : Fin r) {w : Bar D}
    (hwA : w ∈ bar D (aschbacherThm5Preimage D (Abar i)))
    (hwC : w ∈ Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar i)) : Set (Bar D))) :
    ∃ k : ℕ, w ^ 2 ^ k = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  refine ⟨k, eq_one_of_central_odd hyp i (Subgroup.pow_mem _ hwA _)
    (Subgroup.pow_mem _ hwC _) ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) (hkm ▸ dvd_mul_right _ _), hkm,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

theorem not_le_centralizerJoin (hC : Counterexample G D r Abar) {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {V : Subgroup G} (hV : V ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g)) (i : Fin r) :
    ¬ bar D (aschbacherThm5Preimage D (Abar i)) ≤ AschbacherKnownGroup.centralizerJoin
      (bar D V) (bar D (aschbacherThm5Preimage D (Abar i))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVH, hVel, hV4, hVC⟩ := hV
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  have hAH : A ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  set X := ⨆ (v : G) (_ : v ∈ V) (_ : v ≠ 1), A ⊓ Subgroup.centralizer ({v} : Set G) with hXdef
  have hXH : X ≤ H := iSup₂_le fun v _ => iSup_le fun _ => inf_le_left.trans hAH
  have hXHg : X ≤ rightConjugate H g :=
    iSup₂_le fun v hv => iSup_le fun hv1 => inf_le_right.trans (hVC v hv hv1)
  intro hle
  have hLX : bar D A ≤ bar D X := by
    refine hle.trans (iSup₂_le fun u hu => iSup_le fun hu1 => ?_)
    obtain ⟨v, hvV, rfl⟩ := (mem_bar_iff D V u).mp hu
    have hv1 : (v : G) ≠ 1 := by
      intro h
      apply hu1
      rw [show v = 1 from Subtype.ext h, map_one]
    have hvo : orderOf (v : G) = 2 := orderOf_eq_prime (hVel.2 _ hvV) hv1
    rw [← bar_inf_centralizer (core_le_preimage D _) v.2 hvo]
    exact bar_mono D (le_iSup₂_of_le (v : G) hvV (le_iSup_of_le hv1 le_rfl))
  have hAX := le_sup_core_of_bar_le hAH hLX
  exact hg (AschbacherTheorem3.rightConjugate_eq_of_mem
    (mem_normalizer_of_le_sup hC i g X hXHg hXH hAX))

theorem isFourGroup_bar {V : Subgroup G} (hVH : V ≤ Subgroup.normalizer (D : Set G))
    (hVel : IsElemAbelian 2 V) (hV4 : Nat.card V = 4) :
    AschbacherKnownGroup.IsFourGroup (bar D V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  refine ⟨CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hVel _) (toBar D), ?_⟩
  rw [card_bar_of_isPGroup hV2 hVH, hV4]

omit [Finite G] in
theorem conj_mem_centralizer {B : Type} [Group B] {L : Subgroup B} {v c : B}
    (hv : v ∈ Subgroup.normalizer (L : Set B)) (hc : c ∈ Subgroup.centralizer (L : Set B)) :
    v * c * v⁻¹ ∈ Subgroup.centralizer (L : Set B) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro l hl
  have hl' : v⁻¹ * l * v ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set B)).inv_mem hv) l).mp hl
    simpa using this
  have h1 := hc _ hl'
  calc l * (v * c * v⁻¹) = v * ((v⁻¹ * l * v) * c) * v⁻¹ := by group
    _ = v * (c * (v⁻¹ * l * v)) * v⁻¹ := by rw [h1]
    _ = v * c * v⁻¹ * l := by group

theorem exists_q8Pair_of_rank_one (hC : Counterexample G D r Abar) (hin : SectionSixInputs)
    {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {V : Subgroup G} (hV : V ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g)) (i : Fin r)
    (hr : CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i)) ≤ 1) :
    ∃ p q : Bar D, IsQ8Pair p q ∧ p ∈ bar D (aschbacherThm5Preimage D (Abar i)) ∧
      q ∈ bar D (aschbacherThm5Preimage D (Abar i)) ∧
      p ∈ AschbacherToolkit.centralizerJoin (bar D V) ∧
      q ∈ AschbacherToolkit.centralizerJoin (bar D V) ∧
      p ^ 2 ∈ Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar i)) : Set (Bar D)) ∧
      ∀ t ∈ bar D (aschbacherThm5Preimage D (Abar i)), t ^ 2 = 1 → t = 1 ∨ t = p ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  set L := bar D A with hLdef
  have hAH : A ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have hLr : CFSG.Open.pRank 2 L ≤ 1 := pRank_bar_le hAH hr
  have hLq : CFSG.Open.IsQuasisimple L := quasisimple_of_rank_one hC.hyp i hLr
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 L
  have hRq : AschbacherTheorem3.IsQuaternionTwoGroup R :=
    (cyclic_or_quaternion_of_pRank_le_one hR.isPGroup
      ((CFSG.SectionRank.pRank_mono (by norm_num) hR.le).trans hLr)).resolve_left
      (sylow_not_cyclic_of_perfect (bar_factor_perfect hC.hyp i) (bar_factor_ne_bot hC.hyp i) hR)
  obtain ⟨z, hzA, hz, hzc⟩ := Factor.exists_central_involution hC.hyp i hR hRq
  have hzH : z ∈ H := hAH hzA
  set zb := toBar D ⟨z, hzH⟩ with hzbdef
  have hzbL : zb ∈ L := toBar_mem_bar D hzA
  have hzbC : zb ∈ Subgroup.centralizer (L : Set (Bar D)) :=
    (centralizes_iff_mem_centralizer D A (preimage_le D _) ⟨z, hzH⟩).mp hzc
  have hzb2 : zb ^ 2 = 1 := by
    rw [hzbdef, ← map_pow, show (⟨z, hzH⟩ : H) ^ 2 = 1 from
      Subtype.ext (TwoGroups.sq_eq_one_of_orderOf hz), map_one]
  have hzb1 : zb ≠ 1 := by
    intro h
    exact TwoGroups.ne_one_of_orderOf hz (Strong.eq_one_of_mem_core_of_sq
      ((toBar_eq_one_iff D _).mp h) (TwoGroups.sq_eq_one_of_orderOf hz))
  have hzbo : orderOf zb = 2 := orderOf_eq_prime hzb2 hzb1
  have huniq : ∀ t ∈ L, t ^ 2 = 1 → t = 1 ∨ t = zb := by
    intro t htL ht2
    by_cases ht1 : t = 1
    · exact Or.inl ht1
    right
    obtain ⟨c, hcL, hct⟩ := Strong.conj_of_pRank_le_one hLr hzbL hzbo htL
      (orderOf_eq_prime ht2 ht1)
    have hcz : c * zb = zb * c := (Subgroup.mem_centralizer_iff.mp hzbC) c hcL
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = c⁻¹ * zb * c := by rw [hct]
      _ = zb := by rw [mul_assoc, ← hcz]; group
  obtain ⟨hVH, hVel, hV4, -⟩ := id hV
  have hVN := lemma_6_5_one hC hg hV i
  have hVbL : bar D V ≤ Subgroup.normalizer (L : Set (Bar D)) := bar_le_normalizer hVN hAH
  have hVb4 := isFourGroup_bar hVH hVel hV4
  have hgen := not_le_centralizerJoin hC hg hV i
  obtain ⟨h2, -, -⟩ := lemma_3_5_sub hin.knownGroups hLq hLr hVb4 hVbL hgen
  have hfaith : ∀ v ∈ bar D V, v ≠ 1 → v ∉ Subgroup.centralizer (L : Set (Bar D)) := by
    intro v hv hv1 hvC
    apply hgen
    refine le_iSup_of_le v (le_iSup_of_le hv (le_iSup_of_le hv1 (le_inf le_rfl ?_)))
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hvC) l hl
  set CL := Subgroup.centralizer (L : Set (Bar D)) with hCLdef
  have hCLN : CL ≤ Subgroup.normalizer (L : Set (Bar D)) := Subgroup.centralizer_le_normalizer _
  have hVCN : bar D V ≤ Subgroup.normalizer (CL : Set (Bar D)) := fun v hv =>
    AschbacherToolkit.mem_normalizer_of_conj_le fun c hc => conj_mem_centralizer (hVbL hv) hc
  have hLCprod : ((L ⊔ CL : Subgroup (Bar D)) : Set (Bar D)) =
      (L : Set (Bar D)) * (CL : Set (Bar D)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L CL hCLN
  have hVCprod : ((bar D V ⊔ CL : Subgroup (Bar D)) : Set (Bar D)) =
      (bar D V : Set (Bar D)) * (CL : Set (Bar D)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (bar D V) CL hVCN
  have hVsq : ∀ v ∈ bar D V, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact hVb4.1.2 v hv
  set M := L ⊓ (bar D V ⊔ CL) with hMdef
  have hMdecomp : ∀ m ∈ M, ∃ v ∈ bar D V, ∃ c ∈ CL, m = v * c := by
    intro m hm
    have h1 : m ∈ ((bar D V ⊔ CL : Subgroup (Bar D)) : Set (Bar D)) := hm.2
    rw [hVCprod] at h1
    obtain ⟨v, hv, c, hc, hvc⟩ := Set.mem_mul.mp h1
    exact ⟨v, hv, c, hc, hvc.symm⟩
  have hMcomm : ∀ m ∈ L, ∀ v c : Bar D, c ∈ CL → m = v * c → m * v = v * m := by
    intro m hmL v c hc hmvc
    have hv : v = m * c⁻¹ := by rw [hmvc]; group
    have hcm : c⁻¹ * m = m * c⁻¹ :=
      ((Subgroup.mem_centralizer_iff.mp (CL.inv_mem hc)) m hmL).symm
    rw [hv]
    calc m * (m * c⁻¹) = m * (c⁻¹ * m) := by rw [hcm]
      _ = m * c⁻¹ * m := by group
  have hMsq : ∀ m ∈ M, m ^ 2 ∈ CL := by
    intro m hm
    obtain ⟨v, hv, c, hc, hmvc⟩ := hMdecomp m hm
    have hmv := hMcomm m hm.1 v c hc hmvc
    have hc' : c = v⁻¹ * m := by rw [hmvc]; group
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left (hVsq v hv)
    have hc2 : c ^ 2 = m ^ 2 := by
      rw [hc', pow_two, pow_two, hvinv]
      calc v * m * (v * m) = v * (m * v) * m := by group
        _ = v * (v * m) * m := by rw [hmv]
        _ = (v * v) * (m * m) := by group
        _ = m * m := by rw [hVsq v hv, one_mul]
    rw [← hc2]
    exact CL.pow_mem hc 2
  have hM2 : IsPGroup 2 M := by
    intro x
    obtain ⟨k, hk⟩ := central_isTwoElement hC.hyp i (L.pow_mem x.2.1 2) (hMsq x x.2)
    refine ⟨k + 1, Subtype.ext ?_⟩
    rw [pow_succ', pow_mul]
    exact hk
  have hMr : CFSG.Open.pRank 2 M ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left).trans hLr
  obtain ⟨v₁, hv₁, v₂, hv₂, hv₁1, hv₂1, hv₂₁⟩ :=
    AschbacherTheorem3.exists_two_ne_one (show 4 ≤ Nat.card (bar D V) by rw [hVb4.2])
  have hinner : ∀ v ∈ bar D V, ∃ a ∈ L, ∃ c ∈ CL, v = a * c := by
    intro v hv
    have h1 : v ∈ ((L ⊔ CL : Subgroup (Bar D)) : Set (Bar D)) := h2 hv
    rw [hLCprod] at h1
    obtain ⟨a, ha, c, hc, hac⟩ := Set.mem_mul.mp h1
    exact ⟨a, ha, c, hc, hac.symm⟩
  obtain ⟨a₁, ha₁L, c₁, hc₁, hv₁ac⟩ := hinner v₁ hv₁
  obtain ⟨a₂, ha₂L, c₂, hc₂, hv₂ac⟩ := hinner v₂ hv₂
  have haM : ∀ {a c v : Bar D}, a ∈ L → c ∈ CL → v ∈ bar D V → v = a * c → a ∈ M := by
    intro a c v ha hc hv hvac
    refine ⟨ha, ?_⟩
    have h1 : a = v * c⁻¹ := by rw [hvac]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right (CL.inv_mem hc))
  have ha₁M := haM ha₁L hc₁ hv₁ hv₁ac
  have ha₂M := haM ha₂L hc₂ hv₂ hv₂ac
  have ha₁C : a₁ ∉ CL := fun h => hfaith v₁ hv₁ hv₁1 (by rw [hv₁ac]; exact CL.mul_mem h hc₁)
  have ha₂C : a₂ ∉ CL := fun h => hfaith v₂ hv₂ hv₂1 (by rw [hv₂ac]; exact CL.mul_mem h hc₂)
  have ha₁₂C : a₁ * a₂ ∉ CL := by
    intro h
    have hca : c₁ * a₂ = a₂ * c₁ := ((Subgroup.mem_centralizer_iff.mp hc₁) a₂ ha₂L).symm
    have hv12 : v₁ * v₂ ∈ CL := by
      have h1 : v₁ * v₂ = (a₁ * a₂) * (c₁ * c₂) := by
        calc v₁ * v₂ = a₁ * (c₁ * a₂) * c₂ := by rw [hv₁ac, hv₂ac]; group
          _ = a₁ * (a₂ * c₁) * c₂ := by rw [hca]
          _ = (a₁ * a₂) * (c₁ * c₂) := by group
      rw [h1]
      exact CL.mul_mem h (CL.mul_mem hc₁ hc₂)
    have hv121 : v₁ * v₂ ≠ 1 := by
      intro h1
      apply hv₂₁
      rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_left (hVsq v₁ hv₁)]
    exact hfaith _ ((bar D V).mul_mem hv₁ hv₂) hv121 hv12
  have hMnc : ¬ IsCyclic M := by
    intro hcyc
    obtain ⟨x, hx⟩ := hcyc.exists_generator
    have hx2 : ((x : Bar D)) ^ 2 ∈ CL := hMsq x x.2
    have hpowC : ∀ n : ℤ, Even n → (x : Bar D) ^ n ∈ CL := by
      rintro n ⟨t, rfl⟩
      rw [show t + t = 2 * t by ring, zpow_mul]
      exact CL.zpow_mem (by rw [zpow_ofNat]; exact hx2) t
    obtain ⟨n₁, hn₁⟩ := Subgroup.mem_zpowers_iff.mp (hx ⟨a₁, ha₁M⟩)
    obtain ⟨n₂, hn₂⟩ := Subgroup.mem_zpowers_iff.mp (hx ⟨a₂, ha₂M⟩)
    have ha₁x : (x : Bar D) ^ n₁ = a₁ := by
      have h1 := congrArg Subtype.val hn₁
      rwa [Subgroup.coe_zpow] at h1
    have ha₂x : (x : Bar D) ^ n₂ = a₂ := by
      have h1 := congrArg Subtype.val hn₂
      rwa [Subgroup.coe_zpow] at h1
    rcases Int.even_or_odd n₁ with he₁ | ho₁
    · exact ha₁C (ha₁x ▸ hpowC n₁ he₁)
    rcases Int.even_or_odd n₂ with he₂ | ho₂
    · exact ha₂C (ha₂x ▸ hpowC n₂ he₂)
    apply ha₁₂C
    rw [← ha₁x, ← ha₂x, ← zpow_add]
    exact hpowC _ (ho₁.add_odd ho₂)
  have hMq : AschbacherTheorem3.IsQuaternionTwoGroup M :=
    (cyclic_or_quaternion_of_pRank_le_one hM2 hMr).resolve_left hMnc
  obtain ⟨p, hpM, q, hqM, hpq⟩ := exists_q8Pair hMq
  have hnotC : ∀ {p' q' : Bar D}, IsQ8Pair p' q' → q' ∈ L → p' ∉ CL := by
    intro p' q' h hq'L hp'C
    apply h.2.2.2
    have hqp : q' * p' = p' * q' := (Subgroup.mem_centralizer_iff.mp hp'C) q' hq'L
    have h1 := h.2.2.1
    rw [hqp, mul_inv_cancel_right] at h1
    rw [pow_two]
    calc p' * p' = p' * p'⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel p'
  have hCJ : ∀ m ∈ M, m ∉ CL → m ∈ AschbacherToolkit.centralizerJoin (bar D V) := by
    intro m hm hmC
    obtain ⟨v, hv, c, hc, hmvc⟩ := hMdecomp m hm
    have hv1 : v ≠ 1 := by
      rintro rfl
      rw [one_mul] at hmvc
      exact hmC (hmvc ▸ hc)
    have hmv := hMcomm m hm.1 v c hc hmvc
    exact AschbacherToolkit.centralizer_le_centralizerJoin (bar D V) hv hv1
      (Subgroup.mem_centralizer_singleton_iff.mpr hmv)
  have hp2 : p ^ 2 = zb := by
    rcases huniq (p ^ 2) (L.pow_mem hpM.1 2) (by rw [← pow_mul]; exact hpq.1) with h | h
    · exact absurd h hpq.2.2.2
    · exact h
  refine ⟨p, q, hpq, hpM.1, hqM.1, hCJ p hpM (hnotC hpq hqM.1),
    hCJ q hqM (hnotC hpq.swap hpM.1), hp2 ▸ hzbC, fun t ht ht2 => hp2 ▸ huniq t ht ht2⟩

end RankOne

end DeltaLocal

end CFSG.ComponentClassification.AschbacherTheorem5
