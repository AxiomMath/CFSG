module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec83a
import CFSG.Goldschmidt.Steps.Sec8Bender
import CFSG.Goldschmidt.Steps.Sec8Comp
import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.Walter.Bender1970.S4.ComponentTools
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem two_le_card_primesOfOrder (h64 : S_G64) (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ Walter.benderM a) :
    2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) := by
  obtain ⟨ha2, -⟩ := mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  have haF : a ∈ generalizedFittingSubgroupOf H :=
    le_sup_left (a := CFSG.fittingSubgroupOf H)
      (qCoreOf_le_fittingSubgroupOf H 2 Nat.prime_two ha2)
  have hF1 : generalizedFittingSubgroupOf H ≠ ⊥ := fun h => ha1 (by
    rw [h] at haF
    exact Subgroup.mem_bot.mp haF)
  have h1 := Walter.one_le_card_primesOfOrder hF1
  by_contra hlt
  obtain ⟨q, hq, hFq, -⟩ := Walter.exists_isPGroup_of_card_primesOfOrder_eq_one
    (X := generalizedFittingSubgroupOf H) (by omega)
  exact not_isPGroup_fstar h64 hset h4 ha ha1 hH hq hFq

theorem eq_of_le_centralizer (h64 : S_G64) (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a) {p : ℕ}
    (hp : p.Prime) {P : Subgroup G} (hP : P ≤ qCoreOf H p) {M : Subgroup G} (hM : IsCoatom M)
    (hPM : Subgroup.normalizer (P : Set G) ≤ M) (haF : a ∈ generalizedFittingSubgroupOf M)
    (haE : componentLayerOf M ≤ Subgroup.centralizer ({a} : Set G)) : M = H := by
  have := hset.isSimpleGroup
  obtain ⟨-, hHa⟩ := mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  obtain ⟨hXF, hXsub, hXC, hXN⟩ := benderX H hp hP
  set Y := generalizedFittingSubgroupOf M ⊓ Subgroup.centralizer ({a} : Set G) with hY
  have hYH : Y ≤ H := hHa ▸ inf_le_right
  have hYF : Y ≤ generalizedFittingSubgroupOf M := inf_le_left
  have hEY : componentLayerOf M ≤ Y := le_inf le_sup_right haE
  have haY : a ∈ Y := ⟨haF, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hYC : generalizedFittingSubgroupOf M ⊓ Subgroup.centralizer (Y : Set G) ≤ Y :=
    fun z hz => ⟨hz.1, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz.2 a haY).symm⟩
  exact (bender1970_1_7_iii_equalityOfMaximal this H (Walter.isCoatom_of_mem_benderM hH) _ hXF
    hXsub hXC (hXN.trans hPM) hM (Or.inl (two_le_card_primesOfOrder h64 hset h4 ha ha1 hH))
    ⟨Y, hYH, hYF, Walter.isSubnormal_of_componentLayerOf_le hEY hYF, hYC⟩).symm

theorem commutator_mem_oddCoreOf_of_mem (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a) {b h : G}
    (hb : b ∈ A) (hh : h ∈ H) : b * h * b⁻¹ * h⁻¹ ∈ oddCoreOf H := by
  obtain ⟨-, hHO⟩ := eq_oddCoreOf_sup hset h4 ha ha1 hH
  have hCH : Subgroup.centralizer (A : Set G) ≤ H := hHO ▸ le_sup_right
  have hbH : b ∈ H := hset.le.trans (le_of_mem_benderM hset h4 ha hH) hb
  have hh' : h ∈ ((oddCoreOf H ⊔ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
    hHO ▸ hh
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (oddCoreOf H) _
    (hCH.trans (le_normalizer_oddCoreOf H))] at hh'
  obtain ⟨y, hy, c, hc, rfl⟩ := Set.mem_mul.mp hh'
  have hcb : c * b⁻¹ * c⁻¹ = b⁻¹ := by
    rw [← Subgroup.mem_centralizer_iff.mp hc b⁻¹ (A.inv_mem hb)]; group
  have h1 : b * y * b⁻¹ ∈ oddCoreOf H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreOf H hbH) y).mp hy
  have e : b * (y * c) * b⁻¹ * (y * c)⁻¹ = b * y * b⁻¹ * y⁻¹ := by
    calc b * (y * c) * b⁻¹ * (y * c)⁻¹ = b * y * (c * b⁻¹ * c⁻¹) * y⁻¹ := by group
      _ = b * y * b⁻¹ * y⁻¹ := by rw [hcb]
  rw [e]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy)

theorem false_of_isComponentOf_le (h31 : S_G31) (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a)
    {M L : Subgroup G} (hS : IsSStarIn M A)
    (hL : GorensteinWalter.IsComponentOf L (normalClosureIn M A)) (hLH : L ≤ H) : False := by
  have hAL := le_of_isComponentOf h31 hS hset.elem h4 hL
  have hnot := G73.not_inf_le_centralizer h31 hS hset.elem hL
  set N := L ⊓ oddCoreOf H with hN
  have hLL : GorensteinWalter.IsComponentOf L L := ⟨le_rfl, by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.IsSubnormal.top, hL.2.2⟩
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := fun l hl =>
    mem_normalizer_inf (Subgroup.le_normalizer hl) (le_normalizer_oddCoreOf H (hLH hl))
  have hNC : N ≤ Subgroup.centralizer (L : Set G) := by
    rcases Walter.isComponentOf_le_or_commutator_eq_bot hLL inf_le_left hLN with h | h
    · exfalso
      have : Group.IsPerfect L := Walter.isPerfect_of_isComponentOf hL
      exact Walter.ne_bot_of_isComponentOf hL (Walter.eq_bot_of_isPerfect_of_le_isSolvable
        (h.trans inf_le_right) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCoreOf H)))
    · exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  have hAL' : ⁅A, L⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro b hb l hl
    exact ⟨L.mul_mem (L.mul_mem (L.mul_mem (hAL hb) hl) (L.inv_mem (hAL hb))) (L.inv_mem hl),
      commutator_mem_oddCoreOf_of_mem hset h4 ha ha1 hH hb (hLH hl)⟩
  have h1 : ⁅⁅A, L⁆, L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hAL'.trans hNC)
  have h2 : ⁅⁅L, A⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L A]; exact h1
  have h3 : ⁅⁅L, L⁆, A⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [G73.commutator_self_of_isComponentOf hL] at h3
  exact hnot fun x hx => Subgroup.le_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3) hx.1

omit [Finite G] in
theorem exists_sylow_eq_subgroupOf {N K T : Subgroup G} (hT : fusionIsSylowIn 2 T N)
    (hKN : K ≤ N) (hTK : T ≤ K) :
    ∃ P : Sylow 2 K, (P : Subgroup K) = T.subgroupOf K := by
  obtain ⟨P, hP⟩ := (hT.2.1.comap_subtype (K := K)).exists_le_sylow
  refine ⟨P, le_antisymm ?_ hP⟩
  have heq := hT.2.2 ((P : Subgroup K).map K.subtype) ((Subgroup.map_subtype_le _).trans hKN)
    (P.isPGroup'.map _) (fun t ht => ⟨⟨t, hTK ht⟩, hP (Subgroup.mem_subgroupOf.mpr ht), rfl⟩)
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr (heq ▸ ⟨x, hx, rfl⟩)

theorem exists_conj_normalizer_sylow {N T : Subgroup G} (hT : fusionIsSylowIn 2 T N) {x m : G}
    (hm : m ∈ N) (hxT : T ≤ Subgroup.centralizer ({x} : Set G))
    (hyT : T ≤ Subgroup.centralizer ({m⁻¹ * x * m} : Set G)) :
    ∃ n ∈ N, n ∈ Subgroup.normalizer (T : Set G) ∧ n⁻¹ * x * n = m⁻¹ * x * m := by
  set y := m⁻¹ * x * m with hy
  set K := N ⊓ Subgroup.centralizer ({y} : Set G) with hK
  set T' := conjSub m T with hT'
  have hTK : T ≤ K := le_inf hT.1 hyT
  have hT'N : T' ≤ N := fun z hz => by
    have := N.mul_mem (N.mul_mem (N.inv_mem hm) (hT.1 (mem_conjSub.mp hz))) hm
    simpa [mul_assoc] using this
  have hT'K : T' ≤ K := by
    refine le_inf hT'N fun z hz => ?_
    have hz' := Subgroup.mem_centralizer_singleton_iff.mp (hxT (mem_conjSub.mp hz))
    rw [Subgroup.mem_centralizer_singleton_iff, hy]
    calc z * (m⁻¹ * x * m) = m⁻¹ * ((m * z * m⁻¹) * x) * m := by group
      _ = m⁻¹ * (x * (m * z * m⁻¹)) * m := by rw [hz']
      _ = m⁻¹ * x * m * z := by group
  have hT'syl : fusionIsSylowIn 2 T' N := by
    refine ⟨hT'N, hT.2.1.map _, fun Q hQN hQ hT'Q => ?_⟩
    have h1 := hT.2.2 (conjSub m⁻¹ Q) (fun z hz => by
        have := N.mul_mem (N.mul_mem hm (hQN (mem_conjSub.mp hz))) (N.inv_mem hm)
        simpa [mul_assoc] using this) (hQ.map _) (fun t ht => mem_conjSub.mpr (by
        refine hT'Q (mem_conjSub.mpr ?_)
        simpa [mul_assoc] using ht))
    rw [hT', ← h1, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  obtain ⟨P₁, hP₁⟩ := exists_sylow_eq_subgroupOf hT inf_le_left hTK
  obtain ⟨P₂, hP₂⟩ := exists_sylow_eq_subgroupOf hT'syl inf_le_left hT'K
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K P₁ P₂
  have hcT : ∀ t ∈ T, (c : G) * t * (c : G)⁻¹ ∈ T' := fun t ht => by
    have h1 : (⟨t, hTK ht⟩ : K) ∈ (P₁ : Subgroup K) := hP₁ ▸ Subgroup.mem_subgroupOf.mpr ht
    have h2 : c * ⟨t, hTK ht⟩ * c⁻¹ ∈ (P₂ : Subgroup K) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ h1
    rw [hP₂] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hcK : (c : G) ∈ K := c.2
  refine ⟨m * c, N.mul_mem hm hcK.1, ?_, ?_⟩
  · have hle : T ≤ conjSub (m * c) T := by
      intro t ht
      rw [mem_conjSub]
      have h1 := hcT t ht
      rw [hT', mem_conjSub] at h1
      simpa [mul_assoc] using h1
    have heq : T = conjSub (m * c) T :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
    refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
    rw [← mem_conjSub, ← heq]
  · have hcy : (c : G) * y = y * (c : G) := Subgroup.mem_centralizer_singleton_iff.mp hcK.2
    calc (m * (c : G))⁻¹ * x * (m * (c : G)) = ((c : G))⁻¹ * y * (c : G) := by rw [hy]; group
      _ = y := by rw [mul_assoc, ← hcy, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_mem_normalizer_of_isComponentOf (h31 : S_G31) (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) {M L : Subgroup G} (hS : IsSStarIn M A)
    (hL : GorensteinWalter.IsComponentOf L (normalClosureIn M A)) :
    ∃ n ∈ M, n ∈ Subgroup.normalizer (A : Set G) ∧ n ∉ Subgroup.centralizer (A : Set G) := by
  have hAL := le_of_isComponentOf h31 hS hset.elem h4 hL
  have hnot := G73.not_inf_le_centralizer h31 hS hset.elem hL
  have hLM := G73.isComponentOf_of_normalClosureIn hL
  have hLO : oddCoreOf M ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.le_centralizer_iff.mp (G73.le_centralizer_oddCoreOf hLM)
  obtain ⟨x, ⟨hxA, -⟩, hxL⟩ := Set.not_subset.mp hnot
  obtain ⟨-, -, T, hT, hAT, hcl, -⟩ := id hS
  have hTA : T ≤ Subgroup.centralizer (A : Set G) := pGroup_le_centralizer hset h4 hT.2.1 hAT
  have hTx : ∀ z ∈ A, T ≤ Subgroup.centralizer ({z} : Set G) := fun z hz =>
    hTA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz))
  have hx1 : x ≠ 1 := fun h => hxL (h ▸ Subgroup.one_mem _)
  have hx2 : x * x = 1 := mul_self_eq_one hset.elem hxA
  obtain ⟨m, hm, hmT, hmx⟩ : ∃ m ∈ M, m⁻¹ * x * m ∈ T ∧ m⁻¹ * x * m ≠ x := by
    by_contra hiso
    simp only [not_exists, not_and, not_not] at hiso
    have hz := fun m hm => commutator_mem_oddCoreOf hT (hAT hxA) (hTx x hxA) hx2 hx1
      (fun g hg hgT => hiso g hg hgT) (g := m) hm
    have hx' : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx2]
    have hcomm : ⁅L, Subgroup.zpowers x⁆ ≤ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.commutator_le]
      intro l hl g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [zpow_eq_zpow_emod k hx']
      rcases Int.emod_two_eq_zero_or_one k with hk | hk
      · rw [hk, zpow_zero]
        simp
      · rw [hk, zpow_one]
        exact hLO (hz l (hLM.1 hl))
    have h1 : ⁅⁅L, Subgroup.zpowers x⁆, L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcomm
    have h2 : ⁅⁅Subgroup.zpowers x, L⁆, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (Subgroup.zpowers x) L]; exact h1
    have h3 : ⁅⁅L, L⁆, Subgroup.zpowers x⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [G73.commutator_self_of_isComponentOf hL] at h3
    exact hxL (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
      (Subgroup.mem_zpowers x))
  have hyA : m⁻¹ * x * m ∈ A := hcl x hxA m hm hmT
  obtain ⟨n, hnM, hnT, hn⟩ := exists_conj_normalizer_sylow hT hm (hTx x hxA) (hTx _ hyA)
  have hnA : n ∈ Subgroup.normalizer (A : Set G) := by
    have hle : conjSub n A ≤ A := by
      rintro _ ⟨z, hz, rfl⟩
      have h1 : n⁻¹ * z * n ∈ T := by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnT) z).mp (hAT hz)
      simpa [MulAut.conj_apply] using hcl z hz n hnM h1
    have heq : conjSub n A = A :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
    refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
    rw [← mem_conjSub, heq]
  refine ⟨n, hnM, hnA, fun hnC => hmx ?_⟩
  rw [← hn]
  have := conj_eq_of_mem_centralizer (Subgroup.inv_mem _ hnC) hxA
  simpa using this

end CFSG.Goldschmidt.Sec8
