module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Pair
public import CFSG.Quasithin.H13.NQTermThompsonFactorization
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

section Bridge

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_map_subtype_iff {R : Subgroup G} (B : Subgroup R) :
    CFSG.Open.IsElemAbelian 2 B ↔ CFSG.Open.IsElemAbelian 2 (B.map R.subtype) := by
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', haa⟩ := a.2
      obtain ⟨b', hb', hbb⟩ := b.2
      apply Subtype.ext
      have h : (⟨a', ha'⟩ : B) * ⟨b', hb'⟩ = ⟨b', hb'⟩ * ⟨a', ha'⟩ := hc.is_comm.comm _ _
      have this : (a' : G) * (b' : G) = (b' : G) * (a' : G) :=
        congrArg (fun z : B => ((z : R) : G)) h
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← haa, ← hbb]
      exact this
    · rintro _ ⟨y, hy, rfl⟩
      show (y : G) ^ 2 = 1
      rw [← Subgroup.coe_pow, hp y hy]; rfl
  · rintro ⟨hc, hp⟩
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val (hc.is_comm.comm ⟨(a : G), a, a.2, rfl⟩ ⟨(b : G), b, b.2, rfl⟩)
      exact this
    · apply Subtype.ext
      have := hp (x : G) ⟨x, hx, rfl⟩
      exact this

theorem card_subgroupOf_of_le {R B : Subgroup G} (h : B ≤ R) :
    Nat.card (B.subgroupOf R) = Nat.card B :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem isMax_map_subtype {R S : Subgroup G} (hSR : S ≤ R) (A : Subgroup R) :
    CFSG.Quasithin.IsMaxElemAbelian (S.subgroupOf R) A ↔
      CFSG.Quasithin.IsMaxElemAbelian S (A.map R.subtype) := by
  unfold CFSG.Quasithin.IsMaxElemAbelian
  have hcard : Nat.card (A.map R.subtype) = Nat.card A :=
    Subgroup.card_map_of_injective R.subtype_injective
  constructor
  · rintro ⟨hA, hel, hmax⟩
    refine ⟨?_, (isElemAbelian_map_subtype_iff A).1 hel, fun B hBS hB => ?_⟩
    · rintro _ ⟨a, ha, rfl⟩; exact hA ha
    · have hBR : B ≤ R := hBS.trans hSR
      have hB' : B.subgroupOf R ≤ S.subgroupOf R := fun x hx => hBS hx
      have hBel : CFSG.Open.IsElemAbelian 2 (B.subgroupOf R) :=
        (isElemAbelian_map_subtype_iff (B.subgroupOf R)).2
          (by rwa [Subgroup.map_subgroupOf_eq_of_le hBR])
      have := hmax _ hB' hBel
      rw [card_subgroupOf_of_le hBR] at this
      omega
  · rintro ⟨hA, hel, hmax⟩
    refine ⟨?_, (isElemAbelian_map_subtype_iff A).2 hel, fun B hBS hB => ?_⟩
    · intro a ha
      exact hA ⟨a, ha, rfl⟩
    · have hBle : B.map R.subtype ≤ S := by
        rintro _ ⟨b, hb, rfl⟩; exact hBS hb
      have := hmax _ hBle ((isElemAbelian_map_subtype_iff B).1 hB)
      rw [Subgroup.card_map_of_injective R.subtype_injective] at this
      omega

theorem thompsonJ_map_subtype {R S : Subgroup G} (hSR : S ≤ R) :
    (CFSG.Quasithin.thompsonJ (S.subgroupOf R)).map R.subtype = CFSG.Quasithin.thompsonJ S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (A.map R.subtype) ((isMax_map_subtype hSR A).1 hA) le_rfl
  · refine iSup₂_le fun E hE => ?_
    have hER : E ≤ R := hE.1.trans hSR
    have hE' : CFSG.Quasithin.IsMaxElemAbelian (S.subgroupOf R) (E.subgroupOf R) := by
      rw [isMax_map_subtype hSR, Subgroup.map_subgroupOf_eq_of_le hER]; exact hE
    have : E = (E.subgroupOf R).map R.subtype := (Subgroup.map_subgroupOf_eq_of_le hER).symm
    rw [this]
    exact Subgroup.map_mono (le_iSup₂_of_le (E.subgroupOf R) hE' le_rfl)

theorem jOf_eq_thompsonJ (S : Subgroup G) : jOf S = CFSG.Quasithin.thompsonJ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 2 E → ∃ j, Nat.card E = 2 ^ j := by
    intro E hE
    have hp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
    exact (IsPGroup.iff_card (p := 2)).1 hp
  apply le_antisymm
  · refine iSup₂_le fun E hE => le_iSup₂_of_le E ⟨hE.1, hE.2.1, fun B hBS hB => ?_⟩ le_rfl
    obtain ⟨j, hj⟩ := h2 B hB
    have := CFSG.SectionRank.le_pRank Nat.one_lt_two hBS hB hj
    rw [hj, hE.2.2]
    exact Nat.pow_le_pow_right (by norm_num) this
  · refine iSup₂_le fun A hA => le_iSup₂_of_le A ⟨hA.1, hA.2.1, ?_⟩ le_rfl
    obtain ⟨B, hBS, hBel, hBc⟩ := CFSG.SectionRank.exists_pRank Nat.one_lt_two S
    have h1 := hA.2.2 B hBS hBel
    obtain ⟨j, hj⟩ := h2 A hA.2.1
    have hjle := CFSG.SectionRank.le_pRank Nat.one_lt_two hA.1 hA.2.1 hj
    have h3 : 2 ^ j ≤ 2 ^ CFSG.Open.pRank 2 S := Nat.pow_le_pow_right (by norm_num) hjle
    rw [hBc] at h1
    rw [hj] at h1 ⊢
    exact le_antisymm h3 h1

theorem centerOf_eq_inf (S : Subgroup G) : centerOf S = S ⊓ Subgroup.centralizer (S : Set G) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun s hs => ?_⟩
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨s, hs⟩)
  · rintro ⟨hxS, hxc⟩
    refine ⟨⟨x, hxS⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g g.2)

theorem omegaOneZ_eq (S : Subgroup G) : omegaOneZ S = CFSG.Open.quasithinOmegaOneCenter S := by
  unfold omegaOneZ CFSG.Open.quasithinOmegaOneCenter
  rw [centerOf_eq_inf]

theorem map_quasithinOmegaOneCenter {R S : Subgroup G} (hSR : S ≤ R) :
    (CFSG.Open.quasithinOmegaOneCenter (S.subgroupOf R)).map R.subtype =
      CFSG.Open.quasithinOmegaOneCenter S := by
  unfold CFSG.Open.quasithinOmegaOneCenter
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨z, ⟨⟨hzS, hzc⟩, hz2⟩, rfl⟩
    refine ⟨⟨hzS, fun s hs => ?_⟩, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hzc ⟨s, hSR hs⟩ hs)
    · exact congrArg Subtype.val hz2
  · rintro ⟨⟨hxS, hxc⟩, hx2⟩
    refine ⟨⟨x, hSR hxS⟩, ⟨⟨hxS, fun s hs => Subtype.ext ?_⟩, Subtype.ext ?_⟩, rfl⟩
    · exact Subgroup.mem_centralizer_iff.1 hxc s hs
    · exact hx2

theorem mem_normalizer_map_subtype {R : Subgroup G} {J : Subgroup R} {n : R}
    (hn : n ∈ Subgroup.normalizer (J : Set R)) :
    (n : G) ∈ Subgroup.normalizer ((J.map R.subtype : Subgroup G) : Set G) := by
  have key : ∀ {n : R}, n ∈ Subgroup.normalizer (J : Set R) → ∀ y ∈ J.map R.subtype,
      (n : G) * y * (n : G)⁻¹ ∈ J.map R.subtype := by
    rintro n hn _ ⟨j, hj, rfl⟩
    exact ⟨n * j * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn j).1 hj, by simp⟩
  exact mem_normalizer_of_conj_mem' (key hn) (fun y hy => by
    simpa using key (inv_mem hn) y hy)

theorem layer_eq_bot_of_solvable' {X : Type*} [Group X] [Group.IsSolvable X] : CFSG.layer X = ⊥ :=
  CFSG.WholeGroup.layer_eq_bot_of_isSolvable

theorem pair_zero_two {R S : Subgroup G} (hRs : Group.IsSolvable ↥R) (h3 : ¬ 3 ∣ Nat.card R)
    (hO : ∀ N : Subgroup G, N ≤ R → R ≤ Subgroup.normalizer (N : Set G) → ¬ 2 ∣ Nat.card N →
      N = ⊥)
    (hSR : S ≤ R) (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex R) :
    ((Subgroup.normalizer (jOf S : Set G) ⊓ R : Subgroup G) : Set G) *
      ((Subgroup.normalizer (omegaOneZ S : Set G) ⊓ R : Subgroup G) : Set G) = (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS'2 : IsPGroup 2 (S.subgroupOf R) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSR).symm
  have hS'idx : ¬ 2 ∣ (S.subgroupOf R).index := hSidx
  let T : Sylow 2 ↥R := hS'2.toSylow hS'idx
  have hcore : CFSG.pPrimeCore 2 ↥R = ⊥ := by
    refine eq_bot_iff.2 (sSup_le fun K hK => ?_)
    obtain ⟨hKn, hKc⟩ := hK
    have hodd : ¬ 2 ∣ Nat.card K := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hKc
    have hbot := hO (K.map R.subtype) (by rintro _ ⟨k, -, rfl⟩; exact k.2)
      (fun r hr => by
        have key : ∀ r : R, ∀ y ∈ K.map R.subtype, (r : G) * y * (r : G)⁻¹ ∈ K.map R.subtype := by
          rintro r _ ⟨k, hk, rfl⟩
          exact ⟨r * k * r⁻¹, hKn.conj_mem k hk r, by simp⟩
        exact mem_normalizer_of_conj_mem' (key ⟨_, hr⟩) (fun y hy => by
          simpa using key ⟨_, R.inv_mem hr⟩ y hy))
      (by rwa [Subgroup.card_map_of_injective R.subtype_injective])
    exact le_of_eq ((Subgroup.map_eq_bot_iff_of_injective K R.subtype_injective).1 hbot)
  have hchar : CFSG.IsCharacteristicP 2 ↥R :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot ↥R 2 hcore
      layer_eq_bot_of_solvable'
  have hF := (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥R 2).1 hchar
  obtain ⟨-, -, -, -, -, -, hNC, -⟩ :=
    CFSG.Quasithin.H13.NQTerm.solvable_characteristic_two_three_free_thompson_factorization
      (G := ↥R) hF h3 T (Z := CFSG.Open.quasithinOmegaOneCenter (T : Subgroup ↥R))
      (U := Subgroup.normalClosure
        ((CFSG.Open.quasithinOmegaOneCenter (T : Subgroup ↥R) : Subgroup ↥R) : Set ↥R))
      (J := (CFSG.elemThompson (T : Subgroup ↥R) 2).map (T : Subgroup ↥R).subtype)
      rfl rfl rfl
  have hTS : (T : Subgroup ↥R) = S.subgroupOf R := rfl
  have hJ : ((CFSG.elemThompson (T : Subgroup ↥R) 2).map (T : Subgroup ↥R).subtype).map
      R.subtype = jOf S := by
    rw [CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ, hTS,
      thompsonJ_map_subtype hSR, jOf_eq_thompsonJ]
  have hZ : (CFSG.Open.quasithinOmegaOneCenter (T : Subgroup ↥R)).map R.subtype =
      omegaOneZ S := by
    rw [hTS, map_quasithinOmegaOneCenter hSR, omegaOneZ_eq]
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ⟨-, haR⟩, b, ⟨-, hbR⟩, rfl⟩
    exact R.mul_mem haR hbR
  · intro x hx
    have hmem : (⟨x, hx⟩ : ↥R) ∈ ((Subgroup.normalizer
        (((CFSG.elemThompson (T : Subgroup ↥R) 2).map (T : Subgroup ↥R).subtype : Subgroup ↥R) :
          Set ↥R) : Set ↥R)) *
        ((Subgroup.centralizer ((CFSG.Open.quasithinOmegaOneCenter (T : Subgroup ↥R) :
          Subgroup ↥R) : Set ↥R) : Subgroup ↥R) : Set ↥R) := hNC ▸ Set.mem_univ _
    obtain ⟨n, hn, c, hc, hnc⟩ := hmem
    refine ⟨n, ⟨?_, n.2⟩, c, ⟨?_, c.2⟩, congrArg Subtype.val hnc⟩
    · have := mem_normalizer_map_subtype hn
      rwa [hJ] at this
    · have hc' : (c : G) ∈ Subgroup.centralizer
          (((CFSG.Open.quasithinOmegaOneCenter (T : Subgroup ↥R)).map R.subtype : Subgroup G) :
            Set G) := by
        rintro _ ⟨z, hz, rfl⟩
        exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 hc) z hz)
      rw [hZ] at hc'
      have hcomm : ∀ y ∈ omegaOneZ S, (c : G) * y * (c : G)⁻¹ = y := fun y hy => by
        have := Subgroup.mem_centralizer_iff.1 hc' y hy
        rw [← this, mul_assoc, mul_inv_cancel, mul_one]
      exact mem_normalizer_of_conj_mem' (fun y hy => by rw [hcomm y hy]; exact hy)
        (fun y hy => by
          have h := Subgroup.mem_centralizer_iff.1 hc' y hy
          rw [mul_assoc, h, inv_mul_cancel_left]; exact hy)

theorem set_mul_comm_of_eq {R A B : Subgroup G} (hA : A ≤ R) (hB : B ≤ R)
    (h : (A : Set G) * (B : Set G) = (R : Set G)) : (B : Set G) * (A : Set G) = (R : Set G) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨b, hb, a, ha, rfl⟩
    exact R.mul_mem (hB hb) (hA ha)
  · intro x hx
    have : x⁻¹ ∈ (A : Set G) * (B : Set G) := h ▸ R.inv_mem hx
    obtain ⟨a, ha, b, hb, hab⟩ := this
    refine ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha, ?_⟩
    show b⁻¹ * a⁻¹ = x
    rw [← mul_inv_rev]
    have hab' : a * b = x⁻¹ := hab
    rw [hab', inv_inv]

theorem th1_of_th1J1 (h : Th1J1Factorization) : Th1Factorization := by
  intro G _ _ R S hRs h3 h5 hO hSR hS2 hSidx i j hij
  have hN : ∀ k : Fin 3, (Subgroup.normalizer (tripleOf S k : Set G) ⊓ R) ≤ R := fun k => inf_le_right
  have h1 := fun k (hk : k ≠ 1) => h G R S hRs h3 h5 hO hSR hS2 hSidx k hk
  rcases Sec7.fin_three_cases i with rfl | rfl | rfl <;>
    rcases Sec7.fin_three_cases j with rfl | rfl | rfl
  · exact absurd rfl hij
  · exact h1 0 (by decide)
  · exact pair_zero_two hRs h3 hO hSR hS2 hSidx
  · exact set_mul_comm_of_eq (hN 0) (hN 1) (h1 0 (by decide))
  · exact absurd rfl hij
  · exact set_mul_comm_of_eq (hN 2) (hN 1) (h1 2 (by decide))
  · exact set_mul_comm_of_eq (hN 0) (hN 2) (pair_zero_two hRs h3 hO hSR hS2 hSidx)
  · exact h1 2 (by decide)
  · exact absurd rfl hij

end Bridge

theorem input28_8_of_th1J1 (h : Th1J1Factorization) :
    Input28_8 :=
  input28_8_of_th1 (th1_of_th1J1 h)

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8
