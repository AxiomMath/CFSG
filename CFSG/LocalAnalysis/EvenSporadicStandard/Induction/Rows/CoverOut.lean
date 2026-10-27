module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OutLocalQ

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 Cover

section

variable {H : Type} [Group H]

theorem twoAdic_subgroupOf {L K : Subgroup H} (hKL : K ≤ L) :
    twoAdic (K.subgroupOf L) = twoAdic K := by
  unfold twoAdic
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]

theorem subgroupOf_inf_centralizer {L K : Subgroup H} {z : ↥L} :
    K.subgroupOf L ⊓ centralizer ({z} : Set ↥L) =
      (K ⊓ centralizer ({(z : H)} : Set H)).subgroupOf L := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
  exact and_congr Iff.rfl ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem twoAdic_subgroupOf_inf_centralizer {L K : Subgroup H} (hKL : K ≤ L) {z : ↥L} :
    twoAdic (K.subgroupOf L ⊓ centralizer ({z} : Set ↥L)) =
      twoAdic (K ⊓ centralizer ({(z : H)} : Set H)) := by
  rw [subgroupOf_inf_centralizer]
  exact twoAdic_subgroupOf (inf_le_left.trans hKL)

end

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}

theorem outFacts_of_quotient (hodd : Odd (Nat.card (center ↥L)))
    (hLperf : Group.IsPerfect ↥L) (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hKperf : Group.IsPerfect ↥K)
    (F : OutFacts (⊤ : Subgroup (↥L ⧸ center ↥L)) ((K.subgroupOf L).map (q ↥L))
      (q ↥L ⟨u, hu⟩)) : OutFacts L K u := by
  classical
  have hK'perf : Group.IsPerfect ↥(K.subgroupOf L) := isPerfect_subgroupOf_of_le hKL hKperf
  have hK'perf' : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L := isPerfect_iff.mp hK'perf
  have hLtop : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact Group.isPerfect_def.1 hLperf
  have hu'2 : (⟨u, hu⟩ : ↥L) * ⟨u, hu⟩ = 1 := Subtype.ext (mul_self_eq_one_of_orderOf hu2)
  have hKu' : ∀ k ∈ K.subgroupOf L, k * (⟨u, hu⟩ : ↥L) = ⟨u, hu⟩ * k := fun k hk =>
    Subtype.ext (hKu k (Subgroup.mem_subgroupOf.1 hk))
  obtain ⟨huK, hZ, hfuse, hnorm, zt, hzt, hzt2, hzt1, hztm, ⟨lt, -, hltconj⟩, hnoconj, hgen⟩ := F
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro huKK
    exact huK ⟨⟨u, hu⟩, Subgroup.mem_subgroupOf.2 huKK, rfl⟩
  ·
    intro x hx hxc
    have hx' : (⟨x, hKL hx⟩ : ↥L) ∈ K.subgroupOf L := Subgroup.mem_subgroupOf.2 hx
    have hcen : ∀ kt ∈ (K.subgroupOf L).map (q ↥L),
        kt * q ↥L ⟨x, hKL hx⟩ = q ↥L ⟨x, hKL hx⟩ * kt := by
      rintro _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hxc k (Subgroup.mem_subgroupOf.1 hk)).symm
    have h1 := hZ (q ↥L ⟨x, hKL hx⟩) ⟨_, hx', rfl⟩ (fun kt hkt => (hcen kt hkt).symm)
    have h2 := odd_orderOf_of_mk hodd h1
    rwa [Subgroup.orderOf_mk] at h2
  ·
    exact twoCentralFused_of_equiv (Subgroup.subgroupOfEquivOfLe hKL).symm
      (twoCentralFused_of_quotient hodd hfuse)
  ·
    intro c hc
    obtain ⟨hcL, hcu⟩ := hc
    have hcu' : (⟨c, hcL⟩ : ↥L) * ⟨u, hu⟩ = ⟨u, hu⟩ * ⟨c, hcL⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.1 hcu)
    have hcq : q ↥L ⟨c, hcL⟩ ∈ (⊤ : Subgroup (↥L ⧸ center ↥L)) ⊓
        centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L)) :=
      ⟨Subgroup.mem_top _, mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hcu'])⟩
    have h1 := hnorm _ hcq
    have h2 : (K.subgroupOf L).map (conjHom (⟨c, hcL⟩ : ↥L)) = K.subgroupOf L := by
      refine map_conj_eq_of_perfect hK'perf' fun k hk => ?_
      have : q ↥L (⟨c, hcL⟩ * k * ⟨c, hcL⟩⁻¹) ∈ ((K.subgroupOf L).map (q ↥L)).map
          (conjHom (q ↥L ⟨c, hcL⟩)) := ⟨_, ⟨k, hk, rfl⟩, by simp⟩
      rwa [h1] at this
    have hle : K.map (conjHom c) ≤ K := by
      rintro _ ⟨k, hk, rfl⟩
      have : (⟨c, hcL⟩ * ⟨k, hKL hk⟩ * ⟨c, hcL⟩⁻¹ : ↥L) ∈ K.subgroupOf L := by
        rw [← h2]
        exact ⟨⟨k, hKL hk⟩, Subgroup.mem_subgroupOf.2 hk, by simp⟩
      exact Subgroup.mem_subgroupOf.1 this
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (conjHom_injective c)])
  ·
    obtain ⟨z', hz'K, hz'2, hz'q⟩ := exists_involution_lift hodd hzt hzt2
    obtain ⟨l', hl'q⟩ : ∃ l' : ↥L, q ↥L l' = lt := QuotientGroup.mk_surjective lt
    have hz1 : (z' : H) ≠ 1 := fun h => hzt1 (by
      rw [← hz'q, show z' = 1 from Subtype.ext h, map_one])
    have hz'c : z' * (⟨u, hu⟩ : ↥L) = ⟨u, hu⟩ * z' := hKu' z' hz'K
    refine ⟨(z' : H), Subgroup.mem_subgroupOf.1 hz'K, congrArg Subtype.val hz'2, hz1, ?_,
      ⟨(l' : H), l'.2, ?_⟩, ?_, ?_⟩
    · have h1 : twoAdic ((K.subgroupOf L).map (q ↥L)) = twoAdic K :=
        (twoAdic_map_eq hodd _).trans (twoAdic_subgroupOf hKL)
      have h2 := twoAdic_inf_centralizer_map_eq hodd (K.subgroupOf L) hz'2
      have h3 := twoAdic_subgroupOf_inf_centralizer hKL (z := z')
      rw [← h1, ← h3, ← h2, hz'q]
      exact hztm
    · have hmk : q ↥L (l' * ⟨u, hu⟩ * l'⁻¹) = q ↥L (⟨u, hu⟩ * z') := by
        rw [map_mul, map_mul, map_inv, map_mul, hl'q, hz'q]
        exact hltconj
      have hsq1 : (l' * ⟨u, hu⟩ * l'⁻¹) * (l' * ⟨u, hu⟩ * l'⁻¹) = 1 := by
        calc (l' * ⟨u, hu⟩ * l'⁻¹) * (l' * ⟨u, hu⟩ * l'⁻¹)
            = l' * (⟨u, hu⟩ * ⟨u, hu⟩) * l'⁻¹ := by group
          _ = 1 := by rw [hu'2]; group
      have hsq2 : (⟨u, hu⟩ * z') * (⟨u, hu⟩ * z') = 1 := by
        calc (⟨u, hu⟩ * z') * (⟨u, hu⟩ * z') = ⟨u, hu⟩ * (z' * ⟨u, hu⟩) * z' := by group
          _ = ⟨u, hu⟩ * (⟨u, hu⟩ * z') * z' := by rw [hz'c]
          _ = (⟨u, hu⟩ * ⟨u, hu⟩) * (z' * z') := by group
          _ = 1 := by rw [hu'2, hz'2, one_mul]
      exact congrArg Subtype.val (Closing.eq_of_mk_eq_of_sq hodd hsq1 hsq2 hmk)
    · intro l hl hconj
      apply hnoconj (q ↥L ⟨l, hl⟩) (Subgroup.mem_top _)
      rw [← hz'q]
      have : (⟨l, hl⟩ * ⟨u, hu⟩ * ⟨l, hl⟩⁻¹ : ↥L) = z' := Subtype.ext hconj
      rw [← this, map_mul, map_mul, map_inv]
    · intro l hl hconj
      have hconj' : (⟨l, hl⟩ * ⟨u, hu⟩ * ⟨l, hl⟩⁻¹ : ↥L) = ⟨u, hu⟩ * z' := Subtype.ext hconj
      have h1 := hgen (q ↥L ⟨l, hl⟩) (Subgroup.mem_top _) (by
        rw [← hz'q, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← hconj'])
      have hM : (K.subgroupOf L ⊔ (K.subgroupOf L).map (conjHom (⟨l, hl⟩ : ↥L))).map (q ↥L) =
          ⊤ := by
        rw [Subgroup.map_sup, map_map_q_conjHom]
        exact h1
      have hMtop := eq_top_of_map_q_eq_top hLtop hM
      refine le_antisymm (sup_le hKL ?_) fun g hg => ?_
      · rintro _ ⟨k, hk, rfl⟩
        exact L.mul_mem (L.mul_mem hl (hKL hk)) (L.inv_mem hl)
      · have hg' : (⟨g, hg⟩ : ↥L) ∈
            K.subgroupOf L ⊔ (K.subgroupOf L).map (conjHom (⟨l, hl⟩ : ↥L)) := by
          rw [hMtop]; exact Subgroup.mem_top _
        have h2 := Subgroup.mem_map_of_mem L.subtype hg'
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKL] at h2
        have h3 : ((K.subgroupOf L).map (conjHom (⟨l, hl⟩ : ↥L))).map L.subtype =
            K.map (conjHom l) := by
          ext y
          constructor
          · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
            exact ⟨k, Subgroup.mem_subgroupOf.1 hk, rfl⟩
          · rintro ⟨k, hk, rfl⟩
            exact ⟨_, ⟨⟨k, hKL hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩, rfl⟩
        rw [h3] at h2
        exact h2

end CFSG.EvenSporadicStandard.Induction
