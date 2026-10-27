module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSONModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OutLocalQ

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 Cover

structure InFacts {G : Type} [Group G] (L K : Subgroup G) (u : G) : Prop where
  u_mem : u ∈ K
  one : OneClassOutside K
  normalized : ∀ c ∈ L ⊓ centralizer ({u} : Set G), K.map (conjHom c) = K
  rep : ∃ v ∈ vCandidates K u, ∃ l ∈ L, l * u * l⁻¹ = u * v ∧ K ⊔ K.map (conjHom l) = L

theorem InFacts.local39 {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (F : InFacts L K u) (hKL : K ≤ L) (hKcen : u ∈ centralizer (K : Set G))
    (h35 : K = componentProduct K u) :
    (vPairs L K u).Nonempty ∧ Sol78Fusion39 L K u ∧ Sol78Generate L K u := by
  obtain ⟨huK, hone, hnorm, v₀, hv₀, l, hl, hlconj, hgen⟩ := F
  exact ⟨vPairs_nonempty_of_mem (mem_vMaximal_of_oneClass huK hone hv₀) ⟨l, hl, hlconj⟩,
    sol78Fusion39_of_oneClassK hKcen h35 hKL huK hone,
    sol78Generate_of_oneClassK hKcen hKL huK hone hv₀ (generate_of_one hl hlconj hnorm hgen)⟩

section Lift

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem oneClassOutside_of_quotient (hodd : Odd (Nat.card (center X))) {K : Subgroup X}
    (hK : ⁅K, K⁆ = K) (h : OneClassOutside (K.map (q X))) : OneClassOutside K := by
  intro v hv v' hv' hvv hv'v' hv1 hv'1 hvc hv'c
  have hne : ∀ {a : X}, a * a = 1 → a ≠ 1 → q X a ≠ 1 := fun {a} ha2 ha1 h1 =>
    ha1 (Closing.eq_one_of_sq_eq_one_of_odd_center hodd (q_eq_one_iff.1 h1) ha2)
  have hsq : ∀ {a : X}, a * a = 1 → q X a * q X a = 1 := fun {a} ha2 => by
    rw [← map_mul, ha2, map_one]
  have hnc : ∀ {a : X}, a ∈ K → a ∉ (center ↥K).map K.subtype →
      q X a ∉ (center ↥(K.map (q X))).map (K.map (q X)).subtype := by
    intro a ha hac hmem
    apply hac
    obtain ⟨y, hy, hya⟩ := hmem
    refine ⟨⟨a, ha⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    have hcomm : q X a ∈
        centralizer ((K.map (q X) : Subgroup (X ⧸ center X)) : Set (X ⧸ center X)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨q X w, ⟨w, hw, rfl⟩⟩)
      rw [← hya]
      exact h2
    have := (mem_centralizer_iff_of_perfect hK).2 hcomm
    exact Subtype.ext (mem_centralizer_iff.1 this g g.2)
  obtain ⟨ct, hct, hcc⟩ := h (q X v) ⟨v, hv, rfl⟩ (q X v') ⟨v', hv', rfl⟩ (hsq hvv) (hsq hv'v')
    (hne hvv hv1) (hne hv'v' hv'1) (hnc hv hvc) (hnc hv' hv'c)
  obtain ⟨c, hcK, rfl⟩ := hct
  refine ⟨c, hcK, ?_⟩
  have h1 : (c * v * c⁻¹) * (c * v * c⁻¹) = 1 := by
    calc c * v * c⁻¹ * (c * v * c⁻¹) = c * (v * v) * c⁻¹ := by group
      _ = 1 := by rw [hvv]; group
  refine Closing.eq_of_mk_eq_of_sq hodd h1 hv'v' ?_
  rw [← q_apply, ← q_apply, map_mul, map_mul, map_inv]
  exact hcc

end Lift

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}

omit [Finite H] in
theorem sup_conj_eq_of_quotient (hLperf : Group.IsPerfect ↥L) (hKL : K ≤ L) {l : H} (hl : l ∈ L)
    (h : (K.subgroupOf L).map (q ↥L) ⊔
      ((K.subgroupOf L).map (q ↥L)).map (conjHom (q ↥L ⟨l, hl⟩)) = ⊤) :
    K ⊔ K.map (conjHom l) = L := by
  have hLtop : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact Group.isPerfect_def.1 hLperf
  have hM : (K.subgroupOf L ⊔ (K.subgroupOf L).map (conjHom (⟨l, hl⟩ : ↥L))).map (q ↥L) = ⊤ := by
    rw [Subgroup.map_sup, map_map_q_conjHom]
    exact h
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

theorem normalized_of_quotient (hKperf : Group.IsPerfect ↥K) (hu : u ∈ L) (hKL : K ≤ L)
    (hnorm : ∀ c ∈ (⊤ : Subgroup (↥L ⧸ center ↥L)) ⊓
      centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L)),
      ((K.subgroupOf L).map (q ↥L)).map (conjHom c) = (K.subgroupOf L).map (q ↥L)) :
    ∀ c ∈ L ⊓ centralizer ({u} : Set H), K.map (conjHom c) = K := by
  have hK'perf : Group.IsPerfect ↥(K.subgroupOf L) := isPerfect_subgroupOf_of_le hKL hKperf
  have hK'perf' : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L := isPerfect_iff.mp hK'perf
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

theorem inFacts_of_quotient (hodd : Odd (Nat.card (center ↥L)))
    (hLperf : Group.IsPerfect ↥L) (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hKperf : Group.IsPerfect ↥K)
    (F : InFacts (⊤ : Subgroup (↥L ⧸ center ↥L)) ((K.subgroupOf L).map (q ↥L))
      (q ↥L ⟨u, hu⟩)) : InFacts L K u := by
  classical
  have hK'perf : Group.IsPerfect ↥(K.subgroupOf L) := isPerfect_subgroupOf_of_le hKL hKperf
  have hK'perf' : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L := isPerfect_iff.mp hK'perf
  have hu'2 : (⟨u, hu⟩ : ↥L) * ⟨u, hu⟩ = 1 := Subtype.ext (mul_self_eq_one_of_orderOf hu2)
  have hKu' : ∀ k ∈ K.subgroupOf L, k * (⟨u, hu⟩ : ↥L) = ⟨u, hu⟩ * k := fun k hk =>
    Subtype.ext (hKu k (Subgroup.mem_subgroupOf.1 hk))
  obtain ⟨huK, hone, hnorm, vt, hvt, lt, -, hltconj, hgen⟩ := F
  refine ⟨?_, ?_, normalized_of_quotient hKperf hu hKL hnorm, ?_⟩
  ·
    obtain ⟨k, hk, hk2, hkq⟩ := exists_involution_lift hodd huK (by rw [← map_mul, hu'2, map_one])
    have hku : k = ⟨u, hu⟩ := Closing.eq_of_mk_eq_of_sq hodd hk2 hu'2 hkq
    have h1 := Subgroup.mem_subgroupOf.1 hk
    rwa [hku] at h1
  ·
    exact oneClassOutside_of_equiv (Subgroup.subgroupOfEquivOfLe hKL).symm
      (oneClassOutside_of_quotient hodd hK'perf' hone)
  ·
    obtain ⟨hvt1, hvtc, hvt2⟩ := hvt
    have hKsup : (K.subgroupOf L).map (q ↥L) ⊔ zpowers (q ↥L ⟨u, hu⟩) =
        (K.subgroupOf L).map (q ↥L) := sup_eq_left.2 (zpowers_le.2 huK)
    rw [hKsup] at hvt1
    have hvtsq : vt * vt = 1 := mul_self_eq_one_of_orderOf hvt2
    obtain ⟨v', hv'K, hv'2, hv'q⟩ := exists_involution_lift hodd hvt1 hvtsq
    obtain ⟨l', hl'q⟩ : ∃ l' : ↥L, q ↥L l' = lt := QuotientGroup.mk_surjective lt
    have hv'1 : v' ≠ 1 := fun h => by
      rw [h, map_one] at hv'q
      exact ne_one_of_orderOf hvt2 hv'q.symm
    have hv'c : v' * (⟨u, hu⟩ : ↥L) = ⟨u, hu⟩ * v' := hKu' v' hv'K
    have hv'K' : (v' : H) ∈ K := Subgroup.mem_subgroupOf.1 hv'K
    refine ⟨(v' : H), ⟨mem_sup_left hv'K', ?_, ?_⟩, (l' : H), l'.2, ?_, ?_⟩
    ·
      rintro ⟨y, hy, hyv⟩
      apply hvtc
      refine ⟨⟨vt, hvt1⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
      rintro ⟨_, ⟨w, hw, rfl⟩⟩
      have hw' : ((w : ↥L) : H) ∈ K := Subgroup.mem_subgroupOf.1 hw
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨(w : H), hw'⟩)
      have h2 : (w : H) * (v' : H) = (v' : H) * (w : H) := by
        rw [← hyv]
        exact h1
      have h3 : w * v' = v' * w := Subtype.ext h2
      apply Subtype.ext
      show q ↥L w * vt = vt * q ↥L w
      rw [← hv'q, ← map_mul, ← map_mul, h3]
    · exact orderOf_eq_two_of_mul_self (congrArg Subtype.val hv'2) (fun h => hv'1 (Subtype.ext h))
    · have hmk : q ↥L (l' * ⟨u, hu⟩ * l'⁻¹) = q ↥L (⟨u, hu⟩ * v') := by
        rw [map_mul, map_mul, map_inv, map_mul, hl'q, hv'q]
        exact hltconj
      have hsq1 : (l' * ⟨u, hu⟩ * l'⁻¹) * (l' * ⟨u, hu⟩ * l'⁻¹) = 1 := by
        calc (l' * ⟨u, hu⟩ * l'⁻¹) * (l' * ⟨u, hu⟩ * l'⁻¹)
            = l' * (⟨u, hu⟩ * ⟨u, hu⟩) * l'⁻¹ := by group
          _ = 1 := by rw [hu'2]; group
      have hsq2 : (⟨u, hu⟩ * v') * (⟨u, hu⟩ * v') = 1 := by
        calc (⟨u, hu⟩ * v') * (⟨u, hu⟩ * v') = ⟨u, hu⟩ * (v' * ⟨u, hu⟩) * v' := by group
          _ = ⟨u, hu⟩ * (⟨u, hu⟩ * v') * v' := by rw [hv'c]
          _ = (⟨u, hu⟩ * ⟨u, hu⟩) * (v' * v') := by group
          _ = 1 := by rw [hu'2, hv'2, one_mul]
      exact congrArg Subtype.val (Closing.eq_of_mk_eq_of_sq hodd hsq1 hsq2 hmk)
    · refine sup_conj_eq_of_quotient hLperf hKL l'.2 ?_
      have : (⟨(l' : H), l'.2⟩ : ↥L) = l' := rfl
      rw [this, hl'q]
      exact hgen

end CFSG.EvenSporadicStandard.Induction
