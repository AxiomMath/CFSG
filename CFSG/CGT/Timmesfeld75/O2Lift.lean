module

public import CFSG.CGT.Timmesfeld75.O2Wc
public import CFSG.CGT.Timmesfeld75.ZStarSmall
public import CFSG.CGT.Timmesfeld75.ConclusionIso

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Counting

theorem exists_mul_ne_one_of_four_le_card {Q : Type*} [Group Q] {E : Subgroup Q}
    (hE : IsElemAbelian 2 E) (h4 : 4 ≤ Nat.card E) :
    ∃ x ∈ E, ∃ y ∈ E, x ≠ 1 ∧ y ≠ 1 ∧ x * y ≠ 1 := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    simp at h4
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  by_cases hex : ∃ y ∈ E, y ≠ 1 ∧ y ≠ x
  · obtain ⟨y, hy, hy1, hyx⟩ := hex
    refine ⟨x, hx, y, hy, hx1', hy1, fun h => hyx ?_⟩
    rw [eq_inv_of_mul_eq_one_right h]
    exact elemAbelian_inv hE hx
  · exfalso
    push Not at hex
    have hsub : (E : Set Q) ⊆ {1, x} := by
      intro y hy
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · exact Or.inr (hex y hy hy1)
    have hcard : Nat.card E = (E : Set Q).ncard := Nat.card_coe_set_eq (E : Set Q)
    have h2 : (E : Set Q).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le 1 {x}).trans (by simp))
    omega

end Counting

section Lifting

variable {K : Type*} [Group K] [Finite K]

theorem mem_normalizer_of_mk_mem_normalizer_map {T N : Subgroup K} (hT : IsWC T) [N.Normal]
    (hN : IsPGroup 2 N) {k : K}
    (hk : QuotientGroup.mk' N k ∈ Subgroup.normalizer
      ((T.map (QuotientGroup.mk' N) : Subgroup (K ⧸ N)) : Set (K ⧸ N))) :
    k ∈ Subgroup.normalizer (T : Set K) := by
  have hS : IsPGroup 2 (T ⊔ N : Subgroup K) :=
    (isPGroup_two_of_isElemAbelian hT.1).to_sup_of_normal_right hN
  have hle : conjSubgroup k T ≤ T ⊔ N := by
    intro y hy
    have hx : k⁻¹ * y * k ∈ T := mem_conjSubgroup.1 hy
    have h1 := (Subgroup.mem_normalizer_iff.1 hk _).1
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hx)
    have h2 : QuotientGroup.mk' N k * QuotientGroup.mk' N (k⁻¹ * y * k) *
        (QuotientGroup.mk' N k)⁻¹ = QuotientGroup.mk' N y := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    rw [h2] at h1
    obtain ⟨t, ht, hty⟩ := h1
    have hn : t⁻¹ * y ∈ N := QuotientGroup.eq.1 hty
    have hy' : y = t * (t⁻¹ * y) := by group
    rw [hy']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hn)
  exact mem_normalizer_of_conjSubgroup_eq (eq_of_conj_le_pGroup hT hS le_sup_left hle)

theorem exists_mem_normalizer_conj_mul_mem {T N : Subgroup K} (hT : IsWC T) [N.Normal]
    (hN : IsPGroup 2 N)
    (htrans : ∀ x ∈ T.map (QuotientGroup.mk' N), x ≠ 1 → ∀ y ∈ T.map (QuotientGroup.mk' N),
      y ≠ 1 → ∃ g ∈ Subgroup.normalizer
        ((T.map (QuotientGroup.mk' N) : Subgroup (K ⧸ N)) : Set (K ⧸ N)), g * x * g⁻¹ = y)
    {t₁ t₂ : K} (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T) (ht₁N : t₁ ∉ N) (ht₂N : t₂ ∉ N) :
    ∃ k ∈ Subgroup.normalizer (T : Set K), (k * t₁ * k⁻¹)⁻¹ * t₂ ∈ N := by
  obtain ⟨q, hq, hqxy⟩ := htrans (QuotientGroup.mk' N t₁) (Subgroup.mem_map_of_mem _ ht₁)
    (fun h => ht₁N ((QuotientGroup.eq_one_iff t₁).1 h)) (QuotientGroup.mk' N t₂)
    (Subgroup.mem_map_of_mem _ ht₂) (fun h => ht₂N ((QuotientGroup.eq_one_iff t₂).1 h))
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨k, mem_normalizer_of_mk_mem_normalizer_map hT hN hq, ?_⟩
  have h5 : QuotientGroup.mk' N (k * t₁ * k⁻¹) = QuotientGroup.mk' N t₂ := by
    rw [map_mul, map_mul, map_inv]
    exact hqxy
  exact QuotientGroup.eq.1 h5

end Lifting

section Perfect

variable {K : Type*} [Group K]

theorem commutator_quotient_eq_top {T N N₀ : Subgroup K} [N₀.Normal]
    (hK : Subgroup.normalClosure (T : Set K) = ⊤) (hTN : T ⊓ N ≤ N₀)
    (hconj : ∀ t₁ ∈ T, t₁ ∉ N → ∀ t₂ ∈ T, t₂ ∉ N →
      ∃ k : K, k * t₁ * k⁻¹ ∈ T ∧ (k * t₁ * k⁻¹)⁻¹ * t₂ ∈ N)
    (hthree : ∃ t ∈ T, ∃ t' ∈ T, t ∉ N ∧ t' ∉ N ∧ t * t' ∉ N) :
    commutator (K ⧸ N₀) = ⊤ := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : K →* Abelianization (K ⧸ N₀),
      ∀ k : K, ψ k = Abelianization.of (QuotientGroup.mk' N₀ k) :=
    ⟨Abelianization.of.comp (QuotientGroup.mk' N₀), fun _ => rfl⟩
  have hψconj : ∀ k x : K, ψ (k * x * k⁻¹) = ψ x := by
    intro k x
    rw [map_mul, map_mul, map_inv, mul_comm (ψ k), mul_assoc, mul_inv_cancel, mul_one]
  have hψ1 : ∀ n ∈ N₀, ψ n = 1 := by
    intro n hn
    have h1 : QuotientGroup.mk' N₀ n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [hψ, h1, map_one]
  have hψconst : ∀ t₁ ∈ T, t₁ ∉ N → ∀ t₂ ∈ T, t₂ ∉ N → ψ t₁ = ψ t₂ := by
    intro t₁ ht₁ ht₁N t₂ ht₂ ht₂N
    obtain ⟨k, hkT, hkN⟩ := hconj t₁ ht₁ ht₁N t₂ ht₂ ht₂N
    have hu : (k * t₁ * k⁻¹)⁻¹ * t₂ ∈ N₀ := hTN ⟨T.mul_mem (T.inv_mem hkT) ht₂, hkN⟩
    have h1 : ψ ((k * t₁ * k⁻¹)⁻¹ * t₂) = 1 := hψ1 _ hu
    rw [map_mul, map_inv, hψconj] at h1
    exact inv_mul_eq_one.1 h1
  obtain ⟨t, ht, t', ht', htN, ht'N, htt'N⟩ := hthree
  have hc : ψ t = 1 := by
    have h1 : ψ (t * t') = ψ t := hψconst _ (T.mul_mem ht ht') htt'N t ht htN
    have h3 : ψ t' = ψ t := hψconst t' ht' ht'N t ht htN
    rw [map_mul, h3] at h1
    exact mul_left_cancel (h1.trans (mul_one _).symm)
  have hψT : ∀ x ∈ T, ψ x = 1 := by
    intro x hx
    by_cases hxN : x ∈ N
    · exact hψ1 x (hTN ⟨hx, hxN⟩)
    · rw [hψconst x hx hxN t ht htN]
      exact hc
  have hker : Subgroup.normalClosure (T : Set K) ≤ ψ.ker :=
    Subgroup.normalClosure_le_normal fun x hx => MonoidHom.mem_ker.2 (hψT x hx)
  rw [hK] at hker
  rw [eq_top_iff]
  intro y _
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  have h1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top k))
  rw [hψ] at h1
  exact h1

end Perfect

section Covering

theorem isCoveringOfList_of_surjective_ker_le_center {H Q : Type} [Group H] [Group Q]
    (φ : H →* Q) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center H)
    (hperf : commutator H = ⊤) (hQ : IsCoveringOfList Q) : IsCoveringOfList H := by
  obtain ⟨-, Z, hZc, hZn, hlist⟩ := hQ
  obtain ⟨ψ, hψ⟩ : ∃ ψ : H →* Q ⧸ Z, ∀ h : H, ψ h = QuotientGroup.mk' Z (φ h) :=
    ⟨(QuotientGroup.mk' Z).comp φ, fun _ => rfl⟩
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨h, rfl⟩ := hφ q
    exact ⟨h, hψ h⟩
  have hψker : ∀ z : H, z ∈ ψ.ker → φ z ∈ Z := by
    intro z hz
    have h1 : QuotientGroup.mk' Z (φ z) = 1 := by rw [← hψ]; exact hz
    exact (QuotientGroup.eq_one_iff (φ z)).1 h1
  have hcomm : ⁅(⊤ : Subgroup H), ψ.ker⁆ ≤ Subgroup.center H := by
    refine le_trans ?_ hker
    rw [Subgroup.commutator_le]
    intro g _ z hz
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.1 (hZc (hψker z hz)) (φ g)
  have h1 : ⁅⁅(⊤ : Subgroup H), ψ.ker⁆, ⊤⁆ = ⊥ :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.2 hcomm
  have h2 : ⁅⁅ψ.ker, (⊤ : Subgroup H)⁆, (⊤ : Subgroup H)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm ψ.ker ⊤]
    exact h1
  have h3 : ⁅⁅(⊤ : Subgroup H), ⊤⁆, ψ.ker⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [← commutator_def, hperf] at h3
  have hcenter : ψ.ker ≤ Subgroup.center H :=
    Subgroup.commutator_top_left_eq_bot_iff_le_center.1 h3
  exact ⟨hperf, ψ.ker, hcenter, inferInstance,
    ListGroup.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).symm hlist⟩

end Covering

section Lift

theorem conclusionFor_of_pCore_quotient {K : Type} [Group K] [Finite K] {T : Subgroup K}
    (hT : IsWC T) (hK : Subgroup.normalClosure (T : Set K) = ⊤)
    (h : Nat.card (T.map (QuotientGroup.mk' (CFSG.pCore 2 K))) ≤ 2 ∨
      (4 ≤ Nat.card (T.map (QuotientGroup.mk' (CFSG.pCore 2 K))) ∧
        IsCoveringOfList (K ⧸ CFSG.pCore 2 K) ∧
        ∀ x ∈ T.map (QuotientGroup.mk' (CFSG.pCore 2 K)), x ≠ 1 →
          ∀ y ∈ T.map (QuotientGroup.mk' (CFSG.pCore 2 K)), y ≠ 1 →
            ∃ g ∈ Subgroup.normalizer
              ((T.map (QuotientGroup.mk' (CFSG.pCore 2 K)) : Subgroup (K ⧸ CFSG.pCore 2 K)) :
                Set (K ⧸ CFSG.pCore 2 K)), g * x * g⁻¹ = y)) :
    ConclusionFor K := by
  have hN2 : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
  have hTN : T ⊓ CFSG.pCore 2 K ≤ normalClosureInf T (CFSG.pCore 2 K) :=
    inf_le_normalClosureInf T _
  obtain ⟨φ, hφ, hφsurj, hker, hbot⟩ := exists_central_quotient_map_pCore hT hK
  have hWC := isWC_map_normalClosureInf hT
  have hKb : Subgroup.normalClosure
      ((T.map (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K))) :
        Subgroup (K ⧸ normalClosureInf T (CFSG.pCore 2 K))) :
        Set (K ⧸ normalClosureInf T (CFSG.pCore 2 K))) = ⊤ := by
    rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), hK,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hmem : ∀ x ∈ T.map (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K))),
      φ x ∈ T.map (QuotientGroup.mk' (CFSG.pCore 2 K)) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hφ]
    exact Subgroup.mem_map_of_mem _ ht
  have hcard : Nat.card (T.map (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)))) =
      Nat.card (T.map (QuotientGroup.mk' (CFSG.pCore 2 K))) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : T.map (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K))) =>
        (⟨φ x, hmem x x.2⟩ : T.map (QuotientGroup.mk' (CFSG.pCore 2 K)))) ⟨?_, ?_⟩)
    · intro x y hxy
      have h1 : φ x = φ y := congrArg Subtype.val hxy
      have h2 : (x : K ⧸ normalClosureInf T (CFSG.pCore 2 K))⁻¹ * y ∈
          T.map (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K))) ⊓ φ.ker :=
        Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) y.2, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]⟩
      rw [hbot, Subgroup.mem_bot] at h2
      exact Subtype.ext (inv_mul_eq_one.1 h2)
    · rintro ⟨_, t, ht, rfl⟩
      exact ⟨⟨QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)) t,
        Subgroup.mem_map_of_mem _ ht⟩, Subtype.ext (hφ t)⟩
  refine ⟨normalClosureInf T (CFSG.pCore 2 K), inferInstance,
    isElemAbelian_normalClosureInf hT hN2, ?_⟩
  rcases h with hsmall | ⟨h4, hcov, htrans⟩
  · left
    have hpos : 0 < Nat.card (T.map (QuotientGroup.mk' (CFSG.pCore 2 K))) := Nat.card_pos
    by_cases h1 : Nat.card (T.map (QuotientGroup.mk' (CFSG.pCore 2 K))) = 1
    · have hbot' : T.map (QuotientGroup.mk' (CFSG.pCore 2 K)) = ⊥ := Subgroup.card_eq_one.1 h1
      have hTle : T ≤ CFSG.pCore 2 K := by
        intro t ht
        have h3 : QuotientGroup.mk' (CFSG.pCore 2 K) t ∈
            (⊥ : Subgroup (K ⧸ CFSG.pCore 2 K)) := by
          rw [← hbot']
          exact Subgroup.mem_map_of_mem _ ht
        exact (QuotientGroup.eq_one_iff t).1 (Subgroup.mem_bot.1 h3)
      have htop : (⊤ : Subgroup K) ≤ normalClosureInf T (CFSG.pCore 2 K) := by
        rw [← hK]
        exact Subgroup.normalClosure_le_normal fun t ht => hTN ⟨ht, hTle ht⟩
      refine zStarCase_of_comm_mem
        (⊥ : Subgroup (K ⧸ normalClosureInf T (CFSG.pCore 2 K))) (by simp) fun a b => ?_
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      have ha : (a : K ⧸ normalClosureInf T (CFSG.pCore 2 K)) = 1 :=
        (QuotientGroup.eq_one_iff a).2 (htop (Subgroup.mem_top a))
      rw [ha, commutatorElement_one_left]
      exact Subgroup.one_mem _
    · have h2 : Nat.card (T.map (QuotientGroup.mk' (CFSG.pCore 2 K))) = 2 := by omega
      have hz := zStarCase_normalClosure_of_card_two hWC (hcard.trans h2)
      rw [hKb] at hz
      exact zStarCase_of_mulEquiv Subgroup.topEquiv hz
  · right
    have hperf : commutator (K ⧸ normalClosureInf T (CFSG.pCore 2 K)) = ⊤ := by
      refine commutator_quotient_eq_top hK hTN ?_ ?_
      · intro t₁ ht₁ ht₁N t₂ ht₂ ht₂N
        obtain ⟨k, hk, hkN⟩ :=
          exists_mem_normalizer_conj_mul_mem hT hN2 htrans ht₁ ht₂ ht₁N ht₂N
        exact ⟨k, conj_mem_of_mem_normalizer hk ht₁, hkN⟩
      · have hTab := isElemAbelian_map_of_hom hT.1 (QuotientGroup.mk' (CFSG.pCore 2 K))
        obtain ⟨x, hx, y, hy, hx1, hy1, hxy1⟩ := exists_mul_ne_one_of_four_le_card hTab h4
        obtain ⟨t, ht, rfl⟩ := hx
        obtain ⟨t', ht', rfl⟩ := hy
        refine ⟨t, ht, t', ht', fun h => hx1 ?_, fun h => hy1 ?_, fun h => hxy1 ?_⟩
        · exact (QuotientGroup.eq_one_iff t).2 h
        · exact (QuotientGroup.eq_one_iff t').2 h
        · rw [← map_mul]
          exact (QuotientGroup.eq_one_iff (t * t')).2 h
    exact isCoveringOfList_of_surjective_ker_le_center φ hφsurj hker hperf hcov

end Lift

end CFSG.CGT.Timmesfeld75
