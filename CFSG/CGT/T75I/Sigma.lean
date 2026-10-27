module

public import CFSG.CGT.T75I.NAct
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.CGT.T75I.CenK

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem involution_mem_classD [Finite G] (h1 : Sec4NoA) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ 2 2) [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (hhat : IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
      IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))))
    {y : G} (hyH : y ∈ hSub T (normIn T₁ T)) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    y ∈ classD T := by
  classical
  have hTab := hc.hy.pair.wc.1
  set H := hSub T (normIn T₁ T) with hH
  by_cases hyT : y ∈ T
  · exact mem_classD_of_mem hyT hy1
  obtain ⟨x₀, hx₀L, hx₀1, hx₀normD, hx₀nT⟩ := exists_x₀ hc
  have hx₀H : x₀ ∈ H := normD_le_hSub_of_ctx h1 h63 hc hx₀normD
  let π : ↥H →* ↥H ⧸ T.subgroupOf H := QuotientGroup.mk' (T.subgroupOf H)
  let x₀' : ↥H := ⟨x₀, hx₀H⟩
  let y' : ↥H := ⟨y, hyH⟩
  have hπ1 : ∀ z : ↥H, π z = 1 → (z : G) ∈ T := fun z hz =>
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff z).1 hz)
  have hx₀2 : x₀ * x₀ = 1 := mul_self_eq_one_of_mem_classD hTab hx₀normD.1
  have hπx1 : π x₀' ≠ 1 := fun h => hx₀nT (hπ1 x₀' h)
  have hπx2 : π x₀' * π x₀' = 1 := by
    rw [← map_mul]
    have : x₀' * x₀' = 1 := Subtype.ext hx₀2
    rw [this, map_one]
  have hπy1 : π y' ≠ 1 := fun h => hyT (hπ1 y' h)
  have hπy2 : π y' * π y' = 1 := by
    rw [← map_mul]
    have : y' * y' = 1 := Subtype.ext hy2
    rw [this, map_one]
  obtain ⟨γ, hγ⟩ := exists_conj_involutions_of_hat hhat (π x₀') (π y') hπx1 hπx2 hπy1 hπy2
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective γ
  have hh₀N : (h₀ : G) ∈ Subgroup.normalizer (T : Set G) := hSub_le_normalizer' h₀.2
  set x₂ : G := (h₀ : G) * x₀ * (h₀ : G)⁻¹ with hx₂
  have hx₂D : x₂ ∈ classD T := by
    have := classD_conj hx₀normD.1 (h₀ : G)⁻¹
    simpa [hx₂] using this
  have hx₂N : x₂ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem hh₀N hx₀normD.2)
      ((Subgroup.normalizer (T : Set G)).inv_mem hh₀N)
  have hx₂T : x₂ ∉ T := by
    intro hT'
    apply hx₀nT
    have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hh₀N) hT'
    simpa [hx₂, mul_assoc] using this
  have hx₂2 : x₂ * x₂ = 1 := mul_self_eq_one_of_mem_classD hTab hx₂D
  have hty : x₂⁻¹ * y ∈ T := by
    have hconj : π (h₀ * x₀' * h₀⁻¹) = π y' := by
      rw [map_mul, map_mul, map_inv]
      exact hγ
    have := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hconj)
    simpa [hx₂] using this
  have hc4 : Nat.card ↥(T ⊓ Subgroup.centralizer ({x₂} : Set G)) = 4 := by
    rcases h63 G T T₁ 2 2 hc x₂ ⟨hx₂D, hx₂N⟩ hx₂T with h | ⟨-, hL8, -⟩
    · rw [h]
      exact ctx_card_L hc
    · rw [ctx_card_L hc] at hL8
      omega
  have hinv : x₂⁻¹ = x₂ := inv_eq_of_mul_eq_one_right hx₂2
  have hyx : x₂ * y * x₂ = y := by
    have ht0 : (x₂⁻¹ * y) * (x₂⁻¹ * y) = 1 := elemAbelian_mul_self hTab hty
    rw [hinv] at ht0
    have h4 : (x₂ * y * x₂) * y = 1 := by
      calc (x₂ * y * x₂) * y = (x₂ * y) * (x₂ * y) := by group
        _ = 1 := ht0
    exact (mul_eq_one_iff_eq_inv.1 h4).trans (inv_eq_of_mul_eq_one_right hy2)
  have hcomm : (x₂⁻¹ * y) * x₂ = x₂ * (x₂⁻¹ * y) := by
    rw [hinv]
    calc x₂ * y * x₂ = y := hyx
      _ = x₂ * (x₂ * y) := by rw [← mul_assoc, hx₂2, one_mul]
  obtain ⟨s, hsT, hs⟩ := exists_conj_mul_eq_of_card_four hTab (ctx_card_T hc) hx₂N
    (by rw [hx₂2]; exact T.one_mem) hc4 (x₂⁻¹ * y) hty hcomm
  have hys : y = s⁻¹ * x₂ * s := by
    have e1 : y = x₂ * (x₂⁻¹ * y) := by group
    rw [e1, ← hs, elemAbelian_inv hTab hsT]
    group
  rw [hys]
  have := classD_conj hx₂D s
  simpa using this

theorem false_of_involution_outside [Finite G] (h1 : Sec4NoA) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ 2 2) (hC : Subgroup.centralizer (T : Set G) = T)
    [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (hhat : IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
      IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))))
    {x : G} (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hx2 : x * x = 1)
    (hxH : x ∉ hSub T (normIn T₁ T))
    (hcos : ∀ n ∈ Subgroup.normalizer (T : Set G),
      n ∈ hSub T (normIn T₁ T) ∨ x⁻¹ * n ∈ hSub T (normIn T₁ T)) : False := by
  classical
  have : IsSimpleGroup G := hc.hy.simple
  have hTab := hc.hy.pair.wc.1
  set H := hSub T (normIn T₁ T) with hH
  have hx1 : x ≠ 1 := fun h => hxH (h ▸ H.one_mem)
  have hxord : orderOf x = 2 := orderOf_eq_prime (by rwa [← pow_two] at hx2) hx1
  let T' : Subgroup ↥(Subgroup.normalizer (T : Set G)) :=
    T.subgroupOf (Subgroup.normalizer (T : Set G))
  have hT'2 : IsPGroup 2 T' :=
    (isPGroup_two_of_isElemAbelian hTab).comap_subtype
  let x' : ↥(Subgroup.normalizer (T : Set G)) := ⟨x, hxN⟩
  have hx'2 : x' * x' = 1 := Subtype.ext hx2
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hX2 : IsPGroup 2 (Subgroup.zpowers x') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [← pow_two] at hx'2) hx'1]
    simp
  have hR2 : IsPGroup 2 ↥(T' ⊔ Subgroup.zpowers x') := hT'2.to_sup_of_normal_left hX2
  let R : Subgroup G := (T' ⊔ Subgroup.zpowers x').map (Subgroup.normalizer (T : Set G)).subtype
  have hR : IsPGroup 2 R := hR2.map _
  have hTR : T ≤ R := fun t ht =>
    ⟨⟨t, Subgroup.le_normalizer ht⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hxR : x ∈ R := ⟨x', Subgroup.mem_sup_right (Subgroup.mem_zpowers x'), rfl⟩
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  have hTS : T ≤ (S : Subgroup G) := hTR.trans hRS
  have hxS : x ∈ (S : Subgroup G) := hRS hxR
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (T : Set G) := by
    have : Nontrivial ↥(S : Subgroup G) := ⟨⟨⟨x, hxS⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
    have hZ : Nontrivial ↥(Subgroup.center ↥(S : Subgroup G)) := S.2.center_nontrivial
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥(S : Subgroup G)))
    have hzc : ∀ s : ↥(S : Subgroup G), s * z = z * s := fun s => Subgroup.mem_center_iff.1 hz s
    have hzG : ∀ u ∈ (S : Subgroup G), u * (z : G) = (z : G) * u := fun u hu =>
      congrArg Subtype.val (hzc ⟨u, hu⟩)
    have hzT : (z : G) ∈ T := by
      rw [← hC]
      exact Subgroup.mem_centralizer_iff.2 fun u hu => hzG u (hTS hu)
    have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
    intro s hs
    exact hc.hy.pair.wc.centralizer_le_normalizer hzT hz1'
      (Subgroup.mem_centralizer_singleton_iff.2 (hzG s hs))
  set U : Subgroup G := (S : Subgroup G) ⊓ H with hU
  have hUS : U ≤ (S : Subgroup G) := inf_le_left
  have hxU : x ∉ U := fun h => hxH h.2
  have hUidx : U.relIndex (S : Subgroup G) = 2 := by
    have key : (U.subgroupOf (S : Subgroup G)).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨x, hxS⟩, fun b => ?_⟩
      have hbN : (b : G) ∈ Subgroup.normalizer (T : Set G) := hSN b.2
      have hbU : b ∈ U.subgroupOf (S : Subgroup G) ↔ (b : G) ∈ H := by
        rw [Subgroup.mem_subgroupOf, hU, Subgroup.mem_inf]
        exact ⟨fun h => h.2, fun h => ⟨b.2, h⟩⟩
      have hbxU : b * ⟨x, hxS⟩ ∈ U.subgroupOf (S : Subgroup G) ↔ (b : G) * x ∈ H := by
        rw [Subgroup.mem_subgroupOf, hU, Subgroup.mem_inf]
        exact ⟨fun h => h.2, fun h => ⟨(S : Subgroup G).mul_mem b.2 hxS, h⟩⟩
      rw [hbU, hbxU]
      by_cases hb : (b : G) ∈ H
      · right
        refine ⟨hb, fun hbx => hxH ?_⟩
        have : x = (b : G)⁻¹ * ((b : G) * x) := by group
        rw [this]
        exact H.mul_mem (H.inv_mem hb) hbx
      · left
        refine ⟨?_, hb⟩
        have h2 := (hcos _ hbN).resolve_left hb
        have h3 := conj_mem_hSub hxN h2
        have : (b : G) * x = x * (x⁻¹ * b) * x⁻¹ := by
          calc (b : G) * x = x * (x⁻¹ * b) * (x * x) * x⁻¹ := by group
            _ = x * (x⁻¹ * b) * x⁻¹ := by rw [hx2]; group
        rw [this]
        exact h3
    exact key
  have hmin : ∀ y ∈ (S : Subgroup G), y ∉ U → orderOf x ≤ orderOf y := by
    intro y _ hyU
    have hy1 : y ≠ 1 := fun h => hyU (h ▸ U.one_mem)
    have hy0 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
    have hy2 : 0 < orderOf y := orderOf_pos y
    omega
  have hconj : ∀ g : G, g⁻¹ * x * g ∉ U := by
    intro g hg
    have hgH : g⁻¹ * x * g ∈ H := hg.2
    have hg2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
      calc (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
        _ = 1 := by rw [hx2]; group
    have hg1 : g⁻¹ * x * g ≠ 1 := by
      intro h
      apply hx1
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, h]
      group
    have hD := involution_mem_classD h1 h63 hc hhat hgH hg2 hg1
    have hxD : x ∈ classD T := by
      have := classD_conj hD g⁻¹
      rwa [inv_inv, show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
    exact hxH (normD_le_hSub_of_ctx h1 h63 hc ⟨hxD, hxN⟩)
  obtain ⟨M, hMn, hMidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson
    (T := (S : Subgroup G)) (U := U) S.2 S.not_dvd_index hUS hUidx hxS hxU hmin hconj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hM | hM
  · rw [hM, Subgroup.index_bot] at hMidx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc := isCyclic_of_prime_card (p := 2) hMidx
    obtain ⟨a, b, hab⟩ := hc.hy.nonab
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [hM, Subgroup.index_top] at hMidx
    omega

end CFSG.CGT.T75I
