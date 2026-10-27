module

public import CFSG.Holt.H78.Sec4SEAut

public section

namespace CFSG.Holt.H78

open MulAction CFSG.GH74.Uniqueness.Bender

section Bender

variable {K : Type} [Group K] [Finite K] {n i e : ℕ}

theorem BenderType.exists_noncommuting_involutions (h : BenderType K n i e) :
    ∃ a b : K, a * a = 1 ∧ b * b = 1 ∧ a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  obtain ⟨z, hz, hz1⟩ := hc.exists_involution
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hc.center_sq z hz) hz1
  refine ⟨z, t, hc.center_sq z hz, hc.sq_eq_one, fun hzt => hc.not_mem ?_⟩
  have hC := (h.lemma_3_4_b Q hc.sq_eq_one hc.not_mem ⟨le_borel _ (rootCenter_le _ hz), hz2⟩).1
  exact hC (Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm)

theorem BenderType.exists_fixed_noncommuting_involutions (h : BenderType K n i e)
    (α : MulAut K) (hα : α * α = 1) (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹) :
    ∃ y₁ y₂ : K, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ α y₁ = y₁ ∧ α y₂ = y₂ ∧ y₁ * y₂ ≠ y₂ * y₁ := by
  rcases h.cases' with ⟨rfl, rfl, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, hn⟩
  · exact h.exists_fixed_noncommuting_involutions_linear α hα hout
  · exact absurd (h.not_outer_involution_suzuki α hα) hout
  · obtain ⟨φ⟩ := h.fixed_unitary α hα hout
    obtain ⟨a, b, ha, hb, hab⟩ :=
      BenderType.exists_noncommuting_involutions (BenderType.linear n hn φ)
    exact ⟨a, b, congrArg Subtype.val ha, congrArg Subtype.val hb, a.2, b.2,
      fun h' => hab (Subtype.ext h')⟩

omit [Finite K] in
theorem apply_mul_inv_eq_of_inv_mul_apply_eq (α : MulAut K) {x y : K}
    (h : x⁻¹ * α x = y⁻¹ * α y) : α (x * y⁻¹) = x * y⁻¹ := by
  rw [map_mul, map_inv]
  calc α x * (α y)⁻¹ = x * (x⁻¹ * α x) * (y⁻¹ * α y)⁻¹ * y⁻¹ := by group
    _ = x * y⁻¹ := by rw [h]; group

theorem BenderType.exists_eq_inv_mul_apply (h : BenderType K n i e) (Q : Sylow 2 K)
    (α : MulAut K) (hα : α * α = 1) (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹)
    (hQ : ∀ x ∈ (Q : Subgroup K), α x ∈ (Q : Subgroup K)) {r : K}
    (hr : r ∈ (Q : Subgroup K)) (hαr : α r = r⁻¹) :
    ∃ p ∈ (Q : Subgroup K), r = p⁻¹ * α p := by
  classical
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hαα : ∀ y, α (α y) = y := fun y => by
    have := congrArg (fun f : MulAut K => f y) hα
    simpa using this
  set c : K → K := fun p => p⁻¹ * α p with hcdef
  set T : Set K := ((Q : Subgroup K) : Set K) with hT
  have hQcard : T.ncard = (2 ^ n) ^ i := by
    rw [← hc.card_eq, hT, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  rcases h.cases' with ⟨rfl, rfl, hn⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, hn⟩
  ·
    obtain ⟨m, hnm, ⟨φ⟩, -⟩ := h.fixed_linear α hα hout
    have hZQ : rootCenter (Q : Subgroup K) = Q := Subgroup.eq_of_le_of_card_ge
      (rootCenter_le _) (by rw [hc.card_center, hc.card_eq, pow_one])
    have hQsq : ∀ x ∈ (Q : Subgroup K), x * x = 1 := fun x hx =>
      hc.center_sq x (by rw [hZQ]; exact hx)
    have hQab : ∀ x ∈ (Q : Subgroup K), ∀ y ∈ (Q : Subgroup K), x * y = y * x :=
      fun x hx y hy => ((mem_rootCenter_iff.mp (show y ∈ rootCenter (Q : Subgroup K) by
        rw [hZQ]; exact hy)).2 x hx)
    set C : Subgroup K := (Q : Subgroup K) ⊓ autFixed α with hC
    have hCcard : Nat.card C ≤ 2 ^ m := by
      have hE : ∀ x ∈ (C.subgroupOf (autFixed α)).map φ.toMonoidHom, x * x = 1 := by
        rintro _ ⟨x, hx, rfl⟩
        have hxQ : (x : K) ∈ (Q : Subgroup K) := (Subgroup.mem_inf.mp hx).1
        rw [← map_mul, show x * x = 1 from Subtype.ext (hQsq _ hxQ), map_one]
      have := card_le_of_sq_eq_one_psl2 (by omega) _ hE
      rwa [Subgroup.card_map_of_injective φ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at this
    have himg : c '' T ⊆ (C : Set K) := by
      rintro _ ⟨p, hp, rfl⟩
      have hαp := hQ p hp
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hp) hαp, mem_autFixed_iff.mpr ?_⟩
      simp only [hcdef]
      rw [map_mul, map_inv, hαα, inv_eq_of_mul_eq_one_right (hQsq _ hαp),
        inv_eq_of_mul_eq_one_right (hQsq _ hp), hQab _ hαp _ hp]
    have hfib : ∀ x ∈ T, ∀ y ∈ T, c x = c y → x * y⁻¹ ∈ C :=
      fun x hx y hy hxy => Subgroup.mem_inf.mpr ⟨mul_mem hx (inv_mem hy),
        mem_autFixed_iff.mpr (apply_mul_inv_eq_of_inv_mul_apply_eq α hxy)⟩
    have hle := ncard_le_mul_ncard_image c hfib
    rw [hQcard, pow_one, hnm, pow_mul', sq] at hle
    have hN : 2 ^ m ≤ (c '' T).ncard :=
      Nat.le_of_mul_le_mul_left (hle.trans (Nat.mul_le_mul_right _ hCcard)) (by positivity)
    have heq : c '' T = C := Set.eq_of_subset_of_ncard_le himg (by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
      exact hCcard.trans hN)
    have hrC : r ∈ (C : Set K) := Subgroup.mem_inf.mpr ⟨hr, mem_autFixed_iff.mpr (by
      rw [hαr]
      exact inv_eq_of_mul_eq_one_right (hQsq r hr))⟩
    rw [← heq] at hrC
    obtain ⟨p, hp, hpr⟩ := hrC
    exact ⟨p, hp, hpr.symm⟩
  · exact absurd (h.not_outer_involution_suzuki α hα) hout
  ·
    obtain ⟨-, -, hcard, -, -, -, -, -, hmem⟩ := h.lemma_3_4_d5_unitary Q α hα hout hQ
    have himg : c '' T ⊆ (commutatorAut (Q : Subgroup K) α : Set K) := by
      rintro _ ⟨p, hp, rfl⟩
      exact Subgroup.subset_closure ⟨p, hp, rfl⟩
    have hfib : ∀ x ∈ T, ∀ y ∈ T, c x = c y → x * y⁻¹ ∈ rootCenter (Q : Subgroup K) :=
      fun x hx y hy hxy =>
        (h.fixed_iff_rootCenter_unitary Q α hα hout hQ (mul_mem hx (inv_mem hy))).mp
          (apply_mul_inv_eq_of_inv_mul_apply_eq α hxy)
    have hle := ncard_le_mul_ncard_image c hfib
    rw [hQcard, hc.card_center, pow_succ' _ 2] at hle
    have hN : (2 ^ n) ^ 2 ≤ (c '' T).ncard := Nat.le_of_mul_le_mul_left hle (by positivity)
    have heq : c '' T = commutatorAut (Q : Subgroup K) α :=
      Set.eq_of_subset_of_ncard_le himg (by
        rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard]
        exact hN)
    have hrmem : r ∈ commutatorAut (Q : Subgroup K) α := by
      refine (hmem r hr).mp ?_
      rw [hαr, ← mul_inv_rev]
      exact inv_mem (h.sq_mem_rootCenter_unitary Q hr)
    rw [← SetLike.mem_coe, ← heq] at hrmem
    obtain ⟨p, hp, hpr⟩ := hrmem
    exact ⟨p, hp, hpr.symm⟩

end Bender

section Outer

variable {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)} {n i e : ℕ}

omit [Finite Δ] in
theorem normalizerMonoidHom_mul_self {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hx2 : x * x = 1) :
    L.normalizerMonoidHom ⟨x, hx⟩ * L.normalizerMonoidHom ⟨x, hx⟩ = 1 := by
  rw [← map_mul, show (⟨x, hx⟩ : Subgroup.normalizer (L : Set (Equiv.Perm Δ))) * ⟨x, hx⟩ = 1
    from Subtype.ext hx2, map_one]

theorem IsBenderAction.normalizerMonoidHom_mem_sylow (hA : IsBenderAction ↥L Δ n i e) {b : Δ}
    {Q : Sylow 2 ↥L} (hQ : (Q : Subgroup ↥L) ≤ stabilizer ↥L b) {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hxb : x b = b) {q : ↥L}
    (hq : q ∈ (Q : Subgroup ↥L)) : L.normalizerMonoidHom ⟨x, hx⟩ q ∈ (Q : Subgroup ↥L) := by
  have h1 : x * q * x⁻¹ ∈ seRadical L b := conj_mem_seRadical hx hxb (by
    rw [hA.seRadical_eq_map hQ]
    exact ⟨q, hq, rfl⟩)
  rw [hA.seRadical_eq_map hQ] at h1
  obtain ⟨q', hq', hq'eq⟩ := h1
  have : L.normalizerMonoidHom ⟨x, hx⟩ q = q' := Subtype.ext (by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hq'eq.symm)
  rw [this]
  exact hq'

namespace IsNaturalSE

theorem exists_ne_fixed (hL : IsNaturalSE L) {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hx2 : x * x = 1) (hxL : x ∉ L) :
    ∃ c₁ c₂ : Δ, c₁ ≠ c₂ ∧ x c₁ = c₁ ∧ x c₂ = c₂ := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  set σ := L.normalizerMonoidHom ⟨x, hx⟩ with hσ
  obtain ⟨y₁, y₂, h₁, h₂, hf₁, hf₂, hne⟩ := BenderType.exists_fixed_noncommuting_involutions
    hA.benderType σ (normalizerMonoidHom_mul_self hx hx2) (hL.not_inner hx hxL)
  have hy1 : y₁ ≠ 1 := by
    rintro rfl
    exact hne (by simp)
  have hy2 : y₂ ≠ 1 := by
    rintro rfl
    exact hne (by simp)
  have hord : ∀ {y : ↥L}, y * y = 1 → y ≠ 1 → orderOf y = 2 := fun hy hy1 =>
    orderOf_eq_prime (by rw [sq]; exact hy) hy1
  obtain ⟨c₁, hc₁, hu₁⟩ := hA.existsUnique_fixed (hord h₁ hy1)
  obtain ⟨c₂, hc₂, hu₂⟩ := hA.existsUnique_fixed (hord h₂ hy2)
  have hfix : ∀ {y : ↥L} {c : Δ}, σ y = y → y • c = c → (∀ c', y • c' = c' → c' = c) →
      x c = c := fun {y} {c} hy hyc hu => by
    apply hu
    have h' : x * y * x⁻¹ = y := by
      have := congrArg Subtype.val hy
      rwa [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    have h'' : (x * y) c = (y * x) c := by
      rw [show x * (y : Equiv.Perm Δ) = x * y * x⁻¹ * x by group, h']
    simp only [Equiv.Perm.mul_apply] at h''
    rw [Subgroup.smul_def, Equiv.Perm.smul_def] at hyc ⊢
    rw [← h'', hyc]
  refine ⟨c₁, c₂, fun h12 => hne ?_, hfix hf₁ hc₁ hu₁, hfix hf₂ hc₂ hu₂⟩
  subst h12
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer c₁
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  have hz₁ := hc.center_of_involution y₁ ((hA.mem_borel_iff hQ).mpr hc₁) (hord h₁ hy1)
  have hz₂ := hc.center_of_involution y₂ ((hA.mem_borel_iff hQ).mpr hc₂) (hord h₂ hy2)
  exact (mem_rootCenter_iff.mp hz₂).2 y₁ (rootCenter_le _ hz₁)

theorem exists_ne_apply_eq (hL : IsNaturalSE L) {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hx2 : x * x = 1) (hxL : x ∉ L)
    (b : Δ) : ∃ c, c ≠ b ∧ x c = c := by
  obtain ⟨c₁, c₂, hne, h₁, h₂⟩ := hL.exists_ne_fixed hx hx2 hxL
  by_cases h : c₁ = b
  · exact ⟨c₂, fun h' => hne (h.trans h'.symm), h₂⟩
  · exact ⟨c₁, h, h₁⟩

theorem mem_of_existsUnique_fixed (hL : IsNaturalSE L) {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hx2 : x * x = 1)
    (hfix : ∃! δ : Δ, x δ = δ) : x ∈ L := by
  by_contra hxL
  obtain ⟨c₁, c₂, hne, h₁, h₂⟩ := hL.exists_ne_fixed hx hx2 hxL
  obtain ⟨δ, -, hu⟩ := hfix
  exact hne ((hu c₁ h₁).trans (hu c₂ h₂).symm)

theorem three_le_ncard_fixedBy (hL : IsNaturalSE L) {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hx2 : x * x = 1) (hxL : x ∉ L) :
    3 ≤ (fixedBy Δ x).ncard := by
  classical
  have := Fintype.ofFinite Δ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  obtain ⟨c₁, c₂, hne, h₁, h₂⟩ := hL.exists_ne_fixed hx hx2 hxL
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) (σ := x)
    (by rw [pow_one, sq, hx2])
  have hset : fixedBy Δ x = ↑(x.supportᶜ) := by
    ext δ
    simp [Equiv.Perm.mem_support, Equiv.Perm.smul_def]
  rw [hset, Set.ncard_coe_finset]
  have hodd : Odd (Fintype.card Δ) := by
    rw [← Nat.card_eq_fintype_card]
    exact hA.odd_card
  have h2 : 2 ≤ x.supportᶜ.card := by
    have hsub : ({c₁, c₂} : Finset Δ) ⊆ x.supportᶜ := by
      intro δ hδ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hδ
      rcases hδ with rfl | rfl <;> simp [Equiv.Perm.mem_support, *]
    calc 2 = ({c₁, c₂} : Finset Δ).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  rw [Nat.odd_iff] at hodd
  unfold Nat.ModEq at hmod
  omega

end IsNaturalSE

theorem IsBenderAction.mem_of_mul_self_eq_one_of_suzuki (hA : IsBenderAction ↥L Δ n 2 e)
    {x : Equiv.Perm Δ} (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    (hx2 : x * x = 1) : x ∈ L := by
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, 2, e, hA⟩
  by_contra hxL
  exact hL.not_inner hx hxL (hA.benderType.not_outer_involution_suzuki _
    (normalizerMonoidHom_mul_self hx hx2))

theorem IsBenderAction.commute_iff_mem_rootCenter_of_unitary (hA : IsBenderAction ↥L Δ n 3 e)
    {x : Equiv.Perm Δ} (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    (hx2 : x * x = 1) (hxL : x ∉ L) {b : Δ} (hxb : x b = b) {r : Equiv.Perm Δ}
    (hr : r ∈ seRadical L b) : x * r = r * x ↔ r ∈ rootCenter (seRadical L b) := by
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, 3, e, hA⟩
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  rw [hA.seRadical_eq_map hQ] at hr
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  have key := hA.benderType.fixed_iff_rootCenter_unitary Q (L.normalizerMonoidHom ⟨x, hx⟩)
    (normalizerMonoidHom_mul_self hx hx2) (hL.not_inner hx hxL)
    (fun q hq => hA.normalizerMonoidHom_mem_sylow hQ hx hxb hq) hr₀
  rw [hA.rootCenter_seRadical_eq_map hQ, Subgroup.mem_map_iff_mem L.subtype_injective, ← key]
  constructor
  · intro h
    refine Subtype.ext ?_
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp only [Subgroup.coe_subtype] at h
    rw [h, mul_inv_cancel_right]
  · intro h
    have := congrArg Subtype.val h
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    simp only [Subgroup.coe_subtype]
    calc x * r₀ = x * r₀ * x⁻¹ * x := by group
      _ = r₀ * x := by rw [this]

theorem IsNaturalSE.exists_conj_eq_of_mul (hL : IsNaturalSE L) {b : Δ} {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hxb : x b = b) (hx2 : x * x = 1)
    (hxL : x ∉ L) {r : Equiv.Perm Δ} (hr : r ∈ seRadical L b) (hrx : r * x * (r * x) = 1) :
    ∃ p ∈ seRadical L b, r * x = p * x * p⁻¹ := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  rw [hA.seRadical_eq_map hQ] at hr
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  simp only [Subgroup.coe_subtype] at hrx ⊢
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hσr : L.normalizerMonoidHom ⟨x, hx⟩ r₀ = r₀⁻¹ := Subtype.ext (by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv]
    calc x * r₀ * x⁻¹ = (r₀ : Equiv.Perm Δ)⁻¹ * (r₀ * x * (r₀ * x)) := by rw [hxi]; group
      _ = (r₀ : Equiv.Perm Δ)⁻¹ := by rw [hrx, mul_one])
  obtain ⟨p, hp, hpr⟩ := BenderType.exists_eq_inv_mul_apply hA.benderType Q
    (L.normalizerMonoidHom ⟨x, hx⟩) (normalizerMonoidHom_mul_self hx hx2) (hL.not_inner hx hxL)
    (fun q hq => hA.normalizerMonoidHom_mem_sylow hQ hx hxb hq) hr₀ hσr
  refine ⟨((p⁻¹ : ↥L) : Equiv.Perm Δ), ?_, ?_⟩
  · rw [hA.seRadical_eq_map hQ]
    exact ⟨p⁻¹, inv_mem hp, rfl⟩
  · have h1 := congrArg Subtype.val hpr
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    rw [h1, Subgroup.coe_inv]
    group

theorem IsNaturalSE.exists_conj_eq_of_isPGroup (hL : IsNaturalSE L) {b : Δ}
    {S : Subgroup (Equiv.Perm Δ)} (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hSb : ∀ s ∈ S, s b = b)
    {x y : Equiv.Perm Δ} (hxS : x ∈ S) (hyS : y ∈ S) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hxL : x ∉ L) (hyL : y ∉ L) : ∃ p ∈ seRadical L b, y = p * x * p⁻¹ := by
  have hyx : y * x⁻¹ ∈ L := hL.mul_inv_mem_of_isPGroup hS2 hSN hyS hxS hy2 hx2 hyL hxL
  have hrS : y * x⁻¹ ∈ S := mul_mem hyS (inv_mem hxS)
  obtain ⟨k, hk⟩ := hS2 ⟨y * x⁻¹, hrS⟩
  have hr : y * x⁻¹ ∈ seRadical L b := mem_seRadical_of_pow_eq_one hyx (hSb _ hrS) (k := k)
    (by simpa using congrArg Subtype.val hk)
  have hyr : y = y * x⁻¹ * x := by group
  rw [hyr] at hy2 ⊢
  exact hL.exists_conj_eq_of_mul (hSN hxS) (hSb x hxS) hx2 hxL hr hy2

theorem IsBenderAction.card_le_of_mul_self_eq_one (hA : IsBenderAction ↥L Δ n i e)
    {E : Subgroup (Equiv.Perm Δ)} (hEN : E ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ (n + 1) ∧ (i ≠ 3 → Nat.card E ≤ 2 ^ n) := by
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, i, e, hA⟩
  set f : ↥E →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hEN) with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    refine Subgroup.mem_bot.mpr (Subtype.ext (hL.eq_one_of_commute fun ℓ hℓ => ?_))
    have := congrArg Subtype.val (DFunLike.congr_fun hx ⟨ℓ, hℓ⟩)
    rw [hf, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    simp only [Subgroup.coe_inclusion, MulAut.one_apply] at this
    calc (x : Equiv.Perm Δ) * ℓ = x * ℓ * (x : Equiv.Perm Δ)⁻¹ * x := by group
      _ = ℓ * x := by rw [this]
  have hsq : ∀ σ ∈ f.range, σ * σ = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hE x x.2), map_one]
  have hcard : Nat.card f.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [← hcard]
  exact hA.benderType.card_le_of_sq_eq_one_aut f.range hsq

end Outer

end CFSG.Holt.H78
