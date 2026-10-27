module

public import CFSG.GH74.Uniqueness.Section165B0

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec165

omit [Finite X] in
theorem map_autFixed_conjAut {G : Subgroup X} {a : X} (ha : a ∈ normalizer (G : Set X)) :
    (Bender.autFixed (conjAut ha)).map G.subtype = G ⊓ centralizer ({a} : Set X) := by
  ext x
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h1 : a * (y : X) * a⁻¹ = y := congrArg Subtype.val (Bender.mem_autFixed_iff.mp hy)
    calc (y : X) * a = (a * y * a⁻¹) * a := by rw [h1]
      _ = a * y := by group
  · rintro ⟨hxG, hxa⟩
    refine ⟨⟨x, hxG⟩, Bender.mem_autFixed_iff.mpr (Subtype.ext ?_), rfl⟩
    rw [conjAut_apply, ← hxa, mul_inv_cancel_right]

theorem card_psl2_injective {k k' : ℕ} (hk : 1 ≤ k) (hk' : 1 ≤ k')
    (h : 2 ^ k * ((2 ^ k) ^ 2 - 1) = 2 ^ k' * ((2 ^ k') ^ 2 - 1)) : k = k' := by
  have hmono : ∀ a b : ℕ, 1 ≤ a → a < b →
      2 ^ a * ((2 ^ a) ^ 2 - 1) < 2 ^ b * ((2 ^ b) ^ 2 - 1) := by
    intro a b ha hab
    have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
    have h2 : (2 ^ a) ^ 2 < (2 ^ b) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
    have h3 : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    have h4 : 1 ≤ (2 ^ a) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h5 : (2 ^ a) ^ 2 - 1 < (2 ^ b) ^ 2 - 1 := by omega
    exact Nat.mul_lt_mul'' h1 h5
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd h (ne_of_lt (hmono k k' hk hlt))
  · exact heq
  · exact absurd h (ne_of_gt (hmono k' k hk' hgt))

theorem card_eq_six_of_not_comm {H : Type*} [Group H] [Finite H] (h6 : Nat.card H ∣ 6)
    {a b : H} (hab : a * b ≠ b * a) : Nat.card H = 6 := by
  have hcases : Nat.card H = 1 ∨ Nat.card H = 2 ∨ Nat.card H = 3 ∨ Nat.card H = 6 := by
    have hmem : Nat.card H ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨h6, by norm_num⟩
    have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [hdiv] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hcases with h | h | h | h
  · exfalso
    apply hab
    have : Subsingleton H := (Nat.card_eq_one_iff_unique.mp h).1
    exact Subsingleton.elim _ _
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc := isCyclic_of_prime_card h
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc := isCyclic_of_prime_card h
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · exact h

theorem closure_involutions_fixed {G : Subgroup X} {a : X} (ha : a ∈ normalizer (G : Set X))
    {k : ℕ} (hk : 1 ≤ k)
    (hiso : Nonempty (Bender.autFixed (conjAut ha) ≃* CFSG.Theory.Comparator.PSL2Model k)) {z t : X}
    (hzH : z ∈ G ⊓ centralizer ({a} : Set X)) (htH : t ∈ G ⊓ centralizer ({a} : Set X))
    (hz2 : z * z = 1) (ht2 : t * t = 1) (hzt : z * t ≠ t * z) :
    closure {x : X | x ∈ G ⊓ centralizer ({a} : Set X) ∧ x * x = 1} =
      G ⊓ centralizer ({a} : Set X) := by
  obtain ⟨e⟩ := hiso
  set H := G ⊓ centralizer ({a} : Set X) with hH
  set N := closure {x : X | x ∈ H ∧ x * x = 1} with hN
  have hNH : N ≤ H := (closure_le _).mpr fun x hx => hx.1
  have hzN : z ∈ N := subset_closure ⟨hzH, hz2⟩
  have htN : t ∈ N := subset_closure ⟨htH, ht2⟩
  have eH : ↥H ≃* CFSG.Theory.Comparator.PSL2Model k :=
    ((MulEquiv.subgroupCongr (map_autFixed_conjAut ha)).symm.trans
      (Subgroup.equivMapOfInjective _ G.subtype G.subtype_injective).symm).trans e
  have hcardH : Nat.card ↥H = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
    rw [Nat.card_congr eH.toEquiv]
    exact Bender.card_psl2_even k hk
  apply le_antisymm hNH
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  ·
    have hk1' : k = 1 := by omega
    subst hk1'
    have h6 : Nat.card ↥H = 6 := by rw [hcardH]; norm_num
    have hNdvd : Nat.card ↥N ∣ 6 := h6 ▸ card_dvd_of_le hNH
    have hN6 : Nat.card ↥N = 6 :=
      card_eq_six_of_not_comm hNdvd (a := ⟨z, hzN⟩) (b := ⟨t, htN⟩)
        (fun h => hzt (congrArg Subtype.val h))
    exact (Subgroup.eq_of_le_of_card_ge hNH (le_of_eq (h6.trans hN6.symm))).ge
  ·
    have hBT : Bender.BenderType ↥H k 1 1 := Bender.BenderType.linear k hk2 eH
    have hsimple : IsSimpleGroup ↥H := hBT.isSimple
    have hnorm : (N.subgroupOf H).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr ?_
      intro g hg
      rw [mem_normalizer_iff]
      have key : ∀ k ∈ H, ∀ x ∈ N, k * x * k⁻¹ ∈ N := by
        intro k hk x hx
        have hle : N ≤ N.comap (MulAut.conj k).toMonoidHom := by
          refine (closure_le _).mpr ?_
          rintro y ⟨hyH, hy2⟩
          rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          refine subset_closure ⟨H.mul_mem (H.mul_mem hk hyH) (H.inv_mem hk), ?_⟩
          calc k * y * k⁻¹ * (k * y * k⁻¹) = k * (y * y) * k⁻¹ := by group
            _ = 1 := by rw [hy2]; group
        have := hle hx
        rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      intro x
      constructor
      · exact key g hg x
      · intro hx
        have := key g⁻¹ (H.inv_mem hg) _ hx
        simpa [mul_assoc] using this
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf H) with hbot | htop
    · exfalso
      have hz1 : z ≠ 1 := fun h => hzt (by rw [h, one_mul, mul_one])
      have : (⟨z, hzH⟩ : ↥H) ∈ N.subgroupOf H := mem_subgroupOf.mpr hzN
      rw [hbot, mem_bot] at this
      exact hz1 (congrArg Subtype.val this)
    · intro x hx
      have : (⟨x, hx⟩ : ↥H) ∈ N.subgroupOf H := htop ▸ mem_top _
      exact mem_subgroupOf.mp this

theorem z_mul_t_ne (S : ZDSetup X Z M) (c : Ctx16 Z M) : c.z * c.t ≠ c.t * c.z := by
  intro h
  apply c.htM
  refine S.prodDisc.mem_of_conj_mem c.hz c.hzM (g := c.t) ?_
  have e : c.t⁻¹ * c.z * c.t = c.z := by
    calc c.t⁻¹ * c.z * c.t = c.t⁻¹ * (c.z * c.t) := by group
      _ = c.t⁻¹ * (c.t * c.z) := by rw [h]
      _ = c.z := by group
  rw [e]
  exact c.hzM

theorem eq_of_fixed (S : ZDSetup X Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) {w : X} (hwN : w ∈ normalizer (c.B0 : Set X))
    (hwz : w * c.z = c.z * w) (hwt : w * c.t = c.t * w) {k : ℕ} (hk : 1 ≤ k)
    (hisoB : Nonempty (Bender.autFixed (conjAut hwN) ≃* CFSG.Theory.Comparator.PSL2Model k))
    (huN : c.u ∈ normalizer (cenHull Z w : Set X)) (hBw : ∀ y ∈ cenHull Z w, orderOf y = 2 → y ∈ Z)
    {k' : ℕ} (hk' : 1 ≤ k')
    (hisoF : Nonempty (Bender.autFixed (conjAut huN) ≃* CFSG.Theory.Comparator.PSL2Model k')) :
    k = k' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hut : c.u * c.t = c.t * c.u := (mem_centralizer_singleton_iff.mp c.ht_B).symm
  have huz : c.u * c.z = c.z * c.u := (mem_centralizer_singleton_iff.mp (Sec164.z_mem_B c)).symm
  have hz2 := S.invariant.mul_self_eq_one c.hz
  have ht2 := S.invariant.mul_self_eq_one c.ht
  have hzt := z_mul_t_ne S c.toCtx16
  have hzH₁ : c.z ∈ c.B0 ⊓ centralizer ({w} : Set X) :=
    mem_inf.mpr ⟨Sec164.z_mem_B0 c, mem_centralizer_singleton_iff.mpr hwz.symm⟩
  have htH₁ : c.t ∈ c.B0 ⊓ centralizer ({w} : Set X) :=
    mem_inf.mpr ⟨Sec164.t_mem_B0 c, mem_centralizer_singleton_iff.mpr hwt.symm⟩
  have hzF : c.z ∈ cenHull Z w := subset_closure ⟨c.hz, mem_centralizer_singleton_iff.mpr hwz.symm⟩
  have htF : c.t ∈ cenHull Z w := subset_closure ⟨c.ht, mem_centralizer_singleton_iff.mpr hwt.symm⟩
  have hzH₂ : c.z ∈ cenHull Z w ⊓ centralizer ({c.u} : Set X) :=
    mem_inf.mpr ⟨hzF, mem_centralizer_singleton_iff.mpr huz.symm⟩
  have htH₂ : c.t ∈ cenHull Z w ⊓ centralizer ({c.u} : Set X) :=
    mem_inf.mpr ⟨htF, mem_centralizer_singleton_iff.mpr hut.symm⟩
  have hgen₁ := closure_involutions_fixed hwN hk hisoB hzH₁ htH₁ hz2 ht2 hzt
  have hgen₂ := closure_involutions_fixed huN hk' hisoF hzH₂ htH₂ hz2 ht2 hzt
  have hle₁ :
      c.B0 ⊓ centralizer ({w} : Set X) ≤ cenHull Z w ⊓ centralizer ({c.u} : Set X) := by
    rw [← hgen₁]
    refine (closure_le _).mpr ?_
    rintro x ⟨hxH, hx2⟩
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
      have hxB0 := (mem_inf.mp hxH).1
      have hxZ := hB.invol x hxB0 hxo
      refine mem_inf.mpr ⟨subset_closure ⟨hxZ, (mem_inf.mp hxH).2⟩, ?_⟩
      exact Sec164.B0_le_B c hxB0
  have hle₂ :
      cenHull Z w ⊓ centralizer ({c.u} : Set X) ≤ c.B0 ⊓ centralizer ({w} : Set X) := by
    rw [← hgen₂]
    refine (closure_le _).mpr ?_
    rintro x ⟨hxH, hx2⟩
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
      have hxF := (mem_inf.mp hxH).1
      have hxZ := hBw x hxF hxo
      exact mem_inf.mpr ⟨subset_closure ⟨hxZ, (mem_inf.mp hxH).2⟩, Cor713.zHull_le _ hxF⟩
  have heq : c.B0 ⊓ centralizer ({w} : Set X) = cenHull Z w ⊓ centralizer ({c.u} : Set X) :=
    le_antisymm hle₁ hle₂
  obtain ⟨e₁⟩ := hisoB
  obtain ⟨e₂⟩ := hisoF
  have hc₁ : Nat.card ↥(c.B0 ⊓ centralizer ({w} : Set X)) = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
    rw [← map_autFixed_conjAut hwN, card_map_of_injective c.B0.subtype_injective,
      Nat.card_congr e₁.toEquiv]
    exact Bender.card_psl2_even k hk
  have hc₂ : Nat.card ↥(cenHull Z w ⊓ centralizer ({c.u} : Set X)) =
      2 ^ k' * ((2 ^ k') ^ 2 - 1) := by
    rw [← map_autFixed_conjAut huN, card_map_of_injective (cenHull Z w).subtype_injective,
      Nat.card_congr e₂.toEquiv]
    exact Bender.card_psl2_even k' hk'
  rw [heq] at hc₁
  exact card_psl2_injective hk hk' (hc₁.symm.trans hc₂)

end Sec165

end CFSG.GH74.Uniqueness
