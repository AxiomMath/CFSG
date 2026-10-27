module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_mem_conj_le_of_isSylowOf [Finite G] {K T P : Subgroup G} (hT : IsSylowOf 2 T K)
    (hPK : P ≤ K) (hP : IsPGroup 2 P) : ∃ k ∈ K, ∀ x ∈ P, k * x * k⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hT
  have hP' : IsPGroup 2 (P.subgroupOf K) := hP.comap_of_injective K.subtype K.subtype_injective
  obtain ⟨Q', hQ'⟩ := hP'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨((g⁻¹ : K) : G), (g⁻¹ : K).2, fun x hx => ?_⟩
  have hx' : (⟨x, hPK hx⟩ : K) ∈ P.subgroupOf K := hx
  have h1 : (⟨x, hPK hx⟩ : K) ∈ ((g • Q : Sylow 2 K) : Subgroup K) := by rw [hg]; exact hQ' hx'
  have h2 : g⁻¹ * ⟨x, hPK hx⟩ * g ∈ (Q : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul] at h1
    have := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).1 h1
    simpa [MulAut.conj_apply, mul_assoc] using this
  have h3 : ((g⁻¹ * ⟨x, hPK hx⟩ * g : K) : G) ∈ T := by
    rw [← hQ]
    exact Subgroup.mem_map.2 ⟨_, h2, rfl⟩
  simpa using h3

theorem exists_two_ne_one {A : Set G} (h : 2 < A.ncard) (hfin : A.Finite) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff hfin).1 h
  by_cases h1 : a = 1
  · exact ⟨b, hb, c, hc, fun h => hab (h1.trans h.symm), fun h => hac (h1.trans h.symm), hbc⟩
  by_cases h2 : b = 1
  · exact ⟨a, ha, c, hc, h1, fun h => hbc (h2.trans h.symm), hac⟩
  · exact ⟨a, ha, b, hb, h1, h2, hab⟩

theorem isCyclic_quot_of_gen [Finite G] {S J : Subgroup G} [(J.subgroupOf S).Normal]
    (hcyc : ∃ s ∈ S, ∀ x ∈ S, ∃ k : ℤ, (s ^ k)⁻¹ * x ∈ J) : IsCyclic (S ⧸ J.subgroupOf S) := by
  obtain ⟨s, hs, h⟩ := hcyc
  refine ⟨⟨(⟨s, hs⟩ : S), fun y => ?_⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ := h x x.2
  refine ⟨k, ?_⟩
  simp only
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
  exact hk

theorem exists_ne_one_inf_of_cyclic [Finite G] {S J A : Subgroup G} (hJn : (J.subgroupOf S).Normal)
    (hcyc : ∃ s ∈ S, ∀ x ∈ S, ∃ k : ℤ, (s ^ k)⁻¹ * x ∈ J) (hAS : A ≤ S)
    (hA : ∀ x ∈ A, x * x = 1) (hcard : 2 < Nat.card A) : ∃ x ∈ A ⊓ J, x ≠ 1 := by
  classical
  have := hJn
  have : IsCyclic (S ⧸ J.subgroupOf S) := isCyclic_quot_of_gen hcyc
  have : Fintype (S ⧸ J.subgroupOf S) := Fintype.ofFinite _
  have hncard : 2 < (A : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two_ne_one hncard (Set.toFinite _)
  set a' : S ⧸ J.subgroupOf S := QuotientGroup.mk ⟨a, hAS ha⟩ with ha'
  set b' : S ⧸ J.subgroupOf S := QuotientGroup.mk ⟨b, hAS hb⟩ with hb'
  have hsq : ∀ x ∈ A, ∀ hx : x ∈ S,
      (QuotientGroup.mk ⟨x, hx⟩ : S ⧸ J.subgroupOf S) ^ 2 = 1 := by
    intro x hx hxS
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hxS⟩ : S) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hA x hx)
    rw [this]; rfl
  by_cases h1 : a' = 1
  · have := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := J.subgroupOf S) _).1 h1)
    exact ⟨a, ⟨ha, this⟩, ha1⟩
  by_cases h2 : b' = 1
  · have := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := J.subgroupOf S) _).1 h2)
    exact ⟨b, ⟨hb, this⟩, hb1⟩
  by_cases h3 : a' = b'
  · refine ⟨a⁻¹ * b, ⟨A.mul_mem (A.inv_mem ha) hb, ?_⟩, ?_⟩
    · have := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h3)
      simpa using this
    · intro h; apply hab; simpa [inv_mul_eq_one] using h
  exfalso
  have hsub : ({1, a', b'} : Finset (S ⧸ J.subgroupOf S)) ⊆
      Finset.univ.filter (fun w : S ⧸ J.subgroupOf S => w ^ 2 = 1) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with rfl | rfl | rfl
    · simp
    · exact hsq a ha _
    · exact hsq b hb _
  have hcard3 : ({1, a', b'} : Finset (S ⧸ J.subgroupOf S)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using h3
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
  have := Finset.card_le_card hsub
  have h4 := IsCyclic.card_pow_eq_one_le (α := S ⧸ J.subgroupOf S) (n := 2) (by norm_num)
  omega

theorem map_conj_eq_of_ti {Z : Subgroup G}
    (hti : ∀ g : G, Z ⊓ Z.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      Z.map (MulAut.conj g).toMonoidHom = Z)
    (g h : G) (hne : Z.map (MulAut.conj g).toMonoidHom ⊓ Z.map (MulAut.conj h).toMonoidHom ≠ ⊥) :
    Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj h).toMonoidHom := by
  have key : ∀ k : G, Z.map (MulAut.conj (h * k)).toMonoidHom =
      (Z.map (MulAut.conj k).toMonoidHom).map (MulAut.conj h).toMonoidHom := by
    intro k
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hmem : ∃ x : G, x ≠ 1 ∧ x ∈ Z.map (MulAut.conj g).toMonoidHom ∧
      x ∈ Z.map (MulAut.conj h).toMonoidHom := by
    by_contra hcon
    apply hne
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    exact hcon ⟨x, fun h1 => hx1 (by simp [h1]), hx.1, hx.2⟩
  obtain ⟨x, hx1, hxg, hxh⟩ := hmem
  have h1 : Z ⊓ Z.map (MulAut.conj (h⁻¹ * g)).toMonoidHom ≠ ⊥ := by
    intro hbot
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hxh
    obtain ⟨z', hz', hz'x⟩ := Subgroup.mem_map.1 hxg
    have hy : z ∈ Z ⊓ Z.map (MulAut.conj (h⁻¹ * g)).toMonoidHom := by
      refine ⟨hz, Subgroup.mem_map.2 ⟨z', hz', ?_⟩⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hz'x hzx ⊢
      have : h * z * h⁻¹ = g * z' * g⁻¹ := by rw [hzx, hz'x]
      calc h⁻¹ * g * z' * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * z' * g⁻¹) * h := by group
        _ = h⁻¹ * (h * z * h⁻¹) * h := by rw [this]
        _ = z := by group
    rw [hbot] at hy
    have hz1 : z = 1 := by simpa using hy
    apply hx1
    rw [← hzx, hz1]; simp
  have h2 := hti _ h1
  have h3 := key (h⁻¹ * g)
  rw [h2] at h3
  have e : h * (h⁻¹ * g) = g := by group
  rw [e] at h3
  rw [h3]

end CFSG.CGT.PushingUpLit.A78Sp4
