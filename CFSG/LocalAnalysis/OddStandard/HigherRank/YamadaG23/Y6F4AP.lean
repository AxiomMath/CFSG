module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

open scoped Pointwise

variable {X : Type*} [Group X]

private lemma zpowers_eq_one_or_self_of_orderOf {G : Type*} [Group G] {t : G}
    (ht : orderOf t = 2) : ∀ x ∈ zpowers t, x = 1 ∨ x = t := by
  intro x hx
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨k, rfl⟩ := hx
  rw [← zpow_mod_orderOf t k, ht, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem y6f4a_eq_zpowers_of_cent [Finite X] {Q : Subgroup X} (hQ : IsPGroup 2 Q) {τ : X}
    (hτQ : τ ∈ Q) (hτ : orderOf τ = 2) (hc : ∀ x ∈ Q, x * τ = τ * x → x ∈ zpowers τ) :
    Q = zpowers τ := by
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hτ
    omega
  haveI : Nontrivial ↥Q :=
    ⟨⟨τ, hτQ⟩, ⟨1, Q.one_mem⟩, fun h => hτ1 (by simpa using congrArg Subtype.val h)⟩
  haveI : Nontrivial (Subgroup.center ↥Q) := IsPGroup.center_nontrivial hQ
  obtain ⟨z, hz_ne⟩ := exists_ne (1 : Subgroup.center ↥Q)
  have hz_mem : (z : ↥Q) ∈ Subgroup.center ↥Q := z.2
  have hz_ne' : (z : ↥Q) ≠ 1 := fun h => hz_ne (Subtype.ext h)
  have hcomm' : τ * ((z : ↥Q) : X) = ((z : ↥Q) : X) * τ := by
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz_mem (⟨τ, hτQ⟩ : ↥Q))
    simpa using this
  have hzG : ((z : ↥Q) : X) ∈ zpowers τ := hc _ (z : ↥Q).2 hcomm'.symm
  have hzG_ne : ((z : ↥Q) : X) ≠ 1 := fun h => hz_ne' (Subtype.coe_injective h)
  have hzt : (⟨τ, hτQ⟩ : ↥Q) = (z : ↥Q) := by
    rcases zpowers_eq_one_or_self_of_orderOf hτ ((z : ↥Q) : X) hzG with h | h
    · exact absurd h hzG_ne
    · exact Subtype.ext h.symm
  have ht_center : (⟨τ, hτQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
    rw [hzt]; exact hz_mem
  apply le_antisymm
  · intro x hx
    exact hc x hx (by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp ht_center (⟨x, hx⟩ : ↥Q))
      simpa using this)
  · exact Subgroup.zpowers_le.mpr hτQ

theorem y6f4a_sylow_card_two [Finite X] {Z : Subgroup X} {τ : X} (hτZ : τ ∈ Z)
    (hτ : orderOf τ = 2) (hC : Z ⊓ centralizer ({τ} : Set X) = zpowers τ) (S : Sylow 2 ↥Z) :
    Nat.card S = 2 := by
  let τ' : ↥Z := ⟨τ, hτZ⟩
  have hτ' : orderOf τ' = 2 := by rw [Subgroup.orderOf_mk, hτ]
  have hPτ : IsPGroup 2 (zpowers τ') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ']; norm_num)
  obtain ⟨Sτ, hSτ⟩ := IsPGroup.exists_le_sylow hPτ
  have hQ : IsPGroup 2 ((Sτ : Subgroup ↥Z).map Z.subtype) :=
    IsPGroup.map Sτ.isPGroup' Z.subtype
  have hτmem : τ ∈ (Sτ : Subgroup ↥Z).map Z.subtype :=
    Subgroup.mem_map.mpr ⟨τ', hSτ (Subgroup.mem_zpowers τ'), rfl⟩
  have hc : ∀ x ∈ (Sτ : Subgroup ↥Z).map Z.subtype, x * τ = τ * x → x ∈ zpowers τ := by
    intro x hx hcomm
    obtain ⟨q, _hq, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : (q : X) ∈ Z ⊓ centralizer ({τ} : Set X) :=
      Subgroup.mem_inf.mpr ⟨q.2, Subgroup.mem_centralizer_iff.mpr (fun g hg => by
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact hcomm.symm)⟩
    rwa [hC] at hmem
  have hmap : (Sτ : Subgroup ↥Z).map Z.subtype = zpowers τ :=
    y6f4a_eq_zpowers_of_cent hQ hτmem hτ hc
  have hcardSτ : Nat.card Sτ = 2 := by
    change Nat.card ((Sτ : Subgroup ↥Z)) = 2
    rw [← Subgroup.card_subtype Z (Sτ : Subgroup ↥Z), hmap, Nat.card_zpowers, hτ]
  haveI : Finite (Sylow 2 ↥Z) := Sylow.finite_of_finiteIndex Sτ
  have hcard : Nat.card Sτ = Nat.card S :=
    Nat.card_congr (Sylow.equiv Sτ S).toEquiv
  rw [← hcard, hcardSτ]

theorem y6f4a_invol_conj [Finite X] {Z : Subgroup X} {τ : X} (hτZ : τ ∈ Z) (hτ : orderOf τ = 2)
    (hC : Z ⊓ centralizer ({τ} : Set X) = zpowers τ) {u : X} (huZ : u ∈ Z) (hu : orderOf u = 2) :
    ∃ z ∈ Z, z * τ * z⁻¹ = u := by
  let τ' : ↥Z := ⟨τ, hτZ⟩
  let u' : ↥Z := ⟨u, huZ⟩
  have hτ' : orderOf τ' = 2 := by rw [Subgroup.orderOf_mk, hτ]
  have hu' : orderOf u' = 2 := by rw [Subgroup.orderOf_mk, hu]
  have hu'_ne : u' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu'
    omega
  have hPτ : IsPGroup 2 (zpowers τ') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ']; norm_num)
  have hPu : IsPGroup 2 (zpowers u') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu']; norm_num)
  obtain ⟨Sτ, hSτ⟩ := IsPGroup.exists_le_sylow hPτ
  obtain ⟨Su, hSu⟩ := IsPGroup.exists_le_sylow hPu
  have hcSτ : Nat.card Sτ = 2 := y6f4a_sylow_card_two hτZ hτ hC Sτ
  have hcSu : Nat.card Su = 2 := y6f4a_sylow_card_two hτZ hτ hC Su
  have hSτeq : zpowers τ' = (Sτ : Subgroup ↥Z) :=
    Subgroup.eq_of_le_of_card_ge hSτ (by rw [Nat.card_zpowers, hτ', hcSτ])
  have hSueq : zpowers u' = (Su : Subgroup ↥Z) :=
    Subgroup.eq_of_le_of_card_ge hSu (by rw [Nat.card_zpowers, hu', hcSu])
  haveI : Finite (Sylow 2 ↥Z) := Sylow.finite_of_finiteIndex Sτ
  obtain ⟨z, hz⟩ := MulAction.exists_smul_eq (M := ↥Z) Sτ Su
  have hmem : u' ∈ (z • Sτ : Sylow 2 ↥Z) := by
    rw [hz]
    change u' ∈ (Su : Subgroup ↥Z)
    rw [← hSueq]
    exact Subgroup.mem_zpowers u'
  have hmemSet : u' ∈ (MulAut.conj z : MulAut ↥Z) • (Sτ : Set ↥Z) := by
    rw [← Sylow.coe_smul (g := z) (P := Sτ)]
    exact hmem
  rw [Set.mem_smul_set] at hmemSet
  obtain ⟨y, hy, hyu⟩ := hmemSet
  have hyz : y ∈ zpowers τ' := by
    rw [hSτeq]
    exact hy
  rcases zpowers_eq_one_or_self_of_orderOf hτ' y hyz with hy1 | hyτ
  · exfalso
    exact hu'_ne (by rw [← hyu, hy1]; simp)
  · refine ⟨(z : X), z.2, ?_⟩
    have hzu : z * τ' * z⁻¹ = u' := by
      rw [← hyu, hyτ]
      simp [MulAut.smul_def, MulAut.conj_apply]
    have := congrArg (fun w : ↥Z => (w : X)) hzu
    simpa using this

theorem y6f4a_normalizer_eq_mul [Finite X] {Z : Subgroup X} {τ : X} (hτZ : τ ∈ Z)
    (hτ : orderOf τ = 2) (hC : Z ⊓ centralizer ({τ} : Set X) = zpowers τ) {y : X}
    (hy : y ∈ normalizer (Z : Set X)) :
    ∃ z ∈ Z, ∃ c ∈ centralizer ({τ} : Set X), y = z * c := by
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hτ
    omega
  have hτ2 : τ * τ = 1 := by
    have := pow_orderOf_eq_one τ
    rw [hτ] at this
    simpa [pow_two] using this
  have hyZ : y * τ * y⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hy τ).mp hτZ
  have hu1 : y * τ * y⁻¹ ≠ 1 := by
    intro h
    have h' : τ = 1 := by
      have := congrArg (fun w => y⁻¹ * w * y) h
      simpa [mul_assoc] using this
    exact hτ1 h'
  have hu_pow : (y * τ * y⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    calc (y * τ * y⁻¹) * (y * τ * y⁻¹)
        = y * (τ * τ) * y⁻¹ := by group
      _ = 1 := by rw [hτ2]; group
  have hu2 : orderOf (y * τ * y⁻¹) = 2 := orderOf_eq_prime hu_pow hu1
  obtain ⟨z, hzZ, hzu⟩ := y6f4a_invol_conj hτZ hτ hC hyZ hu2
  refine ⟨z, hzZ, z⁻¹ * y, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    have hconjc : (z⁻¹ * y) * τ * (z⁻¹ * y)⁻¹ = τ := by
      calc (z⁻¹ * y) * τ * (z⁻¹ * y)⁻¹
          = z⁻¹ * (y * τ * y⁻¹) * z := by group
        _ = z⁻¹ * (z * τ * z⁻¹) * z := by rw [← hzu]
        _ = τ := by group
    have hcomm : (z⁻¹ * y) * τ = τ * (z⁻¹ * y) := by
      calc (z⁻¹ * y) * τ
          = (z⁻¹ * y) * τ * (z⁻¹ * y)⁻¹ * (z⁻¹ * y) := by group
        _ = τ * (z⁻¹ * y) := by rw [hconjc]
    exact hcomm.symm
  · group

theorem y6f4a_perfect_le_of_solvable {D : Type*} [Group D] [Finite D] (N : Subgroup D)
    [N.Normal] [Group.IsSolvable (D ⧸ N)] {B : Subgroup D} (hB : Group.IsPerfect ↥B) :
    B ≤ N := by
  set f : D →* D ⧸ N := QuotientGroup.mk' N with hf
  have hker : f.ker = N := by
    rw [hf]
    exact QuotientGroup.ker_mk' N
  haveI : Group.IsPerfect ↥B := hB
  have hperf : Group.IsPerfect ↥(B.map f) := by
    have h := Group.IsPerfect.range (f := f.comp B.subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hsub : Subsingleton ↥(B.map f) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    haveI : Nontrivial ↥(B.map f) := h
    haveI : Group.IsPerfect ↥(B.map f) := hperf
    exact Group.IsPerfect.not_isSolvable ↥(B.map f) inferInstance
  have hbot : B.map f = ⊥ := Subgroup.eq_bot_of_subsingleton (H := B.map f)
  rw [← hker]
  intro b hb
  have hbf : f b ∈ B.map f := Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
  rw [hbot] at hbf
  exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hbf)

theorem y6f4a_perfect_le_of_solvable_sub [Finite X] {D A : Subgroup X} (hAD : A ≤ D)
    [(A.subgroupOf D).Normal] [Group.IsSolvable (↥D ⧸ A.subgroupOf D)] {B : Subgroup X}
    (hBD : B ≤ D) (hB : Group.IsPerfect ↥B) : B ≤ A := by
  have hperf : Group.IsPerfect ↥(B.subgroupOf D) := by
    haveI : Group.IsPerfect ↥B := hB
    have hsurj : Function.Surjective
        ((Subgroup.subgroupOfEquivOfLe hBD).symm : ↥B → ↥(B.subgroupOf D)) :=
      fun y => ⟨(Subgroup.subgroupOfEquivOfLe hBD) y, by simp⟩
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hBD).symm.toMonoidHom) hsurj
  have hle : B.subgroupOf D ≤ A.subgroupOf D :=
    y6f4a_perfect_le_of_solvable (D := ↥D) (N := A.subgroupOf D) (B := B.subgroupOf D) hperf
  intro b hb
  have hbD : b ∈ D := hBD hb
  have hmem : (⟨b, hbD⟩ : ↥D) ∈ B.subgroupOf D := by
    rw [Subgroup.mem_subgroupOf]
    exact hb
  have hmemA : (⟨b, hbD⟩ : ↥D) ∈ A.subgroupOf D := hle hmem
  simpa using (Subgroup.mem_subgroupOf.mp hmemA)

end CFSG.OddStandard.HigherRank.YamadaG23
