module

public import CFSG.Holt.Induced
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
import CFSG.GroupTheory.FourGroupOddOrderIdentity

public section

namespace CFSG.Holt

open MulAction

section Orbit

variable {G : Type*} [Group G] [Finite G] {Δ : Type*} [MulAction G Δ]

theorem orbit_inf_centralizer_eq_fixSet {N P : Subgroup G} (hN : Odd (Nat.card N))
    [IsPretransitive N Δ] (hP : IsPGroup 2 P) (hPN : P ≤ Subgroup.normalizer (N : Set G))
    {α : Δ} (hα : α ∈ fixSet Δ P) :
    orbit (N ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) α = fixSet Δ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext β
  constructor
  · rintro ⟨c, rfl⟩ y hy
    have hc : y * (c : G) = c * y := Subgroup.mem_centralizer_iff.mp c.2.2 y hy
    change y • (c : G) • α = (c : G) • α
    rw [← mul_smul, hc, mul_smul, hα y hy]
  · intro hβ
    obtain ⟨g, hg⟩ := exists_smul_eq N α β
    obtain ⟨m, hm, hmα⟩ :=
      exists_mem_centralizer_smul_eq hN.not_two_dvd_nat hP hPN hα hβ g.2 hg
    exact ⟨⟨m, hm⟩, hmα⟩

theorem relIndex_stabilizer_eq_ncard_fixSet {N P : Subgroup G} (hN : Odd (Nat.card N))
    [IsPretransitive N Δ] (hP : IsPGroup 2 P) (hPN : P ≤ Subgroup.normalizer (N : Set G))
    {α : Δ} (hα : α ∈ fixSet Δ P) :
    (stabilizer G α).relIndex (N ⊓ Subgroup.centralizer (P : Set G)) = (fixSet Δ P).ncard := by
  rw [← orbit_inf_centralizer_eq_fixSet hN hP hPN hα, ← index_stabilizer]
  rfl

end Orbit

section BW

variable {G : Type*} [Group G] {Δ : Type*} [MulAction G Δ]

namespace CaseTwo

theorem fixedPointSubgroup_eq_subgroupOf {A : Type*} [Group A] {N P : Subgroup G}
    [MulDistribMulAction A N]
    (h : ∀ n : N, n ∈ fixedPointSubgroup A N ↔ ∀ x ∈ P, x * n * x⁻¹ = n) :
    fixedPointSubgroup A N = (N ⊓ Subgroup.centralizer (P : Set G)).subgroupOf N := by
  ext n
  rw [h, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hn
    refine ⟨n.2, fun x hx => ?_⟩
    calc x * n = x * n * x⁻¹ * x := by group
      _ = n * x := by rw [hn x hx]
  · rintro ⟨-, hn⟩ x hx
    rw [hn x hx]
    group

end CaseTwo

theorem relIndex_fixedPointSubgroup_eq [Finite G] {A : Type*} [Group A] {N P : Subgroup G}
    (hN : Odd (Nat.card N)) [IsPretransitive N Δ] [MulDistribMulAction A N] (hP : IsPGroup 2 P)
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) {α : Δ} (hα : α ∈ fixSet Δ P)
    (h : ∀ n : N, n ∈ fixedPointSubgroup A N ↔ ∀ x ∈ P, x * n * x⁻¹ = n) :
    ((stabilizer G α).subgroupOf N).relIndex (fixedPointSubgroup A N) = (fixSet Δ P).ncard := by
  rw [CaseTwo.fixedPointSubgroup_eq_subgroupOf h, Subgroup.relIndex_subgroupOf inf_le_left,
    relIndex_stabilizer_eq_ncard_fixSet hN hP hPN hα]

namespace CaseTwo

@[expose, reducible] def conjActOfLeNormalizer (T K : Subgroup G)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) : MulDistribMulAction T K where
  smul t k := ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTK t.2) k).mp k.2⟩
  one_smul k := Subtype.ext (by change (1 : G) * k * 1⁻¹ = k; group)
  mul_smul s t k := Subtype.ext (by
    change (s * t : G) * k * (s * t : G)⁻¹ = s * (t * k * (t : G)⁻¹) * (s : G)⁻¹
    group)
  smul_mul t k l := Subtype.ext (by
    change (t : G) * (k * l) * (t : G)⁻¹ = (t * k * (t : G)⁻¹) * (t * l * (t : G)⁻¹)
    group)
  smul_one t := Subtype.ext (by change (t : G) * 1 * (t : G)⁻¹ = 1; group)

end CaseTwo

theorem ncard_mul_ncard_fixedBy_inter_sq [Finite G] {N : Subgroup G} (hN : Odd (Nat.card N))
    [IsPretransitive N Δ] {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) (haN : a ∈ Subgroup.normalizer (N : Set G))
    (hbN : b ∈ Subgroup.normalizer (N : Set G)) {α : Δ} (hαa : a • α = α) (hαb : b • α = α) :
    Nat.card Δ * (fixedBy Δ a ∩ fixedBy Δ b).ncard ^ 2 =
      (fixedBy Δ a).ncard * (fixedBy Δ b).ncard * (fixedBy Δ (a * b)).ncard := by
  classical
  set V := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hab
  have hVK : IsKleinFour V :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a b ha hb ha1 hb1 hne hab
  have hmemV : ∀ x : G, x ∈ V ↔ x = a * b ∨ x = a ∨ x = b ∨ x = 1 := fun x => Iff.rfl
  have haV : a ∈ V := (hmemV a).2 (Or.inr (Or.inl rfl))
  have hbV : b ∈ V := (hmemV b).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hVN : V ≤ Subgroup.normalizer (N : Set G) := fun x hx => by
    rcases (hmemV x).1 hx with rfl | rfl | rfl | rfl
    · exact mul_mem haN hbN
    · exact haN
    · exact hbN
    · exact one_mem _
  have hVα : α ∈ fixSet Δ V := fun x hx => by
    rcases (hmemV x).1 hx with rfl | rfl | rfl | rfl
    · rw [mul_smul, hαb, hαa]
    · exact hαa
    · exact hαb
    · exact one_smul _ _
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; rfl)
  let _ : MulDistribMulAction V N := CaseTwo.conjActOfLeNormalizer V N hVN
  let _ : Fintype V := Fintype.ofFinite V
  set Y : Subgroup N := (stabilizer G α).subgroupOf N
  have hY : ∀ v : V, ∀ y ∈ Y, v • y ∈ Y := by
    intro v y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have hv : (v : G)⁻¹ • α = α := by rw [inv_smul_eq_iff, hVα _ v.2]
    rw [mem_stabilizer_iff]
    change ((v : G) * y * (v : G)⁻¹) • α = α
    rw [mul_smul, mul_smul, hv, mem_stabilizer_iff.mp hy, hVα _ v.2]
  have h := (CFSG.GroupTheory.odd_group_four_group_centralizer_order_identity
    (A := V) (X := N) hN).2 Y hY
  have hYidx : Y.index = Nat.card Δ := by
    have hYst : Y = stabilizer N α := by ext; rfl
    rw [hYst, index_stabilizer_of_transitive]
  have htop : Y.relIndex (fixedPointSubgroup V N) = (fixedBy Δ a ∩ fixedBy Δ b).ncard := by
    rw [relIndex_fixedPointSubgroup_eq (A := V) hN hV2 hVN hVα fun n =>
      ⟨fun hn x hx => congrArg Subtype.val (hn ⟨x, hx⟩),
        fun hn v => Subtype.ext (hn v v.2)⟩]
    congr 1
    ext ω
    refine ⟨fun hω => ⟨hω a haV, hω b hbV⟩, fun hω x hx => ?_⟩
    rcases (hmemV x).1 hx with rfl | rfl | rfl | rfl
    · rw [mul_smul, hω.2, hω.1]
    · exact hω.1
    · exact hω.2
    · exact one_smul _ _
  have hcyc : ∀ t : V, Y.relIndex (fixedPointSubgroup (Subgroup.zpowers t) N) =
      (fixedBy Δ (t : G)).ncard := by
    intro t
    have hle : Subgroup.zpowers (t : G) ≤ V := Subgroup.zpowers_le.mpr t.2
    rw [relIndex_fixedPointSubgroup_eq (A := Subgroup.zpowers t) hN (hV2.to_le hle) (hle.trans hVN)
      (fun x hx => hVα x (hle hx)) fun n => ?_, fixSet_zpowers]
    constructor
    · intro hn x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact congrArg Subtype.val (hn ⟨t ^ k, Subgroup.zpow_mem_zpowers t k⟩)
    · rintro hn ⟨x, hx⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subtype.ext (hn _ ⟨k, by simp⟩)
  set ta : V := ⟨a, haV⟩
  set tb : V := ⟨b, hbV⟩
  have hta : ta ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have htb : tb ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have htab : ta ≠ tb := fun h => hne (congrArg Subtype.val h)
  have habne1 : ta * tb ≠ 1 := fun h => hne (by
    have h' := congrArg Subtype.val (mul_eq_one_iff_eq_inv.mp h)
    simpa [ta, tb, inv_eq_of_mul_eq_one_right hb] using h')
  have habnea : ta * tb ≠ ta := fun h => htb (by simpa using h)
  have habneb : ta * tb ≠ tb := fun h => hta (by simpa using h)
  have herase : Finset.univ.erase (1 : V) = {ta * tb, ta, tb} := by
    rw [← IsKleinFour.eq_finset_univ hta htb htab]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx1, hx | hx | hx | hx⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
      · exact absurd hx hx1
    · rintro (hx | hx | hx) <;> subst hx
      · exact ⟨habne1, Or.inl rfl⟩
      · exact ⟨hta, Or.inr (Or.inl rfl)⟩
      · exact ⟨htb, Or.inr (Or.inr (Or.inl rfl))⟩
  rw [herase, Finset.prod_insert (by simp [habnea, habneb]),
    Finset.prod_insert (by simp [htab]), Finset.prod_singleton, hcyc, hcyc, hcyc, htop,
    hYidx] at h
  rw [h]
  simp only [ta, tb, Subgroup.coe_mul]
  ring

namespace CaseTwo

theorem smul_eq_of_commute_of_fixedBy_eq_singleton {a b : G} (hab : Commute a b) {α : Δ}
    (hb : fixedBy Δ b = {α}) : a • α = α := by
  have hα : b • α = α := by
    have : α ∈ fixedBy Δ b := hb ▸ rfl
    exact this
  have : a • α ∈ fixedBy Δ b := by
    change b • a • α = a • α
    rw [← mul_smul, ← hab.eq, mul_smul, hα]
  rwa [hb, Set.mem_singleton_iff] at this

theorem eq_of_fixedBy_one_eq_singleton {α : Δ} (h : fixedBy Δ (1 : G) = {α}) (ω : Δ) :
    ω = α := by
  have : ω ∈ fixedBy Δ (1 : G) := one_smul G ω
  rwa [h, Set.mem_singleton_iff] at this

end CaseTwo

variable [Finite G]

theorem ncard_eq_mul_of_fixedBy_eq_singleton {N : Subgroup G} (hN : Odd (Nat.card N))
    [IsPretransitive N Δ] {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b)
    (haN : a ∈ Subgroup.normalizer (N : Set G)) (hbN : b ∈ Subgroup.normalizer (N : Set G))
    {α : Δ} (hb' : fixedBy Δ b = {α}) :
    Nat.card Δ = (fixedBy Δ a).ncard * (fixedBy Δ (a * b)).ncard := by
  have hαa := CaseTwo.smul_eq_of_commute_of_fixedBy_eq_singleton hab hb'
  have hαb : b • α = α := by
    have : α ∈ fixedBy Δ b := hb' ▸ rfl
    exact this
  have hunique : ∀ ω : Δ, fixedBy Δ (1 : G) = {α} → ω = α :=
    fun ω h => CaseTwo.eq_of_fixedBy_one_eq_singleton h ω
  by_cases ha1 : a = 1
  · subst ha1
    rw [one_mul, hb', Set.ncard_singleton, mul_one, fixedBy_one_eq_univ, Set.ncard_univ]
  by_cases hb1 : b = 1
  · subst hb1
    have hsub : ∀ ω : Δ, ω = α := fun ω => hunique ω hb'
    have hcard : Nat.card Δ = 1 := Nat.card_eq_one_iff_exists.mpr ⟨α, hsub⟩
    have hFa : fixedBy Δ a = {α} := Set.eq_singleton_iff_unique_mem.mpr ⟨hαa, fun ω _ => hsub ω⟩
    rw [mul_one, hFa, Set.ncard_singleton, hcard]
  by_cases hne : a = b
  · subst hne
    rw [ha, hb', Set.ncard_singleton, one_mul, fixedBy_one_eq_univ, Set.ncard_univ]
  have h := ncard_mul_ncard_fixedBy_inter_sq hN ha hb hab ha1 hb1 hne haN hbN hαa hαb
  have hinter : fixedBy Δ a ∩ fixedBy Δ b = {α} := by
    rw [hb', Set.inter_eq_right, Set.singleton_subset_iff]
    exact hαa
  rw [hinter, hb', Set.ncard_singleton] at h
  simpa using h

end BW

section TypeA

variable {X : Type*} [Group X] (Ω : Type*) [MulAction X Ω]

@[expose] def toCentralizerImage (T : Subgroup X) :
    Subgroup.centralizer (T : Set X) →* centralizerImage Ω T :=
  (MulAction.toPermHom (Subgroup.centralizer (T : Set X)) (fixSet Ω T)).rangeRestrict

variable {Ω}

@[simp] theorem coe_toCentralizerImage_smul (T : Subgroup X) (c : Subgroup.centralizer (T : Set X))
    (ω : fixSet Ω T) : ((toCentralizerImage Ω T c • ω : fixSet Ω T) : Ω) = (c : X) • (ω : Ω) :=
  rfl

variable [Finite Ω]

end TypeA

end CFSG.Holt
