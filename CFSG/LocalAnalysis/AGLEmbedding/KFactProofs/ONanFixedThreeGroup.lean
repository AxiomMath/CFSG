module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups

public section

namespace CFSG.AGLEmbedding.FixedThree

open scoped Pointwise

open CFSG.Open

variable {X : Type} [Group X]

@[expose] def FixedThreeConclusion (L : Subgroup X) (u : X) : Prop :=
  (∃ y ∈ L, IsPGroup 3 (Subgroup.zpowers y) ∧ y * u = u * y ∧ ∃ l ∈ L, y * l ≠ l * y) ∨
  (∃ h ∈ L, h ^ 3 = 1 ∧ ∃ c ∈ L, u * h * u⁻¹ = c * h ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧ c * u = u * c ∧
    ∀ x ∈ L, (∀ l ∈ L, x * l = l * x) ↔ x ∈ Subgroup.zpowers c)

theorem conclusion_of_inner {L : Subgroup X} (hZ : IsPGroup 3 (Subgroup.center L)) {u : X}
    (hu3 : u ^ 3 = 1) (huC : u ∉ Subgroup.centralizer (L : Set X)) {a : X} (haL : a ∈ L)
    (ha : ∀ l ∈ L, u * l * u⁻¹ = a * l * a⁻¹) : FixedThreeConclusion L u := by
  left
  obtain ⟨c, hc⟩ : ∃ c : X, c = a⁻¹ * u := ⟨_, rfl⟩
  have hcC : ∀ l ∈ L, c * l = l * c := by
    intro l hl
    have h1 := ha l hl
    rw [hc]
    calc a⁻¹ * u * l = a⁻¹ * (u * l * u⁻¹) * u := by group
      _ = a⁻¹ * (a * l * a⁻¹) * u := by rw [h1]
      _ = l * (a⁻¹ * u) := by group
  have hac : a * c = c * a := (hcC a haL).symm
  have hu : u = a * c := by rw [hc]; group
  have h3 : a ^ 3 * c ^ 3 = 1 := by
    have : (a * c) ^ 3 = a ^ 3 * c ^ 3 := (Commute.mul_pow hac 3)
    rw [← this, ← hu, hu3]
  have hc3C : ∀ l ∈ L, c ^ 3 * l = l * c ^ 3 := by
    intro l hl
    have : Commute c l := hcC l hl
    exact (this.pow_left 3).eq
  have ha3Z : (⟨a ^ 3, L.pow_mem haL 3⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 : a ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
    show (g : X) * a ^ 3 = a ^ 3 * g
    rw [h1]
    have := hc3C g g.2
    calc (g : X) * (c ^ 3)⁻¹ = (c ^ 3)⁻¹ * (c ^ 3 * g) * (c ^ 3)⁻¹ := by group
      _ = (c ^ 3)⁻¹ * (g * c ^ 3) * (c ^ 3)⁻¹ := by rw [this]
      _ = (c ^ 3)⁻¹ * g := by group
  obtain ⟨k, hk⟩ := hZ ⟨_, ha3Z⟩
  have hak : a ^ (3 ^ (k + 1)) = 1 := by
    have := congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : X)) hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
    rw [pow_succ, mul_comm, pow_mul]
    exact this
  refine ⟨a, haL, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨k + 1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hak, one_zpow]
  · rw [hu]
    calc a * (a * c) = a * (c * a) := by rw [hac]
      _ = a * c * a := by rw [mul_assoc]
  · by_contra hall
    push Not at hall
    apply huC
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := ha l hl
    have h3' : u * l * u⁻¹ = l := by
      rw [h1]
      calc a * l * a⁻¹ = (l * a) * a⁻¹ := by rw [hall l hl]
        _ = l := by group
    calc l * u = (u * l * u⁻¹) * u := by rw [h3']
      _ = u * l := by group

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {g : G} {k : ℕ}
    (h : g ^ (3 ^ k) = 1) : IsPGroup 3 (Subgroup.zpowers g) := by
  intro x
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
  refine ⟨k, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem conclusion_of_center_bot [Finite X] {L : Subgroup X}
    (hZ : Subgroup.center ↥L = ⊥) (h3L : 3 ∣ Nat.card L) {u : X} (hu3 : u ^ 3 = 1)
    (huN : u ∈ Subgroup.normalizer (L : Set X))
    (huC : u ∉ Subgroup.centralizer (L : Set X)) : FixedThreeConclusion L u := by
  have hZp : IsPGroup 3 (Subgroup.center ↥L) := by
    rw [hZ]
    exact IsPGroup.of_bot
  by_cases huL : u ∈ L
  · exact conclusion_of_inner hZp hu3 huC huL (fun l hl => rfl)
  left
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup X := L ⊔ Subgroup.zpowers u with hH
  have hLH : L ≤ H := le_sup_left
  have huH : u ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hHN : H ≤ Subgroup.normalizer (L : Set X) :=
    sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 huN)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  set x' : ↥H := ⟨(x : X), hLH x.2⟩ with hx'
  set u' : ↥H := ⟨u, huH⟩ with hu'
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by
    simp only [hx', Subgroup.coe_pow, OneMemClass.coe_one]
    exact congrArg Subtype.val hx3)
  have hu'3 : u' ^ 3 = 1 := Subtype.ext (by
    simp only [hu', Subgroup.coe_pow, OneMemClass.coe_one]
    exact hu3)
  obtain ⟨Px, hPx⟩ := (isPGroup_zpowers_of_pow_eq_one (g := x') (k := 1)
    (by simpa using hx'3)).exists_le_sylow
  obtain ⟨Pu, hPu⟩ := (isPGroup_zpowers_of_pow_eq_one (g := u') (k := 1)
    (by simpa using hu'3)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) Px Pu
  have hgx : g * x' * g⁻¹ ∈ (Pu : Subgroup ↥H) := by
    have h1 : x' ∈ (Px : Subgroup ↥H) := hPx (Subgroup.mem_zpowers x')
    have h2 := Subgroup.smul_mem_pointwise_smul x' (MulAut.conj g) (Px : Subgroup ↥H) h1
    have h3 : ((g • Px : Sylow 3 ↥H) : Subgroup ↥H) = MulAut.conj g • (Px : Subgroup ↥H) := rfl
    rw [← h3, hg] at h2
    simpa [MulAut.smul_def] using h2
  have : Fact (IsPGroup 3 ↥(Pu : Subgroup ↥H)) := ⟨Pu.isPGroup'⟩
  have hLHn : (L.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN
  set N : Subgroup ↥(Pu : Subgroup ↥H) := (L.subgroupOf H).subgroupOf (Pu : Subgroup ↥H) with hN
  have hNn : N.Normal := hLHn.subgroupOf _
  have hzL : ((g * x' * g⁻¹ : ↥H) : X) ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hHN g.2) (x : X)).1 x.2
    simpa [hx'] using this
  have hzN : (⟨g * x' * g⁻¹, hgx⟩ : ↥(Pu : Subgroup ↥H)) ∈ N := by
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hzL
  have hz1 : (⟨⟨g * x' * g⁻¹, hgx⟩, hzN⟩ : ↥N) ≠ 1 := by
    intro h
    have h1 : g * x' * g⁻¹ = 1 := congrArg (fun w : ↥N => ((w : ↥(Pu : Subgroup ↥H)) : ↥H)) h
    have h2 : x' = 1 := by
      have := congrArg (fun w : ↥H => g⁻¹ * w * g) h1
      simpa [mul_assoc] using this
    have h3 : x = 1 := Subtype.ext (by simpa [hx'] using congrArg Subtype.val h2)
    rw [h3, orderOf_one] at hx
    omega
  have : Nontrivial ↥N := ⟨⟨⟨⟨g * x' * g⁻¹, hgx⟩, hzN⟩, 1, hz1⟩⟩
  obtain ⟨y', hy'1, hy'c⟩ := CFSG.exists_nontrivial_center_mem_normal (G := ↥(Pu : Subgroup ↥H))
    N (p := 3)
  set y : X := (((y' : ↥(Pu : Subgroup ↥H)) : ↥H) : X) with hy
  have hyL : y ∈ L := by
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp y'.2)
  have hy1 : y ≠ 1 := by
    intro h
    apply hy'1
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have huQ : u' ∈ (Pu : Subgroup ↥H) := hPu (Subgroup.mem_zpowers u')
  have hcomm : y * u = u * y := by
    have := Subgroup.mem_center_iff.mp hy'c ⟨u', huQ⟩
    have h2 := congrArg (fun w : ↥(Pu : Subgroup ↥H) => ((w : ↥H) : X)) this
    exact h2.symm
  obtain ⟨k, hk⟩ := Pu.isPGroup' (y' : ↥(Pu : Subgroup ↥H))
  have hyk : y ^ (3 ^ k) = 1 := by
    have h2 := congrArg (fun w : ↥(Pu : Subgroup ↥H) => ((w : ↥H) : X)) hk
    simpa [hy] using h2
  refine ⟨y, hyL, isPGroup_zpowers_of_pow_eq_one hyk, hcomm, ?_⟩
  by_contra hall
  push Not at hall
  apply hy1
  have : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hall l l.2).symm
  rw [hZ, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this


open CFSG.ComponentClassification.OuterAutomorphisms in
theorem three_dvd_card_outer_of_not_inner {L : Subgroup X} (hperf : Group.IsPerfect ↥L) {u : X}
    (hu3 : u ^ 3 = 1) (huN : u ∈ Subgroup.normalizer (L : Set X))
    (hin : ∀ a ∈ L, ∃ l ∈ L, u * l * u⁻¹ ≠ a * l * a⁻¹) :
    3 ∣ Nat.card (Outer (↥L ⧸ Subgroup.center ↥L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set α : MulAut ↥L := L.normalizerMonoidHom ⟨u, huN⟩ with hα
  have hαl : ∀ l : ↥L, ((α l : ↥L) : X) = u * l * u⁻¹ := fun l => rfl
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨u, huN⟩ : ↥(Subgroup.normalizer (L : Set X))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hu3)
    rw [this, map_one]
  set ā : Outer ↥L := QuotientGroup.mk' (inner ↥L) α with hā
  have hā3 : ā ^ 3 = 1 := by rw [hā, ← map_pow, hα3, map_one]
  have hā1 : ā ≠ 1 := by
    intro h
    rw [hā, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨a, ha⟩ := h
    obtain ⟨l, hl, hne⟩ := hin a a.2
    apply hne
    have := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : X)) ha
    simpa [hαl] using this.symm
  have := hperf
  set g : Outer (↥L ⧸ Subgroup.center ↥L) := centerQuotientOuterHom ↥L ā with hg
  have hg3 : g ^ 3 = 1 := by rw [hg, ← map_pow, hā3, map_one]
  have hg1 : g ≠ 1 := by
    intro h
    exact hā1 (centerQuotient_outer_injective ↥L (h.trans (map_one _).symm))
  rw [← orderOf_eq_prime hg3 hg1]
  exact orderOf_dvd_natCard g

end CFSG.AGLEmbedding.FixedThree
