module

public import CFSG.ClassicalInvolution.RouteD.TypeCBlock
public import CFSG.ClassicalInvolution.Balance.GoodDataBasic
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Klein
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Model

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Group

variable {Y : Type*} [Group Y]

theorem centralizes_of_commutator_central {M : Subgroup Y} (hM : ⁅M, M⁆ = M) {h : Y}
    (hc : ∀ m ∈ M, ⁅h, m⁆ ∈ Subgroup.center Y) : ∀ m ∈ M, h * m = m * h := by
  have hle : M ≤ Subgroup.centralizer ({h} : Set Y) := by
    rw [← hM]
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have hcx : ∀ g : Y, g * ⁅h, x⁆ = ⁅h, x⁆ * g := Subgroup.mem_center_iff.mp (hc x hx)
    have hcy : ∀ g : Y, g * ⁅h, y⁆ = ⁅h, y⁆ * g := Subgroup.mem_center_iff.mp (hc y hy)
    have hux : h * x * h⁻¹ = x * ⁅h, x⁆ := by
      rw [hcx x, commutatorElement_def]
      group
    have huy : h * y * h⁻¹ = y * ⁅h, y⁆ := by
      rw [hcy y, commutatorElement_def]
      group
    have key : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ := by
      calc h * ⁅x, y⁆ * h⁻¹ = ⁅h * x * h⁻¹, h * y * h⁻¹⁆ := by
            simp only [commutatorElement_def]
            group
        _ = ⁅x * ⁅h, x⁆, y * ⁅h, y⁆⁆ := by rw [hux, huy]
        _ = ⁅x, y⁆ := commutator_mul_of_central (H := ⊤) trivial trivial trivial
            (fun g _ => (hcx g).symm) (fun g _ => (hcy g).symm)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp key).symm
  intro m hm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hm)).symm

theorem isElemAbelian_sup_zpowers_two [Finite Y] {A : Subgroup Y} (hA : IsElemAbelian 2 A) {y : Y}
    (hy : y ∉ A) (hy2 : y * y = 1) (hyA : ∀ a ∈ A, a * y = y * a) :
    IsElemAbelian 2 (A ⊔ Subgroup.zpowers y) ∧
      Nat.card ↥(A ⊔ Subgroup.zpowers y) = Nat.card A * 2 := by
  have hy1 : y ≠ 1 := fun h => hy (h ▸ A.one_mem)
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hB : ∀ b ∈ Subgroup.zpowers y, b = 1 ∨ b = y := by
    rintro b ⟨k, rfl⟩
    show y ^ k = 1 ∨ y ^ k = y
    rw [← zpow_mod_orderOf, hord]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      have : k % ((2 : ℕ) : ℤ) = 0 := by simpa using h
      rw [this, zpow_zero]
    · right
      have : k % ((2 : ℕ) : ℤ) = 1 := by simpa using h
      rw [this, zpow_one]
  have hBsq : ∀ b ∈ Subgroup.zpowers y, b * b = 1 := by
    intro b hb
    rcases hB b hb with rfl | rfl
    · simp
    · exact hy2
  have hAB : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    rcases hB b hb with rfl | rfl
    · simp
    · exact hyA a ha
  have hBB : ∀ b ∈ Subgroup.zpowers y, ∀ b' ∈ Subgroup.zpowers y, b * b' = b' * b := by
    intro b hb b' hb'
    rcases hB b hb with rfl | rfl <;> rcases hB b' hb' with rfl | rfl <;> simp
  have hAA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hsq : ∀ x ∈ A ⊔ Subgroup.zpowers y, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.ClassicalInvolution.Balance.Bootstrap.exists_mul_eq_of_mem_sup_of_forall_commute hAB hx
    have hc : Commute a b := hAB a ha b hb
    rw [hc.mul_pow, hA.2 a ha, one_mul, pow_two]
    exact hBsq b hb
  refine ⟨⟨⟨⟨fun x x' => ?_⟩⟩, hsq⟩, ?_⟩
  · apply Subtype.ext
    obtain ⟨a, ha, b, hb, hx⟩ :=
      CFSG.ClassicalInvolution.Balance.Bootstrap.exists_mul_eq_of_mem_sup_of_forall_commute hAB x.2
    obtain ⟨a', ha', b', hb', hx'⟩ :=
      CFSG.ClassicalInvolution.Balance.Bootstrap.exists_mul_eq_of_mem_sup_of_forall_commute hAB x'.2
    show (x : Y) * x' = x' * x
    rw [hx, hx']
    have h1 : Commute a a' := hAA a ha a' ha'
    have h2 : Commute a b' := hAB a ha b' hb'
    have h3 : Commute b a' := (hAB a' ha' b hb).symm
    have h4 : Commute b b' := hBB b hb b' hb'
    exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq
  · set φ := MonoidHom.noncommCoprod A.subtype (Subgroup.zpowers y).subtype
      (fun a b => hAB a a.2 b b.2) with hφ
    have hrange : φ.range = A ⊔ Subgroup.zpowers y := by
      have := MonoidHom.noncommCoprod_range A.subtype (Subgroup.zpowers y).subtype
        (fun a b => hAB a a.2 b b.2)
      rwa [Subgroup.range_subtype, Subgroup.range_subtype] at this
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ h
      have h1 : (a : Y) * b = 1 := h
      have hb : (b : Y) = (a : Y)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hbA : (b : Y) ∈ A := hb ▸ A.inv_mem a.2
      rcases hB b b.2 with hb1 | hb1
      · have : (a : Y) = 1 := by rw [hb1, mul_one] at h1; exact h1
        exact Prod.ext (Subtype.ext this) (Subtype.ext hb1)
      · exact absurd (hb1 ▸ hbA) hy
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod,
      Nat.card_zpowers, hord]

end Group

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem bootData_of_exotic_component_of_member {Ω : Set (Subgroup G)}
    {x : G} (hP1 : LocalOddCentral Ω {x}) {N : Subgroup G} {z : G}
    (hN : N ∈ centralizingMembers Ω {x}) (hNz : IsClassicalMember p f N z)
    (D : LieSystemData p f (LocalQuot Ω x) (localFamily Ω x)) {i j : Fin D.card} (hij : i ≠ j)
    (hNj : locImg Ω x N ≤ (D.hom j).range)
    (hZ : Subgroup.center (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K = ⊥)
    (hV : ∃ V : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K,
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x * x = 1) ∧ Nat.card V = 4) :
    BootData p f Ω := by
  classical
  have hNY : N ≤ centralizingLayer Ω {x} := le_centralizingLayer hN
  have hzN : z ∈ N := hNz.mem
  set Y : Subgroup G := centralizingLayer Ω {x} with hY
  set O : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hO
  let π : ↥Y →* LocalQuot Ω x := QuotientGroup.mk' O
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  let z' : ↥Y := ⟨z, hNY hzN⟩
  have hz'ord : orderOf z' = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hNz.orderOf_eq_two
  have hz'O : z' ∉ O := by
    intro h
    have h2 : orderOf (⟨z', h⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hz'ord] at h2
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h2)
  have hπz' : π z' ≠ 1 := fun h => hz'O ((QuotientGroup.eq_one_iff z').mp h)
  set ψ := D.hom i with hψ
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact (D.ker_le_center i).trans hZ.le
  have hcenter : ∀ y ∈ ψ.range, (∀ w : LocalQuot Ω x, w * y = y * w) → y = 1 := by
    rintro _ ⟨k, rfl⟩ hy
    have hk : k ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro k'
      apply hψinj
      rw [map_mul, map_mul]
      exact hy (ψ k')
    rw [hZ] at hk
    rw [Subgroup.mem_bot.mp hk, map_one]
  have hπz'j : π z' ∈ (D.hom j).range :=
    hNj ⟨z', Subgroup.mem_subgroupOf.mpr hzN, rfl⟩
  obtain ⟨V₀, hV₀c, hV₀sq, hV₀card⟩ := hV
  set V' : Subgroup (LocalQuot Ω x) := V₀.map ψ with hV'
  have hV'card : Nat.card V' = 4 := by
    rw [hV', Subgroup.card_map_of_injective hψinj]
    exact hV₀card
  have hV'el : IsElemAbelian 2 V' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨u, hu, hua⟩ := a.2
      obtain ⟨v, hv, hvb⟩ := b.2
      apply Subtype.ext
      show (a : LocalQuot Ω x) * b = b * a
      rw [← hua, ← hvb, ← map_mul, ← map_mul, hV₀c u hu v hv]
    · obtain ⟨u, hu, rfl⟩ := ha
      rw [pow_two, ← map_mul, hV₀sq u hu, map_one]
  obtain ⟨H, hHel, hHmap, hHcard⟩ :=
    CFSG.ClassicalInvolution.Balance.GoodData.exists_isElemAbelian_lift_map O hOodd V' hV'el
  have hπH : ∀ h ∈ H, π h ∈ ψ.range := by
    intro h hh
    have h1 : π h ∈ H.map π := ⟨h, hh, rfl⟩
    rw [hHmap] at h1
    obtain ⟨u, -, hu⟩ := h1
    exact ⟨u, hu⟩
  have hHcomm : ∀ h ∈ H, ∀ m ∈ N.subgroupOf Y, ⁅h, m⁆ ∈ Subgroup.center ↥Y := by
    intro h hh m hm
    obtain ⟨u, hu⟩ := hπH h hh
    obtain ⟨v, hv⟩ := hNj ⟨m, hm, rfl⟩
    have h3 : π h * π m = π m * π h := by
      rw [← hu, ← hv]
      exact D.commute i j hij u v
    have h4 : ⁅h, m⁆ ∈ O := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      show π ⁅h, m⁆ = 1
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, h3]
      group
    exact hP1 h4
  have hN'perf : ⁅N.subgroupOf Y, N.subgroupOf Y⁆ = N.subgroupOf Y :=
    commutator_eq_of_isClassicalMember (hNz.subgroupOf p f hNY)
  have hHN : ∀ h ∈ H, ∀ m ∈ N.subgroupOf Y, h * m = m * h := fun h hh =>
    centralizes_of_commutator_central hN'perf (fun m hm => hHcomm h hh m hm)
  set H' : Subgroup G := H.map Y.subtype with hH'
  have hH'el : IsElemAbelian 2 H' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨u, hu, hua⟩ := a.2
      obtain ⟨v, hv, hvb⟩ := b.2
      apply Subtype.ext
      show (a : G) * b = b * a
      rw [← hua, ← hvb]
      have h2 : u * v = v * u := congrArg Subtype.val (hHel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
      exact congrArg Subtype.val h2
    · obtain ⟨u, hu, rfl⟩ := ha
      have h2 := hHel.2 u hu
      show (u : G) ^ 2 = 1
      rw [← Subgroup.coe_pow, h2]
      rfl
  have hH'card : Nat.card H' = 4 := by
    rw [hH', Subgroup.card_map_of_injective (Subgroup.subtype_injective Y), hHcard]
    exact hV'card
  have hzH' : z ∉ H' := by
    rintro ⟨u, hu, huz⟩
    have huz' : u = z' := Subtype.ext huz
    have hmem : π z' ∈ (D.hom i).range ⊓ (D.hom j).range := ⟨hπH z' (huz' ▸ hu), hπz'j⟩
    have hc := range_inf_le_center D hij hmem
    exact hπz' (hcenter _ (hπH z' (huz' ▸ hu)) (fun w => (Subgroup.mem_center_iff.mp hc w)))
  have hzsq : z * z = 1 := by
    have h2 : z ^ 2 = 1 := by
      rw [← hNz.orderOf_eq_two]
      exact pow_orderOf_eq_one z
    rwa [pow_two] at h2
  have hyA : ∀ y ∈ H', y * z = z * y := by
    rintro _ ⟨u, hu, rfl⟩
    exact congrArg Subtype.val (hHN u hu z' (Subgroup.mem_subgroupOf.mpr hzN))
  obtain ⟨hEel, hEcard⟩ := isElemAbelian_sup_zpowers_two hH'el hzH' hzsq (fun y hy => hyA y hy)
  refine ⟨N, z, H' ⊔ Subgroup.zpowers z, hN.1, hNz, hEel, ?_, ?_, ?_⟩
  · rw [hEcard, hH'card]
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  · intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hle : H' ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer ({m} : Set G) := by
      refine sup_le (fun y hy => ?_) ((Subgroup.zpowers_le).mpr ?_)
      · obtain ⟨u, hu, rfl⟩ := hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hHN u hu ⟨m, hNY hm⟩ (Subgroup.mem_subgroupOf.mpr hm))
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp
          (le_centralizer_of_isClassicalMember hNz hm)).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

omit [Finite G] in
theorem exotic_data (hp2 : p ≠ 2) {Ω : Set (Subgroup G)} {x : G}
    (D : LieSystemData p f (LocalQuot Ω x) (localFamily Ω x)) {i : Fin D.card}
    (ht : D.tag i = .G2 ∨ D.tag i = .trialityD4) :
    Subgroup.center (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K = ⊥ ∧
      ∃ V : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K,
        (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x * x = 1) ∧ Nat.card V = 4 :=
  ⟨RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 ht (D.rank i) (D.admissible i).2.1,
    exists_kleinFour_model hp2 ht (D.admissible i)⟩

theorem bootData_of_exotic_component_of_ne (hp2 : p ≠ 2) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (LocalQuot Ω x) (localFamily Ω x)) {i j : Fin D.card} (hij : i ≠ j)
    (ht : D.tag i = .G2 ∨ D.tag i = .trialityD4) : BootData p f Ω := by
  obtain ⟨R, -, hRΦ⟩ := D.meets j
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp hRΦ
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hLj : locImg Ω x L ≤ (D.hom j).range := hLR ▸ Subgroup.map_le_range _ _
  obtain ⟨hZ, hV⟩ := exotic_data hp2 D ht
  exact bootData_of_exotic_component_of_member hP1 hL hz D hij hLj hZ hV

theorem bootData_of_localShapeT_g2d4 (hp2 : p ≠ 2) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    {z : G} (hP1 : LocalOddCentral Ω {z}) {a : ℕ} (ha : 1 ≤ a)
    {tY : CFSG.Assembly.LowTwoRank.StatedLieTag} {nY : ℕ}
    (ht : tY = .G2 ∨ tY = .trialityD4) (h : RouteD.LocalShapeT p f a tY nY Ω z) :
    BootData p f Ω := by
  obtain ⟨D, hcard, i₁, ht₁, -, -⟩ := h
  have h1 : 1 < Fintype.card (Fin D.card) := by simp; omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card h1 i₁
  exact bootData_of_exotic_component_of_ne hp2 hΩ hP1 D (Ne.symm hj)
    (by rcases ht with h | h <;> [exact Or.inl (ht₁.trans h); exact Or.inr (ht₁.trans h)])

end Main

end CFSG.ClassicalInvolution.G2D4Models
