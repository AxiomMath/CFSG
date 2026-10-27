module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Fixed

theorem exists_mul_central_fixed {Λ : Type*} [Group Λ] (a : Λ →* Λ) (ha : ∀ x, a (a x) = x)
    (hodd : Odd (Nat.card (Subgroup.center Λ))) {x : Λ} (hx : x⁻¹ * a x ∈ Subgroup.center Λ) :
    ∃ c ∈ Subgroup.center Λ, a (x * c) = x * c := by
  set c0 : Λ := x⁻¹ * a x with hc0
  have hc0Z : c0 ∈ Subgroup.center Λ := hx
  have hac0 : a c0 = c0⁻¹ := by
    rw [hc0, map_mul, map_inv, ha]
    group
  have hord : Odd (orderOf c0) := by
    have hdvd : orderOf (⟨c0, hc0Z⟩ : Subgroup.center Λ) ∣ Nat.card (Subgroup.center Λ) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  obtain ⟨j, hj⟩ := hord
  refine ⟨c0 ^ (j + 1), Subgroup.pow_mem _ hc0Z _, ?_⟩
  have h1 : a x = x * c0 := by
    rw [hc0]
    group
  have hpow : c0 ^ (j + 1) * c0 ^ (j + 1) = c0 := by
    rw [← pow_add, show j + 1 + (j + 1) = orderOf c0 + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [map_mul, h1, map_pow, hac0, inv_pow, mul_inv_eq_iff_eq_mul, mul_assoc, hpow]

end Fixed

section Central

variable {G : Type*} [Group G]

theorem eq_one_of_mem_center_of_charTwo {L X : Subgroup G} (hXL : X ≤ L) (hX : CharTwo X)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {x : G} (hxX : x ∈ X)
    (hxZ : ∀ y ∈ L, x * y = y * x) : x = 1 := by
  have hxQ : x ∈ pCoreOf 2 X := by
    refine hX ⟨hxX, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact (hxZ y (hXL (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X hy))).symm
  obtain ⟨k, hk⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X ⟨x, hxQ⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hxL : x ∈ L := hXL hxX
  have hZmem : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hxZ g g.2).symm
  have hdvd : orderOf (⟨⟨x, hxL⟩, hZmem⟩ : Subgroup.center ↥L) ∣ Nat.card (Subgroup.center ↥L) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at hdvd
  have hodd' : Odd (orderOf x) := Odd.of_dvd_nat hodd hdvd
  have hdvd2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi] at hodd'
    exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  exact hi

theorem commutator_mul_central {Λ : Type*} [Group Λ] {a b c d : Λ} (hc : c ∈ Subgroup.center Λ)
    (hd : d ∈ Subgroup.center Λ) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  rw [Subgroup.mem_center_iff] at hc hd
  have hc' : ∀ g, c * g * c⁻¹ = g := fun g => by rw [mul_inv_eq_iff_eq_mul]; exact (hc g).symm
  have hd' : ∀ g, d * g * d⁻¹ = g := fun g => by rw [mul_inv_eq_iff_eq_mul]; exact (hd g).symm
  have e1 : ∀ y : Λ, ⁅a * c, y⁆ = ⁅a, y⁆ := by
    intro y
    simp only [commutatorElement_def, mul_inv_rev]
    calc a * c * y * (c⁻¹ * a⁻¹) * y⁻¹ = a * (c * y * c⁻¹) * a⁻¹ * y⁻¹ := by group
      _ = a * y * a⁻¹ * y⁻¹ := by rw [hc']
  have e2 : ⁅a, b * d⁆ = ⁅a, b⁆ := by
    simp only [commutatorElement_def, mul_inv_rev]
    calc a * (b * d) * a⁻¹ * (d⁻¹ * b⁻¹) = a * b * (d * a⁻¹ * d⁻¹) * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [hd']
  rw [e1, e2]

end Central

section Perm

theorem sq_eq_one_of_cycleType_seven {σ : Equiv.Perm (Fin 7)} (h : σ.cycleType = {2, 2, 2}) :
    σ ^ 2 = 1 := by
  have h1 : orderOf σ = 2 := by
    rw [← Equiv.Perm.lcm_cycleType, h]
    decide
  rw [← h1]
  exact pow_orderOf_eq_one σ

theorem card_fixedPoints_of_cycleType_seven {σ : Equiv.Perm (Fin 7)} (h : σ.cycleType = {2, 2, 2}) :
    Nat.card {i : Fin 7 // σ i = i} = 1 := by
  have h1 := Equiv.Perm.card_fixedPoints σ
  rw [h] at h1
  have h2 : Nat.card {i : Fin 7 // σ i = i} = Nat.card (Function.fixedPoints σ) := rfl
  rw [h2, Nat.card_eq_fintype_card, h1]
  simp

end Perm

section Main

variable {G : Type} [Group G]

theorem isPartitionStabilizerImage_of_a7 (ha7 : L239A7Overgroups) {L M : Subgroup G} {z : G}
    (hq : CFSG.IsQuasisimple ↥L) (φ : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7))
    (σ : Equiv.Perm (Fin 7)) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hσ : σ.cycleType = {2, 2, 2}) (hact : Ch1.InducesPermAction z L φ σ) (hz2 : z ^ 2 = 1)
    (hLM : ¬ L ≤ M) (hCz : Subgroup.centralizer ({z} : Set G) ≤ M) (hML : CharTwo (L ⊓ M)) :
    IsPartitionStabilizerImage L (L ⊓ M) := by
  classical
  have hLq : Group.IsPerfect ↥L := hq.1
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZ
  let π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z
  let f : ↥L →* alternatingGroup (Fin 7) := φ.toMonoidHom.comp π
  have hfsurj : Function.Surjective f := φ.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : ∀ x : ↥L, f x = 1 ↔ x ∈ Z := by
    intro x
    constructor
    · intro h
      have h1 : (QuotientGroup.mk x : ↥L ⧸ Z) = 1 := by
        apply φ.injective
        rw [map_one]
        exact h
      exact (QuotientGroup.eq_one_iff x).mp h1
    · intro h
      show φ (QuotientGroup.mk x) = 1
      rw [(QuotientGroup.eq_one_iff x).mpr h, map_one]
  set ML : Subgroup G := L ⊓ M with hMLdef
  let i : ↥ML →* ↥L := Subgroup.inclusion (inf_le_left : ML ≤ L)
  let g : ↥ML →* alternatingGroup (Fin 7) := f.comp i
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have hmZ : i m ∈ Z := (hker (i m)).mp hm
    have hcomm : ∀ y ∈ L, (m : G) * y = y * (m : G) := by
      intro y hy
      have := Subgroup.mem_center_iff.mp hmZ ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    exact Subtype.ext (eq_one_of_mem_center_of_charTwo inf_le_left hML hodd m.2 hcomm)
  let α : ↥L →* ↥L :=
    { toFun := fun y => ⟨z⁻¹ * (y : G) * z, hact.1 y y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro y y'
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hα : ∀ y : ↥L, ((α y : ↥L) : G) = z⁻¹ * (y : G) * z := fun _ => rfl
  have hαα : ∀ y : ↥L, α (α y) = y := by
    intro y
    apply Subtype.ext
    rw [hα, hα]
    have hzz : z⁻¹ * z⁻¹ = 1 := by
      rw [← mul_inv_rev, ← sq, hz2, inv_one]
    calc z⁻¹ * (z⁻¹ * (y : G) * z) * z = (z⁻¹ * z⁻¹) * (y : G) * (z * z) := by group
      _ = (y : G) := by
        rw [hzz, show z * z = 1 by rw [← sq, hz2]]
        group
  set C : Subgroup (alternatingGroup (Fin 7)) :=
    (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 7)))).comap
      (alternatingGroup (Fin 7)).subtype with hCdef
  have hCY : C ≤ g.range := by
    intro a ha
    have ha' : (a : Equiv.Perm (Fin 7)) ∈ Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 7))) := ha
    have haσ : (a : Equiv.Perm (Fin 7)) * σ = σ * (a : Equiv.Perm (Fin 7)) :=
      Subgroup.mem_centralizer_singleton_iff.mp ha'
    obtain ⟨x, hx⟩ := hfsurj a
    have hfα : f (α x) = f x := by
      have h1 := hact.2 x (α x) (hα x)
      have h2 : ((φ (QuotientGroup.mk x) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
          (a : Equiv.Perm (Fin 7)) := by
        have : φ (QuotientGroup.mk x) = a := hx
        rw [this]
      rw [h2] at h1
      have h3 : σ⁻¹ * (a : Equiv.Perm (Fin 7)) * σ = (a : Equiv.Perm (Fin 7)) := by
        calc σ⁻¹ * (a : Equiv.Perm (Fin 7)) * σ = σ⁻¹ * ((a : Equiv.Perm (Fin 7)) * σ) := by group
          _ = σ⁻¹ * (σ * (a : Equiv.Perm (Fin 7))) := by rw [haσ]
          _ = (a : Equiv.Perm (Fin 7)) := by group
      rw [h3] at h1
      exact Subtype.ext (h1.trans h2.symm)
    have hst : x⁻¹ * α x ∈ Z := by
      rw [← hker, map_mul, map_inv, hfα, inv_mul_cancel]
    obtain ⟨c, hcZ, hfix⟩ := exists_mul_central_fixed α hαα hodd hst
    have hxc : ((x * c : ↥L) : G) ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val hfix
      rw [hα] at h1
      have h2 : z⁻¹ * ((x * c : ↥L) : G) * z = ((x * c : ↥L) : G) := h1
      calc ((x * c : ↥L) : G) * z = z * (z⁻¹ * ((x * c : ↥L) : G) * z) := by group
        _ = z * ((x * c : ↥L) : G) := by rw [h2]
    have hxcM : ((x * c : ↥L) : G) ∈ ML := ⟨(x * c).2, hCz hxc⟩
    refine ⟨⟨((x * c : ↥L) : G), hxcM⟩, ?_⟩
    show f (i ⟨((x * c : ↥L) : G), hxcM⟩) = a
    have hi : i ⟨((x * c : ↥L) : G), hxcM⟩ = x * c := rfl
    rw [hi, map_mul, hx, (hker c).mpr hcZ, mul_one]
  have hYtop : g.range ≠ ⊤ := by
    intro htop
    apply hLM
    have key : ∀ l : ↥L, ∃ m : ↥ML, ∃ c ∈ Z, l = i m * c := by
      intro l
      have hl : f l ∈ g.range := htop ▸ Subgroup.mem_top _
      obtain ⟨m, hm⟩ := hl
      refine ⟨m, (i m)⁻¹ * l, ?_, by group⟩
      rw [← hker, map_mul, map_inv]
      have hm' : f (i m) = f l := hm
      rw [hm', inv_mul_cancel]
    have hcomm : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ≤ ML.subgroupOf L := by
      rw [Subgroup.commutator_le]
      intro l₁ _ l₂ _
      obtain ⟨m₁, c₁, hc₁, h₁⟩ := key l₁
      obtain ⟨m₂, c₂, hc₂, h₂⟩ := key l₂
      rw [h₁, h₂, commutator_mul_central hc₁ hc₂, Subgroup.mem_subgroupOf]
      have : ⁅i m₁, i m₂⁆ = i ⁅m₁, m₂⁆ := (map_commutatorElement i m₁ m₂).symm
      rw [this]
      exact (⁅m₁, m₂⁆ : ↥ML).2
    have htopL : (⊤ : Subgroup ↥L) ≤ ML.subgroupOf L := by
      have h := hLq.commutator_eq_top
      rw [_root_.commutator_def] at h
      rw [← h]
      exact hcomm
    intro x hx
    have := htopL (Subgroup.mem_top ⟨x, hx⟩)
    exact (Subgroup.mem_subgroupOf.mp this).2
  have hYchar : CharTwo g.range :=
    charTwo_iff_internal.mpr
      (CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
        (MonoidHom.ofInjective hginj) (charTwo_iff_internal.mp hML))
  have hY : ((ML.subgroupOf L).map π).map φ.toMonoidHom = g.range := by
    ext a
    constructor
    · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    · rintro ⟨m, rfl⟩
      exact ⟨π (i m), ⟨i m, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩, rfl⟩
  exact ⟨φ, σ, sq_eq_one_of_cycleType_seven hσ, card_fixedPoints_of_cycleType_seven hσ,
    hY.trans (ha7 σ hσ g.range hCY hYtop hYchar)⟩

end Main

end CFSG.QuasithinUnique.Vol2Native.L239
