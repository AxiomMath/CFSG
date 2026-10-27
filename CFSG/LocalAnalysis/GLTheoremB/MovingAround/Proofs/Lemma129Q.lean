module

public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129Q

open CFSG.Open

private theorem exists_endo_zpowers {A : Type*} [Group A] [IsMulCommutative A]
    (hA : Nat.card A = 9) (h3 : ∀ a : A, a ^ 3 = 1) {y : A} (hy : y ≠ 1) :
    ∃ θ : A →* A, (∀ a, θ a ∈ Subgroup.zpowers y) ∧ θ y = 1 ∧ ∃ a, θ a ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf y = 3 := orderOf_eq_prime (h3 y) hy
  have hN : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hord]
  have hQ : Nat.card (A ⧸ Subgroup.zpowers y) = 3 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers y)
    rw [hA, hN] at this
    omega
  haveI : IsCyclic (A ⧸ Subgroup.zpowers y) := isCyclic_of_prime_card hQ
  haveI : IsCyclic (Subgroup.zpowers y) := isCyclic_of_prime_card hN
  let ψ : (A ⧸ Subgroup.zpowers y) ≃* Subgroup.zpowers y :=
    mulEquivOfCyclicCardEq (hQ.trans hN.symm)
  refine ⟨(Subgroup.zpowers y).subtype.comp (ψ.toMonoidHom.comp (QuotientGroup.mk' _)),
    fun a => (ψ (QuotientGroup.mk a)).2, ?_, ?_⟩
  · have : (QuotientGroup.mk y : A ⧸ Subgroup.zpowers y) = 1 :=
      (QuotientGroup.eq_one_iff y).2 (Subgroup.mem_zpowers y)
    simp [this]
  · haveI : Finite (A ⧸ Subgroup.zpowers y) := Nat.finite_of_card_ne_zero (by omega)
    haveI : Nontrivial (A ⧸ Subgroup.zpowers y) :=
      Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨q, hq⟩ := exists_ne (1 : A ⧸ Subgroup.zpowers y)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨a, fun h => hq ?_⟩
    have h1 : ψ (QuotientGroup.mk a) = 1 := Subtype.ext h
    simpa using h1

private theorem exists_shear {A : Type*} [Group A] (θ : A →* A)
    (hθ : ∀ a, θ (θ a) = 1) (h3 : ∀ a : A, a ^ 3 = 1) :
    ∃ m : Equiv.Perm A, (∀ a, m a = a * (θ a)⁻¹) ∧ m ^ 3 = 1 := by
  let m : Equiv.Perm A :=
    { toFun := fun a => a * (θ a)⁻¹
      invFun := fun a => a * θ a
      left_inv := fun a => by simp [map_mul, map_inv, hθ]
      right_inv := fun a => by simp [map_mul, map_inv, hθ] }
  have hm : ∀ a, m a = a * (θ a)⁻¹ := fun _ => rfl
  have hθm : ∀ a, θ (m a) = θ a := fun a => by simp [hm, hθ]
  refine ⟨m, hm, ?_⟩
  refine Equiv.ext fun a => ?_
  have h1 : (m ^ 3) a = m (m (m a)) := by simp [pow_succ]
  have e2 : m (m a) = a * (θ a)⁻¹ * (θ a)⁻¹ := by rw [hm (m a), hθm a, hm a]
  have e3 : m (m (m a)) = a * (θ a)⁻¹ * (θ a)⁻¹ * (θ a)⁻¹ := by
    rw [hm (m (m a)), hθm (m a), hθm a, e2]
  rw [h1, e3]
  have h4 := h3 (θ a)
  show _ = a
  calc a * (θ a)⁻¹ * (θ a)⁻¹ * (θ a)⁻¹ = a * ((θ a) ^ 3)⁻¹ := by group
    _ = a := by rw [h4]; simp

private theorem comm_of_fix_of_supp {Ω₀ : Set (Fin 13)} {a b : Equiv.Perm (Fin 13)}
    (ha : ∀ j ∈ Ω₀, a j = j) (hb : ∀ j, j ∉ Ω₀ → b j = j) : a * b = b * a := by
  refine Equiv.ext fun p => ?_
  by_cases hp : p ∈ Ω₀
  · have hbp : b p ∈ Ω₀ := by
      by_contra h
      have hbpp : b p = p := b.injective (hb _ h)
      apply h
      rw [hbpp]
      exact hp
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha _ hp, ha _ hbp]
  · have hap : a p ∉ Ω₀ := by
      intro h
      have happ : a p = p := a.injective (ha _ h)
      exact hp (happ ▸ h)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hb _ hp, hb _ hap]

private theorem exists_extend {Ω₀ : Set (Fin 13)} {F' : Subgroup (Equiv.Perm (Fin 13))}
    (hFfix : ∀ g ∈ F', ∀ j ∈ Ω₀, g j = j)
    (htrans : ∀ j k : Fin 13, j ∉ Ω₀ → k ∉ Ω₀ → ∃! g : Equiv.Perm (Fin 13), g ∈ F' ∧ g j = k)
    {j₀ : Fin 13} (hj₀ : j₀ ∉ Ω₀) (m : Equiv.Perm F') :
    ∃ x : Equiv.Perm (Fin 13), (∀ p ∈ Ω₀, x p = p) ∧
      (∀ h : F', x ((h : Equiv.Perm (Fin 13)) j₀) = ((m h : F') : Equiv.Perm (Fin 13)) j₀) ∧
      (∀ n : ℕ, m ^ n = 1 → x ^ n = 1) ∧ (m ≠ 1 → x ≠ 1) := by
  classical
  have hpres : ∀ g ∈ F', ∀ j, j ∉ Ω₀ → g j ∉ Ω₀ := fun g hg j hj hgj =>
    hj (g.injective (hFfix g hg _ hgj) ▸ hgj)
  have hbij : Function.Bijective (fun h : F' =>
      (⟨(h : Equiv.Perm (Fin 13)) j₀, hpres h h.2 j₀ hj₀⟩ : {p : Fin 13 // p ∉ Ω₀})) := by
    constructor
    · intro h h' hhh
      have h1 : (h : Equiv.Perm (Fin 13)) j₀ = (h' : Equiv.Perm (Fin 13)) j₀ :=
        congrArg Subtype.val hhh
      obtain ⟨_, _, hu⟩ :=
        htrans j₀ ((h : Equiv.Perm (Fin 13)) j₀) hj₀ (hpres h h.2 j₀ hj₀)
      exact Subtype.ext ((hu h ⟨h.2, rfl⟩).trans (hu h' ⟨h'.2, h1.symm⟩).symm)
    · rintro ⟨p, hp⟩
      obtain ⟨g, ⟨hgF, hgp⟩, _⟩ := htrans j₀ p hj₀ hp
      exact ⟨⟨g, hgF⟩, Subtype.ext hgp⟩
  obtain ⟨e, he⟩ : ∃ e : F' ≃ {p : Fin 13 // p ∉ Ω₀},
      ∀ h : F', (e h : Fin 13) = (h : Equiv.Perm (Fin 13)) j₀ :=
    ⟨Equiv.ofBijective _ hbij, fun _ => rfl⟩
  refine ⟨m.extendDomain e, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact Equiv.Perm.extendDomain_apply_not_subtype m e (not_not.2 hp)
  · intro h
    have := Equiv.Perm.extendDomain_apply_image m e h
    rw [he, he] at this
    exact this
  · intro n hn
    rw [← Equiv.Perm.extendDomain_pow, hn, Equiv.Perm.extendDomain_one]
  · intro hm hx
    exact hm (Equiv.Perm.extendDomain_eq_one_iff.1 hx)

private theorem sup_zpowers_commutator_mem {G : Type*} [Group G] (x y a : G) {H : Subgroup G}
    (hH : ∀ g ∈ H, g * y = y * g ∧ x * g * x⁻¹ * g⁻¹ ∈ Subgroup.zpowers y)
    (ha : a * y = y * a ∧ x * a * x⁻¹ * a⁻¹ ∈ Subgroup.zpowers y) :
    ∀ g ∈ H ⊔ Subgroup.zpowers a, x * g * x⁻¹ * g⁻¹ ∈ Subgroup.zpowers y := by
  have hcomm : ∀ g : G, g * y = y * g → ∀ B ∈ Subgroup.zpowers y, g * B = B * g := by
    intro g hg B hB
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hB
    exact (Commute.zpow_right (show Commute g y from hg) k).eq
  let S : Subgroup G :=
    { carrier := {g | g * y = y * g ∧ x * g * x⁻¹ * g⁻¹ ∈ Subgroup.zpowers y}
      mul_mem' := by
        rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
        refine ⟨by rw [mul_assoc, hh1, ← mul_assoc, hg1, mul_assoc], ?_⟩
        have hB : g * (x * h * x⁻¹ * h⁻¹) * g⁻¹ = x * h * x⁻¹ * h⁻¹ := by
          rw [hcomm g hg1 _ hh2, mul_inv_cancel_right]
        have key : x * (g * h) * x⁻¹ * (g * h)⁻¹ =
            (x * g * x⁻¹ * g⁻¹) * (x * h * x⁻¹ * h⁻¹) := by
          calc x * (g * h) * x⁻¹ * (g * h)⁻¹
              = (x * g * x⁻¹ * g⁻¹) * (g * (x * h * x⁻¹ * h⁻¹) * g⁻¹) := by group
            _ = (x * g * x⁻¹ * g⁻¹) * (x * h * x⁻¹ * h⁻¹) := by rw [hB]
        rw [key]
        exact mul_mem hg2 hh2
      one_mem' := ⟨by rw [one_mul, mul_one], by simp⟩
      inv_mem' := by
        rintro g ⟨hg1, hg2⟩
        refine ⟨(show Commute g y from hg1).inv_left.eq, ?_⟩
        have hC : (x * g * x⁻¹ * g⁻¹)⁻¹ ∈ Subgroup.zpowers y := inv_mem hg2
        have key : x * g⁻¹ * x⁻¹ * g⁻¹⁻¹ = (x * g * x⁻¹ * g⁻¹)⁻¹ := by
          calc x * g⁻¹ * x⁻¹ * g⁻¹⁻¹
              = g⁻¹ * (x * g * x⁻¹ * g⁻¹)⁻¹ * g := by group
            _ = (x * g * x⁻¹ * g⁻¹)⁻¹ := by
              rw [mul_assoc, ← hcomm g hg1 _ hC, inv_mul_cancel_left]
        rw [key]
        exact hC }
  have hHS : H ≤ S := fun g hg => hH g hg
  have haS : Subgroup.zpowers a ≤ S := Subgroup.zpowers_le.2 ha
  intro g hg
  exact (sup_le hHS haS hg).2

open scoped IsMulCommutative in
private theorem shear_mul {A : Type*} [Group A] [IsMulCommutative A] (θ : A →* A) (g h : A) :
    (g * h) * (θ (g * h))⁻¹ = (θ g)⁻¹ * (g * (h * (θ h)⁻¹)) := by
  rw [map_mul, mul_inv_rev]
  simp only [mul_comm, mul_left_comm, mul_assoc]

theorem permB (Ω₀ : Set (Fin 13)) (hΩ₀ : Ω₀.ncard = 4)
    (F' : Subgroup (Equiv.Perm (Fin 13))) (hFel : IsElemAbelian 3 F') (hFcard : Nat.card F' = 9)
    (hFfix : ∀ g ∈ F', ∀ j ∈ Ω₀, g j = j)
    (htrans : ∀ j k : Fin 13, j ∉ Ω₀ → k ∉ Ω₀ → ∃! g : Equiv.Perm (Fin 13), g ∈ F' ∧ g j = k)
    {y : Equiv.Perm (Fin 13)} (hy : y ∈ F') (hy1 : y ≠ 1)
    {σ : Equiv.Perm (Fin 13)} (hσ : σ.IsThreeCycle) (hσsupp : ∀ j, j ∉ Ω₀ → σ j = j) :
    ∃ x : Equiv.Perm (Fin 13), x ∈ alternatingGroup (Fin 13) ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧
      (∀ j ∈ Ω₀, x j = j) ∧
      (∀ g ∈ F' ⊔ Subgroup.zpowers σ, x * g * x⁻¹ * g⁻¹ ∈ Subgroup.zpowers y) ∧
      ∃ c c' : Fin 13, c ∉ Ω₀ ∧ c' ∉ Ω₀ ∧ c ≠ c' ∧ x c = c ∧ x c' = c' := by
  classical
  haveI : IsMulCommutative F' := hFel.1
  have hpres : ∀ g ∈ F', ∀ j, j ∉ Ω₀ → g j ∉ Ω₀ := fun g hg j hj hgj =>
    hj (g.injective (hFfix g hg _ hgj) ▸ hgj)
  have hfree : ∀ g ∈ F', ∀ j, j ∉ Ω₀ → g j = j → g = 1 := by
    intro g hg j hj hgj
    obtain ⟨_, _, huniq⟩ := htrans j j hj hj
    exact (huniq g ⟨hg, hgj⟩).trans (huniq 1 ⟨F'.one_mem, rfl⟩).symm
  obtain ⟨j₀, hj₀⟩ : ∃ j, j ∉ Ω₀ := by
    by_contra h
    push Not at h
    exact hy1 (Equiv.ext fun p => hFfix y hy p (h p))
  have hyj₀ : y j₀ ≠ j₀ := fun h => hy1 (hfree y hy j₀ hj₀ h)
  have hyj₀Ω : y j₀ ∉ Ω₀ := hpres y hy j₀ hj₀
  have h3 : ∀ a : F', a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hFel.2 a a.2)
  let y' : F' := ⟨y, hy⟩
  have hy'1 : y' ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  obtain ⟨θ, hθmem, hθy, a₀, ha₀⟩ := exists_endo_zpowers hFcard h3 hy'1
  have hθmem' : ∀ a : F', ((θ a : F') : Equiv.Perm (Fin 13)) ∈ Subgroup.zpowers y := by
    intro a
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hθmem a)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← hk]; exact (Subgroup.coe_zpow F' y' k).symm⟩
  have hθθ : ∀ a, θ (θ a) = 1 := by
    intro a
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hθmem a)
    rw [← hk, map_zpow, hθy, one_zpow]
  obtain ⟨m, hm, hm3⟩ := exists_shear θ hθθ h3
  obtain ⟨x, hxΩ, hxh, hxpow, hxne⟩ := exists_extend hFfix htrans hj₀ m
  have hx3 : x ^ 3 = 1 := hxpow 3 hm3
  have hxg : ∀ g : F', x * (g : Equiv.Perm (Fin 13)) =
      (((θ g)⁻¹ : F') : Equiv.Perm (Fin 13)) * (g : Equiv.Perm (Fin 13)) * x := by
    intro g
    refine Equiv.ext fun p => ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    by_cases hp : p ∈ Ω₀
    · have hz : (((θ g)⁻¹ : F') : Equiv.Perm (Fin 13)) p = p := hFfix _ ((θ g)⁻¹).2 p hp
      rw [hFfix g g.2 p hp, hxΩ p hp, hFfix g g.2 p hp, hz]
    · obtain ⟨h, hh⟩ : ∃ h : F', (h : Equiv.Perm (Fin 13)) j₀ = p := by
        obtain ⟨g', ⟨hgF, hgp⟩, _⟩ := htrans j₀ p hj₀ hp
        exact ⟨⟨g', hgF⟩, hgp⟩
      subst hh
      have e1 : (g : Equiv.Perm (Fin 13)) ((h : Equiv.Perm (Fin 13)) j₀) =
          ((g * h : F') : Equiv.Perm (Fin 13)) j₀ := rfl
      have e2 : (((θ g)⁻¹ : F') : Equiv.Perm (Fin 13))
          ((g : Equiv.Perm (Fin 13)) ((((m h : F')) : Equiv.Perm (Fin 13)) j₀)) =
          ((((θ g)⁻¹ * (g * m h) : F')) : Equiv.Perm (Fin 13)) j₀ := rfl
      rw [hxh h, e1, hxh (g * h), e2]
      have hFeq : m (g * h) = (θ g)⁻¹ * (g * m h) := by
        rw [hm, hm]
        exact shear_mul θ g h
      rw [hFeq]
  have hFcomm : ∀ g ∈ F', x * g * x⁻¹ * g⁻¹ ∈ Subgroup.zpowers y := by
    intro g hg
    have h1 : x * g = (((θ ⟨g, hg⟩)⁻¹ : F') : Equiv.Perm (Fin 13)) * g * x := hxg ⟨g, hg⟩
    have hz : (((θ ⟨g, hg⟩)⁻¹ : F') : Equiv.Perm (Fin 13)) ∈ Subgroup.zpowers y :=
      inv_mem (hθmem' ⟨g, hg⟩)
    have h2 : x * g * x⁻¹ * g⁻¹ = (((θ ⟨g, hg⟩)⁻¹ : F') : Equiv.Perm (Fin 13)) := by
      rw [h1]
      group
    rw [h2]
    exact hz
  have hm1 : m ≠ 1 := by
    intro h
    apply ha₀
    have h2 := hm a₀
    rw [h] at h2
    have h2' : a₀ = a₀ * (θ a₀)⁻¹ := h2
    simpa using h2'.symm
  have hσy : σ * y = y * σ := (comm_of_fix_of_supp (hFfix y hy) hσsupp).symm
  have hσx : x * σ = σ * x := comm_of_fix_of_supp hxΩ hσsupp
  refine ⟨x, ?_, hxne hm1, hx3, hxΩ, ?_, j₀, y j₀, hj₀, hyj₀Ω, hyj₀.symm, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    have h := congrArg Equiv.Perm.sign hx3
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by decide)
  · refine sup_zpowers_commutator_mem x y σ (H := F')
      (fun g hg => ⟨hFel.comm hg hy, hFcomm g hg⟩) ⟨hσy, ?_⟩
    have h1 : x * σ * x⁻¹ * σ⁻¹ = 1 := by
      rw [hσx]
      group
    rw [h1]
    exact one_mem _
  · simpa [hm] using hxh 1
  · simpa [hm, hθy, y'] using hxh y'

theorem permC (Ω₀ : Set (Fin 13)) (F' : Subgroup (Equiv.Perm (Fin 13))) (hFel : IsElemAbelian 3 F')
    (hFcard : Nat.card F' = 9) (hFfix : ∀ g ∈ F', ∀ j ∈ Ω₀, g j = j)
    (htrans : ∀ j k : Fin 13, j ∉ Ω₀ → k ∉ Ω₀ → ∃! g : Equiv.Perm (Fin 13), g ∈ F' ∧ g j = k)
    {ρ : Equiv.Perm (Fin 13)} (hρ : ∃ k : ℕ, ρ ^ (2 ^ k) = 1) (hcomm : ∀ g ∈ F', ρ * g = g * ρ) :
    ∀ j, j ∉ Ω₀ → ρ j = j := by
  obtain ⟨k, hk⟩ := hρ
  have hfree : ∀ g ∈ F', ∀ j, j ∉ Ω₀ → g j = j → g = 1 := by
    intro g hg j hj hgj
    obtain ⟨_, _, huniq⟩ := htrans j j hj hj
    exact (huniq g ⟨hg, hgj⟩).trans (huniq 1 ⟨F'.one_mem, rfl⟩).symm
  have hpres : ∀ g ∈ F', ∀ j, j ∉ Ω₀ → g j ∉ Ω₀ := by
    intro g hg j hj hgj
    exact hj (g.injective (hFfix g hg _ hgj) ▸ hgj)
  obtain ⟨g₁, hg₁F, hg₁1⟩ : ∃ g ∈ F', g ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card F' = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩, ⟨1⟩⟩
    omega
  obtain ⟨j₁, hj₁⟩ : ∃ j, g₁ j ≠ j := by
    by_contra h
    push Not at h
    exact hg₁1 (Equiv.ext h)
  have hj₁Ω : j₁ ∉ Ω₀ := fun h => hj₁ (hFfix g₁ hg₁F j₁ h)
  have hmoved : ∀ j, j ∉ Ω₀ → g₁ j ≠ j := fun j hj hgj => hg₁1 (hfree g₁ hg₁F j hj hgj)
  have hρpres : ∀ j, j ∉ Ω₀ → ρ j ∉ Ω₀ := by
    intro j hj hρj
    apply hmoved j hj
    apply ρ.injective
    have h1 : ρ (g₁ j) = g₁ (ρ j) := congrArg (fun f => f j) (hcomm g₁ hg₁F)
    rw [h1, hFfix g₁ hg₁F _ hρj]
  obtain ⟨g₀, ⟨hg₀F, hg₀j⟩, _⟩ := htrans j₁ (ρ j₁) hj₁Ω (hρpres j₁ hj₁Ω)
  have hρg₀ : ∀ j, j ∉ Ω₀ → ρ j = g₀ j := by
    intro j hj
    obtain ⟨h, ⟨hhF, hhj⟩, _⟩ := htrans j₁ j hj₁Ω hj
    subst hhj
    have h1 : ρ (h j₁) = h (ρ j₁) := congrArg (fun f => f j₁) (hcomm h hhF)
    have h2 : (h * g₀) j₁ = (g₀ * h) j₁ := by rw [hFel.comm hhF hg₀F]
    rw [h1, ← hg₀j]
    exact h2
  have hpow : ∀ n : ℕ, ∀ j, j ∉ Ω₀ → (ρ ^ n) j = (g₀ ^ n) j := by
    intro n
    induction n with
    | zero => intro j _; simp
    | succ n ih =>
      intro j hj
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hρg₀ j hj,
        ih _ (hpres g₀ hg₀F j hj)]
  have hg₀k : g₀ ^ (2 ^ k) = 1 := by
    refine Equiv.ext fun j => ?_
    by_cases hj : j ∈ Ω₀
    · exact hFfix _ (F'.pow_mem hg₀F _) j hj
    · rw [← hpow _ j hj, hk]
  have hg₀3 : g₀ ^ 3 = 1 := hFel.2 g₀ hg₀F
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have hord : orderOf g₀ = 1 := by
    have h1 : orderOf g₀ ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hg₀k) (orderOf_dvd_of_pow_eq_one hg₀3)
    rw [hcop.gcd_eq_one] at h1
    exact Nat.dvd_one.1 h1
  have hg₀1 : g₀ = 1 := orderOf_eq_one_iff.1 hord
  intro j hj
  rw [hρg₀ j hj, hg₀1]
  rfl

theorem permD {Ω₀ : Set (Fin 13)} {ρ : Equiv.Perm (Fin 13)} (hρ : ∀ j, j ∉ Ω₀ → ρ j = j)
    {ω : Fin 13} (hω : ω ∈ Ω₀) (hρω : ρ ω ≠ ω) {c c' : Fin 13} (hc : c ∉ Ω₀) (hc' : c' ∉ Ω₀)
    (hcc' : c ≠ c') :
    ∃ ζ : Equiv.Perm (Fin 13), ζ.IsThreeCycle ∧ (∀ j, ζ j ≠ j → j = ω ∨ j = c ∨ j = c') ∧
      (ζ * ρ * ζ⁻¹ * ρ⁻¹).IsThreeCycle := by
  have hωc : ω ≠ c := fun h => hc (h ▸ hω)
  have hωc' : ω ≠ c' := fun h => hc' (h ▸ hω)
  have hρc : ρ c = c := hρ c hc
  have hρc' : ρ c' = c' := hρ c' hc'
  have ha : ρ ω ∈ Ω₀ := by
    by_contra h
    exact hρω (ρ.injective (hρ _ h))
  have hac : ρ ω ≠ c := fun h => hc (h ▸ ha)
  have hac' : ρ ω ≠ c' := fun h => hc' (h ▸ ha)
  have hconj : ρ * (Equiv.swap ω c' * Equiv.swap ω c) * ρ⁻¹ =
      Equiv.swap (ρ ω) c' * Equiv.swap (ρ ω) c := by
    have h1 := Equiv.swap_apply_apply ρ ω c
    have h2 := Equiv.swap_apply_apply ρ ω c'
    rw [hρc] at h1
    rw [hρc'] at h2
    calc ρ * (Equiv.swap ω c' * Equiv.swap ω c) * ρ⁻¹
        = (ρ * Equiv.swap ω c' * ρ⁻¹) * (ρ * Equiv.swap ω c * ρ⁻¹) := by group
      _ = _ := by rw [← h1, ← h2]
  refine ⟨Equiv.swap ω c * Equiv.swap ω c',
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hωc hωc' hcc', ?_, ?_⟩
  · intro j hj
    by_contra hne
    push Not at hne
    apply hj
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hne.1 hne.2.2,
      Equiv.swap_apply_of_ne_of_ne hne.1 hne.2.1]
  · have hinv : (Equiv.swap ω c * Equiv.swap ω c')⁻¹ = Equiv.swap ω c' * Equiv.swap ω c := by
      rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
    have hfin : Equiv.swap ω c * Equiv.swap ω c' *
        (Equiv.swap (ρ ω) c' * Equiv.swap (ρ ω) c) =
        Equiv.swap (ρ ω) c' * Equiv.swap (ρ ω) ω := by
      refine Equiv.ext fun x => ?_
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
      by_cases hx1 : x = ρ ω <;> by_cases hx2 : x = ω <;> by_cases hx3 : x = c <;>
        by_cases hx4 : x = c' <;>
        simp [hx1, hx2, hx3, hx4, hωc, hωc', hac, hac', hρω, hcc', hωc.symm, hωc'.symm, hac.symm,
          hac'.symm, hρω.symm, hcc'.symm] <;> grind
    have hcomm : (Equiv.swap ω c * Equiv.swap ω c') * ρ * (Equiv.swap ω c * Equiv.swap ω c')⁻¹ *
        ρ⁻¹ = Equiv.swap (ρ ω) c' * Equiv.swap (ρ ω) ω := by
      calc (Equiv.swap ω c * Equiv.swap ω c') * ρ * (Equiv.swap ω c * Equiv.swap ω c')⁻¹ * ρ⁻¹
          = (Equiv.swap ω c * Equiv.swap ω c') *
              (ρ * (Equiv.swap ω c * Equiv.swap ω c')⁻¹ * ρ⁻¹) := by group
        _ = _ := by rw [hinv, hconj, hfin]
    rw [hcomm]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hac' hρω hωc'.symm

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129Q

end
