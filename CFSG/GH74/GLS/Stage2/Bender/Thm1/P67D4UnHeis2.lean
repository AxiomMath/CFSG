module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnCount

public section

namespace CFSG.GH74.GLS.SP

open Multiplicative

structure UnHeisSub {U : Type*} [Group U] (X₁ X₂ X₃ : Subgroup U) : Prop where
  dec : ∀ u : U, ∃! t : U × U × U,
    t.1 ∈ X₁ ∧ t.2.1 ∈ X₂ ∧ t.2.2 ∈ X₃ ∧ u = t.1 * t.2.1 * t.2.2
  norm₂ : ∀ (u : U), ∀ y ∈ X₂, u * y * u⁻¹ ∈ X₂
  comm : ∀ u v : U, u * v * u⁻¹ * v⁻¹ ∈ X₂

namespace UnHeisSub

variable {U : Type*} [Group U] {X₁ X₂ X₃ : Subgroup U}

theorem normal (F : UnHeisSub X₁ X₂ X₃) : X₂.Normal := ⟨fun n hn g => F.norm₂ g n hn⟩

theorem uniq (F : UnHeisSub X₁ X₂ X₃) {y y' b b' z z' : U} (hy : y ∈ X₁) (hy' : y' ∈ X₁)
    (hb : b ∈ X₂) (hb' : b' ∈ X₂) (hz : z ∈ X₃) (hz' : z' ∈ X₃)
    (h : y * b * z = y' * b' * z') : y = y' ∧ b = b' ∧ z = z' := by
  have := (F.dec (y * b * z)).unique (y₁ := (y, b, z)) (y₂ := (y', b', z'))
    ⟨hy, hb, hz, rfl⟩ ⟨hy', hb', hz', h⟩
  simpa using this

theorem eq_one_of_mem_inter (F : UnHeisSub X₁ X₂ X₃) {y : U} (h₁ : y ∈ X₁) (h₂ : y ∈ X₂) :
    y = 1 :=
  (F.uniq h₁ X₁.one_mem X₂.one_mem h₂ X₃.one_mem X₃.one_mem (by simp)).1

theorem quot_comm (F : UnHeisSub X₁ X₂ X₃) [X₂.Normal] (q q' : U ⧸ X₂) : q * q' = q' * q := by
  refine QuotientGroup.induction_on q fun u => ?_
  refine QuotientGroup.induction_on q' fun v => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have e : (u * v)⁻¹ * (v * u) = v⁻¹ * u⁻¹ * (v⁻¹)⁻¹ * (u⁻¹)⁻¹ := by group
  rw [e]
  exact F.comm v⁻¹ u⁻¹

theorem coset_uniq (F : UnHeisSub X₁ X₂ X₃) [X₂.Normal] {y y' z z' : U} (hy : y ∈ X₁)
    (hy' : y' ∈ X₁) (hz : z ∈ X₃) (hz' : z' ∈ X₃)
    (h : ((y * z : U) : U ⧸ X₂) = ((y' * z' : U) : U ⧸ X₂)) : y = y' ∧ z = z' := by
  rw [QuotientGroup.eq] at h
  have e : y' * 1 * z' = y * (z * ((y * z)⁻¹ * (y' * z')) * z⁻¹) * z := by group
  have := F.uniq hy' hy X₂.one_mem (F.norm₂ z _ h) hz' hz e
  exact ⟨this.1.symm, this.2.2.symm⟩

theorem coset_exists (F : UnHeisSub X₁ X₂ X₃) [X₂.Normal] (q : U ⧸ X₂) :
    ∃ y ∈ X₁, ∃ z ∈ X₃, q = ((y * z : U) : U ⧸ X₂) := by
  refine QuotientGroup.induction_on q fun u => ?_
  obtain ⟨⟨y, b, z⟩, ⟨hy, hb, hz, hu⟩, -⟩ := F.dec u
  have hy' : y ∈ X₁ := hy
  have hb' : b ∈ X₂ := hb
  have hz' : z ∈ X₃ := hz
  have hu' : u = y * b * z := hu
  refine ⟨y, hy', z, hz', ?_⟩
  rw [hu', QuotientGroup.eq]
  have e : (y * b * z)⁻¹ * (y * z) = z⁻¹ * b⁻¹ * (z⁻¹)⁻¹ := by group
  rw [e]
  exact F.norm₂ z⁻¹ b⁻¹ (X₂.inv_mem hb')

theorem mk_mul_of_mem [X₂.Normal] {b : U} (hb : b ∈ X₂) (z : U) :
    ((b * z : U) : U ⧸ X₂) = (z : U ⧸ X₂) := by
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).2 hb, one_mul]

theorem T_X₁ [X₂.Normal] (θ : U ≃* U) (T : U ⧸ X₂ →* U ⧸ X₂)
    (hT : ∀ u : U, T (u : U ⧸ X₂) = ((θ u : U) : U ⧸ X₂))
    (hθ₁ : ∀ y ∈ X₁, ∃ b ∈ X₂, ∃ z ∈ X₃, θ y = b * z) {y : U} (hy : y ∈ X₁) :
    ∃ z ∈ X₃, T (y : U ⧸ X₂) = (z : U ⧸ X₂) := by
  obtain ⟨b, hb, z, hz, h⟩ := hθ₁ y hy
  exact ⟨z, hz, by rw [hT, h, mk_mul_of_mem hb]⟩

theorem T_X₃ [X₂.Normal] (θ : U ≃* U) (T : U ⧸ X₂ →* U ⧸ X₂)
    (hT : ∀ u : U, T (u : U ⧸ X₂) = ((θ u : U) : U ⧸ X₂))
    (hθ₃ : ∀ z ∈ X₃, ∃ b ∈ X₂, ∃ y ∈ X₁, θ z = b * y) {z : U} (hz : z ∈ X₃) :
    ∃ y ∈ X₁, T (z : U ⧸ X₂) = (y : U ⧸ X₂) := by
  obtain ⟨b, hb, y, hy, h⟩ := hθ₃ z hz
  exact ⟨y, hy, by rw [hT, h, mk_mul_of_mem hb]⟩

theorem T_T_X₁ [X₂.Normal] {k : Type*} [Field k] (θ : U ≃* U) (T : U ⧸ X₂ →* U ⧸ X₂)
    (hT : ∀ u : U, T (u : U ⧸ X₂) = ((θ u : U) : U ⧸ X₂)) (x₁ : Multiplicative k →* U)
    (ε : k → k) (ν : k)
    (hθ₁₁ : ∀ a : k, ∃ b ∈ X₂, θ (θ (x₁ (ofAdd a))) = b * x₁ (ofAdd (ν * ε (ε a)))) (a : k) :
    T (T ((x₁ (ofAdd a) : U) : U ⧸ X₂)) = ((x₁ (ofAdd (ν * ε (ε a))) : U) : U ⧸ X₂) := by
  obtain ⟨b, hb, h⟩ := hθ₁₁ a
  rw [hT, hT, h, mk_mul_of_mem hb]

theorem coset_inj_X₁ (F : UnHeisSub X₁ X₂ X₃) [X₂.Normal] {k : Type*} [Field k]
    (x₁ : Multiplicative k →* U) (hx₁ : Function.Injective x₁) (hr₁ : ∀ a, x₁ a ∈ X₁) {a a' : k}
    (h : ((x₁ (ofAdd a) : U) : U ⧸ X₂) = ((x₁ (ofAdd a') : U) : U ⧸ X₂)) : a = a' := by
  have h' : ((x₁ (ofAdd a) * 1 : U) : U ⧸ X₂) = ((x₁ (ofAdd a') * 1 : U) : U ⧸ X₂) := by
    simpa using h
  have := (F.coset_uniq (hr₁ _) (hr₁ _) X₃.one_mem X₃.one_mem h').1
  exact Multiplicative.ofAdd.injective (hx₁ this)

theorem norm_cosets (F : UnHeisSub X₁ X₂ X₃) [X₂.Normal] {k : Type*} [Field k]
    (θ : U ≃* U) (T : U ⧸ X₂ →* U ⧸ X₂)
    (hT : ∀ u : U, T (u : U ⧸ X₂) = ((θ u : U) : U ⧸ X₂))
    (h4 : ∀ u : U, θ (θ (θ (θ u))) = u)
    (x₁ : Multiplicative k →* U) (hx₁ : Function.Injective x₁) (hr₁ : ∀ a, x₁ a ∈ X₁)
    (ε : k → k) (ν : k)
    (hθ₁₁ : ∀ a : k, ∃ b ∈ X₂, θ (θ (x₁ (ofAdd a))) = b * x₁ (ofAdd (ν * ε (ε a)))) (a : k) :
    ν * ε (ε (ν * ε (ε a))) = a := by
  have h4Q : T (T (T (T ((x₁ (ofAdd a) : U) : U ⧸ X₂)))) = ((x₁ (ofAdd a) : U) : U ⧸ X₂) := by
    rw [hT, hT, hT, hT, h4]
  rw [T_T_X₁ θ T hT x₁ ε ν hθ₁₁ a, T_T_X₁ θ T hT x₁ ε ν hθ₁₁ (ν * ε (ε a))] at h4Q
  exact F.coset_inj_X₁ x₁ hx₁ hr₁ h4Q

theorem card_fixed_cosets (F : UnHeisSub X₁ X₂ X₃) [X₂.Normal] {k : Type*} [Field k]
    (θ : U ≃* U) (T : U ⧸ X₂ →* U ⧸ X₂)
    (hT : ∀ u : U, T (u : U ⧸ X₂) = ((θ u : U) : U ⧸ X₂))
    (x₁ : Multiplicative k →* U) (hx₁ : Function.Injective x₁) (hr₁ : ∀ a, x₁ a ∈ X₁)
    (hs₁ : ∀ y ∈ X₁, ∃ a : k, y = x₁ (ofAdd a)) (ε : k → k) (ν : k)
    (hθ₁ : ∀ y ∈ X₁, ∃ b ∈ X₂, ∃ z ∈ X₃, θ y = b * z)
    (hθ₃ : ∀ z ∈ X₃, ∃ b ∈ X₂, ∃ y ∈ X₁, θ z = b * y)
    (hθ₁₁ : ∀ a : k, ∃ b ∈ X₂, θ (θ (x₁ (ofAdd a))) = b * x₁ (ofAdd (ν * ε (ε a)))) :
    Nat.card {q : U ⧸ X₂ // T q = q} = Nat.card {a : k // ν * ε (ε a) = a} := by
  let g : {a : k // ν * ε (ε a) = a} → {q : U ⧸ X₂ // T q = q} := fun a =>
    ⟨((x₁ (ofAdd a.1) : U) : U ⧸ X₂) * T ((x₁ (ofAdd a.1) : U) : U ⧸ X₂), by
      rw [map_mul, T_T_X₁ θ T hT x₁ ε ν hθ₁₁, a.2]
      exact F.quot_comm _ _⟩
  refine (Nat.card_eq_of_bijective g ⟨?_, ?_⟩).symm
  · intro a a' h
    obtain ⟨z, hz, hTz⟩ := T_X₁ θ T hT hθ₁ (hr₁ (ofAdd a.1))
    obtain ⟨z', hz', hTz'⟩ := T_X₁ θ T hT hθ₁ (hr₁ (ofAdd a'.1))
    have h' : ((x₁ (ofAdd a.1) : U) : U ⧸ X₂) * T ((x₁ (ofAdd a.1) : U) : U ⧸ X₂) =
        ((x₁ (ofAdd a'.1) : U) : U ⧸ X₂) * T ((x₁ (ofAdd a'.1) : U) : U ⧸ X₂) :=
      congrArg Subtype.val h
    rw [hTz, hTz', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h'
    have := (F.coset_uniq (hr₁ _) (hr₁ _) hz hz' h').1
    exact Subtype.ext (Multiplicative.ofAdd.injective (hx₁ this))
  · rintro ⟨q, hq⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := F.coset_exists q
    obtain ⟨z₁, hz₁, hTy⟩ := T_X₁ θ T hT hθ₁ hy
    obtain ⟨y₂, hy₂, hTz⟩ := T_X₃ θ T hT hθ₃ hz
    have h1 : ((y₂ * z₁ : U) : U ⧸ X₂) = ((y * z : U) : U ⧸ X₂) := by
      rw [← hq, QuotientGroup.mk_mul X₂ y z, map_mul, hTy, hTz, QuotientGroup.mk_mul X₂ y₂ z₁]
      exact F.quot_comm _ _
    obtain ⟨hyy, hzz⟩ := F.coset_uniq hy₂ hy hz₁ hz h1
    rw [hzz] at hTy
    rw [hyy] at hTz
    obtain ⟨a, rfl⟩ := hs₁ y hy
    have hfix : ν * ε (ε a) = a := by
      apply F.coset_inj_X₁ x₁ hx₁ hr₁
      rw [← T_T_X₁ θ T hT x₁ ε ν hθ₁₁ a, hTy, hTz]
    refine ⟨⟨a, hfix⟩, Subtype.ext ?_⟩
    show ((x₁ (ofAdd a) : U) : U ⧸ X₂) * T ((x₁ (ofAdd a) : U) : U ⧸ X₂) =
      ((x₁ (ofAdd a) * z : U) : U ⧸ X₂)
    rw [hTy, QuotientGroup.mk_mul]

theorem frob_sq {k : Type*} [Field k] (ε : k → k) (r R : ℕ) (hε : ∀ a, ε a = a ^ r)
    (hR : r ^ 2 = R) (a : k) : ε (ε a) = a ^ R := by
  rw [hε, hε, ← pow_mul, ← hR, sq]

theorem card_sub_of_inj {k : Type*} [Field k] (X₂ : Subgroup U) (x₂ : Multiplicative k →* U)
    (hx₂ : Function.Injective x₂) (hr₂ : ∀ a, x₂ a ∈ X₂)
    (hs₂ : ∀ y ∈ X₂, ∃ b : k, y = x₂ (ofAdd b)) : Nat.card X₂ = Nat.card k := by
  refine (Nat.card_eq_of_bijective (fun b : k => (⟨x₂ (ofAdd b), hr₂ _⟩ : X₂)) ⟨?_, ?_⟩).symm
  · intro b b' h
    exact Multiplicative.ofAdd.injective (hx₂ (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨b, rfl⟩ := hs₂ y hy
    exact ⟨b, rfl⟩

theorem norm_mid_of_inj {k : Type*} [Field k] (x₂ : Multiplicative k →* U)
    (hx₂ : Function.Injective x₂) (θ : U ≃* U) (ε : k → k) (L₂ : k)
    (hθ₂ : ∀ b : k, θ (x₂ (ofAdd b)) = x₂ (ofAdd (L₂ * ε b)))
    (h4 : ∀ u : U, θ (θ (θ (θ u))) = u) (b : k) :
    L₂ * ε (L₂ * ε (L₂ * ε (L₂ * ε b))) = b := by
  have h := h4 (x₂ (ofAdd b))
  simp only [hθ₂] at h
  exact Multiplicative.ofAdd.injective (hx₂ h)

theorem card_mid_fixed_of_inj {k : Type*} [Field k] (X₂ : Subgroup U) (x₂ : Multiplicative k →* U)
    (hx₂ : Function.Injective x₂) (hr₂ : ∀ a, x₂ a ∈ X₂)
    (hs₂ : ∀ y ∈ X₂, ∃ b : k, y = x₂ (ofAdd b)) (θ : U ≃* U) (ε : k → k) (r : ℕ)
    (hε : ∀ a, ε a = a ^ r) (L₂ : k)
    (hθ₂ : ∀ b : k, θ (x₂ (ofAdd b)) = x₂ (ofAdd (L₂ * ε b))) :
    Nat.card ↥(X₂ ⊓ foldFix θ) = Nat.card {b : k // L₂ * b ^ r = b} := by
  have hmem : ∀ b : k, L₂ * b ^ r = b → x₂ (ofAdd b) ∈ X₂ ⊓ foldFix θ := by
    intro b hb
    refine Subgroup.mem_inf.2 ⟨hr₂ _, ?_⟩
    rw [mem_foldFix, hθ₂, hε, hb]
  let g : {b : k // L₂ * b ^ r = b} → ↥(X₂ ⊓ foldFix θ) :=
    fun b => ⟨x₂ (ofAdd b.1), hmem b.1 b.2⟩
  refine (Nat.card_eq_of_bijective g ⟨?_, ?_⟩).symm
  · intro b b' h
    exact Subtype.ext (Multiplicative.ofAdd.injective (hx₂ (congrArg Subtype.val h)))
  · rintro ⟨y, hy⟩
    obtain ⟨hyV, hyF⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨b, rfl⟩ := hs₂ y hyV
    have h := mem_foldFix.1 hyF
    rw [hθ₂] at h
    have hb := Multiplicative.ofAdd.injective (hx₂ h)
    refine ⟨⟨b, ?_⟩, rfl⟩
    rw [← hε]
    exact hb

end UnHeisSub

theorem card_fixed_heis' {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 0 < f)
    {k : Type*} [Field k] [Finite k] [CharP k p] (hk : Nat.card k = (p ^ f) ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ (p ^ f))
    {U : Type*} [Group U] [Finite U] (X₁ X₂ X₃ : Subgroup U)
    (x₁ x₂ : Multiplicative k →* U) (hx₁ : Function.Injective x₁) (hx₂ : Function.Injective x₂)
    (hr₁ : ∀ a, x₁ a ∈ X₁) (hr₂ : ∀ a, x₂ a ∈ X₂)
    (hs₁ : ∀ y ∈ X₁, ∃ a : k, y = x₁ (ofAdd a)) (hs₂ : ∀ y ∈ X₂, ∃ b : k, y = x₂ (ofAdd b))
    (hdec : ∀ u : U, ∃! t : U × U × U,
      t.1 ∈ X₁ ∧ t.2.1 ∈ X₂ ∧ t.2.2 ∈ X₃ ∧ u = t.1 * t.2.1 * t.2.2)
    (hnorm₂ : ∀ (u : U), ∀ y ∈ X₂, u * y * u⁻¹ ∈ X₂)
    (hcomm : ∀ u v : U, u * v * u⁻¹ * v⁻¹ ∈ X₂)
    (θ : MulAut U) (hθ4 : θ ^ 4 = 1) (l₂ ν : kˣ)
    (hθ₂ : ∀ b : k, θ (x₂ (ofAdd b)) = x₂ (ofAdd ((l₂ : k) * ε b)))
    (hθ₁ : ∀ y ∈ X₁, ∃ b ∈ X₂, ∃ z ∈ X₃, θ y = b * z)
    (hθ₃ : ∀ z ∈ X₃, ∃ b ∈ X₂, ∃ y ∈ X₁, θ z = b * y)
    (hθ₁₁ : ∀ a : k, ∃ b ∈ X₂, θ (θ (x₁ (ofAdd a))) = b * x₁ (ofAdd ((ν : k) * ε (ε a)))) :
    Nat.card ↥(foldFix (θ : U ≃* U)) = (p ^ f) ^ 3 ∧ IsPGroup p ↥(foldFix (θ : U ≃* U)) ∧
      ∃ y ∈ X₁, y ≠ 1 ∧ ∃ b ∈ X₂, ∃ z ∈ X₃, z ≠ 1 ∧
        y * b * z ∈ foldFix (θ : U ≃* U) := by
  have F : UnHeisSub X₁ X₂ X₃ := ⟨hdec, hnorm₂, hcomm⟩
  have hVn : X₂.Normal := F.normal
  have hp : p.Prime := Fact.out
  have h4 : ∀ u : U, θ (θ (θ (θ u))) = u := by
    intro u
    have := congrArg (fun φ : MulAut U => φ u) hθ4
    simpa [pow_succ, MulAut.mul_apply] using this
  have hVθ : ∀ v ∈ X₂, θ v ∈ X₂ := by
    intro v hv
    obtain ⟨b, rfl⟩ := hs₂ v hv
    rw [hθ₂]
    exact hr₂ _
  have hVcard : Nat.card X₂ = (p ^ f) ^ 4 := by
    rw [UnHeisSub.card_sub_of_inj X₂ x₂ hx₂ hr₂ hs₂, hk]
  have hcop : ¬ 2 ∣ Nat.card X₂ := by
    rw [hVcard]
    exact ((hp.odd_of_ne_two hp2).pow.pow).not_two_dvd_nat
  have hθ4' : (θ : U ≃* U) ^ (2 ^ 2) = 1 := by
    norm_num
    exact hθ4
  have hmul := card_fixed_eq_mul (θ : U ≃* U) hθ4' X₂ hVθ hcop
  have hN₂ : (l₂ : k) ^ (1 + p ^ f + (p ^ f) ^ 2 + (p ^ f) ^ 3) = 1 := by
    have h := UnHeisSub.norm_mid_of_inj x₂ hx₂ (θ : U ≃* U) ε (l₂ : k) hθ₂ h4 1
    simp only [hε] at h
    rw [← h]
    ring
  have hVfix : Nat.card ↥(X₂ ⊓ foldFix (θ : U ≃* U)) = p ^ f := by
    rw [UnHeisSub.card_mid_fixed_of_inj X₂ x₂ hx₂ hr₂ hs₂ (θ : U ≃* U) ε (p ^ f) hε (l₂ : k) hθ₂]
    refine card_fixed_frob_twist (m := 4) (by norm_num) hf hk l₂ ?_
    apply Units.ext
    have hsum : ∑ i ∈ Finset.range 4, (p ^ f) ^ i = 1 + p ^ f + (p ^ f) ^ 2 + (p ^ f) ^ 3 := by
      simp [Finset.sum_range_succ]
    rw [hsum, Units.val_pow_eq_pow_val, Units.val_one]
    exact hN₂
  have hmap : ∀ x : U, QuotientGroup.map X₂ X₂ (θ : U ≃* U).toMonoidHom (fun v hv => hVθ v hv)
      (x : U ⧸ X₂) = (((θ : U ≃* U) x : U) : U ⧸ X₂) :=
    fun x => QuotientGroup.map_mk X₂ X₂ (θ : U ≃* U).toMonoidHom (fun v hv => hVθ v hv) x
  set T := QuotientGroup.map X₂ X₂ (θ : U ≃* U).toMonoidHom (fun v hv => hVθ v hv) with hTdef
  have hR : (p ^ f) ^ 2 = p ^ (2 * f) := (pow_mul' p 2 f).symm
  have hcosets := F.card_fixed_cosets (θ : U ≃* U) T hmap x₁ hx₁ hr₁ hs₁ ε (ν : k) hθ₁ hθ₃ hθ₁₁
  have hsol : ∀ a : k, (ν : k) * ε (ε a) = a ↔ (ν : k) * a ^ (p ^ (2 * f)) = a := by
    intro a
    rw [UnHeisSub.frob_sq ε (p ^ f) (p ^ (2 * f)) hε hR]
  have hν4 : (ν : k) ^ (1 + p ^ (2 * f)) = 1 := by
    have h := F.norm_cosets (θ : U ≃* U) T hmap h4 x₁ hx₁ hr₁ ε (ν : k) hθ₁₁ 1
    simp only [hε] at h
    rw [← hR, ← h]
    ring
  have hcard2 : Nat.card {a : k // (ν : k) * a ^ (p ^ (2 * f)) = a} = p ^ (2 * f) := by
    refine card_fixed_frob_twist (m := 2) (f := 2 * f) (by norm_num) (by omega) ?_ ν ?_
    · rw [hk]
      ring
    · apply Units.ext
      have hsum : ∑ i ∈ Finset.range 2, (p ^ (2 * f)) ^ i = 1 + p ^ (2 * f) := by
        simp [Finset.sum_range_succ]
      rw [hsum, Units.val_pow_eq_pow_val, Units.val_one]
      exact hν4
  have hcard : Nat.card ↥(foldFix (θ : U ≃* U)) = (p ^ f) ^ 3 := by
    rw [hmul, hVfix, hcosets, Nat.card_congr (Equiv.subtypeEquivRight hsol), hcard2]
    ring
  refine ⟨hcard, IsPGroup.of_card (n := f * 3) (by rw [hcard, pow_mul]), ?_⟩
  have hcos2 : 1 < Nat.card {a : k // (ν : k) * a ^ (p ^ (2 * f)) = a} := by
    rw [hcard2]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  have := Finite.one_lt_card_iff_nontrivial.1 hcos2
  have h0 : (ν : k) * (0 : k) ^ (p ^ (2 * f)) = 0 := by
    rw [zero_pow (pow_ne_zero _ hp.ne_zero), mul_zero]
  obtain ⟨⟨a, ha⟩, hne⟩ := exists_ne (⟨0, h0⟩ : {a : k // (ν : k) * a ^ (p ^ (2 * f)) = a})
  have ha0 : a ≠ 0 := fun h => hne (Subtype.ext h)
  have ha' : (ν : k) * ε (ε a) = a := (hsol a).2 ha
  have hy : x₁ (ofAdd a) ∈ X₁ := hr₁ _
  have hy1 : x₁ (ofAdd a) ≠ 1 := by
    intro h
    have h' : x₁ (ofAdd a) = x₁ (ofAdd 0) := by rw [h, ofAdd_zero, map_one]
    exact ha0 (Multiplicative.ofAdd.injective (hx₁ h'))
  obtain ⟨z₀, hz₀, hTy⟩ := UnHeisSub.T_X₁ (θ : U ≃* U) T hmap hθ₁ hy
  have hTz : T (z₀ : U ⧸ X₂) = ((x₁ (ofAdd a) : U) : U ⧸ X₂) := by
    rw [← hTy, UnHeisSub.T_T_X₁ (θ : U ≃* U) T hmap x₁ ε (ν : k) hθ₁₁ a, ha']
  have hfixq : T ((x₁ (ofAdd a) * z₀ : U) : U ⧸ X₂) = ((x₁ (ofAdd a) * z₀ : U) : U ⧸ X₂) := by
    rw [QuotientGroup.mk_mul, map_mul, hTy, hTz]
    exact F.quot_comm _ _
  have hx : (x₁ (ofAdd a) * z₀)⁻¹ * (θ : U ≃* U) (x₁ (ofAdd a) * z₀) ∈ X₂ := by
    rw [hmap] at hfixq
    exact QuotientGroup.eq.1 hfixq.symm
  obtain ⟨v, hvV, hvfix⟩ := exists_fixed_mul_mem_of_coprime (θ : U ≃* U) hθ4' X₂ hVθ hcop hx
  have hb : z₀ * v * z₀⁻¹ ∈ X₂ := hnorm₂ z₀ v hvV
  have hz1 : z₀ ≠ 1 := by
    intro h
    have h1 : ((θ (x₁ (ofAdd a)) : U) : U ⧸ X₂) = ((1 : U) : U ⧸ X₂) := by
      rw [← hmap, hTy, h]
    have h2 : θ (x₁ (ofAdd a)) ∈ X₂ := by
      have := QuotientGroup.eq.1 h1
      simpa using this
    have h3 : x₁ (ofAdd a) ∈ X₂ := by
      have := hVθ _ (hVθ _ (hVθ _ h2))
      rwa [h4] at this
    exact hy1 (F.eq_one_of_mem_inter hy h3)
  refine ⟨x₁ (ofAdd a), hy, hy1, z₀ * v * z₀⁻¹, hb, z₀, hz₀, hz1, ?_⟩
  rw [mem_foldFix]
  have e : x₁ (ofAdd a) * (z₀ * v * z₀⁻¹) * z₀ = x₁ (ofAdd a) * z₀ * v := by group
  rw [e]
  exact hvfix

theorem commute_outer_of_commute_fixed' {X : Type*} [Group X] (U X₁ X₂ X₃ : Subgroup X)
    (hX₁ : X₁ ≤ U) (hX₂ : X₂ ≤ U) (hX₃ : X₃ ≤ U)
    (huniq : ∀ y y' b b' z z' : X, y ∈ X₁ → y' ∈ X₁ → b ∈ X₂ → b' ∈ X₂ → z ∈ X₃ → z' ∈ X₃ →
      y * b * z = y' * b' * z' → y = y' ∧ b = b' ∧ z = z')
    (hnorm₂ : ∀ u ∈ U, ∀ y ∈ X₂, u * y * u⁻¹ ∈ X₂)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ X₂)
    (h u : X) (hu : u ∈ U) (hn₁ : ∀ y ∈ X₁, h * y * h⁻¹ ∈ X₁)
    (hn₂ : ∀ y ∈ X₂, h * y * h⁻¹ ∈ X₂) (hn₃ : ∀ y ∈ X₃, h * y * h⁻¹ ∈ X₃)
    {y b z : X} (hy : y ∈ X₁) (hb : b ∈ X₂) (hz : z ∈ X₃)
    (hk : (h * u) * (y * b * z) * (h * u)⁻¹ = y * b * z) :
    h * y * h⁻¹ = y ∧ h * z * h⁻¹ = z := by
  obtain ⟨v, hvdef⟩ : ∃ v : X, v = y * b * z := ⟨_, rfl⟩
  have hv : v ∈ U := by
    rw [hvdef]
    exact U.mul_mem (U.mul_mem (hX₁ hy) (hX₂ hb)) (hX₃ hz)
  obtain ⟨c, hcdef⟩ : ∃ c : X, c = h * (u * v * u⁻¹ * v⁻¹) * h⁻¹ := ⟨_, rfl⟩
  obtain ⟨y', hy'def⟩ : ∃ y' : X, y' = h * y * h⁻¹ := ⟨_, rfl⟩
  obtain ⟨b', hb'def⟩ : ∃ b' : X, b' = h * b * h⁻¹ := ⟨_, rfl⟩
  obtain ⟨z', hz'def⟩ : ∃ z' : X, z' = h * z * h⁻¹ := ⟨_, rfl⟩
  have hc : c ∈ X₂ := by
    rw [hcdef]
    exact hn₂ _ (hcomm u hu v hv)
  have hy' : y' ∈ X₁ := by
    rw [hy'def]
    exact hn₁ y hy
  have hb' : b' ∈ X₂ := by
    rw [hb'def]
    exact hn₂ b hb
  have hz' : z' ∈ X₃ := by
    rw [hz'def]
    exact hn₃ z hz
  have e1 : c * (y' * b' * z') = y * b * z := by
    calc c * (y' * b' * z') = h * u * (y * b * z) * (h * u)⁻¹ := by
          rw [hcdef, hy'def, hb'def, hz'def, hvdef]
          group
      _ = y * b * z := hk
  have hc'' : y'⁻¹ * c * y' ∈ X₂ := by
    have := hnorm₂ y'⁻¹ (U.inv_mem (hX₁ hy')) c hc
    simpa using this
  have e2 : y' * ((y'⁻¹ * c * y') * b') * z' = y * b * z := by
    rw [← e1]
    group
  obtain ⟨h1, -, h3⟩ := huniq y' y _ b z' z hy' hy (X₂.mul_mem hc'' hb') hb hz' hz e2
  exact ⟨hy'def.symm.trans h1, hz'def.symm.trans h3⟩

end CFSG.GH74.GLS.SP
