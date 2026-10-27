module

public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8

open Subgroup

section Defs
variable {K : Type*} [Group K]

@[expose] def QPair (u v : K) : Prop := u ^ 4 = 1 ∧ u ^ 2 ≠ 1 ∧ v ^ 2 = u ^ 2 ∧ v * u * v⁻¹ = u⁻¹

structure Q8Like (A : Subgroup K) (ζ : K) : Prop where
  ζ_mem : ζ ∈ A
  ζ_ne : ζ ≠ 1
  ζ_sq : ζ ^ 2 = 1
  card : Nat.card A = 8
  pow4 : ∀ a ∈ A, a ^ 4 = 1
  uniq : ∀ a ∈ A, a ^ 2 = 1 → a = 1 ∨ a = ζ
  comm : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ = 1 ∨ a * a' * a⁻¹ * a'⁻¹ = ζ
  center : ∀ a ∈ A, (∀ a' ∈ A, a * a' = a' * a) → a = 1 ∨ a = ζ
  gen : ∃ i j : K, i ∈ A ∧ j ∈ A ∧ QPair i j ∧ A = Subgroup.closure {i, j}

structure QuatLike (B Y : Subgroup K) (ζ : K) : Prop where
  Y_le : Y ≤ B
  Y_cyc : IsCyclic Y
  ζ_mem : ζ ∈ Y
  ζ_ne : ζ ≠ 1
  ζ_sq : ζ ^ 2 = 1
  uniq : ∀ b ∈ B, b ^ 2 = 1 → b = 1 ∨ b = ζ
  idx : ∀ g ∈ B, ∀ h ∈ B, g ∉ Y → h ∉ Y → g * h⁻¹ ∈ Y
  out_sq : ∀ g ∈ B, g ∉ Y → g ^ 2 = ζ
  out_inv : ∀ g ∈ B, g ∉ Y → ∀ y ∈ Y, g * y * g⁻¹ = y⁻¹

end Defs

section

theorem perm_eq_one_of_card_le_four {X : Type*} [Finite X] (hX : Nat.card X ≤ 4)
    (σ : Equiv.Perm X) (m : ℕ) (hσ : σ ^ m = 1) (hm : Nat.Coprime m 6) : σ = 1 := by
  have hdvd : orderOf σ ∣ (Nat.card X).factorial := by
    rw [← Nat.card_perm]
    exact orderOf_dvd_natCard σ
  have hfac : (Nat.card X).factorial ∣ 24 := by
    have h := Nat.factorial_dvd_factorial hX
    have h24 : Nat.factorial 4 = 24 := by decide
    rw [h24] at h
    exact h
  have h216 : (24 : ℕ) ∣ 6 ^ 3 := Nat.dvd_of_mod_eq_zero (by norm_num)
  have hcop : Nat.Coprime m 24 :=
    Nat.Coprime.coprime_dvd_right h216 (Nat.Coprime.pow_right 3 hm)
  have hord : orderOf σ ∣ m := orderOf_dvd_of_pow_eq_one hσ
  have hg : orderOf σ ∣ Nat.gcd m 24 := Nat.dvd_gcd hord (dvd_trans hdvd hfac)
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at hg
  exact orderOf_eq_one_iff.mp hg

theorem aut_coset_fixed {G : Type*} [Group G] [Finite G] (N : Subgroup G) (hidx : N.index ≤ 4)
    (σ : MulAut G) (hσN : ∀ g : G, σ g ∈ N ↔ g ∈ N) (m : ℕ) (hσ : σ ^ m = 1)
    (hm : Nat.Coprime m 6) : ∀ g : G, g⁻¹ * σ g ∈ N := by
  have hσN' : ∀ g : G, σ.symm g ∈ N ↔ g ∈ N := by
    intro g
    have h := hσN (σ.symm g)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hfwd : ∀ τ : MulAut G, (∀ g : G, τ g ∈ N ↔ g ∈ N) →
      ∀ a b : G, (QuotientGroup.leftRel N).r a b → (QuotientGroup.leftRel N).r (τ a) (τ b) := by
    intro τ hτ a b hab
    have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.mp hab
    apply QuotientGroup.leftRel_apply.mpr
    have e : (τ a)⁻¹ * τ b = τ (a⁻¹ * b) := by rw [map_mul, map_inv]
    rw [e]
    exact (hτ _).mpr hab'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Equiv.Perm (G ⧸ N),
      ∀ g : G, ψ (QuotientGroup.mk g) = QuotientGroup.mk (σ g) := by
    refine ⟨{ toFun := Quotient.map' (⇑σ) (hfwd σ hσN)
              invFun := Quotient.map' (⇑σ.symm) (hfwd σ.symm hσN')
              left_inv := ?_
              right_inv := ?_ }, fun g => rfl⟩
    · intro c
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
      show QuotientGroup.mk (σ.symm (σ a)) = QuotientGroup.mk a
      rw [MulEquiv.symm_apply_apply]
    · intro c
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
      show QuotientGroup.mk (σ (σ.symm a)) = QuotientGroup.mk a
      rw [MulEquiv.apply_symm_apply]
  have hpow : ∀ k : ℕ, ∀ g : G,
      (ψ ^ k) (QuotientGroup.mk g) = QuotientGroup.mk ((σ ^ k) g) := by
    intro k
    induction k with
    | zero => intro g; simp [Equiv.Perm.one_apply, MulAut.one_apply]
    | succ k ih =>
      intro g
      rw [pow_succ' ψ k, pow_succ' σ k, Equiv.Perm.mul_apply, ih, hψ, MulAut.mul_apply]
  have hψm : ψ ^ m = 1 := by
    apply Equiv.ext
    intro c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    have hσg : (σ ^ m) g = g := by rw [hσ, MulAut.one_apply]
    rw [hpow m g, hσg, Equiv.Perm.one_apply]
  have hX : Nat.card (G ⧸ N) ≤ 4 := hidx
  have hψ1 : ψ = 1 := perm_eq_one_of_card_le_four hX ψ m hψm hm
  intro g
  have h1 : ψ (QuotientGroup.mk g) = QuotientGroup.mk g := by
    rw [hψ1, Equiv.Perm.one_apply]
  rw [hψ g] at h1
  have h2 : (σ g)⁻¹ * g ∈ N := QuotientGroup.eq.mp h1
  have h3 := N.inv_mem h2
  rw [mul_inv_rev, inv_inv] at h3
  exact h3

theorem conj_coset_fixed {K : Type*} [Group K] [Finite K] (Q N : Subgroup K) (hNQ : N ≤ Q)
    (hidx : N.relIndex Q ≤ 4)
    (x : K) (hxQ : ∀ g ∈ Q, x * g * x⁻¹ ∈ Q) (hxQ' : ∀ g ∈ Q, x⁻¹ * g * x ∈ Q)
    (hxN : ∀ g ∈ Q, (x * g * x⁻¹ ∈ N ↔ g ∈ N)) (m : ℕ) (hx : x ^ m = 1)
    (hm : Nat.Coprime m 6) : ∀ g ∈ Q, g⁻¹ * (x * g * x⁻¹) ∈ N := by
  clear hNQ
  obtain ⟨σ, hσval⟩ : ∃ σ : MulAut Q, ∀ g : Q, ((σ g : Q) : K) = x * (g : K) * x⁻¹ :=
    ⟨{ toFun := fun g => ⟨x * (g : K) * x⁻¹, hxQ g g.2⟩
       invFun := fun g => ⟨x⁻¹ * (g : K) * x, hxQ' g g.2⟩
       left_inv := fun g => Subtype.ext (by simp [mul_assoc])
       right_inv := fun g => Subtype.ext (by simp [mul_assoc])
       map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }, fun g => rfl⟩
  have hσpow : ∀ (k : ℕ) (g : Q), ((σ ^ k) g : K) = x ^ k * (g : K) * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ' σ k, MulAut.mul_apply, hσval, ih, pow_succ' x k, mul_inv_rev]
      simp only [mul_assoc]
  have hσm : σ ^ m = 1 := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    simp only [hσpow m g, hx, one_mul, inv_one, mul_one, MulAut.one_apply]
  have hσN : ∀ g : Q, σ g ∈ N.subgroupOf Q ↔ g ∈ N.subgroupOf Q := by
    intro g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hσval]
    exact hxN (g : K) g.2
  have hres := aut_coset_fixed (N.subgroupOf Q) hidx σ hσN m hσm hm
  intro g hg
  have h := hres ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa [hσval] using h


theorem frat_four_mul_closed {M : Type*} [CommGroup M] (p q : M) (hp : p * p = 1)
    (hq : q * q = 1) (a b : M) (ha : a = 1 ∨ a = p ∨ a = q ∨ a = p * q)
    (hb : b = 1 ∨ b = p ∨ b = q ∨ b = p * q) :
    a * b = 1 ∨ a * b = p ∨ a * b = q ∨ a * b = p * q := by
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb]
  · exact Or.inl (mul_one 1)
  · exact Or.inr (Or.inl (one_mul p))
  · exact Or.inr (Or.inr (Or.inl (one_mul q)))
  · exact Or.inr (Or.inr (Or.inr (one_mul (p * q))))
  · exact Or.inr (Or.inl (mul_one p))
  · exact Or.inl hp
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hp, one_mul])))
  · exact Or.inr (Or.inr (Or.inl (mul_one q)))
  · exact Or.inr (Or.inr (Or.inr (mul_comm q p)))
  · exact Or.inl hq
  · exact Or.inr (Or.inl (by rw [mul_left_comm, hq, mul_one]))
  · exact Or.inr (Or.inr (Or.inr (mul_one (p * q))))
  · exact Or.inr (Or.inr (Or.inl (by rw [mul_right_comm, hp, one_mul])))
  · exact Or.inr (Or.inl (by rw [mul_assoc, hq, mul_one]))
  · exact Or.inl (by rw [mul_mul_mul_comm, hp, hq, one_mul])

theorem aut_eq_one_of_frattini {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H)
    (σ : MulAut H) (m : ℕ) (hσ : σ ^ m = 1) (hm : Nat.Coprime m 2)
    (hfr : ∀ g : H, g⁻¹ * σ g ∈ frattini H) : σ = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : σ ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini H)).ker :=
    (CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel
      (frattini H) σ).mpr (fun g => (QuotientGroup.eq.mpr (hfr g)).symm)
  have hpg := CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup
    2 hH
  obtain ⟨k, hk⟩ := hpg ⟨σ, hker⟩
  have hk' : σ ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k hm
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hσ)
      (orderOf_dvd_of_pow_eq_one hk'))

theorem frattini_index_le_four {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H) (u v : H)
    (hgen : Subgroup.closure {u, v} = ⊤) : (frattini H).index ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hcomm, hpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hH
  letI : CommGroup (H ⧸ frattini H) :=
    { (inferInstance : Group (H ⧸ frattini H)) with
      mul_comm := fun x y => hcomm.is_comm.comm x y }
  have hsq : ∀ y : H ⧸ frattini H, y * y = 1 := fun y => (pow_two y).symm.trans (hpow y)
  have hgenV : ∀ g : H, g ∈ Subgroup.closure ({u, v} : Set H) →
      ((g : H ⧸ frattini H) = 1 ∨ (g : H ⧸ frattini H) = (u : H ⧸ frattini H) ∨
        (g : H ⧸ frattini H) = (v : H ⧸ frattini H) ∨
        (g : H ⧸ frattini H) = (u : H ⧸ frattini H) * (v : H ⧸ frattini H)) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr (Or.inl (by rw [h])))
    | one => exact Or.inl rfl
    | mul x y _ _ ihx ihy =>
      rw [QuotientGroup.mk_mul]
      exact frat_four_mul_closed (u : H ⧸ frattini H) (v : H ⧸ frattini H) (hsq _) (hsq _) _ _
        ihx ihy
    | inv x _ ih =>
      rw [QuotientGroup.mk_inv, inv_eq_of_mul_eq_one_right (hsq (x : H ⧸ frattini H))]
      exact ih
  have hall : ∀ y : H ⧸ frattini H, y = 1 ∨ y = (u : H ⧸ frattini H) ∨
      y = (v : H ⧸ frattini H) ∨ y = (u : H ⧸ frattini H) * (v : H ⧸ frattini H) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact hgenV g (by rw [hgen]; exact Subgroup.mem_top g)
  have hsurj : Function.Surjective
      (![1, (u : H ⧸ frattini H), (v : H ⧸ frattini H),
          (u : H ⧸ frattini H) * (v : H ⧸ frattini H)] : Fin 4 → H ⧸ frattini H) := by
    intro y
    rcases hall y with h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
  have hle : Nat.card (H ⧸ frattini H) ≤ Nat.card (Fin 4) :=
    Nat.card_le_card_of_surjective _ hsurj
  have h4 : Nat.card (Fin 4) = 4 := by simp
  exact hle.trans h4.le

theorem centralizes_of_two_gen {K : Type*} [Group K] [Finite K] (P : Subgroup K)
    (hP : IsPGroup 2 P) (u v : K) (hgen : P = Subgroup.closure {u, v}) (x : K)
    (hxP : ∀ g ∈ P, x * g * x⁻¹ ∈ P) (hxP' : ∀ g ∈ P, x⁻¹ * g * x ∈ P) (m : ℕ)
    (hx : x ^ m = 1) (hm : Nat.Coprime m 6) : ∀ g ∈ P, x * g * x⁻¹ = g := by
  have hu : u ∈ P := by
    rw [hgen]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hv : v ∈ P := by
    rw [hgen]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have key : ∀ k : K, k ∈ Subgroup.closure ({u, v} : Set K) →
      ∃ h : k ∈ P, (⟨k, h⟩ : ↥P) ∈ Subgroup.closure ({⟨u, hu⟩, ⟨v, hv⟩} : Set ↥P) := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h | h
      · subst h
        exact ⟨hu, Subgroup.subset_closure (Set.mem_insert _ _)⟩
      · subst h
        exact ⟨hv, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
    | one => exact ⟨P.one_mem, Subgroup.one_mem _⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨ha, ha'⟩ := iha
      obtain ⟨hb, hb'⟩ := ihb
      exact ⟨P.mul_mem ha hb, Subgroup.mul_mem _ ha' hb'⟩
    | inv a _ iha =>
      obtain ⟨ha, ha'⟩ := iha
      exact ⟨P.inv_mem ha, Subgroup.inv_mem _ ha'⟩
  have htop : Subgroup.closure ({⟨u, hu⟩, ⟨v, hv⟩} : Set ↥P) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro g
    have hg : (g : K) ∈ Subgroup.closure ({u, v} : Set K) := by
      rw [← hgen]
      exact g.2
    obtain ⟨_, hmem⟩ := key (g : K) hg
    exact hmem
  obtain ⟨σ, hσval⟩ : ∃ σ : MulAut ↥P, ∀ g : ↥P, ((σ g : ↥P) : K) = x * (g : K) * x⁻¹ :=
    ⟨{ toFun := fun g => ⟨x * (g : K) * x⁻¹, hxP g g.2⟩
       invFun := fun g => ⟨x⁻¹ * (g : K) * x, hxP' g g.2⟩
       left_inv := fun g => Subtype.ext (by simp [mul_assoc])
       right_inv := fun g => Subtype.ext (by simp [mul_assoc])
       map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }, fun g => rfl⟩
  have hσpow : ∀ (k : ℕ) (g : ↥P), ((σ ^ k) g : K) = x ^ k * (g : K) * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ' σ k, MulAut.mul_apply, hσval, ih, pow_succ' x k, mul_inv_rev]
      simp only [mul_assoc]
  have hσm : σ ^ m = 1 := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    simp only [hσpow m g, hx, one_mul, inv_one, mul_one, MulAut.one_apply]
  have hcomap : (frattini ↥P).comap (MulEquiv.toMonoidHom σ) = frattini ↥P := by
    have hch : (frattini ↥P).Characteristic := inferInstance
    exact hch.fixed σ
  have hσN : ∀ g : ↥P, σ g ∈ frattini ↥P ↔ g ∈ frattini ↥P := by
    intro g
    have hg' : g ∈ (frattini ↥P).comap (MulEquiv.toMonoidHom σ) ↔ g ∈ frattini ↥P := by
      rw [hcomap]
    rw [Subgroup.mem_comap] at hg'
    exact hg'
  have hidx : (frattini ↥P).index ≤ 4 :=
    frattini_index_le_four hP (⟨u, hu⟩ : ↥P) (⟨v, hv⟩ : ↥P) htop
  have hm2 : Nat.Coprime m 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hm
  have hfr := aut_coset_fixed (frattini ↥P) hidx σ hσN m hσm hm
  have hσ1 : σ = 1 := aut_eq_one_of_frattini hP σ m hσm hm2 hfr
  intro g hg
  have h1 : σ (⟨g, hg⟩ : ↥P) = ⟨g, hg⟩ := by
    rw [hσ1, MulAut.one_apply]
  have h2 := hσval (⟨g, hg⟩ : ↥P)
  rw [h1] at h2
  exact h2.symm

end

section

section Small
variable {K : Type*} [Group K]

theorem stab_centralizes (Q N : Subgroup K) (hNQ : N ≤ Q) (hQ : IsPGroup 2 Q)
    (x : K) (m : ℕ) (hx : x ^ m = 1) (hm : Nat.Coprime m 2)
    (hNc : ∀ n ∈ N, x * n * x⁻¹ = n) (hQN : ∀ g ∈ Q, g⁻¹ * (x * g * x⁻¹) ∈ N) :
    ∀ g ∈ Q, x * g * x⁻¹ = g := by
  intro g hg
  obtain ⟨c, hc⟩ : ∃ c : K, c = g⁻¹ * (x * g * x⁻¹) := ⟨_, rfl⟩
  have hcN : c ∈ N := by
    rw [hc]
    exact hQN g hg
  have hcQ : c ∈ Q := hNQ hcN
  have hxg : x * g * x⁻¹ = g * c := by
    rw [hc, mul_inv_cancel_left]
  have hxg' : x * g = g * c * x := mul_inv_eq_iff_eq_mul.mp hxg
  have hcx : Commute x c := by
    show x * c = c * x
    exact mul_inv_eq_iff_eq_mul.mp (hNc c hcN)
  have key : ∀ k : ℕ, x ^ k * g = g * c ^ k * x ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hcxk : x * c ^ k = c ^ k * x := (hcx.pow_right k).eq
      have e1 : x ^ (k + 1) * g = x * (x ^ k * g) := by
        rw [pow_succ', mul_assoc]
      rw [e1, ih]
      calc x * (g * c ^ k * x ^ k) = x * g * c ^ k * x ^ k := by simp only [mul_assoc]
        _ = g * c * x * c ^ k * x ^ k := by rw [hxg']
        _ = g * c * (x * c ^ k) * x ^ k := by simp only [mul_assoc]
        _ = g * c * (c ^ k * x) * x ^ k := by rw [hcxk]
        _ = g * (c * c ^ k) * (x * x ^ k) := by simp only [mul_assoc]
        _ = g * c ^ (k + 1) * x ^ (k + 1) := by rw [pow_succ' c k, pow_succ' x k]
  have hcm : c ^ m = 1 := by
    have h1 := key m
    rw [hx, one_mul, mul_one] at h1
    have h2 : g * c ^ m = g * 1 := by
      rw [mul_one]
      exact h1.symm
    exact mul_left_cancel h2
  obtain ⟨j, hj⟩ := hQ ⟨c, hcQ⟩
  have hc2 : c ^ 2 ^ j = 1 := by
    have h' := congrArg Subtype.val hj
    simpa using h'
  have h1 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one hcm
  have h2 : orderOf c ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hc2
  have hcop : Nat.Coprime m (2 ^ j) := Nat.Coprime.pow_right j hm
  have h3 : orderOf c ∣ Nat.gcd m (2 ^ j) := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at h3
  have hc1 : c = 1 := orderOf_eq_one_iff.mp h3
  rw [hxg, hc1, mul_one]

theorem conj_mem_inv_of_finite [Finite K] (P : Subgroup K) (x : K)
    (h : ∀ g ∈ P, x * g * x⁻¹ ∈ P) : ∀ g ∈ P, x⁻¹ * g * x ∈ P := by
  let f : P → P := fun g => ⟨x * (g : K) * x⁻¹, h (g : K) g.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h1 : x * (a : K) * x⁻¹ = x * (b : K) * x⁻¹ := congrArg Subtype.val hab
    exact mul_left_cancel (mul_right_cancel h1)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro g hg
  obtain ⟨g', hg'⟩ := hsurj ⟨g, hg⟩
  have hval : x * (g' : K) * x⁻¹ = g := congrArg Subtype.val hg'
  have hgg : x⁻¹ * g * x = (g' : K) := by
    rw [← hval]
    group
  rw [hgg]
  exact g'.2

theorem normalizes_of_sq (A : Subgroup K) (x : K) (m : ℕ) (hx : x ^ m = 1)
    (hm : Nat.Coprime m 2) (h : ∀ g ∈ A, x ^ 2 * g * (x ^ 2)⁻¹ ∈ A) :
    ∀ g ∈ A, x * g * x⁻¹ ∈ A := by
  have hnd : ¬ 2 ∣ m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hm.symm
  obtain ⟨t, ht⟩ : ∃ t : ℕ, m = 2 * t + 1 := ⟨m / 2, by omega⟩
  have hpow : ∀ k : ℕ, ∀ g ∈ A, (x ^ 2) ^ k * g * ((x ^ 2) ^ k)⁻¹ ∈ A := by
    intro k
    induction k with
    | zero =>
      intro g hg
      simpa using hg
    | succ k ih =>
      intro g hg
      have e : (x ^ 2) ^ (k + 1) * g * ((x ^ 2) ^ (k + 1))⁻¹ =
          x ^ 2 * ((x ^ 2) ^ k * g * ((x ^ 2) ^ k)⁻¹) * (x ^ 2)⁻¹ := by
        rw [pow_succ' (x ^ 2) k, mul_inv_rev]
        simp only [mul_assoc]
      rw [e]
      exact h _ (ih g hg)
  have hxe : (x ^ 2) ^ (t + 1) = x := by
    rw [← pow_mul]
    have h2t : 2 * (t + 1) = m + 1 := by omega
    rw [h2t, pow_succ, hx, one_mul]
  intro g hg
  have hg' := hpow (t + 1) g hg
  rwa [hxe] at hg'

theorem QPair.conj {u v : K} (h : QPair u v) (x : K) :
    QPair (x * u * x⁻¹) (x * v * x⁻¹) := by
  unfold QPair at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [conj_pow, h1]
    simp
  · intro hc
    apply h2
    rw [conj_pow] at hc
    calc u ^ 2 = x⁻¹ * (x * u ^ 2 * x⁻¹) * x := by group
      _ = x⁻¹ * 1 * x := by rw [hc]
      _ = 1 := by group
  · rw [conj_pow, conj_pow, h3]
  · have e : x * v * x⁻¹ * (x * u * x⁻¹) * (x * v * x⁻¹)⁻¹ = x * (v * u * v⁻¹) * x⁻¹ := by
      group
    rw [e, h4]
    group

theorem qpair_card_ge [Finite K] {u v : K} (h : QPair u v) :
    8 ≤ Nat.card (Subgroup.closure {u, v}) := by
  unfold QPair at h
  obtain ⟨h1, h2, _, h4⟩ := h
  have hord : orderOf u = 4 := by
    have hnot : ¬ u ^ 2 ^ 1 = 1 := by simpa using h2
    have hfin : u ^ 2 ^ (1 + 1) = 1 := by simpa using h1
    exact (orderOf_eq_prime_pow hnot hfin).trans (by norm_num)
  have hzp : Nat.card (Subgroup.zpowers u) = 4 := by
    rw [Nat.card_zpowers, hord]
  obtain ⟨H, hH⟩ : ∃ H : Subgroup K, H = Subgroup.closure {u, v} := ⟨_, rfl⟩
  rw [← hH]
  have huH : u ∈ H := by
    rw [hH]
    exact Subgroup.subset_closure (Set.mem_insert u _)
  have hvH : v ∈ H := by
    rw [hH]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem u (Set.mem_singleton v))
  have hle : Subgroup.zpowers u ≤ H := Subgroup.zpowers_le.mpr huH
  have hvnot : v ∉ Subgroup.zpowers u := by
    intro hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hcomm : Commute u v := by
      rw [← hk]
      exact (Commute.refl u).zpow_right k
    have hvu : v * u * v⁻¹ = u := by
      rw [← hcomm.eq, mul_inv_cancel_right]
    have hu_inv : u = u⁻¹ := hvu.symm.trans h4
    apply h2
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr hu_inv
  have hpos : 0 < Nat.card H := by
    haveI : Nonempty H := ⟨⟨1, H.one_mem⟩⟩
    exact Nat.card_pos
  have hdvd : Nat.card (Subgroup.zpowers u) ∣ Nat.card H := Subgroup.card_dvd_of_le hle
  rw [hzp] at hdvd
  have hne : Nat.card H ≠ 4 := by
    intro heq
    apply hvnot
    have hEq : Subgroup.zpowers u = H := Subgroup.eq_of_le_of_card_ge hle (by omega)
    rw [hEq]
    exact hvH
  omega

theorem closure_eq_of_qpair [Finite K] {A : Subgroup K} {ζ : K} (hA : Q8Like A ζ) {u v : K}
    (hu : u ∈ A) (hv : v ∈ A) (h : QPair u v) : Subgroup.closure {u, v} = A := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv
  · rw [hA.card]
    exact qpair_card_ge h

end Small

end

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8
