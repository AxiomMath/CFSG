module

public import CFSG.CGT.PushingUpLit.A78Sp4.CL
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

variable {K : Type*} [Field K]

section Galois

variable [Finite K] [CharP K 2]

theorem exists_pow_of_ringHom (σ : K →+* K) : ∃ j : ℕ, ∀ x, σ x = x ^ 2 ^ j := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσb : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  let σe : K ≃+* K := RingEquiv.ofBijective σ hσb
  have hcomm : ∀ x : ZMod 2, σe (algebraMap (ZMod 2) K x) = algebraMap (ZMod 2) K x := fun x =>
    DFunLike.congr_fun (RingHom.ext_zmod (σ.comp (algebraMap (ZMod 2) K))
      (algebraMap (ZMod 2) K)) x
  let f : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv hcomm
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) K).2 f
  refine ⟨n, fun x => ?_⟩
  have h1 : ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ (n : ℕ)) x = f x :=
    DFunLike.congr_fun hn x
  have h2 : ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ (n : ℕ)) x =
      x ^ 2 ^ (n : ℕ) := by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  exact (h2.symm.trans h1).symm

end Galois

section Torus

@[expose] def diagPerm (a b : Kˣ) : Equiv.Perm (K × K) where
  toFun p := ((a : K) * p.1, (b : K) * p.2)
  invFun p := (((a⁻¹ : Kˣ) : K) * p.1, ((b⁻¹ : Kˣ) : K) * p.2)
  left_inv p := Prod.ext (Units.inv_mul_cancel_left a p.1) (Units.inv_mul_cancel_left b p.2)
  right_inv p := Prod.ext (Units.mul_inv_cancel_left a p.1) (Units.mul_inv_cancel_left b p.2)

theorem diagPerm_apply (a b : Kˣ) (p : K × K) :
    diagPerm a b p = ((a : K) * p.1, (b : K) * p.2) := rfl

@[expose] def diagHom : Kˣ × Kˣ →* Equiv.Perm (K × K) where
  toFun p := diagPerm p.1 p.2
  map_one' := Equiv.ext fun _ => Prod.ext (one_mul _) (one_mul _)
  map_mul' _ _ := Equiv.ext fun _ => Prod.ext (mul_assoc _ _ _) (mul_assoc _ _ _)

def torus (K : Type*) [Field K] : Subgroup (Equiv.Perm (K × K)) := (diagHom (K := K)).range

section TorusFacts

variable [Finite K] [CharP K 2]

theorem odd_card_units : Odd (Nat.card Kˣ) := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, Fintype.card_units, hn]
  exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow).2 ⟨even_two, n.ne_zero⟩) odd_one

theorem odd_card_torus : Odd (Nat.card (torus K)) := by
  have h1 : Nat.card (torus K) ∣ Nat.card (Kˣ × Kˣ) :=
    Subgroup.card_dvd_of_surjective (MonoidHom.rangeRestrict_surjective (diagHom (K := K)))
  rw [Nat.card_prod] at h1
  exact (odd_card_units.mul odd_card_units).of_dvd_nat h1

@[expose] noncomputable def rhoPerm (K : Type*) [Field K] [Finite K] [CharP K 2] :
    Equiv.Perm (K × K) := (rhoEquiv K).toEquiv

theorem rhoPerm_apply (p : K × K) : rhoPerm K p = (p.2, p.1 ^ 2) := rfl

theorem rho_conj_diag (a b : Kˣ) :
    rhoPerm K * diagPerm a b * (rhoPerm K)⁻¹ = diagPerm b (a ^ 2) := by
  refine Equiv.ext fun p => ?_
  obtain ⟨r, s⟩ := p
  refine Prod.ext rfl ?_
  show (((a : K) * (frobeniusEquiv K 2).symm s) ^ 2) = ((a ^ 2 : Kˣ) : K) * s
  have h : ((frobeniusEquiv K 2).symm s) ^ 2 = s := (frobeniusEquiv K 2).apply_symm_apply s
  rw [mul_pow, h, Units.val_pow_eq_pow_val]

theorem rho_mem_normalizer_torus :
    rhoPerm K ∈ Subgroup.normalizer (torus K : Set (Equiv.Perm (K × K))) := by
  have hle : (torus K).map (MulAut.conj (rhoPerm K)).toMonoidHom ≤ torus K := by
    rintro _ ⟨t, ⟨⟨a, b⟩, rfl⟩, rfl⟩
    refine ⟨(b, a ^ 2), ?_⟩
    show diagPerm b (a ^ 2) = rhoPerm K * diagPerm a b * (rhoPerm K)⁻¹
    rw [rho_conj_diag]
  have hcard : Nat.card (torus K) ≤
      Nat.card ((torus K).map (MulAut.conj (rhoPerm K)).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj (rhoPerm K)).injective).ge
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hle ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨t, ht, hth⟩ := hh
    have : t = h := (MulAut.conj (rhoPerm K)).injective hth
    rwa [this] at ht

theorem rho_sq_apply (p : K × K) : (rhoPerm K ^ 2) p = (p.1 ^ 2, p.2 ^ 2) := rfl

theorem rho_pow_two_mul (j : ℕ) (p : K × K) :
    (rhoPerm K ^ (2 * j)) p = (p.1 ^ 2 ^ j, p.2 ^ 2 ^ j) := by
  induction j generalizing p with
  | zero => simp
  | succ j ih =>
    have e : rhoPerm K ^ (2 * (j + 1)) = rhoPerm K ^ (2 * j) * rhoPerm K ^ 2 := by
      rw [← pow_add]
      congr 1
    rw [e, Equiv.Perm.mul_apply, rho_sq_apply, ih]
    simp only [← pow_mul, ← pow_succ']

noncomputable def torusRho (K : Type*) [Field K] [Finite K] [CharP K 2] :
    Subgroup (Equiv.Perm (K × K)) := Subgroup.zpowers (rhoPerm K) ⊔ torus K

theorem mem_torusRho_of_form {π : Equiv.Perm (K × K)} {gb : K × K →+ K × K}
    (hπ : ∀ p, π p = gb p) (hform : IsDiagForm gb ∨ IsSwapForm gb) : π ∈ torusRho K := by
  have hρ : rhoPerm K ∈ torusRho K := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hpow : ∀ j : ℕ, rhoPerm K ^ (2 * j) ∈ torusRho K := fun j => Subgroup.pow_mem _ hρ _
  have hT : ∀ a b : Kˣ, diagPerm a b ∈ torusRho K := fun a b =>
    Subgroup.mem_sup_right ⟨(a, b), rfl⟩
  rcases hform with ⟨a, b, σ, ha, hb, h⟩ | ⟨a, b, σ, ha, hb, h⟩
  · obtain ⟨j, hj⟩ := exists_pow_of_ringHom σ
    have e : π = diagPerm (Units.mk0 a ha) (Units.mk0 b hb) * rhoPerm K ^ (2 * j) := by
      refine Equiv.ext fun p => ?_
      rw [hπ, Equiv.Perm.mul_apply, rho_pow_two_mul, diagPerm_apply]
      obtain ⟨r, s⟩ := p
      rw [h, hj, hj]
      rfl
    rw [e]
    exact Subgroup.mul_mem _ (hT _ _) (hpow j)
  · obtain ⟨j, hj⟩ := exists_pow_of_ringHom σ
    have e : π = rhoPerm K *
        (diagPerm (Units.mk0 a ha) (Units.mk0 b hb) * rhoPerm K ^ (2 * j)) := by
      refine Equiv.ext fun p => ?_
      rw [hπ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, rho_pow_two_mul, diagPerm_apply,
        rhoPerm_apply]
      obtain ⟨r, s⟩ := p
      rw [h, hj, hj]
      refine Prod.ext rfl ?_
      show a ^ 2 * (r ^ 2 ^ j) ^ 2 = (a * r ^ 2 ^ j) ^ 2
      ring
    rw [e]
    exact Subgroup.mul_mem _ hρ (Subgroup.mul_mem _ (hT _ _) (hpow j))

theorem exists_mul_of_mem_sup_of_le_normalizer {G : Type*} [Group G] {C T : Subgroup G}
    (h : C ≤ Subgroup.normalizer (T : Set G)) {x : G} (hx : x ∈ C ⊔ T) :
    ∃ c ∈ C, ∃ t ∈ T, x = c * t := by
  let S : Subgroup G :=
    { carrier := {x | ∃ c ∈ C, ∃ t ∈ T, x = c * t}
      one_mem' := ⟨1, C.one_mem, 1, T.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨c₁, hc₁, t₁, ht₁, rfl⟩ ⟨c₂, hc₂, t₂, ht₂, rfl⟩
        refine ⟨c₁ * c₂, C.mul_mem hc₁ hc₂, c₂⁻¹ * t₁ * c₂ * t₂, ?_, by group⟩
        refine T.mul_mem ?_ ht₂
        have := (Subgroup.mem_normalizer_iff.mp (h (C.inv_mem hc₂)) t₁).mp ht₁
        simpa [mul_assoc] using this
      inv_mem' := by
        rintro _ ⟨c, hc, t, ht, rfl⟩
        refine ⟨c⁻¹, C.inv_mem hc, c * t⁻¹ * c⁻¹, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (h hc) t⁻¹).mp (T.inv_mem ht)
        simpa [mul_assoc] using this }
  have hle : C ⊔ T ≤ S := sup_le (fun c hc => ⟨c, hc, 1, T.one_mem, (mul_one c).symm⟩)
    (fun t ht => ⟨1, C.one_mem, t, ht, (one_mul t).symm⟩)
  exact hle hx

theorem isCyclic_of_forms {G : Type*} [Group G] (hG : IsPGroup 2 G)
    (θ : G →* AddMonoid.End (K × K)) (hinj : Function.Injective θ)
    (hform : ∀ g, IsDiagForm (θ g : K × K →+ K × K) ∨ IsSwapForm (θ g : K × K →+ K × K)) :
    IsCyclic G := by
  let θP : G →* Equiv.Perm (K × K) :=
    { toFun := fun g =>
        { toFun := fun x => θ g x
          invFun := fun x => θ g⁻¹ x
          left_inv := fun x => by
            show (θ g⁻¹ * θ g) x = x
            rw [← map_mul, inv_mul_cancel, map_one]
            rfl
          right_inv := fun x => by
            show (θ g * θ g⁻¹) x = x
            rw [← map_mul, mul_inv_cancel, map_one]
            rfl }
      map_one' := Equiv.ext fun x => by
        show θ 1 x = x
        rw [map_one]
        rfl
      map_mul' := fun g h => Equiv.ext fun x => by
        show θ (g * h) x = θ g (θ h x)
        rw [map_mul]
        rfl }
  have hmem : ∀ g, θP g ∈ torusRho K := fun g =>
    mem_torusRho_of_form (gb := (θ g : K × K →+ K × K)) (fun p => rfl) (hform g)
  have hnorm : torusRho K ≤ Subgroup.normalizer (torus K : Set (Equiv.Perm (K × K))) := by
    refine sup_le ?_ (Subgroup.le_normalizer (H := torus K))
    rw [Subgroup.zpowers_le]
    exact rho_mem_normalizer_torus
  have hTN : ((torus K).subgroupOf (torusRho K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hnorm
  let θN : G →* torusRho K := θP.codRestrict (torusRho K) hmem
  let κ : G →* torusRho K ⧸ (torus K).subgroupOf (torusRho K) :=
    (QuotientGroup.mk' ((torus K).subgroupOf (torusRho K))).comp θN
  have hcyc : IsCyclic (torusRho K ⧸ (torus K).subgroupOf (torusRho K)) := by
    have hz : Subgroup.zpowers (rhoPerm K) ≤ torusRho K := le_sup_left
    refine isCyclic_of_surjective
      ((QuotientGroup.mk' ((torus K).subgroupOf (torusRho K))).comp (Subgroup.inclusion hz)) ?_
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c, hc, t, ht, hnct⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (C := Subgroup.zpowers (rhoPerm K)) (T := torus K) (by
        rw [Subgroup.zpowers_le]
        exact rho_mem_normalizer_torus) n.2
    refine ⟨⟨c, hc⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hz ⟨c, hc⟩) = QuotientGroup.mk n
    rw [QuotientGroup.eq]
    show ((Subgroup.inclusion hz ⟨c, hc⟩)⁻¹ * n) ∈ (torus K).subgroupOf (torusRho K)
    rw [Subgroup.mem_subgroupOf]
    have : ((Subgroup.inclusion hz ⟨c, hc⟩)⁻¹ * n : torusRho K) =
        ⟨t, Subgroup.mem_sup_right ht⟩ := by
      apply Subtype.ext
      show c⁻¹ * (n : Equiv.Perm (K × K)) = t
      rw [hnct]
      group
    rw [this]
    exact ht
  refine isCyclic_of_injective κ ?_
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgT : θP g ∈ torus K := by
    have h1 : θN g ∈ (torus K).subgroupOf (torusRho K) :=
      (QuotientGroup.eq_one_iff _).1 hg
    exact h1
  obtain ⟨k, hk⟩ := hG g
  have h2 : (θP g) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have h3 : orderOf (θP g) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf (θP g) ∣ Nat.card (torus K) :=
    Subgroup.orderOf_dvd_natCard (torus K) hgT
  have h5 : orderOf (θP g) = 1 := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
    by_contra hne
    have hi0 : i ≠ 0 := fun h0 => hne (by rw [hi, h0, pow_zero])
    have h2d : 2 ∣ orderOf (θP g) := by
      rw [hi]
      exact dvd_pow_self 2 hi0
    exact (Nat.not_even_iff_odd.2 odd_card_torus) (even_iff_two_dvd.2 (h2d.trans h4))
  have h6 : θP g = 1 := orderOf_eq_one_iff.1 h5
  apply hinj
  rw [map_one]
  refine DFunLike.ext _ _ fun x => ?_
  have := congrArg (fun π : Equiv.Perm (K × K) => π x) h6
  exact this

end TorusFacts

end Torus

end CFSG.CGT.PushingUpLit.A78Sp4
