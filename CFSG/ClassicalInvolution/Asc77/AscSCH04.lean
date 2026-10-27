module

public import CFSG.RankThree.CentralLift.ClassicalScalarCover

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralLift

@[expose] def centerPrimeToR (L : Type*) [Group L] (r : ℕ) : Subgroup L where
  carrier := {z | z ∈ Subgroup.center L ∧ Nat.Coprime (orderOf z) r}
  one_mem' := ⟨Subgroup.one_mem _, by rw [orderOf_one]; exact Nat.coprime_one_left r⟩
  mul_mem' := by
    rintro x y ⟨hx, hxr⟩ ⟨hy, hyr⟩
    refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
    have hc : Commute x y := (Subgroup.mem_center_iff.1 hy x)
    exact Nat.Coprime.coprime_dvd_left (hc.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
      (Nat.coprime_mul_iff_left.2 ⟨hxr, hyr⟩)
  inv_mem' := by
    rintro x ⟨hx, hxr⟩
    exact ⟨Subgroup.inv_mem _ hx, by rw [orderOf_inv]; exact hxr⟩

theorem centerPrimeToR_le_center (L : Type*) [Group L] (r : ℕ) :
    centerPrimeToR L r ≤ Subgroup.center L := fun _ hz => hz.1

instance centerPrimeToR_normal (L : Type*) [Group L] (r : ℕ) : (centerPrimeToR L r).Normal :=
  ⟨fun n hn g => by
    have h : g * n * g⁻¹ = n := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_center_iff.1 hn.1 g
    rw [h]
    exact hn⟩

theorem not_dvd_card_center_of_split {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {H : Subgroup (GL ι K)} [Finite H]
    (hD : ∀ d ∈ (StatedScalars ι K).subgroupOf H, d ^ 4 = 1)
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → IsPGroup r π.ker → ∃ s : H →* E, ∀ x, π (s x) = x)
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ Subgroup.center L ≃* StatedProj H) :
    ¬ r ∣ Nat.card (Subgroup.center L) := by
  classical
  intro hdvd
  set Z' := centerPrimeToR L r with hZ'
  have hZ'le : Z' ≤ Subgroup.center L := centerPrimeToR_le_center L r
  let φ₀ : L →* StatedProj H := (e : _ →* _).comp (QuotientGroup.mk' (Subgroup.center L))
  have hφ₀ : ∀ x, φ₀ x = 1 ↔ x ∈ Subgroup.center L := by
    intro x
    change e (QuotientGroup.mk' (Subgroup.center L) x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let η : (L ⧸ Z') →* StatedProj H :=
    QuotientGroup.lift Z' φ₀ (fun z hz => (hφ₀ z).2 (hZ'le hz))
  have hηq : ∀ x : L, η (QuotientGroup.mk' Z' x) = φ₀ x := fun x => rfl
  have hηsurj : Function.Surjective η := by
    intro y
    obtain ⟨u, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    exact ⟨QuotientGroup.mk' Z' x, hηq x⟩
  have hkerη : ∀ x : L, η (QuotientGroup.mk' Z' x) = 1 ↔ x ∈ Subgroup.center L := by
    intro x
    rw [hηq, hφ₀]
  have hcenη : η.ker ≤ Subgroup.center (L ⧸ Z') := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ Subgroup.center L := (hkerη x).1 hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subgroup.mem_center_iff.1 hx g
  have hpgη : IsPGroup r η.ker := by
    intro y
    obtain ⟨x, hxz⟩ : ∃ x : L, (QuotientGroup.mk' Z' x : L ⧸ Z') = y.1 :=
      QuotientGroup.mk_surjective y.1
    have hx : x ∈ Subgroup.center L := (hkerη x).1 (hxz ▸ y.2)
    have hord : orderOf x ≠ 0 := (orderOf_pos x).ne'
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord r (Fact.out : r.Prime).ne_one
    refine ⟨k, Subtype.ext ?_⟩
    have hxk : x ^ (r ^ k) ∈ Z' := by
      refine ⟨Subgroup.pow_mem _ hx _, ?_⟩
      have h1 : orderOf (x ^ (r ^ k)) ∣ m := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← pow_mul, ← hkm]
        exact pow_orderOf_eq_one x
      exact Nat.Coprime.coprime_dvd_left h1
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out : r.Prime)).2 hm))
    have h2 : (QuotientGroup.mk' Z' (x ^ (r ^ k)) : L ⧸ Z') = 1 :=
      (QuotientGroup.eq_one_iff _).2 hxk
    rw [map_pow] at h2
    change y.1 ^ (r ^ k) = 1
    rw [← hxz]
    exact h2
  obtain ⟨φ, -, -, -, -, -, ⟨iso⟩⟩ := exact_scalar_cover_of_forall_section hηsurj hcenη hpgη hsplit
  have hker4 : ∀ y : η.ker, y ^ 4 = 1 := by
    intro y
    obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective (iso y)
    have h1 : (iso y) ^ 4 = 1 := by
      rw [← hd, ← QuotientGroup.mk_pow]
      have : d ^ 4 = 1 := Subtype.ext (hD d.1 d.2)
      rw [this, QuotientGroup.mk_one]
    have := congrArg iso.symm h1
    rwa [map_pow, MulEquiv.symm_apply_apply, map_one] at this
  have hbot : ∀ y : η.ker, y = 1 := by
    intro y
    obtain ⟨k, hk⟩ := hpgη y
    have h4 := hker4 y
    have h1 : orderOf y ∣ r ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf y ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have hcop : Nat.Coprime (r ^ k) 4 := by
      have : Nat.Coprime r 2 := (Nat.coprime_primes (Fact.out : r.Prime) Nat.prime_two).2 hr2
      have h4' : Nat.Coprime r 4 := by
        have := Nat.Coprime.pow_right 2 this
        simpa using this
      exact Nat.Coprime.pow_left k h4'
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) r hdvd
  have hxc : (x : L) ∈ Subgroup.center L := x.2
  have hxk : QuotientGroup.mk' Z' (x : L) ∈ η.ker := by
    rw [MonoidHom.mem_ker, hkerη]
    exact hxc
  have h1 : QuotientGroup.mk' Z' (x : L) = 1 := congrArg Subtype.val (hbot ⟨_, hxk⟩)
  have h2 : (x : L) ∈ Z' := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : Nat.Coprime (orderOf (x : L)) r := h2.2
  rw [Subgroup.orderOf_coe, hx] at h3
  exact (Fact.out : r.Prime).one_lt.ne' ((Nat.coprime_self r).1 h3)

end CFSG.ClassicalInvolution.Asc77.SCH
