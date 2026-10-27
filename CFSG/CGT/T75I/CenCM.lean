module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.CGT.T75I

section CenterOfMass

variable {G : Type*} [Group G]

theorem exists_fixed_of_odd_index {X A : Subgroup G}
    (hA : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hXA : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A) {u : G}
    (hu : ∀ x ∈ X, u⁻¹ * (x * u * x⁻¹) ∈ A) {S : Subgroup ↥X}
    (hS : ∀ s ∈ S, (s : G) * u * (s : G)⁻¹ = u) (hodd : Odd S.index) :
    ∃ a ∈ A, ∀ x ∈ X, x * (u * a) * x⁻¹ = u * a := by
  classical
  let _ : CommGroup ↥A := { (inferInstance : Group ↥A) with
    mul_comm := fun a b => Subtype.ext (hAc _ a.2 _ b.2) }
  have hfin : S.FiniteIndex := ⟨by obtain ⟨k, hk⟩ := hodd; omega⟩
  have : Finite (↥X ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (↥X ⧸ S) := Fintype.ofFinite _
  let f : ↥X → ↥A := fun x => ⟨u⁻¹ * (x * u * x⁻¹), hu x x.2⟩
  have hf_S : ∀ (x s : ↥X), s ∈ S → f (x * s) = f x := by
    intro x s hs
    apply Subtype.ext
    have := hS s hs
    show u⁻¹ * (((x * s : ↥X) : G) * u * ((x * s : ↥X) : G)⁻¹) = u⁻¹ * ((x : G) * u * (x : G)⁻¹)
    calc u⁻¹ * (((x * s : ↥X) : G) * u * ((x * s : ↥X) : G)⁻¹)
        = u⁻¹ * ((x : G) * ((s : G) * u * (s : G)⁻¹) * (x : G)⁻¹) := by
          simp only [Subgroup.coe_mul, mul_inv_rev]; group
      _ = _ := by rw [this]
  let F : ↥X ⧸ S → ↥A := fun q => Quotient.liftOn' q f (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab
    have := hf_S a (a⁻¹ * b) hab
    simpa using this.symm)
  have hF : ∀ y : ↥X, F (QuotientGroup.mk y) = f y := fun y => rfl
  let φ : ↥X → ↥A →* ↥A := fun x =>
    { toFun := fun a => ⟨(x : G) * a * (x : G)⁻¹, hXA x x.2 a a.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hφF : ∀ (x : ↥X) (q : ↥X ⧸ S), φ x (F q) = (f x)⁻¹ * F (x • q) := by
    intro x q
    induction q using QuotientGroup.induction_on with
    | H y =>
      apply Subtype.ext
      show (x : G) * (u⁻¹ * ((y : G) * u * (y : G)⁻¹)) * (x : G)⁻¹ =
        (u⁻¹ * ((x : G) * u * (x : G)⁻¹))⁻¹ * (u⁻¹ * (((x * y : ↥X) : G) * u * ((x * y : ↥X) : G)⁻¹))
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
  set a : ↥A := ∏ q : ↥X ⧸ S, F q with ha
  have hn : Odd (Fintype.card (↥X ⧸ S)) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact hodd
  have hfsq : ∀ x : ↥X, (f x)⁻¹ ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    have h1 := hA _ (f x).2
    have : ((f x : ↥A) : G) * ((f x : ↥A) : G) = 1 := h1
    simp only [Subgroup.coe_pow, Subgroup.coe_inv, Subgroup.coe_one]
    rw [pow_two]
    calc ((f x : ↥A) : G)⁻¹ * ((f x : ↥A) : G)⁻¹ = (((f x : ↥A) : G) * ((f x : ↥A) : G))⁻¹ := by
          group
      _ = 1 := by rw [this]; simp
  have hφa : ∀ x : ↥X, φ x a = (f x)⁻¹ * a := by
    intro x
    have h1 : φ x a = ∏ q : ↥X ⧸ S, φ x (F q) := map_prod (φ x) F Finset.univ
    have h2 : ∏ q : ↥X ⧸ S, φ x (F q) = ∏ q : ↥X ⧸ S, ((f x)⁻¹ * F (x • q)) :=
      Finset.prod_congr rfl fun q _ => hφF x q
    have h3 : ∏ q : ↥X ⧸ S, ((f x)⁻¹ * F (x • q)) =
        ((f x)⁻¹) ^ (Fintype.card (↥X ⧸ S)) * ∏ q : ↥X ⧸ S, F (x • q) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    have h4 : ∏ q : ↥X ⧸ S, F (x • q) = a := by
      rw [ha]
      exact Equiv.prod_comp (MulAction.toPerm x) F
    obtain ⟨k, hk⟩ := hn
    have h5 : ((f x)⁻¹) ^ (Fintype.card (↥X ⧸ S)) = (f x)⁻¹ := by
      rw [hk, pow_succ, pow_mul, hfsq, one_pow, one_mul]
    rw [h1, h2, h3, h4, h5]
  refine ⟨(a : G), a.2, fun x hx => ?_⟩
  have hx1 := hφa ⟨x, hx⟩
  have hx2 : x * (a : G) * x⁻¹ = (u⁻¹ * (x * u * x⁻¹))⁻¹ * (a : G) := by
    have := congrArg Subtype.val hx1
    exact this
  calc x * (u * (a : G)) * x⁻¹ = (x * u * x⁻¹) * (x * (a : G) * x⁻¹) := by group
    _ = (x * u * x⁻¹) * ((u⁻¹ * (x * u * x⁻¹))⁻¹ * (a : G)) := by rw [hx2]
    _ = u * (a : G) := by group

end CenterOfMass

theorem odd_index_centralizer_of_conj_involutions {Y : Type*} [Group Y] [Finite Y]
    (hconj : ∀ x y : Y, x ≠ 1 → x * x = 1 → y ≠ 1 → y * y = 1 → ∃ g : Y, g * x * g⁻¹ = y)
    {y : Y} (hy1 : y ≠ 1) (hy2 : y * y = 1) :
    Odd (Subgroup.centralizer ({y} : Set Y)).index := by
  classical
  have hord : orderOf y = 2 := orderOf_eq_prime (by rwa [← pow_two] at hy2) hy1
  have h2dvd : 2 ∣ Nat.card Y := hord ▸ orderOf_dvd_natCard y
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg2 : IsPGroup 2 (Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    simp
  obtain ⟨Q, hQ⟩ := hg2.exists_le_sylow
  have hyQ : y ∈ (Q : Subgroup Y) := hQ (Subgroup.mem_zpowers y)
  have hQnt : Nontrivial ↥(Q : Subgroup Y) := ⟨⟨⟨y, hyQ⟩, 1, fun h => hy1 (congrArg Subtype.val h)⟩⟩
  have hZnt : Nontrivial ↥(Subgroup.center ↥(Q : Subgroup Y)) := Q.2.center_nontrivial
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥(Q : Subgroup Y)) := Q.2.to_subgroup _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ2
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have := Nat.card_eq_one_iff_unique.1 hn
    obtain ⟨⟨a, b, hab⟩⟩ := hZnt
    exact hab (this.1.elim a b)
  have hdvdZ : 2 ∣ Nat.card ↥(Subgroup.center ↥(Q : Subgroup Y)) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥(Q : Subgroup Y))) 2 hdvdZ
  let z' : Y := ((z : ↥(Q : Subgroup Y)) : Y)
  have hz'1 : z' ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hz
    omega
  have hz'2 : z' * z' = 1 := by
    have : z ^ 2 = 1 := by
      have h0 := pow_orderOf_eq_one z
      rwa [hz] at h0
    have h2 : (z ^ 2 : ↥(Subgroup.center ↥(Q : Subgroup Y))) = z * z := pow_two z
    rw [h2] at this
    have := congrArg (fun w : ↥(Subgroup.center ↥(Q : Subgroup Y)) => ((w : ↥(Q : Subgroup Y)) : Y)) this
    simpa [z'] using this
  have hQC : (Q : Subgroup Y) ≤ Subgroup.centralizer ({z'} : Set Y) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨q, hq⟩)
    simpa [z'] using h
  have hQodd : Odd (Q : Subgroup Y).index := by
    have := Q.not_dvd_index
    exact Nat.odd_iff.2 (by omega)
  have hodd1 : Odd (Subgroup.centralizer ({z'} : Set Y)).index :=
    Odd.of_dvd_nat hQodd (Subgroup.index_dvd_of_le hQC)
  obtain ⟨g, hg⟩ := hconj z' y hz'1 hz'2 hy1 hy2
  have hmap : Subgroup.centralizer ({y} : Set Y) =
      (Subgroup.centralizer ({z'} : Set Y)).map (MulAut.conj g).toMonoidHom := by
    ext w
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    simp only [MulAut.conj_symm_apply]
    rw [← hg]
    constructor
    · intro h
      calc g⁻¹ * w * g * z' = g⁻¹ * (w * (g * z' * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * z' * g⁻¹ * w) * g := by rw [h]
        _ = z' * (g⁻¹ * w * g) := by group
    · intro h
      calc w * (g * z' * g⁻¹) = g * (g⁻¹ * w * g * z') * g⁻¹ := by group
        _ = g * (z' * (g⁻¹ * w * g)) * g⁻¹ := by rw [h]
        _ = g * z' * g⁻¹ * w := by group
  rw [hmap, Subgroup.index_map_of_bijective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).bijective]
  exact hodd1

end CFSG.CGT.T75I
