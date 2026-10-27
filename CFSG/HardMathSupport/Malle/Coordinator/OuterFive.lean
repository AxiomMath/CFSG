module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

variable {G : Type*} [Group G]

structure OuterFiveData (P Z : Subgroup G) (φ : G) : Prop where
  comm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a
  exp : ∀ y ∈ P, y ^ 25 = 1
  le : Z ≤ P
  omega : ∀ y ∈ P, y ^ 5 = 1 → y ∈ Z
  pow_five : ∀ z ∈ Z, z ^ 5 = 1
  conj_mem : ∀ y ∈ P, φ⁻¹ * y * φ ∈ P
  conj_inv_mem : ∀ y ∈ P, φ * y * φ⁻¹ ∈ P
  centralizes : ∀ z ∈ Z, φ * z = z * φ
  fixed : ∀ y ∈ P, φ * y = y * φ → y ∈ Z
  order : φ ^ 5 = 1

theorem inv_conj_pow (a b : G) (n : ℕ) : (a⁻¹ * b * a) ^ n = a⁻¹ * b ^ n * a := by
  simpa using conj_pow (a := a⁻¹) (b := b) (i := n)

namespace OuterFiveData

variable {P Z : Subgroup G} {φ : G} (D : OuterFiveData P Z φ)
include D

theorem commute {a b : G} (ha : a ∈ P) (hb : b ∈ P) : Commute a b := D.comm a ha b hb

theorem pow_five_mem {y : G} (hy : y ∈ P) : y ^ 5 ∈ Z := by
  refine D.omega _ (P.pow_mem hy 5) ?_
  rw [← pow_mul]
  exact D.exp y hy

theorem twist_mem {p : G} (hp : p ∈ P) : p⁻¹ * (φ⁻¹ * p * φ) ∈ Z := by
  have hq := D.conj_mem p hp
  refine D.omega _ (P.mul_mem (P.inv_mem hp) hq) ?_
  have hc : Commute p⁻¹ (φ⁻¹ * p * φ) := D.commute (P.inv_mem hp) hq
  rw [hc.mul_pow, inv_pow]
  rw [inv_conj_pow]
  have hz := D.centralizes _ (D.pow_five_mem hp)
  calc (p ^ 5)⁻¹ * (φ⁻¹ * p ^ 5 * φ) = (p ^ 5)⁻¹ * (φ⁻¹ * (p ^ 5 * φ)) := by group
    _ = (p ^ 5)⁻¹ * (φ⁻¹ * (φ * p ^ 5)) := by rw [hz]
    _ = 1 := by group

theorem twist_mem_P {p : G} (hp : p ∈ P) : p⁻¹ * (φ⁻¹ * p * φ) ∈ P := D.le (D.twist_mem hp)

theorem mul_pow_eq {p : G} (hp : p ∈ P) (n : ℕ) :
    (φ * p) ^ n = φ ^ n * p ^ n * (p⁻¹ * (φ⁻¹ * p * φ)) ^ (n.choose 2) := by
  set w := p⁻¹ * (φ⁻¹ * p * φ) with hw
  have hwZ : w ∈ Z := D.twist_mem hp
  have hwφ : Commute w φ := (D.centralizes w hwZ).symm
  have hwp : Commute w p := D.commute (D.le hwZ) hp
  have hconj : ∀ m : ℕ, φ⁻¹ * p ^ m * φ = p ^ m * w ^ m := by
    intro m
    rw [← inv_conj_pow]
    have : φ⁻¹ * p * φ = p * w := by rw [hw]; group
    rw [this, (hwp.symm).mul_pow]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right]
    have h1 : p ^ n * φ = φ * (p ^ n * w ^ n) := by
      rw [← hconj n]; group
    calc φ ^ n * p ^ n * w ^ n.choose 2 * (φ * p)
        = φ ^ n * (p ^ n * φ) * w ^ n.choose 2 * p := by
          rw [mul_assoc (φ ^ n * p ^ n), ← mul_assoc (w ^ n.choose 2), ((hwφ.pow_left _)).eq]
          group
      _ = φ ^ n * (φ * (p ^ n * w ^ n)) * w ^ n.choose 2 * p := by rw [h1]
      _ = φ ^ (n + 1) * (p ^ n * (w ^ n * w ^ n.choose 2 * p)) := by
          rw [pow_succ]; group
      _ = φ ^ (n + 1) * (p ^ n * (p * w ^ (n + n.choose 2))) := by
          rw [← pow_add, ((hwp.pow_left _)).eq]
      _ = φ ^ (n + 1) * p ^ (n + 1) * w ^ (n + n.choose 2) := by
          rw [pow_succ]; group

theorem mul_pow_five {p : G} (hp : p ∈ P) : (φ * p) ^ 5 = p ^ 5 := by
  rw [D.mul_pow_eq hp 5]
  have hw := D.pow_five _ (D.twist_mem hp)
  have h10 : (5 : ℕ).choose 2 = 5 * 2 := by decide
  rw [D.order, h10, pow_mul, hw, one_pow, one_mul, mul_one]

theorem mul_pow_five_eq_one_iff {p : G} (hp : p ∈ P) : (φ * p) ^ 5 = 1 ↔ p ∈ Z := by
  rw [D.mul_pow_five hp]
  exact ⟨D.omega p hp, D.pow_five p⟩

@[expose] def twistHom : P →* Z where
  toFun p := ⟨(p : G)⁻¹ * (φ⁻¹ * p * φ), D.twist_mem p.2⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul, mul_inv_rev]
    have hA := D.conj_mem _ a.2
    have hB := D.conj_mem _ b.2
    have h1 : φ⁻¹ * ((a : G) * b) * φ = (φ⁻¹ * a * φ) * (φ⁻¹ * b * φ) := by group
    rw [h1]
    have hc : Commute ((b : G)⁻¹) ((a : G)⁻¹ * (φ⁻¹ * a * φ)) :=
      D.commute (P.inv_mem b.2) (P.mul_mem (P.inv_mem a.2) hA)
    calc (b : G)⁻¹ * (a : G)⁻¹ * ((φ⁻¹ * a * φ) * (φ⁻¹ * b * φ))
        = ((b : G)⁻¹ * ((a : G)⁻¹ * (φ⁻¹ * a * φ))) * (φ⁻¹ * b * φ) := by group
      _ = (((a : G)⁻¹ * (φ⁻¹ * a * φ)) * (b : G)⁻¹) * (φ⁻¹ * b * φ) := by rw [hc.eq]
      _ = (a : G)⁻¹ * (φ⁻¹ * a * φ) * ((b : G)⁻¹ * (φ⁻¹ * b * φ)) := by group

theorem twistHom_apply (p : P) :
    (D.twistHom p : G) = (p : G)⁻¹ * (φ⁻¹ * p * φ) := rfl

theorem mem_ker_twistHom (p : P) : p ∈ D.twistHom.ker ↔ (p : G) ∈ Z := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' : (p : G)⁻¹ * (φ⁻¹ * p * φ) = 1 := by
      have := congrArg Subtype.val h
      simpa [D.twistHom_apply] using this
    have : φ⁻¹ * p * φ = p := by
      calc φ⁻¹ * p * φ = (p : G) * ((p : G)⁻¹ * (φ⁻¹ * p * φ)) := by group
        _ = p := by rw [h', mul_one]
    refine D.fixed _ p.2 ?_
    calc φ * p = φ * (φ⁻¹ * p * φ) := by rw [this]
      _ = p * φ := by group
  · intro hz
    apply Subtype.ext
    rw [D.twistHom_apply]
    have hc := D.centralizes _ hz
    show (p : G)⁻¹ * (φ⁻¹ * p * φ) = 1
    calc (p : G)⁻¹ * (φ⁻¹ * p * φ) = (p : G)⁻¹ * (φ⁻¹ * (φ * p)) := by rw [mul_assoc φ⁻¹, hc]
      _ = 1 := by group

theorem twistHom_surjective [Finite G] (hcard : Nat.card P = Nat.card Z * Nat.card Z) :
    Function.Surjective D.twistHom := by
  have hker : Nat.card D.twistHom.ker = Nat.card Z := by
    have : D.twistHom.ker = Z.subgroupOf P := by
      ext p
      rw [D.mem_ker_twistHom, Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.le).toEquiv
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hidx : D.twistHom.ker.index = Nat.card Z := by
    have h := D.twistHom.ker.index_mul_card
    rw [hker, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right hZpos h
  have hrange : Nat.card D.twistHom.range = Nat.card Z := by
    rw [← Subgroup.index_ker, hidx]
  have htop : D.twistHom.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hrange]
  exact MonoidHom.range_eq_top.mp htop

theorem inv_conj_eq {p : G} (hp : p ∈ P) :
    p⁻¹ * φ * p = φ * (p⁻¹ * (φ⁻¹ * p * φ))⁻¹ := by
  have hc : Commute p (p⁻¹ * (φ⁻¹ * p * φ)) := D.commute hp (D.twist_mem_P hp)
  have h1 : φ⁻¹ * p * φ = p * (p⁻¹ * (φ⁻¹ * p * φ)) := by group
  calc p⁻¹ * φ * p = φ * (φ⁻¹ * p * φ)⁻¹ * p := by group
    _ = φ * (p * (p⁻¹ * (φ⁻¹ * p * φ)))⁻¹ * p := by rw [← h1]
    _ = φ * (p⁻¹ * (φ⁻¹ * p * φ))⁻¹ := by
        rw [mul_inv_rev]
        group

theorem exists_conj_eq_mul [Finite G] (hcard : Nat.card P = Nat.card Z * Nat.card Z) {z : G}
    (hz : z ∈ Z) : ∃ p ∈ P, p⁻¹ * φ * p = φ * z := by
  obtain ⟨p, hp⟩ := D.twistHom_surjective hcard ⟨z⁻¹, Z.inv_mem hz⟩
  refine ⟨p, p.2, ?_⟩
  have h := congrArg Subtype.val hp
  rw [D.twistHom_apply] at h
  rw [D.inv_conj_eq p.2, h, inv_inv]

theorem twist_mem_of_centralizer_le {K N : Subgroup G} (hNK : N ≤ K)
    (hNZ : N ≤ Subgroup.normalizer (Z : Set G))
    (hCZ : K ⊓ Subgroup.centralizer (Z : Set G) ≤ P) (hφK : ∀ k ∈ K, φ⁻¹ * k * φ ∈ K)
    {n : G} (hn : n ∈ N) : n⁻¹ * (φ⁻¹ * n * φ) ∈ P := by
  refine hCZ (Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem (hNK hn)) (hφK n (hNK hn)), ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hnz : n * z * n⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hNZ hn) z).mp hz
  have h1 := D.centralizes _ hz
  have h2 := D.centralizes _ hnz
  have hc2 : Commute (n * z * n⁻¹) φ⁻¹ := (show Commute φ (n * z * n⁻¹) from h2).symm.inv_right
  calc z * (n⁻¹ * (φ⁻¹ * n * φ))
      = n⁻¹ * ((n * z * n⁻¹) * φ⁻¹) * n * φ := by group
    _ = n⁻¹ * (φ⁻¹ * (n * z * n⁻¹)) * n * φ := by rw [hc2.eq]
    _ = n⁻¹ * φ⁻¹ * n * (z * φ) := by group
    _ = n⁻¹ * φ⁻¹ * n * (φ * z) := by rw [h1]
    _ = n⁻¹ * (φ⁻¹ * n * φ) * z := by group

theorem exists_inv_conj_eq_mul {n : G} (hn : n⁻¹ * (φ⁻¹ * n * φ) ∈ P) :
    ∃ z ∈ Z, n⁻¹ * φ * n = φ * z := by
  set π := n⁻¹ * (φ⁻¹ * n * φ) with hπ
  have heq : n⁻¹ * φ * n = φ * π⁻¹ := by rw [hπ]; group
  refine ⟨π⁻¹, ?_, heq⟩
  refine (D.mul_pow_five_eq_one_iff (P.inv_mem hn)).mp ?_
  rw [← heq, inv_conj_pow, D.order]
  group

theorem card_eq_mul_card_inf_centralizer [Finite G] {N : Subgroup G} (hPN : P ≤ N)
    (htw : ∀ n ∈ N, n⁻¹ * (φ⁻¹ * n * φ) ∈ P) (hcard : Nat.card P = Nat.card Z * Nat.card Z) :
    Nat.card N = Nat.card Z * Nat.card (N ⊓ Subgroup.centralizer ({φ} : Set G) : Subgroup G) := by
  let _ : MulAction N G := MulAction.compHom G ((MulAut.conj).comp N.subtype)
  have hsmul : ∀ (n : N) (g : G), n • g = (n : G) * g * (n : G)⁻¹ := fun _ _ => rfl
  have hstab : MulAction.stabilizer N φ =
      (N ⊓ Subgroup.centralizer ({φ} : Set G) : Subgroup G).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨n.2, ?_⟩
      calc (n : G) * φ = (n : G) * φ * (n : G)⁻¹ * n := by group
        _ = φ * n := by rw [h]
    · rintro ⟨-, h⟩
      rw [h]; group
  have horbit : MulAction.orbit N φ = (fun z => φ * z) '' (Z : Set G) := by
    ext g
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, rfl⟩
      obtain ⟨z, hz, hzeq⟩ := D.exists_inv_conj_eq_mul (htw _ (N.inv_mem n.2))
      refine ⟨z, hz, ?_⟩
      rw [hsmul]
      simp only [inv_inv] at hzeq
      exact hzeq.symm
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨p, hp, hpeq⟩ := D.exists_conj_eq_mul hcard hz
      refine ⟨⟨p⁻¹, N.inv_mem (hPN hp)⟩, ?_⟩
      rw [hsmul]
      show p⁻¹ * φ * p⁻¹⁻¹ = φ * z
      rw [inv_inv]
      exact hpeq
  have hidx := MulAction.index_stabilizer N φ
  have hZn : (Z : Set G).ncard = Nat.card Z := by rw [← Nat.card_coe_set_eq]; rfl
  rw [hstab, horbit, Set.ncard_image_of_injective _ (mul_right_injective φ), hZn] at hidx
  have h := ((N ⊓ Subgroup.centralizer ({φ} : Set G) : Subgroup G).subgroupOf N).index_mul_card
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  exact h.symm

end OuterFiveData

end CFSG.HardMathSupport.Malle.Coordinator
