module

public import CFSG.RankThree.PerfectCover.HopfCover
public import CFSG.LocalAnalysis.AGLEmbedding.KFacts

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open CFSG.RankThree.PerfectCover

theorem card_ker_pow_le {G : Type*} [CommGroup G] [Finite G] {p : ℕ}
    (h1 : Nat.card (powMonoidHom p : G →* G).ker ≤ p) :
    ∀ k : ℕ, Nat.card (powMonoidHom (p ^ k) : G →* G).ker ≤ p ^ k := by
  intro k
  induction k with
  | zero =>
    have : (powMonoidHom (p ^ 0) : G →* G).ker = ⊥ := by
      ext x
      simp
    rw [this]
    simp
  | succ k ih =>
    set A : Subgroup G := (powMonoidHom (p ^ (k + 1)) : G →* G).ker with hA
    set B : Subgroup G := (powMonoidHom (p ^ k) : G →* G).ker with hB
    have hAB : ∀ x ∈ A, x ^ p ∈ B := by
      intro x hx
      simp only [hA, MonoidHom.mem_ker, powMonoidHom_apply] at hx
      simp only [hB, MonoidHom.mem_ker, powMonoidHom_apply]
      rw [← pow_mul, mul_comm, ← pow_succ]
      exact hx
    let ψ : A →* B := ((powMonoidHom p : G →* G).comp A.subtype).codRestrict B
      (fun x => hAB x x.2)
    have hk := Subgroup.card_ker_mul_card_range ψ
    have h2 : Nat.card ψ.ker ≤ p := by
      have hx : ∀ x : ψ.ker, ((x.1 : A) : G) ^ p = 1 := fun x => by
        have h0 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
        exact h0
      refine le_trans (Nat.card_le_card_of_injective
        (fun x : ψ.ker => (⟨((x.1 : A) : G), by
          rw [MonoidHom.mem_ker, powMonoidHom_apply]; exact hx x⟩ :
            (powMonoidHom p : G →* G).ker)) ?_) h1
      intro x y hxy
      have := congrArg (fun z : (powMonoidHom p : G →* G).ker => z.1) hxy
      exact Subtype.ext (Subtype.ext this)
    have h3 : Nat.card ψ.range ≤ p ^ k :=
      le_trans (Nat.card_le_card_of_injective (fun x : ψ.range => x.1) Subtype.val_injective) ih
    calc Nat.card A = Nat.card ψ.ker * Nat.card ψ.range := hk.symm
      _ ≤ p * p ^ k := Nat.mul_le_mul h2 h3
      _ = p ^ (k + 1) := by ring

theorem eq_of_card_quotient_eq {G : Type*} [Group G] [Finite G] (hcomm : ∀ a b : G, a * b = b * a)
    {p e : ℕ} (hp : p.Prime) (h1 : Nat.card {x : G // x ^ p = 1} ≤ p) {N N' : Subgroup G}
    (hN : Nat.card (G ⧸ N) = p ^ e) (hN' : Nat.card (G ⧸ N') = p ^ e) : N = N' := by
  let _ : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  have h1' : Nat.card (powMonoidHom p : G →* G).ker ≤ p :=
    le_trans (le_of_eq (Nat.card_congr
      (Equiv.subtypeEquivRight fun x => by simp [MonoidHom.mem_ker]))) h1
  have key : ∀ M : Subgroup G, Nat.card (G ⧸ M) = p ^ e →
      M = (powMonoidHom (p ^ e) : G →* G).range := by
    intro M hM
    have hle : (powMonoidHom (p ^ e) : G →* G).range ≤ M := by
      rintro _ ⟨y, rfl⟩
      have h := pow_card_eq_one' (G := G ⧸ M) (x := (y : G ⧸ M))
      rw [hM, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
      exact h
    have hk := Subgroup.card_ker_mul_card_range (powMonoidHom (p ^ e) : G →* G)
    have hker := card_ker_pow_le h1' e
    have hM1 : Nat.card M * p ^ e = Nat.card G := by
      rw [← hM, ← Subgroup.index_eq_card]
      exact Subgroup.card_mul_index M
    have hpos : 0 < p ^ e := pow_pos hp.pos e
    have hcard : Nat.card M ≤ Nat.card (powMonoidHom (p ^ e) : G →* G).range := by
      by_contra hlt
      push Not at hlt
      have : Nat.card (powMonoidHom (p ^ e) : G →* G).range * p ^ e < Nat.card M * p ^ e :=
        Nat.mul_lt_mul_of_pos_right hlt hpos
      have h2 : Nat.card (powMonoidHom (p ^ e) : G →* G).ker *
          Nat.card (powMonoidHom (p ^ e) : G →* G).range ≤
          p ^ e * Nat.card (powMonoidHom (p ^ e) : G →* G).range :=
        Nat.mul_le_mul_right _ hker
      nlinarith
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  rw [key N hN, key N' hN']

theorem exists_mulAut_lift {K X : Type} [Group K] [Finite K] [Group X] [Group.IsPerfect K]
    (π : K →* X) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    {p e : ℕ} (hp : p.Prime) (hcard : Nat.card π.ker = p ^ e)
    [Finite (hopfMultiplier X)]
    (hM : Nat.card {m : hopfMultiplier X // m ^ p = 1} ≤ p) (α : MulAut X) :
    ∃ α' : MulAut K, ∀ k, π (α' k) = α (π k) := by
  have : Finite X := Finite.of_surjective π hπ
  have : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := π) hπ
  let π' : K →* X := (α.symm : X ≃* X).toMonoidHom.comp π
  have hπ' : Function.Surjective π' := α.symm.surjective.comp hπ
  have hker' : π'.ker = π.ker := by
    ext x
    simp [π', MonoidHom.mem_ker]
  obtain ⟨-, h, hh, -, hsurj, -, eh, -⟩ :=
    perfect_central_kernel_quotient_of_hopf_multiplier π hπ hker
  obtain ⟨-, h', hh', -, hsurj', -, eh', -⟩ :=
    perfect_central_kernel_quotient_of_hopf_multiplier π' hπ' (hker'.symm ▸ hker)
  have hcomm : ∀ a b : hopfMultiplier X, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hopfMultiplier_le_center a.2) b.1).symm
  have hN : Nat.card (hopfMultiplier X ⧸ (h.comp (hopfMultiplier X).subtype).ker) = p ^ e :=
    (Nat.card_congr eh.toEquiv).trans hcard
  have hN' : Nat.card (hopfMultiplier X ⧸ (h'.comp (hopfMultiplier X).subtype).ker) = p ^ e :=
    (Nat.card_congr eh'.toEquiv).trans (by rw [hker']; exact hcard)
  have hNN := eq_of_card_quotient_eq hcomm hp hM hN hN'
  have hρ : ∀ x : HopfCover X, π (h x) = hopfCoverMap X x := fun x => congrArg (· x) hh
  have hρ' : ∀ x : HopfCover X, α.symm (π (h' x)) = hopfCoverMap X x := fun x =>
    congrArg (· x) hh'
  have hmemM : ∀ x : HopfCover X, π (h x) = 1 → x ∈ hopfMultiplier X := fun x hx => by
    show hopfCoverMap X x = 1
    rw [← hρ x, hx]
  have hmemM' : ∀ x : HopfCover X, π (h' x) = 1 → x ∈ hopfMultiplier X := fun x hx => by
    show hopfCoverMap X x = 1
    rw [← hρ' x, hx, map_one]
  have hle : ∀ x, h x = 1 → h' x = 1 := by
    intro x hx
    have hxM : x ∈ hopfMultiplier X := hmemM x (by rw [hx, map_one])
    have : (⟨x, hxM⟩ : hopfMultiplier X) ∈ (h.comp (hopfMultiplier X).subtype).ker := hx
    rw [hNN] at this
    exact this
  have hle' : ∀ x, h' x = 1 → h x = 1 := by
    intro x hx
    have hxM : x ∈ hopfMultiplier X := hmemM' x (by rw [hx, map_one])
    have : (⟨x, hxM⟩ : hopfMultiplier X) ∈ (h'.comp (hopfMultiplier X).subtype).ker := hx
    rw [← hNN] at this
    exact this
  let φ : K →* K := MonoidHom.liftOfSurjective h hsurj ⟨h', fun x hx => hle x hx⟩
  let ψ : K →* K := MonoidHom.liftOfSurjective h' hsurj' ⟨h, fun x hx => hle' x hx⟩
  have hφ : ∀ x, φ (h x) = h' x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply h (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨h', fun x hx => hle x hx⟩ x
  have hψ : ∀ x, ψ (h' x) = h x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply h' (Function.surjInv hsurj')
      (Function.rightInverse_surjInv hsurj') ⟨h, fun x hx => hle' x hx⟩ x
  let a : K ≃* K := MonoidHom.toMulEquiv φ ψ
    (MonoidHom.ext fun k => by
      obtain ⟨x, rfl⟩ := hsurj k
      simp [hψ, hφ])
    (MonoidHom.ext fun k => by
      obtain ⟨x, rfl⟩ := hsurj' k
      simp [hψ, hφ])
  refine ⟨a, fun k => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj k
  have h1 : (a (h x)) = h' x := hφ x
  rw [h1, hρ x]
  have := hρ' x
  rw [← this]
  simp

theorem pow_lift_apply {K X : Type} [Group K] [Group X] (π : K →* X) {α : MulAut X}
    {α' : MulAut K} (h : ∀ k, π (α' k) = α (π k)) (n : ℕ) (k : K) :
    π ((α' ^ n) k) = (α ^ n) (π k) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, h]

theorem not_kOutTwoGroup_of_diagOuter {K X : Type} [Group K] [Finite K] [Group X]
    [Group.IsPerfect K] (π : K →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) {p e : ℕ} (hp : p.Prime) (hcard : Nat.card π.ker = p ^ e)
    [Finite (hopfMultiplier X)] (hM : Nat.card {m : hopfMultiplier X // m ^ p = 1} ≤ p)
    (hdiag : ∃ α : MulAut X, ∀ k : ℕ, α ^ (2 ^ k) ∉ (MulAut.conj : X →* MulAut X).range) :
    ¬ KOutTwoGroup K := by
  obtain ⟨α, hα⟩ := hdiag
  obtain ⟨α', hα'⟩ := exists_mulAut_lift π hπ hker hp hcard hM α
  intro hout
  obtain ⟨k, g, hg⟩ := hout α'
  refine hα k ⟨π g, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := hπ y
  have h1 := pow_lift_apply π hα' (2 ^ k) x
  rw [← hg] at h1
  simpa using h1

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
