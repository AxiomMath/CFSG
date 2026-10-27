module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8FrameDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

open Subgroup

variable {Y : Type*} [Group Y]

@[expose] def conjPerm (N : Subgroup Y) (S : Set Y) (hS : ∀ n ∈ N, ∀ x ∈ S, n * x * n⁻¹ ∈ S) :
    N →* Equiv.Perm S where
  toFun n :=
    { toFun := fun x => ⟨n * x * n⁻¹, hS n n.2 x x.2⟩
      invFun := fun x => ⟨n⁻¹ * x * n, by simpa using hS n⁻¹ (N.inv_mem n.2) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  map_one' := Equiv.ext fun x => Subtype.ext (by simp)
  map_mul' a b := Equiv.ext fun x => Subtype.ext (by simp [mul_assoc])

theorem conjPerm_apply (N : Subgroup Y) (S : Set Y) (hS : ∀ n ∈ N, ∀ x ∈ S, n * x * n⁻¹ ∈ S)
    (n : N) (x : S) : ((conjPerm N S hS n x : S) : Y) = (n : Y) * (x : Y) * (n : Y)⁻¹ :=
  rfl

@[expose] def invPerm (S : Set Y) (hS : ∀ x ∈ S, x⁻¹ ∈ S) : Equiv.Perm S where
  toFun x := ⟨(x : Y)⁻¹, hS x x.2⟩
  invFun x := ⟨(x : Y)⁻¹, hS x x.2⟩
  left_inv x := Subtype.ext (inv_inv (x : Y))
  right_inv x := Subtype.ext (inv_inv (x : Y))

theorem invPerm_apply (S : Set Y) (hS : ∀ x ∈ S, x⁻¹ ∈ S) (x : S) :
    ((invPerm S hS x : S) : Y) = (x : Y)⁻¹ :=
  rfl

theorem card_centralizer_invPerm (S : Set Y) (hS : ∀ x ∈ S, x⁻¹ ∈ S) (hcard : S.ncard = 6)
    (hfix : ∀ x ∈ S, x⁻¹ ≠ x) :
    Nat.card (centralizer ({invPerm S hS} : Set (Equiv.Perm S))) = 48 := by
  classical
  have hfin : Finite S := Set.finite_of_ncard_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype S := Fintype.ofFinite S
  have hS6 : Fintype.card S = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hcard]
  have hmove : ∀ x : S, invPerm S hS x ≠ x := fun x hx => hfix x x.2 (congrArg Subtype.val hx)
  have hsq : invPerm S hS ^ 2 = 1 := by
    ext x
    simp [pow_two, invPerm_apply]
  have hne : invPerm S hS ≠ 1 := by
    intro h1
    have hne : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hcard]; norm_num)
    obtain ⟨x, hx⟩ := hne
    exact hmove ⟨x, hx⟩ (by rw [h1]; rfl)
  have hord : orderOf (invPerm S hS) = 2 := orderOf_eq_prime hsq hne
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := invPerm S hS)
    (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hn
  have hsupp : (invPerm S hS).support = Finset.univ := by
    ext x
    simp [Equiv.Perm.mem_support, hmove]
  have hsum := Equiv.Perm.sum_cycleType (invPerm S hS)
  rw [hn, hsupp, Finset.card_univ, hS6, Multiset.sum_replicate] at hsum
  have hn2 : n = 2 := by simp at hsum; omega
  subst hn2
  rw [Equiv.Perm.nat_card_centralizer, hn]
  simp [hS6, Nat.factorial]

theorem FrameProps.relIndex_dvd {ν : Y → ℕ} {s : ℕ} {R J : Subgroup Y} (h : FrameProps ν s R J)
    (hJ3 : ∀ x ∈ J, x ^ 3 = 1)
    (hconj : ∀ y ∈ normalizer (J : Set Y), ∀ x ∈ J, ν (y * x * y⁻¹) = ν x)
    (hinv : ∀ x ∈ J, ν x⁻¹ = ν x) :
    (centralizer (J : Set Y)).relIndex (normalizer (J : Set Y)) ∣ 48 := by
  set S : Set Y := {x | x ∈ J ∧ ν x = s}
  have hSN : ∀ n ∈ normalizer (J : Set Y), ∀ x ∈ S, n * x * n⁻¹ ∈ S := by
    rintro n hn x ⟨hx, hνx⟩
    exact ⟨(mem_normalizer_iff.1 hn x).1 hx, by rw [hconj n hn x hx, hνx]⟩
  have hSinv : ∀ x ∈ S, x⁻¹ ∈ S := fun x ⟨hx, hνx⟩ => ⟨J.inv_mem hx, by rw [hinv x hx, hνx]⟩
  have hker : (conjPerm (normalizer (J : Set Y)) S hSN).ker =
      (centralizer (J : Set Y)).subgroupOf (normalizer (J : Set Y)) := by
    ext n
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro h1 j hj
      have hfix : ∀ x ∈ S, (n : Y) * x = x * n := by
        intro x hx
        have h2 : (n : Y) * x * (n : Y)⁻¹ = x := by
          have h3 := congrArg (fun σ : Equiv.Perm S => ((σ ⟨x, hx⟩ : S) : Y)) h1
          simpa [conjPerm_apply] using h3
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2
      have hle : J ≤ centralizer ({(n : Y)} : Set Y) := by
        refine h.le_closure.trans ((closure_le _).2 fun x hx => ?_)
        rw [SetLike.mem_coe, mem_centralizer_iff]
        rintro _ rfl
        exact hfix x hx
      exact ((mem_centralizer_iff.1 (hle hj)) n rfl).symm
    · intro hc
      refine Equiv.ext fun x => Subtype.ext ?_
      rw [conjPerm_apply, mul_inv_eq_iff_eq_mul]
      exact (hc x x.2.1).symm
  have hrange : (conjPerm (normalizer (J : Set Y)) S hSN).range ≤
      centralizer ({invPerm S hSinv} : Set (Equiv.Perm S)) := by
    rintro _ ⟨n, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ rfl
    refine Equiv.ext fun x => Subtype.ext ?_
    simp [invPerm_apply, conjPerm_apply, mul_assoc]
  have hfix : ∀ x ∈ S, x⁻¹ ≠ x := by
    rintro x ⟨hx, hνx⟩ hxx
    have hx1 : x ≠ 1 := fun h1 => h.one_ne (by rw [← h1]; exact hνx)
    have h2 : x ^ 2 = 1 := by
      calc x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := by rw [hxx]
        _ = 1 := mul_inv_cancel x
    apply hx1
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hJ3 x hx, h2]; simp
  rw [relIndex, ← hker, index_ker]
  exact (card_dvd_of_le hrange).trans
    (card_centralizer_invPerm S hSinv h.ncard_eq hfix).dvd

theorem FrameProps.eq_of_relIndex_eq_three {ν : Y → ℕ} {s : ℕ} {R J : Subgroup Y}
    (h : FrameProps ν s R J) {b : Y} (hb : b ∈ J) (hb3 : orderOf b = 3)
    (hrel : (normalizer ((zpowers b : Subgroup Y) : Set Y)).relIndex
      (normalizer (J : Set Y)) = 3) : ν b = s := by
  by_contra hne
  have hb1 : b ≠ 1 := fun h1 => by simp [h1] at hb3
  obtain ⟨m, hm, hd⟩ := h.sep b hb hb1 hne
  set N := normalizer (J : Set Y)
  set K : Subgroup N := (normalizer ((zpowers b : Subgroup Y) : Set Y)).subgroupOf N
  have hKidx : Nat.card (N ⧸ K) = 3 := hrel
  haveI : Finite (N ⧸ K) := Nat.finite_of_card_ne_zero (by rw [hKidx]; norm_num)
  have hf : Function.Injective
      (fun k : Fin 4 => (QuotientGroup.mk (⟨m k, (hm k).2⟩ : N) : N ⧸ K)) := by
    intro k l hkl
    by_contra hkl'
    rw [QuotientGroup.eq] at hkl
    obtain ⟨u, hu_def⟩ : ∃ u : Y, u = (m k)⁻¹ * m l := ⟨_, rfl⟩
    have hu : u ∈ normalizer ((zpowers b : Subgroup Y) : Set Y) := hu_def ▸ hkl
    have hconj : m l * b * (m l)⁻¹ = m k * (u * b * u⁻¹) * (m k)⁻¹ := by
      have hml : m l = m k * u := by rw [hu_def]; group
      rw [hml]
      group
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 ((mem_normalizer_iff.1 hu b).1 (mem_zpowers b))
    have hi3 : b ^ i = b ^ (i % 3) := by
      rw [← zpow_mod_orderOf b i, hb3]
      rfl
    have hb3' : b ^ 3 = 1 := hb3 ▸ pow_orderOf_eq_one b
    have hmod : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · rw [h0, zpow_zero] at hi3
      rw [hi3] at hi
      refine hb1 ?_
      calc b = u⁻¹ * (u * b * u⁻¹) * u := by group
        _ = 1 := by rw [← hi]; group
    · rw [h1, zpow_one] at hi3
      rw [hi3] at hi
      exact (hd k l hkl').1 (by rw [hconj, ← hi])
    · have hbinv : b ^ (2 : ℤ) = b⁻¹ := by
        rw [zpow_two, eq_inv_iff_mul_eq_one]
        calc b * b * b = b ^ 3 := (pow_three' b).symm
          _ = 1 := hb3'
      rw [h2, hbinv] at hi3
      rw [hi3] at hi
      exact (hd l k (Ne.symm hkl')).2 (by rw [hconj, ← hi])
  have h4 : 4 ≤ Nat.card (N ⧸ K) := by
    simpa using Nat.card_le_card_of_injective _ hf
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame
