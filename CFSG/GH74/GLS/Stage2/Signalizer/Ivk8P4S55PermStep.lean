module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltPerm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55SylTools
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.PermStep

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Syl

theorem exists_disjoint_sevenCycle (c : Perm (Fin 11)) (hc : c.IsThreeCycle) :
    ∃ σ : Perm (Fin 11), σ ∈ alternatingGroup (Fin 11) ∧ orderOf σ = 7 ∧ σ.Disjoint c := by
  classical
  have h3 : c.support.card = 3 := hc.card_support
  have hs : 7 ≤ (Finset.univ \ c.support).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, h3]
    omega
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hs
  have hnd : t.toList.Nodup := Finset.nodup_toList t
  have hlen : t.toList.length = 7 := by rw [Finset.length_toList, htc]
  have hcyc : t.toList.formPerm.IsCycle := List.isCycle_formPerm hnd (by omega)
  have hsupp : t.toList.formPerm.support = t := by
    rw [List.support_formPerm_of_nodup _ hnd (fun x h => by
      have := congrArg List.length h
      simp at this
      omega), Finset.toList_toFinset]
  refine ⟨t.toList.formPerm, ?_, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, hcyc.sign, hsupp, htc]
    decide
  · rw [hcyc.orderOf, hsupp, htc]
  · rw [Equiv.Perm.disjoint_iff_disjoint_support, hsupp, Finset.disjoint_left]
    intro x hx hxc
    have := hts hx
    simp at this
    exact Perm.mem_support.1 hxc this

theorem perm_step {Y : Type*} [Group Y] [Finite Y] {n e p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hne : (n = 8 ∧ e = 6) ∨ (n = 11 ∧ e = 7))
    {R X : Subgroup Y} {τ : Y} (hR : Nat.card ↥R = 2 ^ (e + 1)) (hτR : τ ∈ R)
    (hτ2 : orderOf τ = 2) (hτc : ∀ g ∈ R, g * τ = τ * g)
    (hZ : Nat.card ↥(center ↥(centralizer ({τ} : Set Y))) = 2)
    (E : (↥(centralizer ({τ} : Set Y)) ⧸ center ↥(centralizer ({τ} : Set Y))) ≃*
      alternatingGroup (Fin n))
    (hX : IsPGroup p ↥X) (hXC : X ≤ centralizer ({τ} : Set Y))
    (hN : R ≤ normalizer (X : Set Y)) {y : Y} (hy : y ∈ X) (hy1 : y ≠ 1) (hyp : y ^ p = 1) :
    n = 11 ∧ p = 3 ∧ ∃ s : Y, orderOf s = 7 ∧ y * s = s * y ∧ s * τ = τ * s := by
  classical
  set C : Subgroup Y := centralizer ({τ} : Set Y) with hC
  have hRC : R ≤ C := fun g hg => Subgroup.mem_centralizer_singleton_iff.2 (hτc g hg)
  have hτC : τ ∈ C := hRC hτR
  let τ' : ↥C := ⟨τ, hτC⟩
  have hτ'1 : τ' ≠ 1 := by
    intro h
    have h1 : τ = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hτ2
    omega
  have hτ'Z : τ' ∈ center ↥C := Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hZeq : ∀ z ∈ center ↥C, z = 1 ∨ z = τ' := fun z hz =>
    eq_one_or_eq_of_card_two hZ hτ'Z hτ'1 hz
  let π : ↥C →* Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp (E.toMonoidHom.comp (QuotientGroup.mk' (center ↥C)))
  have hπker : π.ker = center ↥C := by
    ext c
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : E (QuotientGroup.mk c) = 1 := Subtype.ext h
      have h2 : (QuotientGroup.mk c : ↥C ⧸ center ↥C) = 1 := (MulEquiv.map_eq_one_iff E).1 h1
      exact (QuotientGroup.eq_one_iff c).1 h2
    · intro h
      have h2 : (QuotientGroup.mk c : ↥C ⧸ center ↥C) = 1 := (QuotientGroup.eq_one_iff c).2 h
      have h1 : E (QuotientGroup.mk c) = 1 := by rw [h2, map_one]
      exact congrArg Subtype.val h1
  have hπA : ∀ c : ↥C, π c ∈ alternatingGroup (Fin n) := fun c => (E (QuotientGroup.mk c)).2
  let R' : Subgroup ↥C := R.subgroupOf C
  let X' : Subgroup ↥C := X.subgroupOf C
  have hR'card : Nat.card ↥R' = 2 ^ (e + 1) := by
    rw [← hR]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
  have hτ'R' : τ' ∈ R' := hτR
  have hkerR : π.ker ≤ R' := by
    rw [hπker]
    intro z hz
    rcases hZeq z hz with rfl | rfl
    · exact one_mem _
    · exact hτ'R'
  have hkcard : Nat.card ↥π.ker = 2 := by rw [hπker]; exact hZ
  have hTc : Nat.card ↥(R'.map π) = 2 ^ e := by
    have h1 := card_map_mul_card_ker π hkerR
    rw [hkcard, hR'card, pow_succ] at h1
    omega
  have hTA : R'.map π ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨r, _, rfl⟩
    exact hπA r
  have hXp' : IsPGroup p ↥X' := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXC).symm
  have hXp : IsPGroup p ↥(X'.map π) := hXp'.map π
  have hconj : ∀ r ∈ R', ∀ x ∈ X', r * x * r⁻¹ ∈ X' := by
    intro r hr x hx
    have h1 : (r : Y) ∈ R := hr
    have h2 : (x : Y) ∈ X := hx
    exact (Subgroup.mem_normalizer_iff.1 (hN h1) _).1 h2
  have hNT : R'.map π ≤ normalizer ((X'.map π : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨r * x * r⁻¹, hconj r hr x hx, by simp⟩
    · rintro ⟨x, hx, hxg⟩
      refine ⟨r⁻¹ * x * r, ?_, ?_⟩
      · simpa using hconj r⁻¹ (R'.inv_mem hr) x hx
      · have : π (r⁻¹ * x * r) = (π r)⁻¹ * π x * π r := by simp
        rw [this, hxg]
        group
  let y' : ↥C := ⟨y, hXC hy⟩
  have hy'X' : y' ∈ X' := hy
  have hcX : π y' ∈ X'.map π := ⟨y', hy'X', rfl⟩
  have hc1 : π y' ≠ 1 := by
    intro h
    have hz : y' ∈ center ↥C := by rw [← hπker]; exact h
    rcases hZeq y' hz with h1 | h1
    · apply hy1
      exact congrArg Subtype.val h1
    · have h2 : y = τ := congrArg Subtype.val h1
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hX) ⟨y, hy⟩
      have h3 : orderOf (⟨y, hy⟩ : ↥X) = orderOf y := Subgroup.orderOf_mk y hy
      rw [h3, h2, hτ2] at hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · norm_num at hk
      · have : p ∣ 2 := by
          rw [hk]
          exact dvd_pow_self p (by omega)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)
  have hne' : (n = 7 ∧ e = 3) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨ (n = 10 ∧ e = 7) ∨
      (n = 11 ∧ e = 7) := by
    rcases hne with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨hp3, hn, hthree⟩ := AltPerm.perm_core hp2 hne' hTA hTc hXp hNT hcX hc1
  have hn11 : n = 11 := by
    rcases hne with ⟨h8, -⟩ | ⟨h11, -⟩
    · rcases hn with h | h <;> omega
    · exact h11
  refine ⟨hn11, hp3, ?_⟩
  subst hn11
  subst hp3
  obtain ⟨σ, hσA, hσ7, hσd⟩ := exists_disjoint_sevenCycle (π y') hthree
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ↥C, π s₀ = σ := by
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (E.symm ⟨σ, hσA⟩)
    refine ⟨q, ?_⟩
    show ((E (QuotientGroup.mk q) : alternatingGroup (Fin 11)) : Perm (Fin 11)) = σ
    rw [hq, MulEquiv.apply_symm_apply]
  have hs₀7 : s₀ ^ 7 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hs₀, ← hσ7]
    exact pow_orderOf_eq_one σ
  obtain ⟨s, hsσ, hs7⟩ : ∃ s : ↥C, π s = σ ∧ s ^ 7 = 1 := by
    rw [hπker] at hs₀7
    rcases hZeq _ hs₀7 with h | h
    · exact ⟨s₀, hs₀, h⟩
    · refine ⟨s₀ ^ 8, by rw [map_pow, hs₀, pow_succ, ← hσ7, pow_orderOf_eq_one, one_mul], ?_⟩
      have hτ'2 : τ' ^ 2 = 1 := by
        apply Subtype.ext
        simpa using (by rw [← hτ2]; exact pow_orderOf_eq_one τ : τ ^ 2 = 1)
      calc (s₀ ^ 8) ^ 7 = (s₀ ^ 7) ^ 8 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ = 1 := by rw [h, show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, hτ'2, one_pow]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, map_one] at hsσ
    have : orderOf σ = 1 := by rw [← hsσ, orderOf_one]
    omega
  have hord : orderOf (s : Y) = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have h1 : orderOf s = 7 := orderOf_eq_prime hs7 hs1
    rw [← h1, ← Subgroup.orderOf_coe]
  refine ⟨(s : Y), hord, ?_, Subgroup.mem_centralizer_singleton_iff.1 s.2⟩
  have hcomm : π y' * π s = π s * π y' := by
    rw [hsσ]
    exact (hσd.commute.eq).symm
  have hy'3 : y' * y' * y' = 1 := by
    calc y' * y' * y' = y' ^ 3 := (pow_three' y').symm
      _ = 1 := Subtype.ext (by simpa using hyp)
  obtain ⟨z, hzdef⟩ : ∃ z : ↥C, z = y' * s * y'⁻¹ * s⁻¹ := ⟨_, rfl⟩
  have hzker : z ∈ π.ker := by
    rw [MonoidHom.mem_ker, hzdef]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have hzZ : z ∈ center ↥C := hπker ▸ hzker
  have hzc : ∀ g : ↥C, g * z = z * g := Subgroup.mem_center_iff.1 hzZ
  have hconjc : ∀ c t : ↥C, y' * c = c * y' → y' * (c * t) * y'⁻¹ = c * (y' * t * y'⁻¹) := by
    intro c t hc
    calc y' * (c * t) * y'⁻¹ = (y' * c) * t * y'⁻¹ := by group
      _ = (c * y') * t * y'⁻¹ := by rw [hc]
      _ = c * (y' * t * y'⁻¹) := by group
  have e1 : y' * s * y'⁻¹ = z * s := by rw [hzdef]; group
  have e2 : y' * (y' * s * y'⁻¹) * y'⁻¹ = z * z * s := by
    calc y' * (y' * s * y'⁻¹) * y'⁻¹ = y' * (z * s) * y'⁻¹ := by rw [e1]
      _ = z * (y' * s * y'⁻¹) := hconjc z s (hzc y')
      _ = z * z * s := by rw [e1]; group
  have e3 : y' * (y' * (y' * s * y'⁻¹) * y'⁻¹) * y'⁻¹ = z * z * z * s := by
    calc y' * (y' * (y' * s * y'⁻¹) * y'⁻¹) * y'⁻¹ = y' * (z * z * s) * y'⁻¹ := by rw [e2]
      _ = z * z * (y' * s * y'⁻¹) :=
        hconjc (z * z) s (Subgroup.mem_center_iff.1 (mul_mem hzZ hzZ) y')
      _ = z * z * z * s := by rw [e1]; group
  have hs3 : z * z * z * s = s := by
    rw [← e3]
    calc y' * (y' * (y' * s * y'⁻¹) * y'⁻¹) * y'⁻¹
        = (y' * y' * y') * s * (y' * y' * y')⁻¹ := by group
      _ = s := by rw [hy'3]; group
  have hz3 : z * z * z = 1 := by
    calc z * z * z = (z * z * z * s) * s⁻¹ := by group
      _ = s * s⁻¹ := by rw [hs3]
      _ = 1 := by group
  have hτ'2 : τ' * τ' = 1 := by
    apply Subtype.ext
    have : τ ^ 2 = 1 := by rw [← hτ2]; exact pow_orderOf_eq_one τ
    simpa [pow_two] using this
  have hz1 : z = 1 := by
    rcases hZeq z hzZ with h | h
    · exact h
    · exfalso
      rw [h] at hz3
      apply hτ'1
      calc τ' = (τ' * τ') * τ' := by rw [hτ'2, one_mul]
        _ = 1 := hz3
  have hyc : y' * s = s * y' := by
    rw [hz1] at hzdef
    calc y' * s = (y' * s * y'⁻¹ * s⁻¹) * (s * y') := by group
      _ = s * y' := by rw [← hzdef, one_mul]
  exact congrArg Subtype.val hyc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.PermStep
