module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Quasi

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.ComponentClassification CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

structure Ivk93W {J : Type} [Group J] [Finite J] (x : J) (q : ℕ) (B : Subgroup J) : Prop where
  cen : IsCentralInvolution x
  odd : Odd q
  five : 5 ≤ q
  comp : IsPCompIn 2 (centralizer ({x} : Set J)) B
  mem : x ∈ B
  sl : HasSL2Model (↥B ⧸ pPrimeCore 2 ↥B) (fun r => r = q)
  uniq : ∀ M : Subgroup J, IsPCompIn 2 (centralizer ({x} : Set J)) M → M = B

@[expose] def Ivk93WBound (J : Type) [Group J] (q : ℕ) : Prop :=
  (Nat.card J).factorization 2 ≤ (q * (q ^ 2 - 1)).factorization 2 + 3

@[expose] def Ivk93WQuat {J : Type} [Group J] (x : J) (B : Subgroup J) : Prop :=
  ∃ Q : Subgroup J, Q ≤ centralizer ({x} : Set J) ∧ x ∈ Q ∧ Nat.card ↥Q = 8 ∧
    (∃ a ∈ Q, ∃ b ∈ Q, a * a = x ∧ b * b = x ∧ a * b ≠ b * a) ∧
    ∀ a ∈ Q, ∀ b ∈ B, ⁅a, b⁆ ∈ pPrimeCoreOf 2 B

namespace Ivk93W

variable {J : Type} [Group J] [Finite J] {x : J} {q : ℕ} {B : Subgroup J}

theorem ord (h : Ivk93W x q B) : orderOf x = 2 := h.cen.1

theorem mul_self_eq_one (h : Ivk93W x q B) : x * x = 1 := by
  rw [← pow_two, ← h.ord]
  exact pow_orderOf_eq_one x

theorem ne_one (h : Ivk93W x q B) : x ≠ 1 := by
  intro h1
  have := h.ord
  rw [h1, orderOf_one] at this
  omega

theorem le (h : Ivk93W x q B) : B ≤ centralizer ({x} : Set J) := h.comp.1

theorem perfect (h : Ivk93W x q B) : Group.IsPerfect ↥B := by
  have h1 := CatalogueBAlternating.pComponent_perfect h.comp.2
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe h.le).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe h.le).surjective

theorem card (h : Ivk93W x q B) :
    Nat.card ↥B = q * (q ^ 2 - 1) * Nat.card ↥(pPrimeCore 2 ↥B) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥B), card_of_hasSL2Model h.sl]

theorem sl2_card_ge (h : Ivk93W x q B) : 120 ≤ q * (q ^ 2 - 1) := by
  have := sl2_card_mono h.five
  norm_num at this
  omega

theorem card_ge (h : Ivk93W x q B) : 120 ≤ Nat.card ↥B := by
  rw [h.card]
  have h1 : 1 ≤ Nat.card ↥(pPrimeCore 2 ↥B) := Nat.card_pos
  have h2 := h.sl2_card_ge
  nlinarith

theorem nontrivial (h : Ivk93W x q B) : Nontrivial ↥B := by
  have h1 := h.card_ge
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have := Nat.card_of_subsingleton (1 : ↥B)
  omega

theorem not_solvable (h : Ivk93W x q B) : ¬ Group.IsSolvable ↥B := by
  have := h.perfect
  have := h.nontrivial
  exact Group.IsPerfect.not_isSolvable ↥B

theorem false_of_solvable (h : Ivk93W x q B)
    (hs : Group.IsSolvable ↥(centralizer ({x} : Set J))) : False :=
  h.not_solvable (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion h.le) (Subgroup.inclusion_injective h.le))

theorem false_of_card_cent_dvd (h : Ivk93W x q B) {N : ℕ}
    (hC : Nat.card ↥(centralizer ({x} : Set J)) ∣ N)
    (hN : ∀ q : ℕ, 5 ≤ q → ¬ q * (q ^ 2 - 1) ∣ N) : False := by
  have h1 : Nat.card ↥B ∣ Nat.card ↥(centralizer ({x} : Set J)) := Subgroup.card_dvd_of_le h.le
  have h2 : q * (q ^ 2 - 1) ∣ Nat.card ↥B := ⟨_, h.card⟩
  exact hN q h.five (h2.trans (h1.trans hC))

theorem false_of_card_group (h : Ivk93W x q B) {N : ℕ} (hJ : Nat.card J ∣ N)
    (hN : ∀ q : ℕ, 5 ≤ q → ¬ q * (q ^ 2 - 1) ∣ N) : False := by
  have h1 : Nat.card ↥B ∣ Nat.card J := Subgroup.card_subgroup_dvd_card _
  have h2 : q * (q ^ 2 - 1) ∣ Nat.card ↥B := ⟨_, h.card⟩
  exact hN q h.five (h2.trans (h1.trans hJ))

theorem exists_nonabelian_two (h : Ivk93W x q B) :
    ∃ P : Subgroup J, P ≤ B ∧ IsPGroup 2 ↥P ∧ ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model h.sl
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact h.odd
  obtain ⟨Q, hQ, a, ha, b, hb, hab⟩ := sl2_exists_quaternion hodd
  obtain ⟨S', hQS'⟩ := (hQ.map e.toMonoidHom).exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective
    (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥B)) 2 S'
  have hSS' : (S : Subgroup ↥B).map (QuotientGroup.mk' (pPrimeCore 2 ↥B)) = (S' : Subgroup _) := by
    rw [← hS]
    rfl
  have hna : ∃ s ∈ (S : Subgroup ↥B), ∃ t ∈ (S : Subgroup ↥B), s * t ≠ t * s := by
    by_contra hcon
    have hcom : ∀ s ∈ (S : Subgroup ↥B), ∀ t ∈ (S : Subgroup ↥B), s * t = t * s :=
      fun s hs t ht => by
        by_contra hne
        exact hcon ⟨s, hs, t, ht, hne⟩
    apply hab
    have ha' : e a ∈ (S' : Subgroup _) := hQS' ⟨a, ha, rfl⟩
    have hb' : e b ∈ (S' : Subgroup _) := hQS' ⟨b, hb, rfl⟩
    rw [← hSS'] at ha' hb'
    obtain ⟨s, hs, hsa⟩ := ha'
    obtain ⟨t, ht, htb⟩ := hb'
    apply e.injective
    rw [map_mul, map_mul, ← hsa, ← htb]
    show QuotientGroup.mk' (pPrimeCore 2 ↥B) s * QuotientGroup.mk' (pPrimeCore 2 ↥B) t =
      QuotientGroup.mk' (pPrimeCore 2 ↥B) t * QuotientGroup.mk' (pPrimeCore 2 ↥B) s
    rw [← map_mul, ← map_mul, hcom s hs t ht]
  obtain ⟨s, hs, t, ht, hst⟩ := hna
  refine ⟨(S : Subgroup ↥B).map B.subtype, ?_, S.2.map _, (s : J), ⟨s, hs, rfl⟩, (t : J),
    ⟨t, ht, rfl⟩, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · intro hc
    exact hst (Subtype.ext hc)

theorem false_of_abelian_sylow (h : Ivk93W x q B) (hab : CFSG.Walter.HasAbelianSylowTwo J) :
    False := by
  obtain ⟨H, -, hH2, a, ha, b, hb, hab'⟩ := h.exists_nonabelian_two
  obtain ⟨P, hP⟩ := hH2.exists_le_sylow
  apply hab'
  have hc := (hab P).is_comm.comm
  exact hc ⟨a, hP ha⟩ ⟨b, hP hb⟩ |> congrArg Subtype.val

theorem normal_in (h : Ivk93W x q B) :
    (B.subgroupOf (centralizer ({x} : Set J))).Normal := by
  set C := centralizer ({x} : Set J) with hC
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr ?_
  intro c hc
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hφx : (MulAut.conj c) x = x := by
    show c * x * c⁻¹ = x
    rw [hcx]; group
  have hmapC : C.map (MulAut.conj c).toMonoidHom = C := by
    rw [hC, map_centralizer_singleton_equiv', hφx]
  have hcomp : IsPCompIn 2 C (B.map (MulAut.conj c).toMonoidHom) := by
    refine ⟨?_, ?_⟩
    · rw [← hmapC]
      exact Subgroup.map_mono h.le
    · have := (isPComponent_subgroupOf_map_iff' (MulAut.conj c) h.le).1 h.comp.2
      rwa [hmapC] at this
  have hBc := h.uniq _ hcomp
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have : c * b * c⁻¹ ∈ B.map (MulAut.conj c).toMonoidHom := ⟨b, hb, rfl⟩
    rwa [hBc] at this
  · intro hb
    rw [← hBc] at hb
    obtain ⟨u, hu, hub⟩ := hb
    have : u = b := by
      have h1 : c * u * c⁻¹ = c * b * c⁻¹ := hub
      exact mul_left_cancel (mul_right_cancel h1)
    rwa [this] at hu

theorem unique_involution (h : Ivk93W x q B) {u : J} (hu : u ∈ B) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    u = x := by
  classical
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model h.sl
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact h.odd
  have h2F : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  have hOodd : ∀ v : ↥B, v ∈ pPrimeCore 2 ↥B → v * v = 1 → v = 1 := by
    intro v hvO hv2
    have h1 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hv2)
    have h2 : orderOf v ∣ Nat.card ↥(pPrimeCore 2 ↥B) := by
      have := orderOf_dvd_natCard (⟨v, hvO⟩ : ↥(pPrimeCore 2 ↥B))
      rwa [Subgroup.orderOf_mk] at this
    have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥B)
    have h3 : orderOf v ∣ Nat.gcd 2 (Nat.card ↥(pPrimeCore 2 ↥B)) := Nat.dvd_gcd h1 h2
    rw [hcop] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have key : ∀ v : ↥B, v * v = 1 → v ≠ 1 →
      ((e.symm (QuotientGroup.mk v : ↥B ⧸ pPrimeCore 2 ↥B) : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) = -1 := by
    intro v hv2 hv1
    apply CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2F
    · rw [pow_two, ← map_mul, ← QuotientGroup.mk_mul, hv2, QuotientGroup.mk_one, map_one]
    · intro h1
      apply hv1
      have h3 : (QuotientGroup.mk v : ↥B ⧸ pPrimeCore 2 ↥B) = 1 := by
        have := congrArg e h1
        simpa using this
      exact hOodd v ((QuotientGroup.eq_one_iff v).1 h3) hv2
  set u' : ↥B := ⟨u, hu⟩ with hu'
  set x' : ↥B := ⟨x, h.mem⟩ with hx'
  have hu'2 : u' * u' = 1 := Subtype.ext hu2
  have hu'1 : u' ≠ 1 := fun h1 => hu1 (congrArg Subtype.val h1)
  have hx'2 : x' * x' = 1 := Subtype.ext h.mul_self_eq_one
  have hx'1 : x' ≠ 1 := fun h1 => h.ne_one (congrArg Subtype.val h1)
  have hmk : (QuotientGroup.mk u' : ↥B ⧸ pPrimeCore 2 ↥B) = QuotientGroup.mk x' := by
    apply e.symm.injective
    apply Subtype.ext
    rw [key u' hu'2 hu'1, key x' hx'2 hx'1]
  have hxc : x' * u' = u' * x' := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h.le hu)).symm
  have hw : u' * x' ∈ pPrimeCore 2 ↥B := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hmk, ← QuotientGroup.mk_mul, hx'2,
      QuotientGroup.mk_one]
  have hw2 : (u' * x') * (u' * x') = 1 := by
    calc (u' * x') * (u' * x') = u' * (x' * u') * x' := by group
      _ = u' * (u' * x') * x' := by rw [hxc]
      _ = (u' * u') * (x' * x') := by group
      _ = 1 := by rw [hu'2, hx'2, mul_one]
  have hw1 := hOodd _ hw hw2
  have : u' = x' := by
    have h3 : u' = x'⁻¹ := eq_inv_of_mul_eq_one_left hw1
    rw [h3]
    exact inv_eq_of_mul_eq_one_right hx'2
  exact congrArg Subtype.val this

theorem cent_two_part (h : Ivk93W x q B) :
    (Nat.card ↥(centralizer ({x} : Set J))).factorization 2 = (Nat.card J).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, P, hxP, hPc⟩ := h.cen
  have hPC : (P : Subgroup J) ≤ centralizer ({x} : Set J) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (hPc s hs)
  have h1 : Nat.card ↥(P : Subgroup J) ∣ Nat.card ↥(centralizer ({x} : Set J)) :=
    Subgroup.card_dvd_of_le hPC
  have h2 : Nat.card ↥(centralizer ({x} : Set J)) ∣ Nat.card J := Subgroup.card_subgroup_dvd_card _
  rw [Sylow.card_eq_multiplicity P] at h1
  have hC0 : Nat.card ↥(centralizer ({x} : Set J)) ≠ 0 := Nat.card_pos.ne'
  have hJ0 : Nat.card J ≠ 0 := Nat.card_pos.ne'
  apply le_antisymm
  · exact (Nat.factorization_le_iff_dvd hC0 hJ0).2 h2 2
  · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hC0).1 h1

theorem false_of_cent_card (h : Ivk93W x q B) (hB : Ivk93WBound J q) {N : ℕ}
    (hC : Nat.card ↥(centralizer ({x} : Set J)) = N)
    (hN : ∀ q : ℕ, 5 ≤ q → q * (q ^ 2 - 1) ∣ N →
      ¬ N.factorization 2 ≤ (q * (q ^ 2 - 1)).factorization 2 + 3) : False := by
  have h1 : q * (q ^ 2 - 1) ∣ N := by
    rw [← hC]
    exact dvd_trans (show q * (q ^ 2 - 1) ∣ Nat.card ↥B from ⟨_, h.card⟩)
      (Subgroup.card_dvd_of_le h.le)
  apply hN q h.five h1
  rw [← hC, h.cent_two_part]
  exact hB

theorem false_of_quasisimple_centralizer (h : Ivk93W x q B)
    (hq : CFSG.IsQuasisimple ↥(centralizer ({x} : Set J))) {N : ℕ}
    (hC : Nat.card ↥(centralizer ({x} : Set J)) = N)
    (hN : ∀ q : ℕ, 5 ≤ q → q * (q ^ 2 - 1) ∣ N →
      N.factorization 2 ≠ (q * (q ^ 2 - 1)).factorization 2) : False := by
  have hBC : B = centralizer ({x} : Set J) := ivk93x_eq_centralizer_of_pComp h.comp h.not_solvable hq
  have hcard : Nat.card ↥B = N := by rw [hBC]; exact hC
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥B)) :=
    Nat.Coprime.odd_of_left (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥B))
  have h1 : q * (q ^ 2 - 1) ∣ N := by
    rw [← hcard]
    exact ⟨_, h.card⟩
  apply hN q h.five h1
  rw [← hcard, h.card, Nat.factorization_mul]
  · have : (Nat.card ↥(pPrimeCore 2 ↥B)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro hd
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hd))
    simp [this]
  · exact (by have := h.sl2_card_ge; omega)
  · exact Nat.card_pos.ne'

end Ivk93W

end CFSG.GH74.GLS.IVK.Proofs2
