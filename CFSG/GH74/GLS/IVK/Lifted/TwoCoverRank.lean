module

public import CFSG.GH74.Uniqueness.SU.SU13TA1Basic
public import CFSG.GH74.Uniqueness.SU.SU13TA1Invol
public import CFSG.GroupTheory.PRankCoprimeQuotient
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA

theorem pRank_two_congr {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y) :
    CFSG.pRank 2 X = CFSG.pRank 2 Y := CFSG.pRank_congr_of_mulEquiv e 2

theorem le_pRank_two_of_elementaryAbelian {H : Type} [Group H] [Finite H] (E : Subgroup H)
    (hE : CFSG.IsElementaryAbelian 2 E) {k : ℕ} (hk : Nat.card E = 2 ^ k) : k ≤ CFSG.pRank 2 H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

theorem isElementaryAbelian_two_of_sq_eq_one {X : Type} [Group X] {H : Subgroup X}
    (h : ∀ x ∈ H, x ^ 2 = 1) : CFSG.IsElementaryAbelian 2 H := by
  have h' : ∀ x : H, x ^ 2 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, h x x.2, Subgroup.coe_one])
  have hinv : ∀ x : H, x⁻¹ = x := fun x => by
    rw [inv_eq_iff_mul_eq_one, ← sq, h']
  have hcomm : IsMulCommutative H := ⟨⟨fun a b => by
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b * a := by rw [mul_inv_rev, hinv, hinv]⟩⟩
  exact
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one h' }

theorem card_comap_of_surjective_two {X P : Type} [Group X] [Group P] [Finite X] {f : X →* P}
    (hf : Function.Surjective f) (H : Subgroup P) :
    Nat.card (H.comap f) = Nat.card H * Nat.card f.ker := by
  let ψ : H.comap f →* H := (f.comp (H.comap f).subtype).codRestrict _ fun x => x.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hψker : ψ.ker = f.ker.subgroupOf (H.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, ← OneMemClass.coe_eq_one]
    rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, hψker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (f.ker_le_comap H)).toEquiv] at h1
  exact h1

theorem pRank_two_le_one_of_unique_involution {X : Type} [Group X] [Finite X] {u : X}
    (hu : orderOf u = 2) (h : ∀ t : X, orderOf t = 2 → t = u) : CFSG.pRank 2 X ≤ 1 := by
  apply csSup_le'
  rintro r ⟨A, hA, hcard⟩
  have hle : A ≤ Subgroup.zpowers u := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · have hx2 : x ^ 2 = 1 := by
        have := hA
        exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
      rw [h x (orderOf_eq_prime hx2 hx1)]
      exact Subgroup.mem_zpowers u
  have h1 : Nat.card A ≤ Nat.card (Subgroup.zpowers u) := Subgroup.card_le_of_le hle
  rw [hcard, Nat.card_zpowers, hu] at h1
  have h2 : 2 ^ r ≤ 2 ^ 1 := by simpa using h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

theorem one_le_pRank_two_of_involution {X : Type} [Group X] [Finite X] {u : X} (hu : orderOf u = 2) :
    1 ≤ CFSG.pRank 2 X := by
  have hsq : ∀ y ∈ Subgroup.zpowers u, y ^ 2 = 1 := by
    rintro y ⟨k, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hu, pow_orderOf_eq_one,
      one_zpow]
  refine le_pRank_two_of_elementaryAbelian (Subgroup.zpowers u)
    (isElementaryAbelian_two_of_sq_eq_one hsq) ?_
  rw [Nat.card_zpowers, hu, pow_one]

theorem pRank_two_eq_one_of_unique_involution {X : Type} [Group X] [Finite X] {u : X}
    (hu : orderOf u = 2) (h : ∀ t : X, orderOf t = 2 → t = u) : CFSG.pRank 2 X = 1 :=
  le_antisymm (pRank_two_le_one_of_unique_involution hu h) (one_le_pRank_two_of_involution hu)

theorem pRank_two_quot_eq_of_map_eq_top {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : ¬ 2 ∣ Nat.card N) (L : Subgroup X) (hL : L.map (QuotientGroup.mk' N) = ⊤) :
    CFSG.pRank 2 (X ⧸ N) = CFSG.pRank 2 L := by
  let ψ : ↥L →* X ⧸ N := (QuotientGroup.mk' N).comp L.subtype
  have hψ : Function.Surjective ψ := by
    intro y
    have hy : y ∈ L.map (QuotientGroup.mk' N) := by
      rw [hL]
      exact Subgroup.mem_top y
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨⟨l, hl⟩, rfl⟩
  have hker : ψ.ker = N.comap L.subtype := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff (l : X)
  have hkerdvd : Nat.card ψ.ker ∣ Nat.card N := by
    rw [hker]
    exact Subgroup.card_comap_dvd_of_injective N L.subtype L.subtype_injective
  have hodd : ¬ 2 ∣ Nat.card ψ.ker := fun h => hN (h.trans hkerdvd)
  have h1 : CFSG.pRank 2 (↥L ⧸ ψ.ker) = CFSG.pRank 2 ↥L :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two ψ.ker hodd
  rw [← h1]
  exact pRank_two_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm

theorem pRank_two_quot_pPrimeCore (X : Type) [Group X] [Finite X] :
    CFSG.pRank 2 (X ⧸ CFSG.pPrimeCore 2 X) = CFSG.pRank 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 CFSG.pPrimeCore_coprime_card)

private abbrev Z2Cube : Type := Fin 3 → Multiplicative (ZMod 2)

private theorem z2Cube_sq (m : Z2Cube) : m * m = 1 := by
  funext i
  have : ∀ a : Multiplicative (ZMod 2), a * a = 1 := by decide
  exact this _

private theorem z2Cube_card : Fintype.card Z2Cube = 8 := by
  simp [Fintype.card_pi, ZMod.card]

private noncomputable def z2Reg : Z2Cube →* Perm Z2Cube := MulAction.toPermHom Z2Cube Z2Cube

private theorem z2Reg_apply (a x : Z2Cube) : z2Reg a x = a * x := rfl

private theorem z2Reg_injective : Function.Injective z2Reg := by
  intro a b h
  have := congrArg (fun σ => σ 1) h
  simpa [z2Reg_apply] using this

private theorem z2Reg_cycleType {a : Z2Cube} (ha : a ≠ 1) : (z2Reg a).cycleType = {2, 2, 2, 2} := by
  have hsq : (z2Reg a) ^ 2 = 1 := by
    rw [← map_pow, pow_two, z2Cube_sq, map_one]
  have hne : z2Reg a ≠ 1 := fun h => ha (z2Reg_injective (by rw [h, map_one]))
  have hord : orderOf (z2Reg a) = 2 := orderOf_eq_prime hsq hne
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (σ := z2Reg a) (by rw [hord]; exact Nat.prime_two)
  have hsupp : (z2Reg a).support = Finset.univ := by
    ext x
    simp only [Perm.mem_support, Finset.mem_univ, iff_true, z2Reg_apply]
    intro h
    apply ha
    have := congrArg (fun y => y * x⁻¹) h
    simpa using this
  have hsum := Perm.sum_cycleType (z2Reg a)
  rw [hk, hsupp, hord, Multiset.sum_replicate, smul_eq_mul, Finset.card_univ] at hsum
  have hk3 : k = 3 := by
    have := z2Cube_card
    omega
  rw [hk, hk3, hord]
  rfl

private theorem cycleType_viaEmbeddingHom {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (ι : α ↪ β) (σ : Perm α) :
    (Equiv.Perm.viaEmbeddingHom ι σ).cycleType = σ.cycleType := by
  show (Equiv.Perm.viaEmbedding σ ι).cycleType = σ.cycleType
  unfold Equiv.Perm.viaEmbedding
  classical
  convert Equiv.Perm.cycleType_extendDomain (Equiv.ofInjective ι.1 ι.2) (g := σ) using 3

private theorem sign_eq_one_of_cycleType_two_four {n : ℕ} {σ : Perm (Fin n)}
    (h : σ.cycleType = {2, 2, 2, 2}) : Perm.sign σ = 1 := by
  rw [Perm.sign_of_cycleType, h]
  decide

theorem exists_subgroup_eight_cycleType_two_four {n : ℕ} (hn : 8 ≤ n) :
    ∃ R : Subgroup (alternatingGroup (Fin n)), Nat.card R = 8 ∧
      ∀ x ∈ R, x ≠ 1 → ((x : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2} := by
  classical
  obtain ⟨ι⟩ : Nonempty (Z2Cube ↪ Fin n) := Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fin, z2Cube_card]
    exact hn)
  let θ1 : Z2Cube →* Perm (Fin n) := (Equiv.Perm.viaEmbeddingHom ι).comp z2Reg
  have hθ1 : Function.Injective θ1 :=
    (Equiv.Perm.viaEmbeddingHom_injective ι).comp z2Reg_injective
  have hct : ∀ a : Z2Cube, a ≠ 1 → (θ1 a).cycleType = {2, 2, 2, 2} := fun a ha => by
    show (Equiv.Perm.viaEmbeddingHom ι (z2Reg a)).cycleType = _
    rw [cycleType_viaEmbeddingHom, z2Reg_cycleType ha]
  have hev : ∀ a : Z2Cube, θ1 a ∈ alternatingGroup (Fin n) := fun a => by
    by_cases ha : a = 1
    · rw [ha, map_one]
      exact one_mem _
    · exact Perm.mem_alternatingGroup.2 (sign_eq_one_of_cycleType_two_four (hct a ha))
  let θ2 : Z2Cube →* alternatingGroup (Fin n) := θ1.codRestrict _ hev
  have hθ2 : Function.Injective θ2 := fun a b h => hθ1 (congrArg Subtype.val h)
  refine ⟨θ2.range, ?_, ?_⟩
  · calc Nat.card θ2.range = Nat.card Z2Cube :=
        (Nat.card_congr (MonoidHom.ofInjective hθ2).toEquiv).symm
      _ = 8 := by rw [Nat.card_eq_fintype_card, z2Cube_card]
  · rintro _ ⟨a, rfl⟩ hne
    have ha : a ≠ 1 := fun h => hne (by rw [h, map_one])
    exact hct a ha

variable {H : Type} [Group H] {n : ℕ} {π : H →* alternatingGroup (Fin n)}

theorem four_le_pRank_of_twoCover [Finite H] (hπ : TwoCover π) (hn : 8 ≤ n) :
    4 ≤ CFSG.pRank 2 H := by
  obtain ⟨R, hRcard, hR⟩ := exists_subgroup_eight_cycleType_two_four hn
  have hcard : Nat.card (R.comap π) = 2 ^ 4 := by
    rw [card_comap_of_surjective_two hπ.surj, hRcard, hπ.card_ker]
    norm_num
  have hsq : ∀ x ∈ R.comap π, x ^ 2 = 1 := by
    intro x hx
    by_cases h1 : π x = 1
    · exact hπ.sq_eq_one_of_mem_ker' (MonoidHom.mem_ker.2 h1)
    · exact hπ.sq_eq_one_of_cycleType_two_two_two_two hn (hR _ hx h1)
  exact le_pRank_two_of_elementaryAbelian (R.comap π) (isElementaryAbelian_two_of_sq_eq_one hsq) hcard

theorem mem_ker_of_orderOf_eq_two_alt_seven {π : H →* alternatingGroup (Fin 7)} (hπ : TwoCover π)
    {x : H} (hx : orderOf x = 2) : x ∈ π.ker := by
  by_contra hxk
  have hx2 : x ^ 2 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hσ2 : ((π x : alternatingGroup (Fin 7)) : Perm (Fin 7)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hx2, map_one, OneMemClass.coe_one]
  have hσ1 : ((π x : alternatingGroup (Fin 7)) : Perm (Fin 7)) ≠ 1 := fun h =>
    hxk (by rw [MonoidHom.mem_ker]; exact Subtype.ext h)
  have hsign : Perm.sign ((π x : alternatingGroup (Fin 7)) : Perm (Fin 7)) = 1 :=
    Perm.mem_alternatingGroup.mp (π x).2
  obtain ⟨k, hk⟩ : ∃ k, ((π x : alternatingGroup (Fin 7)) : Perm (Fin 7)).cycleType =
      Multiset.replicate k 2 := ⟨_, Perm.cycleType_of_pow_prime_eq_one hσ2⟩
  have hsum := Perm.sum_cycleType_le ((π x : alternatingGroup (Fin 7)) : Perm (Fin 7))
  rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hσ1 (Perm.cycleType_eq_zero.mp hk)
  rw [Perm.sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign
  have hk3 : k ≤ 3 := by omega
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  interval_cases k
  · exact absurd hsign (by decide)
  · exact (hπ.sq_mem_ker_ne_one_of_cycleType_two_two (by omega) (x := x) hk).2 hx2
  · exact absurd hsign (by decide)

theorem pRank_eq_one_of_twoCover_seven [Finite H] {π : H →* alternatingGroup (Fin 7)}
    (hπ : TwoCover π) : CFSG.pRank 2 H = 1 := by
  obtain ⟨z, -, hz1, hz2, hzk⟩ := hπ.exists_z
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  refine pRank_two_eq_one_of_unique_involution hzo (fun t ht => ?_)
  rcases hzk t (mem_ker_of_orderOf_eq_two_alt_seven hπ ht) with h | h
  · rw [h, orderOf_one] at ht
    omega
  · exact h

end CFSG.GH74.GLS.IVK.Lifted
