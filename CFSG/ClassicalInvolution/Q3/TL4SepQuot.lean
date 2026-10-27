module

public import CFSG.ClassicalInvolution.AschTight.S1916Omega
public import CFSG.ClassicalInvolution.Q3.TL3C1
public import CFSG.ClassicalInvolution.Q3.TL3SecOdd

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]

theorem isUniqueInvolution_map_mk (hN : Odd (Nat.card ↥N)) {K : Subgroup G} {u : G}
    (hu : IsUniqueInvolution K u) :
    IsUniqueInvolution (K.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N u) where
  mem := ⟨u, hu.mem, rfl⟩
  ne_one := by
    intro h1
    have huN : u ∈ N := (QuotientGroup.eq_one_iff u).mp h1
    have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, pow_one]
        exact orderOf_eq_prime (by rw [pow_two]; exact hu.sq) hu.ne_one)
    exact hu.ne_one (eq_one_of_isPGroup_of_mem_odd hN huN hu2)
  sq := by rw [← map_mul, hu.sq, map_one]
  unique := by
    rintro _ ⟨y, hyK, rfl⟩ hy2
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    set y₂ := y ^ b with hy₂
    have hy₂2 : y₂ ^ 2 ^ a = 1 := by
      rw [hy₂, ← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
    have himg : QuotientGroup.mk' N y₂ = QuotientGroup.mk' N y := by
      obtain ⟨c, rfl⟩ := hb
      have h2 : QuotientGroup.mk' N y ^ 2 = 1 := by rw [pow_two]; exact hy2
      rw [hy₂, map_pow, pow_succ, pow_mul, h2, one_pow, one_mul]
    have hsq : y₂ * y₂ = 1 := by
      have hN2 : y₂ * y₂ ∈ N := by
        have h1 : QuotientGroup.mk' N (y₂ * y₂) = 1 := by
          rw [map_mul, himg]
          exact hy2
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hy₂p : IsPGroup 2 (Subgroup.zpowers y₂) := by
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
          (orderOf_dvd_of_pow_eq_one hy₂2)
        exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
      refine eq_one_of_isPGroup_of_mem_odd hN hN2 (hy₂p.to_le ?_)
      exact Subgroup.zpowers_le.mpr
        (Subgroup.mul_mem _ (Subgroup.mem_zpowers y₂) (Subgroup.mem_zpowers y₂))
    rcases hu.unique y₂ (K.pow_mem hyK b) hsq with h | h
    · left
      rw [← himg, h, map_one]
    · right
      rw [← himg, h]

omit [Finite G] in
theorem closure_twoElements_map {K : Subgroup G}
    (hK : Subgroup.closure {x : G | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K) :
    Subgroup.closure {x | x ∈ K.map (QuotientGroup.mk' N) ∧ IsPGroup 2 (Subgroup.zpowers x)} =
      K.map (QuotientGroup.mk' N) := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun _ hx => hx.1) ?_
  conv_lhs => rw [← hK]
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, ⟨hxK, hx2⟩, rfl⟩
  refine Subgroup.subset_closure ⟨⟨x, hxK, rfl⟩, ?_⟩
  rw [← MonoidHom.map_zpowers]
  exact hx2.map _

theorem isPGroup_quot_map {K : Subgroup G}
    (hK : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) :
    IsPGroup 2 (↥(K.map (QuotientGroup.mk' N)) ⧸
      classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' N))) := by
  set f := QuotientGroup.mk' N
  set K' := K.map f
  have hle : (oddCoreImg K).map f ≤ oddCoreImg K' := by
    refine TC.le_oddCoreImg_of_normalizes (Subgroup.map_mono (oddCoreImg_le K)) ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩ _ ⟨o, ho, rfl⟩
      exact ⟨k * o * k⁻¹, conj_mem_oddCoreImg (Subgroup.le_normalizer hk) ho, by simp⟩
    · exact (odd_natCard_oddCoreImg K).of_dvd_nat (Subgroup.card_map_dvd _ _)
  intro q
  obtain ⟨⟨_, x, hx, rfl⟩, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥K') q
  obtain ⟨k, hk⟩ := hK (QuotientGroup.mk' (classicalInvolutionOddCore ↥K) ⟨x, hx⟩)
  refine ⟨k, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk ⊢
  have h1 : x ^ 2 ^ k ∈ oddCoreImg K := ⟨_, hk, by simp⟩
  obtain ⟨y, hy, hyx⟩ := hle ⟨_, h1, rfl⟩
  have : y = ⟨f x, ⟨x, hx, rfl⟩⟩ ^ 2 ^ k := Subtype.ext (by
    rw [Subgroup.coe_pow]
    rw [map_pow] at hyx
    exact hyx)
  rw [← this]
  exact hy

theorem quat_map (hN : Odd (Nat.card ↥N)) {K : Subgroup G} {Q : Type*} [Group Q]
    (hK : ∀ P : Subgroup G, IsSylow2In P K → Nonempty (↥P ≃* Q))
    {P' : Subgroup (G ⧸ N)} (hP' : IsSylow2In P' (K.map (QuotientGroup.mk' N))) :
    Nonempty (↥P' ≃* Q) := by
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : ⊥ ≤ K)
  have hPN : P ⊓ N = ⊥ := OddQ.inf_eq_bot_of_two hP.2.1 hN
  have hPm : IsSylow2In (P.map (QuotientGroup.mk' N)) (K.map (QuotientGroup.mk' N)) :=
    Hall196.isSylow2In_map_hom _ hP
  obtain ⟨c, -, hc⟩ := S1916.IsSylow2In.exists_conj hPm hP'
  obtain ⟨e⟩ := hK P hP
  let e₁ : ↥P' ≃* ↥(P.map (QuotientGroup.mk' N)) := (MulEquiv.subgroupCongr hc).symm.trans
    ((P.map (QuotientGroup.mk' N)).equivMapOfInjective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).symm
  exact ⟨(e₁.trans (AscQuot.quotRestrictEquiv hPN).symm).trans e⟩

end CFSG.ClassicalInvolution.Q3.TL4
