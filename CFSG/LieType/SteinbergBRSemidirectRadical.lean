module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LieType.SteinbergBR

open SemidirectProduct

variable {N S : Type*} [CommGroup N] [Group S] {φ : S →* MulAut N}

variable (φ) in
@[expose] def radPre : Subgroup (N ⋊[φ] S) :=
  (Subgroup.center S).comap rightHom

instance radPre_normal : (radPre φ).Normal :=
  Subgroup.normal_comap _

theorem inl_mem_radPre (n : N) : (inl n : N ⋊[φ] S) ∈ radPre φ := by
  change rightHom (inl n : N ⋊[φ] S) ∈ Subgroup.center S
  rw [rightHom_inl]
  exact one_mem _

@[expose] noncomputable def radPreHom : radPre φ →* Subgroup.center S :=
  (rightHom.comp (radPre φ).subtype).codRestrict _ fun x => x.2

theorem radPreHom_surjective : Function.Surjective (radPreHom (φ := φ)) := by
  rintro ⟨s, hs⟩
  have hmem : (SemidirectProduct.inr s : N ⋊[φ] S) ∈ radPre φ := by
    change SemidirectProduct.rightHom (SemidirectProduct.inr s : N ⋊[φ] S) ∈ Subgroup.center S
    rw [SemidirectProduct.rightHom_inr]
    exact hs
  exact ⟨⟨SemidirectProduct.inr s, hmem⟩,
    Subtype.ext (SemidirectProduct.rightHom_inr (N := N) (φ := φ) s)⟩

theorem mem_ker_radPreHom {x : radPre φ} : x ∈ (radPreHom (φ := φ)).ker ↔ rightHom x.1 = 1 := by
  rw [MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem isSolvable_radPre : Group.IsSolvable (radPre φ) := by
  have hcenter : Group.IsSolvable (Subgroup.center S) :=
    Group.isSolvable_of_comm fun x y => Subtype.ext (Subgroup.mem_center_iff.1 y.2 x)
  have hker : Group.IsSolvable (radPreHom (φ := φ)).ker := by
    refine Group.isSolvable_of_comm fun x y => ?_
    have hx : rightHom (x.1.1) = 1 := mem_ker_radPreHom.1 x.2
    have hy : rightHom (y.1.1) = 1 := mem_ker_radPreHom.1 y.2
    rw [← MonoidHom.mem_ker, ← range_inl_eq_ker_rightHom] at hx hy
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    apply Subtype.ext
    apply Subtype.ext
    change x.1.1 * y.1.1 = y.1.1 * x.1.1
    rw [← hm, ← hn, ← map_mul, ← map_mul, mul_comm]
  exact Group.isSolvable_of_ker_le_range (radPreHom (φ := φ)).ker.subtype radPreHom
    fun x hx => ⟨⟨x, hx⟩, rfl⟩

theorem card_radPre : Nat.card (radPre φ) = Nat.card N * Nat.card (Subgroup.center S) := by
  have h := Subgroup.card_ker_mul_card_of_surjective (radPreHom_surjective (φ := φ))
  rw [← h]
  congr 1
  have hmem : ∀ n : N, (⟨SemidirectProduct.inl n, inl_mem_radPre n⟩ : radPre φ) ∈
      (radPreHom (φ := φ)).ker := fun n => mem_ker_radPreHom.2 (rightHom_inl n)
  refine Nat.card_congr (Equiv.ofBijective (fun n : N => ⟨⟨SemidirectProduct.inl n,
    inl_mem_radPre n⟩, hmem n⟩) ⟨?_, ?_⟩).symm
  · intro m n hmn
    exact inl_injective (congrArg (fun x : (radPreHom (φ := φ)).ker => x.1.1) hmn)
  · rintro ⟨x, hx⟩
    have hx' : rightHom x.1 = 1 := mem_ker_radPreHom.1 hx
    rw [← MonoidHom.mem_ker, ← range_inl_eq_ker_rightHom] at hx'
    obtain ⟨n, hn⟩ := hx'
    exact ⟨n, Subtype.ext (Subtype.ext hn)⟩

@[expose] noncomputable def toCenterQuot : N ⋊[φ] S →* S ⧸ Subgroup.center S :=
  (QuotientGroup.mk' (Subgroup.center S)).comp rightHom

theorem toCenterQuot_surjective : Function.Surjective (toCenterQuot (φ := φ)) :=
  (QuotientGroup.mk'_surjective _).comp rightHom_surjective

theorem ker_toCenterQuot : (toCenterQuot (φ := φ)).ker = radPre φ := by
  ext x
  rw [MonoidHom.mem_ker, toCenterQuot, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  rfl

@[expose] noncomputable def quotientRadPreEquiv :
    (N ⋊[φ] S) ⧸ radPre φ ≃* S ⧸ Subgroup.center S :=
  (QuotientGroup.quotientMulEquivOfEq ker_toCenterQuot.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ toCenterQuot_surjective)

theorem solvableRadical_eq_radPre (hsimple : IsSimpleGroup (S ⧸ Subgroup.center S))
    (hns : ¬ Group.IsSolvable (S ⧸ Subgroup.center S)) :
    CFSG.solvableRadical (N ⋊[φ] S) = radPre φ := by
  refine le_antisymm (sSup_le fun M hM => ?_) (le_sSup ⟨radPre_normal, isSolvable_radPre⟩)
  obtain ⟨hMn, hMs⟩ := hM
  have hmapn : (M.map (toCenterQuot (φ := φ))).Normal := hMn.map _ toCenterQuot_surjective
  have hmaps : Group.IsSolvable (M.map (toCenterQuot (φ := φ))) :=
    Group.isSolvable_of_surjective ((toCenterQuot (φ := φ)).subgroupMap_surjective M)
  rcases hmapn.eq_bot_or_eq_top with hbot | htop
  · rw [← ker_toCenterQuot]
    exact (Subgroup.map_eq_bot_iff M).1 hbot
  · exfalso
    rw [htop] at hmaps
    apply hns
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup (S ⧸ Subgroup.center S)) ≃* _).symm.toMonoidHom)
      (MulEquiv.injective _)

theorem pCore_two_eq_bot [Finite N] {p : ℕ} [hp : Fact p.Prime] (hNp : IsPGroup p N)
    (hp2 : p ≠ 2) (hφ : Function.Injective φ) : CFSG.pCore 2 (N ⋊[φ] S) = ⊥ := by
  rw [CFSG.pCore, sSup_eq_bot]
  rintro K ⟨hKn, hK2⟩
  have hKN : ∀ n : N, (inl n : N ⋊[φ] S) ∈ K → n = 1 := by
    intro n hn
    obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.1 hK2) ⟨_, hn⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hNp) n
    rw [Subgroup.orderOf_mk, orderOf_injective inl inl_injective n, hj] at hi
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rwa [pow_zero, orderOf_eq_one_iff] at hj
    · exfalso
      have hdvd : p ∣ 2 ^ i := hi ▸ dvd_pow_self p hjpos.ne'
      have h2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1
        (hp.out.dvd_of_dvd_pow hdvd)
      exact hp2 h2
  have hcomm : ∀ k ∈ K, ∀ n : N, k * inl n = inl n * k := by
    intro k hk n
    have hrange : (inl : N →* N ⋊[φ] S).range.Normal := by
      rw [range_inl_eq_ker_rightHom]
      infer_instance
    have h1 : k * inl n * k⁻¹ * (inl n)⁻¹ ∈ K := by
      rw [show k * inl n * k⁻¹ * (inl n)⁻¹ = k * (inl n * k⁻¹ * (inl n)⁻¹) by group]
      exact K.mul_mem hk (hKn.conj_mem _ (K.inv_mem hk) (inl n))
    have h2 : k * inl n * k⁻¹ * (inl n)⁻¹ ∈ (inl : N →* N ⋊[φ] S).range :=
      Subgroup.mul_mem _ (hrange.conj_mem _ ⟨n, rfl⟩ k) (Subgroup.inv_mem _ ⟨n, rfl⟩)
    obtain ⟨m, hm⟩ := h2
    rw [← hm] at h1
    have hm1 := hKN m h1
    rw [hm1, map_one] at hm
    have hm' := hm.symm
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hm'
    exact hm'
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  have hfix : ∀ n : N, φ k.right n = n := by
    intro n
    have h := congrArg SemidirectProduct.left (hcomm k hk n)
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, left_inl, right_inl, map_one,
      MulAut.one_apply, mul_comm n] at h
    exact mul_left_cancel h
  have hs : k.right = 1 := hφ (by rw [map_one]; exact MulEquiv.ext hfix)
  have hk' : k = inl k.left := by
    rw [← inl_left_mul_inr_right k, hs, map_one, mul_one]
    rfl
  rw [hk'] at hk ⊢
  rw [hKN _ hk, map_one]

end CFSG.LieType.SteinbergBR
