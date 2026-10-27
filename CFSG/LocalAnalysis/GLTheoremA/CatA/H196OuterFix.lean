module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFEH196Card

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

private theorem h196_ker_conj (K : Type) [Group K] :
    (MulAut.conj : K →* MulAut K).ker = Subgroup.center K := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have hx : g * x * g⁻¹ = x := by
      have := congrArg (fun φ : MulAut K => φ x) h
      simpa [MulAut.conj_apply] using this
    exact ((mul_inv_eq_iff_eq_mul).mp hx).symm
  · intro h
    ext x
    show g * x * g⁻¹ = x
    rw [← h x, mul_inv_cancel_right]

private theorem h196_card_inn (K : Type) [Group K] :
    Nat.card (innerAut K) = Nat.card (K ⧸ Subgroup.center K) := by
  rw [← h196_ker_conj K]
  exact (Nat.card_congr
    (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).toEquiv).symm

private theorem h196_innerAut_normal (K : Type) [Group K] : (innerAut K).Normal := by
  unfold innerAut
  refine ⟨?_⟩
  rintro _ ⟨k, rfl⟩ φ
  refine ⟨φ k, ?_⟩
  ext y
  simp [MulAut.conj_apply]

private theorem h196_isPGroup_of_elemAbelian {K : Type} [Group K] {p : ℕ}
    {D : Subgroup (MulAut K)} (hD : CFSG.Open.IsElemAbelian p D) : IsPGroup p D := by
  unfold CFSG.Open.IsElemAbelian at hD
  obtain ⟨-, hpow⟩ := hD
  intro g
  exact ⟨1, Subtype.ext (by simpa [pow_one] using hpow _ g.2)⟩

private theorem h196_characteristic_prime (d : TauCeti.LieTypeIndex) :
    d.characteristic.Prime :=
  TauCeti.LieTypeIndex.characteristic_prime d

private theorem h196_prime_of_ambiguous_lie {p : ℕ} (d : TauCeti.LieTypeIndex) (hv : d.Valid)
    (hi : ambiguousChev p (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) : p.Prime := by
  cases d with
  | A r q =>
    rcases r with _ | _ | r
    · exact (show False from hi).elim
    · have hi' : (q.card = 7 ∧ p = 2) ∨ (q.card = 8 ∧ p = 3) := hi
      rcases hi' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
    · exact (show False from hi).elim
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | r
    · exact (show False from hi).elim
    · exact (show False from hi).elim
    · have hi' : q.card = 3 ∧ p = 2 := hi
      obtain ⟨-, rfl⟩ := hi'
      norm_num
    · have hi' : q.card = 2 ∧ p = 3 := hi
      obtain ⟨-, rfl⟩ := hi'
      norm_num
    · exact (show False from hi).elim
  | _ => exact (show False from hi).elim

private theorem h196_prime_of_chevSimple {p : ℕ} {S : Type} [Group S]
    (h : IsChevSimple p S) : p.Prime := by
  rcases h with ⟨i, hi, -⟩ | ⟨i, hi, -⟩
  · cases i with
    | cyclic r hr => exact (show False from hi).elim
    | alternating n hn => exact (show False from hi).elim
    | lie d =>
      have hc : d.1.characteristic = p := hi
      rw [← hc]
      exact h196_characteristic_prime d.1
    | sporadic s => exact (show False from hi).elim
  · cases i with
    | cyclic r hr => exact (show False from hi).elim
    | alternating n hn =>
      have hs : (n = 5 ∧ (p = 2 ∨ p = 5)) ∨ (n = 6 ∧ (p = 2 ∨ p = 3)) ∨ (n = 8 ∧ p = 2) := hi
      rcases hs with ⟨-, rfl | rfl⟩ | ⟨-, rfl | rfl⟩ | ⟨-, rfl⟩ <;> norm_num
    | lie d => exact h196_prime_of_ambiguous_lie d.1 d.2 hi
    | sporadic s => exact (show False from hi).elim

private theorem h196_normal_meets_center {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P A : Subgroup G} [hA : A.Normal] (hP : IsPGroup p P) (hAP : A ⊓ P ≠ ⊥) :
    ∃ r : G, r ∈ A ∧ r ≠ 1 ∧ r ∈ P ∧ ∀ g ∈ P, g * r = r * g := by
  haveI : Group.IsNilpotent P := IsPGroup.isNilpotent hP
  haveI : (A.subgroupOf P).Normal := hA.subgroupOf P
  have hN : A.subgroupOf P ≠ ⊥ := by
    intro h
    exact hAP (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h))
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN)
  obtain ⟨hzA, hzC⟩ := Subgroup.mem_inf.mp z.2
  refine ⟨(z.1 : G), Subgroup.mem_subgroupOf.mp hzA, ?_, z.1.2, ?_⟩
  · intro h
    apply hz
    exact Subtype.ext (Subtype.ext h)
  · intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzC ⟨g, hg⟩)

private theorem h196_central_order {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {A : Subgroup G} [hA : A.Normal] {D : Subgroup G} (hD : IsPGroup p D)
    (hpA : p ∣ Nat.card A) :
    ∃ s ∈ A ⊓ Subgroup.centralizer (D : Set G), s ≠ 1 ∧ s ^ p = 1 := by
  classical
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) p hpA
  have hyA : (y : G) ∈ A := y.2
  have hyord : orderOf (y : G) = p := by
    rw [Subgroup.orderOf_coe, hy]
  have hy1 : (y : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    exact hp.out.one_lt.ne hyord
  have hZ : IsPGroup p (Subgroup.zpowers (y : G)) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hyord, pow_one]⟩
  obtain ⟨Q, hQ⟩ := hZ.exists_le_sylow
  obtain ⟨P, hP⟩ := hD.exists_le_sylow
  haveI : Finite (Sylow p G) := Sylow.finite_of_finiteIndex P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hyQ : (y : G) ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers _)
  have hgyP : g * (y : G) * g⁻¹ ∈ (P : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul (y : G) (MulAut.conj g) (Q : Subgroup G) hyQ
  have hgyA : g * (y : G) * g⁻¹ ∈ A := hA.conj_mem _ hyA g
  have hAP : A ⊓ (P : Subgroup G) ≠ ⊥ := by
    intro h
    have hmem : g * (y : G) * g⁻¹ ∈ A ⊓ (P : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨hgyA, hgyP⟩
    rw [h, Subgroup.mem_bot] at hmem
    apply hy1
    simpa using hmem
  obtain ⟨r, hrA, hr1, hrP, hrc⟩ := h196_normal_meets_center P.isPGroup' hAP
  obtain ⟨m, hm⟩ := P.isPGroup' ⟨r, hrP⟩
  have hm' : r ^ p ^ m = 1 := by
    simpa using congrArg Subtype.val hm
  have hex : ∃ n : ℕ, r ^ p ^ n = 1 := ⟨m, hm'⟩
  have hne0 : Nat.find hex ≠ 0 := by
    intro h0
    have hs := Nat.find_spec hex
    rw [h0, pow_zero, pow_one] at hs
    exact hr1 hs
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hsp : (r ^ p ^ j) ^ p = 1 := by
    have hexp : p ^ j * p = p ^ Nat.find hex := by
      rw [hj, pow_succ]
    rw [← pow_mul, hexp]
    exact Nat.find_spec hex
  have hsne : r ^ p ^ j ≠ 1 := Nat.find_min hex (show j < Nat.find hex by omega)
  refine ⟨r ^ p ^ j, Subgroup.mem_inf.mpr ⟨A.pow_mem hrA _, ?_⟩, hsne, hsp⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hdr : Commute d r := hrc d (hP hd)
  exact (hdr.pow_right _).eq

theorem i196OuterFix_holds
    : ∀ p : ℕ, I196OuterFix p := by
  intro p
  unfold I196OuterFix
  intro K _ _ hK hchev D hD _ _
  have hp : p.Prime := h196_prime_of_chevSimple hchev
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut K) := inferInstance
  haveI : (innerAut K).Normal := h196_innerAut_normal K
  have hcard : p ∣ Nat.card (K ⧸ Subgroup.center K) :=
    I196ChevCard_holds p hp (K ⧸ Subgroup.center K) hK.2 hchev
  have hpA : p ∣ Nat.card (innerAut K) := by
    rw [h196_card_inn K]
    exact hcard
  exact h196_central_order (h196_isPGroup_of_elemAbelian hD) hpA

end CFSG.LocalAnalysis.GLTheoremA

end
