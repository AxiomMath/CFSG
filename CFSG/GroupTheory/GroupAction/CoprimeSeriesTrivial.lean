module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.SeriesPiGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CentralizerCondition

public section

namespace CFSG

open scoped Pointwise

theorem isPiGroup_singleton_two_of_isPGroup {X : Type*} [Group X] [Finite X]
    (hX : IsPGroup 2 X) : IsPiGroup ({⟨2, Nat.prime_two⟩} : Set Nat.Primes) X := by
  rw [IsPiGroup_iff]
  intro p hp
  obtain ⟨k, hk⟩ := hX.exists_card_dvd_pow
  have hdvd : p.val ∣ 2 := p.2.dvd_of_dvd_pow (hp.trans hk)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h p.2.ne_one
  · exact Subtype.ext (by simpa using h)

theorem coprime_action_trivial_of_fixed_normal_and_quotient
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G] [MulDistribMulAction A G]
    (hodd : Odd (Nat.card A)) (hG2 : IsPGroup 2 G) (N : Subgroup G) [N.Normal]
    [MulDistribMulAction A (G ⧸ N)]
    (hequiv : ∀ a : A, ∀ g : G,
      (QuotientGroup.mk' N) (a • g) = a • (QuotientGroup.mk' N) g)
    (hfixN : ∀ a : A, ∀ g : G, g ∈ N → a • g = g)
    (hfixQ : ∀ a : A, ∀ q : G ⧸ N, a • q = q) :
    ∀ a : A, ∀ g : G, a • g = g := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpiG : IsPiGroup ({⟨2, Nat.prime_two⟩} : Set Nat.Primes) G :=
    isPiGroup_singleton_two_of_isPGroup hG2
  haveI : Group.IsNilpotent G := hG2.isNilpotent
  haveI : Group.IsSolvable G := @IsNilpotent.to_isSolvable G _ (hG2.isNilpotent)
  let Gi : Fin 3 → Subgroup G := ![⊤, N, ⊥]
  let next : Fin 3 → Fin 3 := ![1, 2, 2]
  have hstab : StabilizesNormalSeries (G := G) (A := A) Gi next := by
    refine ⟨⟨0, 2, ?_, ?_, ⟨2, ?_⟩⟩, ?_, ?_, ?_, ?_⟩
    · simp [Gi]
    · simp [Gi]
    · decide
    · intro i
      fin_cases i <;> simp [Gi, next]
    · intro i
      fin_cases i
      · exact Subgroup.normal_top
      · exact ‹N.Normal›
      · exact Subgroup.normal_bot
    · intro i
      fin_cases i
      · exact ⟨fun _ _ => by simp [Gi]⟩
      · refine ⟨fun a g => ?_⟩
        constructor
        · intro hg
          rw [hfixN a g hg]
          exact hg
        · intro hg
          have h := hfixN a⁻¹ (a • g) hg
          rw [smul_smul, inv_mul_cancel, one_smul] at h
          rw [h]
          exact hg
      · refine ⟨fun a g => ?_⟩
        constructor
        · intro hg
          rw [show g = 1 from Subgroup.mem_bot.mp hg]
          exact Subgroup.mem_bot.mpr (MulDistribMulAction.smul_one a)
        · intro hg
          have h1 : a • g = 1 := Subgroup.mem_bot.mp hg
          have h := congrArg (fun x => a⁻¹ • x) h1
          rw [smul_smul, inv_mul_cancel, one_smul, smul_one] at h
          exact Subgroup.mem_bot.mpr h
    · intro i a g hg
      fin_cases i
      · change a • g * g⁻¹ ∈ N
        have h1 : (QuotientGroup.mk' N) (a • g) = (QuotientGroup.mk' N) g := by
          rw [hequiv]
          exact hfixQ a _
        have h1' : (a • g : G) / g ∈ N := by
          rw [← QuotientGroup.eq_iff_div_mem]
          simpa using h1
        simpa [div_eq_mul_inv] using h1'
      · change a • g * g⁻¹ ∈ ⊥
        rw [hfixN a g hg, mul_inv_cancel]
        exact Subgroup.one_mem _
      · change a • g * g⁻¹ ∈ ⊥
        rw [show g = 1 from Subgroup.mem_bot.mp hg, MulDistribMulAction.smul_one, one_mul,
          inv_one]
        exact Subgroup.one_mem _
  let K := fixingSubgroupOf A G (Set.univ : Set G)
  have hker : K.Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [mem_fixingSubgroup_iff] at ha ⊢
    intro x _
    calc (b * a * b⁻¹) • x = b • (a • (b⁻¹ • x)) := by rw [mul_smul, mul_smul]
      _ = b • (b⁻¹ • x) := by rw [ha _ (Set.mem_univ _)]
      _ = x := by rw [smul_smul, mul_inv_cancel, one_smul]
  have hpiQ : IsPiGroup ({⟨2, Nat.prime_two⟩} : Set Nat.Primes) (A ⧸ K) :=
    isPiGroup_quotient_fixingSubgroup_of_stabilizesNormalSeries
      ({⟨2, Nat.prime_two⟩} : Set Nat.Primes) inferInstance hpiG ⟨Fin 3, Gi, next, hstab⟩ hker
  have hK2 : IsPGroup 2 (A ⧸ K) := by
    have hpos : Nat.card (A ⧸ K) ≠ 0 := Nat.card_pos.ne'
    have huniq : ∀ {d : ℕ}, Nat.Prime d → d ∣ Nat.card (A ⧸ K) → d = 2 := by
      intro d hd hdvd
      have hmem :=
        (IsPiGroup_iff ({⟨2, Nat.prime_two⟩} : Set Nat.Primes) (A ⧸ K)).mp hpiQ ⟨d, hd⟩ hdvd
      have hmem' : (⟨d, hd⟩ : Nat.Primes) = ⟨2, Nat.prime_two⟩ :=
        Set.mem_singleton_iff.mp hmem
      exact congrArg (fun p : Nat.Primes => p.val) hmem'
    exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hpos
      (fun {d} hd hdvd => huniq hd hdvd))
  have hoddQ : Odd (Nat.card (A ⧸ K)) :=
    hodd.of_dvd_nat (Subgroup.card_quotient_dvd_card K)
  obtain ⟨k, hk⟩ := hK2.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hkne
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
    rw [pow_succ] at hk
    have heven : 2 ∣ Nat.card (A ⧸ K) := ⟨2 ^ j, by rw [hk]; ring⟩
    exact hoddQ.not_two_dvd_nat heven
  have hcard1 : Nat.card (A ⧸ K) = 1 := by rw [hk, hk0, pow_zero]
  haveI : Subsingleton (A ⧸ K) := Finite.card_le_one_iff_subsingleton.mp (by omega)
  intro a g
  have haK : a ∈ K := by
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  exact (mem_fixingSubgroup_iff (M := A) (s := Set.univ)).mp haK g (Set.mem_univ g)

theorem coprime_action_trivial_mod_of_fixed_normal_and_quotient
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G] [MulDistribMulAction A G]
    (hodd : Odd (Nat.card A)) (hG2 : IsPGroup 2 G)
    (W N : Subgroup G) [hWn : W.Normal] [hNn : N.Normal] (hWN : W ≤ N)
    (hWinv : IsInvariant A G W)
    (hNinv : IsInvariant A G N)
    (hWN_triv : ∀ a : A, ∀ m : G, m ∈ N → (a • m) * m⁻¹ ∈ W)
    (hNQ_triv : ∀ a : A, ∀ x : G, (a • x) * x⁻¹ ∈ N) :
    ∀ a : A, ∀ x : G, (a • x) * x⁻¹ ∈ W := by
  classical
  let qW := G ⧸ W
  let Nq : Subgroup qW := N.map (QuotientGroup.mk' W)
  have hNq_normal : Nq.Normal :=
    Subgroup.Normal.map hNn (QuotientGroup.mk' W) (QuotientGroup.mk'_surjective W)
  haveI : Nq.Normal := hNq_normal
  have hqG2 : IsPGroup 2 qW := by
    obtain ⟨k, hk⟩ := hG2.exists_card_eq
    refine IsPGroup.of_card_dvd_pow (p := 2) (n := k) ?_
    have h := Subgroup.card_quotient_dvd_card W
    rw [hk] at h
    exact h
  have hmemNq : ∀ x : G, QuotientGroup.mk' W x ∈ Nq ↔ x ∈ N := by
    intro x
    constructor
    · intro hx
      obtain ⟨n, hn, hxn⟩ := Subgroup.mem_map.mp hx
      obtain ⟨z, hzW, hzx⟩ := (QuotientGroup.mk'_eq_mk' (N := W)).mp hxn
      rw [← hzx]
      exact N.mul_mem hn (hWN hzW)
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hNq_inv : IsInvariant A qW Nq := by
    refine ⟨fun a q => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change ((x : G ⧸ W) ∈ Nq) ↔ (a • (x : G ⧸ W) ∈ Nq)
    rw [MulAction.Quotient.smul_mk (H := W) (b := a) (g := x)]
    constructor
    · intro hx
      exact (hmemNq (a • x)).mpr ((hNinv.invariant a x).mp ((hmemNq x).mp hx))
    · intro hx
      exact (hmemNq x).mpr ((hNinv.invariant a x).mpr ((hmemNq (a • x)).mp hx))
  haveI : IsInvariant A qW Nq := hNq_inv
  have hfixN : ∀ a : A, ∀ q : qW, q ∈ Nq → a • q = q := by
    intro a q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hxN : x ∈ N := (hmemNq x).mp hq
    have hmem : (a • x) * x⁻¹ ∈ W := hWN_triv a x hxN
    rw [MulAction.Quotient.smul_mk (H := W) (b := a) (g := x), QuotientGroup.eq_iff_div_mem,
      div_eq_mul_inv]
    exact hmem
  have hfixQ : ∀ a : A, ∀ q : qW ⧸ Nq, a • q = q := by
    intro a q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hmem : (a • x) * x⁻¹ ∈ N := hNQ_triv a x
    change a • (((x : G ⧸ W) : (G ⧸ W) ⧸ Nq)) =
      (((x : G ⧸ W) : (G ⧸ W) ⧸ Nq))
    rw [MulAction.Quotient.smul_mk (H := Nq) (b := a) (g := (x : G ⧸ W)),
      MulAction.Quotient.smul_mk (H := W) (b := a) (g := x),
      QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    have h : QuotientGroup.mk' W ((a • x) * x⁻¹) ∈ Nq :=
      (hmemNq _).mpr hmem
    simpa [QuotientGroup.mk'_apply] using h
  have htriv := coprime_action_trivial_of_fixed_normal_and_quotient
    (A := A) (G := qW) hodd hqG2 Nq
    (fun a q => (MulAction.Quotient.smul_mk (H := Nq) (b := a) (g := q)).symm)
    hfixN hfixQ
  intro a x
  have h := htriv a (QuotientGroup.mk' W x)
  change a • (x : G ⧸ W) = (x : G ⧸ W) at h
  rw [MulAction.Quotient.smul_mk (H := W) (b := a) (g := x),
    QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at h
  exact h

end CFSG

namespace CFSG

variable {G : Type*} [Group G]

theorem commutator_zpowers_le_of_mem_commutator {M W : Subgroup G} {a : G}
    (hWN : a ∈ Subgroup.normalizer (W : Set G))
    (h : ∀ m ∈ M, a * m * a⁻¹ * m⁻¹ ∈ W) :
    ∀ z ∈ Subgroup.zpowers a, ∀ m ∈ M, z * m * z⁻¹ * m⁻¹ ∈ W := by
  classical
  let A := Subgroup.zpowers a
  have hAn : A ≤ Subgroup.normalizer (W : Set G) := Subgroup.zpowers_le.mpr hWN
  let K : Subgroup A :=
    { carrier := {z | ∀ m ∈ M, (z : G) * m * (z : G)⁻¹ * m⁻¹ ∈ W}
      one_mem' := by
        intro m hm
        simpa using W.one_mem
      mul_mem' := by
        intro z₁ z₂ hz₁ hz₂ m hm
        have hz₁n : (z₁ : G) ∈ Subgroup.normalizer (W : Set G) := hAn z₁.2
        have hconj : (z₁ : G) * ((z₂ : G) * m * (z₂ : G)⁻¹ * m⁻¹) * (z₁ : G)⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp hz₁n _).mp (hz₂ m hm)
        change (z₁ : G) * (z₂ : G) * m * ((z₁ : G) * (z₂ : G))⁻¹ * m⁻¹ ∈ W
        have hcalc : (z₁ : G) * (z₂ : G) * m * ((z₁ : G) * (z₂ : G))⁻¹ * m⁻¹ =
            (z₁ : G) * ((z₂ : G) * m * (z₂ : G)⁻¹ * m⁻¹) * (z₁ : G)⁻¹ *
              ((z₁ : G) * m * (z₁ : G)⁻¹ * m⁻¹) := by group
        rw [hcalc]
        exact W.mul_mem hconj (hz₁ m hm)
      inv_mem' := by
        intro z hz m hm
        have hzn : (z : G)⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
          Subgroup.inv_mem _ (hAn z.2)
        have hconj : (z : G)⁻¹ * ((z : G) * m * (z : G)⁻¹ * m⁻¹) * ((z : G)⁻¹)⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp hzn _).mp (hz m hm)
        change (z : G)⁻¹ * m * ((z : G)⁻¹)⁻¹ * m⁻¹ ∈ W
        have hcalc : (z : G)⁻¹ * m * ((z : G)⁻¹)⁻¹ * m⁻¹ =
            ((z : G)⁻¹ * ((z : G) * m * (z : G)⁻¹ * m⁻¹) * ((z : G)⁻¹)⁻¹)⁻¹ := by
          group
        rw [hcalc]
        exact W.inv_mem hconj }
  have haK : (⟨a, Subgroup.mem_zpowers a⟩ : A) ∈ K := h
  intro z hz m hm
  have hzA : z ∈ A := hz
  have hgen : (⟨z, hzA⟩ : A) ∈ Subgroup.zpowers (⟨a, Subgroup.mem_zpowers a⟩ : A) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [show (⟨z, hzA⟩ : A) = (⟨a, Subgroup.mem_zpowers a⟩ : A) ^ n from
      Subtype.ext (by simpa using hn.symm)]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n
  exact (Subgroup.zpowers_le.mpr haK) hgen m hm

end CFSG

end
