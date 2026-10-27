module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalNonsplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitPlane

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

section Lift

theorem exists_commuting_lifts_unitary [Finite K] (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 3) (hDl : D ≤ primeFormD h (idGram K n)) :
    ∃ A B : primeFormUnitary h (idGram K n), A * B = B * A ∧
      primeFormConjHom h (idGram K n) A ∈ D ∧ primeFormConjHom h (idGram K n) B ∈ D ∧
      primeFormConjHom h (idGram K n) A ≠ 1 ∧
      primeFormConjHom h (idGram K n) B ∉
        Subgroup.zpowers (primeFormConjHom h (idGram K n) A) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  set ρ := primeFormConjHom h (idGram K n) with hρ
  have hDfin : Finite D :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hD1 : D ≠ ⊥ := by
    intro h'
    rw [h', Subgroup.card_bot] at hcard
    exact absurd hcard.symm (Nat.one_lt_pow (by norm_num) hp.one_lt).ne'
  obtain ⟨⟨X, hXD⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD1
  obtain ⟨A, hA⟩ := hDl hXD
  have hlift : ∀ y : D, ∃ B : primeFormUnitary h (idGram K n), ρ B = y := fun y => hDl y.2
  let L : D → primeFormUnitary h (idGram K n) := fun y => Classical.choose (hlift y)
  have hL : ∀ y, ρ (L y) = y := fun y => Classical.choose_spec (hlift y)
  have hsc : ∀ y : D, ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c =
      (A : GL (Fin n) K) * (L y : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ *
        (L y : GL (Fin n) K)⁻¹ := by
    intro y
    have h1 : ρ (A * L y * A⁻¹ * (L y)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hA, hL, hcomm _ hXD _ y.2]
      group
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp h1
    exact ⟨c, by simpa using hc.symm⟩
  let c : D → Kˣ := fun y => Classical.choose (hsc y)
  have hc : ∀ y, GeneralLinearGroup.scalar (Fin n) (c y) =
      (A : GL (Fin n) K) * (L y : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ *
        (L y : GL (Fin n) K)⁻¹ := fun y => Classical.choose_spec (hsc y)
  have hcentral : ∀ (u : Kˣ) (M : GL (Fin n) K),
      GeneralLinearGroup.scalar (Fin n) u * M = M * GeneralLinearGroup.scalar (Fin n) u :=
    fun u M => GeneralLinearGroup.scalar_commute u M
  have hdiff : ∀ M N : primeFormUnitary h (idGram K n), ρ M = ρ N →
      ∃ s : Kˣ, GeneralLinearGroup.scalar (Fin n) s =
        (M : GL (Fin n) K) * (N : GL (Fin n) K)⁻¹ := by
    intro M N hMN
    have h1 : ρ (M * N⁻¹) = 1 := by rw [map_mul, map_inv, hMN, mul_inv_cancel]
    obtain ⟨s, -, hs⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp h1
    exact ⟨s, by simpa using hs.symm⟩
  have hcomm_scalar : ∀ (s : Kˣ) (M : GL (Fin n) K),
      (A : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) s * M) * (A : GL (Fin n) K)⁻¹ *
        (GeneralLinearGroup.scalar (Fin n) s * M)⁻¹ =
      (A : GL (Fin n) K) * M * (A : GL (Fin n) K)⁻¹ * M⁻¹ := fun s M => by
    rw [← mul_assoc (A : GL (Fin n) K), ← hcentral s (A : GL (Fin n) K)]
    calc GeneralLinearGroup.scalar (Fin n) s * (A : GL (Fin n) K) * M * (A : GL (Fin n) K)⁻¹ *
          (GeneralLinearGroup.scalar (Fin n) s * M)⁻¹
        = GeneralLinearGroup.scalar (Fin n) s * ((A : GL (Fin n) K) * M * (A : GL (Fin n) K)⁻¹ *
          M⁻¹) * (GeneralLinearGroup.scalar (Fin n) s)⁻¹ := by group
      _ = (A : GL (Fin n) K) * M * (A : GL (Fin n) K)⁻¹ * M⁻¹ := by
        rw [hcentral, mul_inv_cancel_right]
  let α : D →* Kˣ :=
    { toFun := c
      map_one' := by
        apply glScalar_injective hn0
        obtain ⟨s, hs⟩ := hdiff (L 1) 1 (by rw [hL, map_one]; rfl)
        rw [Subgroup.coe_one, inv_one, mul_one] at hs
        rw [hc, map_one, ← hs, ← mul_one (GeneralLinearGroup.scalar (Fin n) s),
          hcomm_scalar]
        group
      map_mul' := fun y z => by
        apply glScalar_injective hn0
        obtain ⟨s, hs⟩ := hdiff (L (y * z)) (L y * L z) (by
          rw [map_mul, hL, hL, hL]; rfl)
        have hLyz : (L (y * z) : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) s *
            ((L y : GL (Fin n) K) * (L z : GL (Fin n) K)) := by
          rw [Subgroup.coe_mul] at hs
          rw [hs, inv_mul_cancel_right]
        rw [map_mul, hc, hc, hc, hLyz, hcomm_scalar]
        have hz := hc z
        calc (A : GL (Fin n) K) * ((L y : GL (Fin n) K) * (L z : GL (Fin n) K)) *
              (A : GL (Fin n) K)⁻¹ * ((L y : GL (Fin n) K) * (L z : GL (Fin n) K))⁻¹
            = ((A : GL (Fin n) K) * (L y : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ *
                (L y : GL (Fin n) K)⁻¹) * ((L y : GL (Fin n) K) *
                ((A : GL (Fin n) K) * (L z : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ *
                  (L z : GL (Fin n) K)⁻¹) * (L y : GL (Fin n) K)⁻¹) := by
              group
          _ = ((A : GL (Fin n) K) * (L y : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ *
                (L y : GL (Fin n) K)⁻¹) * ((A : GL (Fin n) K) * (L z : GL (Fin n) K) *
                  (A : GL (Fin n) K)⁻¹ * (L z : GL (Fin n) K)⁻¹) := by
              rw [← hz, ← hcentral (c z) (L y : GL (Fin n) K), mul_inv_cancel_right] }
  have hle := card_le_mul_card_ker' hp (fun h' : D => Subtype.ext (hD.2 h' h'.2)) α
  have hker : p ^ 2 ≤ Nat.card α.ker := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card D ≤ p * (p ^ 2 - 1) := hle.trans (Nat.mul_le_mul_left _ (by omega))
    have h2 : p * (p ^ 2 - 1) < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left (by
      have := Nat.one_le_pow 2 p hp.pos
      omega) hp.pos
    rw [hcard, show p ^ 3 = p * p ^ 2 by ring] at h1
    omega
  obtain ⟨y, hyk, hyx⟩ : ∃ y ∈ α.ker, (y : MulAut (primeFormP h (idGram K n))) ∉
      Subgroup.zpowers X := by
    by_contra hall
    push Not at hall
    have hXp : X ^ p = 1 := hD.2 X hXD
    have : Finite (Subgroup.zpowers X) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [Nat.card_zpowers]
      exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, hXp⟩)).ne'
    have h1 := Subgroup.card_le_of_le (show α.ker ≤ (Subgroup.zpowers X).comap D.subtype from
      fun y hy => hall y hy)
    have h2 : Nat.card ((Subgroup.zpowers X).comap D.subtype) ≤ p := by
      have e1 := Subgroup.card_le_of_le (Subgroup.map_comap_le D.subtype (Subgroup.zpowers X))
      rw [Subgroup.card_map_of_injective D.subtype_injective, Nat.card_zpowers] at e1
      exact e1.trans (orderOf_le_of_pow_eq_one hp.pos hXp)
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  refine ⟨A, L y, ?_, hA ▸ hXD, (hL y).symm ▸ y.2, ?_, ?_⟩
  · have h1 : GeneralLinearGroup.scalar (Fin n) (c y) = 1 := by
      have : c y = 1 := hyk
      rw [this, map_one]
    rw [hc] at h1
    have h2 : (A : GL (Fin n) K) * (L y : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ =
        (L y : GL (Fin n) K) := mul_inv_eq_one.1 h1
    apply Subtype.ext
    calc (A : GL (Fin n) K) * (L y : GL (Fin n) K)
        = (A : GL (Fin n) K) * (L y : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ *
          (A : GL (Fin n) K) := by group
      _ = (L y : GL (Fin n) K) * (A : GL (Fin n) K) := by rw [h2]
  · rw [hA]
    exact fun h' => hx1 (Subtype.ext h')
  · rw [hA, hL]
    exact hyx


end Lift

section Scalars

theorem norm_eq_one_of_pow_norm (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) {d : Kˣ}
    (hd : h.norm ((d ^ p : Kˣ) : K) = 1) : h.norm (d : K) = 1 := by
  have := h.finite
  rw [← pow_succ_eq_one_iff_norm h] at hd ⊢
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hcardU : Nat.card Kˣ = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
    rw [Nat.card_units, h.card, show ℓ ^ (2 * f) = (ℓ ^ f) ^ 2 by rw [← pow_mul, mul_comm]]
    zify [hq1, Nat.one_le_pow 2 (ℓ ^ f) (by omega)]
    ring
  set x : Kˣ := d ^ (ℓ ^ f + 1) with hx
  have hxp : x ^ p = 1 := by rw [hx, ← pow_mul, mul_comm, pow_mul]; exact hd
  have hxq : x ^ (ℓ ^ f - 1) = 1 := by
    rw [hx, ← pow_mul, ← hcardU]
    exact pow_card_eq_one'
  have hord : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases (Nat.dvd_prime hp).mp hord with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    have h2 : p ∣ ℓ ^ f - 1 := h1 ▸ orderOf_dvd_of_pow_eq_one hxq
    have h3 : p ∣ (ℓ ^ f + 1) - (ℓ ^ f - 1) := Nat.dvd_sub hpq h2
    rw [show (ℓ ^ f + 1) - (ℓ ^ f - 1) = 2 by omega] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

theorem scalar_mem_primeFormUnitary_of_norm {u : Kˣ} (hu : h.norm (u : K) = 1) :
    (GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K) ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary]
  have hbu : h.bar (u : K) * u = 1 := by
    have : (u : K) * h.bar u = 1 := hu
    rwa [mul_comm] at this
  simp only [idGram, Units.val_one, Matrix.mul_one, GeneralLinearGroup.coe_scalar]
  rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  simp [hbu]

@[expose] def scalarU (h : UnitaryFieldData ℓ f K) (n : ℕ) (u : Kˣ) (hu : h.norm (u : K) = 1) :
    primeFormUnitary h (idGram K n) :=
  ⟨GeneralLinearGroup.scalar (Fin n) u, scalar_mem_primeFormUnitary_of_norm hu⟩

theorem coe_scalarU (u : Kˣ) (hu : h.norm (u : K) = 1) :
    ((scalarU h n u hu : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) u := rfl

theorem conjHom_scalarU (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (u : Kˣ)
    (hu : h.norm (u : K) = 1) :
    primeFormConjHom h (idGram K n) (scalarU h n u hu) = 1 :=
  (primeFormConjHom_eq_one_iff_of_ne hn hne _).mpr ⟨u, (pow_succ_eq_one_iff_norm h u).mpr hu, rfl⟩


theorem commute_scalarU (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (u : Kˣ)
    (hu : h.norm (u : K) = 1) (g : primeFormUnitary h (idGram K n)) :
    Commute (scalarU h n u hu) g :=
  commute_of_mem_ker_of_ne hn hne (conjHom_scalarU hn hne u hu) g

end Scalars

section Pair

theorem exists_nonsplit_pair_unitary (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) [Finite K] {A B : primeFormUnitary h (idGram K n)}
    (hAB : A * B = B * A) {a b : Kˣ}
    (ha : (A : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) a)
    (hb : (B : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) b) (han : h.norm (a : K) = 1)
    (hbn : h.norm (b : K) = 1) (hA1 : primeFormConjHom h (idGram K n) A ≠ 1)
    (hBA : primeFormConjHom h (idGram K n) B ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K n) A))
    (hns : ¬ ((∃ u : Kˣ, u ^ p = a) ∧ ∃ v : Kˣ, v ^ p = b)) :
    ∃ R S : primeFormUnitary h (idGram K n), R * S = S * R ∧
      (∃ c : Kˣ, (R : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c ∧
        ∀ d : Kˣ, d ^ p ≠ c) ∧ S ^ p = 1 ∧ primeFormConjHom h (idGram K n) S ≠ 1 ∧
      primeFormConjHom h (idGram K n) R ∈
        Subgroup.closure {primeFormConjHom h (idGram K n) A, primeFormConjHom h (idGram K n) B} ∧
      primeFormConjHom h (idGram K n) S ∈
        Subgroup.closure {primeFormConjHom h (idGram K n) A,
          primeFormConjHom h (idGram K n) B} := by
  have hAE : primeFormConjHom h (idGram K n) A ∈
      Subgroup.closure {primeFormConjHom h (idGram K n) A, primeFormConjHom h (idGram K n) B} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hBE : primeFormConjHom h (idGram K n) B ∈
      Subgroup.closure {primeFormConjHom h (idGram K n) A, primeFormConjHom h (idGram K n) B} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  by_cases hap : ∃ u : Kˣ, u ^ p = a
  · obtain ⟨u, rfl⟩ := hap
    have hun : h.norm (u : K) = 1 := norm_eq_one_of_pow_norm hp hp2 hpq (by simpa using han)
    have hbp : ∀ v : Kˣ, v ^ p ≠ b := fun v hv => hns ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    have hu'n : h.norm ((u⁻¹ : Kˣ) : K) = 1 := by
      simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hun
    set z := scalarU h n u⁻¹ hu'n with hz
    have hzc := commute_scalarU hn hne u⁻¹ hu'n
    have hzρ := conjHom_scalarU hn hne u⁻¹ hu'n
    refine ⟨B, z * A, ?_, ⟨b, hb, hbp⟩, ?_, ?_, hBE, ?_⟩
    · rw [← mul_assoc, ← (hzc B).eq, mul_assoc, hAB.symm, ← mul_assoc]
    · apply Subtype.ext
      have hcz : Commute (z : GL (Fin n) K) (A : GL (Fin n) K) := congrArg Subtype.val (hzc A)
      rw [Subgroup.coe_pow, Subgroup.coe_mul, hcz.mul_pow, ha]
      change (GeneralLinearGroup.scalar (Fin n) u⁻¹) ^ p *
        GeneralLinearGroup.scalar (Fin n) (u ^ p) = 1
      rw [← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]
    · rw [map_mul, hzρ, one_mul]
      exact hA1
    · rw [map_mul, hzρ, one_mul]
      exact hAE
  · push Not at hap
    obtain ⟨k, d, hbk⟩ := exists_zpow_mul_pow_of_forall_pow_ne hp hap b
    have hdp : d ^ p = b * a ^ (-k) := by
      rw [hbk, mul_comm (a ^ k) (d ^ p), mul_assoc, _root_.zpow_neg, mul_inv_cancel, mul_one]
    have hdn : h.norm (d : K) = 1 := by
      have hdp1 : (d ^ p) ^ (ℓ ^ f + 1) = 1 := by
        rw [hdp, mul_pow, (pow_succ_eq_one_iff_norm h b).mpr hbn, one_mul, ← zpow_natCast,
          ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
          (pow_succ_eq_one_iff_norm h a).mpr han, _root_.one_zpow]
      exact norm_eq_one_of_pow_norm hp hp2 hpq ((pow_succ_eq_one_iff_norm h (d ^ p)).mp hdp1)
    have hd'n : h.norm ((d⁻¹ : Kˣ) : K) = 1 := by
      simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hdn
    set z := scalarU h n d⁻¹ hd'n with hz
    have hzc := commute_scalarU hn hne d⁻¹ hd'n
    have hzρ := conjHom_scalarU hn hne d⁻¹ hd'n
    refine ⟨A, z * B * A ^ (-k), ?_, ⟨a, ha, hap⟩, ?_, ?_, hAE, ?_⟩
    · exact ((((hzc A).symm).mul_right hAB).mul_right (Commute.self_zpow A (-k))).eq
    · apply Subtype.ext
      have c0 : Commute (z : GL (Fin n) K) (A : GL (Fin n) K) := congrArg Subtype.val (hzc A)
      have c1 : Commute (z : GL (Fin n) K) (B : GL (Fin n) K) := congrArg Subtype.val (hzc B)
      have c2 : Commute (z : GL (Fin n) K) ((A : GL (Fin n) K) ^ (-k)) :=
        Commute.zpow_right c0 (-k)
      have c4 : Commute (B : GL (Fin n) K) (A : GL (Fin n) K) := congrArg Subtype.val hAB.symm
      have c3 : Commute (B : GL (Fin n) K) ((A : GL (Fin n) K) ^ (-k)) :=
        Commute.zpow_right c4 (-k)
      rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow,
        (c2.mul_left c3).mul_pow, c1.mul_pow, hb]
      have hA' : ((A : GL (Fin n) K) ^ (-k)) ^ p =
          GeneralLinearGroup.scalar (Fin n) (a ^ (-k)) := by
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ha,
          ← map_zpow]
      rw [hA']
      change (GeneralLinearGroup.scalar (Fin n) d⁻¹) ^ p * GeneralLinearGroup.scalar (Fin n) b *
        GeneralLinearGroup.scalar (Fin n) (a ^ (-k)) = 1
      rw [← map_pow, ← map_mul, ← map_mul, inv_pow, mul_assoc, ← hdp, inv_mul_cancel, map_one]
    · rw [map_mul, map_mul, hzρ, one_mul, map_zpow]
      intro h1
      apply hBA
      rw [mul_eq_one_iff_eq_inv, ← _root_.zpow_neg, neg_neg] at h1
      rw [h1]
      exact Subgroup.zpow_mem_zpowers _ _
    · rw [map_mul, map_mul, hzρ, one_mul, map_zpow]
      exact Subgroup.mul_mem _ hBE (Subgroup.zpow_mem _ hAE _)


theorem rescale_pow_eq_one (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {A : primeFormUnitary h (idGram K n)}
    {u : Kˣ} (hu'n : h.norm ((u⁻¹ : Kˣ) : K) = 1)
    (ha : (A : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) (u ^ p)) :
    (scalarU h n u⁻¹ hu'n * A) ^ p = 1 := by
  apply Subtype.ext
  have hcz : Commute ((scalarU h n u⁻¹ hu'n : primeFormUnitary h (idGram K n)) : GL (Fin n) K)
      (A : GL (Fin n) K) := congrArg Subtype.val (commute_scalarU hn hne u⁻¹ hu'n A)
  rw [Subgroup.coe_pow, Subgroup.coe_mul, hcz.mul_pow, ha]
  change (GeneralLinearGroup.scalar (Fin n) u⁻¹) ^ p *
    GeneralLinearGroup.scalar (Fin n) (u ^ p) = 1
  rw [← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]

end Pair

section Main

theorem localDeltaIn_eq_bot_of_unitary_plane (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq3 : 3 < ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {A B : primeFormUnitary h (idGram K n)} (hAB : A * B = B * A)
    (hAp : primeFormConjHom h (idGram K n) A ^ p = 1)
    (hBp : primeFormConjHom h (idGram K n) B ^ p = 1)
    (hA1 : primeFormConjHom h (idGram K n) A ≠ 1)
    (hBA : primeFormConjHom h (idGram K n) B ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K n) A))
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) :
    localDeltaIn p H (Subgroup.closure {primeFormConjHom h (idGram K n) A,
      primeFormConjHom h (idGram K n) B}) = ⊥ := by
  have := h.finite
  have hpow : ∀ {X : primeFormUnitary h (idGram K n)}, primeFormConjHom h (idGram K n) X ^ p = 1 →
      ∃ a : Kˣ, h.norm (a : K) = 1 ∧
        (X : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) a := by
    intro X hX
    have h1 : primeFormConjHom h (idGram K n) (X ^ p) = 1 := by rw [map_pow, hX]
    obtain ⟨a, ha, hA'⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp h1
    exact ⟨a, (pow_succ_eq_one_iff_norm h a).mp ha, by simpa using hA'⟩
  obtain ⟨a, han, ha⟩ := hpow hAp
  obtain ⟨b, hbn, hb⟩ := hpow hBp
  by_cases hs : (∃ u : Kˣ, u ^ p = a) ∧ ∃ v : Kˣ, v ^ p = b
  · obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := hs
    have hun : h.norm (u : K) = 1 := norm_eq_one_of_pow_norm hp hp2 hpq (by simpa using han)
    have hvn : h.norm (v : K) = 1 := norm_eq_one_of_pow_norm hp hp2 hpq (by simpa using hbn)
    have hu'n : h.norm ((u⁻¹ : Kˣ) : K) = 1 := by
      simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hun
    have hv'n : h.norm ((v⁻¹ : Kˣ) : K) = 1 := by
      simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hvn
    have hcomm : Commute (scalarU h n u⁻¹ hu'n * A) (scalarU h n v⁻¹ hv'n * B) :=
      (commute_scalarU hn hne u⁻¹ hu'n _).mul_left
        ((commute_scalarU hn hne v⁻¹ hv'n A).symm.mul_right hAB)
    have hA'ρ : primeFormConjHom h (idGram K n) (scalarU h n u⁻¹ hu'n * A) =
        primeFormConjHom h (idGram K n) A := by
      rw [map_mul, conjHom_scalarU hn hne, one_mul]
    have hB'ρ : primeFormConjHom h (idGram K n) (scalarU h n v⁻¹ hv'n * B) =
        primeFormConjHom h (idGram K n) B := by
      rw [map_mul, conjHom_scalarU hn hne, one_mul]
    have := localDeltaIn_eq_bot_of_unitary_split hn hne hq3 hp hp2 hpq
      (A := scalarU h n u⁻¹ hu'n * A) (B := scalarU h n v⁻¹ hv'n * B) hcomm.eq
      (rescale_pow_eq_one hn hne hu'n ha) (rescale_pow_eq_one hn hne hv'n hb)
      (by rw [hA'ρ]; exact hA1) (by rw [hA'ρ, hB'ρ]; exact hBA) hH
    rwa [hA'ρ, hB'ρ] at this
  · obtain ⟨R, S, hRS, ⟨c, hR, hc⟩, hS, hS1, hRE, hSE⟩ :=
      exists_nonsplit_pair_unitary hn hne hp hp2 hpq hAB ha hb han hbn hA1 hBA hs
    exact localDeltaIn_eq_bot_of_unitary_nonsplit hn hne hq3 hp hp2 hpq hRS hR hc hS hS1 hH hRE hSE


theorem localDeltaIn_eq_bot_of_le_primeFormD (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq3 : 3 < ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 3) (hDl : D ≤ primeFormD h (idGram K n))
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) :
    localDeltaIn p H D = ⊥ := by
  have := h.finite
  obtain ⟨A, B, hAB, hAD, hBD, hA1, hBA⟩ :=
    exists_commuting_lifts_unitary hn hne hp hD hcard hDl
  have hED : Subgroup.closure {primeFormConjHom h (idGram K n) A,
      primeFormConjHom h (idGram K n) B} ≤ D := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hAD
    · exact hBD
  have hbot := localDeltaIn_eq_bot_of_unitary_plane hn hne hq3 hp hp2 hpq hAB (hD.2 _ hAD)
    (hD.2 _ hBD) hA1 hBA hH
  exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans hbot.le)

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar
