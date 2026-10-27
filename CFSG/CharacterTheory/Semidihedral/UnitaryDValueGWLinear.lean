module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueGWCycle
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourSelfCentralizer

public section

open scoped Classical

namespace CFSG.Semidihedral.UnitaryDValue.GW

open CFSG.GorensteinWalter

variable {X : Type*} [Group X]

theorem factorization_two_card_of_odd_index [Finite X] {L : Subgroup X} (hL : Odd L.index) :
    (Nat.card L).factorization 2 = (Nat.card X).factorization 2 := by
  rw [← L.card_mul_index, Nat.factorization_mul Nat.card_pos.ne' (Nat.pos_of_ne_zero
      (fun h => by rw [h] at hL; exact absurd hL (by decide))).ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hL)
      (even_iff_two_dvd.mpr h)), add_zero]

theorem mem_of_odd_index {L : Subgroup X} [L.Normal] (hL : Odd L.index) {v : X} {k : ℕ}
    (hv : orderOf v = 2 ^ k) : v ∈ L := by
  have h1 : orderOf (QuotientGroup.mk' L v) ∣ 2 ^ k := hv ▸ orderOf_map_dvd _ v
  have h2 : orderOf (QuotientGroup.mk' L v) ∣ L.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hi0 : i = 0 := by
    by_contra hne
    have h2' : 2 ∣ L.index := (dvd_pow_self 2 hne).trans (hi ▸ h2)
    exact (Nat.not_even_iff_odd.mpr hL) (even_iff_two_dvd.mpr h2')
  rw [hi0, pow_zero, orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hi
  exact hi

theorem eq_one_of_commute_of_psl2
    {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {L : Subgroup X} (eL : L ≃* PSL2 F) {V : Subgroup X}
    (hV : IsKleinFour V) (hVL : V ≤ L) {y : X} (hyL : y ∈ L) (hyV : ∀ v ∈ V, y * v = v * y)
    (hy : Odd (orderOf y)) : y = 1 := by
  by_contra hy1
  let y' : L := ⟨y, hyL⟩
  let eV : V ≃* (V.subgroupOf L).map eL.toMonoidHom :=
    (Subgroup.subgroupOfEquivOfLe hVL).symm.trans
      (Subgroup.equivMapOfInjective _ eL.toMonoidHom eL.injective)
  refine psl2_no_kleinFour_centralizes_odd_cyclic F hF (Subgroup.zpowers (eL y'))
    ((V.subgroupOf L).map eL.toMonoidHom) inferInstance ?_ ?_ ?_ ?_
  · intro h
    rw [Subgroup.zpowers_eq_bot] at h
    apply hy1
    have : y' = 1 := eL.injective (h.trans (map_one eL).symm)
    exact congrArg Subtype.val this
  · rw [Nat.card_zpowers, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hy
  · exact { card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
            exponent_two := (Monoid.exponent_eq_of_mulEquiv eV).symm.trans hV.exponent_two }
  · rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hc' : Commute (eL y') (eL v) := by
      have : y' * v = v * y' := Subtype.ext (hyV v (Subgroup.mem_subgroupOf.mp hv))
      change eL y' * eL v = eL v * eL y'
      rw [← map_mul, ← map_mul, this]
    exact (hc'.zpow_left n).eq

theorem factorization_two_twelve : (12 : ℕ).factorization 2 = 2 := by
  rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem eq_of_card_four_of_psl2_three {F : Type} [Field F] [Finite F] (hF3 : Nat.card F = 3)
    {L : Subgroup X} (eL : L ≃* PSL2 F) {H₁ H₂ : Subgroup X} (h1 : H₁ ≤ L) (h2 : H₂ ≤ L)
    (hc1 : Nat.card H₁ = 4) (hc2 : Nat.card H₂ = 4) : H₁ = H₂ := by
  let _ : Fintype F := Fintype.ofFinite F
  let eF : ZMod 3 ≃+* F :=
    ZMod.ringEquivOfPrime F Nat.prime_three (by rw [← Nat.card_eq_fintype_card]; exact hF3)
  let e : L ≃* alternatingGroup (Fin 4) :=
    eL.trans ((psl2RingEquiv eF).symm.trans psl2_three_equiv_alternatingGroup)
  have h4 : Nat.card (Fin 4) = 4 := by simp
  have key : ∀ H : Subgroup X, H ≤ L → Nat.card H = 4 →
      (H.subgroupOf L).map e.toMonoidHom = alternatingGroup.kleinFour (Fin 4) := by
    intro H hHL hH
    have hcard : Nat.card ((H.subgroupOf L).map e.toMonoidHom) =
        2 ^ (Nat.card (alternatingGroup (Fin 4))).factorization 2 := by
      rw [Subgroup.card_map_of_injective e.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv, hH,
        alternatingGroup.card_of_card_eq_four h4, factorization_two_twelve]
      norm_num
    exact alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four h4 (Sylow.ofCard _ hcard)
  have heq := Subgroup.map_injective (f := e.toMonoidHom) e.injective
    ((key H₁ h1 hc1).trans (key H₂ h2 hc2).symm)
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr h1, inf_eq_left.mpr h2] at heq
  exact heq

theorem normal_of_psl2_three {F : Type} [Field F] [Finite F] (hF3 : Nat.card F = 3)
    {L : Subgroup X} [L.Normal] (eL : L ≃* PSL2 F) {V : Subgroup X} (hVL : V ≤ L)
    (hV4 : Nat.card V = 4) : V.Normal := by
  refine ⟨fun v hv g => ?_⟩
  set H := V.map (MulAut.conj g).toMonoidHom with hH
  have hHL : H ≤ L := by
    rintro _ ⟨u, hu, rfl⟩
    exact (inferInstance : L.Normal).conj_mem u (hVL hu) g
  have hHcard : Nat.card H = 4 := by
    rw [hH, Subgroup.card_map_of_injective (MulAut.conj g).injective, hV4]
  have hHV : H = V := eq_of_card_four_of_psl2_three hF3 eL hHL hVL hHcard hV4
  have hmem : g * v * g⁻¹ ∈ H := ⟨v, hv, by simp [MulAut.conj_apply]⟩
  rw [hHV] at hmem
  exact hmem

theorem not_isSimpleGroup_of_card_four {Y : Type*} [Group Y] [Finite Y] (h : Nat.card Y = 4) :
    ¬ IsSimpleGroup Y := by
  intro hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype Y := Fintype.ofFinite Y
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := Y) 2
    (by rw [← Nat.card_eq_fintype_card, h]; norm_num)
  have hcard : Nat.card (Subgroup.zpowers y) = 2 := by rw [Nat.card_zpowers, hy]
  have hidx : (Subgroup.zpowers y).index = 2 := by
    have := (Subgroup.zpowers y).card_mul_index
    rw [hcard, h] at this
    omega
  have hn := Subgroup.normal_of_index_eq_two hidx
  rcases hn.eq_bot_or_eq_top with hb | ht
  · rw [hb, Subgroup.card_bot] at hcard
    omega
  · rw [ht, Subgroup.card_top, h] at hcard
    omega

theorem five_le_of_isOddPrimePower {q : ℕ} (hq : IsOddPrimePower q) (hq3 : q ≠ 3) : 5 ≤ q := by
  obtain ⟨p, n, hp, hpodd, hn, rfl⟩ := hq
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · rw [h] at hpodd
      exact absurd hpodd (by decide)
    · have := hp.two_le
      obtain ⟨k, hk⟩ := h
      omega
  have hpq : p ≤ p ^ n := Nat.le_self_pow (by omega) p
  have hodd : Odd (p ^ n) := hpodd.pow
  obtain ⟨k, hk⟩ := hodd
  omega

theorem exists_mem_cycle_of_psl2 [Finite X] {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hF3 : Nat.card F ≠ 3) {L : Subgroup X}
    (hLi : Odd L.index) (eL : L ≃* PSL2 F) (hX2 : (Nat.card X).factorization 2 = 2)
    {a b : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) (hVK : IsKleinFour (Subgroup.closure ({a, b} : Set X)))
    (hVL : Subgroup.closure ({a, b} : Set X) ≤ L) :
    ∃ ℓ ∈ L, ℓ * a * ℓ⁻¹ = b ∧ ℓ * b * ℓ⁻¹ = a * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF5 := five_le_of_isOddPrimePower hF hF3
  have : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hLs : IsSimpleGroup L := (MulEquiv.isSimpleGroup_congr eL).mpr inferInstance
  have hL2 : (Nat.card L).factorization 2 = 2 :=
    (factorization_two_card_of_odd_index hLi).trans hX2
  have hVmem : ∀ v ∈ Subgroup.closure ({a, b} : Set X), v = 1 ∨ v = a ∨ v = b ∨ v = a * b :=
    fun v hv => mem_closure_pair ha hb hab hv
  have haV : a ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbV : b ∈ Subgroup.closure ({a, b} : Set X) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hVcomm : ∀ u ∈ Subgroup.closure ({a, b} : Set X), ∀ v ∈ Subgroup.closure ({a, b} : Set X),
      u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (mul_comm_of_exponent_two hVK.exponent_two ⟨u, hu⟩ ⟨v, hv⟩)
  have hV'card : Nat.card ((Subgroup.closure ({a, b} : Set X)).subgroupOf L) =
      2 ^ (Nat.card L).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv, hVK.card_four, hL2]
    norm_num
  let P : Sylow 2 L := Sylow.ofCard _ hV'card
  have hPmem : ∀ u : L, u ∈ (P : Subgroup L) ↔ (u : X) ∈ Subgroup.closure ({a, b} : Set X) :=
    fun u => by
      change u ∈ (Subgroup.closure ({a, b} : Set X)).subgroupOf L ↔ _
      exact Subgroup.mem_subgroupOf
  have hPcard : Nat.card (P : Subgroup L) = 4 := by
    change Nat.card ((Subgroup.closure ({a, b} : Set X)).subgroupOf L) = 4
    rw [hV'card, hL2]
    norm_num
  have hnot : ¬ (Subgroup.normalizer (P : Set L) ≤ Subgroup.centralizer (P : Set L)) := by
    intro hP
    have hcm := (MonoidHom.ker_transferSylow_isComplement' P hP).card_mul_card
    have := hLs
    rcases (inferInstance : (MonoidHom.transferSylow P hP).ker.Normal).eq_bot_or_eq_top with
      h | h
    · rw [h, Subgroup.card_bot, one_mul] at hcm
      exact not_isSimpleGroup_of_card_four (hcm.symm.trans hPcard) hLs
    · rw [h, Subgroup.card_top, hPcard] at hcm
      have hpos : 0 < Nat.card L := Nat.card_pos
      omega
  obtain ⟨ℓ₀, hℓ₀N, hℓ₀C⟩ : ∃ ℓ₀ ∈ Subgroup.normalizer (P : Set L),
      ℓ₀ ∉ Subgroup.centralizer (P : Set L) := by
    by_contra hcon
    push Not at hcon
    exact hnot hcon
  set Q : Subgroup L := (P : Subgroup L) with hQ
  have hℓ₀N' : ℓ₀ ∈ Subgroup.normalizer (Q : Set L) := hℓ₀N
  have hℓ₀C' : ℓ₀ ∉ Subgroup.centralizer (Q : Set L) := hℓ₀C
  set Nz := Subgroup.normalizer (Q : Set L) with hNz
  set Cz := Subgroup.centralizer (Q : Set L) with hCz
  have hCN : Cz ≤ Nz := Subgroup.centralizer_le_normalizer _
  have hCnorm : (Cz.subgroupOf Nz).Normal := ⟨fun c hc n => by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    rw [hCz, Subgroup.mem_centralizer_iff] at hc ⊢
    intro h hh
    have hh' : (n : L)⁻¹ * h * (n : L) ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (Nz.inv_mem n.2) h).mp hh
      simpa using this
    have h1 := hc _ hh'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc h * ((n : L) * c * (n : L)⁻¹) =
        (n : L) * (((n : L)⁻¹ * h * n) * c) * (n : L)⁻¹ := by group
      _ = (n : L) * (c * ((n : L)⁻¹ * h * n)) * (n : L)⁻¹ := by rw [h1]
      _ = (n : L) * c * (n : L)⁻¹ * h := by group⟩
  set r := (Cz.subgroupOf Nz).index with hr
  have hℓr : ℓ₀ ^ r ∈ Cz := by
    have h := (Cz.subgroupOf Nz).pow_index_mem ⟨ℓ₀, hℓ₀N'⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  have hrodd : Odd r := by
    have hPC : Q ≤ Cz := fun u hu => by
      rw [hCz, Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subtype.ext (hVcomm _ ((hPmem v).mp hv) _ ((hPmem u).mp hu))
    have h4C : 4 ∣ Nat.card Cz := hPcard ▸ Subgroup.card_dvd_of_le hPC
    have hNcard : Nat.card Nz = Nat.card Cz * r := by
      rw [hr, ← Subgroup.card_mul_index (Cz.subgroupOf Nz),
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv]
    have hNL : Nat.card Nz ∣ Nat.card L := Subgroup.card_subgroup_dvd_card Nz
    by_contra hr2
    rw [Nat.not_odd_iff_even] at hr2
    obtain ⟨k, hk⟩ := hr2
    have h8 : 2 ^ 3 ∣ Nat.card L := by
      refine dvd_trans ?_ hNL
      rw [hNcard, hk]
      obtain ⟨c, hc⟩ := h4C
      rw [hc]
      exact ⟨c * k, by ring⟩
    have := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h8
    omega
  have hconjV : ∀ v ∈ Subgroup.closure ({a, b} : Set X),
      (ℓ₀ : X) * v * (ℓ₀ : X)⁻¹ ∈ Subgroup.closure ({a, b} : Set X) := by
    intro v hv
    have hvL : v ∈ L := hVL hv
    have h := (Subgroup.mem_normalizer_iff.mp hℓ₀N' (⟨v, hvL⟩ : L)).mp ((hPmem _).mpr hv)
    exact (hPmem _).mp h
  have hcases : ∀ v ∈ Subgroup.closure ({a, b} : Set X), v ≠ 1 →
      (ℓ₀ : X) * v * (ℓ₀ : X)⁻¹ = a ∨ (ℓ₀ : X) * v * (ℓ₀ : X)⁻¹ = b ∨
        (ℓ₀ : X) * v * (ℓ₀ : X)⁻¹ = a * b := by
    intro v hv hv1
    rcases hVmem _ (hconjV v hv) with h | h | h | h
    · exfalso
      apply hv1
      calc v = (ℓ₀ : X)⁻¹ * ((ℓ₀ : X) * v * (ℓ₀ : X)⁻¹) * ℓ₀ := by group
        _ = 1 := by rw [h]; group
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hrcomm : ∀ v ∈ Subgroup.closure ({a, b} : Set X), ((ℓ₀ : X) ^ r) * v = v * (ℓ₀ : X) ^ r := by
    intro v hv
    have h := (Subgroup.mem_centralizer_iff.mp hℓr) ⟨v, hVL hv⟩ ((hPmem _).mpr hv)
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_pow] at h'
    exact h'.symm
  rcases exists_cycle_of_odd ha hb hab hne hrodd (hrcomm a haV) (hrcomm b hbV)
      (hcases a haV ha1) (hcases b hbV hb1) with h | h | h
  · exfalso
    apply hℓ₀C'
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rcases hVmem _ ((hPmem u).mp hu) with h1 | h1 | h1 | h1 <;> rw [h1]
    · simp
    · exact h.1.symm
    · exact h.2.symm
    · rw [mul_assoc, ← h.2, ← mul_assoc, ← h.1, mul_assoc]
  · exact ⟨ℓ₀, ℓ₀.2, h⟩
  · exact ⟨(ℓ₀ : X) ^ 2, L.pow_mem ℓ₀.2 2, h⟩

end CFSG.Semidihedral.UnitaryDValue.GW
