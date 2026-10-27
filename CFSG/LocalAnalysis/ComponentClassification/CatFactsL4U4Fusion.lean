module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerCase
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Coprime
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TypeU4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedLayer

theorem exists_conj_of_mul_odd {G : Type*} [Group G] {z w : G} (hz : z * z = 1) (hw : w * w = 1)
    (ho : Odd (orderOf (z⁻¹ * w))) : ∃ k : ℕ, (z⁻¹ * w) ^ k * z * ((z⁻¹ * w) ^ k)⁻¹ = w := by
  obtain ⟨o, hodef⟩ : ∃ o, o = z⁻¹ * w := ⟨_, rfl⟩
  rw [← hodef] at ho ⊢
  obtain ⟨k, hk⟩ := ho
  refine ⟨k, ?_⟩
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hwo : w = z * o := by rw [hodef, ← mul_assoc, mul_inv_cancel, one_mul]
  have hzoz : z * o * z = o⁻¹ := by
    have h1 : (z * o) * (z * o) = 1 := by rw [← hwo]; exact hw
    calc z * o * z = z * o * z * (o * o⁻¹) := by group
      _ = (z * o) * (z * o) * o⁻¹ := by group
      _ = o⁻¹ := by rw [h1, one_mul]
  have hpow : ∀ n : ℕ, z * o ^ n * z = (o ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      calc z * o ^ (n + 1) * z = (z * o ^ n * z) * (z * o * z) := by
            rw [pow_succ]
            calc z * (o ^ n * o) * z = z * o ^ n * (z * z) * o * z := by rw [hz]; group
              _ = (z * o ^ n * z) * (z * o * z) := by group
        _ = (o ^ n)⁻¹ * o⁻¹ := by rw [ih, hzoz]
        _ = (o ^ (n + 1))⁻¹ := by rw [pow_succ, mul_inv_rev]; group
  have hm : o ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one o
  calc o ^ k * z * (o ^ k)⁻¹ = z * (z * o ^ k * z) * (o ^ k)⁻¹ := by
        calc o ^ k * z * (o ^ k)⁻¹ = (z * z) * o ^ k * z * (o ^ k)⁻¹ := by rw [hz, one_mul]
          _ = z * (z * o ^ k * z) * (o ^ k)⁻¹ := by group
    _ = z * (o ^ k)⁻¹ * (o ^ k)⁻¹ := by rw [hpow, mul_assoc]
    _ = z * o * (o ^ (2 * k + 1))⁻¹ := by
        rw [show 2 * k + 1 = k + k + 1 by ring, pow_succ, pow_add]
        group
    _ = w := by rw [hm, inv_one, mul_one, hwo]

theorem not_mem_of_orderOf_eq_two {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : Nat.Coprime 2 (Nat.card N)) {x : G} (hx : orderOf x = 2) : x ∉ N := by
  intro hxN
  have h1 : orderOf (⟨x, hxN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk, hx]
  have h2 := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
  rw [h1] at h2
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hN h2

theorem exists_conj_L4 {F : Type} [Field F] [Fintype F] (hF : Fintype.card F % 4 = 3)
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ Fintype.card F ^ 2 + 1)
    {u y ℓ' z' y' : StatedProj (StatedSL 4 F)} (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1)
    (hy : orderOf y = s) (huy : u * y = y * u) {J' : Subgroup (StatedProj (StatedSL 4 F))}
    (hℓ'1 : ℓ' ≠ 1) (hℓ'2 : ℓ' ^ 2 = 1) (hJ' : J' ≤ Subgroup.centralizer {ℓ'})
    (hJp : ⁅J', J'⁆ = J') (hy'J : y' ∈ J') (hy' : orderOf y' = s) (hz : z' ∈ J')
    (hz2 : z' * z' = 1) (hz1 : z' ≠ 1) : ∃ w, w * u * w⁻¹ = z' := by
  have hq : Odd (Fintype.card F) := ⟨Fintype.card F / 2, by omega⟩
  obtain ⟨X₁, rfl⟩ := QuotientGroup.mk_surjective u
  have hX₁ := sq_eq_neg_one_of_comm_orderOf hq hu1 hu2 hs hs2 hsq hy huy X₁ rfl
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective ℓ'
  have hk := sq_eq_neg_one_of_comm_orderOf hq hℓ'1 hℓ'2 hs hs2 hsq hy'
    (Subgroup.mem_centralizer_singleton_iff.mp (hJ' hy'J)).symm k rfl
  obtain ⟨X₂, rfl, hX₂⟩ := exists_lift_sq_eq_neg_one_of_perfect hF k hk hJ' hJp hz hz2 hz1
  exact exists_conj_of_sq_eq_neg_one' hF X₁ X₂ hX₁ hX₂

theorem exists_conj_U4 {p f : ℕ} {K' : Type} [Field K'] (h' : UnitaryFieldData p f K')
    (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ (p ^ f) ^ 2 + 1)
    {u y ℓ' z' y' : StatedProj (StatedSU 4 (p ^ f) K')} (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1)
    (hy : orderOf y = s) (huy : u * y = y * u)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K'))}
    (hℓ'1 : ℓ' ≠ 1) (hℓ'2 : ℓ' ^ 2 = 1) (hJ' : J' ≤ Subgroup.centralizer {ℓ'})
    (hJp : ⁅J', J'⁆ = J') (hy'J : y' ∈ J') (hy' : orderOf y' = s) (hz : z' ∈ J')
    (hz2 : z' * z' = 1) (hz1 : z' ≠ 1) : ∃ w, w * u * w⁻¹ = z' := by
  obtain ⟨X₁, rfl⟩ := QuotientGroup.mk_surjective u
  have hX₁ := sq_eq_neg_one_of_comm_orderOf_U4 h' hp2 hu1 hu2 hs hs2 hsq hy huy X₁ rfl
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective ℓ'
  have hk := sq_eq_neg_one_of_comm_orderOf_U4 h' hp2 hℓ'1 hℓ'2 hs hs2 hsq hy'
    (Subgroup.mem_centralizer_singleton_iff.mp (hJ' hy'J)).symm k rfl
  obtain ⟨X₂, rfl, hX₂⟩ :=
    exists_lift_sq_eq_neg_one_of_perfect_U4 h' hp2 hq k hk hJ' hJp hz hz2 hz1
  exact exists_conj_of_sq_eq_neg_one_U4 h' hp2 hq X₁ X₂ hX₁ hX₂

theorem cfRow516InnerFusion : CFRow516InnerFusion := by
  intro H _ _ h hrow hin z hzD hzS hz2 a₁ ha₁ ha₁2
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKa : conjugate h.K h.a = h.K := by
    obtain ⟨-, -, -, -, -, -, hKa, -⟩ := hrow
    exact hKa
  obtain ⟨hZ, p, f, hp, hp2, hf, hJ, hcase⟩ := inner_structure h hrow hin
  obtain ⟨ℓ, -, hℓZ, hℓ2, hJC, hJp, -, ⟨s, hs, hs2, hsq, hsJbar, hsJ⟩, -⟩ :=
    inner_data h hp hp2 hJ hKa hin
  have := Fact.mk hs
  have hzJB : z ∈ GSLit.fixedLayer h.J h.B := mem_fixedLayer_of_mem_D h hzD hzS hz2
  have hzK : z ∈ h.K := fixedLayer_le_K h hKa hzJB
  have hzJ : z ∈ h.J := (Subgroup.mem_inf.1 hzD).2
  obtain ⟨ha₁P, ha₁K⟩ := Subgroup.mem_inf.1 ha₁
  have ha₁J : a₁ ∈ coreActionKernel h.J := (Subgroup.mem_inf.1 ha₁P).2
  have hOK : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥h.K)) := pPrimeCore_coprime_card
  have hOJ : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥h.J)) := pPrimeCore_coprime_card
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have ha₁2' : a₁ * a₁ = 1 := by rw [← pow_two, ← ha₁2, pow_orderOf_eq_one]
  set zbar : OddBar h.K := QuotientGroup.mk ⟨z, hzK⟩ with hzbar
  set abar : OddBar h.K := QuotientGroup.mk ⟨a₁, ha₁K⟩ with habar
  have hzbar1 : zbar ≠ 1 := by
    rw [hzbar, Ne, QuotientGroup.eq_one_iff]
    exact not_mem_of_orderOf_eq_two hOK (by rw [Subgroup.orderOf_mk, hz2])
  have habar1 : abar ≠ 1 := by
    rw [habar, Ne, QuotientGroup.eq_one_iff]
    exact not_mem_of_orderOf_eq_two hOK (by rw [Subgroup.orderOf_mk, ha₁2])
  have hzbar2 : zbar * zbar = 1 := by
    rw [hzbar, ← QuotientGroup.mk_mul]
    have : (⟨z, hzK⟩ : h.K) * ⟨z, hzK⟩ = 1 := Subtype.ext hz2'
    rw [this, QuotientGroup.mk_one]
  have habar2 : abar ^ 2 = 1 := by
    rw [habar, ← QuotientGroup.mk_pow, sq]
    have : (⟨a₁, ha₁K⟩ : h.K) * ⟨a₁, ha₁K⟩ = 1 := Subtype.ext ha₁2'
    rw [this, QuotientGroup.mk_one]
  have hzbarJ : zbar ∈ imJB h := ⟨⟨z, hzK⟩, Subgroup.mem_subgroupOf.2 hzJB, rfl⟩
  have hJs : IsSimpleGroup (OddBar h.J) := isSimpleGroup_of_lieModel_psl_two hJ
  have hJ2 : Even (Nat.card (OddBar h.J)) := by
    set zJ : OddBar h.J := QuotientGroup.mk ⟨z, hzJ⟩ with hzJdef
    have hzJ1 : zJ ≠ 1 := by
      rw [hzJdef, Ne, QuotientGroup.eq_one_iff]
      exact not_mem_of_orderOf_eq_two hOJ (by rw [Subgroup.orderOf_mk, hz2])
    have hzJ2 : zJ ^ 2 = 1 := by
      rw [hzJdef, ← QuotientGroup.mk_pow, sq]
      have : (⟨z, hzJ⟩ : h.J) * ⟨z, hzJ⟩ = 1 := Subtype.ext hz2'
      rw [this, QuotientGroup.mk_one]
    have h1 := orderOf_dvd_natCard zJ
    rw [orderOf_eq_prime hzJ2 hzJ1] at h1
    exact even_iff_two_dvd.2 h1
  have hA2 : IsPGroup 2 (zpowers a₁) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ha₁2, pow_one]
  obtain ⟨y, hy, hyc⟩ := exists_orderOf_eq_comm_of_isPGroup' h hKa hA2 (zpowers_le.2 ha₁K)
    (zpowers_le.2 ha₁J) hJs hJ2 hs hsJbar
  have hay : abar * y = y * abar := hyc a₁ (mem_zpowers a₁)
  obtain ⟨y'', hy''⟩ := exists_prime_orderOf_dvd_card' (G := imJB h) s hsJ
  have hy' : orderOf (y'' : OddBar h.K) = s := by rw [Subgroup.orderOf_coe, hy'']
  have hℓ1 : ℓ ≠ 1 := fun h1 => hℓZ (by rw [h1]; exact one_mem _)
  have hℓ2' : ℓ ^ 2 = 1 := by rw [hZ] at hℓ2; exact Subgroup.mem_bot.1 hℓ2
  have hconj : ∃ g : OddBar h.K, g * abar * g⁻¹ = zbar := by
    have key : ∀ {M : Type} [Group M] (e : OddBar h.K ≃* M),
        (∃ w, w * e abar * w⁻¹ = e zbar) → ∃ g : OddBar h.K, g * abar * g⁻¹ = zbar := by
      intro M _ e ⟨w, hw⟩
      refine ⟨e.symm w, e.injective ?_⟩
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hw]
    have hJ' : ∀ {M : Type} [Group M] (e : OddBar h.K ≃* M),
        (imJB h).map e.toMonoidHom ≤ Subgroup.centralizer {e ℓ} := by
      intro M _ e
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp (hJC hx)]
    have hJp' : ∀ {M : Type} [Group M] (e : OddBar h.K ≃* M),
        ⁅(imJB h).map e.toMonoidHom, (imJB h).map e.toMonoidHom⁆ = (imJB h).map e.toMonoidHom :=
      fun e => by rw [← Subgroup.map_commutator, hJp]
    rcases hcase with ⟨hq, F, _, _, hF, ⟨e⟩⟩ | ⟨hq, K', _, hUF, ⟨e⟩⟩
    · have hF' : Fintype.card F % 4 = 3 := by rw [hF]; exact hq
      exact key e (exists_conj_L4 hF' hs hs2 (by rw [hF]; exact hsq) (u := e abar) (y := e y)
        (ℓ' := e ℓ) (z' := e zbar) (y' := e (y'' : OddBar h.K))
        (J' := (imJB h).map e.toMonoidHom)
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact habar1) (by rw [← map_pow e, habar2, map_one])
        (by rw [MulEquiv.orderOf_eq, hy]) (by rw [← map_mul e, ← map_mul e, hay])
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hℓ1) (by rw [← map_pow e, hℓ2', map_one])
        (hJ' e) (hJp' e) ⟨(y'' : OddBar h.K), y''.2, rfl⟩
        (by rw [MulEquiv.orderOf_eq, hy'])
        ⟨zbar, hzbarJ, rfl⟩ (by rw [← map_mul e, hzbar2, map_one])
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hzbar1))
    · exact key e (exists_conj_U4 hUF hp2 hq hs hs2 hsq (u := e abar) (y := e y)
        (ℓ' := e ℓ) (z' := e zbar) (y' := e (y'' : OddBar h.K))
        (J' := (imJB h).map e.toMonoidHom)
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact habar1) (by rw [← map_pow e, habar2, map_one])
        (by rw [MulEquiv.orderOf_eq, hy]) (by rw [← map_mul e, ← map_mul e, hay])
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hℓ1) (by rw [← map_pow e, hℓ2', map_one])
        (hJ' e) (hJp' e) ⟨(y'' : OddBar h.K), y''.2, rfl⟩
        (by rw [MulEquiv.orderOf_eq, hy'])
        ⟨zbar, hzbarJ, rfl⟩ (by rw [← map_mul e, hzbar2, map_one])
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hzbar1))
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective g
  set w : H := (c₀ : H) * a₁ * (c₀ : H)⁻¹ with hw
  have hwK : w ∈ h.K := mul_mem (mul_mem c₀.2 ha₁K) (inv_mem c₀.2)
  have hwz : (QuotientGroup.mk ⟨w, hwK⟩ : OddBar h.K) = zbar := by
    rw [← hg, habar, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hoO : (⟨z, hzK⟩ : h.K)⁻¹ * ⟨w, hwK⟩ ∈ pPrimeCore 2 ↥h.K := by
    rw [← QuotientGroup.eq]
    exact hwz.symm
  have hoodd : Odd (orderOf (z⁻¹ * w)) := by
    have h1 := orderOf_dvd_natCard (⟨_, hoO⟩ : pPrimeCore 2 ↥h.K)
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf (z⁻¹ * w) = orderOf ((⟨z, hzK⟩ : h.K)⁻¹ * ⟨w, hwK⟩) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [h2]
    have h3 : Odd (Nat.card (pPrimeCore 2 ↥h.K)) := by
      have := hOK.symm
      rwa [Nat.coprime_two_right] at this
    exact Odd.of_dvd_nat h3 h1
  have hw2 : w * w = 1 := by
    rw [hw]
    calc (c₀ : H) * a₁ * (c₀ : H)⁻¹ * ((c₀ : H) * a₁ * (c₀ : H)⁻¹) =
        (c₀ : H) * (a₁ * a₁) * (c₀ : H)⁻¹ := by group
      _ = 1 := by rw [ha₁2', mul_one, mul_inv_cancel]
  obtain ⟨k, hk⟩ := exists_conj_of_mul_odd hz2' hw2 hoodd
  have hoK : z⁻¹ * w ∈ h.K := mul_mem (inv_mem hzK) hwK
  obtain ⟨o, hodef⟩ : ∃ o, o = z⁻¹ * w := ⟨_, rfl⟩
  rw [← hodef] at hk hoK
  refine ⟨(c₀ : H)⁻¹ * o ^ k, mul_mem (inv_mem c₀.2) (pow_mem hoK k), ?_⟩
  calc ((c₀ : H)⁻¹ * o ^ k)⁻¹ * a₁ * ((c₀ : H)⁻¹ * o ^ k) = (o ^ k)⁻¹ * w * o ^ k := by
        rw [hw]; group
    _ = z := by
      rw [← hk]
      group

end CFSG.ComponentClassification.CatFactsL4U4
