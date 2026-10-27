module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResB
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinA
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecTransport

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
open scoped commutatorElement

theorem quat_mul_self_eq_one {n : ℕ} [NeZero n] (x : QuaternionGroup n) (hx : x * x = 1) :
    x = 1 ∨ x = QuaternionGroup.a (n : ZMod (2 * n)) := by
  rcases x with i | i
  · rw [QuaternionGroup.a_mul_a, QuaternionGroup.one_def] at hx
    have h2 : i + i = 0 := QuaternionGroup.a.inj hx
    rcases CFSG.GH74.GLS.IVK.DihedralAux.two_mul_eq_zero_iff i h2 with h0 | h1
    · left
      rw [h0, QuaternionGroup.one_def]
    · right
      rw [h1]
      congr 2
      omega
  · exfalso
    have h5 : QuaternionGroup.xa i ^ 2 = 1 := by rw [sq]; exact hx
    rw [QuaternionGroup.xa_sq, QuaternionGroup.one_def] at h5
    have h6 : ((n : ℕ) : ZMod (2 * n)) ≠ 0 := by
      intro h0
      have hd := (ZMod.natCast_eq_zero_iff n (2 * n)).mp h0
      have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      have := Nat.le_of_dvd hn hd
      omega
    exact h6 (QuaternionGroup.a.inj h5)

theorem card_le_two_of_quat {R : Type*} [Group R] {m : ℕ} [NeZero m]
    (e : R ≃* QuaternionGroup m) (E : Subgroup R) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 := by
  classical
  have hsub : ∀ x ∈ E, x ∈ ({1, e.symm (QuaternionGroup.a (m : ZMod (2 * m)))} : Finset R) := by
    intro x hx
    have h1 : e x * e x = 1 := by rw [← map_mul, hsq x hx, map_one]
    rcases quat_mul_self_eq_one (e x) h1 with h | h
    · simp [e.injective (h.trans (map_one e).symm)]
    · simp [← h]
  calc Nat.card E ≤ Nat.card ({1, e.symm (QuaternionGroup.a (m : ZMod (2 * m)))} : Finset R) := by
        exact Nat.card_le_card_of_injective (fun x : E => (⟨x, hsub x x.2⟩ :
          ({1, e.symm (QuaternionGroup.a (m : ZMod (2 * m)))} : Finset R)))
          (by
            intro x y hxy
            have h := congrArg Subtype.val hxy
            exact Subtype.ext h)
    _ ≤ 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        exact Finset.card_le_two

theorem pPrimeCore_eq_center {A : Type} [Group A] [Finite A] {J : Subgroup A}
    (hJ : IsQuasisimple ↥J) (hZ : Odd (Nat.card (center ↥J))) :
    pPrimeCore 2 ↥J = center ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · rcases LocalCores.quasisimple_normal_subgroups hJ (pPrimeCore_normal (p := 2) (G := ↥J))
      with h | h
    · exfalso
      have hodd : Odd (Nat.card ↥J) := by
        have := pPrimeCore_coprime_card (p := 2) (G := ↥J)
        rw [h, card_top] at this
        exact Nat.coprime_two_left.mp this
      have hsol := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hJ
      have : Group.IsPerfect ↥J := hJ.1
      exact Group.IsPerfect.not_isSolvable (↥J) hsol
    · exact h
  · exact le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hZ⟩

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem isFourSubgroup_barIn_Q₁ (hd : Data5A2 z k S T Tstar p H P t q I Q₁) :
    IVK.IsFourSubgroup (barIn H Q₁) := by
  have := isFourSubgroup_map_barIn hd.Q₁_four (hd.Q₁_le.trans hd.i.good.le_H)
    (f := MonoidHom.id (HBar H)) Function.injective_id
  simpa [Subgroup.map_id] using this

omit [Finite G] in
theorem eq_one_of_mem_barIn_comm (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {x : HBar H}
    (hx : x ∈ barIn H I) (hc : ∀ y ∈ barIn H I, x * y = y * x) (hx2 : x * x = 1) : x = 1 := by
  obtain ⟨i, hi, rfl⟩ := hx
  have hcomm : ∀ j ∈ I, ⁅(i : G), j⁆ ∈ pPrimeCoreOf 2 H := by
    intro j hj
    have hjH : j ∈ H := hd.i.good.le_H hj
    have h1 := hc (QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨j, hjH⟩) ⟨⟨j, hjH⟩, hj, rfl⟩
    have h2 : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⁅i, ⟨j, hjH⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h1
    exact ⟨⁅i, ⟨j, hjH⟩⁆, (QuotientGroup.eq_one_iff _).mp h2, by
      simp [commutatorElement_def]⟩
  have hodd : Odd (orderOf (i : G)) := hd.i.good.noCent (i : G) hi hcomm
  have hd1 : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥H) i) ∣ orderOf (i : G) := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_map_dvd _ _
  have hd2 : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥H) i) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx2)
  have h1 : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥H) i) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hd2 with h | h
    · exact h
    · rw [h] at hd1
      exact absurd (Odd.of_dvd_nat hodd hd1) (by decide)
  exact orderOf_eq_one_iff.mp h1

theorem hat_type (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hQJ : barIn H Q₁ ≤ centralizer (J : Set (HBar H))) :
    Nonempty (Hat J ≃* alternatingGroup (Fin 7)) ∨ IVK.IsL2 (Hat J) Odd := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ4 := isFourSubgroup_barIn_Q₁ hd
  set Q := barIn H Q₁ with hQ
  have := hQ4.1
  have hQsq : ∀ x ∈ Q, x * x = 1 := fun x hx => by
    rw [← sq]
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hW2 : IsPGroup 2 ↥Q := IsElementaryAbelian.isPGroup 2 ↥Q
  have hW1 : Q ≠ ⊥ := by
    intro hbot
    have h4 := hQ4.2
    rw [hbot, card_bot] at h4
    omega
  have hodd : Odd (Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥H)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨Jt, R, ρ, -, -, ⟨eH⟩, hconcl, hρ, hQρ⟩ := sec31_core_hom hL31 h.ctx (H_ne_top h)
    (QuotientGroup.mk' (pPrimeCore 2 ↥H)) (QuotientGroup.mk'_surjective _) hodd hJ hW2 hQJ hW1
  set E : Subgroup ↥R := Q.comap ρ with hE
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => hρ (by rw [map_mul, map_one]; exact hQsq _ hx)
  have hE4 : Nat.card E = 4 := by
    rw [← Subgroup.card_map_of_injective hρ, Subgroup.map_comap_eq_self hQρ, hQ4.2]
  have hdih : IsDihedral ↥R := by
    rcases hconcl.1 with hc | ⟨n, hn, ⟨e⟩⟩ | hdi
    · exfalso
      have := card_le_two_of_isCyclic E hEsq
      omega
    · exfalso
      have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
      have := card_le_two_of_quat e E hEsq
      omega
    · exact hdi
  rcases hconcl.2.1 hdih with he7 | hL2
  · obtain ⟨e7⟩ := he7
    exact Or.inl ⟨eH.symm.trans e7⟩
  · exact Or.inr (Odd87.Transport.isL2_of_mulEquiv eH hL2)

theorem odd_card_center (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H))) : Odd (Nat.card (center ↥J)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQJ : barIn H Q₁ ≤ centralizer (J : Set (HBar H)) :=
    (L52Two.barIn_mono hd.Q₁_le).trans hIJ
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥J)) 2 (even_iff_two_dvd.mp hev)
  set x : HBar H := ((e : ↥J) : HBar H) with hx
  have hxJ : x ∈ J := (e : ↥J).2
  have hx2 : x * x = 1 := by
    have : e ^ 2 = 1 := by
      have h0 := pow_orderOf_eq_one e
      rwa [he] at h0
    have h1 := congrArg (fun y : ↥(center ↥J) => ((y : ↥J) : HBar H)) this
    simpa [sq] using h1
  have hx1 : x ≠ 1 := by
    intro h1
    have : e = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at he
    exact absurd he (by norm_num)
  have hxC : x ∈ centralizer (J : Set (HBar H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_center_iff.mp e.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hxQ : x ∈ centralizer (barIn H Q₁ : Set (HBar H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hQJ hy)) x hxJ).symm
  set A := zpowers x with hA
  have hAJ : A ≤ centralizer (J : Set (HBar H)) := zpowers_le.mpr hxC
  have hAQ : A ≤ centralizer (barIn H Q₁ : Set (HBar H)) := zpowers_le.mpr hxQ
  have hAsq : ∀ y ∈ A, y * y = 1 := by
    rintro _ ⟨n, rfl⟩
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hx2, one_zpow]
  have hinf : A ⊓ barIn H Q₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyA, hyQ⟩
    rw [Subgroup.mem_bot]
    have hyJ : y ∈ J := (zpowers_le.mpr hxJ) hyA
    refine eq_one_of_mem_barIn_comm hd (L52Two.barIn_mono hd.Q₁_le hyQ) (fun w hw => ?_)
      (hAsq y hyA)
    exact (Subgroup.mem_centralizer_iff.mp (hIJ hw)) y hyJ
  have hbot := eq_bot_of_elem_le_centralizer hL31 h hd hJ hQJ hAJ hAQ hAsq hinf
  apply hx1
  have : x ∈ A := Subgroup.mem_zpowers x
  rw [hbot, Subgroup.mem_bot] at this
  exact this

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
