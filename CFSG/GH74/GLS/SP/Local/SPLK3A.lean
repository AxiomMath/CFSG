module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk412Dih
public import CFSG.GH74.GLS.SP.Local.SPLCtC1a

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section General

theorem k3_card_sup_mul_card_inf {H : Type*} [Group H] [Finite H] (L R : Subgroup H)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup H) * Nat.card (L ⊓ R : Subgroup H) =
      Nat.card L * Nat.card R := by
  let μ : L × R →* H := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : H) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup H) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : H), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : H)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]
  exact this

theorem k3_card_of_relIndex_two {G : Type} [Group G] {P X : Subgroup G} (hPX : P ≤ X)
    (hidx : P.relIndex X = 2) : Nat.card ↥X = 2 * Nat.card ↥P := by
  have h := Subgroup.card_mul_index (P.subgroupOf X)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv] at h
  have hidx' : (P.subgroupOf X).index = 2 := hidx
  rw [hidx'] at h
  omega

theorem k3_cyclic_split {G : Type} [Group G] {T : Subgroup G} (hT : IsCyclic ↥T) {e k : ℕ}
    (he : Odd e) (hcard : Nat.card ↥T = e * 2 ^ k) :
    ∃ E R : Subgroup G, E ≤ T ∧ R ≤ T ∧ IsCyclic ↥E ∧ IsCyclic ↥R ∧ Nat.card ↥E = e ∧
      Nat.card ↥R = 2 ^ k ∧ (∀ x : G, x ∈ E ↔ x ∈ T ∧ Odd (orderOf x)) ∧
      (∀ x : G, x ∈ R ↔ x ∈ T ∧ ∃ j : ℕ, x ^ 2 ^ j = 1) := by
  obtain ⟨g, hg⟩ := hT.exists_generator
  have he0 : 0 < e := he.pos
  have hk0 : 0 < 2 ^ k := pow_pos two_pos k
  have hγT : (g : G) ∈ T := g.2
  have hord : orderOf (g : G) = e * 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hmemT : ∀ x ∈ T, ∃ j : ℤ, (g : G) ^ j = x := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  generalize (g : G) = γ at hγT hord hmemT
  have hEcard : Nat.card ↥(zpowers (γ ^ 2 ^ k)) = e := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hk0.ne' (hord ▸ dvd_mul_left _ _), hord,
      Nat.mul_div_cancel e hk0]
  have hRcard : Nat.card ↥(zpowers (γ ^ e)) = 2 ^ k := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd he0.ne' (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ he0]
  refine ⟨zpowers (γ ^ 2 ^ k), zpowers (γ ^ e), zpowers_le.mpr (T.pow_mem hγT _),
    zpowers_le.mpr (T.pow_mem hγT _), inferInstance, inferInstance, hEcard, hRcard, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      refine ⟨zpowers_le.mpr (T.pow_mem hγT _) hx, ?_⟩
      have h1 : orderOf x ∣ e := by
        have := Subgroup.orderOf_dvd_natCard (zpowers (γ ^ 2 ^ k)) hx
        rwa [hEcard] at this
      exact Odd.of_dvd_nat he h1
    · rintro ⟨hxT, hodd⟩
      obtain ⟨j, rfl⟩ := hmemT x hxT
      have hdvd : orderOf (γ ^ j) ∣ e * 2 ^ k := hcard ▸ Subgroup.orderOf_dvd_natCard T hxT
      have hcop : Nat.Coprime (orderOf (γ ^ j)) (2 ^ k) :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
      have hdvd' : orderOf (γ ^ j) ∣ e := hcop.dvd_of_dvd_mul_right hdvd
      have hx1 : (γ ^ j) ^ e = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd'
      have hz : γ ^ (j * (e : ℤ)) = 1 := by rw [zpow_mul, zpow_natCast]; exact hx1
      have hd : ((e * 2 ^ k : ℕ) : ℤ) ∣ j * (e : ℤ) := by
        rw [← hord]; exact orderOf_dvd_iff_zpow_eq_one.mpr hz
      have hd2 : ((2 ^ k : ℕ) : ℤ) ∣ j := by
        have h3 : ((2 ^ k : ℕ) : ℤ) * (e : ℤ) ∣ j * (e : ℤ) := by
          rw [mul_comm ((2 ^ k : ℕ) : ℤ) (e : ℤ)]
          exact_mod_cast hd
        exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast he0.ne') h3
      obtain ⟨j', rfl⟩ := hd2
      exact mem_zpowers_iff.mpr ⟨j', by rw [zpow_mul, zpow_natCast]⟩
  · intro x
    constructor
    · intro hx
      refine ⟨zpowers_le.mpr (T.pow_mem hγT _) hx, k, ?_⟩
      have := Subgroup.orderOf_dvd_natCard (zpowers (γ ^ e)) hx
      rw [hRcard] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    · rintro ⟨hxT, j, hj⟩
      obtain ⟨i, rfl⟩ := hmemT x hxT
      have h2j : orderOf (γ ^ i) ∣ 2 ^ j := orderOf_dvd_iff_pow_eq_one.mpr hj
      obtain ⟨l, -, hlo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2j
      have hdvd : orderOf (γ ^ i) ∣ e * 2 ^ k := hcard ▸ Subgroup.orderOf_dvd_natCard T hxT
      have hcop : Nat.Coprime (2 ^ l) e :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr he)
      have hdvd' : orderOf (γ ^ i) ∣ 2 ^ k := by
        rw [hlo] at hdvd ⊢
        exact hcop.dvd_of_dvd_mul_left hdvd
      have hx1 : (γ ^ i) ^ 2 ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd'
      have hz : γ ^ (i * ((2 ^ k : ℕ) : ℤ)) = 1 := by rw [zpow_mul, zpow_natCast]; exact hx1
      have hd : ((e * 2 ^ k : ℕ) : ℤ) ∣ i * ((2 ^ k : ℕ) : ℤ) := by
        rw [← hord]; exact orderOf_dvd_iff_zpow_eq_one.mpr hz
      have hd2 : (e : ℤ) ∣ i := by
        have h3 : (e : ℤ) * ((2 ^ k : ℕ) : ℤ) ∣ i * ((2 ^ k : ℕ) : ℤ) := by
          exact_mod_cast hd
        exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hk0.ne') h3
      obtain ⟨i', rfl⟩ := hd2
      exact mem_zpowers_iff.mpr ⟨i', by rw [zpow_mul, zpow_natCast]⟩

theorem k3_cyclic_comm {G : Type} [Group G] {T : Subgroup G} (hT : IsCyclic ↥T) {a b : G}
    (ha : a ∈ T) (hb : b ∈ T) : a * b = b * a := by
  have := hT
  have h : (⟨a, ha⟩ : ↥T) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := IsMulCommutative.is_comm.comm _ _
  exact congrArg Subtype.val h

theorem k3_orderOf_conj {G : Type} [Group G] (a n : G) : orderOf (a * n * a⁻¹) = orderOf n := by
  have := MulEquiv.orderOf_eq (MulAut.conj a) n
  rwa [MulAut.conj_apply] at this

theorem k3_comm_of_conj {G : Type} [Group G] {a u : G} (h : a * u * a⁻¹ = u) : a * u = u * a := by
  calc a * u = (a * u * a⁻¹) * a := by group
    _ = u * a := by rw [h]

theorem k3_conj_cent {G : Type} [Group G] {H H' : Subgroup G} {a u u' w : G}
    (hconj : ∀ n ∈ H, a * n * a⁻¹ ∈ H') (hw : ∀ h ∈ H', h * w = w * h)
    (h : a * u * a⁻¹ = u' * w) :
    ∀ n ∈ H ⊓ centralizer ({u} : Set G), a * n * a⁻¹ ∈ H' ⊓ centralizer ({u'} : Set G) := by
  rintro n ⟨hnH, hnu⟩
  have hc : a * n * a⁻¹ ∈ H' := hconj n hnH
  refine ⟨hc, mem_centralizer_singleton_iff.mpr ?_⟩
  have hnu' : n * u = u * n := mem_centralizer_singleton_iff.mp hnu
  have hcα : (a * n * a⁻¹) * (a * u * a⁻¹) = (a * u * a⁻¹) * (a * n * a⁻¹) := by
    calc (a * n * a⁻¹) * (a * u * a⁻¹) = a * (n * u) * a⁻¹ := by group
      _ = a * (u * n) * a⁻¹ := by rw [hnu']
      _ = (a * u * a⁻¹) * (a * n * a⁻¹) := by group
  have hcw : (a * n * a⁻¹) * w = w * (a * n * a⁻¹) := hw _ hc
  have hu : u' = (a * u * a⁻¹) * w⁻¹ := by rw [h]; group
  have h1 : Commute (a * n * a⁻¹) (a * u * a⁻¹) := hcα
  have h2 : Commute (a * n * a⁻¹) w := hcw
  have h3 : Commute (a * n * a⁻¹) ((a * u * a⁻¹) * w⁻¹) := h1.mul_right h2.inv_right
  rw [← hu] at h3
  exact h3.eq

theorem k3_pow_mem_E {G : Type} [Group G] {T E : Subgroup G} {e N : ℕ} (he : Odd e)
    (hcard : Nat.card ↥T = e * N) (hE : ∀ x : G, x ∈ E ↔ x ∈ T ∧ Odd (orderOf x)) {a : G}
    (ha : a ∈ T) : a ^ N ∈ E := by
  rw [hE]
  refine ⟨T.pow_mem ha N, ?_⟩
  have h1 : a ^ (Nat.card ↥T) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard T ha)
  have h2 : (a ^ N) ^ e = 1 := by rw [← pow_mul, mul_comm, ← hcard]; exact h1
  exact Odd.of_dvd_nat he (orderOf_dvd_of_pow_eq_one h2)

theorem k3_mul_mem_T {G : Type} [Group G] {H : Subgroup G} {a a₀ u z : G} (ha : a ∈ H)
    (ha₀ : a₀ ∈ H) (hzc : ∀ h ∈ H, h * z = z * h) (hzz : z * z = 1) (hau : a * u * a⁻¹ = u * z)
    (hia : a₀ * u * a₀⁻¹ = u * z) : a * a₀ ∈ H ⊓ centralizer ({u} : Set G) := by
  have hconjz : a * z * a⁻¹ = z := by
    calc a * z * a⁻¹ = z * a * a⁻¹ := by rw [hzc a ha]
      _ = z := by group
  have e1 : (a * a₀) * u * (a * a₀)⁻¹ = u := by
    calc (a * a₀) * u * (a * a₀)⁻¹ = a * (a₀ * u * a₀⁻¹) * a⁻¹ := by group
      _ = a * (u * z) * a⁻¹ := by rw [hia]
      _ = (a * u * a⁻¹) * (a * z * a⁻¹) := by group
      _ = (u * z) * z := by rw [hau, hconjz]
      _ = u := by rw [mul_assoc, hzz, mul_one]
  exact ⟨H.mul_mem ha ha₀, mem_centralizer_singleton_iff.mpr (k3_comm_of_conj e1)⟩

end General

section Model

theorem k3_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    Nonempty (↥(centralizer ({a} : Set A)) ≃* ↥(centralizer ({e a} : Set B))) := by
  have hmap : (centralizer ({a} : Set A)).map e.toMonoidHom = centralizer ({e a} : Set B) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg e h
      simpa using this
    · intro h
      apply e.injective
      simpa using h
  exact ⟨(Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

theorem k3_model {G : Type} [Group G] {q : ℕ} {z : G} {H : Subgroup G}
    (hH : HasSL2Model ↥H (fun r => r = q)) (hqodd : Odd q) (hq5 : 5 ≤ q)
    (hzH : z ∈ H) (hz : orderOf z = 2) (hzc : ∀ h ∈ H, h * z = z * h)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hq4 : (q : ℤ) ≡ ε [ZMOD 4]) (d : ℕ) (hd : (d : ℤ) = q - ε) :
    (∀ a ∈ H, a * a = 1 → a = 1 ∨ a = z) ∧
    (∀ a ∈ H, ∀ b ∈ H, a * a = z → b * b = z → ∃ g ∈ H, g * a * g⁻¹ = b) ∧
    (∀ a ∈ H, a * a = z → IsCyclic ↥(H ⊓ centralizer ({a} : Set G)) ∧
      Nat.card ↥(H ⊓ centralizer ({a} : Set G)) = d) := by
  obtain ⟨F, hFfield, hFfin, hFq, ⟨e⟩⟩ := hH
  have hFq' : Nat.card F = q := hFq
  have hF : IVK.L2Field F := ⟨by rw [hFq']; exact hqodd, by rw [hFq']; omega⟩
  let ψ : ↥H ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hz' : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hcen : ∀ k : ↥H, k * (⟨z, hzH⟩ : ↥H) = ⟨z, hzH⟩ * k := fun k => Subtype.ext (hzc k k.2)
  obtain ⟨h2, hψz⟩ := IVK.sl_central_involution ψ ⟨z, hzH⟩ hz' hcen
  refine ⟨?_, ?_, ?_⟩
  · intro a ha ha2
    have hinv : (ψ ⟨a, ha⟩)⁻¹ = ψ ⟨a, ha⟩ := by
      rw [← map_inv]
      congr 1
      apply Subtype.ext
      exact inv_eq_of_mul_eq_one_right ha2
    rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 _ hinv with
      h1 | h1
    · left
      have : (⟨a, ha⟩ : ↥H) = 1 := ψ.injective (by rw [h1, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨a, ha⟩ : ↥H) = ⟨z, hzH⟩ := ψ.injective (by rw [h1, hψz])
      exact congrArg Subtype.val this
  · intro a ha b hb haz hbz
    have hF2 : ringChar F ≠ 2 := by
      intro hc
      apply h2
      have := CharP.cast_eq_zero F (ringChar F)
      rw [hc] at this
      exact_mod_cast this
    have hx : ψ ⟨a, ha⟩ * ψ ⟨a, ha⟩ = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
      rw [← map_mul, ← hψz]
      congr 1
      exact Subtype.ext haz
    have hy : ψ ⟨b, hb⟩ * ψ ⟨b, hb⟩ = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
      rw [← map_mul, ← hψz]
      congr 1
      exact Subtype.ext hbz
    obtain ⟨g, hg⟩ := IVK.L2Torus.exists_sl_conj_of_sq_eq_neg_one hF2 h2 _ _ hx hy
    refine ⟨((ψ.symm g : ↥H) : G), (ψ.symm g).2, ?_⟩
    have : ψ.symm g * ⟨a, ha⟩ * (ψ.symm g)⁻¹ = ⟨b, hb⟩ := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]
    exact congrArg Subtype.val this
  · intro a ha haz
    have ho4 : orderOf a = 4 := by
      have hz2 : z ^ 2 = 1 := by
        have := pow_orderOf_eq_one z
        rwa [hz] at this
      have h1 : ¬ a ^ 2 ^ 1 = 1 := by
        rw [pow_one, pow_two, haz]
        intro h
        have := hz
        rw [h, orderOf_one] at this
        omega
      have h2' : a ^ 2 ^ (1 + 1) = 1 := by
        calc a ^ 2 ^ (1 + 1) = a ^ (2 * 2) := by norm_num
          _ = (a ^ 2) ^ 2 := pow_mul a 2 2
          _ = z ^ 2 := by rw [pow_two a, haz]
          _ = 1 := hz2
      have := orderOf_eq_prime_pow (p := 2) (n := 1) h1 h2'
      simpa using this
    have hû : orderOf (e ⟨a, ha⟩) = 4 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact ho4
    have hq' : (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by rw [hFq']; exact hq4
    have hd' : (d : ℤ) = Nat.card F - ε := by rw [hFq']; exact hd
    obtain ⟨hcyc, hcard⟩ := IVK.sl2_centralizer_order_four hF ε hε hq' d hd' (e ⟨a, ha⟩) hû
    obtain ⟨φ⟩ := k3_centralizer_mulEquiv e (⟨a, ha⟩ : ↥H)
    have hmap : (centralizer ({(⟨a, ha⟩ : ↥H)} : Set ↥H)).map H.subtype =
        H ⊓ centralizer ({a} : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))⟩
      · rintro ⟨hx, hxc⟩
        exact ⟨⟨x, hx⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hxc)), rfl⟩
    have hcyc' : IsCyclic ↥(centralizer ({(⟨a, ha⟩ : ↥H)} : Set ↥H)) := φ.isCyclic.2 hcyc
    have hcard' : Nat.card ↥(centralizer ({(⟨a, ha⟩ : ↥H)} : Set ↥H)) = d := by
      rw [Nat.card_congr φ.toEquiv]; exact hcard
    rw [← hmap]
    refine ⟨?_, ?_⟩
    · exact (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).isCyclic.1 hcyc'
    · rw [Subgroup.card_map_of_injective H.subtype_injective]; exact hcard'

end Model

section Elem

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

omit [Finite G] in
theorem k3_eps (hs : SPLSetup D.toSPLNot0) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ((D.q : ℤ) ≡ ε [ZMOD 4]) ∧ ((D.d : ℤ) = (D.q : ℤ) - ε) := by
  obtain ⟨ε, hε, hq4, hd⟩ := exists_eps D hs
  have h4 := four_dvd_d D.toSPLNot0 hs.odd_q
  have h2 : 2 * (D.d / 2) = D.d := by omega
  rw [h2] at hd
  exact ⟨ε, hε, hq4, hd⟩

omit [Finite G] in
theorem k3_model₁ (hs : SPLSetup D.toSPLNot0) :
    (∀ a ∈ D.K₁, a * a = 1 → a = 1 ∨ a = D.z) ∧
    (∀ a ∈ D.K₁, ∀ b ∈ D.K₁, a * a = D.z → b * b = D.z → ∃ g ∈ D.K₁, g * a * g⁻¹ = b) ∧
    (∀ a ∈ D.K₁, a * a = D.z → IsCyclic ↥(D.K₁ ⊓ centralizer ({a} : Set G)) ∧
      Nat.card ↥(D.K₁ ⊓ centralizer ({a} : Set G)) = D.d) := by
  obtain ⟨ε, hε, hq4, hd⟩ := k3_eps D hs
  exact k3_model hs.comps.sl₁ hs.odd_q hs.q_ge (z_mem_K₁' D hs) hs.syl.z_inv
    (fun _ hh => hs.comps.cz₁ hh) ε hε hq4 D.d hd

omit [Finite G] in
theorem k3_model₂ (hs : SPLSetup D.toSPLNot0) :
    (∀ a ∈ D.K₂, a * a = 1 → a = 1 ∨ a = D.z) ∧
    (∀ a ∈ D.K₂, ∀ b ∈ D.K₂, a * a = D.z → b * b = D.z → ∃ g ∈ D.K₂, g * a * g⁻¹ = b) ∧
    (∀ a ∈ D.K₂, a * a = D.z → IsCyclic ↥(D.K₂ ⊓ centralizer ({a} : Set G)) ∧
      Nat.card ↥(D.K₂ ⊓ centralizer ({a} : Set G)) = D.d) := by
  obtain ⟨ε, hε, hq4, hd⟩ := k3_eps D hs
  exact k3_model hs.comps.sl₂ hs.odd_q hs.q_ge (z_mem_K₂' D hs) hs.syl.z_inv
    (fun _ hh => hs.comps.cz₂ hh) ε hε hq4 D.d hd

omit [Finite G] in
theorem k3_zpowers_cases (hs : SPLSetup D.toSPLNot0) {w : G} (hw : w ∈ zpowers D.z) :
    w = 1 ∨ w = D.z := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw
  exact zpow_z_cases' D hs j

omit [Finite G] in
theorem k3_w_sq (hs : SPLSetup D.toSPLNot0) {w : G} (hw : w ∈ zpowers D.z) : w * w = 1 := by
  rcases k3_zpowers_cases D hs hw with h | h
  · rw [h, one_mul]
  · rw [h]; exact z_mul_z' D hs

theorem k3_decomp (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.K) (hu2 : orderOf u = 2)
    (huz : u ≠ D.z) :
    ∃ u₁ ∈ D.K₁, ∃ u₂ ∈ D.K₂, u = u₁ * u₂ ∧ u₁ * u₁ = D.z ∧ u₂ * u₂ = D.z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hs.comps.comm hu
  have huu : (a * b) * (a * b) = 1 := by
    have := pow_orderOf_eq_one (a * b)
    rwa [hu2, pow_two] at this
  have hab : a * b = b * a := hs.comps.comm a ha b hb
  have hsq : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hab]
      _ = (a * b) * (a * b) := by group
      _ = 1 := huu
  have hbb : b * b = (a * a)⁻¹ := eq_inv_of_mul_eq_one_right hsq
  have haaK₂ : a * a ∈ D.K₂ := by
    have : a * a = (b * b)⁻¹ := by rw [hbb, inv_inv]
    rw [this]
    exact D.K₂.inv_mem (D.K₂.mul_mem hb hb)
  have haaz : a * a ∈ zpowers D.z := by
    rw [← hs.comps.inf_eq]; exact ⟨D.K₁.mul_mem ha ha, haaK₂⟩
  rcases k3_zpowers_cases D hs haaz with h1 | h1
  ·
    exfalso
    have hb1 : b * b = 1 := by rw [h1, one_mul] at hsq; exact hsq
    rcases (k3_model₁ D hs).1 a ha h1 with rfl | rfl <;>
      rcases (k3_model₂ D hs).1 b hb hb1 with rfl | rfl
    · rw [one_mul, orderOf_one] at hu2; omega
    · rw [one_mul] at hu2 huz; exact huz rfl
    · rw [mul_one] at huz; exact huz rfl
    · rw [z_mul_z' D hs, orderOf_one] at hu2; omega
  · refine ⟨a, ha, b, hb, rfl, h1, ?_⟩
    rw [h1] at hbb
    have hz1 : D.z⁻¹ = D.z := inv_eq_of_mul_eq_one_right (z_mul_z' D hs)
    rw [hbb, hz1]

theorem K3_decomp (hs : SPLSetup D.toSPLNot0) {u : G}
    (hu : u ∈ D.K) (hu2 : orderOf u = 2) (huz : u ≠ D.z) (hut : D.t * u = u * D.t) :
    ∃ u₁ ∈ D.K₁, ∃ u₂ ∈ D.K₂, u = u₁ * u₂ ∧ u₁ ^ 2 = D.z ∧ u₂ ^ 2 = D.z := by
  have _h := hut
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl, h₁, h₂⟩ := k3_decomp D hs hu hu2 huz
  exact ⟨u₁, hu₁, u₂, hu₂, rfl, by rw [pow_two]; exact h₁, by rw [pow_two]; exact h₂⟩

theorem k3_split_prod (hs : SPLSetup D.toSPLNot0) {α β u₁ u₂ : G} (hα : α ∈ D.K₁)
    (hβ : β ∈ D.K₂) (hu₁ : u₁ ∈ D.K₁) (hu₂ : u₂ ∈ D.K₂) (h : α * β = u₁ * u₂) :
    ∃ w ∈ zpowers D.z, α = u₁ * w ∧ β = u₂ * w := by
  have e : u₁⁻¹ * α = u₂ * β⁻¹ := by
    calc u₁⁻¹ * α = u₁⁻¹ * (α * β) * β⁻¹ := by group
      _ = u₁⁻¹ * (u₁ * u₂) * β⁻¹ := by rw [h]
      _ = u₂ * β⁻¹ := by group
  have hw : u₁⁻¹ * α ∈ zpowers D.z := by
    rw [← hs.comps.inf_eq]
    refine ⟨D.K₁.mul_mem (D.K₁.inv_mem hu₁) hα, ?_⟩
    rw [e]
    exact D.K₂.mul_mem hu₂ (D.K₂.inv_mem hβ)
  obtain ⟨w, hwdef⟩ : ∃ w : G, w = u₁⁻¹ * α := ⟨_, rfl⟩
  rw [← hwdef] at hw
  have hw2 := k3_w_sq D hs hw
  have hwu₂ : w * u₂ = u₂ * w := z_central_in_K D hs hw u₂ (Subgroup.mem_sup_right hu₂)
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  refine ⟨w, hw, by rw [hwdef]; group, ?_⟩
  have e' : w = u₂ * β⁻¹ := by rw [hwdef]; exact e
  have hβe : β = w⁻¹ * u₂ := by rw [e']; group
  rw [hβe, hw', hwu₂]

theorem k3_swap (hs : SPLSetup D.toSPLNot0) {u₁ u₂ : G} (hu₁ : u₁ ∈ D.K₁) (hu₂ : u₂ ∈ D.K₂)
    (hut : D.t * (u₁ * u₂) = (u₁ * u₂) * D.t) :
    ∃ w ∈ zpowers D.z, D.t * u₁ * D.t⁻¹ = u₂ * w ∧ D.t * u₂ * D.t⁻¹ = u₁ * w := by
  have ha : D.t * u₁ * D.t⁻¹ ∈ D.K₂ := t_conj_K₁' D hs u₁ hu₁
  have hb : D.t * u₂ * D.t⁻¹ ∈ D.K₁ := t_conj_K₂' D hs u₂ hu₂
  have hprod : (D.t * u₂ * D.t⁻¹) * (D.t * u₁ * D.t⁻¹) = u₁ * u₂ := by
    calc (D.t * u₂ * D.t⁻¹) * (D.t * u₁ * D.t⁻¹) = D.t * (u₂ * u₁) * D.t⁻¹ := by group
      _ = D.t * (u₁ * u₂) * D.t⁻¹ := by rw [hs.comps.comm u₁ hu₁ u₂ hu₂]
      _ = u₁ * u₂ := by rw [hut]; group
  obtain ⟨w, hw, h1, h2⟩ := k3_split_prod D hs hb ha hu₁ hu₂ hprod
  exact ⟨w, hw, h2, h1⟩

theorem k3_conj_prod {a b u₁ u₂ : G} (hs : SPLSetup D.toSPLNot0) (ha : a ∈ D.K₁)
    (hb : b ∈ D.K₂) (hu₁ : u₁ ∈ D.K₁) (hu₂ : u₂ ∈ D.K₂) :
    (a * b) * (u₁ * u₂) * (a * b)⁻¹ = (a * u₁ * a⁻¹) * (b * u₂ * b⁻¹) := by
  have hβ : b * u₂ * b⁻¹ ∈ D.K₂ := D.K₂.mul_mem (D.K₂.mul_mem hb hu₂) (D.K₂.inv_mem hb)
  have hbu : b * u₁ = u₁ * b := (hs.comps.comm u₁ hu₁ b hb).symm
  have hβa : (b * u₂ * b⁻¹) * a⁻¹ = a⁻¹ * (b * u₂ * b⁻¹) :=
    (hs.comps.comm a⁻¹ (D.K₁.inv_mem ha) _ hβ).symm
  calc (a * b) * (u₁ * u₂) * (a * b)⁻¹ = a * (b * u₁) * u₂ * b⁻¹ * a⁻¹ := by group
    _ = a * (u₁ * b) * u₂ * b⁻¹ * a⁻¹ := by rw [hbu]
    _ = a * u₁ * ((b * u₂ * b⁻¹) * a⁻¹) := by group
    _ = a * u₁ * (a⁻¹ * (b * u₂ * b⁻¹)) := by rw [hβa]
    _ = (a * u₁ * a⁻¹) * (b * u₂ * b⁻¹) := by group

theorem k3_X_decomp (hs : SPLSetup D.toSPLNot0) {u₁ u₂ x : G} (hu₁ : u₁ ∈ D.K₁)
    (hu₂ : u₂ ∈ D.K₂) (hx : x ∈ D.K) (hxu : x * (u₁ * u₂) = (u₁ * u₂) * x) :
    ∃ a ∈ D.K₁, ∃ b ∈ D.K₂, ∃ w ∈ zpowers D.z, x = a * b ∧ a * u₁ * a⁻¹ = u₁ * w ∧
      b * u₂ * b⁻¹ = u₂ * w := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hs.comps.comm hx
  have hα : a * u₁ * a⁻¹ ∈ D.K₁ := D.K₁.mul_mem (D.K₁.mul_mem ha hu₁) (D.K₁.inv_mem ha)
  have hβ : b * u₂ * b⁻¹ ∈ D.K₂ := D.K₂.mul_mem (D.K₂.mul_mem hb hu₂) (D.K₂.inv_mem hb)
  have hprod : (a * u₁ * a⁻¹) * (b * u₂ * b⁻¹) = u₁ * u₂ := by
    rw [← k3_conj_prod D hs ha hb hu₁ hu₂, hxu]; group
  obtain ⟨w, hw, h1, h2⟩ := k3_split_prod D hs hα hβ hu₁ hu₂ hprod
  exact ⟨a, ha, b, hb, w, hw, rfl, h1, h2⟩

omit [Finite G] in
theorem k3_odd_cent (hs : SPLSetup D.toSPLNot0) {u₁ x : G} (hx : x ∈ D.K) {w : G}
    (hw : w ∈ zpowers D.z) (h : x * u₁ * x⁻¹ = u₁ * w) (hodd : Odd (orderOf x)) :
    x * u₁ = u₁ * x := by
  have hw2 := k3_w_sq D hs hw
  have hxw : x * w = w * x := (z_central_in_K D hs hw x hx).symm
  have e : x * u₁ = u₁ * w * x := by
    calc x * u₁ = (x * u₁ * x⁻¹) * x := by group
      _ = u₁ * w * x := by rw [h]
  have h1 : (x * x) * u₁ = u₁ * (x * x) := by
    calc (x * x) * u₁ = x * (x * u₁) := by group
      _ = x * (u₁ * w * x) := by rw [e]
      _ = (x * u₁) * w * x := by group
      _ = (u₁ * w * x) * w * x := by rw [e]
      _ = u₁ * w * (x * w) * x := by group
      _ = u₁ * w * (w * x) * x := by rw [hxw]
      _ = u₁ * (w * w) * (x * x) := by group
      _ = u₁ * (x * x) := by rw [hw2]; group
  obtain ⟨r, hr⟩ := hodd
  have hxx : Commute (x ^ 2) u₁ := by
    show x ^ 2 * u₁ = u₁ * x ^ 2
    rw [pow_two]; exact h1
  have hxp : (x ^ 2) ^ (r + 1) = x := by
    rw [← pow_mul]
    have e2 : 2 * (r + 1) = orderOf x + 1 := by omega
    rw [e2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hc : Commute ((x ^ 2) ^ (r + 1)) u₁ := hxx.pow_left (r + 1)
  rw [hxp] at hc
  exact hc.eq

omit [Finite G] in
theorem k3_exists_iota (hs : SPLSetup D.toSPLNot0) {u₁ u₂ : G} (hu₁ : u₁ ∈ D.K₁)
    (hu₂ : u₂ ∈ D.K₂) (hsq₁ : u₁ * u₁ = D.z) (hsq₂ : u₂ * u₂ = D.z) :
    ∃ a₀ ∈ D.K₁, ∃ b₀ ∈ D.K₂, a₀ * u₁ * a₀⁻¹ = u₁ * D.z ∧ b₀ * u₂ * b₀⁻¹ = u₂ * D.z := by
  have hzz := z_mul_z' D hs
  have hz₁ : u₁ * D.z = D.z * u₁ := hs.comps.cz₁ hu₁
  have hz₂ : u₂ * D.z = D.z * u₂ := hs.comps.cz₂ hu₂
  have hsq₁' : (u₁ * D.z) * (u₁ * D.z) = D.z := by
    calc (u₁ * D.z) * (u₁ * D.z) = u₁ * (D.z * u₁) * D.z := by group
      _ = u₁ * (u₁ * D.z) * D.z := by rw [hz₁]
      _ = (u₁ * u₁) * (D.z * D.z) := by group
      _ = D.z := by rw [hsq₁, hzz, mul_one]
  have hsq₂' : (u₂ * D.z) * (u₂ * D.z) = D.z := by
    calc (u₂ * D.z) * (u₂ * D.z) = u₂ * (D.z * u₂) * D.z := by group
      _ = u₂ * (u₂ * D.z) * D.z := by rw [hz₂]
      _ = (u₂ * u₂) * (D.z * D.z) := by group
      _ = D.z := by rw [hsq₂, hzz, mul_one]
  obtain ⟨a₀, ha₀, h₁⟩ := (k3_model₁ D hs).2.1 u₁ hu₁ (u₁ * D.z)
    (D.K₁.mul_mem hu₁ (z_mem_K₁' D hs)) hsq₁ hsq₁'
  obtain ⟨b₀, hb₀, h₂⟩ := (k3_model₂ D hs).2.1 u₂ hu₂ (u₂ * D.z)
    (D.K₂.mul_mem hu₂ (z_mem_K₂' D hs)) hsq₂ hsq₂'
  exact ⟨a₀, ha₀, b₀, hb₀, h₁, h₂⟩

theorem k3_T₁_comm (hs : SPLSetup D.toSPLNot0) {u₁ u₂ n : G} (hu₂ : u₂ ∈ D.K₂)
    (hn : n ∈ D.K₁ ⊓ centralizer ({u₁} : Set G)) : n * (u₁ * u₂) = (u₁ * u₂) * n := by
  have h1 : n * u₁ = u₁ * n := mem_centralizer_singleton_iff.mp hn.2
  have h2 : n * u₂ = u₂ * n := hs.comps.comm n hn.1 u₂ hu₂
  calc n * (u₁ * u₂) = (n * u₁) * u₂ := by group
    _ = (u₁ * n) * u₂ := by rw [h1]
    _ = u₁ * (n * u₂) := by group
    _ = u₁ * (u₂ * n) := by rw [h2]
    _ = (u₁ * u₂) * n := by group

theorem k3_T₂_comm (hs : SPLSetup D.toSPLNot0) {u₁ u₂ m : G} (hu₁ : u₁ ∈ D.K₁)
    (hm : m ∈ D.K₂ ⊓ centralizer ({u₂} : Set G)) : m * (u₁ * u₂) = (u₁ * u₂) * m := by
  have h1 : m * u₁ = u₁ * m := (hs.comps.comm u₁ hu₁ m hm.1).symm
  have h2 : m * u₂ = u₂ * m := mem_centralizer_singleton_iff.mp hm.2
  calc m * (u₁ * u₂) = (m * u₁) * u₂ := by group
    _ = (u₁ * m) * u₂ := by rw [h1]
    _ = u₁ * (m * u₂) := by group
    _ = u₁ * (u₂ * m) := by rw [h2]
    _ = (u₁ * u₂) * m := by group

theorem k3_T_inf (hs : SPLSetup D.toSPLNot0) {u₁ u₂ : G} (hu₁ : u₁ ∈ D.K₁) (hu₂ : u₂ ∈ D.K₂) :
    (D.K₁ ⊓ centralizer ({u₁} : Set G)) ⊓ (D.K₂ ⊓ centralizer ({u₂} : Set G)) =
      zpowers D.z := by
  apply le_antisymm
  · intro x hx
    rw [← hs.comps.inf_eq]
    exact ⟨hx.1.1, hx.2.1⟩
  · rw [zpowers_le]
    exact ⟨⟨z_mem_K₁' D hs, mem_centralizer_singleton_iff.mpr (hs.comps.cz₁ hu₁).symm⟩,
      ⟨z_mem_K₂' D hs, mem_centralizer_singleton_iff.mpr (hs.comps.cz₂ hu₂).symm⟩⟩

theorem k3_conj_u₁ (hs : SPLSetup D.toSPLNot0) {a b u₁ : G} (hb : b ∈ D.K₂) (hu₁ : u₁ ∈ D.K₁) :
    (a * b) * u₁ * (a * b)⁻¹ = a * u₁ * a⁻¹ := by
  have hbu : b * u₁ = u₁ * b := (hs.comps.comm u₁ hu₁ b hb).symm
  calc (a * b) * u₁ * (a * b)⁻¹ = a * (b * u₁) * b⁻¹ * a⁻¹ := by group
    _ = a * (u₁ * b) * b⁻¹ * a⁻¹ := by rw [hbu]
    _ = a * u₁ * a⁻¹ := by group

theorem k3_E_le (hs : SPLSetup D.toSPLNot0) {u₁ u₂ : G} (hu₁ : u₁ ∈ D.K₁) (hu₂ : u₂ ∈ D.K₂)
    {E₁ E₂ : Subgroup G}
    (hE₁ : ∀ x : G, x ∈ E₁ ↔ x ∈ D.K₁ ⊓ centralizer ({u₁} : Set G) ∧ Odd (orderOf x))
    (hE₂ : ∀ x : G, x ∈ E₂ ↔ x ∈ D.K₂ ⊓ centralizer ({u₂} : Set G) ∧ Odd (orderOf x))
    (hodd : Odd (Nat.card ↥(E₁ ⊔ E₂))) :
    E₁ ⊔ E₂ ≤ pPrimeCoreOf 2 (D.K ⊓ centralizer ({u₁ * u₂} : Set G)) := by
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
    hs.comps.comm a ((hE₁ a).mp ha).1.1 b ((hE₂ b).mp hb).1.1
  have hle : E₁ ⊔ E₂ ≤ D.K ⊓ centralizer ({u₁ * u₂} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · have hxT := ((hE₁ x).mp hx).1
      exact ⟨Subgroup.mem_sup_left hxT.1,
        mem_centralizer_singleton_iff.mpr (k3_T₁_comm D hs hu₂ hxT)⟩
    · have hxT := ((hE₂ x).mp hx).1
      exact ⟨Subgroup.mem_sup_right hxT.1,
        mem_centralizer_singleton_iff.mpr (k3_T₂_comm D hs hu₁ hxT)⟩
  refine Stage1.Thm3.Sec4.le_pPrimeCoreOf' hle ?_ hodd
  have h1 : ∀ x ∈ D.K ⊓ centralizer ({u₁ * u₂} : Set G), ∀ n ∈ E₁, x * n * x⁻¹ ∈ E₁ := by
    intro x hx n hn
    obtain ⟨a, ha, b, hb, w, hw, rfl, hau, hbu⟩ :=
      k3_X_decomp D hs hu₁ hu₂ hx.1 (mem_centralizer_singleton_iff.mp hx.2)
    obtain ⟨hnT, hnodd⟩ := (hE₁ n).mp hn
    have hbn : b * n = n * b := (hs.comps.comm n hnT.1 b hb).symm
    have e : a * b * n * (a * b)⁻¹ = a * n * a⁻¹ := by
      calc a * b * n * (a * b)⁻¹ = a * (b * n) * b⁻¹ * a⁻¹ := by group
        _ = a * (n * b) * b⁻¹ * a⁻¹ := by rw [hbn]
        _ = a * n * a⁻¹ := by group
    rw [e]
    have hT := k3_conj_cent (H := D.K₁) (H' := D.K₁)
      (fun m hm => D.K₁.mul_mem (D.K₁.mul_mem ha hm) (D.K₁.inv_mem ha))
      (fun h hh => (z_central_in_K D hs hw h (Subgroup.mem_sup_left hh)).symm) hau n hnT
    exact (hE₁ _).mpr ⟨hT, by rw [k3_orderOf_conj]; exact hnodd⟩
  have h2 : ∀ x ∈ D.K ⊓ centralizer ({u₁ * u₂} : Set G), ∀ n ∈ E₂, x * n * x⁻¹ ∈ E₂ := by
    intro x hx n hn
    obtain ⟨a, ha, b, hb, w, hw, rfl, hau, hbu⟩ :=
      k3_X_decomp D hs hu₁ hu₂ hx.1 (mem_centralizer_singleton_iff.mp hx.2)
    obtain ⟨hnT, hnodd⟩ := (hE₂ n).mp hn
    have hbn : b * n * b⁻¹ ∈ D.K₂ := D.K₂.mul_mem (D.K₂.mul_mem hb hnT.1) (D.K₂.inv_mem hb)
    have han : a * (b * n * b⁻¹) = (b * n * b⁻¹) * a := hs.comps.comm a ha _ hbn
    have e : a * b * n * (a * b)⁻¹ = b * n * b⁻¹ := by
      calc a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        _ = (b * n * b⁻¹) * a * a⁻¹ := by rw [han]
        _ = b * n * b⁻¹ := by group
    rw [e]
    have hT := k3_conj_cent (H := D.K₂) (H' := D.K₂)
      (fun m hm => D.K₂.mul_mem (D.K₂.mul_mem hb hm) (D.K₂.inv_mem hb))
      (fun h hh => (z_central_in_K D hs hw h (Subgroup.mem_sup_right hh)).symm) hbu n hnT
    exact (hE₂ _).mpr ⟨hT, by rw [k3_orderOf_conj]; exact hnodd⟩
  intro x hx n hn
  obtain ⟨n₁, hn₁, n₂, hn₂, rfl⟩ := mem_sup_of_commute hcomm hn
  have e : x * (n₁ * n₂) * x⁻¹ = (x * n₁ * x⁻¹) * (x * n₂ * x⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem_sup (h1 x hx n₁ hn₁) (h2 x hx n₂ hn₂)

theorem k3_Eu_le (hs : SPLSetup D.toSPLNot0) {u₁ u₂ : G} (hu₁ : u₁ ∈ D.K₁) (hu₂ : u₂ ∈ D.K₂)
    {E₁ E₂ : Subgroup G}
    (hE₁ : ∀ x : G, x ∈ E₁ ↔ x ∈ D.K₁ ⊓ centralizer ({u₁} : Set G) ∧ Odd (orderOf x))
    (hE₂ : ∀ x : G, x ∈ E₂ ↔ x ∈ D.K₂ ⊓ centralizer ({u₂} : Set G) ∧ Odd (orderOf x))
    (he : Odd D.e)
    (hcard₁ : Nat.card ↥(D.K₁ ⊓ centralizer ({u₁} : Set G)) = D.e * 2 ^ (D.n - 1))
    (hcard₂ : Nat.card ↥(D.K₂ ⊓ centralizer ({u₂} : Set G)) = D.e * 2 ^ (D.n - 1)) :
    pPrimeCoreOf 2 (D.K ⊓ centralizer ({u₁ * u₂} : Set G)) ≤ E₁ ⊔ E₂ := by
  intro x hx
  have hxX := TwoThin.pPrimeCoreOf_le _ hx
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd _) (Subgroup.orderOf_dvd_natCard _ hx)
  obtain ⟨a, ha, b, hb, w, hw, rfl, hau, hbu⟩ :=
    k3_X_decomp D hs hu₁ hu₂ hxX.1 (mem_centralizer_singleton_iff.mp hxX.2)
  have hxu₁ : (a * b) * u₁ * (a * b)⁻¹ = u₁ * w := by
    rw [k3_conj_u₁ D hs hb hu₁]; exact hau
  have hcent : (a * b) * u₁ = u₁ * (a * b) := k3_odd_cent D hs hxX.1 hw hxu₁ hxodd
  have hw1 : w = 1 := by
    have h1 : (a * b) * u₁ * (a * b)⁻¹ = u₁ := by rw [hcent]; group
    have h2 : u₁ * w = u₁ * 1 := by rw [mul_one, ← hxu₁, h1]
    exact mul_left_cancel h2
  rw [hw1, mul_one] at hau hbu
  have haT : a ∈ D.K₁ ⊓ centralizer ({u₁} : Set G) :=
    ⟨ha, mem_centralizer_singleton_iff.mpr (k3_comm_of_conj hau)⟩
  have hbT : b ∈ D.K₂ ⊓ centralizer ({u₂} : Set G) :=
    ⟨hb, mem_centralizer_singleton_iff.mpr (k3_comm_of_conj hbu)⟩
  have hcop : Nat.Coprime (orderOf (a * b)) (2 ^ (D.n - 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hxodd)
  have hmem : (a * b) ∈ zpowers ((a * b) ^ (2 ^ (D.n - 1))) := by
    have hle : zpowers ((a * b) ^ (2 ^ (D.n - 1))) ≤ zpowers (a * b) :=
      zpowers_le.mpr (Subgroup.pow_mem _ (mem_zpowers _) _)
    have hcardle : Nat.card ↥(zpowers (a * b)) ≤
        Nat.card ↥(zpowers ((a * b) ^ (2 ^ (D.n - 1)))) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, Nat.Coprime.orderOf_pow hcop]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcardle
    rw [heq]
    exact mem_zpowers _
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
  have hab : Commute (a ^ (2 ^ (D.n - 1))) (b ^ (2 ^ (D.n - 1))) :=
    hs.comps.comm _ (D.K₁.pow_mem ha _) _ (D.K₂.pow_mem hb _)
  have hxN : (a * b) ^ (2 ^ (D.n - 1)) = a ^ (2 ^ (D.n - 1)) * b ^ (2 ^ (D.n - 1)) :=
    Commute.mul_pow (hs.comps.comm a ha b hb : Commute a b) _
  have hmem₁ := k3_pow_mem_E he hcard₁ hE₁ haT
  have hmem₂ := k3_pow_mem_E he hcard₂ hE₂ hbT
  rw [← hj, hxN, Commute.mul_zpow hab]
  exact Subgroup.mul_mem_sup (E₁.zpow_mem hmem₁ j) (E₂.zpow_mem hmem₂ j)

theorem k3_card_X (hs : SPLSetup D.toSPLNot0) {u₁ u₂ : G} (hu₁ : u₁ ∈ D.K₁) (hu₂ : u₂ ∈ D.K₂)
    (hsq₁ : u₁ * u₁ = D.z) (hsq₂ : u₂ * u₂ = D.z)
    (hcard₁ : Nat.card ↥(D.K₁ ⊓ centralizer ({u₁} : Set G)) = D.d)
    (hcard₂ : Nat.card ↥(D.K₂ ⊓ centralizer ({u₂} : Set G)) = D.d) :
    Nat.card ↥(D.K ⊓ centralizer ({u₁ * u₂} : Set G)) = D.d * D.d := by
  set T₁ : Subgroup G := D.K₁ ⊓ centralizer ({u₁} : Set G) with hT₁
  set T₂ : Subgroup G := D.K₂ ⊓ centralizer ({u₂} : Set G) with hT₂
  set X : Subgroup G := D.K ⊓ centralizer ({u₁ * u₂} : Set G) with hX
  have hTcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a := fun a ha b hb =>
    hs.comps.comm a ha.1 b hb.1
  have hP₀X : T₁ ⊔ T₂ ≤ X := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact ⟨Subgroup.mem_sup_left hx.1,
        mem_centralizer_singleton_iff.mpr (k3_T₁_comm D hs hu₂ hx)⟩
    · exact ⟨Subgroup.mem_sup_right hx.1,
        mem_centralizer_singleton_iff.mpr (k3_T₂_comm D hs hu₁ hx)⟩
  have hP₀card : Nat.card ↥(T₁ ⊔ T₂) * 2 = D.d * D.d := by
    have h := k3_card_sup_mul_card_inf T₁ T₂ hTcomm
    rw [k3_T_inf D hs hu₁ hu₂, Nat.card_zpowers, hs.syl.z_inv, hcard₁, hcard₂] at h
    exact h
  obtain ⟨a₀, ha₀, b₀, hb₀, hia, hib⟩ := k3_exists_iota D hs hu₁ hu₂ hsq₁ hsq₂
  have hzz := z_mul_z' D hs
  have hιu : (a₀ * b₀) * (u₁ * u₂) = (u₁ * u₂) * (a₀ * b₀) := by
    have e := k3_conj_prod D hs ha₀ hb₀ hu₁ hu₂
    rw [hia, hib] at e
    have e2 : (u₁ * D.z) * (u₂ * D.z) = u₁ * u₂ := by
      have hz₂ : D.z * u₂ = u₂ * D.z := (hs.comps.cz₂ hu₂).symm
      calc (u₁ * D.z) * (u₂ * D.z) = u₁ * (D.z * u₂) * D.z := by group
        _ = u₁ * (u₂ * D.z) * D.z := by rw [hz₂]
        _ = u₁ * u₂ * (D.z * D.z) := by group
        _ = u₁ * u₂ := by rw [hzz, mul_one]
    rw [e2] at e
    calc (a₀ * b₀) * (u₁ * u₂) = (a₀ * b₀) * (u₁ * u₂) * (a₀ * b₀)⁻¹ * (a₀ * b₀) := by group
      _ = (u₁ * u₂) * (a₀ * b₀) := by rw [e]
  have hι : a₀ * b₀ ∈ X := ⟨Subgroup.mul_mem_sup ha₀ hb₀, mem_centralizer_singleton_iff.mpr hιu⟩
  have hP₀u₁ : T₁ ⊔ T₂ ≤ centralizer ({u₁} : Set G) := by
    refine sup_le (fun x hx => hx.2) (fun x hx => ?_)
    exact mem_centralizer_singleton_iff.mpr (hs.comps.comm u₁ hu₁ x hx.1).symm
  have hι_nmem : a₀ * b₀ ∉ T₁ ⊔ T₂ := by
    intro hmem
    have hc : (a₀ * b₀) * u₁ = u₁ * (a₀ * b₀) := mem_centralizer_singleton_iff.mp (hP₀u₁ hmem)
    have e1 : (a₀ * b₀) * u₁ * (a₀ * b₀)⁻¹ = u₁ := by rw [hc]; group
    rw [k3_conj_u₁ D hs hb₀ hu₁, hia] at e1
    have h2 : u₁ * D.z = u₁ * 1 := by rw [mul_one]; exact e1
    exact z_ne_one' D hs (mul_left_cancel h2)
  have hrel : (T₁ ⊔ T₂).relIndex X = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨a₀ * b₀, hι, hι_nmem, ?_⟩
    intro x hx
    obtain ⟨a, ha, b, hb, w, hw, rfl, hau, hbu⟩ :=
      k3_X_decomp D hs hu₁ hu₂ hx.1 (mem_centralizer_singleton_iff.mp hx.2)
    rcases k3_zpowers_cases D hs hw with rfl | rfl
    · right
      rw [mul_one] at hau hbu
      exact Subgroup.mul_mem_sup ⟨ha, mem_centralizer_singleton_iff.mpr (k3_comm_of_conj hau)⟩
        ⟨hb, mem_centralizer_singleton_iff.mpr (k3_comm_of_conj hbu)⟩
    · left
      have hcomm : b * a₀ = a₀ * b := (hs.comps.comm a₀ ha₀ b hb).symm
      have e : (a * b) * (a₀ * b₀) = (a * a₀) * (b * b₀) := by
        calc (a * b) * (a₀ * b₀) = a * (b * a₀) * b₀ := by group
          _ = a * (a₀ * b) * b₀ := by rw [hcomm]
          _ = (a * a₀) * (b * b₀) := by group
      rw [e]
      exact Subgroup.mul_mem_sup
        (k3_mul_mem_T ha ha₀ (fun h hh => hs.comps.cz₁ hh) hzz hau hia)
        (k3_mul_mem_T hb hb₀ (fun h hh => hs.comps.cz₂ hh) hzz hbu hib)
  have h := k3_card_of_relIndex_two hP₀X hrel
  calc Nat.card ↥X = 2 * Nat.card ↥(T₁ ⊔ T₂) := h
    _ = Nat.card ↥(T₁ ⊔ T₂) * 2 := mul_comm _ _
    _ = D.d * D.d := hP₀card

theorem K3_elem (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.K) (hu2 : orderOf u = 2)
    (huz : u ≠ D.z) (hut : D.t * u = u * D.t) :
    (∃ E₁ E₂ : Subgroup G, E₁ ⊔ E₂ = D.Eu u ∧ E₁ ⊓ E₂ = ⊥ ∧
      (∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) ∧ IsCyclic ↥E₁ ∧ IsCyclic ↥E₂ ∧
      Nat.card ↥E₁ = D.e ∧ Nat.card ↥E₂ = D.e ∧
      (∀ a ∈ E₁, D.t * a * D.t⁻¹ ∈ E₂) ∧ (∀ a ∈ E₂, D.t * a * D.t⁻¹ ∈ E₁)) ∧
    (∃ R : Subgroup G, R ≤ D.C ⊓ centralizer ({u} : Set G) ∧
      (∀ a ∈ D.Eu u, ∀ r ∈ R, a * r = r * a) ∧ IsCyclic ↥R ∧ IsPGroup 2 ↥R ∧
      Nat.card ↥R = 2 ^ (D.n - 1) ∧ D.z ∈ R) ∧
    D.Eu u ⊓ D.F = ⊥ ∧
    Nat.card ↥(D.K ⊓ centralizer ({u} : Set G)) = D.e * D.e * 2 ^ (2 * D.n - 2) := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl, hsq₁, hsq₂⟩ := k3_decomp D hs hu hu2 huz
  obtain ⟨w₀, hw₀, htu₁, htu₂⟩ := k3_swap D hs hu₁ hu₂ hut
  have hd : D.d = D.e * 2 ^ (D.n - 1) := d_eq D.ext3 hs
  have he : Odd D.e := e_odd D.ext3 hs
  obtain ⟨hcyc₁, hcard₁⟩ := (k3_model₁ D hs).2.2 u₁ hu₁ hsq₁
  obtain ⟨hcyc₂, hcard₂⟩ := (k3_model₂ D hs).2.2 u₂ hu₂ hsq₂
  obtain ⟨E₁, R₁, hE₁T, hR₁T, hE₁c, hR₁c, hE₁card, hR₁card, hE₁mem, hR₁mem⟩ :=
    k3_cyclic_split hcyc₁ he (hcard₁.trans hd)
  obtain ⟨E₂, R₂, hE₂T, hR₂T, hE₂c, hR₂c, hE₂card, hR₂card, hE₂mem, hR₂mem⟩ :=
    k3_cyclic_split hcyc₂ he (hcard₂.trans hd)
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
    hs.comps.comm a ((hE₁mem a).mp ha).1.1 b ((hE₂mem b).mp hb).1.1
  have hinf : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₁, hx₂⟩
    have hxz : x ∈ zpowers D.z := by
      rw [← k3_T_inf D hs hu₁ hu₂]
      exact ⟨((hE₁mem x).mp hx₁).1, ((hE₂mem x).mp hx₂).1⟩
    rcases k3_zpowers_cases D hs hxz with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exfalso
      have hodd := ((hE₁mem x).mp hx₁).2
      rw [h, hs.syl.z_inv] at hodd
      exact absurd hodd (by decide)
  have hcardE : Nat.card ↥(E₁ ⊔ E₂) = D.e * D.e := by
    rw [IVK.Proofs2.card_sup_eq_mul hcomm hinf, hE₁card, hE₂card]
  have hEu : E₁ ⊔ E₂ = D.Eu (u₁ * u₂) :=
    le_antisymm (k3_E_le D hs hu₁ hu₂ hE₁mem hE₂mem (by rw [hcardE]; exact he.mul he))
      (k3_Eu_le D hs hu₁ hu₂ hE₁mem hE₂mem he (hcard₁.trans hd) (hcard₂.trans hd))
  refine ⟨⟨E₁, E₂, hEu, hinf, hcomm, hE₁c, hE₂c, hE₁card, hE₂card, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨haT, hodd⟩ := (hE₁mem a).mp ha
    have hT := k3_conj_cent (H := D.K₁) (H' := D.K₂) (a := D.t) (u := u₁) (u' := u₂)
      (w := w₀) (t_conj_K₁' D hs)
      (fun h hh => (z_central_in_K D hs hw₀ h (Subgroup.mem_sup_right hh)).symm) htu₁ a haT
    exact (hE₂mem _).mpr ⟨hT, by rw [k3_orderOf_conj]; exact hodd⟩
  · intro a ha
    obtain ⟨haT, hodd⟩ := (hE₂mem a).mp ha
    have hT := k3_conj_cent (H := D.K₂) (H' := D.K₁) (a := D.t) (u := u₂) (u' := u₁)
      (w := w₀) (t_conj_K₂' D hs)
      (fun h hh => (z_central_in_K D hs hw₀ h (Subgroup.mem_sup_left hh)).symm) htu₂ a haT
    exact (hE₁mem _).mpr ⟨hT, by rw [k3_orderOf_conj]; exact hodd⟩
  · refine ⟨R₁, ?_, ?_, hR₁c, ?_, hR₁card, ?_⟩
    · intro r hr
      have hrT := hR₁T hr
      exact ⟨K₁_le_C' D hs hrT.1, mem_centralizer_singleton_iff.mpr (k3_T₁_comm D hs hu₂ hrT)⟩
    · intro a ha r hr
      have ha' : a ∈ E₁ ⊔ E₂ := hEu ▸ ha
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hcomm ha'
      have hrT : r ∈ D.K₁ ⊓ centralizer ({u₁} : Set G) := hR₁T hr
      have h1 : a₁ * r = r * a₁ := k3_cyclic_comm hcyc₁ (hE₁T ha₁) hrT
      have h2 : a₂ * r = r * a₂ := (hs.comps.comm r hrT.1 a₂ (hE₂T ha₂).1).symm
      calc a₁ * a₂ * r = a₁ * (a₂ * r) := by group
        _ = a₁ * (r * a₂) := by rw [h2]
        _ = (a₁ * r) * a₂ := by group
        _ = (r * a₁) * a₂ := by rw [h1]
        _ = r * (a₁ * a₂) := by group
    · intro r
      obtain ⟨j, hj⟩ := ((hR₁mem r).mp r.2).2
      exact ⟨j, Subtype.ext hj⟩
    · rw [hR₁mem]
      refine ⟨⟨z_mem_K₁' D hs, mem_centralizer_singleton_iff.mpr (hs.comps.cz₁ hu₁).symm⟩, 1, ?_⟩
      rw [pow_one, pow_two]
      exact z_mul_z' D hs
  · rw [eq_bot_iff]
    rintro x ⟨hxE, hxF⟩
    have hxE' : x ∈ pPrimeCoreOf 2 (D.K ⊓ centralizer ({u₁ * u₂} : Set G)) := hxE
    have hxK : x ∈ D.K := (TwoThin.pPrimeCoreOf_le _ hxE').1
    have h : x ∈ D.F ⊓ D.K := ⟨hxF, hxK⟩
    rw [F_inf_K_eq hs] at h
    exact h
  · rw [k3_card_X D hs hu₁ hu₂ hsq₁ hsq₂ hcard₁ hcard₂, hd]
    have h2 : 2 * D.n - 2 = (D.n - 1) + (D.n - 1) := by omega
    rw [h2, pow_add]
    ring

end Elem

end CFSG.GH74.GLS.SP.Local
