module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResC
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTCnt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResA

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
  CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem eq_one_of_mk_eq_one {u : ↥H} (hu : u * u = 1)
    (h1 : QuotientGroup.mk' (pPrimeCore 2 ↥H) u = 1) : u = 1 := by
  have hc : u ∈ pPrimeCore 2 ↥H := (QuotientGroup.eq_one_iff u).mp h1
  have hodd : Odd (orderOf u) :=
    Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (Subgroup.orderOf_dvd_natCard _ hc)
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hu)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hodd
    exact absurd hodd (by decide)

omit [Finite G] in
theorem barIn_U_le_centralizer (hd : Data5A2 z k S T Tstar p H P t q I Q₁) :
    barIn H (L52Two.U4 z t) ≤ centralizer (barIn H I : Set (HBar H)) := by
  rintro _ ⟨u, hu, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨i, hi, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hd.i.good.comm i hi u hu).symm

omit [Finite G] in
theorem barIn_I_perfect (hd : Data5A2 z k S T Tstar p H P t q I Q₁) :
    ⁅barIn H I, barIn H I⁆ = barIn H I := by
  simpa [Subgroup.map_id] using
    commutator_map_barIn hd.i.good.le_H hd.i.perf (MonoidHom.id (HBar H))

theorem barIn_I_ne_bot (hd : Data5A2 z k S T Tstar p H P t q I Q₁) : barIn H I ≠ ⊥ := by
  intro hbot
  have h4 := (isFourSubgroup_barIn_Q₁ hd).2
  have hle : barIn H Q₁ ≤ ⊥ := hbot ▸ L52Two.barIn_mono hd.Q₁_le
  rw [le_bot_iff.mp hle, card_bot] at h4
  omega

theorem eq_one_of_mem_centralizers (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H))) {w : HBar H}
    (hwJ : w ∈ centralizer (J : Set (HBar H))) (hwI : w ∈ centralizer (barIn H I : Set (HBar H)))
    (hww : w * w = 1) : w = 1 := by
  have hQJ : barIn H Q₁ ≤ centralizer (J : Set (HBar H)) :=
    (L52Two.barIn_mono hd.Q₁_le).trans hIJ
  set A := zpowers w with hA
  have hAsq : ∀ y ∈ A, y * y = 1 := by
    rintro _ ⟨n, rfl⟩
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hww, one_zpow]
  have hwQ : w ∈ centralizer (barIn H Q₁ : Set (HBar H)) :=
    Subgroup.centralizer_le (L52Two.barIn_mono hd.Q₁_le) hwI
  have hinf : A ⊓ barIn H Q₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvA, hvQ⟩
    rw [Subgroup.mem_bot]
    refine eq_one_of_mem_barIn_comm hd (L52Two.barIn_mono hd.Q₁_le hvQ) (fun i hi => ?_)
      (hAsq v hvA)
    exact ((Subgroup.mem_centralizer_iff.mp ((zpowers_le.mpr hwI) hvA)) i hi).symm
  have hbot := eq_bot_of_elem_le_centralizer hL31 h hd hJ hQJ (zpowers_le.mpr hwJ)
    (zpowers_le.mpr hwQ) hAsq hinf
  have : w ∈ zpowers w := Subgroup.mem_zpowers w
  rwa [hbot, Subgroup.mem_bot] at this

theorem mem_of_actJ_mem_inner (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H))) {x : HBar H}
    (hxN : x ∈ normalizer (J : Set (HBar H)))
    (hxI : x ∈ centralizer (barIn H I : Set (HBar H))) (hx2 : x * x = 1)
    (hin : actJ J ⟨x, hxN⟩ ∈ inner (↥J ⧸ center ↥J)) : x ∈ J := by
  obtain ⟨y, hy⟩ := hin
  obtain ⟨j₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hj₀N : (j₀ : HBar H) ∈ normalizer (J : Set (HBar H)) := Subgroup.le_normalizer j₀.2
  have h1 : actJ J ⟨(j₀ : HBar H), hj₀N⟩ = MulAut.conj (QuotientGroup.mk j₀) :=
    actJ_of_mem J j₀.2
  have hact : actJ J (⟨x, hxN⟩ * (⟨(j₀ : HBar H), hj₀N⟩)⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, ← hy]
    exact mul_inv_cancel _
  set c : HBar H := x * (j₀ : HBar H)⁻¹ with hc
  have hcJ : c ∈ centralizer (J : Set (HBar H)) := mem_centralizer_of_actJ_eq_one J hJ.1.1 hact
  have hJI : (j₀ : HBar H) ∈ centralizer (barIn H I : Set (HBar H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact ((Subgroup.mem_centralizer_iff.mp (hIJ hi)) _ j₀.2).symm
  have hcI : c ∈ centralizer (barIn H I : Set (HBar H)) :=
    Subgroup.mul_mem _ hxI (Subgroup.inv_mem _ hJI)
  have hodd : Odd (orderOf c) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨m, hm⟩ := hev
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0] at hm
      exact (orderOf_pos c).ne' (by omega)
    have hw2 : orderOf (c ^ m) = 2 := by
      rw [orderOf_pow' c hm0, hm, show m + m = m * 2 by ring, Nat.gcd_mul_right_left]
      exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm0)
    have hww : c ^ m * c ^ m = 1 := by
      have h0 := pow_orderOf_eq_one (c ^ m)
      rwa [hw2, sq] at h0
    have h1 := eq_one_of_mem_centralizers hL31 h hd hJ hIJ (Subgroup.pow_mem _ hcJ m)
      (Subgroup.pow_mem _ hcI m) hww
    rw [h1, orderOf_one] at hw2
    exact absurd hw2 (by norm_num)
  have hcomm : Commute c (j₀ : HBar H) :=
    ((Subgroup.mem_centralizer_iff.mp hcJ) _ j₀.2).symm
  have hxe : x = c * (j₀ : HBar H) := by rw [hc]; group
  obtain ⟨r, hr⟩ := hodd
  have hxm : x ^ orderOf c = x := by
    rw [hr, pow_succ, pow_mul, sq, hx2, one_pow, one_mul]
  have hjm : x ^ orderOf c = (j₀ : HBar H) ^ orderOf c := by
    rw [hxe, hcomm.mul_pow, pow_orderOf_eq_one, one_mul]
  rw [← hxm, hjm]
  exact Subgroup.pow_mem _ j₀.2 _

theorem exists_partner_I (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H))) :
    ∃ J' : Subgroup (HBar H), IsComponent J' ∧ J' ≠ J ∧
      (∀ K : Subgroup (HBar H), IsComponent K → K = J ∨ K = J') ∧ barIn H I ≤ J' :=
  exists_partner (no_three_comps hL31 h (z_mem_H h hd.u)) hJ (barIn_I_perfect hd)
    (barIn_I_ne_bot hd) hd.i.good.layer hIJ

theorem mem_normalizer_of_mem_normalizer_I (hL31 : Lemma31Narrow)
    (h : Cfg55E G z k S T Tstar p H P g X Y) (hd : Data5A2 z k S T Tstar p H P t q I Q₁)
    {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H))) {x : HBar H}
    (hx : x ∈ normalizer (barIn H I : Set (HBar H))) : x ∈ normalizer (J : Set (HBar H)) := by
  obtain ⟨J', hJ', hne, huniq, hIJ'⟩ := exists_partner_I hL31 h hd hJ hIJ
  exact (mem_normalizer_of_partner hJ hJ' hne huniq (barIn_I_perfect hd) (barIn_I_ne_bot hd) hIJ'
    hx).1

theorem barIn_U_le_normalizer (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H))) :
    barIn H (L52Two.U4 z t) ≤ normalizer (J : Set (HBar H)) := fun _ hx =>
  mem_normalizer_of_mem_normalizer_I hL31 h hd hJ hIJ
    (Subgroup.centralizer_le_normalizer _ (barIn_U_le_centralizer hd hx))

theorem exists_actU (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H))) :
    ∃ φ : ↥(L52Two.U4 z t) →* MulAut (↥J ⧸ center ↥J), Function.Injective φ ∧
      ∀ u : ↥(L52Two.U4 z t), ∃ hN : QuotientGroup.mk' (pPrimeCore 2 ↥H)
        ⟨(u : G), U_le_H h hd.u u.2⟩ ∈ normalizer (J : Set (HBar H)),
        φ u = actJ J ⟨_, hN⟩ := by
  set ν : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hν
  have hUH := U_le_H h hd.u
  have hN : ∀ u : ↥(L52Two.U4 z t), ν ⟨(u : G), hUH u.2⟩ ∈ normalizer (J : Set (HBar H)) :=
    fun u => barIn_U_le_normalizer hL31 h hd hJ hIJ ⟨⟨u, hUH u.2⟩, u.2, rfl⟩
  set ψ : ↥(L52Two.U4 z t) →* ↥(normalizer (J : Set (HBar H))) :=
    (ν.comp (Subgroup.inclusion hUH)).codRestrict _ hN with hψ
  refine ⟨(actJ J).comp ψ, ?_, fun u => ⟨hN u, rfl⟩⟩
  rw [injective_iff_map_eq_one]
  intro u hu
  have := hd.u.four.1
  have hu2 : (⟨(u : G), hUH u.2⟩ : ↥H) * ⟨(u : G), hUH u.2⟩ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← sq]
    exact elemPow_eq_one_of_isElementaryAbelian (u : G) u.2
  have hC : ν ⟨(u : G), hUH u.2⟩ ∈ centralizer (J : Set (HBar H)) :=
    mem_centralizer_of_actJ_eq_one J hJ.1.1 (n := ψ u) hu
  have hνu : ν ⟨(u : G), hUH u.2⟩ = 1 := by
    refine eq_one_of_mem_centralizers hL31 h hd hJ hIJ hC
      (barIn_U_le_centralizer hd ⟨⟨u, hUH u.2⟩, u.2, rfl⟩) ?_
    rw [← map_mul, hu2, map_one]
  have h1 := eq_one_of_mk_eq_one hu2 hνu
  have h2 : (u : G) = 1 := congrArg Subtype.val h1
  exact Subtype.ext h2

theorem quot_type (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H))) :
    Nonempty ((↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 7)) ∨
      IVK.IsL2 (↥J ⧸ center ↥J) Odd := by
  have he := pPrimeCore_eq_center hJ.1 (odd_card_center hL31 h hd hJ hIJ)
  have hQJ : barIn H Q₁ ≤ centralizer (J : Set (HBar H)) :=
    (L52Two.barIn_mono hd.Q₁_le).trans hIJ
  have e : (↥J ⧸ pPrimeCore 2 ↥J) ≃* (↥J ⧸ center ↥J) := QuotientGroup.quotientMulEquivOfEq he
  rcases hat_type hL31 h hd hJ hQJ with he7 | hL2
  · obtain ⟨e7⟩ := he7
    exact Or.inl ⟨e.symm.trans e7⟩
  · exact Or.inr (Odd87.Transport.isL2_of_mulEquiv e hL2)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
