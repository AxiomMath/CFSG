module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148InnerLow
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148Inner

open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)
open CFSG.LocalAnalysis.GLTheoremA.S10 (twoPart)

theorem sl2_inner_of_pow_two {L : Type} [Field L] [Finite L] {n : ℕ} (hn : 1 ≤ n)
    (hL : Nat.card L = 2 ^ n) (hodd : n % 2 = 1) {α : MulAut (SL₂ L)} {k : ℕ} (hα : α ^ (2 ^ k) = 1) :
    ∃ M : SL₂ L, MulAut.conj M = α := by
  haveI : CharP L 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hL
  have hcard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (SL₂ L)) = n :=
    CFSG.RankThree.PartOne.KCRootAxis.natCard_out_sl2 hn hL
  have hpow : (QuotientGroup.mk α : CFSG.ComponentClassification.OuterAutomorphisms.Outer (SL₂ L)) ^ (2 ^ k) =
      1 := by
    rw [← QuotientGroup.mk_pow, hα]
    rfl
  have hcop : Nat.Coprime (2 ^ k) n :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
  have hd1 := orderOf_dvd_of_pow_eq_one hpow
  have hd2 := orderOf_dvd_natCard
    (QuotientGroup.mk α : CFSG.ComponentClassification.OuterAutomorphisms.Outer (SL₂ L))
  rw [hcard] at hd2
  have hd : orderOf (QuotientGroup.mk α : CFSG.ComponentClassification.OuterAutomorphisms.Outer (SL₂ L)) ∣ 1 := by
    have := Nat.dvd_gcd hd1 hd2
    rwa [hcop.gcd_eq_one] at this
  have h1 : (QuotientGroup.mk α : CFSG.ComponentClassification.OuterAutomorphisms.Outer (SL₂ L)) = 1 :=
    orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  have hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (SL₂ L) :=
    (QuotientGroup.eq_one_iff α).1 h1
  obtain ⟨M, hM⟩ := MonoidHom.mem_range.1 hin
  exact ⟨M, hM⟩

theorem conj_mem_of_normalizer {G : Type} [Group G] {S : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (S : Set G)) {s : G} (hs : s ∈ S) : x * s * x⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.1 hx s).1 hs

theorem inv_conj_mem_of_normalizer {G : Type} [Group G] {S : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (S : Set G)) {s : G} (hs : s ∈ S) : x⁻¹ * s * x ∈ S := by
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hx) s).1 hs
  rwa [inv_inv] at this

@[expose] def conjSL2 {G : Type} [Group G] {L : Type} [Field L] {S : Subgroup G} (e : SL₂ L ≃* S)
    (x : ↥(Subgroup.normalizer (S : Set G))) : MulAut (SL₂ L) where
  toFun g := e.symm ⟨(x : G) * (e g : G) * (x : G)⁻¹, conj_mem_of_normalizer x.2 (e g).2⟩
  invFun g := e.symm ⟨(x : G)⁻¹ * (e g : G) * (x : G), inv_conj_mem_of_normalizer x.2 (e g).2⟩
  left_inv g := by
    apply e.injective
    apply Subtype.ext
    simp only [MulEquiv.apply_symm_apply, Subgroup.coe_mk]
    group
  right_inv g := by
    apply e.injective
    apply Subtype.ext
    simp only [MulEquiv.apply_symm_apply, Subgroup.coe_mk]
    group
  map_mul' g h := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    group

theorem conjSL2_mul {G : Type} [Group G] {L : Type} [Field L] {S : Subgroup G} (e : SL₂ L ≃* S)
    (x y : ↥(Subgroup.normalizer (S : Set G))) : conjSL2 e (x * y) = conjSL2 e x * conjSL2 e y := by
  apply MulEquiv.ext
  intro g
  show e.symm ⟨((x * y : ↥(Subgroup.normalizer (S : Set G))) : G) * (e g : G) *
      ((x * y : ↥(Subgroup.normalizer (S : Set G))) : G)⁻¹, _⟩ =
    e.symm ⟨(x : G) * (e (e.symm ⟨(y : G) * (e g : G) * (y : G)⁻¹, _⟩) : G) * (x : G)⁻¹, _⟩
  congr 1
  apply Subtype.ext
  simp only [MulEquiv.apply_symm_apply, Subgroup.coe_mul, mul_inv_rev]
  group

@[expose] def conjSL2Hom {G : Type} [Group G] {L : Type} [Field L] {S : Subgroup G} (e : SL₂ L ≃* S) :
    ↥(Subgroup.normalizer (S : Set G)) →* MulAut (SL₂ L) :=
  MonoidHom.mk' (conjSL2 e) (conjSL2_mul e)

theorem two_elem_mem {G : Type} [Group G] {L : Type} [Field L] [Finite L] {n : ℕ} (hn : 1 ≤ n)
    (hL : Nat.card L = 2 ^ n) (hodd : n % 2 = 1) {S C : Subgroup G} (e : SL₂ L ≃* S) (hSC : S ≤ C)
    (hNC : ∀ x ∈ C, x ∈ Subgroup.normalizer (S : Set G)) {N : ℕ} (hN : Nat.Coprime 2 N)
    (hcent : ∀ t ∈ C, (∀ s ∈ S, s * t = t * s) → t ^ N = 1)
    {x : G} (hx : x ∈ C) {k : ℕ} (hxk : x ^ (2 ^ k) = 1) : x ∈ S := by
  classical
  let c : ↥(Subgroup.normalizer (S : Set G)) := ⟨x, hNC x hx⟩
  have hc : c ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact hxk
  have hα : conjSL2Hom e c ^ (2 ^ k) = 1 := by
    rw [← map_pow, hc, map_one]
  obtain ⟨M, hM⟩ := sl2_inner_of_pow_two hn hL hodd hα
  have hconj : ∀ g : SL₂ L, x * (e g : G) * x⁻¹ = (e M : G) * (e g : G) * (e M : G)⁻¹ := by
    intro g
    have h1 : M * g * M⁻¹ = e.symm ⟨x * (e g : G) * x⁻¹, conj_mem_of_normalizer (hNC x hx) (e g).2⟩ := by
      have h := congrArg (fun φ : MulAut (SL₂ L) => φ g) hM
      exact h
    have h2 : e (M * g * M⁻¹) = ⟨x * (e g : G) * x⁻¹, conj_mem_of_normalizer (hNC x hx) (e g).2⟩ := by
      rw [h1, MulEquiv.apply_symm_apply]
    have h3 : (e (M * g * M⁻¹) : G) = x * (e g : G) * x⁻¹ := by rw [h2]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h3
    exact h3.symm
  have ht_C : (e M : G)⁻¹ * x ∈ C := C.mul_mem (C.inv_mem (hSC (e M).2)) hx
  have ht_cent : ∀ u ∈ S, u * ((e M : G)⁻¹ * x) = ((e M : G)⁻¹ * x) * u := by
    intro u hu
    have hu' : u = (e (e.symm ⟨u, hu⟩) : G) := by simp
    have h := hconj (e.symm ⟨u, hu⟩)
    rw [← hu'] at h
    calc u * ((e M : G)⁻¹ * x) = (e M : G)⁻¹ * ((e M : G) * u * (e M : G)⁻¹) * x := by group
      _ = (e M : G)⁻¹ * (x * u * x⁻¹) * x := by rw [h]
      _ = (e M : G)⁻¹ * x * u := by group
  have ht_pow : ((e M : G)⁻¹ * x) ^ N = 1 := hcent _ ht_C ht_cent
  have hcomm : Commute (e M : G) ((e M : G)⁻¹ * x) := ht_cent _ (e M).2
  have hxN : x ^ N ∈ S := by
    have hx_eq : x = (e M : G) * ((e M : G)⁻¹ * x) := by group
    rw [hx_eq, hcomm.mul_pow, ht_pow, mul_one]
    exact S.pow_mem (e M).2 N
  have hcop : Nat.Coprime (2 ^ k) N := Nat.Coprime.pow_left k hN
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ k) N
  rw [hcop.gcd_eq_one] at hbez
  have hxeq : x = (x ^ N) ^ (Nat.gcdB (2 ^ k) N) := by
    calc x = x ^ (((1 : ℕ) : ℤ)) := by simp
      _ = x ^ (((2 ^ k : ℕ) : ℤ) * Nat.gcdA (2 ^ k) N + (N : ℤ) * Nat.gcdB (2 ^ k) N) := by rw [hbez]
      _ = (x ^ (2 ^ k)) ^ Nat.gcdA (2 ^ k) N * (x ^ N) ^ Nat.gcdB (2 ^ k) N := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = (x ^ N) ^ Nat.gcdB (2 ^ k) N := by rw [hxk, one_zpow, one_mul]
  have hmem : (x ^ N) ^ Nat.gcdB (2 ^ k) N ∈ S := S.zpow_mem hxN _
  rwa [← hxeq] at hmem

theorem twoPart_centralizer_3B_odd {f : ℕ} (hf : 1 ≤ f) (hodd : f % 2 = 1) (K : Type) [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (ht : t ∈ Subgroup.centralizer ((CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    twoPart (Nat.card (Subgroup.centralizer
      ({t} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) ≤ (2 ^ f) ^ 3 := by
  classical
  have h3 : ¬ 3 ∣ 2 ^ f := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at this
  obtain ⟨hcomm, hpow⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeBCent_holds K (2 ^ f) σ hK hσ h3 t ht ht3 ht1
  set S := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom with hSdef
  set C := Subgroup.centralizer ({t} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) with hCdef
  have hSC : S ≤ C := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff] at ht
    exact Subgroup.mem_centralizer_singleton_iff.2 (ht s hs)
  have hfwd : ∀ x ∈ C, ∀ h ∈ S, x * h * x⁻¹ ∈ S := by
    intro x hx h hh
    have h1 := hcomm x hx h (hSC hh)
    have e : x * h * x⁻¹ = (x * h * x⁻¹ * h⁻¹) * h := by group
    rw [e]
    exact S.mul_mem h1 hh
  have hNC : ∀ x ∈ C, x ∈ Subgroup.normalizer (S : Set _) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hfwd x hx h hh, fun hh => ?_⟩
    have := hfwd x⁻¹ (C.inv_mem hx) _ hh
    have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rwa [e] at this
  have hσ3 : σ ^ 3 = 1 := sigma_pow_three_eq_one hK hσ
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
  have hLcard := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.natCard_orbitField_d4Outer hσ3
  rw [hK] at hLcard
  have hN : Nat.Coprime 2 ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    have h2 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
    have hpos : 0 < (2 ^ f) ^ 2 := by positivity
    generalize (2 ^ f) ^ 2 = X at h2 hpos ⊢
    omega
  have hcent : ∀ t' ∈ C, (∀ s ∈ S, s * t' = t' * s) → t' ^ ((2 ^ f) ^ 2 - 1) = 1 := fun t' ht' hc' =>
    hpow t' ht' (Subgroup.mem_centralizer_iff.2 hc')
  have hkey : ∀ x ∈ C, ∀ k : ℕ, x ^ (2 ^ k) = 1 → x ∈ S := fun x hx k hxk =>
    two_elem_mem (n := f * 3) (by omega) (by rw [hLcard, pow_mul]) (by omega) e hSC hNC hN hcent hx hxk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T0⟩ := (inferInstance : Nonempty (Sylow 2 C))
  set P : Subgroup C := (T0 : Subgroup C) with hPdef
  have hPle : P.map C.subtype ≤ S := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨k, hk⟩ := T0.isPGroup' ⟨g, hg⟩
    have hk' : (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ^ (2 ^ k) = 1 := by
      have h2 : g ^ (2 ^ k) = (1 : C) := congrArg Subtype.val hk
      exact congrArg Subtype.val h2
    exact hkey g.1 g.2 k hk'
  have hTcard : Nat.card (P.map C.subtype : Subgroup _) = 2 ^ (Nat.card C).factorization 2 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact T0.card_eq_multiplicity
  have hdvd : Nat.card (P.map C.subtype : Subgroup _) ∣ Nat.card S := Subgroup.card_dvd_of_le hPle
  have hSc : Nat.card S = (2 ^ f) ^ 3 * (((2 ^ f) ^ 3) ^ 2 - 1) := by
    rw [hSdef, CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.card_d4ShortSL2 hσ3, hK]
  rw [hTcard, hSc] at hdvd
  have hM' : Nat.Coprime 2 (((2 ^ f) ^ 3) ^ 2 - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    have h2f : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 2 ∣ ((2 ^ f) ^ 3) ^ 2 := dvd_pow (dvd_pow h2f (by norm_num)) (by norm_num)
    have hpos : 0 < ((2 ^ f) ^ 3) ^ 2 := by positivity
    generalize ((2 ^ f) ^ 3) ^ 2 = X at h2 hpos ⊢
    omega
  have hdiv : 2 ^ (Nat.card C).factorization 2 ∣ (2 ^ f) ^ 3 :=
    (Nat.Coprime.pow_left _ hM').dvd_of_dvd_mul_right hdvd
  show 2 ^ (Nat.card C).factorization 2 ≤ (2 ^ f) ^ 3
  exact Nat.le_of_dvd (by positivity) hdiv

end CFSG.LocalAnalysis.GLTheoremA.K148Inner

end
