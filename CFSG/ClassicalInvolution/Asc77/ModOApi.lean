module

public import CFSG.ClassicalInvolution.Asc77.AscSixInv
public import CFSG.ClassicalInvolution.Asc77.AscSixBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem oddCoreOf_le_self (K : Subgroup G) : oddCoreOf K ≤ K := Subgroup.map_subtype_le _

theorem mem_oddCoreOf_iff {K : Subgroup G} {x : G} :
    x ∈ oddCoreOf K ↔ ∃ h : x ∈ K, (⟨x, h⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem oddCoreOf_odd_natCard [Finite G] (K : Subgroup G) : Odd (Nat.card ↥(oddCoreOf K)) := by
  have h : Odd (Nat.card ↥(classicalInvolutionOddCore ↥K)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥K
  have e : Nat.card ↥(oddCoreOf K) = Nat.card ↥(classicalInvolutionOddCore ↥K) :=
    (Nat.card_congr ((classicalInvolutionOddCore ↥K).equivMapOfInjective K.subtype
      K.subtype_injective).toEquiv).symm
  rw [e]
  exact h

theorem eq_one_of_isPGroup_of_mem_odd [Finite G] {A : Subgroup G} (hA : Odd (Nat.card ↥A))
    {x : G} (hx : x ∈ A) (hx2 : IsPGroup 2 (Subgroup.zpowers x)) : x = 1 := by
  obtain ⟨n, hn⟩ := hx2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have hdvd : orderOf x ∣ Nat.card ↥A := Subgroup.orderOf_dvd_natCard A hx
  rw [hn] at hdvd
  have hodd : Odd (2 ^ n) := hA.of_dvd_nat hdvd
  have hn0 : n = 0 := by
    by_contra h
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, h⟩)
  rw [hn0, pow_zero] at hn
  exact orderOf_eq_one_iff.mp hn

theorem isPGroup_zpowers_mul [Finite G] {a b : G} (hab : Commute a b)
    (ha : IsPGroup 2 (Subgroup.zpowers a)) (hb : IsPGroup 2 (Subgroup.zpowers b)) :
    IsPGroup 2 (Subgroup.zpowers (a * b)) := by
  obtain ⟨m, hm⟩ := ha.exists_card_eq
  obtain ⟨n, hn⟩ := hb.exists_card_eq
  rw [Nat.card_zpowers] at hm hn
  have ha' : a ^ 2 ^ (m + n) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hm ▸ pow_dvd_pow 2 (Nat.le_add_right m n))
  have hb' : b ^ 2 ^ (m + n) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hn ▸ pow_dvd_pow 2 (Nat.le_add_left n m))
  have h1 : (a * b) ^ 2 ^ (m + n) = 1 := by rw [hab.mul_pow, ha', hb', one_mul]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])

theorem isPGroup_zpowers_of_mul_self_eq_one {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    IsPGroup 2 (Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hx) hx1, pow_one])

theorem _root_.CFSG.ClassicalInvolution.Generic.IsUniqueInvolution.commute_of_mem
    {K : Subgroup G} {z : G} (h : IsUniqueInvolution K z) {w : G} (hw : w ∈ K) :
    z * w = w * z := by
  have h1 : w * z * w⁻¹ = z := h.conj_eq (conjSub_eq_self_of_mem hw)
  calc z * w = (w * z * w⁻¹) * w := by rw [h1]
    _ = w * z := by group

theorem HypOmegaMod.exists_uniqueInvolution [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) : ∃ z : G, IsUniqueInvolution K z := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact ⟨z, ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz⟩

theorem HypOmegaMod.nonempty_equiv_sl2 (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Nonempty (↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, GaloisField p f)) := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact hz.nonempty_equiv

theorem HypOmegaMod.isPerfect (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Group.IsPerfect ↥K := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact hz.perfect

theorem HypOmegaMod.exists_chart (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ φ : ↥K →* SL(2, GaloisField p f), Function.Surjective φ ∧
      ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K := by
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hK
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun x => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one e, e.injective.eq_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem HypOmegaMod.center_two [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    ∀ w ∈ K, IsPGroup 2 (Subgroup.zpowers w) → (∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) →
      w = 1 ∨ w = z := by
  intro w hwK hw2 hcomm
  obtain ⟨φ, hφs, hφk⟩ := hΩ.exists_chart hK
  have hodd := odd_natCard_galoisField hp hq
  have hoddO := oddCoreOf_odd_natCard K
  have hz2 := isPGroup_zpowers_of_mul_self_eq_one hz.sq hz.ne_one
  have hzN : (⟨z, hz.mem⟩ : ↥K) ∉ classicalInvolutionOddCore ↥K := fun hN =>
    hz.ne_one (eq_one_of_isPGroup_of_mem_odd hoddO (mem_oddCoreOf_iff.mpr ⟨hz.mem, hN⟩) hz2)
  have hφz : φ ⟨z, hz.mem⟩ = -1 := by
    have h1 : φ ⟨z, hz.mem⟩ ≠ 1 := fun h => hzN ((hφk _).mp h)
    have h2 : φ ⟨z, hz.mem⟩ * φ ⟨z, hz.mem⟩ = 1 := by
      rw [← map_mul]
      have : (⟨z, hz.mem⟩ : ↥K) * ⟨z, hz.mem⟩ = 1 := Subtype.ext hz.sq
      rw [this, map_one]
    exact (sl2_orderOf_eq_two_iff hodd _).mp (orderOf_eq_prime (by rw [pow_two]; exact h2) h1)
  have hcen : φ ⟨w, hwK⟩ ∈ Subgroup.center SL(2, GaloisField p f) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨y, rfl⟩ := hφs s
    have h1 : ⁅(⟨w, hwK⟩ : ↥K), y⁆ ∈ classicalInvolutionOddCore ↥K :=
      (mem_oddCoreOf_iff.mp (hcomm (y : G) y.2)).2
    have h2 : φ ⁅(⟨w, hwK⟩ : ↥K), y⁆ = 1 := (hφk _).mpr h1
    rw [map_commutatorElement] at h2
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  rcases (mem_center_sl2_iff _).mp hcen with h | h
  · left
    exact eq_one_of_isPGroup_of_mem_odd hoddO (mem_oddCoreOf_iff.mpr ⟨hwK, (hφk _).mp h⟩) hw2
  · right
    have hwz : (⟨w * z, K.mul_mem hwK hz.mem⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
      rw [← hφk, show (⟨w * z, K.mul_mem hwK hz.mem⟩ : ↥K) = ⟨w, hwK⟩ * ⟨z, hz.mem⟩ from rfl,
        map_mul, h, hφz]
      simp
    have hcz : Commute w z := (hz.commute_of_mem hwK).symm
    have hmem : w * z ∈ oddCoreOf K := mem_oddCoreOf_iff.mpr ⟨K.mul_mem hwK hz.mem, hwz⟩
    have h1 := eq_one_of_isPGroup_of_mem_odd hoddO hmem (isPGroup_zpowers_mul hcz hw2 hz2)
    calc w = w * z * z := by rw [mul_assoc, hz.sq, mul_one]
      _ = z := by rw [h1, one_mul]

theorem isSylow2In_map_sylow (K : Subgroup G) (Q : Sylow 2 ↥K) :
    IsSylow2In ((Q : Subgroup ↥K).map K.subtype) K := by
  refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, fun V' hV'P hV'2 hle => ?_⟩
  have hQV : (Q : Subgroup ↥K) ≤ V'.subgroupOf K := by
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  have hcomap : V'.subgroupOf K = (Q : Subgroup ↥K) := Q.is_maximal' (hV'2.comap_subtype) hQV
  rw [← Subgroup.map_subgroupOf_eq_of_le hV'P, hcomap]

theorem HypOmegaMod.natCard_isSylow2In [Finite G] (hΩ : HypOmegaMod p f Ω) {K R : Subgroup G}
    (hK : K ∈ Ω) (hR : IsSylow2In R K) :
    Nat.card R = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2 := by
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hK
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hQ : Nat.card ↥(Q : Subgroup ↥K) = 2 ^ (Nat.card ↥K).factorization 2 :=
    Sylow.card_eq_multiplicity Q
  have hc : Nat.card ↥((Q : Subgroup ↥K).map K.subtype) = Nat.card ↥(Q : Subgroup ↥K) :=
    (Nat.card_congr ((Q : Subgroup ↥K).equivMapOfInjective K.subtype
      K.subtype_injective).toEquiv).symm
  have hRQ : Nat.card R = Nat.card ↥((Q : Subgroup ↥K).map K.subtype) :=
    hR.natCard_eq (isSylow2In_map_sylow K Q)
  have hmul : Nat.card ↥K = Nat.card (↥K ⧸ classicalInvolutionOddCore ↥K) *
      Nat.card ↥(classicalInvolutionOddCore ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hq1 : Nat.card (↥K ⧸ classicalInvolutionOddCore ↥K) = Nat.card SL(2, GaloisField p f) :=
    Nat.card_congr e.toEquiv
  have hN : Odd (Nat.card ↥(classicalInvolutionOddCore ↥K)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥K
  have h0 : Nat.card SL(2, GaloisField p f) ≠ 0 := Nat.card_pos.ne'
  have hN0 : Nat.card ↥(classicalInvolutionOddCore ↥K) ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card ↥K).factorization 2 =
      (Nat.card SL(2, GaloisField p f)).factorization 2 := by
    rw [hmul, hq1, Nat.factorization_mul h0 hN0]
    have : (Nat.card ↥(classicalInvolutionOddCore ↥K)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hN)
        (even_iff_two_dvd.mpr h2))
    simp [this]
  rw [hRQ, hc, hQ, hfac]

theorem HypOmegaMod.comm_le_oddCore_of_twin [Finite G] (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
  have hdvd : 2 ∣ Nat.card ↥(K ⊓ J) := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ J) (x := z) ⟨hzK.mem, hzJ.mem⟩
    rwa [hz2] at this
  have hN : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have h1 := one_le_padicValNat_of_dvd hN hdvd
  obtain ⟨h2, h3⟩ := hΩ.omega4 K hK J hJ hKJ
  exact h3 (le_antisymm h2 h1)

theorem HypOmegaMod.le_normalizer_of_twin [Finite G] (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : K ≤ Subgroup.normalizer (J : Set G) := by
  have hc := hΩ.comm_le_oddCore_of_twin hK hJ hKJ hzK hzJ
  have key : ∀ k ∈ K, ∀ j ∈ J, k * j * k⁻¹ ∈ J := by
    intro k hk j hj
    have h1 : ⁅k, j⁆ ∈ oddCoreOf J := (hc (Subgroup.commutator_mem_commutator hk hj)).2
    have h2 : ⁅k, j⁆ ∈ J := oddCoreOf_le_self J h1
    have e : k * j * k⁻¹ = ⁅k, j⁆ * j := by rw [commutatorElement_def]; group
    rw [e]
    exact J.mul_mem h2 hj
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key k hk h hh, fun hh => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hh
  have e : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem HypOmegaMod.commutes_of_twin_of_isPGroup [Finite G] (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) {A B : Subgroup G}
    (hA : A ≤ K) (hB : B ≤ J) (hAB : IsPGroup 2 ↥(A ⊔ B)) : Commutes A B := by
  intro a ha b hb
  have hc := hΩ.comm_le_oddCore_of_twin hK hJ hKJ hzK hzJ
  have h1 : ⁅a, b⁆ ∈ oddCoreOf K := (hc (Subgroup.commutator_mem_commutator (hA ha) (hB hb))).1
  have ha' : a ∈ A ⊔ B := Subgroup.mem_sup_left ha
  have hb' : b ∈ A ⊔ B := Subgroup.mem_sup_right hb
  have h2 : ⁅a, b⁆ ∈ A ⊔ B := by
    rw [commutatorElement_def]
    exact (A ⊔ B).mul_mem ((A ⊔ B).mul_mem ((A ⊔ B).mul_mem ha' hb') ((A ⊔ B).inv_mem ha'))
      ((A ⊔ B).inv_mem hb')
  have h3 : IsPGroup 2 (Subgroup.zpowers ⁅a, b⁆) := hAB.to_le (Subgroup.zpowers_le.mpr h2)
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1 h3)

theorem HypOmegaMod.le_of_forall_isSylow2In [Finite G] (hΩ : HypOmegaMod p f Ω) {J M : Subgroup G}
    (hJ : J ∈ Ω) (hM : ∀ V : Subgroup G, IsSylow2In V J → V ≤ M) : J ≤ M := by
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  set V₀ : Subgroup G := (Q₀ : Subgroup ↥J).map J.subtype with hV₀def
  have hV₀ : IsSylow2In V₀ J := isSylow2In_map_sylow J Q₀
  have hV₀sub : V₀.subgroupOf J = (Q₀ : Subgroup ↥J) :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  set N : Subgroup ↥J := Subgroup.normalClosure ((V₀.subgroupOf J : Subgroup ↥J) : Set ↥J) with hN
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have hle : N ≤ M.subgroupOf J := by
    refine (Subgroup.closure_le (M.subgroupOf J)).mpr fun a ha => ?_
    obtain ⟨b, hb, hab⟩ := Group.mem_conjugatesOfSet_iff.mp ha
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    have hae : (a : G) = (c : G) * (b : G) * (c : G)⁻¹ := by rw [← hc]; rfl
    have hmem : (a : G) ∈ conjSub (c : G) V₀ := by
      rw [hae]
      exact conj_mem_conjSub hb
    have hsyl : IsSylow2In (conjSub (c : G) V₀) J := by
      have := IsSylow2In.conj hV₀ (c : G)
      rwa [conjSub_eq_self_of_mem c.2] at this
    exact hM _ hsyl hmem
  have hperf : Group.IsPerfect ↥J := hΩ.isPerfect hJ
  have hodd : Odd (Nat.card (↥J ⧸ N)) := by
    have h1 : N.index ∣ (Q₀ : Subgroup ↥J).index := by
      refine Subgroup.index_dvd_of_le ?_
      rw [← hV₀sub]
      exact fun x hx => Subgroup.subset_normalClosure hx
    have h2 : Odd (Q₀ : Subgroup ↥J).index := by
      rcases Nat.even_or_odd (Q₀ : Subgroup ↥J).index with h | h
      · exact absurd (even_iff_two_dvd.mp h) (Sylow.not_dvd_index Q₀)
      · exact h
    rw [← Subgroup.index_eq_card]
    exact h2.of_dvd_nat h1
  have hsolv : Group.IsSolvable (↥J ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsPerfect ↥J := hperf
  have : Group.IsPerfect (↥J ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hsub : Subsingleton (↥J ⧸ N) := by
    by_contra hns
    have : Nontrivial (↥J ⧸ N) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable (↥J ⧸ N) hsolv
  have hidx : N.index = 1 := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  have htop : N = ⊤ := Subgroup.index_eq_one.mp hidx
  intro j hj
  have hjN : (⟨j, hj⟩ : ↥J) ∈ N := by rw [htop]; exact Subgroup.mem_top _
  exact hle hjN

theorem HypOmegaMod.isQuatSub_of_mem_RSet [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {R : Subgroup G} (hR : R ∈ RSet Ω) : IsQuatSub R := by
  obtain ⟨J, hJ, P, rfl⟩ := hR
  obtain ⟨φ, hφs, hφk⟩ := hΩ.exists_chart hJ
  have hF : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp
  have hP2 : IsPGroup 2 ((P : Subgroup ↥J).map J.subtype) := P.isPGroup'.map _
  have hinj : Function.Injective (φ.comp (P : Subgroup ↥J).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : φ (x : ↥J) = 1 := hx
    have hxN := (hφk _).mp hx1
    have hxG : ((x : ↥J) : G) ∈ ((P : Subgroup ↥J).map J.subtype) := ⟨x, x.2, rfl⟩
    have hx2 : IsPGroup 2 (Subgroup.zpowers ((x : ↥J) : G)) :=
      hP2.to_le (Subgroup.zpowers_le.mpr hxG)
    have : ((x : ↥J) : G) = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J)
        (mem_oddCoreOf_iff.mpr ⟨(x : ↥J).2, hxN⟩) hx2
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨k, hk, ⟨q⟩⟩ := specialLinearGroup_sylow_quaternion (GaloisField p f) hF
    (Sylow.mapSurjective (f := φ) hφs P)
  refine ⟨k, hk, ⟨?_⟩⟩
  have hcoe := Sylow.coe_mapSurjective (f := φ) hφs P
  let e2 : ↥(P : Subgroup ↥J) ≃* ↥((P : Subgroup ↥J).map φ) :=
    MulEquiv.ofBijective ((φ.comp (P : Subgroup ↥J).subtype).codRestrict ((P : Subgroup ↥J).map φ)
      (fun x => ⟨x, x.2, rfl⟩))
      ⟨fun a b h => hinj (congrArg Subtype.val h), by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩⟩
  exact (Subgroup.equivMapOfInjective (P : Subgroup ↥J) J.subtype J.subtype_injective).symm.trans
    (e2.trans ((MulEquiv.subgroupCongr hcoe.symm).trans q))

theorem HypOmegaMod.exists_noncentral [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {J : Subgroup G} (hJ : J ∈ Ω) {A : Subgroup G} (hAJ : A ≤ J)
    (hA2 : IsPGroup 2 A) (hA3 : 3 ≤ Nat.card A) : ∃ v ∈ A, ¬ ∀ w ∈ J, v * w = w * v := by
  by_contra hcon
  have hcon' : ∀ v ∈ A, ∀ w ∈ J, v * w = w * v := fun v hv w hw => by
    by_contra h
    exact hcon ⟨v, hv, fun hall => h (hall w hw)⟩
  obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have := natCard_subgroup_le_two_of_subset (A := A) (a := 1) (b := zJ) fun v hv =>
    hΩ.center_two hp hq hJ hzJ v (hAJ hv) (hA2.to_le (Subgroup.zpowers_le.mpr hv))
      (fun y hy => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcon' v hv y hy)]
        exact (oddCoreOf J).one_mem)
  omega

theorem HypOmegaMod.card_le_two_of_le_inf [Finite G] (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {A : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K)
    (hAJ : A ≤ J) : Nat.card A ≤ 2 := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hdvd : Nat.card A ∣ Nat.card ↥(K ⊓ J) := Subgroup.card_dvd_of_le (le_inf hAK hAJ)
  have hN : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  rw [hn] at hdvd
  have h1 := (padicValNat_dvd_iff_le hN).mp hdvd
  have h2 := (hΩ.omega4 K hK J hJ hKJ).1
  have hn1 : n ≤ 1 := h1.trans h2
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    _ = 2 := by norm_num

theorem HypOmegaMod.eq_of_le_of_le [Finite G] (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) {A : Subgroup G} (hA : IsPGroup 2 A) (h4 : 4 ≤ Nat.card A)
    (hAK : A ≤ K) (hAJ : A ≤ J) : K = J := by
  by_contra hne
  have := hΩ.card_le_two_of_le_inf hK hJ hne hA hAK hAJ
  omega

theorem HypOmegaMod.le_normalizer_of_le_centralizer [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hA3 : 3 ≤ Nat.card A) (hAc : A ≤ Subgroup.centralizer ({z} : Set G)) :
    A ≤ Subgroup.normalizer (K : Set G) := by
  refine le_of_noncentral_mem (J := J) (hΩ.exists_noncentral hp hq hJ hAJ hA2 hA3) ?_
  intro v hv hnc
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := hA2.to_le (Subgroup.zpowers_le.mpr hv)
  exact hΩ.omega5 K hK J hJ hKJ z hz v (hAJ hv) hnc hv2
    (Subgroup.mem_centralizer_singleton_iff.mp (hAc hv))

theorem HypOmegaMod.eight_le_of_mem_RSet [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {R : Subgroup G} (hR : R ∈ RSet Ω) : 8 ≤ Nat.card R :=
  (hΩ.isQuatSub_of_mem_RSet hp hR).eight_le

theorem HypOmegaMod.exists_data_of_mem_USet [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {U : Subgroup G} (hU : U ∈ USet Ω) :
    ∃ R ∈ RSet Ω, ∃ J ∈ Ω, IsSylow2In R J ∧ U ≤ R ∧ IsCyclic ↥U ∧
      Nat.card R = 2 * Nat.card U ∧ 4 ≤ Nat.card U := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have h1 := Subgroup.relIndex_mul_card U R
  rw [inf_eq_left.mpr hUR, hidx] at h1
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  exact ⟨R, hR, J, hJ, hRJ, hUR, hcyc, h1.symm, by omega⟩

theorem HypOmegaMod.isPGroup_of_mem_USet [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {U : Subgroup G} (hU : U ∈ USet Ω) : IsPGroup 2 U := by
  obtain ⟨R, -, J, -, hRJ, hUR, -⟩ := hΩ.exists_data_of_mem_USet hp hU
  exact hRJ.2.1.to_le hUR

theorem HypOmegaMod.exists_member_of_mem_USet [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {U : Subgroup G} (hU : U ∈ USet Ω) : ∃ K ∈ Ω, U ≤ K := by
  obtain ⟨R, -, J, hJ, hRJ, hUR, -⟩ := hΩ.exists_data_of_mem_USet hp hU
  exact ⟨J, hJ, hUR.trans hRJ.1⟩

theorem HypOmegaMod.eq_of_mem_USet [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {U : Subgroup G} (hU : U ∈ USet Ω) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω)
    (hUK : U ≤ K) (hUK' : U ≤ K') : K = K' := by
  obtain ⟨R, -, J, -, hRJ, hUR, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hU
  exact hΩ.eq_of_le_of_le hK hK' (hRJ.2.1.to_le hUR) h4 hUK hUK'

theorem inf_le_oddCoreOf_of_odd [Finite G] {K : Subgroup G} (X : Subgroup G) [X.Normal]
    (hodd : Odd (Nat.card ↥(X ⊓ K))) : K ⊓ X ≤ oddCoreOf K := by
  have hN : (X.subgroupOf K).Normal := inferInstance
  have hcard : Nat.card (X.subgroupOf K) = Nat.card ↥(X ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hle : X.subgroupOf K ≤ classicalInvolutionOddCore ↥K :=
    le_sSup ⟨hN, by rw [hcard]; exact hodd⟩
  intro x hx
  exact mem_oddCoreOf_iff.mpr ⟨hx.1, hle (show (⟨x, hx.1⟩ : ↥K) ∈ X.subgroupOf K from hx.2)⟩

theorem isUniqueInvolution_map_mk_of_odd [Finite G] {K X : Subgroup G} [X.Normal] {z : G}
    (hodd : Odd (Nat.card ↥(X ⊓ K))) (hz : IsUniqueInvolution K z) :
    IsUniqueInvolution (K.map (QuotientGroup.mk' X)) (QuotientGroup.mk' X z) := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  refine ⟨⟨z, hz.mem, rfl⟩, ?_, ?_, ?_⟩
  · intro h
    have hzX : z ∈ X := (QuotientGroup.eq_one_iff z).mp h
    have h2 : 2 ∣ Nat.card ↥(X ⊓ K) := by
      have := Subgroup.orderOf_dvd_natCard (X ⊓ K) (x := z) ⟨hzX, hz.mem⟩
      rwa [hz2] at this
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · rw [← map_mul, hz.sq, map_one]
  · rintro _ ⟨k, hk, rfl⟩ hy
    have hkkX : k * k ∈ X := by
      have h0 : QuotientGroup.mk' X (k * k) = 1 := by rw [map_mul]; exact hy
      exact (QuotientGroup.eq_one_iff _).mp h0
    have hkk : (⟨k * k, hkkX, K.mul_mem hk hk⟩ : ↥(X ⊓ K)) ^ Nat.card ↥(X ⊓ K) = 1 :=
      pow_card_eq_one'
    have hm : (k * k) ^ Nat.card ↥(X ⊓ K) = 1 := congrArg Subtype.val hkk
    have h1 : k ^ Nat.card ↥(X ⊓ K) * k ^ Nat.card ↥(X ⊓ K) = 1 := by
      rw [← (Commute.refl k).mul_pow]
      exact hm
    have hy' : QuotientGroup.mk' X k ^ Nat.card ↥(X ⊓ K) = QuotientGroup.mk' X k := by
      obtain ⟨j, hj⟩ := hodd
      have hsq : QuotientGroup.mk' X k ^ 2 = 1 := by rw [pow_two]; exact hy
      rw [hj, pow_succ, pow_mul, hsq, one_pow, one_mul]
    rcases hz.unique (k ^ Nat.card ↥(X ⊓ K)) (K.pow_mem hk _) h1 with h2 | h2
    · left
      rw [← hy', ← map_pow, h2, map_one]
    · right
      rw [← hy', ← map_pow, h2]

theorem oddCoreOf_map_mk_of_odd [Finite G] {K X : Subgroup G} [X.Normal]
    (hodd : Odd (Nat.card ↥(X ⊓ K))) :
    oddCoreOf (K.map (QuotientGroup.mk' X)) = (oddCoreOf K).map (QuotientGroup.mk' X) := by
  obtain ⟨φ, hφs, hφapp⟩ : ∃ φ : ↥K →* ↥(K.map (QuotientGroup.mk' X)), Function.Surjective φ ∧
      ∀ x : ↥K, ((φ x : ↥(K.map (QuotientGroup.mk' X))) : G ⧸ X) =
        QuotientGroup.mk' X (x : G) :=
    ⟨((QuotientGroup.mk' X).comp K.subtype).codRestrict (K.map (QuotientGroup.mk' X))
      (fun x => ⟨x, x.2, rfl⟩), by
        rintro ⟨_, k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, rfl⟩, fun x => rfl⟩
  have hker : ∀ x : ↥K, φ x = 1 ↔ (x : G) ∈ X := by
    intro x
    rw [Subtype.ext_iff, hφapp]
    exact QuotientGroup.eq_one_iff (x : G)
  have hkerodd : Odd (Nat.card φ.ker) := by
    have h1 : φ.ker = X.subgroupOf K := by
      ext x
      rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    have hcard : Nat.card (X.subgroupOf K) = Nat.card ↥(X ⊓ K) := by
      rw [← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h1, hcard]
    exact hodd
  apply le_antisymm
  · intro b hb
    obtain ⟨hbK, hbN⟩ := mem_oddCoreOf_iff.mp hb
    obtain ⟨κ, hκ⟩ := hφs ⟨b, hbK⟩
    set L : Subgroup ↥K := (classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' X))).comap φ
      with hL
    have hLn : L.Normal := Subgroup.Normal.comap inferInstance φ
    have hle : φ.ker ≤ L := Subgroup.ker_le_comap φ _
    have hcardL : Nat.card φ.ker * φ.ker.relIndex L = Nat.card L := by
      have hmul := (φ.ker.subgroupOf L).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hmul
      exact hmul
    have hidx : φ.ker.relIndex L = Nat.card (L.map φ) := Subgroup.relIndex_ker L φ
    have hmap : L.map φ = classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' X)) :=
      Subgroup.map_comap_eq_self_of_surjective hφs _
    have hLodd : Odd (Nat.card L) := by
      rw [← hcardL, hidx, hmap]
      exact hkerodd.mul (CFSG.ComponentClassification.OddCore.odd_card _)
    have hLN : L ≤ classicalInvolutionOddCore ↥K := le_sSup ⟨hLn, hLodd⟩
    have hκL : κ ∈ L := by
      show φ κ ∈ classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' X))
      rw [hκ]
      exact hbN
    refine ⟨(κ : G), mem_oddCoreOf_iff.mpr ⟨κ.2, hLN hκL⟩, ?_⟩
    have := congrArg Subtype.val hκ
    rw [hφapp] at this
    exact this
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨haK, haN⟩ := mem_oddCoreOf_iff.mp ha
    have hnorm : ((classicalInvolutionOddCore ↥K).map φ).Normal :=
      (classicalInvolutionOddCore_normal ↥K).map φ hφs
    have hoddmap : Odd (Nat.card ↥((classicalInvolutionOddCore ↥K).map φ)) :=
      (CFSG.ComponentClassification.OddCore.odd_card ↥K).of_dvd_nat
        (Subgroup.card_map_dvd (H := classicalInvolutionOddCore ↥K) φ)
    have hN1 : (classicalInvolutionOddCore ↥K).map φ ≤
        classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' X)) := le_sSup ⟨hnorm, hoddmap⟩
    have h1 : (⟨QuotientGroup.mk' X a, ⟨a, haK, rfl⟩⟩ : ↥(K.map (QuotientGroup.mk' X))) =
        φ ⟨a, haK⟩ := Subtype.ext (hφapp ⟨a, haK⟩).symm
    refine mem_oddCoreOf_iff.mpr ⟨⟨a, haK, rfl⟩, ?_⟩
    rw [h1]
    exact hN1 (Subgroup.mem_map_of_mem φ haN)

theorem oddCoreOf_subgroupOf {K Y : Subgroup G} (hKY : K ≤ Y) :
    oddCoreOf (K.subgroupOf Y) = (oddCoreOf K).subgroupOf Y := by
  let e : ↥(K.subgroupOf Y) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKY
  have hinv : (classicalInvolutionOddCore ↥(K.subgroupOf Y)).map e.toMonoidHom =
      classicalInvolutionOddCore ↥K := CFSG.ComponentClassification.OddCore.equiv_invariant e
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    obtain ⟨h, hxN⟩ := mem_oddCoreOf_iff.mp hx
    have h1 : e ⟨x, h⟩ ∈ classicalInvolutionOddCore ↥K := by
      rw [← hinv]
      exact ⟨⟨x, h⟩, hxN, rfl⟩
    exact mem_oddCoreOf_iff.mpr ⟨h, h1⟩
  · intro hx
    obtain ⟨h, hxN⟩ := mem_oddCoreOf_iff.mp hx
    rw [← hinv] at hxN
    obtain ⟨y, hy, hyx⟩ := hxN
    have hyx' : y = ⟨x, h⟩ := e.injective hyx
    exact mem_oddCoreOf_iff.mpr ⟨h, hyx' ▸ hy⟩

end CFSG.ClassicalInvolution.Asc77
