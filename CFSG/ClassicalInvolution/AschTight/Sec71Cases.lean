module

public import CFSG.ClassicalInvolution.AschTight.Sec71Rel
public import CFSG.ClassicalInvolution.Asc77.AscL62Lem33
public import CFSG.ClassicalInvolution.AschTight.Sec71Basic

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem conj_z_eq (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) : t * z * t⁻¹ = z * j ^ k := by
  have := conj_pow_eq (hWc v hd'.u_memW u hd.u_memW) hk (orderOf u / 2)
  rwa [hd.z_eq, hd.j_eq hΩ hd'] at this

theorem comm_z_t (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) : ⁅z, t⁆ = (j ^ k)⁻¹ :=
  comm_eq_of_conj (hWc z hd.z_memW j hd'.z_memW) (conj_z_eq hΩ hd hd' hWc hk)

theorem even_of_comm_mem (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) (hmem : ⁅z, t⁆ ∈ oddCoreOf J) : Even k := by
  rw [comm_z_t hΩ hd hd' hWc hk] at hmem
  by_contra hke
  rw [zpow_eq_self_of_odd hd'.uinv.sq (Int.not_even_iff_odd.mp hke),
    inv_eq_of_mul_eq_one_right hd'.uinv.sq] at hmem
  exact hd'.uinv.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J) hmem
    (isPGroup_zpowers_of_mul_self_eq_one hd'.uinv.sq hd'.uinv.ne_one))

theorem even_of_even (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hzj : z ≠ j) {i k : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k) (hie : Even i) : Even k := by
  have hrj : r * j * r⁻¹ = j := by
    have := conj_pow_eq (hWc u hd.u_memW v hd'.u_memW) hi (orderOf u / 2)
    rwa [hd.j_eq hΩ hd', hd.z_eq, zpow_eq_one_of_even hd.uinv.sq hie, mul_one] at this
  have hRj := hd.le_centralizer hWc hd'.z_memW hrj
  have hRJ := comm_le_oddCore_of_centralizes hp hq hΩ hd'.memK hd.memK hd'.uinv hd.uinv
    (Ne.symm hzj) hd.sylow hRj (hΩ.eight_le_of_mem_RSet hp hd.memD.1)
    (not_isCyclic_of_mem_RSet hp hΩ hd.memD.1)
  have hzR : z ∈ R := hd.uinv.mem_of_le hd.le hd.sylow.2.1
    (by have := hΩ.eight_le_of_mem_RSet hp hd.memD.1; omega)
  exact even_of_comm_mem hΩ hd hd' hWc hk
    (hRJ (Subgroup.commutator_mem_commutator hzR hd'.r_memK))

omit [Finite G] in
theorem odd_orderOf_of_mem {H : Subgroup G} (hH : Odd (Nat.card H)) {x : G} (hx : x ∈ H) :
    Odd (orderOf x) :=
  hH.of_dvd_nat (Subgroup.orderOf_dvd_natCard H hx)

omit [Finite G] in
theorem comm_mem_normalizer (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j) {a b : G}
    (ha : a ∈ R) (hb : b ∈ T) : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.normalizer (W : Set G) := by
  have h1 := hd.memD.2 ha
  have h2 := hd'.memD.2 hb
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1))
    (Subgroup.inv_mem _ h2)

theorem case_two_of_twin (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hKJ : K ≠ J) (hzj : z = j) :
    J ∈ omegaNbr Ω K ∧ ∀ a ∈ R, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ OCW W := by
  subst hzj
  have hJK := hΩ.le_normalizer_of_twin hd'.memK hd.memK (Ne.symm hKJ) hd'.uinv hd.uinv
  have hc := hΩ.comm_le_oddCore_of_twin hd.memK hd'.memK hKJ hd.uinv hd'.uinv
  refine ⟨⟨hd'.memK, Ne.symm hKJ, T, hd'.memD.1, hd'.le, hd'.le.trans hJK⟩, fun a ha b hb => ?_⟩
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf J := by
    have := (hc (Subgroup.commutator_mem_commutator (hd.le ha) (hd'.le hb))).2
    rwa [commutatorElement_def] at this
  exact hd'.mem_OCW_of_odd hΩ (oddCoreOf_le_self J hmem) (comm_mem_normalizer hd hd' ha hb)
    (odd_orderOf_of_mem (oddCoreOf_odd_natCard J) hmem)

theorem odd_natCard_inf (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j) (hzj : z ≠ j) :
    Odd (Nat.card ↥(K ⊓ J)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(K ⊓ J) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hx2 : (x : G) * x = 1 := by
    rw [← pow_two, ← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
  have hx1 : (x : G) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega
  have h1 := (hd.uinv.unique x x.2.1 hx2).resolve_left hx1
  have h2 := (hd'.uinv.unique x x.2.2 hx2).resolve_left hx1
  exact hzj (h1.symm.trans h2)

theorem case_two_of_even (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hKJ : K ≠ J) (hzj : z ≠ j) {i k : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k) (hie : Even i)
    (hke : Even k) : J ∈ omegaNbr Ω K ∧ ∀ a ∈ R, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ OCW W := by
  have hrj : r * j * r⁻¹ = j := by
    have := conj_pow_eq (hWc u hd.u_memW v hd'.u_memW) hi (orderOf u / 2)
    rwa [hd.j_eq hΩ hd', hd.z_eq, zpow_eq_one_of_even hd.uinv.sq hie, mul_one] at this
  have htz : t * z * t⁻¹ = z := by
    rw [conj_z_eq hΩ hd hd' hWc hk, zpow_eq_one_of_even hd'.uinv.sq hke, mul_one]
  have h8 := hΩ.eight_le_of_mem_RSet hp hd.memD.1
  have h8' := hΩ.eight_le_of_mem_RSet hp hd'.memD.1
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hd'.memK hd.memK (Ne.symm hKJ) hd'.uinv hd.le
      hd.sylow.2.1 (by omega) (hd.le_centralizer hWc hd'.z_memW hrj)
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hd.memK hd'.memK hKJ hd.uinv hd'.le
      hd'.sylow.2.1 (by omega) (hd'.le_centralizer hWc hd.z_memW htz)
  refine ⟨⟨hd'.memK, Ne.symm hKJ, T, hd'.memD.1, hd'.le, hTK⟩, fun a ha b hb => ?_⟩
  have hK' : a * b * a⁻¹ * b⁻¹ ∈ K := by
    have h1 : b * a⁻¹ * b⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hTK hb) a⁻¹).mp (K.inv_mem (hd.le ha))
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact K.mul_mem (hd.le ha) h1
  have hJ' : a * b * a⁻¹ * b⁻¹ ∈ J := by
    have h1 : a * b * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hRJ ha) b).mp (hd'.le hb)
    exact J.mul_mem h1 (J.inv_mem (hd'.le hb))
  exact hd.mem_OCW_of_odd hΩ hK' (comm_mem_normalizer hd hd' ha hb)
    (odd_orderOf_of_mem (odd_natCard_inf hd hd' hzj) ⟨hK', hJ'⟩)

theorem case_three_of_odd (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hKJ : K ≠ J) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) (hko : Odd k) :
    J ∈ omegaStarNbr Ω K ∧ J ∉ omegaNbr Ω K := by
  refine ⟨⟨hd'.memK, Ne.symm hKJ, Subgroup.zpowers v, hd'.memU, hd'.U_le_K,
    hd'.U_le_W.trans hd.le_normalizer⟩, ?_⟩
  rintro ⟨-, -, T', hT', hT'J, hT'K⟩
  have hT'syl := Sec7.isSylow2In_of_mem_RSet_of_le hp hΩ hT' hd'.memK hT'J
  have hcz : ∀ x ∈ T', x * z = z * x := fun x hx => by
    have h1 : x * z * x⁻¹ = z :=
      hd.uinv.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hT'K hx))
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [h1]
  have hmem := lemma_3_3_member_involution hp hq hΩ hd'.memK hT'syl hd.uinv.sq
    (hd'.le_normalizer hd.z_memW) hcz t hd'.r_memK
  exact (Int.not_even_iff_odd.mpr hko) (even_of_comm_mem hΩ hd hd' hWc hk hmem)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
