module

public import CFSG.ClassicalInvolution.Q3.Q3CLKey
public import CFSG.ClassicalInvolution.AschTight.Sec6GenL62
public import CFSG.ClassicalInvolution.AschTight.Sec71Cases
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenE612

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
  CFSG.ClassicalInvolution.Q3.Q3CL
open scoped commutatorElement

section Part1


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem etaExists_of_gen (hΩ : HypOmegaGen Ω) : Sec7.EtaExists Ω :=
  fun S => Sec6Gen.exists_invariant_mem_etaSet hΩ S

theorem etaAbelian_of_gen (hΩ : HypOmegaGen Ω) : Sec7.EtaAbelian Ω :=
  fun _ ⟨_, hS, hinv⟩ => (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hS hinv).1

theorem etaMeets_of_gen (hΩ : HypOmegaGen Ω) : Sec7.EtaMeets Ω :=
  Sec6Gen.l6_11Gen G Ω hΩ

theorem orderOf_eq_orderOfGen (hΩ : HypOmegaGen Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) : orderOf u = orderOf v := by
  have h1 := hd.card
  have h2 := hd'.card
  have h3 := Sec6Gen.natCard_isSylow2In_eq hΩ hd.memK hd'.memK hd.sylow hd'.sylow
  omega

theorem jEqGen (hΩ : HypOmegaGen Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) : v ^ (orderOf u / 2) = j := by
  rw [orderOf_eq_orderOfGen hΩ hd hd']
  exact hd'.z_eq

theorem not_isCyclic_of_mem_RSetGen (hΩ : HypOmegaGen Ω)
    {R : Subgroup G} (hR : R ∈ RSet Ω) : ¬ IsCyclic ↥R := by
  intro hc
  obtain ⟨x, hx, y, hy, hxy⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR).exists_not_commute
  obtain ⟨g, hg⟩ := hc.exists_generator
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have h1 : (⟨x, hx⟩ : ↥R) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
    rw [← ha, ← hb]
    exact (Commute.zpow_zpow_self g a b).eq
  exact hxy (congrArg Subtype.val h1)

theorem comm_le_oddCore_of_centralizesGen (hΩ : HypOmegaGen Ω) {K J T : Subgroup G} {z j : G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j) (hzj : z ≠ j)
    (hT : IsSylow2In T J) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (hT8 : 8 ≤ Nat.card T) (hTc : ¬ IsCyclic ↥T) : ⁅T, K⁆ ≤ oddCoreOf K := by
  have hJt : J ∉ twinSet Ω K := by
    rintro ⟨-, z', hz', hj'⟩
    exact hzj ((hz.eq hz').trans (hj'.eq hj))
  have hTs : IsSylow2In T (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    ⟨le_inf hT.1 hTz, hT.2.1, fun V hV hV2 hTV => hT.2.2 V (hV.trans inf_le_left) hV2 hTV⟩
  have hjT : j ∈ T := hj.mem_of_le hT.1 hT.2.1 (by omega)
  have hj2 : Nat.card ↥(Subgroup.zpowers j) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hj.sq) hj.ne_one
  rcases Sec6Gen.l6_2Gen G Ω hΩ K hK z hz J hJ hJt j hj T hTs hjT with h | h | h | h
  · rw [h.1] at hT8
    omega
  · rw [h.1] at hT8
    omega
  · obtain ⟨-, -, -, hc, -⟩ := h.1
    exact absurd hc hTc
  · exact h.2

theorem exists_dDataGen (hΩ : HypOmegaGen Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {u r : G}
    (hu : Subgroup.zpowers u = R ⊓ W) (hRur : R = Subgroup.closure {u, r}) :
    ∃ K : Subgroup G, ∃ z : G, DData Ω W R K u r z := by
  have habel : Sec7.EtaAbelian Ω := etaAbelian_of_gen hΩ
  have h611 : Sec7.EtaMeets Ω := etaMeets_of_gen hΩ
  obtain ⟨K, hK, hRsyl⟩ := exists_isSylow2In_of_mem_RSet hR.1
  have hRK := hRsyl.1
  have hWK := Q3CL.Sec7.le_normalizer_of_mem_DSet hΩ habel h611 hW hR hK hRK
  have hW2 := Sec7.isPGroup_of_mem_WSet hW
  obtain ⟨η, hη, hWη⟩ := id hW
  obtain ⟨S₁, hS₁⟩ := (IsPGroup.to_sup_of_normal_right' (Sec7.isPGroup_of_mem_RSet hR.1) hW2
    hR.2).exists_le_sylow
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR.1
  have hKS₁ : 2 < Nat.card ↥(K ⊓ (S₁ : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hRK (le_sup_left.trans hS₁))
    omega
  have hKWη : K ⊓ W ∈ η := by
    have := h611 S₁ η hη (fun V hV => (hWη ▸ le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) V hV
      le_rfl : V ≤ W).trans (le_sup_right.trans hS₁)) K hK hKS₁
    rwa [← hWη] at this
  have hKWU := Sec7.mem_USet_of_mem_etaG hη hKWη
  have hKW2 : IsPGroup 2 ↥(K ⊓ W) := hW2.to_le inf_le_right
  have hRN : R ≤ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) := fun x hx =>
    Sec7.mem_normalizer_inf (Subgroup.le_normalizer (hRK hx)) (hR.2 hx)
  have hKWR : K ⊓ W ≤ R := by
    have := hRsyl.2.2 (R ⊔ (K ⊓ W)) (sup_le hRK inf_le_left)
      (IsPGroup.to_sup_of_normal_right' hRsyl.2.1 hKW2 hRN) le_sup_left
    rw [← this]
    exact le_sup_right
  have hKWeq : K ⊓ W = Subgroup.zpowers u := by
    rw [hu]
    exact le_antisymm (le_inf hKWR inf_le_right) (inf_le_inf_right W hRK)
  have hUU : Subgroup.zpowers u ∈ USet Ω := hKWeq ▸ hKWU
  have hcardU : Nat.card R = 2 * Nat.card ↥(Subgroup.zpowers u) :=
    Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet hΩ hUU hK hRsyl
  have hcard : Nat.card R = 2 * orderOf u := by rw [hcardU, Nat.card_zpowers]
  have hU2 : IsPGroup 2 ↥(Subgroup.zpowers u) := hKWeq ▸ hKW2
  obtain ⟨n, hn⟩ := hU2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have h4 : 4 ≤ orderOf u := by omega
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have huK : u ∈ K := (show u ∈ K ⊓ W by rw [hKWeq]; exact Subgroup.mem_zpowers u).1
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hn
      omega
    · exact h0
  have hhalf : orderOf u / 2 * 2 = orderOf u := by
    rw [hn]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, Nat.mul_div_cancel _ two_pos]
  have hzeq : u ^ (orderOf u / 2) = z := by
    have hsq : u ^ (orderOf u / 2) * u ^ (orderOf u / 2) = 1 := by
      rw [← pow_add, ← two_mul, mul_comm, hhalf, pow_orderOf_eq_one]
    have hne : u ^ (orderOf u / 2) ≠ 1 :=
      pow_ne_one_of_lt_orderOf (by omega) (by omega)
    exact (hz.unique _ (K.pow_mem huK _) hsq).resolve_left hne
  have hUR : Subgroup.zpowers u ≤ R := hKWeq ▸ hKWR
  have hzR : IsUniqueInvolution R z :=
    AscL62.isUniqueInvolution_of_le hz hRK (hUR (hzeq ▸ Subgroup.npow_mem_zpowers u _))
  have hQ := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR.1
  have hrR : r ∈ R := hRur ▸ Subgroup.subset_closure (by simp)
  have hUc : IsCyclic ↥(Subgroup.zpowers u) := inferInstance
  have hrU : r ∉ Subgroup.zpowers u := by
    intro hr
    have hle : R ≤ Subgroup.zpowers u := by
      rw [hRur, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_zpowers _
      · exact hr
    obtain ⟨x, hx, y, hy, hxy⟩ := hQ.exists_not_commute
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle hx)
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle hy)
    exact hxy (Commute.zpow_zpow_self u a b).eq
  have hconj : ∀ c ∈ Subgroup.zpowers u, r * c * r⁻¹ = c⁻¹ := fun c hc =>
    AscL62.conj_eq_inv_of_not_mem hQ hzR hUR hUc hcardU hrR hrU hc
  refine ⟨K, z, ⟨hK, hRsyl, hR, hKWeq, hUR, hUU, hWK, hcard, ⟨n, hn⟩, h4, hz, hzeq, hrR, hrU,
    hconj u (Subgroup.mem_zpowers u), AscL62.sq_eq_of_not_mem hQ hzR hUR hUc hcardU hrR hrU,
    fun x hx => ?_⟩⟩
  by_cases hxU : x ∈ Subgroup.zpowers u
  · exact Or.inl hxU
  · refine Or.inr ⟨(r⁻¹ * x)⁻¹, Subgroup.inv_mem _
      (AscL62.inv_mul_mem_of_index_two hUR hcardU hrR hx hrU hxU), ?_⟩
    have := hconj _ (AscL62.inv_mul_mem_of_index_two hUR hcardU hrR hx hrU hxU)
    calc x = (r * (r⁻¹ * x) * r⁻¹) * r := by group
      _ = (r⁻¹ * x)⁻¹ * r := by rw [this]

theorem memOCWOfOddGen (_hΩ : HypOmegaGen Ω) (hcl : ClassicalClause Ω)
    (hd : DData Ω W R K u r z) {x : G}
    (hxK : x ∈ K) (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hodd : Odd (orderOf x)) :
    x ∈ OCW W := by
  have hU2 : IsPGroup 2 ↥(K ⊓ W) := by
    obtain ⟨n, hn⟩ := hd.orderOf_eq
    rw [hd.inf_eq]
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hUc : IsCyclic ↥(K ⊓ W) := by rw [hd.inf_eq]; infer_instance
  have hC := Sec7.mem_centralizer_of_odd hd.le_normalizer hUc hU2 hxK hxW hodd
  have hu2 : IsPGroup 2 ↥(Subgroup.zpowers u) := hU2.to_le (Subgroup.zpowers_le.mpr hd.u_mem)
  exact Q3CL.Sec7.oddCoreOf_inf_centralizer_le_OCW hcl hd.memK hd.uinv hd.z_memW
    (Q3CL.Sec7.mem_oddCoreOf_of_odd hcl hd.memK hd.u_memK hd.u_memW hu2 hd.u_sq_ne ⟨hxK, hC⟩ hodd)

theorem conj_z_eqGen (hΩ : HypOmegaGen Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) : t * z * t⁻¹ = z * j ^ k := by
  have := conj_pow_eq (hWc v hd'.u_memW u hd.u_memW) hk (orderOf u / 2)
  rwa [hd.z_eq, jEqGen hΩ hd hd'] at this

theorem comm_z_tGen (hΩ : HypOmegaGen Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) : ⁅z, t⁆ = (j ^ k)⁻¹ :=
  comm_eq_of_conj (hWc z hd.z_memW j hd'.z_memW) (conj_z_eqGen hΩ hd hd' hWc hk)

theorem even_of_comm_memGen (hΩ : HypOmegaGen Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) (hmem : ⁅z, t⁆ ∈ oddCoreOf J) : Even k := by
  rw [comm_z_tGen hΩ hd hd' hWc hk] at hmem
  by_contra hke
  rw [zpow_eq_self_of_odd hd'.uinv.sq (Int.not_even_iff_odd.mp hke),
    inv_eq_of_mul_eq_one_right hd'.uinv.sq] at hmem
  exact hd'.uinv.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J) hmem
    (isPGroup_zpowers_of_mul_self_eq_one hd'.uinv.sq hd'.uinv.ne_one))

theorem even_of_evenGen (hΩ : HypOmegaGen Ω)
    (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hzj : z ≠ j) {i k : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k) (hie : Even i) : Even k := by
  have hrj : r * j * r⁻¹ = j := by
    have := conj_pow_eq (hWc u hd.u_memW v hd'.u_memW) hi (orderOf u / 2)
    rwa [jEqGen hΩ hd hd', hd.z_eq, zpow_eq_one_of_even hd.uinv.sq hie, mul_one] at this
  have hRj := hd.le_centralizer hWc hd'.z_memW hrj
  have hRJ := comm_le_oddCore_of_centralizesGen hΩ hd'.memK hd.memK hd'.uinv hd.uinv
    (Ne.symm hzj) hd.sylow hRj (Sec6Gen.eight_le_of_mem_RSet hΩ hd.memD.1)
    (not_isCyclic_of_mem_RSetGen hΩ hd.memD.1)
  have hzR : z ∈ R := hd.uinv.mem_of_le hd.le hd.sylow.2.1
    (by have := Sec6Gen.eight_le_of_mem_RSet hΩ hd.memD.1; omega)
  exact even_of_comm_memGen hΩ hd hd' hWc hk
    (hRJ (Subgroup.commutator_mem_commutator hzR hd'.r_memK))

theorem case_two_of_evenGen (hΩ : HypOmegaGen Ω) (hcl : ClassicalClause Ω)
    (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hKJ : K ≠ J) (hzj : z ≠ j) {i k : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k) (hie : Even i)
    (hke : Even k) : J ∈ omegaNbr Ω K ∧ ∀ a ∈ R, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ OCW W := by
  have hrj : r * j * r⁻¹ = j := by
    have := conj_pow_eq (hWc u hd.u_memW v hd'.u_memW) hi (orderOf u / 2)
    rwa [jEqGen hΩ hd hd', hd.z_eq, zpow_eq_one_of_even hd.uinv.sq hie, mul_one] at this
  have htz : t * z * t⁻¹ = z := by
    rw [conj_z_eqGen hΩ hd hd' hWc hk, zpow_eq_one_of_even hd'.uinv.sq hke, mul_one]
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hd.memD.1
  have h8' := Sec6Gen.eight_le_of_mem_RSet hΩ hd'.memD.1
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hd'.memK hd.memK (Ne.symm hKJ) hd'.uinv hd.le
      hd.sylow.2.1 (by omega) (hd.le_centralizer hWc hd'.z_memW hrj)
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hd.memK hd'.memK hKJ hd.uinv hd'.le
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
  exact memOCWOfOddGen hΩ hcl hd hK' (comm_mem_normalizer hd hd' ha hb)
    (odd_orderOf_of_mem (odd_natCard_inf hd hd' hzj) ⟨hK', hJ'⟩)

end Part1

end CFSG.ClassicalInvolution.Q3.Q3T6D
