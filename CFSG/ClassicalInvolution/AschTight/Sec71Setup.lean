module

public import CFSG.ClassicalInvolution.AschTight.Sec7KeyD

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

structure DData (Ω : Set (Subgroup G)) (W R K : Subgroup G) (u r z : G) : Prop where
  memK : K ∈ Ω
  sylow : IsSylow2In R K
  memD : R ∈ DSet Ω W
  inf_eq : K ⊓ W = Subgroup.zpowers u
  U_le_R : Subgroup.zpowers u ≤ R
  memU : Subgroup.zpowers u ∈ USet Ω
  le_normalizer : W ≤ Subgroup.normalizer (K : Set G)
  card : Nat.card R = 2 * orderOf u
  orderOf_eq : ∃ n : ℕ, orderOf u = 2 ^ n
  four_le : 4 ≤ orderOf u
  uinv : IsUniqueInvolution K z
  z_eq : u ^ (orderOf u / 2) = z
  r_mem : r ∈ R
  r_not_mem : r ∉ Subgroup.zpowers u
  conj_u : r * u * r⁻¹ = u⁻¹
  sq_r : r * r = z
  cover : ∀ x ∈ R, x ∈ Subgroup.zpowers u ∨ ∃ y ∈ Subgroup.zpowers u, x = y * r

namespace DData

variable {Ω : Set (Subgroup G)} {W R K : Subgroup G} {u r z : G}

theorem le (hd : DData Ω W R K u r z) : R ≤ K := hd.sylow.1

theorem u_mem (hd : DData Ω W R K u r z) : u ∈ K ⊓ W := by
  rw [hd.inf_eq]
  exact Subgroup.mem_zpowers u

theorem z_mem (hd : DData Ω W R K u r z) : z ∈ Subgroup.zpowers u := by
  rw [← hd.z_eq]
  exact Subgroup.npow_mem_zpowers u _

theorem z_memW (hd : DData Ω W R K u r z) : z ∈ W := by
  have : z ∈ K ⊓ W := by rw [hd.inf_eq]; exact hd.z_mem
  exact this.2

theorem r_memK (hd : DData Ω W R K u r z) : r ∈ K := hd.le hd.r_mem

theorem r_normW (hd : DData Ω W R K u r z) : r ∈ Subgroup.normalizer (W : Set G) :=
  hd.memD.2 hd.r_mem

theorem u_memW (hd : DData Ω W R K u r z) : u ∈ W := hd.u_mem.2

theorem u_memK (hd : DData Ω W R K u r z) : u ∈ K := hd.u_mem.1

theorem u_sq_ne (hd : DData Ω W R K u r z) : u * u ≠ 1 := by
  intro h
  have := Nat.le_of_dvd two_pos
    (orderOf_dvd_of_pow_eq_one (x := u) (n := 2) (by rw [pow_two]; exact h))
  have := hd.four_le
  omega

end DData

variable {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_dData [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {u r : G}
    (hu : Subgroup.zpowers u = R ⊓ W) (hRur : R = Subgroup.closure {u, r}) :
    ∃ K : Subgroup G, ∃ z : G, DData Ω W R K u r z := by
  have habel : Sec7.EtaAbelian Ω := fun η ⟨S, hS, hinv⟩ =>
    ((l6_9_proved p f hp hq G Ω hΩ S).2 η hS hinv).1
  have h611 : Sec7.EtaMeets Ω := l6_11_proved p f hp hq G Ω hΩ
  obtain ⟨K, hK, hRsyl⟩ := exists_isSylow2In_of_mem_RSet hR.1
  have hRK := hRsyl.1
  have hWK := Sec7.le_normalizer_of_mem_DSet hp hq hΩ habel h611 hW hR hK hRK
  have hW2 := Sec7.isPGroup_of_mem_WSet hW
  obtain ⟨η, hη, hWη⟩ := id hW
  obtain ⟨S₁, hS₁⟩ := (IsPGroup.to_sup_of_normal_right' (Sec7.isPGroup_of_mem_RSet hR.1) hW2
    hR.2).exists_le_sylow
  have h8 := hΩ.eight_le_of_mem_RSet hp hR.1
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
    Sec7.natCard_eq_two_mul_of_mem_USet hp hΩ hUU hK hRsyl
  have hcard : Nat.card R = 2 * orderOf u := by rw [hcardU, Nat.card_zpowers]
  have hU2 : IsPGroup 2 ↥(Subgroup.zpowers u) := hKWeq ▸ hKW2
  obtain ⟨n, hn⟩ := hU2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have h4 : 4 ≤ orderOf u := by omega
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
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
  have hQ := hΩ.isQuatSub_of_mem_RSet hp hR.1
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

theorem OCW_inf_eq_bot [Finite G] {W : Subgroup G} (hW2 : IsPGroup 2 W) : OCW W ⊓ W = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact (Subgroup.mem_bot).mpr (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hx.1
    (hW2.to_le (Subgroup.zpowers_le.mpr hx.2)))

theorem OCW_le_centralizer (W : Subgroup G) : OCW W ≤ Subgroup.centralizer (W : Set G) :=
  oddCoreOf_le_self _

namespace DData

variable {W R K : Subgroup G} {u r z : G}

theorem inf_normalizer_le [Finite G] (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z) :
    K ⊓ Subgroup.normalizer (W : Set G) ≤ R ⊔ OCW W := by
  have hU2 : IsPGroup 2 ↥(K ⊓ W) := by
    obtain ⟨n, hn⟩ := hd.orderOf_eq
    rw [hd.inf_eq]
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hUc : IsCyclic ↥(K ⊓ W) := by rw [hd.inf_eq]; infer_instance
  have hOH : oddCoreOf (K ⊓ Subgroup.centralizer (W : Set G)) ≤
      K ⊓ Subgroup.normalizer (W : Set G) :=
    (oddCoreOf_le_self _).trans
      (inf_le_inf_left K (Subgroup.centralizer_le_normalizer (W : Set G)))
  have hHO : K ⊓ Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer (oddCoreOf (K ⊓ Subgroup.centralizer (W : Set G)) : Set G) :=
    fun h hh => mem_normalizer_oddCoreOf_of_mem_normalizer
      (Sec7.mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_inf.mp hh).1)
        (Sec7.normalizer_le_normalizer_centralizer W (Subgroup.mem_inf.mp hh).2))
  have hRH : IsSylow2In R (K ⊓ Subgroup.normalizer (W : Set G)) :=
    ⟨le_inf hd.le hd.memD.2, hd.sylow.2.1, fun V' hV'H hV'2 hRV' =>
      hd.sylow.2.2 V' (hV'H.trans inf_le_left) hV'2 hRV'⟩
  have hle := Sec7.le_sup_of_pow_mem hOH hHO hRH fun h hh =>
    Sec7.exists_pow_two_pow_mem hΩ hd.memK hd.le_normalizer hUc hU2 hd.u_mem hd.u_sq_ne
      (Subgroup.mem_inf.mp hh).1 (Subgroup.mem_inf.mp hh).2
  exact hle.trans (sup_le_sup_left
    (Sec7.oddCoreOf_inf_centralizer_le_OCW hΩ hd.memK hd.uinv hd.z_memW) R)

theorem mem_OCW_of_odd [Finite G] (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z) {x : G}
    (hxK : x ∈ K) (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hodd : Odd (orderOf x)) :
    x ∈ OCW W := by
  have hU2 : IsPGroup 2 ↥(K ⊓ W) := by
    obtain ⟨n, hn⟩ := hd.orderOf_eq
    rw [hd.inf_eq]
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hUc : IsCyclic ↥(K ⊓ W) := by rw [hd.inf_eq]; infer_instance
  have hC := Sec7.mem_centralizer_of_odd hd.le_normalizer hUc hU2 hxK hxW hodd
  have hu2 : IsPGroup 2 ↥(Subgroup.zpowers u) := hU2.to_le (Subgroup.zpowers_le.mpr hd.u_mem)
  exact Sec7.oddCoreOf_inf_centralizer_le_OCW hΩ hd.memK hd.uinv hd.z_memW
    (Sec7.mem_oddCoreOf_of_odd hΩ hd.memK hd.u_memK hd.u_memW hu2 hd.u_sq_ne ⟨hxK, hC⟩ hodd)

end DData

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
