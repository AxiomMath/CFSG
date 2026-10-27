module

public import CFSG.GH74.QTGen4.Recog.Ku.A4YC

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

theorem perm5_sq_eq_one_of_pow_64 : ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 →
    τ ^ 64 = 1 → τ ^ 2 = 1 := by
  decide +kernel

theorem perm5_sq_or_cube_of_pow_six : ∀ x : Equiv.Perm (Fin 5), Equiv.Perm.sign x = 1 →
    x ^ 6 = 1 → x ^ 2 = 1 ∨ x ^ 3 = 1 := by
  decide +kernel

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem fpf_of_order_three (h : KuHyp G T M H P z) {y : G} (hyL : y ∈ oTwoUpper M)
    (hy3 : orderOf y = 3) {v : G} (hv : v ∈ pCoreOf 2 M) (hfix : y * v * y⁻¹ = v) : v = 1 := by
  by_contra hv1
  have hcomm : y * v = v * y := by
    calc y * v = y * v * y⁻¹ * y := by group
      _ = v * y := by rw [hfix]
  have hyK : y ∈ oTwoUpper M ⊓ Subgroup.centralizer ({v} : Set G) :=
    ⟨hyL, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  have hd := orderOf_dvd_natCard (⟨y, hyK⟩ : ↥(oTwoUpper M ⊓ Subgroup.centralizer ({v} : Set G)))
  rw [h.card_L_inf_centralizer_of hv hv1, ← Subgroup.orderOf_coe] at hd
  have hd' : orderOf y ∣ 64 := hd
  rw [hy3] at hd'
  norm_num at hd'

theorem normalizer_kuR_of_X (h : KuHyp G T M H P z) {x : G}
    (hx : x ∈ oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) :
    x ∈ Subgroup.normalizer (kuR T M : Set G) := by
  have hw : x * z * x⁻¹ ∈ MulAction.orbit (conjM (oTwoUpper M ⊓
      Subgroup.normalizer (kuV2 T M : Set G))) z :=
    MulAction.mem_orbit_iff.mpr
      ⟨⟨ConjAct.toConjAct x, Subgroup.mem_map_of_mem _ hx⟩, by
        show (ConjAct.toConjAct x : ConjAct G) • z = _
        rw [ConjAct.toConjAct_smul]⟩
  rw [orbit_conjX h] at hw
  have hw1 : x * z * x⁻¹ ≠ 1 := fun e => hw.2 (Set.mem_singleton_iff.mpr e)
  refine Subgroup.mem_normalizer_iff.mpr (fun r => ⟨fun hr => ?_, fun hr => ?_⟩)
  · exact conj_mem_kuR_of h hx.1 hw.1 hw1 rfl hr
  · have hb := conj_inv_mem_kuR_of h hx.1 hw.1 hw1 rfl hr
    have e : x⁻¹ * (x * r * x⁻¹) * x = r := by group
    rw [e] at hb
    exact hb

theorem exists_order_three_X (h : KuHyp G T M H P z) :
    ∃ y ∈ oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G), orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G))) 3
    (by rw [h.card_L_inf_normalizer_kuV2]; norm_num)
  refine ⟨(x : G), x.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hx

theorem clause_f (h : KuHyp G T M H P z) {y : G} (hyL : y ∈ oTwoUpper M)
    (hyN2 : y ∈ Subgroup.normalizer (kuV2 T M : Set G))
    (hK : ∀ v ∈ pCoreOf 2 M, y * v * y⁻¹ = v → v = 1) :
    ∀ v ∈ pCoreOf 2 M, y * v * y⁻¹ * v⁻¹ ∈ kuV2 T M → v ∈ kuV2 T M := by
  have hcomm : ∀ a ∈ pCoreOf 2 M, ∀ b ∈ pCoreOf 2 M, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.vElem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hyV : ∀ v ∈ pCoreOf 2 M, y * v * y⁻¹ ∈ pCoreOf 2 M := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (h.oTwoUpper_le_normalizer_V hyL) v).mp hv
  have hinj : ∀ v ∈ pCoreOf 2 M, ∀ w ∈ pCoreOf 2 M,
      y * v * y⁻¹ * v⁻¹ = y * w * y⁻¹ * w⁻¹ → v = w := by
    intro v hv w hw hFvw
    have hb : y * w * y⁻¹ ∈ pCoreOf 2 M := hyV w hw
    have hwv : w⁻¹ * v ∈ pCoreOf 2 M := (pCoreOf 2 M).mul_mem ((pCoreOf 2 M).inv_mem hw) hv
    have ha_eq : y * v * y⁻¹ = (y * w * y⁻¹) * w⁻¹ * v := by
      calc y * v * y⁻¹ = (y * v * y⁻¹ * v⁻¹) * v := by group
        _ = (y * w * y⁻¹ * w⁻¹) * v := by rw [hFvw]
        _ = (y * w * y⁻¹) * w⁻¹ * v := by group
    have hfix : y * (v * w⁻¹) * y⁻¹ = v * w⁻¹ := by
      calc y * (v * w⁻¹) * y⁻¹ = (y * v * y⁻¹) * (y * w * y⁻¹)⁻¹ := by group
        _ = ((y * w * y⁻¹) * (w⁻¹ * v)) * (y * w * y⁻¹)⁻¹ := by rw [ha_eq]; group
        _ = ((w⁻¹ * v) * (y * w * y⁻¹)) * (y * w * y⁻¹)⁻¹ := by
            rw [hcomm _ hb _ hwv]
        _ = w⁻¹ * v := by group
        _ = v * w⁻¹ := hcomm _ ((pCoreOf 2 M).inv_mem hw) _ hv
    have hu : v * w⁻¹ ∈ pCoreOf 2 M := (pCoreOf 2 M).mul_mem hv ((pCoreOf 2 M).inv_mem hw)
    have h1 : v * w⁻¹ = 1 := hK _ hu hfix
    exact mul_inv_eq_one.mp h1
  intro v hv hF
  let S : Set G := {u | u ∈ pCoreOf 2 M ∧ y * u * y⁻¹ * u⁻¹ ∈ kuV2 T M}
  have hV2S : (kuV2 T M : Set G) ⊆ S := by
    intro x hx
    have hxV : x ∈ pCoreOf 2 M := hx.1
    have hyx : y * x * y⁻¹ ∈ kuV2 T M := (Subgroup.mem_normalizer_iff.mp hyN2 x).mp hx
    exact ⟨hxV, (kuV2 T M).mul_mem hyx ((kuV2 T M).inv_mem hx)⟩
  have hcard : S.ncard ≤ (kuV2 T M : Set G).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun u => y * u * y⁻¹ * u⁻¹) (fun u hu => hu.2)
      (fun a ha b hb hab => hinj a ha.1 b hb.1 hab) (Set.toFinite _)
  have hEq : (kuV2 T M : Set G) = S :=
    Set.eq_of_subset_of_ncard_le hV2S hcard (Set.toFinite _)
  have hvS : v ∈ S := ⟨hv, hF⟩
  rw [← hEq] at hvS
  exact hvS

theorem clause_g (h : KuHyp G T M H P z) {y : G} (hyL : y ∈ oTwoUpper M) (hy3 : orderOf y = 3) :
    ∀ r ∈ kuR T M, y * r * y⁻¹ * r⁻¹ ∈ pCoreOf 2 M → r ∈ pCoreOf 2 M := by
  obtain ⟨φ, -, hker⟩ := h.mQuot
  have hyM : y ∈ M := oTwoUpper_le M hyL
  have hmem : ∀ x : ↥M, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 M := fun x => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have halt : ∀ x (hx : x ∈ oTwoUpper M), φ ⟨x, oTwoUpper_le M hx⟩ ∈ alternatingGroup (Fin 5) := by
    intro x hx
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (oTwoUpper_le_map_comap φ hx)
    have hwe : w = ⟨x, oTwoUpper_le M hx⟩ := Subtype.ext hwx
    rw [← hwe]
    exact hw
  have hsgn : ∀ x (hx : x ∈ oTwoUpper M), Equiv.Perm.sign (φ ⟨x, oTwoUpper_le M hx⟩) = 1 :=
    fun x hx => Equiv.Perm.mem_alternatingGroup.mp (halt x hx)
  intro r hr hcV
  have hrL : r ∈ oTwoUpper M := hr.2
  have hrM : r ∈ M := oTwoUpper_le M hrL
  have hσs : Equiv.Perm.sign (φ ⟨y, hyM⟩) = 1 := hsgn y hyL
  have hτs : Equiv.Perm.sign (φ ⟨r, hrM⟩) = 1 := hsgn r hrL
  have hy3G : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hy3M : (⟨y, hyM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hy3G)
  have hr64G : r ^ 64 = 1 := by
    have hd := orderOf_dvd_natCard (⟨r, hr⟩ : ↥(kuR T M))
    rw [h.card_kuR] at hd
    have hp : (⟨r, hr⟩ : ↥(kuR T M)) ^ 64 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
    have := congrArg Subtype.val hp
    simpa using this
  have hr64M : (⟨r, hrM⟩ : ↥M) ^ 64 = 1 := Subtype.ext (by simpa using hr64G)
  have hτ64 : φ ⟨r, hrM⟩ ^ 64 = 1 := by rw [← map_pow, hr64M, map_one]
  have hτ2 : φ ⟨r, hrM⟩ ^ 2 = 1 := perm5_sq_eq_one_of_pow_64 _ hτs hτ64
  have hσ3 : φ ⟨y, hyM⟩ ^ 3 = 1 := by rw [← map_pow, hy3M, map_one]
  have hσ1 : φ ⟨y, hyM⟩ ≠ 1 := by
    intro e
    have hyV : y ∈ pCoreOf 2 M := (hmem ⟨y, hyM⟩).mp e
    have hy2 : y ^ 2 = 1 := h.vElem.2 y hyV
    have hd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    rw [hy3] at hd
    norm_num at hd
  have hcM : (⟨y, hyM⟩ : ↥M) * ⟨r, hrM⟩ * ⟨y, hyM⟩⁻¹ * ⟨r, hrM⟩⁻¹ =
      ⟨y * r * y⁻¹ * r⁻¹, M.mul_mem (M.mul_mem (M.mul_mem hyM hrM) (M.inv_mem hyM))
        (M.inv_mem hrM)⟩ := Subtype.ext rfl
  have hc1 : φ ((⟨y, hyM⟩ : ↥M) * ⟨r, hrM⟩ * ⟨y, hyM⟩⁻¹ * ⟨r, hrM⟩⁻¹) = 1 := by
    rw [hcM]; exact (hmem _).mpr hcV
  have hc2 := hc1
  simp only [map_mul, map_inv] at hc2
  have e2 : φ ⟨y, hyM⟩ * φ ⟨r, hrM⟩ * (φ ⟨y, hyM⟩)⁻¹ = φ ⟨r, hrM⟩ := mul_inv_eq_one.mp hc2
  have hcomm : φ ⟨y, hyM⟩ * φ ⟨r, hrM⟩ = φ ⟨r, hrM⟩ * φ ⟨y, hyM⟩ := by
    calc φ ⟨y, hyM⟩ * φ ⟨r, hrM⟩
        = φ ⟨y, hyM⟩ * φ ⟨r, hrM⟩ * (φ ⟨y, hyM⟩)⁻¹ * φ ⟨y, hyM⟩ := by group
      _ = φ ⟨r, hrM⟩ * φ ⟨y, hyM⟩ := by rw [e2]
  set σ := φ ⟨y, hyM⟩ with hσdef
  set τ := φ ⟨r, hrM⟩ with hτdef
  have hστ : Commute σ τ := hcomm
  have hxs : Equiv.Perm.sign (σ * τ) = 1 := by rw [map_mul, hσs, hτs, mul_one]
  have hx6 : (σ * τ) ^ 6 = 1 := by
    rw [hστ.mul_pow, show σ ^ 6 = (σ ^ 3) ^ 2 by rw [← pow_mul],
      show τ ^ 6 = (τ ^ 2) ^ 3 by rw [← pow_mul], hσ3, hτ2, one_pow, one_pow, mul_one]
  rcases perm5_sq_or_cube_of_pow_six (σ * τ) hxs hx6 with hx2 | hx3
  · exfalso
    rw [hστ.mul_pow, hτ2, mul_one] at hx2
    have hσ' : σ = 1 := by
      calc σ = σ ^ 3 := by rw [show σ ^ 3 = σ * σ ^ 2 by group, hx2, mul_one]
        _ = 1 := hσ3
    exact hσ1 hσ'
  · have hτ1 : τ = 1 := by
      rw [hστ.mul_pow, hσ3, one_mul] at hx3
      calc τ = τ ^ 3 := by rw [show τ ^ 3 = τ ^ 2 * τ by group, hτ2, one_mul]
        _ = 1 := hx3
    exact (hmem ⟨r, hrM⟩).mp hτ1

theorem exists_y (h : KuHyp G T M H P z) :
    ∃ y : G, y ∈ oTwoUpper M ∧ y ∈ Subgroup.normalizer (kuV2 T M : Set G) ∧ orderOf y = 3 ∧
      y ∈ Subgroup.normalizer (kuR T M : Set G) ∧
      (∀ v ∈ kuV2 T M, y * v * y⁻¹ = v → v = 1) ∧
      (∀ v ∈ pCoreOf 2 M, y * v * y⁻¹ * v⁻¹ ∈ kuV2 T M → v ∈ kuV2 T M) ∧
      (∀ r ∈ kuR T M, y * r * y⁻¹ * r⁻¹ ∈ pCoreOf 2 M → r ∈ pCoreOf 2 M) := by
  obtain ⟨y, hyX, hy3⟩ := h.exists_order_three_X
  have hyL : y ∈ oTwoUpper M := hyX.1
  have hyN2 : y ∈ Subgroup.normalizer (kuV2 T M : Set G) := hyX.2
  have hK : ∀ v ∈ pCoreOf 2 M, y * v * y⁻¹ = v → v = 1 :=
    fun v hv hf => h.fpf_of_order_three hyL hy3 hv hf
  exact ⟨y, hyL, hyN2, hy3, h.normalizer_kuR_of_X hyX, fun v hv hf => hK v hv.1 hf,
    h.clause_f hyL hyN2 hK, h.clause_g hyL hy3⟩

theorem exists_z' (h : KuHyp G T M H P z) :
    ∃ z' ∈ kuV2 T M, z' ≠ 1 ∧ z' ≠ z ∧ ∃ y ∈ M, y * z * y⁻¹ = z' := by
  obtain ⟨y, hyL, hyN, -, -, hE, -, -⟩ := h.exists_y
  have hyM : y ∈ M := oTwoUpper_le M hyL
  have hzV2 : z ∈ kuV2 T M := h.z_mem_kuV2
  have hz' : y * z * y⁻¹ ∈ kuV2 T M := (Subgroup.mem_normalizer_iff.mp hyN z).mp hzV2
  have hne1 : y * z * y⁻¹ ≠ 1 := by
    intro e
    apply h.z_ne_one
    have h1 : y * z = y * 1 := by rw [mul_one]; exact mul_inv_eq_one.mp e
    exact mul_left_cancel h1
  have hnez : y * z * y⁻¹ ≠ z := by
    intro e
    exact h.z_ne_one (hE z hzV2 e)
  exact ⟨y * z * y⁻¹, hz', hne1, hnez, y, hyM, rfl⟩

end KuHyp

end CFSG.GH74.QTGen4.Ku
