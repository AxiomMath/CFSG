module

public import CFSG.GH74.QTGen4.Recog.Ku.Defs
public import CFSG.GH74.QTGen4.Recog.Ku.Orders
public import CFSG.Quasithin.Vol2.Ch6NatMod

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem exists_odd_mem_M (h : KuHyp G T M H P z) : ∃ x ∈ M, x ≠ 1 ∧ Odd (orderOf x) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hd : 3 ∣ Nat.card ↥M := by
    rw [h.card_M]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  refine ⟨(x : G), x.2, ?_, ?_⟩
  · intro e
    rw [e, orderOf_one] at hxo
    norm_num at hxo
  · rw [hxo]
    decide

theorem conj_mem_pCore_of_mem_M (h : KuHyp G T M H P z) {g : G} (hg : g ∈ M) {x : G}
    (hx : x ∈ pCoreOf 2 M) : g * x * g⁻¹ ∈ pCoreOf 2 M := by
  have hgN : g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
    rw [← h.mNorm]; exact hg
  exact (Subgroup.mem_normalizer_iff.mp hgN x).mp hx

theorem conj_mem_oTwoUpper_of_mem_M (_h : KuHyp G T M H P z) {g : G} (hg : g ∈ M) {x : G}
    (hx : x ∈ oTwoUpper M) : g * x * g⁻¹ ∈ oTwoUpper M :=
  conj_mem_oTwoUpper (Subgroup.le_normalizer hg) hx

theorem pCore_le_oTwoUpper (h : KuHyp G T M H P z) : pCoreOf 2 M ≤ oTwoUpper M := by
  have hWL : oTwoUpper M ≤ Subgroup.normalizer ((pCoreOf 2 M ⊓ oTwoUpper M : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hlM : l ∈ M := oTwoUpper_le M hl
    constructor
    · rintro ⟨hxV, hxL⟩
      exact ⟨h.conj_mem_pCore_of_mem_M hlM hxV,
        conj_mem_oTwoUpper (Subgroup.le_normalizer hlM) hxL⟩
    · rintro ⟨hxV, hxL⟩
      have hl' : l⁻¹ ∈ M := M.inv_mem hlM
      have hxV' := h.conj_mem_pCore_of_mem_M hl' hxV
      have hxL' := conj_mem_oTwoUpper (Subgroup.le_normalizer hl') hxL
      have e1 : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
      rw [e1] at hxV' hxL'
      exact ⟨hxV', hxL'⟩
  rcases h.mNat.irreducible (pCoreOf 2 M ⊓ oTwoUpper M) inf_le_left hWL with hbot | htop
  · exfalso
    obtain ⟨x, hxM, hx1, hxo⟩ := h.exists_odd_mem_M
    have hxL : x ∈ oTwoUpper M := mem_oTwoUpper_of_odd hxM hxo
    have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hc : x * v * x⁻¹ * v⁻¹ ∈ pCoreOf 2 M ⊓ oTwoUpper M := by
        constructor
        · exact (pCoreOf 2 M).mul_mem
            (h.conj_mem_pCore_of_mem_M hxM hv) ((pCoreOf 2 M).inv_mem hv)
        · have e : x * v * x⁻¹ * v⁻¹ = x * (v * x⁻¹ * v⁻¹) := by group
          rw [e]
          refine (oTwoUpper M).mul_mem hxL ?_
          have hvM : v ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hv
          exact conj_mem_oTwoUpper_of_mem_M h hvM ((oTwoUpper M).inv_mem hxL)
      rw [hbot, Subgroup.mem_bot] at hc
      have hc' : x * v * x⁻¹ = v := mul_inv_eq_one.mp hc
      exact (mul_inv_eq_iff_eq_mul.mp hc').symm
    have hxV : x ∈ pCoreOf 2 M := by
      have : x ∈ M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) := ⟨hxM, hxC⟩
      rw [h.mCent] at this
      exact this
    have hxbot : x ∈ pCoreOf 2 M ⊓ oTwoUpper M := ⟨hxV, hxL⟩
    rw [hbot, Subgroup.mem_bot] at hxbot
    exact hx1 hxbot
  · exact inf_eq_left.mp htop

theorem oTwoUpper_le_map_comap {X : Subgroup G} (φ : ↥X →* Equiv.Perm (Fin 5)) :
    oTwoUpper X ≤ ((alternatingGroup (Fin 5)).comap φ).map X.subtype := by
  unfold oTwoUpper
  rw [Subgroup.closure_le]
  rintro x ⟨hxX, hodd⟩
  refine Subgroup.mem_map.mpr ⟨⟨x, hxX⟩, ?_, rfl⟩
  show φ ⟨x, hxX⟩ ∈ alternatingGroup (Fin 5)
  rw [Equiv.Perm.mem_alternatingGroup]
  have h2 : orderOf (⟨x, hxX⟩ : ↥X) = orderOf x := (Subgroup.orderOf_coe _).symm
  have hodd2 : Odd (orderOf (⟨x, hxX⟩ : ↥X)) := by rw [h2]; exact hodd
  have hodd' : Odd (orderOf (φ ⟨x, hxX⟩)) := Odd.of_dvd_nat hodd2 (orderOf_map_dvd φ _)
  have hs := congrArg Equiv.Perm.sign (pow_orderOf_eq_one (φ ⟨x, hxX⟩))
  rw [map_pow, map_one] at hs
  rcases Int.units_eq_one_or (Equiv.Perm.sign (φ ⟨x, hxX⟩)) with h1 | h1
  · exact h1
  · rw [h1, Odd.neg_one_pow hodd'] at hs
    exact absurd hs (by decide)

theorem alt_le_map_subgroupOf (h : KuHyp G T M H P z) {φ : ↥M →* Equiv.Perm (Fin 5)}
    (hφ : Function.Surjective φ) :
    alternatingGroup (Fin 5) ≤ ((oTwoUpper M).subgroupOf M).map φ := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  obtain ⟨m, hm⟩ := hφ σ
  have hm1920 : m ^ 1920 = 1 := by
    have hd := orderOf_dvd_natCard m
    rw [h.card_M] at hd
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  have hg15 : (m ^ 256) ^ 15 = 1 := by
    rw [← pow_mul, (by norm_num : (256:ℕ) * 15 = 1920 * 2), pow_mul, hm1920, one_pow]
  have hodd : Odd (orderOf (m ^ 256)) :=
    Odd.of_dvd_nat ⟨7, by norm_num⟩ (orderOf_dvd_of_pow_eq_one hg15)
  have hx : ((m ^ 256 : ↥M) : G) ∈ oTwoUpper M :=
    mem_oTwoUpper_of_odd (m ^ 256).2 (by rw [Subgroup.orderOf_coe]; exact hodd)
  have hφg : φ (m ^ 256) = σ := by
    rw [map_pow, hm]
    have hpm := pow_mod_orderOf σ 256
    rw [Equiv.Perm.IsThreeCycle.orderOf hσ, (by norm_num : (256:ℕ) % 3 = 1), pow_one] at hpm
    exact hpm.symm
  exact Subgroup.mem_map.mpr ⟨m ^ 256, Subgroup.mem_subgroupOf.mpr hx, hφg⟩

theorem card_alt_fin5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [h120] at h2
  omega

theorem card_oTwoUpper (h : KuHyp G T M H P z) : Nat.card (oTwoUpper M) = 960 := by
  obtain ⟨φ, hφs, hker⟩ := h.mQuot
  have hVM : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hLM : oTwoUpper M ≤ M := oTwoUpper_le M
  have hmap : ((oTwoUpper M).subgroupOf M).map φ = alternatingGroup (Fin 5) := by
    apply le_antisymm
    · intro σ hσ
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hσ
      obtain ⟨y, hy, hyx⟩ :=
        Subgroup.mem_map.mp (oTwoUpper_le_map_comap φ (Subgroup.mem_subgroupOf.mp hx))
      have hxy : y = x := Subtype.ext hyx
      rw [← hxy]
      exact hy
    · exact alt_le_map_subgroupOf h hφs
  have hLcard : Nat.card ((oTwoUpper M).subgroupOf M) = Nat.card (oTwoUpper M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  have hsub : φ.ker ≤ (oTwoUpper M).subgroupOf M := by
    rw [hker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact h.pCore_le_oTwoUpper hx
  have hker16 : Nat.card φ.ker = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVM).toEquiv, h.vCard]
  have hmain := Subgroup.relIndex_mul_card (H := φ.ker) (K := (oTwoUpper M).subgroupOf M)
  rw [inf_eq_left.mpr hsub, Subgroup.relIndex_ker, hmap, card_alt_fin5, hker16] at hmain
  omega

theorem relIndex_oTwoUpper (h : KuHyp G T M H P z) : (oTwoUpper M).relIndex M = 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := oTwoUpper M) (K := M)
  rw [inf_eq_left.mpr (oTwoUpper_le M), h.card_M, h.card_oTwoUpper] at h1
  omega

theorem M_le_normalizer_oTwoUpper (h : KuHyp G T M H P z) :
    M ≤ Subgroup.normalizer (oTwoUpper M : Set G) :=
  le_normalizer_oTwoUpper M

theorem pCore_le_kuR (h : KuHyp G T M H P z) : pCoreOf 2 M ≤ kuR T M :=
  le_inf h.pCore_le_T h.pCore_le_oTwoUpper

theorem T_le_normalizer_kuR (h : KuHyp G T M H P z) :
    T ≤ Subgroup.normalizer (kuR T M : Set G) := by
  intro t ht
  have htM : t ∈ M := h.tM ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxT, hxL⟩
    exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht),
      conj_mem_oTwoUpper_of_mem_M h htM hxL⟩
  · rintro ⟨hxT, hxL⟩
    have e1 : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    have htM' : t⁻¹ ∈ M := M.inv_mem htM
    have hxT' := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) (T.inv_mem (T.inv_mem ht))
    have hxL' := conj_mem_oTwoUpper_of_mem_M h htM' hxL
    rw [e1] at hxT' hxL'
    exact ⟨hxT', hxL'⟩

theorem relIndex_kuR (h : KuHyp G T M H P z) : (kuR T M).relIndex T = 2 := by
  have hLM : oTwoUpper M ≤ M := oTwoUpper_le M
  have hTM : T ≤ M := h.tM
  haveI hN : ((oTwoUpper M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hLM).mpr
      (fun g x hx hg => conj_mem_oTwoUpper_of_mem_M h hg hx)
  have h1 := Subgroup.relIndex_subgroupOf (H := oTwoUpper M) (K := T) hTM
  have h2 := Subgroup.relIndex_dvd_index_of_normal
    (H := (oTwoUpper M).subgroupOf M) (K := T.subgroupOf M)
  rw [h1] at h2
  have hdiv : (oTwoUpper M).relIndex T ∣ 2 := by
    rw [← h.relIndex_oTwoUpper]
    exact h2
  have hne : (oTwoUpper M).relIndex T ≠ 1 := by
    intro h3
    rw [Subgroup.relIndex_eq_one] at h3
    have hd := Subgroup.card_dvd_of_le h3
    rw [h.card_T, h.card_oTwoUpper] at hd
    norm_num at hd
  have hL : (oTwoUpper M).relIndex T = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h4 | h4
    · exact absurd h4 hne
    · exact h4
  have hT := (Subgroup.inf_relIndex_left (H := T) (K := oTwoUpper M)).trans hL
  exact hT

theorem card_kuR (h : KuHyp G T M H P z) : Nat.card (kuR T M) = 64 := by
  have h1 := Subgroup.relIndex_mul_card (H := kuR T M) (K := T)
  have hi : kuR T M ⊓ T = kuR T M := inf_eq_left.mpr inf_le_left
  rw [hi, h.relIndex_kuR, h.card_T] at h1
  omega

theorem z_mem_kuV2 (h : KuHyp G T M H P z) : z ∈ kuV2 T M := by
  refine ⟨h.z_mem_pCoreOf, ?_⟩
  show z ∈ Subgroup.centralizer (kuR T M : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  obtain ⟨hrT, -⟩ := (show r ∈ kuR T M from hr)
  have hrH : r ∈ H := h.tH hrT
  rw [h.hCz, Subgroup.mem_centralizer_iff] at hrH
  exact (hrH z (Set.mem_singleton z)).symm

theorem conj_mem_kuV2_of_mem_T (h : KuHyp G T M H P z) {t : G} (ht : t ∈ T) {x : G}
    (hx : x ∈ kuV2 T M) : t * x * t⁻¹ ∈ kuV2 T M := by
  obtain ⟨hxV, hxC⟩ := hx
  have hxC' : x ∈ Subgroup.centralizer (kuR T M : Set G) := hxC
  refine ⟨conj_mem_pCore_of_mem_M h (h.tM ht) hxV, ?_⟩
  show t * x * t⁻¹ ∈ Subgroup.centralizer (kuR T M : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hr' : t⁻¹ * r * t⁻¹⁻¹ ∈ kuR T M :=
    (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer_kuR (T.inv_mem ht)) r).mp hr
  have key := Subgroup.mem_centralizer_iff.mp hxC' _ hr'
  calc r * (t * x * t⁻¹) = t * ((t⁻¹ * r * t⁻¹⁻¹) * x) * t⁻¹ := by group
    _ = t * (x * (t⁻¹ * r * t⁻¹⁻¹)) * t⁻¹ := by rw [key]
    _ = t * x * t⁻¹ * r := by group

theorem T_le_normalizer_kuV2 (h : KuHyp G T M H P z) :
    T ≤ Subgroup.normalizer (kuV2 T M : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_kuV2_of_mem_T h ht hx
  · intro hx
    have e1 : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    have := conj_mem_kuV2_of_mem_T h (T.inv_mem ht) hx
    rw [e1] at this
    exact this

end KuHyp

end CFSG.GH74.QTGen4.Ku
