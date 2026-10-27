module

public import CFSG.GH74.QTGen4.Recog.Ku.A4Y

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem orbit_conjL_of (h : KuHyp G T M H P z) {w : G} (hw : w ∈ pCoreOf 2 M) (hw1 : w ≠ 1) :
    MulAction.orbit (conjM (oTwoUpper M)) w = (pCoreOf 2 M : Set G) \ {1} := by
  ext v
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := MulAction.mem_orbit_iff.mp hv
    obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.mp c.2
    have hmc' : ConjAct.toConjAct m = (c : ConjAct G) := hmc
    have hact : c • w = m * w * m⁻¹ := by
      show (c : ConjAct G) • w = _
      rw [← hmc', ConjAct.toConjAct_smul]
    have hmN : m ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      h.oTwoUpper_le_normalizer_V hm
    refine ⟨?_, ?_⟩
    · rw [hact]
      exact (Subgroup.mem_normalizer_iff.mp hmN w).mp hw
    · intro hone
      rw [Set.mem_singleton_iff] at hone
      apply hw1
      have h1 : m * w * m⁻¹ = 1 := hact.symm.trans hone
      have h2 : m * w = m * 1 := by
        rw [mul_one]
        exact mul_inv_eq_one.mp h1
      exact mul_left_cancel h2
  · rintro ⟨hv, hv1⟩
    obtain ⟨g, hg, hgv⟩ :=
      IsNatModCh5.exists_conj_eq h.mNat hw hv hw1
        (fun e => hv1 (Set.mem_singleton_iff.mpr e))
    refine MulAction.mem_orbit_iff.mpr
      ⟨⟨ConjAct.toConjAct g, Subgroup.mem_map_of_mem _ hg⟩, ?_⟩
    show (ConjAct.toConjAct g : ConjAct G) • w = v
    rw [ConjAct.toConjAct_smul, hgv]

theorem card_L_inf_centralizer_of (h : KuHyp G T M H P z) {w : G} (hw : w ∈ pCoreOf 2 M)
    (hw1 : w ≠ 1) :
    Nat.card ↥(oTwoUpper M ⊓ Subgroup.centralizer ({w} : Set G)) = 64 := by
  have hcardS : Nat.card ↥(conjM (oTwoUpper M)) = 960 := by
    rw [conjM, Subgroup.card_map_of_injective
      (f := (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom)
      (ConjAct.toConjAct : G ≃* ConjAct G).injective]
    exact h.card_oTwoUpper
  have hV16 : ((pCoreOf 2 M : Subgroup G) : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact h.vCard
  have hidx : (MulAction.stabilizer (conjM (oTwoUpper M)) w).index = 15 := by
    rw [MulAction.index_stabilizer, orbit_conjL_of h hw hw1,
      Set.ncard_sdiff_singleton_of_mem
        (show (1 : G) ∈ (pCoreOf 2 M : Set G) from (pCoreOf 2 M).one_mem), hV16]
  have hL := Subgroup.card_mul_index (MulAction.stabilizer (conjM (oTwoUpper M)) w)
  rw [hidx, hcardS] at hL
  have hstab : Nat.card ↥(MulAction.stabilizer (conjM (oTwoUpper M)) w) = 64 := by omega
  have hf : Function.Injective (conjMVal (oTwoUpper M)) :=
    (ConjAct.toConjAct : G ≃* ConjAct G).symm.injective.comp Subtype.val_injective
  have hmap : (MulAction.stabilizer (conjM (oTwoUpper M)) w).map (conjMVal (oTwoUpper M)) =
      oTwoUpper M ⊓ Subgroup.centralizer ({w} : Set G) := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hcS : c • w = w := MulAction.mem_stabilizer_iff.mp hc
      obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.mp c.2
      have hmc' : ConjAct.toConjAct m = (c : ConjAct G) := hmc
      have hfc : conjMVal (oTwoUpper M) c = m := by
        show ConjAct.ofConjAct (c : ConjAct G) = m
        rw [← hmc', ConjAct.ofConjAct_toConjAct]
      rw [hfc]
      have hcS' : m * w * m⁻¹ = w := by
        have : c • w = m * w * m⁻¹ := by
          show (c : ConjAct G) • w = _
          rw [← hmc', ConjAct.toConjAct_smul]
        rw [← this]; exact hcS
      exact ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hcS')⟩
    · rintro ⟨hgL, hgC⟩
      have hcomm : g * w = w * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
      refine ⟨⟨ConjAct.toConjAct g, Subgroup.mem_map_of_mem _ hgL⟩, ?_, ?_⟩
      · show (ConjAct.toConjAct g : ConjAct G) • w = w
        rw [ConjAct.toConjAct_smul]
        exact mul_inv_eq_iff_eq_mul.mpr hcomm
      · show ConjAct.ofConjAct (ConjAct.toConjAct g) = g
        exact ConjAct.ofConjAct_toConjAct g
  have hcardMap : Nat.card ↥(oTwoUpper M ⊓ Subgroup.centralizer ({w} : Set G)) =
      Nat.card ↥(MulAction.stabilizer (conjM (oTwoUpper M)) w) := by
    rw [← hmap, Subgroup.card_map_of_injective hf]
  exact hcardMap.trans hstab

theorem L_inf_centralizer_eq_kuR (h : KuHyp G T M H P z) {w : G} (hw : w ∈ kuV2 T M)
    (hw1 : w ≠ 1) : oTwoUpper M ⊓ Subgroup.centralizer ({w} : Set G) = kuR T M := by
  have hle : kuR T M ≤ oTwoUpper M ⊓ Subgroup.centralizer ({w} : Set G) := by
    intro r hr
    exact ⟨hr.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hw.2 r hr)⟩
  exact (Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (by rw [h.card_kuR, h.card_L_inf_centralizer_of hw.1 hw1]))).symm

theorem conj_mem_kuR_of (h : KuHyp G T M H P z) {g w : G} (hg : g ∈ oTwoUpper M)
    (hw : w ∈ kuV2 T M) (hw1 : w ≠ 1) (hgz : g * z * g⁻¹ = w) {r : G}
    (hr : r ∈ kuR T M) : g * r * g⁻¹ ∈ kuR T M := by
  rw [← L_inf_centralizer_eq_kuR h hw hw1]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hr.2) (Subgroup.inv_mem _ hg), ?_⟩
  have hr' : r ∈ oTwoUpper M ⊓ Subgroup.centralizer ({z} : Set G) := by
    rw [← h.kuR_eq_L_inf_centralizer_z]; exact hr
  have hrz : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp hr'.2
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  rw [← hgz]
  calc g * r * g⁻¹ * (g * z * g⁻¹) = g * (r * z) * g⁻¹ := by group
    _ = g * (z * r) * g⁻¹ := by rw [hrz]
    _ = g * z * g⁻¹ * (g * r * g⁻¹) := by group

theorem conj_inv_mem_kuR_of (h : KuHyp G T M H P z) {g w : G} (hg : g ∈ oTwoUpper M)
    (hw : w ∈ kuV2 T M) (hw1 : w ≠ 1) (hgz : g * z * g⁻¹ = w) {r : G}
    (hr : r ∈ kuR T M) : g⁻¹ * r * g ∈ kuR T M := by
  let F : ↥(kuR T M) → ↥(kuR T M) := fun s =>
    ⟨g * (s : G) * g⁻¹, conj_mem_kuR_of h hg hw hw1 hgz s.2⟩
  have hinj : Function.Injective F := by
    intro s s' hss
    have h1 : g * (s : G) * g⁻¹ = g * (s' : G) * g⁻¹ := congrArg Subtype.val hss
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨s, hs⟩ := Finite.surjective_of_injective hinj ⟨r, hr⟩
  have hs' : g * (s : G) * g⁻¹ = r := congrArg Subtype.val hs
  rw [← hs']
  have e : g⁻¹ * (g * (s : G) * g⁻¹) * g = s := by group
  rw [e]
  exact s.2

theorem conj_mem_kuV2_core (h : KuHyp G T M H P z) {g : G} (hg : g ∈ oTwoUpper M)
    (hbwd : ∀ r ∈ kuR T M, g⁻¹ * r * g ∈ kuR T M) {v : G} (hv : v ∈ kuV2 T M) :
    g * v * g⁻¹ ∈ kuV2 T M := by
  refine ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (h.oTwoUpper_le_normalizer_V hg) v).mp hv.1
  · show g * v * g⁻¹ ∈ Subgroup.centralizer (kuR T M : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' := hbwd r hr
    have hc : (g⁻¹ * r * g) * v = v * (g⁻¹ * r * g) :=
      (Subgroup.mem_centralizer_iff.mp hv.2) _ hr'
    calc r * (g * v * g⁻¹) = g * (g⁻¹ * r * g) * v * g⁻¹ := by group
      _ = g * ((g⁻¹ * r * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * r * g)) * g⁻¹ := by rw [hc]
      _ = g * v * g⁻¹ * r := by group

theorem normalizer_kuV2_of_conj (h : KuHyp G T M H P z) {g w : G} (hg : g ∈ oTwoUpper M)
    (hw : w ∈ kuV2 T M) (hw1 : w ≠ 1) (hgz : g * z * g⁻¹ = w) :
    g ∈ Subgroup.normalizer (kuV2 T M : Set G) := by
  have hfwd : ∀ r ∈ kuR T M, g * r * g⁻¹ ∈ kuR T M :=
    fun r hr => conj_mem_kuR_of h hg hw hw1 hgz hr
  have hbwd : ∀ r ∈ kuR T M, g⁻¹ * r * g ∈ kuR T M :=
    fun r hr => conj_inv_mem_kuR_of h hg hw hw1 hgz hr
  have hfwd' : ∀ r ∈ kuR T M, g⁻¹⁻¹ * r * g⁻¹ ∈ kuR T M := fun r hr => by
    rw [inv_inv]; exact hfwd r hr
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact conj_mem_kuV2_core h hg hbwd hv
  · intro hv
    have key := conj_mem_kuV2_core h (Subgroup.inv_mem _ hg) hfwd' hv
    have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
    rw [e] at key
    exact key

end KuHyp

end CFSG.GH74.QTGen4.Ku
