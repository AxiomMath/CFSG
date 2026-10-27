module

public import CFSG.GH74.QTGen4.Recog.Ku.A4YB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

omit [Finite G] in
theorem card_stab_conjM (K : Subgroup G) (w : G) :
    Nat.card ↥(MulAction.stabilizer (conjM K) w) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({w} : Set G)) := by
  have hf : Function.Injective (conjMVal K) :=
    (ConjAct.toConjAct : G ≃* ConjAct G).symm.injective.comp Subtype.val_injective
  have hmap : (MulAction.stabilizer (conjM K) w).map (conjMVal K) =
      K ⊓ Subgroup.centralizer ({w} : Set G) := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hcS : c • w = w := MulAction.mem_stabilizer_iff.mp hc
      obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.mp c.2
      have hmc' : ConjAct.toConjAct m = (c : ConjAct G) := hmc
      have hfc : conjMVal K c = m := by
        show ConjAct.ofConjAct (c : ConjAct G) = m
        rw [← hmc', ConjAct.ofConjAct_toConjAct]
      rw [hfc]
      have hcS' : m * w * m⁻¹ = w := by
        have : c • w = m * w * m⁻¹ := by
          show (c : ConjAct G) • w = _
          rw [← hmc', ConjAct.toConjAct_smul]
        rw [← this]; exact hcS
      exact ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hcS')⟩
    · rintro ⟨hgK, hgC⟩
      have hcomm : g * w = w * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
      refine ⟨⟨ConjAct.toConjAct g, Subgroup.mem_map_of_mem _ hgK⟩, ?_, ?_⟩
      · show (ConjAct.toConjAct g : ConjAct G) • w = w
        rw [ConjAct.toConjAct_smul]
        exact mul_inv_eq_iff_eq_mul.mpr hcomm
      · show ConjAct.ofConjAct (ConjAct.toConjAct g) = g
        exact ConjAct.ofConjAct_toConjAct g
  rw [← hmap, Subgroup.card_map_of_injective hf]

theorem orbit_conjX (h : KuHyp G T M H P z) :
    MulAction.orbit (conjM (oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G))) z =
      (kuV2 T M : Set G) \ {1} := by
  ext v
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := MulAction.mem_orbit_iff.mp hv
    obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.mp c.2
    have hmc' : ConjAct.toConjAct m = (c : ConjAct G) := hmc
    have hact : c • z = m * z * m⁻¹ := by
      show (c : ConjAct G) • z = _
      rw [← hmc', ConjAct.toConjAct_smul]
    have hmN : m ∈ Subgroup.normalizer (kuV2 T M : Set G) := hm.2
    refine ⟨?_, ?_⟩
    · rw [hact]
      exact (Subgroup.mem_normalizer_iff.mp hmN z).mp h.z_mem_kuV2
    · intro hone
      rw [Set.mem_singleton_iff] at hone
      apply h.z_ne_one
      have h1 : m * z * m⁻¹ = 1 := hact.symm.trans hone
      have h2 : m * z = m * 1 := by
        rw [mul_one]
        exact mul_inv_eq_one.mp h1
      exact mul_left_cancel h2
  · rintro ⟨hv, hv1⟩
    have hv1' : v ≠ 1 := fun e => hv1 (Set.mem_singleton_iff.mpr e)
    have hvL : v ∈ MulAction.orbit (conjM (oTwoUpper M)) z := by
      rw [h.orbit_conjL]
      exact ⟨hv.1, hv1⟩
    obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.mp hvL
    obtain ⟨g, hg, hgc⟩ := Subgroup.mem_map.mp c.2
    have hgc' : ConjAct.toConjAct g = (c : ConjAct G) := hgc
    have hgz : g * z * g⁻¹ = v := by
      have : c • z = g * z * g⁻¹ := by
        show (c : ConjAct G) • z = _
        rw [← hgc', ConjAct.toConjAct_smul]
      rw [← this]; exact hc
    have hgX : g ∈ oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G) :=
      ⟨hg, h.normalizer_kuV2_of_conj hg hv hv1' hgz⟩
    refine MulAction.mem_orbit_iff.mpr
      ⟨⟨ConjAct.toConjAct g, Subgroup.mem_map_of_mem _ hgX⟩, ?_⟩
    show (ConjAct.toConjAct g : ConjAct G) • z = v
    rw [ConjAct.toConjAct_smul, hgz]

theorem card_L_inf_normalizer_kuV2 (h : KuHyp G T M H P z) :
    Nat.card ↥(oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) = 192 := by
  have hcardX : Nat.card ↥(conjM (oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G))) =
      Nat.card ↥(oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) := by
    rw [conjM, Subgroup.card_map_of_injective
      (f := (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom)
      (ConjAct.toConjAct : G ≃* ConjAct G).injective]
  have hV4 : ((kuV2 T M : Subgroup G) : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_kuV2
  have hidx : (MulAction.stabilizer
      (conjM (oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G))) z).index = 3 := by
    rw [MulAction.index_stabilizer, orbit_conjX h,
      Set.ncard_sdiff_singleton_of_mem
        (show (1 : G) ∈ (kuV2 T M : Set G) from (kuV2 T M).one_mem), hV4]
  have hL := Subgroup.card_mul_index (MulAction.stabilizer
    (conjM (oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G))) z)
  rw [hidx, hcardX] at hL
  have hXC : (oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) ⊓
      Subgroup.centralizer ({z} : Set G) =
        oTwoUpper M ⊓ Subgroup.centralizer ({z} : Set G) := by
    apply le_antisymm
    · intro g hg
      exact ⟨hg.1.1, hg.2⟩
    · intro g hg
      have hcomm : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg.2
      exact ⟨⟨hg.1, h.normalizer_kuV2_of_conj hg.1 h.z_mem_kuV2 h.z_ne_one
        (mul_inv_eq_iff_eq_mul.mpr hcomm)⟩, hg.2⟩
  have hstab : Nat.card ↥(MulAction.stabilizer
      (conjM (oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G))) z) = 64 := by
    rw [card_stab_conjM, hXC, h.card_L_inf_centralizer_z]
  rw [hstab] at hL
  omega

theorem card_M_inf_normalizer_kuV2 (h : KuHyp G T M H P z) :
    Nat.card ↥(M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) = 384 := by
  obtain ⟨t, htT, htL⟩ : ∃ t ∈ T, t ∉ oTwoUpper M := by
    by_contra hcon
    push Not at hcon
    have e : kuR T M = T := inf_eq_left.mpr (fun t ht => hcon t ht)
    have hc := h.card_kuR
    rw [e, h.card_T] at hc
    omega
  have htM : t ∈ M := h.tM htT
  have htY : t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G) :=
    ⟨htM, h.T_le_normalizer_kuV2 htT⟩
  obtain ⟨a0, ha0M, ha0⟩ := Subgroup.relIndex_eq_two_iff.mp h.relIndex_oTwoUpper
  have ha0L : a0 ∉ oTwoUpper M := by
    intro hm
    have h1 := xor_iff_iff_not.mp (ha0 1 M.one_mem)
    rw [one_mul] at h1
    exact (h1.mp hm) ((oTwoUpper M).one_mem)
  have hta : t * a0 ∈ oTwoUpper M := (xor_iff_iff_not.mp (ha0 t htM)).mpr htL
  have haa : a0 * a0 ∈ oTwoUpper M := (xor_iff_iff_not.mp (ha0 a0 ha0M)).mpr ha0L
  have hconj : a0⁻¹ * (t * a0) * a0⁻¹⁻¹ ∈ oTwoUpper M :=
    (Subgroup.mem_normalizer_iff.mp
      (h.M_le_normalizer_oTwoUpper (Subgroup.inv_mem _ ha0M)) (t * a0)).mp hta
  have hsq : a0⁻¹ * a0⁻¹ ∈ oTwoUpper M := by
    have := Subgroup.inv_mem _ haa
    rwa [mul_inv_rev] at this
  have key1 : a0⁻¹ * t ∈ oTwoUpper M := by
    have e : a0⁻¹ * t = (a0⁻¹ * (t * a0) * a0⁻¹⁻¹) * (a0⁻¹ * a0⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hconj hsq
  have hcos : ∀ b ∈ M, b ∈ oTwoUpper M ↔ b * t ∉ oTwoUpper M := by
    intro b hbM
    by_cases hb : b ∈ oTwoUpper M
    · refine ⟨fun _ hbt => htL ?_, fun _ => hb⟩
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) hbt
      simpa using this
    · have hba : b * a0 ∈ oTwoUpper M := (xor_iff_iff_not.mp (ha0 b hbM)).mpr hb
      have hbt : b * t ∈ oTwoUpper M := by
        have e : b * t = (b * a0) * (a0⁻¹ * t) := by group
        rw [e]
        exact Subgroup.mul_mem _ hba key1
      exact ⟨fun h' => absurd h' hb, fun h' => absurd hbt h'⟩
  have hXle : oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G) ≤
      M ⊓ Subgroup.normalizer (kuV2 T M : Set G) :=
    fun g hg => ⟨oTwoUpper_le M hg.1, hg.2⟩
  have hrel : (oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G)).relIndex
      (M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨t, htY, fun b hb => ?_⟩
    have hbM : b ∈ M := hb.1
    have hbt : b * t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G) :=
      Subgroup.mul_mem _ hb htY
    have hX : ∀ g ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G),
        g ∈ oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G) ↔ g ∈ oTwoUpper M :=
      fun g hg => ⟨fun hx => hx.1, fun hgL => ⟨hgL, hg.2⟩⟩
    rw [hX _ hbt, hX _ hb]
    exact xor_iff_iff_not.mpr (by have := hcos b hbM; tauto)
  have hm : (oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G)).relIndex
      (M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) *
        Nat.card ↥((oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) ⊓
          (M ⊓ Subgroup.normalizer (kuV2 T M : Set G))) =
      Nat.card ↥(M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) :=
    Subgroup.relIndex_mul_card _ _
  rw [hrel, inf_eq_left.mpr hXle, card_L_inf_normalizer_kuV2 h] at hm
  omega

end KuHyp

end CFSG.GH74.QTGen4.Ku
