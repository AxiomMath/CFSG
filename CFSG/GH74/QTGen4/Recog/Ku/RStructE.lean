module

public import CFSG.GH74.QTGen4.Recog.Ku.RStructF
public import CFSG.GH74.QTGen4.Recog.Ku.A4YD

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem commutator_mem_kuV2 (h : KuHyp G T M H P z) {r s : G} (hr : r ∈ kuR T M)
    (hs : s ∈ kuR T M) : r * s * r⁻¹ * s⁻¹ ∈ kuV2 T M := by
  obtain ⟨y, hyL, -, hy3, hyR, hK, -, hcl⟩ := h.exists_y
  have hyV : y ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := h.oTwoUpper_le_normalizer_V hyL
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  obtain ⟨w0, hw0, hfix⟩ := h.exists_fixed_vec
  obtain ⟨a, hA⟩ := h.conj_y_eq_smul hw0 hfix hyR hyV
  have ha0 : a ≠ 0 := h.a_ne_zero hw0 hyL hyV hA
  have ha1 : a ≠ 1 := h.a_ne_one hw0 hfix hyL hyV hK hA
  have : ((pCoreOf 2 M).subgroupOf (kuR T M)).Normal := h.V_subgroupOf_normal
  have hlB : ∀ x x' y' : ↥(kuR T M),
      Bq h w0 (x * x') y' = Bq h w0 x y' + Bq h w0 x' y' := fun x x' y' => by
    rw [Bq_def, Bq_def, Bq_def]
    exact Bf_mul_left h hfix x.2 x'.2 y'.2
  have hrB : ∀ x y' y'' : ↥(kuR T M),
      Bq h w0 x (y' * y'') = Bq h w0 x y' + Bq h w0 x y'' := fun x y' y'' => by
    rw [Bq_def, Bq_def, Bq_def]
    exact Bf_mul_right h hfix x.2 y'.2 y''.2
  have hVlB : ∀ v ∈ (pCoreOf 2 M).subgroupOf (kuR T M), ∀ y' : ↥(kuR T M),
      Bq h w0 v y' = 0 := fun v hv y' => by
    rw [Bq_def]
    exact Bf_V_left h hw0 hfix ⟨v.1, Subgroup.mem_subgroupOf.mp hv⟩ y'.2
  have hVrB : ∀ v ∈ (pCoreOf 2 M).subgroupOf (kuR T M), ∀ x : ↥(kuR T M),
      Bq h w0 x v = 0 := fun v hv x => by
    rw [Bq_def]
    exact Bf_V_right h hw0 hfix x.2 ⟨v.1, Subgroup.mem_subgroupOf.mp hv⟩
  obtain ⟨B', hB'⟩ := descend_form ((pCoreOf 2 M).subgroupOf (kuR T M)) (Bq h w0)
    hlB hrB hVlB hVrB
  have hl' : ∀ x x' y' : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M),
      B' (x * x') y' = B' x y' + B' x' y' := by
    intro x x' y'
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨p', rfl⟩ := QuotientGroup.mk_surjective x'
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y'
    rw [← QuotientGroup.mk_mul]
    simp only [hB']
    exact hlB p p' q
  have hr' : ∀ x y' y'' : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M),
      B' x (y' * y'') = B' x y' + B' x y'' := by
    intro x y' y''
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y'
    obtain ⟨q', rfl⟩ := QuotientGroup.mk_surjective y''
    rw [← QuotientGroup.mk_mul]
    simp only [hB']
    exact hrB p q q'
  have halt : ∀ x : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M), B' x x = 0 := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hB', Bq_def]
    exact Bf_self h w0 p.2
  have hcomm : ∀ x y' : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M), x * y' = y' * x := by
    intro x y'
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y'
    exact h.quot_comm_kuR p q
  have hB : ∀ x y' : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M),
      B' (h.Nq hyL hyR x) (h.Nq hyL hyR y') = a⁻¹ * B' x y' := by
    intro x y'
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y'
    rw [Nq_mk, Nq_mk, hB', hB', Bq_conj h hyL hyR hyV ha0 hA p q]
  have hμ : a⁻¹ ≠ 1 := by
    intro e
    apply ha1
    rw [← inv_inv a, e, inv_one]
  have hN3 : ∀ x : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M),
      h.Nq hyL hyR (h.Nq hyL hyR (h.Nq hyL hyR x)) = x :=
    fun x => h.Nq_pow3 hyL hyR hy3' x
  have hfixN : ∀ x : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M),
      h.Nq hyL hyR x = x → x = 1 :=
    fun x hx => h.Nq_fix hyL hyR hcl x hx
  have hcard : Nat.card (↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) = 4 :=
    h.card_quot_kuR
  have hcov : ∀ x : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M), x ≠ 1 →
      ∀ y' : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M),
        y' = 1 ∨ y' = x ∨ y' = h.Nq hyL hyR x ∨ y' = h.Nq hyL hyR (h.Nq hyL hyR x) :=
    fun x hx => cover_of_card (h.Nq hyL hyR) hN3 hfixN hcard x hx
  have hzero := alt_zero_of_order3 hcomm B' hl' hr' halt (h.Nq hyL hyR) a⁻¹ hμ hB hN3 hfixN hcov
  have key := hzero (QuotientGroup.mk (⟨r, hr⟩ : ↥(kuR T M)))
    (QuotientGroup.mk (⟨s, hs⟩ : ↥(kuR T M)))
  rw [hB'] at key
  have hdet : detw w0 (Multiplicative.toAdd
      (h.mNat.data.E ⟨r * s * r⁻¹ * s⁻¹, h.comm_mem_pCore hr hs⟩)) = 0 :=
    (Bq_eq_detw h w0 hr hs).symm.trans key
  exact (h.mem_kuV2_iff_detw hw0 hfix ⟨r * s * r⁻¹ * s⁻¹, h.comm_mem_pCore hr hs⟩).mpr hdet

end KuHyp

end CFSG.GH74.QTGen4.Ku
