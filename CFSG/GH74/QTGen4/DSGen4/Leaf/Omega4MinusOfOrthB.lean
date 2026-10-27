module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifySylow

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Pre

variable {G : Type} [Group G] [Finite G]

theorem omega_mem_pCore_iff {L : Subgroup G} (x : ↥L) :
    x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L := by
  unfold pCoreOf
  exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm

theorem omega_a5Pre_self {L : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hc : CharTwo L)
    (he : IsElemAbelian 2 (pCoreOf 2 L)) (h16 : Nat.card (pCoreOf 2 L) = 16) :
    A5Pre L L (pCoreOf 2 L) ⊥ := by
  have hQnorm : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (Subgroup.le_normalizer).trans (normalizer_le_normalizer_pCoreOf L)
  have hcomm : ∀ a ∈ pCoreOf 2 L, ∀ b ∈ pCoreOf 2 L, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (he.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm1 : ∀ a ∈ pCoreOf 2 L, ∀ b ∈ pCoreOf 2 L, ⁅a, b⁆ = 1 := fun a ha b hb =>
    commutatorElement_eq_one_iff_mul_comm.mpr (hcomm a ha b hb)
  refine ⟨le_rfl, Subgroup.le_normalizer, hQnorm, ?_, ⟨bot_le, ?_, ?_⟩, ?_, ?_, hq, ?_⟩
  · intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl; simp
    · intro hx
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, hx]; group
  · exact Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [Subgroup.mem_bot]; exact hcomm1 a ha b hb
  · exact fun e he' => by rw [Subgroup.mem_bot]; exact he.2 e he'
  · rw [Subgroup.relIndex_bot_left]; exact h16
  · exact fun q hq' e he' => by rw [Subgroup.mem_bot]; exact hcomm1 q hq' e he'
  · by_contra hcon
    push_neg at hcon
    have hLQ : L ≤ pCoreOf 2 L := by
      intro l hl
      apply hc
      refine ⟨hl, Subgroup.mem_centralizer_iff.mpr fun e he' => ?_⟩
      have h1 := hcon l hl e he'
      rw [Subgroup.mem_bot] at h1
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
    have h60 : Nat.card (oTwoQuot ↥L) = 60 := by
      rw [Nat.card_congr e.toEquiv]; exact CFSG.QuasithinUnique.A5.Delta5.a5_card
    have htop : CFSG.Open.pCore 2 ↥L = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact (omega_mem_pCore_iff x).mpr (hLQ x.2)
    have h1 : Nat.card (oTwoQuot ↥L) = 1 := by
      show Nat.card (↥L ⧸ CFSG.Open.pCore 2 ↥L) = 1
      rw [htop]
      exact Subgroup.index_top
    omega

theorem omega_blockU_eq_pCoreOf {L : Subgroup G} {H : Finset Certificates.A5GL42.Mat4}
    (hF : Certificates.A5GL42.Facts) (hH : Certificates.A5GL42.GroupFacts H)
    (h : A5Pre L L (pCoreOf 2 L) ⊥) (M : A5Model L L (pCoreOf 2 L) ⊥ H) :
    blockU L = pCoreOf 2 L := by
  have hle : blockU L ≤ pCoreOf 2 L :=
    Subgroup.commutator_le.mpr fun q hq l hl => ElemFrame.comm_right_mem h.norm_E hl hq
  have hLX : L ≤ Subgroup.normalizer (blockU L : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hQ : (pCoreOf 2 L).map (MulAut.conj g).toMonoidHom = pCoreOf 2 L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.norm_E hg)
    have hL : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.norm_L hg)
    show ⁅pCoreOf 2 L, L⁆.map (MulAut.conj g).toMonoidHom = ⁅pCoreOf 2 L, L⁆
    rw [Subgroup.map_commutator, hQ, hL]
  rcases M.eq_or_eq_of_normalizes hF hH h (X := blockU L) bot_le hle hLX with hb | hq
  · exfalso
    obtain ⟨l, hl, e, he, hne⟩ := h.nontriv
    apply hne
    rw [Subgroup.mem_bot]
    have h1 : ⁅e, l⁆ ∈ blockU L := Subgroup.commutator_mem_commutator he hl
    rw [hb, Subgroup.mem_bot] at h1
    rw [← commutatorElement_inv, h1, inv_one]
  · exact hq

end Pre

theorem omega_sl_center_eq_bot {K : Type} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hr1 : r = 1 := by
    have : (r - 1) ^ 2 = 0 := by linear_combination hr - r * h2 + h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linear_combination this
  subst hr1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one, ← hA']
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply]

theorem omega_exists_alpha {G : Type} [Group G] {K : Type} [Field K] [CharP K 2] {L : Subgroup G}
    (e : oTwoQuot ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :
    ∃ α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K,
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L := by
  let ι : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq (omega_sl_center_eq_bot (K := K))).trans QuotientGroup.quotientBot
  let α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K :=
    ι.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
  refine ⟨α, ?_, ?_⟩
  · intro s
    obtain ⟨x, rfl⟩ := ι.surjective s
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨l, rfl⟩
  · ext x
    simp only [MonoidHom.mem_ker, α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [map_eq_one_iff ι ι.injective, map_eq_one_iff e e.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]

end CFSG.GH74.QTGen4.DSGen4
