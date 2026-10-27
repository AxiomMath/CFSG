module

public import CFSG.CGT.PushingUpLit.A78T2.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78T2

open CFSG.Assembly CFSG.ABGLocalTools
open CFSG.CGT.PushingUpLit.A78Sp4 (cj ElemAb2 mul_mem_cj mem_normalizer_of_cj elemAb2_cj card_cj
  cj_mono cj_sup_eq pCoreOf_le_of_isSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L L₂ V V₂ Z J T S M M₂ : Subgroup G} {e : ℕ}

theorem T2Base.V_ne (h : T2Base G V V₂ Z J T S M M₂ e) : V ≠ V₂ := by
  intro hVV
  apply h.not_V_le_Z
  rw [← h.inf, hVV, inf_idem]

theorem T2Base.mem_normalizer_J_of_le (h : T2Base G V V₂ Z J T S M M₂ e) {Q : Subgroup G}
    (hQS : Q ≤ S) (hJQ : J ≤ Q) {n : G} (hn : ∀ q ∈ Q, n * q * n⁻¹ ∈ Q) :
    n ∈ Subgroup.normalizer (J : Set G) := by
  have hcjQ : cj n Q ≤ Q := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact hn y hy
  have hcV : ∀ U : Subgroup G, ElemAb2 U → Nat.card U = 2 ^ (2 * e) → U ≤ Q →
      cj n U = V ∨ cj n U = V₂ := fun U hU hUc hUQ =>
    h.A_S _ (((cj_mono n hUQ).trans hcjQ).trans hQS) (elemAb2_cj hU n) ((card_cj n U).trans hUc)
  have h1 := hcV V h.elem_V h.card_V (h.V_le_J.trans hJQ)
  have h2 := hcV V₂ h.elem_V₂ h.card_V₂ (h.V₂_le_J.trans hJQ)
  have hne : cj n V ≠ cj n V₂ := fun heq =>
    h.V_ne (Subgroup.map_injective (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective heq)
  have hJ : cj n J = J := by
    rw [← h.sup, cj_sup_eq]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
    · exact absurd (h1.trans h2.symm) hne
  exact mem_normalizer_of_cj hJ

theorem T2Loc.J_le_O2 (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) :
    J ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Z : Set G)) := by
  obtain ⟨a, b, c, hH, hT⟩ := h.coords
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (Z : Set G) with hN
  set Q := CFSG.Open.pCoreOf 2 N with hQ
  have hSN : S ≤ N := h.base.S_le_normalizer_Z
  have hQS : Q ≤ S := pCoreOf_le_of_isSylowOf (h.base.sylow.of_le hSN le_top)
  have hQn : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q := fun n hn q hq =>
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N hn) q).1 hq
  have hZp : IsPGroup 2 Z :=
    (CFSG.CGT.PushingUpLit.A78Sp4.ElemAb2.mono h.base.elem_V h.base.Z_le_V).isPGroup
  have hZQ : Z ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hZp
  have hZne : Z ≠ ⊥ := by
    obtain ⟨z, hz, hz1⟩ := h.base.exists_ne_one_Z
    exact fun hbot => hz1 (Subgroup.mem_bot.1 (hbot ▸ hz))
  have hcent : ∀ n ∈ N, (∀ q ∈ Q, n * q = q * n) → n ∈ Q := fun n hn hnq =>
    h.charTwo N ⟨Z, hZne, hZp, rfl⟩
      ⟨hn, Subgroup.mem_centralizer_iff.2 fun q hq => (hnq q hq).symm⟩
  have hJS := h.base.J_le_S
  have hcomm : ∀ q ∈ Q, ∀ j ∈ J, ⁅q, j⁆ ∈ Q ⊓ J := by
    intro q hq j hj
    refine ⟨?_, ?_⟩
    · have h1 := hQn j (hSN (hJS hj)) q⁻¹ (Q.inv_mem hq)
      have : ⁅q, j⁆ = q * (j * q⁻¹ * j⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact Q.mul_mem hq h1
    · have : ⁅q, j⁆ = (q * j * q⁻¹) * j⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact J.mul_mem (h.base.conj_J (hQS hq) hj) (J.inv_mem hj)
  have hJp : IsPGroup 2 J := h.base.isPGroup_S.to_le hJS
  obtain ⟨z₀, hz₀, hz₀1⟩ := h.base.exists_ne_one_Z
  rcases h.torus_cases hH hT (W := Q ⊓ J) (le_inf hZQ h.base.Z_le_J) inf_le_right
      (fun x hxJ hxZ w hw => ⟨hQn x (mem_normalizer_of_conj_mem hxZ) w hw.1, hxJ w hw.2⟩) with
    hW | hW | hW | hW
  ·
    exfalso
    have hQJ : Q ≤ J := fun q hq => h.base.cent_S q (hQS hq) fun j hj => by
      rw [← hW]; exact hcomm q hq j hj
    have hQZ : Q ≤ Z := fun q hq => by rw [← hW]; exact ⟨hq, hQJ hq⟩
    have hJQ : J ≤ Q := fun j hj => hcent j (hSN (hJS hj)) fun q hq =>
      (hH.central h.base.inf h.base.Z_le_J h.base.comm_mem (hQZ hq) hj).symm
    exact h.base.not_V_le_Z ((h.base.V_le_J.trans hJQ).trans hQZ)
  ·
    exfalso
    have hVQ : V ≤ Q := fun v hv => by
      have : v ∈ Q ⊓ J := by rw [hW]; exact hv
      exact this.1
    have hQT : Q ≤ T := by
      intro q hq
      have hqM : q ∈ M := by
        rw [h.side₁.M_eq]
        refine mem_normalizer_of_conj_mem fun v hv => ?_
        have h1 : q * v * q⁻¹ ∈ Q ⊓ J :=
          ⟨Q.mul_mem (Q.mul_mem hq (hVQ hv)) (Q.inv_mem hq),
            h.base.conj_J (hQS hq) (h.base.V_le_J hv)⟩
        rw [hW] at h1
        exact h1
      rw [← h.base.S_inf_M]
      exact ⟨hQS hq, hqM⟩
    have hQJ : Q ≤ J := by
      intro q hq
      by_contra hqJ
      obtain ⟨-, v, hv, hv'⟩ := h.field.fixZ q (hQT hq) hqJ
      apply hv'
      have h1 := hcomm q hq v (h.base.V₂_le_J hv)
      rw [hW] at h1
      have h2 : ⁅q, v⁆ ∈ V₂ := by
        have : ⁅q, v⁆ = (q * v * q⁻¹) * v⁻¹ := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        refine V₂.mul_mem ?_ (V₂.inv_mem hv)
        rw [← (h.base.T_norm q (hQT hq)).2]
        exact mul_mem_cj q hv
      rw [← h.base.inf]
      exact ⟨h1, h2⟩
    have hQV : Q ≤ V := fun q hq => by
      have : q ∈ Q ⊓ J := ⟨hq, hQJ hq⟩
      rw [hW] at this
      exact this
    have hNM : N ≤ M := fun n hn => by
      rw [h.side₁.M_eq]
      exact mem_normalizer_of_conj_mem fun v hv => hQV (hQn n hn v (hVQ hv))
    have hNJ : N ≤ Subgroup.normalizer (J : Set G) := fun n hn =>
      h.side₁.mem_normalizer_J hz₀ hz₀1 (hNM hn) hn
    have hJQ : J ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (fun j hj => hSN (hJS hj)) hNJ hJp
    apply h.base.not_V₂_le_Z
    intro v hv
    rw [← h.base.inf]
    exact ⟨hQV (hJQ (h.base.V₂_le_J hv)), hv⟩
  ·
    exfalso
    have hVQ : V₂ ≤ Q := fun v hv => by
      have : v ∈ Q ⊓ J := by rw [hW]; exact hv
      exact this.1
    have hQT : Q ≤ T := by
      intro q hq
      have hqM : q ∈ M₂ := by
        rw [h.side₂.M_eq]
        refine mem_normalizer_of_conj_mem fun v hv => ?_
        have h1 : q * v * q⁻¹ ∈ Q ⊓ J :=
          ⟨Q.mul_mem (Q.mul_mem hq (hVQ hv)) (Q.inv_mem hq),
            h.base.conj_J (hQS hq) (h.base.V₂_le_J hv)⟩
        rw [hW] at h1
        exact h1
      rw [← h.base.S_inf_M₂]
      exact ⟨hQS hq, hqM⟩
    have hQJ : Q ≤ J := by
      intro q hq
      by_contra hqJ
      obtain ⟨⟨v, hv, hv'⟩, -⟩ := h.field.fixZ q (hQT hq) hqJ
      apply hv'
      have h1 := hcomm q hq v (h.base.V_le_J hv)
      rw [hW] at h1
      have h2 : ⁅q, v⁆ ∈ V := by
        have : ⁅q, v⁆ = (q * v * q⁻¹) * v⁻¹ := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        refine V.mul_mem ?_ (V.inv_mem hv)
        rw [← (h.base.T_norm q (hQT hq)).1]
        exact mul_mem_cj q hv
      rw [← h.base.inf]
      exact ⟨h2, h1⟩
    have hQV : Q ≤ V₂ := fun q hq => by
      have : q ∈ Q ⊓ J := ⟨hq, hQJ hq⟩
      rw [hW] at this
      exact this
    have hNM : N ≤ M₂ := fun n hn => by
      rw [h.side₂.M_eq]
      exact mem_normalizer_of_conj_mem fun v hv => hQV (hQn n hn v (hVQ hv))
    have hNJ : N ≤ Subgroup.normalizer (J : Set G) := fun n hn =>
      h.side₂.mem_normalizer_J hz₀ hz₀1 (hNM hn) hn
    have hJQ : J ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (fun j hj => hSN (hJS hj)) hNJ hJp
    apply h.base.not_V_le_Z
    intro v hv
    rw [← h.base.inf]
    exact ⟨hv, hQV (hJQ (h.base.V_le_J hv))⟩
  · exact inf_eq_right.1 hW

theorem T2Loc.normalizer_Z_le (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) :
    Subgroup.normalizer (Z : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (Z : Set G)
  have hQS : CFSG.Open.pCoreOf 2 N ≤ S :=
    pCoreOf_le_of_isSylowOf (h.base.sylow.of_le h.base.S_le_normalizer_Z le_top)
  intro n hn
  exact h.base.mem_normalizer_J_of_le hQS h.J_le_O2 fun q hq =>
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N hn) q).1 hq

theorem T2Loc.normalizer_J_le (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
  intro n hn
  have hcjJ : cj n J ≤ J := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact (Subgroup.mem_normalizer_iff.1 hn y).1 hy
  have hcV : ∀ U : Subgroup G, ElemAb2 U → Nat.card U = 2 ^ (2 * e) → U ≤ J →
      cj n U = V ∨ cj n U = V₂ := fun U hU hUc hUJ =>
    h.base.A_S _ (((cj_mono n hUJ).trans hcjJ).trans h.base.J_le_S) (elemAb2_cj hU n)
      ((card_cj n U).trans hUc)
  have h1 := hcV V h.base.elem_V h.base.card_V h.base.V_le_J
  have h2 := hcV V₂ h.base.elem_V₂ h.base.card_V₂ h.base.V₂_le_J
  have hne : cj n V ≠ cj n V₂ := fun heq =>
    h.base.V_ne (Subgroup.map_injective (f := (MulAut.conj n).toMonoidHom)
      (MulAut.conj n).injective heq)
  have hZ : cj n Z = Z := by
    rw [← h.base.inf, CFSG.CGT.PushingUpLit.A78Sp4.cj_inf_eq]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, inf_comm]
    · exact absurd (h1.trans h2.symm) hne
  exact mem_normalizer_of_cj hZ

end CFSG.CGT.PushingUpLit.A78T2
