module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011K1b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {A : Type} [Group A] [Finite A] {B : Subgroup A} {t : A} {K : Subgroup (MulAut A)}
  {φ : (Fin 5 → ZMod 2) → A}

private theorem KB_mem_iff {α : MulAut A} :
    α ∈ sec1011_KB B K ↔ α ∈ K ∧ ∀ b ∈ B, α b = b :=
  Iff.rfl

private theorem KB_le_K {α : MulAut A} (hα : α ∈ sec1011_KB B K) : α ∈ K :=
  (KB_mem_iff.mp hα).1

private theorem KB_fixes {α : MulAut A} (hα : α ∈ sec1011_KB B K) : ∀ b ∈ B, α b = b :=
  (KB_mem_iff.mp hα).2

private theorem sq_of_mem_B (h : Sec1011Core B t K φ) {b : A} (hb : b ∈ B) : b * b = 1 := by
  obtain ⟨v, hv, rfl⟩ := (h.mem_B b).1 hb
  exact h.sq hv

private theorem KB_image_stable (h : Sec1011A1 B t K φ) {u : Fin 5 → ZMod 2}
    (hu : IsEvenVec u) (α : MulAut A) (hα : α ∈ sec1011_KB B K)
    (hαt : α t = t * φ u) (σ : Equiv.Perm (Fin 5)) (hσ : σ ∈ alternatingGroup (Fin 5)) :
    ∃ β ∈ sec1011_KB B K, β t = t * φ (permVec σ u) := by
  obtain ⟨n, hnK, hnt, hn⟩ := h.core.N_act σ hσ
  have hninv_t : n⁻¹ t = t := (MulEquiv.symm_apply_eq n).mpr hnt.symm
  refine ⟨n * α * n⁻¹, ⟨K.mul_mem (K.mul_mem hnK (KB_le_K hα)) (K.inv_mem hnK), ?_⟩, ?_⟩
  · intro b hb
    show (n * α * n⁻¹) b = b
    rw [MulAut.mul_apply, MulAut.mul_apply,
      KB_fixes hα (n⁻¹ b) (h.core.B_inv n⁻¹ (K.inv_mem hnK) b hb)]
    exact MulEquiv.apply_symm_apply n b
  · show (n * α * n⁻¹) t = t * φ (permVec σ u)
    rw [MulAut.mul_apply, MulAut.mul_apply, hninv_t, hαt, map_mul, hnt, hn u hu]

theorem Sec1011A1.KB_onto (h : Sec1011A1 B t K φ) :
    ∀ b ∈ B, ∃ α ∈ sec1011_KB B K, α t = t * b := by
  let U : Set (Fin 5 → ZMod 2) :=
    {u | IsEvenVec u ∧ ∃ α ∈ sec1011_KB B K, α t = t * φ u}
  have hUeven : ∀ u ∈ U, IsEvenVec u := fun _ hu => hu.1
  have hUadd : ∀ u ∈ U, ∀ w ∈ U, u + w ∈ U := by
    intro u hu w hw
    obtain ⟨hu_even, α, hαKB, hαt⟩ := hu
    obtain ⟨hw_even, β, hβKB, hβt⟩ := hw
    refine ⟨sec1011_isEvenVec_add hu_even hw_even, α * β,
      (sec1011_KB B K).mul_mem hαKB hβKB, ?_⟩
    show (α * β) t = t * φ (u + w)
    rw [MulAut.mul_apply, hβt, map_mul, hαt, KB_fixes hαKB (φ w) (h.core.mem hw_even)]
    rw [mul_assoc, h.core.hom u w hu_even hw_even]
  have hUperm : ∀ σ ∈ alternatingGroup (Fin 5), ∀ u ∈ U, permVec σ u ∈ U := by
    intro σ hσ u hu
    obtain ⟨hu_even, α, hαKB, hαt⟩ := hu
    exact ⟨isEvenVec_permVec σ hu_even, KB_image_stable h hu_even α hαKB hαt σ hσ⟩
  by_cases hne : ∃ u ∈ U, u ≠ 0
  · intro b hb
    obtain ⟨w, hw_even, hφw⟩ := (h.core.mem_B b).1 hb
    obtain ⟨-, α, hαKB, hαt⟩ :=
      sec1011_alt5_irreducible U hUeven hUadd hUperm hne w hw_even
    exact ⟨α, hαKB, by rw [hαt, hφw]⟩
  · exfalso
    have hUzero : ∀ u ∈ U, u = 0 := by
      intro u hu
      by_contra hu0
      exact hne ⟨u, hu, hu0⟩
    have hKBbot : sec1011_KB B K = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro α hα
      have hb0 : t⁻¹ * α t ∈ B := h.core.coset_inv α (KB_le_K hα)
      obtain ⟨u, hu_even, hφu⟩ := (h.core.mem_B (t⁻¹ * α t)).1 hb0
      have huU : u ∈ U := ⟨hu_even, α, hα, by rw [hφu]; group⟩
      have hu0 : u = 0 := hUzero u huU
      have hαt : α t = t := by
        have h1 : φ u = 1 := by rw [hu0, h.core.map_zero]
        rw [hφu] at h1
        calc α t = t * (t⁻¹ * α t) := by group
          _ = t * 1 := by rw [h1]
          _ = t := mul_one t
      exact h.core.eq_one_of_fix (KB_fixes hα) hαt
    have hle := h.card_K_le
    rw [hKBbot, Subgroup.card_bot] at hle
    simp only [mul_one] at hle
    rcases h.card_K_cases with hc | hc <;> omega

theorem Sec1011A1.KB_card (h : Sec1011A1 B t K φ) : Nat.card ↥(sec1011_KB B K) = 16 := by
  let θ : ↥(sec1011_KB B K) → ↥B :=
    fun α => ⟨t⁻¹ * (α : MulAut A) t, h.core.coset_inv _ (KB_le_K α.2)⟩
  have hbij : Function.Bijective θ := by
    constructor
    · intro α β hαβ
      have hval : t⁻¹ * (α : MulAut A) t = t⁻¹ * (β : MulAut A) t :=
        congrArg Subtype.val hαβ
      have ht : (α : MulAut A) t = (β : MulAut A) t := mul_left_cancel hval
      apply Subtype.ext
      exact h.core.eq_of_eq (fun b hb => (KB_fixes α.2 b hb).trans (KB_fixes β.2 b hb).symm) ht
    · rintro ⟨b, hb⟩
      obtain ⟨α, hαKB, hαt⟩ := Sec1011A1.KB_onto h b hb
      refine ⟨⟨α, hαKB⟩, Subtype.ext ?_⟩
      show t⁻¹ * α t = b
      rw [hαt]
      group
  have hcard := Nat.card_congr (Equiv.ofBijective θ hbij)
  rw [hcard, h.core.card_B]

private theorem KB_comm (h : Sec1011A1 B t K φ) :
    ∀ α β : ↥(sec1011_KB B K), α * β = β * α := by
  intro α β
  have hαK : (α : MulAut A) ∈ K := KB_le_K α.2
  have hβK : (β : MulAut A) ∈ K := KB_le_K β.2
  have hbα : t⁻¹ * (α : MulAut A) t ∈ B := h.core.coset_inv _ hαK
  have hbβ : t⁻¹ * (β : MulAut A) t ∈ B := h.core.coset_inv _ hβK
  apply Subtype.ext
  apply h.core.eq_of_eq
  · intro b hb
    show ((α : MulAut A) * β) b = ((β : MulAut A) * α) b
    simp only [MulAut.mul_apply, KB_fixes α.2 b hb, KB_fixes β.2 b hb]
  · show ((α : MulAut A) * β) t = ((β : MulAut A) * α) t
    have h1 : ((α : MulAut A) * β) t
        = t * ((t⁻¹ * (α : MulAut A) t) * (t⁻¹ * (β : MulAut A) t)) := by
      rw [MulAut.mul_apply,
        show (β : MulAut A) t = t * (t⁻¹ * (β : MulAut A) t) by group, map_mul,
        show (α : MulAut A) t = t * (t⁻¹ * (α : MulAut A) t) by group,
        KB_fixes α.2 _ hbβ]
      group
    have h2 : ((β : MulAut A) * α) t
        = t * ((t⁻¹ * (β : MulAut A) t) * (t⁻¹ * (α : MulAut A) t)) := by
      rw [MulAut.mul_apply,
        show (α : MulAut A) t = t * (t⁻¹ * (α : MulAut A) t) by group, map_mul,
        show (β : MulAut A) t = t * (t⁻¹ * (β : MulAut A) t) by group,
        KB_fixes β.2 _ hbα]
      group
    rw [h1, h2, h.core.comm (t⁻¹ * (α : MulAut A) t) (t⁻¹ * (β : MulAut A) t)]

private theorem KB_sq (h : Sec1011A1 B t K φ) {α : MulAut A}
    (hα : α ∈ sec1011_KB B K) : α ^ 2 = 1 := by
  let b : A := t⁻¹ * α t
  have hb : b ∈ B := h.core.coset_inv α (KB_le_K hα)
  have hαt : α t = t * b := by dsimp [b]; group
  have hfix : α b = b := KB_fixes hα b hb
  have hb2 : b * b = 1 := sq_of_mem_B h.core hb
  apply h.core.eq_one_of_fix (α := α ^ 2)
  · intro b' hb'
    rw [pow_two, MulAut.mul_apply, KB_fixes hα b' hb', KB_fixes hα b' hb']
  · calc (α ^ 2) t = α (α t) := by rw [pow_two, MulAut.mul_apply]
      _ = α (t * b) := by rw [hαt]
      _ = α t * α b := map_mul α t b
      _ = t * (b * b) := by rw [hαt, hfix]; group
      _ = t * 1 := by rw [hb2]
      _ = t := mul_one t

private theorem KB_sup_Kt (h : Sec1011A1 B t K φ) :
    K = sec1011_KB B K ⊔ (K ⊓ MulAction.stabilizer (MulAut A) t) := by
  apply le_antisymm
  · intro γ hγ
    have hb0 : t⁻¹ * γ t ∈ B := h.core.coset_inv γ hγ
    obtain ⟨c, hcKB, hct⟩ := Sec1011A1.KB_onto h (t⁻¹ * γ t) hb0
    have hcK : c ∈ K := KB_le_K hcKB
    have hct' : c t = γ t := by rw [hct]; group
    have hk : c⁻¹ * γ ∈ K ⊓ MulAction.stabilizer (MulAut A) t := by
      rw [Subgroup.mem_inf]
      refine ⟨K.mul_mem (K.inv_mem hcK) hγ, ?_⟩
      rw [MulAction.mem_stabilizer_iff]
      show (c⁻¹ * γ) t = t
      rw [MulAut.mul_apply, ← hct']
      exact MulEquiv.symm_apply_apply c t
    have hγeq : γ = c * (c⁻¹ * γ) := by group
    rw [hγeq]
    exact Subgroup.mul_mem_sup hcKB hk
  · exact sup_le (fun α hα => hα.1) (fun α hα => hα.1)

theorem sec1011_alt1_core (h : Sec1011A1 B t K φ) :
    K = sec1011_KB B K ⊔ (K ⊓ MulAction.stabilizer (MulAut A) t) ∧
      (sec1011_KB B K).subgroupOf K = CFSG.pCore 2 ↥K ∧
      IsElemAb2 (sec1011_KB B K) 4 ∧
      ∀ x y : A, (∃ b ∈ B, x = t * b) → (∃ b ∈ B, y = t * b) →
        ∃! c : ↥(sec1011_KB B K), (c : MulAut A) x = y := by
  have htop := KB_sup_Kt h
  have hKBelem : IsElemAb2 (sec1011_KB B K) 4 := by
    refine ⟨⟨IsMulCommutative.of_comm (KB_comm h), ?_⟩, ?_⟩
    · intro x hx
      exact KB_sq h hx
    · rw [Sec1011A1.KB_card h]
      norm_num
  have hKBnormal : ((sec1011_KB B K).subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    show (g : MulAut A) * (n : MulAut A) * (g : MulAut A)⁻¹ ∈ sec1011_KB B K
    refine ⟨K.mul_mem (K.mul_mem g.2 (KB_le_K hn)) (K.inv_mem g.2), fun b hb => ?_⟩
    show ((g : MulAut A) * (n : MulAut A) * (g : MulAut A)⁻¹) b = b
    rw [MulAut.mul_apply, MulAut.mul_apply,
      KB_fixes hn _ (h.core.B_inv _ (K.inv_mem g.2) b hb)]
    exact MulEquiv.apply_symm_apply (g : MulAut A) b
  have hKBle : ((sec1011_KB B K).subgroupOf K) ≤ CFSG.pCore 2 ↥K := by
    have hp : IsPGroup 2 ↥((sec1011_KB B K).subgroupOf K) := by
      refine IsPGroup.of_card (n := 4) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show sec1011_KB B K ≤ K from
        fun α hα => KB_le_K hα)).toEquiv, Sec1011A1.KB_card h]
      norm_num
    rw [CFSG.pCore]
    exact le_sSup ⟨hKBnormal, hp⟩
  have hpCore_le : CFSG.pCore 2 ↥K ≤ (sec1011_KB B K).subgroupOf K := by
    let Kt : Subgroup (MulAut A) := K ⊓ MulAction.stabilizer (MulAut A) t
    let Z : Subgroup ↥K := Kt.subgroupOf K
    let P : Subgroup ↥K := CFSG.pCore 2 ↥K
    haveI : ((sec1011_KB B K).subgroupOf K).Normal := hKBnormal
    have hQnorm : (P.subgroupOf Z).Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥K)).subgroupOf Z
    have hQp : IsPGroup 2 ↥(P.subgroupOf Z) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).comap_subtype (K := Z)
    have hQbot : P.subgroupOf Z = ⊥ := by
      rcases h.iso with hL | hR
      · let e : ↥Kt ≃* ↥(alternatingGroup (Fin 5)) := Classical.choice hL
        have eZ : ↥Z ≃* ↥(alternatingGroup (Fin 5)) :=
          (Subgroup.subgroupOfEquivOfLe (show Kt ≤ K from inf_le_left)).trans e
        exact (Subgroup.map_eq_bot_iff_of_injective
          (H := P.subgroupOf Z) (f := eZ.toMonoidHom) eZ.injective).mp
          (sec1011_alt5_normal_two _ (hQnorm.map eZ.toMonoidHom eZ.surjective)
            (hQp.map eZ.toMonoidHom))
      · let e : ↥Kt ≃* Equiv.Perm (Fin 5) := Classical.choice hR
        have eZ : ↥Z ≃* Equiv.Perm (Fin 5) :=
          (Subgroup.subgroupOfEquivOfLe (show Kt ≤ K from inf_le_left)).trans e
        exact (Subgroup.map_eq_bot_iff_of_injective
          (H := P.subgroupOf Z) (f := eZ.toMonoidHom) eZ.injective).mp
          (sec1011_perm5_normal_two _ (hQnorm.map eZ.toMonoidHom eZ.surjective)
            (hQp.map eZ.toMonoidHom))
    have hsupZ : (sec1011_KB B K).subgroupOf K ⊔ Z = ⊤ := by
      change (sec1011_KB B K).subgroupOf K ⊔ Kt.subgroupOf K = ⊤
      have hh := Subgroup.subgroupOf_sup (A := sec1011_KB B K) (A' := Kt) (B := K)
        (fun x hx => hx.1) inf_le_left
      rw [← hh, show sec1011_KB B K ⊔ Kt = K from htop.symm]
      exact Subgroup.subgroupOf_self (H := K)
    intro p hp
    have hpmem : p ∈ (sec1011_KB B K).subgroupOf K ⊔ Z := by
      rw [hsupZ]
      exact Subgroup.mem_top p
    obtain ⟨y, hy, z, hz, hyz⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := (sec1011_KB B K).subgroupOf K) (t := Z)
        (x := p)).mp hpmem
    have hyP : y ∈ P := hKBle hy
    have hzP : z ∈ P := by
      have hsplit : y⁻¹ * p = z := by rw [← hyz]; group
      rw [← hsplit]
      exact P.mul_mem (P.inv_mem hyP) hp
    have hz1 : z = 1 := by
      have hmem : (⟨z, hz⟩ : ↥Z) ∈ P.subgroupOf Z := by
        rw [Subgroup.mem_subgroupOf]
        exact hzP
      rw [hQbot] at hmem
      have h1 : (⟨z, hz⟩ : ↥Z) = 1 := by simpa using hmem
      simpa using congrArg (fun x : ↥Z => (x : ↥K)) h1
    have hpeq : p = y := by rw [← hyz, hz1, mul_one]
    rw [hpeq]
    exact hy
  have hreg : ∀ x y : A, (∃ b ∈ B, x = t * b) → (∃ b ∈ B, y = t * b) →
      ∃! c : ↥(sec1011_KB B K), (c : MulAut A) x = y := by
    intro x y hx hy
    obtain ⟨b1, hb1, rfl⟩ := hx
    obtain ⟨b2, hb2, rfl⟩ := hy
    obtain ⟨c, hcKB, hct⟩ :=
      Sec1011A1.KB_onto h (b1⁻¹ * b2) (B.mul_mem (B.inv_mem hb1) hb2)
    have hb12 : (b1⁻¹ * b2) * b1 = b2 := by
      rw [mul_assoc, h.core.comm b2 b1, inv_mul_cancel_left]
    refine ⟨⟨c, hcKB⟩, ?_, ?_⟩
    · show c (t * b1) = t * b2
      rw [map_mul, KB_fixes hcKB b1 hb1, hct, mul_assoc, hb12]
    · intro d hd
      apply Subtype.ext
      apply h.core.eq_of_eq (α := (d : MulAut A)) (β := c)
      · intro b hb
        exact (KB_fixes d.2 b hb).trans (KB_fixes hcKB b hb).symm
      · have hcval : c (t * b1) = t * b2 := by
          rw [map_mul, KB_fixes hcKB b1 hb1, hct, mul_assoc, hb12]
        have hdval : (d : MulAut A) (t * b1) = t * b2 := hd
        have hc_b1 : c b1 = b1 := KB_fixes hcKB b1 hb1
        have hd_b1 : (d : MulAut A) b1 = b1 := KB_fixes d.2 b1 hb1
        have h3 : (d : MulAut A) t * b1 = c t * b1 := by
          calc (d : MulAut A) t * b1 = (d : MulAut A) t * (d : MulAut A) b1 := by rw [hd_b1]
            _ = (d : MulAut A) (t * b1) := (map_mul (d : MulAut A) t b1).symm
            _ = t * b2 := hdval
            _ = c (t * b1) := hcval.symm
            _ = c t * c b1 := map_mul c t b1
            _ = c t * b1 := by rw [hc_b1]
        exact mul_right_cancel h3
  exact ⟨htop, le_antisymm hKBle hpCore_le, hKBelem, hreg⟩

end CFSG.OddStandard.SmallF3.Omega
