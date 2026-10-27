module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplStep2A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

namespace S8Data

variable {P : Type} [Group P] {V1 V2 : Subgroup P} {φ1 φ2 : (Fin 5 → ZMod 2) → P}
  {α β : P →* S8A5}

theorem sup_comm_mem (h : S8Data V1 V2 φ1 φ2 α β) {y y' : P} (hy : y ∈ V1 ⊔ V2)
    (hy' : y' ∈ V1 ⊔ V2) : y * y' = y' * y := by
  obtain ⟨a1, ha1, a2, ha2, rfl⟩ := s8_mem_sup_of_commute h.comm hy
  obtain ⟨b1, hb1, b2, hb2, rfl⟩ := s8_mem_sup_of_commute h.comm hy'
  have h11 : Commute a1 b1 := h.coord1.comm_mem ha1 hb1
  have h12 : Commute a1 b2 := h.comm a1 ha1 b2 hb2
  have h21 : Commute a2 b1 := (h.comm b1 hb1 a2 ha2).symm
  have h22 : Commute a2 b2 := h.coord2.comm_mem ha2 hb2
  exact ((h11.mul_right h12).mul_left (h21.mul_right h22)).eq

theorem act_mod (h : S8Data V1 V2 φ1 φ2 α β) {n y : P} (hn : n ∈ centralizer (V2 : Set P))
    (hy : y ∈ V1 ⊔ V2) : ((n * y * n⁻¹ : P) : P ⧸ V1) = (y : P ⧸ V1) := by
  haveI := h.normal1
  obtain ⟨v1, hv1, v2, hv2, rfl⟩ := s8_mem_sup_of_commute h.comm hy
  have h2 : n * v2 * n⁻¹ = v2 := by
    rw [← Subgroup.mem_centralizer_iff.mp hn v2 hv2]; group
  have e : n * (v1 * v2) * n⁻¹ = (n * v1 * n⁻¹) * v2 := by
    calc n * (v1 * v2) * n⁻¹ = (n * v1 * n⁻¹) * (n * v2 * n⁻¹) := by group
      _ = (n * v1 * n⁻¹) * v2 := by rw [h2]
  rw [e, QuotientGroup.mk_mul V1 (n * v1 * n⁻¹) v2, QuotientGroup.mk_mul V1 v1 v2,
    (QuotientGroup.eq_one_iff (n * v1 * n⁻¹)).mpr (Subgroup.Normal.conj_mem inferInstance v1 hv1 n),
    (QuotientGroup.eq_one_iff v1).mpr hv1]

theorem cross_mem_V (h : S8Data V1 V2 φ1 φ2 α β) {x n : P} (hx : x ∈ centralizer (V1 : Set P))
    (hn : n ∈ centralizer (V2 : Set P)) : x * n * x⁻¹ * n⁻¹ ∈ V1 ⊔ V2 := by
  rw [← h.ker_inf]
  have hx' : α x = 1 := by rw [h.cent_V1] at hx; exact MonoidHom.mem_ker.mp hx
  have hn' : β n = 1 := by rw [h.cent_V2] at hn; exact MonoidHom.mem_ker.mp hn
  refine ⟨MonoidHom.mem_ker.mpr ?_, MonoidHom.mem_ker.mpr ?_⟩
  · simp [hx']
  · simp [hn']

theorem cross_mul_mod [V1.Normal] (h : S8Data V1 V2 φ1 φ2 α β) {x n n' : P}
    (hx : x ∈ centralizer (V1 : Set P)) (hn : n ∈ centralizer (V2 : Set P))
    (hn' : n' ∈ centralizer (V2 : Set P)) :
    ((x * (n * n') * x⁻¹ * (n * n')⁻¹ : P) : P ⧸ V1) =
      ((x * n * x⁻¹ * n⁻¹ : P) : P ⧸ V1) * ((x * n' * x⁻¹ * n'⁻¹ : P) : P ⧸ V1) := by
  have hc' : x * n' * x⁻¹ * n'⁻¹ ∈ V1 ⊔ V2 := h.cross_mem_V hx hn'
  have e : x * (n * n') * x⁻¹ * (n * n')⁻¹ =
      (x * n * x⁻¹ * n⁻¹) * (n * (x * n' * x⁻¹ * n'⁻¹) * n⁻¹) := by group
  rw [e, QuotientGroup.mk_mul, h.act_mod hn hc']

theorem cross_comm_mem (h : S8Data V1 V2 φ1 φ2 α β)
    (hperf : centralizer (V2 : Set P) ≤ s8H V2) {x m : P} (hx : x ∈ centralizer (V1 : Set P))
    (hm : m ∈ centralizer (V2 : Set P)) : x * m * x⁻¹ * m⁻¹ ∈ V1 := by
  haveI := h.normal1
  let S : Subgroup P :=
    { carrier := {n | n ∈ centralizer (V2 : Set P) ∧ x * n * x⁻¹ * n⁻¹ ∈ V1}
      mul_mem' := by
        rintro n n' ⟨hn, hcn⟩ ⟨hn', hcn'⟩
        refine ⟨mul_mem hn hn', ?_⟩
        have e : x * (n * n') * x⁻¹ * (n * n')⁻¹ =
            (x * n * x⁻¹ * n⁻¹) * (n * (x * n' * x⁻¹ * n'⁻¹) * n⁻¹) := by group
        rw [e]
        exact mul_mem hcn (Subgroup.Normal.conj_mem inferInstance _ hcn' n)
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro n ⟨hn, hcn⟩
        refine ⟨inv_mem hn, ?_⟩
        have e : x * n⁻¹ * x⁻¹ * (n⁻¹)⁻¹ = n⁻¹ * (x * n * x⁻¹ * n⁻¹)⁻¹ * (n⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.Normal.conj_mem inferInstance _ (inv_mem hcn) n⁻¹ }
  have hcomm : ∀ n ∈ centralizer (V2 : Set P), ∀ n' ∈ centralizer (V2 : Set P),
      n * n' * n⁻¹ * n'⁻¹ ∈ S := by
    intro n hn n' hn'
    have hM : n * n' * n⁻¹ * n'⁻¹ ∈ centralizer (V2 : Set P) :=
      mul_mem (mul_mem (mul_mem hn hn') (inv_mem hn)) (inv_mem hn')
    refine ⟨hM, ?_⟩
    set F : P → P ⧸ V1 := fun n => ((x * n * x⁻¹ * n⁻¹ : P) : P ⧸ V1) with hF
    have hFmul : ∀ a ∈ centralizer (V2 : Set P), ∀ b ∈ centralizer (V2 : Set P),
        F (a * b) = F a * F b := fun a ha b hb => h.cross_mul_mod hx ha hb
    have hF1 : F 1 = 1 := by simp [hF]
    have hFinv : ∀ a ∈ centralizer (V2 : Set P), F a⁻¹ = (F a)⁻¹ := by
      intro a ha
      have := hFmul a⁻¹ (inv_mem ha) a ha
      rw [inv_mul_cancel, hF1] at this
      exact eq_inv_of_mul_eq_one_left this.symm
    have hFcomm : F n * F n' = F n' * F n := by
      have e := h.sup_comm_mem (h.cross_mem_V hx hn) (h.cross_mem_V hx hn')
      show ((x * n * x⁻¹ * n⁻¹ : P) : P ⧸ V1) * ((x * n' * x⁻¹ * n'⁻¹ : P) : P ⧸ V1) =
        ((x * n' * x⁻¹ * n'⁻¹ : P) : P ⧸ V1) * ((x * n * x⁻¹ * n⁻¹ : P) : P ⧸ V1)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e]
    have h1 : F (n * n' * n⁻¹ * n'⁻¹) = 1 := by
      rw [hFmul _ (mul_mem (mul_mem hn hn') (inv_mem hn)) _ (inv_mem hn'),
        hFmul _ (mul_mem hn hn') _ (inv_mem hn), hFmul n hn n' hn', hFinv n hn, hFinv n' hn',
        hFcomm]
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hM1S : centralizer (V2 : Set P) ≤ S := fun n hn =>
    (Subgroup.commutator_le.mpr hcomm) (hperf hn)
  exact (hM1S hm).2

theorem H_inf_V2 (h : S8Data V1 V2 φ1 φ2 α β) : s8H V2 ⊓ V2 = ⊥ := by
  haveI := h.normal2
  haveI := h.H_normal
  rw [Subgroup.eq_bot_iff_forall]
  by_contra hne
  push_neg at hne
  obtain ⟨d, hd, hd1⟩ := hne
  have hV2H : V2 ≤ s8H V2 := by
    obtain ⟨u, hu, rfl⟩ := h.coord2.surj d hd.2
    have hu0 : u ≠ 0 := fun h0 => hd1 (by rw [h0]; exact h.coord2.map_zero')
    have htr : ∀ a : S8A5, φ2 (permVec (a : Equiv.Perm (Fin 5)) u) ∈ s8H V2 := by
      intro a
      obtain ⟨g, -, hg⟩ := h.surj 1 a
      have := Subgroup.Normal.conj_mem inferInstance _ hd.1 g
      rwa [h.act2 g u hu, hg] at this
    intro y hy
    obtain ⟨w, hw, rfl⟩ := h.coord2.surj y hy
    obtain ⟨a1, a2, hw12⟩ := s8_fin_irred u w hu hw hu0
    rcases hw12 with hw12 | hw12
    · rw [hw12, h.coord2.mul _ _ (s8_isEvenVec_permVec _ hu) (s8_isEvenVec_permVec _ hu)]
      exact mul_mem (htr a1) (htr a2)
    · rw [hw12]; exact htr a1
  have hVH : V1 ⊔ V2 ≤ s8H V2 := sup_le h.V1_le_H hV2H
  have hperf : centralizer (V2 : Set P) ≤ s8H V2 := by
    intro m hm
    have hmk : β m = 1 := by rw [h.cent_V2] at hm; exact MonoidHom.mem_ker.mp hm
    obtain ⟨x, hx, hxa⟩ := h.alpha_surj_H (α m)
    have hxk : β x = 1 := by
      have := h.H_le_cent hx
      rw [h.cent_V2] at this; exact MonoidHom.mem_ker.mp this
    have hxm : x⁻¹ * m ∈ V1 ⊔ V2 := h.ker _ (by simp [hxa]) (by simp [hxk, hmk])
    have e : m = x * (x⁻¹ * m) := by group
    rw [e]
    exact mul_mem hx (hVH hxm)
  have hcent : ∀ x ∈ centralizer (V1 : Set P), ∀ y ∈ V2, x * y * x⁻¹ = y := by
    intro x hx y hy
    have hy' : y ∈ centralizer (V2 : Set P) :=
      Subgroup.mem_centralizer_iff.mpr (fun z hz => h.coord2.comm_mem hz hy)
    have hc := h.cross_comm_mem hperf hx hy'
    have hc2 : x * y * x⁻¹ * y⁻¹ ∈ V2 :=
      mul_mem (Subgroup.Normal.conj_mem inferInstance y hy x) (inv_mem hy)
    have h3 : x * y * x⁻¹ * y⁻¹ ∈ V1 ⊓ V2 := ⟨hc, hc2⟩
    rw [h.disj, Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.mp h3
  obtain ⟨g, hg1, hg2⟩ := h.surj 1 s8PaA
  have hg : g ∈ centralizer (V1 : Set P) := by
    rw [h.cent_V1]; exact MonoidHom.mem_ker.mpr hg1
  apply s8K4_facts.2.2.2.1
  apply s8_fin_faithful
  intro v hv
  have h4 := h.act2 g v hv
  rw [hcent g hg _ (h.coord2.mem v hv), hg2] at h4
  exact (h.coord2.eq_of_eq' hv (s8_isEvenVec_permVec _ hv) h4).symm

theorem H_inf_V (h : S8Data V1 V2 φ1 φ2 α β) : s8H V2 ⊓ (V1 ⊔ V2) = V1 := by
  apply le_antisymm
  · rintro x ⟨hxH, hxV⟩
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ := s8_mem_sup_of_commute h.comm hxV
    have h2 : v2 ∈ s8H V2 ⊓ V2 := ⟨by
      have := mul_mem (inv_mem (h.V1_le_H hv1)) hxH
      simpa using this, hv2⟩
    rw [h.H_inf_V2, Subgroup.mem_bot] at h2
    rw [h2, mul_one]
    exact hv1
  · exact le_inf h.V1_le_H le_sup_left

end S8Data

end CFSG.OddStandard.SmallF3.Omega
