module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

namespace B5a

variable (h : Hyp52 H)

theorem isPGroup_S : IsPGroup 2 h.S := by
  obtain ⟨R, hR⟩ := h.S_sylow
  have h1 : IsPGroup 2 (h.S.subgroupOf (centralizer ({h.a} : Set H) ⊓
      normalizer (h.J : Set H))) := hR ▸ R.isPGroup'
  have h2 := h1.map (centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)).subtype
  rwa [map_subgroupOf_eq_of_le h.S_le] at h2

theorem isPGroup_B : IsPGroup 2 h.B :=
  (isPGroup_S h).to_le (h.B_le.trans inf_le_left)

theorem B_le_T : h.B ≤ h.T :=
  le_inf (le_inf (h.B_le.trans inf_le_left) le_normalizer) h.B_le

instance normal_B_subgroupOf_T : (h.B.subgroupOf h.T).Normal :=
  (normal_subgroupOf_iff_le_normalizer (B_le_T h)).mpr (inf_le_left.trans inf_le_right)

end B5a

namespace Hyp52

variable (h : Hyp52 H)

omit [Finite H] in
private theorem card_subgroupOf_eq (A C : Subgroup H) :
    Nat.card (A.subgroupOf C) = Nat.card ↥(A ⊓ C) := by
  rw [← inf_subgroupOf_right]
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv

theorem sylow_kernel : h.B ≤ coreActionKernel h.V ∧
    ∃ R : Sylow 2 ↥(coreActionKernel h.V),
      (R : Subgroup _) = h.B.subgroupOf (coreActionKernel h.V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel h.V with hC
  set D := normalizer (h.B : Set H) ⊓ C with hD
  have hBD : h.B ≤ D := h.B_le_kernel
  have hBC : h.B ≤ C := hBD.trans inf_le_right
  refine ⟨hBC, ?_⟩
  obtain ⟨n, hn⟩ := (B5a.isPGroup_B h).exists_card_eq
  have hcardB : Nat.card (h.B.subgroupOf C) = 2 ^ n := by
    rw [card_subgroupOf_eq, inf_of_le_left hBC, hn]
  obtain ⟨R₀, hR₀⟩ := h.B_sylow_kernel
  have hR₀card : Nat.card R₀ = 2 ^ n := by
    rw [show Nat.card R₀ = Nat.card (R₀ : Subgroup D) from rfl, hR₀, card_subgroupOf_eq,
      inf_of_le_left hBD, hn]
  have hDfac : (Nat.card D).factorization 2 = n := by
    have h1 := R₀.card_eq_multiplicity
    rw [hR₀card] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hD0 : Nat.card D ≠ 0 := Nat.card_pos.ne'
  have hnD : ¬ 2 ^ (n + 1) ∣ Nat.card D := by
    rw [← hDfac]
    exact Nat.pow_succ_factorization_not_dvd hD0 Nat.prime_two
  have hnC : ¬ 2 ^ (n + 1) ∣ Nat.card C := by
    intro hdvd
    have h1 := Sylow.prime_pow_dvd_card_normalizer hdvd hcardB
    rw [← subgroupOf_normalizer_eq hBC, card_subgroupOf_eq] at h1
    exact hnD h1
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card C).factorization 2 = n := by
    have hle : n ≤ (Nat.card C).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hC0).mp
        (hcardB ▸ Subgroup.card_subgroup_dvd_card _)
    have hlt : ¬ n + 1 ≤ (Nat.card C).factorization 2 := fun h1 =>
      hnC ((Nat.prime_two.pow_dvd_iff_le_factorization hC0).mpr h1)
    omega
  exact ⟨Sylow.ofCard (h.B.subgroupOf C) (by rw [hcardB, hfac]), rfl⟩

end Hyp52

namespace B5a

variable (h : Hyp59 H)

theorem conj_x_mem {b : H} (hb : b ∈ h.B) :
    h.x⁻¹ * b * h.x ∈ h.toHyp52.T ∧ h.x * b * h.x⁻¹ ∈ h.toHyp52.Q := by
  have hxS : h.x ∈ h.S := h.x_mem
  have hxJ : h.x ∈ normalizer (h.J : Set H) := (mem_inf.mp (h.S_le hxS)).2
  have hbP : b ∈ h.toHyp52.P := h.B_le hb
  have hPx : ∀ y ∈ h.toHyp52.P, h.x⁻¹ * y * h.x ∈ h.toHyp52.P ∧ h.x * y * h.x⁻¹ ∈ h.toHyp52.P := by
    intro y hy
    obtain ⟨hyS, hyC⟩ := mem_inf.mp hy
    refine ⟨mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hxS) hyS) hxS,
      conj_mem_coreActionKernel hxJ hyC⟩, mem_inf.mpr ⟨mul_mem (mul_mem hxS hyS) (inv_mem hxS), ?_⟩⟩
    have h1 := conj_mem_coreActionKernel (inv_mem hxJ) hyC
    rwa [inv_inv] at h1
  have hbQ : b ∈ h.toHyp52.Q := (B_le_T h.toHyp52 hb).1
  have hQ : h.x⁻¹ * b * h.x ∈ h.toHyp52.Q ∧ h.x * b * h.x⁻¹ ∈ h.toHyp52.Q := by
    rcases h.x_cond with hx | ⟨hPQ, -⟩
    · have hxN := (mem_inf.mp hx).2
      refine ⟨?_, (mem_normalizer_iff.mp hxN b).mp hbQ⟩
      have h1 := (mem_normalizer_iff.mp (inv_mem hxN) b).mp hbQ
      rwa [inv_inv] at h1
    · exact ⟨hPQ (hPx b hbP).1, hPQ (hPx b hbP).2⟩
  exact ⟨mem_inf.mpr ⟨hQ.1, (hPx b hbP).1⟩, hQ.2⟩

theorem conjugate_B_x_le_T : conjugate h.B h.x ≤ h.toHyp52.T := by
  intro y hy
  rw [mem_conjugate_iff] at hy
  have h1 := (conj_x_mem h hy).1
  rwa [show h.x⁻¹ * (h.x * y * h.x⁻¹) * h.x = y by group] at h1

end B5a

namespace Hyp59

variable (h : Hyp59 H)

theorem prod_conj :
    conjugate h.B h.x ≤ normalizer (h.B : Set H) ∧
      h.B ≤ normalizer (conjugate h.B h.x : Set H) ∧
      ⁅h.B, conjugate h.B h.x⁆ = ⊥ ∧ h.B ⊓ conjugate h.B h.x = ⊥ ∧
      ∃ e : ↥h.B × ↥(conjugate h.B h.x) ≃* ↥(h.B ⊔ conjugate h.B h.x),
        ∀ (b : h.B) (c : conjugate h.B h.x), (e (b, c) : H) = b * c := by
  have hN1 : conjugate h.B h.x ≤ normalizer (h.B : Set H) := fun y hy =>
    (mem_inf.mp (mem_inf.mp (B5a.conjugate_B_x_le_T h hy)).1).2
  have hN2 : h.B ≤ normalizer (conjugate h.B h.x : Set H) := by
    intro b hb
    have hxb : h.x * b * h.x⁻¹ ∈ normalizer (h.B : Set H) :=
      (mem_inf.mp (B5a.conj_x_mem h hb).2).2
    rw [mem_normalizer_iff]
    intro y
    rw [mem_conjugate_iff, mem_conjugate_iff,
      show h.x * (b * y * b⁻¹) * h.x⁻¹ =
        (h.x * b * h.x⁻¹) * (h.x * y * h.x⁻¹) * (h.x * b * h.x⁻¹)⁻¹ by group]
    exact mem_normalizer_iff.mp hxb _
  have hinf : h.B ⊓ conjugate h.B h.x = ⊥ := h.inf_conjugate_x
  have hcomm : ⁅h.B, conjugate h.B h.x⁆ = ⊥ := by
    rw [eq_bot_iff, ← hinf, commutator_le]
    intro b hb c hc
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def, show b * c * b⁻¹ * c⁻¹ = b * (c * b⁻¹ * c⁻¹) by group]
      exact mul_mem hb ((mem_normalizer_iff.mp (hN1 hc) b⁻¹).mp (inv_mem hb))
    · rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp (hN2 hb) c).mp hc) (inv_mem hc)
  refine ⟨hN1, hN2, hcomm, hinf, ?_⟩
  have hc : ∀ (b : h.B) (c : conjugate h.B h.x),
      Commute (h.B.subtype b) ((conjugate h.B h.x).subtype c) := by
    intro b c
    have h1 : ⁅(b : H), (c : H)⁆ = 1 := by
      have h2 : ⁅(b : H), (c : H)⁆ ∈ ⁅h.B, conjugate h.B h.x⁆ :=
        commutator_mem_commutator b.2 c.2
      rwa [hcomm, mem_bot] at h2
    exact commutatorElement_eq_one_iff_commute.mp h1
  set φ := MonoidHom.noncommCoprod h.B.subtype (conjugate h.B h.x).subtype hc with hφ
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨b, c⟩ hbc
    have h1 : (b : H) * c = 1 := hbc
    have h2 : (c : H) = (b : H)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : (c : H) ∈ h.B ⊓ conjugate h.B h.x := mem_inf.mpr ⟨h2 ▸ inv_mem b.2, c.2⟩
    rw [hinf, mem_bot] at h3
    have h4 : (b : H) = 1 := by rw [h3, mul_one] at h1; exact h1
    exact Prod.ext (Subtype.ext h4) (Subtype.ext h3)
  have hrange : φ.range = h.B ⊔ conjugate h.B h.x := by
    rw [hφ, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  refine ⟨(MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hrange), fun b c => ?_⟩
  rfl

theorem embeds_T_quot :
    ∃ f : ↥h.B →* ↥h.toHyp52.T ⧸ h.B.subgroupOf h.toHyp52.T, Function.Injective f := by
  have hmem : ∀ b : h.B, ((MulAut.conj h.x⁻¹).toMonoidHom.comp h.B.subtype) b ∈ h.toHyp52.T := by
    intro b
    show h.x⁻¹ * b * h.x⁻¹⁻¹ ∈ h.toHyp52.T
    rw [inv_inv]
    exact (B5a.conj_x_mem h b.2).1
  let g : ↥h.B →* ↥h.toHyp52.T :=
    ((MulAut.conj h.x⁻¹).toMonoidHom.comp h.B.subtype).codRestrict h.toHyp52.T hmem
  refine ⟨(QuotientGroup.mk' (h.B.subgroupOf h.toHyp52.T)).comp g, ?_⟩
  rw [injective_iff_map_eq_one]
  intro b hb
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_subgroupOf] at hb
  have hb' : h.x⁻¹ * b * h.x ∈ h.B := by
    have h1 : ((g b : h.toHyp52.T) : H) = h.x⁻¹ * b * h.x⁻¹⁻¹ := rfl
    rwa [h1, inv_inv] at hb
  have h2 : h.x⁻¹ * b * h.x ∈ h.B ⊓ conjugate h.B h.x :=
    mem_inf.mpr ⟨hb', conj_mem_conjugate b.2 h.x⟩
  rw [h.inf_conjugate_x, mem_bot] at h2
  apply Subtype.ext
  show (b : H) = 1
  have h3 : (b : H) = h.x * (h.x⁻¹ * b * h.x) * h.x⁻¹ := by group
  rw [h3, h2, mul_one, mul_inv_cancel]

end Hyp59

end CFSG.ComponentClassification.GSThmB
