module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ParaD
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fin4
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L131
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ParaC

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem le_sylow_of_normal [Finite G] {B P Q : Subgroup G} (hP : SylowIn 2 P B) (hQB : Q ≤ B)
    (hQ2 : IsPGroup 2 ↥Q) (hQn : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) : Q ≤ P := by
  obtain ⟨P', hP', hQP'⟩ := SylowIn.exists_ge (p := 2) hQB hQ2
  obtain ⟨c, hcB, hc⟩ := SylowIn.conj (p := 2) hP' hP
  intro q hq
  refine (hc q).2 (hQP' ?_)
  have := hQn c⁻¹ (B.inv_mem hcB) q hq
  have e : c⁻¹ * q * c⁻¹⁻¹ = c⁻¹ * q * c := by rw [inv_inv]
  rw [e] at this
  exact this

theorem cent_cover_conj {x c : G} {V H : Subgroup G}
    (hcov : ∀ b ∈ Bb V H, ∃ h ∈ H, b * x * b⁻¹ = h * x * h⁻¹)
    (hcN : c ∈ normalizer (V : Set G)) (hcx : c * x * c⁻¹ = x) :
    ∀ b ∈ Bb V (cj c⁻¹ H), ∃ h ∈ cj c⁻¹ H, b * x * b⁻¹ = h * x * h⁻¹ := by
  have hmem : ∀ g, g ∈ cj c⁻¹ H ↔ c * g * c⁻¹ ∈ H := fun g => by rw [mem_cj]; simp
  intro b hb
  have hbN : b ∈ normalizer (V : Set G) := hb.1
  have hb2 : c * b * c⁻¹ ∈ Bb V H := by
    refine ⟨(normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).mul_mem hcN hbN)
      ((normalizer (V : Set G)).inv_mem hcN), ?_⟩
    show c * b * c⁻¹ ∈ normalizer (H : Set G)
    rw [mem_normalizer_iff]
    intro g
    have := mem_normalizer_iff.1 hb.2 (c⁻¹ * g * c)
    rw [hmem, hmem] at this
    have e : c * (b * (c⁻¹ * g * c) * b⁻¹) * c⁻¹ = (c * b * c⁻¹) * g * (c * b * c⁻¹)⁻¹ := by group
    have e2 : c * (c⁻¹ * g * c) * c⁻¹ = g := by group
    rw [e, e2] at this
    exact this
  obtain ⟨h, hh, hbx⟩ := hcov _ hb2
  have hh' : c * (c⁻¹ * h * c) * c⁻¹ ∈ H := by
    have e : c * (c⁻¹ * h * c) * c⁻¹ = h := by group
    rw [e]; exact hh
  refine ⟨c⁻¹ * h * c, (hmem _).2 hh', ?_⟩
  have hcx' : c⁻¹ * x * c = x := by
    calc c⁻¹ * x * c = c⁻¹ * (c * x * c⁻¹) * c := by rw [hcx]
      _ = x := by group
  calc b * x * b⁻¹ = c⁻¹ * ((c * b * c⁻¹) * x * (c * b * c⁻¹)⁻¹) * c := by
        have : c⁻¹ * ((c * b * c⁻¹) * x * (c * b * c⁻¹)⁻¹) * c = b * (c⁻¹ * x * c) * b⁻¹ := by group
        rw [this, hcx']
    _ = c⁻¹ * (h * x * h⁻¹) * c := by rw [hbx]
    _ = (c⁻¹ * h * c) * (c⁻¹ * x * c) * (c⁻¹ * h * c)⁻¹ := by group
    _ = (c⁻¹ * h * c) * x * (c⁻¹ * h * c)⁻¹ := by rw [hcx']

theorem lemma13_1_full (h9 : IG_9_16) (h27 : IV2_2_7) : Lemma13_1Full := by
  intro G _ _ x T V hout
  obtain ⟨H, f, d, hc⟩ := lemma13_1_d13 h9 h27 hout
  have hI := d.hI
  have hcov := d.cent_cover hc.sylow
  obtain ⟨c, hcZ, hcT⟩ := exists_conj_T hout hI.E_le hI.H_le hc.sylow hcov
  have hcN : c ∈ normalizer (V : Set G) := hcZ.1
  have hcx : c * x * c⁻¹ = x :=
    mul_inv_eq_iff_eq_mul.2 (mem_centralizer_iff.1 hcZ.2 x rfl).symm
  have hmN : c⁻¹ ∈ normalizer (V : Set G) := (normalizer (V : Set G)).inv_mem hcN
  have hmx : c⁻¹ * x * c⁻¹⁻¹ = x := by
    rw [inv_inv]
    calc c⁻¹ * x * c = c⁻¹ * (c * x * c⁻¹) * c := by rw [hcx]
      _ = x := by group
  have hc' := hc.conj hmN hmx
  refine ⟨cj c⁻¹ H, c⁻¹ * f * c⁻¹⁻¹, hc', ?_⟩
  have hmem : ∀ g, g ∈ cj c⁻¹ H ↔ c * g * c⁻¹ ∈ H := fun g => by rw [mem_cj]; simp
  have hsyl' : Sylow2In (cj c⁻¹ H) (centralizer (V : Set G)) := hc'.sylow
  have hH'C : cj c⁻¹ H ≤ centralizer (V : Set G) := hsyl'.1
  have hEH' : EV x V ≤ cj c⁻¹ H := by
    intro e he
    rw [hmem]
    apply hI.E_le
    obtain ⟨v, hv, he' | he'⟩ := (hout.mem_EV).1 he
    · rw [he']
      exact (hout.mem_EV).2 ⟨c * v * c⁻¹, (mem_normalizer_iff.1 hcN v).1 hv, Or.inl rfl⟩
    · rw [he']
      refine (hout.mem_EV).2 ⟨c * v * c⁻¹, (mem_normalizer_iff.1 hcN v).1 hv, Or.inr ?_⟩
      calc c * (v * x) * c⁻¹ = (c * v * c⁻¹) * (c * x * c⁻¹) := by group
        _ = (c * v * c⁻¹) * x := by rw [hcx]
  have hTnorm : T ≤ normalizer ((cj c⁻¹ H : Subgroup G) : Set G) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro g
    rw [hmem, hmem]
    have hb := hcT t ht
    have e : c * (t * g * t⁻¹) * c⁻¹ = (c * t * c⁻¹) * (c * g * c⁻¹) * (c * t * c⁻¹)⁻¹ := by group
    rw [e]
    exact mem_normalizer_iff.1 hb.2 (c * g * c⁻¹)
  have hTinter : T ⊓ cj c⁻¹ H = EV x V := by
    apply le_antisymm
    · intro g hg
      have : g ∈ T ⊓ centralizer (V : Set G) := ⟨hg.1, hH'C hg.2⟩
      rwa [hout.T_inf_C] at this
    · exact le_inf hout.E_le_T hEH'
  have hElt : EV x V < cj c⁻¹ H := by
    refine lt_of_le_of_ne hEH' ?_
    intro h
    apply hout.not_sylow_E
    rw [h]
    exact hsyl'
  have hcov' := cent_cover_conj hcov hcN hcx
  have hTB' : T ≤ Bb V (cj c⁻¹ H) := fun t ht => ⟨hout.T_le_normalizer ht, hTnorm ht⟩
  have hT2 : IsPGroup 2 ↥T := hout.T_sylow.2.1
  obtain ⟨R₀, hR₀, hTR₀⟩ := SylowIn.exists_ge (p := 2) hTB' hT2
  have hH'B' : cj c⁻¹ H ≤ Bb V (cj c⁻¹ H) := fun g hg =>
    ⟨centralizer_le_normalizer _ (hH'C hg), le_normalizer hg⟩
  have hH'R₀ : cj c⁻¹ H ≤ R₀ :=
    le_sylow_of_normal hR₀ hH'B' hsyl'.2.1 (fun b hb q hq => (mem_normalizer_iff.1 hb.2 q).1 hq)
  have hR₀N : R₀ ≤ normalizer (V : Set G) := fun r hr => (hR₀.le hr).1
  obtain ⟨R₁, hR₁, hR₀R₁⟩ := SylowIn.exists_ge (p := 2) hR₀N hR₀.isPGroup
  have hH'R₁ : cj c⁻¹ H ≤ R₁ := hH'R₀.trans hR₀R₁
  have hTR₁ : T ≤ R₁ := hTR₀.trans hR₀R₁
  have hR₁C : R₁ ⊓ centralizer (V : Set G) = cj c⁻¹ H :=
    eq_of_sylow_le hsyl' inf_le_right (le_inf hH'R₁ hH'C) (hR₁.isPGroup.to_le inf_le_left)
  have hforw : ∀ r ∈ R₁, ∀ g ∈ cj c⁻¹ H, r * g * r⁻¹ ∈ cj c⁻¹ H := by
    intro r hr g hg
    have hg' : g ∈ R₁ ⊓ centralizer (V : Set G) := by rw [hR₁C]; exact hg
    rw [← hR₁C]
    exact ⟨R₁.mul_mem (R₁.mul_mem hr hg'.1) (R₁.inv_mem hr),
      conj_mem_cent (hR₁.le hr) hg'.2⟩
  have hR₁B : ∀ r ∈ R₁, r ∈ Bb V (cj c⁻¹ H) := by
    intro r hr
    refine ⟨hR₁.le hr, ?_⟩
    show r ∈ normalizer ((cj c⁻¹ H : Subgroup G) : Set G)
    rw [mem_normalizer_iff]
    intro g
    refine ⟨hforw r hr g, fun hg => ?_⟩
    have := hforw r⁻¹ (R₁.inv_mem hr) _ hg
    have e : r⁻¹ * (r * g * r⁻¹) * r⁻¹⁻¹ = g := by group
    rw [e] at this
    exact this
  have hTeq : R₁ ⊓ centralizer ({x} : Set G) = T :=
    eq_of_sylow_le hout.T_sylow inf_le_right (le_inf hTR₁ hout.T_sylow.1)
      (hR₁.isPGroup.to_le inf_le_left)
  have hR₁eq : R₁ = cj c⁻¹ H ⊔ T := by
    apply le_antisymm
    · intro p hp
      obtain ⟨h, hh, hbx⟩ := hcov' p (hR₁B p hp)
      have hp' : h⁻¹ * p ∈ R₁ ⊓ centralizer ({x} : Set G) := by
        refine ⟨R₁.mul_mem (R₁.inv_mem (hH'R₁ hh)) hp, ?_⟩
        show h⁻¹ * p ∈ centralizer ({x} : Set G)
        rw [mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have e : (h⁻¹ * p) * x * (h⁻¹ * p)⁻¹ = x := by
          calc (h⁻¹ * p) * x * (h⁻¹ * p)⁻¹ = h⁻¹ * (p * x * p⁻¹) * h := by group
            _ = h⁻¹ * (h * x * h⁻¹) * h := by rw [hbx]
            _ = x := by group
        exact (mul_inv_eq_iff_eq_mul.1 e).symm
      rw [hTeq] at hp'
      have : p = h * (h⁻¹ * p) := by group
      rw [this]
      exact (cj c⁻¹ H ⊔ T).mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hp')
    · exact sup_le hH'R₁ hTR₁
  refine ⟨hEH', hTnorm, hTinter, ?_, ?_, hElt⟩
  · rw [← hR₁eq]
    exact hR₁
  · rw [← hR₁eq]
    have h6 := relIndex_dvd_six hout.V_four.2 (fun r hr => (hR₁.le hr : r ∈ normalizer (V : Set G)))
    rw [inf_comm, hR₁C] at h6
    have hc1 := relIndex_mul_card (cj c⁻¹ H) R₁
    rw [inf_of_le_left hH'R₁] at hc1
    obtain ⟨e, he⟩ := hR₁.isPGroup.exists_card_eq
    have hd2 : (cj c⁻¹ H).relIndex R₁ ∣ 2 ^ e := by
      rw [← he, ← hc1]
      exact Dvd.intro _ rfl
    have hcop : Nat.Coprime ((cj c⁻¹ H).relIndex R₁) 3 :=
      Nat.Coprime.coprime_dvd_left hd2 (Nat.Coprime.pow_left e (by norm_num))
    have h2 : (cj c⁻¹ H).relIndex R₁ ∣ 2 := hcop.dvd_of_dvd_mul_right (by simpa using h6)
    exact Nat.le_of_dvd (by norm_num) h2

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
