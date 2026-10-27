module

public import CFSG.GH74.KGroups.TwoA7Cover
public import CFSG.GH74.GLS.Stage1.Thm6.Prelude
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Uniqueness.SU.SU13TA1Invol

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Equiv Equiv.Perm Subgroup CFSG.ClassicalInvolution.Hat2A7
  CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.KGroups.TwoA7

theorem not_sylow_of_twisted {E : Type} [Group E] [Finite E] (φ : MulAut E) {z : E} (hz1 : z ≠ 1)
    (hz2 : z * z = 1) (hzc : ∀ x : E, x * z = z * x) {w₀ : E} (hw₀ : φ w₀ = z * w₀)
    {P : Subgroup E} (hP : CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In P ⊤) (hfix : ∀ p ∈ P, φ p = p) :
    False := by
  classical
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hz' : ∀ x y : E, x * (z * y) = z * (x * y) := fun x y => by
    rw [← mul_assoc, hzc x, mul_assoc]
  let X : Subgroup E :=
    { carrier := {x | φ x = x ∨ φ x = z * x}
      one_mem' := Or.inl (map_one φ)
      mul_mem' := fun {a b} ha hb => by
        show φ (a * b) = a * b ∨ φ (a * b) = z * (a * b)
        rw [map_mul]
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
        · exact Or.inl rfl
        · exact Or.inr (hz' a b)
        · exact Or.inr (mul_assoc z a b)
        · left
          rw [mul_assoc, hz' a b, ← mul_assoc, hz2, one_mul]
      inv_mem' := fun {a} ha => by
        show φ a⁻¹ = a⁻¹ ∨ φ a⁻¹ = z * a⁻¹
        rw [map_inv]
        rcases ha with ha | ha
        · exact Or.inl (by rw [ha])
        · right
          rw [ha, mul_inv_rev, hzi]
          exact (hzc a⁻¹) }
  let F : Subgroup E :=
    { carrier := {x | φ x = x}
      one_mem' := map_one φ
      mul_mem' := fun {a b} ha hb => by
        show φ (a * b) = a * b
        rw [map_mul, show φ a = a from ha, show φ b = b from hb]
      inv_mem' := fun {a} ha => by
        show φ a⁻¹ = a⁻¹
        rw [map_inv, show φ a = a from ha] }
  have hFX : F ≤ X := fun x hx => Or.inl hx
  have hPF : P ≤ F := fun p hp => hfix p hp
  have hw₀X : w₀ ∈ X := Or.inr hw₀
  have hzne : ∀ x : E, z * x ≠ x := fun x h => hz1 (by
    have := congrArg (fun y => y * x⁻¹) h
    simpa using this)
  have hindex : (F.subgroupOf X).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨w₀, hw₀X⟩, ?_⟩
    rintro ⟨b, hbX⟩
    have hcoe : ((⟨b, hbX⟩ * ⟨w₀, hw₀X⟩ : ↥X) : E) = b * w₀ := rfl
    by_cases hbF : b ∈ F
    · right
      refine ⟨Subgroup.mem_subgroupOf.2 hbF, fun hbw => ?_⟩
      have hbw' : b * w₀ ∈ F := by
        have := Subgroup.mem_subgroupOf.1 hbw
        rwa [hcoe] at this
      have h1 : φ (b * w₀) = b * w₀ := hbw'
      have h2 : φ b = b := hbF
      rw [map_mul, h2, hw₀, hz' b w₀] at h1
      exact hzne _ h1
    · left
      have hφb : φ b = z * b := by
        rcases hbX with h | h
        · exact absurd h hbF
        · exact h
      refine ⟨?_, fun h => hbF (Subgroup.mem_subgroupOf.1 h)⟩
      apply Subgroup.mem_subgroupOf.2
      rw [hcoe]
      show φ (b * w₀) = b * w₀
      rw [map_mul, hφb, hw₀, mul_assoc, hz' b w₀, ← mul_assoc, hz2, one_mul]
  have h1 : F.relIndex X * X.index = F.index := Subgroup.relIndex_mul_index hFX
  have h2 : P.relIndex F * F.index = P.index := Subgroup.relIndex_mul_index hPF
  have h3 : 2 ∣ F.relIndex X := by rw [Subgroup.relIndex, hindex]
  apply hP.2.2
  rw [Subgroup.relIndex_top_right, ← h2, ← h1]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h3 _) _

theorem swap_four_identity {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    swap a c * swap c b * (swap d a * swap b d) = swap a d * swap b c := by
  ext x
  simp only [Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem nodup_four {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : [a, b, c, d].Nodup := by
  simp [List.nodup_cons, hab, hac, had, hbc, hbd, hcd]

theorem exists_even_comm_cycleType_two_two {σ : Perm (Fin 7)} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ∃ ĥ : Perm (Fin 7), Perm.sign ĥ = 1 ∧ (ĥ * σ * ĥ⁻¹ * σ⁻¹).cycleType = {2, 2} := by
  classical
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : Perm (Fin 7) => τ x) hσ2
    simpa using this
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (Equiv.ext hcon)
  obtain ⟨b, hb⟩ : ∃ b, σ a = b := ⟨_, rfl⟩
  have hab : a ≠ b := by
    rw [← hb]
    exact ha.symm
  have hba : σ b = a := by rw [← hb, hσσ]
  by_cases hc : ∃ c, c ≠ a ∧ c ≠ b ∧ σ c ≠ c
  · obtain ⟨c, hca, hcb, hcσ⟩ := hc
    obtain ⟨d, hd⟩ : ∃ d, σ c = d := ⟨_, rfl⟩
    have hdc : σ d = c := by rw [← hd, hσσ]
    have hcd : c ≠ d := by
      rw [← hd]
      exact hcσ.symm
    have hda : d ≠ a := fun h => hcb (by rw [← hdc, h, hb])
    have hdb : d ≠ b := fun h => hca (by rw [← hdc, h, hba])
    refine ⟨swap a c * swap c b, ?_, ?_⟩
    · rw [map_mul, sign_swap hca.symm, sign_swap hcb]
      decide
    · have h1 : σ * (swap a c * swap c b) * σ⁻¹ = swap b d * swap d a := by
        calc σ * (swap a c * swap c b) * σ⁻¹ = (σ * swap a c * σ⁻¹) * (σ * swap c b * σ⁻¹) := by
              group
          _ = swap (σ a) (σ c) * swap (σ c) (σ b) := by
              rw [← swap_apply_apply, ← swap_apply_apply]
          _ = swap b d * swap d a := by rw [hb, hd, hba]
      have h2 : (swap a c * swap c b) * σ * (swap a c * swap c b)⁻¹ * σ⁻¹ =
          swap a d * swap b c := by
        calc (swap a c * swap c b) * σ * (swap a c * swap c b)⁻¹ * σ⁻¹
            = (swap a c * swap c b) * (σ * (swap a c * swap c b) * σ⁻¹)⁻¹ := by group
          _ = (swap a c * swap c b) * (swap b d * swap d a)⁻¹ := by rw [h1]
          _ = swap a c * swap c b * (swap d a * swap b d) := by
              rw [mul_inv_rev, swap_inv, swap_inv]
          _ = swap a d * swap b c :=
              swap_four_identity hab hca.symm hda.symm hcb.symm hdb.symm hcd
      rw [h2]
      exact cycleType_swap_mul_swap_of_nodup
        (nodup_four hda.symm hab hca.symm hdb hcd.symm hcb.symm)
  · push Not at hc
    have hσs : σ = swap a b := by
      ext x
      by_cases hxa : x = a
      · rw [hxa, hb, swap_apply_left]
      · by_cases hxb : x = b
        · rw [hxb, hba, swap_apply_right]
        · rw [hc x hxa hxb, swap_apply_of_ne_of_ne hxa hxb]
    obtain ⟨c, d, hcd, hca, hcb, hda, hdb⟩ : ∃ c d : Fin 7, c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b := by
      have key : ∀ a b : Fin 7, a ≠ b →
          ∃ c d : Fin 7, c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b := by decide
      exact key a b hab
    refine ⟨swap a c * swap b d, ?_, ?_⟩
    · rw [map_mul, sign_swap hca.symm, sign_swap hdb.symm]
      decide
    · have hĥa : (swap a c * swap b d) a = c := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab hda.symm, swap_apply_left]
      have hĥb : (swap a c * swap b d) b = d := by
        rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hda hcd.symm]
      have h2 : (swap a c * swap b d) * σ * (swap a c * swap b d)⁻¹ * σ⁻¹ =
          swap c d * swap a b := by
        calc (swap a c * swap b d) * σ * (swap a c * swap b d)⁻¹ * σ⁻¹
            = ((swap a c * swap b d) * swap a b * (swap a c * swap b d)⁻¹) * σ⁻¹ := by rw [hσs]
          _ = swap ((swap a c * swap b d) a) ((swap a c * swap b d) b) * σ⁻¹ := by
              rw [swap_apply_apply]
          _ = swap c d * swap a b := by rw [hĥa, hĥb, hσinv, hσs]
      rw [h2]
      exact cycleType_swap_mul_swap_of_nodup (nodup_four hcd hca hcb hda hdb hab)

theorem twoCover_of_isDoubleCoverA7 {E : Type} [Group E] {π : E →* alternatingGroup (Fin 7)}
    {z : E} (h : IsDoubleCoverA7 π z) : TwoCover π where
  surj := h.surjective
  ker_le_center := fun x hx => by
    rw [MonoidHom.mem_ker] at hx
    rcases (h.ker_iff x).1 hx with rfl | rfl
    · exact one_mem _
    · rw [Subgroup.mem_center_iff]
      exact fun g => h.central g
  card_ker := h.card_ker
  perfect := h.perfect

theorem a7_phi_moves_sylow {E : Type} [Group E] [Finite E] {π : E →* alternatingGroup (Fin 7)}
    {z : E} (h : IsDoubleCoverA7 π z) (φ : MulAut E) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    {P : Subgroup E} (hP : CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In P ⊤) : ∃ p ∈ P, φ p ≠ p := by
  by_contra hfix
  push Not at hfix
  have hπ : TwoCover π := twoCover_of_isDoubleCoverA7 h
  set σ : Perm (Fin 7) := h.autPerm φ with hσ
  have hσ2 : σ * σ = 1 := by rw [hσ, ← map_mul, hφ2, map_one]
  have hσ1 : σ ≠ 1 := fun h1 => hφ1 (h.autPerm_injective (by rw [← hσ, h1, map_one]))
  obtain ⟨ĥ, hsign, hct⟩ := exists_even_comm_cycleType_two_two hσ2 hσ1
  obtain ⟨h₀, hh₀⟩ := h.surjective ⟨ĥ, Perm.mem_alternatingGroup.2 hsign⟩
  have hπh₀ : ((π h₀ : alternatingGroup (Fin 7)) : Perm (Fin 7)) = ĥ := by rw [hh₀]
  set w₀ : E := h₀ * (φ h₀)⁻¹ with hw₀
  have hπw : ((π w₀ : alternatingGroup (Fin 7)) : Perm (Fin 7)) = ĥ * σ * ĥ⁻¹ * σ⁻¹ := by
    rw [hw₀, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, h.autPerm_spec φ h₀, hπh₀]
    simp only [hσ]
    group
  have hw2 : w₀ ^ 2 = z := by
    obtain ⟨hk, h1⟩ := hπ.sq_mem_ker_ne_one_of_cycleType_two_two (by norm_num) (x := w₀)
      (by rw [hπw]; exact hct)
    rcases (h.ker_iff _).1 hk with h2 | h2
    · exact absurd h2 h1
    · exact h2
  have hww : w₀ * w₀ = z := by rw [← pow_two]; exact hw2
  have hφφ : φ (φ h₀) = h₀ := by
    have := congrArg (fun ρ : MulAut E => ρ h₀) hφ2
    simpa using this
  have hφw : φ w₀ = z * w₀ := by
    have h1 : φ w₀ = w₀⁻¹ := by
      rw [hw₀, map_mul, map_inv, hφφ]
      group
    rw [h1]
    have h2 : w₀⁻¹ = z⁻¹ * w₀ := by
      rw [← hww]
      group
    rw [h2, inv_eq_of_mul_eq_one_right h.sq_eq_one]
  exact not_sylow_of_twisted φ h.ne_one h.sq_eq_one h.central hφw hP hfix

end CFSG.GH74.GLS.IVK.Lifted
