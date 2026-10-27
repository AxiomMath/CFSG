module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ePkg

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr
open Finset
open scoped commutatorElement

theorem vf_const (e : ZMod 2) : mkQ 8 (ofVec (fun _ : Fin 8 => e)) = 1 := by
  rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) e with rfl | rfl
  · have : (ofVec (fun _ : Fin 8 => (0 : ZMod 2)) : Wr 8) = 1 := Wr.ext rfl rfl
    rw [this, map_one]
  · have : (ofVec (fun _ : Fin 8 => (1 : ZMod 2)) : Wr 8) = allOnes 8 := Wr.ext rfl rfl
    rw [this]
    exact (QuotientGroup.eq_one_iff _).2 (Or.inr rfl)

theorem vf_smul (c : ZMod 2) (S : Finset (Fin 8)) :
    mkQ 8 (ofVec (fun z => c * ind S z)) = 1 ∨ mkQ 8 (ofVec (fun z => c * ind S z)) = vq S := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · left
    have : (ofVec (fun z => (0 : ZMod 2) * ind S z) : Wr 8) = 1 :=
      Wr.ext (funext fun z => zero_mul _) rfl
    rw [this, map_one]
  · right
    unfold vq
    congr 2
    funext z
    simp

theorem vf_add (v w : Fin 8 → ZMod 2) :
    mkQ 8 (ofVec (v + w)) = mkQ 8 (ofVec v) * mkQ 8 (ofVec w) := by
  rw [← map_mul, ofVec_mul']

theorem vf_comb (A B : Finset (Fin 8)) (c₁ c₂ e : ZMod 2) :
    mkQ 8 (ofVec (fun z => c₁ * ind A z + c₂ * ind B z + e)) = 1 ∨
      mkQ 8 (ofVec (fun z => c₁ * ind A z + c₂ * ind B z + e)) = vq A ∨
      mkQ 8 (ofVec (fun z => c₁ * ind A z + c₂ * ind B z + e)) = vq B ∨
      mkQ 8 (ofVec (fun z => c₁ * ind A z + c₂ * ind B z + e)) = vq A * vq B := by
  have h : (fun z => c₁ * ind A z + c₂ * ind B z + e) =
      (fun z => c₁ * ind A z) + (fun z => c₂ * ind B z) + (fun _ => e) := rfl
  rw [h, vf_add, vf_add, vf_const, mul_one]
  rcases vf_smul c₁ A with h1 | h1 <;> rcases vf_smul c₂ B with h2 | h2 <;> rw [h1, h2] <;> simp

theorem sum_ind (S : Finset (Fin 8)) : ∑ z, ind S z = (S.card : ZMod 2) := by
  unfold ind
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp

theorem sum_ind_eq_zero {S : Finset (Fin 8)} (hS : Even S.card) : ∑ z, ind S z = 0 := by
  rw [sum_ind]
  exact (ZMod.natCast_eq_zero_iff_even).mpr hS

@[expose] def pull (g : Equiv.Perm (Fin 8)) (T : Finset (Fin 8)) : Finset (Fin 8) :=
  T.map g.symm.toEmbedding

theorem mem_pull {g : Equiv.Perm (Fin 8)} {T : Finset (Fin 8)} {z : Fin 8} :
    z ∈ pull g T ↔ g z ∈ T := by
  unfold pull
  rw [Finset.mem_map_equiv]
  simp

theorem card_pull (g : Equiv.Perm (Fin 8)) (T : Finset (Fin 8)) : (pull g T).card = T.card := by
  unfold pull
  exact Finset.card_map _

theorem ind_pull (g : Equiv.Perm (Fin 8)) (T : Finset (Fin 8)) (z : Fin 8) :
    ind (pull g T) z = ind T (g z) := by
  unfold ind
  simp [mem_pull]

theorem ind_map_perm (π : Equiv.Perm (Fin 8)) (hπ : ∀ z, π (π z) = z) (S : Finset (Fin 8))
    (z : Fin 8) : ind (S.map π.toEmbedding) z = ind S (π z) := by
  unfold ind
  have : π.symm z = π z := by
    apply π.injective
    rw [Equiv.apply_symm_apply, hπ]
  simp [Finset.mem_map_equiv, this]

namespace E8Pkg

variable {Y : Type} [Group Y] {I D : Subgroup Y} (P : E8Pkg I D)

theorem comm_eq {x : Y} {A : Finset (Fin 8)} (hx : x ∈ I) (hxx : x * x = 1) (hA : A.card = 4)
    (hfix : ∀ z, P.rho x z ≠ z) (hpres : ∀ z, P.rho x z ∈ A ↔ z ∈ A) :
    ∃ B : Finset (Fin 8), B.card = 4 ∧ (A ∩ B).card = 2 ∧
      ∀ s₁ ∈ D, ∀ s₂ ∈ D, P.ph s₁ = vq A → P.ph s₂ = vq B →
        ⁅D, Subgroup.zpowers x⁆ = Subgroup.closure ({s₁, s₂} : Set Y) := by
  set π := P.rho x with hπdef
  have hππ : ∀ z, π (π z) = z := by
    intro z
    have h1 : π * π = 1 := by
      rw [hπdef, ← P.rho_mul hx hx, hxx, P.rho_one]
    have := congrArg (fun σ : Equiv.Perm (Fin 8) => σ z) h1
    simpa [Equiv.Perm.mul_apply] using this
  obtain ⟨g, hg, hgA, hgπ⟩ := exists_std hA hππ hfix hpres
  obtain ⟨hca₀, hcB₀, hcab⟩ := a₀_B₀_cross
  set B : Finset (Fin 8) := pull g B₀ with hB
  have hmemA : ∀ z, z ∈ A ↔ g z ∈ a₀ := fun z => (hgA z).symm
  have hBcard : B.card = 4 := by rw [hB, card_pull]; exact hcB₀
  have hABcard : (A ∩ B).card = 2 := by
    have : A ∩ B = pull g (a₀ ∩ B₀) := by
      ext z
      simp [mem_pull, hmemA, hB]
    rw [this, card_pull]
    exact hcab
  refine ⟨B, hBcard, hABcard, fun s₁ hs₁ s₂ hs₂ h₁ h₂ => ?_⟩
  have key : ∀ v : Fin 8 → ZMod 2, ∑ z, v z = 0 →
      ∃ c₁ c₂ e : ZMod 2, ∀ z, v z + v (π z) = c₁ * ind A z + c₂ * ind B z + e := by
    intro v hv
    obtain ⟨c₁, c₂, e, h⟩ := std_comm (fun w => v (g.symm w))
      (by rw [Equiv.sum_comp g.symm v]; exact hv)
    refine ⟨c₁, c₂, e, fun z => ?_⟩
    have h1 := h (g z)
    rw [← hgπ z] at h1
    simp only [Equiv.symm_apply_apply] at h1
    rw [h1]
    have e1 : ind a₀ (g z) = ind A z := by
      unfold ind
      simp [hmemA z]
    have e2 : ind B₀ (g z) = ind B z := by
      rw [hB, ind_pull]
    rw [e1, e2]
  have hcomm : ∀ d ∈ D, ∀ S : Finset (Fin 8), P.ph d = vq S →
      P.ph ⁅d, x⁆ = vq (symmDiff S (S.map π.toEmbedding)) := by
    intro d hd S hS
    have hdI := P.le hd
    have hdx : P.ph ⁅d, x⁆ = P.ph d * P.ph x * (P.ph d)⁻¹ * (P.ph x)⁻¹ := by
      rw [commutatorElement_def,
        P.ph_mul (I.mul_mem (I.mul_mem hdI hx) (I.inv_mem hdI)) (I.inv_mem hx),
        P.ph_mul (I.mul_mem hdI hx) (I.inv_mem hdI), P.ph_mul hdI hx, P.ph_inv hdI, P.ph_inv hx]
    rw [hdx, hS, vq_inv]
    have e : vq S * P.ph x * vq S * (P.ph x)⁻¹ = vq S * (P.ph x * vq S * (P.ph x)⁻¹) := by group
    have hπ' : π = permQ 8 (P.ph x) := rfl
    rw [e, conj_vq, vq_mul, ← hπ']
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hpow : ∀ k : ℤ, x ^ k = 1 ∨ x ^ k = x := by
    intro k
    have hxo : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hxx]
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      rw [hm, zpow_mul, hxo, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, hxo, one_zpow, one_mul, zpow_one]
  have hs₁I : s₁ ∈ I := P.le hs₁
  have hs₂I : s₂ ∈ I := P.le hs₂
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro d hd g' hg'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
    rcases hpow k with hk | hk
    · rw [hk, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rw [hk]
      obtain ⟨S, hSe, hS⟩ := P.vec_of_mem_D hd
      obtain ⟨c₁, c₂, e, hce⟩ := key (ind S) (sum_ind_eq_zero hSe)
      have hph := hcomm d hd S hS
      have hdI := P.le hd
      have hcI : ⁅d, x⁆ ∈ I := by
        rw [commutatorElement_def]
        exact I.mul_mem (I.mul_mem (I.mul_mem hdI hx) (I.inv_mem hdI)) (I.inv_mem hx)
      have hind : ind (symmDiff S (S.map π.toEmbedding)) =
          fun z => c₁ * ind A z + c₂ * ind B z + e := by
        funext z
        rw [ind_symmDiff, ind_map_perm π hππ]
        exact hce z
      have hv : P.ph ⁅d, x⁆ = mkQ 8 (ofVec (fun z => c₁ * ind A z + c₂ * ind B z + e)) := by
        rw [hph]
        unfold vq
        rw [hind]
      rcases vf_comb A B c₁ c₂ e with h | h | h | h
      · have : ⁅d, x⁆ = 1 := P.ph_inj hcI I.one_mem (by rw [hv, h, P.ph_one])
        rw [this]
        exact Subgroup.one_mem _
      · have : ⁅d, x⁆ = s₁ := P.ph_inj hcI hs₁I (by rw [hv, h, h₁])
        rw [this]
        exact Subgroup.subset_closure (by simp)
      · have : ⁅d, x⁆ = s₂ := P.ph_inj hcI hs₂I (by rw [hv, h, h₂])
        rw [this]
        exact Subgroup.subset_closure (by simp)
      · have : ⁅d, x⁆ = s₁ * s₂ :=
          P.ph_inj hcI (I.mul_mem hs₁I hs₂I) (by rw [hv, h, P.ph_mul hs₁I hs₂I, h₁, h₂])
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    have gen1 : ∀ (T : Finset (Fin 8)) (U : Finset (Fin 8)), Even T.card →
        (∀ w, ind T w + ind T (π₀ w) = ind U w) → ∀ s ∈ D, P.ph s = vq (pull g U) →
        s ∈ ⁅D, Subgroup.zpowers x⁆ := by
      intro T U hT hTU s hs hsU
      obtain ⟨d, hd, hdT⟩ := P.exists_vec (S := pull g T)
        (by rw [card_pull]; exact hT)
      have hph := hcomm d hd (pull g T) hdT
      have hdI := P.le hd
      have hcI : ⁅d, x⁆ ∈ I := by
        rw [commutatorElement_def]
        exact I.mul_mem (I.mul_mem (I.mul_mem hdI hx) (I.inv_mem hdI)) (I.inv_mem hx)
      have hind : ind (symmDiff (pull g T) ((pull g T).map π.toEmbedding)) = ind (pull g U) := by
        funext z
        rw [ind_symmDiff, ind_map_perm π hππ, ind_pull, ind_pull, ind_pull, hgπ z]
        exact hTU (g z)
      have : ⁅d, x⁆ = s := by
        apply P.ph_inj hcI (P.le hs)
        rw [hph, hsU]
        unfold vq
        rw [hind]
      rw [← this]
      exact Subgroup.commutator_mem_commutator hd (Subgroup.mem_zpowers x)
    intro s hs
    rcases hs with rfl | hs
    · refine gen1 {0, 2} a₀ (by decide) std_ind_a₀ s hs₁ ?_
      rw [h₁]
      unfold vq
      congr 2
      funext z
      rw [ind_pull]
      unfold ind
      simp [hmemA z]
    · have hs := Set.mem_singleton_iff.mp hs
      subst hs
      refine gen1 {0, 4} B₀ (by decide) std_ind_B₀ s hs₂ ?_
      rw [h₂]

end E8Pkg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
