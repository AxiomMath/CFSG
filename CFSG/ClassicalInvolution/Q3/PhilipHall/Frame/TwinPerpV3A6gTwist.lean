module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eIdent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG CFSG.Open
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
  (aeBar8 vq vq_mul vq_eq_iff conj_vq vq_inv vq_empty E8Pkg)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
  (conjSub_ofPerm_memBar conjSub_ofPerm_ae6AE8 mkQ_ofPerm_inv card_map_perm)
open scoped commutatorElement

section Twist

variable {Y : Type} [Group Y]

@[expose] noncomputable def twistHom (ψ : Equiv.Perm (Fin 8)) : AEQ 8 →* AEQ 8 :=
  (MulAut.conj (mkQ 8 (ofPerm ψ))).toMonoidHom

theorem twistHom_apply (ψ : Equiv.Perm (Fin 8)) (g : AEQ 8) :
    twistHom ψ g = mkQ 8 (ofPerm ψ) * g * (mkQ 8 (ofPerm ψ))⁻¹ := rfl

theorem twistHom_injective (ψ : Equiv.Perm (Fin 8)) : Function.Injective (twistHom ψ) :=
  (MulAut.conj (mkQ 8 (ofPerm ψ))).injective

theorem map_twistHom (ψ : Equiv.Perm (Fin 8)) (H : Subgroup (AEQ 8)) :
    H.map (twistHom ψ) = conjSub (mkQ 8 (ofPerm ψ)) H := rfl

@[expose] noncomputable def _root_.CFSG.ClassicalInvolution.Q3.TC.Thin.AEIdent.twist {P : Set (Subgroup Y)}
    (A : AEIdent P 8) (ψ : Equiv.Perm (Fin 8)) : AEIdent P 8 where
  φ := (twistHom ψ).comp A.φ
  range_eq := by
    rw [MonoidHom.range_comp, A.range_eq]
    exact conjSub_ofPerm_ae6AE8 ψ
  ker_le := by
    intro x hx
    rw [MonoidHom.ker_comp_of_injective _ _ (twistHom_injective ψ)] at hx
    exact A.ker_le hx
  label := by
    intro L hL
    obtain ⟨α, h, b, hlab⟩ := A.label L hL
    obtain ⟨b', hb'⟩ := conjSub_ofPerm_memBar ψ h b
    refine ⟨α.map ψ.toEmbedding, card_map_perm ψ h, b', ?_⟩
    rw [← Subgroup.map_map, hlab]
    exact hb'
  label_surj := by
    intro α h b
    obtain ⟨b', hb'⟩ := conjSub_ofPerm_memBar ψ⁻¹ h b
    obtain ⟨L, hL, hlab⟩ := A.label_surj (α.map ψ⁻¹.toEmbedding) (card_map_perm ψ⁻¹ h) b'
    refine ⟨L, hL, ?_⟩
    rw [← Subgroup.map_map, hlab, map_twistHom, ← hb', ← mkQ_ofPerm_inv]
    exact conjSub_conjSub_inv _ _

theorem twist_ker {P : Set (Subgroup Y)} (A : AEIdent P 8) (ψ : Equiv.Perm (Fin 8)) :
    (A.twist ψ).φ.ker = A.φ.ker :=
  MonoidHom.ker_comp_of_injective _ _ (twistHom_injective ψ)

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e (aeIdent_inj aeIdent_range aeIdent_mem_D E8Lab)

@[expose] noncomputable def pkgOf [Finite Y] {P : Set (Subgroup Y)} (A : AEIdent P 8)
    {I D : Subgroup Y} (hpI : pSpan P = I) (hker : A.φ.ker = ⊥) (hD : pCoreOf 2 I = D) :
    E8Pkg I D where
  φ := A.φ.comp (Subgroup.inclusion hpI.symm.le)
  inj := aeIdent_inj A hpI hker
  range_eq := aeIdent_range A hpI
  le := by
    rw [← hD]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 I
  mem_D := fun x => by
    rw [← hD]
    exact aeIdent_mem_D A hpI hker x

theorem e8Lab_pkgOf [Finite Y] {P : Set (Subgroup Y)} (A : AEIdent P 8) {I D : Subgroup Y}
    (hpI : pSpan P = I) (hker : A.φ.ker = ⊥) (hD : pCoreOf 2 I = D) :
    E8Lab (pkgOf A hpI hker hD) P := by
  subst hpI
  intro L hL
  obtain ⟨α, h, b, hlab⟩ := A.label L hL
  refine ⟨α, h, b, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [← hlab]
    exact A.mem_map hL hx
  · have hx' : A.φ x ∈ (L.subgroupOf (pSpan P)).map A.φ := by rw [hlab]; exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have h1 : Function.Injective A.φ := (MonoidHom.ker_eq_bot_iff _).mp hker
    have : y = x := h1 hyx
    rw [← this]
    exact Subgroup.mem_subgroupOf.mp hy

theorem ph_twist [Finite Y] {P : Set (Subgroup Y)} (A : AEIdent P 8) {I D : Subgroup Y}
    (hpI : pSpan P = I) (hker : A.φ.ker = ⊥) (hD : pCoreOf 2 I = D) (ψ : Equiv.Perm (Fin 8))
    (g : Y) :
    (pkgOf (A.twist ψ) hpI (by rw [twist_ker]; exact hker) hD).ph g =
      twistHom ψ ((pkgOf A hpI hker hD).ph g) := by
  unfold E8Pkg.ph
  by_cases h : g ∈ I
  · simp only [dif_pos h]
    rfl
  · simp only [dif_neg h]
    exact (map_one _).symm

theorem twistHom_vq (ψ : Equiv.Perm (Fin 8)) (S : Finset (Fin 8)) :
    twistHom ψ (vq S) = vq (S.map ψ.toEmbedding) := by
  rw [twistHom_apply, conj_vq]
  rfl

theorem permQ_twistHom (ψ : Equiv.Perm (Fin 8)) (g : AEQ 8) :
    permQ 8 (twistHom ψ g) = ψ * permQ 8 g * ψ⁻¹ := by
  rw [twistHom_apply, map_mul, map_mul, map_inv]
  rfl

theorem map_perm_map_inv (ψ : Equiv.Perm (Fin 8)) (S : Finset (Fin 8)) :
    (S.map ψ.toEmbedding).map ψ⁻¹.toEmbedding = S := by
  ext z
  simp [Finset.mem_map_equiv, Equiv.Perm.inv_def]

end Twist

section Cells

@[expose] def cellOf (a β : Finset (Fin 8)) (z : Fin 8) : ℕ :=
  (if z ∈ a then 0 else 2) + (if z ∈ β then 0 else 1)

theorem exists_perm_std {a β : Finset (Fin 8)} {σ : Equiv.Perm (Fin 8)} (ha : a.card = 4)
    (hβ : β.card = 4) (hab : (a ∩ β).card = 2) (hσσ : ∀ z, σ (σ z) = z) (hfix : ∀ z, σ z ≠ z)
    (hpa : ∀ z, σ z ∈ a ↔ z ∈ a) (hpb : ∀ z, σ z ∈ β ↔ z ∈ β) :
    ∃ ψ : Equiv.Perm (Fin 8), α₀.map ψ.toEmbedding = a ∧ β₀.map ψ.toEmbedding = β ∧
      ψ * σ₀ = σ * ψ := by
  classical
  have hc1 : (a ∩ β).card = 2 := hab
  have hc2 : (a \ β).card = 2 := by
    have := Finset.card_sdiff_add_card_inter a β
    omega
  have hc3 : (β \ a).card = 2 := by
    have := Finset.card_sdiff_add_card_inter β a
    rw [Finset.inter_comm] at this
    omega
  have hc4 : (aᶜ ∩ βᶜ).card = 2 := by
    have h1 : (aᶜ ∩ βᶜ) = (a ∪ β)ᶜ := by ext z; simp
    have h2 : (a ∪ β).card = 6 := by
      have := Finset.card_union_add_card_inter a β
      omega
    rw [h1, Finset.card_compl, h2]
    simp
  obtain ⟨p₁, hp₁⟩ : (a ∩ β).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₂, hp₂⟩ : (a \ β).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₃, hp₃⟩ : (β \ a).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₄, hp₄⟩ : (aᶜ ∩ βᶜ).Nonempty := Finset.card_pos.mp (by omega)
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_compl] at hp₁ hp₂ hp₃ hp₄
  set f : Fin 8 → Fin 8 := ![p₁, σ p₁, p₂, σ p₂, p₃, σ p₃, p₄, σ p₄] with hf
  have hcell : ∀ i : Fin 8, cellOf a β (f i) = i.val / 2 := by
    intro i
    fin_cases i <;>
      simp [hf, cellOf, hpa, hpb, hp₁.1, hp₁.2, hp₂.1, hp₂.2, hp₃.1, hp₃.2, hp₄.1, hp₄.2]
  have hinj : Function.Injective f := by
    intro i j h
    have e : i.val / 2 = j.val / 2 := by rw [← hcell i, ← hcell j, h]
    fin_cases i <;> fin_cases j <;> simp at e ⊢ <;> simp [hf] at h <;>
      first
      | exact absurd h.symm (hfix _)
      | exact absurd h (hfix _)
  have hbij : Function.Bijective f := ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  set ψ : Equiv.Perm (Fin 8) := Equiv.ofBijective f hbij with hψ
  have hψf : ∀ i, ψ i = f i := fun i => rfl
  refine ⟨ψ, ?_, ?_, ?_⟩
  · refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) (le_of_eq (by rw [Finset.card_map, ha, card_α₀]))
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
    have : i ∈ α₀ := hi
    simp only [α₀, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [hψf, hf, hp₁.1, hp₂.1, (hpa _).mpr hp₁.1, (hpa _).mpr hp₂.1]
  · refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) (le_of_eq (by rw [Finset.card_map, hβ, card_β₀]))
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
    have : i ∈ β₀ := hi
    simp only [β₀, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [hψf, hf, hp₁.2, hp₃.1, (hpb _).mpr hp₁.2, (hpb _).mpr hp₃.1]
  · apply Equiv.ext
    intro z
    have hσ₀ := σ₀_apply z
    show ψ (σ₀ z) = σ (ψ z)
    rw [hσ₀]
    fin_cases z <;> simp [hψf, hf, hσσ]

end Cells

section Comm

variable {Y : Type} [Group Y] {I D : Subgroup Y}

theorem map_rho_eq_of_mem_comm (P : E8Pkg I D) {x τ : Y} (hx : x ∈ I) (hxx : x * x = 1)
    (hτ : τ ∈ ⁅D, Subgroup.zpowers x⁆) {β : Finset (Fin 8)} (hβ : P.ph τ = vq β) :
    β.map (P.rho x).toEmbedding = β := by
  set π := P.rho x with hπdef
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  let U : Subgroup Y :=
    { carrier := {g | g ∈ D ∧ ∃ T : Finset (Fin 8), T.map π.toEmbedding = T ∧ P.ph g = vq T}
      mul_mem' := by
        rintro g g' ⟨hg, T, hT, hgT⟩ ⟨hg', T', hT', hgT'⟩
        refine ⟨D.mul_mem hg hg', symmDiff T T', ?_, ?_⟩
        · ext z
          have h1 := Finset.ext_iff.mp hT z
          have h2 := Finset.ext_iff.mp hT' z
          simp only [Finset.mem_map_equiv] at h1 h2 ⊢
          simp only [Finset.mem_symmDiff, h1, h2]
        · rw [P.ph_mul (P.le hg) (P.le hg'), hgT, hgT', vq_mul]
      one_mem' := ⟨D.one_mem, ∅, by simp, by rw [P.ph_one, vq_empty]⟩
      inv_mem' := by
        rintro g ⟨hg, T, hT, hgT⟩
        exact ⟨D.inv_mem hg, T, hT, by rw [P.ph_inv (P.le hg), hgT, vq_inv]⟩ }
  have hcomm : ⁅D, Subgroup.zpowers x⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro d hd g' hg'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
    have hxo : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hxx]
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · have : x ^ k = 1 := by rw [hm, zpow_mul, hxo, one_zpow]
      rw [this, commutatorElement_one_right]
      exact U.one_mem
    · have : x ^ k = x := by
        rw [hm, zpow_add, zpow_mul, hxo, one_zpow, one_mul, zpow_one]
      rw [this]
      have hdI := P.le hd
      have hcD : ⁅d, x⁆ ∈ D := by
        rw [commutatorElement_def]
        have h1 := P.conj_mem_D hx (D.inv_mem hd)
        have := D.mul_mem hd h1
        simpa [mul_assoc] using this
      obtain ⟨S, -, hS⟩ := P.vec_of_mem_D hd
      refine ⟨hcD, symmDiff S (S.map π.toEmbedding), ?_, ?_⟩
      · ext z
        simp only [Finset.mem_map_equiv, Finset.mem_symmDiff]
        have hππ : π * π = 1 := by rw [hπdef, ← P.rho_mul hx hx, hxx, P.rho_one]
        have hπinv : π.symm = π := by
          have := inv_eq_of_mul_eq_one_right hππ
          rwa [Equiv.Perm.inv_def] at this
        have h2 : ∀ w, π.symm (π.symm w) = w := fun w => by
          rw [hπinv]
          have := congrArg (fun σ : Equiv.Perm (Fin 8) => σ w) hππ
          simpa [Equiv.Perm.mul_apply] using this
        rw [h2]
        tauto
      · have hdx : P.ph ⁅d, x⁆ = P.ph d * P.ph x * (P.ph d)⁻¹ * (P.ph x)⁻¹ := by
          rw [commutatorElement_def,
            P.ph_mul (I.mul_mem (I.mul_mem hdI hx) (I.inv_mem hdI)) (I.inv_mem hx),
            P.ph_mul (I.mul_mem hdI hx) (I.inv_mem hdI), P.ph_mul hdI hx, P.ph_inv hdI, P.ph_inv hx]
        rw [hdx, hS, vq_inv]
        have e : vq S * P.ph x * vq S * (P.ph x)⁻¹ = vq S * (P.ph x * vq S * (P.ph x)⁻¹) := by group
        rw [e, conj_vq, vq_mul]
        rfl
  obtain ⟨-, T, hT, hτT⟩ := hcomm hτ
  have hvT : vq T = vq β := hτT.symm.trans hβ
  rcases vq_eq_iff.mp hvT with h | h
  · rw [h]
    exact hT
  ·
    have hβT : β = Tᶜ := h
    ext z
    have h1 := Finset.ext_iff.mp hT (π.symm z)
    simp only [Finset.mem_map_equiv] at h1 ⊢
    rw [hβT]
    simp only [Finset.mem_compl]
    have h2 := Finset.ext_iff.mp hT z
    simp only [Finset.mem_map_equiv] at h2
    rw [h2]

end Comm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
