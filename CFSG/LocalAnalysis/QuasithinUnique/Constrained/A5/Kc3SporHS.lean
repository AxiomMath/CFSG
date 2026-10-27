module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporHSLoc
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Abs
public import CFSG.Sporadic.Schreier.PairHSOrder
public import Certificates.Certificate4062

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporHS

open CFSG.QuasithinUnique.Unc25G2.M2x CFSG.Sporadic.Schreier CFSG.QuasithinUnique.A5

@[expose] noncomputable def fixP (x : ↥hsP) : ℕ :=
  (Finset.univ.filter fun p : Fin 3850 => ((x : ↥hsP) : Equiv.Perm (Fin 3850)) p = p).card

theorem fixP_conj (g x : ↥hsP) : fixP (g * x * g⁻¹) = fixP x := by
  unfold fixP
  set σ : Equiv.Perm (Fin 3850) := (g : Equiv.Perm (Fin 3850))
  set τ : Equiv.Perm (Fin 3850) := (x : Equiv.Perm (Fin 3850))
  have e : ((g * x * g⁻¹ : ↥hsP) : Equiv.Perm (Fin 3850)) = σ * τ * σ⁻¹ := by simp [σ, τ]
  rw [e]
  refine Finset.card_bij' (fun p _ => σ⁻¹ p) (fun q _ => σ q) ?_ ?_ ?_ ?_
  · intro p hp
    have h := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def] at h
    have h2 := congrArg σ.symm h
    rw [Equiv.symm_apply_apply] at h2
    rw [Equiv.Perm.inv_def]
    exact h2
  · intro q hq
    have h := (Finset.mem_filter.1 hq).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, h]
  · intro p _
    simp
  · intro q _
    simp

theorem hs_e16 :
    ∃ (R : Subgroup ↥hsP) (Ek : ℕ → Subgroup ↥hsP), Nat.card R = 512 ∧
      ∀ E : Subgroup ↥hsP, E ≤ R → ElemAb E → Nat.card E = 16 → ∃ k < 8, E = Ek k := by
  obtain ⟨R, hR, E₀, Ek, hD, hcls⟩ := Certificates.certificate4062
  exact ⟨R, Ek, hR, fun E hER hE hcard => (hcls E hER hE.1 hE.2 hcard).1⟩

theorem map_conj_cancel {K : Type} [Group K] (E : Subgroup K) (g : K) :
    (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = E := by
  rw [Subgroup.map_map]
  have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id K := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      MonoidHom.id_apply]
    group
  rw [this, Subgroup.map_id]

theorem map_conj_mul {K : Type} [Group K] (E : Subgroup K) (g r : K) :
    (E.map (MulAut.conj r).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      E.map (MulAut.conj (g * r)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem locClass2_hsP
    : LocClass2 ↥hsP := by
  classical
  intro E β hact
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (comm_of_beta β ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    have h1 : β (⟨x, hx⟩ * ⟨x, hx⟩) = β 1 := by
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      exact Kc3L3.add_self_evenWeight _
    have h2 := β.injective h1
    exact congrArg Subtype.val h2
  have hcard : Nat.card E = 16 := by
    rw [Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.toAdd]
    exact CFSG.QuasithinUnique.AppC.card_evenWeight
  obtain ⟨R, hcardR, E₀, Ek, hD, hclass⟩ := Certificates.certificate4062
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 9) (by rw [hcardR]; norm_num)
  have hidx : ¬ 2 ∣ R.index := by
    have h := R.card_mul_index
    rw [hcardR, card_hsP] at h
    omega
  let S : Sylow 2 ↥hsP := IsPGroup.toSylow hR2 hidx
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  obtain ⟨P, hEP⟩ := hE2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥hsP S P
  have hPR : (P : Subgroup ↥hsP) = R.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Subgroup.toSubmonoid_inj.mp rfl
  have hE'R : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : x ∈ (P : Subgroup ↥hsP) := hEP hx
    rw [hPR] at hxP
    obtain ⟨r', hr', rfl⟩ := hxP
    have e : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom r') = r' := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e]
    exact hr'
  have hE'ab : ElemAb (E.map (MulAut.conj g⁻¹).toMonoidHom) := ElemAb.map (MulAut.conj g⁻¹)
    ⟨hcomm, hsq⟩
  have hE'card : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  have hact' := Delta5Norm.map (MulAut.conj g⁻¹) hact
  have hback : (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = E :=
    map_conj_cancel E g
  rcases (hclass _ hE'R hE'ab.1 hE'ab.2 hE'card).2 with hfib | ⟨r, hr⟩
  · exact (not_delta5Norm_of_cls fixP fixP_conj hfib _ hact').elim
  · refine ⟨E₀, g * r, Or.inr (Or.inl hD), ?_⟩
    rw [← map_conj_mul, ← hr, hback]

noncomputable def hsEquiv
    : CFSG.Blueprint.NativeSporadic.Carrier .HS ≃* ↥hsP := hsPermEquiv

end CFSG.QuasithinUnique.A5.Kc3SporHS

namespace CFSG.QuasithinUnique.A5

theorem kc3LocalFor_hs
    : Kc3LocalFor (Kc3Spor .HS) := by
  intro X _ _ ⟨e⟩
  exact kc3LocalData_of_locClass2
    (LocClass2.of_equiv (e.trans Kc3SporHS.hsEquiv) Kc3SporHS.locClass2_hsP)

theorem kc3For_hs
    : Kc3For (Kc3Spor .HS) :=
  kc3For_of_localFor (isoInv_spor .HS) kc3LocalFor_hs

end CFSG.QuasithinUnique.A5
