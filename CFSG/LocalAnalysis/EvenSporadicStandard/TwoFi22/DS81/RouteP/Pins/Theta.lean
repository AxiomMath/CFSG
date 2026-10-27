module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Mog22
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F11.Rigid

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

universe u v

theorem exists_mulEquiv_induced₂ {B B₀ Q : Type*} [Group B] [Group B₀] [Group Q] (π : B →* Q)
    (π₀ : B₀ →* Q) (hπ : Function.Surjective π) (hπ₀ : Function.Surjective π₀) (θ : B ≃* B₀)
    (hθ : ∀ b, π₀ (θ b) = 1 ↔ π b = 1) : ∃ α : Q ≃* Q, ∀ b, α (π b) = π₀ (θ b) := by
  have hker : (π.ker).map (θ : B →* B₀) = π₀.ker := by
    ext x
    have hm : x ∈ (π.ker).map (θ : B →* B₀) ↔ θ.symm x ∈ π.ker :=
      Subgroup.mem_map_equiv
    rw [hm, MonoidHom.mem_ker, MonoidHom.mem_ker, ← hθ (θ.symm x),
      MulEquiv.apply_symm_apply]
  let e : B ⧸ π.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let e₀ : B₀ ⧸ π₀.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective π₀ hπ₀
  refine ⟨e.symm.trans ((QuotientGroup.congr π.ker π₀.ker θ hker).trans e₀), fun b => ?_⟩
  have hb : e (QuotientGroup.mk b) = π b := rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← hb, MulEquiv.symm_apply_apply,
    QuotientGroup.congr_mk]
  rfl

theorem conj_mem_K22_of_mem_duadStabPlus {k q : ↥AutPerm} (hk : k ∈ duadStabPlus 0 1)
    (hq : q ∈ K22) : k * q * k⁻¹ ∈ K22 := by
  rw [mem_K22_iff] at hq ⊢
  obtain ⟨hq0, hq1⟩ := hq
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
  rcases mem_duadStabPlus_iff.1 hk with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have e0 : ((k : ↥AutPerm) : Equiv.Perm (Fin 24))⁻¹ 0 = 0 := by
      rw [Equiv.Perm.inv_eq_iff_eq, h0]
    have e1 : ((k : ↥AutPerm) : Equiv.Perm (Fin 24))⁻¹ 1 = 1 := by
      rw [Equiv.Perm.inv_eq_iff_eq, h1]
    rw [e0, e1, hq0, hq1, h0, h1]
    exact ⟨rfl, rfl⟩
  · have e0 : ((k : ↥AutPerm) : Equiv.Perm (Fin 24))⁻¹ 0 = 1 := by
      rw [Equiv.Perm.inv_eq_iff_eq, h1]
    have e1 : ((k : ↥AutPerm) : Equiv.Perm (Fin 24))⁻¹ 1 = 0 := by
      rw [Equiv.Perm.inv_eq_iff_eq, h0]
    rw [e0, e1, hq0, hq1, h0, h1]
    exact ⟨rfl, rfl⟩

namespace ExtData

section Abstract

variable {M W N N₀ : Type*} [Group M] [CommGroup W] [Group N] [Group N₀] {ρ : M →* MulAut W}

theorem exists_theta_of_aut_preimage (X : ExtData ρ N) (X₀ : ExtData ρ N₀) {K K' : Subgroup M}
    (hnorm : ∀ k' ∈ K', ∀ q ∈ K, k' * q * k'⁻¹ ∈ K)
    (hEnd : ModEquivAutTrivial (ρ.comp K.subtype))
    (hAut : ∀ α : ↥K ≃* ↥K, ∃ k' ∈ K', ∀ q : ↥K, ((α q : ↥K) : M) = k' * (q : M) * k'⁻¹)
    {B : Subgroup N} {B₀ : Subgroup N₀} (hB : ∀ n, n ∈ B ↔ X.π n ∈ K)
    (hB₀ : ∀ n, n ∈ B₀ ↔ X₀.π n ∈ K) (θ₁ : ↥B ≃* ↥B₀)
    (hθ₁ : ∀ b : ↥B, X₀.π (θ₁ b) = 1 ↔ X.π b = 1) :
    ∃ θ : ↥B ≃* ↥B₀, (∀ b : ↥B, X₀.π (θ b) = X.π b) ∧
      ∀ b : ↥B, X.π b = 1 → X₀.eT (θ b) = X.eT b := by
  let XB := X.restrict K B hB
  let XB₀ := X₀.restrict K B₀ hB₀
  obtain ⟨α, hα⟩ := exists_mulEquiv_induced₂ XB.π XB₀.π XB.π_surjective XB₀.π_surjective θ₁
    (fun b => ⟨fun h1 => Subtype.ext ((hθ₁ b).1 (congrArg Subtype.val h1)),
      fun h1 => Subtype.ext ((hθ₁ b).2 (congrArg Subtype.val h1))⟩)
  obtain ⟨k', hk', hconj⟩ := hAut α
  have hconj' : ∀ b : ↥B, X₀.π (θ₁ b) = k' * X.π b * k'⁻¹ := fun b => by
    have h1 := hconj (XB.π b)
    rw [hα b] at h1
    exact h1
  obtain ⟨c₀, hc₀⟩ := X₀.π_surjective k'⁻¹
  have hmem : ∀ b ∈ B₀, c₀ * b * c₀⁻¹ ∈ B₀ := fun b hb => by
    rw [hB₀] at hb ⊢
    rw [map_mul, map_mul, map_inv, hc₀]
    exact hnorm _ (inv_mem hk') _ hb
  have hmem' : ∀ b ∈ B₀, c₀⁻¹ * b * c₀ ∈ B₀ := fun b hb => by
    rw [hB₀] at hb ⊢
    rw [map_mul, map_mul, map_inv, hc₀, inv_inv]
    exact hnorm _ hk' _ hb
  let θ : ↥B ≃* ↥B₀ := θ₁.trans (conjAut B₀ c₀ hmem hmem')
  have hθ : ∀ b : ↥B, ((θ b : ↥B₀) : N₀) = c₀ * ((θ₁ b : ↥B₀) : N₀) * c₀⁻¹ := fun b => rfl
  have hπθ : ∀ b : ↥B, X₀.π (θ b) = X.π b := fun b => by
    rw [hθ, map_mul, map_mul, map_inv, hc₀, hconj' b]
    group
  refine ⟨θ, hπθ, ?_⟩
  have hker : ∀ b : ↥B, XB₀.π (θ b) = 1 ↔ XB.π b = 1 := fun b => by
    constructor
    · intro h
      exact Subtype.ext ((hπθ b).symm.trans (congrArg Subtype.val h))
    · intro h
      exact Subtype.ext ((hπθ b).trans (congrArg Subtype.val h))
  let κ : ↥XB.π.ker ≃* ↥XB₀.π.ker :=
    { toFun := fun x => ⟨θ x.1, (hker x.1).2 x.2⟩
      invFun := fun y => ⟨θ.symm y.1, (hker (θ.symm y.1)).1
        (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (θ.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (θ.apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext (map_mul θ x.1 y.1) }
  have hκ : ∀ x : ↥XB.π.ker, ((κ x : ↥XB₀.π.ker) : ↥B₀) = θ (x : ↥B) := fun _ => rfl
  let ψ : W ≃* W := XB.kerEquiv.symm.trans (κ.trans XB₀.kerEquiv)
  have hψ : ∀ x : ↥XB.π.ker, ψ (XB.kerEquiv x) = X₀.eT ((θ x.1 : ↥B₀) : N₀) := fun x => by
    show XB₀.kerEquiv (κ (XB.kerEquiv.symm (XB.kerEquiv x))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hcomm : ∀ (q : ↥K) (w : W),
      ψ ((ρ.comp K.subtype) q w) = (ρ.comp K.subtype) q (ψ w) := by
    intro q w
    obtain ⟨b, rfl⟩ := XB.π_surjective q
    obtain ⟨x, rfl⟩ := XB.kerEquiv.surjective w
    have h1 : (ρ.comp K.subtype) (XB.π b) (XB.kerEquiv x) =
        XB.kerEquiv (MulAut.conjNormal b x) := (XB.kerEquiv_conj b x).symm
    have h2 : κ (MulAut.conjNormal b x) = MulAut.conjNormal (θ b) (κ x) := by
      apply Subtype.ext
      rw [hκ, MulAut.conjNormal_apply, MulAut.conjNormal_apply, hκ, map_mul, map_mul, map_inv]
    rw [h1]
    show XB₀.kerEquiv (κ (XB.kerEquiv.symm (XB.kerEquiv (MulAut.conjNormal b x)))) = _
    rw [MulEquiv.symm_apply_apply, h2, XB₀.kerEquiv_conj]
    have h3 : XB₀.π (θ b) = XB.π b := Subtype.ext (hπθ b)
    rw [h3, hψ x]
    rfl
  have hrefl : ψ = MulEquiv.refl W := hEnd ψ hcomm
  intro b hb
  have hbk : b ∈ XB.π.ker := Subtype.ext hb
  have h := hψ ⟨b, hbk⟩
  rw [hrefl] at h
  exact h.symm

end Abstract

section Mathieu

variable {N : Type u} {N₀ : Type v} [Group N] [Group N₀]

theorem exists_theta_K22
    (X : ExtData (rho11 AutPerm le_rfl) N) (X₀ : ExtData (rho11 AutPerm le_rfl) N₀)
    {B : Subgroup N} {B₀ : Subgroup N₀} (hB : ∀ n, n ∈ B ↔ X.π n ∈ K22)
    (hB₀ : ∀ n, n ∈ B₀ ↔ X₀.π n ∈ K22) (θ₁ : ↥B ≃* ↥B₀)
    (hθ₁ : ∀ b : ↥B, X₀.π (θ₁ b) = 1 ↔ X.π b = 1) :
    ∃ θ : ↥B ≃* ↥B₀, (∀ b : ↥B, X₀.π (θ b) = X.π b) ∧
      ∀ b : ↥B, X.π b = 1 → X₀.eT (θ b) = X.eT b :=
  X.exists_theta_of_aut_preimage X₀ (K' := duadStabPlus 0 1)
    (fun _ hk' _ hq => conj_mem_K22_of_mem_duadStabPlus hk' hq) modEquivAutTrivial_K22
    (fun α => by
      obtain ⟨k', hk', hq⟩ := exists_conj_of_aut_K22_aux α
      exact ⟨k', hk', fun q => Subtype.ext (hq q)⟩) hB hB₀ θ₁ hθ₁

theorem exists_theta_duad
    (X : ExtData (rho11 AutPerm le_rfl) N) (X₀ : ExtData (rho11 AutPerm le_rfl) N₀)
    {i j : Fin 24} (hij : i ≠ j) {B : Subgroup N} {B₀ : Subgroup N₀}
    (hB : ∀ n, n ∈ B ↔ ((X.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) i = i ∧
      ((X.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) j = j)
    (hB₀ : ∀ n, n ∈ B₀ ↔ ((X₀.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) i = i ∧
      ((X₀.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) j = j)
    (θ₁ : ↥B ≃* ↥B₀) (hθ₁ : ∀ b : ↥B, X₀.π (θ₁ b) = 1 ↔ X.π b = 1) :
    ∃ θ : ↥B ≃* ↥B₀, (∀ b : ↥B, X₀.π (θ b) = X.π b) ∧
      ∀ b : ↥B, X.π b = 1 → X₀.eT (θ b) = X.eT b := by
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two i j hij
  let t : ↥AutPerm := ⟨τ, hτ⟩
  have hB' : ∀ n, n ∈ B ↔ (X.twist t).π n ∈ K22 := fun n =>
    (hB n).trans (conj_mem_K22_iff hτ0 hτ1 (X.π n)).symm
  have hB₀' : ∀ n, n ∈ B₀ ↔ (X₀.twist t).π n ∈ K22 := fun n =>
    (hB₀ n).trans (conj_mem_K22_iff hτ0 hτ1 (X₀.π n)).symm
  have hθ₁' : ∀ b : ↥B, (X₀.twist t).π (θ₁ b) = 1 ↔ (X.twist t).π b = 1 := fun b => by
    show t⁻¹ * X₀.π (θ₁ b) * t = 1 ↔ t⁻¹ * X.π b * t = 1
    rw [conj_eq_one_iff t, conj_eq_one_iff t]
    exact hθ₁ b
  obtain ⟨θ, hθπ, hθe⟩ := exists_theta_K22 (X := X.twist t) (X₀ := X₀.twist t)
    hB' hB₀' θ₁ hθ₁'
  refine ⟨θ, fun b => ?_, fun b hb => ?_⟩
  · have h : t⁻¹ * (X₀.π (θ b) * t) = t⁻¹ * (X.π b * t) := by
      rw [← mul_assoc, ← mul_assoc]
      exact hθπ b
    exact mul_right_cancel (mul_left_cancel h)
  · exact (rho11 AutPerm le_rfl t⁻¹).injective (hθe b ((conj_eq_one_iff t).2 hb))

end Mathieu

end ExtData

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
