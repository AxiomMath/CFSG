module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L3U3Final
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L3EvenA
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvL3Aut
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvL3Graph
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvL3Field

public section

namespace CFSG.GH74.GLS.IVK

open Matrix Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.GH74.KGroups.L3Eps (exists_projectiveSL_equiv conjAut_mem_inner_of_sq_scalar)
open scoped MatrixGroups commutatorElement

namespace GHInv

theorem graphData_transport {X P : Type*} [Group X] [Group P] (θ : X ≃* P) (c : MulAut X)
    (N₀ : Subgroup P) (hq : CFSG.IsQuasisimple ↥N₀)
    (hfix : ∀ n ∈ N₀, MulAut.congr θ c n = n)
    (hconj : ∀ x, MulAut.congr θ c x = x → ∀ n ∈ N₀, x * n * x⁻¹ ∈ N₀)
    (hcomm : ∀ x y, MulAut.congr θ c x = x → MulAut.congr θ c y = y → ⁅x, y⁆ ∈ N₀) :
    ∃ S : Subgroup X, CFSG.IsQuasisimple ↥S ∧ (∀ y, y ∈ S ↔ θ y ∈ N₀) ∧ (∀ s ∈ S, c s = s) ∧
      (∀ x, c x = x → ∀ s ∈ S, x * s * x⁻¹ ∈ S) ∧ (∀ x y, c x = x → c y = y → ⁅x, y⁆ ∈ S) := by
  have hmem : ∀ y : X, y ∈ N₀.map θ.symm.toMonoidHom ↔ θ y ∈ N₀ := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro h
      exact ⟨θ y, h, by simp⟩
  have hfixc : ∀ x : X, MulAut.congr θ c (θ x) = θ x ↔ c x = x := by
    intro x
    have : MulAut.congr θ c (θ x) = θ (c x) := by
      show θ (c (θ.symm (θ x))) = θ (c x)
      rw [MulEquiv.symm_apply_apply]
    rw [this]
    exact ⟨fun h => θ.injective h, fun h => by rw [h]⟩
  refine ⟨N₀.map θ.symm.toMonoidHom, LocalCores.isQuasisimple_of_mulEquiv
    (MulEquiv.subgroupMap θ.symm N₀) hq, hmem, ?_, ?_, ?_⟩
  · intro s hs
    rw [hmem] at hs
    exact (hfixc s).1 (hfix _ hs)
  · intro x hx s hs
    rw [hmem] at hs ⊢
    rw [map_mul, map_mul, map_inv]
    exact hconj _ ((hfixc x).2 hx) _ hs
  · intro x y hx hy
    rw [hmem, map_commutatorElement]
    exact hcomm _ _ ((hfixc x).2 hx) ((hfixc y).2 hy)

end GHInv

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

omit [Finite N] in
theorem conjNormal_fixed_iff [L.Normal] (e : N) (x : ↥L) :
    MulAut.conjNormal e x = x ↔ (x : N) ∈ centralizer ({e} : Set N) := by
  rw [Subtype.ext_iff, MulAut.conjNormal_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc (x : N) * e = e * x * e⁻¹ * e := by rw [h]
      _ = e * x := by group
  · intro h
    calc e * x * e⁻¹ = x * e * e⁻¹ := by rw [h]
      _ = x := by group

theorem Ivk73Cfg.false_of_L3even
    (h : Ivk73Cfg N L K Q) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hfe : Even f) (hf0 : f ≠ 0)
    (hst : StatedClassicalModel ↥L .PSL 3 p f)
    (hA : ¬ ∃ u : N, u ∈ Q ∧ orderOf u = 2 ∧ u ∈ L) : False := by
  have := h.normal
  obtain ⟨F, _, _, hF, ⟨θ⟩⟩ := exists_projectiveSL_equiv hst
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := Generic.S3.two_ne_zero_of_odd_card hodd
  have hF2 : ringChar F ≠ 2 := fun h' => h2 (by
    have : CharP F 2 := h' ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  obtain ⟨k, hk⟩ := hfe
  have hk1 : 1 ≤ k := by omega
  have hr3 : 3 ≤ p ^ k := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      obtain ⟨m, hm⟩ := hpodd
      omega
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk1
  have hq : p ^ f = p ^ k * p ^ k := by rw [hk, pow_add]
  obtain ⟨m, hm⟩ : Odd (p ^ k) := hpodd.pow
  have hqt : p ^ f + 1 = 2 * (2 * m ^ 2 + 2 * m + 1) := by rw [hq, hm]; ring
  have ht5 : 5 ≤ 2 * m ^ 2 + 2 * m + 1 := by nlinarith
  have ht1 : 2 * m ^ 2 + 2 * m + 1 ≠ 1 := by omega
  have htodd : Odd (2 * m ^ 2 + 2 * m + 1) := ⟨m ^ 2 + m, by ring⟩
  set t := 2 * m ^ 2 + 2 * m + 1 with ht
  have hℓ : (Nat.minFac t).Prime := Nat.minFac_prime ht1
  have hℓt : Nat.minFac t ∣ t := Nat.minFac_dvd t
  have hℓ2 : Nat.minFac t ≠ 2 := by
    intro h2'
    rw [h2'] at hℓt
    exact (Nat.not_even_iff_odd.2 htodd) (even_iff_two_dvd.2 hℓt)
  have hℓdvd : Nat.minFac t ∣ p ^ f + 1 := hqt ▸ Dvd.dvd.mul_left hℓt 2
  have h9 : 9 ≤ p ^ f := by rw [hq]; nlinarith
  have h3 : Nat.card F ≠ 3 := by rw [hF]; omega
  let Ψ : N →* MulAut (projectiveSL 3 F) :=
    (MulAut.congr θ).toMonoidHom.comp (MulAut.conjNormal : N →* MulAut ↥L)
  have hΨ : Function.Injective Ψ :=
    (MulAut.congr θ).injective.comp (conjNormal_injective_of_cent_trivial h.cent_trivial)
  have hΨapp : ∀ (a : N) (x : ↥L), Ψ a (θ x) = θ (MulAut.conjNormal a x) := by
    intro a x
    show θ ((MulAut.conjNormal a) (θ.symm (θ x))) = _
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨E, hEQ, hEa, hE4⟩ := h.exists_E
  have hsq : ∀ a : ↥E, a * a = 1 := fun a => by
    rw [← pow_two]
    exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hEa.exponent_dvd_p) a
  have hsq' : ∀ a : N, a ∈ E → a * a = 1 := fun a ha => congrArg Subtype.val (hsq ⟨a, ha⟩)
  have hEsq : ∀ e ∈ E.map Ψ, e * e = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq' a ha, map_one]
  have hEcard : Nat.card ↥(E.map Ψ) = 4 := by
    rw [Subgroup.card_map_of_injective hΨ]
    exact hE4
  have hDE : ∀ e ∈ E.map Ψ, e ∈ (conjAut 3 F).range → e = 1 := by
    rintro _ ⟨a, ha, rfl⟩ hmem
    obtain ⟨A₀, hA₀⟩ := hmem
    have haa : Ψ a * Ψ a = 1 := by rw [← map_mul, hsq' a ha, map_one]
    have h1 : conjAut 3 F (A₀ * A₀) * fieldAut 3 F 1 = 1 := by
      rw [map_one, mul_one, map_mul, hA₀]
      exact haa
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) (A₀ * A₀) 1 h1
    have hscal : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [smul_one_eq_diagonal]
      rfl
    have hAA : (A₀ : Matrix (Fin 3) (Fin 3) F) * A₀ = (c : F) • 1 := by
      rw [← hscal, hc, Units.val_mul]
    have hinner : conjAut 3 F A₀ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 F) := conjAut_mem_inner_of_sq_scalar A₀ c hAA
    rw [hA₀] at hinner
    obtain ⟨x, hx⟩ := hinner
    set l : ↥L := θ.symm x with hl
    have hΨl : Ψ (l : N) = MulAut.conj x := by
      ext y
      rw [show Ψ (l : N) y = θ ((MulAut.conjNormal (l : N)) (θ.symm y)) from rfl,
        MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv, hl,
        MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply]
    have hal : a = (l : N) := hΨ (hx.symm.trans hΨl.symm)
    have ha1 : a = 1 := by
      by_contra hne
      have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq' a ha) hne
      exact hA ⟨a, hEQ ha, hord, hal ▸ l.2⟩
    rw [ha1, map_one]
  obtain ⟨σ, hσ, s₁, hs₁E, e₂', he₂'E, A, C, hCsymm, hs₁1, he₂'1, hs₁ne, hs₁A, he₂'C⟩ :=
    GHInv.exists_field_graph_pair hp hp2 hF ⟨k, hk⟩ hf0 (E.map Ψ) hEsq hEcard hDE
  obtain ⟨s, hsE, rfl⟩ := Subgroup.mem_map.1 hs₁E
  obtain ⟨e₂, he₂E, rfl⟩ := Subgroup.mem_map.1 he₂'E
  have he₂1 : e₂ ≠ 1 := fun h1 => he₂'1 (by rw [h1, map_one])
  have hord₂ : orderOf e₂ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq' e₂ he₂E) he₂1
  have hterm := h.terminal e₂ hord₂ (h.Q_sylow.le (hEQ he₂E))
  have hKM : K ≤ centralizer ({e₂} : Set N) ⊓ L := le_inf hterm.1 h.K_le
  have hM : IsCompIn (centralizer ({e₂} : Set N) ⊓ L) K :=
    LU.Local.isCompIn_mono' hterm hKM inf_le_left
  have hB : IsCompIn ((centralizer ({e₂} : Set N) ⊓ L).subgroupOf L) (K.subgroupOf L) :=
    ⟨Subgroup.subgroupOf_mono L hKM,
      (LU.Local.isComponent_subgroupOf_iff' (K := K) (M := centralizer ({e₂} : Set N) ⊓ L)
        (H := L) inf_le_right).2 hM.2⟩
  obtain ⟨N₀, hq₀, hfix₀, hconj₀, hcomm₀, g, hg₀, hgord⟩ :=
    GHInv.lin_graph_centralizer_ell hF2 h3 hCsymm hℓ hℓ2 (by rw [hF]; exact hℓdvd)
  rw [← he₂'C] at hfix₀ hconj₀ hcomm₀
  obtain ⟨S, hqS, hmemS, hSfix, hSconj, hScomm⟩ :=
    GHInv.graphData_transport θ (MulAut.conjNormal e₂ : MulAut ↥L) N₀ hq₀ hfix₀ hconj₀ hcomm₀
  have hKS : K.subgroupOf L = S := by
    refine GHInv.eq_of_isCompIn_of_normal_quasisimple hqS ?_ ?_ ?_ hB
    · intro x hx
      have hx' : MulAut.conjNormal e₂ x = x := hSfix x hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨(conjNormal_fixed_iff e₂ x).1 hx', x.2⟩
    · intro x hx y hy
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
      exact hSconj x ((conjNormal_fixed_iff e₂ x).2 hx.1) y hy
    · intro x hx y hy
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx hy
      exact hScomm x y ((conjNormal_fixed_iff e₂ x).2 hx.1) ((conjNormal_fixed_iff e₂ y).2 hy.1)
  set x₀ : ↥L := θ.symm (proj 3 F g) with hx₀
  have hx₀S : x₀ ∈ S := by
    rw [hmemS, hx₀, MulEquiv.apply_symm_apply]
    exact hg₀
  have hx₀K : (x₀ : N) ∈ K := by
    rw [← hKS] at hx₀S
    exact hx₀S
  have hscomm : (x₀ : N) * s = s * x₀ :=
    Subgroup.mem_centralizer_iff.1 (h.Q_sylow.le (hEQ hsE)) _ hx₀K
  have hsfix : (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F g) = proj 3 F g := by
    rw [← hs₁A]
    have h1 : Ψ s (θ x₀) = θ x₀ := by
      rw [hΨapp]
      congr 1
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      calc s * (x₀ : N) * s⁻¹ = (x₀ : N) * s * s⁻¹ := by rw [← hscomm]
        _ = x₀ := by group
    rwa [hx₀, MulEquiv.apply_symm_apply] at h1
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, proj_eq_proj_iff] at hsfix
  obtain ⟨c, hc3, hcg⟩ := mem_scalars.1 hsfix
  have hHmat := coe_slConjugation A (SpecialLinearGroup.map σ.toRingHom g)
  generalize CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
    (SpecialLinearGroup.map σ.toRingHom g) = H at hcg hHmat
  have hgH : (g : Matrix (Fin 3) (Fin 3) F) = (c : F) • (H : Matrix (Fin 3) (Fin 3) F) := by
    have h2 : (g : Matrix (Fin 3) (Fin 3) F) =
        (H : Matrix (Fin 3) (Fin 3) F) * ((H⁻¹ * g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [h2, hcg, Matrix.scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hGσ : ((SpecialLinearGroup.map σ.toRingHom g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F).map (fun a => a ^ (p ^ (f / 2))) := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    congr 1
    funext a
    exact hσ a
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hAinv : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGA : (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • ((A : Matrix (Fin 3) (Fin 3) F) *
        (g : Matrix (Fin 3) (Fin 3) F).map (fun a => a ^ (p ^ (f / 2)))) := by
    have h3 : (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
        ((c : F) • (H : Matrix (Fin 3) (Fin 3) F)) * (A : Matrix (Fin 3) (Fin 3) F) :=
      congrArg (fun X => X * (A : Matrix (Fin 3) (Fin 3) F)) hgH
    rw [h3, hHmat, hGσ, Matrix.smul_mul, Matrix.mul_assoc, hAinv, Matrix.mul_one]
  have hmain : (A : Matrix (Fin 3) (Fin 3) F) *
      (g : Matrix (Fin 3) (Fin 3) F).map (fun a => a ^ (p ^ (f / 2))) =
      (((c⁻¹ : Fˣ) : F)) • ((g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) := by
    rw [hGA, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ hc0, one_smul]
  have hgℓ : g ^ Nat.minFac t = 1 := hgord ▸ pow_orderOf_eq_one g
  have hMℓ : (g : Matrix (Fin 3) (Fin 3) F) ^ Nat.minFac t = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hgℓ, Matrix.SpecialLinearGroup.coe_one]
  have hM1 : (g : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
    intro h1
    have : g = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hgord
    exact hℓ.one_lt.ne hgord
  have hc3' : (((c⁻¹ : Fˣ) : F)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hc3, inv_one, Units.val_one]
  exact GHInv.no_ell_element_commuting_field hp hF ⟨k, hk⟩ hf0 hℓ hℓ2 hℓdvd _ hMℓ hM1
    (A : Matrix (Fin 3) (Fin 3) F) (Units.isUnit A) _ hc3' hmain

theorem ivk73_L3even :
    IVK73_L3even := by
  rintro N _ _ L K Q h ⟨p, f, hp, hp2, hf, hfe, hL⟩
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSL hL
  have hf0 : f ≠ 0 := by omega
  have h5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
      omega
    have hf2 : 2 ≤ f := by
      obtain ⟨k, hk⟩ := hfe
      omega
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf2
  by_cases hA : ∃ u : N, u ∈ Q ∧ orderOf u = 2 ∧ u ∈ L
  · exact h.false_of_comp_mem_of_inv hA (comp_mem_lin_all hp hp2 h5 hst)
  · exact h.false_of_L3even hp hp2 hfe hf0 hst hA

theorem ivk73_L3U3 :
    IVK73_L3U3 :=
  ivk73_L3U3_of_even ivk73_L3even

end CFSG.GH74.GLS.IVK
