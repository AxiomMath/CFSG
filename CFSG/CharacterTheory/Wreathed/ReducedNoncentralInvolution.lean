module

public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolutionComplement
public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolutionConjugation
public import CFSG.CharacterTheory.Wreathed.OddFieldFixedTorusDerivedCentralizer

public noncomputable section

namespace CFSG.Wreathed.ReducedInvolution

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
open CFSG.Wreathed.CentralSL2Abelianization

theorem reduced_noncentral_involution_centralizer_has_exact_odd_torus_field_complement
    {F : Type} [Field F] [Fintype F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (ε : ℤ) (hε : ε = if p ^ f % 4 = 1 then 1 else -1)
    (m : ℕ) (hm : 0 < m) (heven : Even m) (hm2 : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - ε))
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b) (hb : ¬ IsSquare b) :
    let V := CentralExtension F b m hm heven
    let H := SemilinearExtension F b m hm heven Sigma hSigma
    let ι : V →* H := SemidirectProduct.inl
    let iF : SpecialLinearGroup (Fin 2) F →* V := specialInclusion F b m hm heven
    let M : Subgroup V := iF.range
    let u : V := cyclicGenerator F b m hm heven
    let a : V := u ^ 2
    let x₀ : V := u ^ m
    let J₀ : SpecialLinearGroup (Fin 2) F := weyl F
    let y₀ : V := a ^ (m / 4) * iF J₀
    let D : Subgroup V := Subgroup.centralizer {y₀}
    let T : Subgroup (SpecialLinearGroup (Fin 2) F) := Subgroup.centralizer {J₀}
    let C : Subgroup H := Subgroup.centralizer {ι y₀}
    (J₀ : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] ∧
    x₀ = iF (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) ∧
    (∀ g ∈ D, ∀ g' ∈ D, g * g' = g' * g) ∧ (Nat.card D : ℤ) = m * ((p ^ f : ℕ) - ε) ∧
    (∀ P P' : Sylow 2 D, P = P') ∧
    (∀ P : Sylow 2 D, Nat.card (P : Subgroup D) = m ^ 2 ∧
      ∀ σ : Sigma, ∀ g ∈ P, fieldAction F b m hm heven Sigma hSigma σ (g : V) = g) ∧
    M ⊓ D = T.map iF ∧ IsCyclic (T.map iF) ∧ (Nat.card (T.map iF) : ℤ) = (p ^ f : ℕ) - ε ∧
    (∀ y : H, orderOf y = 2 → y ∉ Subgroup.center H → ∃ h : V, (ι h)⁻¹ * y * ι h = ι y₀) ∧
    (∃ W : Subgroup (SpecialLinearGroup (Fin 2) F), ∀ g, g ∈ W ↔ g ∈ T ∧ Odd (orderOf g)) ∧
    ∀ W : Subgroup (SpecialLinearGroup (Fin 2) F), (∀ g, g ∈ W ↔ g ∈ T ∧ Odd (orderOf g)) →
      (∀ g : V, g ∈ D ∧ Odd (orderOf g) ↔ g ∈ W.map iF) ∧
      (∃ φ : Sigma →* MulAut W, ∀ σ w, ((φ σ w : W) : SpecialLinearGroup (Fin 2) F) =
        SpecialLinearGroup.map (σ : F ≃+* F).toRingHom w) ∧
      ∀ φ : Sigma →* MulAut W, (∀ σ w, ((φ σ w : W) : SpecialLinearGroup (Fin 2) F) =
          SpecialLinearGroup.map (σ : F ≃+* F).toRingHom w) →
        (∃ Ψ : W ⋊[φ] Sigma ≃*
            ↥(W.map (ι.comp iF) ⊔ (SemidirectProduct.inr : Sigma →* H).range),
          ∀ x, (Ψ x : H) = ι (iF x.left) * SemidirectProduct.inr x.right) ∧
        (∀ P : Sylow 2 D, ∃ Θ : ↥(P : Subgroup D) × (W ⋊[φ] Sigma) ≃* C,
          ∀ g x, (Θ (g, x) : H) =
            ι ((g : D) : V) * ι (iF x.left) * SemidirectProduct.inr x.right) ∧
        (CFSG.oddCore C).map C.subtype =
          W.map (ι.comp iF) ⊔ (SemidirectProduct.inr : Sigma →* H).range ∧
        ∀ y : H, orderOf y = 2 → y ∉ Subgroup.center H → ∀ h : V, (ι h)⁻¹ * y * ι h = ι y₀ →
          ((CFSG.oddCore (Subgroup.centralizer {y})).map (Subgroup.centralizer {y}).subtype).map
              (MulAut.conj (ι h)⁻¹).toMonoidHom =
            W.map (ι.comp iF) ⊔ (SemidirectProduct.inr : Sigma →* H).range ∧
          ((CFSG.oddCore (Subgroup.centralizer {y})).map (Subgroup.centralizer {y}).subtype ⊓
              M.map ι).map (MulAut.conj (ι h)⁻¹).toMonoidHom = W.map (ι.comp iF) ∧
          ∃ ψ : CFSG.oddCore (Subgroup.centralizer {y}) ≃* W ⋊[φ] Sigma,
            ∀ k : CFSG.oddCore (Subgroup.centralizer {y}),
              ι (iF (ψ k).left) * SemidirectProduct.inr (ψ k).right =
                (ι h)⁻¹ * ((k : Subgroup.centralizer {y}) : H) * ι h ∧
              SemidirectProduct.rightHom (ψ k) =
                SemidirectProduct.rightHom ((k : Subgroup.centralizer {y}) : H) := by
  intro V H ι iF M u a x₀ J₀ y₀ D T C
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
  have hinjF : Function.Injective iF := specialInclusion_injective F b m hm heven
  obtain ⟨-, hm4, -, hWex, hWall⟩ :=
    OddFieldTorus.odd_field_fixed_torus_derived_centralizer hp hp2 hf hcard ε hε m hm2 Sigma hd
  have hsq : IsSquare (-1 : F) ↔ p ^ f % 4 = 1 := by
    obtain ⟨k, hk⟩ := odd_card F h2
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  have hTcard : (Nat.card T : ℤ) = (p ^ f : ℕ) - ε := by
    change (Nat.card (OddFieldTorus.torus F) : ℤ) = _
    rw [OddFieldTorus.torus_card h2, hcard, hε]
  obtain ⟨k, h, hh, hTkh⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card T) Nat.card_pos.ne'
  have hmk : m = 2 ^ k := by
    rw [hm2, ← hTcard, padicValInt.of_nat, hTkh, OddFieldTorus.padicValNat_two_pow_mul_odd hh]
  have hTmh : Nat.card T = m * h := by rw [hTkh, hmk]
  have h4 : 4 ∣ m := by
    rw [hmk]
    have hk2 : 2 ≤ k := by
      by_contra hk
      have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact (Nat.pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
  have hDcomm : ∀ g ∈ D, ∀ g' ∈ D, g * g' = g' * g :=
    fun g hg g' hg' => centralizer_involutionY_comm hb hg hg'
  have : IsMulCommutative D := ⟨⟨fun x y => Subtype.ext (hDcomm _ x.2 _ y.2)⟩⟩
  have hDZ : (Nat.card D : ℤ) = m * ((p ^ f : ℕ) - ε) := by
    have hCW := card_centralizer_involutionY (hm := hm) (heven := heven) hb
    change (Nat.card (Subgroup.centralizer {involutionY F b m hm heven}) : ℤ) = _
    rw [hCW, hcard]
    by_cases hs : IsSquare (-1 : F)
    · rw [ite_eq_left hs, hε, ite_eq_left (hsq.mp hs)]
      push_cast [Nat.cast_sub (show 1 ≤ p ^ f from Nat.one_le_pow _ _ hp.pos)]
      ring
    · rw [ite_eq_right hs, hε, ite_eq_right (fun h => hs (hsq.mpr h))]
      push_cast
      ring
  have hDcard : Nat.card D = m * m * h := by
    have h' : (Nat.card D : ℤ) = ((m * m * h : ℕ) : ℤ) := by
      rw [hDZ, ← hTcard, hTmh]
      push_cast
      ring
    exact_mod_cast h'
  have hsylow_card : ∀ P : Sylow 2 D, Nat.card (P : Subgroup D) = m ^ 2 := by
    intro P
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Sylow.card_eq_multiplicity, hDcard, Nat.factorization_def _ Nat.prime_two, hmk,
      ← pow_add, OddFieldTorus.padicValNat_two_pow_mul_odd hh]
    ring
  have hsylow_fix : ∀ P : Sylow 2 D, ∀ σ : Sigma, ∀ g ∈ P,
      fieldAction F b m hm heven Sigma hSigma σ (g : V) = g := by
    intro P σ g hg
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨g, hg⟩
    have hgn : (g : V) ^ 2 ^ n = 1 := by
      have := congrArg (fun z : (P : Subgroup D) => ((z : D) : V)) hn
      simpa using this
    exact fieldAction_eq_of_pow_two_pow hb hd σ g.2 hgn
  have hinvol : ∀ y : H, orderOf y = 2 → y ∉ Subgroup.center H →
      ∃ h : V, (ι h)⁻¹ * y * ι h = ι y₀ := by
    intro y hy hyc
    have hyy : y * y = 1 := by
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hy)
    have hy' : y = ι y.left := eq_inl_of_mul_self hd hyy
    have hw : y.left * y.left = 1 := by
      have h' : ι (y.left * y.left) = ι 1 := by rw [map_mul, ← hy', hyy, map_one]
      exact SemidirectProduct.inl_injective h'
    rcases involution_cases hb h4 hw with h1 | h1 | h1
    · exfalso
      rw [h1, map_one] at hy'
      rw [hy', orderOf_one] at hy
      omega
    · exfalso
      apply hyc
      rw [hy', h1]
      exact Subgroup.mem_center_iff.mpr fun g => inl_cyclicGenerator_pow_m_comm g
    · obtain ⟨c, hc⟩ := isConj_iff.mp h1
      refine ⟨c, ?_⟩
      rw [hy', ← hc]
      change (ι c)⁻¹ * ι (c * y₀ * c⁻¹) * ι c = ι y₀
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
  refine ⟨weyl_val F, cyclicGenerator_pow_m F b m hm heven, hDcomm, hDZ,
    fun P P' => ?_, fun P => ⟨hsylow_card P, hsylow_fix P⟩, range_inf_centralizer,
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective T iF hinjF)).mp
      (OddFieldTorus.torus_isCyclic h2),
    by rw [Subgroup.card_map_of_injective hinjF, hTcard], hinvol, hWex, fun W hW => ?_⟩
  · have hnormal : (P : Subgroup D).Normal := Subgroup.normal_of_isMulCommutative _
    have := Sylow.unique_of_normal P hnormal
    exact Subsingleton.elim P P'
  obtain ⟨-, hWcardZ, -, hφex, -⟩ := hWall W hW
  have hWcard : Nat.card W = h := by
    have h' : (Nat.card W : ℤ) = h := by
      rw [hWcardZ, ← hTcard, hTmh]
      push_cast
      exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hm.ne')
    exact_mod_cast h'
  have hWD : W.map iF ≤ D := by
    rintro _ ⟨w, hw, rfl⟩
    exact (specialInclusion_mem_centralizer_iff w).mpr ((hW w).mp hw).1
  have hodd_part : ∀ g : V, g ∈ D ∧ Odd (orderOf g) ↔ g ∈ W.map iF := by
    intro g
    constructor
    · rintro ⟨hgD, hgodd⟩
      have hN : ((W.map iF).subgroupOf D).Normal := Subgroup.normal_of_isMulCommutative _
      have hNcard : Nat.card ((W.map iF).subgroupOf D) = h := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWD).toEquiv,
          Subgroup.card_map_of_injective hinjF, hWcard]
      have hindex : ((W.map iF).subgroupOf D).index = m * m := by
        have hci := Subgroup.card_mul_index ((W.map iF).subgroupOf D)
        rw [hNcard, hDcard, mul_comm (m * m) h] at hci
        exact Nat.eq_of_mul_eq_mul_left hh.pos hci
      have hcop : ((W.map iF).subgroupOf D).index.Coprime (orderOf (⟨g, hgD⟩ : D)) := by
        rw [Subgroup.orderOf_mk, hindex, show m * m = 2 ^ (k + k) by rw [pow_add, ← hmk]]
        exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hgodd)
      obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
      have hmem : (⟨g, hgD⟩ : D) ∈ (W.map iF).subgroupOf D := by
        rw [← hn]
        exact Subgroup.pow_mem _ (Subgroup.pow_index_mem _ _) n
      exact Subgroup.mem_subgroupOf.mp hmem
    · rintro ⟨w, hw, rfl⟩
      refine ⟨hWD ⟨w, hw, rfl⟩, ?_⟩
      rw [orderOf_injective _ hinjF]
      exact ((hW w).mp hw).2
  refine ⟨hodd_part, hφex, fun φ hφ => ?_⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup H,
      K = W.map (ι.comp iF) ⊔ (SemidirectProduct.inr : Sigma →* H).range := ⟨_, rfl⟩
  rw [← hKdef]
  obtain ⟨Ψ, hΨ⟩ := exists_complement_equiv b m hm heven hSigma hφ
  have hK : (complementHom b m hm heven hSigma hφ).range = K :=
    (range_complementHom b m hm heven hSigma hφ).trans hKdef.symm
  have hCcard : Nat.card C = m * m * h * Nat.card Sigma := by
    rw [← hDcard]
    exact card_centralizer_inl (y := involutionY F b m hm heven) fieldAction_involutionY
  have hΘex : ∀ P : Sylow 2 D, ∃ Θ : ↥(P : Subgroup D) × (W ⋊[φ] Sigma) ≃* C,
      ∀ g x, (Θ (g, x) : H) =
        ι ((g : D) : V) * ι (iF x.left) * SemidirectProduct.inr x.right := by
    intro P
    have e : Nat.card C = Nat.card (P : Subgroup D) * (Nat.card W * Nat.card Sigma) := by
      rw [hCcard, hsylow_card P, hWcard]
      ring
    exact exists_centralizer_equiv b m hm heven hSigma hφ hb hW (P : Subgroup D) P.isPGroup'
      (hsylow_fix P) e.le
  have hoddC : (CFSG.oddCore C).map C.subtype = K := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 D) := inferInstance
    obtain ⟨Θ, hΘ⟩ := hΘex P
    have hQodd : Odd (Nat.card (W ⋊[φ] Sigma)) := by
      rw [SemidirectProduct.card, hWcard]
      exact hh.mul hd
    rw [oddCore_eq_range_inr Θ P.isPGroup' hQodd, MonoidHom.map_range, ← hK]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change ((Θ (1, x) : C) : H) = complementHom b m hm heven hSigma hφ x
    rw [hΘ, complementHom_apply]
    simp [ι, iF]
  refine ⟨?_, hΘex, hoddC, fun y hy hyc h hh' => ?_⟩
  · rw [hKdef]
    exact ⟨Ψ, hΨ⟩
  have hγy : MulAut.conj (ι h)⁻¹ y = ι y₀ := by
    rw [MulAut.conj_apply, inv_inv]
    exact hh'
  have hOK : ((CFSG.oddCore (Subgroup.centralizer {y})).map
      (Subgroup.centralizer {y}).subtype).map (MulAut.conj (ι h)⁻¹).toMonoidHom = K := by
    have h1 := oddCore_centralizer_map (MulAut.conj (ι h)⁻¹) y
    rw [hγy] at h1
    exact h1.trans hoddC
  have hMnormal : M.Normal := by
    change (specialInclusion F b m hm heven).range.Normal
    rw [← baseResidue_ker]
    infer_instance
  have hMconj : (M.map ι).map (MulAut.conj (ι h)⁻¹).toMonoidHom = M.map ι := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      refine ⟨h⁻¹ * g * h, ?_, ?_⟩
      · have hc := hMnormal.conj_mem g hg h⁻¹
        rwa [inv_inv] at hc
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv]
    · rintro _ ⟨g, hg, rfl⟩
      refine ⟨ι (h * g * h⁻¹), ⟨h * g * h⁻¹, hMnormal.conj_mem g hg h, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv,
        mul_assoc, mul_assoc, inv_mul_cancel, mul_one, ← mul_assoc, inv_mul_cancel, one_mul]
  have hKM : K ⊓ M.map ι = W.map (ι.comp iF) := by
    apply le_antisymm
    · rintro x ⟨hxK, hxM⟩
      rw [← hK] at hxK
      obtain ⟨z, rfl⟩ := hxK
      obtain ⟨g, -, hg⟩ := hxM
      rw [complementHom_apply] at hg ⊢
      have hr : z.right = 1 := by
        have h1 := congrArg SemidirectProduct.right hg
        simpa +zetaDelta using h1.symm
      rw [hr, map_one, mul_one]
      exact ⟨z.left, z.left.2, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨?_, ⟨iF w, ⟨w, rfl⟩, rfl⟩⟩
      rw [hKdef]
      exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hw)
  refine ⟨hOK, ?_, ?_⟩
  · rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj (ι h)⁻¹).injective, hOK, hMconj, hKM]
  · obtain ⟨ψ, hψ⟩ := exists_oddCore_equiv (MulAut.conj (ι h)⁻¹) y Ψ (hOK.trans hKdef)
    refine ⟨ψ, fun k => ?_⟩
    have hk : ι (iF (ψ k).left) * SemidirectProduct.inr (ψ k).right =
        (ι h)⁻¹ * ((k : Subgroup.centralizer {y}) : H) * ι h := by
      rw [← hΨ, hψ, MulAut.conj_apply, inv_inv]
    refine ⟨hk, ?_⟩
    change (ψ k).right = ((k : Subgroup.centralizer {y}) : H).right
    have hr := congrArg SemidirectProduct.right hk
    simpa +zetaDelta using hr

end CFSG.Wreathed.ReducedInvolution
