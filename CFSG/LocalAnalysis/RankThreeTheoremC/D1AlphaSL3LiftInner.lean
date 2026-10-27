module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftFrame
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftGen
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftInnerElt
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftGrp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial

noncomputable def actionAut {X : Type} [Group X] {S : Type} [Group S] (K : Subgroup X)
    [K.Normal] (ψ : S ≃* K) : X →* MulAut S :=
  (MulAut.congr ψ.symm).toMonoidHom.comp (MulAut.conjNormal (H := K))

theorem coe_psi_actionAut {X : Type} [Group X] {S : Type} [Group S] (K : Subgroup X) [K.Normal]
    (ψ : S ≃* K) (x : X) (s : S) :
    ((ψ (actionAut K ψ x s) : K) : X) = x * (ψ s : X) * x⁻¹ := by
  simp [actionAut]

theorem exists_generating_elemAbelian_of_equiv
    {X : Type} [Group X] [Finite X] (R : Sylow 3 X) (K : Subgroup X) [K.Normal] (z : X)
    {k : Type} [Field k] [Finite k] (h3 : 3 ∣ Nat.card k - 1)
    (hσ : ∀ σ : k ≃+* k, σ ^ 3 = 1 → σ = 1)
    (ψ : SpecialLinearGroup (Fin 3) k ≃* K)
    (hzc : z ∈ Subgroup.center X) (hz3 : orderOf z = 3)
    (hΩ : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z)
    (hrank : Open.pRank 3 (R : Subgroup X) = 3) :
    ∃ A : Subgroup X, A ≤ (R : Subgroup X) ∧ Open.IsElemAbelian 3 A ∧ 3 ≤ Open.pRank 3 A ∧
      Subgroup.closure {x : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧
        f * (x : X) * f⁻¹ = x} = ⊤ := by
  classical
  obtain ⟨A, hAR, hAe, hAcard⟩ := exists_elemAbelian_card_27 hrank
  have hzR : z ∈ (R : Subgroup X) := mem_sylow_of_central R hzc hz3
  have hzA : z ∈ A := mem_of_pRank_eq_three hrank hzc hz3 hzR hAR hAe hAcard
  refine ⟨A, hAR, hAe, three_le_pRank_of_card hAe hAcard, ?_⟩
  set C : Subgroup X := Subgroup.centralizer (K : Set X) with hC
  let φ : A →* MulAut (SpecialLinearGroup (Fin 3) k) := (actionAut K ψ).comp A.subtype
  have hφψ : ∀ (a : A) (s : SpecialLinearGroup (Fin 3) k),
      ((ψ (φ a s) : K) : X) = (a : X) * (ψ s : X) * (a : X)⁻¹ := fun a s =>
    coe_psi_actionAut K ψ a s
  have hker : ∀ a : A, a ∈ φ.ker ↔ (a : X) ∈ C := by
    intro a
    rw [MonoidHom.mem_ker, hC, Subgroup.mem_centralizer_iff]
    constructor
    · intro h κ hκ
      obtain ⟨s, hs⟩ := ψ.surjective ⟨κ, hκ⟩
      have h1 := hφψ a s
      rw [h] at h1
      simp only [MulAut.one_apply] at h1
      have h2 : (ψ s : X) = κ := congrArg Subtype.val hs
      rw [h2] at h1
      have : (a : X) * κ = κ * (a : X) := by
        rw [eq_mul_inv_iff_mul_eq] at h1
        exact h1.symm
      exact this.symm
    · intro h
      ext1 s
      apply ψ.injective
      apply Subtype.ext
      rw [hφψ]
      have := h (ψ s : X) (ψ s).2
      simp only [MulAut.one_apply]
      rw [← this]
      group
  have hAC : ∀ a : A, (a : X) ∈ C → (a : X) ∈ Subgroup.zpowers z := by
    intro a ha
    exact mem_zpowers_of_pow_three_eq_one R hzc hz3 hΩ ha (hAe.2 a a.2)
  have hker_card : Nat.card φ.ker ≤ 3 := by
    have hinj : Function.Injective (fun a : φ.ker => (⟨(a.1 : X), hAC a.1 ((hker a.1).1 a.2)⟩ :
        Subgroup.zpowers z)) := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : Subgroup.zpowers z => (x : X)) hab
    calc Nat.card φ.ker ≤ Nat.card (Subgroup.zpowers z) := Nat.card_le_card_of_injective _ hinj
      _ = 3 := by rw [Nat.card_zpowers, hz3]
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (hAe.2 a a.2)
  have hφ3 : ∀ a : A, φ a ^ 3 = 1 := fun a => by rw [← map_pow, hA3, map_one]
  have hφconj : ∀ a : A, ∃ g : GL (Fin 3) k, IsConjBy (φ a) g := fun a =>
    exists_conj_of_pow_three_eq_one hσ (φ a) (hφ3 a)
  obtain ⟨f₁, hf₁ker, s₁, hs₁⟩ := exists_inner_of_index φ hφconj (by omega)
  have hs₁conj : IsConjBy (φ f₁) (Matrix.SpecialLinearGroup.toGL s₁) := by
    intro t
    rw [hs₁ t, ← map_inv]
    rfl
  set κ₁ : X := (ψ s₁ : X) with hκ₁
  have hκ₁K : κ₁ ∈ K := (ψ s₁).2
  set c₁ : X := κ₁⁻¹ * (f₁ : X) with hc₁
  have hc₁C : c₁ ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro κ hκ
    obtain ⟨t, ht⟩ := ψ.surjective ⟨κ, hκ⟩
    have h2 : (ψ t : X) = κ := congrArg Subtype.val ht
    have h1 := hφψ f₁ t
    rw [hs₁ t, map_mul, map_mul, map_inv] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h2] at h1
    rw [hc₁]
    have h3 : (f₁ : X) * κ = κ₁ * κ * κ₁⁻¹ * (f₁ : X) := by
      rw [h1]; group
    calc κ * (κ₁⁻¹ * (f₁ : X)) = κ₁⁻¹ * (κ₁ * κ * κ₁⁻¹ * (f₁ : X)) := by group
      _ = κ₁⁻¹ * ((f₁ : X) * κ) := by rw [h3]
      _ = κ₁⁻¹ * (f₁ : X) * κ := by group
  have hf₁eq : (f₁ : X) = κ₁ * c₁ := by rw [hc₁]; group
  obtain ⟨f₂', hf₂'A, hf₂'not⟩ := exists_mem_not_mem_sup_zpowers hAe hAcard hzA f₁.2
  let f₂ : A := ⟨f₂', hf₂'A⟩
  obtain ⟨g₂, hg₂⟩ := hφconj f₂
  have hcomm : (f₁ : X) * (f₂ : X) = (f₂ : X) * (f₁ : X) := by
    exact congrArg Subtype.val (hAe.1.is_comm.comm f₁ f₂)
  obtain ⟨hζeq, hζmem⟩ := conj_aux_mem (K := K) hcomm hκ₁K hc₁C hf₁eq
  set ζ' : X := κ₁⁻¹ * ((f₂ : X) * κ₁ * (f₂ : X)⁻¹) with hζ'
  have hζ'K : ζ' ∈ K := hζmem.1
  have hζ'C : ζ' ∈ C := hζmem.2
  set w' : SpecialLinearGroup (Fin 3) k := ψ.symm ⟨ζ', hζ'K⟩ with hw'
  have hw'center : w' ∈ Subgroup.center (SpecialLinearGroup (Fin 3) k) := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply ψ.injective
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp hζ'C (ψ t : X) (ψ t).2
    simp only [hw', map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
    exact this
  obtain ⟨w, hw3, hw'eq⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hw'center
  have hθs₁ : φ f₂ s₁ = s₁ * w' := by
    apply ψ.injective
    apply Subtype.ext
    rw [hφψ]
    simp only [hw', map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
    rw [← hκ₁, hζ']
    group
  have hw3' : w ^ 3 = 1 := by simpa using hw3
  have hscalar : (Matrix.scalar (Fin 3) w : Matrix (Fin 3) (Fin 3) k) =
      w • (1 : Matrix (Fin 3) (Fin 3) k) := by
    rw [Matrix.smul_one_eq_diagonal]; rfl
  have hmat : (g₂ : Matrix (Fin 3) (Fin 3) k) * (s₁ : Matrix (Fin 3) (Fin 3) k) *
      ((g₂⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        w • (s₁ : Matrix (Fin 3) (Fin 3) k) := by
    have := hg₂ s₁
    rw [hθs₁, Matrix.SpecialLinearGroup.coe_mul, ← hw'eq, hscalar] at this
    rw [← this]
    simp
  have hw1 : w = 1 := by
    by_contra hw1
    have hs3 := cube_eq_one_of_conj_eq_smul s₁ g₂ hw3' hw1 hmat
    have hκ3 : κ₁ ^ 3 = 1 := by
      have h1 : (s₁ ^ 3 : SpecialLinearGroup (Fin 3) k) = 1 := by
        apply Subtype.ext
        simpa using hs3
      calc κ₁ ^ 3 = ((ψ (s₁ ^ 3) : K) : X) := by simp [hκ₁]
        _ = 1 := by rw [h1]; simp
    have hc3 : c₁ ^ 3 = 1 := by
      have hcm : Commute κ₁ c₁ := Subgroup.mem_centralizer_iff.mp hc₁C κ₁ hκ₁K
      have h1 : (f₁ : X) ^ 3 = 1 := hAe.2 f₁ f₁.2
      rw [hf₁eq, hcm.mul_pow, hκ3, one_mul] at h1
      exact h1
    have hc₁z : c₁ ∈ Subgroup.zpowers z :=
      mem_zpowers_of_pow_three_eq_one R hzc hz3 hΩ hc₁C hc3
    have hconj : (f₂ : X) * c₁ * (f₂ : X)⁻¹ = c₁ := conj_eq_of_mem_zpowers hzc hc₁z f₂
    have hζ'1 : ζ' = 1 := by rw [hζeq, hconj]; group
    have hw'1 : w' = 1 := by
      have : (⟨ζ', hζ'K⟩ : K) = 1 := Subtype.ext hζ'1
      rw [hw', this, map_one]
    apply hw1
    have h00 : ((w' : Matrix (Fin 3) (Fin 3) k)) 0 0 = 1 := by rw [hw'1]; simp
    rw [← hw'eq] at h00
    simpa using h00
  have hcommg : (g₂ : Matrix (Fin 3) (Fin 3) k) * (s₁ : Matrix (Fin 3) (Fin 3) k) =
      (s₁ : Matrix (Fin 3) (Fin 3) k) * (g₂ : Matrix (Fin 3) (Fin 3) k) := by
    rw [hw1, one_smul] at hmat
    calc (g₂ : Matrix (Fin 3) (Fin 3) k) * (s₁ : Matrix (Fin 3) (Fin 3) k)
        = (g₂ : Matrix (Fin 3) (Fin 3) k) * (s₁ : Matrix (Fin 3) (Fin 3) k) *
          ((g₂⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
            (g₂ : Matrix (Fin 3) (Fin 3) k) := by
          rw [Matrix.mul_assoc _ _ (g₂ : Matrix (Fin 3) (Fin 3) k)]
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = (s₁ : Matrix (Fin 3) (Fin 3) k) * (g₂ : Matrix (Fin 3) (Fin 3) k) := by rw [hmat]
  set sG : GL (Fin 3) k := Matrix.SpecialLinearGroup.toGL s₁ with hsG
  have hsGmat : (sG : Matrix (Fin 3) (Fin 3) k) = (s₁ : Matrix (Fin 3) (Fin 3) k) := rfl
  have hdet : (sG : Matrix (Fin 3) (Fin 3) k).det = 1 := by
    rw [hsGmat]; exact s₁.2
  have hcube_id : ∀ (a : A) (M : GL (Fin 3) k), IsConjBy (φ a) M →
      ∃ c : kˣ, ((M : Matrix (Fin 3) (Fin 3) k)) ^ 3 =
        (c : k) • (1 : Matrix (Fin 3) (Fin 3) k) := by
    intro a M hM
    obtain ⟨c, hc⟩ := eq_scalar_of_forall_commute (M ^ 3) (fun t => by
      have h3 := (hM.pow 3) t
      have h4 : (φ a ^ 3) t = t := by rw [hφ3 a]; rfl
      rw [h4] at h3
      exact comm_of_conj_eq h3)
    exact ⟨c, by rw [← Units.val_pow_eq_pow_val]; exact hc⟩
  obtain ⟨c₀, hc₀⟩ := hcube_id f₁ sG hs₁conj
  obtain ⟨c₂, hc₂⟩ := hcube_id f₂ g₂ hg₂
  have hns : ∀ c : k, (sG : Matrix (Fin 3) (Fin 3) k) ≠ c • 1 := by
    intro c hc
    apply hf₁ker
    rw [MonoidHom.mem_ker]
    ext1 t
    apply Subtype.ext
    rw [hs₁conj t]
    apply conj_eq_self_of_comm
    rw [hc]
    simp
  obtain ⟨ωu, hωu⟩ : ∃ ω : kˣ, orderOf ω = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply exists_prime_orderOf_dvd_card' 3
    rw [Nat.card_units]
    exact h3
  have hω3 : (ωu : k) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ωu
    rw [hωu] at this
    simpa [← Units.val_pow_eq_pow_val] using congrArg Units.val this
  have hω1 : (ωu : k) ≠ 1 := by
    intro h
    have : ωu = 1 := Units.ext h
    rw [this, orderOf_one] at hωu
    omega
  obtain ⟨P, u, v, hu, hv⟩ := exists_common_frame hω3 hω1 sG g₂ hcommg.symm hdet hc₀ hc₂ hns
  have hu3 := diag_cube_of_conj P sG u _ hc₀ hu
  have hv3 := diag_cube_of_conj P g₂ v _ hc₂ hv
  have hT := closure_fixed_eq_top P sG g₂ u v hu hv
    (fun a b => (hu3 a).trans (hu3 b).symm) (fun a b => (hv3 a).trans (hv3 b).symm)
  have hf₂C : (f₂ : X) ∉ C := fun h =>
    hf₂'not (Subgroup.mem_sup_left (hAC f₂ h))
  have hnot := not_mem_zpowers_of_not_mem_sup (z := z) (f₁ := (f₁ : X)) (f₂ := f₂')
    (hAe.2 f₂' hf₂'A |> fun h => by simpa using h) hf₂'not
  have hf₁C : (f₁ : X) ∉ C := fun h => hf₁ker ((hker f₁).2 h)
  have hf₁f₂C : ((f₁ * f₂ : A) : X) ∉ C := fun h => hnot.1 (hAC (f₁ * f₂) h)
  have hf₁f₂sqC : ((f₁ * f₂ ^ 2 : A) : X) ∉ C := fun h => hnot.2 (hAC (f₁ * f₂ ^ 2) h)
  have hfix : ∀ (f : A) (M : GL (Fin 3) k), IsConjBy (φ f) M → (f : X) ∉ C →
      ∀ x : SpecialLinearGroup (Fin 3) k,
        (M : Matrix (Fin 3) (Fin 3) k) * (x : Matrix (Fin 3) (Fin 3) k) =
          (x : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k) →
        (ψ x : K) ∈ {y : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧
          f * (y : X) * f⁻¹ = y} := by
    intro f M hM hfC x hx
    refine ⟨(f : X), f.2, hfC, ?_⟩
    have h1 := hφψ f x
    rw [hM.fix hx] at h1
    exact h1.symm
  have hsub : ∀ x ∈ {x : SpecialLinearGroup (Fin 3) k |
      (∃ M ∈ ({sG, g₂, sG * g₂, sG * g₂ ^ 2} : Set (GL (Fin 3) k)),
        (M : Matrix (Fin 3) (Fin 3) k) * (x : Matrix (Fin 3) (Fin 3) k) =
          (x : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k))},
      (ψ x : K) ∈ {y : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧
          f * (y : X) * f⁻¹ = y} := by
    rintro x ⟨M, hM, hMx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact hfix f₁ _ hs₁conj hf₁C x hMx
    · exact hfix f₂ _ hg₂ hf₂C x hMx
    · have hc : IsConjBy (φ (f₁ * f₂)) (sG * g₂) := by
        rw [map_mul]; exact hs₁conj.mul hg₂
      exact hfix (f₁ * f₂) _ hc hf₁f₂C x hMx
    · have hc : IsConjBy (φ (f₁ * f₂ ^ 2)) (sG * g₂ ^ 2) := by
        rw [map_mul, map_pow]; exact hs₁conj.mul (hg₂.pow 2)
      exact hfix (f₁ * f₂ ^ 2) _ hc hf₁f₂sqC x hMx
  rw [eq_top_iff]
  have hmap : Subgroup.map (ψ : SpecialLinearGroup (Fin 3) k →* K) (Subgroup.closure
      {x : SpecialLinearGroup (Fin 3) k |
      (∃ M ∈ ({sG, g₂, sG * g₂, sG * g₂ ^ 2} : Set (GL (Fin 3) k)),
        (M : Matrix (Fin 3) (Fin 3) k) * (x : Matrix (Fin 3) (Fin 3) k) =
          (x : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k))}) = ⊤ := by
    rw [hT, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr ψ.surjective
  rw [MonoidHom.map_closure] at hmap
  rw [← hmap]
  exact Subgroup.closure_mono (Set.image_subset_iff.mpr (fun x hx => hsub x hx))


theorem exists_generating_elemAbelian
    {X : Type} [Group X] [Finite X] (R : Sylow 3 X) (K : Subgroup X) [K.Normal] (z : X)
    {k : Type} [Field k] [Finite k]
    (h3 : 3 ∣ Nat.card k - 1) (h4 : Nat.card k ≠ 4)
    (hσ : ∀ σ : k ≃+* k, σ ^ 3 = 1 → σ = 1)
    (hK : commutator K = ⊤)
    (e : K ⧸ Subgroup.center K ≃* LinearFlag.projectiveSL 3 k)
    (hzc : z ∈ Subgroup.center X) (hzK : z ∈ K) (hz3 : orderOf z = 3)
    (hΩ : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z)
    (hrank : Open.pRank 3 (R : Subgroup X) = 3) :
    ∃ A : Subgroup X, A ≤ (R : Subgroup X) ∧ Open.IsElemAbelian 3 A ∧ 3 ≤ Open.pRank 3 A ∧
      Subgroup.closure {x : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧
        f * (x : X) * f⁻¹ = x} = ⊤ := by
  have hzcenter : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro κ
    exact Subtype.ext (Subgroup.mem_center_iff.mp hzc κ)
  have hZK : Subgroup.center K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hzcenter
    have hz1 : z = 1 := congrArg Subtype.val hzcenter
    rw [hz1, orderOf_one] at hz3
    omega
  obtain ⟨ψ⟩ := exists_mulEquiv_specialLinear h3 h4 hK e hZK
  exact exists_generating_elemAbelian_of_equiv R K z h3 hσ ψ hzc hz3 hΩ hrank

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
