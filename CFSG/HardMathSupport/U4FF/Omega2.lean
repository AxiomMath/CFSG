module

public import CFSG.HardMathSupport.U4FF.Wedge
public import CFSG.HardMathSupport.U4FF.Descent
public import CFSG.HardMathSupport.U4FF.OmegaGroup
public import CFSG.HardMathSupport.U4FF.Model
public import CFSG.RankThree.PartOne.CTP.SU4EvenBridge

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.RankThree.PartOne.CTP.SU4Even CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.RankThreeUC CFSG.Open
open scoped Matrix

theorem exists_ringEquiv_comp_eq {E k : Type*} [Field E] [Finite E] [Field k] (β γ : E →+* k) :
    ∃ θ : E ≃+* E, ∀ x, β x = γ (θ x) := by
  classical
  have := Fintype.ofFinite E
  set q := Fintype.card E with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  have hpdeg : ((Polynomial.X ^ q - Polynomial.X : Polynomial k)).natDegree = q :=
    FiniteField.X_pow_card_sub_X_natDegree_eq k hq1
  have hp0 : (Polynomial.X ^ q - Polynomial.X : Polynomial k) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hpdeg
    omega
  set Rts : Finset k := (Polynomial.X ^ q - Polynomial.X : Polynomial k).roots.toFinset with hRts
  have hRcard : Rts.card ≤ q :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans hpdeg.le)
  have himg : ∀ f : E →+* k, Finset.univ.image f = Rts := fun f => by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
      rw [hRts, Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ← map_pow,
        FiniteField.pow_card, sub_self]
    · rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ]
      exact hRcard
  have hex : ∀ x : E, ∃ y : E, γ y = β x := fun x => by
    have hx : β x ∈ Finset.univ.image β := Finset.mem_image_of_mem _ (Finset.mem_univ x)
    rw [himg β, ← himg γ] at hx
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hx
    exact ⟨y, hy⟩
  choose θ hθ using hex
  let θ' : E →+* E :=
    { toFun := θ
      map_one' := γ.injective (by rw [hθ, map_one, map_one])
      map_zero' := γ.injective (by rw [hθ, map_zero, map_zero])
      map_mul' := fun x y => γ.injective (by rw [hθ, map_mul, map_mul, hθ, hθ])
      map_add' := fun x y => γ.injective (by rw [hθ, map_add, map_add, hθ, hθ]) }
  have hinj : Function.Injective θ' := fun x y h => β.injective (by
    rw [← hθ x, ← hθ y]
    exact congrArg γ h)
  exact ⟨RingEquiv.ofBijective θ' ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩,
    fun x => (hθ x).symm⟩

theorem comp2_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (g : Matrix (Fin 4) (Fin 4) A) : comp2 (g.map f) = (comp2 g).map f := by
  ext a b
  simp [comp2]

@[expose] def reindexGL {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {E : Type*} [CommRing E] (e : ι ≃ κ) : GL ι E ≃* GL κ E :=
  Units.mapEquiv (Matrix.reindexAlgEquiv E E e).toMulEquiv

theorem exists_mulEquiv_su_statedOmega
    {E K : Type} [Field E] [Finite E] [CharP E 2] [Field K]
    [Finite K] [CharP K 2] {n : ℕ} (hE : Nat.card E = 2 ^ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {b c : E} (hirr : ∀ s : E, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (↥(SU (unitaryInvolution K 2 n) 4) ≃* ↥(StatedOmega (StatedQuadMinus 3 E b c))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinDataEven hE hK hirr
  letI : Algebra E K := inst
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hperfSU : Group.IsPerfect (SU (unitaryInvolution K 2 n) 4) :=
    (isQuasisimple_SU hK (by norm_num) (by simp)).1
  let Φ : spinGroup (quadMinus 3 E b c) ≃* SU (unitaryInvolution K 2 n) 4 := D.phiSUEven hK hirr
  have hSpin : Group.IsPerfect (spinGroup (quadMinus 3 E b c)) :=
    Group.IsPerfect.ofSurjective (f := Φ.symm.toMonoidHom) Φ.symm.surjective
  exact ⟨Φ.symm.trans (spinMinusThreeEquiv hirr h2 hSpin)⟩

theorem omega2Input_holds :
    ∀ (S : Type) [CommGroup S] (n : ℕ) (L : Subgroup (MulAut S)), IsU4Group n L →
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = (2 ^ n) ^ 2 →
      ∀ (η : ↥L ≃* ↥(SU (unitaryInvolution K 2 n) 4))
        (E : Type) [Field E] [Finite E], Nat.card E = 2 ^ n →
        ∀ (ε : S ≃* Multiplicative (Fin 6 → E)) (R : ↥L →* GL (Fin 6) E),
          (∀ (l : ↥L) (s : S), ε ((l : MulAut S) s) =
            Multiplicative.ofAdd ((R l : Matrix (Fin 6) (Fin 6) E).mulVec
              (Multiplicative.toAdd (ε s)))) →
          ∀ (k : Type) [Field k] [Algebra E k] [Algebra K k] (P : GL (Fin 6) k) (i₀ : ℕ),
            (∀ l : ↥L, (P : Matrix (Fin 6) (Fin 6) k) *
                (R l : Matrix (Fin 6) (Fin 6) E).map (algebraMap E k) =
              comp2 (((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
                (fun x => algebraMap K k (x ^ 2 ^ i₀))) * (P : Matrix (Fin 6) (Fin 6) k)) →
            NaturalOmega6 n L := by
  intro S _ n L hL K _ _ _ hK η E _ _ hE ε₀ R hR k _ _ _ P i₀ hP
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ n := one_le_of_isU4Group hL
  haveI hEchar : CharP E 2 := by
    have h := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two hn hE
    haveI := ringChar.charP E
    rwa [h] at this
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  haveI hkchar : CharP k 2 := charP_of_injective_algebraMap (algebraMap K k).injective 2
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic E
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinDataEven hE hK hirr
  letI : Algebra E K := inst
  let Φ : spinGroup (quadMinus 3 E b c) ≃* SU (unitaryInvolution K 2 n) 4 :=
    D.phiSUEven hK hirr
  have hperfSU : Group.IsPerfect (SU (unitaryInvolution K 2 n) 4) :=
    (isQuasisimple_SU hK (by norm_num) (by simp)).1
  have hSpin : Group.IsPerfect (spinGroup (quadMinus 3 E b c)) :=
    Group.IsPerfect.ofSurjective (f := Φ.symm.toMonoidHom) Φ.symm.surjective
  let Ω := spinMinusThreeEquiv hirr h2 hSpin
  let ξ : ↥L ≃* spinGroup (quadMinus 3 E b c) := η.trans Φ.symm
  let g : ↥L → Matrix (Fin 4) (Fin 4) K := fun l =>
    ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  have hg : ∀ l, D.PhiMon (ξ l) = g l := fun l => by
    have h1 : Φ (ξ l) = η l := Φ.apply_symm_apply (η l)
    have h3 := congrArg (fun x : SU (unitaryInvolution K 2 n) 4 =>
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h1
    exact (D.coe_PhiSUEven hirr (ξ l)).symm.trans h3
  have hSU : ∀ l, D.PhiGL (ξ l) ∈ SU (unitaryInvolution K 2 n) 4 := fun l =>
    D.PhiGL_mem_SU hirr (ξ l)
  have hW : ∀ l, Tm D * ((spinMatrix (quadMinus 3 E b c) (ξ l) : Matrix VIdx VIdx E).submatrix
      colEquiv colEquiv).map (algebraMap E K) = comp2 (g l) * Tm D := fun l => by
    rw [← hg l]
    exact tm_mul_spin D (ξ l) (hSU l)
  haveI : ExpChar k 2 := ExpChar.prime Nat.prime_two
  let α : K →+* k := algebraMap K k
  let ι₀ : E →+* K := algebraMap E K
  let β : E →+* k := algebraMap E k
  let lam : K →+* k := (iterateFrobenius k 2 i₀).comp α
  let γ : E →+* k := lam.comp ι₀
  have hlam : ∀ x : K, lam x = α (x ^ 2 ^ i₀) := fun x => by
    simp [lam, iterateFrobenius_def, map_pow]
  have hP' : ∀ l, (P : Matrix (Fin 6) (Fin 6) k) * (R l : Matrix (Fin 6) (Fin 6) E).map β =
      comp2 ((g l).map lam) * (P : Matrix (Fin 6) (Fin 6) k) := fun l => by
    have h := hP l
    have e : (g l).map (fun x => algebraMap K k (x ^ 2 ^ i₀)) = (g l).map lam := by
      ext i j
      simp [hlam, α]
    rw [e] at h
    exact h
  let Tl : GL (Fin 6) k := Matrix.GeneralLinearGroup.map lam (TmGL D)
  have hTl : (Tl : Matrix (Fin 6) (Fin 6) k) = (Tm D).map lam := rfl
  let ρ₂ : ↥L →* GL (Fin 6) E :=
    (reindexGL colEquiv.symm).toMonoidHom.comp ((spinMatrix (quadMinus 3 E b c)).comp
      ξ.toMonoidHom)
  have hρ₂ : ∀ l, ((ρ₂ l : GL (Fin 6) E) : Matrix (Fin 6) (Fin 6) E) =
      (spinMatrix (quadMinus 3 E b c) (ξ l) : Matrix VIdx VIdx E).submatrix colEquiv colEquiv :=
    fun l => rfl
  have hW' : ∀ l, (Tl : Matrix (Fin 6) (Fin 6) k) * (ρ₂ l : Matrix (Fin 6) (Fin 6) E).map γ =
      comp2 ((g l).map lam) * (Tl : Matrix (Fin 6) (Fin 6) k) := fun l => by
    have h := congrArg (fun X : Matrix (Fin 6) (Fin 6) K => X.map lam) (hW l)
    simp only [Matrix.map_mul, Matrix.map_map, ← comp2_map] at h
    rw [hTl, hρ₂]
    exact h
  let Q : GL (Fin 6) k := Tl⁻¹ * P
  have hQ : ∀ l, (Q : Matrix (Fin 6) (Fin 6) k) * (R l : Matrix (Fin 6) (Fin 6) E).map β =
      (ρ₂ l : Matrix (Fin 6) (Fin 6) E).map γ * (Q : Matrix (Fin 6) (Fin 6) k) := fun l => by
    have h1 : (Tl⁻¹ : GL (Fin 6) k).val * (Tl : Matrix (Fin 6) (Fin 6) k) = 1 := Units.inv_mul Tl
    have h2 : (Tl : Matrix (Fin 6) (Fin 6) k) * (Tl⁻¹ : GL (Fin 6) k).val = 1 := Units.mul_inv Tl
    have hcomm : (ρ₂ l : Matrix (Fin 6) (Fin 6) E).map γ * (Tl⁻¹ : GL (Fin 6) k).val =
        (Tl⁻¹ : GL (Fin 6) k).val * comp2 ((g l).map lam) := by
      calc (ρ₂ l : Matrix (Fin 6) (Fin 6) E).map γ * (Tl⁻¹ : GL (Fin 6) k).val
          = ((Tl⁻¹ : GL (Fin 6) k).val * (Tl : Matrix (Fin 6) (Fin 6) k)) *
              (ρ₂ l : Matrix (Fin 6) (Fin 6) E).map γ * (Tl⁻¹ : GL (Fin 6) k).val := by
            rw [h1, Matrix.one_mul]
        _ = (Tl⁻¹ : GL (Fin 6) k).val * ((Tl : Matrix (Fin 6) (Fin 6) k) *
              (ρ₂ l : Matrix (Fin 6) (Fin 6) E).map γ) * (Tl⁻¹ : GL (Fin 6) k).val := by
            simp only [Matrix.mul_assoc]
        _ = (Tl⁻¹ : GL (Fin 6) k).val * (comp2 ((g l).map lam) *
              (Tl : Matrix (Fin 6) (Fin 6) k)) * (Tl⁻¹ : GL (Fin 6) k).val := by rw [hW' l]
        _ = (Tl⁻¹ : GL (Fin 6) k).val * comp2 ((g l).map lam) := by
            simp only [Matrix.mul_assoc, h2, Matrix.mul_one]
    show (Tl⁻¹ * P : GL (Fin 6) k).val * _ = _ * (Tl⁻¹ * P : GL (Fin 6) k).val
    rw [Units.val_mul, Matrix.mul_assoc, hP' l, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hcomm]
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comp_eq β γ
  let Rθ : ↥L →* GL (Fin 6) E := (Matrix.GeneralLinearGroup.map (θ : E →+* E)).comp R
  have hRθ : ∀ l, ((Rθ l : GL (Fin 6) E) : Matrix (Fin 6) (Fin 6) E) =
      (R l : Matrix (Fin 6) (Fin 6) E).map θ := fun l => rfl
  have hβγ : ∀ l, (R l : Matrix (Fin 6) (Fin 6) E).map β =
      ((R l : Matrix (Fin 6) (Fin 6) E).map θ).map γ := fun l => by
    rw [Matrix.map_map]
    congr 1
    funext x
    exact hθ x
  obtain ⟨M, hM⟩ := exists_conj_of_conj_extend γ Rθ ρ₂ Q (fun l => by
    rw [hRθ, ← hβγ]
    exact hQ l)
  obtain ⟨ψ, hψ⟩ := exists_coord_equiv colEquiv ε₀ R hR θ M
    ((spinMatrix (quadMinus 3 E b c)).comp ξ.toMonoidHom) (fun l => by
      have h := hM l
      rw [hRθ, hρ₂] at h
      exact h)
  refine ⟨E, inferInstance, inferInstance, b, c, hE, hirr, ξ.trans Ω, ψ, fun l s => ?_⟩
  rw [hψ l s]
  rfl

end CFSG.HardMathSupport.U4FF
