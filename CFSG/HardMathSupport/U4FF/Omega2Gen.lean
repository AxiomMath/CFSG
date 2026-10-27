module

public import CFSG.HardMathSupport.U4FF.ClassFinalDefs
public import CFSG.HardMathSupport.U4FF.Omega2

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.RankThree.PartOne.CTP.SU4Even CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.RankThreeUC CFSG.Open
open scoped Matrix

theorem exists_ringHom_of_card {E₀ E : Type} [Field E₀] [Finite E₀] [CharP E₀ 2] [Field E]
    [Finite E] [CharP E 2] {n m : ℕ} (h₀ : Nat.card E₀ = 2 ^ n) (hE : Nat.card E = 2 ^ (n * m)) :
    Nonempty (E₀ →+* E) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (ZMod 2) E₀ := ZMod.algebra _ _
  letI : Algebra (ZMod 2) E := ZMod.algebra _ _
  have h1 : Module.finrank (ZMod 2) E₀ = n := by
    have h := FiniteField.pow_finrank_eq_natCard 2 E₀
    rw [h₀] at h
    exact Nat.pow_right_injective (le_refl 2) h
  have h2 : Module.finrank (ZMod 2) E = n * m := by
    have h := FiniteField.pow_finrank_eq_natCard 2 E
    rw [hE] at h
    exact Nat.pow_right_injective (le_refl 2) h
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := E₀) (L := E)
    (by rw [h1, h2]; exact dvd_mul_right n m)
  exact ⟨f.toRingHom⟩

theorem omega2InputGen_holds :
    Omega2InputGen := by
  intro S _ n L hL hirrL K _ _ _ hK η E _ _ m hE ε₀ R hR k _ _ _ P i₀ hP
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ n := one_le_of_isU4Group hL
  have hnm : 1 ≤ n * m := by
    have h1 : 1 < Nat.card E := Finite.one_lt_card
    rw [hE] at h1
    by_contra h0
    have : n * m = 0 := by omega
    rw [this] at h1
    simp at h1
  haveI hEchar : CharP E 2 := by
    have h := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two hnm hE
    haveI := ringChar.charP E
    rwa [h] at this
  haveI hkchar : CharP k 2 := charP_of_injective_algebraMap (algebraMap K k).injective 2
  let E₀ : Type := GaloisField 2 n
  have hE₀ : Nat.card E₀ = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic E₀
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinDataEven hE₀ hK hirr
  letI : Algebra E₀ K := inst
  let Φ : spinGroup (quadMinus 3 E₀ b c) ≃* SU (unitaryInvolution K 2 n) 4 :=
    D.phiSUEven hK hirr
  let ξ : ↥L ≃* spinGroup (quadMinus 3 E₀ b c) := η.trans Φ.symm
  let g : ↥L → Matrix (Fin 4) (Fin 4) K := fun l =>
    ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  have hg : ∀ l, D.PhiMon (ξ l) = g l := fun l => by
    have h1 : Φ (ξ l) = η l := Φ.apply_symm_apply (η l)
    have h3 := congrArg (fun x : SU (unitaryInvolution K 2 n) 4 =>
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h1
    exact (D.coe_PhiSUEven hirr (ξ l)).symm.trans h3
  have hSU : ∀ l, D.PhiGL (ξ l) ∈ SU (unitaryInvolution K 2 n) 4 := fun l =>
    D.PhiGL_mem_SU hirr (ξ l)
  have hW : ∀ l, Tm D * ((spinMatrix (quadMinus 3 E₀ b c) (ξ l) : Matrix VIdx VIdx E₀).submatrix
      colEquiv colEquiv).map (algebraMap E₀ K) = comp2 (g l) * Tm D := fun l => by
    rw [← hg l]
    exact tm_mul_spin D (ξ l) (hSU l)
  haveI : ExpChar k 2 := ExpChar.prime Nat.prime_two
  let α : K →+* k := algebraMap K k
  let ι₀ : E₀ →+* K := algebraMap E₀ K
  let β : E →+* k := algebraMap E k
  let lam : K →+* k := (iterateFrobenius k 2 i₀).comp α
  let γ : E₀ →+* k := lam.comp ι₀
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
  let ρ₂ : ↥L →* GL (Fin 6) E₀ :=
    (reindexGL colEquiv.symm).toMonoidHom.comp ((spinMatrix (quadMinus 3 E₀ b c)).comp
      ξ.toMonoidHom)
  have hρ₂ : ∀ l, ((ρ₂ l : GL (Fin 6) E₀) : Matrix (Fin 6) (Fin 6) E₀) =
      (spinMatrix (quadMinus 3 E₀ b c) (ξ l) : Matrix VIdx VIdx E₀).submatrix colEquiv colEquiv :=
    fun l => rfl
  have hW' : ∀ l, (Tl : Matrix (Fin 6) (Fin 6) k) * (ρ₂ l : Matrix (Fin 6) (Fin 6) E₀).map γ =
      comp2 ((g l).map lam) * (Tl : Matrix (Fin 6) (Fin 6) k) := fun l => by
    have h := congrArg (fun X : Matrix (Fin 6) (Fin 6) K => X.map lam) (hW l)
    simp only [Matrix.map_mul, Matrix.map_map, ← comp2_map] at h
    rw [hTl, hρ₂]
    exact h
  let Q : GL (Fin 6) k := Tl⁻¹ * P
  have hQ : ∀ l, (Q : Matrix (Fin 6) (Fin 6) k) * (R l : Matrix (Fin 6) (Fin 6) E).map β =
      (ρ₂ l : Matrix (Fin 6) (Fin 6) E₀).map γ * (Q : Matrix (Fin 6) (Fin 6) k) := fun l => by
    have h1 : (Tl⁻¹ : GL (Fin 6) k).val * (Tl : Matrix (Fin 6) (Fin 6) k) = 1 := Units.inv_mul Tl
    have h2 : (Tl : Matrix (Fin 6) (Fin 6) k) * (Tl⁻¹ : GL (Fin 6) k).val = 1 := Units.mul_inv Tl
    have hcomm : (ρ₂ l : Matrix (Fin 6) (Fin 6) E₀).map γ * (Tl⁻¹ : GL (Fin 6) k).val =
        (Tl⁻¹ : GL (Fin 6) k).val * comp2 ((g l).map lam) := by
      calc (ρ₂ l : Matrix (Fin 6) (Fin 6) E₀).map γ * (Tl⁻¹ : GL (Fin 6) k).val
          = ((Tl⁻¹ : GL (Fin 6) k).val * (Tl : Matrix (Fin 6) (Fin 6) k)) *
              (ρ₂ l : Matrix (Fin 6) (Fin 6) E₀).map γ * (Tl⁻¹ : GL (Fin 6) k).val := by
            rw [h1, Matrix.one_mul]
        _ = (Tl⁻¹ : GL (Fin 6) k).val * ((Tl : Matrix (Fin 6) (Fin 6) k) *
              (ρ₂ l : Matrix (Fin 6) (Fin 6) E₀).map γ) * (Tl⁻¹ : GL (Fin 6) k).val := by
            simp only [Matrix.mul_assoc]
        _ = (Tl⁻¹ : GL (Fin 6) k).val * (comp2 ((g l).map lam) *
              (Tl : Matrix (Fin 6) (Fin 6) k)) * (Tl⁻¹ : GL (Fin 6) k).val := by rw [hW' l]
        _ = (Tl⁻¹ : GL (Fin 6) k).val * comp2 ((g l).map lam) := by
            simp only [Matrix.mul_assoc, h2, Matrix.mul_one]
    show (Tl⁻¹ * P : GL (Fin 6) k).val * _ = _ * (Tl⁻¹ * P : GL (Fin 6) k).val
    rw [Units.val_mul, Matrix.mul_assoc, hP' l, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hcomm]
  obtain ⟨μ⟩ := exists_ringHom_of_card hE₀ hE
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comp_eq (β.comp μ) γ
  let ρ₃ : ↥L →* GL (Fin 6) E :=
    (Matrix.GeneralLinearGroup.map μ).comp
      ((Matrix.GeneralLinearGroup.map (θ.symm : E₀ →+* E₀)).comp ρ₂)
  have hρ₃ : ∀ l, ((ρ₃ l : GL (Fin 6) E) : Matrix (Fin 6) (Fin 6) E) =
      ((ρ₂ l : Matrix (Fin 6) (Fin 6) E₀).map θ.symm).map μ := fun l => rfl
  have hQ' : ∀ l, (Q : Matrix (Fin 6) (Fin 6) k) * (R l : Matrix (Fin 6) (Fin 6) E).map β =
      (ρ₃ l : Matrix (Fin 6) (Fin 6) E).map β * (Q : Matrix (Fin 6) (Fin 6) k) := fun l => by
    have e : (ρ₂ l : Matrix (Fin 6) (Fin 6) E₀).map γ =
        (ρ₃ l : Matrix (Fin 6) (Fin 6) E).map β := by
      rw [hρ₃, Matrix.map_map, Matrix.map_map]
      congr 1
      funext x
      have := hθ (θ.symm x)
      rw [RingEquiv.apply_symm_apply] at this
      exact this.symm
    rw [← e]
    exact hQ l
  obtain ⟨M, hM⟩ := exists_conj_of_conj_extend β R ρ₃ Q hQ'
  let vec : S → (Fin 6 → E) := fun s =>
    (M : Matrix (Fin 6) (Fin 6) E) *ᵥ Multiplicative.toAdd (ε₀ s)
  have hvec_mul : ∀ s t, vec (s * t) = vec s + vec t := fun s t => by
    simp only [vec, map_mul, toAdd_mul, Matrix.mulVec_add]
  have hvec_one : vec 1 = 0 := by
    simp [vec]
  have hvec_inv : ∀ s, vec s⁻¹ = -vec s := fun s => by
    simp only [vec, map_inv, toAdd_inv, Matrix.mulVec_neg]
  have hvec_surj : ∀ w : Fin 6 → E, ∃ s, vec s = w := fun w => by
    refine ⟨ε₀.symm (Multiplicative.ofAdd ((M⁻¹ : GL (Fin 6) E).val *ᵥ w)), ?_⟩
    simp only [vec, MulEquiv.apply_symm_apply, toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [Units.mul_inv, Matrix.one_mulVec]
  have hvec_act : ∀ (l : ↥L) (s : S), vec ((l : MulAut S) s) =
      (ρ₃ l : Matrix (Fin 6) (Fin 6) E) *ᵥ vec s := fun l s => by
    simp only [vec, hR l s, toAdd_ofAdd, Matrix.mulVec_mulVec, hM l]
  let W : Subgroup S :=
    { carrier := {s | ∀ i, vec s i ∈ μ.range}
      mul_mem' := fun {s t} hs ht i => by
        rw [hvec_mul, Pi.add_apply]
        exact add_mem (hs i) (ht i)
      one_mem' := fun i => by
        rw [hvec_one]
        exact zero_mem _
      inv_mem' := fun {s} hs i => by
        rw [hvec_inv, Pi.neg_apply]
        exact neg_mem (hs i) }
  have hWinv : ∀ x ∈ L, ∀ w ∈ W, x w ∈ W := by
    intro x hx w hw i
    have h := hvec_act ⟨x, hx⟩ w
    change vec (x w) i ∈ μ.range
    rw [show (x : MulAut S) = ((⟨x, hx⟩ : ↥L) : MulAut S) from rfl, h, hρ₃]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (hw j)
    exact ⟨θ.symm ((ρ₂ ⟨x, hx⟩ : GL (Fin 6) E₀) i j), rfl⟩
  have hsurj : Function.Surjective μ := by
    rcases hirrL W hWinv with hbot | htop
    · exfalso
      obtain ⟨s, hs⟩ := hvec_surj (Pi.single 0 1)
      have hsW : s ∈ W := fun i => by
        rw [hs]
        by_cases hi : i = 0
        · subst hi
          simp only [Pi.single_eq_same]
          exact ⟨1, map_one _⟩
        · rw [Pi.single_eq_of_ne hi]
          exact zero_mem _
      rw [hbot, Subgroup.mem_bot] at hsW
      rw [hsW, hvec_one] at hs
      have := congrFun hs 0
      simp at this
    · intro y
      obtain ⟨s, hs⟩ := hvec_surj (Pi.single 0 y)
      have hsW : s ∈ W := by rw [htop]; exact Subgroup.mem_top s
      have := hsW 0
      rw [hs, Pi.single_eq_same] at this
      exact this
  have hEn : Nat.card E = 2 ^ n := by
    rw [← hE₀]
    exact (Nat.card_congr (RingEquiv.ofBijective μ ⟨μ.injective, hsurj⟩).toEquiv).symm
  exact omega2Input_holds S n L hL K hK η E hEn ε₀ R hR k P i₀ hP

end CFSG.HardMathSupport.U4FF
