module

public import CFSG.HardMathSupport.U4FF.Natural4Defs
public import CFSG.HardMathSupport.U4FF.Descent
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis.RankThreeUC CFSG.Open CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped Matrix

theorem natural4Input_holds : Natural4Input := by
  intro S _ n L hL hirr K _ _ _ hK η E _ _ ι ε R hR k _ _ P i₀ hP
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  let β : E →+* k := algebraMap E k
  let fr : K →+* K := iterateFrobenius K 2 i₀
  let f : K →+* E := ι.comp fr
  let R₀ : ↥L →* GL (Fin 4) E :=
    (Matrix.GeneralLinearGroup.map f).comp
      ((SU (unitaryInvolution K 2 n) 4).subtype.comp η.toMonoidHom)
  have hR₀ : ∀ l, ((R₀ l : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) =
      ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map f := fun l => rfl
  have hP' : ∀ l, (P : Matrix (Fin 4) (Fin 4) k) * (R l : Matrix (Fin 4) (Fin 4) E).map β =
      (R₀ l : Matrix (Fin 4) (Fin 4) E).map β * (P : Matrix (Fin 4) (Fin 4) k) := fun l => by
    have h := hP l
    have e : ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (fun x => β (ι (x ^ 2 ^ i₀))) =
        (R₀ l : Matrix (Fin 4) (Fin 4) E).map β := by
      rw [hR₀, Matrix.map_map]
      ext i j
      simp [f, fr, iterateFrobenius_def]
    rw [← e]
    exact h
  obtain ⟨M, hM⟩ := exists_conj_of_conj_extend β R R₀ P hP'
  let vec : S → (Fin 4 → E) := fun s => (M : Matrix (Fin 4) (Fin 4) E) *ᵥ Multiplicative.toAdd (ε s)
  have hvec_mul : ∀ s t, vec (s * t) = vec s + vec t := fun s t => by
    simp only [vec, map_mul, toAdd_mul, Matrix.mulVec_add]
  have hvec_one : vec 1 = 0 := by
    simp [vec]
  have hvec_inv : ∀ s, vec s⁻¹ = -vec s := fun s => by
    simp only [vec, map_inv, toAdd_inv, Matrix.mulVec_neg]
  have hvec_surj : ∀ w : Fin 4 → E, ∃ s, vec s = w := fun w => by
    refine ⟨ε.symm (Multiplicative.ofAdd ((M⁻¹ : GL (Fin 4) E).val *ᵥ w)), ?_⟩
    simp only [vec, MulEquiv.apply_symm_apply, toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [Units.mul_inv, Matrix.one_mulVec]
  have hvec_act : ∀ (l : ↥L) (s : S), vec ((l : MulAut S) s) = (R₀ l : Matrix (Fin 4) (Fin 4) E) *ᵥ
      vec s := fun l s => by
    simp only [vec, hR l s, toAdd_ofAdd, Matrix.mulVec_mulVec, hM l]
  let W : Subgroup S :=
    { carrier := {s | ∀ i, vec s i ∈ ι.range}
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
    change vec (x w) i ∈ ι.range
    rw [show (x : MulAut S) = ((⟨x, hx⟩ : ↥L) : MulAut S) from rfl, h, hR₀]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (hw j)
    exact ⟨fr ((η ⟨x, hx⟩ : GL (Fin 4) K) i j), rfl⟩
  have hsurj : Function.Surjective ι := by
    rcases hirr W hWinv with hbot | htop
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
  let ιe : K ≃+* E := RingEquiv.ofBijective ι ⟨ι.injective, hsurj⟩
  let fre : K ≃+* K := RingEquiv.ofBijective fr
    ⟨fr.injective, Finite.injective_iff_surjective.1 fr.injective⟩
  let τ : E ≃+* K := ιe.symm.trans fre.symm
  have hτ : ∀ x : K, τ (f x) = x := fun x => by
    change fre.symm (ιe.symm (ι (fr x))) = x
    have h1 : ιe.symm (ι (fr x)) = fr x := ιe.symm_apply_apply (fr x)
    rw [h1]
    exact fre.symm_apply_apply x
  obtain ⟨Pw, hPw⟩ := exists_wittMatrix hK 4
  let εL : ↥L ≃* ↥(StatedSU 4 (2 ^ n) K) :=
    (η.trans (conjEquiv Pw hPw)).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 4))
  have hεL : ∀ l, ((εL l : ↥(StatedSU 4 (2 ^ n) K)) : GL (Fin 4) K) =
      Pw * ((η l : GL (Fin 4) K)) * Pw⁻¹ := fun l => coe_conjEquiv Pw hPw (η l)
  let M' : GL (Fin 4) K := Pw * Matrix.GeneralLinearGroup.map (τ : E →+* K) M
  let ρ : ↥L →* GL (Fin 4) K := (StatedSU 4 (2 ^ n) K).subtype.comp εL.toMonoidHom
  have hMρ : ∀ l : ↥L, (M' : Matrix (Fin 4) (Fin 4) K) * (R l : Matrix (Fin 4) (Fin 4) E).map τ =
      (ρ l : Matrix (Fin 4) (Fin 4) K).submatrix (Equiv.refl (Fin 4)) (Equiv.refl (Fin 4)) *
        (M' : Matrix (Fin 4) (Fin 4) K) := fun l => by
    have h1 : (M : Matrix (Fin 4) (Fin 4) E).map τ * (R l : Matrix (Fin 4) (Fin 4) E).map τ =
        ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (M : Matrix (Fin 4) (Fin 4) E).map τ := by
      have h := congrArg (fun X : Matrix (Fin 4) (Fin 4) E => X.map τ) (hM l)
      simp only [Matrix.map_mul, hR₀, Matrix.map_map] at h
      have e : ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (⇑τ ∘ ⇑f) =
          ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
        ext i j
        simp [hτ]
      rw [e] at h
      exact h
    have h2 : ((Pw⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (Pw : Matrix (Fin 4) (Fin 4) K) = 1 := Units.inv_mul Pw
    have hM'val : (M' : Matrix (Fin 4) (Fin 4) K) =
        (Pw : Matrix (Fin 4) (Fin 4) K) * (M : Matrix (Fin 4) (Fin 4) E).map τ := rfl
    have hρval : (ρ l : Matrix (Fin 4) (Fin 4) K) = (Pw : Matrix (Fin 4) (Fin 4) K) *
        ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((Pw⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      show ((εL l : ↥(StatedSU 4 (2 ^ n) K)) : GL (Fin 4) K).val = _
      rw [hεL, Units.val_mul, Units.val_mul]
    rw [hM'val, hρval]
    simp only [Equiv.coe_refl, Matrix.submatrix_id_id]
    calc (Pw : Matrix (Fin 4) (Fin 4) K) * (M : Matrix (Fin 4) (Fin 4) E).map τ *
          (R l : Matrix (Fin 4) (Fin 4) E).map τ
        = (Pw : Matrix (Fin 4) (Fin 4) K) * ((M : Matrix (Fin 4) (Fin 4) E).map τ *
          (R l : Matrix (Fin 4) (Fin 4) E).map τ) := by rw [Matrix.mul_assoc]
      _ = (Pw : Matrix (Fin 4) (Fin 4) K) * (((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (M : Matrix (Fin 4) (Fin 4) E).map τ) := by rw [h1]
      _ = (Pw : Matrix (Fin 4) (Fin 4) K) * ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (((Pw⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Pw : Matrix (Fin 4) (Fin 4) K)) *
            (M : Matrix (Fin 4) (Fin 4) E).map τ := by
          rw [h2, Matrix.mul_one, Matrix.mul_assoc]
      _ = (Pw : Matrix (Fin 4) (Fin 4) K) * ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((Pw⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            ((Pw : Matrix (Fin 4) (Fin 4) K) * (M : Matrix (Fin 4) (Fin 4) E).map τ) := by
          simp only [Matrix.mul_assoc]
  obtain ⟨ψ, hψ⟩ := exists_coord_equiv (Equiv.refl (Fin 4)) ε R hR τ M' ρ hMρ
  exact ⟨K, inferInstance, inferInstance, hK, εL, ψ, fun l s => hψ l s⟩

end CFSG.HardMathSupport.U4FF
