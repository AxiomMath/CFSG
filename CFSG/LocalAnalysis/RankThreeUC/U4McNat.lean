module

public import CFSG.LocalAnalysis.RankThreeUC.U4McOff
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFAbs
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmMinus

public section

namespace CFSG.LocalAnalysis.RankThreeUC.U4Mc

open Matrix CFSG.Quasithin CFSG.Open

variable {S : Type} [CommGroup S]

theorem natSU4_or_omega_of_abstract {n : ℕ} {L : Subgroup (MulAut S)}
    (h : RankThreeUC.NaturalU4Abstract n L) (hcomm : commV L = ⊤) (hfix : fixV L = ⊥) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
      Nonempty (NatSU4 n L F)) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F), Nat.card F = 2 ^ n ∧
      (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ (ε : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
        (ψ : S ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
        ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
          (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
            Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
            (Multiplicative.toAdd (ψ s)))) := by
  let e : ↥(commV L) ≃* S := (MulEquiv.subgroupCongr hcomm).trans Subgroup.topEquiv
  have he : ∀ s : S, ((e.symm s : ↥(commV L)) : S) = s := fun s => rfl
  have hker : ∀ {X : Type} [Group X] (φ : ↥(commV L) →* X),
      φ.ker = (fixV L).subgroupOf (commV L) → Function.Injective φ := by
    intro X _ φ hφ
    rw [← MonoidHom.ker_eq_bot_iff, hφ, hfix]
    exact Subgroup.bot_subgroupOf _
  rcases h with ⟨F, hF, hFin, hcard, ε, φ, hs, hk, heq⟩ |
    ⟨F, hF, hFin, b, c, hcard, hirr, ε, φ, hs, hk, heq⟩
  · refine Or.inl ⟨F, hF, hFin, hcard, ⟨⟨ε, e.symm.trans (MulEquiv.ofBijective φ ⟨hker φ hk, hs⟩),
      fun l s => ?_⟩⟩⟩
    exact heq l (e.symm s) (e.symm ((l : MulAut S) s)) (by rw [he, he])
  · refine Or.inr ⟨F, hF, hFin, b, c, hcard, hirr, ε,
      e.symm.trans (MulEquiv.ofBijective φ ⟨hker φ hk, hs⟩), fun l s => ?_⟩
    exact heq l (e.symm s) (e.symm ((l : MulAut S) s)) (by rw [he, he])

theorem quad_mulVec_of_mem_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Q : (ι → K) → K} {g : GL ι K} (hg : g ∈ StatedOmega Q) (v : ι → K) :
    Q ((g : Matrix ι ι K) *ᵥ v) = Q v := by
  let I : Subgroup (GL ι K) :=
    { carrier := {A | ∀ v : ι → K, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}
      mul_mem' := fun {A B} hA hB v => by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
      one_mem' := fun v => by rw [Units.val_one, Matrix.one_mulVec]
      inv_mem' := fun {A} hA v => by
        rw [← hA ((A⁻¹ : GL ι K) *ᵥ v), Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.one_mulVec] }
  have hcore : CFSG.MatrixModel.isometryCore Q ≤ I := (Subgroup.closure_le I).mpr fun A hA => hA
  have hle : StatedOmega Q ≤ I :=
    Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => I.mul_mem
      (I.mul_mem (I.mul_mem (hcore h₁) (hcore h₂)) (I.inv_mem (hcore h₁))) (I.inv_mem (hcore h₂))
  exact hle hg v

theorem exists_cubeRoot_of_even {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : Even n) : ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, rfl⟩ := hn
  have h3 : 3 ∣ Fintype.card Fˣ := by
    have e : 2 ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hF, e]
    have h : 1 ≡ 4 ^ m [MOD 3] := by
      have := (show 1 ≡ 4 [MOD 3] by decide).pow m
      rwa [one_pow] at this
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 h3
  have hu3 : (u : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : (u : F) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    omega
  refine ⟨u, ?_⟩
  have h : ((u : F) - 1) * ((u : F) ^ 2 + u + 1) = 0 := by linear_combination hu3
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hu1
  · exact h

theorem false_of_omegaMinus {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hg : g ∈ StatedOmega (StatedQuadMinus 3 F b c))
    (hg3 : ∀ v, (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
      ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
        ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          v)) = v)
    (hfix : ∀ v, (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v = v → v = 0) : False := by
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨ω, hω⟩ := exists_cubeRoot_of_even hF hn
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hsing : ∀ μ : F, μ ^ 2 ≠ 1 → ∀ w ∈ LinearMap.ker (Matrix.toLin'
      (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) -
      μ • LinearMap.id), CFSG.LieType.Universal.Spin.quadMinus 3 F b c w = 0 := by
    intro μ hμ w hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hw
    have h1 := quad_mulVec_of_mem_statedOmega hg w
    rw [hw, ← CFSG.LieType.Universal.Spin.coe_quadMinus, QuadraticMap.map_smul, smul_eq_mul] at h1
    have h2 : (μ ^ 2 - 1) * CFSG.LieType.Universal.Spin.quadMinus 3 F b c w = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hμ)
  have hμ1 : ω ^ 2 ≠ 1 := by
    intro h
    have hω0 : ω = 0 := by linear_combination hω - h - h2F
    rw [hω0] at h
    norm_num at h
  have hμ2 : (ω ^ 2) ^ 2 ≠ 1 := by
    intro h
    have hω' : ω = 1 := by linear_combination h - ω * hω3
    rw [hω'] at hω
    have h10 : (1 : F) = 0 := by linear_combination hω - h2F
    exact one_ne_zero h10
  have hd1 := CFSG.StandardType.OrdPOm.finrank_le_of_singular_quadMinus hirr
    (by norm_num : 1 ≤ 3) _ (hsing ω hμ1)
  have hd2 := CFSG.StandardType.OrdPOm.finrank_le_of_singular_quadMinus hirr
    (by norm_num : 1 ≤ 3) _ (hsing (ω ^ 2) hμ2)
  have hsum := card_le_finrank_add_finrank_eigen hg3 hfix hω
  simp only [Fintype.card_sum, Fintype.card_fin] at hsum
  omega

theorem commV_eq_top_of_fixedPointFree (hS : ∀ s : S, s ^ 2 = 1) {L : Subgroup (MulAut S)}
    {β : MulAut S} (hβ : β ∈ L) (hβ3 : β ^ 3 = 1) (hfix : ∀ s : S, β s = s → s = 1) :
    commV L = ⊤ := by
  refine eq_top_iff.mpr fun s _ => ?_
  have hβ3s : ∀ t : S, β (β (β t)) = t := fun t => by
    have := congrArg (fun γ : MulAut S => γ t) hβ3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hw : s * β s * β (β s) = 1 := by
    apply hfix
    rw [map_mul, map_mul, hβ3s]
    rw [mul_comm (β s * β (β s)) s, mul_assoc]
  have h1 : β s * s⁻¹ ∈ commV L := Subgroup.subset_closure ⟨β, hβ, s, rfl⟩
  have h2 : (β ^ 2) s * s⁻¹ ∈ commV L :=
    Subgroup.subset_closure ⟨β ^ 2, L.pow_mem hβ 2, s, rfl⟩
  have e : s = (β s * s⁻¹) * ((β ^ 2) s * s⁻¹) := by
    have hs2 : s * s = 1 := by rw [← sq]; exact hS s
    have hb2 : (β ^ 2) s = β (β s) := by rw [sq, MulAut.mul_apply]
    have hinv : s⁻¹ = s := inv_eq_iff_mul_eq_one.mpr hs2
    have hbb : β s * β (β s) = s := by
      have h' : s * (β s * β (β s)) = 1 := by rw [← mul_assoc]; exact hw
      calc β s * β (β s) = s⁻¹ := eq_inv_of_mul_eq_one_right h'
        _ = s := hinv
    rw [hb2, hinv, mul_mul_mul_comm, hs2, mul_one, hbb]
  rw [e]
  exact (commV L).mul_mem h1 h2

theorem fixV_eq_bot_of_fixedPointFree {L : Subgroup (MulAut S)} {β : MulAut S} (hβ : β ∈ L)
    (hfix : ∀ s : S, β s = s → s = 1) : fixV L = ⊥ :=
  eq_bot_iff.mpr fun s hs => Subgroup.mem_bot.mpr (hfix s (hs β hβ))

@[expose] def planeSub {n : ℕ} {L : Subgroup (MulAut S)} {F : Type} [Field F] (N : NatSU4 n L F)
    (W : Submodule F (Fin 4 → F)) : Subgroup S where
  carrier := {s | N.vec s ∈ W}
  mul_mem' := fun {a b} ha hb => by
    show N.vec (a * b) ∈ W
    rw [N.vec_mul]
    exact W.add_mem ha hb
  one_mem' := by
    show N.vec 1 ∈ W
    rw [N.vec_one]
    exact W.zero_mem
  inv_mem' := fun {a} ha => by
    show N.vec a⁻¹ ∈ W
    have h : N.vec a⁻¹ = -N.vec a := by
      rw [eq_neg_iff_add_eq_zero, ← N.vec_mul, inv_mul_cancel, N.vec_one]
    rw [h]
    exact W.neg_mem ha

theorem mem_planeSub {n : ℕ} {L : Subgroup (MulAut S)} {F : Type} [Field F] (N : NatSU4 n L F)
    (W : Submodule F (Fin 4 → F)) (s : S) : s ∈ planeSub N W ↔ N.vec s ∈ W :=
  Iff.rfl

end CFSG.LocalAnalysis.RankThreeUC.U4Mc
