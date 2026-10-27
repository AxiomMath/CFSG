module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Matrix LinearAlgebra.Projectivization

theorem suzuki_natural_action_standard_pair (m : ℕ) (hm : 1 ≤ m) :
    let K := BinaryGaloisField (2 * m + 1)
    let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
    let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
    let G := SuzukiMatrixGroup m
    ∃ (rho : G →* Equiv.Perm Omega) (b : Omega) (S : Sylow 2 G),
      (∀ (g : G) (z : Omega), ((rho g z : Omega) : ℙ K (Fin 4 → K)) =
        (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K)).toLinearEquiv •
          (z : ℙ K (Fin 4 → K))) ∧
      letI : MulAction G Omega := MulAction.compHom Omega rho
      Subgroup.normalizer ((S : Subgroup G) : Set G) = MulAction.stabilizer G b ∧
      MulAction.IsMultiplyPretransitive G Omega 2 ∧
      ∃ (a0 b0 : Omega) (w : G) (T0 : Subgroup G),
        a0 ≠ b0 ∧ w • a0 = b0 ∧ w • b0 = a0 ∧
        (T0 : Set G) = {x | x • a0 = a0 ∧ x • b0 = b0} ∧
        IsCyclic T0 ∧ Nat.card T0 = 2 ^ (2 * m + 1) - 1 ∧
        ∀ x ∈ T0, rightConjugateElem x w = x⁻¹ := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := fun x =>
    iterateFrobeniusEquiv_def K 2 (m + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq m pi hpi
  let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
  let G := SuzukiMatrixGroup m
  obtain ⟨rho, b, S, hrho, hN, _hregular, htwoRaw⟩ :=
    suzuki_sylow_normalizer_action m (by omega)
  refine ⟨rho, b, S, hrho, ?_⟩
  let : MulAction G Omega := MulAction.compHom Omega rho
  have hN' : Subgroup.normalizer ((S : Subgroup G) : Set G) =
      MulAction.stabilizer G b := by
    rw [hN]
    ext g
    rfl
  have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact htwoRaw a b c d hab hcd
  let a0 : Omega := ⟨pinf, Or.inl rfl⟩
  let b0 : Omega := ⟨p 0 0, Or.inr ⟨(0, 0), rfl⟩⟩
  have hab : a0 ≠ b0 := by
    intro h
    have hraw : pinf = p 0 0 := congrArg Subtype.val h
    apply External.suzukiOvoidInfinity_not_mem_range m pi
    exact ⟨(0, 0), by simpa [p] using hraw.symm⟩
  let w : G := ⟨SuzukiWeylGL m, Subgroup.subset_closure
    (show SuzukiWeylGL m ∈ SuzukiMatrixGeneratorSet m from Or.inr (Or.inr rfl))⟩
  have hwa : w • a0 = b0 := by
    apply Subtype.ext
    change ((rho w a0 : Omega) : ℙ K (Fin 4 → K)) = p 0 0
    rw [hrho]
    simpa [w, a0, b0, p, pinf] using External.suzukiWeyl_smul_infinity m pi
  have hwb : w • b0 = a0 := by
    apply Subtype.ext
    change ((rho w b0 : Omega) : ℙ K (Fin 4 → K)) = pinf
    rw [hrho]
    simpa [w, a0, b0, p, pinf] using External.suzukiWeyl_smul_zero m pi
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  have hHleG : H ≤ G := by
    dsimp [H, G]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  let T0 : Subgroup G := H.subgroupOf G
  have hTset : (T0 : Set G) = {x | x • a0 = a0 ∧ x • b0 = b0} := by
    ext x
    change ((x : G) : GL (Fin 4) K) ∈ H ↔ _
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := (External.suzukiTorusGL_mem_closure_iff m
        ((x : G) : GL (Fin 4) K)).mp hx
      constructor
      · apply Subtype.ext
        change ((rho x a0 : Omega) : ℙ K (Fin 4 → K)) = pinf
        rw [hrho, hc]
        simpa [a0, pinf] using External.suzukiTorus_smul_infinity m c
      · apply Subtype.ext
        change ((rho x b0 : Omega) : ℙ K (Fin 4 → K)) = p 0 0
        rw [hrho, hc]
        simpa [b0, p] using External.suzukiTorus_smul_finite m pi hpi_sq hpi c 0 0
    · intro hx
      apply External.suzukiMatrixGroup_mem_torus_of_fix_infinity_zero m pi hpi_sq hpi x
      · calc
          (Matrix.GeneralLinearGroup.toLin ((x : G) : GL (Fin 4) K)).toLinearEquiv • pinf =
              ((rho x a0 : Omega) : ℙ K (Fin 4 → K)) := by
                simpa [a0, pinf] using (hrho x a0).symm
          _ = pinf := congrArg Subtype.val hx.1
      · calc
          (Matrix.GeneralLinearGroup.toLin ((x : G) : GL (Fin 4) K)).toLinearEquiv • p 0 0 =
              ((rho x b0 : Omega) : ℙ K (Fin 4 → K)) := by
                simpa [b0, p] using (hrho x b0).symm
          _ = p 0 0 := congrArg Subtype.val hx.2
  obtain ⟨_hu, _hf, _hp, _hp4, _ho4, _hclass, _hFcard, _htype,
      _hmul, _hcomm, _hcoords, ⟨eH, _heH⟩, _hconj, _hdisjoint, _hfree⟩ :=
    External.huppert_blackburn_XI_3_1 m (by omega) pi hpi_sq
  let eT : T0 ≃* H := Subgroup.subgroupOfEquivOfLe hHleG
  have hTcyclic : IsCyclic T0 := eT.isCyclic.mpr
    (eH.isCyclic.mp (inferInstance : IsCyclic Kˣ))
  have hTcard : Nat.card T0 = 2 ^ (2 * m + 1) - 1 := by
    calc
      Nat.card T0 = Nat.card H := Nat.card_congr eT.toEquiv
      _ = Nat.card Kˣ := Nat.card_congr eH.toEquiv.symm
      _ = Nat.card K - 1 := Nat.card_units K
      _ = 2 ^ (2 * m + 1) - 1 := by
        rw [show Nat.card K = 2 ^ (2 * m + 1) from
          GaloisField.card 2 (2 * m + 1) (by omega)]
  have hinvert : ∀ x ∈ T0, rightConjugateElem x w = x⁻¹ := by
    intro x hx
    obtain ⟨c, hc⟩ := (External.suzukiTorusGL_mem_closure_iff m
      ((x : G) : GL (Fin 4) K)).mp hx
    have hwinv : (SuzukiWeylGL m)⁻¹ = SuzukiWeylGL m :=
      eq_inv_of_mul_eq_one_right (External.suzukiWeylGL_mul_self m)
    rw [rightConjugateElem]
    apply Subtype.ext
    change (SuzukiWeylGL m)⁻¹ * ((x : G) : GL (Fin 4) K) * SuzukiWeylGL m =
      ((x : G) : GL (Fin 4) K)⁻¹
    rw [hwinv, hc, External.suzukiWeylGL_conj_torus, External.suzukiTorusGL_inv]
  exact ⟨hN', htwo, a0, b0, w, T0, hab, hwa, hwb, hTset, hTcyclic, hTcard, hinvert⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
