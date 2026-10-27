module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveFourFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveSylowRat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveFourCount

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false


namespace Four

theorem natCast_eq_two_or_three {q : ℕ} (he : orderOf ((q : ℕ) : ZMod 5) = 4) :
    ((q : ℕ) : ZMod 5) = 2 ∨ ((q : ℕ) : ZMod 5) = 3 := by
  have h1 := pow_orderOf_eq_one ((q : ℕ) : ZMod 5)
  rw [he] at h1
  have h2 : ((q : ℕ) : ZMod 5) ^ 2 ≠ 1 := fun h' => by
    have := orderOf_dvd_of_pow_eq_one h'
    rw [he] at this
    omega
  generalize ((q : ℕ) : ZMod 5) = x at h1 h2 ⊢
  revert x
  decide

theorem five_dvd_of_orderOf_four {q : ℕ} (he : orderOf ((q : ℕ) : ZMod 5) = 4) :
    5 ∣ q * q + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rcases natCast_eq_two_or_three he with h | h <;> rw [h] <;> decide

theorem exists_langPlaneData_vElt (K : Type) [Field K] [Finite K]
    (he : orderOf ((Nat.card K : ℕ) : ZMod 5) = 4) (E₀ : Subgroup (adjointGroup .E8 K))
    (hE₀ : IsElemAbelian 5 E₀) (hc : Nat.card E₀ = 5 ^ 3) :
    ∃ D : LangPlaneData .E8 K E₀, D.w = vElt := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  set L := AlgebraicClosure K with hL
  have hq5 := natCast_eq_two_or_three he
  have h5 := five_dvd_of_orderOf_four he
  have hℓ5 : ¬ ringChar K ∣ 5 := by
    intro h
    have h1 : ringChar K = 5 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).1 h
    have h2 : 5 ∣ Nat.card K := by
      rw [hK, h1]
      exact dvd_pow_self 5 f.pos.ne'
    have := (Nat.dvd_add_right (Dvd.dvd.mul_right h2 _)).1 h5
    exact absurd (Nat.dvd_one.1 this) (by norm_num)
  have hFr : ∀ c, iterateFrobenius L (ringChar K) f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def (ringChar K) f c
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf (L := L) (ℓ := ringChar K) Nat.prime_five hℓ5
  obtain ⟨F, hFn⟩ := exists_frame_canonical K f.pos hK L
  obtain ⟨m, hm⟩ := exists_isLift F hFn hK
  have hT0 := card_twistedTorus F hK f.pos
  haveI : Finite (sylowGrp F m) := Nat.finite_of_card_ne_zero (by
    rw [card_sylowGrp hm, hT0]
    positivity)
  have hE5 : IsPGroup 5 E₀ := IsPGroup.of_card (n := 3) hc
  obtain ⟨c₁, hc₁⟩ := exists_conj_into_sylowRat hm hK f.pos h5 hE5
  let ψ₀ : adjointGroup .E8 K →* ModGL .E8 L :=
    (MulAut.conj F.g0⁻¹).toMonoidHom.comp
      ((adjEmb .E8 K L).comp (MulAut.conj c₁).toMonoidHom)
  have hψ₀ : ∀ x, ψ₀ x = F.g0⁻¹ * adjEmb .E8 K L (c₁ * x * c₁⁻¹) * F.g0 := fun x => by
    simp [ψ₀, MulAut.conj_apply]
  have hψ₀inj : Function.Injective ψ₀ :=
    (MulAut.conj F.g0⁻¹).injective.comp
      ((adjEmb_injective (τ := .E8) (K := K) (L := L)).comp (MulAut.conj c₁).injective)
  have hψ₀mem : ∀ x ∈ E₀, ψ₀ x ∈ sylowGrp F m := fun x hx => by
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hc₁ x hx))
    have : ψ₀ x = s := by
      rw [hψ₀, ← hsx]
      show F.g0⁻¹ * (F.g0 * s * F.g0⁻¹) * F.g0 = s
      group
    rw [this]
    exact hs
  let ψ : E₀ →* sylowGrp F m :=
    (ψ₀.comp E₀.subtype).codRestrict (sylowGrp F m) (fun x => hψ₀mem x x.2)
  have hψ : ∀ x : E₀, ((ψ x : sylowGrp F m) : ModGL .E8 L) = ψ₀ x := fun x => rfl
  have hψinj : Function.Injective ψ := fun x y hxy =>
    Subtype.ext (hψ₀inj (by
      have := congrArg Subtype.val hxy
      exact this))
  have hker := cube_le_ker (sylowRho hm) (card_sylowRho_range hm)
    (fun y hy => ncard_sylow_fixed_le hm hζ hFr hq5 y hy) ψ.range
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (hE₀.1.is_comm.comm a b))
    (by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 5 = 1 := Subtype.ext (by simpa using hE₀.2 a a.2)
      rw [this, map_one])
    (by
      rw [Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv.symm]
      exact hc)
  have hT : ∀ x ∈ E₀, ψ₀ x ∈ twistedTorusOf F.n
      (Units.map (entrywiseHom (iterateFrobenius L (ringChar K) f))) := fun x hx => by
    have h1 : ψ ⟨x, hx⟩ ∈ (sylowRho hm).ker := hker ⟨⟨x, hx⟩, rfl⟩
    exact (sylowRho_eq_one_iff hm _).1 (MonoidHom.mem_ker.1 h1)
  refine ⟨{ w := vElt
            Fr := iterateFrobenius L (ringChar K) f
            hFr := hFr
            g0 := F.g0
            hg0C := F.hg0C
            hg0 := ?_
            c := c₁
            hc := fun x hx => ?_ }, rfl⟩
  · rw [F.hg0, hFn]
  · refine Subgroup.mem_map.2 ⟨ψ₀ x, ?_, ?_⟩
    · rw [← hFn]
      exact hT x hx
    · rw [hψ₀]
      have e : F.g0 * (F.g0⁻¹ * adjEmb .E8 K L (c₁ * x * c₁⁻¹) * F.g0) * F.g0⁻¹ =
          adjEmb .E8 K L (c₁ * x * c₁⁻¹) := by group
      exact e

theorem vElt_sq_smul (u : Fin Tag.E8.rank → ℤ) : vElt • (vElt • u) = -u := by
  rw [vElt, e8P4_weylImage, e8P4_weylImage, Matrix.mulVec_mulVec, e8P4V_sq, Matrix.neg_mulVec,
    Matrix.one_mulVec]

theorem exists_conj_le_e8D4Group (K : Type) [Field K] [Finite K]
    (he : orderOf ((Nat.card K : ℕ) : ZMod 5) = 4) (E₀ : Subgroup (adjointGroup .E8 K))
    (hE₀ : IsElemAbelian 5 E₀) (hc : Nat.card E₀ = 5 ^ 3) :
    ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8D4Group K := by
  obtain ⟨D, hD⟩ := exists_langPlaneData_vElt K he E₀ hE₀ hc
  have hsq : ∀ u : Fin Tag.E8.rank → ℤ, D.w • (D.w • u) = -u := fun u => by
    rw [hD]
    exact vElt_sq_smul u
  exact exists_conj_le_of_frameDatum hE₀.2 D (e8FiveFourFrameDatum_holds K he D.Fr D.hFr D.w hsq)

end Four

theorem e8FourFiveCubeRest_holds : SeitzExcOpenRest3.E8FourFiveCubeRest := by
  intro K _ _ he E₀ hE₀ hc _ hnot
  obtain ⟨g, hg⟩ := Four.exists_conj_le_e8D4Group K he E₀ hE₀ hc
  exact absurd ⟨g, hg⟩ hnot

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
