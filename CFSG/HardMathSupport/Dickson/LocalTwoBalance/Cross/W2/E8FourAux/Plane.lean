module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Dichotomy
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Bridge
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidAssembly

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

set_option linter.unusedSectionVars false

theorem commute_of_pow_commute {C : Type*} [Group C] {p k : ℕ} (hp : p.Prime) (hk : ¬ p ∣ k)
    {v u : C} (h1 : v ^ k * u = u * v ^ k) (h2 : v ^ p * u = u * v ^ p) : v * u = u * v := by
  have hcop : Nat.Coprime k p := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hk))
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hkm : k * m = 1 + p * (k * m / p) := by
    have := Nat.div_add_mod (k * m) p
    omega
  set s := k * m / p with hs
  have hc1 : Commute u (v ^ (k * m)) := by
    rw [pow_mul]
    exact (Commute.pow_right (show Commute u (v ^ k) from h1.symm) m)
  have hc2 : Commute u ((v ^ p) ^ s) := Commute.pow_right (show Commute u (v ^ p) from h2.symm) s
  have hv : v = v ^ (k * m) * ((v ^ p) ^ s)⁻¹ := by
    rw [hkm, pow_add, pow_one, pow_mul]
    group
  have hc : Commute u v := by
    rw [hv]
    exact hc1.mul_right (hc2.inv_right)
  exact hc.symm.eq

section Gamma


variable {L : Type} [Field L] [IsAlgClosed L]

theorem innerPlaneBalance_Gamma_of_lift (S : LangSetup .E8 L 5) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl) (hMΓ : S.D.model ≤ S.Γ)
    (hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ))
    (hord : (Nat.card ↥S.Γ).factorization 5 =
      (Nat.card ↥(S.D.torus.subgroupOf S.Γ)).factorization 5 + 1)
    (hP : ∀ D₁ : Subgroup ↥S.Γ, (∀ x ∈ D₁, x ^ 5 = 1) → 5 < Nat.card D₁ →
      D₁ ≤ S.D.torus.subgroupOf S.Γ → ∀ H : Subgroup (MulAut ↥S.Γ), innerAut ↥S.Γ ≤ H →
        localDeltaIn 5 H (D₁.map (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ)) = ⊥)
    (hQ : ∀ v : ↥S.Γ, (∀ a : Fin Tag.E8.rank → Lˣ,
        rootDiagUnit Tag.E8 a * (v : ModGL Tag.E8 L) = (v : ModGL Tag.E8 L) * rootDiagUnit Tag.E8 a ↔
          z0 ∈ rootCharStabilizer a) →
      ∀ u : ↥S.Γ, (u : ModGL Tag.E8 L) ∈ S.D.torus → u ≠ 1 → u ^ 5 = 1 → v * u = u * v →
        ∀ H : Subgroup (MulAut ↥S.Γ), innerAut ↥S.Γ ≤ H →
          localDeltaIn 5 H ((Subgroup.zpowers u).map (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ)) = ⊥) :
    InnerPlaneBalance 5 ↥S.Γ := by
  classical
  haveI := S.finite_Γ
  obtain ⟨v, hvT, hvp, hvn, hvc⟩ := exists_lift_Γ S hFr hΦ hn hMΓ
  have hTc : ∀ x ∈ S.D.torus.subgroupOf S.Γ, ∀ y ∈ S.D.torus.subgroupOf S.Γ, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact E8Lift.torusGroup_mul_comm ((mem_torus_iff S).1 hx).1 ((mem_torus_iff S).1 hy).1
  refine innerPlaneBalance_of_dichotomy S.hp hinj (S.D.torus.subgroupOf S.Γ) hTc v
    (fun t ht => hvT t ht) hvp hvn hord hP ?_
  intro u huT hu1 hu5 hk H hH
  obtain ⟨k, hk, hkc⟩ := hk
  have h5c : v ^ 5 * u = u * v ^ 5 := hTc _ hvp u huT
  exact hQ v hvc u huT hu1 hu5 (commute_of_pow_commute S.hp hk hkc h5c) H hH

theorem innerPlaneBalance_Gamma_E8_ge3
    (S : LangSetup .E8 L 5) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
    (hw4 : ∀ δ : Fin Tag.E8.rank → ℤ, IsRoot .E8 δ → e8PhiFourWeyl • e8PhiFourWeyl • δ = -δ)
    (hMΓ : S.D.model ≤ S.Γ) (hAlg : S.IsAlgebraic) (hcp : LangComponentPieces)
    (hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ))
    (hAK : AnyKindCommute) (hAK3 : AnyKindCommuteThreeFull)
    (hq5 : 5 ∣ S.D.q ^ 2 + 1) (hq3 : 3 ≤ S.D.q) (hrig : SetupRigid S)
    (hord : (Nat.card ↥S.Γ).factorization 5 =
      (Nat.card ↥(S.D.torus.subgroupOf S.Γ)).factorization 5 + 1) :
    InnerPlaneBalance 5 ↥S.Γ := by
  have hbal := frameBalanced_of_langSetup S hrig hcp.subnormal hcp.inner hcp.suN hcp.twoD hcp.exc
    hinj
  refine innerPlaneBalance_Gamma_of_lift S hFr hΦ hn hMΓ hinj hord ?_ ?_
  · intro D₁ hexp hcard hD₁T H hH
    refine hbal D₁ (fun x hx => ?_) hexp hcard H hH
    refine S.E_all _ (Subgroup.mem_inf.2 ⟨hD₁T hx, x.2⟩) ?_
    have h1 := congrArg Subtype.val (hexp x hx)
    simpa using h1
  · intro v hvc u huT hu1 hu5 hvu H hH
    exact localDeltaIn_zpowers_eq_bot_of_commute_lift S hFr hΦ hn hw4 hMΓ hAlg hcp.subnormal
      hcp.inner hcp.suN hcp.twoD hcp.exc hinj hAK hAK3 hq5 hq3 hvc huT hu1 hu5 hvu hH

theorem innerPlaneBalance_Gamma_E8_two (S : LangSetup .E8 L 5) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl) (hMΓ : S.D.model ≤ S.Γ)
    (hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ))
    (hord : (Nat.card ↥S.Γ).factorization 5 =
      (Nat.card ↥(S.D.torus.subgroupOf S.Γ)).factorization 5 + 1)
    (hcore2 : ∀ u : ↥S.Γ, u ≠ 1 → (u : ModGL Tag.E8 L) ∈ S.D.torus →
      ∀ H : Subgroup (MulAut ↥S.Γ), innerAut ↥S.Γ ≤ H →
        localDeltaIn 5 H ((Subgroup.zpowers u).map (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ)) = ⊥) :
    InnerPlaneBalance 5 ↥S.Γ := by
  refine innerPlaneBalance_Gamma_of_lift S hFr hΦ hn hMΓ hinj hord ?_ ?_
  · intro D₁ hexp hcard hD₁T H hH
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ D₁, u ≠ 1 := by
      by_contra hall
      push Not at hall
      have : D₁ = ⊥ := (Subgroup.eq_bot_iff_forall D₁).2 hall
      rw [this, Subgroup.card_bot] at hcard
      omega
    have hle : Subgroup.zpowers u ≤ D₁ := (Subgroup.zpowers_le).2 hu
    exact le_bot_iff.1 ((localDeltaIn_antitone H (Subgroup.map_mono hle)).trans
      (le_of_eq (hcore2 u hu1 (hD₁T hu) H hH)))
  · intro v hvc u huT hu1 hu5 hvu H hH
    exact hcore2 u hu1 huT H hH

end Gamma

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
