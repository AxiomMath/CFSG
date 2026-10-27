module

public import CFSG.GroupTheory.NilpotentCyclicNorm
public import CFSG.LieType.AlgebraicGroups.UnipotentCoprimeTorsor
public import CFSG.LieType.AlgebraicGroups.FixedConnectedGenerators
public import CFSG.LieType.AlgebraicGroups.FixedComponentCentralIsogeny

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem connectedSpace_fixedCoordinate_of_unipotent_of_charZero [CharZero k]
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hH : ∀ g : WithConv (H →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint g)
    (σ : H →ₐc[k] H) : ConnectedSpace (PrimeSpectrum (fixedCoordinate H σ)) := by
  let F := fixedCoordinate H σ
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  let : Group (_root_.ConnectedComponents (PrimeSpectrum F)) :=
    TauCeti.FiniteTypeCommHopfAlgCat.instGroupConnectedComponents F
  let : Finite (_root_.ConnectedComponents (PrimeSpectrum F)) :=
    TauCeti.FiniteTypeCommHopfAlgCat.instFiniteConnectedComponents F
  let n := Nat.card (_root_.ConnectedComponents (PrimeSpectrum F))
  have hn : 0 < n := Nat.card_pos
  have hroot := pow_bijective_of_unipotent H hH
    (show (n : k) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
  apply connectedSpace_of_componentPointsHom_eq_one F
  intro x
  let g := TauCeti.AlgHom.mapDomain (A := k) q x
  obtain ⟨y, hy⟩ := hroot.2 g
  change y ^ n = g at hy
  have hfixg : TauCeti.AlgHom.mapDomain σ g = g := fixedCoordinate_point_fixed H σ x
  have hfixy : TauCeti.AlgHom.mapDomain σ y = y := by
    apply hroot.1
    change (TauCeti.AlgHom.mapDomain σ y) ^ n = y ^ n
    rw [← map_pow, hy]
    exact hfixg
  have hmem : y ∈ (TauCeti.AlgHom.mapDomain (A := k) q).range := by
    rw [fixedCoordinate_points_range]
    exact hfixy
  obtain ⟨z, hz⟩ := hmem
  have hzx : z ^ n = x := by
    apply TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj (fixedHopfIdeal H σ)
      (CommAlgCat.of k k)
    change TauCeti.AlgHom.mapDomain q (z ^ n) = g
    rw [map_pow, hz, hy]
  apply (componentPointsHom_eq_one_iff F x).2
  rw [← hzx, map_pow]
  exact pow_card_eq_one'

@[expose] def cyclicNormThreeAlgHom (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σ : H →ₐc[k] H) (m : ℤ) : H →ₐ[k] H :=
  ((toConv (AlgHom.id k H) * toConv σ.toAlgHom *
    toConv (σ.comp σ).toAlgHom) ^ m).ofConv

omit [IsAlgClosed k] in
theorem cyclicNormThreeAlgHom_on_points
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : H →ₐc[k] H)
    (m : ℤ) (g : WithConv (H →ₐ[k] k)) :
    toConv (g.ofConv.comp (cyclicNormThreeAlgHom H σ m)) =
      CFSG.GroupTheory.cyclicNormThreePow (TauCeti.AlgHom.mapDomain σ) m g := by
  have h := map_zpow (TauCeti.AlgHom.mapValue g.ofConv)
    (toConv (AlgHom.id k H) * toConv σ.toAlgHom * toConv (σ.comp σ).toAlgHom) m
  simpa only [cyclicNormThreeAlgHom, CFSG.GroupTheory.cyclicNormThreePow, map_mul,
    TauCeti.AlgHom.mapValue_apply, ofConv_toConv, toConv_ofConv, AlgHom.comp_id,
    TauCeti.AlgHom.mapDomain_apply, BialgHom.comp_toAlgHom, AlgHom.comp_assoc] using h

omit [IsAlgClosed k] in
theorem iterate_cyclicNormThreeAlgHom_on_points
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : H →ₐc[k] H)
    (m : ℤ) (n : ℕ) (g : WithConv (H →ₐ[k] k)) :
    toConv (g.ofConv.comp (cyclicNormThreeAlgHom H σ m ^ n)) =
      (CFSG.GroupTheory.cyclicNormThreePow (TauCeti.AlgHom.mapDomain σ) m)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    change toConv ((g.ofConv.comp (cyclicNormThreeAlgHom H σ m ^ n)).comp
      (cyclicNormThreeAlgHom H σ m)) = _
    rw [cyclicNormThreeAlgHom_on_points]
    rw [ih, Function.iterate_succ_apply']

theorem connectedSpace_fixedCoordinate_of_nilpotent_powInverse_three
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)]
    [Group.IsNilpotent (WithConv (H →ₐ[k] k))]
    (σ : H →ₐc[k] H) (hσ : (σ.comp σ).comp σ = BialgHom.id k H)
    (m : ℤ) (hpow : ∀ g : WithConv (H →ₐ[k] k), (g ^ (3 : ℕ)) ^ m = g) :
    ConnectedSpace (PrimeSpectrum (fixedCoordinate H σ)) := by
  let F := fixedCoordinate H σ
  let α := TauCeti.AlgHom.mapDomain (A := k) σ
  let d := Group.nilpotencyClass (WithConv (H →ₐ[k] k))
  let f := cyclicNormThreeAlgHom H σ m ^ d
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  have hα : ∀ g, α (α (α g)) = g := by
    intro g
    apply WithConv.ext
    ext a
    change g.ofConv (σ (σ (σ a))) = g.ofConv a
    exact congrArg g.ofConv (congrArg (fun t : H →ₐc[k] H => t a) hσ)
  have hfix : ∀ g : WithConv (H →ₐ[k] k),
      α (toConv (g.ofConv.comp f)) = toConv (g.ofConv.comp f) := by
    intro g
    dsimp only [f]
    rw [iterate_cyclicNormThreeAlgHom_on_points]
    exact CFSG.GroupTheory.iterate_cyclicNormThreePow_fixed α m hα hpow g
  have hcomp : f.comp σ.toAlgHom = f := by
    apply AlgHom.ext
    intro a
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
    intro x
    have hx := congrArg (fun g : WithConv (H →ₐ[k] k) => g.ofConv a) (hfix (toConv x))
    exact hx
  have hker : (fixedHopfIdeal H σ).toIdeal ≤ RingHom.ker f.toRingHom := by
    apply (TauCeti.HopfIdeal.equalizer_le_ker_iff _).2
    intro a
    exact congrArg (fun t : H →ₐ[k] H => t a) hcomp
  let s : F →ₐ[k] H := Ideal.Quotient.liftₐ (fixedHopfIdeal H σ).toIdeal f hker
  have hs : s.comp q.toAlgHom = f := by
    apply AlgHom.ext
    intro a
    change s (q a) = f a
    have hqa : q a = Ideal.Quotient.mkₐ k (fixedHopfIdeal H σ).toIdeal a :=
      TauCeti.CommHopfAlgCat.mkQuotient_apply H.obj (fixedHopfIdeal H σ) a
    rw [hqa]
    rfl
  have hsection : ∀ x : WithConv (F →ₐ[k] k),
      toConv ((TauCeti.AlgHom.mapDomain q x).ofConv.comp s) = x := by
    intro x
    let g := TauCeti.AlgHom.mapDomain (A := k) q x
    have hg : α g = g := fixedCoordinate_point_fixed H σ x
    have hself := CFSG.GroupTheory.cyclicNormThreePow_eq_self_of_fixed α m hpow hg
    have hiter : ∀ n, (CFSG.GroupTheory.cyclicNormThreePow α m)^[n] g = g := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, hself]
    apply TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj (fixedHopfIdeal H σ)
      (CommAlgCat.of k k)
    change toConv (g.ofConv.comp (s.comp q.toAlgHom)) = g
    rw [hs]
    dsimp only [f]
    rw [iterate_cyclicNormThreeAlgHom_on_points]
    exact hiter d
  have hp₀ : toConv ((1 : WithConv (H →ₐ[k] k)).ofConv.comp s) =
      (1 : WithConv (F →ₐ[k] k)) := by
    simpa only [map_one] using hsection 1
  apply connectedSpace_of_componentPointsHom_eq_one F
  intro x
  have h := componentPointsHom_comp_eq_one_of_connected F s inferInstance
    (1 : WithConv (H →ₐ[k] k)).ofConv hp₀ (TauCeti.AlgHom.mapDomain q x).ofConv
  rw [hsection x] at h
  exact h

theorem connectedSpace_fixedCoordinate_of_unipotent_three
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)]
    (hH : ∀ g : WithConv (H →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint g)
    (h3 : (3 : k) ≠ 0) (σ : H →ₐc[k] H)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    ConnectedSpace (PrimeSpectrum (fixedCoordinate H σ)) := by
  by_cases hchar : CharZero k
  · let := hchar
    exact connectedSpace_fixedCoordinate_of_unipotent_of_charZero H hH σ
  · let p := ringChar k
    have hp0 : p ≠ 0 := fun h =>
      hchar ((CharP.ringChar_zero_iff_CharZero k).mp h)
    have hp : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right hp0
    obtain ⟨e, he⟩ := exists_uniform_pow_eq_one_of_unipotent H
      (⊤ : Subgroup (WithConv (H →ₐ[k] k))) (fun g _ => hH g) hp
    let N := p ^ e
    have hbound : ∀ g : WithConv (H →ₐ[k] k), g ^ N = 1 :=
      fun g => he g (Subgroup.mem_top g)
    have hcop : Nat.Coprime 3 N :=
      ((hp.coprime_iff_not_dvd).mpr
        (fun h => h3 ((CharP.cast_eq_zero_iff k p 3).mpr h))).symm.pow_right e
    let m := Nat.gcdA 3 N
    have hbez : (3 : ℤ) * m + (N : ℤ) * Nat.gcdB 3 N = 1 := by
      simpa only [m, hcop.gcd_eq_one, Nat.cast_one, Nat.cast_ofNat] using
        (Nat.gcd_eq_gcd_ab 3 N).symm
    have hpow : ∀ g : WithConv (H →ₐ[k] k), (g ^ (3 : ℕ)) ^ m = g := by
      intro g
      symm
      calc
        g = g ^ ((3 : ℤ) * m + (N : ℤ) * Nat.gcdB 3 N) := by rw [hbez, zpow_one]
        _ = (g ^ (3 : ℕ)) ^ m * (g ^ N) ^ Nat.gcdB 3 N := by
          simp only [zpow_add, zpow_mul, zpow_natCast, zpow_ofNat]
        _ = (g ^ (3 : ℕ)) ^ m := by rw [hbound g, one_zpow, mul_one]
    let : Group.IsNilpotent (WithConv (H →ₐ[k] k)) :=
      isNilpotent_points_of_forall_isUnipotentPoint H hH
    exact connectedSpace_fixedCoordinate_of_nilpotent_powInverse_three H σ hσ m hpow

end CFSG.LieType.AlgebraicGroups
