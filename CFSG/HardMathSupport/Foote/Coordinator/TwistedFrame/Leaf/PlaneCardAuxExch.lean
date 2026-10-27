module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCardAuxDescent
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCardAux
public import CFSG.RankThree.PartOne.TCX.E.ExchangeModel

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints adjEmb
  exists_finite_field_isAlgClosure exists_aut_of_rootData_n)

open CFSG.RankThree.PartOne.KLCE (sl_center_pow)

open CFSG.RankThree.PartOne.TCX.E (twist_rootSpan_le_w)

open CFSG.RankThree.Classical2
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem charP_langLevi {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hk : Nat.card K = ℓ ^ f) : CharP D.L ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  exact (RingHom.charP_iff (algebraMap K D.L) (algebraMap K D.L).injective ℓ).1 inferInstance

theorem exchange_dvd {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) {S Sa Sb : Set (Fin τ.rank → ℤ)} (Ea : UFrame τ D.L 3 Sa)
    (hSaroot : ∀ α ∈ Sa, IsRoot τ α) (hSbroot : ∀ α ∈ Sb, IsRoot τ α)
    (hab : ∀ α ∈ Sa, w • α ∈ Sb) (hba : ∀ α ∈ Sb, w • α ∈ Sa)
    (hsq : ∀ i j : Fin 3, i ≠ j → w • (w • Ea.r i j) = Ea.r i j)
    (hS : rootSpan τ D.L S = rootSpan τ D.L Sa ⊔ rootSpan τ D.L Sb)
    (hcomm : ∀ x ∈ rootSpan τ D.L Sa, ∀ y ∈ rootSpan τ D.L Sb, x * y = y * x)
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hrat : ∀ P : Subgroup (ModGL τ D.L), Finite P → P ≤ adjointGroup τ D.L →
      (∀ x ∈ P, Units.map (entrywiseHom D.Fr) x = x) → IsPGroup p P →
        P ≤ (adjEmb τ K D.L).range)
    {k : ℕ} (hk : p ^ k ∣ Nat.card K ^ 6 * ((Nat.card K ^ 4 - 1) * (Nat.card K ^ 6 - 1))) :
    p ^ k ∣ Nat.card ↥(D.frame S) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨ℓ, f, hℓ, hf, hkK⟩ := exists_prime_pow_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP D.L ℓ := charP_langLevi D hℓ hkK
  set n := canonicalRep (coxeterSystem τ) D.L w with hn
  set Φ : ModGL τ D.L →* ModGL τ D.L := Units.map (entrywiseHom D.Fr) with hΦ
  have hnm : n ∈ monomialSubgroup τ D.L := canonicalRep_mem_monomialSubgroup D.L w
  have hwn : weylQuotientHom τ D.L ⟨n, hnm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hΦn : Φ n = n :=
    entrywise_canonicalRep (RingEquiv.ofBijective D.Fr (frobenius_bijective' D)) w
  let T : ModGL τ D.L →* ModGL τ D.L := (MulAut.conj n).toMonoidHom.comp Φ
  have hT : ∀ x, T x = n * Φ x * n⁻¹ := fun x => by simp [T, MulAut.conj_apply]
  have hTab : ∀ x ∈ rootSpan τ D.L Sa, T x ∈ rootSpan τ D.L Sb := fun x hx => by
    rw [hT]
    exact twist_rootSpan_le_w D.Fr n hnm hSaroot (fun α hα => by rw [hwn]; exact hab α hα) x hx
  have hΦΦ : ∀ x, Φ (Φ x) = Units.map (entrywiseHom (D.Fr.comp D.Fr)) x := fun x =>
    units_map_comp D.Fr D.Fr x
  have hTT : ∀ x, T (T x) =
      (n * n) * Units.map (entrywiseHom (D.Fr.comp D.Fr)) x * (n * n)⁻¹ := by
    intro x
    rw [hT, hT, map_mul, map_mul, map_inv, hΦn, hΦΦ]
    group
  have hFr₂bij : Function.Bijective (D.Fr.comp D.Fr) :=
    (frobenius_bijective' D).comp (frobenius_bijective' D)
  have hn₂m : n * n ∈ monomialSubgroup τ D.L := mul_mem hnm hnm
  have hwn₂ : weylQuotientHom τ D.L ⟨n * n, hn₂m⟩ = w * w := by
    have : (⟨n * n, hn₂m⟩ : ↥(monomialSubgroup τ D.L)) = ⟨n, hnm⟩ * ⟨n, hnm⟩ := rfl
    rw [this, map_mul, hwn]
  have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : D.Lˣ, ∀ c : D.L,
      (n * n) * pinnedX τ D.L (Ea.r i j) c * (n * n)⁻¹ =
        pinnedX τ D.L (Ea.r ((fun i j => (i, j)) i j).1 ((fun i j => (i, j)) i j).2) ((b : D.L) * c) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn₂m (Ea.isRoot i j hij)
    refine ⟨μ, fun c => ?_⟩
    rw [hμ c, hwn₂, mul_smul, hsq i j hij]
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n Ea.ρ Ea.inj Ea.r Ea.ε Ea.gen
    (D.Fr.comp D.Fr) hFr₂bij (n * n) (fun i j => (i, j)) (fun i j hij => hij)
    (fun i j hij => ⟨i, j, hij, rfl⟩) hconj
  obtain ⟨K₂, _, _, hK₂ac, hK₂card⟩ := exists_finite_field_isAlgClosure ℓ (2 * f) (by omega) K D.L
  haveI : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂card]
    exact pow_ne_zero _ hℓ.ne_zero)
  have hshape' : ∀ (i j : Fin 3) (hij : i ≠ j) (t : D.L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, D.L)) :
        Matrix (Fin 3) (Fin 3) D.L) =
      1 + Matrix.single ((Equiv.refl (Fin 3)) i) ((Equiv.refl (Fin 3)) j)
        ((b i j : D.L) * t ^ ℓ ^ (2 * f)) := by
    intro i j hij t
    rw [hshape i j hij t]
    have : (D.Fr.comp D.Fr) t = t ^ ℓ ^ (2 * f) := by
      rw [RingHom.comp_apply, D.hFr, D.hFr, hkK, ← pow_mul, ← pow_add, two_mul]
    rw [this]
    rfl
  obtain ⟨-, ⟨H, hH⟩, hfin, -, -⟩ := sln_root_permuting_frobenius_fixed_split (k := K₂)
    (Ω := D.L) hℓ (by omega : 1 ≤ 2 * f) hK₂card (by norm_num : 3 ≤ 3) (Equiv.refl (Fin 3)) Φ' b
    hshape'
  have hK₂q : Nat.card K₂ = Nat.card K ^ 2 := by
    rw [hK₂card, hkK]
    ring
  have hcardFix : Nat.card ↥(fixSubgroup Φ') =
      Nat.card K ^ 6 * ((Nat.card K ^ 4 - 1) * (Nat.card K ^ 6 - 1)) := by
    let ι : SL(3, K₂) →* SL(3, D.L) := Matrix.SpecialLinearGroup.map (algebraMap K₂ D.L)
    let θ₀ : SL(3, K₂) →* SL(3, D.L) := (MulAut.conj H).toMonoidHom.comp ι
    have hι : Function.Injective ι :=
      specialLinearGroup_map_injective (algebraMap K₂ D.L).injective
    have hθ₀ : Function.Injective θ₀ := (MulAut.conj H).injective.comp hι
    have hrange : θ₀.range = fixSubgroup Φ' := by
      ext X
      constructor
      · rintro ⟨Y, rfl⟩
        exact (hH _).2 ⟨Y, by simp [θ₀, ι, MulAut.conj_apply]⟩
      · intro hX
        obtain ⟨Y, hY⟩ := (hH X).1 hX
        exact ⟨Y, by simp [θ₀, ι, MulAut.conj_apply, hY]⟩
    have hc : Nat.card ↥θ₀.range = Nat.card SL(3, K₂) := Nat.card_range_of_injective hθ₀
    rw [← hrange, hc]
    exact PlaneCard.card_SL_three_sq hK₂q
  haveI := hfin
  have hdvdFix : p ^ k ∣ Nat.card ↥(fixSubgroup Φ') := hcardFix ▸ hk
  obtain ⟨H₀, hH₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(fixSubgroup Φ')) p hdvdFix
  have hρSa : ∀ X, Ea.ρ X ∈ rootSpan τ D.L Sa := fun X => by
    rw [← Ea.range]
    exact ⟨X, rfl⟩
  let θ : SL(3, D.L) →* ModGL τ D.L :=
    { toFun := fun X => Ea.ρ X * T (Ea.ρ X)
      map_one' := by simp
      map_mul' := fun X Y => by
        have hc : Ea.ρ Y * T (Ea.ρ X) = T (Ea.ρ X) * Ea.ρ Y :=
          hcomm _ (hρSa Y) _ (hTab _ (hρSa X))
        show Ea.ρ (X * Y) * T (Ea.ρ (X * Y)) = Ea.ρ X * T (Ea.ρ X) * (Ea.ρ Y * T (Ea.ρ Y))
        rw [map_mul, map_mul]
        calc Ea.ρ X * Ea.ρ Y * (T (Ea.ρ X) * T (Ea.ρ Y))
            = Ea.ρ X * (Ea.ρ Y * T (Ea.ρ X)) * T (Ea.ρ Y) := by group
          _ = Ea.ρ X * (T (Ea.ρ X) * Ea.ρ Y) * T (Ea.ρ Y) := by rw [hc]
          _ = Ea.ρ X * T (Ea.ρ X) * (Ea.ρ Y * T (Ea.ρ Y)) := by group }
  let κ : ↥H₀ →* ModGL τ D.L := θ.comp ((fixSubgroup Φ').subtype.comp H₀.subtype)
  have hκ : ∀ x : ↥H₀, κ x = Ea.ρ (((x : ↥(fixSubgroup Φ')) : SL(3, D.L))) *
      T (Ea.ρ (((x : ↥(fixSubgroup Φ')) : SL(3, D.L)))) := fun x => rfl
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    set X : SL(3, D.L) := ((x : ↥(fixSubgroup Φ')) : SL(3, D.L)) with hX
    have h1 : Ea.ρ X * T (Ea.ρ X) = 1 := by rw [← hκ]; exact hx
    have h2 : Ea.ρ X ∈ rootSpan τ D.L Sb := by
      have : Ea.ρ X = (T (Ea.ρ X))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact inv_mem (hTab _ (hρSa X))
    have hXc : X ∈ Subgroup.center SL(3, D.L) := by
      rw [Subgroup.mem_center_iff]
      intro Y
      apply Ea.inj
      rw [map_mul, map_mul]
      exact hcomm _ (hρSa Y) _ h2
    have hX3 : X ^ 3 = 1 := sl_center_pow (m := 1) X hXc
    have hx3 : x ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hX3
    have hdvd3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have hdvdp : orderOf x ∣ p ^ k := hH₀ ▸ orderOf_dvd_natCard x
    have hcop : Nat.Coprime 3 (p ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
    have h1' : orderOf x ∣ Nat.gcd 3 (p ^ k) := Nat.dvd_gcd hdvd3 hdvdp
    rw [hcop] at h1'
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1')
  have hP₀ : κ.range ≤ fixedRootGroup D S := by
    rintro _ ⟨x, rfl⟩
    rw [hκ]
    set X : SL(3, D.L) := ((x : ↥(fixSubgroup Φ')) : SL(3, D.L)) with hX
    refine Subgroup.mem_inf.2 ⟨?_, mem_twistedFixedPoints.2 ?_⟩
    · rw [hS]
      exact mul_mem (Subgroup.mem_sup_left (hρSa X)) (Subgroup.mem_sup_right (hTab _ (hρSa X)))
    · have hXfix : Φ' X = X := (x : ↥(fixSubgroup Φ')).2
      have hTTx : T (T (Ea.ρ X)) = Ea.ρ X := by rw [hTT, hΦ' X, hXfix]
      have hc : Ea.ρ X * T (Ea.ρ X) = T (Ea.ρ X) * Ea.ρ X :=
        hcomm _ (hρSa X) _ (hTab _ (hρSa X))
      have h3 : T (Ea.ρ X * T (Ea.ρ X)) = Ea.ρ X * T (Ea.ρ X) := by
        rw [map_mul, hTTx, ← hc]
      exact (hT _).symm.trans h3
  haveI : Finite ↥H₀ := inferInstance
  have hcardP : Nat.card ↥κ.range = p ^ k := by
    have h : Nat.card ↥κ.range = Nat.card ↥H₀ := Nat.card_range_of_injective hκinj
    rw [h, hH₀]
  have hfinP : Finite ↥κ.range :=
    Nat.finite_of_card_ne_zero (by rw [hcardP]; exact pow_ne_zero _ hp.ne_zero)
  have hpg : IsPGroup p ↥κ.range := IsPGroup.of_card hcardP
  have hdvd := frame_card_dvd_pgroup D S hrat κ.range hP₀ hfinP hpg
  rwa [hcardP] at hdvd

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux
