module

public import CFSG.RankThree.PartOne.KD4L.TranspositionLayer
public import CFSG.RankThree.PartOne.KE.SigmaTransport
public import CFSG.RankThree.PartOne.KGD.D4QA3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KD4L CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

section E6Level

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}

@[expose] def FixOrd (ℓ f p : ℕ) [Fact ℓ.Prime] [CharP L ℓ] (n₂ : ModGL Tag.E6 L) : Prop :=
  ∃ g ∈ fixE6 ℓ f n₂, orderOf g = p

theorem fixOrd_dN (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + 1) : FixOrd (L := L) ℓ f p (dN L) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set D := tauDatum L ℓ f hf with hD
  have hO := orbit24_mem (L := L) (ℓ := ℓ) (f := f) hf
  obtain ⟨hc, -⟩ := pair_data hf rfl hO
  set K := D.orbitField ({Pi.single 2 1, Pi.single 4 1} : Set (Fin Tag.E6.rank → ℤ)) with hK
  have hKcard : Nat.card K = (ℓ ^ f) ^ 2 := by
    rw [hK, D.card_orbitField hO, hc]
    rfl
  have hℓ : 0 < ℓ ^ f := pow_pos (Fact.out : ℓ.Prime).pos _
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; positivity)
  have hdvd : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [← CFSG.Open.StatedAPI.card_statedSL 2 K, CFSG.Open.StatedAPI.card_statedSL_two K, hKcard]
    refine Dvd.dvd.mul_left ?_ _
    have h1 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ hℓ
    have h2 : 1 ≤ ((ℓ ^ f) ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have hfac : ((ℓ ^ f) ^ 2) ^ 2 - 1 = ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 2 + 1) := by
      zify [h1, h2]
      ring
    rw [hfac]
    exact Dvd.dvd.mul_left hpq _
  obtain ⟨A, hA⟩ := exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 2) K) p hdvd
  set R := D.orbitMapHom hO with hR
  have hRA : R A ^ p = 1 := by rw [← map_pow, ← hA, pow_orderOf_eq_one, map_one]
  have hRne : R A ≠ 1 := by
    intro h1
    have h2 := D.eq_one_or_neg_one_of_orbitMap_eq_one hO (by rw [← D.orbitMapHom_apply hO]; exact h1)
    rcases h2 with h3 | h3
    · rw [h3, orderOf_one] at hA
      exact hp.one_lt.ne hA
    · have h4 : A ^ 2 = 1 := by rw [h3]; simp
      have h5 := orderOf_dvd_of_pow_eq_one h4
      rw [hA] at h5
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h5)
  have hord : orderOf (R A) = p := orderOf_eq_prime hRA hRne
  have hmem : R A ∈ D.orbitGroup := D.orbitMap_mem_orbitGroup hO A
  refine ⟨R A, ?_, hord⟩
  rw [fixE6_dN hf]
  exact hmem

omit [IsAlgClosed L] in
theorem FixOrd.conj {n₀ R : ModGL Tag.E6 L} {p : ℕ}
    (hR : (subsystemGroup Tag.E6 L d4Support).map (MulAut.conj R).toMonoidHom =
      subsystemGroup Tag.E6 L d4Support)
    (hFr : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) R = R) (h : FixOrd ℓ f p n₀) :
    FixOrd ℓ f p (R * n₀ * R⁻¹) := by
  obtain ⟨g, hg, hgo⟩ := h
  refine ⟨R * g * R⁻¹, ?_, ?_⟩
  · rw [fixE6_conj hR hFr]
    exact ⟨g, hg, by simp [MulAut.conj_apply]⟩
  · rw [← hgo]
    have := orderOf_injective (MulAut.conj R).toMonoidHom (MulAut.conj R).injective g
    simpa [MulAut.conj_apply] using this

variable (hf : 1 ≤ f)

include hf in
theorem exists_fixOrd_swap13 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ (ℓ ^ f) ^ 2 + 1) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 1 3) ∧ FixOrd ℓ f p n₂ :=
  ⟨dN L, acts_dN, fixOrd_dN hf hp hp2 hpq⟩

include hf in
theorem exists_fixOrd_swap03 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ (ℓ ^ f) ^ 2 + 1) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 3) ∧ FixOrd ℓ f p n₂ := by
  refine ⟨d4TrialityRep L * dN L * (d4TrialityRep L)⁻¹, ?_, ?_⟩
  · have h := Acts.conj (acts_d4TrialityRep (L := L)) (acts_dN (L := L))
    rwa [rho_conj_swap] at h
  · exact FixOrd.conj map_conj_d4TrialityRep frob_d4TrialityRep (fixOrd_dN hf hp hp2 hpq)

include hf in
theorem exists_fixOrd_swap01 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ (ℓ ^ f) ^ 2 + 1) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 1) ∧ FixOrd ℓ f p n₂ := by
  refine ⟨(d4TrialityRep L * d4TrialityRep L) * dN L * (d4TrialityRep L * d4TrialityRep L)⁻¹, ?_, ?_⟩
  · have h := Acts.conj ((acts_d4TrialityRep (L := L)).mul (acts_d4TrialityRep (L := L)))
      (acts_dN (L := L))
    rwa [rho_sq_conj_swap] at h
  · refine FixOrd.conj (map_conj_mul map_conj_d4TrialityRep map_conj_d4TrialityRep) ?_
      (fixOrd_dN hf hp hp2 hpq)
    rw [map_mul, frob_d4TrialityRep]

end E6Level

section Layer

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem layer_orderOf_generic (hf : 1 ≤ f) (σ : Equiv.Perm (Fin Tag.D4.rank)) {p : ℕ}
    (hE : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ σ ∧ FixOrd ℓ f p n₂)
    (π : Equiv.Perm (Fin τ.rank)) (hπσ : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (σ k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ u ∈ P, orderOf u = p := by
  obtain ⟨n₂, h₂, hfix⟩ := hE
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdSwap n₁ π σ := ⟨hπ, hπ', hπσ, hgen⟩
  have hd4 : d4Nodes τ = d4Set τ := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan] at hP
  obtain ⟨g, hg, hgo⟩ := hfix
  have e := hstd.layerEquiv (ℓ := ℓ) (f := f) h₂
  obtain ⟨w, hwU, hwo⟩ : ∃ w ∈ stdLayer ℓ f n₁, orderOf w = p := by
    refine ⟨((hstd.layerEquiv (ℓ := ℓ) (f := f) h₂).symm ⟨g, hg⟩ : stdLayer ℓ f n₁), ?_, ?_⟩
    · exact ((hstd.layerEquiv (ℓ := ℓ) (f := f) h₂).symm ⟨g, hg⟩).2
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hgo]
  have hmem : ∀ x : ModGL τ L, x ∈ P ↔ h * x * h⁻¹ ∈ stdLayer ℓ f n₁ := fun x => by
    rw [hP, Subgroup.mem_inf, mem_stdLayer, mem_twistedFixedPoints, hlang x]
    refine and_congr_left fun _ => ⟨fun hx => mul_mem (mul_mem hh hx) (inv_mem hh), fun hx => ?_⟩
    have := mul_mem (mul_mem (inv_mem hh) hx) hh
    simpa [mul_assoc] using this
  refine ⟨h⁻¹ * w * h, (hmem _).2 (by simpa [mul_assoc] using hwU), ?_⟩
  have := orderOf_injective (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective w
  simpa [MulAut.conj_apply, hwo] using this

theorem layer_orderOf_of_leafSwap
    (hleaf : ∀ i j : Fin τ.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
      (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
      ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4)))
    (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ (ℓ ^ f) ^ 2 + 1)
    {i j : Fin τ.rank} (hij : i ≠ j) (hi : i.val ∈ ({1, 2, 4} : Set ℕ))
    (hj : j.val ∈ ({1, 2, 4} : Set ℕ)) (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ u ∈ P, orderOf u = p := by
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := hleaf i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact layer_orderOf_generic hf (Equiv.swap 1 3)
      (exists_fixOrd_swap13 (L := L) (ℓ := ℓ) hf hp hp2 hpq) (Equiv.swap i j) h1
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact layer_orderOf_generic hf (Equiv.swap 0 3)
      (exists_fixOrd_swap03 (L := L) (ℓ := ℓ) hf hp hp2 hpq) (Equiv.swap i j) h2
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact layer_orderOf_generic hf (Equiv.swap 0 1)
      (exists_fixOrd_swap01 (L := L) (ℓ := ℓ) hf hp hp2 hpq) (Equiv.swap i j) h3
      (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP

end Layer

section E7

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem d4TranspositionLayer_E7_orderOf (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + 1) {i j : Fin Tag.E7.rank} (hij : i ≠ j)
    (hi : i.val ∈ ({1, 2, 4} : Set ℕ)) (hj : j.val ∈ ({1, 2, 4} : Set ℕ))
    (n : ModGL Tag.E7 L) (hn : n ∈ monomialSubgroup Tag.E7 L)
    (hact : ∃ u ∈ parabolicWeylGroup Tag.E7 (d4Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (d4Nodes Tag.E7),
        weylQuotientHom Tag.E7 L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α)
    (P : Subgroup (ModGL Tag.E7 L)) (hP : P = rootSpan Tag.E7 L (parabolicRoots Tag.E7 (d4Nodes Tag.E7)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ u ∈ P, orderOf u = p :=
  layer_orderOf_of_leafSwap leafSwap_E7 hf hp hp2 hpq hij hi hj n hn hact P hP

end E7

section Swap

open CFSG.RankThree.PartOne.KGD (iterateFrobenius_bijective)


variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem exists_orderOf_swap_layer (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + 1) (v : WeylGroup Tag.E7) (n : ModGL Tag.E7 L)
    (hn : n ∈ monomialSubgroup Tag.E7 L) (a b : Fin Tag.E7.rank) (hab : a ≠ b)
    (ha : a.val ∈ ({1, 2, 4} : Set ℕ)) (hb : b.val ∈ ({1, 2, 4} : Set ℕ))
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E7 (d4Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (d4Nodes Tag.E7),
        (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hn⟩ * v) • α =
          u • permLattice (Equiv.swap a b) α)
    (P : Subgroup (ModGL Tag.E7 L))
    (hP : P = rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ u ∈ P, orderOf u = p := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFrbij : Function.Bijective Fr := iterateFrobenius_bijective
  set Φ : ModGL Tag.E7 L →* ModGL Tag.E7 L := Units.map (entrywiseHom Fr) with hΦ
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L v
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  set n' : ModGL Tag.E7 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVm) hn) hVm
  have hπV : weylQuotientHom Tag.E7 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hn⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E7 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hn⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  set P' : Subgroup (ModGL Tag.E7 L) :=
    rootSpan Tag.E7 L (parabolicRoots Tag.E7 (d4Nodes Tag.E7)) ⊓ twistedFixedPoints n' Φ
    with hP'
  obtain ⟨u', hu'P', hu'o⟩ := d4TranspositionLayer_E7_orderOf hf hp hp2 hpq hab ha hb n' hn'm
    (by rw [hπn']; exact hcert) P' rfl
  have hroots : ∀ r ∈ parabolicRoots Tag.E7 (d4Nodes Tag.E7), IsRoot Tag.E7 r := fun r hr => hr.1
  set c₀ : ModGL Tag.E7 L →* ModGL Tag.E7 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hPeq : P'.map c₀ =
      rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7)) ⊓
        twistedFixedPoints n Φ := by
    have hQ : (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (d4Nodes Tag.E7))).map c₀ =
        rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7)) :=
      map_conj_rootSpan v hroots
    have hR : (twistedFixedPoints n' Φ).map c₀ = twistedFixedPoints n Φ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hcapp]
        exact (mem_twistedFixedPoints_conj hΦV).1 hx
      · intro hy
        refine ⟨V⁻¹ * y * V, (mem_twistedFixedPoints_conj hΦV).2 ?_, ?_⟩
        · have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
          rw [e]
          exact hy
        · rw [hcapp]
          group
    rw [hP', Subgroup.map_inf _ _ c₀ (MulAut.conj V).injective, hQ, hR]
  refine ⟨V * u' * V⁻¹, ?_, ?_⟩
  · rw [hP, ← hPeq]
    exact ⟨u', hu'P', hcapp u'⟩
  · have := orderOf_injective (MulAut.conj V).toMonoidHom (MulAut.conj V).injective u'
    simpa [MulAut.conj_apply, hu'o] using this

end Swap

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
