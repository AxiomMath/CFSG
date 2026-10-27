module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDDatum
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDChain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDKlein
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMinus
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.LieType.AlgebraicGroups CFSG.Open CFSG.RankThree.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CompsPTwoDDatumG

open CompsPTwoDDatum

section Recog

variable (r : ℕ) [Fact r.Prime] (L : Type) [Field L] [CharP L r] [IsAlgClosed L]

@[expose] def TwoDChainRecog (e m : ℕ) : Prop :=
  ∀ {G : Type} [Group G] (ρ : ℕ → SL(2, L) →* G) (Φ : SL(4, L) →* G) (C : Subgroup G),
    (∀ i, i < m → Function.Injective (ρ i)) →
    (∀ i j : ℕ, i < m → j < m → i ≠ j → ¬ CompsPTwoDChain.dEdge m i j →
      ¬ CompsPTwoDChain.dEdge m j i → ∀ A B, ρ i A * ρ j B = ρ j B * ρ i A) →
    (∀ i : ℕ, i + 3 < m → ∃ θ : SL(3, L) →* G,
      θ.comp (blockSL L 3 2 0 (by omega)) = ρ i ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = ρ (i + 1)) →
    Φ.comp (blockSL2 L 3 0) = ρ (m - 2) → Φ.comp (blockSL2 L 3 1) = ρ (m - 3) →
    Φ.comp (blockSL2 L 3 2) = ρ (m - 1) →
    (⨆ i : Fin (m - 1), if i.val + 2 < m then
        ((ρ i.val).comp (Matrix.SpecialLinearGroup.map
          ((frobeniusFixedField L r (e * 2)).subtype.comp (algebraMap
            ↥(frobeniusFixedField L r e) ↥(frobeniusFixedField L r (e * 2)))))).range
      else ((Φ.comp (Matrix.SpecialLinearGroup.map (frobeniusFixedField L r (e * 2)).subtype)).comp
        (usbSL (CompsPTwoDKlein.frobInvol (k := L) (p := r) e).toRingHom
          (fun x => CompsPTwoDKlein.frobHom_frobHom e x))).range) = C →
    LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaMinus m r e

end Recog

section Main


open CFSG.Timmesfeld CFSG.Timmesfeld.LevisSpin

theorem exists_chain_of_datum_core {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L] {M : Type}
    [CommGroup M] (D : GenFixedRootDatum τ r L M) {m : ℕ}
    (hm4 : 4 ≤ m) (b : Fin m → Fin τ.rank → ℤ)
    (hroot : ∀ j, IsRoot τ (b j))
    (hbinj : Function.Injective b)
    (hG : ∀ j k, iform (b j) (b k) = CFSG.LieType.Universal.Spin.cartanD m j k)
    (hsimple : D.simpleRootsJ = Set.range b)
    (hfix : ∀ j : Fin m, j.val + 2 < m → D.θ (toReal (b j)) = toReal (b j))
    (hswap01 : D.θ (toReal (b ⟨m - 2, by omega⟩)) = toReal (b ⟨m - 1, by omega⟩))
    (hswap10 : D.θ (toReal (b ⟨m - 1, by omega⟩)) = toReal (b ⟨m - 2, by omega⟩))
    (horb : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) =
      b ⟨m - 2, by omega⟩)
    (hframe : ∀ j k : Fin m, CFSG.LieType.Universal.Spin.cartanD m j k = -1 →
      ∃ θ : SL(3, L) →* ModGL τ L, θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (b j) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (b k)) :
    ∃ (ρ : ℕ → SL(2, L) →* ModGL τ L) (Φ : SL(4, L) →* ModGL τ L),
      (∀ j : Fin m, ρ j.val = rootSL2 τ L (b j)) ∧
      (∀ i, i < m → Function.Injective (ρ i)) ∧
      (∀ i j : ℕ, i < m → j < m → i ≠ j → ¬ CompsPTwoDChain.dEdge m i j →
        ¬ CompsPTwoDChain.dEdge m j i → ∀ A B, ρ i A * ρ j B = ρ j B * ρ i A) ∧
      (∀ i : ℕ, i + 3 < m → ∃ θ : SL(3, L) →* ModGL τ L,
        θ.comp (blockSL L 3 2 0 (by omega)) = ρ i ∧
          θ.comp (blockSL L 3 2 1 (by omega)) = ρ (i + 1)) ∧
      Φ.comp (blockSL2 L 3 0) = ρ (m - 2) ∧
      Φ.comp (blockSL2 L 3 1) = ρ (m - 3) ∧
      Φ.comp (blockSL2 L 3 2) = ρ (m - 1) ∧
      (⨆ i : Fin (m - 1), if i.val + 2 < m then
        ((ρ i.val).comp (Matrix.SpecialLinearGroup.map
          ((frobeniusFixedField L r (D.e * 2)).subtype.comp (algebraMap
            ↥(frobeniusFixedField L r D.e) ↥(frobeniusFixedField L r (D.e * 2)))))).range
      else ((Φ.comp (Matrix.SpecialLinearGroup.map (frobeniusFixedField L r (D.e * 2)).subtype)).comp
        (usbSL (CompsPTwoDKlein.frobInvol (k := L) (p := r) D.e).toRingHom
          (fun x => CompsPTwoDKlein.frobHom_frobHom D.e x))).range) = D.orbitGroup := by
  classical
  set a0 : Fin m := ⟨m - 2, by omega⟩ with ha0
  set a1 : Fin m := ⟨m - 1, by omega⟩ with ha1
  set a2 : Fin m := ⟨m - 3, by omega⟩ with ha2
  have hdiag : ∀ j : Fin m, CFSG.LieType.Universal.Spin.cartanD m j j = 2 := fun j => by
    rw [cartanD_apply]; simp
  have hbD : ∀ j, b j ∈ D.simpleRootsJ := fun j => by rw [hsimple]; exact ⟨j, rfl⟩
  have hmemOrb : ∀ j, thetaOrbit D.θ (b j) ∈ D.orbits := fun j => ⟨b j, hbD j, rfl⟩
  have hOfix : ∀ j : Fin m, j.val + 2 < m → thetaOrbit D.θ (b j) = {b j} := fun j hj =>
    thetaOrbit_of_fixed (hfix j hj)
  have hOf : thetaOrbit D.θ (b a0) = {b a0, b a1} := thetaOrbit_of_swap hswap01 hswap10
  have hOf' : thetaOrbit D.θ (b a1) = {b a0, b a1} := by
    rw [thetaOrbit_of_swap hswap10 hswap01, Set.pair_comm]
  have hne01 : b a0 ≠ b a1 := fun h => by
    have := hbinj h
    simp only [ha0, ha1, Fin.mk.injEq] at this
    omega
  have hOcases : ∀ O ∈ D.orbits, (∃ j : Fin m, j.val + 2 < m ∧ O = thetaOrbit D.θ (b j)) ∨
      O = thetaOrbit D.θ (b a0) := by
    rintro O ⟨β, hβ, rfl⟩
    rw [hsimple] at hβ
    obtain ⟨j, rfl⟩ := hβ
    by_cases hj : j.val + 2 < m
    · exact Or.inl ⟨j, hj, rfl⟩
    · right
      have hj' : j = a0 ∨ j = a1 := by
        have : j.val = m - 2 ∨ j.val = m - 1 := by have := j.isLt; omega
        rcases this with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hj' with rfl | rfl
      · rfl
      · rw [hOf', hOf]
  have hcard1 : ∀ j : Fin m, j.val + 2 < m →
      GenFixedRootDatum.orbitCard (thetaOrbit D.θ (b j)) = 1 := fun j hj => by
    rw [hOfix j hj]
    exact Set.ncard_singleton _
  have hcard2 : GenFixedRootDatum.orbitCard (thetaOrbit D.θ (b a0)) = 2 := by
    rw [hOf]
    exact Set.ncard_pair hne01
  have hroot1 : ∀ j : Fin m, j.val + 2 < m →
      GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b j)) = b j := fun j hj => by
    rw [hOfix j hj]
    exact Set.mem_singleton_iff.1 (lexLeast_mem (Set.finite_singleton _) (Set.singleton_nonempty _))
  have hX : ∀ O ∈ D.orbits, ∀ c : ↥(D.orbitField O), D.orbitX O c ∈ D.orbitGroup ∧
      D.orbitY O c ∈ D.orbitGroup := fun O hO c =>
    ⟨Subgroup.subset_closure ⟨O, hO, c, Or.inl rfl⟩, Subgroup.subset_closure ⟨O, hO, c, Or.inr rfl⟩⟩
  have hmemq : ∀ O : Set (Fin τ.rank → ℤ), ∀ x : L, x ∈ D.orbitField O ↔
      x ^ r ^ (D.e * GenFixedRootDatum.orbitCard O) = x := fun O x => by
    rw [D.mem_orbitField, GenFixedRootDatum.q, pow_mul]
  have hXeq : ∀ j : Fin m, j.val + 2 < m → ∀ c : ↥(D.orbitField (thetaOrbit D.θ (b j))),
      D.orbitX (thetaOrbit D.θ (b j)) c = rootSL2 τ L (b j) (uSL (c : L)) ∧
        D.orbitY (thetaOrbit D.θ (b j)) c = rootSL2 τ L (b j) (vSL (c : L)) := by
    intro j hj c
    refine ⟨?_, ?_⟩
    · rw [GenFixedRootDatum.orbitX, orbitMap_single D (hcard1 j hj), hroot1 j hj, map_uSL']
      rfl
    · rw [GenFixedRootDatum.orbitY, orbitMap_single D (hcard1 j hj), hroot1 j hj, map_vSL']
      rfl
  have hXeqf : ∀ c : ↥(D.orbitField (thetaOrbit D.θ (b a0))),
      D.orbitX (thetaOrbit D.θ (b a0)) c =
        rootSL2 τ L (b a0) (uSL (c : L)) * rootSL2 τ L (b a1) (uSL ((c : L) ^ r ^ D.e)) ∧
      D.orbitY (thetaOrbit D.θ (b a0)) c =
        rootSL2 τ L (b a0) (vSL (c : L)) * rootSL2 τ L (b a1) (vSL ((c : L) ^ r ^ D.e)) := by
    intro c
    refine ⟨?_, ?_⟩
    · rw [GenFixedRootDatum.orbitX, orbitMap_pair D hcard2 horb hswap01]
      simp only [map_uSL', Subfield.coe_subtype, iterateFrobenius_def]
    · rw [GenFixedRootDatum.orbitY, orbitMap_pair D hcard2 horb hswap01]
      simp only [map_vSL', Subfield.coe_subtype, iterateFrobenius_def]
  have hlongmem : ∀ j : Fin m, j.val + 2 < m → ∀ x : L, x ^ r ^ D.e = x →
      rootSL2 τ L (b j) (uSL x) ∈ D.orbitGroup ∧ rootSL2 τ L (b j) (vSL x) ∈ D.orbitGroup := by
    intro j hj x hx
    have hxO : x ∈ D.orbitField (thetaOrbit D.θ (b j)) := by
      rw [hmemq, hcard1 j hj, mul_one]
      exact hx
    obtain ⟨h1, h2⟩ := hX _ (hmemOrb j) ⟨x, hxO⟩
    obtain ⟨e1, e2⟩ := hXeq j hj ⟨x, hxO⟩
    exact ⟨e1 ▸ h1, e2 ▸ h2⟩
  have hforkmem : ∀ x : L, x ^ r ^ (D.e * 2) = x →
      rootSL2 τ L (b a0) (uSL x) * rootSL2 τ L (b a1) (uSL (x ^ r ^ D.e)) ∈ D.orbitGroup ∧
        rootSL2 τ L (b a0) (vSL x) * rootSL2 τ L (b a1) (vSL (x ^ r ^ D.e)) ∈ D.orbitGroup := by
    intro x hx
    have hxO : x ∈ D.orbitField (thetaOrbit D.θ (b a0)) := by
      rw [hmemq, hcard2]
      exact hx
    obtain ⟨h1, h2⟩ := hX _ (hmemOrb a0) ⟨x, hxO⟩
    obtain ⟨e1, e2⟩ := hXeqf ⟨x, hxO⟩
    exact ⟨e1 ▸ h1, e2 ▸ h2⟩
  let bn : ℕ → Fin τ.rank → ℤ := fun i => if h : i < m then b ⟨i, h⟩ else 0
  have hbn : ∀ j : Fin m, bn j.val = b j := fun j => by simp [bn, j.isLt]
  let ρ : ℕ → SL(2, L) →* ModGL τ L := fun i => rootSL2 τ L (bn i)
  have hρi : ∀ j : Fin m, ρ j.val = rootSL2 τ L (b j) := fun j => by simp only [ρ, hbn]
  have hρinj : ∀ i, i < m → Function.Injective (ρ i) := fun i _ => rootSL2_injective_of_field _
  have hcomm : ∀ i j : ℕ, i < m → j < m → i ≠ j → ¬ CompsPTwoDChain.dEdge m i j →
      ¬ CompsPTwoDChain.dEdge m j i → ∀ A B, ρ i A * ρ j B = ρ j B * ρ i A := by
    intro i j hi hj hij h1 h2 A B
    have h0 : iform (b ⟨i, hi⟩) (b ⟨j, hj⟩) = 0 := by
      rw [hG]
      exact (cartanD_of_not_edgeD (n := m) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
        (fun h => hij (by simpa using congrArg Fin.val h)) h1 h2).1
    have := (commute_rootSL2_of_iform_eq_zero hτ (hroot ⟨i, hi⟩) (hroot ⟨j, hj⟩) h0 A B).eq
    have e1 := hρi ⟨i, hi⟩
    have e2 := hρi ⟨j, hj⟩
    simp only at e1 e2
    rw [e1, e2]
    exact this
  have hfr : ∀ i : ℕ, i + 3 < m → ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = ρ i ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = ρ (i + 1) := by
    intro i hi
    have hedge : edgeD m ⟨i, by omega⟩ ⟨i + 1, by omega⟩ :=
      Or.inl ⟨rfl, by simp only; omega⟩
    obtain ⟨θ, h0, h1⟩ := hframe ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (cartanD_of_edgeD hedge).1
    exact ⟨θ, h0.trans (hρi ⟨i, by omega⟩).symm, h1.trans (hρi ⟨i + 1, by omega⟩).symm⟩
  have v1 : CFSG.LieType.Universal.Spin.cartanD m a0 a2 = -1 := (cartanD_fork_values hm4).1
  have v2 : CFSG.LieType.Universal.Spin.cartanD m a2 a0 = -1 := (cartanD_fork_values hm4).2.1
  have v3 : CFSG.LieType.Universal.Spin.cartanD m a1 a2 = -1 := (cartanD_fork_values hm4).2.2.1
  have v4 : CFSG.LieType.Universal.Spin.cartanD m a2 a1 = -1 := (cartanD_fork_values hm4).2.2.2.1
  have v5 : CFSG.LieType.Universal.Spin.cartanD m a0 a1 = 0 :=
    (cartanD_fork_values hm4).2.2.2.2.1
  have v6 : CFSG.LieType.Universal.Spin.cartanD m a1 a0 = 0 :=
    (cartanD_fork_values hm4).2.2.2.2.2
  let β3 : Fin 3 → Fin τ.rank → ℤ := ![b a0, b a2, b a1]
  have hβroot : ∀ c, IsRoot τ (β3 c) := fun c => by
    fin_cases c
    · exact hroot a0
    · exact hroot a2
    · exact hroot a1
  have hGβ : ∀ c d, iform (β3 c) (β3 d) = chainGram c d := by
    intro c d
    fin_cases c <;> fin_cases d <;>
      simp [β3, chainGram, hG, hdiag, v1, v2, v3, v4, v5, v6]
  have hθβ : ∀ (c : Fin 3) (h : (c : ℕ) + 1 < 3), ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (β3 c) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (β3 ⟨c + 1, h⟩) := by
    intro c h
    fin_cases c
    · exact hframe a0 a2 v1
    · exact hframe a2 a1 v4
    · exact absurd h (by decide)
  obtain ⟨Φ, hΦ⟩ := exists_chainHom hτ β3 hβroot hGβ hθβ
  have hΦ0 : Φ.comp (blockSL2 L 3 0) = ρ (m - 2) := (hΦ 0).trans (hρi a0).symm
  have hΦ1 : Φ.comp (blockSL2 L 3 1) = ρ (m - 3) := (hΦ 1).trans (hρi a2).symm
  have hΦ2 : Φ.comp (blockSL2 L 3 2) = ρ (m - 1) := (hΦ 2).trans (hρi a1).symm
  set ι : ↥(frobeniusFixedField L r (D.e * 2)) →+* L :=
    (frobeniusFixedField L r (D.e * 2)).subtype with hι
  have hσσ : ∀ x : ↥(frobeniusFixedField L r (D.e * 2)),
      (CompsPTwoDKlein.frobInvol (k := L) (p := r) D.e).toRingHom
        ((CompsPTwoDKlein.frobInvol (k := L) (p := r) D.e).toRingHom x) = x :=
    fun x => CompsPTwoDKlein.frobHom_frobHom D.e x
  let linNode : ℕ → Subgroup (ModGL τ L) := fun i =>
    ((ρ i).comp (Matrix.SpecialLinearGroup.map (ι.comp (algebraMap
      ↥(frobeniusFixedField L r D.e) ↥(frobeniusFixedField L r (D.e * 2)))))).range
  let Vg : Subgroup (ModGL τ L) := ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
    (usbSL (CompsPTwoDKlein.frobInvol (k := L) (p := r) D.e).toRingHom hσσ)).range
  have hlongrange : ∀ j : Fin m, j.val + 2 < m → ∀ x : L, x ^ r ^ D.e = x →
      rootSL2 τ L (b j) (uSL x) ∈ linNode j.val ∧ rootSL2 τ L (b j) (vSL x) ∈ linNode j.val := by
    intro j hj x hx
    have hxF : x ∈ frobeniusFixedField L r D.e :=
      CFSG.LieType.Chevalley.mem_frobeniusFixedField.2 hx
    refine ⟨⟨uSL (⟨x, hxF⟩ : ↥(frobeniusFixedField L r D.e)), ?_⟩,
      ⟨vSL (⟨x, hxF⟩ : ↥(frobeniusFixedField L r D.e)), ?_⟩⟩
    · simp only [MonoidHom.comp_apply, map_uSL', hρi j]
      rfl
    · simp only [MonoidHom.comp_apply, map_vSL', hρi j]
      rfl
  have hρ0 : ρ (m - 2) = rootSL2 τ L (b a0) := hρi a0
  have hρ1 : ρ (m - 1) = rootSL2 τ L (b a1) := hρi a1
  have hforkrange : ∀ x : L, x ^ r ^ (D.e * 2) = x →
      rootSL2 τ L (b a0) (uSL x) * rootSL2 τ L (b a1) (uSL (x ^ r ^ D.e)) ∈ Vg ∧
        rootSL2 τ L (b a0) (vSL x) * rootSL2 τ L (b a1) (vSL (x ^ r ^ D.e)) ∈ Vg := by
    intro x hx
    have hxK : x ∈ frobeniusFixedField L r (D.e * 2) :=
      CFSG.LieType.Chevalley.mem_frobeniusFixedField.2 hx
    refine ⟨⟨uSL (⟨x, hxK⟩ : ↥(frobeniusFixedField L r (D.e * 2))), ?_⟩,
      ⟨vSL (⟨x, hxK⟩ : ↥(frobeniusFixedField L r (D.e * 2))), ?_⟩⟩
    · simp only [MonoidHom.comp_apply]
      rw [CompsPTwoDChain.phi_usbSL ι hσσ Φ hΦ0 hΦ2, map_uSL', map_uSL', hρ0, hρ1]
      rfl
    · simp only [MonoidHom.comp_apply]
      rw [CompsPTwoDChain.phi_usbSL ι hσσ Φ hΦ0 hΦ2, map_vSL', map_vSL', hρ0, hρ1]
      rfl
  have hle_long : ∀ j : Fin m, j.val + 2 < m → linNode j.val ≤
      ⨆ i : Fin (m - 1), if i.val + 2 < m then linNode i.val else Vg := by
    intro j hj
    have hlt : j.val < m - 1 := by omega
    have := le_iSup (fun i : Fin (m - 1) => if i.val + 2 < m then linNode i.val else Vg)
      ⟨j.val, hlt⟩
    simpa only [if_pos (show (⟨j.val, hlt⟩ : Fin (m - 1)).val + 2 < m from hj)] using this
  have hle_fork : Vg ≤ ⨆ i : Fin (m - 1), if i.val + 2 < m then linNode i.val else Vg := by
    have hlt : m - 2 < m - 1 := by omega
    have hcond : ¬ (⟨m - 2, hlt⟩ : Fin (m - 1)).val + 2 < m := by
      show ¬ m - 2 + 2 < m
      omega
    have := le_iSup (fun i : Fin (m - 1) => if i.val + 2 < m then linNode i.val else Vg)
      ⟨m - 2, hlt⟩
    simpa only [if_neg hcond] using this
  have hC : (⨆ i : Fin (m - 1), if i.val + 2 < m then linNode i.val else Vg) =
      D.orbitGroup := by
    refine le_antisymm (iSup_le fun i => ?_) ?_
    · by_cases hi : i.val + 2 < m
      · rw [if_pos hi]
        rintro _ ⟨A, rfl⟩
        refine sl2_hom_mem_of_gens _ D.orbitGroup (fun t => ?_) (fun t => ?_) A
        · have h := (hlongmem ⟨i.val, by omega⟩ hi (t : L)
            (CFSG.LieType.Chevalley.mem_frobeniusFixedField.1 t.2)).1
          rw [← hρi ⟨i.val, by omega⟩] at h
          simp only [MonoidHom.comp_apply, map_uSL']
          exact h
        · have h := (hlongmem ⟨i.val, by omega⟩ hi (t : L)
            (CFSG.LieType.Chevalley.mem_frobeniusFixedField.1 t.2)).2
          rw [← hρi ⟨i.val, by omega⟩] at h
          simp only [MonoidHom.comp_apply, map_vSL']
          exact h
      · rw [if_neg hi]
        rintro _ ⟨B, rfl⟩
        refine sl2_hom_mem_of_gens _ D.orbitGroup (fun t => ?_) (fun t => ?_) B
        · have h := (hforkmem (t : L) (CFSG.LieType.Chevalley.mem_frobeniusFixedField.1 t.2)).1
          rw [← hρi a0, ← hρi a1] at h
          have e := CompsPTwoDChain.phi_usbSL ι hσσ Φ hΦ0 hΦ2 (uSL t)
          simp only [MonoidHom.comp_apply, e, map_uSL']
          exact h
        · have h := (hforkmem (t : L) (CFSG.LieType.Chevalley.mem_frobeniusFixedField.1 t.2)).2
          rw [← hρi a0, ← hρi a1] at h
          have e := CompsPTwoDChain.phi_usbSL ι hσσ Φ hΦ0 hΦ2 (vSL t)
          simp only [MonoidHom.comp_apply, e, map_vSL']
          exact h
    · have hgen : ∀ O ∈ D.orbits, ∀ c : ↥(D.orbitField O),
          D.orbitX O c ∈ (⨆ i : Fin (m - 1), if i.val + 2 < m then linNode i.val else Vg) ∧
          D.orbitY O c ∈ (⨆ i : Fin (m - 1), if i.val + 2 < m then linNode i.val else Vg) := by
        intro O hO c
        rcases hOcases O hO with ⟨j, hj, rfl⟩ | rfl
        · have hx : (c : L) ^ r ^ D.e = c := by
            have := (hmemq _ (c : L)).1 c.2
            rwa [hcard1 j hj, mul_one] at this
          obtain ⟨h1, h2⟩ := hlongrange j hj (c : L) hx
          obtain ⟨e1, e2⟩ := hXeq j hj c
          exact ⟨e1 ▸ hle_long j hj h1, e2 ▸ hle_long j hj h2⟩
        · have hx : (c : L) ^ r ^ (D.e * 2) = c := by
            have := (hmemq _ (c : L)).1 c.2
            rwa [hcard2] at this
          obtain ⟨h1, h2⟩ := hforkrange (c : L) hx
          obtain ⟨e1, e2⟩ := hXeqf c
          exact ⟨e1 ▸ hle_fork h1, e2 ▸ hle_fork h2⟩
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨O, hO, c, rfl | rfl⟩
      · exact (hgen O hO c).1
      · exact (hgen O hO c).2
  exact ⟨ρ, Φ, hρi, hρinj, hcomm, hfr, hΦ0, hΦ1, hΦ2, hC⟩

theorem rationalLieType_of_datum_core_gen {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L] {M : Type}
    [CommGroup M] (D : GenFixedRootDatum τ r L M) {m : ℕ}
    (hm5 : 5 ≤ m) (hrec : TwoDChainRecog r L D.e m) (b : Fin m → Fin τ.rank → ℤ)
    (hroot : ∀ j, IsRoot τ (b j))
    (hbinj : Function.Injective b)
    (hG : ∀ j k, iform (b j) (b k) = CFSG.LieType.Universal.Spin.cartanD m j k)
    (hsimple : D.simpleRootsJ = Set.range b)
    (hfix : ∀ j : Fin m, j.val + 2 < m → D.θ (toReal (b j)) = toReal (b j))
    (hswap01 : D.θ (toReal (b ⟨m - 2, by omega⟩)) = toReal (b ⟨m - 1, by omega⟩))
    (hswap10 : D.θ (toReal (b ⟨m - 1, by omega⟩)) = toReal (b ⟨m - 2, by omega⟩))
    (horb : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) =
      b ⟨m - 2, by omega⟩)
    (hframe : ∀ j k : Fin m, CFSG.LieType.Universal.Spin.cartanD m j k = -1 →
      ∃ θ : SL(3, L) →* ModGL τ L, θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (b j) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (b k)) :
    RationalLieType r D.orbitGroup := by
  obtain ⟨ρ, Φ, -, hρinj, hcomm, hfr, hΦ0, hΦ1, hΦ2, hC⟩ :=
    exists_chain_of_datum_core hτ D (by omega) b hroot hbinj hG hsimple hfix hswap01 hswap10
      horb hframe
  exact lieModel_pominus_chev (hrec ρ Φ D.orbitGroup hρinj hcomm hfr hΦ0 hΦ1 hΦ2 hC)

theorem rationalLieType_of_datum_gen {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L] {M : Type}
    [CommGroup M] (D : GenFixedRootDatum τ r L M) {m : ℕ}
    (hm5 : 5 ≤ m) (hrec : TwoDChainRecog r L D.e m) (b : Fin m → Fin τ.rank → ℤ)
    (hroot : ∀ j, IsRoot τ (b j))
    (hbinj : Function.Injective b)
    (hG : ∀ j k, iform (b j) (b k) = CFSG.LieType.Universal.Spin.cartanD m j k)
    (hsimple : D.simpleRootsJ = Set.range b)
    (hfix : ∀ j : Fin m, j.val + 2 < m → D.θ (toReal (b j)) = toReal (b j))
    (hswap01 : D.θ (toReal (b ⟨m - 2, by omega⟩)) = toReal (b ⟨m - 1, by omega⟩))
    (hswap10 : D.θ (toReal (b ⟨m - 1, by omega⟩)) = toReal (b ⟨m - 2, by omega⟩))
    (hframe : ∀ j k : Fin m, CFSG.LieType.Universal.Spin.cartanD m j k = -1 →
      ∃ θ : SL(3, L) →* ModGL τ L, θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (b j) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (b k)) :
    RationalLieType r D.orbitGroup := by
  classical
  have hm4 : 4 ≤ m := by omega
  have hOf : thetaOrbit D.θ (b ⟨m - 2, by omega⟩) = {b ⟨m - 2, by omega⟩, b ⟨m - 1, by omega⟩} :=
    thetaOrbit_of_swap hswap01 hswap10
  have hOf' : thetaOrbit D.θ (b ⟨m - 1, by omega⟩) =
      {b ⟨m - 2, by omega⟩, b ⟨m - 1, by omega⟩} := by
    rw [thetaOrbit_of_swap hswap10 hswap01, Set.pair_comm]
  by_cases h : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) =
      b ⟨m - 2, by omega⟩
  · exact rationalLieType_of_datum_core_gen hτ D hm5 hrec b hroot hbinj hG hsimple hfix hswap01
      hswap10 h hframe
  · have hmem : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) ∈
        thetaOrbit D.θ (b ⟨m - 2, by omega⟩) :=
      lexLeast_mem (by rw [hOf]; exact Set.toFinite _) ⟨_, self_mem_thetaOrbit _ _⟩
    have h1 : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) =
        b ⟨m - 1, by omega⟩ := by
      have hmem' : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) ∈
          ({b ⟨m - 2, by omega⟩, b ⟨m - 1, by omega⟩} : Set (Fin τ.rank → ℤ)) := by
        rw [← hOf]
        exact hmem
      rcases hmem' with h' | h'
      · exact absurd h' h
      · exact h'
    have hsw0 : Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ =
        ⟨m - 1, by omega⟩ := Equiv.swap_apply_left _ _
    have hsw1 : Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩ =
        ⟨m - 2, by omega⟩ := Equiv.swap_apply_right _ _
    refine rationalLieType_of_datum_core_gen hτ D hm5 hrec
      (fun j => b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ j))
      (fun j => hroot _) (hbinj.comp (Equiv.injective _))
      (fun j k => by rw [hG, cartanD_swap hm4]) ?_ (fun j hj => ?_) ?_ ?_ ?_ (fun j k hjk => ?_)
    · rw [hsimple]
      exact ((Equiv.swap (⟨m - 2, by omega⟩ : Fin m)
        ⟨m - 1, by omega⟩).surjective.range_comp b).symm
    · have e : Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ j = j :=
        Equiv.swap_apply_of_ne_of_ne
          (fun h' => by rw [h'] at hj; simp only [Fin.val_mk] at hj; omega)
          (fun h' => by rw [h'] at hj; simp only [Fin.val_mk] at hj; omega)
      show D.θ (toReal (b (Equiv.swap _ _ j))) = toReal (b (Equiv.swap _ _ j))
      rw [e]
      exact hfix j hj
    · show D.θ (toReal (b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩
        ⟨m - 2, by omega⟩))) = toReal (b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m)
          ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩))
      rw [hsw0, hsw1]
      exact hswap10
    · show D.θ (toReal (b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩
        ⟨m - 1, by omega⟩))) = toReal (b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m)
          ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩))
      rw [hsw0, hsw1]
      exact hswap01
    · show GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m)
        ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩))) =
          b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩)
      rw [hsw0, hOf', ← hOf, h1]
    · exact hframe _ _ (by rw [cartanD_swap hm4]; exact hjk)

end Main

end CompsPTwoDDatumG

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
