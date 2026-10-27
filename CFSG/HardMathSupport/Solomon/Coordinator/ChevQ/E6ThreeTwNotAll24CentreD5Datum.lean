module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Recog
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMainG

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.LieType.AlgebraicGroups CFSG.Open CFSG.RankThree.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisSpin CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDDatum
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDDatumG
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDMain
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDMainG
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

theorem DStrongModel.of_equiv {G G' : Type} [Group G] [Group G'] {R : Subgroup G}
    {C : Subgroup G'} {m r e : ℕ} (eRC : ↥R ≃* ↥C) (hC : DStrongModel C m r e) :
    DStrongModel R m r e := by
  obtain ⟨hlie, hq, hz⟩ := hC
  refine ⟨?_, ?_, fun z hz' => ?_⟩
  · let g : (↥R ⧸ Subgroup.center ↥R) ≃* (↥C ⧸ Subgroup.center ↥C) :=
      QuotientGroup.congr _ _ eRC (Subgroup.map_center_eq eRC)
    exact CFSG.Blueprint.LieModel.of_mulEquiv g.symm hlie
  · exact hq.of_mulEquiv eRC
  · have hzC : eRC z ∈ Subgroup.center ↥C := by
      have := Subgroup.map_center_eq eRC
      rw [← this]
      exact ⟨z, hz', rfl⟩
    have := hz _ hzC
    apply eRC.injective
    rw [map_pow, this, map_one]

theorem DStrongModel.of_map_eq {G : Type} [Group G] (φ : G ≃* G) {R C : Subgroup G} {m r e : ℕ}
    (h : R.map φ.toMonoidHom = C) (hC : DStrongModel C m r e) : DStrongModel R m r e :=
  DStrongModel.of_equiv
    ((R.equivMapOfInjective φ.toMonoidHom φ.injective).trans (MulEquiv.subgroupCongr h)) hC

section Main


theorem strongModel_of_datum_core_gen {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L] {M : Type}
    [CommGroup M] (D : GenFixedRootDatum τ r L M) {m : ℕ}
    (hm5 : 5 ≤ m) (hrec : TwoDChainRecogS r L D.e m) (b : Fin m → Fin τ.rank → ℤ)
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
    DStrongModel D.orbitGroup m r D.e := by
  classical
  have hm4 : 4 ≤ m := by omega
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
  exact hrec ρ Φ D.orbitGroup hρinj hcomm hfr hΦ0 hΦ1 hΦ2 hC


theorem strongModel_of_datum_gen {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L] {M : Type}
    [CommGroup M] (D : GenFixedRootDatum τ r L M) {m : ℕ}
    (hm5 : 5 ≤ m) (hrec : TwoDChainRecogS r L D.e m) (b : Fin m → Fin τ.rank → ℤ)
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
    DStrongModel D.orbitGroup m r D.e := by
  classical
  have hm4 : 4 ≤ m := by omega
  have hOf : thetaOrbit D.θ (b ⟨m - 2, by omega⟩) = {b ⟨m - 2, by omega⟩, b ⟨m - 1, by omega⟩} :=
    thetaOrbit_of_swap hswap01 hswap10
  have hOf' : thetaOrbit D.θ (b ⟨m - 1, by omega⟩) =
      {b ⟨m - 2, by omega⟩, b ⟨m - 1, by omega⟩} := by
    rw [thetaOrbit_of_swap hswap10 hswap01, Set.pair_comm]
  by_cases h : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) =
      b ⟨m - 2, by omega⟩
  · exact strongModel_of_datum_core_gen hτ D hm5 hrec b hroot hbinj hG hsimple hfix hswap01
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
    refine strongModel_of_datum_core_gen hτ D hm5 hrec
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


variable {τ : Tag}

theorem strongModel_of_dClassTwistedG (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 4 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = 2 * c.length * (c.length - 1) →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (Q : ℕ → ℕ → Prop) (hrec : TwoDChainRecogSAll L Q) (hQ : Q (ringChar L) S.D.q) :
    ∃ (r e m : ℕ), ringChar L = r ∧ S.D.q = r ^ e ∧ 5 ≤ m ∧
      m = compRank (componentRoots (rootCharHom a) i) ∧
        DStrongModel (rationalComponent S.ρ S.Γ (rootCharHom a) i) m r e := by
  classical
  obtain ⟨r, e, m, hr, hchar, hm5, z, ε, D, hq, he, hDe, hRC, hDs, hCart, hfix, hswap⟩ :=
    CompsPTwoDExport.exists_twoD_export S hτ hTor i hkind h5
  haveI := hr
  haveI := hchar
  have hrc : ringChar L = r := ringChar.eq L r
  have hQ' : Q r (r ^ e) := by
    have h := hQ
    rw [hrc, hq] at h
    exact h
  have hR : TwoDChainRecogS r L D.e m := by
    rw [hDe]
    exact hrec r e m he hm5 hQ'
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) := isRootComponent_componentRoots i
  have hsl : ∀ β ∈ componentRoots (rootCharHom a) i, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  have hbroot : ∀ j : Fin m, IsRoot τ (ε.symm j : Fin τ.rank → ℤ) := fun j =>
    simpleRoots_isRoot (ε.symm j).2
  have hbinj : Function.Injective (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) :=
    fun j k h => ε.symm.injective (Subtype.ext h)
  have hG : ∀ j k : Fin m, iform (ε.symm j : Fin τ.rank → ℤ) (ε.symm k) =
      CFSG.LieType.Universal.Spin.cartanD m j k := by
    intro j k
    have h := hCart (ε.symm j) (ε.symm k)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    rw [← h]
    exact (CompsPTwoDBase.corootPair_eq_iform (hbroot j)
      (hsl _ (simpleRoots_subset (ε.symm j).2)) _).symm
  have hrange : Set.range (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) =
      ((simpleRoots (componentRoots (rootCharHom a) i) : Finset (Fin τ.rank → ℤ)) :
        Set (Fin τ.rank → ℤ)) := by
    ext β
    constructor
    · rintro ⟨j, rfl⟩
      exact (ε.symm j).2
    · intro hβ
      exact ⟨ε ⟨β, hβ⟩, by simp⟩
  have hsw := hswap ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
    (by simp only [Fin.val_mk]; omega)
  have hdat := strongModel_of_datum_gen hτ D hm5 hR
    (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) hbroot hbinj hG (hDs.trans hrange.symm) hfix
    hsw.1 hsw.2
    (fun j k hjk => exists_dFrames hτ K hK hT hadj hcheck hlt hcard hcount htrees hframes S hp hpL
      hTp i (by omega) hn ε hCart L j k hjk)
  have hmc : m = compRank (componentRoots (rootCharHom a) i) := by
    rw [CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ]
    have := Fintype.card_congr ε
    simpa using this.symm
  refine ⟨r, e, m, hrc, hq, hm5, hmc, ?_⟩
  rw [hDe] at hdat
  exact DStrongModel.of_map_eq (MulAut.conj z⁻¹) hRC hdat

section PerTag

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}

theorem strongModel_of_dClassTwistedG_E6 (S : LangSetup Tag.E6 L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (Q : ℕ → ℕ → Prop) (hrec : TwoDChainRecogSAll L Q) (hQ : Q (ringChar L) S.D.q) :
    ∃ (r e m : ℕ), ringChar L = r ∧ S.D.q = r ^ e ∧ 5 ≤ m ∧
      m = compRank (componentRoots (rootCharHom a) i) ∧
        DStrongModel (rationalComponent S.ρ S.Γ (rootCharHom a) i) m r e :=
  strongModel_of_dClassTwistedG (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check
    e6_lt e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp i h5
    hn hkind Q hrec hQ

end PerTag

end Main

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
