module

public import CFSG.ClassicalInvolution.Q3.Q3VF4CModel
public import CFSG.ClassicalInvolution.Q3.Q3VChain3Row
public import CFSG.ClassicalInvolution.Q3.Q3VF4Row

set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.Blueprint.Chevalley CFSG.ComponentClassification.CatLeafProof
  CFSG.ClassicalInvolution.RouteD

theorem lieModel_of_top_center {G : Type} [Group G] (hZ : Subgroup.center G = ⊥)
    {H : Subgroup G} (hH : H = ⊤) {t : StatedLieTag} {n p f : ℕ}
    (h : Blueprint.LieModel (↥H ⧸ Subgroup.center ↥H) t n p f) : Blueprint.LieModel G t n p f := by
  let eX : ↥H ≃* G := (MulEquiv.subgroupCongr hH).trans Subgroup.topEquiv
  have hZX : Subgroup.center ↥H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : eX x ∈ Subgroup.center G :=
      Subgroup.map_center_le_center (f := eX.toMonoidHom) eX.surjective ⟨x, hx, rfl⟩
    rw [hZ, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (eX.injective (by rw [hx', map_one]))
  exact CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZX).trans (QuotientGroup.quotientBot.trans eX)) h


@[expose] def F4Chain3 {G : Type} [Group G] (K : Subgroup G) : Prop :=
  ∃ U : Fin 4 → Subgroup G, U 1 ∈ conjClass3 K ∧
    (∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) ∧
    (∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
      ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) ∧
    (∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U 1) (U 2))

theorem oddLieType_of_f4Chain3 (hC6 : Q3Z.V6Collapse) (hC3 : Q3TW.B3Collapse) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (hR : Q3W.RouteD3Setup K z)
    (hshape : Q3W.LocalShapeC3 1 (CompData.model .PSp 3) (conjClass3 K) z)
    (hO3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z) (hch : F4Chain3 K) :
    Blueprint.OddLieType G := by
  obtain ⟨U, hU1, hcomm, hpair, hsp⟩ := hch
  obtain ⟨Ψ, hker, hrange, -, hlie, hblk⟩ := weakCT3_f4_subgroup hC6 hC3 U hcomm hpair hsp
  obtain ⟨M⟩ := nonempty_extModel3_F4 hC6
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadm : StatedLieAdmissible .F4 0 3 1 := ⟨hp, le_rfl, rfl⟩
  have hscT : FundamentalSingleClass .F4 (modelUniv .F4 0 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .F4 0 3 1 hp trivial hadm (by decide) (by decide)
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hΩψ : ∀ R ∈ fundamentalSubgroups .F4 (modelUniv .F4 0 3 1 Nat.prime_three).D,
      R.map Ψ ∈ conjClass3 K := by
    intro R hRf
    obtain ⟨g, hg⟩ := hscT _ (rankOne_mem_fund (F := GaloisField 3 1) (k := f4Node 1)
      (by decide)) R hRf
    have h1 : (CurtisTits.rankOne (Steinberg.Adjoint.f4Datum (GaloisField 3 1)).rootGroup
        (f4Node 1)).map Ψ = U 1 := hblk (f4Node 1)
    have h2 := map_conjSub_eq Ψ g (CurtisTits.rankOne
      (Steinberg.Adjoint.f4Datum (GaloisField 3 1)).rootGroup (f4Node 1))
    rw [h1] at h2
    have h3 : R.map Ψ = conjSub (Ψ g) (U 1) := (congrArg (Subgroup.map Ψ) hg).trans h2
    rw [h3]
    exact hR.inClass.conjInvariant _ _ hU1
  obtain ⟨hsurj, -⟩ := Q3W.routeD_core3 (le_refl 1) hscT (finite_psp_rank 3) M hR.inClass hex hK
    hsingle hconn hR.cls hshape hP1 hO3 Ψ hker hΩψ
  have htop : (⨆ k, U k) = ⊤ := by
    rw [← hrange]
    exact MonoidHom.range_eq_top.mpr hsurj
  exact ⟨.F4, 0, 3, 1, hp, by norm_num, hadm,
    lieModel_of_top_center (CoreAssembly.center_eq_bot hnab) htop hlie⟩

@[expose] def ChainPiece3F4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), Q3W.RouteD3Setup K z →
      Q3W.LocalShapeC3 1 (CompData.model .PSp 3) (conjClass3 K) z →
      Q3W.LocalOddThreeFree3 (conjClass3 K) z →
      (∃ Kf : Fin 4 → Subgroup G, IsMemberFrame (conjClass3 K) Kf ∧
        ¬ Chain3.LayersCommute4 (conjClass3 K) Kf) → F4Chain3 K

theorem sp3F4NoncommInput_of_chain (hC6 : Q3Z.V6Collapse) (hC3 : Q3TW.B3Collapse)
    (h : ChainPiece3F4) : Chain3.Sp3F4NoncommInput :=
  fun G _ _ _ hnab K z hR hshape hO3 hfr =>
    oddLieType_of_f4Chain3 hC6 hC3 hnab hR hshape hO3 (h G hnab K z hR hshape hO3 hfr)

theorem sp3F4NoncommInput_proved
    (h : ChainPiece3F4) : Chain3.Sp3F4NoncommInput :=
  sp3F4NoncommInput_of_chain v6Collapse_proved Q3TW.b3Collapse_proved h

end CFSG.ClassicalInvolution.Q3.Q3V
