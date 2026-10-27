module

public import CFSG.ClassicalInvolution.Q3.TL4E3Odd

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.conjSub_orbGen_of_cent (hF : E3Frame n R S t J u) {x : Y}
    (hx : x ∈ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J)
    (hst : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hcent : ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
      ⁅x * t * x⁻¹, y⁆ ∈
        oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J))
    (hex : ¬ ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
      ⁅x * (u * t) * x⁻¹, y⁆ ∈
        oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J)) :
    conjSub x (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J) =
      E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set π := orbOf (TC.nbrAdj Ω) (tightCore R) J with hπdef
  set P := E3.orbGen Ω (tightCore R) J with hPdef
  set s := x * t * x⁻¹ with hsdef
  set J₁ := conjSub x (tightCore R) with hJ₁def
  have hFam := hF.graphFam
  have hd := hF.large.datum
  have hΩG := hd.hypOmegaGen
  have hR : TypeRFam 3 Ω := TightLargeHypR.typeRFam hF.large
  have hc : ConjInvariant Ω := hΩG.conjInvariant
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hπ : π ∈ maxOrbs (TC.nbrAdj Ω) (tightCore R) := hF.maxAdj.2
  have hπK : ∀ N ∈ π, N ∈ omegaNbr Ω (tightCore R) := fun N hN =>
    (adj_of_mem_isMaxOrb hFam hπ hN).2
  have hJ₁Ω : J₁ ∈ Ω := hc x _ hK₀Ω
  have hsJ₁ : IsUniqueInvolution J₁ s := hd.isUniqueInvolution_core.conj x
  have hCt : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), conjSub c P = P := fun c hc' =>
    hF.conjSub_orbGen_core hc'
  have hNO : ∀ {c : Y}, c ∈ Subgroup.centralizer ({t} : Set Y) → ∀ y ∈ oddCoreOf P,
      c * y * c⁻¹ ∈ oddCoreOf P := fun hc' _ hy =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (mem_normalizer_iff_conjSub_eq.mpr (hCt _ hc')) hy
  have hsC : s ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hst
  have huC : u ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hF.t_mem_centralizer).symm
  have hPC : P ≤ Subgroup.centralizer ({t} : Set Y) := by
    refine iSup₂_le fun L hL => ?_
    obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩG (hπK L hL).1
    exact edge_le_centralizer_of_alpha hd (hπK L hL) hv (hF.alpha L (hπK L hL) v hv)
  have hOC : oddCoreOf P ≤ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) :=
    Asc77.T8.oddCoreOf_le_oddCoreOf_of_normalized hPC hCt
  have hON : ∀ L ∈ π, oddCoreOf P ≤ Subgroup.normalizer (L : Set Y) := by
    intro L hL
    obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩG (hπK L hL).1
    have h1 := E3.oddCore_le_centralizer_of_alpha (hF.alpha L (hπK L hL) v hv) (ne_one_of_datum hd)
    exact (hOC.trans h1).trans (hR.tight L (hπK L hL).1 v hv)
  have hs2 : IsPGroup 2 (Subgroup.zpowers s) :=
    isPGroup_zpowers_of_mul_self_eq_one hsJ₁.sq hsJ₁.ne_one
  have hsyl : ∀ L ∈ π, ∃ Q : Subgroup Y, IsSylow2In Q L ∧
      Q ≤ Subgroup.centralizer ({s} : Set Y) := by
    intro L hL
    refine E3.exists_sylow_le_centralizer_of_modOdd (oddCoreOf_odd_natCard P) (hON L hL) hs2
      (hNO hsC) fun l hl => ?_
    have h1 := hcent l (le_iSup₂ (f := fun N (_ : N ∈ π) => N) L hL hl)
    rwa [commutatorElement_def] at h1
  have hCs : Subgroup.centralizer ({s} : Set Y) ≤ Subgroup.normalizer (J₁ : Set Y) :=
    hR.tight J₁ hJ₁Ω s hsJ₁
  have hJ₁π : J₁ ∉ π := by
    intro hJ₁
    obtain ⟨p, hp, hpJ⟩ := hF.lemma1710.trans J (mem_orbOf_self _ _) J₁ hJ₁
    have hps : p * u * p⁻¹ = s := by
      have h1 := hF.inv.conj p
      rw [hpJ] at h1
      exact h1.eq hsJ₁
    have hpP : p ∈ P := hp
    have hPO : ∀ {q : Y}, q ∈ P → ∀ y ∈ oddCoreOf P, q * y * q⁻¹ ∈ oddCoreOf P := fun hq _ hy =>
      mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hq) hy
    have hu : ∀ y ∈ P, ⁅u, y⁆ ∈ oddCoreOf P := by
      intro y hy
      have h1 := hcent (p * y * p⁻¹) (P.mul_mem (P.mul_mem hpP hy) (P.inv_mem hpP))
      have h2 := hPO (P.inv_mem hpP) _ h1
      convert h2 using 1
      rw [← hps]
      simp only [commutatorElement_def]
      group
    apply hex
    intro y hy
    have hxu : x * u * x⁻¹ = u := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hF.nbrGen_le_centralizer hx)
      calc x * u * x⁻¹ = u * x * x⁻¹ := by rw [← h1]
        _ = u := by group
    have h1 := (oddCoreOf P).mul_mem (hNO huC _ (hcent y hy)) (hu y hy)
    convert h1 using 1
    calc ⁅x * (u * t) * x⁻¹, y⁆ = ⁅(x * u * x⁻¹) * s, y⁆ := by rw [hsdef]; group
      _ = u * ⁅s, y⁆ * u⁻¹ * ⁅u, y⁆ := by
        rw [hxu]
        simp only [commutatorElement_def]
        group
  have hβ : J₁ ∈ PhilipHall.Frame.betaOf (TC.nbrAdj Ω) Ω π := by
    refine ⟨hJ₁Ω, fun L hL => ⟨hJ₁Ω, (hπK L hL).1, fun h => hJ₁π (h ▸ hL), ?_⟩⟩
    obtain ⟨Q, hQ, hQs⟩ := hsyl L hL
    exact ⟨Q, mem_RSet_of_isSylow2In (hπK L hL).1 hQ, hQ.1, hQs.trans hCs⟩
  have h1 : π ∈ maxOrbs (TC.nbrAdj Ω) J₁ :=
    (PhilipHall.Frame.mem_betaOf_iff hFam hK₀Ω hπ).mp hβ
  have h2 : conjSub x '' π ∈ maxOrbs (TC.nbrAdj Ω) J₁ := isMaxOrb_conj hFam hπ x
  have h3 : conjSub x '' π = π := maxOrb_unique hFam hJ₁Ω h2 h1
  have h4 := E3.orbGen_conj hc hK₀Ω (J := J) x
  have h5 := orbOf_conj hFam.graph (tightCore R) J x
  rw [← h4]
  show (⨆ M ∈ orbOf (TC.nbrAdj Ω) (conjSub x (tightCore R)) (conjSub x J), M) = ⨆ M ∈ π, M
  rw [h5, h3]

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
