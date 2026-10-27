module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262GF2Cls
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE7
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE8

import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangTorus
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295e2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcMax

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc
open CFSG.HardMathSupport.Timmesfeld.Steinberg
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem dotT_eq_triPairing {τ : Tag} (u : Fin τ.rank → ZMod 3) (x : Fin τ.rank → ℤ) :
    dotT u x = triPairing u x := by
  unfold dotT triPairing
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem triAct_zero {τ : Tag} (l : List (Fin τ.rank)) :
    triAct l (0 : Fin τ.rank → ZMod 3) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change triReflect i (triAct l 0) = 0
    rw [ih]
    funext j
    simp [triReflect]

theorem rootDiagUnit_thetaTupleG_eq_conj_of_triAct
    {τ : Tag} {L : Type} [Field L] {ζ : Lˣ}
    (hζ : ζ ^ 3 = 1) (ω : List ℕ) (u v : Fin τ.rank → ZMod 3)
    (hω : triAct (toFinWord3 ω) v = u) :
    rootDiagUnit τ (thetaTupleG τ ζ u) =
      canonicalRep (coxeterSystem τ) L ((coxeterSystem τ).wordProd (toFinWord3 ω)) *
        rootDiagUnit τ (thetaTupleG τ ζ v) *
        (canonicalRep (coxeterSystem τ) L ((coxeterSystem τ).wordProd (toFinWord3 ω)))⁻¹ := by
  set t : WeylGroup τ := (coxeterSystem τ).wordProd (toFinWord3 ω) with ht
  rw [rootDiagUnit_eq_conj_canonicalRep_iff]
  intro y
  rw [rootChar_thetaTupleG hζ, rootChar_thetaTupleG hζ]
  congr 1
  have htri' : triChar u (Multiplicative.ofAdd (t • y)) =
      triChar v (Multiplicative.ofAdd y) := by
    have h := triChar_triAct (toFinWord3 ω) v (t • y)
    rw [hω] at h
    have hcancel : t⁻¹ • (t • y) = y := by
      rw [← mul_smul, inv_mul_cancel, one_smul]
    rw [← ht] at h
    rwa [hcancel] at h
  have hpair : triPairing u (t • y) = triPairing v y := by
    simpa using Z3.ofAdd_eq_ofAdd_iff.1 htri'
  rw [dotT_eq_triPairing, dotT_eq_triPairing, hpair]

theorem gf2E7_cases {e : TauCeti.LieTypeIndex} (h : gf2E7 e) :
    ∃ q : TauCeti.PrimePower, e = .E7 q ∧ q.card = 2 := by
  cases e <;> simp only [gf2E7] at h
  · exact ⟨_, rfl, h⟩
  all_goals exact h.elim

theorem gf2E8_cases {e : TauCeti.LieTypeIndex} (h : gf2E8 e) :
    ∃ q : TauCeti.PrimePower, e = .E8 q ∧ q.card = 2 := by
  cases e <;> simp only [gf2E8] at h
  · exact ⟨_, rfl, h⟩
  all_goals exact h.elim

theorem exists_perfect_centralizer_E78
    {τ : Tag} (d : ℕ) (hτ : (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (w : WeylGroup τ) (hw : ∀ x : Fin τ.rank → ℤ, w • x = -x) (hmax : ExcMaxRank τ w)
    {reps : List (List ℕ)} {entries : List ℕ} (horb : orbitCheck3 τ reps entries = true)
    (hgood : ∀ ρ < reps.length, vec3 (τ := τ) (reps.getD ρ []) ≠ 0 →
      ∃ u : Fin τ.rank → ZMod 3, ExcGood τ u (vec3 (τ := τ) (reps.getD ρ [])))
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (hperf : Group.IsPerfect ↥(adjointGroup τ K))
    (helem : ∀ t : adjointGroup τ K, t ^ 3 = 1 →
      ∃ E : Subgroup ↥(adjointGroup τ K), t ∈ E ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ τ.rank)
    (x : adjointGroup τ K) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ P : Subgroup ↥(adjointGroup τ K), P ≤ Subgroup.centralizer {x} ∧ ⁅P, P⁆ = P ∧
      3 ∣ Nat.card P := by
  classical
  obtain ⟨L, _, _, _, _, S, Fr, hFr, hq2, hΦ, hn, hAlg, hρ, ⟨φ⟩, h3sub⟩ :=
    exists_exc_setup d hτ w K hK hperf
  obtain ⟨-, hconj⟩ := hmax L S Fr K hK ⟨φ⟩ hFr hq2 hΦ hn h3sub
  obtain ⟨ζ, hζ, hζ'⟩ := exists_cube_root_unity L (natCast_three_ne_zero_of_q_two S hq2)
  have hTor : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ 3 = 1) → rootDiagUnit τ a ∈ S.D.torus :=
    fun a ha => rootDiagUnit_mem_langTorus S Fr hFr w hΦ hn hw ha
  have hρ' : ∀ γ, IsRoot τ γ → S.ρ γ = -γ := fun γ hγ => (hρ γ hγ).trans (hw γ)
  have h2L : ((2 : ℕ) : L) = 0 := by
    have := S.hqpow.2
    rwa [hq2] at this
  haveI : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2L
  have hΓM : ∀ m ∈ S.D.model, ∀ y ∈ S.Γ, m * y * m⁻¹ ∈ S.Γ := by
    intro m hm y hy
    have h := Subgroup.normalizer_commutator_ge_left (H₁ := S.D.model) (H₂ := S.D.model) hm
    exact (Subgroup.mem_normalizer_iff.1 h y).1 hy
  let ψ : adjointGroup τ K →* ModGL τ L := S.Γ.subtype.comp φ.toMonoidHom
  have hψinj : Function.Injective ψ := (Subgroup.subtype_injective S.Γ).comp φ.injective
  obtain ⟨E, hxE, hEel, hEcard⟩ := helem x hx3
  let E' : Subgroup (ModGL τ L) := E.map ψ
  have hE'Γ : E' ≤ S.Γ := by
    intro y hy
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact (φ e).2
  have hE'el : IsElemAbelian 3 E' := hEel.map ψ
  have hE'card : 3 ^ τ.rank ≤ Nat.card E' := by
    change 3 ^ τ.rank ≤ Nat.card (E.map ψ)
    rw [Subgroup.card_map_of_injective hψinj, hEcard]
  obtain ⟨m, hmM, hmE⟩ := hconj E' hE'Γ hE'el hE'card
  have hxE' : ψ x ∈ E' := Subgroup.mem_map_of_mem ψ hxE
  have hmx : m * ψ x * m⁻¹ ∈ torus3 τ L := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom hxE'
    rw [hmE] at h
    simpa [MulAut.conj_apply] using h
  have hmx' : m * ψ x * m⁻¹ ∈ (psiG τ hζ).range := by
    rw [range_psiG hζ hζ']
    exact hmx
  obtain ⟨u, hu⟩ := hmx'
  have hdu : rootDiagUnit τ (thetaTupleG τ ζ (Multiplicative.toAdd u)) = m * ψ x * m⁻¹ := by
    simpa [psiG_apply] using hu
  have ha0 : Multiplicative.toAdd u ≠ 0 := by
    intro h0
    have hθ : thetaTupleG τ ζ (Multiplicative.toAdd u) = 1 := by
      funext i
      rw [h0]
      exact theta_zero' ζ
    have hd1 : rootDiagUnit τ (thetaTupleG τ ζ (Multiplicative.toAdd u)) = 1 := by
      rw [hθ, rootDiagUnit_one]
    have hψx1 : ψ x = 1 := by
      calc ψ x = m⁻¹ * (m * ψ x * m⁻¹) * m := by group
        _ = m⁻¹ * rootDiagUnit τ (thetaTupleG τ ζ (Multiplicative.toAdd u)) * m := by
              rw [hdu]
        _ = 1 := by rw [hd1]; group
    exact hx1 (hψinj (by rw [hψx1, map_one]))
  obtain ⟨ρ, hρlen, ω, hω⟩ := exists_word_of_orbitCheck3 horb (Multiplicative.toAdd u)
  set v : Fin τ.rank → ZMod 3 := vec3 (τ := τ) (reps.getD ρ []) with hv
  have hvne : v ≠ 0 := by
    intro hv0
    apply ha0
    rw [← hω, hv0]
    exact triAct_zero (toFinWord3 ω)
  obtain ⟨u', hgoodu'⟩ := hgood ρ hρlen hvne
  obtain ⟨J, hJsub, hJq, hJ3⟩ := hgoodu' L S hq2 hAlg hρ' ζ hζ hζ' hTor
  have hJle : J ≤ S.Γ ⊓ Subgroup.centralizer
      ({rootDiagUnit τ (thetaTupleG τ ζ u')} : Set (ModGL τ L)) ⊓
      Subgroup.centralizer ({rootDiagUnit τ (thetaTupleG τ ζ v)} : Set (ModGL τ L)) :=
    CFSG.Open.IsSubnormal.le hJsub
  have hJΓ : J ≤ S.Γ := hJle.trans (le_trans inf_le_left inf_le_left)
  have hJcentv : J ≤ Subgroup.centralizer
      ({rootDiagUnit τ (thetaTupleG τ ζ v)} : Set (ModGL τ L)) :=
    hJle.trans inf_le_right
  have hJperf : ⁅J, J⁆ = J := by
    haveI : Group.IsPerfect ↥J := ⟨hJq.1⟩
    exact Subgroup.commutator_eq_self
  have hJ3card : 3 ∣ Nat.card J :=
    hJ3.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥J))
  set t : WeylGroup τ := (coxeterSystem τ).wordProd (toFinWord3 ω) with ht
  have hduEq : rootDiagUnit τ (thetaTupleG τ ζ (Multiplicative.toAdd u)) =
      canonicalRep (coxeterSystem τ) L t * rootDiagUnit τ (thetaTupleG τ ζ v) *
        (canonicalRep (coxeterSystem τ) L t)⁻¹ := by
    rw [ht]
    exact rootDiagUnit_thetaTupleG_eq_conj_of_triAct (L := L) hζ ω
      (Multiplicative.toAdd u) v hω
  have hn_model : canonicalRep (coxeterSystem τ) L t ∈ S.D.model :=
    canonicalRep_mem_model S Fr w hΦ hn hw t
  let g : ModGL τ L := m⁻¹ * canonicalRep (coxeterSystem τ) L t
  have hgM : g ∈ S.D.model := Subgroup.mul_mem _ (Subgroup.inv_mem _ hmM) hn_model
  have hgd : g * rootDiagUnit τ (thetaTupleG τ ζ v) * g⁻¹ = ψ x := by
    simp only [g]
    calc m⁻¹ * canonicalRep (coxeterSystem τ) L t * rootDiagUnit τ (thetaTupleG τ ζ v) *
          (m⁻¹ * canonicalRep (coxeterSystem τ) L t)⁻¹
        = m⁻¹ * (canonicalRep (coxeterSystem τ) L t * rootDiagUnit τ (thetaTupleG τ ζ v) *
            (canonicalRep (coxeterSystem τ) L t)⁻¹) * m := by group
      _ = m⁻¹ * rootDiagUnit τ (thetaTupleG τ ζ (Multiplicative.toAdd u)) * m := by
            rw [← hduEq]
      _ = ψ x := by rw [hdu]; group
  let Jg : Subgroup (ModGL τ L) := J.map (MulAut.conj g).toMonoidHom
  have hJgΓ : Jg ≤ S.Γ := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hy
    exact hΓM g hgM j (hJΓ hj)
  have hJgcent : Jg ≤ Subgroup.centralizer ({ψ x} : Set (ModGL τ L)) := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hjd : j * rootDiagUnit τ (thetaTupleG τ ζ v) =
        rootDiagUnit τ (thetaTupleG τ ζ v) * j :=
      Subgroup.mem_centralizer_singleton_iff.1 (hJcentv hj)
    calc (g * j * g⁻¹) * ψ x
        = (g * j * g⁻¹) * (g * rootDiagUnit τ (thetaTupleG τ ζ v) * g⁻¹) := by rw [hgd]
      _ = g * (j * rootDiagUnit τ (thetaTupleG τ ζ v)) * g⁻¹ := by group
      _ = g * (rootDiagUnit τ (thetaTupleG τ ζ v) * j) * g⁻¹ := by rw [hjd]
      _ = (g * rootDiagUnit τ (thetaTupleG τ ζ v) * g⁻¹) * (g * j * g⁻¹) := by group
      _ = ψ x * (g * j * g⁻¹) := by rw [hgd]
  have hJgperf : ⁅Jg, Jg⁆ = Jg := by
    change ⁅J.map (MulAut.conj g).toMonoidHom, J.map (MulAut.conj g).toMonoidHom⁆ =
      J.map (MulAut.conj g).toMonoidHom
    rw [← Subgroup.map_commutator, hJperf]
  have hJgcard : Nat.card Jg = Nat.card J := by
    change Nat.card (J.map (MulAut.conj g).toMonoidHom) = Nat.card J
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hJgrange : Jg ≤ ψ.range := by
    intro y hy
    exact ⟨φ.symm ⟨y, hJgΓ hy⟩, by simp [ψ]⟩
  obtain ⟨P, hPcent, hPperf, hPcard⟩ :=
    exists_perfect_le_centralizer_of_injective ψ hψinj hJgrange hJgperf hJgcent
  refine ⟨P, hPcent, hPperf, ?_⟩
  rw [hPcard, hJgcard]
  exact hJ3card

theorem fixed_perfect_of_mulEquiv {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (φ : G ≃* H)
    (hinn : ∀ α : MulAut H, α ∈ (MulAut.conj : H →* MulAut H).range)
    (hZ : Subgroup.center H = ⊥)
    (hH : ∀ x : H, x ^ 3 = 1 → x ≠ 1 →
      ∃ P : Subgroup H, P ≤ Subgroup.centralizer ({x} : Set H) ∧ ⁅P, P⁆ = P ∧
        3 ∣ Nat.card P) :
    ∀ a : MulAut G, a ≠ 1 → a ^ 3 = 1 →
      ∃ P : Subgroup G, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  intro a ha1 ha3
  obtain ⟨g, hg⟩ := mulAut_mem_range_conj_of_equiv φ hinn a
  have hg1 : g ≠ 1 := by
    intro h
    apply ha1
    rw [← hg, h, map_one]
  have hg3 : g ^ 3 = 1 := by
    apply conj_injective_of_equiv φ hZ
    rw [map_pow, hg, ha3, map_one]
  obtain ⟨P, hPcent, hPperf, hP3⟩ := hH (φ g)
    (by rw [← map_pow, hg3, map_one])
    (fun h => hg1 (φ.injective (h.trans (map_one φ).symm)))
  refine ⟨P.map φ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [show fixSubgroup a = Subgroup.centralizer ({g} : Set G) from by
      rw [← hg, CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj]]
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hpcent : p * φ g = φ g * p :=
      Subgroup.mem_centralizer_singleton_iff.1 (hPcent hp)
    rw [← MulEquiv.symm_apply_apply φ g]
    simpa using congrArg φ.symm hpcent
  · rw [← Subgroup.map_commutator, hPperf]
  · rw [Subgroup.card_map_of_injective φ.symm.injective]
    exact hP3

theorem fixed_perfect_gf2E7
    (h7 : ∀ ρ < e7ThreeReps.length, vec3 (τ := .E7) (e7ThreeReps.getD ρ []) ≠ 0 →
      ∃ u : Fin Tag.E7.rank → ZMod 3, ExcGood .E7 u (vec3 (τ := .E7) (e7ThreeReps.getD ρ []))) :
    ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
      gf2E7 d.1 → ∀ a : MulAut (TauCeti.CFSGIndex.lie d).Group, a ≠ 1 → a ^ 3 = 1 →
        ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧
          3 ∣ Nat.card P := by
  intro d _ hd a ha1 ha3
  obtain ⟨e, hv⟩ := d
  change gf2E7 e at hd
  obtain ⟨q, he, hq⟩ := gf2E7_cases hd
  subst e
  obtain ⟨K, _, _, hK, -, ⟨φ⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
  have hK2 : Nat.card K = 2 := hK.trans hq
  have hperf : Group.IsPerfect ↥(adjointGroup Tag.E7 K) :=
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K).1
  have helem : ∀ t : adjointGroup Tag.E7 K, t ^ 3 = 1 →
      ∃ E : Subgroup ↥(adjointGroup Tag.E7 K), t ∈ E ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ Tag.E7.rank :=
    fun t ht =>
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295e.exists_elemAbelian_E7_two
        hK2 t ht
  haveI : Finite (ModGL Tag.E7 K) := finite_modGL
  exact fixed_perfect_of_mulEquiv φ
    (mulAut_mem_range_conj_E78 (Or.inl rfl) K hK2)
    center_adjointGroup_eq_bot
    (fun x hx3 hx1 =>
      exists_perfect_centralizer_E78 2 (Or.inl ⟨rfl, rfl⟩) e7Neg e7Neg_smul exc_maxRank_E7
        e7ThreeOrbit_check h7 K hK2 hperf helem x hx3 hx1)
    a ha1 ha3

theorem good3On_gf2E7
    (hPL : KD264PL 3)
    (h7 : ∀ ρ < e7ThreeReps.length, vec3 (τ := .E7) (e7ThreeReps.getD ρ []) ≠ 0 →
      ∃ u : Fin Tag.E7.rank → ZMod 3, ExcGood .E7 u (vec3 (τ := .E7) (e7ThreeReps.getD ρ []))) :
    Good3On gf2E7 :=
  good3On_of_fixed_perfect hPL (fun e he => by
    cases e <;> simp only [gf2E7] at he
    · exact three_ne_characteristic_of_card_two (TauCeti.LieTypeIndex.characteristic_E7 _) he
    all_goals exact he.elim)
    (by
      intro d _ hd
      exact fixed_perfect_gf2E7 h7 d hd)

theorem fixed_perfect_gf2E8
    (h8 : ∀ ρ < e8ThreeReps.length, vec3 (τ := .E8) (e8ThreeReps.getD ρ []) ≠ 0 →
      ∃ u : Fin Tag.E8.rank → ZMod 3, ExcGood .E8 u (vec3 (τ := .E8) (e8ThreeReps.getD ρ []))) :
    ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
      gf2E8 d.1 → ∀ a : MulAut (TauCeti.CFSGIndex.lie d).Group, a ≠ 1 → a ^ 3 = 1 →
        ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧
          3 ∣ Nat.card P := by
  intro d _ hd a ha1 ha3
  obtain ⟨e, hv⟩ := d
  change gf2E8 e at hd
  obtain ⟨q, he, hq⟩ := gf2E8_cases hd
  subst e
  obtain ⟨K, _, _, hK, -, ⟨φ⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  have hK2 : Nat.card K = 2 := hK.trans hq
  have hperf : Group.IsPerfect ↥(adjointGroup Tag.E8 K) :=
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K).1
  have helem : ∀ t : adjointGroup Tag.E8 K, t ^ 3 = 1 →
      ∃ E : Subgroup ↥(adjointGroup Tag.E8 K), t ∈ E ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ Tag.E8.rank :=
    fun t ht =>
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295e.exists_elemAbelian_E8_two
        hK2 t ht
  haveI : Finite (ModGL Tag.E8 K) := finite_modGL
  exact fixed_perfect_of_mulEquiv φ
    (mulAut_mem_range_conj_E78 (Or.inr rfl) K hK2)
    center_adjointGroup_eq_bot
    (fun x hx3 hx1 =>
      exists_perfect_centralizer_E78 1 (Or.inr ⟨rfl, rfl⟩) e8Neg e8Neg_smul exc_maxRank_E8
        e8ThreeOrbit_check h8 K hK2 hperf helem x hx3 hx1)
    a ha1 ha3

theorem good3On_gf2E8
    (hPL : KD264PL 3)
    (h8 : ∀ ρ < e8ThreeReps.length, vec3 (τ := .E8) (e8ThreeReps.getD ρ []) ≠ 0 →
      ∃ u : Fin Tag.E8.rank → ZMod 3, ExcGood .E8 u (vec3 (τ := .E8) (e8ThreeReps.getD ρ []))) :
    Good3On gf2E8 :=
  good3On_of_fixed_perfect hPL (fun e he => by
    cases e <;> simp only [gf2E8] at he
    · exact three_ne_characteristic_of_card_two (TauCeti.LieTypeIndex.characteristic_E8 _) he
    all_goals exact he.elim)
    (by
      intro d _ hd
      exact fixed_perfect_gf2E8 h8 d hd)

end CFSG.LocalAnalysis.GLTheoremA.S262

end
