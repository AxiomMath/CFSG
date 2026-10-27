module

public import CFSG.ClassicalInvolution.Q3.Q3TLTInner
public import CFSG.ClassicalInvolution.Q3.TL3GlueCoc
public import CFSG.ClassicalInvolution.Q3.TL3S8Std

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem oddCoreOf_tightCore_le (R : Subgroup G) : oddCoreOf (tightCore R) ≤ oddCoreImg R := by
  have hKR : oddCoreOf (tightCore R) ≤ R :=
    (Subgroup.map_subtype_le _).trans (tightCore_le R)
  have hnorm : R ≤ Subgroup.normalizer ((oddCoreOf (tightCore R) : Subgroup G) : Set G) := by
    refine GlueLie.le_normalizer_of_forall_conj_mem fun r hr o ho => ?_
    have hrK : r ∈ Subgroup.normalizer ((tightCore R : Subgroup G) : Set G) :=
      mem_normalizer_of_conjSub_eq
        (conjSub_tightCore_of_mem_normalizer (Subgroup.le_normalizer hr))
    exact conj_mem_oddCoreImg hrK ho
  have hodd : Odd (Nat.card (oddCoreOf (tightCore R))) := oddCoreOf_odd_natCard _
  exact Balance.le_oddCoreIn_of_normalizes hKR hnorm hodd

theorem TightDatum.mem_ker_act_of_sylow (hd : TightDatum R S t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({t} : Set G))
    (h : ∀ s ∈ (S : Subgroup R).map R.subtype, ⁅g, s⁆ ∈ oddCoreImg R) :
    (⟨g, hg⟩ : Subgroup.centralizer ({t} : Set G)) ∈ hd.act.ker := by
  have d : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S hd.quat hd.mem hd.order hd.cent hd.normal hd.twoGroup
  rw [hd.mem_ker_act_iff]
  intro r hr
  obtain ⟨s, hs, o, ho, rfl⟩ := d.exists_mul_S_O r hr
  have hgN : g ∈ Subgroup.normalizer (R : Set G) := hd.le_normalizer hg
  have hsR : s ∈ R := d.S_le hs
  have h1 : g * o * g⁻¹ * o⁻¹ ∈ oddCoreImg R :=
    (oddCoreImg R).mul_mem (conj_mem_oddCoreImg hgN ho) ((oddCoreImg R).inv_mem ho)
  have h2 : s * (g * o * g⁻¹ * o⁻¹) * s⁻¹ ∈ oddCoreImg R :=
    conj_mem_oddCoreImg (Subgroup.le_normalizer hsR) h1
  have e : ⁅g, s * o⁆ = ⁅g, s⁆ * (s * (g * o * g⁻¹ * o⁻¹) * s⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (oddCoreImg R).mul_mem (h s hs) h2

theorem TightDatum.edge_sylow (hd : TightDatum R S t) {J : Subgroup G}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : G}
    (hu : IsUniqueInvolution J u) :
    u ≠ t ∧ ∃ T : Subgroup G, IsSylow2In T J ∧ u ∈ T ∧
      T ≤ Subgroup.centralizer ({t} : Set G) ∧ ⁅T, tightCore R⁆ ≤ oddCoreOf (tightCore R) := by
  have hΩ := hd.hypOmegaGen
  have huniq := hd.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨hJΩ, hJK, T, hT, hTJ, hTN⟩ := hJ
  have hTs : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hT
  have huT : u ∈ T := mem_of_isPGroup hu hTJ hTs.2.1 (by omega)
  have hTc : T ≤ Subgroup.centralizer ({t} : Set G) :=
    Sec6Gen.le_centralizer_of_le_normalizer' huniq hTN
  have hnt : J ∉ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rw [hd.twinSet_eq]
    exact hJK
  have hut : u ≠ t := by
    rintro rfl
    exact hnt ⟨hJΩ, u, huniq, hu⟩
  refine ⟨hut, T, hTs, huT, hTc, ?_⟩
  have hV : IsSylow2In T (J ⊓ Subgroup.centralizer ({t} : Set G)) :=
    ⟨le_inf hTJ hTc, hTs.2.1, fun V' hV'P hV'2 hle =>
      hTs.2.2 V' (hV'P.trans inf_le_left) hV'2 hle⟩
  rcases Sec6Gen.l6_2Gen G _ hΩ _ hK t huniq J hJΩ hnt u hu T hV huT with
    ⟨hT1, -⟩ | ⟨hT1, -⟩ | ⟨hTU, -⟩ | ⟨-, hc⟩
  · exfalso
    have : Nat.card T = 2 := by
      rw [hT1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hu.sq) hu.ne_one]
    omega
  · exfalso
    have : Nat.card T = 2 := by
      rw [hT1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hu.sq) hu.ne_one]
    omega
  · exfalso
    obtain ⟨T', -, J', hJ', hT'J', hTT', -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hTU
    have e1 := Sec6Gen.natCard_isSylow2In_eq hΩ hJ' hJΩ hT'J' hTs
    have h0 : 0 < Nat.card T := Nat.card_pos
    omega
  · exact hc

theorem TightDatum.edge_involution (hd : TightDatum R S t) {J : Subgroup G}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : G}
    (hu : IsUniqueInvolution J u) :
    u ≠ t ∧ u * u = 1 ∧ ∃ (hut : u ∈ Subgroup.centralizer ({t} : Set G)),
      t ∈ Subgroup.centralizer ({u} : Set G) ∧
      (⟨u, hut⟩ : Subgroup.centralizer ({t} : Set G)) ∈ hd.act.ker ∧
      ∃ T : Subgroup G, IsSylow2In T J ∧ u ∈ T ∧
        ∃ hTc : T ≤ Subgroup.centralizer ({t} : Set G),
          ∀ τ (hτ : τ ∈ T), (⟨τ, hTc hτ⟩ : Subgroup.centralizer ({t} : Set G)) ∈ hd.act.ker := by
  obtain ⟨hut, T, hTs, huT, hTc, hcomm⟩ := hd.edge_sylow hJ hu
  have hS0 : (S : Subgroup R).map R.subtype ≤ tightCore R := hd.sylow_core.1
  have hT : ∀ τ (hτ : τ ∈ T), (⟨τ, hTc hτ⟩ : Subgroup.centralizer ({t} : Set G)) ∈ hd.act.ker :=
    fun τ hτ => hd.mem_ker_act_of_sylow (hTc hτ) fun s hs =>
      oddCoreOf_tightCore_le R (hcomm (Subgroup.commutator_mem_commutator hτ (hS0 hs)))
  have hutc : u ∈ Subgroup.centralizer ({t} : Set G) := hTc huT
  refine ⟨hut, hu.sq, hutc, ?_, hT u huT, T, hTs, huT, hTc, hT⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_singleton_iff.mp hutc).symm

theorem TightDatum.conj (hd : TightDatum R S t) (g : G) :
    ∃ S' : Sylow 2 ↥(conjSub g R), TightDatum (conjSub g R) S' (g * t * g⁻¹) ∧
      Nonempty ((S' : Subgroup ↥(conjSub g R)) ≃* (S : Subgroup R)) := by
  classical
  set σ : G →* G := (MulAut.conj g).toMonoidHom with hσ
  have hσinj : Function.Injective σ := (MulAut.conj g).injective
  set e : ↥R ≃* ↥(conjSub g R) := R.equivMapOfInjective σ hσinj with he
  set S' : Sylow 2 ↥(conjSub g R) := S.mapSurjective (f := e.toMonoidHom) e.surjective with hS'
  have hS'eq : (S' : Subgroup ↥(conjSub g R)) = (S : Subgroup R).map e.toMonoidHom := rfl
  have eS : (S : Subgroup R) ≃* (S' : Subgroup ↥(conjSub g R)) := by
    rw [hS'eq]
    exact (S : Subgroup R).equivMapOfInjective e.toMonoidHom e.injective
  have hσt : σ t = g * t * g⁻¹ := rfl
  have hcent : conjSub g R ≤ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : r * t = t * r := Subgroup.mem_centralizer_singleton_iff.mp (hd.cent hr)
    show g * r * g⁻¹ * (g * t * g⁻¹) = g * t * g⁻¹ * (g * r * g⁻¹)
    calc g * r * g⁻¹ * (g * t * g⁻¹) = g * (r * t) * g⁻¹ := by group
      _ = g * (t * r) * g⁻¹ := by rw [h1]
      _ = g * t * g⁻¹ * (g * r * g⁻¹) := by group
  refine ⟨S', ⟨?_, ?_, ?_, hcent, ?_, ?_⟩, ⟨eS.symm⟩⟩
  · obtain ⟨r, hr, ⟨e'⟩⟩ := hd.quat
    exact ⟨r, hr, ⟨eS.symm.trans e'⟩⟩
  · obtain ⟨s, hs, rfl⟩ := hd.mem
    refine ⟨e s, ⟨s, hs, rfl⟩, rfl⟩
  · rw [← hσt]
    exact (orderOf_injective σ hσinj t).trans hd.order
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer hcent).mpr fun c hc => ?_
    have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : c * (g * t * g⁻¹) = (g * t * g⁻¹) * c :=
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
      calc g⁻¹ * c * g * t = g⁻¹ * (c * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * c) * g := by rw [h1]
        _ = t * (g⁻¹ * c * g) := by group
    have hN := hd.le_normalizer hc'
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro x
    rw [mem_conjSub_iff, mem_conjSub_iff]
    have := hN (g⁻¹ * x * g)
    have e1 : g⁻¹ * (c * x * c⁻¹) * g = (g⁻¹ * c * g) * (g⁻¹ * x * g) * (g⁻¹ * c * g)⁻¹ := by
      group
    rw [e1]
    exact this
  · have hO : (classicalInvolutionOddCore ↥R).map e.toMonoidHom =
        classicalInvolutionOddCore ↥(conjSub g R) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact hd.twoGroup.of_equiv (QuotientGroup.congr _ _ e hO)

end CFSG.ClassicalInvolution.Q3
