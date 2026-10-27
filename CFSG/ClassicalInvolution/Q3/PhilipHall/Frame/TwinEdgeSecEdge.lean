module

public import CFSG.ClassicalInvolution.Q3.TL3GlueEdge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmA

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem edge_sylow (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (hut : u ≠ t) :
    ∃ T : Subgroup Y, IsSylow2In T J ∧ u ∈ T ∧
      T ≤ Subgroup.centralizer ({t} : Set Y) ∧ ⁅T, tightCore R⁆ ≤ oddCoreOf (tightCore R) := by
  have huniq := Q8Datum.isUniqueInvolution_core hd
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨hJΩ, hJK, T, hT, hTJ, hTN⟩ := hJ
  have hTs : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hT
  have huT : u ∈ T := mem_of_isPGroup hu hTJ hTs.2.1 (by omega)
  have hTc : T ≤ Subgroup.centralizer ({t} : Set Y) :=
    Sec6Gen.le_centralizer_of_le_normalizer' huniq hTN
  have hnt : J ∉ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rintro ⟨-, z, hzK, hzJ⟩
    exact hut ((hzJ.eq hu).symm.trans (hzK.eq huniq))
  refine ⟨T, hTs, huT, hTc, ?_⟩
  have hV : IsSylow2In T (J ⊓ Subgroup.centralizer ({t} : Set Y)) :=
    ⟨le_inf hTJ hTc, hTs.2.1, fun V' hV'P hV'2 hle =>
      hTs.2.2 V' (hV'P.trans inf_le_left) hV'2 hle⟩
  rcases Sec6Gen.l6_2Gen Y _ hΩ _ hK t huniq J hJΩ hnt u hu T hV huT with
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


theorem mem_centralizerModOdd_of_commutator {u : Y} (hu2 : u * u = 1)
    (hcomm : ∀ r ∈ R, ⁅u, r⁆ ∈ oddCoreImg R) : u ∈ centralizerModOdd ⊤ R := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have h1 : ∀ r ∈ R, u * r * u⁻¹ ∈ R := fun r hr => by
    have e : u * r * u⁻¹ = ⁅u, r⁆ * r := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact R.mul_mem (oddCoreImg_le R (hcomm r hr)) hr
  have hN : u ∈ Subgroup.normalizer (R : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨h1 h, fun hh => ?_⟩
    have := h1 _ hh
    have e : u * (u * h * u⁻¹) * u⁻¹ = h := by
      rw [hu']
      calc u * (u * h * u) * u = (u * u) * h * (u * u) := by group
        _ = h := by rw [hu2]; group
    rwa [e] at this
  refine ⟨trivial, hN, ?_, hcomm⟩
  rw [Subgroup.mem_normalizer_iff]
  intro o
  constructor
  · intro ho
    exact conj_mem_oddCoreImg hN ho
  · intro ho
    have h := conj_mem_oddCoreImg (Subgroup.inv_mem _ hN) ho
    have e : u⁻¹ * (u * o * u⁻¹) * u⁻¹⁻¹ = o := by group
    rwa [e] at h

theorem edge_involution (hd : Q8TwinDatum R S t) (hRc : tightCore R = R)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (hut : u ≠ t) :
    u * u = 1 ∧ t ∈ Subgroup.centralizer ({u} : Set Y) ∧ u ∈ centralizerModOdd ⊤ R := by
  obtain ⟨T, -, huT, hTc, hcomm⟩ := edge_sylow hd hΩ hJ hu hut
  have htu : t ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hTc huT)).symm
  refine ⟨hu.sq, htu, mem_centralizerModOdd_of_commutator hu.sq fun r hr => ?_⟩
  have hr' : r ∈ tightCore R := by rw [hRc]; exact hr
  exact oddCoreOf_tightCore_le R (hcomm (Subgroup.commutator_mem_commutator huT hr'))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
