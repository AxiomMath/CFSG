module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Spine
public import CFSG.ClassicalInvolution.Q3.TL3S8Setup
public import CFSG.ClassicalInvolution.Q3.TL3DichThmA

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

namespace StdR

variable {r : ℕ} {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G} (h : StdR r R S t T)
include h

theorem isUniqueInvolution : IsUniqueInvolution (tightCore R) t :=
  h.datum.isUniqueInvolution_core

theorem normalizer_core_eq :
    Subgroup.normalizer (tightCore R : Set G) = Subgroup.centralizer ({t} : Set G) :=
  h.datum.normalizer_core_eq

theorem hypOmegaGen : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.datum.hypOmegaGen

theorem partIHypG : Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) := h.datum.partIHypG

theorem sylow_core : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) :=
  h.datum.sylow_core

theorem hTN : (T : Subgroup G) ≤ Subgroup.normalizer (tightCore R : Set G) := by
  rw [h.normalizer_core_eq]
  exact h.hTt

theorem mem_T : t ∈ (T : Subgroup G) := h.hST h.datum.mem

theorem setup194 : Q3T6.SD.Setup194Three (tightCore R) t :=
  h.datum.setup194 h.edgeless

theorem inf_core_eq :
    (T : Subgroup G) ⊓ tightCore R = (S : Subgroup R).map R.subtype := by
  have hsyl : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) := h.sylow_core
  rw [inf_comm]
  exact hsyl.2.2 _ inf_le_left (T.isPGroup'.to_le inf_le_right) (le_inf hsyl.1 h.hST)

theorem comm_of_mem_normalizer_inf_core {n : G}
    (hn : n ∈ Subgroup.normalizer (((T : Subgroup G) ⊓ tightCore R : Subgroup G) : Set G)) :
    n * t = t * n := by
  have htI : t ∈ (T : Subgroup G) ⊓ tightCore R := ⟨h.hST h.datum.mem, h.isUniqueInvolution.mem⟩
  have h1 : n * t * n⁻¹ ∈ (T : Subgroup G) ⊓ tightCore R :=
    (Subgroup.mem_normalizer_iff.mp hn t).mp htI
  have h2 : n * t * n⁻¹ * (n * t * n⁻¹) = 1 := by
    rw [show n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ by group, t_mul_t h.datum]
    group
  rcases h.isUniqueInvolution.unique _ h1.2 h2 with h3 | h3
  · exfalso
    apply h.isUniqueInvolution.ne_one
    calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
      _ = 1 := by rw [h3]; group
  · calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [h3]

theorem exists_w69 :
    ∃ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), W ≤ (T : Subgroup G) := by
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet h.hypOmegaGen T
  exact ⟨⨆ U ∈ η, U, ⟨η, ⟨T, hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2⟩

end StdR

theorem exists_stdR_of_sylowCase {r : ℕ} {R : Subgroup G} {S : Sylow 2 R} {t : G}
    (hd : TightDatum R S t) (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))))
    (he : Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)))
    (hn : ¬ TwoSubgroupsFourGenerated (genFittingFStar G)) {T : Subgroup G}
    (hT : IsSylow2Of T
      (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)))
    (hTG : IsSylow2Of T ⊤) :
    ∃ T' : Sylow 2 G, (T' : Subgroup G) = T ∧ StdR r R S t T' := by
  classical
  have h3 : 3 ≤ r := by
    obtain ⟨r', hr', ⟨e'⟩⟩ := hd.quat
    obtain ⟨e⟩ := hq
    have hc := Nat.card_congr (e.symm.toEquiv.trans e'.toEquiv)
    have hne : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
    have hne' : NeZero (2 ^ (r' - 2)) := ⟨by positivity⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, QuaternionGroup.card,
      QuaternionGroup.card] at hc
    have h2 : 2 ^ (r - 2) = 2 ^ (r' - 2) := by omega
    have h4 := Nat.pow_right_injective (le_refl 2) h2
    omega
  set S0 : Subgroup G := (S : Subgroup R).map R.subtype with hS0
  have d : OddByQuat R S0 t :=
    OddByQuat.of_quaternion S hd.quat hd.mem hd.order hd.cent hd.normal hd.twoGroup
  let T' : Sylow 2 G :=
    { toSubgroup := T
      isPGroup' := hTG.2.1
      is_maximal' := fun {Q} hQ hle => hTG.2.2 Q le_top hQ hle }
  have hS0N : S0 ≤ Subgroup.normalizer (S0 : Set G) := Subgroup.le_normalizer
  have hST : S0 ≤ T := by
    have hsup : IsPGroup 2 ↥(T ⊔ S0) :=
      hT.2.1.to_sup_of_normal_right' d.S_two hT.1
    have heq := hT.2.2 (T ⊔ S0) (sup_le hT.1 hS0N) hsup le_sup_left
    rw [← heq]
    exact le_sup_right
  have hTt : T ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (S0 : Set G) := hT.1 hx
    have hxt : x * t * x⁻¹ ∈ S0 := (Subgroup.mem_normalizer_iff.mp hxN t).mp d.t_mem
    have hord : orderOf (x * t * x⁻¹) = 2 := by
      have := (MulAut.conj x).orderOf_eq t
      rwa [MulAut.conj_apply, hd.order] at this
    have h2 : x * t * x⁻¹ = t := d.unique _ hxt hord
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [h2]
  exact ⟨T', rfl, ⟨hd, hq, h3, he, hn, hST, hTt⟩⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4
