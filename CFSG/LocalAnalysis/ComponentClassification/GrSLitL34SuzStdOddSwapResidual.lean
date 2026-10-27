module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Layer0
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Res
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdStandard
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HLambda
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.SylowAutomorphism

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {t : G}

theorem le_of_isPerfect_of_le_normalizer_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) {X : Subgroup G} (hX : Group.IsPerfect ↥X)
    (hXN : X ≤ normalizer (A : Set G)) : X ≤ A := by
  have hAperf : Group.IsPerfect ↥A := hS.standard.1.1
  have hAcomm : commutator A = ⊤ := hAperf.commutator_eq_top
  let I : Subgroup (MulAut (↥A ⧸ center ↥A)) :=
    (MulAut.conj : (↥A ⧸ center ↥A) →* MulAut (↥A ⧸ center ↥A)).range
  have hIindex : I.index ∣ 2 :=
    CFSG.EvenSporadicStandard.TwoSuz.index_dvd_two_of_isSporadic_suz hS.suz
  have hIcomm : IsMulCommutative (MulAut (↥A ⧸ center ↥A) ⧸ I) := by
    have hcard : Nat.card (MulAut (↥A ⧸ center ↥A) ⧸ I) ∣ 2 := by
      rw [← Subgroup.index_eq_card]
      exact hIindex
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (isCyclic_of_card_dvd_prime hcard).isMulCommutative
  have hcomm_le_I : _root_.commutator (MulAut (↥A ⧸ center ↥A)) ≤ I :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hIcomm
  have hX_le_AC : X ≤ A ⊔ centralizer (A : Set G) := by
    intro x hx
    have hxN : x ∈ normalizer (A : Set G) := hXN hx
    rw [← CFSG.EvenSporadicStandard.normalizerAction_mem_range_conj_iff hAcomm ⟨x, hxN⟩]
    let φ : ↥X →* MulAut (↥A ⧸ center ↥A) :=
      (CFSG.EvenSporadicStandard.normalizerAction A).comp (Subgroup.inclusion hXN)
    have hφperf : Group.IsPerfect φ.range := Group.IsPerfect.range (f := φ)
    have hφrange_le_I : φ.range ≤ I := by
      calc φ.range = ⁅φ.range, φ.range⁆ := (Subgroup.isPerfect_iff.mp hφperf).symm
        _ ≤ _root_.commutator (MulAut (↥A ⧸ center ↥A)) :=
          Subgroup.commutator_mono le_top le_top
        _ ≤ I := hcomm_le_I
    have hφx : φ ⟨x, hx⟩ = CFSG.EvenSporadicStandard.normalizerAction A ⟨x, hxN⟩ := rfl
    rw [← hφx]
    exact hφrange_le_I ⟨⟨x, hx⟩, rfl⟩
  have hCsolv : Group.IsSolvable ↥(centralizer (A : Set G)) := by
    apply CFSG.EvenSporadicStandard.Solomon78.isSolvable_of_cyclic_sylow_two
    intro P
    have hP : Nat.card P = 2 := hS.card_sylow P
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_card_dvd_prime (by rw [hP])
  have hCN : centralizer (A : Set G) ≤ normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer _
  exact CFSG.GH74.GLS.Stage2.Bender.Thm2.L102.perfect_le_of_le_sup_solvable
    (Subgroup.isPerfect_iff.mp hX) hCsolv hCN hX_le_AC

theorem map_conj_centralizerResidual_eq_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) {a d : G} (hat : a * t * a⁻¹ = d * t) (had : a * d * a⁻¹ = d) :
    (HarrisLit.centralizerResidual A d).map (MulAut.conj a).toMonoidHom =
      HarrisLit.centralizerResidual A d := by
  set L : Subgroup G := HarrisLit.centralizerResidual A d with hL
  have hLperf : Group.IsPerfect ↥L := by
    rw [hL, HarrisLit.centralizerResidual]
    exact HarrisLit.isPerfect_perfectResidual_map _
  have hLle : L ≤ A ⊓ centralizer ({d} : Set G) := by
    rw [hL]
    exact HarrisLit.centralizerResidual_le
  have hLA : L ≤ A := hLle.trans inf_le_left
  have hLd : L ≤ centralizer ({d} : Set G) := hLle.trans inf_le_right
  have hLt : L ≤ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp hS.t_mem x (hLA hx)
  have hLaperf : Group.IsPerfect ↥(L.map (MulAut.conj a).toMonoidHom) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hLperf]
  have hconj_d : ∀ y ∈ L, (MulAut.conj a) y * d = d * (MulAut.conj a) y := by
    intro y hy
    have hyd : y * d = d * y := mem_centralizer_singleton_iff.mp (hLd hy)
    calc (MulAut.conj a) y * d = (a * y * a⁻¹) * d := by rw [MulAut.conj_apply]
      _ = (a * y * a⁻¹) * (a * d * a⁻¹) := by rw [had]
      _ = a * y * d * a⁻¹ := by group
      _ = a * (y * d) * a⁻¹ := by group
      _ = a * (d * y) * a⁻¹ := by rw [hyd]
      _ = a * d * y * a⁻¹ := by group
      _ = (a * d * a⁻¹) * (a * y * a⁻¹) := by group
      _ = d * (a * y * a⁻¹) := by rw [had]
      _ = d * (MulAut.conj a) y := by rw [MulAut.conj_apply]
  have hconj_dt : ∀ y ∈ L, (MulAut.conj a) y * (d * t) = (d * t) * (MulAut.conj a) y := by
    intro y hy
    have hyt : y * t = t * y := mem_centralizer_singleton_iff.mp (hLt hy)
    calc (MulAut.conj a) y * (d * t) = (a * y * a⁻¹) * (d * t) := by rw [MulAut.conj_apply]
      _ = (a * y * a⁻¹) * (a * t * a⁻¹) := by rw [hat]
      _ = a * y * t * a⁻¹ := by group
      _ = a * (y * t) * a⁻¹ := by group
      _ = a * (t * y) * a⁻¹ := by rw [hyt]
      _ = a * t * y * a⁻¹ := by group
      _ = (a * t * a⁻¹) * (a * y * a⁻¹) := by group
      _ = (d * t) * (a * y * a⁻¹) := by rw [hat]
      _ = (d * t) * (MulAut.conj a) y := by rw [MulAut.conj_apply]
  have hLa_le_Ct : L.map (MulAut.conj a).toMonoidHom ≤ centralizer ({t} : Set G) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_centralizer_singleton_iff]
    have hxd' : (MulAut.conj a) y * d⁻¹ = d⁻¹ * (MulAut.conj a) y :=
      Commute.inv_right (show Commute ((MulAut.conj a) y) d from hconj_d y hy)
    calc (MulAut.conj a) y * t = (MulAut.conj a) y * (d⁻¹ * (d * t)) := by
          rw [inv_mul_cancel_left]
      _ = ((MulAut.conj a) y * d⁻¹) * (d * t) := by group
      _ = (d⁻¹ * (MulAut.conj a) y) * (d * t) := by rw [hxd']
      _ = d⁻¹ * ((MulAut.conj a) y * (d * t)) := by group
      _ = d⁻¹ * ((d * t) * (MulAut.conj a) y) := by rw [hconj_dt y hy]
      _ = (d⁻¹ * (d * t)) * (MulAut.conj a) y := by group
      _ = t * (MulAut.conj a) y := by rw [inv_mul_cancel_left]
  have hLa_le_N : L.map (MulAut.conj a).toMonoidHom ≤ normalizer (A : Set G) :=
    hLa_le_Ct.trans
      (CFSG.ComponentClassification.RestrictedStd.centralizer_le_normalizer hS.standard
        hS.t_mem hS.orderOf_t)
  have hLa_le_A : L.map (MulAut.conj a).toMonoidHom ≤ A :=
    le_of_isPerfect_of_le_normalizer_of_l34SuzOdd hS hLaperf hLa_le_N
  have hLa_le_Ad : L.map (MulAut.conj a).toMonoidHom ≤ A ⊓ centralizer ({d} : Set G) := by
    refine le_inf hLa_le_A ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_centralizer_singleton_iff]
    exact hconj_d y hy
  have hLa_le_L : L.map (MulAut.conj a).toMonoidHom ≤ L := by
    have h := CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
      (L.map (MulAut.conj a).toMonoidHom) (A ⊓ centralizer ({d} : Set G)) hLaperf hLa_le_Ad
    rw [hL, HarrisLit.centralizerResidual]
    exact h
  have hcard : Nat.card ↥(L.map (MulAut.conj a).toMonoidHom) = Nat.card ↥L := by
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]
  exact Subgroup.eq_of_le_of_card_ge hLa_le_L (by rw [hcard])

end CFSG.ComponentClassification.GrSLit.L34Sec5S
