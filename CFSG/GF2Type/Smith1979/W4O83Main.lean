module

public import CFSG.GF2Type.Smith1979.W4O83Local
public import CFSG.LargeExtraspecial.S11Basic
public import CFSG.Yardstones.M3aba7dc4b8a8.Definitions
public import CFSG.LargeExtraspecial.S14W4LocTI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4O83

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.Open
open CFSG.Yardstones.M3aba7dc4b8a8

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem hyp4_cons311_of_w4 (hTI : WeaklyClosedTITransitive.{0}) (hw : S.width = 4)
    (hno : S11.NoA2All S) (hirr : ¬ S.IsReducible) :
    ∀ g' : G, g' * S.z * g'⁻¹ ∈ S.QG → g' * S.z * g'⁻¹ ≠ S.z → Hyp4 S g' ∧ Cons311 S g' :=
  fun g' h1 h2 =>
    ⟨S14.W4Loc.hyp4_of_w4 hTI (by omega) h1 h2 (hno g' h1 h2) hirr,
      S14.W4Loc.cons311_of_w4 hTI (by omega) h1 h2 (hno g' h1 h2) hirr⟩

theorem Omega83Config.false_of_base (C : Omega83Config S) (hchar : IsCharTwoType G)
    (hbase : ∀ g' : G, g' * S.z * g'⁻¹ ∈ S.QG → g' * S.z * g'⁻¹ ≠ S.z →
      Hyp4 S g' ∧ Cons311 S g')
    (hw : S.width = 4) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    False := by
  obtain ⟨H, Cn⟩ := hbase g haQ hne
  obtain ⟨t, htQ, htQa, ht2', ht0, hk₀⟩ := C.exists_t H Cn hw 0
  have ht1 : t ≠ 1 := fun h => ht0 (by rw [h, S.cl_one])
  have ht2 : orderOf t = 2 := orderOf_eq_prime ht2' ht1
  obtain ⟨l, hl⟩ :=
    C.exists_fixed_index (fun g' h1 h2 => (hbase g' h1 h2).1) haQ hne htQ htQa hk₀ ht0
  have ht'Q : g⁻¹ * t * g ∈ S.QG := (mem_Qa_iff' g t).mp htQa
  have hstep := C.step_one_conj hchar ht2 ht'Q hl
  have hzQa : S.z ∈ S.Qa g := S.z_mem_Qa haQ hne
  have hz'Q : g⁻¹ * S.z * g ∈ S.QG := (mem_Qa_iff' g S.z).mp hzQa
  have hz'Q' : g⁻¹ * S.z * g⁻¹⁻¹ ∈ S.QG := by rwa [inv_inv]
  have hz'ne : g⁻¹ * S.z * g⁻¹⁻¹ ≠ S.z := by
    rw [inv_inv]
    intro h
    apply hne
    have h1 : g * S.z = S.z * g := by
      calc g * S.z = g * (g⁻¹ * S.z * g) := by rw [h]
        _ = S.z * g := by group
    calc g * S.z * g⁻¹ = S.z * g * g⁻¹ := by rw [h1]
      _ = S.z := by group
  have hfull := C.th_ne_cl_conj_z (hbase g⁻¹ hz'Q' hz'ne).1 l
  rw [inv_inv] at hfull
  have hprw : C.prL l (S.cl (g⁻¹ * S.z * g)) ≠ 0 :=
    (C.th_ne_iff l (S.cl (g⁻¹ * S.z * g))).mp hfull
  obtain ⟨y', hy'Q, hy'cl⟩ := S.exists_cl (C.prL l (S.cl (g⁻¹ * S.z * g)))
  have hy'plane : S.cl y' ∈ C.plane l := by
    rw [hy'cl]
    exact C.prL_mem_plane l _
  have hyU := hstep y' hy'Q hy'plane
  have hyQa : g * y' * g⁻¹ ∈ S.Qa g := by
    rw [mem_Qa_iff']
    have e : g⁻¹ * (g * y' * g⁻¹) * g = y' := by group
    rw [e]
    exact hy'Q
  have hpol : polar S.q (S.cl y') (S.cl (g⁻¹ * S.z * g)) = 0 := by
    rw [hy'cl, polar_comm, C.polar_eq_polar_prL l _ (C.prL_mem_plane l _)]
    exact CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero S.q _
  have hcomm' : y' * (g⁻¹ * S.z * g) = (g⁻¹ * S.z * g) * y' :=
    (S.polar_cl_eq_zero_iff hy'Q hz'Q).mp hpol
  have hyz : g * y' * g⁻¹ * S.z = S.z * (g * y' * g⁻¹) := by
    calc g * y' * g⁻¹ * S.z = g * (y' * (g⁻¹ * S.z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * S.z * g) * y') * g⁻¹ := by rw [hcomm']
      _ = S.z * (g * y' * g⁻¹) := by group
  have hyM : g * y' * g⁻¹ ∈ S.M := S.mem_M_iff.mpr hyz
  have hy2 : (g * y' * g⁻¹) ^ 2 ≠ 1 := by
    intro h
    have h1 : y' ^ 2 = 1 := by
      calc y' ^ 2 = g⁻¹ * (g * y' * g⁻¹) ^ 2 * g := by
            rw [pow_two, pow_two]
            group
        _ = 1 := by rw [h]; group
    have hq : S.q (S.cl y') = 1 := by
      rw [hy'cl]
      exact C.q_eq_one l _ (C.prL_mem_plane l _) hprw
    exact ((S.q_cl_eq_one_iff hy'Q).mp hq) h1
  have hL0 : g * y' * g⁻¹ ∈ S.L0 g := mem_inf.mpr ⟨hyQa, hyM⟩
  have hyL : S.ρ ⟨g * y' * g⁻¹, hyM⟩ ∈ S.Lbar g := S.ρ_mem_Lbar hL0
  obtain ⟨θ₀, hθρ, hθ3⟩ := C.exists_lift 0
  have hθOb : S.ρ θ₀ ∈ Ob S := hθρ ▸ C.theta_mem_Ob 0
  have hθt : (θ₀ : G) * t = t * θ₀ :=
    mul_comm_of_apply_eq θ₀.2 hθ3 htQ (by rw [rho_apply_eq_th C hθρ]; exact hk₀)
  have hθC : (θ₀ : G) ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr hθt
  obtain ⟨hU2, -, hUnorm⟩ := pCoreOf_facts (centralizer ({t} : Set G))
  have hu : (θ₀ : G) * (g * y' * g⁻¹) * (θ₀ : G)⁻¹ * (g * y' * g⁻¹)⁻¹ ∈
      pCoreOf 2 (centralizer ({t} : Set G)) := mul_mem (hUnorm _ hθC _ hyU) (inv_mem hyU)
  obtain ⟨n, hn⟩ := hU2 ⟨_, hu⟩
  have hn' : ((θ₀ : G) * (g * y' * g⁻¹) * (θ₀ : G)⁻¹ * (g * y' * g⁻¹)⁻¹) ^ 2 ^ n = 1 := by
    simpa using congrArg Subtype.val hn
  have hcommQ := commutator_mem_Q (x₀ := ⟨g * y' * g⁻¹, hyM⟩) hθOb hn'
  have h1 := (S.ρ_eq_one_iff _).mpr hcommQ
  simp only [map_mul, map_inv, hθρ] at h1
  have hcomm : C.theta 0 * S.ρ ⟨g * y' * g⁻¹, hyM⟩ = S.ρ ⟨g * y' * g⁻¹, hyM⟩ * C.theta 0 := by
    calc C.theta 0 * S.ρ ⟨g * y' * g⁻¹, hyM⟩
        = C.theta 0 * S.ρ ⟨g * y' * g⁻¹, hyM⟩ * (C.theta 0)⁻¹ * (S.ρ ⟨g * y' * g⁻¹, hyM⟩)⁻¹ *
          (S.ρ ⟨g * y' * g⁻¹, hyM⟩ * C.theta 0) := by group
      _ = S.ρ ⟨g * y' * g⁻¹, hyM⟩ * C.theta 0 := by rw [h1, one_mul]
  have hyL1 := C.eq_one_of_comm_th H Cn hyL 0 hcomm
  have hyQ : g * y' * g⁻¹ ∈ S.QG := (S.ρ_eq_one_iff ⟨g * y' * g⁻¹, hyM⟩).mp hyL1
  exact hy2 (S.QG_inf_Qa_sq hne (mem_inf.mpr ⟨hyQ, hyQa⟩))

theorem false_of_omega83 {z : G} (hset : GF2RankFourSetting G z) (S : Setting G)
    (_hSz : S.z = z) (hw : S.width = 4) (hno : S11.NoA2All S)
    (hTI : WeaklyClosedTITransitive.{0}) (hirr : ¬ S.IsReducible)
    (hex : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) (hC : Omega83Config S) :
    False := by
  obtain ⟨g, haQ, hne⟩ := hex
  exact hC.false_of_base hset.2.2.1 (hyp4_cons311_of_w4 hTI hw hno hirr) hw haQ hne

theorem false_of_omega83_of_not_weaklyClosed {z : G} (hset : GF2RankFourSetting G z)
    (S : Setting G) (hSz : S.z = z) (hSQ : S.QG = coreQ z) (hw : S.width = 4)
    (hno : S11.NoA2All S) (hTI : WeaklyClosedTITransitive.{0}) (hirr : ¬ S.IsReducible)
    (hnwc : ¬ ZWeaklyClosedInCore z) (hC : Omega83Config S) : False := by
  refine false_of_omega83 hset S hSz hw hno hTI hirr ?_ hC
  by_contra hcon
  refine hnwc fun g hg => ?_
  by_contra hne
  refine hcon ⟨g⁻¹, ?_, ?_⟩
  · rw [hSQ, hSz, inv_inv]
    exact hg
  · rw [hSz, inv_inv]
    exact hne

end CFSG.GF2Type.Smith1979.W4O83
