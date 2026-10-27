module

public import CFSG.Quasithin.H13.A6S1372L76N3j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1354
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76N3i

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem nonempty_c3Hom_F4 (h139 : Stmt13_3_9_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (hNS : ¬ LieModel G .PSp 3 2 1) (hhat : ¬ IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} (hK : K ∈ cComp H) (hL1K : S.L1 ≤ K)
    (hSL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1) :
    Nonempty (S.C3Hom H K) := by
  obtain ⟨hHK, Φ, h1, h2, h3, h4, h5⟩ :=
    S.exists_c3Hom_F4 h139 h37 h38 h13315 h1356two hNS hhat hH hab hK hL1K hSL
  exact ⟨⟨le_of_mem_cComp hK, hHK, Φ, h1, h2, h3, h4, h5⟩⟩

theorem not_mem_normalizer_L_of_cube_F4 (h1337 : Stmt13_3_7_F4)
    (hhat : ¬ IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz) {k : G} (hkH : k ∈ H)
    (hkC : k ∈ Subgroup.centralizer (S.V2 : Set G)) (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) :
    k ∉ Subgroup.normalizer (L : Set G) := by
  intro hkL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkV : k ∈ Subgroup.normalizer (V : Set G) := S.inf_M_le_NV' hH ⟨hkH, hkL⟩
  set kn : ↥(Subgroup.normalizer (V : Set G)) := ⟨k, hkV⟩ with hkn

  have hv : ((S.frame.ψ ⟨(kn : G) * S.v2 * (kn : G)⁻¹, S.conj_v2_mem_V kn⟩ : ↥W4) : P6) =
      dv 0 1 := by
    have e : k * S.v2 * k⁻¹ = S.v2 := by
      have := Subgroup.mem_centralizer_iff.1 hkC S.v2 S.v2_mem_V2
      rw [← this]
      group
    have e' : (⟨(kn : G) * S.v2 * (kn : G)⁻¹, S.conj_v2_mem_V kn⟩ : ↥V) = ⟨S.v2, S.v2_mem_V⟩ :=
      Subtype.ext e
    rw [e', S.psi_v2]
  rw [S.psi_conj_v2] at hv
  have hz : act4f (S.frame.ρ kn) e0123 = e0123 := by
    have hzc : k * S.z * k⁻¹ = S.z := by
      have h1 : k ∈ S.G1 := hH.2.1 hkH
      rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
      rw [h1, mul_inv_cancel_right]
    have h3 := S.psi_conj kn ⟨S.z, S.z_mem_V⟩
    have e : (⟨(kn : G) * S.z * (kn : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hkV _).mp S.z_mem_V⟩ :
        ↥V) = ⟨S.z, S.z_mem_V⟩ := Subtype.ext hzc
    rw [e, S.psi_z] at h3
    exact (congrArg Subtype.val h3).symm
  have hρ3 : S.frame.ρ kn ^ 3 = 1 := by
    have : kn ^ 3 = 1 := Subtype.ext (by simpa [hkn] using hk3)
    rw [← map_pow, this, map_one]
  have hρ1 := A6L76N3.perm_fix_v2_z_cube _ hρ3 hv hz
  have hkCV : k ∈ Subgroup.centralizer (V : Set G) := (S.rho_eq_one_iff kn).1 hρ1
  rcases h1337 G T L V S.h13 S.irr S.a6 with h3 | ⟨hhat', -⟩
  · apply h3
    have h1 := Subgroup.orderOf_dvd_natCard _ hkCV
    rwa [orderOf_eq_prime hk3 hk1] at h1
  · exact hhat hhat'

variable {S} {H K : Subgroup G} (D : S.C3Hom H K)
include D

theorem C3Hom.exists_c2_F4 (h13314 : Stmt13_3_14_F4)
    (h13315 : Stmt13_3_15_F4) (hhat : ¬ IsHatA6 L) (hH : H ∈ S.Hz) (hK : K ∈ cComp H) :
    ∃ c : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (c : G) ∈ T ∧
      (c : G) ∈ Subgroup.centralizer (S.V2 : Set G) ∧ ¬ A6L76N3.InR (D.Φ c) := by
  by_contra hcon
  push Not at hcon
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  have hTG1 : T ≤ g1 T V := hg1 ▸ hTH.trans hH.2.1

  have h9 := (S.lemma13_5_4_F4 h13314 h13315 (L₁Of L S.V2) (fun h => absurd h hhat)
    (fun _ => rfl)).2.2.2.2.2.2.2.2
  obtain ⟨q₀, hq₀G, hq₀C⟩ := IsConcreteLE.not_le_iff_exists.1 h9
  have hq₀T : q₀ ∈ T := pCoreOf_le_of_sylow S.h13.sylow hTG1 hq₀G
  have hq₀Q : q₀ ∈ pCoreOf 2 H := by
    rw [hg1] at hq₀G
    exact S.pCoreOf_G1_le_QH hTH hH.2.1 hq₀G
  have hzT : ∀ t ∈ T, t * S.z * t⁻¹ = S.z := by
    intro t ht
    have h1 : t ∈ S.G1 := hH.2.1 (hTH ht)
    rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
    rw [h1, mul_inv_cancel_right]
  have hq₀v : q₀ * S.v2 * q₀⁻¹ = S.z * S.v2 := by
    rcases S.conj_v2_cases (S.T_le_normalizer_V2 hq₀T) (hzT q₀ hq₀T) with h | h
    · exact absurd (S.mem_centralizer_V2_of (hzT q₀ hq₀T) h) hq₀C
    · exact h
  have hq₀1 : D.Φ ⟨q₀, D.T_le hH hq₀T⟩ = 1 := D.triv _ hq₀Q

  have hTR : ∀ t (ht : t ∈ T), A6L76N3.InR (D.Φ ⟨t, D.T_le hH ht⟩) := by
    intro t ht
    rcases S.conj_v2_cases (S.T_le_normalizer_V2 ht) (hzT t ht) with h | h
    · exact hcon _ ht (S.mem_centralizer_V2_of (hzT t ht) h)
    · have hc : q₀⁻¹ * t ∈ T := T.mul_mem (T.inv_mem hq₀T) ht
      have hcz := hzT _ hc
      have hcv : (q₀⁻¹ * t) * S.v2 * (q₀⁻¹ * t)⁻¹ = S.v2 := by
        have e1 : q₀⁻¹ * S.z * q₀ = S.z := by
          calc q₀⁻¹ * S.z * q₀ = q₀⁻¹ * (q₀ * S.z * q₀⁻¹) * q₀ := by rw [hzT q₀ hq₀T]
            _ = S.z := by group
        have e2 : q₀⁻¹ * S.v2 * q₀ = S.z * S.v2 := by
          have hzz : S.z * S.z = 1 := by rw [← pow_two]; exact S.z_sq
          calc q₀⁻¹ * S.v2 * q₀ = q₀⁻¹ * (S.z * (S.z * S.v2)) * q₀ := by
                rw [← mul_assoc S.z S.z S.v2, hzz, one_mul]
            _ = q₀⁻¹ * (S.z * (q₀ * S.v2 * q₀⁻¹)) * q₀ := by rw [hq₀v]
            _ = (q₀⁻¹ * S.z * q₀) * S.v2 := by group
            _ = S.z * S.v2 := by rw [e1]
        calc (q₀⁻¹ * t) * S.v2 * (q₀⁻¹ * t)⁻¹ = q₀⁻¹ * (t * S.v2 * t⁻¹) * q₀ := by group
          _ = q₀⁻¹ * (S.z * S.v2) * q₀ := by rw [h]
          _ = (q₀⁻¹ * S.z * q₀) * (q₀⁻¹ * S.v2 * q₀) := by group
          _ = S.z * (S.z * S.v2) := by rw [e1, e2]
          _ = S.v2 := by
            rw [← mul_assoc, show S.z * S.z = 1 by rw [← pow_two]; exact S.z_sq, one_mul]
      have hR := hcon ⟨q₀⁻¹ * t, D.T_le hH hc⟩ hc (S.mem_centralizer_V2_of hcz hcv)
      have e : (⟨t, D.T_le hH ht⟩ : ↥(H ⊓ Subgroup.normalizer (K : Set G))) =
          ⟨q₀, D.T_le hH hq₀T⟩ * ⟨q₀⁻¹ * t, D.T_le hH hc⟩ := Subtype.ext (by
            show t = q₀ * (q₀⁻¹ * t)
            group)
      rw [e, map_mul, hq₀1, one_mul]
      exact hR

  let φK : ↥K →* SL3.S := D.Φ.comp (Subgroup.inclusion (le_inf D.K_le Subgroup.le_normalizer))
  have hφK : Function.Surjective φK := by
    intro A
    obtain ⟨k, hkK, hk⟩ := D.surj A
    exact ⟨⟨k, hkK⟩, hk⟩
  have hle : ((T ⊓ K).subgroupOf K).map φK ≤ A6L76N3.R := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : G) ∈ T ⊓ K := ht
    exact hTR t ht'.1
  have hsyl := S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hK) hTs
  have hdvd := (Subgroup.index_dvd_of_le hle).trans
    (Subgroup.index_map_dvd ((T ⊓ K).subgroupOf K) hφK)
  rw [A6L76N3.index_R] at hdvd
  exact hsyl.2.2 ((by norm_num : (2 : ℕ) ∣ 42).trans hdvd)

end Setting4

end CFSG.Quasithin.H13.A6
