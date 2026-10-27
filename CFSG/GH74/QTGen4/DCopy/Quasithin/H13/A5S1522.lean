module

public import CFSG.Quasithin.H13.A5S1522
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1514

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Fischer CFSG.LieType.BorelTits
open CFSG.Quasithin.A5Model
open scoped commutatorElement MatrixGroups Pointwise

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem sq_eq_one_of_mem_S2_F4 (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (S.V1 : Set G)) {x : G}
    (hx : x ∈ conjClosure S.V1 L ⊔ (conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) g)) :
    x ^ 2 = 1 := by
  rw [S.conjClosure_V1_L] at hx
  have hUN : ∀ u ∈ conjClosure S.V3 H, u ∈ Subgroup.normalizer (V : Set G) := fun u hu =>
    S.frame.T_le (S.conjClosure_V3_le_T_F4 h1323 hH hu)
  have hgV : g ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hg
  have hzg : g * S.z * g⁻¹ = S.z → False := by
    intro hgz
    apply hgN
    rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
    calc g * S.z = g * S.z * g⁻¹ * g := by group
      _ = S.z * g := by rw [hgz]

  have hg4 : S.frame.ρ ⟨g, hgV⟩ 4 ≠ 4 := by
    intro h4
    apply hzg
    rw [S.conj_eq_iff ⟨g, hgV⟩ ⟨S.z, S.z_mem_V⟩, S.psi_z]
    exact pact_W4 h4

  have hcent : ∀ w ∈ conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) g,
      w ∈ Subgroup.centralizer (V : Set G) := by
    intro w hw
    obtain ⟨hwU, hwg⟩ := Subgroup.mem_inf.mp hw
    rw [mem_rconj] at hwg
    have h1 := (S.lemma_13_5_14_two_F4 h1323 hH hna).1 w hwU
    have h2 := (S.lemma_13_5_14_two_F4 h1323 hH hna).1 _ hwg
    have e : S.frame.ρ ⟨g * w * g⁻¹, hUN _ hwg⟩ =
        S.frame.ρ ⟨g, hgV⟩ * S.frame.ρ ⟨w, hUN w hwU⟩ * (S.frame.ρ ⟨g, hgV⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e] at h2
    have hw1 : S.frame.ρ ⟨w, hUN w hwU⟩ = 1 := by
      obtain ⟨n1, n2, n3⟩ := K4_inter_conj _ hg4
      rcases h1 with h | h | h | h
      · exact h
      · rw [h] at h2; exact absurd h2 n1
      · rw [h] at h2; exact absurd h2 n2
      · rw [h] at h2; exact absurd h2 n3
    exact S.frame.mem_centralizer_of_rho _ hw1

  have hsq : ∀ w ∈ conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) g, w ^ 2 = 1 := by
    intro w hw
    obtain ⟨hwU, hwg⟩ := Subgroup.mem_inf.mp hw
    rw [mem_rconj] at hwg
    have hF := S.hypF91_F4 h1323 hH
    have h1 := S.mem_V1.mp (hF.sq_mem_conjClosure w hwU)
    have h2 := S.mem_V1.mp (hF.sq_mem_conjClosure _ hwg)
    rcases h1 with h1 | h1
    · exact h1
    · exfalso
      have e : (g * w * g⁻¹) ^ 2 = g * w ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
      rw [e, h1] at h2
      rcases h2 with h2 | h2
      · apply S.z_ne_one
        have : g⁻¹ * (g * S.z * g⁻¹) * g = S.z := by group
        rw [h2] at this
        simpa using this.symm
      · exact hzg h2

  have hle : conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) g ≤
      Subgroup.normalizer (V : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (hcent w hw)
  have hx' : x ∈ (V : Set G) *
      ((conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) g : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left V _ hle]
    exact hx
  obtain ⟨v, hv, w, hw, rfl⟩ := Set.mem_mul.mp hx'
  have hvw : v * w = w * v := Subgroup.mem_centralizer_iff.mp (hcent w hw) v hv
  have hv2 : v ^ 2 = 1 := S.elemAbelian_V.2 v hv
  calc (v * w) ^ 2 = v ^ 2 * w ^ 2 := by
        rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc w, ← hvw, mul_assoc, mul_assoc]
    _ = 1 := by rw [hv2, hsq w hw, mul_one]

theorem sq_eq_one_of_comm_cL1_F4
    (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {u : G} (hu : u ∈ conjClosure S.V3 H)
    (huc : u * S.cL1 = S.cL1 * u) : u ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, hgN⟩ := S.exists_L_not_normalizer_V1
  have hyp := S.almostSpecialA5Hyp_F4 h1323 hH hna
  obtain ⟨⟨s, hs⟩, -⟩ := hyp.G24_six' rfl hg hgN rfl rfl rfl
  have hI := (S.lemma_13_5_14_three_F4 h1323 hH hna hg hgN).1
  have hcI : (S.cL1 : G) ∈ conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) g := by
    rw [hI]
    exact Subgroup.mem_sup_left (S.L1_le_L S.cL1_mem)
  have huI : u ∈ conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) g := Subgroup.mem_sup_left hu

  have hcS : (S.cL1 : G) ∉ pCoreOf 2 (conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) g) := by
    intro h
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 _ ⟨_, h⟩
    have hk' : (S.cL1 : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    apply S.cL1_not_mem
    have h1 : orderOf (S.cL1 : G) ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one S.cL1_cube) (orderOf_dvd_of_pow_eq_one hk')
    rw [Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2), Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    rw [h1]
    exact Subgroup.one_mem _

  obtain ⟨k, hk⟩ := S.isPGroup_T ⟨u, S.conjClosure_V3_le_T_F4 h1323 hH hu⟩
  have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hS2 := mem_of_comm_of_isSum hs (c := ⟨_, hcI⟩) (x := ⟨u, huI⟩)
    (Subtype.ext S.cL1_cube) hcS (k := k) (Subtype.ext hk') (Subtype.ext huc.symm)
  exact S.sq_eq_one_of_mem_S2_F4 h1323 hH hna hg hgN hS2

end Setting

end CFSG.Quasithin.H13.A5
