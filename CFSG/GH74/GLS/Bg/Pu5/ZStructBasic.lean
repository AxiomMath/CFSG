module

public import CFSG.GH74.GLS.Bg.Iii2.TailZStar

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

variable {G : Type} [Group G]

section Sylow

theorem exists_isSylowOf_ge' {K X : Subgroup G} (hXK : X ≤ K) (hX : IsPGroup 2 ↥X) :
    ∃ P : Subgroup G, IsSylowOf 2 P K ∧ X ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hXK hx⟩, hS hx, rfl⟩

theorem exists_conj_mem_of_isSylowOf' [Finite G] {K T : Subgroup G} (hT : IsSylowOf 2 T K) {g : G}
    (hg : g ∈ K) (hgp : ∃ k : ℕ, orderOf g = 2 ^ k) : ∃ h ∈ K, h * g * h⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := hT
  obtain ⟨k, hk⟩ := hgp
  have hZ : IsPGroup 2 (zpowers (⟨g, hg⟩ : K)) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk])
  obtain ⟨S', hS'⟩ := hZ.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq K S' S
  have hmem : n * ⟨g, hg⟩ * n⁻¹ ∈ (S : Subgroup K) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (mem_zpowers _))
  exact ⟨n, n.2, ⟨_, hmem, rfl⟩⟩

end Sylow

section TwoGroups

omit [Group G] in
theorem isPGroup_zpowers_of_pow_eq_one [Group G] {y : G} (hy : ∃ n : ℕ, y ^ (2 ^ n) = 1) :
    IsPGroup 2 ↥(zpowers y) := by
  obtain ⟨n, hn⟩ := hy
  have h1 : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

theorem isPGroup_zpowers_sup {y b : G} (hy : ∃ n : ℕ, y ^ (2 ^ n) = 1)
    (hb : ∃ n : ℕ, b ^ (2 ^ n) = 1) (hyb : y * b = b * y) :
    IsPGroup 2 ↥(zpowers y ⊔ zpowers b) := by
  refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_eq_one hy)
    (isPGroup_zpowers_of_pow_eq_one hb) ?_
  have hyc : y ∈ centralizer (zpowers b : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro g ⟨k, rfl⟩
    exact ((Commute.zpow_right (show Commute y b from hyb) k).eq).symm
  exact zpowers_le.2 (Subgroup.centralizer_le_normalizer (zpowers b : Set G) hyc)

end TwoGroups

omit [Group G] in
theorem exists_two_pow_eq_one_of_orderOf [Group G] {w : G} (h : orderOf w = 2) :
    ∃ n : ℕ, w ^ (2 ^ n) = 1 :=
  ⟨1, by have := pow_orderOf_eq_one w; rwa [h, ← pow_one 2] at this⟩

omit [Group G] in
theorem orderOf_conj_eq' [Group G] (c x : G) : orderOf (c * x * c⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x

omit [Group G] in
theorem conj_mem_cmap' [Group G] {K : Subgroup G} {w : G} (hw : w ∈ K) (c : G) :
    c * w * c⁻¹ ∈ cmap c K :=
  Subgroup.mem_map_of_mem _ hw

theorem qdata_orderOf {T K : Subgroup G} {z : G} (h : QData T K z) : orderOf z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h.sq) h.ne

section Rigid

variable [Finite G]

omit [Finite G] in
theorem rigidProduct_le_cent (a : G) : rigidProduct a ≤ centralizer ({a} : Set G) :=
  sSup_le fun _ hK => (rr_pcomp hK).1

omit [Finite G] in
theorem mem_zStar_of_forall_comm {X : Subgroup G} {c : G} (hc : c ∈ X)
    (hcomm : ∀ k ∈ X, k * c = c * k) : c ∈ zStar X := by
  refine ⟨hc, Subgroup.le_normalizer hc,
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hc), fun k hk => ?_⟩
  have : ⁅k, c⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hcomm k hk)
  rw [this]
  exact one_mem _

omit [Finite G] in
theorem self_mem_zStar_rigidProduct {a : G} (h : a ∈ rigidProduct a) :
    a ∈ zStar (rigidProduct a) :=
  mem_zStar_of_forall_comm h fun _ hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (rigidProduct_le_cent a hk)

theorem mem_zStar_of_involution (h44 : II4_44) (hG : IsKProperSimple G) {x : G} {K : Subgroup G}
    (hK : IsRigidRankOneComp x K) {w : G} (hwK : w ∈ K) (hw2 : orderOf w = 2) : w ∈ zStar K :=
  ⟨hwK, rr_inv_mem_cSec h44 hG hK hwK hw2⟩

theorem comm_of_mem_cSec {T K : Subgroup G} (hT : IsPGroup 2 ↥T) {x y : G} (hxT : x ∈ T)
    (hyT : y ∈ T) (hxK : x ∈ K) (hy : y ∈ cSec K) : x * y = y * x := by
  have h1 : ⁅x, y⁆ ∈ pPrimeCoreOf 2 K := hy.2.2 x hxK
  have h2 : ⁅x, y⁆ ∈ T :=
    T.mul_mem (T.mul_mem (T.mul_mem hxT hyT) (T.inv_mem hxT)) (T.inv_mem hyT)
  have h3 : ⁅x, y⁆ ∈ T ⊓ pPrimeCoreOf 2 K := ⟨h2, h1⟩
  rw [inf_pPrimeCoreOf_eq_bot hT, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h3

omit [Finite G] in
theorem conj_mem_cSec_cmap {K : Subgroup G} {x : G} (hx : x ∈ cSec K) (c : G) :
    c * x * c⁻¹ ∈ cSec (cmap c K) := by
  have h := cmap_mem_centralizerSection hx c
  rw [← pPrimeCoreOf_cmap] at h
  exact h

theorem mem_rigidProduct_conj {z x : G} (hx : x ∈ rigidProduct z) (c : G) :
    c * x * c⁻¹ ∈ rigidProduct (c * z * c⁻¹) := by
  have hle : rigidProduct z ≤ cmap c⁻¹ (rigidProduct (c * z * c⁻¹)) := by
    refine sSup_le fun K hK => ?_
    have hK' : IsRigidRankOneComp (c * z * c⁻¹) (cmap c K) :=
      ⟨isPRigid_cmap hK.1 c, by rw [pRank_cmap]; exact hK.2⟩
    have h1 : cmap c⁻¹ (cmap c K) ≤ cmap c⁻¹ (rigidProduct (c * z * c⁻¹)) :=
      Subgroup.map_mono (le_sSup hK')
    rwa [cmap_inv_cancel] at h1
  have h2 := hle hx
  rw [mem_cmap] at h2
  simpa using h2

theorem exists_involution_inf (hquat : II4_4_quat) (hG : IsKProperSimple G) {x : G}
    {K T : Subgroup G} (hK : IsRigidRankOneComp x K)
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) : ∃ w, w ∈ T ⊓ K ∧ orderOf w = 2 := by
  obtain ⟨w, hw⟩ := exists_qdata (hquat G hG x (rr_ord hK) T K hT (rr_pcomp hK) hK.2)
  exact ⟨w, hw.mem, qdata_orderOf hw⟩

end Rigid

end CFSG.GH74.GLS.Bg.Pu5
