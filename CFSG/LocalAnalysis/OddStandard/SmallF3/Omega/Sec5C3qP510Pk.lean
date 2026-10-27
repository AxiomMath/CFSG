module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510R
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFacts
public import CFSG.Walter.AStar.Subnormal
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec510Pk (G : Type) [Group G] (t : G) (L S : Subgroup G) (z : G)
    (K₁ K₂ : Subgroup G) : Prop where
  pocket₁ : Sl23PocketIn L z K₁
  pocket₂ : Sl23PocketIn L z K₂
  ne : K₁ ≠ K₂
  q : Sec510Q G L z (twoCoreIn K₁) (twoCoreIn K₂)
  inf₁ : S ⊓ K₁ = twoCoreIn K₁
  inf₂ : S ⊓ K₂ = twoCoreIn K₂
  z_mem : z ∈ twoCoreIn K₁ ⊔ twoCoreIn K₂
  t_not_mem : t ∉ twoCoreIn K₁ ⊔ twoCoreIn K₂

theorem Sec510Pk.Q_le_S {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G}
    {K₁ K₂ : Subgroup G} (hk : Sec510Pk G t L S z K₁ K₂) :
    twoCoreIn K₁ ⊔ twoCoreIn K₂ ≤ S :=
  sup_le (hk.inf₁.symm.le.trans inf_le_left) (hk.inf₂.symm.le.trans inf_le_left)

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G}

theorem sec5p510_isSylow2Of_inf_subnormal {X P K : Subgroup G} (hP : IsSylow2Of P X)
    (hKX : K ≤ X) (hK : (K.subgroupOf X).IsSubnormal) : IsSylow2Of (P ⊓ K) K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Ps, hPs⟩ := hP.exists_sylow
  obtain ⟨P', hP'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Ps hK
  let e : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  have hcomp : K.subtype.comp e.toMonoidHom = X.subtype.comp (K.subgroupOf X).subtype := by
    ext x
    rfl
  have key : ((P'.mapSurjective he : Sylow 2 ↥K) : Subgroup ↥K).map K.subtype = P ⊓ K := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, hcomp, ← Subgroup.map_map, hP',
      Subgroup.map_inf_eq _ _ X.subtype X.subtype_injective, hPs,
      Subgroup.map_subgroupOf_eq_of_le hKX]
  rw [← key]
  exact isSylow2Of_map_sylow _

theorem sec5p510_isSylow2Of_inf_cent (hy : Sec5B59Hyp) (h : Sec5Ctx G t L S z) :
    IsSylow2Of (S ⊓ L) (L ⊓ centralizer ({z} : Set G)) := by
  have hSL : IsSylow2Of (S ⊓ L) L :=
    sec4_isSylow2Of_inf (sec5p510_L_le_centralizer_t h)
      (sec4_mem_normalizer hy.h36 h.toSec5Setting.toSec3SettingLB) h.sylow
  have hle : S ⊓ L ≤ L ⊓ centralizer ({z} : Set G) := fun x hx =>
    ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.mpr (h.central x hx.1)⟩
  refine ⟨hle, hSL.2.1, fun h2 => hSL.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex (H := S ⊓ L) (K := L ⊓ centralizer ({z} : Set G))
    (L := L) hle inf_le_left
  exact h2.trans ⟨_, h1.symm⟩

theorem sec5p510_twoCoreIn_le {K P : Subgroup G} (hP : IsSylow2Of P K) : twoCoreIn K ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow
  rw [← hQ]
  exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := ↥K)).le_sylow_of_normal Q)

private theorem sec5p510_odd_card_oddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem sec5p510_card_pocket {K : Subgroup G} (hK : IsSL23Mod K) :
    ∃ m : ℕ, Odd m ∧ Nat.card K = m * 24 := by
  obtain ⟨e⟩ := hK
  refine ⟨Nat.card (oddCore ↥K), sec5p510_odd_card_oddCore _, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (oddCore ↥K)
  have h2 : Nat.card (↥K ⧸ oddCore ↥K) = 24 := by
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field 2]
    simp [ZMod.card, Fin.prod_univ_two]
  rw [h1, h2, mul_comm]

theorem sec5p510_sylow_eq_twoCore {K P : Subgroup G} (hK : IsSL23Mod K) (hP : IsSylow2Of P K)
    (hQ : Nonempty (↥(twoCoreIn K) ≃* QuaternionGroup 2)) : P = twoCoreIn K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := sec5p510_twoCoreIn_le hP
  obtain ⟨m, hm, hmc⟩ := sec5p510_card_pocket hK
  obtain ⟨k, hk⟩ := hP.2.1.exists_card_eq
  have hdvd : Nat.card ↥P ∣ m * 24 := by
    have := Subgroup.card_dvd_of_le hP.1
    rwa [hmc] at this
  have hcop : Nat.Coprime (Nat.card ↥P) m := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have h24 : 2 ^ k ∣ 24 := by
    have := hcop.dvd_of_dvd_mul_left hdvd
    rwa [hk] at this
  have hk3 : k ≤ 3 := by
    by_contra hk3
    have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h16.trans h24
    norm_num at this
  have hQc : Nat.card ↥(twoCoreIn K) = 8 := by
    obtain ⟨e⟩ := hQ
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hQc, hk]
  calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 8 := by norm_num

theorem sec5p510_inf_pocket (hy : Sec5B59Hyp) (h : Sec5Ctx G t L S z) {K : Subgroup G}
    (hK : Sl23PocketIn L z K) (hQ : Nonempty (↥(twoCoreIn K) ≃* QuaternionGroup 2)) :
    S ⊓ K = twoCoreIn K := by
  obtain ⟨-, hKX, hKs, hK23⟩ := hK
  have h1 := sec5p510_isSylow2Of_inf_subnormal (sec5p510_isSylow2Of_inf_cent hy h) hKX hKs
  rw [inf_assoc, inf_eq_right.mpr (hKX.trans inf_le_left)] at h1
  exact sec5p510_sylow_eq_twoCore hK23 h1 hQ

theorem sec5p510_exists_pk (hy : Sec5B59Hyp) (hF0 : Asc82FactPockets6)
    (h : Sec5Ctx G t L S z) : ∃ K₁ K₂ : Subgroup G, Sec510Pk G t L S z K₁ K₂ := by
  obtain ⟨K₁, K₂, hp₁, hp₂, hne, hi₁, hi₂, hcomm, hcard, hcenter, hZ⟩ :=
    hF0 G L z h.toSec5Setting.isOm6Z2 h.pocket
  have hzQ : z ∈ twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
    have hz : z ∈ centerIn (twoCoreIn K₁ ⊔ twoCoreIn K₂) := by
      rw [hcenter]
      exact Subgroup.mem_zpowers z
    exact (sec5_mem_centerIn_iff.mp hz).1
  have hle₁ : twoCoreIn K₁ ≤ L :=
    (Subgroup.map_subtype_le _).trans (hp₁.2.1.trans inf_le_left)
  have hle₂ : twoCoreIn K₂ ≤ L :=
    (Subgroup.map_subtype_le _).trans (hp₂.2.1.trans inf_le_left)
  have hzL : z ∉ centerIn L := by
    intro hzC
    have hz1 : z ∈ (twoCoreIn K₁ ⊔ twoCoreIn K₂) ⊓ centerIn L := ⟨hzQ, hzC⟩
    rw [hZ, Subgroup.mem_bot] at hz1
    have h2 := h.pocket.1
    rw [hz1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have htL : t ∈ L := (hy.h52b G t L h.toSec5Setting).1
  have htC : t ∈ centerIn L := sec5_mem_centerIn_iff.mpr ⟨htL, fun y hy' =>
    (Subgroup.mem_centralizer_iff.mp (sec5p510_t_mem_centralizer_L h) y hy').symm⟩
  have htQ : t ∉ twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
    intro htQ
    have ht1 : t ∈ (twoCoreIn K₁ ⊔ twoCoreIn K₂) ⊓ centerIn L := ⟨htQ, htC⟩
    rw [hZ, Subgroup.mem_bot] at ht1
    have h2 := h.involution
    rw [ht1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  exact ⟨K₁, K₂, hp₁, hp₂, hne, ⟨hle₁, hle₂, hi₁, hi₂, hcomm, hcard, hcenter, hzL⟩,
    sec5p510_inf_pocket hy h hp₁ hi₁, sec5p510_inf_pocket hy h hp₂ hi₂, hzQ, htQ⟩

end CFSG.OddStandard.SmallF3.Omega
