module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Center
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec5o_mem_zpowers_eq_one_or_eq {G : Type} [Group G] {g x : G}
    (hg : orderOf g = 2) (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g := by
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨k, rfl⟩ := hx
  rw [← zpow_mod_orderOf, hg]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [Nat.cast_ofNat, h, zpow_zero]
  · right; rw [Nat.cast_ofNat, h, zpow_one]

private theorem sec5o_not_isCyclic_q8 : ¬ IsCyclic (QuaternionGroup 2) := by
  intro hcyc
  haveI : IsCyclic (QuaternionGroup 2) := hcyc
  have hc : IsMulCommutative (QuaternionGroup 2) := inferInstance
  exact absurd (hc.is_comm.comm (QuaternionGroup.a (1 : ZMod (2 * 2)))
    (QuaternionGroup.xa (0 : ZMod (2 * 2)))) (by decide)

theorem sec5o_twoCoreIn_le_conj (h34a : Asc82Lemma34a) (h36 : Asc82Lemma36)
    (h52a : Asc82Lemma52a) [Finite G] {t : G} {L S : Subgroup G} {z : G}
    (hs : Sec5Ctx G t L S z) {g : G} (hg : g⁻¹ * t * g = t * z) {K : Subgroup G}
    (hK : Sl23PocketIn L z K) (hq : Nonempty (↥(twoCoreIn K) ≃* QuaternionGroup 2)) :
    twoCoreIn K ≤ CFSG.conjugate L g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Sec3SettingLB G t L := hs.toSec5Setting.toSec3SettingLB
  have hLF : InFStar L :=
    (h36 G t L hS t L hS.involution hS.component (Or.inl hS.inF)).1
  have hnorm : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L :=
    conjugate_eq_self_of_lemma36 h36 hS
  have hD : Sec3PocketData t L z K :=
    sec3PocketData_of_sl23PocketIn hS.involution hS.component hLF hnorm hs.pocket.1 hK
  have hord : orderOf (t * z) = 2 := by
    rw [← hg, orderOf_conjugate_eq t g, hS.involution]
  have htcent : t ∈ centralizer (((L ⊔ zpowers t : Subgroup G)) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hle : L ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
      sup_le hS.component.le (Subgroup.zpowers_le.mpr (by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        rfl))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hc : ∃ c ∈ centralizer ((L ⊔ zpowers t : Subgroup G) : Set G), t * z = c * z :=
    ⟨t, htcent, rfl⟩
  have hsI : Sec5Setting G (g⁻¹ * t * g) (CFSG.conjugate L g) := hs.toSec5Setting.conjugate g
  have hcomp : IsComponentIn (CFSG.conjugate L g) (centralizer ({t * z} : Set G)) := by
    rw [← hg]
    exact hsI.component
  have hInF : InFStar (CFSG.conjugate L g) := hLF.conjugate g
  rcases h34a G t L hS t L z K (t * z) (CFSG.conjugate L g) hD hord hc hcomp hInF with
    hcomm | hle
  · exfalso
    let H : Subgroup G := centralizer ((CFSG.conjugate L g : Subgroup G) : Set G)
    have hKc : K ≤ H := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hQK : twoCoreIn K ≤ K := Subgroup.map_subtype_le (H := K) (CFSG.pCore 2 K)
    have hQH : twoCoreIn K ≤ H := hQK.trans hKc
    have hQ2 : IsPGroup 2 (twoCoreIn K) :=
      (CFSG.pCore_isPGroup (p := 2) (G := K)).map K.subtype
    have hsub : IsPGroup 2 ((twoCoreIn K).subgroupOf H) :=
      IsPGroup.comap_subtype hQ2 (K := H)
    obtain ⟨P, hQP⟩ := hsub.exists_le_sylow
    have h52a' : ∀ P : Sylow 2 ↥H, IsCyclic (P : Subgroup ↥H) :=
      h52a G (g⁻¹ * t * g) (CFSG.conjugate L g) hsI
    have hle' : twoCoreIn K ≤ (P : Subgroup ↥H).map H.subtype := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hQH hx⟩, hQP hx, rfl⟩
    have hSyl : IsSylow2Of ((P : Subgroup ↥H).map H.subtype) H := isSylow2Of_map_sylow P
    haveI : IsCyclic ↥((P : Subgroup ↥H).map H.subtype) :=
      sec5_isCyclic_of_isSylow2Of h52a' hSyl
    have hcycQ : IsCyclic ↥(twoCoreIn K) := Subgroup.isCyclic_of_le hle'
    obtain ⟨e⟩ := hq
    exact sec5o_not_isCyclic_q8 (e.isCyclic.mp hcycQ)
  · exact hle

theorem sec5o_inf_centerIn_conj (h52b : Asc82Lemma52b) [Finite G] {t : G} {L S : Subgroup G}
    {z : G} (hs : Sec5Ctx G t L S z) {g : G} (hg : g⁻¹ * t * g = t * z) {Q : Subgroup G}
    (hQ : Q ≤ CFSG.conjugate L g) (hZ : centerIn Q = zpowers z) :
    Q ⊓ centerIn (CFSG.conjugate L g) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxQ, hxZ⟩ := Subgroup.mem_inf.mp hx
  have hS : Sec3SettingLB G t L := hs.toSec5Setting.toSec3SettingLB
  have hz2 : orderOf z = 2 := hs.pocket.1
  have hxZQ : x ∈ centerIn Q := by
    rw [sec5_mem_centerIn_iff]
    exact ⟨hxQ, fun y hy => (sec5_mem_centerIn_iff.mp hxZ).2 y (hQ hy)⟩
  rw [hZ] at hxZQ
  rcases sec5o_mem_zpowers_eq_one_or_eq hz2 hxZQ with hx1 | hxz
  · exact hx1
  · exfalso
    have hzZ : z ∈ centerIn (CFSG.conjugate L g) := hxz ▸ hxZ
    have hsI : Sec5Setting G (g⁻¹ * t * g) (CFSG.conjugate L g) := hs.toSec5Setting.conjugate g
    have h52b' := h52b G (g⁻¹ * t * g) (CFSG.conjugate L g) hsI
    have hzI : z ∈ twoCoreIn (CFSG.conjugate L g) :=
      sec5_zpowers_le_twoCoreIn hzZ hz2 (Subgroup.mem_zpowers z)
    have hzpow : z ∈ zpowers (t * z) := by
      rw [← hg]
      rw [← h52b'.2]
      exact hzI
    have htz2 : orderOf (t * z) = 2 := by
      rw [← hg, orderOf_conjugate_eq t g, hS.involution]
    rcases sec5o_mem_zpowers_eq_one_or_eq htz2 hzpow with hz1 | hztz
    · exact absurd hz2 (by rw [hz1, orderOf_one]; decide)
    · have ht1 : t = 1 := by
        refine mul_right_cancel (a := t) (b := z) (c := 1) ?_
        rw [one_mul]
        exact hztz.symm
      exact absurd hS.involution (by rw [ht1, orderOf_one]; decide)

end CFSG.OddStandard.SmallF3.Omega
