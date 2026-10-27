module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasic
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStarSylow
import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Ext

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

section

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {n : ℕ} {z : G}

theorem StdSetup.mem_centralizer_of_centralizes_sylow' (h : StdSetup G L n z)
    {C : Subgroup G} (hC : C = centralizer ({z} : Set G)) (S : Sylow 2 ↥C) {y : G}
    (hyC : y ∈ C) (hy2 : y * y = 1)
    (hy : ∀ t ∈ (S : Subgroup ↥C).map C.subtype ⊓ L, y * t = t * y) :
    y ∈ centralizer (L : Set G) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyN : y ∈ normalizer (L : Set G) := h.mem_normalizer_of_mem_centralizer (hC ▸ hyC)
  set M := h.model with hM
  set σ : Perm (Fin n) := M.perm y hyN with hσdef
  have hσ2 : σ * σ = 1 := by
    have h1 := M.perm_mul h.hn hyN hyN
    have h2 : (⟨y, hyN⟩ : ↥(normalizer (L : Set G))) * ⟨y, hyN⟩ = 1 := Subtype.ext hy2
    have h3 := congrArg (M.permHom h.hn) h2
    rw [map_mul, map_one] at h3
    exact h3
  by_cases hσ1 : σ = 1
  · exact (h.perm_eq_one_iff M hyN).1 hσ1
  · exfalso
    have hLC : L ≤ C := hC ▸ h.le_centralizer_singleton
    have hCN : C ≤ normalizer (L : Set G) := hC ▸ h.cent_eq.le
    have hLn : (L.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).2 hCN
    obtain ⟨P0, hP0⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_subnormal S
      hLn.isSubnormal
    let φ : ↥(L.subgroupOf C) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
    let ξ : ↥L →* M.K := M.e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L))
    have hξ : Function.Surjective ξ := fun k => by
      obtain ⟨a, ha⟩ := M.surj_mk k
      exact ⟨a, ha⟩
    let ξ' : ↥(L.subgroupOf C) →* M.K := ξ.comp φ.toMonoidHom
    have hξ' : Function.Surjective ξ' := hξ.comp φ.surjective
    let Pb : Sylow 2 M.K := Sylow.mapSurjective hξ' P0
    have hPb : ∀ p ∈ (Pb : Subgroup M.K), ∃ u ∈ (P0 : Subgroup ↥(L.subgroupOf C)), ξ' u = p :=
      fun p hp => by
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hp
        exact ⟨u, hu, rfl⟩
    have hind : M.C.Induces (M.autOf y hyN) σ := M.induces_perm h.hn y hyN
    have hpow : σ ^ 2 = 1 := by rw [pow_two]; exact hσ2
    have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one hpow
    have hsum := Equiv.Perm.sum_cycleType σ
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hk : σ.support.card = 2 * σ.cycleType.card := by omega
    have hk1 : 1 ≤ σ.cycleType.card := by
      by_contra hcon
      have h0 : σ.support.card = 0 := by omega
      exact hσ1 (Equiv.Perm.card_support_eq_zero.1 h0)
    have hfix : (Pb : Subgroup M.K) ≤ AhatData.fixSub (M.autOf y hyN) := by
      intro p hp
      obtain ⟨u, hu, rfl⟩ := hPb p hp
      have hu' : (u : ↥C) ∈ (P0 : Subgroup ↥(L.subgroupOf C)).map (L.subgroupOf C).subtype :=
        Subgroup.mem_map_of_mem _ hu
      rw [hP0] at hu'
      have huS : ((u : ↥C) : G) ∈ (S : Subgroup ↥C).map C.subtype ⊓ L :=
        ⟨⟨u, hu'.1, rfl⟩, u.2⟩
      have hyu := hy _ huS
      rw [AhatData.mem_fixSub]
      show M.autOf y hyN (M.e (QuotientGroup.mk (φ u))) = M.e (QuotientGroup.mk (φ u))
      rw [M.autOf_mk]
      congr 2
      apply Subtype.ext
      show y * ((u : ↥C) : G) * y⁻¹ = ((u : ↥C) : G)
      rw [hyu]; group
    exact hind.not_sylow_le_fixSub h.hn hσ2 hk hk1 Pb hfix

theorem StdSetup.isSylowTwoIn_top' (h : StdSetup G L n z)
    {C : Subgroup G} (hC : C = centralizer ({z} : Set G)) (S : Sylow 2 ↥C) :
    IsSylowTwoIn (⊤ : Subgroup G) ((S : Subgroup ↥C).map C.subtype) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmemC : ∀ x : G, x ∈ C ↔ x * z = z * x := fun x => by
    rw [hC]
    exact Subgroup.mem_centralizer_singleton_iff
  set T : Subgroup G := (S : Subgroup ↥C).map C.subtype with hT
  have hT2 : IsPGroup 2 ↥T := S.isPGroup'.map C.subtype
  obtain ⟨P, hTP⟩ := hT2.exists_le_sylow
  have hzC : z ∈ C := (hmemC z).2 rfl
  have hz1 : z ≠ 1 := by
    intro h1
    have := h.hz
    rw [h1, orderOf_one] at this
    omega
  have hzT : z ∈ T := by
    have hzcen : (⟨z, hzC⟩ : ↥C) ∈ center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext ((hmemC c).1 c.2)
    have := ComponentClassification.StandardRecognition.mem_sylow_of_mem_center_of_orderOf_eq_two
      hzcen (by rw [Subgroup.orderOf_mk]; exact h.hz) S
    exact ⟨⟨z, hzC⟩, this, rfl⟩
  have hzP : z ∈ (P : Subgroup G) := hTP hzT
  have hPnt : Nontrivial ↥(P : Subgroup G) :=
    ⟨⟨⟨z, hzP⟩, 1, fun h1 => hz1 (congrArg Subtype.val h1)⟩⟩
  have hcn : Nontrivial ↥(Subgroup.center ↥(P : Subgroup G)) := P.isPGroup'.center_nontrivial
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥(P : Subgroup G)) := by
    obtain ⟨k, hk⟩ := (P.isPGroup'.to_subgroup (Subgroup.center ↥(P : Subgroup G))).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h1' : Nat.card ↥(Subgroup.center ↥(P : Subgroup G)) = 1 := by simpa using hk
      exact (Finite.one_lt_card_iff_nontrivial.2 hcn).ne' (by
        simpa [Nat.card_eq_fintype_card] using h1')
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨y', hy'2⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set y : G := ((y' : ↥(P : Subgroup G)) : G) with hy
  have hyc : ∀ p ∈ (P : Subgroup G), y * p = p * y := fun p hp => by
    have := congrArg (fun w : ↥(P : Subgroup G) => (w : G))
      (Subgroup.mem_center_iff.1 y'.2 ⟨p, hp⟩).symm
    simpa using this
  have hy2 : orderOf y = 2 := by
    rw [hy, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hy'2
  have hysq : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, sq] at this
  have hyC : y ∈ C := (hmemC y).2 (hyc z hzP)
  have hyK : y ∈ centralizer (L : Set G) :=
    h.mem_centralizer_of_centralizes_sylow' hC S hyC hysq (fun t ht => hyc t (hTP ht.1))
  have hyz : y = z := h.inv_unique y hyK hy2
  have hPC : (P : Subgroup G) ≤ C := fun p hp => by
    rw [hmemC]
    have := hyc p hp
    rw [hyz] at this
    exact this.symm
  have hSP : (S : Subgroup ↥C) ≤ (P : Subgroup G).subgroupOf C := fun s hs =>
    hTP ⟨s, hs, rfl⟩
  have hP2' : IsPGroup 2 ↥((P : Subgroup G).subgroupOf C) :=
    P.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  have heq : (P : Subgroup G).subgroupOf C = (S : Subgroup ↥C) := S.is_maximal' hP2' hSP
  have hPT : (P : Subgroup G) = T := by
    rw [hT, ← heq, Subgroup.map_subgroupOf_eq_of_le hPC]
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hPT]
    exact P.isPGroup'
  · rw [← hPT, Subgroup.relIndex_top_right]
    exact P.not_dvd_index

theorem StdSetup.isSylowTwoIn_top (h : StdSetup G L n z)
    (S : Sylow 2 ↥(centralizer ({z} : Set G))) :
    IsSylowTwoIn (⊤ : Subgroup G) ((S : Subgroup ↥(centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype) :=
  h.isSylowTwoIn_top' rfl S

end

end CFSG.OddStandard.Solomon75
