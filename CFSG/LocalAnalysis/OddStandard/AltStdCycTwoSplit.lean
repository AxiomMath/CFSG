module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalJ

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup Equiv Equiv.Perm AltStdBal
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem even_card_centralizer (hS : StandardSetting G L) :
    Even (Nat.card (centralizer (L : Set G))) :=
  hS.standard.2.1

theorem cyc_of_sylow (hS : StandardSetting G L) (S : Sylow 2 (centralizer (L : Set G)))
    (hc : IsCyclic (S : Subgroup (centralizer (L : Set G)))) : ∃ z, Cyc L (sylowSub S) z := by
  have h2 : 2 ∣ Nat.card (sylowSub S) := by
    rw [card_sylowSub]
    exact two_dvd_card_sylow (even_card_centralizer hS) S
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := sylowSub S) 2 h2
  refine ⟨(x : G), Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_, ?_, ?_, x.2⟩
  · have : (sylowSub S).relIndex (centralizer (L : Set G)) =
        (S : Subgroup (centralizer (L : Set G))).index := by
      unfold Subgroup.relIndex sylowSub
      rw [Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
    rw [this]
    exact S.not_dvd_index
  · exact (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).isCyclic.1 hc
  · rw [Subgroup.orderOf_coe]
    exact hx

theorem cent_le_normalizer (hS : StandardSetting G L) (d : Cyc L Q z) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
  (standard_involution_centralizer_normality hS.standard (d.le d.mem) d.order).1

theorem le_cent_single (hS : StandardSetting G L) (d : Cyc L Q z) :
    L ≤ centralizer ({z} : Set G) :=
  (standard_involution_centralizer_normality hS.standard (d.le d.mem) d.order).2.1

theorem mem_zpowers_of_two_pow (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {c : G}
    (hc : c ∈ centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) {k : ℕ}
    (hck : c ^ 2 ^ k = 1) : c ∈ zpowers z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer (L : Set G) ⊓ centralizer ({z} : Set G) with hM
  have hQz : zpowers z = Q := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 d.mem)
    (by rw [hQ2, Nat.card_zpowers, d.order])
  have hQM : Q ≤ M := by
    rw [← hQz, zpowers_le]
    exact ⟨d.le d.mem, mem_centralizer_singleton_iff.2 rfl⟩
  have hMK : M ≤ centralizer (L : Set G) := inf_le_left
  have hi : ¬ 2 ∣ (Q.subgroupOf M).index := by
    intro h2
    apply d.odd_index
    exact h2.trans (Dvd.intro _ (relIndex_mul_relIndex Q M (centralizer (L : Set G)) hQM hMK))
  have hQp : IsPGroup 2 (Q.subgroupOf M) := d.pgroup.of_equiv (subgroupOfEquivOfLe hQM).symm
  have hQn : (Q.subgroupOf M).Normal := by
    refine ⟨fun q hq m => ?_⟩
    have hq' : (q : G) ∈ zpowers z := by rw [hQz]; exact hq
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hq'
    have hmz : (m : G) * z = z * m := (mem_centralizer_singleton_iff.1 m.2.2)
    have hcomm : (m : G) * q = q * m := by
      rw [← hj]
      exact ((Commute.zpow_right (show Commute (m : G) z from hmz) j)).eq
    show (m : G) * q * (m : G)⁻¹ ∈ Q
    rw [hcomm, mul_inv_cancel_right]
    exact hq
  let S : Sylow 2 M := hQp.toSylow hi
  have hSeq : (S : Subgroup M) = Q.subgroupOf M := IsPGroup.toSylow_coe hQp hi
  have hSn : (S : Subgroup M).Normal := by rw [hSeq]; exact hQn
  let c' : M := ⟨c, hc⟩
  have hc'k : c' ^ 2 ^ k = 1 := Subtype.ext (by simpa using hck)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hc'k)
  have hcp : IsPGroup 2 (zpowers c') := IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have := hSn
  have hsup : IsPGroup 2 ((S : Subgroup M) ⊔ zpowers c' : Subgroup M) :=
    S.isPGroup'.to_sup_of_normal_left hcp
  have heq := S.is_maximal' hsup le_sup_left
  have hcS : c' ∈ (S : Subgroup M) := heq ▸ (le_sup_right (a := (S : Subgroup M)))
    (mem_zpowers c')
  rw [hSeq] at hcS
  have : c ∈ Q := hcS
  rw [← hQz] at this
  exact this

@[expose] noncomputable def evenAct (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) :
    Subgroup G :=
  ((alternatingGroup (Fin n)).comap (rho θ hn)).map (normalizer (L : Set G)).subtype

theorem mem_evenAct_iff (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {x : G}
    (hx : x ∈ normalizer (L : Set G)) :
    x ∈ evenAct θ hn ↔ rho θ hn ⟨x, hx⟩ ∈ alternatingGroup (Fin n) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem sup_le_evenAct (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) :
    L ⊔ centralizer (L : Set G) ≤ evenAct θ hn := by
  refine sup_le (fun l hl => ?_) (fun c hc => ?_)
  · have hlN : l ∈ normalizer (L : Set G) := Subgroup.le_normalizer hl
    rw [mem_evenAct_iff θ hn hlN, rho_of_mem θ hn ⟨l, hl⟩ hlN]
    exact (θ ⟨l, hl⟩).2
  · have hcN : c ∈ normalizer (L : Set G) := Subgroup.centralizer_le_normalizer (L : Set G) hc
    rw [mem_evenAct_iff θ hn hcN, (rho_eq_one_iff θ hn ⟨c, hcN⟩).2 hc]
    exact one_mem _

theorem mem_sup_of_rho_mem (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {c : G}
    (hcN : c ∈ normalizer (L : Set G)) (hc : rho θ hn ⟨c, hcN⟩ ∈ alternatingGroup (Fin n)) :
    c ∈ L ⊔ centralizer (L : Set G) := by
  set l : L := θ.symm ⟨rho θ hn ⟨c, hcN⟩, hc⟩ with hl
  have hlN : (l : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer l.2
  have hρl : rho θ hn ⟨l, hlN⟩ = rho θ hn ⟨c, hcN⟩ := by
    rw [rho_of_mem θ hn l hlN, hl, MulEquiv.apply_symm_apply]
  have hinv : (l : G)⁻¹ * c ∈ normalizer (L : Set G) := mul_mem (inv_mem hlN) hcN
  have h1 : rho θ hn ⟨(l : G)⁻¹ * c, hinv⟩ = 1 := by
    have : (⟨(l : G)⁻¹ * c, hinv⟩ : normalizer (L : Set G)) = ⟨l, hlN⟩⁻¹ * ⟨c, hcN⟩ := rfl
    rw [this, map_mul, map_inv, hρl, inv_mul_cancel]
  have h2 : (l : G)⁻¹ * c ∈ centralizer (L : Set G) := (rho_eq_one_iff θ hn _).1 h1
  have : c = (l : G) * ((l : G)⁻¹ * c) := by group
  rw [this]
  exact mul_mem (mem_sup_left l.2) (mem_sup_right h2)

theorem exists_outer_sq (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hO : ¬ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    ∃ u ∈ centralizer ({z} : Set G), u ∉ L ⊔ centralizer (L : Set G) ∧
      (u ^ 2 = 1 ∨ u ^ 2 = z) := by
  classical
  obtain ⟨c, hcC, hcO⟩ := Set.not_subset.1 hO
  have hCN := cent_le_normalizer hS d
  have hcN : c ∈ normalizer (L : Set G) := hCN hcC
  have hsgn : sign (rho θ hn ⟨c, hcN⟩) = -1 := by
    rcases Int.units_eq_one_or (sign (rho θ hn ⟨c, hcN⟩)) with h | h
    · exact absurd (mem_sup_of_rho_mem θ hn hcN (mem_alternatingGroup.2 h)) hcO
    · exact h
  let τ : Perm (Fin n) := swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
  have hτsgn : sign τ = -1 := sign_swap (by simp [Fin.ext_iff])
  have hmem : τ * (rho θ hn ⟨c, hcN⟩)⁻¹ ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, map_mul, map_inv, hτsgn, hsgn]
    decide
  let l : L := θ.symm ⟨τ * (rho θ hn ⟨c, hcN⟩)⁻¹, hmem⟩
  have hlN : (l : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer l.2
  have hρl : rho θ hn ⟨l, hlN⟩ = τ * (rho θ hn ⟨c, hcN⟩)⁻¹ := by
    rw [rho_of_mem θ hn l hlN]
    simp [l]
  have hlC : (l : G) ∈ centralizer ({z} : Set G) := le_cent_single hS d l.2
  set u₀ : G := (l : G) * c with hu₀
  have hu₀C : u₀ ∈ centralizer ({z} : Set G) := mul_mem hlC hcC
  have hu₀N : u₀ ∈ normalizer (L : Set G) := hCN hu₀C
  have hρu₀ : rho θ hn ⟨u₀, hu₀N⟩ = τ := by
    have : (⟨u₀, hu₀N⟩ : normalizer (L : Set G)) = ⟨l, hlN⟩ * ⟨c, hcN⟩ := rfl
    rw [this, map_mul, hρl, inv_mul_cancel_right]
  have hk0 : orderOf (u₀ ^ 2) ≠ 0 := (orderOf_pos (u₀ ^ 2)).ne'
  obtain ⟨a, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd hk0
  set u : G := u₀ ^ m with hudef
  have huC : u ∈ centralizer ({z} : Set G) := pow_mem hu₀C m
  have huN : u ∈ normalizer (L : Set G) := hCN huC
  have hρu : rho θ hn ⟨u, huN⟩ = τ := by
    have : (⟨u, huN⟩ : normalizer (L : Set G)) = ⟨u₀, hu₀N⟩ ^ m := rfl
    rw [this, map_pow, hρu₀]
    obtain ⟨j, rfl⟩ := hm
    have hτ2 : τ ^ 2 = 1 := by rw [sq]; exact swap_mul_self _ _
    rw [pow_succ, pow_mul, hτ2, one_pow, one_mul]
  refine ⟨u, huC, fun hu => ?_, ?_⟩
  ·
    have h1 := (mem_evenAct_iff θ hn huN).1 (sup_le_evenAct θ hn hu)
    rw [hρu, mem_alternatingGroup, hτsgn] at h1
    exact absurd h1 (by decide)
  ·
    have hu2N : u ^ 2 ∈ normalizer (L : Set G) := pow_mem huN 2
    have hu2K : u ^ 2 ∈ centralizer (L : Set G) := by
      have : (⟨u ^ 2, hu2N⟩ : normalizer (L : Set G)) = ⟨u, huN⟩ ^ 2 := rfl
      refine (rho_eq_one_iff θ hn ⟨u ^ 2, hu2N⟩).1 ?_
      rw [this, map_pow, hρu, sq, swap_mul_self]
    have hu2C : u ^ 2 ∈ centralizer ({z} : Set G) := pow_mem huC 2
    have hpow : (u ^ 2) ^ 2 ^ a = 1 := by
      rw [hudef, ← pow_mul, ← pow_mul, show m * (2 * 2 ^ a) = 2 * (2 ^ a * m) by ring, pow_mul,
        ← hk, pow_orderOf_eq_one]
    have hz := mem_zpowers_of_two_pow d hQ2 ⟨hu2K, hu2C⟩ hpow
    have hQz : zpowers z = Q := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 d.mem)
      (by rw [hQ2, Nat.card_zpowers, d.order])
    rw [hQz] at hz
    exact eq_one_or_eq_of_card_eq_two d hQ2 hz

end CFSG.OddStandard.AltStdCycTwo
