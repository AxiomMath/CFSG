module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigPiA

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Core

variable {G : Type} [Group G] [Finite G]

theorem exists_piData {r : ℕ} {Λ Q A' : Subgroup G} {d : G} (hQΛ : Q ≤ Λ) (hdΛ : d ∈ Λ)
    (hQ2 : IsPGroup 2 ↥Q) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hd : quatInvolution r e = d)
    (hA'N : A' ≤ Subgroup.normalizer (Λ : Set G)) (hA'2 : IsPGroup 2 ↥A')
    (hA'Q : ∀ x ∈ A', ∀ y ∈ Q, x * y * x⁻¹ ∈ Q) :
    ∃ (Qb : Subgroup (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))
      (eb : ↥Qb ≃* QuaternionGroup (2 ^ (r - 2)))
      (H : Subgroup (MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))),
      IsPGroup 2 ↥H ∧ (∀ β ∈ H, ∀ x ∈ Qb, β x ∈ Qb) ∧
        quatInvolution r eb = QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ) ∧
        ∀ (x : G) (hx : x ∈ A'), actAut Λ ⟨x, hA'N hx⟩ ∈ H := by
  let O := classicalInvolutionOddCore ↥Λ
  let ι : ↥(Q.subgroupOf Λ) →* ↥Λ ⧸ O := (QuotientGroup.mk' O).comp (Q.subgroupOf Λ).subtype
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyO : (y : ↥Λ) ∈ O := (QuotientGroup.eq_one_iff _).mp hy
    have hyQ : (((y : ↥Λ) : G)) ∈ Q := Subgroup.mem_subgroupOf.mp y.2
    obtain ⟨j, hj⟩ := hQ2 ⟨_, hyQ⟩
    have hj' : ((y : ↥Λ) : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h1 : ((y : ↥Λ) : G) = 1 :=
      eq_one_of_mem_oddCoreOf (mem_oddCoreOf_iff.mpr ⟨(y : ↥Λ).2, hyO⟩) hj'
    exact Subtype.ext (Subtype.ext h1)
  let Qb : Subgroup (↥Λ ⧸ O) := ι.range
  let eb : ↥Qb ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (MonoidHom.ofInjective hι).symm.trans ((Subgroup.subgroupOfEquivOfLe hQΛ).trans e)
  let ρ : ↥A' →* MulAut (↥Λ ⧸ O) := (actAut Λ).comp (Subgroup.inclusion hA'N)
  let H : Subgroup (MulAut (↥Λ ⧸ O)) := ρ.range
  refine ⟨Qb, eb, H, ?_, ?_, ?_, ?_⟩
  · show IsPGroup 2 ↥(ρ.range)
    exact IsPGroup.of_surjective hA'2 ρ.rangeRestrict ρ.rangeRestrict_surjective
  · rintro β hβ x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hβ
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hx
    have hqQ : ((q : ↥Λ) : G) ∈ Q := Subgroup.mem_subgroupOf.mp q.2
    have haQ : a.val * ((q : ↥Λ) : G) * a.val⁻¹ ∈ Q := hA'Q a.val a.2 _ hqQ
    have hwΛ : a.val * ((q : ↥Λ) : G) * a.val⁻¹ ∈ Λ := hQΛ haQ
    refine MonoidHom.mem_range.mpr
      ⟨⟨⟨a.val * ((q : ↥Λ) : G) * a.val⁻¹, hwΛ⟩, Subgroup.mem_subgroupOf.mpr haQ⟩, ?_⟩
    change QuotientGroup.mk (⟨a.val * ((q : ↥Λ) : G) * a.val⁻¹, hwΛ⟩ : ↥Λ) =
      actAut Λ ⟨a.val, hA'N a.2⟩ (QuotientGroup.mk (q : ↥Λ))
    rw [actAut_mk]
    congr 1
  · change ((eb.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) :
        ↥Qb) : ↥Λ ⧸ O) = QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ)
    change ι ((Subgroup.subgroupOfEquivOfLe hQΛ).symm
      (e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))))) = _
    change QuotientGroup.mk _ = _
    congr 1
    exact Subtype.ext hd
  · intro x hx
    exact MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩

private theorem quatInvolution_mem_of_eq {r : ℕ} {Λ Q : Subgroup G} {d : G} (hQΛ : Q ≤ Λ)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hd : quatInvolution r e = d) : d ∈ Λ :=
  hd ▸ hQΛ (e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))))).2

theorem pi_cyc_of_concl {r E : ℕ} {Λ Q A' : Subgroup G} {d : G} (hQΛ : Q ≤ Λ)
    (hQ2 : IsPGroup 2 ↥Q) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hd : quatInvolution r e = d)
    (hA'N : A' ≤ Subgroup.normalizer (Λ : Set G)) (hA'2 : IsPGroup 2 ↥A')
    (hA'Q : ∀ x ∈ A', ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    (hPi : PiCycConcl r E (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))
    {x : G} (hx : x ∈ A') {K : ℕ} (hK : E < K) (h1 : ActsTriv Λ (x ^ 2 ^ K))
    (h2 : ¬ ActsTriv Λ (x ^ 2 ^ (K - 1))) :
    ActsLike Λ (x ^ 2 ^ (K - 1)) d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdΛ : d ∈ Λ := quatInvolution_mem_of_eq hQΛ e hd
  obtain ⟨Qb, eb, H, hH2, hHN, hquat, hmem⟩ :=
    exists_piData hQΛ hdΛ hQ2 e hd hA'N hA'2 hA'Q
  have hxN : x ∈ Subgroup.normalizer (Λ : Set G) := hA'N hx
  let β : MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) := actAut Λ ⟨x, hxN⟩
  have hβmem : β ∈ H := hmem x hx
  have hβK : β ^ 2 ^ K = 1 := by
    rw [← actAut_pow hxN (2 ^ K)]
    exact (actAut_eq_one_iff (Subgroup.pow_mem _ hxN (2 ^ K))).mpr h1
  have hβnot : β ^ 2 ^ (K - 1) ≠ 1 := by
    intro h
    apply h2
    have h' : actAut Λ ⟨x ^ 2 ^ (K - 1), Subgroup.pow_mem _ hxN (2 ^ (K - 1))⟩ = 1 := by
      rw [actAut_pow hxN (2 ^ (K - 1))]
      exact h
    exact (actAut_eq_one_iff (Subgroup.pow_mem _ hxN (2 ^ (K - 1)))).mp h'
  have hK1 : 1 ≤ K := by omega
  have hord : orderOf β = 2 ^ K := by
    have hfin : β ^ 2 ^ (K - 1 + 1) = 1 := by rwa [← Nat.sub_add_cancel hK1] at hβK
    have := orderOf_eq_prime_pow (n := K - 1) hβnot hfin
    rwa [Nat.sub_add_cancel hK1] at this
  have ho : 2 ^ E < orderOf β := by
    rw [hord]
    exact Nat.pow_lt_pow_right (by norm_num) hK
  have hkey := hPi Qb eb H hH2 hHN β hβmem ho
  have hhalf : orderOf β / 2 = 2 ^ (K - 1) := by
    rw [hord]
    rw [show 2 ^ K = 2 * 2 ^ (K - 1) by
      rw [← pow_succ', Nat.sub_add_cancel hK1]]
    exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)
  rw [hhalf, hquat] at hkey
  exact (actAut_eq_conj_iff (Subgroup.pow_mem _ hxN (2 ^ (K - 1))) hdΛ).mp
    ((actAut_pow hxN (2 ^ (K - 1))).trans hkey)

theorem pi_quat_of_concl {r : ℕ} {Λ Q A' : Subgroup G} {d : G} (hQΛ : Q ≤ Λ)
    (hQ2 : IsPGroup 2 ↥Q) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hd : quatInvolution r e = d)
    (hA'N : A' ≤ Subgroup.normalizer (Λ : Set G)) (hA'2 : IsPGroup 2 ↥A')
    (hA'Q : ∀ x ∈ A', ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    (hPi : PiQuatConcl r (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))
    {m : ℕ} (hm : 1 ≤ m) {B : Subgroup G} (hBA' : B ≤ A') (eB : ↥B ≃* QuaternionGroup (2 ^ m))
    (hinj : ∀ y ∈ B, ActsTriv Λ y → y = 1) :
    ActsLike Λ ((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B) : G) d := by
  have hdΛ : d ∈ Λ := quatInvolution_mem_of_eq hQΛ e hd
  obtain ⟨Qb, eb, H, hH2, hHN, hquat, hmem⟩ :=
    exists_piData hQΛ hdΛ hQ2 e hd hA'N hA'2 hA'Q
  let ρB : ↥B →* MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) :=
    (actAut Λ).comp (Subgroup.inclusion (hBA'.trans hA'N))
  have hρB : Function.Injective ρB := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hbN : (b : G) ∈ Subgroup.normalizer (Λ : Set G) := (hBA'.trans hA'N) b.2
    have htriv : ActsTriv Λ (b : G) := (actAut_eq_one_iff hbN).mp hb
    exact Subtype.ext (hinj b.val b.2 htriv)
  let Bb : Subgroup (MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) := ρB.range
  have hBbH : Bb ≤ H := by
    intro γ hγ
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hγ
    exact hmem b.val (hBA' b.2)
  let eBb : ↥Bb ≃* QuaternionGroup (2 ^ m) := (MonoidHom.ofInjective hρB).symm.trans eB
  have hkey := hPi Qb eb H hH2 hHN m hm Bb hBbH eBb
  rw [hquat] at hkey
  have hcoe : ((eBb.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥Bb) :
      MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) =
      actAut Λ ⟨((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B) : G),
        hA'N (hBA' (eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)))).2)⟩ := rfl
  exact (actAut_eq_conj_iff _ hdΛ).mp (hcoe ▸ hkey)

theorem pi4_of_concl {r : ℕ} {Λ Q A' : Subgroup G} {d : G} (hQΛ : Q ≤ Λ)
    (hQ2 : IsPGroup 2 ↥Q) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hd : quatInvolution r e = d)
    (hA'N : A' ≤ Subgroup.normalizer (Λ : Set G)) (hA'2 : IsPGroup 2 ↥A')
    (hA'Q : ∀ x ∈ A', ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    (hPi : Pi4Concl r (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))
    {x : G} (hx : x ∈ A') {K : ℕ} (hK : 2 ≤ K) (h1 : ActsTriv Λ (x ^ 2 ^ K))
    (h2 : ¬ ActsTriv Λ (x ^ 2 ^ (K - 1))) :
    ActsLike Λ (x ^ 2 ^ (K - 1)) d ∨ ¬ InnerModOdd Λ (x ^ 2 ^ (K - 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdΛ : d ∈ Λ := quatInvolution_mem_of_eq hQΛ e hd
  obtain ⟨Qb, eb, H, hH2, hHN, hquat, hmem⟩ :=
    exists_piData hQΛ hdΛ hQ2 e hd hA'N hA'2 hA'Q
  have hxN : x ∈ Subgroup.normalizer (Λ : Set G) := hA'N hx
  let β : MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) := actAut Λ ⟨x, hxN⟩
  have hβmem : β ∈ H := hmem x hx
  have hβK : β ^ 2 ^ K = 1 := by
    rw [← actAut_pow hxN (2 ^ K)]
    exact (actAut_eq_one_iff (Subgroup.pow_mem _ hxN (2 ^ K))).mpr h1
  have hβnot : β ^ 2 ^ (K - 1) ≠ 1 := by
    intro h
    apply h2
    have h' : actAut Λ ⟨x ^ 2 ^ (K - 1), Subgroup.pow_mem _ hxN (2 ^ (K - 1))⟩ = 1 := by
      rw [actAut_pow hxN (2 ^ (K - 1))]
      exact h
    exact (actAut_eq_one_iff (Subgroup.pow_mem _ hxN (2 ^ (K - 1)))).mp h'
  have hK1 : 1 ≤ K := by omega
  have hord : orderOf β = 2 ^ K := by
    have hfin : β ^ 2 ^ (K - 1 + 1) = 1 := by rwa [← Nat.sub_add_cancel hK1] at hβK
    have := orderOf_eq_prime_pow (n := K - 1) hβnot hfin
    rwa [Nat.sub_add_cancel hK1] at this
  have hkey := hPi Qb eb H hH2 hHN β hβmem K hK hord
  rw [hquat] at hkey
  rcases hkey with h | h
  · left
    exact (actAut_eq_conj_iff (Subgroup.pow_mem _ hxN (2 ^ (K - 1))) hdΛ).mp
      ((actAut_pow hxN (2 ^ (K - 1))).trans h)
  · right
    intro hinner
    exact h ((actAut_pow hxN (2 ^ (K - 1))) ▸
      (actAut_mem_innGrp_iff (Subgroup.pow_mem _ hxN (2 ^ (K - 1)))).mpr hinner)

theorem pi4_involution_of_concl {r : ℕ} {Λ Q A' : Subgroup G} {d : G} (hQΛ : Q ≤ Λ)
    (hQ2 : IsPGroup 2 ↥Q) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hd : quatInvolution r e = d)
    (hA'N : A' ≤ Subgroup.normalizer (Λ : Set G)) (hA'2 : IsPGroup 2 ↥A')
    (hA'Q : ∀ x ∈ A', ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    (hPi : Pi4Concl r (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))
    {x : G} (hx : x ∈ A') {L : ℕ} (hL : 2 ≤ L) (hxL : x ^ 2 ^ L = 1) :
    ActsTriv Λ (x ^ 2 ^ (L - 1)) ∨ ActsLike Λ (x ^ 2 ^ (L - 1)) d ∨
      ¬ InnerModOdd Λ (x ^ 2 ^ (L - 1)) := by
  classical
  have hxN : x ∈ Subgroup.normalizer (Λ : Set G) := hA'N hx
  have htriv1 : ActsTriv Λ (1 : G) := by intro z hz; simp
  have hLtriv : ActsTriv Λ (x ^ 2 ^ L) := by rw [hxL]; exact htriv1
  have hex : ∃ j : ℕ, ActsTriv Λ (x ^ 2 ^ j) := ⟨L, hLtriv⟩
  let j : ℕ := Nat.find hex
  have hj : ActsTriv Λ (x ^ 2 ^ j) := Nat.find_spec hex
  have hjmin : ∀ k < j, ¬ ActsTriv Λ (x ^ 2 ^ k) := fun k hk => Nat.find_min hex hk
  have hjle : j ≤ L := Nat.find_min' hex hLtriv
  by_cases hjl : j < L
  · left
    have he : (x ^ 2 ^ j) ^ 2 ^ (L - 1 - j) = x ^ 2 ^ (L - 1) := by
      rw [← pow_mul, ← pow_add]
      rw [show j + (L - 1 - j) = L - 1 by omega]
    exact he ▸ actsTriv_pow (Subgroup.pow_mem _ hxN (2 ^ j)) hj (2 ^ (L - 1 - j))
  · right
    have hjL : j = L := by omega
    exact pi4_of_concl (K := L) hQΛ hQ2 e hd hA'N hA'2 hA'Q hPi hx hL
      (hjL ▸ hj) (hjmin (L - 1) (by omega))

end Core

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
