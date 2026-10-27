module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafGLR
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocal2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafM23Num
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafM23Transport

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint


theorem m23_sixtyfour_dvd {M : Type} [Group M] [Finite M] (hM : IsPGroup 2 M)
    (h : 64 ≤ Nat.card M) : 64 ∣ Nat.card M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hM
  rw [hn] at h ⊢
  have h6 : 6 ≤ n := by
    by_contra hlt
    have hlt' : n < 6 := by omega
    interval_cases n <;> norm_num at h
  simpa using Nat.pow_dvd_pow 2 h6

theorem localM23'_holds : LocalNoQ16Q16' (fun F _ => NativeSporadic.IsSporadic F .M23) := by
  intro F _ hF Y _ _ N _ hN hC t ht K K' hK hK' h2 h2' x hx y hy x' hx' y' hy' hxt hq
  obtain ⟨eN⟩ := hN
  obtain ⟨e⟩ := hF
  have e' : F ≃* NativeSporadic.M23 := e
  have hO : Nobq.OutTwoCyclic ↥N :=
    Nobq.OutTwoCyclic.of_mulEquiv (eN.trans e') Nobq.outTwoCyclic_M23
  obtain ⟨D, Ob, M, hDC, hObD, hMD, htM, hDc, hObc, hObodd, hD2, hM2, hM64⟩ :=
    Q16Q16.local_reduction N hC hO hK hK' h2 h2' hx hy hx' hy' hq hxt
  have htN : t ∈ N := (Subgroup.mem_inf.1 (hDC (hMD htM))).1
  obtain ⟨hperfC, hcardC⟩ := m23_centralizer_perfect_card N eN e' htN ht
  haveI := hperfC
  set C : Subgroup Y := N ⊓ Subgroup.centralizer ({t} : Set Y)
  have hObC : Ob ≤ C := hObD.trans hDC
  haveI : (D.subgroupOf C).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hDc (g : Y) g.2 (n : Y) hn⟩
  haveI : (Ob.subgroupOf C).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hObc (g : Y) g.2 (n : Y) hn⟩
  have hD64 : 64 ∣ Nat.card (D.subgroupOf C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
    exact (m23_sixtyfour_dvd hM2 hM64).trans (Subgroup.card_dvd_of_le hMD)
  have hOodd : Odd (Nat.card (Ob.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hObC).toEquiv]
    exact hObodd
  have hDO : ∀ g ∈ D.subgroupOf C, ∃ k : ℕ, g ^ 2 ^ k ∈ Ob.subgroupOf C := by
    intro g hg
    obtain ⟨k, hk⟩ := hD2 (g : Y) (Subgroup.mem_subgroupOf.1 hg)
    refine ⟨k, Subgroup.mem_subgroupOf.2 ?_⟩
    simpa using hk
  exact m23_perfect_core hcardC (D.subgroupOf C) (Ob.subgroupOf C) hD64 hOodd hDO

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
