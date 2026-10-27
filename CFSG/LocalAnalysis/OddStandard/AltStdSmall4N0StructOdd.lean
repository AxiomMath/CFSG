module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructBase

public section

namespace CFSG.OddStandard.AltStdSmall4.N0

open Subgroup Equiv Equiv.Perm AltStdCycTwo
open scoped Pointwise

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

@[expose] def B0 (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) : Subgroup G :=
  E θ hn ⊔ zpowers z

@[expose] def C0 (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) : Subgroup G :=
  centralizer (B0 θ hn z : Set G)

theorem le_oddCoreOf {H O : Subgroup G} (hOH : O ≤ H) (hnorm : ∀ g ∈ H, ∀ o ∈ O, g * o * g⁻¹ ∈ O)
    (hodd : Odd (Nat.card O)) : O ≤ AltStdSec.oddCoreOf H := by
  have hN : (O.subgroupOf H).Normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    exact hnorm g g.2 x hx⟩
  have hc : Nat.card (O.subgroupOf H) = Nat.card O :=
    Nat.card_congr (subgroupOfEquivOfLe hOH).toEquiv
  have hle : O.subgroupOf H ≤ CFSG.oddCore H := le_sSup ⟨hN, hc ▸ hodd⟩
  intro x hx
  exact ⟨⟨x, hOH hx⟩, hle (by rw [mem_subgroupOf]; exact hx), rfl⟩

section Config

variable [Finite G] {Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
  (hn : 8 ≤ n) (c : Config G L Q n θ z)

include c

theorem mem_C0_iff (x : G) :
    x ∈ C0 θ hn z ↔ (∀ i, x * eps θ hn i = eps θ hn i * x) ∧ x * z = z * x := by
  rw [C0, mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun i => (h _ (eps_mem_B0 hn c i)).symm, (h _ (z_mem_B0 hn c)).symm⟩
  · rintro ⟨h1, h2⟩ y hy
    obtain ⟨i, rfl | rfl⟩ := (mem_B0_iff hn c y).1 hy
    · exact (h1 i).symm
    · rw [mul_assoc, ← h1 i, ← mul_assoc, ← h2, mul_assoc]

theorem mem_B0_iff' (x : G) :
    x ∈ B0 θ hn z ↔ ∃ i, x = eps θ hn i ∨ x = z * eps θ hn i := mem_B0_iff hn c x

theorem B0_comm_eps {x : G} (hx : x ∈ B0 θ hn z) (j : Fin 8) :
    x * eps θ hn j = eps θ hn j * x := by
  obtain ⟨i, rfl | rfl⟩ := (mem_B0_iff hn c x).1 hx
  · exact eps_comm θ hn i j
  · rw [mul_assoc, eps_comm θ hn i j, ← mul_assoc, ← eps_comm_z hn c, mul_assoc]

theorem B0_comm_z {x : G} (hx : x ∈ B0 θ hn z) : x * z = z * x := by
  obtain ⟨i, rfl | rfl⟩ := (mem_B0_iff hn c x).1 hx
  · exact eps_comm_z hn c i
  · rw [mul_assoc, eps_comm_z hn c, ← mul_assoc]

theorem B0_comm {x y : G} (hx : x ∈ B0 θ hn z) (hy : y ∈ B0 θ hn z) : x * y = y * x := by
  obtain ⟨j, rfl | rfl⟩ := (mem_B0_iff hn c y).1 hy
  · exact B0_comm_eps hn c hx j
  · rw [← mul_assoc, B0_comm_z hn c hx, mul_assoc, B0_comm_eps hn c hx j, mul_assoc]

theorem B0_sq {x : G} (hx : x ∈ B0 θ hn z) : x * x = 1 := by
  obtain ⟨i, rfl | rfl⟩ := (mem_B0_iff hn c x).1 hx
  · exact eps_mul_self θ hn i
  · rw [show z * eps θ hn i * (z * eps θ hn i) = z * (eps θ hn i * z) * eps θ hn i by group,
      eps_comm_z hn c, show z * (z * eps θ hn i) * eps θ hn i = (z * z) * (eps θ hn i *
        eps θ hn i) by group, c.ot.cyc.mul_self, eps_mul_self, one_mul]

theorem B0_isPGroup : IsPGroup 2 (B0 θ hn z) := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [sq]
  exact B0_sq hn c x.2

theorem B0_le_C0 : B0 θ hn z ≤ C0 θ hn z := by
  intro x hx
  rw [C0, mem_centralizer_iff]
  intro y hy
  exact B0_comm hn c hy hx

theorem C0_le_N0 : C0 θ hn z ≤ N0 θ hn z :=
  centralizer_le_normalizer _

theorem C0_le_D0 : C0 θ hn z ≤ D0 θ hn z := by
  intro x hx
  refine Subgroup.mem_inf.2 ⟨C0_le_N0 hn c hx, ?_⟩
  rw [mem_centralizer_E_iff]
  exact ((mem_C0_iff hn c x).1 hx).1

theorem B0_le_N0 : B0 θ hn z ≤ N0 θ hn z := le_normalizer

theorem B0_le_D0 : B0 θ hn z ≤ D0 θ hn z := (B0_le_C0 hn c).trans (C0_le_D0 hn c)

theorem conj_mem_C0 {g : G} (hg : g ∈ N0 θ hn z) {x : G} (hx : x ∈ C0 θ hn z) :
    g * x * g⁻¹ ∈ C0 θ hn z := by
  rw [C0, mem_centralizer_iff] at hx ⊢
  intro y hy
  have hy' : g⁻¹ * y * g ∈ B0 θ hn z := by
    have := (mem_normalizer_iff''.1 hg y).1 hy
    exact this
  have := hx _ hy'
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
    _ = g * x * g⁻¹ * y := by group

theorem mem_B0_of_two_pow {x : G} (hx : x ∈ C0 θ hn z) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x ∈ B0 θ hn z := by
  obtain ⟨hxE, hxz⟩ := (mem_C0_iff hn c x).1 hx
  have hxC : x ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hxz
  have hxN : x ∈ normalizer (L : Set G) := cent_le_normalizer c.ot.std c.ot.cyc hxC
  set π := AltStdBal.rho θ hn ⟨x, hxN⟩ with hπ
  have hcomm : ∀ e ∈ eBar hn, π * (e : Perm (Fin n)) = e * π := by
    intro e he
    obtain ⟨i, hi⟩ := (mem_E_iff θ hn _).1 (mem_E_of_mem_eBar θ hn he)
    have h1 := AltStdBal.rho_conj θ hn ⟨x, hxN⟩ e
    have h2 : (⟨x * ((θ.symm e : L) : G) * x⁻¹,
        (mem_normalizer_iff.mp hxN _).mp (θ.symm e).2⟩ : L) = θ.symm e := by
      apply Subtype.ext
      change x * ((θ.symm e : L) : G) * x⁻¹ = ((θ.symm e : L) : G)
      rw [hi, hxE i, mul_inv_cancel_right]
    rw [h2, MulEquiv.apply_symm_apply] at h1
    calc π * (e : Perm (Fin n)) = π * e * π⁻¹ * π := by group
      _ = e * π := by rw [h1]
  have hπk : π ^ 2 ^ k = 1 := by
    rw [hπ, ← map_pow]
    have : (⟨x, hxN⟩ : normalizer (L : Set G)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hev : n ≤ 9 ∨ π ∈ alternatingGroup (Fin n) := by
    rcases c.shape with h | ⟨h9, -⟩
    · exact Or.inr ((mem_evenAct_iff θ hn hxN).1 (sup_le_evenAct θ hn (h hxC)))
    · exact Or.inl h9
  obtain ⟨e, he, hπe⟩ := exists_eBar_eq_of_comm hn c.small hcomm hπk hev
  obtain ⟨i₀, hi₀⟩ := (mem_E_iff θ hn _).1 (mem_E_of_mem_eBar θ hn he)
  have heN : eps θ hn i₀ ∈ normalizer (L : Set G) := le_normalizer (eps_mem_L θ hn i₀)
  have hρe : AltStdBal.rho θ hn ⟨eps θ hn i₀, heN⟩ = π := by
    have h1 : (⟨eps θ hn i₀, heN⟩ : normalizer (L : Set G)) =
        ⟨((θ.symm e : L) : G), le_normalizer (θ.symm e).2⟩ := Subtype.ext hi₀.symm
    rw [h1, AltStdBal.rho_of_mem, MulEquiv.apply_symm_apply, hπe]
  have hyN : x * (eps θ hn i₀)⁻¹ ∈ normalizer (L : Set G) := mul_mem hxN (inv_mem heN)
  have hyK : x * (eps θ hn i₀)⁻¹ ∈ centralizer (L : Set G) := by
    refine (AltStdBal.rho_eq_one_iff θ hn ⟨_, hyN⟩).1 ?_
    have : (⟨x * (eps θ hn i₀)⁻¹, hyN⟩ : normalizer (L : Set G)) =
        ⟨x, hxN⟩ * ⟨eps θ hn i₀, heN⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, hρe, ← hπ, mul_inv_cancel]
  have hyz : x * (eps θ hn i₀)⁻¹ ∈ centralizer ({z} : Set G) :=
    mul_mem hxC (inv_mem (le_cent_single c.ot.std c.ot.cyc (eps_mem_L θ hn i₀)))
  have hcx : Commute x (eps θ hn i₀)⁻¹ := Commute.inv_right (hxE i₀)
  have hyk : (x * (eps θ hn i₀)⁻¹) ^ 2 ^ (k + 1) = 1 := by
    rw [hcx.mul_pow, eps_inv]
    have e1 : eps θ hn i₀ ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ', pow_mul, sq, eps_mul_self, one_pow]
    have e2 : x ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
    rw [e1, e2, one_mul]
  have hyZ := mem_zpowers_of_two_pow c.ot.cyc c.ot.card ⟨hyK, hyz⟩ hyk
  have hxeq : x = x * (eps θ hn i₀)⁻¹ * eps θ hn i₀ := by group
  rw [hxeq]
  exact mul_mem (mem_sup_right hyZ) (mem_sup_left (eps_mem_E θ hn i₀))

theorem exists_O0 : ∃ O : Subgroup G, O ≤ C0 θ hn z ∧ Odd (Nat.card O) ∧
    (∀ g ∈ N0 θ hn z, ∀ o ∈ O, g * o * g⁻¹ ∈ O) ∧
    ∃ a : ℕ, Nat.card (C0 θ hn z) = 2 ^ a * Nat.card O := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := C0 θ hn z with hC
  obtain ⟨S⟩ : Nonempty (Sylow 2 C) := inferInstance
  have hSB : ∀ x : C, x ∈ (S : Subgroup C) → (x : G) ∈ B0 θ hn z := by
    intro x hx
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
    have : (x : G) ^ 2 ^ k = 1 := by
      have := congrArg (fun y : (S : Subgroup C) => ((y : C) : G)) hk
      simpa using this
    exact mem_B0_of_two_pow hn c x.2 this
  have hP : normalizer (S : Set C) ≤ centralizer (S : Set C) := by
    intro g _
    rw [mem_centralizer_iff]
    intro h hh
    apply Subtype.ext
    have hgC : (g : G) ∈ centralizer (B0 θ hn z : Set G) := g.2
    rw [mem_centralizer_iff] at hgC
    exact hgC _ (hSB h hh)
  set K := (MonoidHom.transferSylow S hP).ker with hK
  have hcomp := MonoidHom.ker_transferSylow_isComplement' S hP
  have hKodd : ¬ 2 ∣ Nat.card K := MonoidHom.not_dvd_card_ker_transferSylow S hP
  refine ⟨K.map C.subtype, map_subtype_le K, ?_, ?_, ?_⟩
  · rw [card_map_of_injective C.subtype_injective]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hKodd)
  ·
    intro g hg o ho
    obtain ⟨k₀, hk₀, rfl⟩ := ho
    have hgo : g * (k₀ : G) * g⁻¹ ∈ C := conj_mem_C0 hn c hg k₀.2
    set y : C := ⟨g * (k₀ : G) * g⁻¹, hgo⟩ with hy
    obtain ⟨⟨⟨k, hk⟩, ⟨s, hs⟩⟩, hks⟩ := hcomp.2 y
    simp only at hks
    have hsk : s * k = k * s := by
      apply Subtype.ext
      have hkC : (k : G) ∈ centralizer (B0 θ hn z : Set G) := k.2
      rw [mem_centralizer_iff] at hkC
      exact (hkC _ (hSB s hs))
    have hord : orderOf y = orderOf (k₀ : C) := by
      have : orderOf (g * (k₀ : G) * g⁻¹) = orderOf (k₀ : G) := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe (k₀ : C)]
      exact this
    have hodd : Odd (orderOf (k₀ : C)) := by
      have h1 : orderOf (k₀ : C) ∣ Nat.card K := by
        have := orderOf_dvd_natCard (⟨k₀, hk₀⟩ : K)
        rwa [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hKodd)) h1
    set m := orderOf (k₀ : C) with hm
    have hym : y ^ m = 1 := by rw [← hord]; exact pow_orderOf_eq_one y
    rw [← hks] at hym
    have hcomm : Commute k s := hsk.symm
    rw [hcomm.mul_pow] at hym
    have hsm : s ^ m ∈ K := by
      rw [eq_inv_of_mul_eq_one_right hym]
      exact inv_mem (pow_mem hk m)
    have hsmS : s ^ m ∈ (S : Subgroup C) := pow_mem hs m
    have hs1 : s ^ m = 1 := by
      have := hcomp.1
      have hdisj : Disjoint K (S : Subgroup C) := by
        rw [disjoint_iff]
        exact MonoidHom.ker_transferSylow_disjoint S hP _ S.isPGroup' |>.eq_bot
      exact (Subgroup.disjoint_def.1 hdisj) hsm hsmS
    have hs2 : s * s = 1 := by
      apply Subtype.ext
      exact B0_sq hn c (hSB s hs)
    have hsone : s = 1 := by
      obtain ⟨j, hj⟩ := hodd
      rw [hj, pow_succ, pow_mul, sq, hs2, one_pow, one_mul] at hs1
      exact hs1
    rw [hsone, mul_one] at hks
    refine ⟨k, hk, ?_⟩
    rw [hks]
    rfl
  · obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
    refine ⟨a, ?_⟩
    rw [card_map_of_injective C.subtype_injective, ← hcomp.card_mul_card, ha, mul_comm]

end Config

end CFSG.OddStandard.AltStdSmall4.N0
