module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13CD1

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem comm_of_sq_eq_one {M : Type*} [Group M] {p p' : M} (hp : p * p = 1)
    (hp' : p' * p' = 1) (h : (p * p') * (p * p') = 1) : p * p' = p' * p := by
  have h1 : (p * p')⁻¹ = p * p' := inv_eq_of_mul_eq_one_right h
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hp', inv_eq_of_mul_eq_one_right hp] at h1
  exact h1.symm

theorem eq_prod_of_card {K : Type*} [Group K] [Finite K] {A : Subgroup (K × K)}
    (hcomm : ∀ p ∈ A, ∀ p' ∈ A, p * p' = p' * p) (hsq : ∀ p ∈ A, p * p = 1)
    (hEA : ∀ B : Subgroup K, (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ a ∈ B, a * a = 1) →
      Nat.card ↥B ≤ 16)
    (hcard : Nat.card ↥A = 256) :
    A = (A.map (MonoidHom.fst K K)).prod (A.map (MonoidHom.snd K K)) := by
  have h1 : Nat.card ↥(A.map (MonoidHom.fst K K)) ≤ 16 := by
    apply hEA
    · intro a ha b hb
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.1 hb
      exact congrArg Prod.fst (hcomm p hp p' hp')
    · intro a ha
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ha
      exact congrArg Prod.fst (hsq p hp)
  have h2 : Nat.card ↥(A.map (MonoidHom.snd K K)) ≤ 16 := by
    apply hEA
    · intro a ha b hb
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.1 hb
      exact congrArg Prod.snd (hcomm p hp p' hp')
    · intro a ha
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ha
      exact congrArg Prod.snd (hsq p hp)
  have hle : A ≤ (A.map (MonoidHom.fst K K)).prod (A.map (MonoidHom.snd K K)) := fun p hp =>
    Subgroup.mem_prod.2 ⟨Subgroup.mem_map.2 ⟨p, hp, rfl⟩, Subgroup.mem_map.2 ⟨p, hp, rfl⟩⟩
  have hprod : Nat.card ↥((A.map (MonoidHom.fst K K)).prod (A.map (MonoidHom.snd K K))) =
      Nat.card ↥(A.map (MonoidHom.fst K K)) * Nat.card ↥(A.map (MonoidHom.snd K K)) := by
    rw [Nat.card_congr ((A.map (MonoidHom.fst K K)).prodEquiv (A.map (MonoidHom.snd K K))).toEquiv,
      Nat.card_prod]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hprod, hcard]
  exact (Nat.mul_le_mul h1 h2).trans (by norm_num)

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

theorem card_Rhat_of (Y : Subgroup G) (hYN : Y ≤ c.N1) (hYK : Y ⊓ c.KR ≤ c.Zs)
    (hZY : c.Zs ≤ Y) (hY : Nat.card ↥Y = 1024) : Nat.card ↥(c.Rhat Y) = 256 := by
  let φ : ↥(Y.subgroupOf c.N1) →* MulAut ↥E × MulAut ↥E :=
    c.rho.comp (Y.subgroupOf c.N1).subtype
  let ι : ↥(Y.subgroupOf c.N1) →* G := c.N1.subtype.comp (Y.subgroupOf c.N1).subtype
  have hrange : φ.range = c.Rhat Y := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact c.mem_Rhat.2 ⟨x.1, Subgroup.mem_subgroupOf.1 x.2, rfl⟩
    · intro hp
      obtain ⟨r, hr, rfl⟩ := c.mem_Rhat.1 hp
      exact ⟨⟨r, Subgroup.mem_subgroupOf.2 hr⟩, rfl⟩
  have hι : Function.Injective ι := fun a b h => Subtype.ext (Subtype.ext h)
  have hkerZ : φ.ker.map ι = c.Zs := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxK : ((x.1 : c.N1) : G) ∈ c.KR := c.mem_KR.2 ⟨(x.1 : c.N1).2, MonoidHom.mem_ker.1 hx⟩
      exact hYK ⟨Subgroup.mem_subgroupOf.1 x.2, hxK⟩
    · intro hg
      refine ⟨⟨⟨g, c.Zs_le_N1 hg⟩, Subgroup.mem_subgroupOf.2 (hZY hg)⟩, ?_, rfl⟩
      exact MonoidHom.mem_ker.2 (c.rho_Zs hg)
  have hcardker : Nat.card ↥φ.ker = 4 := by
    have h4 : Nat.card ↥(φ.ker.map ι) = Nat.card ↥φ.ker := Subgroup.card_map_of_injective hι
    rw [← h4, hkerZ]
    exact c.h.card_Zs c.hα
  have hcardHn : Nat.card ↥(Y.subgroupOf c.N1) = 1024 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv]
    exact hY
  have hfin : Nat.card ↥φ.range = 256 := by
    have hmul := Subgroup.card_ker_mul_card_range φ
    rw [hcardker, hcardHn] at hmul
    omega
  rw [← hrange]
  exact hfin

namespace IsRs

variable {c}
variable {Rs : Subgroup G} (hR : c.IsRs Rs)

include hR

theorem normalizer_le_Nc {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (hD : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ π a = π b)
    (hEA : ∀ A : Subgroup (MulAut ↥E), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a * a = 1) → Nat.card ↥A ≤ 16)
    {n : G} (hn : n ∈ normalizer (Rs : Set G)) : n ∈ c.Nc := by
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = c.Qs.map (MulAut.conj n).toMonoidHom := ⟨_, rfl⟩
  have hmemY : ∀ y, y ∈ Y ↔ ∃ q ∈ c.Qs, n * q * n⁻¹ = y := by
    intro y
    rw [hY, Subgroup.mem_map]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hcardY : Nat.card ↥Y = 1024 := by
    rw [hY, Subgroup.card_map_of_injective (f := (MulAut.conj n).toMonoidHom)
      (MulAut.conj n).injective]
    exact c.card_Qs
  have hZY : c.Zs ≤ Y := by
    intro x hx
    rw [hmemY]
    exact ⟨n⁻¹ * x * n, c.Zs_le_Qs (hR.conj_inv_Zs hn hx), by group⟩
  have hYR : Y ≤ Rs ⊓ c.N1 := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := (hmemY _).1 hy
    have hqR : q ∈ Rs := hR.Qs_le hq
    have hyR : n * q * n⁻¹ ∈ Rs := (mem_normalizer_iff.1 hn q).1 hqR
    refine ⟨hyR, c.mem_N1.2 ⟨hR.le_Nc hyR, ?_⟩⟩
    have ha : n⁻¹ * α * n ∈ c.Zs := hR.conj_inv_Zs hn c.alpha_mem_Zs
    have hqa : q * (n⁻¹ * α * n) = (n⁻¹ * α * n) * q := (c.Zs_comm_Qs ha hq).symm
    calc n * q * n⁻¹ * α * (n * q * n⁻¹)⁻¹
        = n * (q * (n⁻¹ * α * n) * q⁻¹) * n⁻¹ := by group
      _ = n * ((n⁻¹ * α * n) * q * q⁻¹) * n⁻¹ := by rw [hqa]
      _ = α := by group
  have hYN : Y ≤ c.N1 := hYR.trans inf_le_right
  have hYsq : ∀ y ∈ Y, y * y ∈ c.Zs := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := (hmemY _).1 hy
    have h1 : q * q ∈ c.Zs := by
      rw [c.mem_Zs]
      exact c.h.QF_sq c.hα hq
    have h2 := hR.normalizer_Zs hn h1
    have e : n * q * n⁻¹ * (n * q * n⁻¹) = n * (q * q) * n⁻¹ := by group
    rw [e]
    exact h2
  have hsqA : ∀ p ∈ c.Rhat Y, p * p = 1 := by
    intro p hp
    obtain ⟨r, hrY, rfl⟩ := c.mem_Rhat.1 hp
    rw [← map_mul]
    have e : r * r = (⟨(r : G) * (r : G), c.Zs_le_N1 (hYsq _ hrY)⟩ : c.N1) := Subtype.ext rfl
    rw [e, c.rho_Zs (hYsq _ hrY)]
  have hcommA : ∀ p ∈ c.Rhat Y, ∀ p' ∈ c.Rhat Y, p * p' = p' * p := fun p hp p' hp' =>
    comm_of_sq_eq_one (hsqA p hp) (hsqA p' hp') (hsqA _ (mul_mem hp hp'))
  have hYK : Y ⊓ c.KR ≤ c.Zs := fun y hy => hR.R_inf_KR_le ⟨hYR hy.1, hy.2⟩
  have hcardA : Nat.card ↥(c.Rhat Y) = 256 := c.card_Rhat_of Y hYN hYK hZY hcardY
  have hEq := eq_prod_of_card hcommA hsqA hEA hcardA
  have hInn : ∀ p ∈ c.Rhat Y, p.1 ∈ innAutE E ∧ p.2 ∈ innAutE E := by
    intro p hp
    have hp1 : (p.1, (1 : MulAut ↥E)) ∈ c.Rhat Y := by
      rw [hEq]
      exact Subgroup.mem_prod.2 ⟨Subgroup.mem_map.2 ⟨p, hp, rfl⟩, one_mem _⟩
    have hp2 : ((1 : MulAut ↥E), p.2) ∈ c.Rhat Y := by
      rw [hEq]
      exact Subgroup.mem_prod.2 ⟨one_mem _, Subgroup.mem_map.2 ⟨p, hp, rfl⟩⟩
    have hD1 : π p.1 = π 1 := (hD p.1 1).1 (c.Rhat_le_range Y hp1)
    have hD2 : π 1 = π p.2 := (hD 1 p.2).1 (c.Rhat_le_range Y hp2)
    refine ⟨(hπ.ker _).1 ?_, (hπ.ker _).1 ?_⟩
    · rw [hD1, map_one]
    · rw [← hD2, map_one]
  have hYQ : Y ≤ c.Qs := by
    intro y hy
    have hyN : y ∈ c.N1 := hYN hy
    have hp : c.rho ⟨y, hyN⟩ ∈ c.Rhat Y := c.mem_Rhat.2 ⟨⟨y, hyN⟩, hy, rfl⟩
    obtain ⟨e1, he1⟩ := MonoidHom.mem_range.1 (hInn _ hp).1
    obtain ⟨e2, he2⟩ := MonoidHom.mem_range.1 (hInn _ hp).2
    obtain ⟨q, hq, hρq⟩ := c.exists_rho_Qs e1 e2
    have hqN : q ∈ c.N1 := c.Qs_le_N1 hq
    have hρ : c.rho ⟨q, hqN⟩ = c.rho ⟨y, hyN⟩ := hρq.trans (Prod.ext he1 he2)
    have hwK : q⁻¹ * y ∈ c.KR := by
      refine c.mem_KR.2 ⟨mul_mem (inv_mem hqN) hyN, ?_⟩
      have e : (⟨q⁻¹ * y, mul_mem (inv_mem hqN) hyN⟩ : c.N1) =
          (⟨q, hqN⟩ : c.N1)⁻¹ * ⟨y, hyN⟩ := Subtype.ext rfl
      rw [e, map_mul, map_inv, hρ, inv_mul_cancel]
    have hwRN : q⁻¹ * y ∈ Rs ⊓ c.N1 :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hR.Qs_le hq)) (hYR hy).1, mul_mem (inv_mem hqN) hyN⟩
    have hwZ : q⁻¹ * y ∈ c.Zs := hR.R_inf_KR_le ⟨hwRN, hwK⟩
    have h := mul_mem hq (c.Zs_le_Qs hwZ)
    rwa [mul_inv_cancel_left] at h
  have hYeq : Y = c.Qs :=
    Subgroup.eq_of_le_of_card_ge hYQ (le_of_eq (by rw [hcardY, c.card_Qs]))
  rw [c.mem_Nc]
  intro q
  constructor
  · intro hq
    have h : n * q * n⁻¹ ∈ Y := (hmemY _).2 ⟨q, hq, rfl⟩
    rwa [hYeq] at h
  · intro hq
    rw [← hYeq] at hq
    obtain ⟨q', hq', hq'eq⟩ := (hmemY _).1 hq
    have hqq : q' = q := mul_left_cancel (mul_right_cancel hq'eq)
    rwa [hqq] at hq'

theorem isSylow {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (hD : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ π a = π b)
    (hEA : ∀ A : Subgroup (MulAut ↥E), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a * a = 1) → Nat.card ↥A ≤ 16) :
    ∀ P : Subgroup G, IsPGroup 2 P → Rs ≤ P → P = Rs := by
  intro P hP hRP
  by_contra hne
  have hlt : Rs < P := lt_of_le_of_ne hRP (Ne.symm hne)
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have hRsP : Rs.subgroupOf P ≠ ⊤ := by
    intro htop
    apply hne
    refine le_antisymm ?_ hRP
    intro y hy
    have hmem : (⟨y, hy⟩ : P) ∈ Rs.subgroupOf P := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem
  have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent
  obtain ⟨x, hxN, hxR⟩ := IsConcreteLE.exists_of_lt
    (hnc (Rs.subgroupOf P) (lt_top_iff_ne_top.2 hRsP))
  have hxnorm : (x : G) ∈ normalizer (Rs : Set G) := by
    have h1 : x ∈ (normalizer (Rs : Set G)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq hRP]
      exact hxN
    exact Subgroup.mem_subgroupOf.1 h1
  have hxR' : (x : G) ∉ Rs := fun h => hxR (Subgroup.mem_subgroupOf.2 h)
  have hxNc : (x : G) ∈ c.Nc := hR.normalizer_le_Nc hπ hD hEA hxnorm
  have hMP : Rs ⊔ zpowers (x : G) ≤ P := sup_le hRP (zpowers_le.2 x.2)
  have hMp : IsPGroup 2 (Rs ⊔ zpowers (x : G) : Subgroup G) := hP.to_le hMP
  have hMN : (Rs ⊔ zpowers (x : G) : Subgroup G) ≤ c.Nc :=
    sup_le hR.le_Nc (zpowers_le.2 hxNc)
  have hMeq : Rs ⊔ zpowers (x : G) = Rs := hR.max _ hMp hMN le_sup_left
  have hxM : (x : G) ∈ Rs ⊔ zpowers (x : G) := mem_sup_right (mem_zpowers _)
  rw [hMeq] at hxM
  exact hxR' hxM

end IsRs

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
