module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Str
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModRes
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Ker
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

variable {G : Type} [Group G] {E B : Subgroup G} {u : MulAut ↥E}
  {A H P : Subgroup (MulAut ↥E)}

theorem HCtx.resHom_apply_eq_self_iff (S : HCtx E B u A H) {a : MulAut ↥E} (ha : a ∈ A)
    (b : ↥B) :
    (T84Mod.resHom S.hBE u S.fix A S.A_comm ⟨a, ha⟩) b = b ↔
      a (T84Mod.embB S.hBE b) = T84Mod.embB S.hBE b := by
  have hres : T84Mod.resHom S.hBE u S.fix A S.A_comm ⟨a, ha⟩ =
      T84Mod.resB S.hBE u S.fix a (S.A_comm a ha) :=
    T84Mod.resHom_apply S.hBE u S.fix A S.A_comm ⟨a, ha⟩
  have hemb : Function.Injective (T84Mod.embB S.hBE) :=
    fun x y h => Subtype.ext (congrArg (fun e : ↥E => (e : G)) h)
  constructor
  · intro h
    have h1 : T84Mod.resB S.hBE u S.fix a (S.A_comm a ha) b = b := by
      rwa [hres] at h
    have h2 := T84Mod.embB_resB S.hBE u S.fix a (S.A_comm a ha) b
    rw [h1] at h2
    exact h2.symm
  · intro h
    have h2 := T84Mod.embB_resB S.hBE u S.fix a (S.A_comm a ha) b
    have h3 : T84Mod.embB S.hBE
        (T84Mod.resB S.hBE u S.fix a (S.A_comm a ha) b) = T84Mod.embB S.hBE b := by
      rw [h2, h]
    have h4 := hemb h3
    simpa [hres] using h4

theorem HCtx.card_fixB_of_inv (hInv : Sec8T84FactInv) (S : HCtx E B u A H) {a : MulAut ↥E}
    (ha : a ∈ A) (h1 : a ≠ 1) (h2 : a * a = 1) :
    Nat.card {e : ↥E // (e : G) ∈ B ∧ a e = e} = 4 := by
  classical
  let ρ : ↥A →* MulAut ↥B := T84Mod.resHom S.hBE u S.fix A S.A_comm
  have hinj : Function.Injective ρ :=
    T84Mod.resHom_injective S.hBE u S.fix A S.A_comm S.A_faith
  let H' : Subgroup (MulAut ↥B) := ρ.range
  have hH' : Nonempty (↥H' ≃* alternatingGroup (Fin 6)) :=
    ⟨(MonoidHom.ofInjective hinj).symm.trans S.A_iso.some⟩
  have hne : ρ ⟨a, ha⟩ ≠ 1 := by
    intro h
    have hA : (⟨a, ha⟩ : ↥A) = 1 := hinj (by rw [h, map_one])
    exact h1 (congrArg Subtype.val hA)
  have hsq : ρ ⟨a, ha⟩ * ρ ⟨a, ha⟩ = 1 := by
    have hmul : (⟨a, ha⟩ : ↥A) * ⟨a, ha⟩ = 1 := by
      apply Subtype.ext
      simpa using h2
    rw [← map_mul, hmul, map_one]
  have hfix4 : Nat.card {b : ↥B // ρ ⟨a, ha⟩ b = b} = 4 :=
    hInv G B S.hB H' hH' (ρ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩ hne hsq
  refine (Nat.card_congr
    { toFun := fun e => ⟨⟨(e.1 : G), e.2.1⟩, by
        change (T84Mod.resHom S.hBE u S.fix A S.A_comm ⟨a, ha⟩)
            ⟨(e.1 : G), e.2.1⟩ = ⟨(e.1 : G), e.2.1⟩
        rw [HCtx.resHom_apply_eq_self_iff S ha]
        have hemb : T84Mod.embB S.hBE ⟨(e.1 : G), e.2.1⟩ = e.1 := Subtype.ext rfl
        rw [hemb]
        exact e.2.2⟩
      invFun := fun b => ⟨⟨(b.1 : G), S.hBE b.1.2⟩, by
        have hb2 : (T84Mod.resHom S.hBE u S.fix A S.A_comm ⟨a, ha⟩) b.1 = b.1 := by
          change (ρ ⟨a, ha⟩) b.1 = b.1
          exact b.2
        have hb : a (T84Mod.embB S.hBE b.1) = T84Mod.embB S.hBE b.1 :=
          (HCtx.resHom_apply_eq_self_iff S ha b.1).mp hb2
        have hemb : T84Mod.embB S.hBE b.1 = ⟨(b.1 : G), S.hBE b.1.2⟩ := Subtype.ext rfl
        rw [hemb] at hb
        exact ⟨b.1.2, hb⟩⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }).trans hfix4

theorem HCtx.card_fixB_ua (hInv : Sec8T84FactInv) (S : HCtx E B u A H) {a : MulAut ↥E}
    (ha : a ∈ A) (h1 : a ≠ 1) (h2 : a * a = 1) :
    Nat.card {e : ↥E // (e : G) ∈ B ∧ (u * a) e = e} = 4 := by
  have hiff : ∀ e : ↥E, ((e : G) ∈ B ∧ (u * a) e = e) ↔ ((e : G) ∈ B ∧ a e = e) := by
    intro e
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      have hafix : u (a e) = a e :=
        (S.fix (a e)).mpr (T84Mod.preserves_B u S.fix a (S.A_comm a ha) e h.1)
      have h2' := h.2
      rw [MulAut.mul_apply, hafix] at h2'
      exact h2'
    · intro h
      refine ⟨h.1, ?_⟩
      rw [MulAut.mul_apply, h.2]
      exact (S.fix e).mpr h.1
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact HCtx.card_fixB_of_inv hInv S ha h1 h2

private theorem card_fixB_subgroupOf (hInv : Sec8T84FactInv) (S : HCtx E B u A H)
    {a : MulAut ↥E} (ha : a ∈ A) (h1 : a ≠ 1) (h2 : a * a = 1) :
    Nat.card {e : ↥E // e ∈ B.subgroupOf E ∧ a e = e} = 4 := by
  have hiff : ∀ e : ↥E,
      (e ∈ B.subgroupOf E ∧ a e = e) ↔ ((e : G) ∈ B ∧ a e = e) :=
    fun e => and_congr Subgroup.mem_subgroupOf Iff.rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact HCtx.card_fixB_of_inv hInv S ha h1 h2

private theorem card_fixB_ua_subgroupOf (hInv : Sec8T84FactInv) (S : HCtx E B u A H)
    {a : MulAut ↥E} (ha : a ∈ A) (h1 : a ≠ 1) (h2 : a * a = 1) :
    Nat.card {e : ↥E // e ∈ B.subgroupOf E ∧ (u * a) e = e} = 4 := by
  have hiff : ∀ e : ↥E,
      (e ∈ B.subgroupOf E ∧ (u * a) e = e) ↔ ((e : G) ∈ B ∧ (u * a) e = e) :=
    fun e => and_congr Subgroup.mem_subgroupOf Iff.rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact HCtx.card_fixB_ua hInv S ha h1 h2

theorem HCtx.card_fix_of_invol (hInv : Sec8T84FactInv) (S : HCtx E B u A H)
    (O : OddNormal H P) (hc : ∀ h ∈ H, h * u * h⁻¹ * u⁻¹ ∈ P) {h : MulAut ↥E} (hh : h ∈ H)
    (hh1 : h ≠ 1) (hh2 : h * h = 1) : Nat.card {e : ↥E // h e = e} = 16 := by
  classical
  obtain ⟨g, _, c, hcH, hcu, hcc, hc1, hh_eq⟩ := S.exists_invol_conj O hc hh hh2 hh1
  obtain ⟨⟨_, hEexp⟩, hEcard⟩ := S.hE
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with
      mul_comm := fun a b => Subtype.ext (mul_comm_of_mem_isMulCommutative E a.2 b.2) }
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  have hsq : ∀ v : ↥E, v * v = 1 :=
    fun v => Subtype.ext (by simpa [pow_two] using hEexp v v.2)
  have hfixE : ∀ e : ↥E, u e = e ↔ e ∈ B.subgroupOf E :=
    fun e => (S.fix e).trans Subgroup.mem_subgroupOf.symm
  have hconj : Nat.card {e : ↥E // h e = e} = Nat.card {e : ↥E // c e = e} := by
    have := card_fix_conj g c
    rwa [← hh_eq] at this
  rw [hconj]
  have hcmem : c ∈ A ⊔ zpowers u := S.cent c hcH hcu
  have hcomm : ∀ x ∈ A, ∀ y ∈ zpowers u, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_right ((commute_iff_eq x u).mpr (S.A_comm x hx)) m
  obtain ⟨a, haA, v, hv, hcv⟩ := A3.exists_mul_of_comm hcomm hcmem
  have hv1u : v = 1 ∨ v = u := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hu2z : u ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = 1 + 1 by norm_num, zpow_add_one, zpow_one, S.u_sq]
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
    · left
      rw [← hn, hk, zpow_mul, hu2z, one_zpow]
    · right
      rw [← hn, hk, zpow_add_one, zpow_mul, hu2z, one_zpow, one_mul]
  rcases hv1u with hv1 | hvu
  · rw [hv1, mul_one] at hcv
    have haa : a * a = 1 := by rwa [hcv] at hcc
    have hB4 : Nat.card {b : ↥E // b ∈ B.subgroupOf E ∧ a b = b} = 4 :=
      card_fixB_subgroupOf hInv S haA (by rwa [hcv] at hc1) haa
    have h16 := card_fix_eq_sixteen hsq hEcard u a S.u_sq haa (S.A_comm a haA)
      (B.subgroupOf E) hfixE hB4
    rw [hcv]
    exact h16
  · rw [hvu] at hcv
    by_cases ha1 : a = 1
    · rw [ha1, one_mul] at hcv
      rw [hcv]
      have hset : Nat.card {e : ↥E // u e = e} = Nat.card {e : ↥E // (e : G) ∈ B} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun e => S.fix e))
      rw [hset]
      have hB : Nat.card {e : ↥E // (e : G) ∈ B} = Nat.card ↥B :=
        Nat.card_congr
          { toFun := fun e => ⟨(e : G), e.2⟩
            invFun := fun b => ⟨⟨(b : G), S.hBE b.2⟩, b.2⟩
            left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
            right_inv := fun _ => Subtype.ext rfl }
      rw [hB, S.hB.2]
      norm_num
    · have haa : a * a = 1 := by
        have h : (a * u) * (a * u) = 1 := by rwa [hcv] at hcc
        rw [Commute.mul_mul_mul_comm (show Commute u a from (S.A_comm a haA).symm) a u,
          S.u_sq, mul_one] at h
        exact h
      have hB4 : Nat.card {b : ↥E // b ∈ B.subgroupOf E ∧ (a * u) b = b} = 4 := by
        rw [S.A_comm a haA]
        exact card_fixB_ua_subgroupOf hInv S haA ha1 haa
      have hauu : (a * u) * u = u * (a * u) := by
        calc (a * u) * u = a * (u * u) := by rw [mul_assoc]
          _ = a := by rw [S.u_sq, mul_one]
          _ = (u * a) * u := by rw [← S.A_comm a haA, mul_assoc, S.u_sq, mul_one]
          _ = u * (a * u) := by rw [mul_assoc]
      have h16 := card_fix_eq_sixteen hsq hEcard u (a * u) S.u_sq (by rwa [hcv] at hcc) hauu
        (B.subgroupOf E) hfixE hB4
      rw [hcv]
      exact h16

end C10

end CFSG.OddStandard.SmallF3.Omega
