module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUD8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Aut
import CFSG.ClassicalGroups.Unitary.Simple

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.U16

open Subgroup CFSG.Monster.B.Co2 CFSG.EvenSporadicStandard.M24Std.CU43
  CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem isSimpleGroup_X₀ : IsSimpleGroup CFSG.LieType.Multipliers.U43.X₀ := by
  have h := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
    CFSG.LieType.Multipliers.U43.F9 3 1
    (by rw [Nat.card_eq_fintype_card, CFSG.LieType.Multipliers.U43.F9.card_eq]; norm_num) 4
    (by norm_num) (by simp)
  rwa [pow_one] at h

theorem isSimpleGroup_P : IsSimpleGroup ↥P := by
  haveI := isSimpleGroup_X₀
  exact MulEquiv.isSimpleGroup psiEquiv.symm

theorem index_P_U43Ext : (P.subgroupOf U43Ext).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨rhoPerm, rho_mem_U43Ext⟩, fun b => ?_⟩
  have hmem : ∀ x : ↥U43Ext, x ∈ P.subgroupOf U43Ext ↔ (x : Equiv.Perm (Fin 820)) ∈ P :=
    fun x => Subgroup.mem_subgroupOf
  rw [hmem, hmem]
  by_cases hb : (b : Equiv.Perm (Fin 820)) ∈ P
  · right
    refine ⟨hb, ?_⟩
    intro h
    apply rho_not_mem_P
    have : rhoPerm = (b : Equiv.Perm (Fin 820))⁻¹ * ((b * ⟨rhoPerm, rho_mem_U43Ext⟩ : ↥U43Ext) :
        Equiv.Perm (Fin 820)) := by
      simp
    rw [this]
    exact P.mul_mem (P.inv_mem hb) h
  · left
    refine ⟨?_, hb⟩
    obtain hP | ⟨g, hg, hbg⟩ := mem_U43Ext_iff.1 b.2
    · exact absurd hP hb
    · have : ((b * ⟨rhoPerm, rho_mem_U43Ext⟩ : ↥U43Ext) : Equiv.Perm (Fin 820)) = g := by
        show (b : Equiv.Perm (Fin 820)) * rhoPerm = g
        rw [hbg, mul_assoc, rho_sq, mul_one]
      show ((b * ⟨rhoPerm, rho_mem_U43Ext⟩ : ↥U43Ext) : Equiv.Perm (Fin 820)) ∈ P
      rw [this]
      exact hg

theorem card_U43ExtStar : Nat.card ↥U43ExtStar = 4 * Nat.card ↥P := by
  let vIx : Fin 4 → ℕ := ![0, 2, 5, 7]
  have hv8 : ∀ i, vIx i < 8 := fun i => by fin_cases i <;> simp [vIx]
  have hvV : ∀ i, InV (vIx i) := fun i => by fin_cases i <;> simp [vIx, InV]
  let f : ↥P × Fin 4 → ↥U43ExtStar := fun p =>
    ⟨(p.1 : Equiv.Perm (Fin 820)) * tP (vIx p.2), (p.1 : Equiv.Perm (Fin 820)), p.1.2, vIx p.2, hv8 _, hvV _, rfl⟩
  have hinj : Function.Injective f := by
    rintro ⟨g, i⟩ ⟨g', i'⟩ h
    have h1 : (g : Equiv.Perm (Fin 820)) * tP (vIx i) = g' * tP (vIx i') := congrArg Subtype.val h
    have hii : vIx i = vIx i' := by
      by_contra hne
      apply tP_mul_inv_not_mem (hv8 i) (hv8 i') hne
      have e : tP (vIx i) * (tP (vIx i'))⁻¹ = (g : Equiv.Perm (Fin 820))⁻¹ * g' := by
        calc tP (vIx i) * (tP (vIx i'))⁻¹
            = (g : Equiv.Perm (Fin 820))⁻¹ * ((g : Equiv.Perm (Fin 820)) * tP (vIx i)) *
              (tP (vIx i'))⁻¹ := by group
          _ = (g : Equiv.Perm (Fin 820))⁻¹ * (g' * tP (vIx i')) * (tP (vIx i'))⁻¹ := by rw [h1]
          _ = _ := by group
      rw [e]
      exact P.mul_mem (P.inv_mem g.2) g'.2
    have hi : i = i' := by
      fin_cases i <;> fin_cases i' <;> simp [vIx] at hii ⊢
    subst hi
    have : (g : Equiv.Perm (Fin 820)) = g' := mul_right_cancel h1
    exact Prod.ext (Subtype.ext this) rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨x, g, hg, k, hk, hkV, rfl⟩
    have : ∃ i : Fin 4, vIx i = k := by
      rcases hkV with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    obtain ⟨i, rfl⟩ := this
    exact ⟨(⟨g, hg⟩, i), rfl⟩
  have := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at this
  omega

theorem odd_mem_P {x : ↥U43Ext} (hx : Odd (orderOf x)) : (x : Equiv.Perm (Fin 820)) ∈ P := by
  have hH : (P.subgroupOf U43Ext).index = 2 := index_P_U43Ext
  obtain ⟨k, hk⟩ := hx
  have hxk : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hx2 : x * x ∈ P.subgroupOf U43Ext := by rw [Subgroup.mul_mem_iff_of_index_two hH]
  have : x = (x * x) ^ (k + 1) := by
    calc x = x ^ (2 * k + 1) * x := by rw [hxk, one_mul]
      _ = x ^ (2 * (k + 1)) := by rw [← pow_succ, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
      _ = (x * x) ^ (k + 1) := by rw [pow_mul, sq]
  have hxm : x ∈ P.subgroupOf U43Ext := by
    rw [this]
    exact pow_mem hx2 _
  exact Subgroup.mem_subgroupOf.1 hxm

theorem closure_odd_eq : Subgroup.closure {x : ↥U43Ext | Odd (orderOf x)} = P.subgroupOf U43Ext := by
  classical
  haveI : IsSimpleGroup ↥P := isSimpleGroup_P
  set T : Subgroup ↥U43Ext := Subgroup.closure {x : ↥U43Ext | Odd (orderOf x)} with hT
  have hTle : T ≤ P.subgroupOf U43Ext := by
    rw [hT, Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (odd_mem_P hx)
  refine le_antisymm hTle ?_
  have hTn : T.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hT] at hn ⊢
    induction hn using Subgroup.closure_induction with
    | mem y hy =>
      apply Subgroup.subset_closure
      show Odd (orderOf (g * y * g⁻¹))
      have h1 : g * y * g⁻¹ = (MulAut.conj g) y := rfl
      rw [h1, MulEquiv.orderOf_eq]
      exact hy
    | one => simp
    | mul a b _ _ ha hb => simpa [mul_assoc] using Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  let eP : ↥(P.subgroupOf U43Ext) ≃* ↥P := Subgroup.subgroupOfEquivOfLe P_le_U43Ext
  haveI : IsSimpleGroup ↥(P.subgroupOf U43Ext) := MulEquiv.isSimpleGroup eP
  have hnorm : (T.subgroupOf (P.subgroupOf U43Ext)).Normal := by
    haveI := hTn
    exact Subgroup.normal_subgroupOf
  have hne : T.subgroupOf (P.subgroupOf U43Ext) ≠ ⊥ := by
    intro h
    have h3 : 3 ∣ Nat.card ↥(P.subgroupOf U43Ext) := by
      rw [Nat.card_congr eP.toEquiv, card_P]
      norm_num
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hyT : (y : ↥U43Ext) ∈ T := by
      apply Subgroup.subset_closure
      show Odd (orderOf (y : ↥U43Ext))
      rw [Subgroup.orderOf_coe, hy]
      exact ⟨1, rfl⟩
    have : y ∈ T.subgroupOf (P.subgroupOf U43Ext) := Subgroup.mem_subgroupOf.2 hyT
    rw [h, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have htop : T.subgroupOf (P.subgroupOf U43Ext) = ⊤ := by
    haveI := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf (P.subgroupOf U43Ext)) with h | h
    · exact absurd h hne
    · exact h
  intro x hx
  have : (⟨x, hx⟩ : ↥(P.subgroupOf U43Ext)) ∈ T.subgroupOf (P.subgroupOf U43Ext) := by
    rw [htop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 this

theorem P_char (α : MulAut ↥U43Ext) {x : ↥U43Ext} (hx : (x : Equiv.Perm (Fin 820)) ∈ P) :
    ((α x : ↥U43Ext) : Equiv.Perm (Fin 820)) ∈ P := by
  have hxm : x ∈ P.subgroupOf U43Ext := Subgroup.mem_subgroupOf.2 hx
  rw [← closure_odd_eq] at hxm
  have key : ∀ y ∈ Subgroup.closure {x : ↥U43Ext | Odd (orderOf x)}, α y ∈ P.subgroupOf U43Ext := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem a ha =>
      apply Subgroup.mem_subgroupOf.2
      apply odd_mem_P
      rw [MulEquiv.orderOf_eq]
      exact ha
    | one => simp
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      rw [map_inv]
      exact Subgroup.inv_mem _ ha
  exact Subgroup.mem_subgroupOf.1 (key x hxm)

@[expose] noncomputable def resP (α : MulAut ↥U43Ext) : MulAut ↥P where
  toFun p := ⟨((α ⟨p, P_le_U43Ext p.2⟩ : ↥U43Ext) : Equiv.Perm (Fin 820)), P_char α p.2⟩
  invFun p := ⟨((α.symm ⟨p, P_le_U43Ext p.2⟩ : ↥U43Ext) : Equiv.Perm (Fin 820)),
    P_char α.symm p.2⟩
  left_inv p := by
    apply Subtype.ext
    simp only [Subtype.coe_eta]
    exact congrArg Subtype.val (α.symm_apply_apply ⟨p, P_le_U43Ext p.2⟩)
  right_inv p := by
    apply Subtype.ext
    simp only [Subtype.coe_eta]
    exact congrArg Subtype.val (α.apply_symm_apply ⟨p, P_le_U43Ext p.2⟩)
  map_mul' p q := by
    apply Subtype.ext
    show ((α ⟨(p * q : ↥P).1, P_le_U43Ext (p * q).2⟩ : ↥U43Ext) : Equiv.Perm (Fin 820)) = _
    have e : (⟨(p * q : ↥P).1, P_le_U43Ext (p * q).2⟩ : ↥U43Ext) =
        ⟨p.1, P_le_U43Ext p.2⟩ * ⟨q.1, P_le_U43Ext q.2⟩ := rfl
    rw [e, map_mul]
    rfl

theorem aut_induced (α : MulAut ↥U43Ext) :
    ∃ r ∈ U43ExtStar, ∀ x : ↥U43Ext,
      ((α x : ↥U43Ext) : Equiv.Perm (Fin 820)) = r * x * r⁻¹ := by
  obtain ⟨r, hrR, hr⟩ := autModel.surj (resP α)
  have hres : ∀ y : ↥U43Ext, (y : Equiv.Perm (Fin 820)) ∈ P →
      ((α y : ↥U43Ext) : Equiv.Perm (Fin 820)) = r * y * r⁻¹ := fun y hy => hr ⟨y, hy⟩
  have hKR : ∀ k : ↥U43Ext, (k : Equiv.Perm (Fin 820)) ∈ R := fun k =>
    U43ExtStar_le_R (U43Ext_le_U43ExtStar k.2)
  have hext : ∀ k : ↥U43Ext, ((α k : ↥U43Ext) : Equiv.Perm (Fin 820)) = r * k * r⁻¹ := by
    intro k
    have hw : (r * (k : Equiv.Perm (Fin 820)) * r⁻¹)⁻¹ * ((α k : ↥U43Ext) : Equiv.Perm (Fin 820))
        ∈ R :=
      R.mul_mem (R.inv_mem (R.mul_mem (R.mul_mem hrR (hKR k)) (R.inv_mem hrR)))
        (hKR (α k))
    have hcomm : ∀ p ∈ P, ((r * (k : Equiv.Perm (Fin 820)) * r⁻¹)⁻¹ *
        ((α k : ↥U43Ext) : Equiv.Perm (Fin 820))) * p =
        p * ((r * (k : Equiv.Perm (Fin 820)) * r⁻¹)⁻¹ *
          ((α k : ↥U43Ext) : Equiv.Perm (Fin 820))) := by
      intro p hp
      set q : ↥U43Ext := α.symm ⟨p, P_le_U43Ext hp⟩ with hq
      have hqP : (q : Equiv.Perm (Fin 820)) ∈ P := P_char α.symm hp
      have hαq : ((α q : ↥U43Ext) : Equiv.Perm (Fin 820)) = p := by
        rw [hq, α.apply_symm_apply]
      have h1 : p = r * (q : Equiv.Perm (Fin 820)) * r⁻¹ := by rw [← hres q hqP, hαq]
      have hkq : (k : Equiv.Perm (Fin 820)) * q * (k : Equiv.Perm (Fin 820))⁻¹ ∈ P :=
        conj_mem_P (hKR k) hqP
      have h2 : ((α (k * q * k⁻¹) : ↥U43Ext) : Equiv.Perm (Fin 820)) =
          ((α k : ↥U43Ext) : Equiv.Perm (Fin 820)) * p *
            ((α k : ↥U43Ext) : Equiv.Perm (Fin 820))⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hαq]
      have h3 : ((α (k * q * k⁻¹) : ↥U43Ext) : Equiv.Perm (Fin 820)) =
          r * ((k : Equiv.Perm (Fin 820)) * q * (k : Equiv.Perm (Fin 820))⁻¹) * r⁻¹ :=
        hres _ hkq
      have h4 : ((α k : ↥U43Ext) : Equiv.Perm (Fin 820)) * p *
          ((α k : ↥U43Ext) : Equiv.Perm (Fin 820))⁻¹ =
          r * ((k : Equiv.Perm (Fin 820)) * q * (k : Equiv.Perm (Fin 820))⁻¹) * r⁻¹ := by
        rw [← h2, h3]
      calc ((r * (k : Equiv.Perm (Fin 820)) * r⁻¹)⁻¹ *
            ((α k : ↥U43Ext) : Equiv.Perm (Fin 820))) * p
          = (r * (k : Equiv.Perm (Fin 820)) * r⁻¹)⁻¹ *
            (((α k : ↥U43Ext) : Equiv.Perm (Fin 820)) * p *
              ((α k : ↥U43Ext) : Equiv.Perm (Fin 820))⁻¹) *
            ((α k : ↥U43Ext) : Equiv.Perm (Fin 820)) := by group
        _ = (r * (k : Equiv.Perm (Fin 820)) * r⁻¹)⁻¹ *
            (r * ((k : Equiv.Perm (Fin 820)) * q * (k : Equiv.Perm (Fin 820))⁻¹) * r⁻¹) *
            ((α k : ↥U43Ext) : Equiv.Perm (Fin 820)) := by rw [h4]
        _ = p * ((r * (k : Equiv.Perm (Fin 820)) * r⁻¹)⁻¹ *
            ((α k : ↥U43Ext) : Equiv.Perm (Fin 820))) := by rw [h1]; group
    have h1 := inj_of_comm hw hcomm
    exact (inv_mul_eq_one.1 h1).symm
  have hnorm : ∀ k ∈ U43Ext, r * k * r⁻¹ ∈ U43Ext := fun k hk => by
    have := hext ⟨k, hk⟩
    rw [← this]
    exact (α ⟨k, hk⟩).2
  exact ⟨r, normalizer_U43Ext hrR hnorm, hext⟩

theorem autModel_U43Ext : CFSG.Sporadic.SmallOddCore.AutModel U43Ext U43ExtStar where
  le := U43Ext_le_U43ExtStar
  conj_mem := fun _ hx _ hk => conj_mem_U43Ext hx hk
  surj := fun α => by
    obtain ⟨r, hr, h⟩ := aut_induced α
    exact ⟨r, hr, h⟩
  inj := fun _ hx hc => inj_of_comm (U43ExtStar_le_R hx)
    (fun p hp => hc p (P_le_U43Ext hp))

end CFSG.EvenSporadicStandard.Fin76b.U16
