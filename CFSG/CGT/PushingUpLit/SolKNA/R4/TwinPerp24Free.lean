module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22Basic
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Perp24

section Group

variable {Y : Type} [Group Y] [Finite Y]

theorem commute_of_normalizes {C L : Subgroup Y} (hLC : L ≤ C) (hL : oddCoreIn L = ⊥) {o : Y}
    (ho : o ∈ oddCoreIn C) (hoL : o ∈ Subgroup.normalizer (L : Set Y)) :
    ∀ k ∈ L, o * k = k * o := by
  intro k hk
  have h1 : o * k * o⁻¹ * k⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp hoL k).mp hk) (L.inv_mem hk)
  have h2 : o * k * o⁻¹ * k⁻¹ ∈ oddCoreIn C := by
    have e : o * k * o⁻¹ * k⁻¹ = o * (k * o⁻¹ * k⁻¹) := by group
    rw [e]
    exact (oddCoreIn C).mul_mem ho (conj_mem_oddCoreIn (hLC hk) ((oddCoreIn C).inv_mem ho))
  have hnorm : L ≤ Subgroup.normalizer ((L ⊓ oddCoreIn C : Subgroup Y) : Set Y) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, normalizer_oddCoreIn C (hLC hx)⟩
  have hodd : Odd (Nat.card ↥(L ⊓ oddCoreIn C)) :=
    (odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hle : L ⊓ oddCoreIn C ≤ oddCoreIn L := le_oddCoreIn_of_normalizes inf_le_left hnorm hodd
  have h3 := hle ⟨h1, h2⟩
  rw [hL, Subgroup.mem_bot] at h3
  calc o * k = (o * k * o⁻¹ * k⁻¹) * (k * o) := by group
    _ = k * o := by rw [h3, one_mul]

theorem mem_of_index_two_of_odd {H : Subgroup Y} (hH : H.index = 2) {o : Y} (hodd : Odd (orderOf o)) :
    o ∈ H := by
  obtain ⟨l, hl⟩ := hodd
  have h1 : o ^ (2 * l + 1) = 1 := by rw [← hl]; exact pow_orderOf_eq_one o
  have h2 : o = ((o * o) ^ l)⁻¹ := by
    have : o * (o * o) ^ l = 1 := by
      calc o * (o * o) ^ l = o ^ (2 * l + 1) := by
            rw [← pow_two, ← pow_mul, pow_succ', mul_comm 2 l]
        _ = 1 := h1
    exact eq_inv_of_mul_eq_one_left this
  rw [h2]
  exact H.inv_mem (H.pow_mem (Subgroup.mul_self_mem_of_index_two hH o) l)

theorem closure_pair_cases {a b : Y} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set Y), x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hba : b * a = a * b := hab.symm
  have ha' : ∀ w : Y, a * (a * w) = w := fun w => by rw [← mul_assoc, ha, one_mul]
  have hb' : ∀ w : Y, b * (b * w) = w := fun w => by rw [← mul_assoc, hb, one_mul]
  have hba' : ∀ w : Y, b * (a * w) = a * (b * w) := fun w => by
    rw [← mul_assoc, hba, mul_assoc]
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · right; left; exact hx
    · right; right; left; exact Set.mem_singleton_iff.mp hx
  | one => left; rfl
  | mul x y _ _ h1 h2 =>
    rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;> rw [h1, h2] <;>
      simp only [mul_assoc, ha, hb, ha', hb', hba, hba', one_mul, mul_one, true_or, or_true]
  | inv x _ h =>
    rcases h with h | h | h | h <;> rw [h]
    · left; simp
    · right; left; exact inv_eq_of_mul_eq_one_right ha
    · right; right; left; exact inv_eq_of_mul_eq_one_right hb
    · right; right; right
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb, hba]

theorem odd_card_alphaOf_of_commute {A : Subgroup Y} {a₀ : Y} (ha₀ : a₀ ∈ A) (ha₁ : a₀ ≠ 1)
    (hc : ∀ a ∈ A, a ≠ 1 → ∀ o ∈ oddCoreIn (Subgroup.centralizer ({a} : Set Y)), ∀ x ∈ A,
      o * x = x * o) :
    Odd (Nat.card (alphaOf A)) := by
  have hle : alphaOf A ≤ oddCoreIn (Subgroup.centralizer ({a₀} : Set Y)) := by
    refine sup_le ?_ (iInf₂_le_of_le a₀ ha₀ (iInf_le_of_le ha₁ le_rfl))
    refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
    have hbot : ⁅oddCoreOf (Subgroup.centralizer ({a} : Set Y)), A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro o ho
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hc a ha ha1 o ho x hx).symm
    rw [hbot]
    exact bot_le
  exact (odd_card_oddCoreIn _).of_dvd_nat (Subgroup.card_dvd_of_le hle)

end Group

section Twin

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem oddCore_le_centralizer_sup (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R)
    {K' : Subgroup Y} (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R) (hK : oddCoreIn (tightCore R) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({t} : Set Y)) ≤
      Subgroup.centralizer ((tightCore R ⊔ K' : Subgroup Y) : Set Y) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set K := tightCore R with hKdef
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  have hpair : twinSet Ω K = {K, K'} := TwinPerp.twinSet_eq_pair h2 hK' hne
  have hz : IsUniqueInvolution K t := Inner.isUniqueInvolution_core h.core.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hK'
  have hKC : K ≤ C := CFSG.ClassicalInvolution.Asc77.isUniqueInvolution_le_centralizer hz
  have hK'C : K' ≤ C := CFSG.ClassicalInvolution.Asc77.isUniqueInvolution_le_centralizer hz'
  have hK'O : oddCoreIn K' = ⊥ := by
    obtain ⟨c, -, hc⟩ := h.exists_centralizer_conj hK'
    rw [← hc]
    have := AscE184Sect.oddCoreOf_conjSub c K
    have h1 : oddCoreIn (conjSub c K) = conjSub c (oddCoreIn K) := this
    rw [h1, hK]
    exact Subgroup.map_bot _
  have hidx : ((C ⊓ Subgroup.normalizer (K : Set Y)).subgroupOf C).index = 2 := by
    have h1 := h.card_twinSet
    rw [hpair, Nat.card_coe_set_eq, Set.ncard_pair hne.symm] at h1
    exact h1.symm
  intro o ho
  have hoC : o ∈ C := oddCoreIn_le C ho
  have hodd : Odd (orderOf o) :=
    (odd_card_oddCoreIn C).of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCoreIn C) ho)
  have hoN : o ∈ Subgroup.normalizer (K : Set Y) := by
    have h1 := mem_of_index_two_of_odd hidx (o := (⟨o, hoC⟩ : ↥C))
      (by rw [← Subgroup.orderOf_coe]; exact hodd)
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h1)).2
  have hinj : ∀ A B : Subgroup Y, conjSub o A = conjSub o B → A = B := fun A B heq => by
    have h1 := congrArg (conjSub o⁻¹) heq
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h1
  have hoN' : o ∈ Subgroup.normalizer (K' : Set Y) := by
    have h1 : conjSub o K' ∈ twinSet Ω K := h.conj_mem_twinSet hK' hoC
    rw [hpair] at h1
    rw [mem_normalizer_iff_conjSub_eq]
    rcases h1 with h1 | h1
    · exact absurd (hinj _ _ (h1.trans (mem_normalizer_iff_conjSub_eq.mp hoN).symm)) hne
    · exact Set.mem_singleton_iff.mp h1
  have hcK := commute_of_normalizes hKC hK ho hoN
  have hcK' := commute_of_normalizes hK'C hK'O ho hoN'
  have hle : K ⊔ K' ≤ Subgroup.centralizer ({o} : Set Y) := by
    refine sup_le (fun k hk => ?_) (fun k hk => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcK k hk).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcK' k hk).symm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem alphaOf_odd_of_oddCore_bot (hr : 4 ≤ r) (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (htW : t ∈ W)
    (hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W)
    (hnc : ¬ TwinPerp.WCentralNontrivial W) (hK : oddCoreIn (tightCore R) = ⊥) {g : Y}
    (hg : g ∈ MGrp (CoreAssembly.conjClass (tightCore R)) W) :
    Odd (Nat.card (alphaOf (Subgroup.closure ({t, g * t * g⁻¹} : Set Y)))) := by
  classical
  obtain ⟨K', hK', hne, ⟨D⟩⟩ := Perp23.Two.exists_twoFrame h h2 hW htW hS4
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have cx : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W :=
    Q3CL.T8.ctxOf h.partIHypG hW
  have hwc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := WTool.comm_of_mem_wSet hΩ hW
  have hz : IsUniqueInvolution (tightCore R) t := D.hzK
  have hz2 : t * t = 1 := hz.sq
  have hz1 : t ≠ 1 := hz.ne_one
  have hj2 : D.F.j * D.F.j = 1 := D.j_sq
  have htj : t * D.F.j = D.F.j * t := hwc t D.t_mem_W D.F.j D.j_mem_W
  have hEN : ∀ g ∈ MGrp (CoreAssembly.conjClass (tightCore R)) W,
      g ∈ Subgroup.normalizer (Subgroup.closure ({t, D.F.j} : Set Y) : Set Y) := fun g hg =>
    D.mgrp_le_normalizer hΩ hW cx hg
  have hsup : D.F.j ∈ tightCore R ⊔ K' := D.j_mem_sup hΩ hW cx hnc
  have hsM := D.s_mem_mgrp
  have hrM := D.r_mem_mgrp
  have hst : D.F.ρ₃.r * t * D.F.ρ₃.r⁻¹ = t * D.F.j := D.s_t hwc
  have hrt : D.F.ρ.r * t * D.F.ρ.r⁻¹ = t := by rw [D.r_t]; group
  have hrj : D.F.ρ.r * D.F.j * D.F.ρ.r⁻¹ = D.F.j * t := D.r_j hwc
  generalize D.F.j = j at *
  generalize D.F.ρ₃.r = s at *
  generalize D.F.ρ.r = r' at *
  set E : Subgroup Y := Subgroup.closure ({t, j} : Set Y) with hEdef
  have htE : t ∈ E := Subgroup.subset_closure (Set.mem_insert _ _)
  have hZ : ∀ o ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y)), ∀ x ∈ E, o * x = x * o := by
    intro o ho x hx
    have hcent := oddCore_le_centralizer_sup h h2 hK' hne hK ho
    have hEle : E ≤ Subgroup.centralizer ({o} : Set Y) := by
      rw [hEdef, Subgroup.closure_le]
      rintro y (hy | hy)
      · rw [hy]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (oddCoreIn_le _ ho)).symm
      · rw [Set.mem_singleton_iff.mp hy]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hcent _ hsup)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hEle hx)).symm
  have hsN : s ∈ Subgroup.normalizer (E : Set Y) := hEN s hsM
  have hrN : r' ∈ Subgroup.normalizer (E : Set Y) := hEN r' hrM
  have hconj : ∀ k ∈ Subgroup.normalizer (E : Set Y),
      ∀ o ∈ oddCoreIn (Subgroup.centralizer ({k * t * k⁻¹} : Set Y)), ∀ x ∈ E, o * x = x * o := by
    intro k hk o ho x hx
    have h1 : oddCoreOf (Subgroup.centralizer ({k * t * k⁻¹} : Set Y)) =
        conjSub k (oddCoreOf (Subgroup.centralizer ({t} : Set Y))) :=
      T7A.oddCoreOf_centralizer_conj k t
    have ho' : o ∈ conjSub k (oddCoreOf (Subgroup.centralizer ({t} : Set Y))) := h1 ▸ ho
    rw [mem_conjSub_iff] at ho'
    have hx' : k⁻¹ * x * k ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) x).mp hx
      simpa using this
    have h3 := hZ (k⁻¹ * o * k) ho' (k⁻¹ * x * k) hx'
    calc o * x = k * ((k⁻¹ * o * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * x * k) * (k⁻¹ * o * k)) * k⁻¹ := by rw [h3]
      _ = x * o := by group
  have hj' : (r' * s) * t * (r' * s)⁻¹ = j := by
    calc (r' * s) * t * (r' * s)⁻¹ = r' * (s * t * s⁻¹) * r'⁻¹ := by group
      _ = r' * (t * j) * r'⁻¹ := by rw [hst]
      _ = (r' * t * r'⁻¹) * (r' * j * r'⁻¹) := by group
      _ = t * (j * t) := by rw [hrt, hrj]
      _ = (t * j) * t := by group
      _ = (j * t) * t := by rw [htj]
      _ = j := by rw [mul_assoc, hz2, mul_one]
  have hnoz : ∀ a ∈ E, a ≠ 1 → ∀ o ∈ oddCoreIn (Subgroup.centralizer ({a} : Set Y)),
      ∀ x ∈ E, o * x = x * o := by
    intro a ha ha1
    rcases closure_pair_cases hz2 hj2 htj a ha with h1 | h1 | h1 | h1
    · exact absurd h1 ha1
    · rw [h1]
      exact hZ
    · rw [h1, ← hj']
      exact hconj _ (Subgroup.mul_mem _ hrN hsN)
    · rw [h1, ← hst]
      exact hconj _ hsN
  have hvE : g * t * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hEN g hg) t).mp htE
  have hE'E : Subgroup.closure ({t, g * t * g⁻¹} : Set Y) ≤ E := by
    rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · rw [hy]; exact htE
    · rw [Set.mem_singleton_iff.mp hy]; exact hvE
  refine odd_card_alphaOf_of_commute (a₀ := t) (Subgroup.subset_closure (Set.mem_insert _ _)) hz1 ?_
  intro a ha ha1 o ho x hx
  exact hnoz a (hE'E ha) ha1 o ho x (hE'E hx)

end Twin

end Perp24

end CFSG.CGT.PushingUpLit.SolKNA.R4
