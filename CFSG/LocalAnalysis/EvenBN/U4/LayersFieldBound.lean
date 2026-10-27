module

public import CFSG.LocalAnalysis.EvenBN.U4.LayersModel
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivQuot
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenBN.U4.RootF2
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf)

abbrev miyamotoH1G {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {G : Type}
    [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G) : Subgroup G :=
  normalizer (miyamotoF1G h L η t : Set G) ⊓ centralizer (miyamotoI1G h L η : Set G)

theorem eq_one_of_odd_of_pow_two_pow_eq_one {G : Type*} [Group G] {X : Subgroup G}
    [Finite X] (hX : Odd (Nat.card X)) {x : G} (hx : x ∈ X) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card X := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card X) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hX)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem t_mem_centralizer_I1 (hS : Setting h L η t Q T) :
    t ∈ centralizer (miyamotoI1G h L η : Set G) :=
  mem_centralizer_iff.2 fun _ hs => mem_centralizer_singleton_iff.1 (hS.I1_le_C hs)

theorem t_mem_H1 (hS : Setting h L η t Q T) : t ∈ miyamotoH1G h L η t :=
  ⟨hS.t_mem_normalizer_F1, hS.t_mem_centralizer_I1⟩

theorem N1G_le_centralizer_I1 (_hS : Setting h L η t Q T) :
    miyamotoN1G h L η ≤ centralizer (miyamotoI1G h L η : Set G) := fun _ hn =>
  mem_centralizer_iff.2 fun _ hi => I1G_commute_N1G h L η hi hn

theorem N1G_le_H1 (hS : Setting h L η t Q T) : miyamotoN1G h L η ≤ miyamotoH1G h L η t :=
  le_inf hS.N1_le_normalizer_F1 hS.N1G_le_centralizer_I1

theorem N1G_le_C (hS : Setting h L η t Q T) :
    miyamotoN1G h L η ≤ centralizer ({t} : Set G) :=
  (miyamotoPull_le h L η _).trans hS.L_le_centralizer

theorem t_mem_centralizer_N1 (hS : Setting h L η t Q T) :
    t ∈ centralizer (miyamotoN1G h L η : Set G) :=
  mem_centralizer_iff.2 fun _ hn => mem_centralizer_singleton_iff.1 (hS.N1G_le_C hn)

theorem F1_inf_C (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊓ centralizer ({t} : Set G) = miyamotoA1G h L η := by
  rw [← hS.F1_inf_B1, ← hS.D1_inf_C, ← inf_assoc, inf_eq_left.2 hS.F1_le_D1]

theorem mem_normalizer_A1_of_mem (hS : Setting h L η t Q T) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G)) (hxF : x ∈ normalizer (miyamotoF1G h L η t : Set G)) :
    x ∈ normalizer (miyamotoA1G h L η : Set G) := by
  rw [← hS.F1_inf_C]
  exact mem_normalizer_inf hxF (le_normalizer hxC)

theorem exists_act_eq_of_mem_H1 (hS : Setting h L η t Q T) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G)) (hx : x ∈ miyamotoH1G h L η t) :
    ∃ s : gramSU h (miyamotoJ4 K), (∃ i ∈ miyamotoI1 h, ∃ n ∈ miyamotoN1 h,
      (s : GL (Fin 4) K) = i * n) ∧ ∃ φ : K ≃+* K, (φ = RingEquiv.refl K ∨
        ∀ c, φ c = h.bar c) ∧
          miyamotoAct h L η ⟨x, hS.centralizer_le_normalizer hxC⟩ =
            MulAut.conj s * miyamotoFieldAut h φ :=
  (fixes_miyamotoI1_and_stabilizes_A1_iff h hS.two_le _).mp
    ⟨fun _ hg => miyamotoAct_apply_of_mem_centralizer h L η _ hx.2 hg,
      fun g => miyamotoAct_mem_iff_of_mem_normalizer h L η _
        (hS.mem_normalizer_A1_of_mem hxC hx.1) g⟩

omit [Finite G] in
theorem coe_act_apply_of_eq {x : normalizer (L : Set G)} {s : gramSU h (miyamotoJ4 K)}
    {φ : K ≃+* K} (hα : miyamotoAct h L η x = MulAut.conj s * miyamotoFieldAut h φ)
    (g : gramSU h (miyamotoJ4 K)) :
    ((miyamotoAct h L η x g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      (s : GL (Fin 4) K) * glAut φ (g : GL (Fin 4) K) * (s : GL (Fin 4) K)⁻¹ := by
  rw [hα, MulAut.mul_apply, MulAut.conj_apply, coe_mul, coe_mul, coe_inv,
    coe_miyamotoFieldAut_apply]

theorem mem_normalizer_N1_of_mem_H1 (hS : Setting h L η t Q T) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G)) (hx : x ∈ miyamotoH1G h L η t) :
    x ∈ normalizer (miyamotoN1G h L η : Set G) := by
  obtain ⟨s, ⟨i, hi, n, hn, hs⟩, φ, -, hα⟩ := hS.exists_act_eq_of_mem_H1 hxC hx
  refine mem_normalizer_fintype fun y hy => ?_
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hy
  have e := coe_symm_miyamotoAct_apply h L η ⟨x, hS.centralizer_le_normalizer hxC⟩ g
  simp only at e
  rw [SetLike.mem_coe, ← e, symm_mem_miyamotoPull_iff, coe_act_apply_of_eq hα, hs]
  exact conj_glAut_mem_N1 h hi hn φ hg

theorem exists_sq_eq_mul_of_mem_H1 (hS : Setting h L η t Q T) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G)) (hx : x ∈ miyamotoH1G h L η t) :
    ∃ a ∈ miyamotoN1G h L η, ∃ c ∈ miyamotoH1G h L η t ⊓
      centralizer (miyamotoN1G h L η : Set G), x ^ 2 = a * c := by
  have : CharP K 2 := h.charP
  obtain ⟨s, ⟨i, hi, n, hn, hs⟩, c₀, hc₀, hx2⟩ := exists_sq_eq_miyamotoI1_N1_mul h L η hS.two_le
    ⟨x, hS.centralizer_le_normalizer hxC⟩ hx.2 (hS.mem_normalizer_A1_of_mem hxC hx.1)
  set i' : G := ((η.symm ⟨i, miyamotoI1_le_gramSU h hi⟩ : L) : G) with hi'def
  set n' : G := ((η.symm ⟨n, miyamotoN1_le_gramSU h hn⟩ : L) : G) with hn'def
  have hi' : i' ∈ miyamotoI1G h L η := (symm_mem_miyamotoPull_iff h L η).2 hi
  have hn' : n' ∈ miyamotoN1G h L η := (symm_mem_miyamotoPull_iff h L η).2 hn
  have hs' : ((η.symm s : L) : G) = i' * n' := by
    rw [hi'def, hn'def, ← L.coe_mul, ← map_mul]
    congr 2
    exact Subtype.ext hs
  have hin : i' * n' = n' * i' := I1G_commute_N1G h L η hi' hn'
  have hx2' : (x : G) ^ 2 = n' * (i' * c₀) := by
    simp only at hx2
    rw [hx2, hs', hin, mul_assoc]
  have hc : i' * c₀ = n'⁻¹ * x ^ 2 := by rw [hx2', inv_mul_cancel_left]
  have hxH : x ^ 2 ∈ miyamotoH1G h L η t := pow_mem hx 2
  have hn'H : n' ∈ miyamotoH1G h L η t := hS.N1G_le_H1 hn'
  refine ⟨n', hn', i' * c₀, mem_inf.2 ⟨?_, ?_⟩, hx2'⟩
  · rw [hc]
    exact mul_mem (inv_mem hn'H) hxH
  · refine mem_centralizer_iff.2 fun y hy => ?_
    have hyL : y ∈ L := miyamotoPull_le h L η _ hy
    have h1 : y * i' = i' * y := (I1G_commute_N1G h L η hi' hy).symm
    have h2 : y * c₀ = c₀ * y := mem_centralizer_iff.1 hc₀ y hyL
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem isSylowOf_zpowers_H1 (hS : Setting h L η t Q T) :
    IsSylowOf 2 (zpowers t)
      (miyamotoH1G h L η t ⊓ centralizer (miyamotoN1G h L η : Set G)) := by
  have : CharP K 2 := h.charP
  refine CFSG.ComponentClassification.AS81.Sec2Quot.isSylowOf_of_forall_mem_normalizer
    (zpowers_le.2 ⟨hS.t_mem_H1, hS.t_mem_centralizer_N1⟩)
    (IsPGroup.of_card (n := 1) (by rw [hS.card_zpowers_t, pow_one]))
    fun c hc hcN ⟨k, hk⟩ => ?_
  have hct : c ∈ centralizer ({t} : Set G) := by
    have h1 : c * t * c⁻¹ ∈ zpowers t := (mem_normalizer_iff.1 hcN t).1 (mem_zpowers t)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h1
    rcases hS.zpow_t_eq j with e | e
    · exfalso
      apply hS.t_ne_one
      have : c * t * c⁻¹ = 1 := by rw [← hj, e]
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [this]; group
    · rw [mem_centralizer_singleton_iff]
      have : c * t * c⁻¹ = t := by rw [← hj, e]
      calc c * t = c * t * c⁻¹ * c := by group
        _ = t * c := by rw [this]
  obtain ⟨s, ⟨i, hi, n, hn, hs⟩, φ, -, hα⟩ := hS.exists_act_eq_of_mem_H1 hct hc.1
  have hfix : ∀ g ∈ miyamotoN1 h, i * n * glAut φ g * (i * n)⁻¹ = g := by
    intro g hg
    have e := miyamotoAct_apply_of_mem_centralizer h L η ⟨c, hS.centralizer_le_normalizer hct⟩
      hc.2 (g := ⟨g, miyamotoN1_le_gramSU h hg⟩) hg
    have e2 := congrArg (fun y : gramSU h (miyamotoJ4 K) => (y : GL (Fin 4) K)) e
    simp only at e2
    rw [coe_act_apply_of_eq hα, hs] at e2
    exact e2
  obtain ⟨hφ, rfl⟩ := eq_refl_and_eq_one_of_fixes_N1 h hi hn hfix
  rw [mul_one] at hs
  have hα' : miyamotoAct h L η ⟨c, hS.centralizer_le_normalizer hct⟩ = MulAut.conj s := by
    rw [hα, hφ, miyamotoFieldAut_refl, mul_one]
  obtain ⟨z, hzL, hcz⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η _ s hα'
  simp only at hcz
  set i' : G := ((η.symm s : L) : G) with hi'def
  have hi' : i' ∈ miyamotoI1G h L η := (symm_mem_miyamotoPull_iff h L η).2 (hs ▸ hi)
  have hzC : z ∈ centralizer ({t} : Set G) := by
    have hi'C : i' ∈ centralizer ({t} : Set G) := hS.I1_le_C hi'
    have := mul_mem (inv_mem hi'C) hct
    rwa [hcz, inv_mul_cancel_left] at this
  have hzt : z ∈ zpowers t := by
    rw [← hS.kernel_eq_zpowers']
    exact ⟨hzL, hzC⟩
  have hiz : i' * z = z * i' := (mem_centralizer_iff.1 hzL i' (miyamotoPull_le h L η _ hi'))
  have hz2 : z ^ 2 = 1 := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hzt
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hS.t_two,
      pow_orderOf_eq_one, one_zpow]
  have hi'1 : i' = 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [pow_zero, pow_one, hcz] at hk
      have h1 : i' ∈ L ⊓ centralizer (L : Set G) := by
        refine mem_inf.2 ⟨miyamotoPull_le h L η _ hi', ?_⟩
        rw [eq_inv_of_mul_eq_one_left hk]
        exact inv_mem hzL
      rw [hS.inf_centralizer_eq_bot, mem_bot] at h1
      exact h1
    · have hzk : z ^ 2 ^ k = 1 := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [pow_succ', pow_mul, hz2, one_pow]
      have : i' ^ 2 ^ k = 1 := by
        rw [hcz, (Commute.mul_pow hiz (2 ^ k)), hzk, mul_one] at hk
        exact hk
      exact eq_one_of_odd_of_pow_two_pow_eq_one (hS.odd_card_I1) hi' this
  rw [hcz, hi'1, one_mul]
  exact hzt

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
