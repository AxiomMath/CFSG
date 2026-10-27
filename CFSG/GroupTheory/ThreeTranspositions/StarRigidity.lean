module

public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Fischer.Classification.Uniqueness.Star
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

import CFSG.Fischer.Aut.Complete
import CFSG.GroupTheory.TwoElementSquare
import CFSG.LargeExtraspecial.AS35LAut
import CFSG.GroupTheory.ThreeTranspositions.NoLine
public import TauCeti.GroupTheory.DerivedCentralQuotient
import CFSG.Fischer.Classification.Basic.Local
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
open scoped commutatorElement

theorem centralizer_commutator_eq_bot {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
    (hna : ∃ a b : commutator G, a * b ≠ b * a) :
    Subgroup.centralizer (commutator G : Set G) = ⊥ := by
  have hZ' : Subgroup.center (commutator G) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (commutator G)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab ((Subgroup.center_eq_top_iff.mp h).is_comm.comm a b)
  have hinf : Subgroup.centralizer (commutator G : Set G) ⊓ commutator G = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.2⟩ : commutator G) ∈ Subgroup.center (commutator G) := by
      rw [Subgroup.mem_center_iff]
      intro m
      exact Subtype.ext (by simpa using Subgroup.mem_centralizer_iff.mp hx.1 (m : G) m.2)
    rw [hZ', Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxZ
  have hbot : ⁅Subgroup.centralizer (commutator G : Set G), (⊤ : Subgroup G)⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine le_trans (le_inf ?_ ?_) (le_of_eq hinf)
    · rw [Subgroup.commutator_le]
      intro c hc g _
      have hnormal : (Subgroup.centralizer (commutator G : Set G)).Normal := inferInstance
      have hmem := hnormal.conj_mem (c⁻¹) (Subgroup.inv_mem _ hc) g
      simpa only [commutatorElement_def, mul_assoc] using Subgroup.mul_mem _ hc hmem
    · rw [_root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_rfl
  have hle : Subgroup.centralizer (commutator G : Set G) ≤ Subgroup.center G :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mp hbot
  rw [hZ] at hle
  exact le_bot_iff.mp hle

theorem eq_bot_of_isPGroup_le_normalizer_commutator {G : Type*} [Group G] [Finite G]
    (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
    (hna : ∃ a b : commutator G, a * b ≠ b * a)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPn : commutator G ≤ Subgroup.normalizer (P : Set G)) :
    P = ⊥ := by
  have hR : ((P ⊓ commutator G).subgroupOf (commutator G)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact (le_inf hPn Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hR2 : IsPGroup 2 ((P ⊓ commutator G).subgroupOf (commutator G)) :=
    (hP.to_inf_left (K := commutator G)).of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hRbot : (P ⊓ commutator G).subgroupOf (commutator G) = ⊥ :=
    eq_bot_of_normal_isPGroup_of_isSimpleGroup hna hR2
  have hPG' : P ⊓ commutator G = ⊥ := by
    have h : (P ⊓ commutator G).subgroupOf (commutator G) =
        (⊥ : Subgroup G).subgroupOf (commutator G) := by
      rw [hRbot, Subgroup.bot_subgroupOf]
    have h' := (Subgroup.subgroupOf_inj (K := commutator G)).mp h
    rwa [inf_assoc, inf_idem, bot_inf_eq] at h'
  have hcomm : ⁅P, commutator G⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine le_trans ?_ (le_of_eq hPG')
    rw [Subgroup.commutator_le]
    intro p hp g hg
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hmem : g * p⁻¹ * g⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hPn hg) p⁻¹).mp (Subgroup.inv_mem _ hp)
      simpa only [commutatorElement_def, mul_assoc] using Subgroup.mul_mem _ hp hmem
    · have hnormal : (commutator G).Normal := inferInstance
      have hmem : p * g * p⁻¹ ∈ commutator G := hnormal.conj_mem g hg p
      simpa only [commutatorElement_def, mul_assoc] using
        Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hg)
  have hcent : P ≤ Subgroup.centralizer (commutator G : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := P)
      (H₂ := commutator G)).mp hcomm
  rw [centralizer_commutator_eq_bot hZ hS hna] at hcent
  exact le_bot_iff.mp hcent

section Rigidity

variable {Y : Type} [Group Y] [Finite Y] {F : Set Y} {d : Y} {M : Subgroup Y}

omit [Finite Y] in
theorem isPerfect_commutator_localQuotient (hLS : IsSimpleGroup (commutator (LocalQuotient F d)))
    (hLna : ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a) :
    Group.IsPerfect (commutator (LocalQuotient F d)) := by
  have := hLS
  refine TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun h => ?_
  obtain ⟨a, b, hab⟩ := hLna
  exact hab (h.is_comm.comm a b)

theorem mul_not_mem_of_hyp (hH : Hyp Y F) {a b : Y} (ha : a ∈ F) (hb : b ∈ F) : a * b ∉ F := by
  refine mul_not_mem (fun e he => Pair.orderOf_eq_two hH.pair he) ?_ ?_ ha hb
  · intro e he f hf
    rcases Pair.orderOf_mul_mem hH.pair he hf with h | h | h <;> rw [h] <;> norm_num
  · intro a' ha' b' hb'
    obtain ⟨x, hx⟩ := isConj_iff.1 (Pair.isConj hH.pair ha' hb')
    exact ⟨x, by rw [Pair.closure_eq hH.pair]; exact Subgroup.mem_top x, hx.symm⟩

omit [Finite Y] in
theorem map_eq_one_of_centralizes (hH : Hyp Y F) (hd : d ∈ F)
    (hLS : IsSimpleGroup (commutator (LocalQuotient F d)))
    (hLna : ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a)
    (hMq : commutator (LocalQuotient F d) ≤
      (M.subgroupOf (LocalGroup F d)).map
        (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))))
    {k : ↥(LocalGroup F d)} (hkM : ∀ m ∈ M, (k : Y) * m * (k : Y)⁻¹ = m) :
    QuotientGroup.mk' (Subgroup.center (LocalGroup F d)) k = 1 := by
  have hcent : QuotientGroup.mk' (Subgroup.center (LocalGroup F d)) k ∈
      Subgroup.centralizer (commutator (LocalQuotient F d) : Set (LocalQuotient F d)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨m, hm, hfm⟩ := Subgroup.mem_map.mp (hMq hq)
    have hmM : (m : Y) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have hmk : (m : Y) * (k : Y) = (k : Y) * (m : Y) := by
      calc (m : Y) * (k : Y) = (k * (m : Y) * (k : Y)⁻¹) * (k : Y) := by
            rw [hkM (m : Y) hmM]
        _ = (k : Y) * (m : Y) := by group
    rw [← hfm, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hmk)
  rw [centralizer_commutator_eq_bot
    (Pair.center_localQuotient hH.pair hH.center hH.simple hd) hLS hLna,
    Subgroup.mem_bot] at hcent
  exact hcent

omit [Finite Y] in
theorem mul_mul_inv_centralizes
    (hMn : ∀ c ∈ Subgroup.centralizer ({d} : Set Y), ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    {c : Y} (hcM : ∀ m ∈ M, c * m * c⁻¹ = m)
    {e : Y} (heC : e ∈ Subgroup.centralizer ({d} : Set Y)) {m : Y} (hm : m ∈ M) :
    ((c * e * c⁻¹) * e⁻¹) * m * ((c * e * c⁻¹) * e⁻¹)⁻¹ = m := by
  have hn : e⁻¹ * m * e ∈ M := by
    simpa using hMn e⁻¹ (Subgroup.inv_mem _ heC) m hm
  have hcn : c * (e⁻¹ * m * e) * c⁻¹ = e⁻¹ * m * e := hcM _ hn
  have hcn' : c⁻¹ * (e⁻¹ * m * e) * c = e⁻¹ * m * e := by
    have h := congrArg (fun x : Y => c⁻¹ * x * c) hcn
    rw [show c⁻¹ * (c * (e⁻¹ * m * e) * c⁻¹) * c = e⁻¹ * m * e by group] at h
    exact h.symm
  calc ((c * e * c⁻¹) * e⁻¹) * m * ((c * e * c⁻¹) * e⁻¹)⁻¹
      = c * (e * (c⁻¹ * (e⁻¹ * m * e) * c) * e⁻¹) * c⁻¹ := by group
    _ = c * (e * (e⁻¹ * m * e) * e⁻¹) * c⁻¹ := by rw [hcn']
    _ = c * m * c⁻¹ := by rw [show e * (e⁻¹ * m * e) * e⁻¹ = m by group]
    _ = m := hcM m hm

omit [Finite Y] in
theorem eq_one_or_eq_of_centralizes_large (hH : Hyp Y F) (hna : NonabelianCommutator Y)
    (hT : TripleProperty F) (hd : d ∈ F) (hLS : IsSimpleGroup (commutator (LocalQuotient F d)))
    (hLna : ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a)
    (hMn : ∀ c ∈ Subgroup.centralizer ({d} : Set Y), ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hMq : commutator (LocalQuotient F d) ≤
      (M.subgroupOf (LocalGroup F d)).map
        (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))))
    {c : Y} (hc : c ∈ Subgroup.centralizer ({d} : Set Y))
    (hcM : ∀ m ∈ M, c * m * c⁻¹ = m) : c = 1 ∨ c = d := by
  have hcd : c * d = d * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcomm : ∀ e ∈ LocalClass F d, c * e = e * c := by
    intro e he
    have heC : e ∈ Subgroup.centralizer ({d} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr he.2.2
    have hce : c * e * c⁻¹ ∈ LocalClass F d := by
      have h := (Pair.conj_mem_localClass_iff hH.pair c).2 he
      rwa [hcd, mul_assoc, mul_inv_cancel, mul_one] at h
    have hkL : ((c * e * c⁻¹) * e⁻¹) ∈ LocalGroup F d :=
      Subgroup.mul_mem _ (mem_localGroup hce) (Subgroup.inv_mem _ (mem_localGroup he))
    have hkM : ∀ m ∈ M, (((c * e * c⁻¹) * e⁻¹)) * m * (((c * e * c⁻¹) * e⁻¹))⁻¹ = m :=
      fun m hm => mul_mul_inv_centralizes hMn hcM heC hm
    have hk_one : QuotientGroup.mk' (Subgroup.center (LocalGroup F d))
        ⟨(c * e * c⁻¹) * e⁻¹, hkL⟩ = 1 :=
      map_eq_one_of_centralizes hH hd hLS hLna hMq hkM
    have hstar : starImage F d ⟨c * e * c⁻¹, hce⟩ = starImage F d ⟨e, he⟩ := by
      rw [starImage, starImage]
      change QuotientGroup.mk' (Subgroup.center (LocalGroup F d))
          ⟨c * e * c⁻¹, mem_localGroup hce⟩ =
        QuotientGroup.mk' (Subgroup.center (LocalGroup F d)) ⟨e, mem_localGroup he⟩
      have hprod : (⟨c * e * c⁻¹, mem_localGroup hce⟩ : LocalGroup F d) =
          (⟨(c * e * c⁻¹) * e⁻¹, hkL⟩ : LocalGroup F d) * ⟨e, mem_localGroup he⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group
      rw [hprod, map_mul, hk_one, one_mul]
    have heq : c * e * c⁻¹ = e :=
      congrArg Subtype.val
        (Pair.starImage_injective_of_simple hH.pair hH.center hH.simple hd hstar)
    calc c * e = (c * e * c⁻¹) * c := by group
      _ = e * c := by rw [heq]
  exact Pair.eq_one_or_eq_of_centralizes hH.pair hH.center hH.simple hna hT hd hcd hcomm

theorem mulAut_eq_one_or_conj_of_fix_large (hH : Hyp Y F) (hna : NonabelianCommutator Y)
    (hT : TripleProperty F) (hd : d ∈ F) (hLS : IsSimpleGroup (commutator (LocalQuotient F d)))
    (hLna : ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a)
    (hMn : ∀ c ∈ Subgroup.centralizer ({d} : Set Y), ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hMq : commutator (LocalQuotient F d) ≤
      (M.subgroupOf (LocalGroup F d)).map
        (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))))
    {β : MulAut Y} (hβE : ∀ e ∈ F, β e ∈ F) (hβd : β d = d)
    (hβM : ∀ m ∈ M, β m = m) : β = 1 ∨ β = MulAut.conj d := by
  have hfix : ∀ f ∈ LocalClass F d, β f = f := by
    intro e he
    have heC : e ∈ Subgroup.centralizer ({d} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr he.2.2
    have hβe : β e ∈ LocalClass F d := by
      refine ⟨hβE e he.1, ?_, ?_⟩
      · intro h
        exact he.2.1 (β.injective (by rw [hβd, h]))
      · rw [← hβd, ← map_mul, ← map_mul, he.2.2]
    have hcC : e⁻¹ * β e ∈ Subgroup.centralizer ({d} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : β e * d = d * β e := by
        rw [← hβd, ← map_mul, ← map_mul, he.2.2]
      have hei : e⁻¹ * d = d * e⁻¹ := (Commute.inv_left ((commute_iff_eq e d).mpr he.2.2)).eq
      calc e⁻¹ * β e * d = e⁻¹ * (β e * d) := by group
        _ = e⁻¹ * (d * β e) := by rw [h1]
        _ = d * (e⁻¹ * β e) := by rw [← mul_assoc, hei, mul_assoc]
    have hcM : ∀ m ∈ M, (e⁻¹ * β e) * m * (e⁻¹ * β e)⁻¹ = m := by
      intro m hm
      have hem : e * m * e⁻¹ ∈ M := hMn e heC m hm
      have hβem : β (e * m * e⁻¹) = e * m * e⁻¹ := hβM _ hem
      calc (e⁻¹ * β e) * m * (e⁻¹ * β e)⁻¹
          = e⁻¹ * (β e * m * (β e)⁻¹) * e := by group
        _ = e⁻¹ * β (e * m * e⁻¹) * e := by
            rw [map_mul, map_mul, map_inv, hβM m hm]
        _ = m := by rw [hβem]; group
    rcases eq_one_or_eq_of_centralizes_large hH hna hT hd hLS hLna hMn hMq hcC hcM with h | h
    · have h1 : e⁻¹ * β e = 1 := by rw [← h]
      calc β e = e * (e⁻¹ * β e) := by group
        _ = e := by rw [h1, mul_one]
    · exfalso
      have h1 : e⁻¹ * β e = d := by rw [← h]
      have hβe_eq : β e = e * d := by
        calc β e = e * (e⁻¹ * β e) := by group
          _ = e * d := by rw [h1]
      exact mul_not_mem_of_hyp hH he.1 hd (hβe_eq ▸ hβe.1)
  exact CFSG.LargeExtraspecial.AS35L.mulAut_eq_one_or_conj_of_fix hH.pair hH.center hH.simple hna hT
    hd β hβE hβd hfix

omit [Finite Y] in
theorem commutator_commutator_normalized
    (hMn : ∀ c ∈ Subgroup.centralizer ({d} : Set Y), ∀ m ∈ M, c * m * c⁻¹ ∈ M) :
    ∀ c ∈ Subgroup.centralizer ({d} : Set Y), ∀ n ∈ ⁅M, M⁆, c * n * c⁻¹ ∈ ⁅M, M⁆ := by
  intro c hc n hn
  have hMmap : M.map (MulAut.conj c).toMonoidHom = M := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
      simpa [MulAut.conj_apply] using hMn c hc m hm
    · intro m hm
      refine Subgroup.mem_map.mpr ⟨c⁻¹ * m * c, ?_, ?_⟩
      · simpa [MulAut.conj_apply] using hMn c⁻¹ (Subgroup.inv_mem _ hc) m hm
      · show (MulAut.conj c) (c⁻¹ * m * c) = m
        rw [MulAut.conj_apply]
        group
  have hmap : (⁅M, M⁆).map (MulAut.conj c).toMonoidHom = ⁅M, M⁆ := by
    rw [Subgroup.map_commutator, hMmap]
  have hmem : (MulAut.conj c).toMonoidHom n ∈ (⁅M, M⁆).map (MulAut.conj c).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hn
  rw [hmap] at hmem
  simpa [MulAut.conj_apply] using hmem

omit [Finite Y] in
theorem commutator_le_map_commutator_commutator
    (hLS : IsSimpleGroup (commutator (LocalQuotient F d)))
    (hLna : ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a)
    (hML : M ≤ LocalGroup F d)
    (hMq : commutator (LocalQuotient F d) ≤
      (M.subgroupOf (LocalGroup F d)).map
        (QuotientGroup.mk' (Subgroup.center (LocalGroup F d)))) :
    commutator (LocalQuotient F d) ≤
      (⁅M, M⁆.subgroupOf (LocalGroup F d)).map
        (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))) := by
  have : Group.IsPerfect (commutator (LocalQuotient F d)) :=
    isPerfect_commutator_localQuotient hLS hLna
  have hperf : ⁅commutator (LocalQuotient F d), commutator (LocalQuotient F d)⁆ =
      commutator (LocalQuotient F d) := Subgroup.commutator_eq_self
  rw [← hperf]
  refine (Subgroup.commutator_mono hMq hMq).trans (le_of_eq ?_)
  rw [← Subgroup.map_commutator (M.subgroupOf (LocalGroup F d))
    (M.subgroupOf (LocalGroup F d)) (QuotientGroup.mk' (Subgroup.center (LocalGroup F d)))]
  congr 1
  have h := Subgroup.map_commutator (H₁ := M.subgroupOf (LocalGroup F d))
    (H₂ := M.subgroupOf (LocalGroup F d)) (f := (LocalGroup F d).subtype)
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hML] at h
  rw [← h]
  refine le_antisymm ?_ ?_
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ hx)
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    rwa [show y = x from Subtype.ext hyx] at hy

theorem map_inf_subgroupOf_localQuotient_eq_bot (hH : Hyp Y F) (hd : d ∈ F)
    (hLS : IsSimpleGroup (commutator (LocalQuotient F d)))
    (hLna : ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a)
    (hML : M ≤ LocalGroup F d)
    (hMq : commutator (LocalQuotient F d) ≤
      (M.subgroupOf (LocalGroup F d)).map
        (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))))
    {B : Subgroup Y} (hB : IsPGroup 2 B)
    (hMB : ∀ m ∈ M, ∀ b ∈ B, m * b * m⁻¹ ∈ B) :
    ((B ⊓ M).subgroupOf (LocalGroup F d)).map
      (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))) = ⊥ := by
  let f : ↥(LocalGroup F d) →* LocalQuotient F d :=
    QuotientGroup.mk' (Subgroup.center (LocalGroup F d))
  let K : Subgroup ↥(LocalGroup F d) := (B ⊓ M).subgroupOf (LocalGroup F d)
  let Q : Subgroup (LocalQuotient F d) := K.map f
  have hK2 : IsPGroup 2 K :=
    (hB.to_inf_left (K := M)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hML)).symm
  have hconjK : ∀ m ∈ M.subgroupOf (LocalGroup F d), ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
    intro m hm k hk
    rw [Subgroup.mem_subgroupOf] at hm hk ⊢
    obtain ⟨hkB, hkM⟩ := Subgroup.mem_inf.mp hk
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := hMB (m : Y) hm (k : Y) hkB
      simpa using h
    · simpa using M.mul_mem (M.mul_mem hm hkM) (M.inv_mem hm)
  have hQn : commutator (LocalQuotient F d) ≤
      Subgroup.normalizer (Q : Set (LocalQuotient F d)) := by
    refine hMq.trans ?_
    intro p hp
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hp
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hq
      refine Subgroup.mem_map.mpr ⟨m * k * m⁻¹, hconjK m hm k hk, ?_⟩
      show f (m * k * m⁻¹) = f m * f k * (f m)⁻¹
      simp only [map_mul, map_inv]
    · intro hq
      obtain ⟨k, hk, hkq⟩ := Subgroup.mem_map.mp hq
      have hkq' : f k = f m * q * (f m)⁻¹ := hkq
      have hmem : m⁻¹ * k * m ∈ K := by
        simpa using hconjK m⁻¹ (Subgroup.inv_mem _ hm) k hk
      refine Subgroup.mem_map.mpr ⟨m⁻¹ * k * m, hmem, ?_⟩
      calc f (m⁻¹ * k * m) = (f m)⁻¹ * f k * f m := by simp only [map_mul, map_inv]
        _ = q := by rw [hkq']; group
  exact eq_bot_of_isPGroup_le_normalizer_commutator
    (Pair.center_localQuotient hH.pair hH.center hH.simple hd) hLS hLna (hK2.map f) hQn

omit [Finite Y] in
theorem centralizes_localGroup_of_map_inf_eq_bot (hML : M ≤ LocalGroup F d)
    {B : Subgroup Y}
    (hQbot : ((B ⊓ M).subgroupOf (LocalGroup F d)).map
      (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))) = ⊥) :
    ∀ x ∈ B ⊓ M, ∀ l ∈ LocalGroup F d, l * x = x * l := by
  intro x hx l hl
  have hxK : (⟨x, hML hx.2⟩ : ↥(LocalGroup F d)) ∈
      (B ⊓ M).subgroupOf (LocalGroup F d) := Subgroup.mem_subgroupOf.mpr hx
  have hx1 : QuotientGroup.mk' (Subgroup.center (LocalGroup F d)) ⟨x, hML hx.2⟩ = 1 := by
    have hmem : QuotientGroup.mk' (Subgroup.center (LocalGroup F d)) ⟨x, hML hx.2⟩ ∈
        ((B ⊓ M).subgroupOf (LocalGroup F d)).map
          (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))) :=
      Subgroup.mem_map.mpr ⟨_, hxK, rfl⟩
    rwa [hQbot, Subgroup.mem_bot] at hmem
  have hxcenter : (⟨x, hML hx.2⟩ : ↥(LocalGroup F d)) ∈ Subgroup.center (LocalGroup F d) := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact hx1
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxcenter ⟨l, hl⟩)

theorem eq_one_or_eq_of_isPGroup_normalized (hH : Hyp Y F) (hna : NonabelianCommutator Y)
    (hT : TripleProperty F) (hd : d ∈ F) (hLS : IsSimpleGroup (commutator (LocalQuotient F d)))
    (hLna : ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a)
    (hML : M ≤ LocalGroup F d)
    (hMn : ∀ c ∈ Subgroup.centralizer ({d} : Set Y), ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hMq : commutator (LocalQuotient F d) ≤
      (M.subgroupOf (LocalGroup F d)).map
        (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))))
    {B : Subgroup Y} (hB : IsPGroup 2 B)
    (hBd : B ≤ Subgroup.centralizer ({d} : Set Y))
    (hMB : ∀ m ∈ M, ∀ b ∈ B, m * b * m⁻¹ ∈ B)
    {b : Y} (hb : b ∈ B) : b = 1 ∨ b = d := by
  have hQbot := map_inf_subgroupOf_localQuotient_eq_bot hH hd hLS hLna hML hMq hB hMB
  have hBMcenter := centralizes_localGroup_of_map_inf_eq_bot hML hQbot
  have hcommBM : ⁅B, M⁆ ≤ Subgroup.centralizer (M : Set Y) := by
    rw [Subgroup.commutator_le]
    intro b' hb' m hm
    have hmem : ⁅b', m⁆ ∈ B ⊓ M := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h := hMB m hm b'⁻¹ (Subgroup.inv_mem _ hb')
        simpa only [commutatorElement_def, mul_assoc] using Subgroup.mul_mem _ hb' h
      · have h := hMn b' (hBd hb') m hm
        simpa only [commutatorElement_def, mul_assoc] using
          Subgroup.mul_mem _ h (Subgroup.inv_mem _ hm)
    rw [Subgroup.mem_centralizer_iff]
    intro m' hm'
    exact hBMcenter ⁅b', m⁆ hmem m' (hML hm')
  have h3 : ⁅⁅B, M⁆, M⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ⁅B, M⁆) (H₂ := M)).mpr hcommBM
  have h4 : ⁅⁅M, M⁆, B⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := M) (H₂ := M) (H₃ := B) ?_ ?_
    · rw [Subgroup.commutator_comm (H₁ := M) (H₂ := B)]
      exact h3
    · exact h3
  have hNB : ⁅M, M⁆ ≤ Subgroup.centralizer (B : Set Y) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ⁅M, M⁆) (H₂ := B)).mp h4
  have hbN : ∀ n ∈ ⁅M, M⁆, b * n * b⁻¹ = n := by
    intro n hn
    have h := (Subgroup.mem_centralizer_iff.mp (hNB hn)) b hb
    calc b * n * b⁻¹ = (n * b) * b⁻¹ := by rw [h]
      _ = n := by rw [mul_assoc, mul_inv_cancel, mul_one]
  rcases eq_one_or_eq_of_centralizes_large hH hna hT hd hLS hLna
    (commutator_commutator_normalized hMn)
    (commutator_le_map_commutator_commutator hLS hLna hML hMq) (hBd hb) hbN with h | h
  · exact Or.inl h
  · exact Or.inr h

omit [Finite Y] in
theorem commutatorElement_mul_commute {a b δ₁ δ₂ : Y}
    (h1b : Commute δ₁ (b * δ₂)) (h2a : Commute δ₂ a) :
    ⁅a * δ₁, b * δ₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, h1b.commutator_eq,
    commutatorElement_mul_right_eq_mul_conj, h2a.symm.commutator_eq, mul_one, mul_one]
  group

omit [Finite Y] in
theorem mulAut_mul_inv_mem_comap_conj {A : Subgroup (MulAut Y)}
    (hAn : ∀ m ∈ M, ∀ β ∈ A, MulAut.conj m * β * (MulAut.conj m)⁻¹ ∈ A)
    {β : MulAut Y} (hβ : β ∈ A) {m : Y} (hm : m ∈ M) :
    β m * m⁻¹ ∈ A.comap (MulAut.conj : Y →* MulAut Y) := by
  change MulAut.conj (β m * m⁻¹) ∈ A
  have h1 : MulAut.conj m * β⁻¹ * (MulAut.conj m)⁻¹ ∈ A := hAn m hm β⁻¹ (Subgroup.inv_mem _ hβ)
  have h2 : β * (MulAut.conj m * β⁻¹ * (MulAut.conj m)⁻¹) ∈ A :=
    Subgroup.mul_mem _ hβ h1
  have hconj : MulAut.conj (β m) = β * MulAut.conj m * β⁻¹ := by
    ext x
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv]
    simp
  convert h2 using 2
  rw [map_mul, map_inv, hconj]
  group

omit [Finite Y] in
theorem mulAut_fixes_commutator_commutator {A : Subgroup (MulAut Y)}
    (hML : M ≤ LocalGroup F d)
    (hAn : ∀ m ∈ M, ∀ β ∈ A, MulAut.conj m * β * (MulAut.conj m)⁻¹ ∈ A)
    (hBval : ∀ b ∈ A.comap (MulAut.conj : Y →* MulAut Y), b = 1 ∨ b = d)
    {β : MulAut Y} (hβ : β ∈ A) : ∀ n ∈ ⁅M, M⁆, β n = n := by
  have hdcomm : ∀ x ∈ M, Commute d x := fun x hx =>
    ((commute_iff_eq x d).mpr (commute_of_mem_localGroup' (hML hx))).symm
  have hstep : ∀ m ∈ M, β m * m⁻¹ = 1 ∨ β m * m⁻¹ = d := fun m hm =>
    hBval _ (mulAut_mul_inv_mem_comap_conj hAn hβ hm)
  have hfixgen : ∀ a ∈ M, ∀ b ∈ M, β ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a ha b hb
    set δ₁ : Y := β a * a⁻¹ with hδ₁
    set δ₂ : Y := β b * b⁻¹ with hδ₂
    have h1 : δ₁ = 1 ∨ δ₁ = d := hstep a ha
    have h2 : δ₂ = 1 ∨ δ₂ = d := hstep b hb
    have hβa : β a = a * δ₁ := by
      have h : β a = δ₁ * a := by rw [hδ₁]; group
      rw [h]
      rcases h1 with h1' | h1' <;> rw [h1']
      · simp
      · exact (hdcomm a ha).eq
    have hβb : β b = b * δ₂ := by
      have h : β b = δ₂ * b := by rw [hδ₂]; group
      rw [h]
      rcases h2 with h2' | h2' <;> rw [h2']
      · simp
      · exact (hdcomm b hb).eq
    have hcomm2a : Commute δ₂ a := by
      rcases h2 with h | h <;> rw [h]
      · exact Commute.one_left a
      · exact hdcomm a ha
    have hcomm1b : Commute δ₁ (b * δ₂) := by
      rcases h1 with h | h <;> rw [h]
      · exact Commute.one_left _
      · rcases h2 with h2' | h2' <;> rw [h2']
        · simpa using hdcomm b hb
        · exact (hdcomm b hb).mul_right (Commute.refl d)
    rw [map_commutatorElement, hβa, hβb]
    exact commutatorElement_mul_commute hcomm1b hcomm2a
  intro n hn
  rw [Subgroup.commutator_def] at hn
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
    exact hfixgen g₁ hg₁ g₂ hg₂
  | one => exact map_one β
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  | inv x _ hx => rw [map_inv, hx]

theorem mulAut_eq_one_or_conj_of_isPGroup_normalized (hH : Hyp Y F)
    (hna : NonabelianCommutator Y) (hT : TripleProperty F) (hd : d ∈ F)
    (hLS : IsSimpleGroup (commutator (LocalQuotient F d)))
    (hLna : ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a)
    (hML : M ≤ LocalGroup F d)
    (hMn : ∀ c ∈ Subgroup.centralizer ({d} : Set Y), ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hMq : commutator (LocalQuotient F d) ≤
      (M.subgroupOf (LocalGroup F d)).map
        (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))))
    {A : Subgroup (MulAut Y)} (hA : IsPGroup 2 A)
    (hAE : ∀ β ∈ A, ∀ e ∈ F, β e ∈ F) (hAd : ∀ β ∈ A, β d = d)
    (hAn : ∀ m ∈ M, ∀ β ∈ A, MulAut.conj m * β * (MulAut.conj m)⁻¹ ∈ A)
    {β : MulAut Y} (hβ : β ∈ A) : β = 1 ∨ β = MulAut.conj d := by
  have hinj := CFSG.Fischer.mulAutConj_injective hH.center
  let B : Subgroup Y := A.comap (MulAut.conj : Y →* MulAut Y)
  have hB2 : IsPGroup 2 B := by
    have hmap : B.map (MulAut.conj : Y →* MulAut Y) ≤ A :=
      Subgroup.map_comap_le (MulAut.conj : Y →* MulAut Y) A
    exact (hA.to_le hmap).of_equiv
      (Subgroup.equivMapOfInjective B (MulAut.conj : Y →* MulAut Y) hinj).symm
  have hBd : B ≤ Subgroup.centralizer ({d} : Set Y) := by
    intro b hb
    have h1 : MulAut.conj b d = d := hAd _ hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [MulAut.conj_apply] at h1
    calc b * d = (b * d * b⁻¹) * b := by group
      _ = d * b := by rw [h1]
  have hMB : ∀ m ∈ M, ∀ b ∈ B, m * b * m⁻¹ ∈ B := by
    intro m hm b hb
    have h0 : MulAut.conj b ∈ A := hb
    have h1 : MulAut.conj m * MulAut.conj b * (MulAut.conj m)⁻¹ ∈ A := hAn m hm _ h0
    change MulAut.conj (m * b * m⁻¹) ∈ A
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hBval : ∀ b ∈ B, b = 1 ∨ b = d := fun b hb =>
    eq_one_or_eq_of_isPGroup_normalized hH hna hT hd hLS hLna hML hMn hMq hB2 hBd hMB hb
  exact mulAut_eq_one_or_conj_of_fix_large hH hna hT hd hLS hLna
    (commutator_commutator_normalized hMn)
    (commutator_le_map_commutator_commutator hLS hLna hML hMq)
    (fun e he => hAE β hβ e he) (hAd β hβ)
    (mulAut_fixes_commutator_commutator hML hAn hBval hβ)

theorem card_le_two_of_isPGroup_normalized (hH : Hyp Y F) (hna : NonabelianCommutator Y)
    (hT : TripleProperty F) (hd : d ∈ F)
    (hLS : IsSimpleGroup (commutator (LocalQuotient F d)))
    (hLna : ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a)
    (hML : M ≤ LocalGroup F d)
    (hMn : ∀ c ∈ Subgroup.centralizer ({d} : Set Y), ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hMq : commutator (LocalQuotient F d) ≤
      (M.subgroupOf (LocalGroup F d)).map
        (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))))
    {A : Subgroup (MulAut Y)} (hA : IsPGroup 2 A)
    (hAE : ∀ β ∈ A, ∀ e ∈ F, β e ∈ F) (hAd : ∀ β ∈ A, β d = d)
    (hAn : ∀ m ∈ M, ∀ β ∈ A, MulAut.conj m * β * (MulAut.conj m)⁻¹ ∈ A) :
    Nat.card A ≤ 2 := by
  have hsub : (A : Set (MulAut Y)) ⊆ ({1, MulAut.conj d} : Set (MulAut Y)) := by
    intro β hβ
    rcases mulAut_eq_one_or_conj_of_isPGroup_normalized hH hna hT hd hLS hLna hML hMn hMq hA hAE
      hAd hAn hβ with h | h <;> simp [h]
  have h1 : Nat.card (A : Set (MulAut Y)) ≤ Nat.card ({1, MulAut.conj d} : Set (MulAut Y)) :=
    Nat.card_mono (Set.toFinite _) hsub
  have h2 : Nat.card ({1, MulAut.conj d} : Set (MulAut Y)) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    calc ({1, MulAut.conj d} : Set (MulAut Y)).ncard
        ≤ ({MulAut.conj d} : Set (MulAut Y)).ncard + 1 := Set.ncard_insert_le _ _
      _ = 1 + 1 := by rw [Set.ncard_singleton]
      _ = 2 := rfl
  exact le_trans (le_of_eq rfl) (h1.trans h2)

abbrev localPerfectResidual (F : Set Y) (d : Y) : Subgroup Y :=
  (perfectResidual ↥(LocalGroup F d)).map (LocalGroup F d).subtype

omit [Finite Y] in
theorem localPerfectResidual_eq_perfectResidualOf (F : Set Y) (d : Y) :
    localPerfectResidual F d =
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf (LocalGroup F d) :=
  rfl

theorem localPerfectResidual_isPerfect (F : Set Y) (d : Y) :
    Group.IsPerfect (localPerfectResidual F d) := by
  rw [localPerfectResidual_eq_perfectResidualOf]
  exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect (LocalGroup F d)

omit [Finite Y] in
theorem localPerfectResidual_le_localGroup (F : Set Y) (d : Y) :
    localPerfectResidual F d ≤ LocalGroup F d := by
  rw [localPerfectResidual_eq_perfectResidualOf]
  exact Subgroup.map_subtype_le _

omit [Finite Y] in
theorem mem_normalizer_localGroup (hH : Hyp Y F) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({d} : Set Y)) :
    c ∈ Subgroup.normalizer (LocalGroup F d : Set Y) := by
  have hforward : ∀ u ∈ Subgroup.centralizer ({d} : Set Y), ∀ x ∈ LocalGroup F d,
      u * x * u⁻¹ ∈ LocalGroup F d := by
    intro u hu x hx
    have hud : u * d = d * u := Subgroup.mem_centralizer_singleton_iff.mp hu
    rw [LocalGroup] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      refine Subgroup.subset_closure ?_
      have h := (Pair.conj_mem_localClass_iff hH.pair u).2 hy
      rwa [hud, mul_assoc, mul_inv_cancel, mul_one] at h
    | one => simp
    | mul y z _ _ hy hz =>
      rw [show u * (y * z) * u⁻¹ = (u * y * u⁻¹) * (u * z * u⁻¹) by group]
      exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      rw [show u * y⁻¹ * u⁻¹ = (u * y * u⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward c hc x
  · intro hx
    have h := hforward c⁻¹ (Subgroup.inv_mem _ hc) _ hx
    rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h

omit [Finite Y] in
theorem centralizer_normalizes_localPerfectResidual (hH : Hyp Y F) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({d} : Set Y)) :
    ∀ m ∈ localPerfectResidual F d, c * m * c⁻¹ ∈ localPerfectResidual F d := by
  simp only [localPerfectResidual_eq_perfectResidualOf]
  have hmem :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains (LocalGroup F d)
      (mem_normalizer_localGroup hH hc)
  rw [Subgroup.mem_normalizer_iff] at hmem
  exact fun m hm => (hmem m).mp hm

theorem commutator_le_map_localPerfectResidual
    (hLS : IsSimpleGroup (commutator (LocalQuotient F d)))
    (hLna : ∃ a b : commutator (LocalQuotient F d), a * b ≠ b * a) :
    commutator (LocalQuotient F d) ≤
      ((localPerfectResidual F d).subgroupOf (LocalGroup F d)).map
        (QuotientGroup.mk' (Subgroup.center (LocalGroup F d))) := by
  simp only [localPerfectResidual_eq_perfectResidualOf]
  have hsub : (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (LocalGroup F d)).subgroupOf (LocalGroup F d) =
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥(LocalGroup F d) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hx
      rwa [show p = x from Subtype.ext hpx] at hp
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ hx)
  rw [hsub]
  rw [CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq
    (QuotientGroup.mk' (Subgroup.center (LocalGroup F d)))
    (QuotientGroup.mk'_surjective _)]
  exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual
    (commutator (LocalQuotient F d)) (isPerfect_commutator_localQuotient hLS hLna)

theorem localPerfectResidual_le_centralizer : localPerfectResidual F d ≤
    (perfectResidual ↥(Subgroup.centralizer ({d} : Set Y))).map
      (Subgroup.centralizer ({d} : Set Y)).subtype := by
  have hle : localPerfectResidual F d ≤ Subgroup.centralizer ({d} : Set Y) := by
    refine (localPerfectResidual_le_localGroup F d).trans ?_
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_localGroup' hx)
  exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
    (localPerfectResidual F d) (Subgroup.centralizer ({d} : Set Y))
    (localPerfectResidual_isPerfect F d) hle

end Rigidity

end CFSG.GroupTheory.ThreeTranspositions
