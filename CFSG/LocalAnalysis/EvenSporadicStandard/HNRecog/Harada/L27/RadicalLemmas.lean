module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.A5Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup
open scoped commutatorElement

private theorem card_of_equiv_a5 {X : Type*} [Group X] (F : Subgroup X)
    (eF : F ≃* alternatingGroup (Fin 5)) : Nat.card F = 60 := by
  rw [Nat.card_congr eF.toEquiv, card_alternatingGroup_five]

private theorem orderOf_of_mul_self_eq_one {X : Type*} [Group X] {v : X} (hv2 : v * v = 1)
    (hv : v ≠ 1) : orderOf v = 2 := by
  rw [orderOf_eq_prime_iff]
  exact ⟨by rwa [pow_two], hv⟩

theorem not_mem_solvableRadical {X : Type*} [Group X] [Finite X] (P : Subgroup X)
    (hP : P ⊓ CFSG.solvableRadical X = ⊥) {v : X} (hv : v ≠ 1)
    (hcard : Nat.card (Subgroup.centralizer ({v} : Set X)) ≤ Nat.card P) :
    v ∉ CFSG.solvableRadical X := by
  classical
  intro hvS0
  set S : Subgroup X := CFSG.solvableRadical X with hS
  haveI hSn : S.Normal := by rw [hS]; infer_instance
  have hP' : P ⊓ S = ⊥ := by rw [hS]; exact hP
  have hvS : v ∈ S := by rw [hS]; exact hvS0
  have hsub : conjugatesOf v ⊆ (S : Set X) := by
    intro x hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 (show IsConj v x from hx)
    exact hSn.conj_mem v hvS c
  have h1c : (1 : X) ∉ conjugatesOf v := by
    intro h
    exact hv (isConj_one_left.mp (show IsConj v 1 from h))
  have hproper : conjugatesOf v ⊂ (S : Set X) :=
    (Set.ssubset_iff_of_subset hsub).mpr ⟨(1 : X), S.one_mem, h1c⟩
  have hfin : (S : Set X).Finite := Set.toFinite _
  have hcardS : Nat.card S = (S : Set X).ncard := Nat.card_coe_set_eq (S : Set X)
  have hindex_lt : (Subgroup.centralizer ({v} : Set X)).index < Nat.card S := by
    rw [Subgroup.index_centralizer_eq_ncard, hcardS]
    exact Set.ncard_lt_ncard hproper hfin
  have hPS : Nat.card P ≤ Nat.card (X ⧸ S) := by
    let f : P →* X ⧸ S := (QuotientGroup.mk' S).comp P.subtype
    have hker : f.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      rw [MonoidHom.mem_ker] at hx
      apply Subtype.ext
      have hxS : (x : X) ∈ S := by
        rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      have : (x : X) ∈ P ⊓ S := ⟨x.2, hxS⟩
      rw [hP'] at this
      simpa using this
    have hfinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
    exact Nat.card_le_card_of_injective f hfinj
  have hCpos : 0 < Nat.card (Subgroup.centralizer ({v} : Set X)) := Nat.card_pos
  have h1 := Nat.mul_lt_mul_of_pos_right hindex_lt hCpos
  have h2 : Nat.card S * Nat.card (Subgroup.centralizer ({v} : Set X)) ≤
      Nat.card S * Nat.card (X ⧸ S) :=
    Nat.mul_le_mul_left _ (hcard.trans hPS)
  have h3 : Nat.card S * Nat.card (X ⧸ S) = Nat.card X := by
    rw [mul_comm, ← Subgroup.card_eq_card_quotient_mul_card_subgroup S]
  have h4 : (Subgroup.centralizer ({v} : Set X)).index *
      Nat.card (Subgroup.centralizer ({v} : Set X)) = Nat.card X :=
    Subgroup.index_mul_card _
  have : Nat.card X < Nat.card X := by
    calc Nat.card X = (Subgroup.centralizer ({v} : Set X)).index *
          Nat.card (Subgroup.centralizer ({v} : Set X)) := h4.symm
      _ < Nat.card S * Nat.card (Subgroup.centralizer ({v} : Set X)) := h1
      _ ≤ Nat.card S * Nat.card (X ⧸ S) := h2
      _ = Nat.card X := h3
  exact lt_irrefl _ this

theorem card_centralizer_le_one_twenty {X : Type*} [Group X] [Finite X] (F : Subgroup X)
    (eF : F ≃* alternatingGroup (Fin 5)) {v : X} (hv2 : v * v = 1)
    (hFv : ∀ f ∈ F, f * v = v * f)
    (hC : ∀ g : X, g * v = v * g → g ∈ F ⊔ Subgroup.zpowers v) :
    Nat.card (Subgroup.centralizer ({v} : Set X)) ≤ 120 := by
  classical
  by_cases hvF : v ∈ F
  · have hv1 : v = 1 := eq_one_of_forall_comm_of_equiv_a5 F eF hvF hFv
    have hcent : Subgroup.centralizer ({v} : Set X) = ⊤ := by
      rw [hv1, eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      simp
    have hFtop : F = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg := hC g (by rw [hv1]; simp)
      rwa [hv1, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hg
    have hcardF : Nat.card F = 60 := card_of_equiv_a5 F eF
    have hXeqF : Nat.card X = Nat.card F := by rw [hFtop, Subgroup.card_top]
    calc Nat.card (Subgroup.centralizer ({v} : Set X))
        = Nat.card (⊤ : Subgroup X) := by rw [hcent]
      _ = Nat.card X := Subgroup.card_top
      _ = Nat.card F := hXeqF
      _ = 60 := hcardF
      _ ≤ 120 := by norm_num
  · have hv1 : v ≠ 1 := fun h => hvF (h ▸ F.one_mem)
    have horder : orderOf v = 2 := orderOf_of_mul_self_eq_one hv2 hv1
    have hzpc : Nat.card (Subgroup.zpowers v) = 2 := by rw [Nat.card_zpowers, horder]
    have hcardF : Nat.card F = 60 := card_of_equiv_a5 F eF
    have hcomm : ∀ a : F, ∀ b : Subgroup.zpowers v, Commute ((a : X)) ((b : X)) := by
      intro a b
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
      rw [← hk]
      exact (show Commute ((a : X)) v from hFv (a : X) a.2).zpow_right k
    let φ : F × Subgroup.zpowers v →* X :=
      MonoidHom.noncommCoprod F.subtype (Subgroup.zpowers v).subtype hcomm
    have hrange : φ.range = F ⊔ Subgroup.zpowers v := by
      have h := MonoidHom.noncommCoprod_range F.subtype (Subgroup.zpowers v).subtype hcomm
      rw [Subgroup.range_subtype, Subgroup.range_subtype] at h
      exact h
    have hsurj : Function.Surjective φ.rangeRestrict := MonoidHom.rangeRestrict_surjective φ
    have hle : Nat.card (↥(F ⊔ Subgroup.zpowers v)) ≤ Nat.card (F × Subgroup.zpowers v) := by
      have h := Nat.card_le_card_of_surjective φ.rangeRestrict hsurj
      rwa [hrange] at h
    have hprod : Nat.card (F × Subgroup.zpowers v) = 120 := by
      rw [Nat.card_prod, hcardF, hzpc]
    have hsup_le : Nat.card (↥(F ⊔ Subgroup.zpowers v)) ≤ 120 := by
      rw [← hprod]; exact hle
    have hcent_le : Subgroup.centralizer ({v} : Set X) ≤ F ⊔ Subgroup.zpowers v := by
      intro g hg
      exact hC g ((Subgroup.mem_centralizer_iff.mp hg v (Set.mem_singleton v)).symm)
    have hcard_le : Nat.card (Subgroup.centralizer ({v} : Set X)) ≤
        Nat.card (↥(F ⊔ Subgroup.zpowers v)) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hcent_le)
        (Subgroup.inclusion_injective hcent_le)
    exact hcard_le.trans hsup_le

theorem eq_one_of_commute_of_normal_solvable {X : Type*} [Group X] (F : Subgroup X)
    (eF : F ≃* alternatingGroup (Fin 5)) {v : X} (hv2 : v * v = 1)
    (hFv : ∀ f ∈ F, f * v = v * f) (hC : ∀ g : X, g * v = v * g → g ∈ F ⊔ Subgroup.zpowers v)
    (S : Subgroup X) [S.Normal] (hS : Group.IsSolvable S) (hvS : v ∉ S) :
    ∀ s ∈ S, v * s = s * v → s = 1 := by
  classical
  haveI hSn : S.Normal := inferInstance
  intro s hsS hvs
  have hv1 : v ≠ 1 := fun h => hvS (h ▸ S.one_mem)
  have horder : orderOf v = 2 := orderOf_of_mul_self_eq_one hv2 hv1
  have hs_mem : s ∈ F ⊔ Subgroup.zpowers v := hC s hvs.symm
  have hcomm : ∀ a : F, ∀ b : Subgroup.zpowers v, Commute ((a : X)) ((b : X)) := by
    intro a b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [← hk]
    exact (show Commute ((a : X)) v from hFv (a : X) a.2).zpow_right k
  let φ : F × Subgroup.zpowers v →* X :=
    MonoidHom.noncommCoprod F.subtype (Subgroup.zpowers v).subtype hcomm
  have hrange : φ.range = F ⊔ Subgroup.zpowers v := by
    have h := MonoidHom.noncommCoprod_range F.subtype (Subgroup.zpowers v).subtype hcomm
    rw [Subgroup.range_subtype, Subgroup.range_subtype] at h
    exact h
  obtain ⟨⟨a, b⟩, hab⟩ :=
    MonoidHom.mem_range.mp (by rw [hrange]; exact hs_mem)
  have hs_eq : s = (a : X) * (b : X) := hab.symm
  have hb : (b : X) = 1 ∨ (b : X) = v := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
    have hmod := zpow_mod_orderOf v k
    rw [horder] at hmod
    have hcases : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by
      simpa using Int.emod_two_eq_zero_or_one k
    rcases hcases with h0 | h1
    · left; rw [← hk, ← hmod, h0]; simp
    · right; rw [← hk, ← hmod, h1]; simp
  rcases hb with hb1 | hbv
  · have haS : (a : X) ∈ S := by
      have hsa : s = (a : X) := by rw [hs_eq, hb1, mul_one]
      exact hsa ▸ hsS
    have habot : (a : X) ∈ F ⊓ S := ⟨a.2, haS⟩
    rw [inf_eq_bot_of_equiv_a5 F eF S hS, Subgroup.mem_bot] at habot
    calc s = (a : X) * (b : X) := hs_eq
      _ = (a : X) * 1 := by rw [hb1]
      _ = 1 := by rw [habot, mul_one]
  · have ha_one : (a : X) = 1 := by
      apply eq_one_of_forall_comm_of_equiv_a5 F eF a.2
      intro f' hf'
      have hcomm_eq : ⁅(f' : X), (a : X)⁆ = ⁅(f' : X), s⁆ := by
        rw [hs_eq, hbv, commutatorElement_mul_right_eq_mul_conj,
          commutatorElement_eq_one_iff_commute.mpr (hFv (f' : X) hf')]
        group
      have hmemF : ⁅(f' : X), (a : X)⁆ ∈ F := by
        rw [commutatorElement_def]
        exact F.mul_mem (F.mul_mem (F.mul_mem hf' a.2) (F.inv_mem hf')) (F.inv_mem a.2)
      have hmemS : ⁅(f' : X), (a : X)⁆ ∈ S := by
        rw [hcomm_eq, commutatorElement_def]
        exact S.mul_mem (hSn.conj_mem s hsS f') (S.inv_mem hsS)
      have hbot : ⁅(f' : X), (a : X)⁆ ∈ F ⊓ S := ⟨hmemF, hmemS⟩
      rw [inf_eq_bot_of_equiv_a5 F eF S hS, Subgroup.mem_bot] at hbot
      exact commutatorElement_eq_one_iff_commute.mp hbot
    have hs_eq_v : s = v := by rw [hs_eq, hbv, ha_one, one_mul]
    exact absurd (hs_eq_v ▸ hsS) hvS

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
