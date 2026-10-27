module

import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S12.PushingUp

public section

namespace CFSG.CGT.PushingUp

open CFSG CFSG.Quasithin CFSG.QuasithinUnique.Setup.Campbell CFSG.RankThree.PartOne
open scoped commutatorElement

section Characteristic

variable {G : Type} [Group G]

private theorem exists_mulAut_restrict {P S : Subgroup G} (hSP : S ≤ P)
    (hS : (S.subgroupOf P).Characteristic) (φ : MulAut P) :
    ∃ ψ : MulAut S, ∀ s : S, ((ψ s : S) : G) = ((φ ⟨s, hSP s.2⟩ : P) : G) := by
  have hmem : ∀ (χ : MulAut P) (s : S), ((χ ⟨s, hSP s.2⟩ : P) : G) ∈ S := fun χ s =>
    (Subgroup.characteristic_iff_le_comap.mp hS) χ s.2
  exact ⟨{ toFun := fun s => ⟨(φ ⟨s, hSP s.2⟩ : P), hmem φ s⟩
           invFun := fun s => ⟨(φ.symm ⟨s, hSP s.2⟩ : P), hmem φ.symm s⟩
           left_inv := fun s => Subtype.ext (by simp)
           right_inv := fun s => Subtype.ext (by simp)
           map_mul' := fun a b => Subtype.ext (by
             have h := congrArg (fun y : P => (y : G)) (map_mul φ ⟨a, hSP a.2⟩ ⟨b, hSP b.2⟩)
             exact h) }, fun s => rfl⟩

theorem characteristic_trans {T₁ S P : Subgroup G} (h₁ : T₁ ≤ S) (h₂ : S ≤ P)
    (hT : (T₁.subgroupOf S).Characteristic) (hS : (S.subgroupOf P).Characteristic) :
    (T₁.subgroupOf P).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  obtain ⟨ψ, hψ⟩ := exists_mulAut_restrict h₂ hS φ
  have hxS : (x : G) ∈ S := h₁ hx
  have h := (Subgroup.characteristic_iff_le_comap.mp hT) ψ (show (⟨x, hxS⟩ : S) ∈ _ from hx)
  change ((ψ ⟨x, hxS⟩ : S) : G) ∈ T₁ at h
  rw [hψ] at h
  exact h

theorem normalizer_le_normalizer_of_characteristic' {C P : Subgroup G} (hCP : C ≤ P)
    (hC : (C.subgroupOf P).Characteristic) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (P : Set G) → ∀ {w : G}, w ∈ C →
      g * w * g⁻¹ ∈ C := by
    intro g hg w hw
    let φ : MulAut P := Subgroup.normalizerMonoidHom P ⟨g, hg⟩
    exact (Subgroup.characteristic_iff_le_comap.mp hC) φ (show (⟨w, hCP hw⟩ : P) ∈ _ from hw)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key hg hh, fun hh => ?_⟩
  have := key (inv_mem hg) hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

private theorem comm_map_of_forall_comm {P : Subgroup G} (φ : MulAut P) {x : P}
    (hx : ∀ k ∈ P, k * (x : G) = x * k) : ∀ k ∈ P, k * ((φ x : P) : G) = (φ x) * k := by
  intro k hk
  have h1 : φ.symm ⟨k, hk⟩ * x = x * φ.symm ⟨k, hk⟩ := Subtype.ext (hx _ (φ.symm ⟨k, hk⟩).2)
  have h2 := congrArg φ h1
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  exact congrArg Subtype.val h2

private theorem characteristic_centralizer_subgroupOf (P : Subgroup G) :
    ((Subgroup.centralizer (P : Set G)).subgroupOf P).Characteristic := by
  have h : (Subgroup.centralizer (P : Set G)).subgroupOf P = Subgroup.center P := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
    exact ⟨fun hx y => Subtype.ext (hx y y.2), fun hx k hk => congrArg Subtype.val (hx ⟨k, hk⟩)⟩
  rw [h]
  infer_instance

private theorem characteristic_map_subtype_of_characteristic {P S : Subgroup G} (hSP : S ≤ P)
    (hS : (S.subgroupOf P).Characteristic) {K : Subgroup S} (hK : K.Characteristic) :
    ((K.map S.subtype).subgroupOf P).Characteristic :=
  characteristic_trans (Subgroup.map_subtype_le K) hSP
    (by rwa [show (K.map S.subtype).subgroupOf S = K from
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective K]) hS

private theorem characteristic_map_inf_centralizer {P S : Subgroup G} (hSP : S ≤ P)
    (hS : (S.subgroupOf P).Characteristic) {K : Subgroup S} (hK : K.Characteristic) :
    ((K.map S.subtype ⊓ Subgroup.centralizer (P : Set G)).subgroupOf P).Characteristic := by
  have := characteristic_map_subtype_of_characteristic hSP hS hK
  have := characteristic_centralizer_subgroupOf P
  have h : (K.map S.subtype ⊓ Subgroup.centralizer (P : Set G)).subgroupOf P =
      (K.map S.subtype).subgroupOf P ⊓ (Subgroup.centralizer (P : Set G)).subgroupOf P := rfl
  rw [h]
  infer_instance

end Characteristic

section PushingUpS

variable {G : Type} [Group G]

theorem pushingUpS_le (P : Subgroup G) : pushingUpS P ≤ P :=
  inf_le_left

private theorem mem_pushingUpS_iff {P : Subgroup G} {x : G} :
    x ∈ pushingUpS P ↔ x ∈ P ∧
      ∀ z ∈ inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) P, z * x = x * z := by
  simp [pushingUpS, Subgroup.mem_centralizer_iff]

theorem characteristic_pushingUpS [Finite G] (P : Subgroup G) :
    ((pushingUpS P).subgroupOf P).Characteristic := by
  have h : (pushingUpS P).subgroupOf P =
      Subgroup.centralizer (elemThompsonCenterTorsion ↥P 2 : Set ↥P) := by
    ext x
    rw [Subgroup.mem_subgroupOf, mem_pushingUpS_iff, Subgroup.mem_centralizer_iff]
    refine ⟨fun h e he => ?_, fun hx => ⟨x.2, ?_⟩⟩
    · exact Subtype.ext (h.2 _ ⟨e, he, rfl⟩)
    · rintro _ ⟨e, he, rfl⟩
      exact congrArg Subtype.val (hx e he)
  rw [h]
  have := BlueprintB2.elemThompsonCenterTorsion_characteristic P 2
  infer_instance

private theorem elemThompson_le_pushingUpS [Finite G] (P : Subgroup G) :
    elemThompson P 2 ≤ (pushingUpS P).subgroupOf P := by
  intro x hx
  rw [Subgroup.mem_subgroupOf, mem_pushingUpS_iff]
  refine ⟨x.2, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have hc := (BlueprintB2.mem_elemThompsonCenterTorsion_iff_centralizer.mp he).1
  exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc x hx)).symm

private theorem elemCenterIn_pushingUpS [Finite G] (P : Subgroup G) :
    elemCenterIn 2 (pushingUpS P) = elemCenterIn 2 P := by
  have hle : pushingUpS P ≤ P := pushingUpS_le P
  have h1 := BlueprintB2.elemThompsonCenterTorsion_map_subtype (p := 2) (R := ↥P)
    (Y := (pushingUpS P).subgroupOf P) (elemThompson_le_pushingUpS P)
  have h2 := elemCenterIn_map_subtype (S := G) 2 (A := P) ((pushingUpS P).subgroupOf P)
  rw [Subgroup.map_subgroupOf_eq_of_le hle] at h2
  rw [← h2]
  exact congrArg (Subgroup.map P.subtype) h1

private theorem centralizer_elemThompsonCenterTorsion_pushingUpS [Finite G] (P : Subgroup G) :
    Subgroup.centralizer
      (elemThompsonCenterTorsion ↥(pushingUpS P) 2 : Set ↥(pushingUpS P)) = ⊤ := by
  refine eq_top_iff.mpr fun s _ => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzG : (z : G) ∈ inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) P := by
    have : (z : G) ∈ elemCenterIn 2 (pushingUpS P) := ⟨z, hz, rfl⟩
    rwa [elemCenterIn_pushingUpS] at this
  exact Subtype.ext ((mem_pushingUpS_iff.mp s.2).2 _ hzG)

theorem mem_omegaOneCenterIn_iff {P : Subgroup G} {z : G} :
    z ∈ omegaOneCenterIn P ↔ z ∈ P ∧ (∀ k ∈ P, k * z = z * k) ∧ z ^ 2 = 1 := by
  have h : omegaOneCenterIn P = BlueprintB2.centerTorsion 2 P :=
    (BlueprintB2.centerTorsion_eq_closure 2 P).symm
  rw [h]
  exact BlueprintB2.mem_centerTorsion_iff

theorem omegaOneCenterIn_le (P : Subgroup G) : omegaOneCenterIn P ≤ P :=
  fun _ h => (mem_omegaOneCenterIn_iff.mp h).1

theorem characteristic_omegaOneCenterIn (P : Subgroup G) :
    ((omegaOneCenterIn P).subgroupOf P).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  obtain ⟨-, hc, hsq⟩ := mem_omegaOneCenterIn_iff.mp (Subgroup.mem_subgroupOf.mp hx)
  refine Subgroup.mem_subgroupOf.mpr (mem_omegaOneCenterIn_iff.mpr
    ⟨(φ x).2, comm_map_of_forall_comm φ hc, ?_⟩)
  have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hsq)
  have h2 : (φ x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
  simpa using congrArg Subtype.val h2

theorem omegaOneCenterIn_le_pushingUpS (P : Subgroup G) : omegaOneCenterIn P ≤ pushingUpS P := by
  intro z hz
  obtain ⟨hzP, hzc, -⟩ := mem_omegaOneCenterIn_iff.mp hz
  refine mem_pushingUpS_iff.mpr ⟨hzP, fun w hw => ?_⟩
  have hwP : w ∈ P := by
    obtain ⟨e, -, rfl⟩ := hw
    exact e.2
  exact hzc w hwP

private theorem exists_mem_center_orderOf_two {K : Type*} [Group K] [Finite K] [Nontrivial K]
    (hK : IsPGroup 2 K) : ∃ z ∈ Subgroup.center K, orderOf z = 2 := by
  have hc : Nontrivial (Subgroup.center K) := hK.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center K) := hK.to_subgroup _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcp
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
    exact not_subsingleton (Subgroup.center K) hn.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  exact ⟨(x : K), x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem omegaOneCenterIn_ne_bot [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    omegaOneCenterIn P ≠ ⊥ := by
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  obtain ⟨x, hxc, hx2⟩ := exists_mem_center_orderOf_two hP
  have hxsq : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hgmem : (x : G) ∈ omegaOneCenterIn P :=
    mem_omegaOneCenterIn_iff.mpr ⟨x.2, fun k hk =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨k, hk⟩), by
        simpa using congrArg Subtype.val hxsq⟩
  intro h
  rw [h, Subgroup.mem_bot] at hgmem
  have hx1 : x = 1 := Subtype.ext hgmem
  rw [hx1, orderOf_one] at hx2
  omega

theorem pushingUpS_ne_bot [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    pushingUpS P ≠ ⊥ := fun h =>
  omegaOneCenterIn_ne_bot hP hP1
    (le_bot_iff.mp ((omegaOneCenterIn_le_pushingUpS P).trans h.le))

private theorem subgroupOf_omegaOneCenterIn_le (P : Subgroup G) :
    (omegaOneCenterIn P).subgroupOf (pushingUpS P) ≤
      omegaOne 2 (Subgroup.center ↥(pushingUpS P)) := by
  intro s hs
  obtain ⟨-, hc, hsq⟩ := mem_omegaOneCenterIn_iff.mp (Subgroup.mem_subgroupOf.mp hs)
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hc k (pushingUpS_le P k.2))
  · exact Subtype.ext hsq

end PushingUpS

section General

variable {G : Type} [Group G]

private theorem inf_centralizer_ne_bot_of_normalized [Finite G] {P W : Subgroup G}
    (hP : IsPGroup 2 P) (hWP : W ≤ P) (hnorm : P ≤ Subgroup.normalizer (W : Set G))
    (hW : W ≠ ⊥) : W ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ W ⊓ Subgroup.centralizer (P : Set G) := ⟨hy.1, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

end General

section Automorphisms

private theorem characteristic_iSup_map_mulAut {M : Type*} [Group M] (X : Subgroup M) :
    (⨆ α : MulAut M, X.map α.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_iSup]
  refine iSup_le fun α => ?_
  rw [Subgroup.map_map]
  exact le_iSup (fun β : MulAut M => X.map β.toMonoidHom) (φ * α)

private theorem map_mulAut_centerTorsion_le {M : Type*} [Group M] (φ : MulAut M) :
    (BlueprintB2.centerTorsion 2 (⊤ : Subgroup M)).map φ.toMonoidHom ≤
      BlueprintB2.centerTorsion 2 (⊤ : Subgroup M) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨-, hc, hp⟩ := BlueprintB2.mem_centerTorsion_iff.mp hx
  rw [BlueprintB2.mem_centerTorsion_iff]
  refine ⟨trivial, fun k _ => ?_, ?_⟩
  · have h2 := congrArg φ (hc (φ.symm k) trivial)
    simpa using h2
  · show φ x ^ 2 = 1
    rw [← map_pow, hp, map_one]

private theorem iSup_map_mulAut_le_centerTorsion {M : Type*} [Group M] {X : Subgroup M}
    (hX : X ≤ BlueprintB2.centerTorsion 2 (⊤ : Subgroup M)) :
    (⨆ α : MulAut M, X.map α.toMonoidHom) ≤ BlueprintB2.centerTorsion 2 (⊤ : Subgroup M) :=
  iSup_le fun α => (Subgroup.map_mono hX).trans (map_mulAut_centerTorsion_le α)

end Automorphisms

section Triples

private theorem tripleE_normal (H : Type) [Group H] [Finite H] : (tripleE H).Normal :=
  elemCenterIn_normal 2 (pCore 2 H)

private theorem tripleE_le_pCore (H : Type) [Group H] : tripleE H ≤ pCore 2 H :=
  Subgroup.map_subtype_le _

private theorem sq_eq_one_of_mem_tripleE (H : Type) [Group H] [Finite H] {x : H}
    (hx : x ∈ tripleE H) : x ^ 2 = 1 :=
  (BlueprintB2.isElementaryAbelian_iff.mp (elemCenterIn_isElementaryAbelian 2 (pCore 2 H))).2 x hx

private theorem tripleV_le_tripleE (H : Type) [Group H] [Finite H] : tripleV H ≤ tripleE H := by
  have := tripleE_normal H
  exact Subgroup.commutator_le_right _ _

private theorem tripleV_normal (H : Type) [Group H] [Finite H] : (tripleV H).Normal := by
  have := tripleE_normal H
  exact Subgroup.commutator_normal _ _

end Triples

section InClassGFacts

private theorem elemThompson_ne_bot_two {R : Type*} [Group R] [Finite R] [Nontrivial R]
    (hR : IsPGroup 2 R) : elemThompson R 2 ≠ ⊥ := by
  intro hJ
  obtain ⟨A, hA, hAc⟩ := BlueprintB2.exists_card_eq_pow_pRank R 2
  have hAJ : A ≤ elemThompson R 2 := le_sSup ⟨hA, hAc⟩
  rw [hJ, le_bot_iff] at hAJ
  rw [hAJ, Subgroup.card_bot] at hAc
  have hdvd : 2 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
    have h1 : 1 < Nat.card R := Finite.one_lt_card
    rw [hn] at h1 ⊢
    exact dvd_pow_self 2 (by rintro rfl; simp at h1)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hE : IsElementaryAbelian 2 (Subgroup.zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← hx]; exact pow_orderOf_eq_one x)
  have hle := BlueprintB2.card_le_pow_pRank (R := R) hE
  rw [Nat.card_zpowers, hx, ← hAc] at hle
  exact absurd hle (by norm_num)

private theorem elemThompsonCenterTorsion_ne_bot_two {R : Type*} [Group R] [Finite R]
    [Nontrivial R] (hR : IsPGroup 2 R) : elemThompsonCenterTorsion R 2 ≠ ⊥ := by
  have : Nontrivial (elemThompson R 2) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (elemThompson_ne_bot_two hR)
  obtain ⟨z, hzc, hz2⟩ := exists_mem_center_orderOf_two (hR.to_subgroup (elemThompson R 2))
  have hzsq : ((z : elemThompson R 2) : R) ^ 2 = 1 := by
    have := congrArg (fun y : elemThompson R 2 => (y : R)) (hz2 ▸ pow_orderOf_eq_one z)
    simpa using this
  have hmem : ((z : elemThompson R 2) : R) ∈ elemThompsonCenterTorsion R 2 :=
    BlueprintB2.mem_centerTorsion_iff.mpr ⟨z.2, fun k hk =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨k, hk⟩), hzsq⟩
  intro h
  rw [h, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext hmem
  rw [hz1, orderOf_one] at hz2
  omega

variable {S H : Type} [Group S] [Group H] [Finite H] {ι : S →* H}

private theorem pCore_le_range (hG : InClassG S H ι) : pCore 2 H ≤ ι.range := by
  have hp : IsPGroup 2 ι.range := hG.sylow.2.1
  have hidx : ¬ 2 ∣ ι.range.index := by
    have := hG.sylow.2.2
    rwa [Subgroup.relIndex_top_right] at this
  exact (pCore_isPGroup (p := 2) (G := H)).le_sylow_of_normal (hp.toSylow hidx)

private theorem tripleE_le_range (hG : InClassG S H ι) : tripleE H ≤ ι.range :=
  (tripleE_le_pCore H).trans (pCore_le_range hG)

private theorem pCore_ne_bot_of_inClassG [Nontrivial S] (hG : InClassG S H ι) :
    pCore 2 H ≠ ⊥ := by
  intro hbot
  have hF : generalizedFitting H = ⊥ := hG.fitting_eq.trans hbot
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  have hι : ι s ≠ 1 := fun h => hs (hG.injective (by rw [h, map_one]))
  have hmem : ι s ∈ Subgroup.centralizer (generalizedFitting H : Set H) := by
    rw [hF, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
    rw [hh, one_mul, mul_one]
  have := centralizer_generalizedFitting_le H hmem
  rw [hF, Subgroup.mem_bot] at this
  exact hι this

private theorem tripleE_ne_bot [Nontrivial S] (hG : InClassG S H ι) : tripleE H ≠ ⊥ := by
  have : Nontrivial (pCore 2 H) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (pCore_ne_bot_of_inClassG hG)
  intro h
  exact elemThompsonCenterTorsion_ne_bot_two (pCore_isPGroup (p := 2) (G := H))
    ((Subgroup.map_eq_bot_iff_of_injective _ (pCore 2 H).subtype_injective).mp h)

private theorem commute_of_mem_pCore (hG : InClassG S H ι) {x : S}
    (hxc : x ∈ Subgroup.center S) {q : H} (hq : q ∈ pCore 2 H) : q * ι x = ι x * q := by
  obtain ⟨s', rfl⟩ := pCore_le_range hG hq
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hxc s']

private theorem map_center_mem_pCore (hG : InClassG S H ι) {x : S}
    (hxc : x ∈ Subgroup.center S) : ι x ∈ pCore 2 H := by
  have hmem : ι x ∈ Subgroup.centralizer (generalizedFitting H : Set H) := by
    rw [hG.fitting_eq, Subgroup.mem_centralizer_iff]
    intro q hq
    exact commute_of_mem_pCore hG hxc hq
  have h := centralizer_generalizedFitting_le H hmem
  rwa [hG.fitting_eq] at h

private theorem map_center_sq_mem_tripleE (hG : InClassG S H ι) {x : S}
    (hxc : x ∈ Subgroup.center S) (hx2 : x ^ 2 = 1) : ι x ∈ tripleE H := by
  have hQ := map_center_mem_pCore hG hxc
  refine ⟨⟨ι x, hQ⟩, ?_, rfl⟩
  refine BlueprintB2.mem_elemThompsonCenterTorsion_iff_centralizer.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro j _
    exact Subtype.ext (commute_of_mem_pCore hG hxc j.2)
  · refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hx2, map_one]

private theorem map_omegaOne_center_le_tripleE (hG : InClassG S H ι) :
    (omegaOne 2 (Subgroup.center S)).map ι ≤ tripleE H := by
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxc, hx2⟩
  exact map_center_sq_mem_tripleE hG hxc hx2

private theorem tripleV_ne_bot_of_commutator_ne_bot (hG : InClassG S H ι)
    (hne : ⁅(⊤ : Subgroup H), (omegaOne 2 (Subgroup.center S)).map ι⁆ ≠ ⊥) :
    tripleV H ≠ ⊥ := by
  intro h
  apply hne
  have hle : ⁅(⊤ : Subgroup H), (omegaOne 2 (Subgroup.center S)).map ι⁆ ≤ tripleV H :=
    Subgroup.commutator_mono le_rfl (map_omegaOne_center_le_tripleE hG)
  rw [h] at hle
  exact le_bot_iff.mp hle

end InClassGFacts

section Pair

private theorem comap_centralizer_tripleV_ne_bot {S H : Type} [Group S] [Finite S] [Group H]
    [Finite H] {ι : S →* H} (hS : IsPGroup 2 S) (hG : InClassG S H ι)
    (hne : ⁅(⊤ : Subgroup H), (omegaOne 2 (Subgroup.center S)).map ι⁆ ≠ ⊥) :
    (tripleV H ⊓ Subgroup.centralizer (ι.range : Set H)).comap ι ≠ ⊥ := by
  have hV := tripleV_ne_bot_of_commutator_ne_bot hG hne
  have hVr : tripleV H ≤ ι.range := (tripleV_le_tripleE H).trans (tripleE_le_range hG)
  have hnormal : ((tripleV H).comap ι).Normal := (tripleV_normal H).comap ι
  have hVS : (tripleV H).comap ι ≠ ⊥ := by
    intro h
    apply hV
    rw [← Subgroup.map_comap_eq_self hVr, h, Subgroup.map_bot]
  have : Group.IsNilpotent S := hS.isNilpotent
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hVS)
  intro h
  have hxC : ι (x : S) ∈ Subgroup.centralizer (ι.range : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp x.2.2 k]
  have hxmem : (x : S) ∈ (tripleV H ⊓ Subgroup.centralizer (ι.range : Set H)).comap ι :=
    Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨x.2.1, hxC⟩)
  rw [h, Subgroup.mem_bot] at hxmem
  exact hx1 (Subtype.ext hxmem)

private theorem comap_centralizer_tripleV_le_centerTorsion {S H : Type} [Group S] [Group H]
    [Finite H] {ι : S →* H} (hG : InClassG S H ι) :
    (tripleV H ⊓ Subgroup.centralizer (ι.range : Set H)).comap ι ≤
      BlueprintB2.centerTorsion 2 (⊤ : Subgroup S) := by
  intro x hx
  obtain ⟨hxV, hxC⟩ := hx
  rw [BlueprintB2.mem_centerTorsion_iff]
  refine ⟨trivial, fun k _ => ?_, ?_⟩
  · apply hG.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hxC (ι k) ⟨k, rfl⟩
  · apply hG.injective
    rw [map_pow, map_one]
    exact sq_eq_one_of_mem_tripleE H ((tripleV_le_tripleE H) hxV)

variable {G : Type} [Group G]

private theorem centralizer_part [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    {K : Subgroup ↥(pushingUpS P)} (hKchar : K.Characteristic)
    (hKW : K ≤ BlueprintB2.centerTorsion 2 (⊤ : Subgroup ↥(pushingUpS P))) (hK1 : K ≠ ⊥) :
    K.map (pushingUpS P).subtype ⊓ Subgroup.centralizer (P : Set G) ≤ omegaOneCenterIn P ∧
    K.map (pushingUpS P).subtype ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ ∧
    (K.map (pushingUpS P).subtype ⊓ Subgroup.centralizer (P : Set G)).subgroupOf
      (pushingUpS P) ≤ K := by
  have hKP : K.map (pushingUpS P).subtype ≤ P := (Subgroup.map_subtype_le K).trans (pushingUpS_le P)
  refine ⟨?_, ?_, ?_⟩
  · rintro t ⟨⟨s, hs, rfl⟩, htC⟩
    obtain ⟨-, -, hs2⟩ := BlueprintB2.mem_centerTorsion_iff.mp (hKW hs)
    exact mem_omegaOneCenterIn_iff.mpr ⟨pushingUpS_le P s.2,
      fun k hk => Subgroup.mem_centralizer_iff.mp htC k hk, by simpa using congrArg Subtype.val hs2⟩
  · refine inf_centralizer_ne_bot_of_normalized hP hKP ?_ ?_
    · exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_of_characteristic' hKP
        (characteristic_map_subtype_of_characteristic (pushingUpS_le P)
          (characteristic_pushingUpS P) hKchar))
    · exact fun h => hK1 ((Subgroup.map_eq_bot_iff_of_injective K
        (pushingUpS P).subtype_injective).mp h)
  · intro s hs
    obtain ⟨k, hk, hks⟩ := (Subgroup.mem_subgroupOf.mp hs).1
    have : k = s := Subtype.ext hks
    exact this ▸ hk

private theorem exists_pair_of_dichotomy [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    {K₁ K₂ : Subgroup ↥(pushingUpS P)} (hK₁ : K₁.Characteristic) (hK₁1 : K₁ ≠ ⊥)
    (hK₂ : K₂.Characteristic)
    (hK₂W : K₂ ≤ BlueprintB2.centerTorsion 2 (⊤ : Subgroup ↥(pushingUpS P))) (hK₂1 : K₂ ≠ ⊥)
    (hdich : ∀ (H : Type) [Group H] [Finite H] (ι : ↥(pushingUpS P) →* H),
      InClassG ↥(pushingUpS P) H ι → ¬ InClassX ↥(oResidualTwo H) →
        (K₁.map ι).Normal ∨ K₂.map ι ≤ Subgroup.center H) :
    ∃ T₁ T₂ : Subgroup G, T₁ ≤ pushingUpS P ∧ (T₁.subgroupOf (pushingUpS P)).Characteristic ∧
      (T₁.subgroupOf P).Characteristic ∧ T₁ ≠ ⊥ ∧
      T₂ ≤ omegaOneCenterIn P ∧ (T₂.subgroupOf P).Characteristic ∧ T₂ ≠ ⊥ ∧
      PushingUpWhenever (pushingUpS P) T₁ T₂ := by
  obtain ⟨hT₂le, hT₂ne, hT₂S⟩ := centralizer_part hP hK₂ hK₂W hK₂1
  have hsub : (K₁.map (pushingUpS P).subtype).subgroupOf (pushingUpS P) = K₁ :=
    Subgroup.comap_map_eq_self_of_injective (pushingUpS P).subtype_injective _
  refine ⟨K₁.map (pushingUpS P).subtype,
    K₂.map (pushingUpS P).subtype ⊓ Subgroup.centralizer (P : Set G),
    Subgroup.map_subtype_le _, by rwa [hsub],
    characteristic_map_subtype_of_characteristic (pushingUpS_le P) (characteristic_pushingUpS P)
      hK₁, fun h => hK₁1 ((Subgroup.map_eq_bot_iff_of_injective _
        (pushingUpS P).subtype_injective).mp h), hT₂le,
    characteristic_map_inf_centralizer (pushingUpS_le P) (characteristic_pushingUpS P) hK₂, hT₂ne,
    ?_⟩
  intro H _ _ ι hG hnX
  rw [hsub]
  rcases hdich H ι hG hnX with h1 | h2
  · exact Or.inl h1
  · exact Or.inr ((Subgroup.map_mono hT₂S).trans h2)

private theorem exists_pair_of_good [Finite G] (hCamp : CampbellTheoremAsPrinted)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) {H₀ : Type} [Group H₀] [Finite H₀]
    {ι₀ : ↥(pushingUpS P) →* H₀} (hG₀ : InClassG ↥(pushingUpS P) H₀ ι₀)
    (hne : ⁅(⊤ : Subgroup H₀), (omegaOne 2 (Subgroup.center ↥(pushingUpS P))).map ι₀⁆ ≠ ⊥) :
    ∃ T₁ T₂ : Subgroup G, T₁ ≤ pushingUpS P ∧ (T₁.subgroupOf (pushingUpS P)).Characteristic ∧
      (T₁.subgroupOf P).Characteristic ∧ T₁ ≠ ⊥ ∧
      T₂ ≤ omegaOneCenterIn P ∧ (T₂.subgroupOf P).Characteristic ∧ T₂ ≠ ⊥ ∧
      PushingUpWhenever (pushingUpS P) T₁ T₂ := by
  have hS2 : IsPGroup 2 (pushingUpS P) := hP.to_le (pushingUpS_le P)
  have hS1 : pushingUpS P ≠ ⊥ := pushingUpS_ne_bot hP hP1
  have : Nontrivial (pushingUpS P) := (Subgroup.nontrivial_iff_ne_bot _).mpr hS1
  have hK₁ne : (⨆ α : MulAut ↥(pushingUpS P), ((tripleE H₀).comap ι₀).map α.toMonoidHom) ≠ ⊥ := by
    intro h
    have hle : (tripleE H₀).comap ι₀ ≤
        ⨆ α : MulAut ↥(pushingUpS P), ((tripleE H₀).comap ι₀).map α.toMonoidHom :=
      fun x hx => le_iSup (fun α : MulAut ↥(pushingUpS P) =>
        ((tripleE H₀).comap ι₀).map α.toMonoidHom) 1 ⟨x, hx, rfl⟩
    rw [h, le_bot_iff] at hle
    apply tripleE_ne_bot hG₀
    rw [← Subgroup.map_comap_eq_self (tripleE_le_range hG₀), hle, Subgroup.map_bot]
  have hK₂ne : (⨆ α : MulAut ↥(pushingUpS P),
      ((tripleV H₀ ⊓ Subgroup.centralizer (ι₀.range : Set H₀)).comap ι₀).map
        α.toMonoidHom) ≠ ⊥ := by
    intro h
    have hle : (tripleV H₀ ⊓ Subgroup.centralizer (ι₀.range : Set H₀)).comap ι₀ ≤
        ⨆ α : MulAut ↥(pushingUpS P), ((tripleV H₀ ⊓ Subgroup.centralizer
          (ι₀.range : Set H₀)).comap ι₀).map α.toMonoidHom :=
      fun x hx => le_iSup (fun α : MulAut ↥(pushingUpS P) =>
        ((tripleV H₀ ⊓ Subgroup.centralizer (ι₀.range : Set H₀)).comap ι₀).map
          α.toMonoidHom) 1 ⟨x, hx, rfl⟩
    rw [h, le_bot_iff] at hle
    exact comap_centralizer_tripleV_ne_bot hS2 hG₀ hne hle
  refine exists_pair_of_dichotomy hP (characteristic_iSup_map_mulAut _) hK₁ne
    (characteristic_iSup_map_mulAut _)
    (iSup_map_mulAut_le_centerTorsion (comap_centralizer_tripleV_le_centerTorsion hG₀)) hK₂ne ?_
  intro H _ _ ι hG hnX
  rcases hCamp ↥(pushingUpS P) hS2 (centralizer_elemThompsonCenterTorsion_pushingUpS P) H ι hG
    H₀ ι₀ hG₀ hne with h1 | h2 | ⟨-, hX, -⟩
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd hX hnX

private theorem exists_pair_of_no_good [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    (hP1 : P ≠ ⊥)
    (hbad : ∀ (H : Type) [Group H] [Finite H] (ι : ↥(pushingUpS P) →* H),
      InClassG ↥(pushingUpS P) H ι →
        ⁅(⊤ : Subgroup H), (omegaOne 2 (Subgroup.center ↥(pushingUpS P))).map ι⁆ = ⊥) :
    ∃ T₁ T₂ : Subgroup G, T₁ ≤ pushingUpS P ∧ (T₁.subgroupOf (pushingUpS P)).Characteristic ∧
      (T₁.subgroupOf P).Characteristic ∧ T₁ ≠ ⊥ ∧
      T₂ ≤ omegaOneCenterIn P ∧ (T₂.subgroupOf P).Characteristic ∧ T₂ ≠ ⊥ ∧
      PushingUpWhenever (pushingUpS P) T₁ T₂ := by
  refine ⟨pushingUpS P, omegaOneCenterIn P, le_rfl, ?_, characteristic_pushingUpS P,
    pushingUpS_ne_bot hP hP1, le_rfl, characteristic_omegaOneCenterIn P,
    omegaOneCenterIn_ne_bot hP hP1, ?_⟩
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · intro H _ _ ι hG _
    right
    have h0 := hbad H ι hG
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ] at h0
    exact (Subgroup.map_mono (subgroupOf_omegaOneCenterIn_le P)).trans h0

theorem exists_campbell_pair [Finite G] (hCamp : CampbellTheoremAsPrinted) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    ∃ T₁ T₂ : Subgroup G, T₁ ≤ pushingUpS P ∧ (T₁.subgroupOf (pushingUpS P)).Characteristic ∧
      (T₁.subgroupOf P).Characteristic ∧ T₁ ≠ ⊥ ∧
      T₂ ≤ omegaOneCenterIn P ∧ (T₂.subgroupOf P).Characteristic ∧ T₂ ≠ ⊥ ∧
      PushingUpWhenever (pushingUpS P) T₁ T₂ := by
  by_cases hex : ∃ (H : Type) (_ : Group H) (_ : Finite H) (ι : ↥(pushingUpS P) →* H),
      InClassG ↥(pushingUpS P) H ι ∧
        ⁅(⊤ : Subgroup H), (omegaOne 2 (Subgroup.center ↥(pushingUpS P))).map ι⁆ ≠ ⊥
  · obtain ⟨H₀, _, _, ι₀, hG₀, hne⟩ := hex
    exact exists_pair_of_good hCamp hP hP1 hG₀ hne
  · refine exists_pair_of_no_good hP hP1 fun H _ _ ι hG => ?_
    by_contra hne
    exact hex ⟨H, inferInstance, inferInstance, ι, hG, hne⟩

end Pair

end CFSG.CGT.PushingUp
