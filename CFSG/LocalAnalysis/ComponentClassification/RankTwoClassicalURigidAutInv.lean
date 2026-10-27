module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidCen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinBarW

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

theorem isPGroup_ker_zBlockHom : IsPGroup 2 (zBlockHom (ε := ε) h).ker := by
  intro x
  obtain ⟨n, hn⟩ := isPGroup_eichSub h (⟨((x : stabE (ε := ε) h) : hypSU h 1 ε),
    (mem_ker_zBlockHom h _).mp x.2⟩ : eichSub (ε := ε) h)
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := congrArg Subtype.val hn
  simpa using h1

theorem map_ker_zBlockHom [Finite K] (hf : 2 ≤ f) (hε : 2 ≤ ε) (β : MulAut (stabE (ε := ε) h)) :
    (zBlockHom h).ker.map β.toMonoidHom = (zBlockHom h).ker := by
  have hle : (zBlockHom h).ker.map β.toMonoidHom ≤ (zBlockHom h).ker := by
    have hQn : ((zBlockHom h).ker.map β.toMonoidHom).Normal :=
      (zBlockHom h).normal_ker.map β.toMonoidHom β.surjective
    have hρ : (((zBlockHom h).ker.map β.toMonoidHom).map (zBlockHom h)).Normal :=
      hQn.map _ (zBlockHom_surjective h)
    have hbot := eq_bot_of_normal_statedSU h hf hε
      (((isPGroup_ker_zBlockHom h).map β.toMonoidHom).map (zBlockHom h))
    intro x hx
    rw [MonoidHom.mem_ker]
    have h1 : zBlockHom h x ∈ ((zBlockHom h).ker.map β.toMonoidHom).map (zBlockHom h) :=
      ⟨x, hx, rfl⟩
    rwa [hbot, mem_bot] at h1
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective β.injective).ge

theorem map_tvSub [Finite K] (hf : 2 ≤ f) (hε : 2 ≤ ε) (β : MulAut (stabE (ε := ε) h)) :
    (tvSub h).map β.toMonoidHom = tvSub h := by
  rw [← centralizer_inf_ker_eq_tvSub, Subgroup.map_inf _ _ _ β.injective, centralizer_map_mulAut,
    map_ker_zBlockHom h hf hε]

theorem avecPre_top : avecPre h (⊤ : AddSubgroup (Fin ε → K)) = (zBlockHom h).ker := by
  ext x
  simp [mem_avecPre]

theorem card_eq_of_card_avecPre {S S' : AddSubgroup (Fin ε → K)}
    (hc : Nat.card (avecPre (ε := ε) h S) = Nat.card (avecPre h S')) :
    Nat.card S = Nat.card S' := by
  rw [card_avecPre, card_avecPre] at hc
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hc

section Map

variable {h} {β : MulAut (stabE (ε := ε) h)}
  (hE : (zBlockHom h).ker.map β.toMonoidHom = (zBlockHom h).ker)
  (hT : (tvSub h).map β.toMonoidHom = tvSub h)
include hE hT

theorem map_commutator_sup_tvSub (H : Subgroup (stabE (ε := ε) h)) :
    (⁅(zBlockHom (ε := ε) h).ker, H⁆ ⊔ tvSub h).map β.toMonoidHom =
      ⁅(zBlockHom (ε := ε) h).ker, H.map β.toMonoidHom⁆ ⊔ tvSub h := by
  rw [Subgroup.map_sup, Subgroup.map_commutator, hE, hT]

theorem card_commSpace_map (H : Subgroup (stabE (ε := ε) h)) :
    Nat.card (commSpace h (H.map β.toMonoidHom)) = Nat.card (commSpace h H) := by
  apply card_eq_of_card_avecPre h
  rw [← commutator_sup_tvSub_eq, ← commutator_sup_tvSub_eq, ← map_commutator_sup_tvSub hE hT,
    Subgroup.card_map_of_injective β.injective]

omit hT in
theorem card_fixSpace_map {H : Subgroup (stabE (ε := ε) h)} (hH : ⁅H, H⁆ = H) :
    Nat.card (fixSpace h (H.map β.toMonoidHom)) = Nat.card (fixSpace h H) := by
  have hH' : ⁅H.map β.toMonoidHom, H.map β.toMonoidHom⁆ = H.map β.toMonoidHom := by
    rw [← Subgroup.map_commutator, hH]
  have h1 := centralizer_inf_avecPre_eq h hH ⊤
  have h2 := centralizer_inf_avecPre_eq h hH' ⊤
  rw [avecPre_top] at h1 h2
  have h3 : (centralizer (H : Set (stabE (ε := ε) h)) ⊓ (zBlockHom h).ker).map β.toMonoidHom =
      centralizer ((H.map β.toMonoidHom : Subgroup (stabE (ε := ε) h)) :
        Set (stabE (ε := ε) h)) ⊓ (zBlockHom h).ker := by
    rw [Subgroup.map_inf _ _ _ β.injective, centralizer_map_mulAut, hE]
  have h4 := card_eq_of_card_avecPre h (S := ⊤ ⊓ fixSpace h (H.map β.toMonoidHom))
    (S' := ⊤ ⊓ fixSpace h H) (by rw [← h1, ← h2, ← h3, Subgroup.card_map_of_injective β.injective])
  simpa only [top_inf_eq] using h4

theorem card_commSpace_inf_fixSpace_map {H : Subgroup (stabE (ε := ε) h)} (hH : ⁅H, H⁆ = H) :
    Nat.card ↥(commSpace h (H.map β.toMonoidHom) ⊓ fixSpace h (H.map β.toMonoidHom)) =
      Nat.card ↥(commSpace h H ⊓ fixSpace h H) := by
  have hH' : ⁅H.map β.toMonoidHom, H.map β.toMonoidHom⁆ = H.map β.toMonoidHom := by
    rw [← Subgroup.map_commutator, hH]
  have h1 := centralizer_inf_avecPre_eq h hH (commSpace h H)
  have h2 := centralizer_inf_avecPre_eq h hH' (commSpace h (H.map β.toMonoidHom))
  rw [← commutator_sup_tvSub_eq] at h1 h2
  have h3 : (centralizer (H : Set (stabE (ε := ε) h)) ⊓
      (⁅(zBlockHom (ε := ε) h).ker, H⁆ ⊔ tvSub h)).map β.toMonoidHom =
        centralizer ((H.map β.toMonoidHom : Subgroup (stabE (ε := ε) h)) :
          Set (stabE (ε := ε) h)) ⊓
            (⁅(zBlockHom (ε := ε) h).ker, H.map β.toMonoidHom⁆ ⊔ tvSub h) := by
    rw [Subgroup.map_inf _ _ _ β.injective, centralizer_map_mulAut,
      map_commutator_sup_tvSub hE hT]
  apply card_eq_of_card_avecPre h
  rw [← h1, ← h2, ← h3, Subgroup.card_map_of_injective β.injective]

theorem card_commSpace_inf_fixOne_map (H : Subgroup (stabE (ε := ε) h))
    {z : stabE (ε := ε) h} {m : ℕ} (hm : Odd m) (hz : z ^ m = 1) :
    Nat.card ↥(commSpace h (H.map β.toMonoidHom) ⊓ fixOne h (β z)) =
      Nat.card ↥(commSpace h H ⊓ fixOne h z) := by
  have hz' : (β z) ^ m = 1 := by rw [← map_pow, hz, map_one]
  have h1 := centralizer_singleton_inf_avecPre_eq h hm hz (commSpace h H)
  have h2 := centralizer_singleton_inf_avecPre_eq h hm hz' (commSpace h (H.map β.toMonoidHom))
  rw [← commutator_sup_tvSub_eq] at h1 h2
  have h3 : (centralizer ({z} : Set (stabE (ε := ε) h)) ⊓
      (⁅(zBlockHom (ε := ε) h).ker, H⁆ ⊔ tvSub h)).map β.toMonoidHom =
        centralizer ({β z} : Set (stabE (ε := ε) h)) ⊓
          (⁅(zBlockHom (ε := ε) h).ker, H.map β.toMonoidHom⁆ ⊔ tvSub h) := by
    rw [Subgroup.map_inf _ _ _ β.injective, map_centralizer_singleton_mulEquiv β z,
      map_commutator_sup_tvSub hE hT]
  apply card_eq_of_card_avecPre h
  rw [← h1, ← h2, ← h3, Subgroup.card_map_of_injective β.injective]

end Map

section Hyps

omit [CharP K 2] in
theorem finrank_eq_of_card_eq [Finite K] {V V' : Submodule K (Fin ε → K)}
    (hc : Nat.card V = Nat.card V') : Module.finrank K V = Module.finrank K V' := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥V),
    Module.natCard_eq_pow_finrank (K := K) (V := ↥V')] at hc
  exact Nat.pow_right_injective Finite.one_lt_card hc

omit [CharP K 2] in
theorem inf_eq_bot_of_card {V W : Submodule K (Fin ε → K)}
    (h1 : Nat.card ↥(V.toAddSubgroup ⊓ W.toAddSubgroup) = 1) : V ⊓ W = ⊥ := by
  have hs := (Nat.card_eq_one_iff_unique.mp h1).1
  rw [eq_bot_iff]
  intro x hx
  have h2 : (⟨x, hx⟩ : ↥(V.toAddSubgroup ⊓ W.toAddSubgroup)) = 0 := Subsingleton.elim _ _
  exact (Submodule.mem_bot K).mpr (congrArg Subtype.val h2)

omit [CharP K 2] in
theorem card_of_inf_eq_bot {V W : Submodule K (Fin ε → K)} (hb : V ⊓ W = ⊥) :
    Nat.card ↥(V.toAddSubgroup ⊓ W.toAddSubgroup) = 1 := by
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨0⟩⟩
  have hx : (x : Fin ε → K) ∈ V ⊓ W := x.2
  have hy : (y : Fin ε → K) ∈ V ⊓ W := y.2
  rw [hb, Submodule.mem_bot] at hx hy
  rw [hx, hy]

theorem toAddSubgroup_commSub (H : Subgroup (stabE (ε := ε) h)) :
    (commSub h H).toAddSubgroup = commSpace h H :=
  AddSubgroup.ext fun _ => Iff.rfl

theorem toAddSubgroup_fixSub (H : Subgroup (stabE (ε := ε) h)) :
    (fixSub h H).toAddSubgroup = fixSpace h H :=
  AddSubgroup.ext fun _ => Iff.rfl

theorem toAddSubgroup_fixOneSub (z : stabE (ε := ε) h) :
    (fixOneSub h z).toAddSubgroup = fixOne h z :=
  AddSubgroup.ext fun _ => Iff.rfl

theorem card_commSub (H : Subgroup (stabE (ε := ε) h)) :
    Nat.card ↥(commSub h H) = Nat.card ↥(commSpace h H) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem card_fixSub (H : Subgroup (stabE (ε := ε) h)) :
    Nat.card ↥(fixSub h H) = Nat.card ↥(fixSpace h H) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem module_hyps_map [Finite K] (hf : 2 ≤ f) (hε : 2 ≤ ε) (β : MulAut (stabE (ε := ε) h))
    {H : Subgroup (stabE (ε := ε) h)} (hH : ⁅H, H⁆ = H)
    (hS : Module.finrank K (commSub h H) = 2) (hC : Module.finrank K (fixSub h H) = ε - 2)
    (hSC : commSub h H ⊓ fixSub h H = ⊥) {z : stabE (ε := ε) h} {m : ℕ} (hm : Odd m)
    (hzm : z ^ m = 1) (hzH : ∀ g ∈ H, z * g = g * z) (hzS : commSub h H ⊓ fixOneSub h z = ⊥) :
    ⁅H.map β.toMonoidHom, H.map β.toMonoidHom⁆ = H.map β.toMonoidHom ∧
      Module.finrank K (commSub h (H.map β.toMonoidHom)) = 2 ∧
      Module.finrank K (fixSub h (H.map β.toMonoidHom)) = ε - 2 ∧
      commSub h (H.map β.toMonoidHom) ⊓ fixSub h (H.map β.toMonoidHom) = ⊥ ∧
      (∀ g ∈ H.map β.toMonoidHom, β z * g = g * β z) ∧
      commSub h (H.map β.toMonoidHom) ⊓ fixOneSub h (β z) = ⊥ := by
  have hE := map_ker_zBlockHom h hf hε β
  have hT := map_tvSub h hf hε β
  refine ⟨by rw [← Subgroup.map_commutator, hH], ?_, ?_, ?_, ?_, ?_⟩
  · refine Eq.trans (finrank_eq_of_card_eq ?_) hS
    rw [card_commSub, card_commSub]
    exact card_commSpace_map hE hT H
  · refine Eq.trans (finrank_eq_of_card_eq ?_) hC
    rw [card_fixSub, card_fixSub]
    exact card_fixSpace_map hE hH
  · have h1 := card_of_inf_eq_bot hSC
    rw [toAddSubgroup_commSub, toAddSubgroup_fixSub] at h1
    apply inf_eq_bot_of_card
    rw [toAddSubgroup_commSub, toAddSubgroup_fixSub, card_commSpace_inf_fixSpace_map hE hT hH, h1]
  · rintro _ ⟨g, hg, rfl⟩
    change β z * β g = β g * β z
    rw [← map_mul, ← map_mul, hzH g hg]
  · have h1 := card_of_inf_eq_bot hzS
    rw [toAddSubgroup_commSub, toAddSubgroup_fixOneSub] at h1
    apply inf_eq_bot_of_card
    rw [toAddSubgroup_commSub, toAddSubgroup_fixOneSub,
      card_commSpace_inf_fixOne_map hE hT H hm hzm, h1]

end Hyps

end CFSG.ComponentClassification.RankTwoClassical.URigid
