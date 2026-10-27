module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmAlign
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmGlue
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNRModel
public import Certificates.Certificate15106

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open Subgroup CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7
open CFSG.ComponentClassification.GMS78.RuN CFSG.GMS78RuN

theorem lift_mk_renumber {m : ℕ} {H : Type*} [Group H] (S : List (Fin m)) (g : Fin m → H)
    {w : List (Fin m × Bool)} {w' : List (Fin S.length × Bool)} (h : renumber S w = some w') :
    FreeGroup.lift (fun j => g (S.get j)) (FreeGroup.mk w') =
      FreeGroup.lift g (FreeGroup.mk w) := by
  rw [← map_renumber S w w' h, FreeGroup.lift_mk, FreeGroup.lift_mk, List.map_map]
  rfl

theorem toGroup_mk {m : ℕ} {rels : Set (FreeGroup (Fin m))} {H : Type*} [Group H]
    {f : Fin m → H} (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (x : FreeGroup (Fin m)) :
    PresentedGroup.toGroup h (PresentedGroup.mk rels x) = FreeGroup.lift f x := by
  have e : (PresentedGroup.toGroup h).comp (PresentedGroup.mk rels) = FreeGroup.lift f :=
    FreeGroup.ext_hom _ _ fun i => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      exact PresentedGroup.toGroup.of h
  exact DFunLike.congr_fun e x

theorem lift_ruRels2 {H : Type*} [Group H] (g : Fin 7 → H)
    (hg : ∀ r ∈ pi7Rels, (renumber ruSub2 r).isSome → FreeGroup.lift g (FreeGroup.mk r) = 1) :
    ∀ r ∈ {r : FreeGroup (Fin ruSub2.length) | r ∈ ruRels2.map FreeGroup.mk},
      FreeGroup.lift (fun j => g (ruSub2.get j)) r = 1 := by
  rintro _ hr
  obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hr
  obtain ⟨w, hw, hren⟩ := List.mem_filterMap.mp hw'
  rw [lift_mk_renumber ruSub2 g hren]
  exact hg w hw (by rw [hren]; rfl)

abbrev RuP2 : Type := PG ruSub2.length ruRels2

theorem ruSub2_eq : ruSub2 = [0, 1, 2, 3, 4, 6] := by decide

theorem renumber_isSome_ruA0Words : ∀ w ∈ ruA0Words, (renumber ruSub2 w).isSome = true := by
  decide

theorem lift_of_pi7Rels :
    ∀ r ∈ pi7Rels, (renumber ruSub2 r).isSome →
      FreeGroup.lift (fun i => (PresentedGroup.of i : Pi7)) (FreeGroup.mk r) = 1 :=
  fun r hr _ => (pi7Word_eq_lift r).symm.trans (pi7Word_eq_one hr)

@[expose] noncomputable def ruP2ToPi7 : RuP2 →* Pi7 :=
  PresentedGroup.toGroup (lift_ruRels2 _ lift_of_pi7Rels)

theorem ruP2ToPi7_of (j : Fin ruSub2.length) :
    ruP2ToPi7 (PresentedGroup.of j) = PresentedGroup.of (ruSub2.get j) :=
  PresentedGroup.toGroup.of _

theorem ruP2ToPi7_mk {w : List (Fin 7 × Bool)} {w' : List (Fin ruSub2.length × Bool)}
    (h : renumber ruSub2 w = some w') :
    ruP2ToPi7 (PresentedGroup.mk _ (FreeGroup.mk w')) = pi7Word w := by
  rw [ruP2ToPi7, toGroup_mk, lift_mk_renumber ruSub2 _ h, pi7Word_eq_lift]

theorem range_ruP2ToPi7 : ruP2ToPi7.range = ruM2 := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure, ruM2,
    letterSub]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨ruSub2.get j, ?_, ?_⟩
    · change ruSub2.get j ∈ ([0, 1, 2, 3, 4, 6] : List (Fin 7))
      rw [← ruSub2_eq]
      exact List.get_mem _ _
    · exact (ruP2ToPi7_of j).symm
  · rintro ⟨x, hx, rfl⟩
    change x ∈ ([0, 1, 2, 3, 4, 6] : List (Fin 7)) at hx
    rw [← ruSub2_eq] at hx
    obtain ⟨j, hj⟩ := List.get_of_mem hx
    exact ⟨j, by rw [← hj]; exact ruP2ToPi7_of j⟩

theorem lift_ruNImg_pi7Rels :
    ∀ r ∈ pi7Rels, (renumber ruSub2 r).isSome →
      FreeGroup.lift ruNImg (FreeGroup.mk r) = 1 := by
  intro r hr hs
  have h := Certificates.certificate15106.2.1
  simp only [ruNACheckModel, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h r hr with h1 | h1
  · rw [Option.isNone_iff_eq_none] at h1
    rw [h1] at hs
    exact absurd hs (by decide)
  · rw [(lift_ruNImg r).2, h1, toModel_one]

@[expose] noncomputable def ruP2ToModel : RuP2 →* RuNModel :=
  PresentedGroup.toGroup (lift_ruRels2 _ lift_ruNImg_pi7Rels)

theorem ruP2ToModel_mk {w : List (Fin 7 × Bool)} {w' : List (Fin ruSub2.length × Bool)}
    (h : renumber ruSub2 w = some w') :
    ruP2ToModel (PresentedGroup.mk _ (FreeGroup.mk w')) =
      FreeGroup.lift ruNImg (FreeGroup.mk w) := by
  rw [ruP2ToModel, toGroup_mk, lift_mk_renumber ruSub2 _ h]

theorem card_ruP2_le : Finite RuP2 ∧ Nat.card RuP2 ≤ 344064 :=
  Certificates.certificate15106.1

theorem ruP2ToModel_surjective : Function.Surjective ruP2ToModel := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← ruNImg_closure, closure_le]
  rintro _ ⟨i, hi, rfl⟩
  change i ∈ ([0, 1, 2, 3, 4, 6] : List (Fin 7)) at hi
  rw [← ruSub2_eq] at hi
  obtain ⟨j, hj⟩ := List.get_of_mem hi
  exact ⟨PresentedGroup.of j, by rw [← hj]; exact PresentedGroup.toGroup.of _⟩

theorem ruP2ToModel_bijective : Function.Bijective ruP2ToModel := by
  have := card_ruP2_le.1
  exact ruP2ToModel_surjective.bijective_of_nat_card_le
    (card_ruP2_le.2.trans card_RuNModel.ge)

theorem ruA0Elt_ne_one {e : ℕ} (he : e < 8) (he0 : e ≠ 0) : ruA0Elt e ≠ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [ruA0Elt, ← pi7Word_nil]
  exact pi7Word_ne_of_wordProd (Certificates.certificate15106.2.2 k (by omega))

theorem ruZ0_ne_one : ruZ0 ≠ 1 := by
  have h := ruA0Elt_ne_one (e := 1) (by norm_num) (by norm_num)
  rwa [ruA0Elt, show ruA0PowWord 1 = ruZ0Word by decide] at h

theorem ruP2ToPi7_injective : Function.Injective ruP2ToPi7 := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hK
  have hKn : (ruP2ToPi7.ker.map ruP2ToModel).Normal :=
    Subgroup.Normal.map inferInstance ruP2ToModel ruP2ToModel_surjective
  have hK1 : ruP2ToPi7.ker.map ruP2ToModel ≠ ⊥ := by
    intro h
    apply hK
    rw [eq_bot_iff]
    intro k hk
    have h1 : ruP2ToModel k ∈ ruP2ToPi7.ker.map ruP2ToModel := ⟨k, hk, rfl⟩
    rw [h, mem_bot] at h1
    rw [mem_bot]
    exact ruP2ToModel_bijective.1 (h1.trans (map_one ruP2ToModel).symm)
  have hA := le_of_normal_ne_bot (ruP2ToPi7.ker.map ruP2ToModel) hK1
  have hz0 : ruZ0Word ∈ ruA0Words := by decide
  obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp (renumber_isSome_ruA0Words _ hz0)
  obtain ⟨k, hk, hkz⟩ := hA (ruNImg_A0 _ hz0)
  rw [← ruP2ToModel_mk hw'] at hkz
  have hk' := ruP2ToModel_bijective.1 hkz
  have hk2 : ruP2ToPi7 (PresentedGroup.mk _ (FreeGroup.mk w')) = 1 := hk' ▸ hk
  rw [ruP2ToPi7_mk hw'] at hk2
  exact ruZ0_ne_one hk2

@[expose] noncomputable def ruM2EquivModel : ↥ruM2 ≃* RuNModel :=
  ((MulEquiv.subgroupCongr range_ruP2ToPi7.symm).trans
    (MonoidHom.ofInjective ruP2ToPi7_injective).symm).trans
    (MulEquiv.ofBijective ruP2ToModel ruP2ToModel_bijective)

theorem ruM2EquivModel_symm_apply (x : RuP2) :
    ((ruM2EquivModel.symm (ruP2ToModel x) : ↥ruM2) : Pi7) = ruP2ToPi7 x := by
  have h1 : (MulEquiv.ofBijective ruP2ToModel ruP2ToModel_bijective).symm (ruP2ToModel x) = x :=
    (MulEquiv.ofBijective ruP2ToModel ruP2ToModel_bijective).symm_apply_apply x
  simp only [ruM2EquivModel, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, h1]
  rfl

theorem card_ruA0 : Nat.card ruA0 = 8 := by
  have hinj : Function.Injective fun e : Fin 8 => ruA0Elt e.val := by
    intro e e' h
    by_contra hne
    have hne' : e.val ^^^ e'.val ≠ 0 := fun h0 => hne (Fin.ext (xor_eq_zero_iff.mp h0))
    apply ruA0Elt_ne_one (xor_lt_eight e.isLt e'.isLt) hne'
    rw [← ruA0Elt_mul e.isLt e'.isLt]
    simp only at h
    rw [h, ruA0Elt_mul e'.isLt e'.isLt, Nat.xor_self, ruA0Elt_zero]
  have hbij : Function.Bijective fun e : Fin 8 => (⟨ruA0Elt e.val, ruA0Elt_mem _⟩ : ↥ruA0) := by
    refine ⟨fun e e' h => hinj (congrArg Subtype.val h), fun a => ?_⟩
    obtain ⟨e, he, h⟩ := mem_ruA0_iff.1 a.2
    exact ⟨⟨e, he⟩, Subtype.ext h.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem mem_ruA0_iff_model (m : ↥ruM2) : (m : Pi7) ∈ ruA0 ↔ ruM2EquivModel m ∈ A1model := by
  set θ : RuNModel →* Pi7 := ruM2.subtype.comp ruM2EquivModel.symm.toMonoidHom with hθ
  have hθinj : Function.Injective θ :=
    Subtype.val_injective.comp ruM2EquivModel.symm.injective
  have hθe : ∀ x : ↥ruM2, θ (ruM2EquivModel x) = x := fun x => by
    rw [hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hbasis : ∀ w ∈ ruA0Words, pi7Word w ∈ A1model.map θ := by
    intro w hw
    obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp (renumber_isSome_ruA0Words w hw)
    refine ⟨ruP2ToModel (PresentedGroup.mk _ (FreeGroup.mk w')), ?_, ?_⟩
    · rw [ruP2ToModel_mk hw']
      exact ruNImg_A0 w hw
    · rw [hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype,
        ruM2EquivModel_symm_apply, ruP2ToPi7_mk hw']
  have hle : ruA0 ≤ A1model.map θ := (closure_le _).2 fun x ⟨w, hw, hx⟩ => hx ▸ hbasis w hw
  have : Finite Pi7 := card_pi7_le.1
  have heq : ruA0 = A1model.map θ := Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective hθinj, card_A1model, card_ruA0])
  rw [heq]
  constructor
  · rintro ⟨a, ha, hax⟩
    have e : a = ruM2EquivModel m := hθinj (by rw [hax, hθe])
    rwa [← e]
  · intro h
    exact ⟨_, h, hθe m⟩

theorem ruNAIso_of_model {G : Type} [Group G] {A : Subgroup G}
    (h : ∃ f : RuNModel ≃* ↥(normalizer (A : Set G)),
      ∀ m, m ∈ A1model ↔ ((f m : ↥(normalizer (A : Set G))) : G) ∈ A) :
    RuNAIso A := by
  obtain ⟨f, hf⟩ := h
  exact ⟨ruM2EquivModel.trans f, fun m => by
    rw [mem_ruA0_iff_model, MulEquiv.trans_apply, hf]⟩

end CFSG.ComponentClassification.GMS78.RuAsm
