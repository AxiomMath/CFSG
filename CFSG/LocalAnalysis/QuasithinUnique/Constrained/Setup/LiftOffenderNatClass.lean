module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderNat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyNatural

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Generic

theorem isElementaryAbelian_bot {G : Type*} [Group G] (p : ℕ) :
    CFSG.IsElementaryAbelian p (⊥ : Subgroup G) where
  is_comm := ⟨fun x y => by
    have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
    have hy : y = 1 := Subtype.ext (Subgroup.mem_bot.1 y.2)
    rw [hx, hy]⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
    have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
    rw [hx, one_pow]

theorem isElementaryAbelian_sup_of_commute {G : Type*} [Group G] {p : ℕ} {A D : Subgroup G}
    (hA : CFSG.IsElementaryAbelian p A) (hD : CFSG.IsElementaryAbelian p D)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) : CFSG.IsElementaryAbelian p ↥(A ⊔ D) := by
  have hmem : ∀ x ∈ A ⊔ D, ∃ a ∈ A, ∃ d ∈ D, x = a * d := fun x hx =>
    exists_mul_of_mem_sup_of_commute hcomm hx
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.1.1 ⟨a, ha⟩ ⟨a', ha'⟩)
  have hDc : ∀ d ∈ D, ∀ d' ∈ D, d * d' = d' * d := fun d hd d' hd' =>
    congrArg Subtype.val (hD.1.1.1 ⟨d, hd⟩ ⟨d', hd'⟩)
  have hApow : ∀ a ∈ A, a ^ p = 1 := fun a ha => by
    have := hA
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hDpow : ∀ d ∈ D, d ^ p = 1 := fun d hd => by
    have := hD
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian d hd
  exact
    { is_comm := ⟨fun x y => by
        obtain ⟨a, ha, d, hd, hx⟩ := hmem x.1 x.2
        obtain ⟨a', ha', d', hd', hy⟩ := hmem y.1 y.2
        apply Subtype.ext
        show (x : G) * y = y * x
        rw [hx, hy]
        calc a * d * (a' * d') = a * (d * a') * d' := by group
          _ = a * (a' * d) * d' := by rw [← hcomm a' ha' d hd]
          _ = (a * a') * (d * d') := by group
          _ = (a' * a) * (d' * d) := by rw [hAc a ha a' ha', hDc d hd d' hd']
          _ = a' * (a * d') * d := by group
          _ = a' * (d' * a) * d := by rw [hcomm a ha d' hd']
          _ = a' * d' * (a * d) := by group⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        obtain ⟨a, ha, d, hd, hx⟩ := hmem x.1 x.2
        apply Subtype.ext
        show (x : G) ^ p = 1
        rw [hx, (show Commute a d from hcomm a ha d hd).mul_pow, hApow a ha, hDpow d hd, one_mul] }

theorem eq_of_commute_isSylowTwoOf {G : Type*} [Group G] [Finite G] {L A A' : Subgroup G}
    (hS : IsSylowTwoOf A L) (hS' : IsSylowTwoOf A' L) (hAe : CFSG.IsElementaryAbelian 2 A)
    (hAe' : CFSG.IsElementaryAbelian 2 A') (hcomm : ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a) :
    A = A' := by
  have := isElementaryAbelian_sup_of_commute hAe hAe' hcomm
  have hP : IsPGroup 2 (A ⊔ A' : Subgroup G) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have key : ∀ {B B' : Subgroup G}, IsSylowTwoOf B L → IsSylowTwoOf B' L →
      IsPGroup 2 (B ⊔ B' : Subgroup G) → B' ≤ B := by
    intro B B' hB hB' hBB'
    obtain ⟨Q, hQ⟩ := (isSylowOf_two_of hB).exists_sylow_eq_subgroupOf
    have hsupL : B ⊔ B' ≤ L := sup_le hB.1 hB'.1
    have hPp : IsPGroup 2 ((B ⊔ B').subgroupOf L) :=
      hBB'.of_equiv (Subgroup.subgroupOfEquivOfLe hsupL).symm
    have hle : (Q : Subgroup ↥L) ≤ (B ⊔ B').subgroupOf L := by
      rw [hQ]
      intro x hx
      exact (le_sup_left : B ≤ B ⊔ B') hx
    have heq := Q.is_maximal' hPp hle
    intro b' hb'
    have h1 : (⟨b', hB'.1 hb'⟩ : ↥L) ∈ (B ⊔ B').subgroupOf L := (le_sup_right : B' ≤ B ⊔ B') hb'
    rw [heq, hQ] at h1
    exact h1
  exact le_antisymm (key hS' hS (by rw [sup_comm]; exact hP)) (key hS hS' hP)

end Generic

section Natural

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] in
theorem moves_of_le_of_ne_bot (ctx : FamilyCtx H T n F r Lc) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    {i : Fin r} (hA : A ≤ Lc i) (hne : A ≠ ⊥) : ⁅Lc i, A⁆ ≠ ⊥ := by
  intro hbot
  apply hne
  rw [eq_bot_iff]
  intro a ha
  have hcent : ∀ l : ↥(Lc i), (⟨a, hA ha⟩ : ↥(Lc i)) * l = l * ⟨a, hA ha⟩ := by
    intro l
    apply Subtype.ext
    have h1 : ⁅(l : V ≃ₗ[ZMod 2] V), a⁆ ∈ ⁅Lc i, A⁆ := Subgroup.commutator_mem_commutator l.2 ha
    rw [hbot, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_commute.1 h1).symm.eq
  have hz : (⟨a, hA ha⟩ : ↥(Lc i)) ∈ Subgroup.center ↥(Lc i) :=
    Subgroup.mem_center_iff.2 fun l => (hcent l).symm
  rw [ctx.layer.center_trivial i, Subgroup.mem_bot] at hz
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hz)

theorem natural_iSup_weight (ctx : FamilyCtx H T n F r Lc)
    (hglob : ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i) (U : Fin r → Subgroup (V ≃ₗ[ZMod 2] V))
    (I : Finset (Fin r)) (hU : ∀ i ∈ I, IsSylowTwoOf (U i) (Lc i)) :
    CFSG.IsElementaryAbelian 2 ↥(⨆ i ∈ I, U i) ∧
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (⨆ i ∈ I, U i) = Nat.card V ∧
      (⨆ i ∈ I, U i) ≤ H := by
  classical
  have hnat := natural_family ctx hglob
  induction I using Finset.induction_on with
  | empty =>
    have hbot : (⨆ i ∈ (∅ : Finset (Fin r)), U i) = ⊥ := by simp
    rw [hbot]
    exact ⟨isElementaryAbelian_bot 2, weight_bot _, bot_le⟩
  | insert j I' hj ih =>
    have hU' : ∀ i ∈ I', IsSylowTwoOf (U i) (Lc i) := fun i hi => hU i (Finset.mem_insert_of_mem hi)
    obtain ⟨ihel, ihw, ihH⟩ := ih hU'
    have hSj : IsSylowTwoOf (U j) (Lc j) := hU j (Finset.mem_insert_self _ _)
    have hA : IsMinOffender H (U j) := (hnat.P_eq (U j)).2 ⟨j, hSj⟩
    have hmove : ⁅Lc j, U j⁆ ≠ ⊥ := moves_of_le_of_ne_bot ctx hSj.1 hA.2.1
    rw [Finset.iSup_insert]
    have hDL : (⨆ i ∈ I', U i) ≤ ⨆ i, ⨆ (_ : i ≠ j), Lc i :=
      iSup₂_le fun i hi => (hU' i hi).1.trans (le_iSup₂_of_le i (fun h => hj (h ▸ hi)) le_rfl)
    have hcomm : ∀ a ∈ U j, ∀ d ∈ (⨆ i ∈ I', U i), a * d = d * a := by
      intro a ha d hd
      have : (⨆ i ∈ I', U i) ≤ Subgroup.centralizer (Lc j : Set (V ≃ₗ[ZMod 2] V)) := by
        refine hDL.trans (iSup₂_le fun i hij z hz => ?_)
        exact Subgroup.mem_centralizer_iff.2 fun l hl =>
          ctx.hLc.elem_commute (Ne.symm hij) l hl z hz
      exact Subgroup.mem_centralizer_iff.1 (this hd) a (hSj.1 ha)
    have hdisj : Disjoint (U j) (⨆ i ∈ I', U i) := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have h1 : x ∈ Lc j ⊓ ⨆ i, ⨆ (_ : i ≠ j), Lc i := ⟨hSj.1 hx.1, hDL hx.2⟩
      rw [ctx.layer.direct j] at h1
      exact h1
    have hDW : commGL (Lc j) ⊤ ≤ fixSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (⨆ i ∈ I', U i) := by
      intro w hw d hd
      have hle : (⨆ i ∈ I', U i) ≤ centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (commGL (Lc j) ⊤) :=
        hDL.trans (iSup₂_le fun i hij z hz => mem_centSub.2 fun v hv =>
          ctx.layer.others_fix j i hij z hz v hv)
      exact mem_centSub.1 (hle hd) w hw
    obtain ⟨hd, -⟩ := ctx.offd (U j) hA j hmove
    obtain ⟨-, -, h3⟩ := fixed_codimensions_add (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (U j)
      (⨆ i ∈ I', U i) hcomm (commGL (Lc j) ⊤) hDW hd.V_split
    obtain ⟨h4, -⟩ := h3 hdisj
    have hwj := weight_eq_of_mem ctx hA
    refine ⟨isElementaryAbelian_sup_of_commute hA.2.2.1 ihel hcomm, ?_,
      sup_le (hA.1) ihH⟩
    rw [hwj, ihw] at h4
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card V) h4

theorem isSylowTwoOf_of_moves (ctx : FamilyCtx H T n F r Lc)
    (hglob : ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hA : IsMinOffender H A) {i : Fin r} (hmove : ⁅Lc i, A⁆ ≠ ⊥) :
    IsSylowTwoOf A (Lc i) :=
  isSylowTwoOf_of_natData ctx ((alt_dichotomy ctx hA i hmove).resolve_right fun h =>
    h.2.2.1 (hglob i A hA hmove))

theorem natural_offender_iff (ctx : FamilyCtx H T n F r Lc)
    (hglob : ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i)
    (E : Subgroup (V ≃ₗ[ZMod 2] V)) :
    IsOffender H E ↔ ∃ (I : Finset (Fin r)) (U : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)), I.Nonempty ∧
      (∀ i ∈ I, IsSylowTwoOf (U i) (Lc i)) ∧ E = ⨆ i ∈ I, U i := by
  classical
  have hnat := natural_family ctx hglob
  constructor
  · intro hE
    suffices h : ∀ m : ℕ, ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), Nat.card E = m → IsOffender H E →
        ∃ (I : Finset (Fin r)) (U : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)), I.Nonempty ∧
          (∀ i ∈ I, IsSylowTwoOf (U i) (Lc i)) ∧ E = ⨆ i ∈ I, U i from h _ E rfl hE
    have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro E hm hE
      obtain ⟨A, hAE, hA⟩ := exists_minOffender_le hE
      obtain ⟨-, i, hi, -⟩ := ctx.layer.offender A hA
      obtain ⟨D, hDE, hAD, hED, hDw, hDc⟩ := natural_split ctx hglob hA hi hE hAE
      have hSA : IsSylowTwoOf A (Lc i) := isSylowTwoOf_of_moves ctx hglob hA hi
      by_cases hD : D = ⊥
      · refine ⟨{i}, fun _ => A, Finset.singleton_nonempty _, ?_, ?_⟩
        · intro j hj
          have hji := Finset.mem_singleton.1 hj
          subst hji
          exact hSA
        · rw [hED, hD, sup_bot_eq]
          simp
      · have hDoff : IsOffender H D :=
          ⟨hDE.trans hE.1, hD, isElementaryAbelian_of_le hDE hE.2.2.1, hDw.ge⟩
        have hDne : D ≠ E := by
          intro hDE'
          apply hA.2.1
          rw [← hAD, eq_comm, inf_eq_left, hDE']
          exact hAE
        have hlt : Nat.card D < m := by
          rw [← hm]
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hDE) fun hcard => hDne ?_
          exact Subgroup.eq_of_le_of_card_ge hDE hcard.symm.le
        obtain ⟨I', U', hne', hU', hDeq⟩ := ih (Nat.card D) hlt D rfl hDoff
        have hi' : i ∉ I' := by
          intro hiI
          have hSi := hU' i hiI
          have hUD : U' i ≤ D := hDeq ▸ le_iSup₂_of_le i hiI le_rfl
          have hUne : U' i ≠ ⊥ := ((hnat.P_eq (U' i)).2 ⟨i, hSi⟩).2.1
          refine moves_of_le_of_ne_bot ctx hSi.1 hUne ?_
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun l hl =>
            Subgroup.mem_centralizer_iff.2 fun u hu => hDc u (hUD hu) l hl
        refine ⟨insert i I', Function.update U' i A, Finset.insert_nonempty _ _, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.1 hj with rfl | hj
          · simpa using hSA
          · rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi')]
            exact hU' j hj
        · rw [Finset.iSup_insert, Function.update_self, hED, hDeq]
          congr 1
          exact iSup_congr fun j => iSup_congr fun hj => by
            rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi')]
  · rintro ⟨I, U, hne, hU, rfl⟩
    obtain ⟨hel, hw, hH⟩ := natural_iSup_weight ctx hglob U I hU
    obtain ⟨j, hj⟩ := hne
    have hA : IsMinOffender H (U j) := (hnat.P_eq (U j)).2 ⟨j, hU j hj⟩
    refine ⟨hH, ?_, hel, hw.ge⟩
    intro hbot
    apply hA.2.1
    rw [eq_bot_iff, ← hbot]
    exact le_iSup₂_of_le j hj le_rfl

theorem natural_product_weight (ctx : FamilyCtx H T n F r Lc)
    (hglob : ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i)
    (s : Finset (Subgroup (V ≃ₗ[ZMod 2] V))) (hs : ∀ A ∈ s, IsMinOffender H A)
    (hind : s.SupIndep id)
    (hcomm : ∀ A ∈ s, ∀ A' ∈ s, ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a) :
    CFSG.IsElementaryAbelian 2 ↥(s.sup id) ∧
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (s.sup id) = Nat.card V ∧ s.sup id ≤ H := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hbot : ((∅ : Finset (Subgroup (V ≃ₗ[ZMod 2] V))).sup id) = ⊥ := by simp
    rw [hbot]
    exact ⟨isElementaryAbelian_bot 2, weight_bot _, bot_le⟩
  | insert A s' hAs' ih =>
    have hs' : ∀ A'' ∈ s', IsMinOffender H A'' := fun A'' h =>
      hs A'' (Finset.mem_insert_of_mem h)
    have hind' : s'.SupIndep id := hind.subset (Finset.subset_insert _ _)
    have hcomm' : ∀ A₁ ∈ s', ∀ A₂ ∈ s', ∀ a ∈ A₁, ∀ a' ∈ A₂, a * a' = a' * a :=
      fun A₁ h₁ A₂ h₂ => hcomm A₁ (Finset.mem_insert_of_mem h₁) A₂ (Finset.mem_insert_of_mem h₂)
    obtain ⟨ihel, ihw, ihH⟩ := ih hs' hind' hcomm'
    have hA : IsMinOffender H A := hs A (Finset.mem_insert_self _ _)
    obtain ⟨-, i, hmove, -⟩ := ctx.layer.offender A hA
    have hSA := isSylowTwoOf_of_moves ctx hglob hA hmove
    have hdisj : Disjoint A (s'.sup id) :=
      hind (Finset.subset_insert A s') (Finset.mem_insert_self A s') hAs'
    have hfix : s'.sup id ≤ centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (commGL (Lc i) ⊤) := by
      refine Finset.sup_le fun A'' hA''s => ?_
      have hA'' := hs' A'' hA''s
      obtain ⟨-, j, hj, -⟩ := ctx.layer.offender A'' hA''
      have hSA'' := isSylowTwoOf_of_moves ctx hglob hA'' hj
      have hji : j ≠ i := by
        rintro rfl
        have heq := eq_of_commute_isSylowTwoOf hSA hSA'' hA.2.2.1 hA''.2.2.1
          (hcomm A (Finset.mem_insert_self _ _) A'' (Finset.mem_insert_of_mem hA''s))
        exact hAs' (heq ▸ hA''s)
      intro z hz
      exact mem_centSub.2 fun v hv => ctx.layer.others_fix i j hji z (hSA''.1 hz) v hv
    have hcommA : ∀ a ∈ A, ∀ d ∈ s'.sup id, a * d = d * a := by
      have : s'.sup id ≤ Subgroup.centralizer (A : Set (V ≃ₗ[ZMod 2] V)) :=
        Finset.sup_le fun A'' hA''s z hz => Subgroup.mem_centralizer_iff.2 fun a ha =>
          hcomm A (Finset.mem_insert_self _ _) A'' (Finset.mem_insert_of_mem hA''s) a ha z hz
      intro a ha d hd
      exact Subgroup.mem_centralizer_iff.1 (this hd) a ha
    have hDW : commGL (Lc i) ⊤ ≤ fixSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (s'.sup id) :=
      fun w hw d hd => mem_centSub.1 (hfix hd) w hw
    obtain ⟨hd, -⟩ := ctx.offd A hA i hmove
    obtain ⟨-, -, h3⟩ := fixed_codimensions_add (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A (s'.sup id)
      hcommA (commGL (Lc i) ⊤) hDW hd.V_split
    obtain ⟨h4, -⟩ := h3 hdisj
    rw [Finset.sup_insert]
    have hwj := weight_eq_of_mem ctx hA
    refine ⟨isElementaryAbelian_sup_of_commute hA.2.2.1 ihel hcommA, ?_, sup_le hA.1 ihH⟩
    rw [hwj, ihw] at h4
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card V) h4

theorem natural_internal_product_iff (ctx : FamilyCtx H T n F r Lc)
    (hglob : ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i)
    (E : Subgroup (V ≃ₗ[ZMod 2] V)) :
    IsOffender H E ↔ ∃ s : Finset (Subgroup (V ≃ₗ[ZMod 2] V)), s.Nonempty ∧
      (∀ A ∈ s, IsMinOffender H A) ∧ IsInternalProduct E s := by
  constructor
  · intro hE
    exact offender_internal_product (natural_offenderSplit ctx hglob) hE
  · rintro ⟨s, hne, hs, hind, rfl, hcomm⟩
    obtain ⟨hel, hw, hH⟩ := natural_product_weight ctx hglob s hs hind hcomm
    obtain ⟨A, hAs⟩ := hne
    refine ⟨hH, ?_, hel, hw.ge⟩
    intro hbot
    apply (hs A hAs).2.1
    rw [eq_bot_iff, ← hbot]
    exact Finset.le_sup (f := id) hAs

end Natural

end CFSG.QuasithinUnique.Setup.Lift
