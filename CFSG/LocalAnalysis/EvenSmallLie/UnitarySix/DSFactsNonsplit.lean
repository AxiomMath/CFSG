module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFacts
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsNonsplitData

public section

namespace CFSG.EvenSmallLie.UnitarySix

open Subgroup CFSG.Sporadic.Schreier CFSG.Quasithin
open scoped commutatorElement

namespace ToddParabolic

variable {Q : Type} [Group Q] (D : ToddParabolic Q)

theorem conjClass_subset_of_mem {X : Subgroup Q} (hXK : ∀ k ∈ D.K, ∀ x ∈ X, k * x * k⁻¹ ∈ X)
    {a x : Q} (hx : x ∈ conjClass D.K a) (hxX : x ∈ X) : conjClass D.K a ⊆ X := by
  obtain ⟨c, hc, rfl⟩ := hx
  rintro _ ⟨k, hk, rfl⟩
  have := hXK (k * c⁻¹) (D.K.mul_mem hk (D.K.inv_mem hc)) _ hxX
  rwa [show k * c⁻¹ * (c * a * c⁻¹) * (k * c⁻¹)⁻¹ = k * a * k⁻¹ by group] at this

theorem conjClass_eq_of_mem {a b : Q} (h : b ∈ conjClass D.K a) :
    conjClass D.K b = conjClass D.K a := by
  obtain ⟨c, hc, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * c, D.K.mul_mem hk hc, by group⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * c⁻¹, D.K.mul_mem hk (D.K.inv_mem hc), by group⟩

theorem one_not_mem_conjClass {a : Q} (ha : a ≠ 1) : (1 : Q) ∉ conjClass D.K a := by
  rintro ⟨c, -, hc⟩
  apply ha
  have : a = c⁻¹ * (c * a * c⁻¹) * c := by group
  rw [this, ← hc]
  group

theorem ncard_inter_conjClass {X : Subgroup Q} (hXK : ∀ k ∈ D.K, ∀ x ∈ X, k * x * k⁻¹ ∈ X)
    (a : Q) : ((X : Set Q) ∩ conjClass D.K a).ncard = 0 ∨
      ((X : Set Q) ∩ conjClass D.K a).ncard = (conjClass D.K a).ncard := by
  by_cases h : ((X : Set Q) ∩ conjClass D.K a).Nonempty
  · obtain ⟨x, hxX, hx⟩ := h
    right
    rw [Set.inter_eq_right.2 (D.conjClass_subset_of_mem hXK hx hxX)]
  · left
    rw [Set.not_nonempty_iff_eq_empty.1 h, Set.ncard_empty]

theorem a_ne_one {a : Q} (h : 2 ≤ (conjClass D.K a).ncard) : a ≠ 1 := by
  rintro rfl
  have : conjClass D.K 1 ⊆ {1} := by
    rintro _ ⟨c, -, rfl⟩
    simp
  have := Set.ncard_le_ncard this (Set.finite_singleton _)
  rw [Set.ncard_singleton] at this
  omega

theorem disjoint_conjClass {a b : Q} (h : (conjClass D.K a).ncard ≠ (conjClass D.K b).ncard) :
    Disjoint (conjClass D.K a) (conjClass D.K b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  exact h (by rw [← D.conjClass_eq_of_mem hxa, D.conjClass_eq_of_mem hxb])

theorem eq_A_of_invariant {X : Subgroup Q} (hXA : X ≤ D.A)
    (hXK : ∀ k ∈ D.K, ∀ x ∈ X, k * x * k⁻¹ ∈ X) (hX : X ≠ ⊥) : X = D.A := by
  have := D.finite
  obtain ⟨h1, h2, h3⟩ := D.orbit_card
  set C₁ := conjClass D.K D.a₁
  set C₂ := conjClass D.K D.a₂
  set C₃ := conjClass D.K D.a₃
  have hd12 : Disjoint C₁ C₂ := D.disjoint_conjClass (by rw [h1, h2]; norm_num)
  have hd13 : Disjoint C₁ C₃ := D.disjoint_conjClass (by rw [h1, h3]; norm_num)
  have hd23 : Disjoint C₂ C₃ := D.disjoint_conjClass (by rw [h2, h3]; norm_num)
  have n1 : (1 : Q) ∉ C₁ := D.one_not_mem_conjClass (D.a_ne_one (by rw [h1]; norm_num))
  have n2 : (1 : Q) ∉ C₂ := D.one_not_mem_conjClass (D.a_ne_one (by rw [h2]; norm_num))
  have n3 : (1 : Q) ∉ C₃ := D.one_not_mem_conjClass (D.a_ne_one (by rw [h3]; norm_num))
  set Y₁ := (X : Set Q) ∩ C₁
  set Y₂ := (X : Set Q) ∩ C₂
  set Y₃ := (X : Set Q) ∩ C₃
  have hcover : (X : Set Q) = {1} ∪ (Y₁ ∪ (Y₂ ∪ Y₃)) := by
    ext x
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · rcases D.orbits x (hXA hx) hx1 with h | h | h
        · exact Or.inr (Or.inl ⟨hx, h⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨hx, h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hx, h⟩))
    · rintro (h | h | h | h)
      · rw [Set.mem_singleton_iff.1 h]
        exact X.one_mem
      · exact h.1
      · exact h.1
      · exact h.1
  have hdisj1 : Disjoint ({1} : Set Q) (Y₁ ∪ (Y₂ ∪ Y₃)) := by
    rw [Set.disjoint_singleton_left]
    rintro (h | h | h)
    exacts [n1 h.2, n2 h.2, n3 h.2]
  have hdisj2 : Disjoint Y₁ (Y₂ ∪ Y₃) :=
    Set.disjoint_union_right.2 ⟨(hd12.mono Set.inter_subset_right Set.inter_subset_right),
      (hd13.mono Set.inter_subset_right Set.inter_subset_right)⟩
  have hdisj3 : Disjoint Y₂ Y₃ := hd23.mono Set.inter_subset_right Set.inter_subset_right
  have hcard : Nat.card X = 1 + Y₁.ncard + Y₂.ncard + Y₃.ncard := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hcover,
      Set.ncard_union_eq hdisj1 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hdisj2 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hdisj3 (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton]
    ring
  have hdvd : Nat.card X ∣ 2 ^ 9 := D.card_A ▸ Subgroup.card_dvd_of_le hXA
  have hX1 : Nat.card X ≠ 1 := fun h => hX (Subgroup.card_eq_one.1 h)
  have hle : Nat.card D.A ≤ Nat.card X := by
    rw [D.card_A]
    rcases D.ncard_inter_conjClass hXK D.a₁ with e1 | e1 <;>
      rcases D.ncard_inter_conjClass hXK D.a₂ with e2 | e2 <;>
      rcases D.ncard_inter_conjClass hXK D.a₃ with e3 | e3 <;>
      · rw [hcard, e1, e2, e3] at hdvd hX1 ⊢
        rw [h1, h2, h3] at *
        revert hdvd hX1
        norm_num
  exact eq_of_le_of_card_ge hXA hle

end ToddParabolic

section Words

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62 CFSG.Sporadic.Th CFSG.Fischer
  CFSG.F4.Native

theorem getD_u62Letters
    {i : ℕ} (hi : i < 46) : u62Letters.getD i 1 = t46G ((i : ℤ) + 1) := by
  rw [u62Letters, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_finRange]
  exact letter_eq i hi

theorem t46G_neg (z : ℤ) : t46G (-z) = t46G z := by
  have h : CFSG.Sporadic.Fi22.Native.t46Gen (-z) = CFSG.Sporadic.Fi22.Native.t46Gen z := by
    simp only [CFSG.Sporadic.Fi22.Native.t46Gen, Int.natAbs_neg]
  have h2 : Rep 693 (CFSG.Sporadic.Fi22.Native.t46Gen (-z)) (t46G z) := by
    rw [h]
    exact rep_t46G z
  exact rep_unique (rep_t46G (-z)) h2

theorem evalCodes_u62Letters
    (w : List ℤ) (hw : ∀ z ∈ w, 0 < z.natAbs ∧ z.natAbs ≤ 46) :
    evalCodes u62Letters w = wordG t46G w := by
  induction w with
  | nil => simp [evalCodes, wordG]
  | cons z w ih =>
    have hz := hw z List.mem_cons_self
    have ih' := ih (fun z' hz' => hw z' (List.mem_cons_of_mem _ hz'))
    have e1 : evalCodes u62Letters (z :: w) = (if 0 < z then u62Letters.getD (z.toNat - 1) 1
        else (u62Letters.getD ((-z).toNat - 1) 1)⁻¹) * evalCodes u62Letters w := rfl
    have e2 : wordG t46G (z :: w) = t46G z * wordG t46G w := by
      simp only [wordG, List.map_cons, List.prod_cons]
    have e3 : (if 0 < z then u62Letters.getD (z.toNat - 1) 1
        else (u62Letters.getD ((-z).toNat - 1) 1)⁻¹) = t46G z := by
      split_ifs with h
      · rw [getD_u62Letters (by omega), show ((z.toNat - 1 : ℕ) : ℤ) + 1 = z by omega]
      · rw [getD_u62Letters (by omega), t46G_inv, ← t46G_neg z,
          show (((-z).toNat - 1 : ℕ) : ℤ) + 1 = -z by omega]
    rw [e1, e2, ih', e3]

theorem mem_expand {v : List (Fin 5 × Bool)} {z : ℤ} (hz : z ∈ expand v) :
    0 < z.natAbs ∧ z.natAbs ≤ 46 := by
  have key : ∀ i : Fin 5, ∀ z ∈ genWord i, 0 < z.natAbs ∧ z.natAbs ≤ 46 := by decide
  simp only [expand, List.mem_flatMap] at hz
  obtain ⟨l, -, hl⟩ := hz
  split_ifs at hl
  · exact key _ _ hl
  · exact key _ _ (List.mem_reverse.1 hl)

theorem coe_lift_genE
    (v : List (Fin 5 × Bool)) :
    ((FreeGroup.lift genE (FreeGroup.mk v) : T46) : Equiv.Perm (Fin 693)) = u62W (expand v) := by
  rw [lift_genE_val, lift_genP, u62W, tab_eq,
    evalCodes_u62Letters _ fun z hz => mem_expand hz]

theorem ns_facts :
    ((FreeGroup.lift genE (FreeGroup.mk nsE) : T46) : Equiv.Perm (Fin 693)) ∈ uA ∧
      ((FreeGroup.lift genE (FreeGroup.mk nsN₁) : T46) : Equiv.Perm (Fin 693)) ∈
        normalizer (uA : Set (Equiv.Perm (Fin 693))) ∧
      ((FreeGroup.lift genE (FreeGroup.mk nsN₂) : T46) : Equiv.Perm (Fin 693)) ∈
        normalizer (uA : Set (Equiv.Perm (Fin 693))) ∧
      FreeGroup.lift genE (FreeGroup.mk nsC₁) = 1 ∧
        FreeGroup.lift genE (FreeGroup.mk nsC₂) = 1 := by
  obtain ⟨hE, hN, hC₁, hC₂⟩ := ns_t46_check
  have hrep := Rep.wordT (n := 693) (by norm_num) (gens := CFSG.Sporadic.Fi22.Native.t46Gen)
    (gensG := t46G)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [coe_lift_genE, uA_eq]
    exact hE
  · rw [coe_lift_genE]
    exact mem_normalizer_of_conj_gens uA_eq fun a ha => by
      rw [uA_eq]
      exact hN _ List.mem_cons_self a ha
  · rw [coe_lift_genE]
    exact mem_normalizer_of_conj_gens uA_eq fun a ha => by
      rw [uA_eq]
      exact hN _ (List.mem_cons_of_mem _ List.mem_cons_self) a ha
  · refine Subtype.ext ?_
    rw [lift_genE_val, lift_genP]
    exact t46_eq_one_of_fixAll (hrep _ fun l _ => rep_t46G l) hC₁
  · refine Subtype.ext ?_
    rw [lift_genE_val, lift_genP]
    exact t46_eq_one_of_fixAll (hrep _ fun l _ => rep_t46G l) hC₂

theorem mkC_commWord (u v : List (Fin 5 × Bool)) :
    mkC (commWord u v) = ⁅mkC u, mkC v⁆ := by
  rw [commWord, mkC_append, mkC_append, mkC_append, mkC_invRev, mkC_invRev,
    commutatorElement_def]

theorem ns_cover_facts
    : mkC nsC₁ = mkC kerTwo ∧ mkC nsC₂ = mkC kerTwo' := by
  obtain ⟨E, _, ψ, hmove⟩ := ns_cover_check
  obtain ⟨-, -, -, hC₁, hC₂⟩ := ns_facts
  have hk₁ : mkC nsC₁ ∈ coverπ.ker := by
    rw [MonoidHom.mem_ker, coverπ_mk]
    exact hC₁
  have hk₂ : mkC nsC₂ ∈ coverπ.ker := by
    rw [MonoidHom.mem_ker, coverπ_mk]
    exact hC₂
  refine ⟨?_, ?_⟩
  · rw [eq_zWord_of_exclWords ψ hk₁ (0, 1, 0) fun v hv => hmove v (List.mem_append_left _ hv),
      mkC_zWord]
    simp
  · rw [eq_zWord_of_exclWords ψ hk₂ (0, 0, 1) fun v hv => hmove v (List.mem_append_right _ hv),
      mkC_zWord]
    simp

end Words

section Lift

variable {G : Type} [Group G] {L : Subgroup G} {Q : Type} [Group Q] {t : G} {π : L →* Q}

theorem map_conj_commutator_eq {E : Subgroup G} {l : G}
    (hl : l ∈ normalizer (E : Set G) ⊓ L) :
    ⁅E, normalizer (E : Set G) ⊓ L⁆.map (MulAut.conj l).toMonoidHom =
      ⁅E, normalizer (E : Set G) ⊓ L⁆ := by
  have hE : E.map (MulAut.conj l).toMonoidHom = E := by
    have := conjSubgroup_eq_iff_mem_normalizer.2 (inv_mem hl.1)
    rwa [conjSubgroup, inv_inv] at this
  have hN : (normalizer (E : Set G) ⊓ L).map (MulAut.conj l).toMonoidHom =
      normalizer (E : Set G) ⊓ L := by
    have := conjSubgroup_eq_iff_mem_normalizer.2
      (le_normalizer (H := normalizer (E : Set G) ⊓ L) (inv_mem hl))
    rwa [conjSubgroup, inv_inv] at this
  rw [map_commutator, hE, hN]

theorem IsDoubleCover.toddLift_le_commutator (H : IsDoubleCover t L π) (D : ToddParabolic Q)
    (ht : t ∈ ⁅liftSub π D.A, normalizer (liftSub π D.A : Set G) ⊓ L⁆) :
    liftSub π D.A ≤ ⁅liftSub π D.A, normalizer (liftSub π D.A : Set G) ⊓ L⁆ := by
  set E := liftSub π D.A
  set N := normalizer (E : Set G) ⊓ L
  set C := ⁅E, N⁆
  have hCE : C ≤ E := by
    rw [commutator_le]
    intro e he n hn
    have h1 : n * e⁻¹ * n⁻¹ ∈ E := (mem_normalizer_iff.1 hn.1 _).1 (inv_mem he)
    rw [commutatorElement_def]
    simpa [mul_assoc] using E.mul_mem he h1
  have hXA : imgSub π C ≤ D.A := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨h1, h2⟩ := mem_liftSub.1 (hCE hc)
    exact h2
  have hXK : ∀ k ∈ D.K, ∀ x ∈ imgSub π C, k * x * k⁻¹ ∈ imgSub π C := by
    rintro k hk _ ⟨c, hc, rfl⟩
    obtain ⟨l, hl, rfl⟩ := H.exists_mem_eq k
    have hlN : l ∈ N := H.mem_normalizer_of_pi D hl (D.K_le_normalizer hk)
    have hlc : l * c * l⁻¹ ∈ C := by
      have h := map_conj_commutator_eq (E := E) (L := L) hlN
      change C.map (MulAut.conj l).toMonoidHom = C at h
      have h2 : l * c * l⁻¹ ∈ C.map (MulAut.conj l).toMonoidHom := ⟨c, hc, rfl⟩
      rwa [h] at h2
    exact ⟨⟨l * c * l⁻¹, L.mul_mem (L.mul_mem hl c.2) (L.inv_mem hl)⟩, hlc, pi_conj π hl c.2⟩
  have hX : imgSub π C ≠ ⊥ := by
    have h21 := D.orbit_card.1
    have ha1 : D.a₁ ≠ 1 := D.a_ne_one (by rw [h21]; norm_num)
    intro hbot
    refine ha1 (D.eq_one_of_forall_conj D.a_mem.1 fun k hk => ?_)
    obtain ⟨l, hl, rfl⟩ := H.exists_mem_eq k
    obtain ⟨e, he, hea⟩ := H.exists_mem_eq D.a₁
    have hc : ⁅e, l⁆ ∈ C := commutator_mem_commutator (mem_liftSub.2 ⟨he, hea ▸ D.a_mem.1⟩)
      (H.mem_normalizer_of_pi D hl (D.K_le_normalizer hk))
    have hmem : π ⁅(⟨e, he⟩ : L), ⟨l, hl⟩⁆ ∈ imgSub π C := ⟨_, hc, rfl⟩
    rw [hbot, mem_bot, map_commutatorElement, hea, commutatorElement_def] at hmem
    have hak : D.a₁ * π ⟨l, hl⟩ = π ⟨l, hl⟩ * D.a₁ := by
      calc D.a₁ * π ⟨l, hl⟩
          = (D.a₁ * π ⟨l, hl⟩ * D.a₁⁻¹ * (π ⟨l, hl⟩)⁻¹) * (π ⟨l, hl⟩ * D.a₁) := by group
        _ = π ⟨l, hl⟩ * D.a₁ := by rw [hmem, one_mul]
    rw [← hak, mul_inv_cancel_right]
  have hXeq := D.eq_A_of_invariant hXA hXK hX
  intro e he
  obtain ⟨heL, heA⟩ := mem_liftSub.1 he
  rw [← hXeq] at heA
  obtain ⟨c, hc, hce⟩ := heA
  rcases H.eq_or_eq_mul_of_pi_eq hce with h | h
  · change e = c at h
    rw [h]
    exact hc
  · change e = c * t at h
    rw [h]
    exact C.mul_mem hc ht

end Lift

section Cover

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62 CFSG.Fischer

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

theorem t_mem_commutator_toddLift
    [Group.IsPerfect L] {p : L →* Equiv.Perm (Fin 693)}
    (hp : ∀ y, p y ∈ T46) (H : IsDoubleCover t L (p.codRestrict T46 hp)) :
    t ∈ ⁅liftSub (p.codRestrict T46 hp) toddT46.A,
      normalizer (liftSub (p.codRestrict T46 hp) toddT46.A : Set G) ⊓ L⁆ := by
  set q := p.codRestrict T46 hp
  set E := liftSub q toddT46.A
  have hcen : q.ker ≤ center L := fun y hy => by
    rcases (H.ker y).1 hy with h | h
    · rw [show y = 1 from Subtype.ext h]
      exact (center L).one_mem
    · refine mem_center_iff.2 fun g => Subtype.ext ?_
      simp only [coe_mul]
      rw [h]
      exact H.comm_t g.2
  obtain ⟨h, hhs, hhq⟩ := exists_cover_hom q H.surj hcen
  obtain ⟨hE, hN₁, hN₂, -, -⟩ := ns_facts
  obtain ⟨hc₁, hc₂⟩ := ns_cover_facts
  have hq : ∀ v, q (h (mkC v)) = FreeGroup.lift genE (FreeGroup.mk v) := fun v => by
    rw [hhq, coverπ_mk]
  have heE : ((h (mkC nsE) : L) : G) ∈ E := mem_liftSub.2 ⟨(h (mkC nsE)).2, by
    change ((q (h (mkC nsE)) : T46) : Equiv.Perm (Fin 693)) ∈ uA
    rw [hq]
    exact hE⟩
  have hnN : ∀ v, ((FreeGroup.lift genE (FreeGroup.mk v) : T46) : Equiv.Perm (Fin 693)) ∈
      normalizer (uA : Set (Equiv.Perm (Fin 693))) →
      ((h (mkC v) : L) : G) ∈ normalizer (E : Set G) ⊓ L := fun v hv =>
    H.mem_normalizer_of_pi toddT46 (h (mkC v)).2 ((mem_normalizer_T46 uA_le_T46).2 (by
      change ((q (h (mkC v)) : T46) : Equiv.Perm (Fin 693)) ∈ _
      rw [hq]
      exact hv))
  have hcomm : ∀ v, ((h (mkC (commWord v nsE)) : L) : G) =
      ⁅((h (mkC v) : L) : G), ((h (mkC nsE) : L) : G)⁆ := fun v => by
    rw [mkC_commWord, map_commutatorElement]
    rfl
  obtain ⟨hgen, hz₂, hz₂', hz₃, h3, -, -, -, -⟩ := cover_kernel_facts
  have hval : ∀ x ∈ coverπ.ker, ((h x : L) : G) = 1 ∨ ((h x : L) : G) = t := fun x hx =>
    (H.ker (h x)).1 (by rw [hhq, MonoidHom.mem_ker.1 hx])
  have hnot : ¬ (((h (mkC kerTwo) : L) : G) = 1 ∧ ((h (mkC kerTwo') : L) : G) = 1) := by
    rintro ⟨h1, h2⟩
    have h3' : ((h (mkC kerThree) : L) : G) = 1 := by
      rcases hval _ hz₃ with h0 | h0
      · exact h0
      · exfalso
        have : ((h (mkC kerThree) ^ 3 : L) : G) = 1 := by
          rw [← map_pow, h3, map_one]
          rfl
        rw [SubgroupClass.coe_pow, h0, pow_succ, H.t_sq, one_mul] at this
        exact H.t_ne_one this
    have hK : ∀ x ∈ coverπ.ker, h x = 1 := fun x hx => by
      have hle : closure ({mkC kerTwo, mkC kerTwo', mkC kerThree} : Set Cover) ≤ h.ker := by
        rw [closure_le]
        rintro _ (rfl | rfl | rfl)
        · exact Subtype.ext h1
        · exact Subtype.ext h2
        · exact Subtype.ext h3'
      exact hle (hgen x hx)
    obtain ⟨x, hx⟩ := hhs ⟨t, H.t_mem⟩
    have hxk : x ∈ coverπ.ker := by
      rw [MonoidHom.mem_ker, ← hhq, hx]
      exact H.pi_t
    exact H.t_ne_one (congrArg Subtype.val (hx.symm.trans (hK x hxk)))
  have hcN : ∀ v, ((h (mkC v) : L) : G) ∈ normalizer (E : Set G) ⊓ L →
      ((h (mkC (commWord v nsE)) : L) : G) ∈ ⁅E, normalizer (E : Set G) ⊓ L⁆ := by
    intro v hv
    rw [hcomm v, commutator_comm]
    exact commutator_mem_commutator hv heE
  by_cases hz : ((h (mkC kerTwo) : L) : G) = 1
  · have h2' : ((h (mkC kerTwo') : L) : G) = t :=
      (hval _ hz₂').resolve_left fun h2 => hnot ⟨hz, h2⟩
    rw [← h2', ← hc₂]
    exact hcN nsN₂ (hnN nsN₂ hN₂)
  · have h2 : ((h (mkC kerTwo) : L) : G) = t := (hval _ hz₂).resolve_left hz
    rw [← h2, ← hc₁]
    exact hcN nsN₁ (hnN nsN₁ hN₁)

theorem toddLift_nonsplit
    [Group.IsPerfect L] {p : L →* Equiv.Perm (Fin 693)}
    (hp : ∀ y, p y ∈ T46) (hsurj : ∀ x ∈ T46, ∃ y, p y = x)
    (hker : ∀ y : L, p y = 1 ↔ (y : G) = 1 ∨ (y : G) = t) (htL : t ∈ L)
    (hLt : L ≤ centralizer {t}) (ht : orderOf t = 2) :
    (uA.comap p).map L.subtype ≤
      ⁅(uA.comap p).map L.subtype, normalizer ((uA.comap p).map L.subtype : Set G) ⊓ L⁆ := by
  have H := isDoubleCover_codRestrict hp hsurj hker htL hLt ht
  rw [map_comap_uA_eq_liftSub hp]
  exact H.toddLift_le_commutator toddT46 (t_mem_commutator_toddLift hp H)

theorem std_toddOrbit_fields
    [Finite G] (hset : StandardSetting G L) (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) (h2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) {p : L →* Equiv.Perm (Fin 693)}
    (hp : ∀ y, p y ∈ T46) (hsurj : ∀ x ∈ T46, ∃ y, p y = x)
    (hker : ∀ y : L, p y = 1 ↔ (y : G) = 1 ∨ (y : G) = t) :
    (∀ e ∈ (uA.comap p).map L.subtype, e ^ 2 = 1) ∧
      (∀ g ∈ centralizer {t}, Odd (orderOf g) → g ∈ L) ∧
      (∀ g : G, g⁻¹ * t * g ∈ (uA.comap p).map L.subtype →
        ∃ n ∈ normalizer ((uA.comap p).map L.subtype : Set G), g⁻¹ * t * g = n⁻¹ * t * n) ∧
      (∃ n ∈ normalizer ((uA.comap p).map L.subtype : Set G), n⁻¹ * t * n ≠ t) ∧
      (uA.comap p).map L.subtype ≤
        ⁅(uA.comap p).map L.subtype, normalizer ((uA.comap p).map L.subtype : Set G) ⊓ L⁆ := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 hset.standard.1.1
  obtain ⟨D, -, hodd⟩ := davisSolomonFacts_uA hset ht htZ h2 hQ hp hsurj hker
  obtain ⟨-, -, -, -, -, hLt, -⟩ := std_center_facts hset ht htZ
  have htL : t ∈ L := by
    obtain ⟨z, -, rfl⟩ := htZ
    exact z.2
  exact ⟨D.E_sq, hodd, fun g hg => D.fusion hg, std_exists_normalizer_conj_ne hset ht D,
    toddLift_nonsplit hp hsurj hker htL hLt ht⟩

end Cover

end CFSG.EvenSmallLie.UnitarySix
