module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupRankOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Basic
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Local
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup)
open CFSG.ComponentClassification.AschbacherKnownGroup (HasDihedralSylowTwo)
open scoped Pointwise

section FourGroup

variable {G : Type*} [Group G]

theorem sq_eq_one_of_mem_zpowers {u : G} (hu : u ^ 2 = 1) {x : G} (hx : x ∈ zpowers u) :
    x ^ 2 = 1 := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  calc (u ^ i) ^ 2 = (u ^ 2) ^ i := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    _ = 1 := by rw [hu, one_zpow]

omit [Group G] in
theorem eq_one_or_eq_of_mem_zpowers [Group G] [Finite G] {u x : G} (hu : u ^ 2 = 1)
    (hu1 : u ≠ 1) (hx : x ∈ zpowers u) : x = 1 ∨ x = u := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime hu hu1] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  interval_cases i
  · left; exact pow_zero u
  · right; exact pow_one u

theorem hasFourGroup_of_commute [Finite G] {X : Subgroup G} {u w : G} (huX : u ∈ X) (hwX : w ∈ X)
    (hu : u ^ 2 = 1) (hw : w ^ 2 = 1) (hu1 : u ≠ 1) (hw1 : w ≠ 1) (huw : u ≠ w)
    (hc : u * w = w * u) : HasFourGroup X := by
  have hcomm : Commute u w := hc
  have hN : zpowers u ≤ normalizer (zpowers w : Set G) :=
    (zpowers_le.mpr (mem_centralizer_iff.mpr fun h hh => by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
      exact (hcomm.symm.zpow_left j).eq)).trans (centralizer_le_normalizer _)
  refine ⟨zpowers u ⊔ zpowers w, sup_le (zpowers_le.mpr huX) (zpowers_le.mpr hwX), ?_, ?_⟩
  · intro e he
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hN] at he
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp he
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    rw [(hcomm.zpow_zpow i j).mul_pow, sq_eq_one_of_mem_zpowers hu (zpow_mem (mem_zpowers u) i),
      sq_eq_one_of_mem_zpowers hw (zpow_mem (mem_zpowers w) j), one_mul]
  · have h1 := card_sup_mul_card_inf hN
    have hinf : zpowers u ⊓ zpowers w = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxu, hxw⟩ := mem_inf.mp hx
      rcases eq_one_or_eq_of_mem_zpowers hu hu1 hxu with rfl | rfl
      · exact one_mem _
      · rcases eq_one_or_eq_of_mem_zpowers hw hw1 hxw with h | h
        · exact absurd h hu1
        · exact absurd h huw
    rw [hinf, card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hu hu1,
      orderOf_eq_prime hw hw1] at h1
    exact h1

theorem mul_comm_of_sq_eq_one {E : Subgroup G} (hE : ∀ e ∈ E, e ^ 2 = 1) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := by
  have h1 := hE _ (mul_mem ha hb)
  have h2 := hE a ha
  have h3 := hE b hb
  rw [pow_two] at h1 h2 h3
  calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right h3, inv_eq_of_mul_eq_one_right h2]

theorem HasFourGroup.exists_commute [Finite G] {X : Subgroup G} (h : HasFourGroup X) :
    ∃ u ∈ X, ∃ w ∈ X, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u := by
  classical
  obtain ⟨E, hEX, hE, hE4⟩ := h
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    mul_comm_of_sq_eq_one hE ha hb
  have hcard : 2 < Nat.card E := by omega
  obtain ⟨⟨u, huE⟩, hu1⟩ : ∃ x : E, x ≠ 1 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have : Subsingleton E := ⟨fun a b => (hcon a).trans (hcon b).symm⟩
    have := Finite.card_le_one_iff_subsingleton.mpr this
    omega
  have hex : ∃ x : E, x ≠ 1 ∧ x ≠ ⟨u, huE⟩ := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : Nat.card E ≤ 2 := by
      have : Fintype E := Fintype.ofFinite E
      have hsub : (Finset.univ : Finset E) ⊆ {1, ⟨u, huE⟩} := fun x _ => by
        by_cases h1 : x = 1
        · simp [h1]
        · simp [hcon x h1]
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  obtain ⟨⟨w, hwE⟩, hw1, hwu⟩ := hex
  refine ⟨u, hEX huE, w, hEX hwE, hE u huE, hE w hwE, fun h => hu1 (Subtype.ext h),
    fun h => hw1 (Subtype.ext h), fun h => hwu (Subtype.ext h.symm), hcomm u huE w hwE⟩

end FourGroup

section Dihedral

variable {X : Type} [Group X] [Finite X]

theorem isCyclic_or_dihedral_of_isSylowOf {R M P : Subgroup X} (hR : IsSylowOf 2 R M)
    (hRd : IsDihedralTwoGroup R) (hPM : P ≤ M) (hP : IsPGroup 2 P) :
    IsCyclic P ∨ ∃ k : ℕ, 1 ≤ k ∧ Nonempty (P ≃* DihedralGroup (2 ^ k)) := by
  obtain ⟨c, -, hcR⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hR hP hPM
  obtain ⟨n, hn, ⟨e⟩⟩ := hRd
  set P' := rightConjugate P c
  let e₁ : P ≃* P' := P.equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective
  let e₂ : P' ≃* P'.subgroupOf R := (subgroupOfEquivOfLe hcR).symm
  let e₃ : P'.subgroupOf R ≃* (P'.subgroupOf R).map e.toMonoidHom :=
    (P'.subgroupOf R).equivMapOfInjective e.toMonoidHom e.injective
  let E := e₁.trans (e₂.trans e₃)
  rcases CFSG.GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral (m := n - 1)
      (by omega) ((P'.subgroupOf R).map e.toMonoidHom) with h | ⟨k, hk, ⟨f⟩⟩
  · exact Or.inl ((MulEquiv.isCyclic E).mpr h)
  · exact Or.inr ⟨k, hk, ⟨E.trans f⟩⟩

omit [Finite X] in
theorem dihedral_not_commute {n : ℕ} (hn : 3 ≤ n) :
    DihedralGroup.r (1 : ZMod n) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r (1 : ZMod n) := by
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
  intro h
  have h1 : (0 - 1 : ZMod n) = 0 + 1 := DihedralGroup.sr.inj h
  have h2 : ((2 : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_ofNat]
    linear_combination -h1
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem card_le_four_of_sq_eq_one {R M E : Subgroup X} (hR : IsSylowOf 2 R M)
    (hRd : IsDihedralTwoGroup R) (hEM : E ≤ M) (hE : ∀ e ∈ E, e ^ 2 = 1)
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) : Nat.card E ≤ 4 := by
  classical
  rcases isCyclic_or_dihedral_of_isSylowOf hR hRd hEM (isPGroup_of_sq_eq_one hE) with
    h | ⟨k, hk, ⟨f⟩⟩
  ·
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
    have hg2 : g ^ 2 = 1 := Subtype.ext (by simpa using hE g g.2)
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)).trans (by norm_num)
  ·
    have hk1 : k = 1 := by
      by_contra hk1
      have h4 : 3 ≤ 2 ^ k := by
        have : 2 ≤ k := by omega
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
      apply dihedral_not_commute h4
      have := hc (f.symm (DihedralGroup.r 1)) (f.symm (DihedralGroup.r 1)).2
        (f.symm (DihedralGroup.sr 0)) (f.symm (DihedralGroup.sr 0)).2
      have h' : f.symm (DihedralGroup.r 1) * f.symm (DihedralGroup.sr 0) =
          f.symm (DihedralGroup.sr 0) * f.symm (DihedralGroup.r 1) := Subtype.ext this
      rw [← map_mul, ← map_mul] at h'
      exact f.symm.injective h'
    rw [Nat.card_congr f.toEquiv, hk1, Nat.card_eq_fintype_card, DihedralGroup.card]
    norm_num

theorem hasDihedralSylowTwo_of_le {R M L : Subgroup X} (hR : IsSylowOf 2 R M)
    (hRd : IsDihedralTwoGroup R) (hLM : L ≤ M) (h4 : HasFourGroup L) : HasDihedralSylowTwo L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 L))
  obtain ⟨u, huL, w, hwL, hu, hw, hu1, hw1, huw, hc⟩ := h4.exists_commute
  have hnc : ¬ IsCyclic (S : Subgroup L) :=
    AschbacherKnownGroup.FactsL2.not_isCyclic_sylow_of_commuting_involutions
      (u := (⟨u, huL⟩ : L)) (w := (⟨w, hwL⟩ : L)) (Subtype.ext hu) (Subtype.ext hw)
      (fun h => hu1 (congrArg Subtype.val h)) (fun h => hw1 (congrArg Subtype.val h))
      (fun h => huw (congrArg Subtype.val h)) (Subtype.ext hc) S
  set P := (S : Subgroup L).map L.subtype
  let e : (S : Subgroup L) ≃* P := (S : Subgroup L).equivMapOfInjective L.subtype
    L.subtype_injective
  rcases isCyclic_or_dihedral_of_isSylowOf hR hRd ((map_subtype_le _).trans hLM)
      (S.isPGroup'.map L.subtype) with h | ⟨k, hk, ⟨f⟩⟩
  · exact absurd ((MulEquiv.isCyclic e).mpr h) hnc
  · exact ⟨S, k + 1, by omega, ⟨e.trans (by rw [Nat.add_sub_cancel]; exact f)⟩⟩

end Dihedral

section Simple

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem open_isQuasisimple_of_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

omit [Finite A] in
theorem mul_comm_of_isCyclic {Y : Type*} [Group Y] (h : IsCyclic Y) (a b : Y) : a * b = b * a := by
  obtain ⟨g, hg⟩ := h.exists_generator
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hg a)
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hg b)
  rw [← zpow_add, ← zpow_add, add_comm]

theorem not_isCyclic_sylow_of_isPerfect {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (he : Even (Nat.card Y)) (S : Sylow 2 Y) : ¬ IsCyclic (S : Subgroup Y) := by
  intro hcyc
  obtain ⟨-, hmul, -, ⟨hN, hodd, -, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hcyc
  set N := CFSG.pPrimeCore 2 Y
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (S : Subgroup Y).subtype) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    have hx : x ∈ (N : Set Y) * (S : Set Y) := hmul ▸ Set.mem_univ x
    obtain ⟨a, ha, t, ht, rfl⟩ := Set.mem_mul.mp hx
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [MonoidHom.comp_apply, coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have := hN.conj_mem a ha t⁻¹
    simpa [mul_assoc] using this
  have hQc : ∀ z w : Y ⧸ N, z * w = w * z := by
    intro z w
    obtain ⟨s, rfl⟩ := hsurj z
    obtain ⟨t, rfl⟩ := hsurj w
    rw [← map_mul, ← map_mul, mul_comm_of_isCyclic hcyc]
  have hcomm : commutator Y ≤ N := by
    rw [_root_.commutator_def, commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hQc (x : Y ⧸ N) y]
    group
  rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at hcomm
  rw [hcomm, card_top] at hodd
  exact Nat.not_even_iff_odd.mpr hodd he

theorem hasFourGroup_of_isComponent {R : Subgroup A} (hR : IsSylowOf 2 R ⊤)
    (hRd : IsDihedralTwoGroup R) {C : Subgroup A} (hC : CFSG.IsComponent C) : HasFourGroup C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect C := hC.1.1
  obtain ⟨SC⟩ := (inferInstance : Nonempty (Sylow 2 C))
  let e : (SC : Subgroup C) ≃* (SC : Subgroup C).map C.subtype :=
    (SC : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective
  rcases isCyclic_or_dihedral_of_isSylowOf hR hRd le_top (SC.isPGroup'.map C.subtype) with
    h | ⟨k, hk, ⟨f⟩⟩
  · exact absurd ((MulEquiv.isCyclic e).mpr h)
      (not_isCyclic_sylow_of_isPerfect (even_card_of_isComponent hC) SC)
  · have hev : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
    obtain ⟨u, w, hu, hw, hu1, hw1, huw, hc, -, -⟩ :=
      AschbacherKnownGroup.FactsL2.dihedral_exists_commuting_involutions hev
        (by positivity) 1 (one_pow 2)
    have hmem : ∀ x : DihedralGroup (2 ^ k),
        ((f.symm x : (SC : Subgroup C).map C.subtype) : A) ∈ C :=
      fun x => map_subtype_le _ (f.symm x).2
    have hinj : ∀ x y : DihedralGroup (2 ^ k),
        ((f.symm x : (SC : Subgroup C).map C.subtype) : A) = (f.symm y : _) → x = y :=
      fun x y h => f.symm.injective (Subtype.ext h)
    refine hasFourGroup_of_commute (hmem u) (hmem w) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← coe_pow, ← map_pow, hu, map_one, coe_one]
    · rw [← coe_pow, ← map_pow, hw, map_one, coe_one]
    · intro h
      exact hu1 (hinj u 1 (by rw [h, map_one, coe_one]))
    · intro h
      exact hw1 (hinj w 1 (by rw [h, map_one, coe_one]))
    · exact fun h => huw (hinj u w h)
    · rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, hc]

theorem isSimpleGroup_of_layer_eq_top (hlay : CFSG.layer A = ⊤)
    (hO : CFSG.Assembly.oddCore A = ⊥) (hd : HasDihedralSylowTwo A) : IsSimpleGroup A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, n, hn, ⟨e⟩⟩ := hd
  have hSs : IsSylowOf 2 (S : Subgroup A) ⊤ :=
    isSylowOf_of_card le_top (by rw [card_top]; exact S.card_eq_multiplicity)
  have hSd : IsDihedralTwoGroup (S : Subgroup A) := ⟨n, hn, ⟨e⟩⟩
  have hZ : ∀ C : Subgroup A, CFSG.IsComponent C →
      (Nat.card (center C)).factorization 2 = 0 := fun C hC =>
    (AschbacherKnownGroup.dihedral_quotient_center (open_isQuasisimple_of_isQuasisimple hC.1)
      (hasDihedralSylowTwo_of_le hSs hSd le_top (hasFourGroup_of_isComponent hSs hSd hC))).2
  have huniq : ∀ C₁ C₂ : Subgroup A, CFSG.IsComponent C₁ → CFSG.IsComponent C₂ → C₁ = C₂ := by
    intro C₁ C₂ h1 h2
    by_contra hne
    have hcomm := (CFSG.LocalCores.distinct_components_commute h1 h2).resolve_left hne
    obtain ⟨V₁, hV₁, hE₁, hc₁⟩ := hasFourGroup_of_isComponent hSs hSd h1
    obtain ⟨V₂, hV₂, hE₂, hc₂⟩ := hasFourGroup_of_isComponent hSs hSd h2
    have hC12 : C₁ ≤ centralizer (C₂ : Set A) := commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hV12 : V₁ ≤ centralizer (V₂ : Set A) := (hV₁.trans hC12).trans (centralizer_le hV₂)
    have hN : V₁ ≤ normalizer (V₂ : Set A) := hV12.trans (centralizer_le_normalizer _)
    have hsq : ∀ x ∈ V₁ ⊔ V₂, x ^ 2 = 1 := by
      intro x hx
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hN] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
      have hab : Commute a b := (mem_centralizer_iff.mp (hV12 ha) b hb).symm
      rw [hab.mul_pow, hE₁ a ha, hE₂ b hb, one_mul]
    have h4 := card_le_four_of_sq_eq_one hSs hSd le_top hsq
      (fun a ha b hb => mul_comm_of_sq_eq_one hsq ha hb)
    have h16 := card_sup_mul_card_inf hN
    rw [hc₁, hc₂] at h16
    have hge : 4 ≤ Nat.card (V₁ ⊓ V₂ : Subgroup A) := by
      by_contra h
      have hpos : 0 < Nat.card (V₁ ⊔ V₂ : Subgroup A) := Nat.card_pos
      nlinarith
    have hinf : V₁ ⊓ V₂ = V₁ := eq_of_le_of_card_ge inf_le_left (by omega)
    have hV₁C₂ : V₁ ≤ C₂ := (inf_eq_left.mp hinf).trans hV₂
    have hV₁Z : V₁.subgroupOf C₁ ≤ center C₁ := fun x hx => by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext ((mem_centralizer_iff.mp (hC12 y.2) _ (hV₁C₂ hx)).symm)
    have hdvd : 2 ∣ Nat.card (center C₁) := by
      have h1 := card_dvd_of_le hV₁Z
      rw [Nat.card_congr (subgroupOfEquivOfLe hV₁).toEquiv, hc₁] at h1
      exact (show 2 ∣ 4 by norm_num).trans h1
    have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hdvd
    rw [hZ C₁ h1] at this
    exact lt_irrefl 0 this
  have hex : ∃ C : Subgroup A, CFSG.IsComponent C := by
    by_contra hcon
    simp only [not_exists] at hcon
    have h1 := CFSG.LocalCores.layer_eq_bot_of_forall hcon
    rw [hlay] at h1
    have hcard : Nat.card A = 1 := by rw [← card_top, h1, card_bot]
    have hS : Nat.card (S : Subgroup A) = 2 ^ n := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card,
        ← pow_succ', Nat.sub_add_cancel (by omega)]
    have hle : Nat.card (S : Subgroup A) ≤ Nat.card A := card_le_card_group _
    rw [hS, hcard] at hle
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨C, hC⟩ := hex
  have hCtop : C = ⊤ := by
    rw [← hlay]
    exact le_antisymm (CFSG.LocalCores.component_le_layer hC)
      (sSup_le fun C' hC' => (huniq C' C hC' hC).le)
  have hq : CFSG.IsQuasisimple A := by
    have h := hC.1
    rw [hCtop] at h
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv topEquiv h
  have hZA : center A = ⊥ := by
    have hZ2 := (AschbacherKnownGroup.dihedral_quotient_center
      (open_isQuasisimple_of_isQuasisimple hq) ⟨S, n, hn, ⟨e⟩⟩).2
    have hodd : Odd (Nat.card (center A)) := by
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      intro h2
      have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
      rw [hZ2] at this
      exact lt_irrefl 0 this
    have h := le_assemblyOddCore (center A).normal_of_characteristic hodd
    rw [hO] at h
    exact le_bot_iff.mp h
  have : IsSimpleGroup (A ⧸ center A) := hq.2.1
  exact MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hZA.symm))

end Simple

end CFSG.ComponentClassification.Asc75T4
