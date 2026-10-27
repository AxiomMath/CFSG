module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123CentralZeroAbs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup Equiv

section Abstract

open CFSG.QuasithinUnique.L246.C123 CFSG.SectionRank.Ccomm

theorem a7h_sixteen_mul_card_le {V : Type} [CommGroup V] [Finite V] [Nontrivial V]
    (hV2 : ∀ v : V, v ^ 2 = 1) {Λ : Type} [Group Λ] (act : Λ →* MulAut V) (α : Λ →* A7)
    (hα : Function.Surjective α) (hker : ∀ q : Λ, α q = 1 → act q = 1) (Z : Subgroup V)
    (hZfix : ∀ g : Λ, ∀ z ∈ Z, act g z = z)
    (hgen : Subgroup.closure {x : V | ∃ (g : Λ) (v : V), x = act g v * v⁻¹} = ⊤) :
    16 * Nat.card Z ≤ Nat.card V := by
  have hstab : ∀ g : Λ, act g ∈ CFSG.Quasithin.stabSub Z := by
    intro g u
    constructor
    · intro h
      have hu : act g u = u := (act g).injective (hZfix g _ h)
      rw [hu] at h
      exact h
    · intro h
      rw [hZfix g u h]
      exact h
  let actHat : Λ →* MulAut (V ⧸ Z) :=
    (CFSG.Quasithin.quotHom Z).comp (act.codRestrict (CFSG.Quasithin.stabSub Z) hstab)
  have hactHat : ∀ (g : Λ) (v : V),
      actHat g (QuotientGroup.mk v) = QuotientGroup.mk (act g v) := fun g v => rfl
  have hker' : α.ker ≤ actHat.ker := by
    intro q hq
    have h1 : act.codRestrict (CFSG.Quasithin.stabSub Z) hstab q = 1 := Subtype.ext (hker q hq)
    show CFSG.Quasithin.quotHom Z (act.codRestrict (CFSG.Quasithin.stabSub Z) hstab q) = 1
    rw [h1, map_one]
  let σ : A7 →* MulAut (V ⧸ Z) := (MonoidHom.liftOfSurjective α hα) ⟨actHat, hker'⟩
  have hσ : ∀ g : Λ, σ (α g) = actHat g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply α _ _ ⟨actHat, hker'⟩ g
  have hinj : Function.Injective σ := by
    have := isSimple_A7
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal σ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff σ).1 h
    · exfalso
      have hall : ∀ (g : Λ) (v : V), act g v * v⁻¹ ∈ Z := by
        intro g v
        have h1 : actHat g = 1 := by
          rw [← hσ]
          exact (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top (α g))
        have h2 := congrArg (fun φ : MulAut (V ⧸ Z) => φ (QuotientGroup.mk v)) h1
        simp only [hactHat, MulAut.one_apply] at h2
        exact (CFSG.Quasithin.mk_eq_mk_iff _ _).1 h2
      have hZtop : Z = ⊤ := by
        rw [eq_top_iff, ← hgen, Subgroup.closure_le]
        rintro _ ⟨g, v, rfl⟩
        exact hall g v
      have hbot : Subgroup.closure {x : V | ∃ (g : Λ) (v : V), x = act g v * v⁻¹} = ⊥ := by
        rw [eq_bot_iff, Subgroup.closure_le]
        rintro _ ⟨g, v, rfl⟩
        rw [hZfix g v (hZtop ▸ Subgroup.mem_top v), mul_inv_cancel]
        exact Subgroup.one_mem _
      rw [hgen] at hbot
      exact top_ne_bot hbot
  have hQ2 : ∀ x : V ⧸ Z, x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hV2 v]; rfl
  have hQp : IsPGroup 2 (V ⧸ Z) := fun x => ⟨1, by rw [pow_one]; exact hQ2 x⟩
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (p := 2) (W := V ⧸ Z)
    (fun a b => mul_comm a b) hQ2 hk
  have h1 : Nat.card A7 ≤ Nat.card (GL (Fin k) (ZMod 2)) :=
    Nat.card_le_card_of_injective ((elemAutEquivGL e) ∘ σ)
      ((elemAutEquivGL e).injective.comp hinj)
  rw [card_A7, card_GL_zmod] at h1
  have hk4 : 4 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k <;> simp [Fin.prod_univ_succ] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  rw [hk] at h2
  have h3 : 16 ≤ 2 ^ k :=
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
  rw [h2]
  exact Nat.mul_le_mul_right _ h3

end Abstract

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem a7h_conj_mem {J X : Subgroup G} (hX : ∀ j ∈ J, X.map (MulAut.conj j).toMonoidHom = X)
    {j x : G} (hj : j ∈ J) (hx : x ∈ X) : j * x * j⁻¹ ∈ X := by
  rw [← hX j hj]
  exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem a7h_commutator_le {J X : Subgroup G}
    (hX : ∀ j ∈ J, X.map (MulAut.conj j).toMonoidHom = X) : ⁅X, J⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx j hj
  rw [commutatorElement_def, show x * j * x⁻¹ * j⁻¹ = x * (j * x⁻¹ * j⁻¹) by group]
  exact X.mul_mem hx (a7h_conj_mem hX hj (X.inv_mem hx))

omit [Finite G] in
theorem a7h_exists_largest (J W : Subgroup G) :
    ∃ U : Subgroup G, U ≤ W ∧ (∀ j ∈ J, U.map (MulAut.conj j).toMonoidHom = U) ∧ ⁅U, J⁆ = U ∧
      ∀ X : Subgroup G, X ≤ W → (∀ j ∈ J, X.map (MulAut.conj j).toMonoidHom = X) →
        ⁅X, J⁆ = X → X ≤ U := by
  let S : Set (Subgroup G) :=
    {X | X ≤ W ∧ (∀ j ∈ J, X.map (MulAut.conj j).toMonoidHom = X) ∧ ⁅X, J⁆ = X}
  have hle : ∀ j ∈ J, (sSup S).map (MulAut.conj j).toMonoidHom ≤ sSup S := by
    intro j hj
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun X hX => ?_
    rw [← Subgroup.map_le_iff_le_comap, hX.2.1 j hj]
    exact le_sSup hX
  have hinv : ∀ j ∈ J, (sSup S).map (MulAut.conj j).toMonoidHom = sSup S := by
    intro j hj
    refine le_antisymm (hle j hj) fun x hx => ⟨j⁻¹ * x * j, ?_, ?_⟩
    · have h := hle j⁻¹ (J.inv_mem hj) ⟨x, hx, rfl⟩
      simpa using h
    · simp [mul_assoc]
  refine ⟨sSup S, sSup_le fun X hX => hX.1, hinv,
    le_antisymm (a7h_commutator_le hinv) (sSup_le fun X hX => ?_),
    fun X hXW hXJ hXc => le_sSup ⟨hXW, hXJ, hXc⟩⟩
  calc X = ⁅X, J⁆ := hX.2.2.symm
    _ ≤ ⁅sSup S, J⁆ := Subgroup.commutator_mono_left (le_sSup hX)

omit [Finite G] in
def a7h_conj {J U : Subgroup G} (hU : ∀ j ∈ J, ∀ u ∈ U, j * u * j⁻¹ ∈ U) :
    ↥J →* MulAut ↥U where
  toFun j :=
    { toFun := fun u => ⟨(j : G) * u * (j : G)⁻¹, hU j j.2 u u.2⟩
      invFun := fun u => ⟨(j : G)⁻¹ * u * (j : G), by
        simpa using hU (j : G)⁻¹ (J.inv_mem j.2) u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun u => Subtype.ext (by simp)
  map_mul' j k := MulEquiv.ext fun u => Subtype.ext (by simp [mul_assoc])

open CFSG.QuasithinUnique.L246.C123 in
theorem exists_a7_natural_module {H : Subgroup G}
    {ι : ↥H →* Perm (Fin 7)} {J W : Subgroup G} (hJH : J ≤ H)
    (hJW : ∀ j ∈ J, W.map (MulAut.conj j).toMonoidHom = W) (hW : IsElemAbelian 2 W)
    (hι : (J.subgroupOf H).map ι = alternatingGroup (Fin 7))
    (hker : ∀ j : ↥H, (j : G) ∈ J → ι j = 1 → ∀ w ∈ W, (j : G) * w * (j : G)⁻¹ = w)
    (hbound : Nat.card W ≤ 16 * Nat.card (W ⊓ centralizer (J : Set G) : Subgroup G))
    {X₀ : Subgroup G} (hX₀W : X₀ ≤ W)
    (hX₀J : ∀ j ∈ J, X₀.map (MulAut.conj j).toMonoidHom = X₀)
    (hX₀ne : X₀ ≠ ⊥) (hX₀c : ⁅X₀, J⁆ = X₀) :
    ∃ U : Subgroup G, U ≤ W ∧ Nat.card U = 16 ∧ U ⊓ centralizer (J : Set G) = ⊥ ∧
      W ≤ U ⊔ (W ⊓ centralizer (J : Set G)) ∧
      (∀ j ∈ J, U.map (MulAut.conj j).toMonoidHom = U) ∧ ⁅U, J⁆ = U ∧
      ∀ X : Subgroup G, X ≤ W → (∀ j ∈ J, X.map (MulAut.conj j).toMonoidHom = X) →
        ⁅X, J⁆ = X → X ≤ U := by
  have _ := hJW
  obtain ⟨U, hUW, hUJ, hUc, hUmax⟩ := a7h_exists_largest J W
  have hX₀U : X₀ ≤ U := hUmax X₀ hX₀W hX₀J hX₀c
  have hUne : U ≠ ⊥ := fun h => hX₀ne (eq_bot_iff.2 (h ▸ hX₀U))
  have hCU : (W ⊓ centralizer (J : Set G)) ⊓ U = U ⊓ centralizer (J : Set G) := by
    rw [inf_comm W, inf_assoc, inf_of_le_right hUW, inf_comm]
  generalize hC : W ⊓ centralizer (J : Set G) = C at hbound hCU ⊢
  have hCW : C ≤ W := hC ▸ inf_le_left
  have hWC := Subgroup.relIndex_mul_card C W
  rw [inf_of_le_left hCW] at hWC
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hidx : C.relIndex W ≤ 16 := by
    by_contra h
    push Not at h
    have h17 : 17 * Nat.card C ≤ C.relIndex W * Nat.card C := Nat.mul_le_mul_right _ h
    omega
  have hne : C.relIndex W ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hWC
    omega
  have hUidx := Subgroup.relIndex_le_of_le_right hUW hne
  have hUC := Subgroup.relIndex_mul_card C U
  rw [hCU] at hUC
  have hupper : Nat.card U ≤ 16 * Nat.card (U ⊓ centralizer (J : Set G) : Subgroup G) := by
    rw [← hUC]
    exact Nat.mul_le_mul_right _ (hUidx.trans hidx)
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    have h := @mul_comm' _ _ hW.1 (⟨x, hx⟩ : ↥W) ⟨y, hy⟩
    exact congrArg Subtype.val h
  let _ : CommGroup ↥U :=
    { (inferInstance : Group ↥U) with
      mul_comm := fun a b => Subtype.ext (hWcomm _ (hUW a.2) _ (hUW b.2)) }
  have hUinv : ∀ j ∈ J, ∀ u ∈ U, j * u * j⁻¹ ∈ U := fun j hj u hu => a7h_conj_mem hUJ hj hu
  let act : ↥J →* MulAut ↥U := a7h_conj hUinv
  have hιJ : ∀ x : ↥J, (ι.comp (Subgroup.inclusion hJH)) x ∈ alternatingGroup (Fin 7) := by
    intro x
    rw [← hι]
    exact ⟨Subgroup.inclusion hJH x, x.2, rfl⟩
  let α : ↥J →* A7 := (ι.comp (Subgroup.inclusion hJH)).codRestrict _ hιJ
  have hα : Function.Surjective α := by
    intro σ
    have hσ : (σ : Perm (Fin 7)) ∈ (J.subgroupOf H).map ι := by
      rw [hι]
      exact σ.2
    obtain ⟨h, hh, hhσ⟩ := hσ
    refine ⟨⟨h, hh⟩, Subtype.ext ?_⟩
    show ι (Subgroup.inclusion hJH ⟨(h : G), hh⟩) = σ
    rw [← hhσ]
    rfl
  have hkerα : ∀ q : ↥J, α q = 1 → act q = 1 := by
    intro q hq
    have h1 : ι (Subgroup.inclusion hJH q) = 1 := congrArg Subtype.val hq
    refine MulEquiv.ext fun u => Subtype.ext ?_
    exact hker (Subgroup.inclusion hJH q) q.2 h1 u (hUW u.2)
  let Z : Subgroup ↥U := (U ⊓ centralizer (J : Set G)).subgroupOf U
  have hZfix : ∀ g : ↥J, ∀ z ∈ Z, act g z = z := by
    intro g z hz
    have hz' : (z : G) ∈ centralizer (J : Set G) := (Subgroup.mem_subgroupOf.1 hz).2
    refine Subtype.ext ?_
    show (g : G) * z * (g : G)⁻¹ = z
    rw [Subgroup.mem_centralizer_iff] at hz'
    rw [hz' g g.2, mul_inv_cancel_right]
  have hgen : Subgroup.closure {x : ↥U | ∃ (g : ↥J) (v : ↥U), x = act g v * v⁻¹} = ⊤ := by
    rw [eq_top_iff]
    rintro u -
    have hle : ⁅U, J⁆ ≤
        (Subgroup.closure {x : ↥U | ∃ (g : ↥J) (v : ↥U), x = act g v * v⁻¹}).map U.subtype := by
      rw [Subgroup.commutator_le]
      intro a ha j hj
      refine ⟨act ⟨j, hj⟩ ⟨a⁻¹, U.inv_mem ha⟩ * (⟨a⁻¹, U.inv_mem ha⟩ : ↥U)⁻¹,
        Subgroup.subset_closure ⟨⟨j, hj⟩, _, rfl⟩, ?_⟩
      rw [commutatorElement_def]
      show j * a⁻¹ * j⁻¹ * a⁻¹⁻¹ = a * j * a⁻¹ * j⁻¹
      rw [inv_inv]
      have h := hWcomm _ (hUW (hUinv j hj _ (U.inv_mem ha))) a (hUW ha)
      calc j * a⁻¹ * j⁻¹ * a = a * (j * a⁻¹ * j⁻¹) := h
        _ = a * j * a⁻¹ * j⁻¹ := by group
    have hu : (u : G) ∈ ⁅U, J⁆ := by
      rw [hUc]
      exact u.2
    obtain ⟨y, hy, hyu⟩ := hle hu
    have : y = u := Subtype.ext hyu
    exact this ▸ hy
  have hV2 : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (hW.2 v (hUW v.2))
  have : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).2 hUne
  have hZcard : Nat.card Z = Nat.card (U ⊓ centralizer (J : Set G) : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hlower := a7h_sixteen_mul_card_le hV2 act α hα hkerα Z hZfix hgen
  rw [hZcard] at hlower
  have hcard : Nat.card ↥U = 16 * Nat.card Z := by
    rw [hZcard]
    omega
  have hZ := central_zero_abstract hV2 act α hα hkerα Z hZfix hcard hgen
  have hUC0 : U ⊓ centralizer (J : Set G) = ⊥ := by
    rw [← Subgroup.card_eq_one, ← hZcard, hZ, Subgroup.card_bot]
  have hU16 : Nat.card U = 16 := by
    rw [hcard, hZ, Subgroup.card_bot, mul_one]
  refine ⟨U, hUW, hU16, hUC0, ?_, hUJ, hUc, hUmax⟩
  have hSW : U ⊔ C ≤ W := sup_le hUW hCW
  rw [hUC0, Subgroup.card_bot, mul_one, hU16] at hUC
  have h2 := Subgroup.relIndex_mul_card C (U ⊔ C)
  rw [inf_of_le_left (le_sup_right : C ≤ U ⊔ C)] at h2
  have hne' : C.relIndex (U ⊔ C) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    have : 0 < Nat.card (U ⊔ C : Subgroup G) := Nat.card_pos
    omega
  have h1 := Subgroup.relIndex_le_of_le_right (le_sup_left : U ≤ U ⊔ C) hne'
  have h3 : Nat.card W ≤ Nat.card (U ⊔ C : Subgroup G) := by
    rw [← h2]
    calc Nat.card W ≤ 16 * Nat.card C := hbound
      _ ≤ C.relIndex (U ⊔ C) * Nat.card C := Nat.mul_le_mul_right _ (hUC ▸ h1)
  exact (Subgroup.eq_of_le_of_card_ge hSW h3).ge

end CFSG.LocalAnalysis.RankThreeTheoremC
