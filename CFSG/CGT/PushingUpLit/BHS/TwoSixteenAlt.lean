module

public import CFSG.CGT.PushingUpLit.BHS.AltCore
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteen
public import CFSG.Quasithin.Background.D216Restrict

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement

section Wrap

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem cenIn_eq_inf (A : Subgroup (MulAut V)) (U : Subgroup V) : cenIn A U = A ⊓ centSub U := by
  ext a
  simp [mem_cenIn, mem_centSub]

omit [Finite V] in
theorem normalizer_commV_le_stabSub (E : Subgroup (MulAut V)) :
    Subgroup.normalizer (E : Set (MulAut V)) ≤ stabSub (commV E) := by
  intro g hg u
  constructor
  · intro h
    have := CFSG.Quasithin.B15P4.map_commV_mem ((Subgroup.normalizer _).inv_mem hg) (g u) h
    simpa using this
  · exact fun h => CFSG.Quasithin.B15P4.map_commV_mem hg u h

omit [Finite V] in
theorem autSub_sup {E A : Subgroup (MulAut V)} {U : Subgroup V} (hE : E ≤ stabSub U)
    (hA : A ≤ stabSub U) : autSub (E ⊔ A) U = autSub E U ⊔ autSub A U := by
  unfold autSub
  rw [Subgroup.subgroupOf_sup hE hA, Subgroup.map_sup]

omit [Finite V] in
theorem exists_mulEquiv_autSub {U : Subgroup V} {X : Subgroup (MulAut V)} (hX : X ≤ stabSub U)
    (hinj : X ⊓ centSub U = ⊥) :
    ∃ φ : ↥X ≃* ↥(autSub X U), ∀ (x : ↥X) (u : ↥U),
      ((((φ x : ↥(autSub X U)) : MulAut ↥U) u : ↥U) : V) = (x : MulAut V) (u : V) := by
  let r : ↥X →* MulAut ↥U := (resHom U).comp (Subgroup.inclusion hX)
  have hr : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (Subgroup.inclusion hX x : stabSub U) ∈ (resHom U).ker := hx
    rw [ker_resHom, Subgroup.mem_subgroupOf, ] at h1
    have h2 : (x : MulAut V) ∈ X ⊓ centSub U := ⟨x.2, h1⟩
    rw [hinj, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hrange : r.range = autSub X U := by
    ext φ
    simp only [MonoidHom.mem_range, mem_autSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hX x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.1, hg⟩, rfl⟩
  refine ⟨(MonoidHom.ofInjective hr).trans (MulEquiv.subgroupCongr hrange), fun x u => rfl⟩


omit [Finite V] in
theorem autSub_le_normalizer {E A : Subgroup (MulAut V)} {U : Subgroup V}
    (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut V))) :
    autSub A U ≤ Subgroup.normalizer ((autSub E U : Subgroup (MulAut U)) : Set (MulAut U)) := by
  have key : ∀ x ∈ autSub A U, ∀ h ∈ autSub E U, x * h * x⁻¹ ∈ autSub E U := by
    intro x hx h hh
    obtain ⟨g, hgA, rfl⟩ := mem_autSub.mp hx
    obtain ⟨e, heE, rfl⟩ := mem_autSub.mp hh
    refine mem_autSub.mpr ⟨g * e * g⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hAN hgA) e).mp heE
    · rw [map_mul, map_mul, map_inv]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key x hx h
  · intro hxh
    have := key x⁻¹ ((autSub A U).inv_mem hx) _ hxh
    rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at this

omit [Finite V] in
theorem isElemAbelian2_autSub {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : IsElemAbelian2 A) :
    IsElemAbelian2 (autSub A U) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
    obtain ⟨h, hh, rfl⟩ := mem_autSub.mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.1 _ hg _ hh)
  · obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
    rw [← map_pow]
    have : g ^ 2 = 1 := Subtype.ext (hA.2 _ hg)
    rw [this, map_one]

omit [Finite V] in
theorem commutator_autSub_ne_bot {E A : Subgroup (MulAut V)} {U : Subgroup V} (hE : E ≤ stabSub U)
    (hA : A ≤ stabSub U) (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut V)))
    (hinj : E ⊓ centSub U = ⊥) (h : ⁅E, A⁆ ≠ ⊥) : ⁅autSub E U, autSub A U⁆ ≠ ⊥ := by
  intro hbot
  apply h
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro e he a ha
  have hcomm : ⁅e, a⁆ ∈ E := by
    have : a * e * a⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hAN ha) e).mp he
    have h2 : ⁅e, a⁆ = e * (a * e * a⁻¹)⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact E.mul_mem he (E.inv_mem this)
  have hx : (resHom U ⟨e, hE he⟩) ∈ autSub E U := mem_autSub.mpr ⟨⟨e, hE he⟩, he, rfl⟩
  have hy : (resHom U ⟨a, hA ha⟩) ∈ autSub A U := mem_autSub.mpr ⟨⟨a, hA ha⟩, ha, rfl⟩
  have h1 := Subgroup.commutator_mem_commutator hx hy
  rw [hbot, Subgroup.mem_bot, ← map_commutatorElement] at h1
  have h2 : (⁅(⟨e, hE he⟩ : stabSub U), (⟨a, hA ha⟩ : stabSub U)⁆ : stabSub U) ∈ (resHom U).ker :=
    h1
  rw [ker_resHom, Subgroup.mem_subgroupOf] at h2
  have h3 : ⁅e, a⁆ ∈ E ⊓ centSub U := ⟨hcomm, h2⟩
  rw [hinj] at h3
  exact h3


theorem card_autSub_eq_relIndex {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U) :
    Nat.card (autSub A U) = (cenIn A U).relIndex A := by
  have h1 := card_autSub_mul hA
  have h2 := relIndex_cenIn_mul_card A U
  rw [cenIn_eq_inf] at h2 ⊢
  have hpos : 0 < Nat.card ↥(A ⊓ centSub U) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem two_sixteen_alt_gen (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : Odd n) (h5 : 5 ≤ n)
    {A E : Subgroup (MulAut V)} {W : Subgroup V} (hWE : commV E = W)
    (θ : E ≃* alternatingGroup (Fin n)) (β : ↥W →* coreMod n) (hβs : Function.Surjective β)
    (hβk : β.ker = (W ⊓ fixV E).subgroupOf W)
    (hβe : ∀ (x : E) (p : ↥W) (hp : (x : MulAut V) p ∈ W),
      β ⟨(x : MulAut V) p, hp⟩ =
        coreAct n ((θ x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) (β p))
    (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut V))) (hAoff : IsOff A)
    (hEA : ⁅E, A⁆ ≠ ⊥) :
    W ⊓ fixV E = ⊥ ∧
      ∃ θX : ↥(autSub E W ⊔ autSub A W) ≃* Equiv.Perm (Fin n),
        Function.Bijective β ∧
        (∀ (x : ↥(autSub E W ⊔ autSub A W)) (w : ↥W),
          β ((x : MulAut ↥W) w) = coreAct n (θX x) (β w)) ∧
        (∃ T : Set (Equiv.Perm (Fin n)), T.Nonempty ∧ (∀ t ∈ T, t.IsSwap) ∧
          (∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) ∧
          ((autSub A W).subgroupOf (autSub E W ⊔ autSub A W)).map θX.toMonoidHom =
            Subgroup.closure T) ∧
        (∀ a ∈ A, ∀ a' ∈ A, ∀ w ∈ W, a' (a w * w⁻¹) = a w * w⁻¹) ∧
        (fixV A).relIndex W = (cenIn A W).relIndex A := by
  classical
  have h3 : 3 ≤ n := by omega
  have hEst : E ≤ stabSub W := by
    rw [← hWE]
    exact Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub E)
  have hAst : A ≤ stabSub W := by
    rw [← hWE]
    exact hAN.trans (normalizer_commV_le_stabSub E)
  have hEq : CFSG.Open.IsQuasisimple ↥E :=
    isQuasisimple_of_mulEquiv' θ.symm (isQuasisimple_alternatingGroup h5)
  have hperf : ⁅E, E⁆ = E := by
    have htop : (⊤ : Subgroup ↥E).map E.subtype = E := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥E)) (H₂ := ⊤) E.subtype
    rw [htop] at h
    rw [← h, ← commutator_def, hEq.1, htop]
  have hcomm : commSub W E = W := by
    have := CFSG.Quasithin.B15P4.commSub_commV_of_perfect hperf
    rwa [hWE] at this
  have hEcen : E ⊓ centSub W = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun e he => ?_
    obtain ⟨heE, hecen⟩ := he
    have h1 : θ ⟨e, heE⟩ = 1 := by
      apply Subtype.ext
      apply coreAct_injective h3
      apply MulEquiv.ext
      intro d
      obtain ⟨p, rfl⟩ := hβs d
      have hp : (e : MulAut V) p ∈ W := by rw [hecen p p.2]; exact p.2
      have := hβe ⟨e, heE⟩ p hp
      have hp' : (⟨e p, hp⟩ : ↥W) = p := Subtype.ext (hecen p p.2)
      rw [hp'] at this
      exact this.symm
    have : (⟨e, heE⟩ : ↥E) = 1 := θ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  obtain ⟨φE, hφE⟩ := exists_mulEquiv_autSub hEst hEcen
  have htopW : (⊤ : Subgroup ↥W).map W.subtype = W := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hW' : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hV w)
  let D : AltNatData (autSub E W) n :=
    { θ := φE.symm.trans θ
      β := β
      surj := hβs
      ker_fix := fun w hw g hg => by
        obtain ⟨e, he⟩ := φE.surjective ⟨g, hg⟩
        have h1 : (w : V) ∈ W ⊓ fixV E := by
          have : w ∈ β.ker := hw
          rw [hβk, Subgroup.mem_subgroupOf] at this
          exact this
        have h2 : (e : MulAut V) w = w := h1.2 e e.2
        apply Subtype.ext
        have := hφE e w
        rw [he] at this
        rw [this]
        exact h2
      equivar := fun e' w => by
        obtain ⟨e, rfl⟩ := φE.surjective e'
        have hp : (e : MulAut V) w ∈ W := by
          have h2 := (((φE e : ↥(autSub E W)) : MulAut ↥W) w).2
          rw [hφE e w] at h2
          exact h2
        have h3 : (((φE e : ↥(autSub E W)) : MulAut ↥W) w) = ⟨(e : MulAut V) w, hp⟩ :=
          Subtype.ext (hφE e w)
        rw [h3, hβe e w hp]
        simp
      comm_top := by
        refine Subgroup.map_injective W.subtype_injective ?_
        rw [← commSub_eq_map_commV hEst, hcomm, htopW] }
  have hAN' : autSub A W ≤ Subgroup.normalizer ((autSub E W : Subgroup (MulAut ↥W)) :
      Set (MulAut ↥W)) := autSub_le_normalizer hAN
  have hel' : IsElemAbelian2 (autSub A W) := isElemAbelian2_autSub hAoff.2.2.1
  have hcardA : Nat.card (autSub A W) = (cenIn A W).relIndex A := card_autSub_eq_relIndex hAst
  have hcardF : Nat.card (fixV (autSub A W)) = Nat.card ↥(fixV A ⊓ W) := by
    have h1 := map_subtype_fixV_autSub hAst
    have h2 : Nat.card ((fixV (autSub A W)).map W.subtype) = Nat.card (fixV (autSub A W)) :=
      Subgroup.card_map_of_injective W.subtype_injective
    rw [h1, inf_comm] at h2
    exact h2.symm
  have hcardW : (fixV A).relIndex W * Nat.card ↥(fixV A ⊓ W) = Nat.card ↥W :=
    Subgroup.relIndex_mul_card (fixV A) W
  have hoffW : (fixV A).relIndex W ≤ (cenIn A W).relIndex A := by
    have := offender_card_le hAoff W
    exact this
  have hAw' : Nat.card ↥W ≤ Nat.card (autSub A W) * Nat.card (fixV (autSub A W)) := by
    rw [hcardA, hcardF, ← hcardW]
    exact Nat.mul_le_mul_right _ hoffW
  have hEA' : ⁅autSub E W, autSub A W⁆ ≠ ⊥ :=
    commutator_autSub_ne_bot hEst hAst hAN hEcen hEA
  obtain ⟨hfixE', θX, hθXE, hequi, ⟨T, hTne, hTsw, hTcomm, hTeq⟩, hquad, hcard⟩ :=
    alt_core hW' hn h5 D hAN' hel' hAw' hEA'
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have := (D.ker_iff hn h3 w).mp hw
    rw [hfixE'] at this
    exact Subgroup.mem_bot.mp this
  refine ⟨?_, θX, ⟨hβinj, hβs⟩, hequi, ⟨T, hTne, hTsw, hTcomm, hTeq⟩, ?_, ?_⟩
  · refine eq_bot_iff.2 fun z hz => ?_
    have hzfix : (⟨z, hz.1⟩ : ↥W) ∈ fixV (autSub E W) := by
      intro g hg
      obtain ⟨e, he⟩ := φE.surjective ⟨g, hg⟩
      apply Subtype.ext
      have := hφE e ⟨z, hz.1⟩
      rw [he] at this
      rw [this]
      exact hz.2 e e.2
    rw [hfixE'] at hzfix
    have := Subgroup.mem_bot.mp hzfix
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · intro a ha a' ha' w hw
    have hgen : (resHom W ⟨a, hAst ha⟩) ⟨w, hw⟩ * (⟨w, hw⟩ : ↥W)⁻¹ ∈ commV (autSub A W) :=
      Subgroup.subset_closure ⟨resHom W ⟨a, hAst ha⟩,
        mem_autSub.mpr ⟨⟨a, hAst ha⟩, ha, rfl⟩, ⟨w, hw⟩, rfl⟩
    have hfx := hquad hgen (resHom W ⟨a', hAst ha'⟩)
      (mem_autSub.mpr ⟨⟨a', hAst ha'⟩, ha', rfl⟩)
    exact congrArg Subtype.val hfx
  · have h := hcard
    rw [hcardA, hcardF, ← hcardW] at h
    have hpos : 0 < Nat.card ↥(fixV A ⊓ W) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h


end Wrap

theorem two_sixteen_alt {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ}
    (hm : 2 ≤ m) {G A E : Subgroup (MulAut V)} (hA : IsOff A) (hAG : A ≤ G) (hEG : E ≤ G)
    (hsub : CFSG.Open.IsSubnormal E G)
    (hnat : IsAltNatSection E (commV E) (commV E ⊓ fixV E) (2 * m + 1))
    (hEA : ⁅E, A⁆ ≠ ⊥) :
    A ≤ Subgroup.normalizer (E : Set (MulAut V)) ∧ commV E ⊓ fixV E = ⊥ ∧
      ∃ (β : ↥(commV E) →* coreMod (2 * m + 1))
        (θX : ↥(autSub E (commV E) ⊔ autSub A (commV E)) ≃* Equiv.Perm (Fin (2 * m + 1))),
        Function.Bijective β ∧
        (∀ (x : ↥(autSub E (commV E) ⊔ autSub A (commV E))) (w : ↥(commV E)),
          β ((x : MulAut ↥(commV E)) w) = coreAct (2 * m + 1) (θX x) (β w)) ∧
        (∃ T : Set (Equiv.Perm (Fin (2 * m + 1))), T.Nonempty ∧ (∀ t ∈ T, t.IsSwap) ∧
          (∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) ∧
          ((autSub A (commV E)).subgroupOf
            (autSub E (commV E) ⊔ autSub A (commV E))).map θX.toMonoidHom =
            Subgroup.closure T) ∧
        (∀ a ∈ A, ∀ a' ∈ A, ∀ w ∈ commV E, a' (a w * w⁻¹) = a w * w⁻¹) ∧
        (fixV A).relIndex (commV E) = (cenIn A (commV E)).relIndex A := by
  have hAN := two_sixteen_a_alt hV hm hA hAG hEG hsub hnat
  obtain ⟨-, θ, β, hβs, hβk, hβe⟩ := hnat
  have hn : Odd (2 * m + 1) := ⟨m, rfl⟩
  obtain ⟨hfix, θX, hbij, hequi, hT, hquad, hidx⟩ :=
    two_sixteen_alt_gen hV hn (by omega) rfl θ β hβs hβk hβe hAN hA hEA
  exact ⟨hAN, hfix, β, θX, hbij, hequi, hT, hquad, hidx⟩

end CFSG.CGT.PushingUpLit.BHS
