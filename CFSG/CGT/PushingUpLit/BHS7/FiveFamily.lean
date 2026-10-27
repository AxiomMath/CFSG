module

public import CFSG.CGT.PushingUpLit.BHS6.FaithfulAlt
public import CFSG.CGT.PushingUpLit.BHS5.SymGlue
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenThree

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5 CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem exists_slNatData_autSub {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : ∃ s : Finset F, s.card = 4) {E : Subgroup (MulAut V)} {W : Subgroup V}
    (hWE : commV E = W) (θ : E ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (β : ↥W →* Multiplicative (Fin 2 → F)) (hβs : Function.Surjective β)
    (hβk : β.ker = (W ⊓ fixV E).subgroupOf W)
    (hβe : ∀ (x : E) (p : ↥W) (hp : (x : MulAut V) p ∈ W),
      β ⟨(x : MulAut V) p, hp⟩ = Multiplicative.ofAdd
        ((θ x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β p)))) :
    Nonempty (SLNatData (autSub E W) F) := by
  classical
  have hEst : E ≤ stabSub W := by
    rw [← hWE]
    exact Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub E)
  have hEq : CFSG.Open.IsQuasisimple ↥E :=
    isQuasisimple_of_mulEquiv' θ.symm (isQuasisimple_special_linear_two h4)
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
      apply eq_one_of_forall_smul_vec
      intro v
      obtain ⟨p, hp⟩ := hβs (Multiplicative.ofAdd v)
      have hpW : (e : MulAut V) p ∈ W := by rw [hecen p p.2]; exact p.2
      have hp' : (⟨e p, hpW⟩ : ↥W) = p := Subtype.ext (hecen p p.2)
      have := hβe ⟨e, heE⟩ p hpW
      rw [hp', hp] at this
      have h2 := congrArg Multiplicative.toAdd this
      have h3 : (θ ⟨e, heE⟩ : Matrix (Fin 2) (Fin 2) F).mulVec v = v := by
        simpa only [toAdd_ofAdd] using h2.symm
      exact h3
    have : (⟨e, heE⟩ : ↥E) = 1 := θ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  obtain ⟨φE, hφE⟩ := exists_mulEquiv_autSub hEst hEcen
  have htopW : (⊤ : Subgroup ↥W).map W.subtype = W := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact ⟨{ θ := φE.symm.trans θ
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
             rw [← commSub_eq_map_commV hEst, hcomm, htopW] }⟩

theorem card_le_autSub_mul_card_fixV {A : Subgroup (MulAut V)} {W : Subgroup V}
    (hAst : A ≤ stabSub W) (hAoff : IsOff A) :
    Nat.card ↥W ≤ Nat.card (autSub A W) * Nat.card (fixV (autSub A W)) := by
  have hcardA : Nat.card (autSub A W) = (cenIn A W).relIndex A := card_autSub_eq_relIndex hAst
  have hcardF : Nat.card (fixV (autSub A W)) = Nat.card ↥(fixV A ⊓ W) := by
    have h1 := map_subtype_fixV_autSub hAst
    have h2 : Nat.card ((fixV (autSub A W)).map W.subtype) = Nat.card (fixV (autSub A W)) :=
      Subgroup.card_map_of_injective W.subtype_injective
    rw [h1, inf_comm] at h2
    exact h2.symm
  have hcardW : (fixV A).relIndex W * Nat.card ↥(fixV A ⊓ W) = Nat.card ↥W :=
    Subgroup.relIndex_mul_card (fixV A) W
  have hoffW : (fixV A).relIndex W ≤ (cenIn A W).relIndex A := offender_card_le hAoff W
  rw [hcardA, hcardF, ← hcardW]
  exact Nat.mul_le_mul_right _ hoffW

omit [Finite V] in
theorem autSub_eq_bot_of_le_centSub {A : Subgroup (MulAut V)} {W : Subgroup V}
    (h : A ≤ centSub W) : autSub A W = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  obtain ⟨g, hgA, rfl⟩ := mem_autSub.mp hφ
  have : g ∈ (resHom W).ker := by
    rw [ker_resHom, Subgroup.mem_subgroupOf]
    exact h hgA
  rw [Subgroup.mem_bot]
  exact this

omit [Finite V] in
theorem autSub_ne_bot_of_not_le_centSub {A : Subgroup (MulAut V)} {W : Subgroup V}
    (hAst : A ≤ stabSub W) (h : ¬ A ≤ centSub W) : autSub A W ≠ ⊥ := fun hb => h (by
  intro a ha
  have hmem : resHom W ⟨a, hAst ha⟩ ∈ autSub A W := mem_autSub.mpr ⟨⟨a, hAst ha⟩, ha, rfl⟩
  rw [hb, Subgroup.mem_bot] at hmem
  have : (⟨a, hAst ha⟩ : stabSub W) ∈ (resHom W).ker := hmem
  rw [ker_resHom, Subgroup.mem_subgroupOf] at this
  exact this)

omit [Finite V] in
theorem autSub_iSup_le {S : Set (Subgroup (MulAut V))} {W : Subgroup V} {U₀ : Subgroup (MulAut ↥W)}
    (h : ∀ A ∈ S, A ≤ stabSub W ∧ autSub A W ≤ U₀) : autSub (⨆ A ∈ S, A) W ≤ U₀ := by
  let K : Subgroup (MulAut V) := (U₀.comap (resHom W)).map (stabSub W).subtype
  have hAK : ∀ A ∈ S, A ≤ K := by
    intro A hA x hx
    refine ⟨⟨x, (h A hA).1 hx⟩, ?_, rfl⟩
    exact (h A hA).2 (mem_autSub.mpr ⟨⟨x, (h A hA).1 hx⟩, hx, rfl⟩)
  have hJK : (⨆ A ∈ S, A : Subgroup (MulAut V)) ≤ K := iSup₂_le fun A hA => hAK A hA
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
  obtain ⟨g', hg'U, hg'⟩ := hJK hg
  have : g' = g := Subtype.ext hg'
  rw [← this]
  exact hg'U

omit [Finite V] in
theorem fixV_autSub_iff {X : Subgroup (MulAut V)} {W : Subgroup V} (hX : X ≤ stabSub W) (u : ↥W) :
    u ∈ fixV (autSub X W) ↔ (u : V) ∈ fixV X := by
  rw [mem_fixV_autSub]
  exact ⟨fun h g hg => h g hg (hX hg), fun h g hg _ => h g hg⟩

theorem sl_fix_baum {k : ℕ} (hk : 2 ≤ k) {E : Subgroup (MulAut V)}
    (hnat : IsSLNatSection E (commV E) (commV E ⊓ fixV E) k)
    {𝒜 : Set (Subgroup (MulAut V))} {X : Subgroup (MulAut V)} (hXdef : X = ⨆ A ∈ 𝒜, A)
    (hoff : ∀ A ∈ 𝒜, IsOff A) (hX2 : IsPGroup 2 ↥X)
    (hXN : X ≤ Subgroup.normalizer (E : Set (MulAut V)))
    (hne : ∃ A ∈ 𝒜, ¬ A ≤ centSub (commV E)) :
    (∃ w ∈ commV E, w ∉ fixV E ∧ w ∈ fixV X) ∧
    (∀ Q : Subgroup (MulAut V), IsPGroup 2 ↥Q → Q ≤ Subgroup.normalizer (E : Set (MulAut V)) →
      X ≤ Q → fixV X ≤ fixV Q → autSub Q (commV E) ≤ autSub X (commV E)) ∧
    autSub X (commV E) ≤ autSub E (commV E) := by
  classical
  have hXA : ∀ A ∈ 𝒜, A ≤ X := fun A hA => hXdef ▸ le_iSup₂ (f := fun A (_ : A ∈ 𝒜) => A) A hA
  obtain ⟨-, θ, β, hβs, hβk, hβe⟩ := hnat
  have hEst : E ≤ stabSub (commV E) :=
    Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub E)
  have hXst : X ≤ stabSub (commV E) := hXN.trans (normalizer_commV_le_stabSub E)
  obtain ⟨D⟩ := exists_slNatData_autSub (exists_finset_card_four_galoisField hk) rfl θ β hβs hβk
    hβe
  generalize commV E = W at *
  have hAst : ∀ A ∈ 𝒜, A ≤ stabSub W := fun A hA => (hXA A hA).trans hXst
  have hF : 2 ≤ Nat.card (GaloisField 2 k) := by
    rw [GaloisField.card 2 k (by omega)]
    exact Nat.le_self_pow (by omega) 2
  let 𝒜W : Set (Subgroup (MulAut ↥W)) :=
    {B | ∃ A ∈ 𝒜, ¬ A ≤ centSub W ∧ B = autSub A W}
  have hne' : 𝒜W.Nonempty := by
    obtain ⟨A, hA, hAc⟩ := hne
    exact ⟨autSub A W, A, hA, hAc, rfl⟩
  have h𝒜W : ∀ B ∈ 𝒜W, B ≤ autSub X W ∧ IsElemAbelian2 B ∧ B ≠ ⊥ ∧
      Nat.card ↥W ≤ Nat.card ↥B * Nat.card ↥(fixV B) := by
    rintro B ⟨A, hA, hAc, rfl⟩
    have h1 : autSub A W ≤ autSub X W := autSub_mono (hXA A hA) W
    have h2 : IsElemAbelian2 (autSub A W) := isElemAbelian2_autSub (hoff A hA).2.2.1
    have h3 : autSub A W ≠ ⊥ := autSub_ne_bot_of_not_le_centSub (hAst A hA) hAc
    have h4 := card_le_autSub_mul_card_fixV (hAst A hA) (hoff A hA)
    exact ⟨h1, h2, h3, h4⟩
  have hQ : IsPGroup 2 ↥(autSub X W) := isPGroup_autSub hX2
  have hQN : autSub X W ≤ Subgroup.normalizer (autSub E W : Set (MulAut ↥W)) :=
    autSub_le_normalizer hXN
  obtain ⟨U₀, hU₀E, hU₀card, hUeq, hnfix, hfixed⟩ := sl_family D hF hQ hQN hne' h𝒜W
  have hJU : autSub X W = U₀ := by
    refine le_antisymm ?_ ?_
    · rw [hXdef]
      refine autSub_iSup_le fun A hA => ⟨hAst A hA, ?_⟩
      by_cases hAc : A ≤ centSub W
      · rw [autSub_eq_bot_of_le_centSub hAc]
        exact bot_le
      · exact (hUeq _ ⟨A, hA, hAc, rfl⟩).le
    · obtain ⟨A, hA, hAc⟩ := hne
      rw [← hUeq _ ⟨A, hA, hAc, rfl⟩]
      exact autSub_mono (hXA A hA) W
  refine ⟨?_, fun Q hQ2 hQNE hXQ hfix => ?_, hJU.le.trans hU₀E⟩
  · obtain ⟨w, hwU, hwE⟩ := IsConcreteLE.not_le_iff_exists.mp hnfix
    refine ⟨(w : V), w.2, fun h => hwE ?_, ?_⟩
    · exact (fixV_autSub_iff hEst w).mpr h
    · rw [← hJU] at hwU
      exact (fixV_autSub_iff hXst w).mp hwU
  · have hQ2' : IsPGroup 2 ↥(autSub Q W) := isPGroup_autSub hQ2
    have hQN' : autSub Q W ≤ Subgroup.normalizer (autSub E W : Set (MulAut ↥W)) :=
      autSub_le_normalizer hQNE
    have hfix' : fixV U₀ ≤ fixV (autSub Q W) := by
      intro u hu
      rw [← hJU] at hu
      have h1 := (fixV_autSub_iff hXst u).mp hu
      rw [mem_fixV_autSub]
      intro g hg _
      exact (mem_fixV.mp (hfix h1)) g hg
    obtain ⟨-, hQcard⟩ := hfixed _ hQ2' hQN' hfix'
    have hle : U₀ ≤ autSub Q W := hJU ▸ autSub_mono hXQ W
    have hEq : U₀ = autSub Q W :=
      Subgroup.eq_of_le_of_card_ge hle (hQcard.trans hU₀card.symm.le)
    rw [hJU, hEq]

omit [Finite V] in
theorem exists_altNatData_autSub {n : ℕ} (h5 : 5 ≤ n) {E : Subgroup (MulAut V)}
    {W : Subgroup V} (hWE : commV E = W) (θ : E ≃* alternatingGroup (Fin n))
    (β : ↥W →* coreMod n) (hβs : Function.Surjective β)
    (hβk : β.ker = (W ⊓ fixV E).subgroupOf W)
    (hβe : ∀ (x : E) (p : ↥W) (hp : (x : MulAut V) p ∈ W),
      β ⟨(x : MulAut V) p, hp⟩ =
        coreAct n ((θ x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) (β p)) :
    Nonempty (AltNatData (autSub E W) n) := by
  classical
  have h3 : 3 ≤ n := by omega
  have hEst : E ≤ stabSub W := by
    rw [← hWE]
    exact Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub E)
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
  exact ⟨{ θ := φE.symm.trans θ
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
             rw [← commSub_eq_map_commV hEst, hcomm, htopW] }⟩

omit [Finite V] in
theorem altOf_eq_commutator {E : Subgroup (MulAut V)} {m : ℕ} (h5 : 5 ≤ m)
    (θ : ↥E ≃* Equiv.Perm (Fin m)) : altOf θ = ⁅E, E⁆ := by
  have hcomm : ⁅(⊤ : Subgroup ↥E), ⊤⁆ = (alternatingGroup (Fin m)).comap θ.toMonoidHom := by
    have h1 : (⁅(⊤ : Subgroup ↥E), ⊤⁆ : Subgroup ↥E).map θ.toMonoidHom =
        ⁅(⊤ : Subgroup (Equiv.Perm (Fin m))), ⊤⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr θ.surjective]
    have h2 : ⁅(⊤ : Subgroup (Equiv.Perm (Fin m))), ⊤⁆ = alternatingGroup (Fin m) := by
      have := alternatingGroup.commutator_perm_eq (α := Fin m) (by simpa using h5)
      exact this
    rw [h2] at h1
    rw [← h1, Subgroup.comap_map_eq_self_of_injective θ.injective]
  have htop : (⊤ : Subgroup ↥E).map E.subtype = E := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥E)) (H₂ := ⊤) E.subtype
  rw [htop] at h
  rw [← h, hcomm]
  rfl

omit [Finite V] in
theorem normalizer_le_normalizer_altOf {E : Subgroup (MulAut V)} {m : ℕ} (h5 : 5 ≤ m)
    (θ : ↥E ≃* Equiv.Perm (Fin m)) :
    Subgroup.normalizer (E : Set (MulAut V)) ≤ Subgroup.normalizer ((altOf θ : Subgroup _) :
      Set (MulAut V)) := by
  intro g hg
  rw [altOf_eq_commutator h5 θ, Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ g ∈ Subgroup.normalizer (E : Set (MulAut V)), ∀ x ∈ (⁅E, E⁆ : Subgroup _),
      g * x * g⁻¹ ∈ (⁅E, E⁆ : Subgroup _) := by
    intro g hg x hx
    have h1 : ((⁅E, E⁆ : Subgroup (MulAut V))).map (MulAut.conj g).toMonoidHom =
        ⁅E.map (MulAut.conj g).toMonoidHom, E.map (MulAut.conj g).toMonoidHom⁆ :=
      Subgroup.map_commutator _ _ _
    have h2 : E.map (MulAut.conj g).toMonoidHom = E := by
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hg z).mp hz
      · intro hy
        refine ⟨g⁻¹ * y * g, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg) y).mp hy
        simpa using this
    rw [h2] at h1
    have : g * x * g⁻¹ ∈ ((⁅E, E⁆ : Subgroup (MulAut V))).map (MulAut.conj g).toMonoidHom :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [h1] at this
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer _).inv_mem hg) _ hx
  simpa [mul_assoc] using this

omit [Finite V] in
theorem exists_ne_one_mem_fixV {X : Subgroup (MulAut V)} (hX : IsPGroup 2 ↥X) {W : Subgroup V}
    (hW2 : IsPGroup 2 ↥W) (hW : W ≠ ⊥) (hXst : X ≤ stabSub W) [Finite V] :
    ∃ w ∈ W, w ≠ 1 ∧ w ∈ fixV X := by
  classical
  let act : ↥X →* MulAut ↥W := (resHom W).comp (Subgroup.inclusion hXst)
  let _inst : MulAction ↥X ↥W := MulAction.compHom ↥W act
  have hsm : ∀ (x : ↥X) (w : ↥W), ((x • w : ↥W) : V) = (x : MulAut V) (w : V) := fun x w => rfl
  have hmod := hX.card_modEq_card_fixedPoints ↥W
  have h2 : 2 ∣ Nat.card ↥W := by
    have : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW
    obtain ⟨n, hn, hcard⟩ := (hW2.nontrivial_iff_card).mp inferInstance
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  have h3 : 2 ∣ Nat.card (MulAction.fixedPoints ↥X ↥W) := by
    have := (Nat.modEq_zero_iff_dvd).mpr h2
    exact (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans this)
  have h1mem : (1 : ↥W) ∈ MulAction.fixedPoints ↥X ↥W := fun x => by
    show x • (1 : ↥W) = 1
    exact Subtype.ext (map_one (x : MulAut V))
  have : Nonempty ↑(MulAction.fixedPoints ↥X ↥W) := ⟨⟨1, h1mem⟩⟩
  have hgt : 1 < Nat.card (MulAction.fixedPoints ↥X ↥W) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥X ↥W) := Nat.card_pos
    have := Nat.le_of_dvd hpos h3
    omega
  have hnt : Nontrivial ↑(MulAction.fixedPoints ↥X ↥W) := Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨⟨w, hw⟩, hwne⟩ := exists_ne (⟨1, h1mem⟩ : ↑(MulAction.fixedPoints ↥X ↥W))
  refine ⟨(w : V), w.2, ?_, fun x hx => ?_⟩
  · intro h
    apply hwne
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  · have := congrArg (fun y : ↥W => (y : V)) (hw ⟨x, hx⟩)
    exact this

omit [Finite V] in
theorem commV_ne_bot_of_symDat [Finite V] {E : Subgroup (MulAut V)} {m : ℕ} (D : SymDat E m) :
    commV E ≠ ⊥ := by
  intro hbot
  have h1 := Nat.card_le_card_of_surjective D.β D.surj
  have h2 : Nat.card ↥(commV E) = 1 := by rw [hbot]; exact Subgroup.card_bot
  have h3 := card_coreMod_mul_two D.odd
  have h4 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) D.three_le
  omega

theorem sym_fix (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} {E : Subgroup (MulAut V)} (D : SymDat E m)
    {X : Subgroup (MulAut V)} (hX2 : IsPGroup 2 ↥X)
    (hXN : X ≤ Subgroup.normalizer (E : Set (MulAut V))) :
    ∃ w ∈ commV E, w ∉ fixV E ∧ w ∈ fixV X := by
  have hXst : X ≤ stabSub (commV E) := hXN.trans (normalizer_commV_le_stabSub E)
  have hW2 : IsPGroup 2 ↥(commV E) :=
    isPGroup_two_of_sq_eq_one (fun w => Subtype.ext (by simpa [sq] using hV w))
  obtain ⟨w, hw, hw1, hwX⟩ := exists_ne_one_mem_fixV hX2 hW2 (commV_ne_bot_of_symDat D) hXst
  refine ⟨w, hw, fun hwE => hw1 ?_, hwX⟩
  have h1 : w ∈ commV (altOf D.θ) ⊓ fixV (altOf D.θ) :=
    ⟨D.commV_altOf ▸ hw, fun x hx => hwE x (altOf_le D.θ hx)⟩
  rw [D.commV_inf_fixV_altOf, Subgroup.mem_bot] at h1
  exact h1

theorem three_baum (hV : ∀ v : V, v ^ 2 = 1) {E : Subgroup (MulAut V)} (D : SymDat E 3)
    {X Q : Subgroup (MulAut V)} (hX2 : IsPGroup 2 ↥X) (hQ2 : IsPGroup 2 ↥Q) (hXQ : X ≤ Q)
    (hXst : X ≤ stabSub (commV E)) (hX : ¬ X ≤ centSub (commV E)) :
    autSub Q (commV E) ≤ autSub X (commV E) := by
  classical
  have hW' : ∀ w : ↥(commV E), w ^ 2 = 1 := fun w => Subtype.ext (by simpa [sq] using hV w)
  have hcard : Nat.card ↥(commV E) = 4 := by
    rw [Nat.card_congr (Equiv.ofBijective D.β ⟨D.injective_β, D.surj⟩)]
    exact card_coreMod_three'
  have hrk : rk ↥(commV E) = 2 := by
    have h := card_eq_two_pow_rk hW'
    rw [hcard] at h
    have h2 : (2 : ℕ) ^ rk ↥(commV E) = 2 ^ 2 := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective le_rfl h2
  have hautcard : Nat.card (MulAut ↥(commV E)) = 6 := by
    rw [card_mulAut_eq hW', hrk]
    simp [Fin.prod_univ_two]
  have hle2 : ∀ P : Subgroup (MulAut ↥(commV E)), IsPGroup 2 ↥P → Nat.card ↥P ≤ 2 := by
    intro P hP
    have hdvd : Nat.card ↥P ∣ 6 := hautcard ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨a, ha⟩ := hP.exists_card_eq
    rw [ha] at hdvd ⊢
    by_contra hlt
    have ha2 : 2 ≤ a := by
      by_contra h
      have : a ≤ 1 := by omega
      have : 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      omega
    have h4 : 2 ^ 2 ∣ 2 ^ a := pow_dvd_pow 2 ha2
    have := dvd_trans h4 hdvd
    omega
  have hXne : autSub X (commV E) ≠ ⊥ := autSub_ne_bot_of_not_le_centSub hXst hX
  have hXcard : 1 < Nat.card ↥(autSub X (commV E)) :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hXne)
  have hX2' : IsPGroup 2 ↥(autSub X (commV E)) := isPGroup_autSub hX2
  have hQ2' : IsPGroup 2 ↥(autSub Q (commV E)) := isPGroup_autSub hQ2
  have hXQ' : autSub X (commV E) ≤ autSub Q (commV E) := autSub_mono hXQ _
  have hXle := hle2 _ hX2'
  have hQle := hle2 _ hQ2'
  have heq : autSub X (commV E) = autSub Q (commV E) :=
    Subgroup.eq_of_le_of_card_ge hXQ' (by omega)
  exact heq.ge

theorem alt_baum (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (h5 : 5 ≤ m) {E : Subgroup (MulAut V)}
    (D : SymDat E m) {𝒜 : Set (Subgroup (MulAut V))} {X : Subgroup (MulAut V)}
    (hXdef : X = ⨆ A ∈ 𝒜, A) (hoff : ∀ A ∈ 𝒜, IsOff A) (hX2 : IsPGroup 2 ↥X)
    (hXN : X ≤ Subgroup.normalizer (E : Set (MulAut V)))
    (hne : ∃ A ∈ 𝒜, ¬ A ≤ centSub (commV E)) :
    ∀ Q : Subgroup (MulAut V), IsPGroup 2 ↥Q → Q ≤ Subgroup.normalizer (E : Set (MulAut V)) →
      fixV X ≤ fixV Q → autSub Q (commV E) ≤ autSub X (commV E) := by
  classical
  intro Q hQ2 hQNE hfix
  have hXA : ∀ A ∈ 𝒜, A ≤ X := fun A hA => hXdef ▸ le_iSup₂ (f := fun A (_ : A ∈ 𝒜) => A) A hA
  have hE'N : Subgroup.normalizer (E : Set (MulAut V)) ≤
      Subgroup.normalizer ((altOf D.θ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    normalizer_le_normalizer_altOf h5 D.θ
  obtain ⟨-, θ', β', hβs, hβk, hβe⟩ := D.isAltNatSection_altOf
  obtain ⟨D'⟩ := exists_altNatData_autSub h5 rfl θ' β' hβs hβk hβe
  rw [← D.commV_altOf] at hne ⊢
  have hXst : X ≤ stabSub (commV (altOf D.θ)) := (hXN.trans hE'N).trans
    (normalizer_commV_le_stabSub (altOf D.θ))
  generalize commV (altOf D.θ) = W at *
  have hAst : ∀ A ∈ 𝒜, A ≤ stabSub W := fun A hA => (hXA A hA).trans hXst
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa [sq] using hV w)
  let 𝒜W : Set (Subgroup (MulAut ↥W)) :=
    {B | ∃ A ∈ 𝒜, ¬ A ≤ centSub W ∧ B = autSub A W}
  have hne' : 𝒜W.Nonempty := by
    obtain ⟨A, hA, hAc⟩ := hne
    exact ⟨autSub A W, A, hA, hAc, rfl⟩
  have h𝒜W : ∀ B ∈ 𝒜W, B ≤ autSub X W ∧ IsElemAbelian2 B ∧ B ≠ ⊥ ∧
      Nat.card ↥W ≤ Nat.card ↥B * Nat.card ↥(fixV B) := by
    rintro B ⟨A, hA, hAc, rfl⟩
    have h1 : autSub A W ≤ autSub X W := autSub_mono (hXA A hA) W
    have h2 : IsElemAbelian2 (autSub A W) := isElemAbelian2_autSub (hoff A hA).2.2.1
    have h3 : autSub A W ≠ ⊥ := autSub_ne_bot_of_not_le_centSub (hAst A hA) hAc
    have h4 := card_le_autSub_mul_card_fixV (hAst A hA) (hoff A hA)
    exact ⟨h1, h2, h3, h4⟩
  have hQ : IsPGroup 2 ↥(autSub X W) := isPGroup_autSub hX2
  have hQN : autSub X W ≤ Subgroup.normalizer (autSub (altOf D.θ) W : Set (MulAut ↥W)) :=
    autSub_le_normalizer (hXN.trans hE'N)
  obtain ⟨-, -, -, -, -, hfixed⟩ := alt_family hW2 D.odd h5 D' hQ hQN hne' h𝒜W
  have hJU : autSub X W = ⨆ B ∈ 𝒜W, B := by
    refine le_antisymm ?_ (iSup₂_le fun B hB => ?_)
    · rw [hXdef]
      refine autSub_iSup_le fun A hA => ⟨hAst A hA, ?_⟩
      by_cases hAc : A ≤ centSub W
      · rw [autSub_eq_bot_of_le_centSub hAc]
        exact bot_le
      · exact le_iSup₂_of_le (autSub A W) ⟨A, hA, hAc, rfl⟩ le_rfl
    · obtain ⟨A, hA, -, rfl⟩ := hB
      exact autSub_mono (hXA A hA) W
  have hQ2' : IsPGroup 2 ↥(autSub Q W) := isPGroup_autSub hQ2
  have hQN' : autSub Q W ≤ Subgroup.normalizer (autSub (altOf D.θ) W : Set (MulAut ↥W)) :=
    autSub_le_normalizer (hQNE.trans hE'N)
  have hfix' : fixV (⨆ B ∈ 𝒜W, B) ≤ fixV (autSub Q W) := by
    intro u hu
    rw [← hJU] at hu
    have h1 := (fixV_autSub_iff hXst u).mp hu
    rw [mem_fixV_autSub]
    intro g hg _
    exact (mem_fixV.mp (hfix h1)) g hg
  rw [hJU]
  exact hfixed _ hQ2' hQN' hfix'

end CFSG.CGT.PushingUpLit.BHS7
