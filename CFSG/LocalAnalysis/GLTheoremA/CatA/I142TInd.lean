module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TTransfer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142MClose
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I142N
open scoped commutatorElement

theorem typesA_orbit_of_stab {S : Type} [Group S] [Finite S] (E : Subgroup (MulAut S))
    {X : Subgroup S} (hXE : ∀ a : ↥E, X.map (E.subtype a).toMonoidHom = X)
    {K₀ : Subgroup S} (hK₀ : IsComponentOf K₀ X)
    (hq : ∀ (B : Subgroup ↥E)
      (hinv : ∀ a : ↥B, K₀.map ((E.subtype.comp B.subtype) a).toMonoidHom = K₀),
      (∀ a : ↥E, K₀.map (E.subtype a).toMonoidHom = K₀ → a ∈ B) →
        TypesA (quotAct (E.subtype.comp B.subtype) K₀ hinv) ⊤) :
    TypesA E.subtype (sSup (orbitOf E.subtype K₀)) := by
  classical
  haveI : Finite (Subgroup S) := Finite.of_injective (fun H : Subgroup S => (H : Set S))
    (fun H K h => SetLike.coe_injective h)
  haveI : Fintype ↥(orbitOf E.subtype K₀) := Fintype.ofFinite _
  set ρ : ↥E →* MulAut S := E.subtype with hρ
  set O := orbitOf ρ K₀ with hOdef
  have hcomp : ∀ K ∈ O, IsComponentOf K X :=
    fun K hK => isComponentOf_orbit (ρ := ρ) hXE hK₀ hK
  have hO : ∀ K ∈ O, ∀ a : ↥E, K.map (ρ a).toMonoidHom ∈ O := fun K hK a => orbitOf_map_mem ρ hK a
  set σ := orbitAct ρ O hO with hσ
  set i₀ : ↥O := ⟨K₀, mem_orbitOf_self ρ K₀⟩ with hi₀
  have hcomm' : ∀ i j : ↥O, i ≠ j → ∀ x ∈ i.1, ∀ y ∈ j.1, Commute x y := by
    intro i j hij x hx y hy
    rcases isComponent_commute_or_eq (hcomp i.1 i.2) (hcomp j.1 j.2) with h | h
    · exact absurd (Subtype.ext h) hij
    · have hxy : ⁅x, y⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator hx hy
        rw [h, Subgroup.mem_bot] at this
        exact this
      exact commutatorElement_eq_one_iff_mul_comm.1 hxy
  have hmap : ∀ (a : ↥E) (K : ↥O), K.1.map (ρ a).toMonoidHom = (σ a K).1 := fun a K => rfl
  have htrans : ∀ K' : ↥O, ∃ a : ↥E, σ a i₀ = K' := by
    intro K'
    obtain ⟨a, ha⟩ := K'.2
    exact ⟨a, Subtype.ext ha⟩
  have hinv₀ : ∀ a : ↥(stabSub σ i₀),
      K₀.map ((ρ.comp (stabSub σ i₀).subtype) a).toMonoidHom = K₀ := by
    intro a
    have ha : σ (a : ↥E) i₀ = i₀ := (mem_stabSub σ i₀ _).1 a.2
    have h1 := congrArg Subtype.val ha
    exact h1
  have hB : ∀ a : ↥E, K₀.map (E.subtype a).toMonoidHom = K₀ → a ∈ stabSub σ i₀ := by
    intro a ha
    rw [mem_stabSub]
    apply Subtype.ext
    show (σ a i₀).1 = K₀
    rw [← hmap a i₀]
    exact ha
  have hT : TypesA (quotAct (ρ.comp (stabSub σ i₀).subtype) K₀ hinv₀) ⊤ :=
    hq (stabSub σ i₀) hinv₀ hB
  have htypes0 : TypesA ρ (⨆ K : ↥O, K.1) :=
    typesA_iSup_transitive ρ (fun K : ↥O => K.1) hcomm' σ hmap i₀ htrans
      (typesA_of_component (ρ.comp (stabSub σ i₀).subtype) K₀ hinv₀ (fun Kb hKb =>
        hT Kb (by rwa [inf_top_eq])))
  rw [sSup_eq_iSup']
  exact htypes0

theorem typesA_glaLayer_of_orbits {S : Type} [Group S] [Finite S] (E : Subgroup (MulAut S))
    {X : Subgroup S} (hXE : ∀ a : ↥E, X.map (E.subtype a).toMonoidHom = X)
    (horb : ∀ K₀ : Subgroup S, IsComponentOf K₀ X →
      TypesA E.subtype (sSup (orbitOf E.subtype K₀))) :
    TypesA E.subtype (GLALayer X) := by
  classical
  haveI : Finite (Subgroup S) := Finite.of_injective (fun H : Subgroup S => (H : Set S))
    (fun H K h => SetLike.coe_injective h)
  let ι := {O : Set (Subgroup S) // ∃ K, IsComponentOf K X ∧ O = orbitOf E.subtype K}
  haveI : Finite ι := Subtype.finite
  haveI : Fintype ι := Fintype.ofFinite ι
  have hmemO : ∀ O : ι, ∀ K ∈ O.1, IsComponentOf K X := by
    rintro ⟨O, K₁, hK₁, rfl⟩ K hK
    exact isComponentOf_orbit hXE hK₁ hK
  have hOinv : ∀ O : ι, ∀ K ∈ O.1, ∀ a : ↥E, K.map (E.subtype a).toMonoidHom ∈ O.1 := by
    rintro ⟨O, K₁, hK₁, rfl⟩ K hK a
    exact orbitOf_map_mem _ hK a
  let H : ι → Subgroup S := fun O => sSup O.1
  have hcomm : ∀ i j : ι, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y := by
    intro i j hij x hx y hy
    have hdisj : ∀ K ∈ i.1, ∀ K' ∈ j.1, K ≠ K' := by
      intro K hK' K' hK'' hKK
      subst hKK
      obtain ⟨K₁, _, hi⟩ := i.2
      obtain ⟨K₂, _, hj⟩ := j.2
      apply hij
      apply Subtype.ext
      rw [hi, hj]
      rw [hi] at hK'
      rw [hj] at hK''
      exact orbitOf_eq_of_common E.subtype hK' hK''
    have hc := commutator_sSup_eq_bot (fun K hK => hmemO i K hK) (fun K hK => hmemO j K hK) hdisj
    have hxy : ⁅x, y⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hx hy
      rw [hc, Subgroup.mem_bot] at this
      exact this
    exact commutatorElement_eq_one_iff_mul_comm.1 hxy
  have hinv : ∀ (a : ↥E) (i : ι), (H i).map (E.subtype a).toMonoidHom = H i := by
    intro a i
    exact sSup_orbit_map E.subtype i.1 (fun K hK b => hOinv i K hK b) a
  have hfac : ∀ i : ι, TypesA E.subtype (H i) := by
    intro i
    obtain ⟨K₁, hK₁, hi⟩ := i.2
    have := horb K₁ hK₁
    rw [← hi] at this
    exact this
  have hG := typesA_iSup_coord E.subtype H hcomm hinv hfac
  have hL : GLALayer X = ⨆ i : ι, H i := by
    refine layer_eq_iSup_orbits E.subtype hXE (fun i : ι => i.1) ?_ ?_
    · intro K hK
      exact ⟨⟨orbitOf E.subtype K, K, hK, rfl⟩, mem_orbitOf_self _ K⟩
    · intro i K hK
      exact hmemO i K hK
  rw [hL]
  exact hG

theorem types_orbit {S : Type} [Group S] [Finite S] {p : ℕ} (E : Subgroup (MulAut S))
    (hE : IsElemAbelian p E) {z : MulAut S} (hzE : z ∈ E) (hz1 : z ≠ 1)
    {X : Subgroup S} (hX : X = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z)
    {n : ℕ} (hcard : Nat.card E ≤ n)
    (ih : ∀ m < n, ∀ (S' : Type) [Group S'] [Finite S'], CPlus S' →
      ∀ E' : Subgroup (MulAut S'), IsElemAbelian p E' → Nat.card E' ≤ m →
      ∀ K, IsComponentOf K (I142.centFix E') → CPlus (↥K ⧸ Subgroup.center ↥K))
    (hK : ∀ K : Subgroup S, IsComponentOf K X → CPlus (↥K ⧸ Subgroup.center ↥K))
    {K₀ : Subgroup S} (hK₀ : IsComponentOf K₀ X) :
    TypesA E.subtype (sSup (orbitOf E.subtype K₀)) := by
  classical
  have hcE : ∀ a b : ↥E, a * b = b * a := fun a b => (hE.1.is_comm).comm a b
  have hXE : ∀ a : ↥E, X.map (E.subtype a).toMonoidHom = X := by
    intro a
    rw [hX]
    refine fixSubgroup_map_of_comm ?_
    have := congrArg Subtype.val (hcE a ⟨z, hzE⟩)
    exact this
  have hzX : ∀ x ∈ X, z x = x := by
    intro x hx
    rw [hX] at hx
    exact hx
  have hzK : ∀ y ∈ K₀, z y = y := fun y hy => hzX y (hK₀.1 hy)
  have hz_fix : K₀.map z.toMonoidHom = K₀ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := hzK y hy
      show z y ∈ K₀
      rw [this]
      exact hy
    · intro hx
      exact Subgroup.mem_map.2 ⟨x, hx, hzK x hx⟩
  refine typesA_orbit_of_stab E hXE hK₀ ?_
  intro B hinv hB
  set ρ₀ := E.subtype.comp B.subtype with hρ₀
  set σ' := quotAct ρ₀ K₀ hinv with hσ'
  have hzB : (⟨z, hzE⟩ : ↥E) ∈ B := hB ⟨z, hzE⟩ hz_fix
  set zA : ↥B := ⟨⟨z, hzE⟩, hzB⟩ with hzA
  have hzA_ne : zA ≠ 1 := by
    intro h
    apply hz1
    have := congrArg (fun u : ↥B => ((u : ↥E) : MulAut S)) h
    exact this
  have hzk : σ' zA = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    show quotAct ρ₀ K₀ hinv zA (QuotientGroup.mk' (Subgroup.center ↥K₀) x) =
      (1 : MulAut (↥K₀ ⧸ Subgroup.center ↥K₀)) (QuotientGroup.mk' (Subgroup.center ↥K₀) x)
    rw [← quotAct_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [restrictAct_apply]
    exact hzK x x.2
  have hc : ∀ a b : ↥B, a * b = b * a := fun a b => Subtype.ext (hcE a.1 b.1)
  have he : ∀ a : ↥B, a ^ p = 1 := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    exact hE.2 (a.1 : MulAut S) (a.1).2
  have hEab : IsElemAbelian p σ'.range := isElemAbelian_range p σ' hc he
  have hCP : CPlus (↥K₀ ⧸ Subgroup.center ↥K₀) := hK K₀ hK₀
  have hlt : Nat.card σ'.range < n := by
    have h1 := card_range_lt σ' hzA_ne hzk
    have h2 : Nat.card ↥B ≤ Nat.card E := Subgroup.card_le_card_group _
    omega
  have hIH := ih (Nat.card σ'.range) hlt (↥K₀ ⧸ Subgroup.center ↥K₀) hCP σ'.range hEab le_rfl
  intro Kb hKb
  rw [inf_top_eq] at hKb
  rw [fixA_eq_range, fixA_subtype_eq_centFix] at hKb
  exact hIH Kb hKb

theorem types_layer {S : Type} [Group S] [Finite S] {p : ℕ} (E : Subgroup (MulAut S))
    (hE : IsElemAbelian p E) {z : MulAut S} (hzE : z ∈ E) (hz1 : z ≠ 1)
    {X : Subgroup S} (hX : X = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z)
    {n : ℕ} (hcard : Nat.card E ≤ n)
    (ih : ∀ m < n, ∀ (S' : Type) [Group S'] [Finite S'], CPlus S' →
      ∀ E' : Subgroup (MulAut S'), IsElemAbelian p E' → Nat.card E' ≤ m →
      ∀ K, IsComponentOf K (I142.centFix E') → CPlus (↥K ⧸ Subgroup.center ↥K))
    (hK : ∀ K : Subgroup S, IsComponentOf K X → CPlus (↥K ⧸ Subgroup.center ↥K)) :
    TypesA E.subtype (GLALayer X) := by
  classical
  have hcE : ∀ a b : ↥E, a * b = b * a := fun a b => (hE.1.is_comm).comm a b
  have hXE : ∀ a : ↥E, X.map (E.subtype a).toMonoidHom = X := by
    intro a
    rw [hX]
    refine fixSubgroup_map_of_comm ?_
    have := congrArg Subtype.val (hcE a ⟨z, hzE⟩)
    exact this
  exact typesA_glaLayer_of_orbits E hXE (fun K₀ hK₀ =>
    types_orbit E hE hzE hz1 hX hcard ih hK hK₀)

section Cert


theorem types_step {S : Type} [Group S] [Finite S] (hK : CompTypesCyc) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {n : ℕ}
    (ih : ∀ m < n, ∀ (S' : Type) [Group S'] [Finite S'], CPlus S' →
      ∀ E' : Subgroup (MulAut S'), IsElemAbelian p E' → Nat.card E' ≤ m →
      ∀ K, IsComponentOf K (I142.centFix E') → CPlus (↥K ⧸ Subgroup.center ↥K))
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (hchev : IsChevSimple 2 S)
    (E : Subgroup (MulAut S)) (hE : IsElemAbelian p E) (hcard : Nat.card E ≤ n)
    {z : MulAut S} (hzE : z ∈ E) (hz1 : z ≠ 1) :
    ∀ K : Subgroup S, IsComponentOf K (I142.centFix E) → CPlus (↥K ⧸ Subgroup.center ↥K) := by
  have hzp : z ^ p = 1 := hE.2 z hzE
  have hXfix : I142.centFix (Subgroup.zpowers z) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z := I142.centFix_zpowers z
  have hKc : ∀ K : Subgroup S, IsComponentOf K (I142.centFix (Subgroup.zpowers z)) →
      CPlus (↥K ⧸ Subgroup.center ↥K) := fun K hK' => hK S hS hnc hchev p hp hp2 z hzp K hK'
  have hGL := types_layer E hE hzE hz1 hXfix hcard ih hKc
  intro K hK
  have hzfix : ∀ x ∈ I142.centFix E, z x = x := fun x hx => I142.mem_centFix.1 hx z hzE
  have hKz : K ≤ I142.centFix (Subgroup.zpowers z) := by
    intro x hx
    rw [hXfix]
    exact hzfix x (hK.1 hx)
  have hKL : K ≤ GLALayer (I142.centFix (Subgroup.zpowers z)) :=
    cyclic_good hS hnc hchev hp hp2 z hzp K hKz
      (comm_self_eq_of_commutator_top hK.2.2.1)
  have hKfix : IsComponentOf K (fixA E.subtype) := by
    rw [fixA_subtype_eq_centFix]
    exact hK
  have hKle : K ≤ fixA E.subtype ⊓ GLALayer (I142.centFix (Subgroup.zpowers z)) := by
    rw [fixA_subtype_eq_centFix]
    exact le_inf hK.1 hKL
  exact hGL K (isComponentOf_of_le hKfix hKle inf_le_left)

theorem typesA_all (hCyc : CompTypesCyc) (hT : TitsCentSolv) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ∀ n : ℕ, ∀ (S : Type) [Group S] [Finite S], CPlus S → ∀ E : Subgroup (MulAut S),
      IsElemAbelian p E → Nat.card E ≤ n → ∀ K : Subgroup S, IsComponentOf K (I142.centFix E) →
        CPlus (↥K ⧸ Subgroup.center ↥K) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hS E hE hcard K hK
  obtain ⟨hsimp, hnc, hcl⟩ := hS
  by_cases hTits : catalogIs S (onLie (· = TauCeti.LieTypeIndex.tits))
  · by_cases hbot : E = ⊥
    · subst hbot
      rw [I142.centFix_bot] at hK
      haveI : IsSimpleGroup S := hsimp
      haveI : IsSimpleGroup ↥(⊤ : Subgroup S) := Subgroup.topEquiv.isSimpleGroup
      have hKne : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1
        (nontrivial_of_isQuasisimple hK.2.2)
      have hKtop : K = ⊤ :=
        CFSG.LocalAnalysis.GLTheoremA.AltDown.eq_of_isSubnormal_of_isSimpleGroup hK.2.1 hKne
      have eK : ↥K ≃* S := (MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv
      haveI : IsSimpleGroup ↥K := eK.isSimpleGroup
      have hncK : ∃ a b : ↥K, a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hnc
        exact ⟨eK.symm a, eK.symm b, fun h => hab (eK.symm.injective (by simpa using h))⟩
      have hZ : Subgroup.center ↥K = ⊥ :=
        CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hncK
      have e : (↥K ⧸ Subgroup.center ↥K) ≃* S :=
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eK
      exact cplus_of_mulEquiv e ⟨hsimp, hnc, hcl⟩
    · haveI := hT S hTits p hp hp2 E hE hbot
      have hKb : K = ⊥ := eq_bot_of_le_solvable (C := I142.centFix E) hK.1
        (comm_self_eq_of_commutator_top hK.2.2.1)
      exact absurd hKb ((Subgroup.nontrivial_iff_ne_bot K).1
        (nontrivial_of_isQuasisimple hK.2.2))
  · have hchev : IsChevSimple 2 S := hcl.resolve_right hTits
    by_cases hcyc : ∃ β : MulAut S, E = Subgroup.zpowers β
    · obtain ⟨β, rfl⟩ := hcyc
      exact hCyc S hsimp hnc hchev p hp hp2 β (hE.2 β (Subgroup.mem_zpowers β)) K hK
    · have hz : ∃ z ∈ E, z ≠ 1 := by
        by_contra h
        apply hcyc
        refine ⟨1, ?_⟩
        rw [Subgroup.zpowers_one_eq_bot]
        exact eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (by
          by_contra hx1
          exact h ⟨x, hx, hx1⟩)
      obtain ⟨z, hzE, hz1⟩ := hz
      exact types_step hCyc hp hp2 ih hsimp hnc hchev E hE hcard hzE hz1 K hK

theorem compTypesElem_holds : CompTypesElem := by
  intro S _ _ hS hnc hchev p hp hp2 E hE K hK
  exact isChevSimple_of_cplus (typesA_all I142M.compTypesCyc_holds I142M.titsCentSolv_holds
    p hp hp2
    (Nat.card E) S ⟨hS, hnc, Or.inl hchev⟩ E hE le_rfl K hK)

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I142T
