module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NStep
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NChain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NOrbit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142N

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

theorem eq_bot_of_le_solvable {S : Type} [Group S] {C P : Subgroup S} [Group.IsSolvable ↥C]
    (hPC : P ≤ C) (hPp : ⁅P, P⁆ = P) : P = ⊥ := by
  haveI : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPC)
  by_contra hne
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hne
  haveI : Group.IsPerfect ↥P := ⟨commutator_top_of_comm_self_eq hPp⟩
  exact (Group.IsPerfect.not_isSolvable (G := ↥P)) inferInstance

theorem fixSubgroup_map_conj {S : Type} [Group S] {z : MulAut S} {g : S} (hg : z g = g) :
    (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z).map
      (MulAut.conj g).toMonoidHom ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : z x = x := hx
  show z (g * x * g⁻¹) = g * x * g⁻¹
  rw [map_mul, map_mul, map_inv, hg, hx']

theorem fixSubgroup_map_conj_eq {S : Type} [Group S] {z : MulAut S} {g : S} (hg : z g = g) :
    (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z).map
      (MulAut.conj g).toMonoidHom = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z := by
  apply le_antisymm (fixSubgroup_map_conj hg)
  intro x hx
  have hg' : z g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  refine Subgroup.mem_map.2 ⟨(MulAut.conj g⁻¹) x, fixSubgroup_map_conj hg' ⟨x, hx, rfl⟩, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply]
  group

theorem layer_conj_mem {S : Type} [Group S] {z : MulAut S} (X : Subgroup S)
    (hX : X = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z) {g : S} (hg : g ∈ X)
    {n : S} (hn : n ∈ GLALayer X) : g * n * g⁻¹ ∈ GLALayer X := by
  have hgz : z g = g := by
    have : g ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z := hX ▸ hg
    exact this
  have h := map_GLALayer_le_of_eq (MulAut.conj g) (X := X)
    (by rw [hX]; exact fixSubgroup_map_conj_eq hgz)
  have h2 := h (Subgroup.mem_map.2 ⟨n, hn, rfl⟩)
  simpa [MulAut.conj_apply] using h2

theorem isSubnormal_inf_layer {S : Type} [Group S] {z : MulAut S} (X : Subgroup S)
    (hX : X = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z) {W : Subgroup S}
    (hWX : W ≤ X) : IsSubnormal (W ⊓ GLALayer X) W := by
  refine IsSubnormal.step inf_le_left ⟨fun n hn g => ?_⟩ (IsSubnormal.refl W)
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnW, hnL⟩ := Subgroup.mem_inf.1 hn
  exact Subgroup.mem_inf.2 ⟨W.mul_mem (W.mul_mem g.2 hnW) (W.inv_mem g.2),
    layer_conj_mem X hX (hWX g.2) hnL⟩

section Cert


theorem good_orbit {S : Type} [Group S] [Finite S] {p : ℕ} (E : Subgroup (MulAut S))
    (hE : IsElemAbelian p E) {z : MulAut S} (hzE : z ∈ E) (hz1 : z ≠ 1)
    {X : Subgroup S} (hX : X = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z)
    {n : ℕ} (hcard : Nat.card E ≤ n)
    (ih : ∀ m < n, ∀ (S' : Type) [Group S'] [Finite S'], CPlus S' →
      ∀ E' : Subgroup (MulAut S'), IsElemAbelian p E' → Nat.card E' ≤ m → GoodA E'.subtype ⊤)
    (hK : ∀ K : Subgroup S, CFSG.Open.IsComponentOf K X → CPlus (↥K ⧸ Subgroup.center ↥K))
    {K₀ : Subgroup S} (hK₀ : CFSG.Open.IsComponentOf K₀ X) :
    GoodA E.subtype (sSup (orbitOf E.subtype K₀)) := by
  classical
  haveI : Finite (Subgroup S) := Finite.of_injective (fun H : Subgroup S => (H : Set S))
    (fun H K h => SetLike.coe_injective h)
  haveI : Fintype ↥(orbitOf E.subtype K₀) := Fintype.ofFinite _
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
  have hK₀X : K₀ ≤ X := hK₀.1
  have hzK : ∀ y ∈ K₀, z y = y := fun y hy => hzX y (hK₀X hy)
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
  set ρ : ↥E →* MulAut S := E.subtype with hρ
  set O := orbitOf ρ K₀ with hOdef
  have hcomp : ∀ K ∈ O, CFSG.Open.IsComponentOf K X := fun K hK => isComponentOf_orbit hXE hK₀ hK
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
  have hq : CFSG.Open.IsQuasisimple ↥K₀ := hK₀.2.2
  have hsig : ∀ P : Subgroup (↥K₀ ⧸ Subgroup.center ↥K₀),
      P ≤ fixA (quotAct (ρ.comp (stabSub σ i₀).subtype) K₀ hinv₀) → ⁅P, P⁆ = P →
        P ≤ GLALayer (fixA (quotAct (ρ.comp (stabSub σ i₀).subtype) K₀ hinv₀)) := by
    set ρ₀ := ρ.comp (stabSub σ i₀).subtype with hρ₀
    set σ' := quotAct ρ₀ K₀ hinv₀ with hσ'
    have hzstab : (⟨z, hzE⟩ : ↥E) ∈ stabSub σ i₀ := by
      rw [mem_stabSub]
      apply Subtype.ext
      show K₀.map (ρ ⟨z, hzE⟩).toMonoidHom = K₀
      exact hz_fix
    set zA : ↥(stabSub σ i₀) := ⟨⟨z, hzE⟩, hzstab⟩ with hzA
    have hzA_ne : zA ≠ 1 := by
      intro h
      apply hz1
      have := congrArg (fun u : ↥(stabSub σ i₀) => ((u : ↥E) : MulAut S)) h
      exact this
    have hzk : σ' zA = 1 := by
      ext q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      show quotAct ρ₀ K₀ hinv₀ zA (QuotientGroup.mk' (Subgroup.center ↥K₀) x) =
        (1 : MulAut (↥K₀ ⧸ Subgroup.center ↥K₀)) (QuotientGroup.mk' (Subgroup.center ↥K₀) x)
      rw [← quotAct_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [restrictAct_apply]
      exact hzK x x.2
    have hc : ∀ a b : ↥(stabSub σ i₀), a * b = b * a := fun a b => Subtype.ext (hcE a.1 b.1)
    have he : ∀ a : ↥(stabSub σ i₀), a ^ p = 1 := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      exact hE.2 (a.1 : MulAut S) (a.1).2
    have hEab : IsElemAbelian p σ'.range := isElemAbelian_range p σ' hc he
    have hCP : CPlus (↥K₀ ⧸ Subgroup.center ↥K₀) := hK K₀ hK₀
    have hlt : Nat.card σ'.range < n := by
      have h1 := card_range_lt σ' hzA_ne hzk
      have h2 : Nat.card ↥(stabSub σ i₀) ≤ Nat.card E := Subgroup.card_le_card_group _
      omega
    have hIH := ih (Nat.card σ'.range) hlt (↥K₀ ⧸ Subgroup.center ↥K₀) hCP σ'.range hEab le_rfl
    intro P hP hPp
    have hP' : P ≤ fixA σ'.range.subtype ⊓ ⊤ := by
      rw [inf_top_eq, ← fixA_eq_range]
      exact hP
    have h3 := hIH P hP' hPp
    rw [inf_top_eq, ← fixA_eq_range] at h3
    exact h3
  have hgood0 : GoodA ρ (⨆ K : ↥O, K.1) :=
    goodA_iSup_transitive ρ (fun K : ↥O => K.1) hcomm' σ hmap i₀ htrans
      (goodA_of_component (ρ.comp (stabSub σ i₀).subtype) K₀ hinv₀ hq hsig)
  rw [sSup_eq_iSup']
  exact hgood0

theorem good_layer {S : Type} [Group S] [Finite S] {p : ℕ} (E : Subgroup (MulAut S))
    (hE : IsElemAbelian p E) {z : MulAut S} (hzE : z ∈ E) (hz1 : z ≠ 1)
    {X : Subgroup S} (hX : X = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z)
    {n : ℕ} (hcard : Nat.card E ≤ n)
    (ih : ∀ m < n, ∀ (S' : Type) [Group S'] [Finite S'], CPlus S' →
      ∀ E' : Subgroup (MulAut S'), IsElemAbelian p E' → Nat.card E' ≤ m → GoodA E'.subtype ⊤)
    (hK : ∀ K : Subgroup S, CFSG.Open.IsComponentOf K X → CPlus (↥K ⧸ Subgroup.center ↥K)) :
    GoodA E.subtype (GLALayer X) := by
  classical
  haveI : Finite (Subgroup S) := Finite.of_injective (fun H : Subgroup S => (H : Set S))
    (fun H K h => SetLike.coe_injective h)
  have hcE : ∀ a b : ↥E, a * b = b * a := fun a b => (hE.1.is_comm).comm a b
  have hXE : ∀ a : ↥E, X.map (E.subtype a).toMonoidHom = X := by
    intro a
    rw [hX]
    refine fixSubgroup_map_of_comm ?_
    have := congrArg Subtype.val (hcE a ⟨z, hzE⟩)
    exact this
  let ι := {O : Set (Subgroup S) // ∃ K, CFSG.Open.IsComponentOf K X ∧ O = orbitOf E.subtype K}
  haveI : Finite ι := Subtype.finite
  haveI : Fintype ι := Fintype.ofFinite ι
  have hmemO : ∀ O : ι, ∀ K ∈ O.1, CFSG.Open.IsComponentOf K X := by
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
  have hfac : ∀ i : ι, GoodA E.subtype (H i) := by
    intro i
    obtain ⟨K₁, hK₁, hi⟩ := i.2
    have := good_orbit E hE hzE hz1 hX hcard ih hK hK₁
    rw [← hi] at this
    exact this
  have hG := goodA_iSup_coord E.subtype H hcomm hinv hfac
  have hL : GLALayer X = ⨆ i : ι, H i := by
    refine layer_eq_iSup_orbits E.subtype hXE (fun i : ι => i.1) ?_ ?_
    · intro K hK
      exact ⟨⟨orbitOf E.subtype K, K, hK, rfl⟩, mem_orbitOf_self _ K⟩
    · intro i K hK
      exact hmemO i K hK
  rw [hL]
  exact hG

theorem step_good {S : Type} [Group S] [Finite S] (hK : CompTypesCyc) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {n : ℕ}
    (ih : ∀ m < n, ∀ (S' : Type) [Group S'] [Finite S'], CPlus S' →
      ∀ E' : Subgroup (MulAut S'), IsElemAbelian p E' → Nat.card E' ≤ m → GoodA E'.subtype ⊤)
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (hchev : IsChevSimple 2 S)
    (E : Subgroup (MulAut S)) (hE : IsElemAbelian p E) (hcard : Nat.card E ≤ n)
    {z : MulAut S} (hzE : z ∈ E) (hz1 : z ≠ 1) : GoodA E.subtype ⊤ := by
  have hzp : z ^ p = 1 := hE.2 z hzE
  have hXfix : I142.centFix (Subgroup.zpowers z) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z := I142.centFix_zpowers z
  have hKc : ∀ K : Subgroup S, CFSG.Open.IsComponentOf K (I142.centFix (Subgroup.zpowers z)) →
      CPlus (↥K ⧸ Subgroup.center ↥K) := fun K hK' => hK S hS hnc hchev p hp hp2 z hzp K hK'
  have hGL := good_layer E hE hzE hz1 hXfix hcard ih hKc
  have hcz := cyclic_good hS hnc hchev hp hp2 z hzp
  apply goodA_subtype_top_of_centFix
  intro P hP hPp
  have hzfix : ∀ x ∈ I142.centFix E, z x = x := fun x hx => I142.mem_centFix.1 hx z hzE
  have hPX : P ≤ I142.centFix (Subgroup.zpowers z) := by
    intro x hx
    rw [hXfix]
    exact hzfix x (hP hx)
  have hPL : P ≤ GLALayer (I142.centFix (Subgroup.zpowers z)) := hcz P hPX hPp
  have hP2 : P ≤ fixA E.subtype ⊓ GLALayer (I142.centFix (Subgroup.zpowers z)) := by
    rw [fixA_subtype_eq_centFix]
    exact le_inf hP hPL
  have h1 := hGL P hP2 hPp
  have hWX : fixA E.subtype ≤ I142.centFix (Subgroup.zpowers z) := by
    intro x hx
    rw [fixA_subtype_eq_centFix] at hx
    rw [hXfix]
    exact hzfix x hx
  have hsub := isSubnormal_inf_layer (I142.centFix (Subgroup.zpowers z)) hXfix hWX
  rw [fixA_subtype_eq_centFix] at h1 hsub
  exact h1.trans (GLALayer_mono_of_isSubnormal hsub)

theorem goodA_all (hK : CompTypesCyc) (hT : TitsCentSolv) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ n : ℕ, ∀ (S : Type) [Group S] [Finite S], CPlus S → ∀ E : Subgroup (MulAut S),
      IsElemAbelian p E → Nat.card E ≤ n → GoodA E.subtype ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hS E hE hcard
  obtain ⟨hsimp, hnc, hcl⟩ := hS
  by_cases hTits : catalogIs S (onLie (· = TauCeti.LieTypeIndex.tits))
  · apply goodA_subtype_top_of_centFix
    by_cases hbot : E = ⊥
    · subst hbot
      rw [I142.centFix_bot]
      intro P _ _
      exact I142.perfect_le_layer_top hsimp hnc P
    · intro P hP hPp
      haveI := hT S hTits p hp hp2 E hE hbot
      have hPb := eq_bot_of_le_solvable (C := I142.centFix E) hP hPp
      rw [hPb]
      exact bot_le
  · have hchev : IsChevSimple 2 S := hcl.resolve_right hTits
    by_cases hcyc : ∃ β : MulAut S, E = Subgroup.zpowers β
    · obtain ⟨β, rfl⟩ := hcyc
      apply goodA_subtype_top_of_centFix
      exact cyclic_good hsimp hnc hchev hp hp2 β (hE.2 β (Subgroup.mem_zpowers β))
    · have hz : ∃ z ∈ E, z ≠ 1 := by
        by_contra h
        push Not at h
        apply hcyc
        refine ⟨1, ?_⟩
        rw [Subgroup.zpowers_one_eq_bot]
        exact eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx)
      obtain ⟨z, hzE, hz1⟩ := hz
      exact step_good hK hp hp2 ih hsimp hnc hchev E hE hcard hzE hz1

theorem residualNonCyc_of_K (hK : CompTypesCyc) (hT : TitsCentSolv) :
    I142.ResidualNonCyc := by
  intro S _ _ hS hnc hchev p hp hp2 E hE _ P hP hperf
  have hC : CPlus S := ⟨hS, hnc, Or.inl hchev⟩
  have hG := goodA_all hK hT p hp hp2 (Nat.card E) S hC E hE le_rfl
  have h := hG P (by rw [inf_top_eq, fixA_subtype_eq_centFix]; exact hP) hperf
  rw [inf_top_eq, fixA_subtype_eq_centFix] at h
  exact h

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I142N
