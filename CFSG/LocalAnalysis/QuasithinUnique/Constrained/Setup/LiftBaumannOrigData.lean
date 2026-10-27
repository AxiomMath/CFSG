module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigImages
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannSpan
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAut
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannGen

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization commutatorElement

section Dict

variable {G : Type} [Group G] {V : Subgroup G} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : ↥V ≃* Multiplicative W)

@[expose] def vecOf (v : ↥V) : W := Multiplicative.toAdd (θ v)

@[expose] def elOf (w : W) : ↥V := θ.symm (Multiplicative.ofAdd w)

omit [Module (ZMod 2) W] in
theorem vecOf_elOf (w : W) : vecOf θ (elOf θ w) = w := by simp [vecOf, elOf]

omit [Module (ZMod 2) W] in
theorem elOf_vecOf (v : ↥V) : elOf θ (vecOf θ v) = v := by simp [vecOf, elOf]

omit [Module (ZMod 2) W] in
theorem elOf_add (w w' : W) : elOf θ (w + w') = elOf θ w * elOf θ w' := by simp [elOf]

omit [Module (ZMod 2) W] in
theorem elOf_zero : elOf θ (0 : W) = 1 := by simp [elOf]

theorem binPsi_conjAct_vecOf (g : Subgroup.normalizer (V : Set G)) (v : ↥V) :
    binPsi θ (conjAct V g) (vecOf θ v) = vecOf θ (conjAct V g v) := by
  simp [binPsi_apply, vecOf]

theorem mem_fixGL_map_autOn_iff {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (v : ↥V) :
    vecOf θ v ∈ fixGL ((autOn A V).map (binPsi θ).toMonoidHom) ↔
      ∀ a ∈ A, (a : G) * (v : G) = (v : G) * a := by
  rw [mem_fixGL]
  constructor
  · intro h a ha
    have h1 : binPsi θ (conjAct V ⟨a, hA ha⟩) (vecOf θ v) = vecOf θ v :=
      h ((binPsi θ).toMonoidHom (conjAct V ⟨a, hA ha⟩))
        ⟨conjAct V ⟨a, hA ha⟩, mem_autOn_iff.2 ⟨⟨a, hA ha⟩, ha, rfl⟩, rfl⟩
    rw [binPsi_conjAct_vecOf] at h1
    have h2 : conjAct V ⟨a, hA ha⟩ v = v := by
      apply θ.injective
      apply Multiplicative.toAdd.injective
      exact h1
    have h3 : (a : G) * (v : G) * (a : G)⁻¹ = (v : G) := by
      have h3' := congrArg (fun x : ↥V => (x : G)) h2
      simpa [coe_conjAct_apply] using h3'
    calc (a : G) * (v : G) = ((a : G) * v * (a : G)⁻¹) * a := by group
      _ = (v : G) * a := by rw [h3]
  · intro h x hx
    obtain ⟨φ, hφ, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := mem_autOn_iff.1 hφ
    have h3 : conjAct V g v = v := by
      apply Subtype.ext
      rw [coe_conjAct_apply]
      have h4 := h g hg
      rw [h4, mul_inv_cancel_right]
    show binPsi θ (conjAct V g) (vecOf θ v) = vecOf θ v
    rw [binPsi_conjAct_vecOf, h3]

theorem natCard_centralizer_eq {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card ↥(fixGL ((autOn A V).map (binPsi θ).toMonoidHom)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨vecOf θ ⟨x.1, x.2.1⟩,
        (mem_fixGL_map_autOn_iff θ hA _).2 fun a ha => Subgroup.mem_centralizer_iff.1 x.2.2 a ha⟩
      invFun := fun y => ⟨((elOf θ y.1 : ↥V) : G), (elOf θ y.1).2,
        Subgroup.mem_centralizer_iff.2 ((mem_fixGL_map_autOn_iff θ hA (elOf θ y.1)).1
          (by rw [vecOf_elOf]; exact y.2))⟩
      left_inv := fun x => Subtype.ext (by simp [elOf_vecOf])
      right_inv := fun y => Subtype.ext (by simp [vecOf_elOf]) }

theorem elOf_mem_of_span (N : Subgroup G) {S : Set W}
    (hS : ∀ w ∈ S, ((elOf θ w : ↥V) : G) ∈ N) {w : W}
    (hw : w ∈ Submodule.span (ZMod 2) S) : ((elOf θ w : ↥V) : G) ∈ N := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact hS w hw
  | zero => simp [elOf_zero]
  | add a b _ _ ha hb =>
    rw [elOf_add]
    exact N.mul_mem ha hb
  | smul c a _ ha =>
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · simp [elOf_zero]
    · simpa using ha

theorem vspan_of_dict [V.Normal] {J L : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (V : Set G))
    (hspan : Submodule.span (ZMod 2)
      {w : W | ∃ k ∈ (autOn L V).map (binPsi θ).toMonoidHom,
        ∃ y ∈ fixGL ((autOn J V).map (binPsi θ).toMonoidHom), w = k y} = ⊤) :
    (⨆ l ∈ L, Campbell.cj (V ⊓ Subgroup.centralizer (J : Set G)) l) = V := by
  apply le_antisymm
  · refine iSup₂_le fun l hl => ?_
    intro y hy
    have hy' := (Campbell.mem_cj).1 hy
    have hyV : (l : G) * y * l⁻¹ ∈ V := (inf_le_left : V ⊓ _ ≤ V) hy'
    have h2 := (inferInstance : V.Normal).conj_mem _ hyV l⁻¹
    simpa [mul_assoc] using h2
  · intro v hv
    have hw : vecOf θ ⟨v, hv⟩ ∈ (⊤ : Submodule (ZMod 2) W) := Submodule.mem_top
    rw [← hspan] at hw
    have hmem : ((elOf θ (vecOf θ ⟨v, hv⟩) : ↥V) : G) ∈
        ⨆ l ∈ L, Campbell.cj (V ⊓ Subgroup.centralizer (J : Set G)) l := by
      refine elOf_mem_of_span θ _ ?_ hw
      rintro w ⟨k, hk, y, hy, rfl⟩
      obtain ⟨φ', hφ', rfl⟩ := hk
      obtain ⟨l, hl, rfl⟩ := mem_autOn_iff.1 hφ'
      have hv₀ := (mem_fixGL_map_autOn_iff θ hJ (elOf θ y)).1
        (by rw [vecOf_elOf]; exact hy)
      have h1 : elOf θ ((binPsi θ).toMonoidHom (conjAct V l) y) = conjAct V l (elOf θ y) := by
        have h3 := binPsi_conjAct_vecOf θ l (elOf θ y)
        rw [vecOf_elOf] at h3
        show elOf θ (binPsi θ (conjAct V l) y) = _
        rw [h3, elOf_vecOf]
      have hlL : ((l : G))⁻¹ ∈ L := L.inv_mem hl
      have hv₀A : ((elOf θ y : ↥V) : G) ∈ V ⊓ Subgroup.centralizer (J : Set G) :=
        ⟨(elOf θ y).2, Subgroup.mem_centralizer_iff.2 hv₀⟩
      have hcj : (l : G) * ((elOf θ y : ↥V) : G) * (l : G)⁻¹ ∈
          Campbell.cj (V ⊓ Subgroup.centralizer (J : Set G)) ((l : G)⁻¹) := by
        rw [Campbell.mem_cj]
        simpa [mul_assoc] using hv₀A
      rw [h1, coe_conjAct_apply]
      exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hlL hcj)
    simpa [elOf_vecOf] using hmem

theorem split_of_dict [V.Normal] {L : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hVW : commGL ((autOn L V).map (binPsi θ).toMonoidHom) ⊤ ⊔
      fixGL ((autOn L V).map (binPsi θ).toMonoidHom) = ⊤) :
    V ≤ ⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) := by
  intro v hv
  have hw : vecOf θ ⟨v, hv⟩ ∈ commGL ((autOn L V).map (binPsi θ).toMonoidHom) ⊤ ⊔
      fixGL ((autOn L V).map (binPsi θ).toMonoidHom) := by
    rw [hVW]
    trivial
  obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.1 hw
  have hv' : (⟨v, hv⟩ : ↥V) = elOf θ y * elOf θ c := by
    rw [← elOf_add, hyc, elOf_vecOf]
  have hy1 : ((elOf θ y : ↥V) : G) ∈ ⁅V, L⁆ := by
    refine elOf_mem_of_span θ _ ?_ hy
    rintro w ⟨b, hb, u, -, rfl⟩
    obtain ⟨φ', hφ', rfl⟩ := hb
    obtain ⟨l, hl, rfl⟩ := mem_autOn_iff.1 hφ'
    have h1 : elOf θ ((MonoidHom.id (W ≃ₗ[ZMod 2] W)) ((binPsi θ).toMonoidHom (conjAct V l)) u - u) =
        conjAct V l (elOf θ u) * (elOf θ u)⁻¹ := by
      have h3 := binPsi_conjAct_vecOf θ l (elOf θ u)
      rw [vecOf_elOf] at h3
      have h4 : (MonoidHom.id (W ≃ₗ[ZMod 2] W)) ((binPsi θ).toMonoidHom (conjAct V l)) u =
          vecOf θ (conjAct V l (elOf θ u)) := h3
      rw [h4]
      simp [elOf, vecOf, sub_eq_add_neg]
    rw [h1]
    have h5 : ((conjAct V l (elOf θ u) * (elOf θ u)⁻¹ : ↥V) : G) =
        ⁅(l : G), ((elOf θ u : ↥V) : G)⁆ := by
      simp [coe_conjAct_apply, commutatorElement_def]
    rw [h5, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hl (elOf θ u).2
  have hc1 : ((elOf θ c : ↥V) : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨(elOf θ c).2, Subgroup.mem_centralizer_iff.2 ?_⟩
    refine (mem_fixGL_map_autOn_iff θ hL (elOf θ c)).1 ?_
    rw [vecOf_elOf]
    exact hc
  have hv'' : v = ((elOf θ y : ↥V) : G) * ((elOf θ c : ↥V) : G) := by
    have := congrArg (fun z : ↥V => (z : G)) hv'
    simpa using this
  rw [hv'']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy1) (Subgroup.mem_sup_right hc1)

end Dict

section Conj

variable {G : Type} [Group G]

theorem autOn_conjugate (V : Subgroup G) [V.Normal] (X : Subgroup G) (l : G) :
    autOn (CFSG.conjugate X l) V =
      (autOn X V).map (MulAut.conj (MulAut.conjNormal (H := V) l⁻¹)).toMonoidHom := by
  rw [autOn_eq_map_conjNormal, autOn_eq_map_conjNormal]
  unfold CFSG.conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

end Conj

section Natural

variable {G : Type} [Group G] [Finite G]

structure NaturalOriginalData (R V : Subgroup G) : Prop where
  l_gen : ∃ l ∈ oddOrderSubgroup (⊤ : Subgroup G),
    autOn (oddOrderSubgroup (⊤ : Subgroup G)) V ≤
        autOn (thompsonJ R ⊔ CFSG.conjugate (thompsonJ R) l) V ∧
      (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)).relIndex V *
          (V ⊓ Subgroup.centralizer ((CFSG.conjugate (thompsonJ R) l : Subgroup G) :
            Set G)).relIndex V ≤
        (V ⊓ Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G)).relIndex V
  baum_eq : autOn (baum R) V = autOn (thompsonJ R) V
  image_sylow : IsSylowTwoOf (autOn (thompsonJ R) V) (autOn (oddOrderSubgroup (⊤ : Subgroup G)) V)
  V_span : (⨆ l ∈ oddOrderSubgroup (⊤ : Subgroup G),
      Campbell.cj (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) l) = V
  V_split : V = ⁅V, oddOrderSubgroup (⊤ : Subgroup G)⁆ ⊔
    (V ⊓ Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G))

theorem relIndex_eq_of_card {V Y : Subgroup G} {m : ℕ}
    (hc : Nat.card ↥V = m * Nat.card ↥(V ⊓ Y)) : (V ⊓ Y).relIndex V = m := by
  have h1 := Subgroup.relIndex_mul_card (V ⊓ Y) V
  rw [inf_eq_left.2 (inf_le_left : V ⊓ Y ≤ V), hc] at h1
  have hpos : 0 < Nat.card ↥(V ⊓ Y) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem natural_original_data
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn (⊤ : Subgroup G) V) r Lc)
    (hle : autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V) :
    NaturalOriginalData R V := by
  classical
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ F (Fin 2 → F)) := Classical.decEq _
  have hF : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hS.card_eq
  have hred := hS.reduced
  have hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hnorm : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ =>
    hX (Subgroup.mem_top x)
  obtain ⟨⟨W, hW1, hW2, hW3, θ, hmax, himg⟩⟩ := even_SL2_original_images hS hLc
  have hbridge := even_SL2_original_bridge hS hLc
  set ψ := (binPsi θ).toMonoidHom with hψ
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  have hbK : autOn L V = oddOrderSubgroup (autOn (⊤ : Subgroup G) V) := hbridge.K_eq
  have hKL : (autOn L V).map ψ = oddGen ((autOn (⊤ : Subgroup G) V).map ψ) := by
    rw [hbK]
    exact map_closure_odd (binPsi θ) (autOn (⊤ : Subgroup G) V)
  have hnat : NaturalFamily ((autOn (⊤ : Subgroup G) V).map ψ) F r
      (fun i => (Lc i).map ψ) := by
    rcases hmax.offenders.family.alternatives with ⟨hnat, -⟩ | ⟨hdel, -⟩
    · exact hnat
    · exfalso
      apply (himg.deleted hdel).1
      rw [← hKL]
      exact Subgroup.map_mono hle
  have ctx := familyCtx_of_layer hS.two_le hF (isCompListIn_map (binPsi θ) hLc)
    hmax.offenders.family.layer
  obtain ⟨hD1, hD2, -, hD4⟩ := himg.natural hnat
  obtain ⟨g, hgK, hgen⟩ := natural_exists_gen_element ctx hnat hmax.U_sylow
  have hgK' : g⁻¹ ∈ (autOn L V).map ψ := by
    rw [hKL, ctx.layer.K_eq]
    exact Subgroup.inv_mem _ hgK
  obtain ⟨φ, hφ, hφg⟩ := hgK'
  obtain ⟨x, hxL, hxφ⟩ := mem_autOn_iff.1 hφ
  have hφg' : binPsi θ φ = g⁻¹ := hφg
  have := hVn
  have hψc : binPsi θ (MulAut.conjNormal (H := V) ((x : G)⁻¹)) = g := by
    have h1 : MulAut.conjNormal (H := V) ((x : G)⁻¹) = φ⁻¹ := by
      rw [map_inv, ← BlueprintB2.conjAct_eq_conjNormal V x, hxφ]
    rw [h1, map_inv, hφg', inv_inv]
  have hconj : (autOn (CFSG.conjugate (thompsonJ R) (x : G)) V).map ψ =
      B6.conjSub g ((autOn (thompsonJ R) V).map ψ) := by
    rw [autOn_conjugate V (thompsonJ R) (x : G), Subgroup.map_map]
    have hcomp : ψ.comp (MulAut.conj (MulAut.conjNormal (H := V) ((x : G)⁻¹))).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp ψ := by
      ext a
      simp [hψ, ← hψc]
    rw [hcomp, ← Subgroup.map_map]
    rfl
  have hF1 : autOn L V ≤ autOn (thompsonJ R ⊔ CFSG.conjugate (thompsonJ R) (x : G)) V := by
    refine (Subgroup.map_le_map_iff_of_injective (f := ψ) (binPsi θ).injective).1 ?_
    have hsup : autOn (thompsonJ R ⊔ CFSG.conjugate (thompsonJ R) (x : G)) V =
        autOn (thompsonJ R) V ⊔ autOn (CFSG.conjugate (thompsonJ R) (x : G)) V := by
      rw [autOn_eq_map_conjNormal, autOn_eq_map_conjNormal, autOn_eq_map_conjNormal,
        Subgroup.map_sup]
    rw [hKL, hsup, Subgroup.map_sup, hconj, ctx.layer.K_eq, hD1]
    exact hgen
  have hVW : Nat.card ↥V = Nat.card W := Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)
  have hcardJ : Nat.card ↥(V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) =
      Nat.card ↥(fixGL ((autOn (thompsonJ R) V).map ψ)) := natCard_centralizer_eq θ (hnorm _)
  have hcardJl : Nat.card ↥(V ⊓ Subgroup.centralizer
      ((CFSG.conjugate (thompsonJ R) (x : G) : Subgroup G) : Set G)) =
      Nat.card ↥(fixGL ((autOn (thompsonJ R) V).map ψ)) := by
    rw [natCard_centralizer_eq θ (hnorm _), hconj, fixGL_conjSub]
    exact natCard_map_linearEquiv g _
  have hcardL : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) =
      Nat.card ↥(fixGL (oddGen ((autOn (⊤ : Subgroup G) V).map ψ))) := by
    rw [natCard_centralizer_eq θ (hnorm _), hKL]
  have hKcard := card_V_natural ctx hnat
  have hr1 : (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)).relIndex V = 2 ^ (n * r) := by
    refine relIndex_eq_of_card ?_
    rw [hVW, hD4, hcardJ]
  have hr2 : (V ⊓ Subgroup.centralizer
      ((CFSG.conjugate (thompsonJ R) (x : G) : Subgroup G) : Set G)).relIndex V =
        2 ^ (n * r) := by
    refine relIndex_eq_of_card ?_
    rw [hVW, hD4, hcardJl]
  have hr3 : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V = 2 ^ (2 * n * r) := by
    refine relIndex_eq_of_card ?_
    rw [hVW, hKcard, hcardL, mul_comm]
  have hcodim : (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)).relIndex V *
      (V ⊓ Subgroup.centralizer
        ((CFSG.conjugate (thompsonJ R) (x : G) : Subgroup G) : Set G)).relIndex V ≤
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V := by
    rw [hr1, hr2, hr3, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [show 2 * n * r = n * r + n * r by ring])
  have hspan := natural_span ctx hnat hmax.U_sylow
  have hVspan : (⨆ l ∈ L, Campbell.cj (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) l) = V := by
    refine vspan_of_dict θ (hnorm (thompsonJ R)) ?_
    rw [hKL, hD1]
    exact hspan
  have hsplit : V ≤ ⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) := by
    refine split_of_dict θ (hnorm L) ?_
    rw [hKL]
    exact V_eq_of_ctx ctx
  refine ⟨⟨(x : G), hxL, hF1, hcodim⟩, ?_, ?_, hVspan, ?_⟩
  · exact Subgroup.map_injective (f := ψ) (binPsi θ).injective himg.baumann_eq.symm
  · have h := hD2
    rw [← hKL] at h
    exact (isSylowTwoOf_map_mulEquiv (binPsi θ)).1 h
  · refine le_antisymm hsplit ?_
    refine sup_le (Subgroup.commutator_le.2 fun v hv l _ => ?_) inf_le_left
    have h1 : (l : G) * v⁻¹ * l⁻¹ ∈ V := hVn.conj_mem _ (V.inv_mem hv) l
    have h2 := V.mul_mem hv h1
    simpa [commutatorElement_def, mul_assoc] using h2

end Natural

end CFSG.QuasithinUnique.Setup.Lift
