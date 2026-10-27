module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeFam
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocle

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open scoped commutatorElement

section Aut

variable {Q : Type*} [Group Q]

theorem mulAut_mem_center (φ : Q ≃* Q) {x : Q} (hx : x ∈ Subgroup.center Q) :
    φ x ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro g
  have h2 := congrArg φ (hx (φ.symm g))
  simpa using h2

theorem map_center_mulAut (φ : Q ≃* Q) :
    (Subgroup.center Q).map φ.toMonoidHom = Subgroup.center Q := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact mulAut_mem_center φ hx
  · intro x hx
    exact ⟨φ.symm x, mulAut_mem_center φ.symm hx, by simp⟩

@[expose] def quotCenterAut (φ : Q ≃* Q) : (Q ⧸ Subgroup.center Q) ≃* (Q ⧸ Subgroup.center Q) :=
  QuotientGroup.congr (Subgroup.center Q) (Subgroup.center Q) φ (map_center_mulAut φ)

@[simp] theorem quotCenterAut_mk (φ : Q ≃* Q) (x : Q) :
    quotCenterAut φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem quotCenterAut_symm_mk (φ : Q ≃* Q) (x : Q) :
    (quotCenterAut φ).symm (QuotientGroup.mk x) = QuotientGroup.mk (φ.symm x) := by
  apply (quotCenterAut φ).injective
  simp

end Aut

section Comm

variable {A : Type*} [Group A]

theorem false_of_comm_aut {z : A} (hz2 : z * z = 1) (V W : A ≃* A) (hV2 : ∀ x, V (V x) = x)
    (hWz : W z = z) (hVd : (∀ x, V x = x) ∨ (∀ x, V x = z * x * z⁻¹))
    (hc : ∀ x, V (W (V (W.symm x))) = z * x * z⁻¹) : ∀ x, z * x * z⁻¹ = x := by
  intro x
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  rcases hVd with h | h
  · have h1 := hc x
    rw [h, h] at h1
    simpa using h1.symm
  · have h1 := hc x
    have e1 : V (W.symm x) = z * W.symm x * z⁻¹ := h _
    have e2 : W (z * W.symm x * z⁻¹) = z * x * z⁻¹ := by
      rw [map_mul, map_mul, hWz, map_inv, hWz]
      simp
    have e3 : V (z * x * z⁻¹) = z * (z * x * z⁻¹) * z⁻¹ := h _
    rw [e1, e2, e3] at h1
    have e4 : z * (z * x * z⁻¹) * z⁻¹ = x := by
      calc z * (z * x * z⁻¹) * z⁻¹ = (z * z) * x * (z⁻¹ * z⁻¹) := by group
        _ = x := by rw [hz2, ← mul_inv_rev, hz2, inv_one]; group
    rw [e4] at h1
    exact h1.symm

end Comm

section Struct

variable {r : ℕ} {Q : Type} [Group Q] [Finite Q] {R : Subgroup Q} {S : Sylow 2 R} {z : Q}

theorem isQuasisimple_of_open_R {P : Type*} [Group P] (h : CFSG.Open.IsQuasisimple P) :
    CFSG.IsQuasisimple P := by
  have hp : Group.IsPerfect P := ⟨h.1⟩
  have hs : IsSimpleGroup (P ⧸ Subgroup.center P) := h.2
  refine ⟨hp, hs, ?_⟩
  have := Group.IsPerfect.not_isMulCommutative (P ⧸ Subgroup.center P)
  simpa only [isMulCommutative_iff, not_forall] using this

theorem exists_normal_component (hd : TightDatum R S z) (hc : TightClsR r Q R S z)
    (hnO : ¬ TightInO2 z) :
    ∃ L : Subgroup Q, CFSG.IsQuasisimple ↥L ∧ L.Normal ∧
      Subgroup.centralizer (L : Set Q) = Subgroup.center Q := by
  have hcent : ∀ (L : Subgroup Q), Subgroup.center Q ≤ Subgroup.centralizer (L : Set Q) :=
    fun L x hx => Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp hx g
  rcases tightDichotomyR_holds r (Nat.card Q) Q rfl R S z hd hc with h | hQ | ⟨L, hLc, hLn, hlayer, hzL, hLnc, hFZ, hFL⟩
  · exact absurd h hnO
  · refine ⟨genFittingFStar Q, isQuasisimple_of_open_R hQ, genFittingFStar_normal Q, ?_⟩
    refine le_antisymm ?_ (hcent _)
    intro g hg
    have hgF : g ∈ genFittingFStar Q := CFSG.Adapters.generalized_fitting_self_centralizing Q hg
    have hg' : (⟨g, hgF⟩ : ↥(genFittingFStar Q)) ∈ Subgroup.center ↥(genFittingFStar Q) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg y.1 y.2)
    exact fstarCenter_le_center_R hd hc hnO ⟨⟨g, hgF⟩, hg', rfl⟩
  · refine ⟨L, hLc.1, hLn, le_antisymm ?_ (hcent L)⟩
    intro g hg
    set F := genFittingFitting Q with hF
    have hFstar : genFittingFStar Q = F ⊔ L := by
      show genFittingFitting Q ⊔ genFittingLayer Q = _
      rw [genFittingLayer_eq_layer, hlayer]
    haveI hFn : F.Normal := ⟨fun n hn g' => by
      have := Subgroup.mem_center_iff.mp (hFZ hn) g'
      rw [this, mul_inv_cancel_right]
      exact hn⟩
    have hFcent : ∀ y : Q, F ≤ Subgroup.centralizer ({y} : Set Q) := fun y f hf =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp (hFZ hf) y).symm
    have hLg : L ≤ Subgroup.centralizer ({g} : Set Q) := fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hg l hl)
    have hgC : g ∈ Subgroup.centralizer (genFittingFStar Q : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hFstar] at hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (sup_le (hFcent g) hLg hy)
    have hgF : g ∈ genFittingFStar Q := CFSG.Adapters.generalized_fitting_self_centralizing Q hgC
    rw [hFstar, sup_comm] at hgF
    obtain ⟨l, hl, f, hf, hlf⟩ := Subgroup.mem_sup_of_normal_right.mp hgF
    have hlcL : l ∈ Subgroup.centralizer (L : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l' hl'
      have h1 := Subgroup.mem_centralizer_iff.mp hg l' hl'
      have h2 : l = g * f⁻¹ := by rw [← hlf]; group
      have h3 := Subgroup.mem_center_iff.mp (hFZ hf) l'
      rw [h2]
      calc l' * (g * f⁻¹) = (l' * g) * f⁻¹ := by group
        _ = (g * l') * f⁻¹ := by rw [h1]
        _ = g * (l' * f⁻¹) := by group
        _ = g * (f⁻¹ * l') := by
          congr 1
          have := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ (hFZ hf)) l'
          exact this
        _ = (g * f⁻¹) * l' := by group
    have hlF : l ∈ genFittingFStar Q := by
      rw [hFstar]
      exact Subgroup.mem_sup_right hl
    have hlc : (⟨l, hlF⟩ : ↥(genFittingFStar Q)) ∈ Subgroup.center ↥(genFittingFStar Q) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : (y : Q) ∈ Subgroup.centralizer ({l} : Set Q) := by
        have hle : genFittingFStar Q ≤ Subgroup.centralizer ({l} : Set Q) := by
          rw [hFstar]
          exact sup_le (hFcent l) (fun l' hl' => Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hlcL l' hl'))
        exact hle y.2
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy)
    have hlZ : l ∈ Subgroup.center Q := fstarCenter_le_center_R hd hc hnO ⟨⟨l, hlF⟩, hlc, rfl⟩
    rw [← hlf]
    exact Subgroup.mul_mem _ hlZ (hFZ hf)

theorem center_le_fstarCenter' (Q : Type) [Group Q] [Finite Q] :
    Subgroup.center Q ≤ TA3.fstarCenter Q := by
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (genFittingFStar Q : Set Q) :=
    Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp hx g
  have hxF : x ∈ genFittingFStar Q := CFSG.Adapters.generalized_fitting_self_centralizing Q hxC
  refine ⟨⟨x, hxF⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.mp hx y)

theorem isPGroup_center_R (hc : TightClsR r Q R S z) : IsPGroup 2 ↥(Subgroup.center Q) :=
  (isPGroup_fstarCenter_R hc).to_le (center_le_fstarCenter' Q)

end Struct

section Model

@[expose] def Model163R (r : ℕ) : Prop :=
  4 ≤ r → ∀ (A : Type) [Group A] [Finite A] (T : Subgroup A) [T.Normal], IsSimpleGroup ↥T →
    (∃ a b : ↥T, a * b ≠ b * a) → Subgroup.centralizer (T : Set A) = ⊥ → EdgelessFamily ↥T →
    ∀ (R : Subgroup A) (S : Sylow 2 R) (z : A), TightDatum R S z → TightClsR r A R S z →
      ¬ TightInO2 z → TightEdgeless R →
      ∀ φ : A ≃* A, (∀ x, φ (φ x) = x) → (∀ s ∈ (S : Subgroup R).map R.subtype, φ s = s) →
        (∀ x, φ x = x) ∨ (∀ x, φ x = z * x * z⁻¹)

end Model

section Ident


theorem layerAut {r n : ℕ} (hr : 4 ≤ r) (hA : CIT3Below n) (hB : TightBelowR r n)
    (hList : SmallListR) (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m) (hM : Model163R r)
    {Q : Type} [Group Q] [Finite Q] (hQn : Nat.card Q < n) {R : Subgroup Q} {S : Sylow 2 R}
    {z : Q} (hd : TightDatum R S z) (hc : TightClsR r Q R S z) (hnO : ¬ TightInO2 z)
    (hE : TightEdgeless R) :
    (∀ φ : Q ≃* Q, (∀ x, φ (φ x) = x) → (∀ s ∈ (S : Subgroup R).map R.subtype, φ s = s) →
      (∀ y, quotCenterAut φ y = y) ∨
        (∀ y, quotCenterAut φ y = QuotientGroup.mk z * y * (QuotientGroup.mk z)⁻¹)) ∧
    z ∉ Subgroup.center Q ∧
    ((∀ y : Q ⧸ Subgroup.center Q, QuotientGroup.mk z * y = y * QuotientGroup.mk z) →
      z ∈ Subgroup.center Q) := by
  classical
  obtain ⟨L, hLq, hLn, hLC⟩ := exists_normal_component hd hc hnO
  have hN2 : IsPGroup 2 ↥(Subgroup.center Q) := isPGroup_center_R hc
  have htN : z ∉ (Subgroup.center Q) := fun h => hnO ⟨(Subgroup.center Q), inferInstance, hN2, h⟩
  have hNc : (Subgroup.center Q) ≤ Subgroup.center Q := le_rfl
  have hnt : ∀ y : Q, ∀ n ∈ (Subgroup.center Q), y * z * y⁻¹ = z * n → n = 1 := by
    intro y n hn hy
    by_contra h1
    exact hd.not_edgeless_of_twin hn h1 hy hE
  have hd' := TwistQ.datum hd hN2 htN hnt
  have hc' := twistQ_clsR hd hNc hN2 htN hc
  have hnO' : ¬ TightInO2 (QuotientGroup.mk' (Subgroup.center Q) z) := fun h => hnO (TwistQ.inO2_of hN2 h)
  haveI := hLn
  have hTs : IsSimpleGroup ↥(socleOf L) := isSimpleGroup_socle hLq hLC
  have hTab := exists_ne_comm_socle hLq hLC
  have hTC := centralizer_socle_eq_bot hLq hLC
  have hAn : Nat.card (Q ⧸ (Subgroup.center Q)) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center Q))) hQn
  have hZA : Subgroup.center (Q ⧸ (Subgroup.center Q)) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [← hTC, Subgroup.mem_centralizer_iff]
    intro g _
    exact (Subgroup.mem_center_iff.mp hx g)
  have hE' : TightEdgeless (R.map (QuotientGroup.mk' (Subgroup.center Q))) := by
    rcases (hB (Q ⧸ (Subgroup.center Q)) hAn _ _ _ hd' hc').resolve_right
      (not_goodThreeElement_of_four_le hr hd' hc'.1) with h2 | ⟨he, -⟩ | ⟨he, -⟩ | h4
    · exact absurd h2 hnO'
    · exact he
    · exact he
    · exact absurd h4 (not_tightE4_R hd' hc' hnO' hZA)
  have hT : socleOf L ≤ (MonoidHom.id (Q ⧸ (Subgroup.center Q))).range := fun x _ => ⟨x, rfl⟩
  have h4gen := twoSubgroupsFourGenerated_socle hr hA hB h6 (socleOf L) hTs hTab hTC hAn
    (MonoidHom.id (Q ⧸ (Subgroup.center Q))) Function.injective_id hT hd' hc' hnO'
  have hfam := edgelessFamily_of_embedded hr hList hO (socleOf L) hTs hTab hTC h4gen
    (MonoidHom.id (Q ⧸ (Subgroup.center Q))) Function.injective_id hT hd' hc'
  refine ⟨fun φ hφ2 hφS => ?_, htN, fun hz => ?_⟩
  · have hmk : ∀ x : Q, QuotientGroup.mk' (Subgroup.center Q) x = (QuotientGroup.mk x : Q ⧸ (Subgroup.center Q)) := fun x => rfl
    have h := hM hr (Q ⧸ (Subgroup.center Q)) (socleOf L) hTs hTab hTC hfam _ _ _ hd' hc' hnO' hE' (quotCenterAut φ)
      (by
        intro y
        induction y using QuotientGroup.induction_on with
        | H x => simp [hφ2])
      (by
        intro s hs
        rw [TwistQ.sylowMap_map_subtype] at hs
        obtain ⟨s₀, hs₀, rfl⟩ := hs
        simp [hφS s₀ hs₀])
    exact h
  · have hz' : (QuotientGroup.mk z : Q ⧸ (Subgroup.center Q)) ∈ Subgroup.centralizer (socleOf L : Set (Q ⧸ (Subgroup.center Q))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g _
      exact (hz g).symm
    rw [hTC, Subgroup.mem_bot] at hz'
    exact (QuotientGroup.eq_one_iff z).mp hz'

theorem false_of_layer_aut {r n : ℕ} (hr : 4 ≤ r) (hA : CIT3Below n) (hB : TightBelowR r n)
    (hList : SmallListR) (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m) (hM : Model163R r)
    {Q : Type} [Group Q] [Finite Q] (hQn : Nat.card Q < n) {R : Subgroup Q} {S : Sylow 2 R}
    {z : Q} (hd : TightDatum R S z) (hc : TightClsR r Q R S z) (hnO : ¬ TightInO2 z)
    (hE : TightEdgeless R) (V W : Q ≃* Q) (hV2 : ∀ x, V (V x) = x)
    (hVS : ∀ s ∈ (S : Subgroup R).map R.subtype, V s = s) (hWz : W z = z)
    (hcomm : ∀ x, V (W (V (W.symm x))) = z * x * z⁻¹) : False := by
  obtain ⟨hdich, hzn, hz3⟩ := layerAut hr hA hB hList hO h6 hM hQn hd hc hnO hE
  have hz2 : z * z = 1 := by rw [← pow_two, ← hd.order, pow_orderOf_eq_one]
  have hcen := false_of_comm_aut (A := Q ⧸ Subgroup.center Q) (z := QuotientGroup.mk z)
    (by rw [← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one]) (quotCenterAut V) (quotCenterAut W)
    (by
      intro y
      induction y using QuotientGroup.induction_on with
      | H x => simp [hV2])
    (by simp [hWz]) (hdich V hV2 hVS)
    (by
      intro y
      induction y using QuotientGroup.induction_on with
      | H x =>
        rw [quotCenterAut_symm_mk]
        simp [hcomm x])
  exact hzn (hz3 fun y => by
    have := hcen y
    calc QuotientGroup.mk z * y = (QuotientGroup.mk z * y * (QuotientGroup.mk z)⁻¹) * QuotientGroup.mk z := by
          group
      _ = y * QuotientGroup.mk z := by rw [this])

end Ident

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest
