module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PU3Res
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PU3Embed
import CFSG.HardMathSupport.Solomon.Coordinator.WeakHolds
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotOuter
import CFSG.GroupTheory.HuppertProduct.RankBound
import CFSG.RankThree.PartOne.BRANCH.RankArith
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PU3Res

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.ComponentClassification.OuterAutomorphisms

variable {n : ℕ} {K : Type} [Field K]

private theorem count_primeFormD (h : UnitaryFieldData 2 n K) (h1 : 1 < n) :
    ∀ A : Subgroup (MulAut (pI h)), IsElemAbelian 3 A →
      Nat.card A ≤ 3 * Nat.card ↥(A ⊓
        primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  classical
  haveI : Finite K := h.finite
  have hq := hq_aux h1
  intro A hA
  let D : Subgroup (MulAut (pI h)) :=
    primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  let φ := primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq
  let f : A →* RingAut K := φ.comp A.subtype
  have hkerφ : φ.ker = D := ker_primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq
  have hcardker : Nat.card f.ker = Nat.card ↥(A ⊓ D) := by
    have h1' : f.ker = D.comap A.subtype := by
      rw [← hkerφ, MonoidHom.comap_ker]
    rw [h1', Subgroup.comap_subtype, ← Subgroup.inf_subgroupOf_left D A]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := A ⊓ D) (K := A) inf_le_left).toEquiv
  haveI : IsCyclic (RingAut K) :=
    (card_ringAut_and_isCyclic h.prime K h.card).2
  haveI : Finite (RingAut K) :=
    Nat.finite_of_card_ne_zero (by
      rw [(card_ringAut_and_isCyclic h.prime K h.card).1]
      exact (Nat.mul_pos (by norm_num) h.one_le).ne')
  have hcyc : IsCyclic f.range :=
    isCyclic_of_injective f.range.subtype Subtype.val_injective
  have hexp : ∀ e ∈ f.range, e ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    have ha3 : a ^ 3 = 1 := Subtype.ext (hA.2 a a.2)
    rw [← map_pow, ha3, map_one]
  have hrange : Nat.card f.range ≤ 3 :=
    CFSG.GroupTheory.HuppertProduct.card_le_three_of_isCyclic hcyc le_rfl hexp
  have hcard := Subgroup.card_ker_mul_card_range f
  calc Nat.card A = Nat.card ↥(A ⊓ D) * Nat.card f.range := by rw [← hcard, hcardker]
    _ ≤ Nat.card ↥(A ⊓ D) * 3 := Nat.mul_le_mul_left _ hrange
    _ = 3 * Nat.card ↥(A ⊓ D) := Nat.mul_comm _ _

private theorem bend_primeFormD (h : UnitaryFieldData 2 n K) (h1 : 1 < n) :
    ∀ (E : Subgroup (MulAut (pI h))), IsElemAbelian 3 E →
      E ≤ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →
      ∀ T : Subgroup (pI h), IsPGroup 2 T → T ≠ ⊥ →
        (∀ α ∈ E, ∀ y ∈ T, α y ∈ T) → Nat.card E ≤ 3 := by
  classical
  haveI : Finite K := h.finite
  have hq := hq_aux h1
  have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner (pI h) ≤
      primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    CFSG.SeitzReduction.UnitaryPilot.inner_le_primeFormD h _
  intro E hE hED T hT2 hT0 hnorm
  let c : pI h →* MulAut (pI h) := MulAut.conj
  let T' : Subgroup (MulAut (pI h)) := T.map c
  have hsimple : IsSimpleGroup (pI h) :=
    CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one h (by norm_num) hq
  have hnc : ¬ ∀ x y : pI h, x * y = y * x :=
    CFSG.RankThree.Classical.not_commute_primeFormP_one h (by norm_num) hq
  have hnab : ∃ x y : pI h, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    exact hnc hcon
  have hcenter : Subgroup.center (pI h) = ⊥ :=
    CFSG.ComponentClassification.OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  have hinj : Function.Injective c :=
    CFSG.ComponentClassification.OutcomeLocal.conj_injective_of_center_eq_bot hcenter
  have hT'2 : IsPGroup 2 T' := hT2.map c
  have hT'le : T' ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (pI h) :=
    Subgroup.map_le_range (f := c) T
  have hT'0 : T' ≠ ⊥ := by
    change T.map c ≠ ⊥
    exact fun hbot => hT0 ((Subgroup.map_eq_bot_iff_of_injective T (f := c) hinj).1 hbot)
  have hT'D : T' ⊓ primeFormD h
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ ⊥ := by
    rw [inf_eq_left.mpr (hT'le.trans hinner)]
    exact hT'0
  have hnorm' : E ≤ Subgroup.normalizer (T' : Set (MulAut (pI h))) := by
    intro α hα
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨α y, hnorm α hα y hy,
        (CFSG.ComponentClassification.OutcomeLocal.mulAut_mul_conj_mul_inv α y).symm⟩
    · rintro ⟨y, hy, hxy⟩
      refine ⟨α⁻¹ y, hnorm α⁻¹ (E.inv_mem hα) y hy, ?_⟩
      calc MulAut.conj (α⁻¹ y) = α⁻¹ * MulAut.conj y * α := by
            simpa using
              (CFSG.ComponentClassification.OutcomeLocal.mulAut_mul_conj_mul_inv α⁻¹ y).symm
        _ = α⁻¹ * (α * x * α⁻¹) * α := by rw [← hxy]
        _ = x := by group
  obtain ⟨θ, hθ⟩ :=
    exists_injective_units_of_normalizes h h1 E T' hE.isPGroup hED hT'2 hT'D hnorm'
  let E' : Subgroup Kˣ := θ.range
  have hEcyc : IsCyclic E' :=
    isCyclic_of_injective E'.subtype Subtype.val_injective
  have hEexp : ∀ e ∈ E', e ^ 3 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    have he3 : e ^ 3 = 1 := Subtype.ext (hE.2 e e.2)
    rw [← map_pow, he3, map_one]
  have hcardmap : Nat.card E' ≤ 3 :=
    CFSG.GroupTheory.HuppertProduct.card_le_three_of_isCyclic hEcyc le_rfl hEexp
  have hE'card : Nat.card E' = Nat.card E := by
    rw [show E' = (⊤ : Subgroup E).map θ from MonoidHom.range_eq_map θ]
    rw [Subgroup.card_map_of_injective (K := ⊤) hθ, Subgroup.card_top]
  rw [hE'card] at hcardmap
  exact hcardmap

private theorem i1015U3Res_primeFormP (h : UnitaryFieldData 2 n K) (h1 : 1 < n) :
    I1015U3Res (pI h) := by
  classical
  haveI : Finite K := h.finite
  have hq := hq_aux h1
  let D : Subgroup (MulAut (pI h)) :=
    primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hDnormal : D.Normal := by
    dsimp only [D]
    rw [← ker_primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq]
    infer_instance
  have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner (pI h) ≤ D :=
    CFSG.SeitzReduction.UnitaryPilot.inner_le_primeFormD h
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  refine ⟨D, hDnormal, hinner, ?_, ?_⟩
  · exact count_primeFormD h h1
  · exact bend_primeFormD h h1

theorem i1015U3Res_of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L)
    (h : I1015U3Res L) : I1015U3Res K := by
  obtain ⟨P, hPn, hinner, hcount, hbend⟩ := h
  let c : MulAut K ≃* MulAut L := MulAut.congr e
  let Q : Subgroup (MulAut K) := P.comap c.toMonoidHom
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · dsimp only [Q]
    exact hPn.comap c.toMonoidHom
  · intro α hα
    exact hinner ((congr_mem_inner_iff e α).2 hα)
  · intro A hA
    have hA' : IsElemAbelian 3 (A.map c.toMonoidHom) := hA.map c.toMonoidHom
    have hc := hcount (A.map c.toMonoidHom) hA'
    have hcardA : Nat.card (A.map c.toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective c.injective
    have hmap : (A ⊓ Q).map c.toMonoidHom = A.map c.toMonoidHom ⊓ P := by
      rw [Subgroup.map_inf A Q c.toMonoidHom c.injective]
      congr 1
      dsimp only [Q]
      exact Subgroup.map_comap_eq_self (f := c.toMonoidHom) (H := P) (by
        rw [show c.toMonoidHom.range = ⊤ from MonoidHom.range_eq_top.2 c.surjective]
        exact le_top)
    have hcardQ : Nat.card ↥(A ⊓ Q) = Nat.card ↥(A.map c.toMonoidHom ⊓ P) := by
      rw [← hmap]
      exact (Subgroup.card_map_of_injective (f := c.toMonoidHom) c.injective).symm
    calc Nat.card A = Nat.card (A.map c.toMonoidHom) := hcardA.symm
      _ ≤ 3 * Nat.card ↥(A.map c.toMonoidHom ⊓ P) := hc
      _ = 3 * Nat.card ↥(A ⊓ Q) := by rw [hcardQ]
  · intro E hE hEQ T hT2 hT0 hnorm
    have hE' : IsElemAbelian 3 (E.map c.toMonoidHom) := hE.map c.toMonoidHom
    have hE'P : E.map c.toMonoidHom ≤ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact hEQ hx
    have hT' : IsPGroup 2 (T.map e.toMonoidHom) := hT2.map e.toMonoidHom
    have hT'0 : T.map e.toMonoidHom ≠ ⊥ := by
      exact fun hbot =>
        hT0 ((Subgroup.map_eq_bot_iff_of_injective T (f := e.toMonoidHom) e.injective).1 hbot)
    have hnorm' : ∀ α' ∈ E.map c.toMonoidHom, ∀ y' ∈ T.map e.toMonoidHom,
        α' y' ∈ T.map e.toMonoidHom := by
      rintro _ ⟨α, hα, rfl⟩ _ ⟨y, hy, rfl⟩
      refine ⟨α y, hnorm α hα y hy, ?_⟩
      change e (α y) = e (α (e.symm (e y)))
      rw [e.symm_apply_apply]
    have hb := hbend (E.map c.toMonoidHom) hE' hE'P (T.map e.toMonoidHom) hT' hT'0 hnorm'
    rwa [Subgroup.card_map_of_injective (f := c.toMonoidHom) c.injective] at hb

private theorem extract {i : TauCeti.CFSGIndex} (hi : S9.isU3char2 i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid),
      i = .lie ⟨.twistedA 2 q, hv⟩ ∧ q.p = 2 ∧ q.card % 3 = 2 := by
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA n q =>
      by_cases hn : n = 2
      · subst hn
        simp only [S9.isU3char2, onLie] at hi
        exact ⟨q, hv, rfl, hi⟩
      · simp [S9.isU3char2, onLie, hn] at hi
    | _ => simp [S9.isU3char2, onLie] at hi
  | cyclic p hp => simp [S9.isU3char2, onLie] at hi
  | alternating n hn => simp [S9.isU3char2, onLie] at hi
  | sporadic name => simp [S9.isU3char2, onLie] at hi

theorem i1015U3Res_holds :
    ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isU3char2 → I1015U3Res K := by
  intro K _ _ hK
  obtain ⟨i, hi, ⟨eK⟩⟩ := hK
  obtain ⟨Q, hv, rfl, h2q, hqmod⟩ := extract hi
  let Q2 : TauCeti.PrimePower := ⟨2, Q.exponent, Nat.prime_two, Q.exponent_pos⟩
  have hQ2 : Q2 = Q := TauCeti.PrimePower.ext h2q.symm rfl
  have hv2 : (TauCeti.LieTypeIndex.twistedA 2 Q2).Valid := by
    rw [hQ2]
    exact hv
  let i0 : TauCeti.CFSGIndex := .lie ⟨TauCeti.LieTypeIndex.twistedA 2 Q, hv⟩
  let i2 : TauCeti.CFSGIndex := .lie ⟨TauCeti.LieTypeIndex.twistedA 2 Q2, hv2⟩
  have hi02 : i0 = i2 := by
    apply congrArg TauCeti.CFSGIndex.lie
    apply Subtype.ext
    exact congrArg (fun q => TauCeti.LieTypeIndex.twistedA 2 q) hQ2.symm
  let eK2 : K ≃* i2.Group := eK.trans (MulEquiv.cast hi02)
  obtain ⟨F, _, h, hne, ⟨eP⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.unitary_catalogue_model 2 Q2 hv2 eK2
  have hne2 : 2 ^ Q.exponent ≠ 2 := fun hc => hne ⟨rfl, hc⟩
  have h1 : 1 < Q.exponent := by
    have hcard2 : Q.card = 2 ^ Q.exponent := by
      rw [TauCeti.PrimePower.card_def, h2q]
    rcases CFSG.RankThree.PartOne.BRANCH.two_pow_mod_three Q.exponent with
      ⟨hmod, -⟩ | ⟨-, hodd⟩
    · rw [hcard2] at hqmod
      omega
    · obtain ⟨m, hm⟩ := hodd
      rcases m with _ | m
      · have h2 : 2 ^ Q.exponent = 2 := by rw [hm]; norm_num
        exact absurd h2 hne2
      · omega
  let h' : UnitaryFieldData 2 Q.exponent F := h
  exact i1015U3Res_of_mulEquiv eP (i1015U3Res_primeFormP h' h1)

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PU3Res
