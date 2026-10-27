module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H2017LFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxAll
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts4
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.GenNormality
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Cent
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017Cls

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA (I2017LieA8Shape I2017LieClassification)

@[expose] def HasA8Comp {T : Type} [Group T] (β : MulAut T) : Prop :=
  ∃ K : Subgroup T, GLAPComponent 3 (fixSubgroup β) K ∧ IsComponentOf K (fixSubgroup β) ∧
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃* ↥(alternatingGroup (Fin 8)))

@[expose] def InnA8 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, KD264Lie.fieldSize d.1 = 2 →
    Finite (TauCeti.CFSGIndex.lie d).Group → IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group →
    ∀ β : MulAut (TauCeti.CFSGIndex.lie d).Group, β ∈ innAutDerived _ → β ^ 3 = 1 → β ≠ 1 →
      HasA8Comp β → I2017LieA8Shape d.1

@[expose] def OutA8 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
    Finite (TauCeti.CFSGIndex.lie d).Group → IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group →
    ∀ β : MulAut (TauCeti.CFSGIndex.lie d).Group, β ∉ innAutDerived _ → β ^ 3 = 1 →
      HasA8Comp β → I2017LieA8Shape d.1

private theorem eq_one_of_central_diff {K : Type} [Group K] (hK : commutator K = ⊤)
    (φ : MulAut K) (h : ∀ k : K, φ k * k⁻¹ ∈ Subgroup.center K) : φ = 1 := by
  let lam : K →* Subgroup.center K :=
    { toFun := fun k => ⟨φ k * k⁻¹, h k⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := Subgroup.mem_center_iff.1 (h b)
        show φ (a * b) * (a * b)⁻¹ = (φ a * a⁻¹) * (φ b * b⁻¹)
        calc φ (a * b) * (a * b)⁻¹ = φ a * ((φ b * b⁻¹) * a⁻¹) := by rw [map_mul]; group
          _ = φ a * (a⁻¹ * (φ b * b⁻¹)) := by rw [← hb a⁻¹]
          _ = (φ a * a⁻¹) * (φ b * b⁻¹) := by group }
  have hker : commutator K ≤ lam.ker := Abelianization.commutator_subset_ker lam
  rw [hK] at hker
  ext k
  have h1 : lam k = 1 := hker (Subgroup.mem_top k)
  have h2 : φ k * k⁻¹ = 1 := congrArg Subtype.val h1
  show φ k = k
  exact mul_inv_eq_one.1 h2

private theorem characteristic_prime (d : TauCeti.LieTypeIndex) : d.characteristic.Prime := by
  cases d <;> simp <;>
    first | exact ‹TauCeti.PrimePower›.prime_p | exact Nat.prime_two | exact Nat.prime_three

private theorem nonempty_quotCenter_alt8 {X : Type} [Group X]
    (f : X ≃* ↥(alternatingGroup (Fin 8))) :
    Nonempty (X ⧸ Subgroup.center X ≃* ↥(alternatingGroup (Fin 8))) := by
  have hA : Subgroup.center ↥(alternatingGroup (Fin 8)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
  have hX : Subgroup.center X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hfx : f x ∈ Subgroup.center ↥(alternatingGroup (Fin 8)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := f.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx z]
    rw [hA, Subgroup.mem_bot] at hfx
    rw [Subgroup.mem_bot]
    exact f.injective (by rw [hfx, map_one])
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hX).trans QuotientGroup.quotientBot).trans f⟩

private theorem card_alt (n : ℕ) (hn : 2 ≤ n) :
    Nat.card ↥(alternatingGroup (Fin n)) = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [nat_card_alternatingGroup, Nat.card_fin]

section Cert


theorem i2017LieClassification_of (hI : InnA8) (hO : OutA8) : I2017LieClassification := by
  intro Q _ _ hQ α J hα3 hα1 hJ hJ8 d hcat
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨idx, hidx, ⟨e⟩⟩ : ∃ idx : TauCeti.ValidLieTypeIndex, idx.1 = d ∧
      Nonempty (Q ⧸ Subgroup.center Q ≃* (TauCeti.CFSGIndex.lie idx).Group) := by
    obtain ⟨i, hi, he⟩ := hcat
    cases i
    case lie idx => exact ⟨idx, hi, he⟩
    all_goals exact (hi : False).elim
  subst hidx
  set T : Type := (TauCeti.CFSGIndex.lie idx).Group with hTdef
  haveI : Finite T := Finite.of_equiv _ e.toEquiv
  set Z := Subgroup.center Q with hZdef
  set ψ : Q →* T := e.toMonoidHom.comp (QuotientGroup.mk' Z) with hψdef
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hψker : ∀ x : Q, ψ x = 1 ↔ x ∈ Z := by
    intro x
    have h1 : ψ x = e (QuotientGroup.mk' Z x) := rfl
    rw [h1, e.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : ψ.ker ≤ Subgroup.center Q := fun x hx => (hψker x).1 hx
  set αb : MulAut (Q ⧸ Z) := QuotientGroup.congr Z Z α (Subgroup.map_center_eq α) with hαbdef
  set β : MulAut T := (e.symm.trans αb).trans e with hβdef
  have hαβ : ∀ k : Q, ψ (α k) = β (ψ k) := by
    intro k
    show e (QuotientGroup.mk' Z (α k)) = e (αb (e.symm (e (QuotientGroup.mk' Z k))))
    rw [e.symm_apply_apply]
    rfl
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hψs y
    have h1 : (α ^ 3) x = x := by rw [hα3]; rfl
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply] at h1
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, ← hαβ, ← hαβ, ← hαβ, h1,
      MulAut.one_apply]
  have hβ1 : β ≠ 1 := by
    intro hb
    apply hα1
    refine eq_one_of_central_diff hQ.1 α fun k => (hψker _).1 ?_
    rw [map_mul, map_inv, hαβ, hb, MulAut.one_apply, mul_inv_cancel]
  set J' : Subgroup T := J.map ψ with hJ'def
  have hJ' : GLAPComponent 3 (fixSubgroup β) J' :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup ψ hker α β hαβ hψs
      Nat.prime_three hJ
  obtain ⟨f8⟩ := hJ8
  obtain ⟨f8'⟩ := nonempty_quotCenter_alt8 f8
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map Nat.prime_three ψ hJ hJ'
  have eS : PSimple 3 J' ≃* ↥(alternatingGroup (Fin 8)) := eJ.symm.trans f8'
  have hsimp : IsSimpleGroup T := e.isSimpleGroup_congr.1 hQ.2
  have hna : ∃ a b : T, a * b ≠ b * a :=
    CFSG.LocalAnalysis.GLTheoremA.exists_mul_ne_mul_of_glaPComponent Nat.prime_three hJ'
  have hfix : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub β = fixSubgroup β :=
    Subgroup.ext fun _ => Iff.rfl
  have hchar : idx.1.characteristic = 2 := by
    have hLC := (CFSG.LocalAnalysis.GLTheoremA.lieComp_holds T hsimp hna idx ⟨MulEquiv.refl _⟩ β hβ3
      J' (hfix ▸ hJ')).1.chev
    rw [CFSG.HardMathSupport.Solomon.Coordinator.YS08.lieIndexChar_eq_characteristic] at hLC
    by_contra h2
    exact CFSG.LocalAnalysis.GLTheoremA.up7a8_not_chev_alt8_odd (characteristic_prime idx.1) h2 eS hLC
  have hpil := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent T hsimp hna
    idx ⟨MulEquiv.refl _⟩ 3 Nat.prime_three (by norm_num) (by rw [hchar]; norm_num) β hβ3 hβ1
  have hJle : J' ≤ GLALayer (fixSubgroup β) := hpil J' hJ'.1 (glaPComponent_perfect hJ')
  have hcomp : IsComponentOf J' (fixSubgroup β) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ' hJle).1
  have hJ'q : CFSG.Open.IsQuasisimple ↥J' := hcomp.2.2
  have eC : ↥J' ⧸ Subgroup.center ↥J' ≃* ↥(alternatingGroup (Fin 8)) :=
    (CFSG.LocalAnalysis.GLTheoremA.S171.chevIso' Nat.prime_three hJ' hJ'q).trans eS
  have hA8 : HasA8Comp β := ⟨J', hJ', hcomp, ⟨eC⟩⟩
  by_cases hmem : β ∈ innAutDerived T
  ·
    refine hI idx ?_ inferInstance hsimp β hmem hβ3 hβ1 hA8
    have hCI : KD264Lie.CompIdxAt 3 idx.1 T :=
      KD264Lie.lieCompIdx_all idx 3 Nat.prime_three (by norm_num) (by rw [hchar]; norm_num) trivial
    obtain ⟨i, ⟨g⟩, hrel⟩ := hCI β hmem hβ3 hβ1 J' hcomp
    have g8 : ↥(alternatingGroup (Fin 8)) ≃* i.Group := eC.symm.trans g
    cases i
    case lie e' =>
      exact ((CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts4.inputAltNotLie_holds 8 e'
        (by norm_num)).false g8).elim
    case alternating n hn =>
      rcases hrel with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, h2⟩
      · have hcard : Nat.card ↥(alternatingGroup (Fin 8)) = Nat.card ↥(alternatingGroup (Fin 5)) :=
          Nat.card_congr g8.toEquiv
        rw [card_alt 8 (by norm_num), card_alt 5 (by norm_num)] at hcard
        exact absurd hcard (by norm_num [Nat.factorial])
      · have hcard : Nat.card ↥(alternatingGroup (Fin 8)) = Nat.card ↥(alternatingGroup (Fin 6)) :=
          Nat.card_congr g8.toEquiv
        rw [card_alt 8 (by norm_num), card_alt 6 (by norm_num)] at hcard
        exact absurd hcard (by norm_num [Nat.factorial])
      · exact h2
    all_goals exact (hrel : False).elim
  ·
    exact hO idx hchar inferInstance hsimp β hmem hβ3 hA8

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I2017Cls

end
