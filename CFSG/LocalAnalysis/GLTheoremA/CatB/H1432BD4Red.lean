module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432BD4Field
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432ClsRed
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432WitD4

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.BD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)


set_option linter.unusedSectionVars false

private theorem card_le_of_equiv (hInn : KDChevInner 3) (hN : BD4FieldNormalForm)
    {Q : Type} [Group Q] [Finite Q] {K I B : Subgroup Q} {y : Q} (hM : I1432Model K I y)
    (hIcard : Nat.card (PSimple 3 I) = 4952179814400) (hchev : IsChevSimple 3 (PSimple 3 K))
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set Q)) (hyB : y ∈ B)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 27)
    (e : PSimple 3 K ≃* ↥(adjointGroup Tag.D4 F)) :
    Nat.card B ≤ 3 ^ 9 * Nat.card ↥(B ⊓ centModSubgroup 3 K) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI := finite_modGL (τ := Tag.D4) (K := F)
  obtain ⟨hq, -, hyN, hy3, hIc, -⟩ := id hM
  have hyp := ClsRed.isPGroup_zpowers_three hy3
  have hJ := glaPComponent_chevTransfer hp hyN hyp hIc
  have hβ3 : chevAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hyN hy3
  have hβout : chevAut 3 K ⟨y, hyN⟩ ∉ inner (PSimple 3 K) := fun hin => by
    have hbot := hInn (PSimple 3 K) hq.2
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq) hchev _
      hβ3 (ClsRed.model_chevAut_ne_one hM) hin
    exact glaPComponent_ne_bot' hJ (le_bot_iff.1 (hbot ▸ le_sSup hJ))
  set α : MulAut ↥(adjointGroup Tag.D4 F) := MulAut.congr e (chevAut 3 K ⟨y, hyN⟩) with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hβ3, map_one]
  have hαout : α ∉ inner ↥(adjointGroup Tag.D4 F) := fun hin => by
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hin
    have h1 : MulAut.congr e (MulAut.conj (e.symm x)) = MulAut.conj x :=
      MulEquiv.ext fun z => by simp [MulAut.congr_apply, MulAut.conj_apply]
    exact hβout (MonoidHom.mem_range.2 ⟨e.symm x, (MulAut.congr e).injective (h1.trans hx)⟩)
  obtain ⟨hA, ⟨g₁⟩⟩ := chevQ_transport hp e hJ
  obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp hIc
  have hcard : Nat.card (PSimple 3 ((chevTransfer 3 K I).map e.toMonoidHom)) = 4952179814400 :=
    (Nat.card_congr (g.trans g₁).toEquiv).symm.trans hIcard
  set ρ : ↥B →* MulAut ↥(adjointGroup Tag.D4 F) :=
    (MulAut.congr e).toMonoidHom.comp ((chevAut 3 K).comp (Subgroup.inclusion hBN))
  have hρ1 : ∀ b : ↥B, ρ b = 1 ↔ (b : Q) ∈ centModSubgroup 3 K := fun b => by
    have h1 : ρ b = MulAut.congr e (chevAut 3 K ⟨b.1, hBN b.2⟩) := rfl
    rw [h1, MulEquiv.map_eq_one_iff, ClsRed.chevAut_eq_one_iff' hq (hBN b.2), centMod_iff]
  have hker : Nat.card ρ.ker = Nat.card ↥(B ⊓ centModSubgroup 3 K) :=
    Nat.card_congr
      { toFun := fun b =>
          ⟨b.1.1, Subgroup.mem_inf.2 ⟨b.1.2, (hρ1 b.1).1 (MonoidHom.mem_ker.1 b.2)⟩⟩
        invFun := fun b => ⟨⟨b.1, (Subgroup.mem_inf.1 b.2).1⟩, MonoidHom.mem_ker.2
          ((hρ1 ⟨b.1, (Subgroup.mem_inf.1 b.2).1⟩).2 (Subgroup.mem_inf.1 b.2).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcommB : ∀ a b : ↥B, a * b = b * a := fun a b => Subtype.ext (d3f_commute hB a.2 b.2)
  have hpowB : ∀ a : ↥B, a ^ 3 = 1 := fun a => Subtype.ext (hB.2 a.1 a.2)
  have hRE : IsElemAbelian 3 ρ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : MulAut ↥(adjointGroup Tag.D4 F)) * b = b * a
      rw [← hu, ← hw, ← map_mul, ← map_mul, hcommB]
    · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hz
      rw [← map_pow, hpowB, map_one]
  have hR := card_le_pow_nine_of_fieldNormalForm hN hF α hα3 hαout hA hcard hRE
    (MonoidHom.mem_range.2 ⟨⟨y, hyB⟩, rfl⟩)
  rw [← Subgroup.card_ker_mul_card_range ρ, hker]
  exact (mul_comm _ _).trans_le (Nat.mul_le_mul hR le_rfl)

theorem i1432BD4_of_fieldNormalForm (hb : LieOrderBridge) (hInn : KDChevInner 3)
    (hN : BD4FieldNormalForm) : I1432BD4 := by
  intro Q _ _ K I B y hM hI hK hB hBN hyB
  obtain ⟨q, hv, hq27, ⟨f⟩⟩ := WitD4.exists_D4_of_catalogIs hK
  have hp3 : q.p = 3 := by
    have h1 : q.p ∣ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    rw [hq27.trans (by norm_num : (27 : ℕ) = 3 ^ 3)] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 (q.prime_p.dvd_of_dvd_pow h1)
  have hchar : onLie (fun d => d.characteristic = 3) (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩) := by
    change (TauCeti.LieTypeIndex.D 4 q).characteristic = 3
    exact (TauCeti.LieTypeIndex.characteristic_D 4 q).trans hp3
  have hF : Nat.card (GaloisField 3 3) = 27 :=
    (GaloisField.card 3 3 (by norm_num)).trans (by norm_num)
  obtain ⟨φ⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_adjointQuotient_D4_equiv
    (GaloisField 3 3) q hv (hF.trans hq27.symm)
  have hZ := center_adjointGroup_eq_bot_field Tag.D4 (GaloisField 3 3)
  exact card_le_of_equiv hInn hN hM (ClsRed.card_d4three hb hI.1) (Or.inl ⟨_, hchar, ⟨f⟩⟩) hB
    hBN hyB hF (f.trans (φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot)))

end CFSG.LocalAnalysis.GLTheoremA.H1420.BD4

end
