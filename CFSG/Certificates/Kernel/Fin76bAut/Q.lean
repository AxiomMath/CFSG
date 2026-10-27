module

public import CFSG.Certificates.Kernel.Fin76bAut.Pos
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EQDef

public section

universe u

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum
  CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.AutETable
  CFSG.EvenSporadicStandard.Fin76b.E69

section Q

variable {H : Type u} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)
  {ET T : ℕ → ℕ} {cnt : ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)
  {Φ : ℕ → MulAut H}

include hM in
theorem common_invol_of_checks (pd : PosData R T cnt Φ) (hc : eCtrK ET = true)
    {INN INE QC : ℕ → ℕ} (hinn : eInnK ET cnt T 16 INN INE = true)
    (hq : eQK cnt T 16 INN QC = true) :
    ∀ a ∈ (MulAut.conj : H →* MulAut H).range, ∀ b ∈ (MulAut.conj : H →* MulAut H).range,
      ∃ c : MulAut H, c ∉ (MulAut.conj : H →* MulAut H).range ∧ c * c = 1 ∧ c * a = a * c ∧
        c * b = b * c := by
  intro a ha b hb
  obtain ⟨u, hu, rfl⟩ := (inn_iff R hM pd hc hinn a).1 ha
  obtain ⟨v, hv, rfl⟩ := (inn_iff R hM pd hc hinn b).1 hb
  obtain ⟨hlt, hnot, hinv, hcu, hcv⟩ := eQK_spec hq u hu v hv
  have hC := pd.acts _ hlt
  have hU := pd.acts _ (eInnK_spec hinn u hu).1
  have hV := pd.acts _ (eInnK_spec hinn v hv).1
  refine ⟨Φ (QC (16 * u + v)), fun hm => ?_, hC.sq_iff.2 (eInvK_spec hinv).1,
    (hC.mul hU).ext (hU.mul hC) fun x _ => by rw [hcu],
    (hC.mul hV).ext (hV.mul hC) fun x _ => by rw [hcv]⟩
  obtain ⟨w, hw, e⟩ := (inn_iff R hM pd hc hinn _).1 hm
  exact hnot w hw (pd.inj _ (eInnK_spec hinn w hw).1 _ hlt e).symm

end Q

theorem eFactsQ_of_checks {G : Type u} [Group G] {E : Subgroup G} {t : G} {mulE : ℕ → ℕ → ℕ}
    {eltE : ℕ → G} {ET : ℕ → ℕ} (hL : ELabelling E t mulE 21 eltE)
    (hET : ∀ a < 32, ∀ b < 32, mulE a b = eMul ET a b) {T INN INE QC : ℕ → ℕ} {GN kg f c : ℕ}
    (hrec : RecOK.{u} ET 1920 T) (htup : eTupK ET GN kg f c = true)
    (hinn : eInnK ET 1920 T 16 INN INE = true) (hq : eQK 1920 T 16 INN QC = true) :
    EFactsQ E t := by
  obtain ⟨elt, R, -⟩ := realizes_of_labelling hL
  have hM : ∀ a < 32, ∀ b < 32, mt (tab2 32 mulE) a b = eMul ET a b := fun a ha b hb =>
    (mt_tab2 mulE ha hb).trans (hET a ha b hb)
  obtain ⟨Φ, pd⟩ := exists_posData R hM hrec
  exact ⟨common_invol_of_checks R hM pd (tup_ctr htup) hinn hq⟩

end CFSG.KS.EAut

end
