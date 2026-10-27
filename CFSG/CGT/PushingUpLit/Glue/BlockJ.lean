module

public import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
public import CFSG.CGT.PushingUpLit.BHS.BlockStatements
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Glue.ClassXBasic

public section

namespace CFSG.CGT.PushingUpLit.Glue

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem oTwoIn_eq_pCoreOf' (E : Subgroup Γ) : oTwoIn E = CFSG.Open.pCoreOf 2 E := by
  unfold oTwoIn CFSG.Open.pCoreOf inSubgroup
  show Subgroup.map E.subtype (CFSG.pCore 2 ↥E) = Subgroup.map E.subtype (CFSG.Open.pCore 2 ↥E)
  try with_reducible rfl

theorem conj_mem_centralizer {W : Subgroup Γ} {g x : Γ} (hg : g ∈ Subgroup.normalizer (W : Set Γ))
    (hx : x ∈ Subgroup.centralizer (W : Set Γ)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (W : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  have hy' : g⁻¹ * y * g ∈ W := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) y).1 hy
    simpa using this
  have h1 := hx _ hy'
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * y := by group

variable [Finite Γ]

theorem commutator_thompsonJ_eq {G T E : Subgroup Γ} (hE : BHS.IsBTBlock G T E)
    (hX : InClassX ↥E) (hT2 : IsPGroup 2 T) (hWT : oTwoIn E ≤ T) :
    CFSG.Quasithin.thompsonJ T ≤ Subgroup.normalizer (E : Set Γ) ∧
      ⁅E, CFSG.Quasithin.thompsonJ T⁆ = E := by
  have hW : oTwoIn E = CFSG.Open.pCoreOf 2 E := oTwoIn_eq_pCoreOf' E
  have hab : ∀ x ∈ oTwoIn E, ∀ y ∈ oTwoIn E, x * y = y * x := by
    rw [hW]
    exact hE.elemAbelian.1
  have hexp : ∀ x ∈ oTwoIn E, x ^ 2 = 1 := by
    rw [hW]
    exact hE.elemAbelian.2
  have hperf : ⁅oTwoIn E, E⁆ = oTwoIn E := by
    rw [hW]
    exact hE.perfect
  have hBn : CFSG.Quasithin.baum T ≤ Subgroup.normalizer (E : Set Γ) := by
    have := Subgroup.normalizer_commutator_ge_right E (CFSG.Quasithin.baum T)
    rwa [hE.commutator] at this
  have hIB : CFSG.Quasithin.thompsonJ T ≤ CFSG.Quasithin.baum T :=
    CFSG.Quasithin.B6.thompsonJ_le_baum T
  have hIn : CFSG.Quasithin.thompsonJ T ≤ Subgroup.normalizer (E : Set Γ) := hIB.trans hBn
  refine ⟨hIn, ?_⟩
  have hNX : ⁅E, CFSG.Quasithin.thompsonJ T⁆ ≤ E :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 hIn
  have hXN : E ≤ Subgroup.normalizer ((⁅E, CFSG.Quasithin.thompsonJ T⁆ : Subgroup Γ) : Set Γ) :=
    Subgroup.normalizer_commutator_ge_left E _
  rcases inClassX_normal_le_or_sup hX hNX hXN with h1 | h1
  · exfalso
    have hWne : oTwoIn E ≠ ⊥ := fun h => blockU_ne_bot_of_short hX.1 (hperf.trans h)
    have hc : ∀ i ∈ CFSG.Quasithin.thompsonJ T, ∀ e ∈ E, i * e * i⁻¹ * e⁻¹ ∈ oTwoIn E := by
      intro i hi e he
      have : ⁅i, e⁆ ∈ ⁅E, CFSG.Quasithin.thompsonJ T⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hi he
      exact h1 this
    have hcen := centralizes_oTwoIn_of_commutator_le hX.1 hab hperf
      (CFSG.QuasithinUnique.GammaExtra.isPGroup_thompsonJ hT2) hIn hc
    have hcomm : ∀ i ∈ CFSG.Quasithin.thompsonJ T, ∀ w ∈ oTwoIn E, i * w = w * i := by
      intro i hi w hw
      calc i * w = (i * w * i⁻¹) * i := by group
        _ = w * i := by rw [hcen i hi w hw]
    obtain ⟨A, hA⟩ := CFSG.QuasithinUnique.GammaExtra.exists_isMaxElemAbelian T
    have hAI : A ≤ CFSG.Quasithin.thompsonJ T := CFSG.QuasithinUnique.GammaExtra.le_thompsonJ hA
    have hAc : A ≤ Subgroup.centralizer (oTwoIn E : Set Γ) := fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun w hw => (hcomm a (hAI ha) w hw).symm
    have hWel : CFSG.Open.IsElemAbelian 2 (oTwoIn E) :=
      ⟨⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩, hexp⟩
    have hAel := CFSG.CGT.PushingUpLit.BHS.isElemAbelian_sup_of_le_centralizer hA.2.1 hWel hAc
    have hcard := hA.2.2 _ (sup_le hA.1 hWT) hAel
    have heq : A = A ⊔ oTwoIn E := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
    have hWA : oTwoIn E ≤ A := le_sup_right.trans heq.symm.le
    have hWI : oTwoIn E ≤ CFSG.Quasithin.thompsonJ T := hWA.trans hAI
    have hWΩ : oTwoIn E ≤ CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T) := by
      intro w hw
      refine Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨hWI hw, ?_⟩, hexp w hw⟩
      exact Subgroup.mem_centralizer_iff.2 fun y hy => hcomm y hy w hw
    have hBc : ∀ b ∈ CFSG.Quasithin.baum T, ∀ w ∈ oTwoIn E, b * w = w * b := by
      intro b hb w hw
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 w (hWΩ hw)).symm
    have hCE : E ⊓ Subgroup.centralizer (oTwoIn E : Set Γ) ≤ oTwoIn E := by
      have hnorm : E ≤ Subgroup.normalizer ((E ⊓ Subgroup.centralizer (oTwoIn E : Set Γ) :
          Subgroup Γ) : Set Γ) := by
        intro g hg
        have hgW : g ∈ Subgroup.normalizer (oTwoIn E : Set Γ) :=
          normalizer_le_normalizer_oTwoIn E (Subgroup.le_normalizer hg)
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · rintro ⟨hxE, hxC⟩
          exact ⟨E.mul_mem (E.mul_mem hg hxE) (E.inv_mem hg), conj_mem_centralizer hgW hxC⟩
        · rintro ⟨hxE, hxC⟩
          have hx1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
          refine ⟨?_, ?_⟩
          · have := E.mul_mem (E.mul_mem (E.inv_mem hg) hxE) hg
            rwa [hx1] at this
          · have := conj_mem_centralizer (inv_mem hgW) hxC
            rw [inv_inv] at this
            rwa [hx1] at this
      rcases inClassX_normal_le_or_sup hX inf_le_left hnorm with h2 | h2
      · exact h2
      · exfalso
        have hWle : oTwoIn E ≤ E ⊓ Subgroup.centralizer (oTwoIn E : Set Γ) :=
          le_inf (oTwoIn_le E) fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => hab y hy x hx
        have hN : E ⊓ Subgroup.centralizer (oTwoIn E : Set Γ) = E := by
          rwa [sup_eq_left.2 hWle] at h2
        have hEC : E ≤ Subgroup.centralizer (oTwoIn E : Set Γ) := fun x hx =>
          (Subgroup.mem_inf.1 (hN.symm ▸ hx : x ∈ E ⊓ Subgroup.centralizer (oTwoIn E : Set Γ))).2
        apply hWne
        rw [← hperf, Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact fun w hw => Subgroup.mem_centralizer_iff.2 fun e he =>
          (Subgroup.mem_centralizer_iff.1 (hEC he) w hw).symm
    have hEB : ⁅E, CFSG.Quasithin.baum T⁆ ≤ oTwoIn E := by
      refine Subgroup.commutator_le.2 fun e he b hb => ?_
      have hbe : b * e⁻¹ * b⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (hBn hb) e⁻¹).1 (E.inv_mem he)
      have hc1 : ⁅e, b⁆ ∈ E := by
        have : ⁅e, b⁆ = e * (b * e⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
        rw [this]
        exact E.mul_mem he hbe
      have hc2 : ⁅e, b⁆ ∈ Subgroup.centralizer (oTwoIn E : Set Γ) := by
        refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
        have hw' : e⁻¹ * w * e ∈ oTwoIn E := by
          simpa using conj_mem_oTwoIn (Subgroup.le_normalizer (E.inv_mem he)) hw
        have h3 := hBc b hb w hw
        have h4 := hBc b hb _ hw'
        rw [commutatorElement_def]
        have hwb : w * b⁻¹ = b⁻¹ * w :=
          calc w * b⁻¹ = b⁻¹ * (b * w) * b⁻¹ := by group
            _ = b⁻¹ * (w * b) * b⁻¹ := by rw [h3]
            _ = b⁻¹ * w := by group
        calc w * (e * b * e⁻¹ * b⁻¹)
            = e * ((e⁻¹ * w * e) * b) * e⁻¹ * b⁻¹ := by group
          _ = e * (b * (e⁻¹ * w * e)) * e⁻¹ * b⁻¹ := by rw [← h4]
          _ = e * b * e⁻¹ * (w * b⁻¹) := by group
          _ = e * b * e⁻¹ * (b⁻¹ * w) := by rw [hwb]
          _ = e * b * e⁻¹ * b⁻¹ * w := by group
      exact hCE ⟨hc1, hc2⟩
    have hEW : E ≤ oTwoIn E :=
      calc E = ⁅E, CFSG.Quasithin.baum T⁆ := hE.commutator.symm
        _ ≤ oTwoIn E := hEB
    exact isShortGroup_not_isPGroup hX.1 ((isPGroup_oTwoIn E).to_le hEW)
  · exact isShortGroup_eq_of_sup_oTwoIn hX.1 hNX hXN h1

end CFSG.CGT.PushingUpLit.Glue
