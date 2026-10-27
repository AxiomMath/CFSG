module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921AutPerm
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Asm

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)

section Rho

variable {X : Type} [Group X] [Finite X] (K : Subgroup X)

abbrev Kbar : Type := ↥K ⧸ Subgroup.center ↥K

@[expose] noncomputable def rhoK :
    ↥(Subgroup.normalizer (K : Set X)) →* MulAut (Kbar K) :=
  quotAutOfCentreHom.comp K.normalizerMonoidHom

theorem rhoK_mk (n : ↥(Subgroup.normalizer (K : Set X))) (k : ↥K) :
    rhoK K n (QuotientGroup.mk k) = QuotientGroup.mk (K.normalizerMonoidHom n k) :=
  quotAutOfCentre_mk _ _

variable {K}

theorem rhoK_eq_one_iff (hK : IsComponentOf K ⊤) {w : X}
    (hw : w ∈ Subgroup.normalizer (K : Set X)) :
    rhoK K ⟨w, hw⟩ = 1 ↔ w ∈ Subgroup.centralizer (K : Set X) := by
  rw [← normalizerMonoidHom_eq_one_iff hw]
  constructor
  · intro h
    refine eq_one_of_forall_mk_eq_aut hK.2.2.1 _ fun x => ?_
    have := congrArg (fun ψ : MulAut (Kbar K) => ψ (QuotientGroup.mk x)) h
    simpa [rhoK_mk] using this
  · intro h
    show quotAutOfCentreHom (K.normalizerMonoidHom ⟨w, hw⟩) = 1
    rw [h, map_one]

theorem center_Kbar (hK : IsComponentOf K ⊤) : Subgroup.center (Kbar K) = ⊥ := by
  haveI : IsSimpleGroup (Kbar K) := hK.2.2.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Kbar K)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := (isQuasisimple_of_comp hK).2.2
    have ha : a ∈ Subgroup.center (Kbar K) := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem conj_injective_of_center_bot (hZ : Subgroup.center (Kbar K) = ⊥) :
    Function.Injective (MulAut.conj : Kbar K →* MulAut (Kbar K)) := by
  intro a b h
  have h1 : ∀ x : Kbar K, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
    have := congrArg (fun φ : MulAut (Kbar K) => φ x) h
    simpa [MulAut.conj_apply] using this
  have hc : b⁻¹ * a ∈ Subgroup.center (Kbar K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h1 g]
      _ = b⁻¹ * a * g := by group
  rw [hZ] at hc
  exact (inv_mul_eq_one.1 (Subgroup.mem_bot.1 hc)).symm

theorem rhoK_conj (k : ↥K) :
    rhoK K ⟨(k : X), Subgroup.le_normalizer k.2⟩ = MulAut.conj (QuotientGroup.mk k : Kbar K) := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H a =>
    rw [rhoK_mk, rho_conj]
    simp [MulAut.conj_apply]

theorem quotAutOfCentreHom_conj (k : ↥K) :
    quotAutOfCentreHom (MulAut.conj k) = MulAut.conj (QuotientGroup.mk k : Kbar K) := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H a =>
    show quotAutOfCentre (MulAut.conj k) (QuotientGroup.mk a) = _
    rw [quotAutOfCentre_mk]
    simp [MulAut.conj_apply]

theorem mulAut_mul_conj_mul_inv {G : Type*} [Group G] (φ : MulAut G) (a : G) :
    φ * MulAut.conj a * φ⁻¹ = MulAut.conj (φ a) := by
  apply MulEquiv.ext
  intro y
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]

noncomputable abbrev Kinn (K : Subgroup X) : Subgroup (MulAut (Kbar K)) :=
  (MulAut.conj : Kbar K →* MulAut (Kbar K)).range

instance Kinn_normal (K : Subgroup X) : (Kinn K).Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ g
    refine ⟨g a, ?_⟩
    apply MulEquiv.ext
    intro y
    simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]

end Rho

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
