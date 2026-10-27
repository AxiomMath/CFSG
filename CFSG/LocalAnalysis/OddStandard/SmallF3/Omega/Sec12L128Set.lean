module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Alt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Cr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Nm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128SplB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Base

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec128_alt1_nat {t : G} {S L E X : Subgroup G} (hX : Sec12X t S L E X)
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))))
    (hV : CFSG.Open.IsElemAbelian 2 (secV t S L E)) :
    ∃ V1 V2 : Subgroup G, V1 ⊔ V2 = secV t S L E ∧ V1 ⊓ V2 = ⊥ ∧
      IsNatModA5 V1 ⊥ X ∧ IsNatModA5 V2 ⊥ X := by
  rcases hX.alt with ⟨-, V1, V2, hsup, hinf, hcase⟩ | ⟨hZ4, -⟩
  · rcases hcase with ⟨-, h1, h2⟩ | ⟨hS5, -, -⟩
    · exact ⟨V1, V2, hsup, hinf, h1, h2⟩
    · exact absurd hS5 (sec127_not_perm_iso hA5)
  · exact absurd hZ4 (sec127_not_isZ4Pow4 hV)

theorem sec128_natfix {V V1 V2 X : Subgroup G} {φ1 φ2 : (Fin 5 → ZMod 2) → G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (hsup : V1 ⊔ V2 = V) (hinf : V1 ⊓ V2 = ⊥)
    (hXN : X ≤ normalizer (V : Set G)) (hc1 : Sec127NatCoord V1 X φ1)
    (hc2 : Sec127NatCoord V2 X φ2) :
    ∀ u : ↥V, (∀ x ∈ autIn X V, x u = u) → u = 1 := by
  intro u hu
  have h1V : V1 ≤ V := le_trans le_sup_left hsup.le
  have h2V : V2 ≤ V := le_trans le_sup_right hsup.le
  obtain ⟨d1, hd1, d2, hd2, hd⟩ := sec127_mem_sup_mul hV h1V h2V (hsup.ge u.2)
  have hcen : ∀ h ∈ X, h * d1 * h⁻¹ = d1 ∧ h * d2 * h⁻¹ = d2 := by
    intro h hh
    have hfix : ((betaOf V h u : ↥V) : G) = u :=
      congrArg Subtype.val (hu _ (sec127_mem_autIn_iff.mpr ⟨h, hh, hXN hh, rfl⟩))
    rw [sec127_betaOf_apply (hXN hh)] at hfix
    have hn1 : h * d1 * h⁻¹ ∈ V1 :=
      (Subgroup.mem_normalizer_iff.mp (hc1.normalizes hh) d1).mp hd1
    have hn2 : h * d2 * h⁻¹ ∈ V2 :=
      (Subgroup.mem_normalizer_iff.mp (hc2.normalizes hh) d2).mp hd2
    have hconj : (h * d1 * h⁻¹) * (h * d2 * h⁻¹) = d1 * d2 := by
      calc (h * d1 * h⁻¹) * (h * d2 * h⁻¹) = h * (d1 * d2) * h⁻¹ := by group
        _ = h * (u : G) * h⁻¹ := by rw [hd]
        _ = u := hfix
        _ = d1 * d2 := hd.symm
    exact sec127_decomp_unique hinf hn1 hd1 hn2 hd2 hconj
  have hnat : ∀ (W : Subgroup G) (φ : (Fin 5 → ZMod 2) → G) (d : G), Sec127NatCoord W X φ →
      d ∈ W → (∀ h ∈ X, h * d * h⁻¹ = d) → d = 1 := by
    intro W φ d hc hd hfix
    obtain ⟨v, hv, rfl⟩ := hc.surj d hd
    have hv0 : v = 0 := by
      refine sec128_fixed_zero hv fun a => ?_
      obtain ⟨h, hh, hact⟩ := hc.onto (a : Equiv.Perm (Fin 5)) a.2
      have h1 := hfix h hh
      rw [hact v hv] at h1
      exact (hc.eq_iff (sec127_isEvenVec_permVec _ hv) hv).mp h1
    rw [hv0]
    exact hc.map_zero
  have e1 := hnat V1 φ1 d1 hc1 hd1 fun h hh => (hcen h hh).1
  have e2 := hnat V2 φ2 d2 hc2 hd2 fun h hh => (hcen h hh).2
  apply Subtype.ext
  rw [← hd, e1, e2, mul_one]
  rfl

theorem sec128_autIn_equiv {V X : Subgroup G} (hXN : X ≤ normalizer (V : Set G))
    (hbot : X ⊓ centralizer (V : Set G) = ⊥) : Nonempty (↥X ≃* ↥(autIn X V)) := by
  let f : ↥X →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hXN)
  have hf : ∀ x : ↥X, f x = betaOf V x.1 := fun x => (sec127_betaOf_of_mem (hXN x.2)).symm
  have hrange : autIn X V = f.range := by
    ext b
    rw [sec127_mem_autIn_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨n, hnX, hnN, rfl⟩
      exact ⟨⟨n, hnX⟩, hf ⟨n, hnX⟩⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, hXN x.2, hf x⟩
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hf] at hx
    have h2 := (sec127_betaOf_eq_one_iff (hXN x.2)).mp hx
    have h3 : x.1 ∈ X ⊓ centralizer (V : Set G) := Subgroup.mem_inf.mpr ⟨x.2, h2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.mpr (Subtype.ext h3)
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)⟩

theorem sec128_X_le_ML [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 E X : Subgroup G} (hctx : Sec12Ctx G t L S z K1 K2 E) (hX : Sec12X t S L E X)
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) : X ≤ secM t S L ⊓ L := by
  have hXle : X ≤ (secM t S L ⊓ L) ⊔ S := by
    have h1 : X ≤ X ⊔ secA t S L := le_sup_left
    rw [hX.sup] at h1
    exact h1
  exact sec127_le_of_alt5_sup hctx.sylow.2.1 (sec127_S_le_normalizer_ML hp hctx) hA5 hXle

theorem sec128_D_data [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 E X : Subgroup G} (hctx : Sec12Ctx G t L S z K1 K2 E) (hX : Sec12X t S L E X)
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) :
    ∃ (B X0 : Subgroup G) (φ₀ : (Fin 5 → ZMod 2) → G), B ≤ secM t S L ⊓ L ∧
      X0 ≤ secM t S L ⊓ L ∧ X0 ⊓ B = ⊥ ∧ Nonempty (↥X0 ≃* ↥(alternatingGroup (Fin 5))) ∧
      IsPermModuleVia IsEvenVec φ₀ B (secM t S L ⊓ L) (alternatingGroup (Fin 5)) ∧
      centralizer (B : Set G) ⊓ (secM t S L ⊓ L) = B := by
  obtain ⟨hBL, -, hCB, hAL, hML, φ, hperm, -⟩ :=
    sec10BData_of hp.basic hp.facts.b5 hctx.toSec10Z
  have hBD : secB S L ≤ secM t S L ⊓ L := by
    rw [hML]
    exact le_inf hBL Subgroup.le_normalizer
  have hBC : secB S L ≤ centralizer (secB S L : Set G) := by
    calc secB S L = centralizer (secB S L : Set G) ⊓ L := hCB.symm
      _ ≤ centralizer (secB S L : Set G) := inf_le_left
  have hBA : secB S L ≤ secA t S L := by
    calc secB S L = secA t S L ⊓ L := hAL.symm
      _ ≤ secA t S L := inf_le_left
  refine ⟨secB S L, X, φ, hBD, sec128_X_le_ML hp hctx hX hA5, ?_, hA5, ?_, ?_⟩
  · exact eq_bot_iff.mpr (le_trans (inf_le_inf_left X hBA) hX.inf.le)
  · rw [hML]
    exact hperm
  · refine le_antisymm ?_ (le_inf hBC hBD)
    calc centralizer (secB S L : Set G) ⊓ (secM t S L ⊓ L)
        ≤ centralizer (secB S L : Set G) ⊓ L := inf_le_inf_left _ inf_le_right
      _ = secB S L := hCB

end CFSG.OddStandard.SmallF3.Omega
