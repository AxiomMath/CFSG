module

public import CFSG.LocalAnalysis.GH72.GWForm
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteRankThree

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.GorensteinWalter (HasDihedralSylowTwo IsOddPrimePower)

theorem card_le_eight_of_mulAut_of_isL2OrA7
    {L : Type*} [Group L] {qmin : ℕ} (hq : 2 ≤ qmin)
    (h : IsL2OrA7 L qmin) (E : Subgroup (MulAut L)) (hE : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 8 := by
  rcases h with ⟨⟨e⟩⟩ | ⟨p, k, hp, hp2, hpk, ⟨e⟩⟩
  · set Ψ : MulAut L ≃* Equiv.Perm (Fin 7) :=
      (MulAut.congr e).trans CFSG.ComponentClassification.AutL2Facts.a7AutEquiv.symm
    rw [← Subgroup.card_map_of_injective (f := Ψ.toMonoidHom) Ψ.injective]
    apply CFSG.ComponentClassification.AutL2Facts.perm7_card_le_eight_of_sq
    rintro _ ⟨x, hx, rfl⟩
    change Ψ x * Ψ x = 1
    rw [← map_mul, hE x hx, map_one]
  · have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hpk
      omega
    have hF : IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hp.out, hp.out.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hk,
        GaloisField.card p k hk⟩
    let Ψ := CFSG.ComponentClassification.AutL2Facts.autEquiv e
    rw [← Subgroup.card_map_of_injective (f := Ψ.toMonoidHom) Ψ.injective]
    apply CFSG.ComponentClassification.AutL2Facts.pGammaL2_card_le_eight_of_sq hF
    rintro _ ⟨x, hx, rfl⟩
    change Ψ x * Ψ x = 1
    rw [← map_mul, hE x hx, map_one]

theorem card_le_eight_of_mulAut_of_mulEquiv_alternatingGroup_four {L : Type*} [Group L]
    (e : L ≃* alternatingGroup (Fin 4)) (E : Subgroup (MulAut L)) (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 8 := by
  let eA : Equiv.Perm (Fin 4) ≃* MulAut (alternatingGroup (Fin 4)) :=
    MulEquiv.ofBijective _ CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
  let Ψ : MulAut L →* Equiv.Perm (Fin 7) :=
    (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (by norm_num))).comp
      ((MulAut.congr e).trans eA.symm).toMonoidHom
  have hΨ : Function.Injective Ψ :=
    (Equiv.Perm.viaEmbeddingHom_injective _).comp (MulEquiv.injective _)
  rw [← Subgroup.card_map_of_injective hΨ]
  apply CFSG.ComponentClassification.AutL2Facts.perm7_card_le_eight_of_sq
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, hE x hx, map_one]

theorem card_le_of_inf_centralizer_eq_bot {X : Type*} [Group X] (F : Subgroup X) [F.Normal]
    (E : Subgroup X) (hEC : E ⊓ centralizer (F : Set X) = ⊥) (hE : ∀ e ∈ E, e * e = 1) {B : ℕ}
    (hB : ∀ E' : Subgroup (MulAut F), (∀ x ∈ E', x * x = 1) → Nat.card E' ≤ B) :
    Nat.card E ≤ B := by
  let φ : E →* MulAut F := (MulAut.conjNormal : X →* MulAut F).comp E.subtype
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxc : (x : X) ∈ centralizer (F : Set X) := by
      rw [mem_centralizer_iff]
      intro f hf
      have h := congrArg (fun ψ : MulAut F => ((ψ ⟨f, hf⟩ : F) : X)) hx
      simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
        MulAut.one_apply] at h
      calc f * x = (x : X) * f * (x : X)⁻¹ * x := by rw [h]
        _ = x * f := by group
    have : (x : X) ∈ E ⊓ centralizer (F : Set X) := ⟨x.2, hxc⟩
    rw [hEC, mem_bot] at this
    exact (mem_bot).2 (Subtype.ext this)
  rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
  refine hB _ ?_
  rintro _ ⟨x, rfl⟩
  rw [← map_mul, show x * x = 1 from Subtype.ext (hE x x.2), map_one]

theorem centralizer_le_centralizer_of_inf_centralizer_eq_bot {X : Type*} [Group X]
    {F K : Subgroup X} [F.Normal] [K.Normal] (hC : K ⊓ centralizer (F : Set X) = ⊥) :
    centralizer (F : Set X) ≤ centralizer (K : Set X) := by
  intro c hc
  rw [mem_centralizer_iff]
  intro k hk
  have hdK : c * k * c⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem (Normal.conj_mem inferInstance k hk c) (K.inv_mem hk)
  have hdC : c * k * c⁻¹ * k⁻¹ ∈ centralizer (F : Set X) := by
    have hc' : k * c⁻¹ * k⁻¹ ∈ centralizer (F : Set X) :=
      (normal_centralizer (H := F)).conj_mem _ (inv_mem hc) k
    have := mul_mem hc hc'
    rwa [← mul_assoc, ← mul_assoc] at this
  have hd : c * k * c⁻¹ * k⁻¹ ∈ K ⊓ centralizer (F : Set X) := ⟨hdK, hdC⟩
  rw [hC, mem_bot] at hd
  calc k * c = (c * k * c⁻¹ * k⁻¹)⁻¹ * (c * k) := by group
    _ = c * k := by rw [hd, inv_one, one_mul]

theorem gw_inf_centralizer_ne_bot
    {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal] (hO : CFSG.oddCore K = ⊥)
    (h2 : ∀ N : Subgroup K, N.Normal → N.index ≠ 2) (hD : HasDihedralSylowTwo K)
    (E : Subgroup X) (hE : ∀ e ∈ E, e * e = 1) (hcard : 8 < Nat.card E) :
    E ⊓ centralizer (K : Set X) ≠ ⊥ := by
  intro hEC
  rcases gw_alternatingGroup_four_or_commutator hO h2 hD with ⟨⟨e⟩⟩ | ⟨-, hF, hC⟩
  · exact absurd (card_le_of_inf_centralizer_eq_bot K E hEC hE
      (card_le_eight_of_mulAut_of_mulEquiv_alternatingGroup_four e)) (by omega)
  set F : Subgroup X := (commutator K).map K.subtype with hFdef
  haveI : F.Normal := ConjAct.normal_of_characteristic_of_normal
  have hKF : K ⊓ centralizer (F : Set X) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxC⟩
    have hx : (⟨x, hxK⟩ : K) ∈ centralizer (commutator K : Set K) := by
      rw [mem_centralizer_iff]
      intro f hf
      exact Subtype.ext (mem_centralizer_iff.mp hxC (f : X) ⟨f, hf, rfl⟩)
    rw [hC, mem_bot] at hx
    exact (mem_bot).2 (congrArg Subtype.val hx)
  have hEF : E ⊓ centralizer (F : Set X) = ⊥ := by
    rw [eq_bot_iff, ← hEC]
    exact inf_le_inf_left _ (centralizer_le_centralizer_of_inf_centralizer_eq_bot hKF)
  have hF' : IsL2OrA7 F 5 :=
    isL2OrA7_of_mulEquiv ((commutator K).equivMapOfInjective K.subtype K.subtype_injective).symm
      hF
  exact absurd (card_le_of_inf_centralizer_eq_bot F E hEF hE
    (card_le_eight_of_mulAut_of_isL2OrA7 (by norm_num) hF')) (by omega)

theorem gw_inf_centralizer_ne_bot_of_isE16
    {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal] (hO : CFSG.oddCore K = ⊥)
    (h2 : ∀ N : Subgroup K, N.Normal → N.index ≠ 2) (hD : HasDihedralSylowTwo K)
    {E : Subgroup X} (hE : IsE16 E) : E ⊓ centralizer (K : Set X) ≠ ⊥ :=
  gw_inf_centralizer_ne_bot K hO h2 hD E (fun e he => by rw [← pow_two]; exact hE.1.2 e he)
    (by rw [hE.2]; norm_num)

theorem gw_inf_centralizer_eq_bot
    {X : Type} [Group X] (K : Subgroup X) [Finite K] (hO : CFSG.oddCore K = ⊥)
    (h2 : ∀ N : Subgroup K, N.Normal → N.index ≠ 2) (hD : HasDihedralSylowTwo K) :
    K ⊓ centralizer (K : Set X) = ⊥ := by
  have hZ := gw_center_eq_bot hO h2 hD
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxC⟩
  have hx : (⟨x, hxK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (mem_centralizer_iff.mp hxC (k : X) k.2)
  rw [hZ, mem_bot] at hx
  exact (mem_bot).2 (congrArg Subtype.val hx)

end CFSG.GH72
