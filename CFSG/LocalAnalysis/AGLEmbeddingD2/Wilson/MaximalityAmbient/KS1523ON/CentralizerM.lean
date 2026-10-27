module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.NoIndex
public import CFSG.Sporadic.ONOddCore.LocalComp
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CF67SL34

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON

open Subgroup CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.ComponentClassification.PSL3Four
  CFSG.LocalAnalysis.ComponentInitial

theorem exists_surj_of_ker_le {A B S : Type*} [Group A] [Group B] [Group S] (π : A →* B)
    (f : A →* S) (hker : π.ker ≤ f.ker) (hf : Function.Surjective f) :
    ∃ g : π.range →* S, Function.Surjective g := by
  have hs : Function.Surjective π.rangeRestrict := MonoidHom.rangeRestrict_surjective π
  have hinv : Function.RightInverse (Function.surjInv hs) π.rangeRestrict :=
    Function.rightInverse_surjInv hs
  have hk : π.rangeRestrict.ker ≤ f.ker := by rwa [MonoidHom.ker_rangeRestrict]
  refine ⟨MonoidHom.liftOfRightInverse π.rangeRestrict (Function.surjInv hs) hinv ⟨f, hk⟩, ?_⟩
  have hcomp := MonoidHom.liftOfRightInverse_comp π.rangeRestrict (Function.surjInv hs) hinv
    ⟨f, hk⟩
  have : Function.Surjective ((MonoidHom.liftOfRightInverse π.rangeRestrict
      (Function.surjInv hs) hinv ⟨f, hk⟩).comp π.rangeRestrict) := by rw [hcomp]; exact hf
  exact Function.Surjective.of_comp this


section M

set_option linter.unusedSectionVars false


noncomputable def xrEquivS : XR ≃* CFSG.ComponentClassification.PSL3Four.S :=
  XREquiv.trans (thetaX.symm.trans theta)

theorem card_XR : Nat.card XR = 20160 := by
  rw [Nat.card_congr XREquiv.toEquiv, card_onX]

theorem xr_no_comm {g h : XR} (hgh : g * h = h * g) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hh5 : h ^ 5 = 1) (hh1 : h ≠ 1) : False := by
  have e3 : ((xrEquivS g : CFSG.ComponentClassification.PSL3Four.S) :
      Equiv.Perm (Fin 42)) ^ 3 = 1 := by
    have := congrArg (fun x => ((xrEquivS x : CFSG.ComponentClassification.PSL3Four.S) :
      Equiv.Perm (Fin 42))) hg3
    simpa using this
  have e5 : ((xrEquivS h : CFSG.ComponentClassification.PSL3Four.S) :
      Equiv.Perm (Fin 42)) ^ 5 = 1 := by
    have := congrArg (fun x => ((xrEquivS x : CFSG.ComponentClassification.PSL3Four.S) :
      Equiv.Perm (Fin 42))) hh5
    simpa using this
  refine CFSG.GH74.GLS.Stage2.Bender.Thm1.CF67S.S_no_comm (xrEquivS g).2 (xrEquivS h).2 ?_
    (Or.inl rfl) e3 ?_ e5 ?_
  · have := congrArg (fun x => ((xrEquivS x : CFSG.ComponentClassification.PSL3Four.S) :
      Equiv.Perm (Fin 42))) hgh
    simpa using this
  · intro h1
    apply hg1
    apply xrEquivS.injective
    exact Subtype.ext (by simpa using h1)
  · intro h1
    apply hh1
    apply xrEquivS.injective
    exact Subtype.ext (by simpa using h1)

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp
  decide

theorem no_surj_alt7_of_M {W : Type*} [Group W] [Finite W] (ψ : W →* onM)
    (hψ : Function.Injective ψ) (f : W →* alternatingGroup (Fin 7))
    (hf : Function.Surjective f) : False := by
  classical
  have hS : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let ρ : W →* RM := piR.comp ψ
  have hK0card : Nat.card ρ.ker ∣ 4 := by
    let κ : ρ.ker →* (onQ.subgroupOf onM) :=
      (ψ.comp ρ.ker.subtype).codRestrict (onQ.subgroupOf onM) (fun w => by
        have h : ψ w.1 ∈ piR.ker := MonoidHom.mem_ker.2 w.2
        rwa [ker_piR] at h)
    have hκ : Function.Injective κ := fun a b hab =>
      Subtype.ext (hψ (congrArg Subtype.val hab))
    rw [← card_onQ_subgroupOf_M]
    exact Subgroup.card_dvd_of_injective κ hκ
  have hK0p : IsPGroup 2 ρ.ker := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show Nat.card ρ.ker ∣ 2 ^ 2 by simpa using hK0card)
    exact IsPGroup.of_card hm
  have hfK0 : ρ.ker ≤ f.ker := by
    have hn : (ρ.ker.map f).Normal := Subgroup.Normal.map inferInstance f hf
    rcases hS.eq_bot_or_eq_top_of_normal (ρ.ker.map f) with h | h
    · intro w hw
      have : f w ∈ ρ.ker.map f := ⟨w, hw, rfl⟩
      rw [h] at this
      exact this
    · exfalso
      have h1 : Nat.card (alternatingGroup (Fin 7)) ∣ Nat.card ρ.ker := by
        have := Subgroup.card_map_dvd ρ.ker f
        rw [h, Subgroup.card_top] at this
        exact this
      rw [card_alt7] at h1
      have := h1.trans hK0card
      omega
  set W₁ : Subgroup W := XR.comap ρ with hW₁
  have hW₁n : W₁.Normal := inferInstance
  have hW₁i : W₁.index ∣ 2 := by
    rw [hW₁, Subgroup.index_comap]
    exact (Subgroup.relIndex_dvd_index_of_normal (H := XR) (K := ρ.range)).trans
      (by rw [XR_index])
  have hfW₁ : W₁.map f = ⊤ := by
    have hnm : (W₁.map f).Normal := Subgroup.Normal.map hW₁n f hf
    rcases hS.eq_bot_or_eq_top_of_normal (W₁.map f) with h | h
    · exfalso
      have hle : W₁ ≤ f.ker := by
        intro w hw
        have : f w ∈ W₁.map f := ⟨w, hw, rfl⟩
        rw [h] at this
        exact this
      have h1 : f.ker.index ∣ 2 := (Subgroup.index_dvd_of_le hle).trans hW₁i
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hf, Subgroup.card_top, card_alt7] at h1
      omega
    · exact h
  have hsurj : Function.Surjective (f.comp W₁.subtype) := by
    intro s
    have : s ∈ W₁.map f := by rw [hfW₁]; trivial
    obtain ⟨w, hw, rfl⟩ := this
    exact ⟨⟨w, hw⟩, rfl⟩
  let ι₁ : W₁ →* XR := (ρ.comp W₁.subtype).codRestrict XR (fun w => Subgroup.mem_comap.1 w.2)
  have hker : ι₁.ker ≤ (f.comp W₁.subtype).ker := by
    intro w hw
    have h1 : ρ w.1 = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hw)
      simpa [ι₁] using this
    exact hfK0 (MonoidHom.mem_ker.2 h1)
  obtain ⟨g, hg⟩ := exists_surj_of_ker_le ι₁ (f.comp W₁.subtype) hker hsurj
  have := XR_simple
  exact no_surj_from_group card_XR card_alt7 (fun a b hab h3 h1 h5 h1' => xr_no_comm hab h3 h1 h5 h1')
    ι₁.range.subtype (Subgroup.subtype_injective _) g hg

noncomputable def centralizerEquivM {T : Type} [Group T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.ON) {t : T} (ht : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set T) ≃* onM := by
  set f : T ≃* Pv := e.trans onEquivPv
  have hft : orderOf (f t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  exact (centralizerCongr f t).trans (Classical.choice (centralizer_P_equiv_M hft))

theorem no_surj_alt7_of_centralizer {T : Type} [Group T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.ON) {t : T} (ht : orderOf t = 2)
    {W : Type*} [Group W] [Finite W] (ψ : W →* T) (hψ : Function.Injective ψ)
    (hψC : ∀ w, ψ w ∈ Subgroup.centralizer ({t} : Set T))
    (f : W →* alternatingGroup (Fin 7)) (hf : Function.Surjective f) : False := by
  let ψ' : W →* Subgroup.centralizer ({t} : Set T) := ψ.codRestrict _ hψC
  have hψ' : Function.Injective ψ' := fun a b h => hψ (congrArg Subtype.val h)
  exact no_surj_alt7_of_M ((centralizerEquivM e ht).toMonoidHom.comp ψ')
    ((centralizerEquivM e ht).injective.comp hψ') f hf

theorem not_dvd_of_centralizer {T : Type} [Group T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.ON) {t : T} (ht : orderOf t = 2)
    {W : Type*} [Group W] [Finite W] (ψ : W →* T) (hψ : Function.Injective ψ)
    (hψC : ∀ w, ψ w ∈ Subgroup.centralizer ({t} : Set T))
    {S : Type*} [Group S] [Finite S] (f : W →* S) (hf : Function.Surjective f)
    (h19 : 19 ∣ Nat.card S) : False := by
  let ψ' : W →* Subgroup.centralizer ({t} : Set T) := ψ.codRestrict _ hψC
  have hψ' : Function.Injective ψ' := fun a b h => hψ (congrArg Subtype.val h)
  have h1 : Nat.card S ∣ Nat.card W := Subgroup.card_dvd_of_surjective hf
  have h2 : Nat.card W ∣ Nat.card (Subgroup.centralizer ({t} : Set T)) :=
    Subgroup.card_dvd_of_injective ψ' hψ'
  have h3 : Nat.card (Subgroup.centralizer ({t} : Set T)) = 161280 := by
    rw [Nat.card_congr (centralizerEquivM e ht).toEquiv]
    exact card_onM
  rw [h3] at h2
  have := (h19.trans h1).trans h2
  omega

end M

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON
