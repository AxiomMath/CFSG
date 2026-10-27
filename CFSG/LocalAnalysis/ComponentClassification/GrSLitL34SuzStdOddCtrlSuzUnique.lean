module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma44SuzFourGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzEquiv
public import CFSG.GroupTheory.Commutator.RelIndexLeFour
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Sporadic.SuzOddCore

theorem le_of_isPerfect_of_centralizer_eq_sup {S : Type*} [Group S] [Finite S]
    {E H P : Subgroup S} {e : S} (he : e ∈ E) (hCE : centralizer (E : Set S) = H ⊔ E)
    (hHE : H ⊓ E = ⊥) (hHC : H ≤ centralizer (E : Set S))
    (hH : ⁅centralizer (E : Set S), centralizer (E : Set S)⁆ = H)
    (hcard : Nat.card (centralizer ({e} : Set S)) = 2 * (Nat.card H * Nat.card E))
    (hP : P ≤ centralizer ({e} : Set S)) (hPp : ⁅P, P⁆ = P) : P ≤ H := by
  have hCE_le : centralizer (E : Set S) ≤ centralizer ({e} : Set S) :=
    centralizer_le (by rintro y rfl; exact he)
  have hdisj : Disjoint H E := by
    rw [disjoint_iff_inf_le]
    exact le_of_eq hHE
  have hHnorm : H ≤ normalizer (E : Set S) :=
    hHC.trans (centralizer_le_normalizer E)
  have hcard_sup : Nat.card (centralizer (E : Set S)) = Nat.card H * Nat.card E := by
    rw [hCE, sup_comm,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E H hHnorm hdisj.symm,
      mul_comm]
  have hrel : (centralizer (E : Set S)).relIndex (centralizer ({e} : Set S)) = 2 := by
    have h := Subgroup.relIndex_mul_card
      (H := centralizer (E : Set S)) (K := centralizer ({e} : Set S))
    rw [inf_eq_left.mpr hCE_le, hcard, hcard_sup] at h
    have : Nonempty ↥H := ⟨1⟩
    have : Nonempty ↥E := ⟨1⟩
    have hpos : 0 < Nat.card H * Nat.card E := Nat.mul_pos Nat.card_pos Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h
  have hnorm_sub :
      ((centralizer (E : Set S)).subgroupOf (centralizer ({e} : Set S))).Normal := by
    apply Subgroup.normal_of_index_eq_two
    exact hrel
  have hnorm : centralizer ({e} : Set S) ≤
      Subgroup.normalizer (centralizer (E : Set S) : Set S) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hCE_le
  have hcomm : ⁅centralizer ({e} : Set S), centralizer ({e} : Set S)⁆ ≤
      centralizer (E : Set S) :=
    CFSG.GroupTheory.commutator_le_of_relIndex_le_four hnorm (by rw [hrel]; norm_num)
  have hP_CE : P ≤ centralizer (E : Set S) := by
    calc P = ⁅P, P⁆ := hPp.symm
      _ ≤ ⁅centralizer ({e} : Set S), centralizer ({e} : Set S)⁆ :=
        Subgroup.commutator_mono hP hP
      _ ≤ centralizer (E : Set S) := hcomm
  calc P = ⁅P, P⁆ := hPp.symm
    _ ≤ ⁅centralizer (E : Set S), centralizer (E : Set S)⁆ :=
      Subgroup.commutator_mono hP_CE hP_CE
    _ = H := hH

theorem exists_mulEquiv_suzM_apply_eq_suzInv_zero
    {S : Type} [Group S] (hS : Blueprint.NativeSporadic.IsSporadic S .Suz) {x : S}
    (hx : x * x = 1) (hxC : Nat.card (centralizer ({x} : Set S)) = 161280) :
    ∃ f : S ≃* ↥suzM, (f x : Equiv.Perm (Fin 1782)) = suzInv 0 := by
  obtain ⟨eS⟩ := hS
  let f₀ : S ≃* ↥suzM := eS.trans suzEquivM
  have hS_card : Nat.card S = 448345497600 := by
    rw [Nat.card_congr eS.toEquiv]
    change Nat.card (Blueprint.NativeSporadic.Suz) = 448345497600
    rw [Nat.card_congr suzEquivM.toEquiv, suzM_card]
  have hx_ne : x ≠ 1 := by
    intro hx1
    have htop : centralizer ({x} : Set S) = ⊤ := by
      rw [hx1]
      ext y
      simp [Subgroup.mem_centralizer_singleton_iff]
    have hcard : Nat.card S = 161280 := by
      rw [← Subgroup.card_top, ← htop, hxC]
    rw [hS_card] at hcard
    norm_num at hcard
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    exact hx
  have hxord : orderOf x = 2 := orderOf_eq_prime hx2 hx_ne
  have hdvd : 20160 ∣ Nat.card (centralizer ({x} : Set S)) := by
    rw [hxC]
    norm_num
  obtain ⟨Ψ, hΨinj, hΨmem, hΨsurj, hΨx⟩ :=
    CFSG.EvenSporadicStandard.Solomon78.suz_exists_model_aux f₀ x hxord hdvd
  let Ψ' : S →* ↥suzM := Ψ.codRestrict suzM hΨmem
  have hΨ'inj : Function.Injective Ψ' := by
    intro a b hab
    exact hΨinj (congrArg Subtype.val hab)
  have hΨ'surj : Function.Surjective Ψ' := by
    intro y
    obtain ⟨z, hz⟩ := hΨsurj y y.2
    exact ⟨z, Subtype.ext hz⟩
  let f : S ≃* ↥suzM := MulEquiv.ofBijective Ψ' ⟨hΨ'inj, hΨ'surj⟩
  refine ⟨f, ?_⟩
  change (Ψ' x : Equiv.Perm (Fin 1782)) = suzInv 0
  exact hΨx

theorem eq_of_perfect_of_card_eq_of_isSporadic_suz
    {S : Type} [Group S]
    (hS : Blueprint.NativeSporadic.IsSporadic S .Suz) {x : S} (hx : x * x = 1)
    (hxC : Nat.card (centralizer ({x} : Set S)) = 161280) {L₁ L₂ : Subgroup S}
    (h₁ : L₁ ≤ centralizer ({x} : Set S)) (h₂ : L₂ ≤ centralizer ({x} : Set S))
    (hp₁ : ⁅L₁, L₁⁆ = L₁) (hp₂ : ⁅L₂, L₂⁆ = L₂) (hc₁ : Nat.card L₁ = 20160)
    (hc₂ : Nat.card L₂ = 20160) : L₁ = L₂ := by
  let eS : S ≃* Blueprint.NativeSporadic.Carrier .Suz := hS.some
  have hS_card : Nat.card S = 448345497600 := by
    rw [Nat.card_congr eS.toEquiv]
    change Nat.card (Blueprint.NativeSporadic.Suz) = 448345497600
    rw [Nat.card_congr suzEquivM.toEquiv, suzM_card]
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [hS_card]; norm_num)
  have hSol := CFSG.EvenSporadicStandard.Solomon78.sol78Lemma44SuzFourGroup_holds
  rw [CFSG.EvenSporadicStandard.Solomon78.Sol78Lemma44SuzFourGroup] at hSol
  obtain ⟨E₀, H₀, n, hE₀card, hE₀sq, hE₀cent, hCE₀, hH₀E₀, hH₀C, hH₀comm, hH₀der,
    hH₀card, -, -, -, -⟩ := hSol S hS
  have hE₀_ne_bot : E₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hE₀card
    norm_num at hE₀card
  have hnt : Nontrivial E₀ := E₀.nontrivial_iff_ne_bot.mpr hE₀_ne_bot
  obtain ⟨e, heE₀, he_ne⟩ := @Subgroup.exists_ne_one_of_nontrivial _ _ E₀ hnt
  have he2 : e * e = 1 := by
    have := hE₀sq e heE₀
    simpa [pow_two] using this
  have heC : Nat.card (centralizer ({e} : Set S)) = 161280 :=
    hE₀cent e heE₀ he_ne
  obtain ⟨f₁, hf₁⟩ := exists_mulEquiv_suzM_apply_eq_suzInv_zero hS hx hxC
  obtain ⟨f₂, hf₂⟩ := exists_mulEquiv_suzM_apply_eq_suzInv_zero hS he2 heC
  let σ : S ≃* S := f₁.trans f₂.symm
  have hσx : σ x = e := by
    have h1 : f₁ x = f₂ e := by
      apply Subtype.ext
      rw [hf₁, hf₂]
    change f₂.symm (f₁ x) = e
    rw [h1, MulEquiv.symm_apply_apply]
  have hcardU : Nat.card (centralizer ({e} : Set S)) = 2 * (Nat.card H₀ * Nat.card E₀) := by
    rw [heC, hH₀card, hE₀card]
  have hL₁ : L₁.map σ.toMonoidHom ≤ H₀ := by
    refine le_of_isPerfect_of_centralizer_eq_sup (S := S) (E := E₀) (H := H₀)
      (P := L₁.map σ.toMonoidHom) (e := e) heE₀ hCE₀ hH₀E₀ hH₀C hH₀comm hcardU ?_ ?_
    · rintro y ⟨l, hl, rfl⟩
      have hlx : l ∈ centralizer ({x} : Set S) := h₁ hl
      rw [Subgroup.mem_centralizer_singleton_iff] at hlx ⊢
      rw [← hσx]
      simpa [map_mul] using congrArg σ hlx
    · rw [← Subgroup.map_commutator, hp₁]
  have hL₂ : L₂.map σ.toMonoidHom ≤ H₀ := by
    refine le_of_isPerfect_of_centralizer_eq_sup (S := S) (E := E₀) (H := H₀)
      (P := L₂.map σ.toMonoidHom) (e := e) heE₀ hCE₀ hH₀E₀ hH₀C hH₀comm hcardU ?_ ?_
    · rintro y ⟨l, hl, rfl⟩
      have hlx : l ∈ centralizer ({x} : Set S) := h₂ hl
      rw [Subgroup.mem_centralizer_singleton_iff] at hlx ⊢
      rw [← hσx]
      simpa [map_mul] using congrArg σ hlx
    · rw [← Subgroup.map_commutator, hp₂]
  have hcard_map₁ : Nat.card (L₁.map σ.toMonoidHom) = Nat.card H₀ := by
    rw [Subgroup.card_map_of_injective σ.injective, hc₁, hH₀card]
  have hcard_map₂ : Nat.card (L₂.map σ.toMonoidHom) = Nat.card H₀ := by
    rw [Subgroup.card_map_of_injective σ.injective, hc₂, hH₀card]
  have heq₁ : L₁.map σ.toMonoidHom = H₀ :=
    Subgroup.eq_of_le_of_card_ge hL₁ (by rw [hcard_map₁])
  have heq₂ : L₂.map σ.toMonoidHom = H₀ :=
    Subgroup.eq_of_le_of_card_ge hL₂ (by rw [hcard_map₂])
  have hmap : L₁.map σ.toMonoidHom = L₂.map σ.toMonoidHom := heq₁.trans heq₂.symm
  exact (Subgroup.map_injective σ.injective) hmap

end CFSG.ComponentClassification.GrSLit.L34Sec5S
