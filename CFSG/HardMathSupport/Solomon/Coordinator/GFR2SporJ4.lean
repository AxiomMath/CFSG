module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporHat
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEQuasisimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4ThreeClass
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporRed

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.HardMathSupport.Timmesfeld.Tables.Census

private theorem isSubnormal_eq_or_le_center_j4 {X : Type*} [Group X] {A B : Subgroup X}
    (h : CFSG.Open.IsSubnormal A B) (hB : CFSG.IsQuasisimple ↥B) :
    A = B ∨ A ≤ (Subgroup.center ↥B).map B.subtype := by
  induction h with
  | refl A => exact Or.inl rfl
  | step hAM hn _ ih =>
    rename_i A M
    rcases ih hB with hMB | hM
    · subst hMB
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hB hn with h | h
      · exact Or.inl (le_antisymm hAM (Subgroup.subgroupOf_eq_top.mp h))
      · exact Or.inr fun x hx => ⟨⟨x, hAM hx⟩, h hx, rfl⟩
    · exact Or.inr (hAM.trans hM)

private theorem eq_bot_of_perfect_of_le_center_j4 {X : Type*} [Group X] {A B : Subgroup X}
    (hA : ⁅A, A⁆ = A) (h : A ≤ (Subgroup.center ↥B).map B.subtype) : A = ⊥ := by
  have hcomm : ⁅A, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨z, hz, rfl⟩ := h ha
    obtain ⟨w, -, rfl⟩ := h hb
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz w)
  rw [← hA, hcomm]

private theorem eq_of_isSubnormal_of_perfect_j4 {X : Type*} [Group X] {A B : Subgroup X}
    (hB : CFSG.IsQuasisimple ↥B) (h : CFSG.Open.IsSubnormal A B) (hA : ⁅A, A⁆ = A)
    (hne : A ≠ ⊥) : A = B := by
  rcases isSubnormal_eq_or_le_center_j4 h hB with h1 | h1
  · exact h1
  · exact absurd (eq_bot_of_perfect_of_le_center_j4 hA h1) hne

private theorem card_GLAPPrimeCoreOf_le_card_center_j4 {X : Type*} [Group X] [Finite X]
    {C : Subgroup X} {p : ℕ} (hp : p.Prime) (hC : CFSG.IsQuasisimple ↥C) (hpC : p ∣ Nat.card C) :
    Nat.card (GLAPPrimeCoreOf p C) ≤ Nat.card (Subgroup.center ↥C) := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hC (GLAPPrimeCore.normal p ↥C) with
    htop | hle
  · exfalso
    have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥C)) :=
      CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp ↥C
    rw [htop, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpC
  · unfold GLAPPrimeCoreOf
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact Subgroup.card_le_of_le hle

private theorem map_centralizer_mulEquiv_j4 {S M : Type*} [Group S] [Group M] (e : S ≃* M)
    (s : S) : (Subgroup.centralizer ({s} : Set S)).map e.toMonoidHom =
      Subgroup.centralizer ({e s} : Set M) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hy]

private theorem centralizer_facts_of_model_j4 {S G₀ : Type*} [Group S] [Group G₀]
    {H : Subgroup G₀} {c : ↥H} {N : ℕ} (e : S ≃* ↥H)
    (hconj : ∀ y : ↥H, orderOf y = 3 → ∃ k : ↥H, k * y * k⁻¹ = c)
    (hq : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({c} : Set ↥H)))
    (hz : Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({c} : Set ↥H))) = 6)
    (hc : Nat.card ↥(Subgroup.centralizer ({c} : Set ↥H)) = N) {s : S} (hs : orderOf s = 3) :
    CFSG.IsQuasisimple ↥(Subgroup.centralizer ({s} : Set S)) ∧
      Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({s} : Set S))) = 6 ∧
      Nat.card ↥(Subgroup.centralizer ({s} : Set S)) = N := by
  obtain ⟨k, hk⟩ := hconj (e s) (by rw [MulEquiv.orderOf_eq]; exact hs)
  let φ : S ≃* ↥H := (MulAut.conj (e.symm k)).trans e
  have hφ : φ s = c := by
    rw [← hk]
    simp only [φ, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have hqs : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({φ s} : Set ↥H)) := hφ ▸ hq
  have hzs : Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({φ s} : Set ↥H))) = 6 := hφ ▸ hz
  have hcs : Nat.card ↥(Subgroup.centralizer ({φ s} : Set ↥H)) = N := hφ ▸ hc
  let ψ : ↥(Subgroup.centralizer ({s} : Set S)) ≃* ↥(Subgroup.centralizer ({φ s} : Set ↥H)) :=
    (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (map_centralizer_mulEquiv_j4 φ s))
  refine ⟨CFSG.IsQuasisimple.of_mulEquiv ψ hqs, ?_, ?_⟩
  · rw [← hzs, ← Subgroup.map_center_eq ψ, Subgroup.card_map_of_injective ψ.injective]
  · rw [← hcs]
    exact Nat.card_congr ψ.toEquiv

section Centralizers


private theorem j4_centralizer_facts {S : Type*} [Group S] (e : S ≃* ↥CFSG.Sporadic.J4.J) {s : S}
    (hs : orderOf s = 3) :
    CFSG.IsQuasisimple ↥(Subgroup.centralizer ({s} : Set S)) ∧
      Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({s} : Set S))) = 6 ∧
      Nat.card ↥(Subgroup.centralizer ({s} : Set S)) = 2661120 := by
  obtain ⟨hq, hz, ⟨hm⟩⟩ := CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.centralizer_cE_quasisimple
    CFSG.Sporadic.J4.j4Facts
  refine centralizer_facts_of_model_j4 (H := CFSG.Sporadic.J4.J) (c := CFSG.Quasithin.J4M2.cE) e ?_
    hq hz ?_ hs
  · intro y hy
    refine CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.exists_conj_cE_of_orderThree y
      (hy ▸ pow_orderOf_eq_one y) ?_
    intro h1
    rw [h1, orderOf_one] at hy
    exact absurd hy (by norm_num)
  · have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} : Set ↥CFSG.Sporadic.J4.J)))
    rw [Nat.card_congr hm.toEquiv, CFSG.Sporadic.Mathieu.card_M22, hz] at h
    omega

end Centralizers

theorem sporNoPumpup_J4
    (hSpM : SporadicMultipliers) (hOG : UniquenessMaximal.InputONGroup)
    (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) : SporNoPumpup .J4 := by
  intro Y _ _ hq _hKg hcore ⟨e⟩ x hxo J₁ hJ₁ hty
  have hcen : Subgroup.center Y = ⊥ :=
    center_eq_bot_of_not_three_dvd hSpM (by decide) hq hcore e
  obtain ⟨s, hs3, hs⟩ := hatCfg_of_component hOut hq e hxo
  obtain ⟨-, hsub⟩ := hs J₁ hJ₁.2.1
  have h1080 := gfr2spor_card_ge hOG hty
  have hproj : Function.Injective (projOf e) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_projOf e, hcen])
  haveI : Finite (TauCeti.CFSGIndex.sporadic .J4).Group := Finite.of_equiv _ e.toEquiv
  let φ : (TauCeti.CFSGIndex.sporadic .J4).Group ≃* ↥CFSG.Sporadic.J4.J :=
    ((hbr .J4).some).symm.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  obtain ⟨hqC, hzC, hcC⟩ := j4_centralizer_facts φ hs3
  have hcardJ : Nat.card (J₁.map (projOf e)) = Nat.card J₁ :=
    Subgroup.card_map_of_injective hproj
  have hperf : ⁅J₁, J₁⁆ = J₁ := glaPComponent_perfect hJ₁
  have hperf' : ⁅J₁.map (projOf e), J₁.map (projOf e)⁆ = J₁.map (projOf e) := by
    rw [← Subgroup.map_commutator, hperf]
  have hne : J₁.map (projOf e) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardJ
    omega
  have hIC := eq_of_isSubnormal_of_perfect_j4 hqC hsub hperf' hne
  have hJcard : Nat.card J₁ = 2661120 := by rw [← hcardJ, hIC, hcC]
  have h3C : 3 ∣ Nat.card (Subgroup.centralizer
      ({s} : Set (TauCeti.CFSGIndex.sporadic .J4).Group)) := by
    rw [hcC]; norm_num
  have hO : Nat.card (GLAPPrimeCore 3 ↥J₁) ≤ 6 := by
    have h1 := card_GLAPPrimeCoreOf_le_card_center_j4 Nat.prime_three hqC h3C
    rw [hzC] at h1
    have h2 : Nat.card (GLAPPrimeCoreOf 3 J₁) =
        Nat.card (GLAPPrimeCoreOf 3 (J₁.map (projOf e))) := by
      rw [← map_glaPPrimeCoreOf_of_injective 3 (projOf e) hproj J₁,
        Subgroup.card_map_of_injective hproj]
    have h3 : Nat.card (GLAPPrimeCore 3 ↥J₁) = Nat.card (GLAPPrimeCoreOf 3 J₁) := by
      unfold GLAPPrimeCoreOf
      rw [Subgroup.card_map_of_injective J₁.subtype_injective]
    rw [h3, h2, hIC]
    exact h1
  have hmul : Nat.card J₁ = Nat.card (barOf 3 J₁) * Nat.card (GLAPPrimeCore 3 ↥J₁) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rcases hty with hON | hSix
  · have hbc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (barOf 3 J₁))
    rw [(UniquenessMaximal.isSimple_card_of_isHatON hOG hON).2, hON.2.1] at hbc
    unfold orderON at hbc
    have hdvd : Nat.card (barOf 3 J₁) ∣ Nat.card J₁ := Subgroup.card_quotient_dvd_card _
    have := Nat.le_of_dvd Nat.card_pos hdvd
    omega
  · have h6 := gfr2_card_isHatSix hSix
    rw [h6] at hmul
    omega

end CFSG.HardMathSupport.Solomon.Coordinator
