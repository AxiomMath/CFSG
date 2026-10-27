module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6KFacts
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313U
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Prelim
public import CFSG.LocalAnalysis.ComponentClassification.GMS78BenderLift
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_commutator_sup_inf_centralizer_of_odd {R A : Subgroup G}
    (hAR : A ≤ normalizer (R : Set G)) (hR : IsPGroup 2 R) (hA : Odd (Nat.card A)) :
    R ≤ ⁅R, A⁆ ⊔ R ⊓ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent R := hR.isNilpotent
  have hsolv : Group.IsSolvable R := inferInstance
  have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hA)
  have : Subgroup.Normalizes A R := ⟨hAR⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := R) (A := A) hsolv hcop
  have hcomm : (CFSG.commutatorAction (A := A) (G := R)).map R.subtype = ⁅R, A⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator R A hAR
  have hfix : CFSG.fixedPointSubgroup A R = (CFSG.subgroupCentralizerIn R A).subgroupOf R :=
    CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn R A hAR
  intro x hx
  have h1 : (⟨x, hx⟩ : R) ∈ CFSG.fixedPointSubgroup A R ⊔ CFSG.commutatorAction A R := by
    rw [hsup]
    exact Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem R.subtype h1
  rw [Subgroup.map_sup, hcomm, hfix, CFSG.subgroupCentralizerIn,
    Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h2
  rw [sup_comm]
  exact h2

omit [Finite G] in
theorem rightConjugate_le_centralizer {V X : Subgroup G} (hX : X ≤ centralizer (V : Set G))
    {n : G} (hn : n ∈ normalizer (V : Set G)) :
    rightConjugate X n ≤ centralizer (V : Set G) := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  rw [mem_centralizer_iff]
  intro v hv
  have hv' : n * v * n⁻¹ ∈ V := (mem_normalizer_iff.mp hn v).mp hv
  have hc := (mem_centralizer_iff.mp (hX hx)) _ hv'
  calc v * x = n⁻¹ * ((n * v * n⁻¹) * (n * x * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * x * n⁻¹) * (n * v * n⁻¹)) * n := by rw [hc]
    _ = x * v := by group

namespace Sec3

variable {L T : Subgroup G}

theorem centralizer_gmsV_le_normalizer
    (h : Sec3 G L T) (hF : Foundation) :
    centralizer (gmsV L T : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.T₀_ne_bot
  have ht1' : (t : G) ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
  have htt : (t : G) * t = 1 := by
    rw [← sq]
    exact (h.isElemAbelian_T₀ hF).2 t t.2
  intro c hc
  apply h.centralizer_le_normalizer_of_mem (mem_inf.mp t.2).2 ht1' htt
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp hc (t : G) (mem_sup_right t.2)).symm

theorem centralizer_gmsV_le_normalizer_conj
    (h : Sec3 G L T) (hF : Foundation) {n : G}
    (hn : n ∈ normalizer (gmsV L T : Set G)) :
    centralizer (gmsV L T : Set G) ≤ normalizer (rightConjugate L n : Set G) := by
  intro c hc
  have hc' : n * c * n⁻¹ ∈ centralizer (gmsV L T : Set G) := by
    have h1 := rightConjugate_le_centralizer (le_refl (centralizer (gmsV L T : Set G)))
      (inv_mem hn)
    have h2 : n * c * n⁻¹ ∈ rightConjugate (centralizer (gmsV L T : Set G)) n⁻¹ := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hc
    exact h1 h2
  have hcN := h.centralizer_gmsV_le_normalizer hF hc'
  rw [mem_normalizer_iff] at hcN ⊢
  intro x
  rw [mem_rightConjugate_iff, mem_rightConjugate_iff]
  have e : n * (c * x * c⁻¹) * n⁻¹ = (n * c * n⁻¹) * (n * x * n⁻¹) * (n * c * n⁻¹)⁻¹ := by group
  rw [e]
  exact hcN _

theorem centralizer_gmsV_le_normalizer_T₁
    (h : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) :
    centralizer (gmsV L T : Set G) ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := h.facts_of_psu3 hF hf e
  obtain ⟨k, hB⟩ := hX.borel
  have hZ := hX.oddCenter
  have hP := h.isSylowOf_T₁
  obtain ⟨-, hA₁card, -⟩ := sylow_of_psu3 hZ hf e hP
  obtain ⟨a, ha1⟩ : ∃ a : gmsA L T, a ≠ 1 := by
    refine Subgroup.ne_bot_iff_exists_ne_one.mp fun hbot => ?_
    have h1 : Nat.card (gmsA L T) = 1 := by rw [hbot, card_bot]
    have h2 : Nat.card (gmsA L T) = 2 ^ f := hA₁card
    have h3 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    omega
  have ha1' : (a : G) ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
  intro c hc
  have hcN : c ∈ normalizer (L : Set G) := h.centralizer_gmsV_le_normalizer hF hc
  have hP' : IsSylowOf 2 ((T ⊓ L).map (MulAut.conj c).toMonoidHom) L := by
    refine isSylowOf_of_card ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.mp hcN x).mp (hP.le hx)
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
        (MulAut.conj c).injective, hP.card_eq]
  have haP : (a : G) ∈ T ⊓ L := (mem_inf.mp a.2).1
  have haP' : (a : G) ∈ (T ⊓ L).map (MulAut.conj c).toMonoidHom := by
    refine ⟨a, haP, ?_⟩
    have hca := (mem_centralizer_iff.mp hc) (a : G) (mem_sup_left a.2)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hca, mul_inv_cancel_right]
  have heq := eq_of_mem_of_mem hZ hP hP' hB haP haP' ha1'
  rw [mem_normalizer_iff_map_conj_eq]
  exact heq.symm

theorem rightConjugate_gmsA_eq {q : ℕ} (h313 : Lemma313 L T q) {n : G}
    (hn : n ∈ normalizer (gmsV L T : Set G)) :
    rightConjugate (gmsA L T) n = gmsA L T := by
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (rightConjugate_card _ n).ge
  rw [mem_rightConjugate_iff] at hx
  have hxV : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ ∈ gmsV L T :=
    (mem_normalizer_iff.mp (inv_mem hn) _).mp (mem_sup_left hx)
  have h1 := h313.stronglyClosed _ hx n⁻¹ hxV
  simpa [mul_assoc] using h1

theorem rightConjugate_T₁_eq
    (h : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f)
    {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {n : G} (hn : n ∈ normalizer (gmsV L T : Set G)) :
    rightConjugate (T ⊓ L) n = T ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h313 := h.lemma313_of_psu3 hF hf e
  have hZ : Odd (Nat.card (center L)) := odd_card_center_of_psu3 h.hyp.standard.1.1 hf e
  obtain ⟨-, -, -, hCT, -⟩ := u3K_facts h hf e hKL hKo hKH
  set T₁ := T ⊓ L with hT₁def
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀def
  set A₁ := gmsA L T with hA₁def
  set V := gmsV L T with hVdef
  set I := L ⊔ centralizer (L : Set G) with hIdef
  have hP := h.isSylowOf_T₁
  have hT₁2 : IsPGroup 2 T₁ := hP.isPGroup
  have hKN : K ≤ normalizer (T₁ : Set G) := by
    have : K ≤ T₁ ⊔ K := le_sup_right
    rw [hKH] at this
    exact fun k hk => (mem_inf.mp (mem_inf.mp (this hk)).1).2
  have hKA : K ≤ centralizer (A₁ : Set G) := by
    have : K ≤ T₁ ⊔ K := le_sup_right
    rw [hKH] at this
    exact fun k hk => (mem_inf.mp (this hk)).2
  have hT₀L : T₀ ≤ centralizer (L : Set G) := inf_le_right
  have hKV : K ≤ centralizer (V : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ((Subgroup.le_centralizer_iff).mp hKA) ?_
    exact hT₀L.trans (Subgroup.centralizer_le hKL)
  have hT₁V : T₁ ≤ centralizer (V : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le inf_le_right ?_
    exact hT₀L.trans (Subgroup.centralizer_le inf_le_right)
  have hCN := h.centralizer_gmsV_le_normalizer hF
  have hCT₁ := h.centralizer_gmsV_le_normalizer_T₁ hF hf e
  set S := rightConjugate T₁ n with hSdef
  set K' := rightConjugate K n with hK'def
  have hSV : S ≤ centralizer (V : Set G) := rightConjugate_le_centralizer hT₁V hn
  have hK'V : K' ≤ centralizer (V : Set G) := rightConjugate_le_centralizer hKV hn
  have hS2 : IsPGroup 2 S := hT₁2.map _
  have hK'o : Odd (Nat.card K') := by rw [hK'def, rightConjugate_card]; exact hKo
  have hK'S : K' ≤ normalizer (S : Set G) := by
    intro k hk
    have hk' : n * k * n⁻¹ ∈ K := (mem_rightConjugate_iff K n k).mp hk
    rw [mem_normalizer_iff]
    intro s
    show s ∈ rightConjugate T₁ n ↔ k * s * k⁻¹ ∈ rightConjugate T₁ n
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff]
    have e₁ : n * (k * s * k⁻¹) * n⁻¹ = (n * k * n⁻¹) * (n * s * n⁻¹) * (n * k * n⁻¹)⁻¹ := by
      group
    rw [e₁]
    exact (mem_normalizer_iff.mp (hKN hk') _)
  have hSK : S ⊓ centralizer (K' : Set G) ≤ A₁ := by
    intro x hx
    have hxS : n * x * n⁻¹ ∈ T₁ := (mem_rightConjugate_iff T₁ n x).mp (mem_inf.mp hx).1
    have hxK : x ∈ centralizer (K' : Set G) := (mem_inf.mp hx).2
    have hx1 : n * x * n⁻¹ ∈ T₁ ⊓ centralizer (K : Set G) := by
      refine mem_inf.mpr ⟨hxS, mem_centralizer_iff.mpr fun k hk => ?_⟩
      have hk' : n⁻¹ * k * n ∈ K' := by
        show n⁻¹ * k * n ∈ rightConjugate K n
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using hk
      have hc := (mem_centralizer_iff.mp hxK) _ hk'
      calc k * (n * x * n⁻¹) = n * ((n⁻¹ * k * n) * x) * n⁻¹ := by group
        _ = n * (x * (n⁻¹ * k * n)) * n⁻¹ := by rw [hc]
        _ = n * x * n⁻¹ * k := by group
    have hx2 := hCT hx1
    have hx3 : x ∈ rightConjugate A₁ n := (mem_rightConjugate_iff A₁ n x).mpr hx2
    rwa [rightConjugate_gmsA_eq h313 hn] at hx3
  have hdec := le_commutator_sup_inf_centralizer_of_odd hK'S hS2 hK'o
  have hIN : ∀ x ∈ normalizer (L : Set G), x ∈ normalizer (I : Set G) := fun x hx =>
    mem_normalizer_sup hx (h.normalizer_le_normalizer_centralizer hx)
  have hEN : S ⊔ T₁ ≤ normalizer (L : Set G) :=
    sup_le (hSV.trans hCN) (hP.le.trans le_normalizer)
  have hET : S ⊔ T₁ ≤ normalizer (T₁ : Set G) := sup_le (hSV.trans hCT₁) le_normalizer
  have hE2 : IsPGroup 2 (S ⊔ T₁ : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hS2 hT₁2 (hSV.trans hCT₁)
  have hEA : ∀ x ∈ S ⊔ T₁, ∀ a ∈ T₁ ⊓ centralizer (T₁ : Set G), x * a = a * x := by
    intro x hx a ha
    have hxV : x ∈ centralizer (V : Set G) := sup_le hSV hT₁V hx
    exact ((mem_centralizer_iff.mp hxV) a (mem_sup_left ha)).symm
  have houter : ∀ {x₁ x₂ : G}, x₁ ∈ S ⊔ T₁ → x₂ ∈ S ⊔ T₁ → x₁ ∉ I → x₂ ∉ I → x₁ * x₂ ∈ I :=
    fun h₁ h₂ h₁I h₂I => mul_mem_sup_of_psu3 h.hyp.standard.1.1 hZ hf e hP hE2 hEN
      (fun x hx p hp => (mem_normalizer_iff.mp (hET hx) p).mp hp) hEA le_sup_right h₁ h₂ h₁I h₂I
  have hcommI : ⁅S, K'⁆ ≤ I := by
    rw [commutator_le]
    intro s hs k hk
    have hkN : k ∈ normalizer (L : Set G) := hCN (hK'V hk)
    have hs' : k * s * k⁻¹ ∈ S := (mem_normalizer_iff.mp (hK'S hk) s).mp hs
    have hcomm : ⁅s, k⁆ = s * (k * s * k⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hcomm]
    by_cases hsI : s ∈ I
    · have h1 : k * s * k⁻¹ ∈ I := (mem_normalizer_iff.mp (hIN k hkN) s).mp hsI
      exact mul_mem hsI (inv_mem h1)
    · have h1 : (k * s * k⁻¹)⁻¹ ∉ I := by
        intro h1
        apply hsI
        have h2 := (mem_normalizer_iff.mp (hIN k hkN) s).mpr (by simpa using inv_mem h1)
        exact h2
      exact houter (mem_sup_left hs) (mem_sup_left (inv_mem hs')) hsI h1
  have hA₁L : A₁ ≤ L := inf_le_left.trans inf_le_right
  have hSI : S ≤ I := hdec.trans (sup_le hcommI (hSK.trans (hA₁L.trans le_sup_left)))
  have hLKN : I ≤ normalizer (L : Set G) := sup_le le_normalizer h.centralizer_le_normalizer
  have hWsyl : IsSylowOf 2 (T₁ ⊔ T₀) I := by
    have h1 := h.sylow.inf_of_le_normalizer hLKN hIN
    rwa [h.inf_sup_eq] at h1
  have hT₀T₁ : T₀ ≤ centralizer (T₁ : Set G) :=
    hT₀L.trans (Subgroup.centralizer_le inf_le_right)
  have hSnW : S ≤ normalizer ((T₁ ⊔ T₀ : Subgroup G) : Set G) := by
    intro x hx
    have hxT₀ : x ∈ centralizer (T₀ : Set G) :=
      Subgroup.centralizer_le (le_sup_right : T₀ ≤ V) (hSV hx)
    exact mem_normalizer_sup (hCT₁ (hSV hx)) (Subgroup.centralizer_le_normalizer _ hxT₀)
  have hSW2 : IsPGroup 2 (S ⊔ (T₁ ⊔ T₀) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hS2 hWsyl.isPGroup hSnW
  have heqW := hWsyl.eq_of_le le_sup_right (sup_le hSI hWsyl.le) hSW2
  have hSW : S ≤ T₁ ⊔ T₀ := heqW ▸ le_sup_left
  have hT₀N : T₀ ≤ normalizer (T₁ : Set G) := hT₀T₁.trans (Subgroup.centralizer_le_normalizer _)
  have hcommT₁ : ⁅S, K'⁆ ≤ T₁ := by
    rw [commutator_le]
    intro s hs k hk
    have hsW : s ∈ ((T₁ ⊔ T₀ : Subgroup G) : Set G) := hSW hs
    rw [coe_mul_of_right_le_normalizer_left T₁ T₀ hT₀N] at hsW
    obtain ⟨t₁, ht₁, t₀, ht₀, rfl⟩ := Set.mem_mul.mp hsW
    have hkt₀ : t₀ * k = k * t₀ := (mem_centralizer_iff.mp (hK'V hk)) t₀ (mem_sup_right ht₀)
    have hkN : k ∈ normalizer (T₁ : Set G) := hCT₁ (hK'V hk)
    have e₂ : ⁅t₁ * t₀, k⁆ = t₁ * (k * t₁⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      calc t₁ * t₀ * k * (t₁ * t₀)⁻¹ * k⁻¹ = t₁ * (t₀ * k) * t₀⁻¹ * t₁⁻¹ * k⁻¹ := by group
        _ = t₁ * (k * t₀) * t₀⁻¹ * t₁⁻¹ * k⁻¹ := by rw [hkt₀]
        _ = t₁ * (k * t₁⁻¹ * k⁻¹) := by group
    rw [e₂]
    exact mul_mem ht₁ ((mem_normalizer_iff.mp hkN _).mp (inv_mem ht₁))
  have hST₁ : S ≤ T₁ := hdec.trans (sup_le hcommT₁ (hSK.trans inf_le_left))
  exact Subgroup.eq_of_le_of_card_ge hST₁ (by rw [hSdef, rightConjugate_card])

end Sec3

end CFSG.ComponentClassification.GMS78
