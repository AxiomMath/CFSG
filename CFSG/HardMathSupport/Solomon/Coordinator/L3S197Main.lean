module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3S197Het
public import CFSG.HardMathSupport.Solomon.Coordinator.L3S197L
public import CFSG.HardMathSupport.Solomon.Coordinator.L3S197U
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510ii
public import CFSG.HardMathSupport.Solomon.Coordinator.L3S197Cover

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma513Ns

section Generic

theorem exists_inner_ne_one {K : Type} [Group K] [Finite K] {D : Subgroup (MulAut K)}
    (hcard : Nat.card D = 9) (hle : D ≤ innerDiag K)
    (hidx : ((innerAut K).subgroupOf (innerDiag K)).index ≤ 3) :
    ∃ x : K, (MulAut.conj x : MulAut K) ∈ D ∧ (MulAut.conj x : MulAut K) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) (fun a b h => MulEquiv.ext (congrFun h))
  set I := (innerAut K).subgroupOf (innerDiag K) with hI
  let g : D → ↥(innerDiag K) ⧸ I := fun d => QuotientGroup.mk ⟨d.1, hle d.2⟩
  have hg : Function.Injective g := by
    intro d d' hdd
    have h1 := (QuotientGroup.eq).1 hdd
    rw [hI, Subgroup.mem_subgroupOf] at h1
    obtain ⟨x, hx⟩ := h1
    have hx' : (MulAut.conj x : MulAut K) = d.1⁻¹ * d'.1 := hx
    have hxD : (MulAut.conj x : MulAut K) ∈ D := by
      rw [hx']
      exact mul_mem (inv_mem d.2) d'.2
    have := hcon x hxD
    apply Subtype.ext
    have h2 : d.1⁻¹ * d'.1 = 1 := by rw [← hx']; exact this
    exact (inv_mul_eq_one.1 h2)
  have h3 := Nat.card_le_card_of_injective g hg
  have h4 : Nat.card (↥(innerDiag K) ⧸ I) ≤ 3 := hidx
  omega

theorem seitz_generic {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hT : IsExtremalType K ∨ IsSLThreeEps K) {π : Bool} {p f : ℕ} {F : Type} [Field F]
    (hF : PiField π p f F) (hmod : ModThree π (p ^ f)) (hq2 : π = false → 2 < p ^ f)
    {M : Type} [Group M]
    (η : (↥(slPi π 3 (p ^ f) F) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) F)) ≃* M)
    (P : PinnedAut M) (hP : GoodPinned P)
    (ε : (K ⧸ Subgroup.center K) ≃*
      (↥(slPi π 3 (p ^ f) F) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) F)))
    (hε : Subgroup.center K ≠ ⊥ → ∃ eK : K ≃* ↥(slPi π 3 (p ^ f) F), ε = barEquiv eK)
    (hconv : ∀ α : MulAut K, MulAut.congr (ε.trans η) (centerDescend K α) ∈ P.inndiag →
      α ∈ diagAut K)
    (model : ∀ D' H' : Subgroup (MulAut M), IsElemAbelian 3 D' → Nat.card D' = 9 →
      innerAut M ≤ H' → localDeltaIn 3 H' D' ≠ ⊥ →
        D' ≤ P.inndiag ∧ (∀ α ∈ P.inndiag, (∀ d ∈ D', α * d = d * α) → α ∈ D') ∧
          ∃ a b : ↥(glPi π 3 (p ^ f) F), lam hF η a ∈ D' ∧ lam hF η b ∈ D' ∧ a * b ≠ b * a)
    {D H : Subgroup (MulAut K)} (hD : IsEkIn 3 2 ⊤ D) (hH : innerAut K ≤ H)
    (hne : localDeltaIn 3 H D ≠ ⊥) :
    (D ≤ innerDiag K ∧ ∀ α ∈ innerDiag K, (∀ d ∈ D, α * d = d * α) → α ∈ D) ∧
      (∀ x : K, (MulAut.conj x : MulAut K) ≠ 1 → (MulAut.conj x : MulAut K) ∈ D → x ^ 3 = 1) ∧
      ∀ (Ŵ : Type) [Group Ŵ] (π' : Ŵ →* MulAut K) (ι : K →* Ŵ), IsThreeCover π' ι →
        π'.range = D ⊔ innerAut K → ∃ x ∈ D.comap π', ∃ y ∈ D.comap π', x * y ≠ y * x := by
  have hDab : IsElemAbelian 3 D := hD.2.1
  have hcard : Nat.card D = 9 := by rw [hD.2.2]; norm_num
  set ε' := ε.trans η with hε'
  set Ψ : MulAut K →* MulAut M := (MulAut.congr ε').toMonoidHom.comp (centerDescend K) with hΨ
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro α hα
    apply eq_one_of_centerDescend_eq_one hq
    exact (MulAut.congr ε').injective (by
      have : MulAut.congr ε' (centerDescend K α) = 1 := hα
      rw [this, map_one])
  have hΨconj : ∀ y : K, Ψ (MulAut.conj y) = MulAut.conj (ε' (QuotientGroup.mk y)) := by
    intro y
    simp only [hΨ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [CFSG.HardMathSupport.Solomon.Coordinator.centerDescend_conj, congr_mulAutConj]
  have hinn : innerAut M ≤ (innerAut K).map Ψ := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨z, rfl⟩ := ε'.surjective m
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨MulAut.conj y, ⟨y, rfl⟩, hΨconj y⟩
  have hD'ab : IsElemAbelian 3 (D.map Ψ) := LocalBalance.AutL3.isElemAbelian_map Ψ hDab
  have hcard' : Nat.card (D.map Ψ) = 9 := by
    rw [Subgroup.card_map_of_injective hΨinj, hcard]
  have hH' : innerAut M ≤ H.map Ψ := hinn.trans (Subgroup.map_mono hH)
  have hne' : localDeltaIn 3 (H.map Ψ) (D.map Ψ) ≠ ⊥ := by
    intro hb
    apply hne
    rw [eq_bot_iff]
    intro α hα
    have h1 := Timmesfeld.Coordinator.map_localDeltaIn_le 3 Ψ hΨinj H D ⟨α, hα, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact hΨinj (by rw [h1, map_one])
  obtain ⟨M1, M2, M3⟩ := model _ _ hD'ab hcard' hH' hne'
  have hA1 : D ≤ innerDiag K := fun d hd =>
    Subgroup.mem_sup_right (hconv d (M1 ⟨d, hd, rfl⟩))
  have hA2 : ∀ α ∈ innerDiag K, (∀ d ∈ D, α * d = d * α) → α ∈ D := by
    intro α hα hcomm
    have h1 : Ψ α ∈ P.inndiag := inndiag_of_mem_innerDiag hq ε' P hP hα
    have h2 : ∀ d' ∈ D.map Ψ, Ψ α * d' = d' * Ψ α := by
      rintro _ ⟨d, hd, rfl⟩
      rw [← map_mul, ← map_mul, hcomm d hd]
    obtain ⟨d, hd, hdα⟩ := M2 (Ψ α) h1 h2
    have : d = α := hΨinj hdα
    rw [← this]
    exact hd
  refine ⟨⟨hA1, hA2⟩, ?_⟩
  by_cases hZ : Subgroup.center K = ⊥
  · refine ⟨fun x _ hxD => ?_, fun Ŵ _ π' ι hc _ => ?_⟩
    · have h3 : (MulAut.conj x : MulAut K) ^ 3 = 1 := hDab.2 _ hxD
      have h4 : (MulAut.conj (x ^ 3) : MulAut K) = MulAut.conj 1 := by
        rw [map_pow, h3, map_one]
      have h5 := mem_center_of_conj_eq h4
      rw [hZ] at h5
      simpa using h5
    · exact (center_ne_bot_of_cover hc hZ).elim
  · obtain ⟨eK, hεeK⟩ := hε hZ
    set DG : Subgroup (MulAut ↥(slPi π 3 (p ^ f) F)) := D.map (MulAut.congr eK).toMonoidHom
      with hDG
    have hΨeq : ∀ v : MulAut K, Ψ v = psiG hF η (MulAut.congr eK v) := by
      intro v
      show MulAut.congr (ε.trans η) (centerDescend K v) = _
      rw [hεeK, congr_trans', congr_barEquiv]
      rfl
    have hmapΨ : DG.map (psiG hF η) = D.map Ψ := by
      rw [hDG, Subgroup.map_map]
      congr 1
      exact MonoidHom.ext fun v => (hΨeq v).symm
    have hDGab : IsElemAbelian 3 (DG.map (psiG hF η)) := by rw [hmapΨ]; exact hD'ab
    have hcardDG : Nat.card (DG.map (psiG hF η)) = 9 := by rw [hmapΨ]; exact hcard'
    have hnc : ∃ a b : ↥(glPi π 3 (p ^ f) F), lam hF η a ∈ DG.map (psiG hF η) ∧
        lam hF η b ∈ DG.map (psiG hF η) ∧ a * b ≠ b * a := by
      rw [hmapΨ]
      exact M3
    have het : ∀ x : K, (MulAut.conj x : MulAut K) ∈ D → (MulAut.conj x : MulAut K) ≠ 1 →
        ∃ v ∈ D, ∃ b : ↥(glPi π 3 (p ^ f) F), MulAut.congr eK v = cj hF b.2 ∧ v x ≠ x := by
      intro x hxD hx1
      have hcg : (MulAut.conj (eK x) : MulAut ↥(slPi π 3 (p ^ f) F)) =
          MulAut.congr eK (MulAut.conj x) := (congr_conj_eq eK x).symm
      obtain ⟨vG, hvG, b, hvb, hvGx⟩ := het_G hF hmod hq2 η hDGab hcardDG hnc (eK x)
        (by rw [hcg]; exact ⟨_, hxD, rfl⟩)
        (by
          rw [hcg]
          intro h
          apply hx1
          exact (MulAut.congr eK).injective (by rw [h, map_one]))
      obtain ⟨v, hv, rfl⟩ := hvG
      refine ⟨v, hv, b, hvb, fun hvx => hvGx ?_⟩
      show (MulAut.congr eK v) (eK x) = eK x
      simp [MulAut.congr_apply, hvx]
    refine ⟨fun x hx1 hxD => ?_, fun Ŵ _ π' ι hc hrange => ?_⟩
    · obtain ⟨v, hv, b, hvb, hvx⟩ := het x hxD hx1
      have hcomm : v * MulAut.conj x = MulAut.conj x * v := by
        have := hDab.1.is_comm.comm ⟨v, hv⟩ ⟨MulAut.conj x, hxD⟩
        exact congrArg Subtype.val this
      have h1 : (MulAut.conj (v x) : MulAut K) = MulAut.conj x := by
        rw [← mul_conj_mul_inv, hcomm, mul_inv_cancel_right]
      have hzc := mem_center_of_conj_eq h1
      have hz1 : x⁻¹ * v x ≠ 1 := fun h => hvx (by
        simpa using congrArg (fun y => x * y) h)
      have hzG : eK (x⁻¹ * v x) ∈ Subgroup.center ↥(slPi π 3 (p ^ f) F) := by
        have := Subgroup.map_center_eq eK
        rw [← this]
        exact ⟨_, hzc, rfl⟩
      have hzG1 : eK (x⁻¹ * v x) ≠ 1 := fun h => hz1 (eK.injective (by rw [h, map_one]))
      have hcj : cj hF b.2 (eK x) = eK x * eK (x⁻¹ * v x) := by
        rw [← hvb, MulAut.congr_apply]
        simp
      have h3 := cube_of_conj_central hF hmod (eK x) b hzG hzG1 hcj
      apply eK.injective
      rw [map_pow, h3, map_one]
    · obtain ⟨x, hxD, hx1⟩ := exists_inner_ne_one hcard hA1
        (LocalBalance.AutL3.inputInnDiagStructure_holds K hq hT).1
      obtain ⟨v, hv, -, -, hvx⟩ := het x hxD hx1
      exact exists_noncomm_of_cover hq.1 hc hrange hxD hv hvx

end Generic

theorem exists_model_K {K : Type} [Group K] (hq : CFSG.Open.IsQuasisimple K)
    (hT : IsExtremalType K ∨ IsSLThreeEps K) :
    ∃ (π : Bool) (p f : ℕ) (F : Type) (_ : Field F) (_ : PiField π p f F),
      ModThree π (p ^ f) ∧ (π = false → p ^ f ≠ 8) ∧ 2 < p ^ f ∧
        ∃ ε : (K ⧸ Subgroup.center K) ≃*
          (↥(slPi π 3 (p ^ f) F) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) F)),
          Subgroup.center K ≠ ⊥ → ∃ eK : K ≃* ↥(slPi π 3 (p ^ f) F), ε = barEquiv eK := by
  rcases model_of_type hq hT with ⟨π, p, f, F, _, hF, hmod, h8, h2, ⟨e⟩⟩ |
      ⟨π, p, f, F, _, hF, hmod, h8, h2, ⟨e⟩⟩
  · exact ⟨π, p, f, F, inferInstance, hF, hmod, h8, h2, barEquiv e, fun _ => ⟨e, rfl⟩⟩
  · have hGq : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ f) F) :=
      isQuasisimple_slPi hF (fun _ h => by omega)
    have hGp : Group.IsPerfect ↥(slPi π 3 (p ^ f) F) := (Group.isPerfect_def).2 hGq.1
    have hcQ : Subgroup.center (↥(slPi π 3 (p ^ f) F) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) F)) =
        ⊥ := Group.IsPerfect.center_quotient_center_eq_bot _
    have hZ : Subgroup.center K = ⊥ := center_eq_bot_of_mulEquiv_of_center_eq_bot e hcQ
    exact ⟨π, p, f, F, inferInstance, hF, hmod, h8, h2, (barEquivBot hZ).trans e,
      fun hne => absurd hZ hne⟩

section Models

variable {p f : ℕ} {F : Type} [Field F]

theorem lam_true (hF : PiField true p f F) (g : ↥(glPi true 3 (p ^ f) F)) :
    lam hF (etaTrue (p ^ f) F) g = conjAut 3 F (g : GL (Fin 3) F) :=
  congr_etaTrue_conj (p ^ f) (cj hF g.2) (fun _ => rfl)

theorem lam_false (hF : PiField false p f F) (hq2 : 2 < p ^ f) (g : ↥(glPi false 3 (p ^ f) F)) :
    lam hF (etaFalse hF hq2) g =
      psuConj hF.unitary ⟨g.1, mem_unitaryIsom3.2 ((mem_glPi_false hF.unitary).1 g.2)⟩ :=
  congr_eta_false_conj hF hq2 (cj hF g.2) g.2 (fun _ => rfl)

theorem model_true (hF : PiField true p f F) (hmod : ModThree true (p ^ f)) :
    ∀ D' H' : Subgroup (MulAut (projectiveSL 3 F)), IsElemAbelian 3 D' → Nat.card D' = 9 →
      innerAut (projectiveSL 3 F) ≤ H' → localDeltaIn 3 H' D' ≠ ⊥ →
        D' ≤ (stdPinnedPSL 3 F).inndiag ∧
          (∀ α ∈ (stdPinnedPSL 3 F).inndiag, (∀ d ∈ D', α * d = d * α) → α ∈ D') ∧
          ∃ a b : ↥(glPi true 3 (p ^ f) F), lam hF (etaTrue (p ^ f) F) a ∈ D' ∧
            lam hF (etaTrue (p ^ f) F) b ∈ D' ∧ a * b ≠ b * a := by
  intro D' H' hD hcard hH hne
  have := hF.finite
  have hF3 : 3 ∣ Nat.card F - 1 := by
    have h1 : Nat.card F = p ^ f := by simpa [piCard] using hF.card
    have h2 : p ^ f % 3 = 1 := hmod
    omega
  obtain ⟨M1, M2, A, B, hA, hB, hAB⟩ := seitz_model_L hF3 hD hcard hH hne
  rw [stdPinnedPSL_inndiag]
  refine ⟨M1, M2, ⟨A, mem_glPi_true _ A⟩, ⟨B, mem_glPi_true _ B⟩, ?_, ?_,
    fun h => hAB (congrArg Subtype.val h)⟩
  · rw [lam_true]
    exact hA
  · rw [lam_true]
    exact hB

theorem model_false (hF : PiField false p f F) (hq2 : 2 < p ^ f) (h8 : p ^ f ≠ 8)
    (hmod : ModThree false (p ^ f)) :
    ∀ D' H' : Subgroup (MulAut (unitaryPSU hF.unitary 3)), IsElemAbelian 3 D' →
      Nat.card D' = 9 → innerAut (unitaryPSU hF.unitary 3) ≤ H' → localDeltaIn 3 H' D' ≠ ⊥ →
        D' ≤ (stdPinnedPSU3 hF.unitary).inndiag ∧
          (∀ α ∈ (stdPinnedPSU3 hF.unitary).inndiag, (∀ d ∈ D', α * d = d * α) → α ∈ D') ∧
          ∃ a b : ↥(glPi false 3 (p ^ f) F), lam hF (etaFalse hF hq2) a ∈ D' ∧
            lam hF (etaFalse hF hq2) b ∈ D' ∧ a * b ≠ b * a := by
  intro D' H' hD hcard hH hne
  have hmod' : p ^ f % 3 = 2 := hmod
  obtain ⟨M1, M2, A, B, hA, hB, hAB⟩ := seitz_model_U hF.unitary hq2 h8 hmod' hD hcard hH hne
  refine ⟨M1, ?_, ⟨A.1, (mem_glPi_false hF.unitary).2 (mem_unitaryIsom3.1 A.2)⟩,
    ⟨B.1, (mem_glPi_false hF.unitary).2 (mem_unitaryIsom3.1 B.2)⟩, ?_, ?_, ?_⟩
  · rintro α ⟨C, rfl⟩ hcomm
    exact M2 C hcomm
  · rw [lam_false]
    exact hA
  · rw [lam_false]
    exact hB
  · intro h
    apply hAB
    apply Subtype.ext
    have h1 := congrArg (fun z : ↥(glPi false 3 (p ^ f) F) => (z : GL (Fin 3) F)) h
    exact h1

end Models

theorem input19_7_Seitz_holds : Lemma510iiNs.Input19_7_Seitz := by
  intro K _ _ hq _ hT D H hD hH _ hne
  obtain ⟨π, p, f, F, _, hF, hmod, h8, h2, ε, hε⟩ := exists_model_K hq hT
  have hfin := hF.finite
  cases π
  · exact seitz_generic hq hT hF hmod (fun _ => h2) (etaFalse hF h2) (stdPinnedPSU3 hF.unitary)
      (goodPinned_psu hF.unitary h2) ε hε
      (fun α hα => mem_diagAut_of_mem_psuConj_range hF.unitary (ε.trans (etaFalse hF h2)) hα)
      (model_false hF h2 (h8 rfl) hmod) hD hH hne
  · exact seitz_generic hq hT hF hmod (fun h => absurd h (by simp)) (etaTrue (p ^ f) F)
      (stdPinnedPSL 3 F) (goodPinned_psl F) ε hε
      (fun α hα => mem_diagAut_of_mem_linearAutGroup (ε.trans (etaTrue (p ^ f) F)) (by
        rw [← stdPinnedPSL_inndiag]; exact hα))
      (model_true hF hmod) hD hH hne


end CFSG.HardMathSupport.Solomon.Coordinator
