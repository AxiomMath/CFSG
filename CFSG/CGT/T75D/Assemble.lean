module

public import CFSG.CGT.T75D.LayerBound
public import CFSG.CGT.T75D.ActionKernel
public import CFSG.CGT.T75D.CardL
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGLayer
public import CFSG.CGT.Timmesfeld75.BenderInputs5
public import CFSG.CGT.Timmesfeld75.BenderInputs6

public section

namespace CFSG.CGT.T75D

open CFSG.Open CFSG.Goldschmidt CFSG.CGT.Timmesfeld75
open scoped commutatorElement

section Three

variable {G : Type} [Group G] {T U : Subgroup G}

theorem bar_comm_of_cfg (c : Cfg T U) {g y y' : NQuot T}
    (hy : y ∈ barSub T (normIn U T)) (hy1 : y ≠ 1) (hy' : y' ∈ barSub T (normIn U T))
    (hyy : y = g * y' * g⁻¹) :
    ∀ y₁ ∈ barSub T (normIn U T), ∀ y₂ ∈ barSub T (normIn U T),
      (g * y₁ * g⁻¹) * y₂ = y₂ * (g * y₁ * g⁻¹) := by
  obtain ⟨gg, rfl⟩ := QuotientGroup.mk_surjective g
  have hhN : (gg : G) ∈ Subgroup.normalizer (T : Set G) := gg.2
  have hbar : (QuotientGroup.mk gg : NQuot T) = barElt T hhN := rfl
  set h : G := (gg : G) with hh
  obtain ⟨u, huN, huL, hu⟩ := exists_eq_barElt_of_mem_barSub hy
  obtain ⟨u', hu'N, hu'L, hu'⟩ := exists_eq_barElt_of_mem_barSub hy'
  have hwN : h * u' * h⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem ((Subgroup.normalizer (T : Set G)).mul_mem hhN hu'N)
      ((Subgroup.normalizer (T : Set G)).inv_mem hhN)
  have hyw : y = barElt T hwN := by
    rw [hyy, hbar, ← hu']
    rfl
  have huw : u⁻¹ * (h * u' * h⁻¹) ∈ T := by
    have : barElt T huN = barElt T hwN := by rw [hu, hyw]
    exact (barElt_eq_iff huN hwN).1 this
  have hne : conjSubgroup h (normIn U T) ⊓ (normIn U T ⊔ T) ≠ ⊥ := by
    intro hbot
    have hmem : h * u' * h⁻¹ ∈ conjSubgroup h (normIn U T) ⊓ (normIn U T ⊔ T) := by
      refine ⟨conj_mem_conjSubgroup h hu'L, ?_⟩
      have e : h * u' * h⁻¹ = u * (u⁻¹ * (h * u' * h⁻¹)) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left huL) (Subgroup.mem_sup_right huw)
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hy1
    rw [hyw]
    exact (barElt_eq_one_iff hwN).2 (by rw [hmem]; exact T.one_mem)
  intro y₁ hy₁ y₂ hy₂
  obtain ⟨v₁, hv₁N, hv₁L, rfl⟩ := exists_eq_barElt_of_mem_barSub hy₁
  obtain ⟨v₂, hv₂N, hv₂L, rfl⟩ := exists_eq_barElt_of_mem_barSub hy₂
  have hc : (h * v₁ * h⁻¹) * v₂ = v₂ * (h * v₁ * h⁻¹) :=
    (c.commute_conj_L₁ hhN hne).1 _ (conj_mem_conjSubgroup h hv₁L) v₂ hv₂L
  have hP1 : (h * v₁ * h⁻¹) * v₂ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hhN hv₁N)
        ((Subgroup.normalizer (T : Set G)).inv_mem hhN)) hv₂N
  have hP2 : v₂ * (h * v₁ * h⁻¹) ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem hv₂N
      ((Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hhN hv₁N)
        ((Subgroup.normalizer (T : Set G)).inv_mem hhN))
  have e1 : barElt T hhN * barElt T hv₁N * (barElt T hhN)⁻¹ * barElt T hv₂N = barElt T hP1 := rfl
  have e2 : barElt T hv₂N * (barElt T hhN * barElt T hv₁N * (barElt T hhN)⁻¹) = barElt T hP2 :=
    rfl
  rw [hbar, e1, e2, barElt_eq_iff hP1 hP2, hc, inv_mul_cancel]
  exact T.one_mem

end Three

section Main

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem normal_of_le_kerK (h : Sec4Hyp T T₁ a T₂) (hA : sec4A T T₁ T₂ ≤ kerK T T₁) :
    ∀ g ∈ Subgroup.normalizer (T : Set G), conjSubgroup g (normIn T T₁) = normIn T T₁ := by
  have hT := h.pair.wc.1
  have hLsec : normIn T T₁ ≤ secA T T₁ := by
    intro u hu
    obtain ⟨x, hxT, hxM⟩ := IsConcreteLE.not_le_iff_exists.1 h.sec3.not_le_cfgM
    obtain ⟨l, hl, hlx⟩ := h.sec3.exists_mem_normIn₁_conj_eq hxT hxM hu
    have hlN := (mem_normIn.1 hl).2
    have hlR : l ∈ sec4R T T₁ T₂ := sec4N_le_sec4R (normIn_le_sec4N_mid hl)
    have hbarA : barElt T hlN ∈ sec4A T T₁ T₂ := barElt_mem_barSub hlN hlR
    have hlK := (mem_kerK_iff hT hlN).1 (hA hbarA)
    have h1 := hlK.2 x hxT
    have e : l * x * l⁻¹ * x⁻¹ = u := by
      rw [hlx, elemAbelian_mul_comm hT hxT (normIn_le _ _ hu)]
      group
    rwa [e] at h1
  have hsec : secA T T₁ = normIn T T₁ := le_antisymm secA_le_normIn hLsec
  intro g hg
  have := conjSubgroup_secA (T₁ := T₁) hg
  rwa [hsec] at this

omit [Finite G] in
theorem barSub_normIn_mid_le_sec4A : barSub T (normIn T₁ T) ≤ sec4A T T₁ T₂ := by
  intro y hy
  obtain ⟨u, huN, huL, rfl⟩ := exists_eq_barElt_of_mem_barSub hy
  exact barElt_mem_barSub huN (sec4N_le_sec4R (normIn_le_sec4N_mid huL))

omit [Finite G] in
theorem barSub_normIn_right_le_sec4A : barSub T (normIn T₂ T) ≤ sec4A T T₁ T₂ := by
  intro y hy
  obtain ⟨u, huN, huL, rfl⟩ := exists_eq_barElt_of_mem_barSub hy
  exact barElt_mem_barSub huN (sec4N_le_sec4R (normIn_le_sec4N_right huL))

theorem false_of_not_le_kerK
    (hG : Goldschmidt1974) (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (hP : Sec4PlusHolds T T₁ T₂)
    (hA : ¬ sec4A T T₁ T₂ ≤ kerK T T₁) : False := by
  classical
  set A : Subgroup (NQuot T) := sec4A T T₁ T₂ with hAdef
  set Hk : Subgroup (NQuot T) := Subgroup.normalClosure (A : Set (NQuot T)) with hHk
  have hHkn : Hk.Normal := Subgroup.normalClosure_normal
  have hAab : IsElemAbelian 2 A := h.isElemAbelian_sec4A
  have hAH : A ≤ Hk := Subgroup.le_normalClosure
  obtain ⟨S, hAS⟩ := (isPGroup_two_of_isElemAbelian hAab).exists_le_sylow
  have hcl : ∀ x ∈ A, ∀ k : NQuot T, k⁻¹ * x * k ∈ (S : Subgroup (NQuot T)) →
      k⁻¹ * x * k ∈ A :=
    fun x hx k hk => h.sec4A_stronglyClosed hP S.isPGroup' hAS hx k hk
  obtain ⟨ha, -, hc⟩ := hG (NQuot T) S A hAS hAab.1 hcl
  have hcentral : ∀ o ∈ goldschmidtOddCore ↥Hk, ∀ x : ↥Hk, x * o = o * x := by
    intro o ho x
    have hmem : (o : NQuot T) ∈ oddCoreOf Hk := ⟨o, ho, rfl⟩
    have : (oddCoreOf Hk).Normal := oddCoreOf_normal hHkn
    have h1 := h.oddNormal_comm_normalClosure hq (oddCoreOf Hk) (odd_card_oddCoreOf Hk)
      (o : NQuot T) hmem (x : NQuot T) x.2
    exact Subtype.ext h1
  set P₁ : Subgroup ↥Hk := (barSub T (normIn T₁ T)).subgroupOf Hk with hP₁
  set P₂ : Subgroup ↥Hk := (barSub T (normIn T₂ T)).subgroupOf Hk with hP₂
  have hP₁A : P₁ ≤ A.subgroupOf Hk := fun y hy =>
    Subgroup.mem_subgroupOf.2 (barSub_normIn_mid_le_sec4A (Subgroup.mem_subgroupOf.1 hy))
  have hP₂A : P₂ ≤ A.subgroupOf Hk := fun y hy =>
    Subgroup.mem_subgroupOf.2 (barSub_normIn_right_le_sec4A (Subgroup.mem_subgroupOf.1 hy))
  have hAP : ∀ α ∈ A.subgroupOf Hk, ∃ x ∈ P₁, ∃ y ∈ P₂, α = x * y := by
    intro α hα
    obtain ⟨a', b', ha', hb', hab⟩ := exists_eq_barElt_mul_of_mem_sec4A h
      (Subgroup.mem_subgroupOf.1 hα)
    have hx : barElt T (mem_normIn.1 ha').2 ∈ barSub T (normIn T₁ T) :=
      barElt_mem_barSub (mem_normIn.1 ha').2 ha'
    have hy : barElt T (mem_normIn.1 hb').2 ∈ barSub T (normIn T₂ T) :=
      barElt_mem_barSub (mem_normIn.1 hb').2 hb'
    refine ⟨⟨_, hAH (barSub_normIn_mid_le_sec4A hx)⟩, hx, ⟨_, hAH (barSub_normIn_right_le_sec4A hy)⟩,
      hy, ?_⟩
    exact Subtype.ext hab
  have h36 : ∀ {U : Subgroup G}, Cfg T U → ∀ g : ↥Hk,
      (∃ y ∈ (barSub T (normIn U T)).subgroupOf Hk, y ≠ 1 ∧
        ∃ y' ∈ (barSub T (normIn U T)).subgroupOf Hk, y = g * y' * g⁻¹) →
      ∀ y₁ ∈ (barSub T (normIn U T)).subgroupOf Hk, ∀ y₂ ∈ (barSub T (normIn U T)).subgroupOf Hk,
        (g * y₁ * g⁻¹) * y₂ = y₂ * (g * y₁ * g⁻¹) := by
    intro U c g ⟨y, hy, hy1, y', hy', hyy⟩ y₁ hy₁ y₂ hy₂
    have h1 := bar_comm_of_cfg c (Subgroup.mem_subgroupOf.1 hy) (fun h0 => hy1 (Subtype.ext h0))
      (Subgroup.mem_subgroupOf.1 hy') (congrArg Subtype.val hyy)
      (y₁ : NQuot T) (Subgroup.mem_subgroupOf.1 hy₁) (y₂ : NQuot T) (Subgroup.mem_subgroupOf.1 hy₂)
    exact Subtype.ext h1
  have hH₁ : CFSG.pCore 2 ↥Hk ≤ (kerK T T₁).subgroupOf Hk := by
    set 𝔓 : Subgroup (NQuot T) := (CFSG.pCore 2 ↥Hk).map Hk.subtype with h𝔓
    have h𝔓n : 𝔓.Normal := by
      refine ⟨fun n hn k => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hn
      have hchar : (CFSG.pCore 2 ↥Hk).Characteristic := inferInstance
      let φ : MulAut ↥Hk := MulAut.conjNormal k
      have hmem : x ∈ (CFSG.pCore 2 ↥Hk).comap φ.toMonoidHom := by
        rw [hchar.fixed φ]
        exact hx
      exact ⟨φ x, hmem, by simp [φ]⟩
    have h𝔓p : IsPGroup 2 𝔓 := (CFSG.pCore_isPGroup (p := 2) (G := ↥Hk)).map Hk.subtype
    intro x hx
    exact normal_pGroup_le_kerK h h𝔓p ⟨x, hx, rfl⟩
  have hTab := h.pair.wc.1
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => elemAbelian_mul_comm hTab ha hb
  let ρ : ↥Hk →* MulAut ↥T := (actT hTcomm).comp Hk.subtype
  have hρ : ρ.ker ≤ (kerK T T₁).subgroupOf Hk := fun x hx =>
    Subgroup.mem_subgroupOf.2 (ker_actT_le hTcomm (MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hx)))
  obtain ⟨d, hd⟩ := (isPGroup_two_of_isElemAbelian hTab).exists_card_eq
  have hA₁ : ¬ A.subgroupOf Hk ≤ (kerK T T₁).subgroupOf Hk := by
    intro hle
    apply hA
    intro y hy
    exact Subgroup.mem_subgroupOf.1 (hle (Subgroup.mem_subgroupOf.2 hy : (⟨y, hAH hy⟩ : ↥Hk) ∈
      A.subgroupOf Hk))
  have hres := layer_bound hcentral ha hc (isElemAbelian_subgroupOf hAab) hP₁A hP₂A hAP
    (h36 h.sec3.cfg) (h36 h.cfg₂) hH₁ hd ρ hρ hA₁
  obtain ⟨hlt, h16⟩ := card_lt_sq_card_normIn hAsc h hq
  have hLT : Nat.card T = 2 ^ d := hd
  have hcard₁ : Nat.card P₁ = Nat.card (normIn T T₁) := by
    rw [hP₁, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((barSub_normIn_mid_le_sec4A (T₂ := T₂)).trans hAH)).toEquiv,
      card_barSub (fun x hx => (mem_normIn.1 hx).2) (by
        rw [eq_bot_iff, ← h.sec3.cfg.symm.inf]
        exact inf_le_inf (normIn_le _ _) le_rfl)]
    exact h.card_normIn₁
  have hcard₂ : Nat.card P₂ = Nat.card (normIn T T₁) := by
    rw [hP₂, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((barSub_normIn_right_le_sec4A (T₁ := T₁)).trans hAH)).toEquiv,
      card_barSub (fun x hx => (mem_normIn.1 hx).2) (by
        rw [eq_bot_iff, inf_comm, ← h.inf_left_eq_bot]
        exact inf_le_inf le_rfl (normIn_le _ _))]
    exact h.card_normIn₂_eq h.mem_normalizer_normIn
  rw [hcard₁, hcard₂] at hres
  have key : Nat.card (normIn T T₁) ≤ 8 ∨ Nat.card (normIn T T₁) ^ 2 ≤ Nat.card T := by
    rw [hLT]
    rcases hres with (h1 | h1) | (h1 | h1)
    · exact Or.inl h1
    · exact Or.inr h1
    · exact Or.inl h1
    · exact Or.inr h1
  rcases key with k | k <;> omega

end Main

theorem noLayer_of_inputs
    (hG : Goldschmidt1974) (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (h214 : Lemma214) :
    Sec4I5NoLayer := by
  intro G _ _ _ hnab _ T T₁ T₂ a h hq _ _ hP
  exfalso
  by_cases hA : sec4A T T₁ T₂ ≤ kerK T T₁
  · exact false_of_normal_of_maxPair hTO benderWCInput_of_repo h214
      involutionClassInput_of_repo hnab h.pair h.sec3 (normal_of_le_kerK h hA)
  · exact false_of_not_le_kerK hG aschbacherNoPolarInput_of_repo h hq hP hA

end CFSG.CGT.T75D
