module

public import CFSG.CGT.T75R.CaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIMain
public import CFSG.CGT.T75R.XConstr

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem false_of_two_lines [Finite G] {T T₁ : Subgroup G} (hP : MaxPair T T₁)
    (hTc : Nat.card T = 8) (hLc : Nat.card (normIn T T₁) ≤ 4) {Tx : Subgroup G}
    (hTx : ∃ g : G, Tx = conjSubgroup g T) {x : G} (hx : x ∈ Tx) (hx1 : x ≠ 1)
    (hxD : x ∈ classD T) (hx2 : x * x = 1) {L M₁ M₂ N : Subgroup G} (hN : IsElemAbelian 2 N)
    (hLN : L ≤ N) (hxN : x ∈ Subgroup.normalizer (N : Set G))
    (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hLnot : ¬ L ≤ Subgroup.normalizer (Tx : Set G)) (hLM₁ : L ≤ M₁) (hM₁N : M₁ ≤ N)
    (hM₂N : M₂ ≤ N) (hM12 : M₁ ⊓ M₂ ≤ L) {l e₁ e₂ : G} (hl : l ∈ L) (hxl : x * l ≠ l * x)
    (he₁ : e₁ ∈ M₁) (he₂ : e₂ ∈ M₂) (hc₁ : ⁅x, e₁⁆ ∈ M₁) (hc₁L : ⁅x, e₁⁆ ∉ L)
    (hc₂ : ⁅x, e₂⁆ ∈ M₂) (hc₂L : ⁅x, e₂⁆ ∉ L) : False := by
  have hcl : ⁅x, l⁆ ∈ L := by
    have e1 : ⁅x, l⁆ = (x * l * x⁻¹) * l⁻¹ := by simp only [commutatorElement_def]
    rw [e1]
    exact L.mul_mem (conj_mem_of_mem_normalizer hxL hl) (L.inv_mem hl)
  have i1 : ⁅x, l⁆ ≠ 1 := by
    intro h1
    apply hxl
    simp only [commutatorElement_def] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hc₂M₁ : ⁅x, e₂⁆ ∉ M₁ := fun h => hc₂L (hM12 ⟨h, hc₂⟩)
  have i12 : ⁅x, e₁⁆ ≠ ⁅x, e₂⁆ := fun h => hc₂M₁ (h ▸ hc₁)
  have i13 : ⁅x, e₁⁆ ≠ ⁅x, l⁆ := fun h => hc₁L (h ▸ hcl)
  have i23 : ⁅x, e₂⁆ ≠ ⁅x, l⁆ := fun h => hc₂L (h ▸ hcl)
  have i123 : ⁅x, l⁆ ≠ ⁅x, e₁⁆ * ⁅x, e₂⁆ := by
    intro h
    apply hc₂M₁
    have : ⁅x, e₂⁆ = (⁅x, e₁⁆)⁻¹ * ⁅x, l⁆ := by rw [h]; group
    rw [this]
    exact M₁.mul_mem (M₁.inv_mem hc₁) (hLM₁ hcl)
  exact false_of_three_commutators hP hTc hLc hTx hx hx1 hxD hx2 hN hLN hxN hLnot (hM₁N he₁)
    (hM₂N he₂) (hLN hl) (fun h => hc₁L (h ▸ L.one_mem)) (fun h => hc₂L (h ▸ L.one_mem)) i1 i12
    i13 i23 i123

theorem mem_classD_of_mem_conj {T U : Subgroup G} (hU : ∃ u : G, U = conjSubgroup u T) {z : G}
    (hz : z ∈ U) (hz1 : z ≠ 1) : z ∈ classD T := by
  obtain ⟨u, rfl⟩ := hU
  have h1 : u⁻¹ * z * u ∈ T := mem_conjSubgroup.1 hz
  refine ⟨u⁻¹, u⁻¹ * z * u, h1, ?_, by group⟩
  intro h
  apply hz1
  have : z = u * (u⁻¹ * z * u) * u⁻¹ := by group
  rw [this, h]
  group

theorem conjSubgroup_eq_of_le_of_sq {N : Subgroup G} {x : G} (hx2 : x * x = 1)
    (h : conjSubgroup x N ≤ N) : conjSubgroup x N = N := by
  apply le_antisymm h
  have := conjSubgroup_mono (g := x) h
  rwa [conjSubgroup_conjSubgroup, hx2, conjSubgroup_one] at this

variable [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

omit [Finite G] in
theorem Sec4Hyp.false_of_conj_eq (h : Sec4Hyp T T₁ a T₂) {t : G} (ht : t ∈ T)
    (h2 : T₂ = conjSubgroup t T₁) : False := by
  have hma := h.mem_normIn₂
  rw [h2, normIn_conj_right_of_mem_normalizer (Subgroup.le_normalizer ht)] at hma
  obtain ⟨e, he, hae⟩ := mem_conjSubgroup_iff_exists.1 hma
  apply h.haL
  have hc : ⁅t, e⁆ ∈ T := (normIn_le T T₁) (h.sec3.cfg.comm_mem_normIn ht he)
  have e1 : a = ⁅t, e⁆ * e := by
    rw [hae]
    simp only [commutatorElement_def]
    group
  rw [e1]
  exact (T ⊔ normIn T₁ T).mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right he)

theorem Sec4Hyp.false_of_card_eight [IsSimpleGroup G] (h214 : Lemma214)
    (hInv : InvolutionClassInput) (hSz : Section3SzInput)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput)
    (hnab : ∃ a b : G, a * b ≠ b * a) (htri : TriA) (hy : StepHyp T T₁)
    (h : Sec4Hyp T T₁ a T₂) (hq : Nat.card T = 2 * Nat.card (normIn T T₁))
    (hT8 : Nat.card T = 8) : False := by
  have hLc : Nat.card (normIn T T₁) = 4 := by omega
  have hB := h.mem_normalizer_normIn
  have e1 : normIn T T₂ = normIn T T₁ := h.normIn_eq hB
  have hLT : normIn T T₁ ≤ T := normIn_le T T₁
  obtain ⟨g, hg, x, hxg, hx1, hx2, hxT, hxL, hxact, hxl, hLnot⟩ :=
    Sec4Hyp.exists_x_eight h214 hInv hTO hBW hnab h hq hT8
  let Kg : Subgroup G :=
    Subgroup.normalizer (T : Set G) ⊓ Subgroup.normalizer (normIn T T₁ : Set G)
  have hNK : sec4N T T₁ T₂ ≤ Kg := fun n hn =>
    ⟨sec4N_le_normalizer_left hn, mem_normalizer_of_commute fun m hm =>
      elemAbelian_mul_comm h.isElemAbelian_sec4N hn (normIn_le_sec4N_left hm)⟩
  have hxK : x ∈ Kg := ⟨hxT, hxL⟩
  have hcl : Subgroup.closure ({x} : Set G) ≤ conjSubgroup g (normIn T₁ T) := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hxg
  have hclK : Subgroup.closure ({x} : Set G) ≤ Kg := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hxK
  have hclP : IsPGroup 2 (Subgroup.closure ({x} : Set G)) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_of_le
      (isElemAbelian_conjSubgroup h.sec3.cfg.wc₁.1 g)
      (hcl.trans (conjSubgroup_mono (normIn_le T₁ T))))
  obtain ⟨k, hkK, S, hSP, hSK, hAS, hBS⟩ :=
    exists_two_group_conj_le hclP h.isPGroup_sec4N hclK hNK
  have hkT : k ∈ Subgroup.normalizer (T : Set G) := hkK.1
  have hkL : k ∈ Subgroup.normalizer (normIn T T₁ : Set G) := hkK.2
  have hLk : conjSubgroup k (normIn T T₁) = normIn T T₁ := mem_normalizer_iff_conjSubgroup_eq.1 hkL
  have hxS : x ∈ S := hAS (Subgroup.subset_closure (Set.mem_singleton x))
  have hSN : S ≤ Subgroup.normalizer (T : Set G) := fun w hw => (hSK hw).1
  have hSL : S ≤ Subgroup.normalizer (normIn T T₁ : Set G) := fun w hw => (hSK hw).2
  have h' := h.conj_of_mem_normalizer hkT
  have hS₂ : Sec3 T T₂ := sec3_of_conj_conj h.glob ⟨1, (conjSubgroup_one T).symm⟩ h.conj
    h.ne_left h.normIn_ne_bot
  have hV₁ : Nbr T (normIn T T₁) S (conjSubgroup k T₁) :=
    { sec3 := h'.sec3
      conj := h'.pair.conj
      hL := by rw [normIn_conj_left_of_mem_normalizer hkT T₁, hLk]
      hS := by
        rw [normIn_conj_right_of_mem_normalizer hkT T₁]
        exact (conjSubgroup_mono (normIn_le_sec4N_mid (T₂ := T₂))).trans hBS }
  have hV₂ : Nbr T (normIn T T₁) S (conjSubgroup k T₂) :=
    { sec3 := hS₂.conj_of_mem_normalizer hkT
      conj := h'.conj
      hL := by rw [normIn_conj_left_of_mem_normalizer hkT T₂, e1, hLk]
      hS := by
        rw [normIn_conj_right_of_mem_normalizer hkT T₂]
        exact (conjSubgroup_mono (normIn_le_sec4N_right (T₁ := T₁))).trans hBS }
  obtain ⟨v, hv⟩ := h.pair.conj
  have hTx : ∃ g' : G, conjSubgroup g T₁ = conjSubgroup g' T := ⟨g * v, by
    rw [hv, conjSubgroup_conjSubgroup]⟩
  have hxTx : x ∈ conjSubgroup g T₁ := conjSubgroup_mono (normIn_le T₁ T) hxg
  have hX : XData T (normIn T T₁) (conjSubgroup g T₁) x :=
    { hx1 := hx1, hx2 := hx2, hxT := hxT, hxL := hxL, hxact := hxact, hxl := hxl
      hxD := mem_classD_of_mem_conj hTx hxTx hx1, hTx := hTx, hxTx := hxTx, hLnot := hLnot }
  have hy' : StepHyp T (conjSubgroup k T₁) := { hy with pair := h'.pair }
  have hq' : Nat.card T = 2 * Nat.card (normIn T (conjSubgroup k T₁)) := by rw [hV₁.hL]; exact hq
  have hLc' : Nat.card (normIn T T₁) = 4 := hLc
  rcases Nbr.dichotomy h214 hInv hSz hnab htri hy' h'.glob h'.iso hq' hT8 hV₁.hL hV₁ hSP hSN hSL
    hxS hX with ⟨t₁, ht₁, htV₁⟩ | ⟨hVx₁, hB₁⟩
  swap
  · exact Nbr.false_of_caseB h214 hInv hSz hnab h'.pair hT8 hV₁.hL hLc' hV₁ hSP hSN hSL hxS hX
      hVx₁ hB₁
  rcases Nbr.dichotomy h214 hInv hSz hnab htri hy' h'.glob h'.iso hq' hT8 hV₁.hL hV₂ hSP hSN hSL
    hxS hX with ⟨t₂, ht₂, htV₂⟩ | ⟨hVx₂, hB₂⟩
  swap
  · exact Nbr.false_of_caseB h214 hInv hSz hnab h'.pair hT8 hV₁.hL hLc' hV₂ hSP hSN hSL hxS hX
      hVx₂ hB₂
  obtain ⟨e₁, he₁, hc₁, hc₁L⟩ := hV₁.caseA_data hX ht₁ htV₁
  obtain ⟨e₂, he₂, hc₂, hc₂L⟩ := hV₂.caseA_data hX ht₂ htV₂
  have hcomm12 : ∀ y ∈ normIn (conjSubgroup k T₁) T, ∀ z ∈ normIn (conjSubgroup k T₂) T,
      y * z = z * y := fun y hy z hz =>
    elemAbelian_mul_comm h'.isElemAbelian_sec4N (normIn_le_sec4N_mid hy) (normIn_le_sec4N_right hz)
  have hdir : normIn (conjSubgroup k T₂) T ⊓ cfgM T (conjSubgroup k T₁) = ⊥ := by
    rcases htri G T (conjSubgroup k T₁) hy' h'.glob h'.iso hq' hT8 (conjSubgroup k T₁)
      (conjSubgroup k T₂) hV₁.conj hV₂.conj (hV₁.ne_left (by rw [← hLc] at *; exact hq))
      (hV₂.ne_left (by exact hq)) h'.ne_right rfl (hV₂.hL.trans hV₁.hL.symm) hcomm12 with
      h0 | ⟨t, ht, -, htc⟩
    · exact h0
    · exact (Sec4Hyp.false_of_conj_eq h' ht htc).elim
  have hM12 : cfgM T (conjSubgroup k T₁) ⊓ cfgM T (conjSubgroup k T₂) ≤ normIn T T₁ := by
    rintro z ⟨hz1, hz2⟩
    have hcfg2 : cfgM T (conjSubgroup k T₂) = normIn T T₁ ⊔ normIn (conjSubgroup k T₂) T := by
      rw [cfgM, hV₂.hL]
    rw [hcfg2] at hz2
    have hcommL : ∀ l ∈ normIn T T₁, ∀ b ∈ normIn (conjSubgroup k T₂) T, l * b = b * l :=
      fun l hl b hb => hV₂.sec3.cfg.comm_L_L₁ (hV₂.hL ▸ hl) hb
    obtain ⟨l', hl', b, hb, rfl⟩ := (mem_sup_iff_of_comm hcommL).1 hz2
    have hb1 : b ∈ cfgM T (conjSubgroup k T₁) := by
      have := (cfgM T (conjSubgroup k T₁)).mul_mem
        ((cfgM T (conjSubgroup k T₁)).inv_mem
          (Cfg.normIn_le_cfgM_left T (conjSubgroup k T₁) (hV₁.hL ▸ hl'))) hz1
      simpa using this
    have hb0 : b ∈ normIn (conjSubgroup k T₂) T ⊓ cfgM T (conjSubgroup k T₁) := ⟨hb, hb1⟩
    rw [hdir, Subgroup.mem_bot] at hb0
    rw [hb0, mul_one]
    exact hl'
  have hLN : normIn T T₁ ≤ sec4N T (conjSubgroup k T₁) (conjSubgroup k T₂) := by
    rw [← hV₁.hL]; exact normIn_le_sec4N_left
  have hM₁N : cfgM T (conjSubgroup k T₁) ≤ sec4N T (conjSubgroup k T₁) (conjSubgroup k T₂) :=
    cfgM_le_sec4N
  have hM₂N : cfgM T (conjSubgroup k T₂) ≤ sec4N T (conjSubgroup k T₁) (conjSubgroup k T₂) :=
    sup_le (by rw [hV₂.hL, ← hV₁.hL]; exact normIn_le_sec4N_left) normIn_le_sec4N_right
  have hxL' : conjSubgroup x (normIn T T₁) = normIn T T₁ := mem_normalizer_iff_conjSubgroup_eq.1 hxL
  have hxN : x ∈ Subgroup.normalizer
      ((sec4N T (conjSubgroup k T₁) (conjSubgroup k T₂) : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conjSubgroup_eq
    apply conjSubgroup_eq_of_le_of_sq hx2
    unfold sec4N
    rw [conjSubgroup_sup_eq_sup, conjSubgroup_sup_eq_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [hV₁.hL, hxL']
      exact le_sup_left.trans le_sup_left
    · exact (hV₁.conj_x_le hX ht₁ htV₁).trans hM₁N
    · exact (hV₂.conj_x_le hX ht₂ htV₂).trans hM₂N
  obtain ⟨l, hl, hxl'⟩ := hxl
  exact false_of_two_lines h'.pair hT8 (by rw [hV₁.hL]; exact hLc.le) hX.hTx hX.hxTx hx1 hX.hxD
    hx2 h'.isElemAbelian_sec4N hLN hxN hxL hLnot
    (by rw [← hV₁.hL]; exact Cfg.normIn_le_cfgM_left T (conjSubgroup k T₁)) hM₁N hM₂N hM12 hl
    hxl' (Cfg.normIn_le_cfgM_right T (conjSubgroup k T₁) he₁)
    (Cfg.normIn_le_cfgM_right T (conjSubgroup k T₂) he₂) hc₁ hc₁L hc₂ hc₂L

theorem sec4CaseIIIEight_of_triA (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hSz : Section3SzInput) (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne)
    (hBW : BenderWCInput) (htri : TriA) : Sec4CaseIIIEight := by
  intro G _ T T₁ hy hS hSI hq hT8 a ha haL hcomm
  have hfin : Finite G := hy.finite
  have hsimple : IsSimpleGroup G := hy.simple
  obtain ⟨g, t, htT, ht1, hg⟩ := ha.1
  have h : Sec4Hyp T T₁ a (conjSubgroup g⁻¹ T) :=
    ⟨hy.pair, hS, hSI, ha, haL, hcomm, ⟨g⁻¹, rfl⟩, mem_conjSubgroup.mpr (by
      rw [inv_inv, hg]
      have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
      rw [e]
      exact htT)⟩
  exact Sec4Hyp.false_of_card_eight h214 hInv hSz hTO hBW hy.nonab htri hy h hq hT8

end CFSG.CGT.T75R
