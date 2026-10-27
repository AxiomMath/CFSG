module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Maschke
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open scoped commutatorElement

private theorem exists_mul_of_mem_sup {Y : Type} [Group Y] (A C : Subgroup Y)
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) :
    ∀ v ∈ A ⊔ C, ∃ a ∈ A, ∃ c ∈ C, v = a * c := by
  intro v hv
  rw [Subgroup.sup_eq_closure] at hv
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, C.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, C.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    obtain ⟨a', ha', c', hc', rfl⟩ := hy
    refine ⟨a * a', A.mul_mem ha ha', c * c', C.mul_mem hc hc', ?_⟩
    have h1 := hcomm a' ha' c hc
    calc a * c * (a' * c') = a * (c * a') * c' := by group
      _ = a * (a' * c) * c' := by rw [← h1]
      _ = a * a' * (c * c') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
    have h1 := hcomm a ha c hc
    calc (a * c)⁻¹ = (c * a)⁻¹ := by rw [h1]
      _ = a⁻¹ * c⁻¹ := by group

private theorem commutator_mul_mul {Y : Type} [Group Y] {t t' u w : Y}
    (h1 : u * t' = t' * u) (h2 : u * w = w * u) (h3 : w * t = t * w) :
    (t * u) * (t' * w) * (t * u)⁻¹ * (t' * w)⁻¹ = t * t' * t⁻¹ * t'⁻¹ := by
  have hu : Commute u t' := h1
  have huw : Commute u w := h2
  have hw : Commute w t := h3
  have e1 : u * (t' * w) * u⁻¹ = t' * w := (hu.mul_right huw).mul_inv_cancel
  have e2 : w * t⁻¹ * w⁻¹ = t⁻¹ := hw.inv_right.mul_inv_cancel
  calc (t * u) * (t' * w) * (t * u)⁻¹ * (t' * w)⁻¹
      = t * (u * (t' * w) * u⁻¹) * t⁻¹ * w⁻¹ * t'⁻¹ := by group
    _ = t * (t' * w) * t⁻¹ * w⁻¹ * t'⁻¹ := by rw [e1]
    _ = t * t' * (w * t⁻¹ * w⁻¹) * t'⁻¹ := by group
    _ = t * t' * t⁻¹ * t'⁻¹ := by rw [e2]

namespace Case2Data

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

private theorem comm_T_zpowers (h : Case2Data p P T D F x) :
    ∀ t ∈ T, ∀ c ∈ zpowers x, t * c = c * t := by
  intro t ht c hc
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  exact (Commute.zpow_right (show Commute t x from h.pdata.comm t ht x h.pdata.x_mem) j).eq

private theorem commutator_P (h : Case2Data p P T D F x) :
    ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ zOf T := by
  intro a ha b hb
  obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul a ha
  obtain ⟨t', ht', d', hd', rfl⟩ := h.exists_mul b hb
  haveI := h.pdata.D_cyc
  have hDD : d * d' = d' * d :=
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := D)).is_comm.comm ⟨d, hd⟩ ⟨d', hd'⟩)
  rw [commutator_mul_mul (h.pdata.comm t' ht' d hd).symm hDD (h.pdata.comm t ht d' hd').symm]
  exact h.commutator_mem t ht t' ht'

private theorem commutator_T_eq (h : Case2Data p P T D F x) : ⁅T, T⁆ = zOf T := by
  haveI := h.fact
  have hle : ⁅T, T⁆ ≤ zOf T :=
    Subgroup.commutator_le.2 (fun a ha b hb => h.commutator_mem a ha b hb)
  have hne : ⁅T, T⁆ ≠ ⊥ := by
    intro hbot
    apply h.pdata.T_nonab
    refine ⟨⟨fun a b => ?_⟩⟩
    have hab : ⁅(a : Y), (b : Y)⁆ ∈ ⁅T, T⁆ := Subgroup.commutator_mem_commutator a.2 b.2
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
    exact Subtype.ext hab
  have hdvd : Nat.card (⁅T, T⁆ : Subgroup Y) ∣ p := h.zOf_card ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime h.prime).1 hdvd with h1 | h1
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h.zOf_card, h1])

private theorem V_exp (h : Case2Data p P T D F x) : ∀ v ∈ T ⊔ zpowers x, v ^ p = 1 := by
  have hxp : x ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.pdata.x_ord] at this
  intro v hv
  obtain ⟨t, ht, c, hc, rfl⟩ := exists_mul_of_mem_sup T (zpowers x) h.comm_T_zpowers v hv
  rw [Commute.mul_pow (h.comm_T_zpowers t ht c hc), h.pdata.T_exp t ht]
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  rw [one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]

private theorem V_le_P (h : Case2Data p P T D F x) : T ⊔ zpowers x ≤ P :=
  sup_le h.pdata.T_le ((Subgroup.zpowers_le).2 (h.pdata.D_le h.pdata.x_mem))

private theorem pCore_le_P (h : Case2Data p P T D F x) : CFSG.pCore p Y ≤ P := by
  haveI := h.fact
  obtain ⟨S, hS⟩ := h.sylow
  rw [← hS]
  exact (CFSG.pCore_isPGroup (p := p) (G := Y)).le_sylow_of_normal S

theorem eq_of_complements (h : Case2Data p P T D F x) {T' : Subgroup Y}
    (hT'V : T' ≤ T ⊔ zpowers x) (hZT' : zOf T ≤ T') (hT'Λ : T' ⊓ zpowers x = ⊥)
    (hT'Λ' : T' ⊔ zpowers x = T ⊔ zpowers x) (hF : ∀ f ∈ F, ∀ a ∈ T', f * a * f⁻¹ ∈ T') :
    T' = T := by
  haveI := h.fact
  have hcommV : ∀ v ∈ T ⊔ zpowers x, ∀ c ∈ zpowers x, v * c = c * v := by
    intro v hv c hc
    obtain ⟨t, ht, c', hc', rfl⟩ := exists_mul_of_mem_sup T (zpowers x) h.comm_T_zpowers v hv
    have h2 : c' * c = c * c' := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
      exact (Commute.zpow_zpow_self x j i).eq
    calc t * c' * c = t * (c' * c) := mul_assoc _ _ _
      _ = t * (c * c') := by rw [h2]
      _ = (t * c) * c' := (mul_assoc _ _ _).symm
      _ = (c * t) * c' := by rw [h.comm_T_zpowers t ht c hc]
      _ = c * (t * c') := mul_assoc _ _ _
  have hBinv : ∀ f ∈ F, ∀ a ∈ T ⊓ T', f * a * f⁻¹ ∈ T ⊓ T' :=
    fun f hf a ha => ⟨h.torus.F_T f hf a ha.1, hF f hf a ha.2⟩
  rcases h.torus.irred (T ⊓ T') inf_le_left (le_inf h.zOf_le hZT') hBinv with hB | hB
  ·
    exfalso
    have hX_card : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, h.pdata.x_ord]
    have hXV : ∀ c ∈ zpowers x, c ∈ T ⊔ zpowers x := fun c hc => Subgroup.mem_sup_right hc
    have h1 : T'.relIndex (T ⊔ zpowers x) ≤ p := by
      rw [← hX_card]
      let φ : zpowers x → (↥(T ⊔ zpowers x)) ⧸ T'.subgroupOf (T ⊔ zpowers x) :=
        fun c => QuotientGroup.mk ⟨c.1, hXV c.1 c.2⟩
      have hφ : Function.Surjective φ := by
        intro q
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
        have hv : (v : Y) ∈ T' ⊔ zpowers x := by rw [hT'Λ']; exact v.2
        obtain ⟨a, ha, c, hc, hvac⟩ := exists_mul_of_mem_sup T' (zpowers x)
          (fun a ha c hc => hcommV a (hT'V ha) c hc) v hv
        refine ⟨⟨c, hc⟩, ?_⟩
        show (QuotientGroup.mk ⟨c, hXV c hc⟩ : (↥(T ⊔ zpowers x)) ⧸ T'.subgroupOf (T ⊔ zpowers x))
          = QuotientGroup.mk v
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hac : a * c = c * a := hcommV a (hT'V ha) c hc
        have hmem : c⁻¹ * (v : Y) ∈ T' := by
          rw [hvac, hac, inv_mul_cancel_left]
          exact ha
        exact hmem
      exact Nat.card_le_card_of_surjective φ hφ
    have hne : T'.relIndex (T ⊔ zpowers x) ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card ..) Nat.card_pos).ne'
    have h2 : T'.relIndex T ≤ T'.relIndex (T ⊔ zpowers x) :=
      Subgroup.relIndex_le_of_le_right le_sup_left hne
    have h3 : T'.relIndex T * Nat.card (T' ⊓ T : Subgroup Y) = Nat.card T :=
      Subgroup.relIndex_mul_card T' T
    rw [inf_comm, hB, h.zOf_card, h.pdata.T_card] at h3
    have hp0 : 0 < p := h.prime.pos
    have h4 : T'.relIndex T = p ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_right hp0
      rw [h3]; ring
    have h5 : p ^ 2 ≤ p := h4 ▸ h2.trans h1
    nlinarith [h.five]
  ·
    have hTT' : T ≤ T' := inf_eq_left.1 hB
    refine le_antisymm ?_ hTT'
    intro a ha
    obtain ⟨t, ht, c, hc, rfl⟩ :=
      exists_mul_of_mem_sup T (zpowers x) h.comm_T_zpowers a (hT'V ha)
    have hc' : c ∈ T' := by
      have := T'.mul_mem (T'.inv_mem (hTT' ht)) ha
      simpa using this
    have hc1 : c ∈ T' ⊓ zpowers x := ⟨hc', hc⟩
    rw [hT'Λ, Subgroup.mem_bot] at hc1
    rw [hc1, mul_one]
    exact ht

theorem V_normal (h : Case2Data p P T D F x) (hT : T ≤ CFSG.pCore p Y) (hx : x ∈ CFSG.pCore p Y) :
    ∀ y : Y, ∀ v ∈ T ⊔ zpowers x, y * v * y⁻¹ ∈ T ⊔ zpowers x := by
  haveI := h.fact
  have key : ∀ v : Y, v ∈ T ⊔ zpowers x ↔ v ∈ CFSG.pCore p Y ∧ v ^ p = 1 := by
    intro v
    constructor
    · intro hv
      exact ⟨(sup_le hT ((Subgroup.zpowers_le).2 hx)) hv, h.V_exp v hv⟩
    · rintro ⟨hvO, hvp⟩
      obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul v (h.pCore_le_P hvO)
      rw [Commute.mul_pow (h.pdata.comm t ht d hd), h.pdata.T_exp t ht, one_mul] at hvp
      exact Subgroup.mul_mem_sup ht (h.mem_zpowers_of_pow_eq_one d hd hvp)
  intro y v hv
  rw [key] at hv ⊢
  obtain ⟨hvO, hvp⟩ := hv
  refine ⟨(CFSG.pCore_normal (p := p) (G := Y)).conj_mem v hvO y, ?_⟩
  rw [conj_pow, hvp]
  simp

theorem zpowers_normal (h : Case2Data p P T D F x)
    (hV : ∀ y : Y, ∀ v ∈ T ⊔ zpowers x, y * v * y⁻¹ ∈ T ⊔ zpowers x) :
    ∀ y : Y, ∀ v ∈ zpowers x, y * v * y⁻¹ ∈ zpowers x := by
  intro y v hv
  have hle : (zpowers x).map (MulAut.conj y).toMonoidHom ≤ P := by
    rintro _ ⟨w, hw, rfl⟩
    exact h.V_le_P (hV y w (Subgroup.mem_sup_right hw))
  have heq := h.wc y hle
  have hmem : y * v * y⁻¹ ∈ (zpowers x).map (MulAut.conj y).toMonoidHom :=
    ⟨v, hv, by simp [MulAut.conj_apply]⟩
  rwa [heq] at hmem

theorem zOf_normal (h : Case2Data p P T D F x)
    (hV : ∀ y : Y, ∀ v ∈ T ⊔ zpowers x, y * v * y⁻¹ ∈ T ⊔ zpowers x) :
    ∀ y : Y, ∀ z ∈ zOf T, y * z * y⁻¹ ∈ zOf T := by
  haveI : (T ⊔ zpowers x).Normal := ⟨fun v hv y => hV y v hv⟩
  have hVV : ⁅T ⊔ zpowers x, T ⊔ zpowers x⁆ = zOf T := by
    apply le_antisymm
    · exact Subgroup.commutator_le.2
        (fun a ha b hb => h.commutator_P a (h.V_le_P ha) b (h.V_le_P hb))
    · rw [← h.commutator_T_eq]
      exact Subgroup.commutator_mono le_sup_left le_sup_left
  intro y z hz
  have hz' : z ∈ ⁅T ⊔ zpowers x, T ⊔ zpowers x⁆ := hVV ▸ hz
  have := (Subgroup.commutator_normal (T ⊔ zpowers x) (T ⊔ zpowers x)).conj_mem z hz' y
  rwa [hVV] at this

theorem normal_of_le_pCore (h : Case2Data p P T D F x) (hT : T ≤ CFSG.pCore p Y) :
    ∀ y : Y, ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
  haveI := h.fact
  by_cases hx : x ∈ CFSG.pCore p Y
  ·
    obtain ⟨S, hS⟩ := h.sylow
    have hV := h.V_normal hT hx
    have hΛ := h.zpowers_normal hV
    have hZ := h.zOf_normal hV
    haveI hVn : (T ⊔ zpowers x).Normal := ⟨fun v hv y => hV y v hv⟩
    haveI hΛn : (zpowers x).Normal := ⟨fun v hv y => hΛ y v hv⟩
    haveI hZn : (zOf T).Normal := ⟨fun v hv y => hZ y v hv⟩
    obtain ⟨T', hT'n, hZT', hT'V, hT'Λ, hT'sup⟩ :=
      exists_normal_complement h.prime S (T ⊔ zpowers x) (zpowers x) (zOf T) hVn hΛn hZn
        le_sup_right (h.zOf_le.trans le_sup_left)
        (fun a ha b hb => h.commutator_P a (h.V_le_P ha) b (h.V_le_P hb))
        h.V_exp
        (fun s hs v hv => h.commutator_P s (hS ▸ hs) v (h.V_le_P hv))
        (by rw [Nat.card_zpowers, h.pdata.x_ord])
        (by
          rw [eq_bot_iff]
          intro v hv
          have hvT : v ∈ T ⊓ zpowers x := ⟨h.zOf_le hv.2, hv.1⟩
          rw [h.T_inf_zpowers] at hvT
          exact hvT)
    have hTT' : T' = T :=
      h.eq_of_complements hT'V hZT' hT'Λ hT'sup (fun f _ a ha => hT'n.conj_mem a ha f)
    rw [← hTT']
    intro y t ht
    exact hT'n.conj_mem t ht y
  ·
    have hbot : CFSG.pCore p Y ⊓ D = ⊥ := by
      by_contra hne
      exact hx (h.x_mem_of_ne_bot (CFSG.pCore p Y ⊓ D) inf_le_right hne).1
    have hOT : CFSG.pCore p Y ≤ T := by
      intro o ho
      obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul o (h.pCore_le_P ho)
      have hd' : d ∈ CFSG.pCore p Y := by
        have := (CFSG.pCore p Y).mul_mem ((CFSG.pCore p Y).inv_mem (hT ht)) ho
        simpa using this
      have hd1 : d ∈ CFSG.pCore p Y ⊓ D := ⟨hd', hd⟩
      rw [hbot, Subgroup.mem_bot] at hd1
      rw [hd1, mul_one]
      exact ht
    intro y t ht
    exact hOT ((CFSG.pCore_normal (p := p) (G := Y)).conj_mem t (hT ht) y)

end Case2Data

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
