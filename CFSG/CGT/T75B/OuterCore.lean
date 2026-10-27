module

public import CFSG.CGT.T75B.FNorm
public import CFSG.CGT.T75B.NormAll
public import CFSG.CGT.T75B.TxMeetN
public import CFSG.CGT.T75B.Front
public import CFSG.CGT.Timmesfeld75.Sec4CaseIProps
public import CFSG.CGT.T75B.XFam

public section

namespace CFSG.CGT.T75B

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {T T₁ T₂ : Subgroup G} {a : G}

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.false_of_outer_fixed
    (hAsc : AschbacherNoPolarInput) (h215 : Lemma215Stmt)
    (h26 : Lemma26Input) (hId : Sec4I4RootGroupInput) (hA : Sec4I4TrivialAction)
    (hW : ∀ (f : ℕ) (P : Type) [Group P] [Finite P], 2 ≤ f → (P ≃* PSU3Model f) →
      Lemma21Input P)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (h : Sec4Hyp T T₁ a T₂) (hq : 2 * Nat.card (normIn T T₁) < Nat.card T)
    (h16 : Nat.card T ≠ 16) (hL16 : 16 ≤ Nat.card (normIn T T₁)) {x : G} (hxD : x ∈ classD T)
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) (hx₁ : x ∈ Subgroup.normalizer (T₁ : Set G))
    (hxN : x ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G))
    (hout : ∀ t ∈ T, ¬ Sec4ActsTriv T T₁ T₂ (x * t)) : False := by
  classical
  have hTab := h.pair.wc.1
  have hxD' := hxD
  obtain ⟨g, t, ht, -, hxg⟩ := hxD'
  have hTx : ∃ k : G, conjSubgroup g⁻¹ T = conjSubgroup k T := ⟨g⁻¹, rfl⟩
  have hxTx : x ∈ conjSubgroup g⁻¹ T := by
    have e : (g⁻¹)⁻¹ * x * g⁻¹ = t := by rw [hxg]; group
    exact mem_conjSubgroup.2 (e ▸ ht)
  have hTxWC : IsWC (conjSubgroup g⁻¹ T) := h.pair.wc.conj g⁻¹
  have hxx : x * x = 1 := elemAbelian_mul_self hTxWC.1 hxTx
  have hxnT : x ∉ T := by
    intro hxT'
    refine hout x⁻¹ (T.inv_mem hxT') ?_
    rw [mul_inv_cancel]
    exact mem_sec4Ker.1 (sec4Ker T T₁ T₂).one_mem
  have hxnN : x ∉ sec4N T T₁ T₂ := by
    intro hxN'
    refine hout 1 T.one_mem ?_
    rw [mul_one]
    exact mem_sec4Ker.1 (h.sec4N_le_sec4Ker hxN')
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ sec4Y T T₁ T₂, x ∉ Subgroup.normalizer (conjSubgroup y T : Set G) := by
    by_contra hall
    push Not at hall
    obtain ⟨y₂, hy₂, hT₂⟩ := h.exists_mem_sec4Y_conj₂
    have hx₂ : x ∈ Subgroup.normalizer (T₂ : Set G) := hT₂ ▸ hall y₂ hy₂
    have := h.actsTriv_of_normalizes hnab h16 hxD hxT hx₁ hx₂
    refine hout 1 T.one_mem ?_
    rw [mul_one]
    exact this
  have hU0 := h.inf_sec4N_eq_bot_of_not_normalizer hxT hxN hxnN hxnT hy hxy hTx hxTx
  obtain ⟨F, hFTx, hF4, hFN, hFc⟩ := h.exists_big_F hnab h16 hL16 hxT hx₁ hxN hxnT hTx hxTx
  have hFab : IsElemAbelian 2 F := isElemAbelian_of_le hTxWC.1 hFTx
  have hFNN := h.le_normalizer_of_F hAsc h215 h26 hId hnab hind hq h16 hFab hFN hFc
  obtain ⟨f, P, _, _, π, e, hf, hsurj, hker, S, S₁, hS, hS₁, hS₁ne⟩ := h.exists_pi_two hAsc hq
  have hW' := hW f P hf e
  have hker' : ∀ y : ↥(sec4Y T T₁ T₂), π y = 1 → Sec4ActsTriv T T₁ T₂ (y : G) :=
    fun y hy => (hker y).1 hy
  have hn := h.sec4_three hAsc hq
  have hYinv : ∀ w ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G), ∀ y ∈ sec4Y T T₁ T₂,
      w * y * w⁻¹ ∈ sec4Y T T₁ T₂ := fun w hw y hy => by
    have := hn.conj_mem ⟨y, h.sec4Y_le_normalizer hy⟩ (Subgroup.mem_subgroupOf.2 hy) ⟨w, hw⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hff : ∀ w ∈ F, w * w = 1 := fun w hw => elemAbelian_mul_self hFab hw
  have hαex : ∀ (w : G) (hw : w ∈ F), ∃ α : MulAut P,
      (∀ y : ↥(sec4Y T T₁ T₂), α (π y) = π ⟨w * y * w⁻¹, hYinv w (hFNN w hw) y y.2⟩) ∧
        α * α = 1 := fun w hw =>
    h.exists_induced_aut π hsurj hker (hff w hw) (hYinv w (hFNN w hw)) (hFNN w hw)
  have hpres : ∀ (w : G) (hw : w ∈ F) (α : MulAut P)
      (_ : ∀ y : ↥(sec4Y T T₁ T₂), α (π y) = π ⟨w * y * w⁻¹, hYinv w (hFNN w hw) y y.2⟩)
      (U : Subgroup G) (hUY : U ≤ sec4Y T T₁ T₂),
      w ∈ Subgroup.normalizer (U : Set G) →
        ∀ z ∈ (U.subgroupOf (sec4Y T T₁ T₂)).map π, α z ∈ (U.subgroupOf (sec4Y T T₁ T₂)).map π := by
    intro w hw α hα U hUY hwU z hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hz
    rw [hα]
    exact Subgroup.mem_map.2 ⟨⟨w * u * w⁻¹, hYinv w (hFNN w hw) _ u.2⟩, Subgroup.mem_subgroupOf.2
      (conj_mem_of_mem_normalizer hwU (Subgroup.mem_subgroupOf.1 hu)), rfl⟩
  have hfinish : ∀ (w : G) (hw : w ∈ F), w ≠ 1 →
      (∀ y : ↥(sec4Y T T₁ T₂), π ⟨w * y * w⁻¹, hYinv w (hFNN w hw) y y.2⟩ = π y) → False := by
    intro w hw hw1 hπ
    have hact := h.actsTriv_of_pi_conj hq π hker' (hYinv w (hFNN w hw)) (hFNN w hw) hπ
    have hwTx : w ∈ conjSubgroup g⁻¹ T := hFTx hw
    have hwD : w ∈ classD T := mem_classD_of_mem_conjSubgroup hwTx hw1
    have hwN : w ∈ sec4N T T₁ T₂ :=
      hA G hnab hind T T₁ T₂ a h hq h16 w hwD (hFN w hw).1 hact
    have : w ∈ conjSubgroup g⁻¹ T ⊓ sec4N T T₁ T₂ := ⟨hwTx, hwN⟩
    rw [hU0, Subgroup.mem_bot] at this
    exact hw1 this
  obtain ⟨f₁, hf₁, hf₁1⟩ : ∃ f₁ ∈ F, f₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hcon
    rw [this, Subgroup.card_bot] at hF4
    omega
  obtain ⟨f₂, hf₂, hf₂K⟩ : ∃ f₂ ∈ F, f₂ ∉ Subgroup.zpowers f₁ := by
    by_contra hcon
    push Not at hcon
    have hle : F ≤ Subgroup.zpowers f₁ := hcon
    have h1 : Nat.card ↥F ≤ Nat.card ↥(Subgroup.zpowers f₁) := Subgroup.card_le_of_le hle
    have h2 : Nat.card ↥(Subgroup.zpowers f₁) ≤ 2 := by
      rw [Nat.card_zpowers]
      have hord : orderOf f₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by
        rw [pow_two]; exact hff f₁ hf₁)
      exact Nat.le_of_dvd (by norm_num) hord
    omega
  have hf₂1 : f₂ ≠ 1 := fun h1 => hf₂K (h1 ▸ (Subgroup.zpowers f₁).one_mem)
  have hf₁₂ : f₁ ≠ f₂ := fun h1 => hf₂K (h1 ▸ Subgroup.mem_zpowers f₁)
  have hcomm₁₂ : f₁ * f₂ = f₂ * f₁ := elemAbelian_mul_comm hFab hf₁ hf₂
  obtain ⟨α, hα, hαα⟩ := hαex f₁ hf₁
  obtain ⟨β, hβ, hββ⟩ := hαex f₂ hf₂
  have hTT : (T.subgroupOf (sec4Y T T₁ T₂)).map π = rootGroup S := hS
  have hTT₁ : (T₁.subgroupOf (sec4Y T T₁ T₂)).map π = rootGroup S₁ := hS₁
  have hαS : ∀ z ∈ rootGroup S, α z ∈ rootGroup S := fun z hz => by
    rw [← hTT] at hz ⊢
    exact hpres f₁ hf₁ α hα T left_le_sec4Y (hFN f₁ hf₁).1 z hz
  have hαS₁ : ∀ z ∈ rootGroup S₁, α z ∈ rootGroup S₁ := fun z hz => by
    rw [← hTT₁] at hz ⊢
    exact hpres f₁ hf₁ α hα T₁ mid_le_sec4Y (hFN f₁ hf₁).2 z hz
  have hβS : ∀ z ∈ rootGroup S, β z ∈ rootGroup S := fun z hz => by
    rw [← hTT] at hz ⊢
    exact hpres f₂ hf₂ β hβ T left_le_sec4Y (hFN f₂ hf₂).1 z hz
  have hβS₁ : ∀ z ∈ rootGroup S₁, β z ∈ rootGroup S₁ := fun z hz => by
    rw [← hTT₁] at hz ⊢
    exact hpres f₂ hf₂ β hβ T₁ mid_le_sec4Y (hFN f₂ hf₂).2 z hz
  have hαβ : α * β = β * α := by
    ext p
    obtain ⟨y, rfl⟩ := hsurj p
    have e1 : (α * β) (π y) = π ⟨f₁ * (f₂ * y * f₂⁻¹) * f₁⁻¹, hYinv f₁ (hFNN f₁ hf₁) _
        (hYinv f₂ (hFNN f₂ hf₂) y y.2)⟩ := by
      rw [MulAut.mul_apply, hβ y, hα ⟨f₂ * y * f₂⁻¹, hYinv f₂ (hFNN f₂ hf₂) y y.2⟩]
    have e2 : (β * α) (π y) = π ⟨f₂ * (f₁ * y * f₁⁻¹) * f₂⁻¹, hYinv f₂ (hFNN f₂ hf₂) _
        (hYinv f₁ (hFNN f₁ hf₁) y y.2)⟩ := by
      rw [MulAut.mul_apply, hα y, hβ ⟨f₁ * y * f₁⁻¹, hYinv f₁ (hFNN f₁ hf₁) y y.2⟩]
    rw [e1, e2]
    congr 1
    apply Subtype.ext
    calc f₁ * (f₂ * (y : G) * f₂⁻¹) * f₁⁻¹ = (f₁ * f₂) * y * (f₁ * f₂)⁻¹ := by group
      _ = (f₂ * f₁) * y * (f₂ * f₁)⁻¹ := by rw [hcomm₁₂]
      _ = f₂ * (f₁ * (y : G) * f₁⁻¹) * f₂⁻¹ := by group
  rcases hW'.klein S S₁ hS₁ne α β hαα hββ hαβ hαS hαS₁ hβS hβS₁ with h1 | h1 | h1
  · refine hfinish f₁ hf₁ hf₁1 fun y => ?_
    have := hα y
    rw [h1] at this
    exact this.symm
  · refine hfinish f₂ hf₂ hf₂1 fun y => ?_
    have := hβ y
    rw [h1] at this
    exact this.symm
  · have hf₁₂F : f₁ * f₂ ∈ F := F.mul_mem hf₁ hf₂
    have hf₁₂1 : f₁ * f₂ ≠ 1 := by
      intro h1'
      apply hf₁₂
      have : f₁ = f₂⁻¹ := eq_inv_of_mul_eq_one_left h1'
      rw [this]
      exact (inv_eq_of_mul_eq_one_right (hff f₂ hf₂)).symm ▸ rfl
    refine hfinish (f₁ * f₂) hf₁₂F hf₁₂1 fun y => ?_
    have e3 : π ⟨(f₁ * f₂) * y * (f₁ * f₂)⁻¹, hYinv _ (hFNN _ hf₁₂F) y y.2⟩ =
        α (β (π y)) := by
      rw [hβ y, hα ⟨f₂ * y * f₂⁻¹, hYinv f₂ (hFNN f₂ hf₂) y y.2⟩]
      congr 1
      apply Subtype.ext
      show (f₁ * f₂) * (y : G) * (f₁ * f₂)⁻¹ = f₁ * (f₂ * y * f₂⁻¹) * f₁⁻¹
      group
    rw [e3, ← h1]
    have := congrArg (fun m : MulAut P => m (π y)) hαα
    simpa using this

end CFSG.CGT.T75B
