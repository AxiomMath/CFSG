module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Cfg

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4

variable {G : Type} [Group G]

theorem relIndex_le_of_cover [Finite G] {K R V : Subgroup G} (hVR : V ≤ R)
    (hcov : ∀ r ∈ R, ∃ w ∈ V, w * r ∈ K) : K.relIndex R ≤ Nat.card V := by
  let f : ↥V → ↥R ⧸ K.subgroupOf R := fun w => QuotientGroup.mk ⟨(w : G)⁻¹, R.inv_mem (hVR w.2)⟩
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H r =>
      obtain ⟨w, hw, hwr⟩ := hcov r r.2
      refine ⟨⟨w, hw⟩, ?_⟩
      show (QuotientGroup.mk ⟨w⁻¹, _⟩ : ↥R ⧸ K.subgroupOf R) = QuotientGroup.mk r
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hwr
  have := Nat.card_le_card_of_surjective f hsurj
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact this

namespace Pair

variable {t s : Two G} (h : Pair t s)
include h

theorem lemma5 [Finite G] (hc : ∀ a ∈ t.A, ∀ b ∈ s.A, a * b = b * a) : False := by
  have hRmem : ∀ {x : G}, x ∈ t.A ⊔ s.A ↔ ∃ a ∈ t.A, ∃ b ∈ s.A, x = a * b :=
    fun {x} => mem_sup_of_commute hc
  have hAR : t.A ≤ t.A ⊔ s.A := le_sup_left
  have hBR : s.A ≤ t.A ⊔ s.A := le_sup_right
  have hAM : t.A ≤ t.M := h.cM.A_le_M
  have hBN : s.A ≤ s.M := h.cN.A_le_M
  have hRM : t.A ⊔ s.A ≤ t.M := sup_le hAM h.BleM
  have hRN : t.A ⊔ s.A ≤ s.M := sup_le h.AleN hBN
  have hRsq : ∀ {x : G}, x ∈ t.A ⊔ s.A → x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hRmem.1 hx
    have c1 := hc a ha b hb
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← c1]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [h.cM.A_sq ha, h.cN.A_sq hb, one_mul]
  have hRA : ∀ {x : G}, x ∈ t.A ⊔ s.A → ∀ a ∈ t.A, x * a = a * x := by
    intro x hx a ha
    obtain ⟨a', ha', b, hb, rfl⟩ := hRmem.1 hx
    have c1 := h.cM.A_comm ha' ha
    have c2 := hc a ha b hb
    calc a' * b * a = a' * (b * a) := by group
      _ = a' * (a * b) := by rw [← c2]
      _ = (a' * a) * b := by group
      _ = (a * a') * b := by rw [c1]
      _ = a * (a' * b) := by group
  have hRB : ∀ {x : G}, x ∈ t.A ⊔ s.A → ∀ b ∈ s.A, x * b = b * x := by
    intro x hx b hb
    obtain ⟨a', ha', b', hb', rfl⟩ := hRmem.1 hx
    have c1 := h.cN.A_comm hb' hb
    have c2 := hc a' ha' b hb
    calc a' * b' * b = a' * (b' * b) := by group
      _ = a' * (b * b') := by rw [c1]
      _ = (a' * b) * b' := by group
      _ = (b * a') * b' := by rw [c2]
      _ = b * (a' * b') := by group
  have hrX₂ : ∀ r ∈ t.A ⊔ s.A, conjSub r t.X₂ = t.X₂ := by
    intro r hr
    rcases h.cM.perm r (hRM hr) with ⟨-, e2⟩ | ⟨e1, e2⟩
    · exact e2
    · exfalso
      obtain ⟨w, hw, hw1⟩ := h.cM.blk₂.exists_ne_one
      have hcw : r * w = w * r := hRA hr w (t.V₂_le_A hw)
      have h1 : r * w * r⁻¹ ∈ conjSub r t.V₂ := conj_mem_conjSub hw
      have e : conjSub r t.V₂ = t.V₁ := by
        show conjSub r (pCoreOf 2 t.X₂) = pCoreOf 2 t.X₁
        rw [← pCoreOf_conjSub, e2]
      rw [e] at h1
      have e3 : r * w * r⁻¹ = w := by rw [hcw]; group
      rw [e3] at h1
      exact hw1 (h.cM.inf_V h1 hw)
  have hrY₂ : ∀ r ∈ t.A ⊔ s.A, conjSub r s.X₂ = s.X₂ := by
    intro r hr
    rcases h.cN.perm r (hRN hr) with ⟨-, e2⟩ | ⟨e1, e2⟩
    · exact e2
    · exfalso
      obtain ⟨w, hw, hw1⟩ := h.cN.blk₂.exists_ne_one
      have hcw : r * w = w * r := hRB hr w (s.V₂_le_A hw)
      have h1 : r * w * r⁻¹ ∈ conjSub r s.V₂ := conj_mem_conjSub hw
      have e : conjSub r s.V₂ = s.V₁ := by
        show conjSub r (pCoreOf 2 s.X₂) = pCoreOf 2 s.X₁
        rw [← pCoreOf_conjSub, e2]
      rw [e] at h1
      have e3 : r * w * r⁻¹ = w := by rw [hcw]; group
      rw [e3] at h1
      exact hw1 (h.cN.inf_V h1 hw)
  have hcov₁ : ∀ r ∈ t.A ⊔ s.A, ∃ w ∈ t.V₂, w * r ∈ Subgroup.centralizer (t.X₂ : Set G) := by
    intro r hr
    obtain ⟨w, hw, hwc⟩ := Blk3.exists_correction h.cM.blk₂ (hrX₂ r hr)
      (fun w hw => hRA hr w (t.V₂_le_A hw))
    refine ⟨w, hw, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hwc x hx).symm
  have hcov₂ : ∀ r ∈ t.A ⊔ s.A, ∃ w ∈ s.V₂, w * r ∈ Subgroup.centralizer (s.X₂ : Set G) := by
    intro r hr
    obtain ⟨w, hw, hwc⟩ := Blk3.exists_correction h.cN.blk₂ (hrY₂ r hr)
      (fun w hw => hRB hr w (s.V₂_le_A hw))
    refine ⟨w, hw, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hwc x hx).symm
  have hK₁ : (Subgroup.centralizer (t.X₂ : Set G)).relIndex (t.A ⊔ s.A) ≤ 4 := by
    have := relIndex_le_of_cover (le_trans t.V₂_le_A hAR) hcov₁
    rwa [h.cM.card_V₂] at this
  have hK₂ : (Subgroup.centralizer (s.X₂ : Set G)).relIndex (t.A ⊔ s.A) ≤ 4 := by
    have := relIndex_le_of_cover (le_trans s.V₂_le_A hBR) hcov₂
    rwa [h.cN.card_V₂] at this
  have hKK : (Subgroup.centralizer (t.X₂ : Set G) ⊓ Subgroup.centralizer (s.X₂ : Set G)).relIndex
      (t.A ⊔ s.A) ≤ 16 :=
    calc _ ≤ (Subgroup.centralizer (t.X₂ : Set G)).relIndex (t.A ⊔ s.A) *
          (Subgroup.centralizer (s.X₂ : Set G)).relIndex (t.A ⊔ s.A) := Subgroup.relIndex_inf_le
      _ ≤ 4 * 4 := Nat.mul_le_mul hK₁ hK₂
  have hcard := Subgroup.relIndex_mul_card
    (Subgroup.centralizer (t.X₂ : Set G) ⊓ Subgroup.centralizer (s.X₂ : Set G)) (t.A ⊔ s.A)
  have hne : (Subgroup.centralizer (t.X₂ : Set G) ⊓ Subgroup.centralizer (s.X₂ : Set G)) ⊓
      (t.A ⊔ s.A) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥((Subgroup.centralizer (t.X₂ : Set G) ⊓
        Subgroup.centralizer (s.X₂ : Set G)) ⊓ (t.A ⊔ s.A)) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    rw [h1, mul_one] at hcard
    have hRA' : t.A = t.A ⊔ s.A :=
      Subgroup.eq_of_le_of_card_ge hAR (by rw [h.cM.card_A, ← hcard]; exact hKK)
    have hBA : s.A ≤ t.A := by rw [hRA']; exact hBR
    have : s.A = t.A := Subgroup.eq_of_le_of_card_ge hBA (by rw [h.cM.card_A, h.cN.card_A])
    exact h.AneB this.symm
  obtain ⟨r, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hr := Subgroup.mem_inf.1 r.2
  have hrR : (r : G) ∈ t.A ⊔ s.A := hr.2
  have hrC := Subgroup.mem_inf.1 hr.1
  have hr1' : (r : G) ≠ 1 := fun e => hr1 (Subtype.ext e)
  have hcent : Subgroup.centralizer ({(r : G)} : Set G) ≤ t.M :=
    h.cM.cent r hr1' (hRsq hrR) (Or.inr fun x hx =>
      (Subgroup.mem_centralizer_iff.1 hrC.1 x hx).symm)
  apply h.Y₂nle
  intro y hy
  apply hcent
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.1 hrC.2 y hy

end Pair

end CFSG.CGT.PushingUpLit.A4.L34
