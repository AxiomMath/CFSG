module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Three
public import CFSG.CGT.PushingUpLit.LIT.A4.L34One

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4

variable {G : Type} [Group G]

namespace Pair

variable {t s : Two G} (h : Pair t s)
include h

theorem comm_of_normalizes [Finite G] {a : G} (ha : a ∈ t.A) (ha1 : conjSub a s.X₁ = s.X₁) :
    ∀ b ∈ s.A, a * b = b * a := by
  have haN : a ∈ s.M := h.AleN ha
  have ha2 : conjSub a s.X₂ = s.X₂ := by
    rcases h.cN.perm a haN with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact e2
    · exact absurd (ha1.symm.trans e1) h.cN.X_ne
  have key : ∀ {X : Subgroup G} (w : G), conjSub a X = X → w ∈ s.A → w ∈ pCoreOf 2 X →
      (∀ z, z ∈ pCoreOf 2 X → z ∈ t.A → z = 1) → a * w = w * a := by
    intro X w hX hwB hwV hinf
    have h1 : a * w * a⁻¹ * w⁻¹ ∈ pCoreOf 2 X :=
      (pCoreOf 2 X).mul_mem (conj_mem_pCoreOf hX hwV) ((pCoreOf 2 X).inv_mem hwV)
    have h2 : a * w * a⁻¹ * w⁻¹ ∈ t.A := by
      have hwM : w ∈ t.M := h.BleM hwB
      have h3 : w * a⁻¹ * w⁻¹ ∈ conjSub w t.A := conj_mem_conjSub (t.A.inv_mem ha)
      rw [h.cM.conjSub_A hwM] at h3
      have := t.A.mul_mem ha h3
      simpa [mul_assoc] using this
    have h4 := hinf _ h1 h2
    have h5 : a * w * a⁻¹ = w := by
      have := mul_inv_eq_one.1 h4
      exact this
    exact mul_inv_eq_iff_eq_mul.1 h5
  intro b hb
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := h.cN.mem_A_iff.1 hb
  have c1 : a * w₁ = w₁ * a :=
    key w₁ ha1 (s.V₁_le_A hw₁) hw₁ (fun z hz hzA => h.A_inf_W₁ hz hzA)
  have c2 : a * w₂ = w₂ * a :=
    key w₂ ha2 (s.V₂_le_A hw₂) hw₂ (fun z hz hzA => h.A_inf_W₂ hz hzA)
  calc a * (w₁ * w₂) = (a * w₁) * w₂ := by group
    _ = (w₁ * a) * w₂ := by rw [c1]
    _ = w₁ * (a * w₂) := by group
    _ = w₁ * (w₂ * a) := by rw [c2]
    _ = (w₁ * w₂) * a := by group

theorem comm_of_normalizes' [Finite G] {b : G} (hb : b ∈ s.A) (hb1 : conjSub b t.X₁ = t.X₁) :
    ∀ a ∈ t.A, b * a = a * b :=
  h.symm.comm_of_normalizes hb hb1

theorem exists_normalizing [Finite G] :
    ∃ w ∈ s.V₁, w ≠ 1 ∧ conjSub w t.X₁ = t.X₁ := by
  have hW1 : Nat.card s.V₁ = 4 := h.cN.card_V₁
  have hsq : ∀ x ∈ s.V₁, x * x = 1 := fun x hx => h.cN.sq_V₁ hx
  obtain ⟨p, hp, hp1⟩ := h.cN.blk₁.exists_ne_one
  obtain ⟨q, hq, hq1, hqp⟩ := exists_ne_of_card_four hW1 hsq hp
  have hpM : p ∈ t.M := h.BleM (s.V₁_le_A hp)
  have hqM : q ∈ t.M := h.BleM (s.V₁_le_A hq)
  rcases h.cM.perm p hpM with ⟨e1, -⟩ | ⟨e1, e1'⟩
  · exact ⟨p, hp, hp1, e1⟩
  · rcases h.cM.perm q hqM with ⟨f1, -⟩ | ⟨f1, f1'⟩
    · exact ⟨q, hq, hq1, f1⟩
    · refine ⟨p * q, s.V₁.mul_mem hp hq, ?_, ?_⟩
      · intro e
        apply hqp
        have h1 : q = p⁻¹ := eq_inv_of_mul_eq_one_right e
        rw [h1]
        exact inv_eq_of_mul_eq_one_right (hsq p hp)
      · rw [← conjSub_conjSub, f1, e1']

theorem normalizes_Y₁ [Finite G] {a : G} (ha : a ∈ t.A) : conjSub a s.X₁ = s.X₁ := by
  by_contra hne
  have haN : a ∈ s.M := h.AleN ha
  have hswap : conjSub a s.X₁ = s.X₂ ∧ conjSub a s.X₂ = s.X₁ := by
    rcases h.cN.perm a haN with hh | hh
    · exact absurd hh.1 hne
    · exact hh
  obtain ⟨w, hw, hw1, hwX⟩ := h.exists_normalizing
  have hwB : w ∈ s.A := s.V₁_le_A hw
  have hc : w * a = a * w := h.comm_of_normalizes' hwB hwX a ha
  have hw2 : w ∈ s.V₂ := by
    have h1 : a * w * a⁻¹ ∈ conjSub a s.V₁ := conj_mem_conjSub hw
    have e : conjSub a s.V₁ = s.V₂ := by
      show conjSub a (pCoreOf 2 s.X₁) = pCoreOf 2 s.X₂
      rw [← pCoreOf_conjSub, hswap.1]
    rw [e] at h1
    have e2 : a * w * a⁻¹ = w := by rw [← hc]; group
    rwa [e2] at h1
  exact hw1 (h.cN.inf_V hw hw2)

theorem comm_AB [Finite G] : ∀ a ∈ t.A, ∀ b ∈ s.A, a * b = b * a :=
  fun _ ha => h.comm_of_normalizes ha (h.normalizes_Y₁ ha)

end Pair


end CFSG.CGT.PushingUpLit.A4.L34
