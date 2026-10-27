module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {H : Type} [Group H] [Finite H]

theorem l62_commute_of_isElemAbelian {A : Subgroup H} (hA : IsElemAbelian 3 A) (x y : A) :
    Commute (x : H) (y : H) :=
  (commute_iff_eq _ _).2 (congrArg Subtype.val (hA.1.is_comm.comm x y))

theorem l62_card_le_three_of_cyclic {A : Subgroup H} (hA : IsElemAbelian 3 A) (hc : IsCyclic A) :
    Nat.card A ≤ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥A)
  have h3 : (g : H) ^ 3 = 1 := hA.2 _ g.2
  have hg3 : g ^ 3 = 1 := Subtype.ext h3
  have hord : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  rw [orderOf_eq_card_of_forall_mem_zpowers hg] at hord
  exact Nat.le_of_dvd (by norm_num) hord

theorem l62_card_triple_prod {A₁ A₂ A₃ : Subgroup H}
    (h₁ : IsElemAbelian 3 A₁) (h₂ : IsElemAbelian 3 A₂) (h₃ : IsElemAbelian 3 A₃)
    (c12 : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (c13 : ∀ a ∈ A₁, ∀ c ∈ A₃, a * c = c * a)
    (c23 : ∀ b ∈ A₂, ∀ c ∈ A₃, b * c = c * b)
    (n₁ : Nat.card A₁ = 9) (n₂ : Nat.card A₂ = 9) (n₃ : Nat.card A₃ = 9)
    {Z₂ Z₃ : Subgroup H} (hZ₂ : Nat.card Z₂ ≤ 3) (hZ₃ : Nat.card Z₃ ≤ 3)
    (hker : ∀ a ∈ A₁, ∀ b ∈ A₂, ∀ c ∈ A₃, a * b * c = 1 → b ∈ Z₂ ∧ c ∈ Z₃) :
    IsElemAbelian 3 (A₁ ⊔ A₂ ⊔ A₃) ∧ 81 ≤ Nat.card ↥(A₁ ⊔ A₂ ⊔ A₃) := by
  have k12 : ∀ a : ↥A₁, ∀ b : ↥A₂, Commute (a : H) (b : H) := fun a b =>
    (commute_iff_eq _ _).2 (c12 a a.2 b b.2)
  have k13 : ∀ a : ↥A₁, ∀ c : ↥A₃, Commute (a : H) (c : H) := fun a c =>
    (commute_iff_eq _ _).2 (c13 a a.2 c c.2)
  have k23 : ∀ b : ↥A₂, ∀ c : ↥A₃, Commute (b : H) (c : H) := fun b c =>
    (commute_iff_eq _ _).2 (c23 b b.2 c c.2)
  obtain ⟨ψ₁₂, hψ₁₂⟩ : ∃ ψ₁₂ : (↥A₁ × ↥A₂) →* H,
      ∀ m : ↥A₁ × ↥A₂, ψ₁₂ m = (m.1 : H) * (m.2 : H) :=
    ⟨A₁.subtype.noncommCoprod A₂.subtype (fun a b => by simpa using k12 a b),
      fun m => by simp [MonoidHom.noncommCoprod_apply]⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ((↥A₁ × ↥A₂) × ↥A₃) →* H,
      ∀ (a : ↥A₁) (b : ↥A₂) (c : ↥A₃), ψ ((a, b), c) = (a : H) * (b : H) * (c : H) :=
    ⟨ψ₁₂.noncommCoprod A₃.subtype (fun m c => by
        rw [hψ₁₂]
        simp only [Subgroup.coe_subtype]
        exact Commute.mul_left (k13 m.1 c) (k23 m.2 c)),
      fun a b c => by simp [MonoidHom.noncommCoprod_apply, hψ₁₂]⟩
  have hS : A₁ ⊔ A₂ ⊔ A₃ = ψ.range := by
    refine le_antisymm (sup_le (sup_le ?_ ?_) ?_) ?_
    · intro x hx
      exact MonoidHom.mem_range.2 ⟨((⟨x, hx⟩, 1), 1), by simp [hψ]⟩
    · intro x hx
      exact MonoidHom.mem_range.2 ⟨((1, ⟨x, hx⟩), 1), by simp [hψ]⟩
    · intro x hx
      exact MonoidHom.mem_range.2 ⟨((1, 1), ⟨x, hx⟩), by simp [hψ]⟩
    · intro y hy
      obtain ⟨⟨⟨a, b⟩, c⟩, rfl⟩ := MonoidHom.mem_range.1 hy
      rw [hψ]
      exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left a.2))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right b.2))) (Subgroup.mem_sup_right c.2)
  have hcomm : ∀ u ∈ ψ.range, ∀ v ∈ ψ.range, u * v = v * u := by
    intro u hu v hv
    obtain ⟨⟨⟨a, b⟩, c⟩, rfl⟩ := MonoidHom.mem_range.1 hu
    obtain ⟨⟨⟨a', b'⟩, c'⟩, rfl⟩ := MonoidHom.mem_range.1 hv
    simp only [hψ]
    have va : Commute (a : H) ((a' : H) * (b' : H) * (c' : H)) :=
      ((l62_commute_of_isElemAbelian h₁ a a').mul_right (k12 a b')).mul_right (k13 a c')
    have vb : Commute (b : H) ((a' : H) * (b' : H) * (c' : H)) :=
      ((k12 a' b).symm.mul_right (l62_commute_of_isElemAbelian h₂ b b')).mul_right (k23 b c')
    have vc : Commute (c : H) ((a' : H) * (b' : H) * (c' : H)) :=
      ((k13 a' c).symm.mul_right (k23 b' c).symm).mul_right
        (l62_commute_of_isElemAbelian h₃ c c')
    exact (commute_iff_eq _ _).1 ((va.mul_left vb).mul_left vc)
  have hpow : ∀ g ∈ ψ.range, g ^ 3 = 1 := by
    intro g hg
    obtain ⟨⟨⟨a, b⟩, c⟩, rfl⟩ := MonoidHom.mem_range.1 hg
    simp only [hψ]
    have ha3 : (a : H) ^ 3 = 1 := h₁.2 _ a.2
    have hb3 : (b : H) ^ 3 = 1 := h₂.2 _ b.2
    have hc3 : (c : H) ^ 3 = 1 := h₃.2 _ c.2
    rw [(Commute.mul_left (k13 a c) (k23 b c)).mul_pow 3, (k12 a b).mul_pow 3]
    simp [ha3, hb3, hc3]
  have hEA : IsElemAbelian 3 ψ.range :=
    ⟨⟨⟨fun u v => Subtype.ext (hcomm (u : H) u.2 (v : H) v.2)⟩⟩, fun g hg => hpow g hg⟩
  have hmem : ∀ x : (↥A₁ × ↥A₂) × ↥A₃, x ∈ ψ.ker → (x.1.2 : H) ∈ Z₂ ∧ (x.2 : H) ∈ Z₃ := by
    rintro ⟨⟨a, b⟩, c⟩ hx
    have h1 : (a : H) * (b : H) * (c : H) = 1 := by
      have := MonoidHom.mem_ker.1 hx
      rwa [hψ] at this
    exact hker (a : H) a.2 (b : H) b.2 (c : H) c.2 h1
  have hkey : ∀ x x' : (↥A₁ × ↥A₂) × ↥A₃, x ∈ ψ.ker → x' ∈ ψ.ker →
      (x.1.2 : H) = (x'.1.2 : H) → (x.2 : H) = (x'.2 : H) → x = x' := by
    rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ hx hx' hb0 hc0
    have hb : (b : H) = (b' : H) := hb0
    have hc : (c : H) = (c' : H) := hc0
    have h1 : (a : H) * (b : H) * (c : H) = 1 := by
      have := MonoidHom.mem_ker.1 hx
      rwa [hψ] at this
    have h2 : (a' : H) * (b' : H) * (c' : H) = 1 := by
      have := MonoidHom.mem_ker.1 hx'
      rwa [hψ] at this
    have h3 : (a : H) * (b : H) * (c : H) = (a' : H) * (b' : H) * (c' : H) := by
      rw [h1, h2]
    rw [hb, hc] at h3
    have e : (a : H) = (a' : H) := mul_right_cancel (mul_right_cancel h3)
    have ea : a = a' := Subtype.ext e
    have eb : b = b' := Subtype.ext hb
    have ec : c = c' := Subtype.ext hc
    rw [ea, eb, ec]
  have hkerle : Nat.card ↥ψ.ker ≤ 9 := by
    let f : ↥ψ.ker → Z₂ × Z₃ := fun y =>
      (⟨(y.1.1.2 : H), (hmem y.1 y.2).1⟩, ⟨(y.1.2 : H), (hmem y.1 y.2).2⟩)
    have hf : Function.Injective f := by
      intro y y' hyy
      have hb : (y.1.1.2 : H) = (y'.1.1.2 : H) := congrArg (fun p : Z₂ × Z₃ => (p.1 : H)) hyy
      have hc : (y.1.2 : H) = (y'.1.2 : H) := congrArg (fun p : Z₂ × Z₃ => (p.2 : H)) hyy
      exact Subtype.ext (hkey y.1 y'.1 y.2 y'.2 hb hc)
    have hle := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at hle
    exact le_trans hle (le_trans (Nat.mul_le_mul hZ₂ hZ₃) (by norm_num))
  have hG : Nat.card ((↥A₁ × ↥A₂) × ↥A₃) = 729 := by
    simp [Nat.card_prod, n₁, n₂, n₃]
  have hsplit : Nat.card ((↥A₁ × ↥A₂) × ↥A₃) = Nat.card ↥ψ.range * Nat.card ↥ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have h729 : Nat.card ↥ψ.range * Nat.card ↥ψ.ker = 729 := by
    rw [← hsplit, hG]
  have h9 : Nat.card ↥ψ.range * Nat.card ↥ψ.ker ≤ Nat.card ↥ψ.range * 9 :=
    Nat.mul_le_mul (le_refl _) hkerle
  have hR : 81 ≤ Nat.card ↥ψ.range := by
    linarith
  rw [hS]
  exact ⟨hEA, hR⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
