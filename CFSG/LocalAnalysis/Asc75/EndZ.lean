module

public import CFSG.LocalAnalysis.Asc75.Swap
public import CFSG.GH74.Uniqueness.Statements

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

variable {G : Type*} [Group G]

@[expose] def zInvSet (A₁ A₂ : Subgroup G) : Set G :=
  {y | ∃ a ∈ uSet A₁ A₂, a ≠ 1 ∧ a * a = 1 ∧ ∃ g : G, y = g⁻¹ * a * g}

section ZSet

variable {A₁ A₂ : Subgroup G}

theorem mem_zInvSet_of_involution {a : G} (ha : a ∈ uSet A₁ A₂) (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    a ∈ zInvSet A₁ A₂ :=
  ⟨a, ha, ha1, ha2, 1, by simp⟩

theorem zInvSet_conj {y : G} (hy : y ∈ zInvSet A₁ A₂) (g : G) : g⁻¹ * y * g ∈ zInvSet A₁ A₂ := by
  obtain ⟨a, ha, ha1, ha2, k, rfl⟩ := hy
  exact ⟨a, ha, ha1, ha2, k * g, by group⟩

theorem zInvSet_mul_self {y : G} (hy : y ∈ zInvSet A₁ A₂) : y * y = 1 := by
  obtain ⟨a, ha, ha1, ha2, k, rfl⟩ := hy
  calc k⁻¹ * a * k * (k⁻¹ * a * k) = k⁻¹ * (a * a) * k := by group
    _ = 1 := by rw [ha2]; group

theorem zInvSet_ne_one {y : G} (hy : y ∈ zInvSet A₁ A₂) : y ≠ 1 := by
  obtain ⟨a, ha, ha1, ha2, k, rfl⟩ := hy
  intro e
  apply ha1
  calc a = k * (k⁻¹ * a * k) * k⁻¹ := by group
    _ = 1 := by rw [e]; group

theorem zInvSet_orderOf {y : G} (hy : y ∈ zInvSet A₁ A₂) : orderOf y = 2 :=
  orderOf_eq_two_of_mul_self_eq_one (zInvSet_mul_self hy) (zInvSet_ne_one hy)

theorem isInvariantInvolutionSet_zInvSet :
    CFSG.GH74.Uniqueness.IsInvariantInvolutionSet (zInvSet A₁ A₂) :=
  ⟨fun _ hz => zInvSet_orderOf hz, fun _ hz g => zInvSet_conj hz g⟩

end ZSet

section Rank

variable [Finite G]

theorem exists_involution_pair {A : Subgroup G} (h : 1 < CFSG.Open.pRank 2 A) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧ a * b = b * a := by
  obtain ⟨E, hEA, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two A
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 A := Nat.pow_le_pow_right (by norm_num) h
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE.2 x hx
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hne : E ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at h4
    omega
  obtain ⟨a', ha'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have haE : (a' : G) ∈ E := a'.2
  have ha1 : (a' : G) ≠ 1 := fun e => ha' (Subtype.ext e)
  have hnle : ¬ E ≤ Subgroup.zpowers (a' : G) := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_two_of_mul_self_eq_one (hsq _ haE) ha1] at h1
    omega
  obtain ⟨b, hbE, hbz⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hb1 : b ≠ 1 := fun e => hbz (by rw [e]; exact Subgroup.one_mem _)
  have hab : (a' : G) ≠ b := fun e => hbz (by rw [← e]; exact Subgroup.mem_zpowers _)
  exact ⟨a', hEA haE, b, hEA hbE, ha1, hb1, hab, hsq _ haE, hsq _ hbE, hcomm _ haE _ hbE⟩

theorem exists_involution_of_one_lt_pRank {A : Subgroup G} (h : 1 < CFSG.Open.pRank 2 A) :
    ∃ a ∈ A, a ≠ 1 ∧ a * a = 1 := by
  obtain ⟨a, ha, -, -, ha1, -, -, ha2, -, -⟩ := exists_involution_pair h
  exact ⟨a, ha, ha1, ha2⟩

theorem le_twoRank_of_elemAbelian_le {L E : Subgroup G} (hEL : E ≤ L)
    (hE : CFSG.Open.IsElemAbelian 2 E) {k : ℕ} (hk : Nat.card E = 2 ^ k) :
    k ≤ CFSG.Open.twoRank ↥L := by
  have := hE.1
  exact CFSG.SectionRank.le_pRank_of_injective (G := ↥L) one_lt_two
    (fun a b => mul_comm' a b) (fun a => Subtype.ext (by simpa using hE.2 a a.2)) hk
    (Subgroup.inclusion hEL) (Subgroup.inclusion_injective hEL) le_top

end Rank

theorem isPGroup_closure_commuting_involutions {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : IsPGroup 2 (Subgroup.closure ({x, y} : Set G)) := by
  have hgen : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.centralizer ({x, y} : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    intro c hc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro d hd
    rcases hd with rfl | hd
    · rcases hc with rfl | hc
      · rfl
      · rw [Set.mem_singleton_iff] at hc
        rw [hc]; exact hxy
    · rw [Set.mem_singleton_iff] at hd
      subst hd
      rcases hc with rfl | hc
      · exact hxy.symm
      · rw [Set.mem_singleton_iff] at hc
        rw [hc]
  have hcomm : ∀ a ∈ Subgroup.closure ({x, y} : Set G), ∀ b ∈ Subgroup.closure ({x, y} : Set G),
      a * b = b * a := by
    intro a ha b hb
    have ha' := Subgroup.mem_centralizer_iff.1 (hgen ha)
    have hle : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
      refine (Subgroup.closure_le _).2 ?_
      intro c hc
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro d hd
      rw [Set.mem_singleton_iff] at hd
      subst hd
      exact (ha' c hc).symm
    exact Subgroup.mem_centralizer_iff.1 (hle hb) a (Set.mem_singleton a)
  have hsq : ∀ w ∈ Subgroup.closure ({x, y} : Set G), w * w = 1 := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem c hc =>
      rcases hc with rfl | hc
      · exact hx
      · rw [Set.mem_singleton_iff] at hc
        rw [hc]; exact hy
    | one => simp
    | mul a b ha hb iha ihb =>
      have := hcomm a ha b hb
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [this]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb]; simp
    | inv a ha iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha]; simp
  intro w
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [pow_one, sq] using hsq w.1 w.2

section Product

variable [Finite G] {S A₁ A₂ H : Subgroup G}

theorem Hyp.exists_conj_pair_mem (h : Hyp S A₁ A₂ H) {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : ∃ k : G, k⁻¹ * x * k ∈ S ∧ k⁻¹ * y * k ∈ S := by
  obtain ⟨k, -, hk⟩ := exists_conj_mem_sylow (⊤ : Subgroup G) h.sylowG le_top
    (Subgroup.closure ({x, y} : Set G)) le_top (isPGroup_closure_commuting_involutions hx hy hxy)
  exact ⟨k, hk x (Subgroup.subset_closure (by simp)), hk y (Subgroup.subset_closure (by simp))⟩

theorem Hyp.mem_uSet_of_mem_zInvSet (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥) {y : G}
    (hy : y ∈ zInvSet A₁ A₂) {k : G} (hk : k⁻¹ * y * k ∈ S) : k⁻¹ * y * k ∈ uSet A₁ A₂ := by
  obtain ⟨a, ha, ha1, ha2, g, rfl⟩ := hy
  have e : k⁻¹ * (g⁻¹ * a * g) * k = (g * k)⁻¹ * a * (g * k) := by group
  rw [e] at hk ⊢
  exact h.closed_G hdisj ha hk

omit [Finite G] in
theorem fixedOnlyElt_mul_of_mem_uSet
    (hf : ∀ a ∈ uSet A₁ A₂, a ≠ 1 → FixedOnlyElt H a)
    (hg : ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂, a₁ ≠ 1 → a₂ ≠ 1 → a₁ * a₁ = 1 → a₂ * a₂ = 1 →
      FixedOnlyElt H (a₁ * a₂))
    {x y : G} (hx : x ∈ uSet A₁ A₂) (hy : y ∈ uSet A₁ A₂) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) (hne : x * y ≠ 1) :
    FixedOnlyElt H (x * y) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hf _ (Or.inl (A₁.mul_mem hx hy)) hne
  · exact hg x hx y hy hx1 hy1 hx2 hy2
  · have := hg y hy x hx hy1 hx1 hy2 hx2
    rwa [← hxy] at this
  · exact hf _ (Or.inr (A₂.mul_mem hx hy)) hne

theorem isProductDisconnected_zInvSet (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥) (hne : H ≠ ⊤)
    (hf : ∀ a ∈ uSet A₁ A₂, a ≠ 1 → FixedOnlyElt H a)
    (hg : ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂, a₁ ≠ 1 → a₂ ≠ 1 → a₁ * a₁ = 1 → a₂ * a₂ = 1 →
      FixedOnlyElt H (a₁ * a₂)) :
    CFSG.GH74.Uniqueness.IsProductDisconnected (zInvSet A₁ A₂) H := by
  refine ⟨hne, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, ha1, ha2⟩ := exists_involution_of_one_lt_pRank h.rank₁
    exact ⟨a, mem_zInvSet_of_involution (Or.inl ha) ha1 ha2, h.le_H₁ ha⟩
  · intro z hz hzH g
    obtain ⟨a, ha, ha1, ha2, k, rfl⟩ := hz
    have hfa := hf a ha ha1
    have hk : k ∈ H := hfa.2 k hzH
    constructor
    · intro hg'
      have hkg : (k * g)⁻¹ * a * (k * g) ∈ H := by
        have e : (k * g)⁻¹ * a * (k * g) = g⁻¹ * (k⁻¹ * a * k) * g := by group
        rw [e]; exact hg'
      have := hfa.2 _ hkg
      have e : g = k⁻¹ * (k * g) := by group
      rw [e]
      exact H.mul_mem (H.inv_mem hk) this
    · intro hgH
      exact H.mul_mem (H.mul_mem (H.inv_mem hgH) hzH) hgH
  · rintro u ⟨hu2, x, hx, y, hy, hxy, rfl⟩ huH d hd
    have hx2 := zInvSet_mul_self hx
    have hy2 := zInvSet_mul_self hy
    have hu1 : x * y ≠ 1 := fun e => by rw [e, orderOf_one] at hu2; omega
    obtain ⟨k, hkx, hky⟩ := h.exists_conj_pair_mem hx2 hy2 hxy
    have hx' := h.mem_uSet_of_mem_zInvSet hdisj hx hkx
    have hy' := h.mem_uSet_of_mem_zInvSet hdisj hy hky
    have hx'1 : k⁻¹ * x * k ≠ 1 := by
      intro e
      apply zInvSet_ne_one hx
      calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
        _ = 1 := by rw [e]; group
    have hy'1 : k⁻¹ * y * k ≠ 1 := by
      intro e
      apply zInvSet_ne_one hy
      calc y = k * (k⁻¹ * y * k) * k⁻¹ := by group
        _ = 1 := by rw [e]; group
    have hx'2 : (k⁻¹ * x * k) * (k⁻¹ * x * k) = 1 := by
      calc (k⁻¹ * x * k) * (k⁻¹ * x * k) = k⁻¹ * (x * x) * k := by group
        _ = 1 := by rw [hx2]; group
    have hy'2 : (k⁻¹ * y * k) * (k⁻¹ * y * k) = 1 := by
      calc (k⁻¹ * y * k) * (k⁻¹ * y * k) = k⁻¹ * (y * y) * k := by group
        _ = 1 := by rw [hy2]; group
    have hxy' : (k⁻¹ * x * k) * (k⁻¹ * y * k) = (k⁻¹ * y * k) * (k⁻¹ * x * k) := by
      calc (k⁻¹ * x * k) * (k⁻¹ * y * k) = k⁻¹ * (x * y) * k := by group
        _ = k⁻¹ * (y * x) * k := by rw [hxy]
        _ = (k⁻¹ * y * k) * (k⁻¹ * x * k) := by group
    have hu'1 : (k⁻¹ * x * k) * (k⁻¹ * y * k) ≠ 1 := by
      intro e
      apply hu1
      calc x * y = k * ((k⁻¹ * x * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
        _ = 1 := by rw [e]; group
    have hfix : FixedOnlyElt H ((k⁻¹ * x * k) * (k⁻¹ * y * k)) :=
      fixedOnlyElt_mul_of_mem_uSet hf hg hx' hy' hx'1 hy'1 hx'2 hy'2 hxy' hu'1
    have hkH : k ∈ H := by
      have hk' : k⁻¹ ∈ H := by
        refine hfix.2 k⁻¹ ?_
        have e : (k⁻¹)⁻¹ * ((k⁻¹ * x * k) * (k⁻¹ * y * k)) * k⁻¹ = x * y := by group
        rw [e]; exact huH
      simpa using H.inv_mem hk'
    have hdc : (x * y) * d = d * (x * y) := Subgroup.mem_centralizer_iff.1 hd (x * y) rfl
    have h1 : d⁻¹ * (x * y) * d = x * y := by
      calc d⁻¹ * (x * y) * d = d⁻¹ * ((x * y) * d) := by group
        _ = d⁻¹ * (d * (x * y)) := by rw [hdc]
        _ = x * y := by group
    have hconj : (k⁻¹ * d * k)⁻¹ * ((k⁻¹ * x * k) * (k⁻¹ * y * k)) * (k⁻¹ * d * k) =
        (k⁻¹ * x * k) * (k⁻¹ * y * k) := by
      calc (k⁻¹ * d * k)⁻¹ * ((k⁻¹ * x * k) * (k⁻¹ * y * k)) * (k⁻¹ * d * k)
          = k⁻¹ * (d⁻¹ * (x * y) * d) * k := by group
        _ = k⁻¹ * (x * y) * k := by rw [h1]
        _ = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by group
    have hd' : k⁻¹ * d * k ∈ H := hfix.mem_of_conj_eq hconj
    have e : d = k * (k⁻¹ * d * k) * k⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hkH hd') (H.inv_mem hkH)

end Product

end CFSG.Asc75
