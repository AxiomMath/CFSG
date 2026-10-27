module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Relations
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open scoped commutatorElement
open Subgroup Relation CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup H}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : H} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, (mul_one x).symm⟩
    · exact ⟨1, A.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hc a' ha' b hb]
      _ = a * a' * (b * b') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := hc a ha b hb
    calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [this]
      _ = a⁻¹ * b⁻¹ := by group

theorem commutator_mul_left_of_commute {ζ x y : H} (hx : Commute ζ x) (hy : Commute ζ y) :
    ⁅ζ * x, y⁆ = ⁅x, y⁆ := by
  have hw : Commute ζ (x * y * x⁻¹) := (hx.mul_right hy).mul_right hx.inv_right
  calc ⁅ζ * x, y⁆ = ζ * (x * y * x⁻¹) * ζ⁻¹ * y⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ := by rw [hw.eq, mul_inv_cancel_right]; simp only [commutatorElement_def]

theorem commutator_mul_right_of_commute {ζ x y : H} (hx : Commute ζ x) (hy : Commute ζ y) :
    ⁅x, ζ * y⁆ = ⁅x, y⁆ := by
  rw [← commutatorElement_inv, commutator_mul_left_of_commute hy hx, commutatorElement_inv]

theorem commutator_mul_mul_of_commute {ζ₁ ζ₂ p₁ p₂ : H} (h12 : Commute ζ₁ ζ₂)
    (h1 : Commute ζ₁ p₁) (h2 : Commute ζ₁ p₂) (h3 : Commute ζ₂ p₁) (h4 : Commute ζ₂ p₂) :
    ⁅ζ₁ * p₁, ζ₂ * p₂⁆ = ⁅p₁, p₂⁆ := by
  rw [commutator_mul_left_of_commute h1 (h12.mul_right h2),
    commutator_mul_right_of_commute h3 h4]


theorem mul_self_eq_one_of_orderOf_eq_two {s : H} (hs : orderOf s = 2) : s * s = 1 := by
  rw [← pow_two, ← hs, pow_orderOf_eq_one]

@[expose] def foldHom (s : H) (L : Subgroup H)
    (hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj s).toMonoidHom, a * b = b * a) : ↥L →* H where
  toFun a := (a : H) * (s * a * s⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have h := hc b b.2 (s * a * s⁻¹) ⟨a, a.2, by simp [MulAut.conj_apply]⟩
    show (a : H) * b * (s * (a * b) * s⁻¹) = (a * (s * a * s⁻¹)) * (b * (s * b * s⁻¹))
    calc (a : H) * b * (s * (a * b) * s⁻¹)
        = a * (b * (s * a * s⁻¹)) * (s * b * s⁻¹) := by group
      _ = a * ((s * a * s⁻¹) * b) * (s * b * s⁻¹) := by rw [h]
      _ = _ := by group

theorem foldHom_apply (s : H) (L : Subgroup H)
    (hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj s).toMonoidHom, a * b = b * a) (a : ↥L) :
    foldHom s L hc a = (a : H) * (s * a * s⁻¹) := rfl


theorem exists_eq_mul_foldHom {s : H} (hs : s * s = 1) {L : Subgroup H}
    (hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj s).toMonoidHom, a * b = b * a) {k : H}
    (hks : s * k = k * s) (hk : k ∈ L ⊔ L.map (MulAut.conj s).toMonoidHom) :
    ∃ ζ ∈ L, ζ ∈ L.map (MulAut.conj s).toMonoidHom ∧ ∃ b : ↥L, k = ζ * foldHom s L hc b := by
  obtain ⟨a, ha, b', hb', rfl⟩ := exists_mul_of_mem_sup_of_commute hc hk
  obtain ⟨b, hb, rfl⟩ := hb'
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hbs : (MulAut.conj s).toMonoidHom b = s * b * s := by
    simp [MulAut.conj_apply, hsi]
  rw [hbs] at hks ⊢
  set a₁ := s * a * s with ha₁
  set b' := s * b * s with hb'
  have hb'L : b' ∈ L.map (MulAut.conj s).toMonoidHom := ⟨b, hb, hbs⟩
  have ha₁L : a₁ ∈ L.map (MulAut.conj s).toMonoidHom :=
    ⟨a, ha, by simp [MulAut.conj_apply, hsi, ha₁]⟩
  have h1 : a₁ * b = a * b' := by
    refine mul_right_cancel (b := s) ?_
    calc a₁ * b * s = s * (a * b') := by simp only [ha₁, hb']; group
      _ = a * b' * s := hks
  have hba : b * a₁ = a₁ * b := hc b hb a₁ ha₁L
  have hζ' : b⁻¹ * a ∈ L.map (MulAut.conj s).toMonoidHom := by
    have : b⁻¹ * a = a₁ * b'⁻¹ := by
      calc b⁻¹ * a = b⁻¹ * (a₁ * b) * b'⁻¹ := by rw [h1]; group
        _ = a₁ * b'⁻¹ := by rw [← hba]; group
    rw [this]
    exact Subgroup.mul_mem _ ha₁L (Subgroup.inv_mem _ hb'L)
  have hζ : b⁻¹ * a ∈ L := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) ha
  refine ⟨b⁻¹ * a, hζ, hζ', ⟨b, hb⟩, ?_⟩
  have hbζ : b * (b⁻¹ * a) = (b⁻¹ * a) * b := hc b hb _ hζ'
  rw [foldHom_apply]
  simp only [hsi]
  calc a * b' = b * (b⁻¹ * a) * b' := by group
    _ = (b⁻¹ * a) * b * b' := by rw [hbζ]
    _ = _ := by simp only [hb']; group


theorem commute_foldHom {s : H} {L : Subgroup H}
    (hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj s).toMonoidHom, a * b = b * a) {ζ : H} (hζ : ζ ∈ L)
    (hζ' : ζ ∈ L.map (MulAut.conj s).toMonoidHom) (b : ↥L) : Commute ζ (foldHom s L hc b) := by
  rw [foldHom_apply]
  refine Commute.mul_right (hc b b.2 ζ hζ').symm ?_
  exact hc ζ hζ _ ⟨b, b.2, by simp [MulAut.conj_apply]⟩

theorem le_range_foldHom {s : H} (hs : s * s = 1) {K L : Subgroup H}
    (hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj s).toMonoidHom, a * b = b * a)
    (hKs : K ≤ centralizer ({s} : Set H)) (hKp : Group.IsPerfect ↥K)
    (hKL : K ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom) : K ≤ (foldHom s L hc).range := by
  have hper : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 hKp
  calc K = ⁅K, K⁆ := hper.symm
    _ ≤ _ := by
      rw [Subgroup.commutator_le]
      intro k₁ hk₁ k₂ hk₂
      obtain ⟨ζ₁, hζ₁, hζ₁', b₁, rfl⟩ := exists_eq_mul_foldHom hs hc
        (mem_centralizer_singleton_iff.1 (hKs hk₁)).symm (hKL hk₁)
      obtain ⟨ζ₂, hζ₂, hζ₂', b₂, rfl⟩ := exists_eq_mul_foldHom hs hc
        (mem_centralizer_singleton_iff.1 (hKs hk₂)).symm (hKL hk₂)
      rw [commutator_mul_mul_of_commute (hc ζ₁ hζ₁ ζ₂ hζ₂') (commute_foldHom hc hζ₁ hζ₁' b₁)
        (commute_foldHom hc hζ₁ hζ₁' b₂) (commute_foldHom hc hζ₂ hζ₂' b₁)
        (commute_foldHom hc hζ₂ hζ₂' b₂), ← map_commutatorElement]
      exact ⟨_, rfl⟩


theorem le_of_conj_eq {K L : Subgroup H} {s : H} (hLe : L.map (MulAut.conj s).toMonoidHom = L)
    (hKL : K ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom) : K ≤ L := by
  rwa [hLe, sup_idem] at hKL

theorem isCompIn_conj_of_commute {L : Subgroup H} {s t : H} (hst : s * t = t * s)
    (hL : IsCompIn L (centralizer ({t} : Set H))) :
    IsCompIn (L.map (MulAut.conj s).toMonoidHom) (centralizer ({t} : Set H)) :=
  hL.map_conj (mem_centralizer_singleton_iff.2 hst)

theorem commute_conj_of_ne [Finite H] {L : Subgroup H} {s t : H} (hst : s * t = t * s)
    (hL : IsCompIn L (centralizer ({t} : Set H)))
    (hLe : L.map (MulAut.conj s).toMonoidHom ≠ L) :
    ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj s).toMonoidHom, a * b = b * a :=
  hL.commute_of_ne (isCompIn_conj_of_commute hst hL) (Ne.symm hLe)

theorem inLF_right_of_ltF {K L : Subgroup H} (h : LtF K L) : InLF L := by
  obtain ⟨-, t, -, ht, -, -, hL, -⟩ := h
  exact ⟨t, ht, hL⟩

theorem inLF_right_of_transGen_ltF {K L : Subgroup H} (h : TransGen LtF K L) : InLF L := by
  induction h with
  | single h => exact inLF_right_of_ltF h
  | tail _ h _ => exact inLF_right_of_ltF h

section Finite

variable [Finite H]

theorem card_le_of_ltF_aux {K L : Subgroup H} {s t : H} (hs : orderOf s = 2) (hst : s * t = t * s)
    (hK : IsCompIn K (centralizer ({s} : Set H))) (hL : IsCompIn L (centralizer ({t} : Set H)))
    (hKL : K ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom) :
    Nat.card K ≤ Nat.card L ∧ (Nat.card K = Nat.card L → Nonempty (↥K ≃* ↥L)) := by
  by_cases hLe : L.map (MulAut.conj s).toMonoidHom = L
  · have hKL' := le_of_conj_eq hLe hKL
    refine ⟨Subgroup.card_le_of_le hKL', fun h => ?_⟩
    exact ⟨MulEquiv.subgroupCongr (Subgroup.eq_of_le_of_card_ge hKL' h.ge)⟩
  · have hc := commute_conj_of_ne hst hL hLe
    have hle := le_range_foldHom (mul_self_eq_one_of_orderOf_eq_two hs) hc
      (fun _ hx => hK.le hx) hK.isQuasisimple.1 hKL
    have hsurj := (foldHom s L hc).rangeRestrict_surjective
    have hrL : Nat.card (foldHom s L hc).range ≤ Nat.card L :=
      Nat.card_le_card_of_surjective _ hsurj
    have hKr : Nat.card K ≤ Nat.card (foldHom s L hc).range := Subgroup.card_le_of_le hle
    refine ⟨hKr.trans hrL, fun h => ?_⟩
    have hKeq : K = (foldHom s L hc).range :=
      Subgroup.eq_of_le_of_card_ge hle (hrL.trans h.ge)
    have hbij := hsurj.bijective_of_nat_card_le (h ▸ hKr)
    exact ⟨(MulEquiv.subgroupCongr hKeq).trans (MulEquiv.ofBijective _ hbij).symm⟩

theorem card_le_of_ltF {K L : Subgroup H} (h : LtF K L) :
    Nat.card K ≤ Nat.card L ∧ (Nat.card K = Nat.card L → Nonempty (↥K ≃* ↥L)) := by
  obtain ⟨s, t, hs, -, hst, hK, hL, hKL⟩ := h
  exact card_le_of_ltF_aux hs hst hK hL hKL

theorem card_le_of_transGen_ltF {K L : Subgroup H} (h : TransGen LtF K L) :
    Nat.card K ≤ Nat.card L ∧ (Nat.card K = Nat.card L → Nonempty (↥K ≃* ↥L)) := by
  induction h with
  | single h => exact card_le_of_ltF h
  | tail _ h ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := card_le_of_ltF h
    refine ⟨h1.trans h3, fun heq => ?_⟩
    obtain ⟨e1⟩ := h2 (by omega)
    obtain ⟨e2⟩ := h4 (by omega)
    exact ⟨e1.trans e2⟩

theorem exists_maximalF_above {K₀ : Subgroup H} (h₀ : InLF K₀) :
    ∃ M : Subgroup H, (M = K₀ ∨ TransGen LtF K₀ M) ∧ MaximalF M ∧
      ∀ L : Subgroup H, TransGen LtF K₀ L → Nat.card L ≤ Nat.card M := by
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image {L : Subgroup H | L = K₀ ∨ TransGen LtF K₀ L}
    (fun L => Nat.card L) (Set.toFinite _) ⟨K₀, Or.inl rfl⟩
  have hup : ∀ L, TransGen LtF K₀ L → Nat.card L ≤ Nat.card M := fun L hL => hmax L (Or.inr hL)
  have hMtrans : ∀ L, TransGen LtF M L → TransGen LtF K₀ L := by
    intro L hL
    rcases hM with rfl | hM
    · exact hL
    · exact hM.trans hL
  refine ⟨M, hM, ⟨?_, fun L hL => ?_⟩, hup⟩
  · rcases hM with rfl | hM
    · exact h₀
    · exact inLF_right_of_transGen_ltF hM
  · obtain ⟨h1, h2⟩ := card_le_of_transGen_ltF hL
    exact h2 (le_antisymm (hup L (hMtrans L hL)) h1).symm

end Finite

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
