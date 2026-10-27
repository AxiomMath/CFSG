module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndGame
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Census

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

section Transport

variable {W U : Type*} [Group W] [Group U] (ι : W →* U)

theorem map_mem_fourSet {a b x : W} (hx : x ∈ fourSet a b) : ι x ∈ fourSet (ι a) (ι b) := by
  rcases mem_four hx with h | h | h | h <;> rw [h]
  · rw [map_one]; exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · rw [map_mul]; exact Or.inr (Or.inr (Or.inr rfl))

theorem exists_of_mem_fourSet_map {a b : W} {y : U} (hy : y ∈ fourSet (ι a) (ι b)) :
    ∃ x ∈ fourSet a b, ι x = y := by
  rcases mem_four hy with h | h | h | h <;> rw [h]
  · exact ⟨1, Or.inl rfl, map_one ι⟩
  · exact ⟨a, Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨b, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  · exact ⟨a * b, Or.inr (Or.inr (Or.inr rfl)), map_mul ι a b⟩

theorem map_conj_eq (g x : W) : ι (g * x * g⁻¹) = ι g * ι x * (ι g)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

theorem SwapFacts.of_map (hι : Function.Injective ι) {e₁ e₂ c₁ c₂ a₀ b₀ : W}
    (h : SwapFacts (ι e₁) (ι e₂) (ι c₁) (ι c₂) (ι a₀) (ι b₀)) : SwapFacts e₁ e₂ c₁ c₂ a₀ b₀ := by
  obtain ⟨he₁, he₂, he, he₁1, he₂1, hc₁, hc₁', hc₂, hc₂', hf₁₁, hf₁₂, hf₂₁, hf₂₂, hf₁n, hg₁m,
    hg₂m, hg₁n, hg₁n'⟩ := h
  have hf : ∀ i : W, ι (a₀ * i * a₀⁻¹) = ι a₀ * ι i * (ι a₀)⁻¹ := map_conj_eq ι a₀
  have hg : ∀ i : W, ι (b₀ * i * b₀⁻¹) = ι b₀ * ι i * (ι b₀)⁻¹ := map_conj_eq ι b₀
  have hmem : ∀ {g' : W}, (∃ x ∈ fourSet (ι e₁) (ι e₂),
      ∃ y ∈ fourSet (ι a₀ * ι e₁ * (ι a₀)⁻¹) (ι a₀ * ι e₂ * (ι a₀)⁻¹), ι g' = x * y) →
      ∃ x ∈ fourSet e₁ e₂, ∃ y ∈ fourSet (a₀ * e₁ * a₀⁻¹) (a₀ * e₂ * a₀⁻¹), g' = x * y := by
    rintro g' ⟨x, hx, y, hy, hxy⟩
    obtain ⟨x', hx', rfl⟩ := exists_of_mem_fourSet_map ι hx
    rw [← hf, ← hf] at hy
    obtain ⟨y', hy', rfl⟩ := exists_of_mem_fourSet_map ι hy
    exact ⟨x', hx', y', hy', hι (by rw [map_mul]; exact hxy)⟩
  have hnot : ∀ {g' a b : W}, ι g' ∉ fourSet (ι a) (ι b) → g' ∉ fourSet a b :=
    fun hn hm => hn (map_mem_fourSet ι hm)
  refine ⟨hι (by rw [map_mul, map_one]; exact he₁), hι (by rw [map_mul, map_one]; exact he₂),
    hι (by rw [map_mul, map_mul]; exact he), fun h1 => he₁1 (by rw [h1, map_one]),
    fun h1 => he₂1 (by rw [h1, map_one]), hι (by rw [map_mul, map_mul]; exact hc₁),
    hι (by rw [map_mul, map_mul, map_mul]; exact hc₁'), hι (by rw [map_mul, map_mul]; exact hc₂),
    hι (by rw [map_mul, map_mul, map_mul]; exact hc₂'),
    hι (by simp only [map_mul, map_inv]; exact hf₁₁),
    hι (by simp only [map_mul, map_inv]; exact hf₁₂),
    hι (by simp only [map_mul, map_inv]; exact hf₂₁),
    hι (by simp only [map_mul, map_inv]; exact hf₂₂),
    hnot (by rw [hf]; exact hf₁n), hmem (by rw [hg]; exact hg₁m), hmem (by rw [hg]; exact hg₂m),
    hnot (by rw [hg]; exact hg₁n), hnot (by rw [hg, hf, hf]; exact hg₁n')⟩

end Transport

section Rows

theorem ne_of_rows {x y : Native.Rows} {g h : GL24} (hx : MRep x g) (hy : MRep y h)
    (hvx : CFSG.Sporadic.Co1.InvNative.validRows x = true)
    (hvy : CFSG.Sporadic.Co1.InvNative.validRows y = true) (hne : y ≠ x) : h ≠ g := by
  intro e
  apply hne
  refine rows_eq_of_mrep hvy hvx hy ?_
  rw [e]
  exact hx

theorem not_mem_fourSet_of_notInR {x a b : Native.Rows} {gx ga gb : GL24} (hx : MRep x gx)
    (ha : MRep a ga) (hb : MRep b gb) (h : notInR x (fourR a b) = true) : gx ∉ fourSet ga gb := by
  simp only [notInR, fourR, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨hvx, ⟨hv1, h1⟩, ⟨hva, h2⟩, ⟨hvb, h3⟩, ⟨hvab, h4⟩⟩ := h
  intro hm
  rcases mem_four hm with e | e | e | e
  · exact ne_of_rows hx MRep.one hvx hv1 h1 e.symm
  · exact ne_of_rows hx ha hvx hva h2 e.symm
  · exact ne_of_rows hx hb hvx hvb h3 e.symm
  · exact ne_of_rows hx (ha.mul hb) hvx hvab h4 e.symm

theorem exists_rep_getD {a b : Native.Rows} {ga gb : GL24} (ha : MRep a ga) (hb : MRep b gb)
    (i : ℕ) : ∃ g ∈ fourSet ga gb, MRep ((fourR a b).getD i Native.one) g := by
  match i with
  | 0 => exact ⟨1, Or.inl rfl, MRep.one⟩
  | 1 => exact ⟨ga, Or.inr (Or.inl rfl), ha⟩
  | 2 => exact ⟨gb, Or.inr (Or.inr (Or.inl rfl)), hb⟩
  | 3 => exact ⟨ga * gb, Or.inr (Or.inr (Or.inr rfl)), ha.mul hb⟩
  | n + 4 =>
    refine ⟨1, Or.inl rfl, ?_⟩
    have : (fourR a b).getD (n + 4) Native.one = Native.one := by simp [fourR]
    rw [this]
    exact MRep.one

theorem comm_of_commR {x y : Native.Rows} {g h : GL24} (hx : MRep x g) (hy : MRep y h)
    (hc : commR x y = true) : g * h = h * g := by
  simp only [commR, beq_iff_eq] at hc
  exact (hx.mul hy).eq (by rw [hc]; exact hy.mul hx)

theorem swapFacts_of_rows {e₂r c₁r c₂r ar br : Native.Rows}
    {e₂ c₁ c₂ a b : GL24} (he : MRep e₂r e₂) (hc₁ : MRep c₁r c₁) (hc₂ : MRep c₂r c₂)
    (ha : MRep ar a) (hb : MRep br b) {db : List ℕ}
    (h : co1EndElemOK e₂r c₁r c₂r ar br db = true) : SwapFacts A₁ e₂ c₁ c₂ a b := by
  simp only [co1EndElemOK, co1EndSwapOK, co1EndConjOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hAA⟩, hEE⟩, hAE⟩, hnA⟩, hnE⟩, hc₁A⟩, hc₁E⟩, hc₂E⟩, hc₂A⟩, hia⟩, hib⟩,
    ⟨⟨⟨⟨⟨⟨⟨⟨hf₁A, hf₁E⟩, hf₂A⟩, hf₂E⟩, hf₁n⟩, hg₁⟩, hg₂⟩, hg₁n⟩, hg₁n'⟩⟩ := h
  have hA := rep_A₁
  have hai := ha.inv hia
  have hbi := hb.inv hib
  have hf₁ : MRep (conjR ar Native.aR) (a * A₁ * a⁻¹) := (ha.mul hA).mul hai
  have hf₂ : MRep (conjR ar e₂r) (a * e₂ * a⁻¹) := (ha.mul he).mul hai
  have hg₁r : MRep (conjR br Native.aR) (b * A₁ * b⁻¹) := (hb.mul hA).mul hbi
  have hg₂r : MRep (conjR br e₂r) (b * e₂ * b⁻¹) := (hb.mul he).mul hbi
  have hne : ∀ {x y : Native.Rows} {g h : GL24}, MRep x g → MRep y h →
      notInR x [y] = true → h ≠ g := by
    intro x y g h hx hy hn
    simp only [notInR, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at hn
    exact ne_of_rows hx hy hn.1 hn.2.1 hn.2.2
  have hnE' : notInR e₂r [Native.one] = true ∧ notInR e₂r [Native.aR] = true := by
    simp only [notInR, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hnE ⊢
    exact ⟨⟨hnE.1, hnE.2.1⟩, ⟨hnE.1, hnE.2.2⟩⟩
  obtain ⟨x₁, hx₁, hx₁r⟩ := exists_rep_getD hA he (db.getD 0 0)
  obtain ⟨y₁, hy₁, hy₁r⟩ := exists_rep_getD hf₁ hf₂ (db.getD 1 0)
  obtain ⟨x₂, hx₂, hx₂r⟩ := exists_rep_getD hA he (db.getD 2 0)
  obtain ⟨y₂, hy₂, hy₂r⟩ := exists_rep_getD hf₁ hf₂ (db.getD 3 0)
  have hc₂' : c₂ * A₁ = A₁ * e₂ * c₂ :=
    (hc₂.mul hA).eq (by rw [hc₂A]; exact (hA.mul he).mul hc₂)
  refine ⟨(hA.mul hA).eq (by rw [hAA]; exact MRep.one),
    (he.mul he).eq (by rw [hEE]; exact MRep.one), comm_of_commR hA he hAE,
    (hne hA MRep.one hnA).symm, (hne he MRep.one hnE'.1).symm,
    comm_of_commR hc₁ hA hc₁A, (hc₁.mul he).eq (by rw [hc₁E]; exact (hA.mul he).mul hc₁),
    comm_of_commR hc₂ he hc₂E, ?_, ?_, ?_, ?_, ?_, not_mem_fourSet_of_notInR hf₁ hA he hf₁n,
    ⟨x₁, hx₁, y₁, hy₁, hg₁r.eq (by rw [hg₁]; exact hx₁r.mul hy₁r)⟩,
    ⟨x₂, hx₂, y₂, hy₂, hg₂r.eq (by rw [hg₂]; exact hx₂r.mul hy₂r)⟩,
    not_mem_fourSet_of_notInR hg₁r hA he hg₁n, not_mem_fourSet_of_notInR hg₁r hf₁ hf₂ hg₁n'⟩
  · rw [hc₂', comm_of_commR hA he hAE]
  · exact comm_of_commR hf₁ hA hf₁A
  · exact comm_of_commR hf₁ he hf₁E
  · exact comm_of_commR hf₂ hA hf₂A
  · exact comm_of_commR hf₂ he hf₂E

end Rows

@[expose] noncomputable def co1EndBaseG :
    List GL24 :=
  [A₁, A₂, ((co1XC : GA) : GL24), ((co1YC : GA) : GL24)]

theorem rep_co1EndBase :
    List.Forall₂ MRep co1EndBase co1EndBaseG :=
  .cons rep_A₁ (.cons rep_A₂ (.cons rep_co1XC (.cons rep_co1YC .nil)))

theorem co1EndBaseG_mem :
    ∀ g ∈ co1EndBaseG, g ∈ GA := by
  intro g hg
  simp only [co1EndBaseG, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h <;> rw [h]
  · exact A₁_mem
  · exact A₂_mem
  · exact (co1XC : GA).2
  · exact (co1YC : GA).2

theorem co1_swapFacts_of_check
    {d : List (List ℕ)} {idx db : List ℕ} (h : co1EndCheck d idx db = true) :
    ∃ c₁ c₂ a₀ b₀ : Blueprint.NativeSporadic.Co1, SwapFacts co1E1 co1E2 c₁ c₂ a₀ b₀ := by
  simp only [co1EndCheck, co1EndCoreOK, Bool.and_eq_true] at h
  obtain ⟨hdag, hcore⟩ := h
  have hrep := dag_rep rep_co1EndBase (d.map Native.decWord) hdag
  have hmem : ∀ g ∈ dagG co1EndBaseG (d.map Native.decWord), g ∈ GA :=
    dagG_mem co1EndBaseG_mem _
  set EG := dagG co1EndBaseG (d.map Native.decWord) with hEG
  have he₂r : entryR (Native.dag co1EndBase (d.map Native.decWord)).1 (idx.getD 0 0) =
      co1E2R := by
    have h1 := hcore
    simp only [co1EndElemOK, co1EndSwapOK, Bool.and_eq_true, beq_iff_eq] at h1
    exact h1.1.1.1.1.1.1.1.1.1.1.1.1
  have he₂ : MRep (entryR (Native.dag co1EndBase (d.map Native.decWord)).1 (idx.getD 0 0))
      co1E2G := by
    rw [he₂r, co1E2G_eq]
    exact rep_co1E2C
  have hS := swapFacts_of_rows he₂ (mrep_entry hrep (idx.getD 1 0))
    (mrep_entry hrep (idx.getD 2 0)) (mrep_entry hrep (idx.getD 3 0))
    (mrep_entry hrep (idx.getD 4 0)) hcore
  refine ⟨co1MatEquiv.symm ⟨_, entryG_mem hmem (idx.getD 1 0)⟩,
    co1MatEquiv.symm ⟨_, entryG_mem hmem (idx.getD 2 0)⟩,
    co1MatEquiv.symm ⟨_, entryG_mem hmem (idx.getD 3 0)⟩,
    co1MatEquiv.symm ⟨_, entryG_mem hmem (idx.getD 4 0)⟩, SwapFacts.of_map co1ι co1ι_injective ?_⟩
  rw [co1ι_co1E1, co1ι_co1E2, co1ι_symm, co1ι_symm, co1ι_symm, co1ι_symm]
  exact hS

end CFSG.ComponentClassification.RankTwoSporadic.Co1
