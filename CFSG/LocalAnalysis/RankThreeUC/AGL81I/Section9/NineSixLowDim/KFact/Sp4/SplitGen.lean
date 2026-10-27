module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.Defs
import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
open TauCeti.GLSymplecticFin (RootSubgroupIndex eq_top_of_root_subgroups)

private theorem diagonal_mul_E {n : ℕ} {F : Type} [Field F] (d : Fin n ⊕ Fin n → F)
    (r : RootSubgroupIndex n) (h1 : d (pos1 r).1 = d (pos1 r).2)
    (h2 : d (pos2 r).1 = d (pos2 r).2) : diagonal d * E F r = E F r * diagonal d := by
  ext a b
  rw [diagonal_mul, mul_diagonal]
  by_cases h : E F r a b = 0
  · simp [h]
  · rcases eq_pos_of_E_ne_zero r a b h with h' | h' <;> obtain ⟨ha, hb⟩ := Prod.ext_iff.mp h' <;>
      simp only at ha hb <;> rw [ha, hb]
    · rw [h1, mul_comm]
    · rw [h2, mul_comm]

private theorem elt_pow_char {n q : ℕ} [Fact q.Prime] (r : RootSubgroupIndex n) (c : ZMod q) :
    elt r c ^ q = 1 := by
  have key : ∀ m : ℕ, elt r c ^ m = elt r ((m : ZMod q) * c) := by
    intro m
    induction m with
    | zero => simp [elt_zero]
    | succ m ih =>
      rw [pow_succ, ih, ← elt_add]
      congr 1
      push_cast
      ring
  rw [key, ZMod.natCast_self, zero_mul, elt_zero]

private theorem elt_mem_fixSetSp {q : ℕ} [Fact q.Prime] {p : ℕ} (hp1 : p ≠ 1) (hpq : p ≠ q)
    {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} (r : RootSubgroupIndex 2) (c : ZMod q)
    {g : GL (Fin 2 ⊕ Fin 2) (ZMod q)} (hgE : g ∈ E) {d : Fin 2 ⊕ Fin 2 → ZMod q}
    (hg : (g : Matrix _ _ (ZMod q)) = diagonal d) (a : Fin 2 ⊕ Fin 2) (ha : d a ≠ 1)
    (h1 : d (pos1 r).1 = d (pos1 r).2) (h2 : d (pos2 r).1 = d (pos2 r).2) :
    ((elt r c : CFSG.Open.StatedSp 2 (ZMod q)) : GL (Fin 2 ⊕ Fin 2) (ZMod q)) ∈ fixSetSp p E := by
  refine ⟨(elt r c).2, ?_, g, hgE, ?_, ?_⟩
  · have hdvd : orderOf ((elt r c : CFSG.Open.StatedSp 2 (ZMod q)) :
        GL (Fin 2 ⊕ Fin 2) (ZMod q)) ∣ q := orderOf_dvd_of_pow_eq_one (by
      rw [← Subgroup.coe_pow, elt_pow_char, Subgroup.coe_one])
    intro hp
    rcases (Nat.dvd_prime Fact.out).1 hdvd with h | h <;> rw [h] at hp
    · exact hp1 (Nat.dvd_one.1 hp)
    · rcases (Nat.dvd_prime Fact.out).1 hp with h' | h'
      exacts [hp1 h', hpq h']
  · rintro rfl
    apply ha
    simpa using (congrFun (congrFun hg a) a).symm
  · apply Units.ext
    have hm : (((elt r c : CFSG.Open.StatedSp 2 (ZMod q)) : GL (Fin 2 ⊕ Fin 2) (ZMod q)) :
        Matrix _ _ (ZMod q)) = 1 + c • SpExtras.E (ZMod q) r := mat_elt r c
    rw [Units.val_mul, Units.val_mul, hm, hg, mul_add, add_mul, mul_one, one_mul, mul_smul_comm,
      smul_mul_assoc, diagonal_mul_E d r h1 h2]

private theorem statedSp_le_of_elt_mem {q : ℕ} [Fact q.Prime]
    (H : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q)))
    (h : ∀ (r : RootSubgroupIndex 2) (c : ZMod q),
      ((elt r c : CFSG.Open.StatedSp 2 (ZMod q)) : GL (Fin 2 ⊕ Fin 2) (ZMod q)) ∈ H) :
    CFSG.Open.StatedSp 2 (ZMod q) ≤ H := by
  intro x hx
  have hT : ((H.comap (CFSG.Open.StatedSp 2 (ZMod q)).subtype).comap
      (equivStatedSp 2 (ZMod q)).toMonoidHom) = ⊤ :=
    eq_top_of_root_subgroups _ fun r c => h r c.toAdd
  obtain ⟨y, hy⟩ := (equivStatedSp 2 (ZMod q)).surjective ⟨x, hx⟩
  have hy' := hT ▸ Subgroup.mem_top y
  rw [Subgroup.mem_comap, Subgroup.mem_comap] at hy'
  simpa [hy] using hy'

private theorem elt_mem_fixSetSp_of_four {q : ℕ} [Fact q.Prime] {p : ℕ} (hp1 : p ≠ 1)
    (hpq : p ≠ q) {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} {ζ : ZMod q} (hζ : ζ ≠ 1)
    {g₀ g₁ g₂ g₃ : GL (Fin 2 ⊕ Fin 2) (ZMod q)} (hE₀ : g₀ ∈ E) (hE₁ : g₁ ∈ E) (hE₂ : g₂ ∈ E)
    (hE₃ : g₃ ∈ E) (hg₀ : (g₀ : Matrix _ _ (ZMod q)) = diagonal (Sum.elim ![ζ, 1] ![ζ⁻¹, 1]))
    (hg₁ : (g₁ : Matrix _ _ (ZMod q)) = diagonal (Sum.elim ![1, ζ] ![1, ζ⁻¹]))
    (hg₂ : (g₂ : Matrix _ _ (ZMod q)) = diagonal (Sum.elim ![ζ, ζ] ![ζ⁻¹, ζ⁻¹]))
    (hg₃ : (g₃ : Matrix _ _ (ZMod q)) = diagonal (Sum.elim ![ζ, ζ⁻¹] ![ζ⁻¹, ζ]))
    (r : RootSubgroupIndex 2) (c : ZMod q) :
    ((elt r c : CFSG.Open.StatedSp 2 (ZMod q)) : GL (Fin 2 ⊕ Fin 2) (ZMod q)) ∈ fixSetSp p E := by
  cases r with
  | positiveLong i =>
    fin_cases i
    · exact elt_mem_fixSetSp hp1 hpq _ c hE₁ hg₁ (.inl 1) (by simpa using hζ) (by simp [pos1])
        (by simp [pos2])
    · exact elt_mem_fixSetSp hp1 hpq _ c hE₀ hg₀ (.inl 0) (by simpa using hζ) (by simp [pos1])
        (by simp [pos2])
  | negativeLong i =>
    fin_cases i
    · exact elt_mem_fixSetSp hp1 hpq _ c hE₁ hg₁ (.inl 1) (by simpa using hζ) (by simp [pos1])
        (by simp [pos2])
    · exact elt_mem_fixSetSp hp1 hpq _ c hE₀ hg₀ (.inl 0) (by simpa using hζ) (by simp [pos1])
        (by simp [pos2])
  | difference i j hij =>
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact elt_mem_fixSetSp hp1 hpq _ c hE₂ hg₂ (.inl 0) (by simpa using hζ) (by simp [pos1])
        (by simp [pos2])
    · exact elt_mem_fixSetSp hp1 hpq _ c hE₂ hg₂ (.inl 0) (by simpa using hζ) (by simp [pos1])
        (by simp [pos2])
    · exact absurd rfl hij
  | positiveSum i j hij =>
    fin_cases i <;> fin_cases j <;> try exact absurd hij (by decide)
    exact elt_mem_fixSetSp hp1 hpq _ c hE₃ hg₃ (.inl 0) (by simpa using hζ) (by simp [pos1])
      (by simp [pos2])
  | negativeSum i j hij =>
    fin_cases i <;> fin_cases j <;> try exact absurd hij (by decide)
    exact elt_mem_fixSetSp hp1 hpq _ c hE₃ hg₃ (.inl 0) (by simpa using hζ) (by simp [pos1])
      (by simp [pos2])

theorem closure_fixSetSp_of_spDiag_of_ne_one {q : ℕ} [Fact q.Prime] {p : ℕ} (hp1 : p ≠ 1)
    (hpq : p ≠ q) {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} {ζ : ZMod q} (hζ : ζ ≠ 1)
    (h₀ : ∃ g ∈ E, (g : Matrix _ _ (ZMod q)) = spDiagMatrix ζ 1)
    (h₁ : ∃ g ∈ E, (g : Matrix _ _ (ZMod q)) = spDiagMatrix 1 ζ) :
    Subgroup.closure (fixSetSp p E) = CFSG.Open.StatedSp 2 (ZMod q) := by
  obtain ⟨g₀, hE₀, hg₀⟩ := h₀
  obtain ⟨g₁, hE₁, hg₁⟩ := h₁
  simp only [spDiagMatrix, inv_one] at hg₀ hg₁
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    have := congrFun (congrFun g₀.mul_inv (.inl 0)) (.inl 0)
    rw [hg₀, diagonal_mul] at this
    simp at this
  have hinv : ((g₁⁻¹ : GL (Fin 2 ⊕ Fin 2) (ZMod q)) : Matrix _ _ (ZMod q)) =
      diagonal (Sum.elim ![1, ζ⁻¹] ![1, ζ]) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hg₁, diagonal_mul_diagonal]
    refine Eq.trans ?_ diagonal_one
    congr 1
    funext a
    rcases a with i | i <;> fin_cases i <;> simp [hζ0]
  have hg₂ : ((g₀ * g₁ : GL (Fin 2 ⊕ Fin 2) (ZMod q)) : Matrix _ _ (ZMod q)) =
      diagonal (Sum.elim ![ζ, ζ] ![ζ⁻¹, ζ⁻¹]) := by
    rw [Units.val_mul, hg₀, hg₁, diagonal_mul_diagonal]
    congr 1
    funext a
    rcases a with i | i <;> fin_cases i <;> simp
  have hg₃ : ((g₀ * g₁⁻¹ : GL (Fin 2 ⊕ Fin 2) (ZMod q)) : Matrix _ _ (ZMod q)) =
      diagonal (Sum.elim ![ζ, ζ⁻¹] ![ζ⁻¹, ζ]) := by
    rw [Units.val_mul, hg₀, hinv, diagonal_mul_diagonal]
    congr 1
    funext a
    rcases a with i | i <;> fin_cases i <;> simp
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx.1) ?_
  exact statedSp_le_of_elt_mem _ fun r c => Subgroup.subset_closure
    (elt_mem_fixSetSp_of_four hp1 hpq hζ hE₀ hE₁ (E.mul_mem hE₀ hE₁)
      (E.mul_mem hE₀ (E.inv_mem hE₁)) hg₀ hg₁ hg₂ hg₃ r c)

theorem closure_fixSetSp_of_spDiag {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} {ζ : ZMod q} (hζ : ζ ≠ 1)
    (h₀ : ∃ g ∈ E, (g : Matrix _ _ (ZMod q)) = spDiagMatrix ζ 1)
    (h₁ : ∃ g ∈ E, (g : Matrix _ _ (ZMod q)) = spDiagMatrix 1 ζ) :
    Subgroup.closure (fixSetSp p E) = CFSG.Open.StatedSp 2 (ZMod q) :=
  closure_fixSetSp_of_spDiag_of_ne_one hp.ne_one hpq hζ h₀ h₁

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
