module

public import CFSG.CGT.Timmesfeld75.Sec63Main
public import CFSG.CGT.Timmesfeld75.JLemma
public import CFSG.CGT.Timmesfeld75.JLemmaTrans

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem sec63_core (h215 : Lemma215Stmt) (h26 : Lemma26Input) (hA : Sec63A6) {G : Type} [Group G]
    {T T₁ : Subgroup G} {n m : ℕ} {x : G} {T₃ : Subgroup G} (hc : Sec6Ctx T T₁ n m)
    (cfg : Sec63Cfg T T₁ n m x T₃)
    (hF : ∀ j : Fin 3, (⨅ i, normIn (sec63Fam T T₁ T₃ j) (sec63Fam T T₁ T₃ i)) ≠ ⊥) : False := by
  have hfin := hc.finite
  have : IsSimpleGroup G := hc.hy.simple
  have hlt := cfg.small
  have hbig := cfg.big
  obtain ⟨g, rfl⟩ := cfg.conj
  set T₃ := conjSubgroup g T with hT₃
  have hT := hc.hy.pair.wc
  obtain ⟨y₁, hy₁, hy₁eq⟩ := hc.sec3.conj
  obtain ⟨y₃, hy₃, hy₃eq⟩ := cfg.sec3.conj
  have hRfam : (⨆ i, sec63Fam T T₁ T₃ i) = T ⊔ T₁ ⊔ T₃ := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · exact sup_le (sup_le (le_iSup (sec63Fam T T₁ T₃) 0) (le_iSup (sec63Fam T T₁ T₃) 1))
        (le_iSup (sec63Fam T T₁ T₃) 2)
  set R := T ⊔ T₁ ⊔ T₃ with hR
  have hTR : T ≤ R := le_sup_left.trans le_sup_left
  have hX₁ : T ⊔ T₁ ≤ R := le_sup_left
  have hX₃ : T ⊔ T₃ ≤ R := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hy₁R : y₁ ∈ R := hX₁ hy₁
  have hy₃R : y₃ ∈ R := hX₃ hy₃
  have hinj : Function.Injective (sec63Fam T T₁ T₃) := by
    have h01 : T ≠ T₁ := fun h => hc.hy.pair.ne h.symm
    have h02 : T ≠ T₃ := fun h => cfg.ne_left h.symm
    have h12 : T₁ ≠ T₃ := fun h => cfg.ne_mid h.symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [sec63Fam, h01.symm]
  have hconj : ∀ i, ∃ g : G, sec63Fam T T₁ T₃ i = conjSubgroup g T := by
    intro i
    fin_cases i
    · exact ⟨1, (conjSubgroup_one T).symm⟩
    · exact hc.hy.pair.conj
    · exact ⟨g, rfl⟩
  have hRconj : ∀ i, ∃ g' ∈ R, sec63Fam T T₁ T₃ i = conjSubgroup g' T := by
    intro i
    fin_cases i
    · exact ⟨1, R.one_mem, (conjSubgroup_one T).symm⟩
    · exact ⟨y₁, hy₁R, hy₁eq⟩
    · exact ⟨y₃, hy₃R, hy₃eq⟩
  have hq : ∃ j, 2 * Nat.card ↥(normIn T (sec63Fam T T₁ T₃ j)) < Nat.card T := by
    refine ⟨2, ?_⟩
    have h1 : Nat.card ↥(normIn T T₃) < Nat.card ↥(normIn T T₁) := by
      rw [cfg.card_normIn]
      exact hlt
    have h2 := hc.two_mul_card_normIn_le
    show 2 * Nat.card ↥(normIn T T₃) < Nat.card T
    omega
  obtain ⟨-, -, hhyp, hconcl, -, -⟩ := jLemma h215 h26 hc.hy.nonab hc.hy.ind hT hc.hS hc.hI
    (by omega) (r := 3) (Ts := sec63Fam T T₁ T₃) (by norm_num) hinj hconj ⟨0, rfl⟩
    hF hRfam hRconj hq
  by_cases hA6 : Nonempty (jQuot ↥R ⧸ Subgroup.center (jQuot ↥R) ≃* alternatingGroup (Fin 6))
  · exact hA G T T₁ n m x T₃ cfg hF hA6
  · have hone : conjSubgroup (1 : G) T ≠ conjSubgroup y₁ T := by
      rw [conjSubgroup_one, ← hy₁eq]
      exact fun h => hc.hy.pair.ne h.symm
    have hone3 : conjSubgroup (1 : G) T ≠ conjSubgroup y₃ T := by
      rw [conjSubgroup_one, ← hy₃eq]
      exact fun h => cfg.ne_left h.symm
    obtain ⟨r, -, h1, h2⟩ := exists_mem_conj_of_jMap_sub hT hTR hconcl hA6 (a₁ := 1) (a₂ := y₁)
      (b₁ := 1) (b₂ := y₃) R.one_mem hy₁R R.one_mem hy₃R hone hone3
    rw [conjSubgroup_one] at h1
    rw [← hy₁eq, ← hy₃eq] at h2
    have h3 := normIn_conj r T₁ T
    rw [h1, h2] at h3
    have h4 := cfg.card_normIn_lt
    rw [h3, card_conjSubgroup, hc.card_normIn_swap] at h4
    exact lt_irrefl _ h4

end CFSG.CGT.Timmesfeld75
