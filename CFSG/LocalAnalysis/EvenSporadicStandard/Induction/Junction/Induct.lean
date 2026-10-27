module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Base
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Diag.Link
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ChainLemmas

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

section Step

variable {T W W' M K : Subgroup H} {s : H}

omit [Finite H] in
theorem DiagData.sup_zpowers_eq (h : DiagData T W W' M K s) :
    (W' ⊔ T) ⊔ zpowers s = W ⊔ T := by
  refine le_antisymm (sup_le (sup_le (h.W'_le.trans le_sup_left) le_sup_right)
    ((zpowers_le.2 h.s_mem).trans le_sup_left)) (sup_le ?_ ?_)
  · intro g hg
    rcases h.cover g hg with h1 | h1
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left h1)
    · have hg' : g = s * (s⁻¹ * g) := by group
      rw [hg']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers s))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left h1))
  · exact (le_sup_right : T ≤ W' ⊔ T).trans le_sup_left

theorem DiagData.not_K_le (h : DiagData T W W' M K s) : ¬ K ≤ M := by
  intro hKM
  have hne : M ≠ M.map (MulAut.conj s).toMonoidHom := by
    intro heq
    exact h.s_not_mem (h.normalizer_le s h.s_mem
      (Solomon78.mem_normalizer_iff_map_conj_eq.2 heq.symm))
  have hKs : K ≤ M.map (MulAut.conj s).toMonoidHom := by
    intro x hx
    have hxs : s * x * s⁻¹ = x := by
      rw [h.mem_centralizer_W hx s h.s_mem]
      group
    exact ⟨x, hKM hx, by simp [MulAut.conj_apply, hxs]⟩
  exact not_forall_commute_of_isQuasisimple h.isComp_K.isQuasisimple fun a ha b hb =>
    h.isComp_M.commute_of_ne (h.isComp_conj h.s_mem) hne a (hKM ha) b (hKs hb)

end Step

theorem junction_conn (hcor : ∀ (G : Type) [Group G] [Finite G],
      CFSG.SignalizerFunctorTheorem.IsSectionOf G H → Nat.card G < Nat.card H → Cor23SAt G)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) :
    ∀ (n : ℕ) {T W K M : Subgroup H}, Nat.card W = n → T ≠ ⊥ → IsPGroup 2 T → IsPGroup 2 W →
      W ≤ normalizer (T : Set H) → IsCompIn M (centralizer (T : Set H)) →
      IsCompIn K (centralizer ((W ⊔ T : Subgroup H) : Set H)) → K ≤ conjClosure M W →
      NotExc K → JConn K M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T W K M hn hT hT2 hW2 hWT hM hK hKW hexc
    have hTM : T ≤ normalizer (M : Set H) := fun t ht =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx =>
        (mem_centralizer_iff.1 (hM.1 hx) t ht).symm)
    by_cases hWM : W ≤ normalizer (M : Set H)
    · have hKM : K ≤ M := by
        have := hKW
        rwa [conjClosure_of_le_normalizer hWM] at this
      have hV2 : IsPGroup 2 ↥(W ⊔ T) := IsPGroup.to_sup_of_normal_right' hW2 hT2 hWT
      exact junction_base hcor hkp hT hT2 hM hV2 le_sup_right
        (sup_le hWT Subgroup.le_normalizer) (sup_le hWM hTM) hK hKM hexc
    · have hne : W ⊓ normalizer (M : Set H) ≠ W := fun h => hWM (inf_eq_left.1 h)
      obtain ⟨W', s, hW₁, hW'W, hsW, hsW', hsq, hconj, hcover⟩ :=
        exists_index_two hW2 inf_le_left hne
      have hd : DiagData T W W' M K s :=
        ⟨hWT, hW'W, hsW, hsW', hsq, hconj, hcover, hM, fun g hg hgM => hW₁ ⟨hg, hgM⟩, hK, hKW⟩
      obtain ⟨X, hX, hXne, hKX, hlayer, ⟨e⟩, hXle⟩ := diag_step hd
      have hlt : W' < W := lt_of_le_of_ne hW'W fun h => hsW' (h ▸ hsW)
      have hW'2 : IsPGroup 2 W' := hW2.to_le hW'W
      have hW'T : W' ≤ normalizer (T : Set H) := hW'W.trans hWT
      obtain ⟨m, L, T', s', hl, hL0, hLm, hT', -⟩ := ih (Nat.card W')
        (hn ▸ Subgroup.card_lt_of_lt hlt) (T := T) (W := W') (K := X) (M := M) rfl hT hT2 hW'2
        hW'T hM hX hXle (hexc.of_cqEquiv e)
      have hT0 : IsPGroup 2 ↥(W ⊔ T) := IsPGroup.to_sup_of_normal_right' hW2 hT2 hWT
      have hT1 : IsPGroup 2 ↥(W' ⊔ T) := IsPGroup.to_sup_of_normal_right' hW'2 hT2 hW'T
      have hs2 : IsPGroup 2 ↥(zpowers s) := hW2.to_le (zpowers_le.2 hsW)
      have hsN : s ∈ normalizer ((W' ⊔ T : Subgroup H) : Set H) := hd.s_mem_normalizer
      have hsT : s ^ 2 ∈ W' ⊔ T := Subgroup.mem_sup_left hsq
      have hKs : IsCompIn K (centralizer (((W' ⊔ T) ⊔ zpowers s : Subgroup H) : Set H)) := by
        rw [hd.sup_zpowers_eq]
        exact hK
      have h1 := Sol78Links.single hT0 hT1 hK hX hs2 hsN hsT hKs hKX hlayer (Or.inl ⟨hXne, ⟨e⟩⟩)
      have hjoin : L 0 = (fun i => if i = 0 then K else X) 1 := by simp [hL0]
      have hT1ne : W' ⊔ T ≠ ⊥ := fun h => hT (le_bot_iff.1 (le_sup_right.trans h.le))
      refine ⟨1 + m, concat 1 (fun i => if i = 0 then K else X) L,
        concat 1 (fun i => if i = 0 then W ⊔ T else W' ⊔ T) T', concat 1 (fun _ => s) s',
        h1.concat hl hjoin, ?_, ?_, ?_, fun hKM => absurd hKM hd.not_K_le⟩
      · rw [concat_of_le (Nat.zero_le 1)]
        simp
      · rw [concat_add hjoin]
        exact hLm
      · intro i hi1 hi
        by_cases hi' : i ≤ 1
        · rw [concat_of_le hi']
          obtain rfl : i = 1 := le_antisymm hi' hi1
          simpa using hT1ne
        · obtain ⟨k, rfl⟩ : ∃ k, i = 1 + (k + 1) := ⟨i - 2, by omega⟩
          rw [concat_add_succ]
          exact hT' (k + 1) (by omega) (by omega)

end CFSG.EvenSporadicStandard.Induction.Junction
