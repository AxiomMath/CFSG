module

public import CFSG.GH74.GLS.C3.Layer1.Back91
public import CFSG.GH74.GLS.C3.Layer1.BkL92Stmt

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

@[expose] def B_ivk_6_big : Prop :=
  ∀ (K : Type) [Group K] [Finite K], HasL2Model K (fun r => Odd r ∧ 9 < r) →
    ∀ B : Subgroup (MulAut K), CFSG.IsElementaryAbelian 2 ↥B → Nat.card ↥B = 4 → gammaAut K B = ⊤

@[expose] def B_ivk_6_small : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W : Subgroup (MulAut K)),
    (HasL2Model K (fun r => r = 5 ∨ r = 7 ∨ r = 9) ∨ Nonempty (K ≃* alternatingGroup (Fin 7))) →
    IsPGroup 2 ↥W → 2 ≤ CFSG.pRank 2 ↥W → gammaAut K W ≠ ⊤ →
      (CFSG.IsElementaryAbelian 2 ↥W ∧ Nat.card ↥W = 4) ∧
      W ≤ (MulAut.conj : K →* MulAut K).range

theorem gammaAut_mono {K : Type} [Group K] {W W' : Subgroup (MulAut K)} (h : W ≤ W') :
    gammaAut K W ≤ gammaAut K W' :=
  iSup_mono fun _ => iSup_mono' fun hw => ⟨h hw, le_rfl⟩

theorem b_ivk_6_of_parts (hs : B_ivk_6_small) (hb : B_ivk_6_big) : B_ivk_6 := by
  intro K _ _ W hshape hW2 hWr hΓ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : HasL2Model K Odd → ∃ q ∈ ({5, 7, 9} : Finset ℕ), HasL2Model K (fun r => r = q) := by
    intro hL
    obtain ⟨p, f, hp, hf, hodd, hLie⟩ := hL
    by_cases hbig : 9 < p ^ f
    · exfalso
      have hWr' : 2 ≤ CFSG.Open.pRank 2 W := (TwoThin.pRank_two_subgroup_eq_open W) ▸ hWr
      obtain ⟨E, hEW, hEab, hE4⟩ :=
        CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) hWr'
      have hel : CFSG.IsElementaryAbelian 2 ↥E :=
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).2 hEab
      have hgam : gammaAut K E = ⊤ :=
        hb K ⟨p, f, hp, hf, ⟨hodd, hbig⟩, hLie⟩ E hel (by rw [hE4]; norm_num)
      apply hΓ
      exact top_le_iff.1 (hgam ▸ gammaAut_mono hEW)
    ·
      have hf1 : 2 ≤ p ^ f := by
        calc 2 ≤ p := hp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
      have hq3 : p ^ f ≠ 3 := by
        intro h3
        rcases hLie with ⟨-, hmod⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
        · obtain ⟨hadm, -⟩ := hmod
          exact hadm.2.2.2.2 (by rw [h3])
        all_goals exact absurd h0 (by norm_num)
      have hmem : p ^ f ∈ ({5, 7, 9} : Finset ℕ) := by
        have hlt : p ^ f ≤ 9 := by omega
        have h2 : (p ^ f) % 2 = 1 := Nat.odd_iff.1 hodd
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact ⟨p ^ f, hmem, p, f, hp, hf, rfl, hLie⟩
  have hshape' : HasL2Model K (fun r => r = 5 ∨ r = 7 ∨ r = 9) ∨
      Nonempty (K ≃* alternatingGroup (Fin 7)) := by
    rcases hshape with hL | hA
    · obtain ⟨q, hqm, hLq⟩ := hq hL
      refine Or.inl (hasL2Model_mono (fun r hr => ?_) hLq)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqm
      subst hr
      exact hqm
    · exact Or.inr hA
  exact ⟨hq, hs K W hshape' hW2 hWr hΓ⟩

end CFSG.GH74.GLS.C3.Layer1.Bk
