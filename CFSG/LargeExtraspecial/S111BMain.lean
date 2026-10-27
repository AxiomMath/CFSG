module

public import CFSG.LargeExtraspecial.S111BA5End
public import CFSG.LargeExtraspecial.S111CShult

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}
  {h k : G} {m : S.M}

theorem Pair111.false_of_commute (P : Pair111 S g A h k ((m : G) * k))
    (hA5 : Ebar S k ((m : G) * k) ≠ ⊥ →
      4 * Nat.card (Ebar S k ((m : G) * k)) ≤ Nat.card (S.Lbar k) →
      ∃ φ : ↥(S.Lbar k ⊔ S.Lbar ((m : G) * k)) →* alternatingGroup (Fin 5),
        Function.Surjective φ ∧ φ.ker = CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar ((m : G) * k)))
    {σ τ : S.O} (hσ : σ ∈ S.Lbar k) (hσ1 : σ ≠ 1) (hτ : τ ∈ S.Lbar ((m : G) * k))
    (hτ1 : τ ≠ 1) (hc : σ * τ = τ * σ) : False := by
  have hE : Ebar S k ((m : G) * k) ≠ ⊥ := fun h0 => hσ1 (by
    have hmem := (P.mem_Ebar_of_commute hσ hσ1 hτ hτ1 hc).1
    rw [h0] at hmem
    exact Subgroup.mem_bot.mp hmem)
  have X97 := P.hyp97 hE
  by_cases hidx : Nat.card (S.Lbar k) = 2 * Nat.card (Ebar S k ((m : G) * k))
  · exact P.false_of_index_two hE hidx
  · have h4 := X97.four_mul_card_le P.not_Lbar_le_O2Sub (by rw [P.inf_O2Sub_eq]; exact hidx)
    rw [P.inf_O2Sub_eq] at h4
    obtain ⟨φ, hφs, hφk⟩ := hA5 hE h4
    exact P.false_of_A5 hφs hφk h4

theorem Cfg111.no_commuting_pair (C : Cfg111 S g A) (hh : h ∈ S.M)
    (hA : A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z) {k j : G}
    (hk : k * S.z * k⁻¹ ∈ A) (hkz : k * S.z * k⁻¹ ≠ S.z)
    (hj : j * S.z * j⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom) (hjz : j * S.z * j⁻¹ ≠ S.z)
    (hA5 : ∀ m : S.M, ((m : G) * k) * S.z * ((m : G) * k)⁻¹ = j * S.z * j⁻¹ →
      Ebar S k ((m : G) * k) ≠ ⊥ →
      4 * Nat.card (Ebar S k ((m : G) * k)) ≤ Nat.card (S.Lbar k) →
      ∃ φ : ↥(S.Lbar k ⊔ S.Lbar ((m : G) * k)) →* alternatingGroup (Fin 5),
        Function.Surjective φ ∧ φ.ker = CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar ((m : G) * k)))
    {σ τ : S.O} (hσ : σ ∈ S.Lbar k) (hτ : τ ∈ S.Lbar j) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) :
    σ * τ ≠ τ * σ := by
  intro hc
  have P : Pair111 S g A h k j := ⟨C, hh, hA, hk, hkz, hj, hjz⟩
  obtain ⟨m, hm⟩ := P.exists_conj
  have P' : Pair111 S g A h k ((m : G) * k) :=
    ⟨C, hh, hA, hk, hkz, hm ▸ hj, hm ▸ hjz⟩
  have hτ' : τ ∈ S.Lbar ((m : G) * k) := by rwa [Lbar_eq_of_conj_eq S hm]
  exact P'.false_of_commute (hA5 m hm) hσ hσ1 hτ' hτ1 hc

theorem noCommuting111_of (hA5 : A5Input111) : NoCommuting111 := by
  intro G _ _ _ S g A C h6 h hh hA k j hk hkz hj hjz σ hσ τ hτ hσ1 hτ1
  exact C.no_commuting_pair hh hA hk hkz hj hjz
    (fun m hm hE h4 => hA5 G S g A C h6 h hh hA k m hk hkz (hm ▸ hj) hE h4) hσ hτ hσ1 hτ1

theorem a5Input111_of (hTI : TIClaim111) (hRes : Residual97For111) : A5Input111 := by
  intro G _ _ _ S g A C h6 h hh hA k m hk hkz hmk hE h4
  have P : Pair111 S g A h k ((m : G) * k) := ⟨C, hh, hA, hk, hkz, hmk, conj_ne_z' S m.2 hkz⟩
  have hti := hTI G S g A C h6 h hh hA k ((m : G) * k) hk hkz hmk P.ne' hE h4
  have hC := S9.timmesfeld_9_7 (hRes G S g A C h6 h hh hA k m hk hkz hmk _) (P.hyp97 hE)
    (P.isTI97 hti) P.not_Lbar_le_O2Sub
  rcases hC with ⟨φ, hφs, hφk⟩ | ⟨φ, hφs, hφk⟩
  · exfalso
    have h1 := card_eq_card_inf_mul_card_range le_sup_left φ hφk
    rw [P.inf_O2Sub_eq] at h1
    have h2 : IsPGroup 2 (φ.comp (inclusion (le_sup_left :
        S.Lbar k ≤ S.Lbar k ⊔ S.Lbar ((m : G) * k)))).range :=
      (isPGroup_Lbar S P.memQ).of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    have h3 := card_le_two_of_isPGroup_perm_three h2
    have hE0 : 0 < Nat.card (Ebar S k ((m : G) * k)) := Nat.card_pos
    nlinarith
  · exact ⟨φ, hφs, hφk.trans (subgroupOf_O2Sub _)⟩

end CFSG.LargeExtraspecial.S11
