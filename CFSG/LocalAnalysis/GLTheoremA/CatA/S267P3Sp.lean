module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3SpModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Iso
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier
import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Sp

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S267.P3 CFSG.LocalAnalysis.GLTheoremA.S267.P3.Form

theorem concA_of_C3 {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    (H : P3Hyp q S B) {Q : TauCeti.PrimePower} (hQq : Q.p = q)
    (hv : (TauCeti.LieTypeIndex.C 3 Q).Valid)
    (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.C 3 Q, hv⟩).Group) : S267ConcA 3 S B := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC 3 Q hv e
  haveI : CharP K Q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hp2 : Q.p ≠ 2 := hQq ▸ H.two
  have hp3 : Q.p ≠ 3 := hQq ▸ H.three
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    exact (hp.five_le_of_ne_two_of_ne_three hp2 hp3).trans (Nat.le_self_pow (by omega) _)
  have hZ : Subgroup.center ↥S = ⊥ := by
    refine H.center_eq_bot_of_multiplier e₁ ?_
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_hopfMultiplier (K := K) (n := 3)
        (by norm_num) hK5
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    intro hd
    have h1 := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num)) hd
    have h2 := Nat.gcd_le_left (Nat.card K - 1) (show 0 < 2 by norm_num)
    omega
  have hcast : ∀ n : ℕ, n.Prime → Q.p ≠ n → ((n : ℕ) : K) ≠ 0 := fun n hn' hne h =>
    hne ((Nat.prime_dvd_prime_iff_eq hp hn').1 ((CharP.cast_eq_zero_iff K Q.p n).1 h))
  have h2K : (2 : K) ≠ 0 := by exact_mod_cast hcast 2 Nat.prime_two hp2
  have h3K : (3 : K) ≠ 0 := by exact_mod_cast hcast 3 Nat.prime_three hp3
  obtain ⟨φ, hφ, hφS⟩ := exists_embedding_of_mulEquiv H hZ (spProjEquiv.trans e₁.symm)
  exact concA_of_modelA H hZ φ hφ hφS
    ((spData (F := K)).modelA h3K h2K (isQuasisimple_spOn (by norm_num) (by omega) ek reindex_Jk)
      (isQuasisimple_spOn (by norm_num) (by omega) el reindex_Jl) noThree_spData)

theorem p3At_C3 {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.C 3 Q).Valid) :
    P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exact Or.inl (concA_of_C3 H (by simpa using hchar) hv e)

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Sp

end
