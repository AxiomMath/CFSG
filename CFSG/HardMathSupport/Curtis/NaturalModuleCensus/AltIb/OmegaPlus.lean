module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCore
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusFlagS

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbedding.LieOut
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

theorem exists_model_d {G : Type} [Group G] (hX : IsLieOf IdxD G) :
    ∃ (n : ℕ) (F : Type) (_ : Field F), Finite F ∧ CharP F 2 ∧ 4 ≤ n ∧
      (Nat.card F = 2 ∨ 4 ≤ Nat.card F) ∧
      Nonempty (G ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) := by
  obtain ⟨⟨d, hv⟩, hPd, ⟨e⟩⟩ := hX
  cases d with
  | D r q =>
    have hq2 : q.p = 2 := hPd
    have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq2 e
    rw [hq2] at hmodel
    obtain ⟨⟨-, hf1, hr⟩, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hmodel
    have hchar : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hf1 hcard
    refine ⟨r, K, hK, hKfin, hchar, hr, ?_, ⟨e'⟩⟩
    rw [hcard]
    rcases Nat.eq_or_lt_of_le hf1 with h1 | h2
    · left; rw [← h1]; norm_num
    · right
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
  | _ => exact hPd.elim

theorem altIbBarCell_d : AltIbBarCell (IsLieOf IdxD) := by
  intro G _ _ hX Jb hsyl hJtop p hp57 a1 a2 x hxp hfix V E hVJ hVx hV hEV hEel hEc
  obtain ⟨n, F, _, hfin, hchar, hn, hK, ⟨ee⟩⟩ := exists_model_d hX
  have : Finite F := hfin
  have : CharP F 2 := hchar
  obtain ⟨T, hT, hNT⟩ := hsyl
  have hidx : ¬ 2 ∣ T.index := by
    have h2 := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 G := hT.2.1.toSylow hidx
  obtain ⟨θ, K, hKne, hθ⟩ := exists_flag_data hn ee T' Jb hNT hJtop
  obtain ⟨σ, S, hSne, hS, hS1, hσ⟩ := exists_JO_of_JK (F := F) hn hKne
  set θ' : G ≃* ↥(Om n F) := θ.trans σ with hθ'def
  have hθ' : Jb.map θ'.toMonoidHom = JO n F S := by
    rw [← hσ, ← hθ, Subgroup.map_map]
    rfl
  have hA1 := transport_a1 θ' a1
  have hA2 := transport_a2 θ' a2
  rw [hθ'] at hA1 hA2
  have hxp' : (θ' x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hfix' : ∀ g : ↥(Om n F), g * θ' x = θ' x * g → g ∈ JO n F S := by
    intro g hg
    have : θ'.symm g * x = x * θ'.symm g := by
      apply θ'.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hg
    rw [← hθ']
    exact ⟨θ'.symm g, hfix _ this, by simp⟩
  have hVJ' : V.map θ'.toMonoidHom ≤ JO n F S := by
    rw [← hθ']; exact Subgroup.map_mono hVJ
  have hVx' : V.map θ'.toMonoidHom ≤ Subgroup.centralizer ({θ' x} : Set ↥(Om n F)) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    show θ' x * θ' v = θ' v * θ' x
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 (hVx hv) x (Set.mem_singleton x))]
  have hV' : ⁅V.map θ'.toMonoidHom, V.map θ'.toMonoidHom⁆ = V.map θ'.toMonoidHom := by
    rw [← Subgroup.map_commutator, hV]
  have hEc' : Nat.card (E.map θ'.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective θ'.injective, hEc]
  exact false_of_flag_D hp57 hK hn hS hS1 hSne hA1 hA2 hxp' hfix' hVJ' hVx' hV'
    (Subgroup.map_mono hEV) (isElemAbelian_map θ' hEel) hEc'

theorem altIbCell_d (hSch : KFactCatalogSchreier)
    (hGA : CFSG.Open.GriessAllModelsStatement) : AltIbCell (IsLieOf IdxD) :=
  altIbCell_of_barCell hSch hGA (fun _ _ hX => Or.inr (Or.inl hX)) altIbBarCell_d

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
