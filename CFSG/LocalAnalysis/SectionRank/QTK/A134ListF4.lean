module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListSL2
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeRee.Torus
import CFSG.LocalAnalysis.SectionRank.LargeReeCover
import CFSG.RankThree.Chevalley.OddRankOneExceptionalModel

public section

namespace CFSG.SectionRank.QTK

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Assembly.LowTwoRank CFSG.SectionRank.LargeRee CFSG.RankThree.Chevalley


theorem oddLocalWitness_twistedF4 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ReeTitsModel S .twistedF4 2 f) : OddLocalWitness S := by
  obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model hm
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one (f := 2 * a + 1) (by omega)
  have hcard : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hrd
  refine ⟨r, hr, hr2, ?_, ?_⟩
  · let T₀ := reeTorusHom a hK fi_zero_mem_longSet
    let T₁ := reeTorusHom a hK fi_one_mem_longSet
    have hcomm : ∀ u v, Commute (T₀ u) (T₁ v) := fun u v =>
      commute_of_mem_reeTorusPart (reeTorusSub_le_reeTorusPart hK _ ⟨u, rfl⟩)
        (reeTorusSub_le_reeTorusPart hK _ ⟨v, rfl⟩)
    have hchar1 : ∀ k, simpleChar (1 : adjointGroup ReeTag.F4.tag K) k = 1 := fun k => by
      simp [simpleChar]
    have hT₀ : ∀ u, T₀ u = 1 → u = 1 := fun u hu => by
      have h1 : ReeTag.F4.reeTorus a (fi 0) u = 1 := congrArg Subtype.val hu
      have h2 := congrArg (fun g => simpleChar g (fi 0)) h1
      simp only [simpleChar_reeTorus, reeExp_zero_zero, hchar1] at h2
      have h3 : ((u : K)) ^ 2 = 1 ^ 2 := by
        rw [one_pow, ← Units.val_pow_eq_pow_val, ← zpow_natCast]
        exact h2
      exact Units.ext (CharTwo.sq_injective h3)
    have hT₁ : ∀ v, T₁ v = 1 → v = 1 := fun v hv => by
      have h1 : ReeTag.F4.reeTorus a (fi 1) v = 1 := congrArg Subtype.val hv
      have h2 := congrArg (fun g => simpleChar g (fi 0)) h1
      simp only [simpleChar_reeTorus, reeExp_one_zero, hchar1] at h2
      have h3 : v⁻¹ = 1 := Units.ext (by rw [← zpow_neg_one]; exact h2)
      exact inv_eq_one.1 h3
    let Ψ : Kˣ × Kˣ →* reeFixed ReeTag.F4 K a := MonoidHom.noncommCoprod T₀ T₁ hcomm
    have hΨ : Function.Injective Ψ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨u, v⟩ huv
      have h1 : T₀ u * T₁ v = 1 := huv
      have hmem : T₀ u ∈ reeTorusSub a hK fi_zero_mem_longSet ⊓
          reeTorusSub a hK fi_one_mem_longSet :=
        ⟨⟨u, rfl⟩, ⟨v⁻¹, by rw [map_inv]; exact (eq_inv_of_mul_eq_one_left h1).symm⟩⟩
      rw [reeTorusSub_inf hK, Subgroup.mem_bot] at hmem
      have hu := hT₀ u hmem
      rw [hmem, one_mul] at h1
      have hv := hT₁ v h1
      rw [hu, hv]
      rfl
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact two_le_pRank_of_injective_prod hr hcard hcard (e.symm.toMonoidHom.comp Ψ)
      (e.symm.injective.comp hΨ)
  · obtain ⟨ψ, hψ, -⟩ := exists_sl2_rankOne (a := a) hK
    exact one_le_localRank_of_SL2 (e.symm.toMonoidHom.comp ψ) (e.symm.injective.comp hψ) hr hcard

end CFSG.SectionRank.QTK
