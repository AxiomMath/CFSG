module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
public import CFSG.Blueprint.Catalog
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListSL2
import CFSG.RankThree.Chevalley.OddRankOneExceptionalModel
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
public import CFSG.LieType.Chevalley.RootCommutatorData

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley


theorem oddLocalWitness_G2 {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (hm : ChevalleyExceptionalModel S .G2 2 f) : OddLocalWitness S := by
  obtain ⟨-, hm⟩ := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hm
  have : CharP K 2 := charP_two_of_natCard hK
  obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one hf
  have hcard : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hrd
  refine ⟨r, hr, hr2, ?_, ?_⟩
  · obtain ⟨eT, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
    have hTle : torusGroup .G2 K ≤ adjointGroup .G2 K := by
      rw [torusGroup, Subgroup.closure_le]
      rintro _ ⟨⟨i, u⟩, rfl⟩
      exact torusElt_mem_adjointGroup i u
    let g : Kˣ × Kˣ →* (Fin Tag.G2.rank → Kˣ) :=
      { toFun := fun p i => if (i : ℕ) = 0 then p.1 else p.2
        map_one' := by
          funext i
          simp
        map_mul' := fun p q => by
          funext i
          simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
          split_ifs <;> rfl }
    have hg : Function.Injective g := fun p q hpq => by
      have h0 := congrFun hpq ⟨0, by decide⟩
      have h1 := congrFun hpq ⟨1, by decide⟩
      simp only [g, MonoidHom.coe_mk, OneHom.coe_mk] at h0 h1
      exact Prod.ext (by simpa using h0) (by simpa using h1)
    let φ : Kˣ × Kˣ →* S :=
      e.toMonoidHom.comp ((Subgroup.inclusion hTle).comp (eT.toMonoidHom.comp g))
    have hφ : Function.Injective φ :=
      e.injective.comp ((Subgroup.inclusion_injective hTle).comp (eT.injective.comp hg))
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact two_le_pRank_of_injective_prod hr hcard hcard φ hφ
  · obtain ⟨-, -, -, -, -, -, -, ⟨ρ, -, -, hrange, hinj⟩, -⟩ :=
      ComponentClassification.UnbalancedCatalog.even_G2_highest_long_root_centralizer K
    have hmem : ∀ A, ρ A ∈ adjointGroup .G2 K := fun A =>
      ComponentClassification.UnbalancedCatalog.g2RankOne_le_adjointGroup _ (by
        rw [← hrange]
        exact ⟨A, rfl⟩)
    exact one_le_localRank_of_SL2 (e.toMonoidHom.comp (ρ.codRestrict _ hmem))
      (e.injective.comp fun A B h => hinj (congrArg Subtype.val h)) hr hcard

end CFSG.SectionRank.QTK
