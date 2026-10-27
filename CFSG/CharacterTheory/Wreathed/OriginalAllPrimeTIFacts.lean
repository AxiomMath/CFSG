module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTIFactsModel
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTIFactsSylow

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB

theorem wreathedSetting_tiFacts
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hM : ModelSignalizers.AllModelSignalizerFacts) :
    (wreathedSetting n S e p f).TIFacts := by
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨F, hfield, hfinite, Sigma, b, hSigma, ρ, Ψ, hdata⟩ :=
    exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hp2 hf hlocal
  let : Field F := hfield
  let : Finite F := hfinite
  let : Fintype F := Fintype.ofFinite F
  have hm2 := NormalComponentLift.two_pow_eq_two_part hnonab hfour hp hp2 hf hlocal
  have hMf := hM F p f hp hpodd hf hdata.card hq _ rfl (2 ^ n) (wreathModulus_pos n)
    (wreathModulus_even hn) hm2 Sigma hdata.sigma_odd b hSigma hdata.nonsquare
  obtain ⟨h, hh⟩ := TIFacts.exists_liftMap_eq_modelY hnonab hfour hp hpodd hf hlocal hdata
  have hφ := TIFacts.liftMap_isModelMap hnonab hfour hp hpodd hf hlocal hdata hh
  obtain ⟨z, hzD, hzN, hz⟩ := TIFacts.exists_swap_conj hn hφ
    (TIFacts.liftMap_x_eq hnonab hfour hp hpodd hf hlocal hdata h)
  have hheight : (wreathedSetting n S e p f).height ≠ 1 := by
    change n ≠ 1
    omega
  have hδ : (wreathedSetting n S e p f).DeltaEpsMinus → (wreathedSetting n S e p f).q % 4 = 1 := by
    rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · exact absurd h1 hheight
    · exact h2
  exact
    { F₀_abelian := TIFacts.wreathedSetting_F₀_abelian n hn S e p f
      F₀_omega := TIFacts.wreathedSetting_F₀_omega n hn S e p f
      C_eq := TIFacts.wreathedSetting_C_eq n hn S e p f
      commutator_le := TIFacts.wreathedSetting_commutator_le hnonab n hn S e hfour p f hp hpodd hf
        hlocal
      cyclic := hφ.cyclic (TIFacts.isCyclic_modelLayer_inf_modelC hp hpodd hf hdata.card
        (wreathModulus_pos n) (wreathModulus_even hn) hm2 hdata.sigma_odd hSigma hdata.nonsquare)
      centralizer_le := hφ.centralizer_le hMf.centralizer_le (TIFacts.modelBase_le_map_L hn hφ)
      signalizer_le := hφ.signalizer_le hMf.signalizer_le
      layer_signalizer := hφ.layer_signalizer hheight hMf.layer_signalizer
      layer_signalizer_pair := hφ.layer_signalizer_pair hMf.layer_signalizer_pair hδ hzD hzN hz
      permutable_le := hφ.permutable_le hMf.permutable_le }

end CFSG.Wreathed.OriginalAllPrime
