module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Inner
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6FTw

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open CFSG.Blueprint CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.YS04E6F (meets_inner_E6_untw meets_inner_E6_tw)

theorem k35Good_of_e6 {X : Type} [Group X] {q : ℕ} (hm : UntwistedChevalleyModel X .E6 q)
    (h3 : 3 ∣ q - 1) : K35Good X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
  refine K35Good.of_mulEquiv e ?_
  intro A hA hA9
  obtain ⟨α, ⟨hαA, hαI⟩, hα1⟩ := meets_inner_E6_untw (K := K) (by rwa [hK]) A hA hA9
  exact Or.inl ⟨α, hαA, hα1, hαI⟩

theorem k35Good_of_twistedE6 {r f : ℕ} (hr : r.Prime) (hf : 1 ≤ f) {X : Type} [Group X]
    (hm : TwistedChevalleyModel X .E6 (r ^ f)) (h3 : 3 ∣ r ^ f + 1) : K35Good X := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .E6 hr hf K hK
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨E⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hr hf K hK σ' hσ'
  refine K35Good.of_mulEquiv (e.trans E) ?_
  intro A hA hA9
  obtain ⟨α, ⟨hαA, hαI⟩, hα1⟩ := meets_inner_E6_tw σ' hr hf hK hσ' h3 A hA hA9
  exact Or.inl ⟨α, hαA, hα1, hαI⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
