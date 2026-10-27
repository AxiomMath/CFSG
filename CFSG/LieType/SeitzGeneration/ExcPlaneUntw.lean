module

public import CFSG.LieType.SeitzGeneration.ExcPlaneLevi
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.RegimesExc

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti
  CFSG.LieType.Steinberg.Adjoint CFSG.Open CFSG.AGLEmbeddingD2


theorem exists_plane_untwisted_levi {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : Even.UntwistedBridgeAll τ c) (hchar : ∀ q, (c q).characteristic = q.p)
    (hτ : NoG2 τ) {i j k l : Fin τ.rank} (hij : i ≠ j) (hc : τ.cartan i j = 0)
    (hlong : ∀ m, τ.symmetrizer m m ≤ τ.symmetrizer i i) (hk : τ.cartan i k = -1)
    (hl : τ.cartan j l = -1) (hJ : ({i, j} : Set (Fin τ.rank)) ≠ Set.univ) (q : PrimePower)
    (hv : (c q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ q.card ^ 2 - 1) :
    ∃ E : Subgroup (MulAut (Cat ⟨c q, hv⟩)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane ⟨c q, hv⟩ p E ∧ NormalizesRSubgroup ⟨c q, hv⟩ E := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hKr : Nat.card K = q.p ^ q.exponent := by rw [hK, PrimePower.card_def]
  have hdvd' : p ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [hK]
    exact Dvd.dvd.mul_left hdvd _
  obtain ⟨A, R, hAN, hRN, hA, hAcard, hR, hRp, hAR⟩ := exists_levi_plane (K := K) hτ hij hc hlong
    hk hl hJ hKr hp hp2 hdvd'
  obtain ⟨E, hE, hEc, hEin, R', hR'1, hR'p, hR'n⟩ := exists_plane_of_native e hZ hAN hA hAcard hRN
    hRp hR hAR
  exact ⟨E, hE, hEc, hEin, R', hR'1, by simpa [hchar] using hR'p, hR'n⟩

end CFSG.LieType.SeitzGeneration
