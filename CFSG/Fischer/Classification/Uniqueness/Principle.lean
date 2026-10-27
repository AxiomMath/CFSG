module

public import CFSG.Fischer.Classification.Uniqueness.Family
public import CFSG.Fischer.Classification.Uniqueness.Triple

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem Pair.exists_mulEquiv_of_localQuotient (hE : Pair X E) (hF : Pair Y F)
    (hZE : Subgroup.center X = ⊥) (hZF : Subgroup.center Y = ⊥)
    (hconnE : (commGraph E).Connected) (hTF : TripleProperty F) {d : X} {d' : Y} (hd : d ∈ E)
    (hd' : d' ∈ F) (hiE : Function.Injective (starImage E d))
    (hiF : Function.Injective (starImage F d')) (hTL : TripleProperty (LocalImages F d'))
    (α : LocalQuotient E d ≃* LocalQuotient F d') (hα : α '' LocalImages E d = LocalImages F d')
    {x : X} (hx : x ∈ E) (hxd : x * d ≠ d * x) {x' : Y} (hx' : x' ∈ F)
    (hxd' : x' * d' ≠ d' * x')
    (hμ : α '' (starImage E d '' {f | (f : X) ∈ muSet E d x}) =
      starImage F d' '' {g | (g : Y) ∈ muSet F d' x'})
    (htrE : ∀ c ∈ E, c * d ≠ d * c →
      ∃ g ∈ LocalGroup E d, muSet E d c = (fun s => g * s * g⁻¹) '' muSet E d x)
    {r : muFamily F d'} (hr : CoverRigid (muGraph F d') r) :
    ∃ ψ : X ≃* Y, ψ '' E = F ∧ ψ d = d' ∧ ∀ f : LocalClass E d,
      ∃ h : ψ f ∈ LocalClass F d', starImage F d' ⟨ψ f, h⟩ = α (starImage E d f) := by
  obtain ⟨φ, hφ, hcomm, htau⟩ := Pair.exists_starEquiv_of_localQuotient hE hF hiE hiF α hα
  have hTE : TripleProperty E := Pair.tripleProperty_of_localImages hE hconnE hd hiE
    ((tripleProperty_congr α hα).2 hTL)
  have hne : (LocalClass F d').Nonempty := by
    obtain ⟨f, hf⟩ := Pair.muSet_nonempty hE hconnE hd hx hxd
    exact ⟨_, (φ ⟨f, hf.1⟩).2⟩
  have h : starMap φ (muSet E d x) = muSet F d' x' :=
    starMap_eq_of_image_eq φ α hφ hiF (muSet_subset_localClass d' x') hμ
  obtain ⟨ψ, h1, h2, h3⟩ := Pair.exists_mulEquiv_of_muSet hE hF hZE hZF hTE hTF hd hd' hne φ
    hcomm htau hx hxd hx' hxd' h htrE hr
  refine ⟨ψ, h1, h2, fun f => ⟨by rw [h3]; exact (φ f).2, ?_⟩⟩
  rw [← hφ]
  congr 1
  exact Subtype.ext (h3 f)

end CFSG.Fischer.Classification
