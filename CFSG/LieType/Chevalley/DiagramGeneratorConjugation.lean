module

public import CFSG.LieType.Chevalley.TwistMap

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem diagram_generator_conjugation
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    (∀ (i : Fin t.tag.rank) (c : K),
      twistHom t K σ.toRingHom (xUnit t.tag K i c) = xUnit t.tag K (t.perm i) (σ c)) ∧
    (∀ (i : Fin t.tag.rank) (c : K),
      twistHom t K σ.toRingHom (yUnit t.tag K i c) = yUnit t.tag K (t.perm i) (σ c)) ∧
    ∃ e : adjointGroup t.tag K ≃* adjointGroup t.tag K, ∀ g : adjointGroup t.tag K,
      (e g : ModGL t.tag K) = twistHom t K σ.toRingHom g :=
  ⟨fun i c => twistHom_xUnit t K σ.toRingHom i c, fun i c => twistHom_yUnit t K σ.toRingHom i c,
    twistEquiv t K σ.toRingHom σ.surjective, fun _ => rfl⟩

end CFSG.LieType.Chevalley
