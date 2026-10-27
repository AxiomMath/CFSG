module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporCert

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

theorem pairsFor_of_localPair_equiv (s : TauCeti.SporadicName) {Γ : Type} [Group Γ] [Finite Γ]
    (e : NativeSporadic.Carrier s ≃* Γ) (h : LocalPair Γ) : PairsFor (TypeSporadic s) := by
  intro G _ _ L R hq hty hR hRN hS
  obtain ⟨e'⟩ := hty
  obtain ⟨S₀, K₁, K₂, hS₀, hS₀i, hinv₁, hinv₂, hne₁, hne₂, hsup, hg₁, hg₂⟩ := h
  let θ0 : ↥L →* Γ := (e'.trans e).toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hθ0 : Function.Surjective θ0 :=
    (e'.trans e).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : θ0.ker = CFSG.pCore 2 ↥L := by
    ext x
    simp [θ0]
  exact pairConclusion_of_local_pair hRN hS θ0 hθ0 hker S₀ hS₀ hS₀i K₁ K₂ hinv₁ hinv₂ hne₁ hne₂
    hsup hg₁ hg₂

end CFSG.QuasithinUnique.Vol2Native.L239
