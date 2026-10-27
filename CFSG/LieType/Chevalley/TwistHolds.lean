module

public import CFSG.LieType.Chevalley.FixedNative
public import CFSG.LieType.Chevalley.RelativeWeylTwist
public import CFSG.LieType.Chevalley.TwistUnipotent
public import CFSG.LieType.Chevalley.FixedCollection

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.BorelTits CFSG.LieType.BorelTits.Weighted RootSpace

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] noncomputable def twistFixed : Subgroup (adjointGroup t.tag K) :=
  MonoidHom.eqLocus (twistC t K σ) (MonoidHom.id _)

theorem mem_twistFixed {g : adjointGroup t.tag K} : g ∈ twistFixed t K σ ↔ twistC t K σ g = g :=
  Iff.rfl

variable [Finite K]

theorem twistFixed_bruhat (hσ : Function.Surjective σ) :
    ∀ g ∈ twistFixed t K σ, ∃ w ∈ relWeylTwist t, ∃ b₁ ∈ (nativeData t.tag K).B,
      b₁ ∈ twistFixed t K σ ∧ ∃ b₂ ∈ (nativeData t.tag K).B, b₂ ∈ twistFixed t K σ ∧
        g = b₁ * nrep t.tag K w * b₂ := by
  intro g hg
  obtain ⟨w, hw, b, hb, hbF, u, hu, huF, rfl⟩ := nativeData_exists_fixed_mul
    (twistEquiv t K σ hσ) (weylTwist t) (twistEquiv_mem_B t K σ hσ)
    (twistEquiv_mem_monomialGroup t K σ hσ) (weylHom_twistEquiv t K σ hσ)
    (twistEquiv_mem_Uminus t K σ hσ) (twistEquiv_nrep t K σ hσ) (g := g) hg
  exact ⟨w, hw, b, hb, hbF, u, RootGroupData.U_le_B (Uminus_le_U t.tag K w hu), huF, rfl⟩

omit [Finite K] in
theorem nrep_mem_twistFixed (hσ : Function.Surjective σ) {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) : nrep t.tag K w ∈ twistFixed t K σ :=
  twistEquiv_nrep t K σ hσ w hw

theorem twistFixed_hUw (hσ : Function.Surjective σ) :
    ∀ w ∈ relWeylTwist t, w ≠ 1 → ∃ u ∈ (nativeData t.tag K).U, u ∈ twistFixed t K σ ∧
      nrep t.tag K w * u * (nrep t.tag K w)⁻¹ ∉ (nativeData t.tag K).U := by
  intro w hw hw1
  obtain ⟨u, hu, hF, hn⟩ := exists_twistEquiv_fixed_conj_not_mem_U t K σ hσ hw hw1
  exact ⟨u, hu, hF, hn⟩

theorem holds_twistFixed (p : ℕ) [Fact p.Prime] [CharP K p] (hσ : Function.Surjective σ) :
    Holds (twistFixed t K σ) p :=
  holds_of_fixedNative p (twistFixed t K σ) (relWeylTwist t) (fixedSpace (twistIsometry t))
    (heightVector t.tag) (fun _ hα => IsRoot.inner_heightVector_pos hα)
    (heightVector_mem_fixedSpace_twist t) (fun _ hw _ hx => weylAct_mem_fixedSpace_twist t hw hx)
    (fun _ hw => nrep_mem_twistFixed t K σ hσ hw) (fun _ hv hfix => relWeylTwist_fixfree t hv hfix)
    (fun _ hx => relWeylTwist_cover t hx) (twistFixed_bruhat t K σ hσ) (twistFixed_hUw t K σ hσ)

theorem exists_sylow_twistFixed (p : ℕ) [Fact p.Prime] [CharP K p]
    (hσ : Function.Surjective σ) :
    ∃ S : Sylow p (twistFixed t K σ), (S : Subgroup (twistFixed t K σ)) =
      (nativeData t.tag K).U.comap (twistFixed t K σ).subtype := by
  set F := nativeRootSubgroups t.tag K
  have hS₀p : IsPGroup p ((nativeData t.tag K).U.comap (twistFixed t K σ).subtype) :=
    (F.isPGroup_U p).comap_of_injective _ Subtype.val_injective
  refine exists_sylow_eq_of_normalizer p hS₀p fun g hg ⟨k, hk⟩ => ?_
  have hgB := normalizer_le_of_fixedData (nrep t.tag K) (nativeData t.tag K).B
    (nativeData t.tag K).U (twistFixed t K σ) (relWeylTwist t) (twistFixed_bruhat t K σ hσ)
    F.B_le_normalizer_U (by rw [nrep_one]; exact one_mem _) (twistFixed_hUw t K σ hσ) hg
  exact F.mem_U_of_pow_eq_one p hgB (k := k) (by simpa using congrArg Subtype.val hk)

end CFSG.LieType.Chevalley
