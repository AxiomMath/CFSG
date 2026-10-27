module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenFour
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LargeExtraspecial.BridgeNat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem TwoCentralData.comap (e : G ≃* G') {k : ℕ} {z : G} {R' : Subgroup G'}
    (D : TwoCentralData k (e z) R') : TwoCentralData k z (R'.comap e.toMonoidHom) := by
  have hc : R'.comap e.toMonoidHom = R'.map e.symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm e R'
  have hmem : ∀ x : G, x ∈ R'.comap e.toMonoidHom ↔ e x ∈ R' := fun x => Iff.rfl
  have hcomm : ∀ a b : G, a * b = b * a ↔ e a * e b = e b * e a := fun a b => by
    rw [← map_mul, ← map_mul]
    exact ⟨fun h => by rw [h], fun h => e.injective h⟩
  refine ⟨?_, ?_, D.z_mem, fun h => D.z_ne_one (by rw [h, map_one]), ?_, ?_, ?_, ?_⟩
  · rw [hc]
    exact CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
      (MulEquiv.subgroupMap e.symm R') D.extraspecial
  · rw [hc, Subgroup.card_map_of_injective e.symm.injective, D.card]
  · intro p hp
    exact (hcomm p z).2 (D.z_central (e p) hp)
  · intro g hg hcg
    refine (hmem g).2 (D.cent_le (e g) ((hcomm g z).1 hg) fun p hp => ?_)
    have hp' : e.symm p ∈ R'.comap e.toMonoidHom := by
      rw [hmem, MulEquiv.apply_symm_apply]
      exact hp
    have := (hcomm (e.symm p) g).1 (hcg _ hp')
    simpa using this
  · intro g hg
    have hN := Subgroup.mem_normalizer_iff.1 (D.normalizes (e g) ((hcomm g z).1 hg))
    refine Subgroup.mem_normalizer_iff.2 fun h => ?_
    rw [hmem, hmem, map_mul, map_mul, map_inv]
    exact hN (e h)
  · intro F X hF hX hFe hFc hX2 hFN
    have hcent : ∀ {H : Subgroup G}, H ≤ Subgroup.centralizer ({z} : Set G) →
        H.map e.toMonoidHom ≤ Subgroup.centralizer ({e z} : Set G') := by
      intro H hH x hx
      obtain ⟨h, hh, rfl⟩ := hx
      exact Subgroup.mem_centralizer_singleton_iff.2
        ((hcomm h z).1 (Subgroup.mem_centralizer_singleton_iff.1 (hH hh)))
    have hXR : X.map e.toMonoidHom ≤ R' := by
      refine D.contains (F.map e.toMonoidHom) (X.map e.toMonoidHom) (hcent hF) (hcent hX)
        (hFe.map _) ?_ ?_ ?_
      · rw [Subgroup.card_map_of_injective e.injective, hFc]
      · exact hX2.of_equiv (MulEquiv.subgroupMap e X)
      · intro f hf
        obtain ⟨f₀, hf₀, rfl⟩ := hf
        refine Subgroup.mem_normalizer_iff.2 fun h => ?_
        have hN := Subgroup.mem_normalizer_iff.1 (hFN hf₀) (e.symm h)
        have e1 : ∀ w : G', w ∈ X.map e.toMonoidHom ↔ e.symm w ∈ X := fun w =>
          Subgroup.mem_map_equiv
        have e2 : e.symm (e.toMonoidHom f₀ * h * (e.toMonoidHom f₀)⁻¹) =
            f₀ * e.symm h * f₀⁻¹ := by simp
        rw [e1, e1, e2]
        exact hN
    intro x hx
    exact hXR ⟨x, hx, rfl⟩

end Transport

section Normal

variable {G : Type*} [Group G]

theorem TwoCentralData.of_normal {z : G} (hz1 : z ≠ 1)
    {Q : Subgroup (Subgroup.centralizer ({z} : Set G))} (hQn : Q.Normal)
    (hQe : timmesfeldIsExtraspecial ↥Q)
    (hQc : Subgroup.centralizer (Q : Set (Subgroup.centralizer ({z} : Set G))) ≤ Q) {k : ℕ}
    (hQcard : Nat.card Q = 2 ^ (2 * k + 1))
    (hU : ∀ F X : Subgroup G, F ≤ Subgroup.centralizer ({z} : Set G) →
      X ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 F → Nat.card F = 3 ^ k →
      IsPGroup 2 X → F ≤ Subgroup.normalizer (X : Set G) →
      X ≤ Q.map (Subgroup.centralizer ({z} : Set G)).subtype) :
    TwoCentralData k z (Q.map (Subgroup.centralizer ({z} : Set G)).subtype) := by
  have hN : ∀ g : G, g * z = z * g → g ∈ Subgroup.centralizer ({z} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 hg
  have hzQ : (⟨z, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ :
      Subgroup.centralizer ({z} : Set G)) ∈ Q := hQc
    (Subgroup.mem_centralizer_iff.2 fun h _ =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 h.2))
  have key : ∀ (c : Subgroup.centralizer ({z} : Set G)) (x : G),
      x ∈ Q.map (Subgroup.centralizer ({z} : Set G)).subtype →
        (c : G) * x * (c : G)⁻¹ ∈ Q.map (Subgroup.centralizer ({z} : Set G)).subtype := by
    rintro c _ ⟨q, hq, rfl⟩
    exact ⟨c * q * c⁻¹, hQn.conj_mem q hq c, by simp⟩
  refine ⟨?_, ?_, ⟨_, hzQ, rfl⟩, hz1, ?_, ?_, ?_, hU⟩
  · exact CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
      (Q.equivMapOfInjective _ (Subgroup.subtype_injective _)) hQe
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hQcard]
  · rintro p ⟨c, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 c.2
  · intro g hg hcomm
    have hgN := hN g hg
    have hmem : (⟨g, hgN⟩ : Subgroup.centralizer ({z} : Set G)) ∈
        Subgroup.centralizer (Q : Set (Subgroup.centralizer ({z} : Set G))) :=
      Subgroup.mem_centralizer_iff.2 fun q hq => Subtype.ext (hcomm q ⟨q, hq, rfl⟩)
    exact ⟨⟨g, hgN⟩, hQc hmem, rfl⟩
  · intro g hg
    have hgN := hN g hg
    refine Subgroup.mem_normalizer_iff.2 fun x => ⟨key ⟨g, hgN⟩ x, fun hx => ?_⟩
    have h2 := key (⟨g, hgN⟩⁻¹) _ hx
    simpa [mul_assoc] using h2

end Normal

section Inner

variable {S T : Type*} [Group S] [Group T]

theorem nonempty_mulAut_equiv_of_inner (e : S ≃* T)
    (hZ : ∀ t : T, (∀ u : T, u * t = t * u) → t = 1)
    (h : ∀ α : MulAut S, ∃ g : S, α = MulAut.conj g) : Nonempty (MulAut S ≃* T) := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : ∀ u : T, u * e g = e g * u := fun u => by
      have := congrArg (fun φ : MulAut S => φ (e.symm u)) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      apply e.symm.injective
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    exact e.injective (by rw [hZ _ hc, map_one])
  have hsurj : Function.Surjective (MulAut.conj : S →* MulAut S) := fun α =>
    let ⟨g, hg⟩ := h α
    ⟨g, hg.symm⟩
  exact ⟨(MulEquiv.ofBijective (MulAut.conj : S →* MulAut S) ⟨hinj, hsurj⟩).symm.trans e⟩

end Inner

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
