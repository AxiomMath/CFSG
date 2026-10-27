module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixedRootMono
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LeviCatalogueCentralizer
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootQ1

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Core

variable {G : Type*} [Group G]

private theorem map_conj_map_conj' (X : Subgroup G) (g h : G) :
    (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_one' (X : Subgroup G) :
    X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
  rw [h, Subgroup.map_id]

private theorem map_conj_eq_of_fix (X : Subgroup G) {c : G} (hc : ∀ a ∈ X, c * a * c⁻¹ = a) :
    X.map (MulAut.conj c).toMonoidHom = X := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    change c * b * c⁻¹ ∈ X
    rw [hc b hb]
    exact hb
  · intro ha
    exact ⟨a, ha, hc a ha⟩

theorem normalizesRGroup_of_conj_orbit {r : ℕ} [Fact r.Prime] (E₀ X : Subgroup G)
    (hX : X ≠ ⊥) (hXr : IsPGroup r X) (z : G) (hz3 : z ^ 3 = 1)
    (hzE : ∀ x ∈ E₀, Commute z x)
    (h12 : ∀ a ∈ X, ∀ b ∈ X, Commute a (z * b * z⁻¹))
    (h13 : ∀ a ∈ X, ∀ b ∈ X, Commute a (z ^ 2 * b * (z ^ 2)⁻¹))
    (h23 : ∀ a ∈ X, ∀ b ∈ X, Commute (z * a * z⁻¹) (z ^ 2 * b * (z ^ 2)⁻¹))
    (hfix : ∀ x ∈ E₀, ∃ k : ℕ, ∀ a ∈ X, z ^ k * x * a * (z ^ k * x)⁻¹ = a) :
    NormalizesRGroup r E₀ := by
  set X₁ := X.map (MulAut.conj z).toMonoidHom with hX₁
  set X₂ := X.map (MulAut.conj (z ^ 2)).toMonoidHom with hX₂
  have h01 : X₁ ≤ Subgroup.centralizer (X : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (h12 a ha b hb).eq
  have h02 : X₂ ≤ Subgroup.centralizer (X : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (h13 a ha b hb).eq
  have h12' : X₂ ≤ Subgroup.centralizer (X₁ : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact (h23 a ha b hb).eq
  have hY : IsPGroup r (X₁ ⊔ X₂ : Subgroup G) := (hXr.map _).to_sup_of_normal_right' (hXr.map _)
    ((Subgroup.le_centralizer_iff.1 h12').trans (Subgroup.centralizer_le_normalizer _))
  have hR : IsPGroup r (X ⊔ (X₁ ⊔ X₂) : Subgroup G) := hXr.to_sup_of_normal_right' hY
    ((Subgroup.le_centralizer_iff.2 (sup_le h01 h02)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hzR : (X ⊔ (X₁ ⊔ X₂)).map (MulAut.conj z).toMonoidHom = X ⊔ (X₁ ⊔ X₂) := by
    rw [Subgroup.map_sup, Subgroup.map_sup, hX₁, hX₂, map_conj_map_conj', map_conj_map_conj',
      ← pow_two, show z * z ^ 2 = 1 by rw [← pow_succ']; exact hz3, map_conj_one', ← sup_assoc,
      sup_comm]
  have hcR : ∀ c : G, (∀ a ∈ X, c * a * c⁻¹ = a) → Commute c z →
      (X ⊔ (X₁ ⊔ X₂)).map (MulAut.conj c).toMonoidHom = X ⊔ (X₁ ⊔ X₂) := by
    intro c hc hcz
    have hcX := map_conj_eq_of_fix X hc
    have hg : ∀ g : G, Commute c g →
        (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj c).toMonoidHom =
          X.map (MulAut.conj g).toMonoidHom := fun g hcg => by
      rw [map_conj_map_conj', hcg.eq, ← map_conj_map_conj', hcX]
    rw [Subgroup.map_sup, Subgroup.map_sup, hcX, hX₁, hX₂, hg z hcz,
      hg (z ^ 2) (hcz.pow_right 2)]
  have hN : ∀ g : G, (X ⊔ (X₁ ⊔ X₂)).map (MulAut.conj g).toMonoidHom = X ⊔ (X₁ ⊔ X₂) →
      g ∈ Subgroup.normalizer ((X ⊔ (X₁ ⊔ X₂) : Subgroup G) : Set G) := fun g h => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rwa [MulEquiv.toMonoidHom_eq_coe] at h
  refine ⟨X ⊔ (X₁ ⊔ X₂), fun h => hX (eq_bot_iff.2 (h ▸ le_sup_left)), hR, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hfix x hx
  have hcz : Commute (z ^ k * x) z := ((Commute.refl z).pow_left k).mul_left (hzE x hx).symm
  have hxN : x ∈ Subgroup.normalizer ((X ⊔ (X₁ ⊔ X₂) : Subgroup G) : Set G) := by
    have hx' : x = (z ^ k)⁻¹ * (z ^ k * x) := by group
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (hN z hzR) k))
      (hN _ (hcR _ hk hcz))
  have := Subgroup.mem_normalizer_iff_map_conj_eq.1 hxN
  rwa [← MulEquiv.toMonoidHom_eq_coe] at this

end Core

section Roots


theorem commute_rootSpan_pair_of_iform_eq_zero {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L]
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (h0 : iform β γ = 0) :
    ∀ x ∈ rootSpan τ L {β, -β}, ∀ y ∈ rootSpan τ L {γ, -γ}, Commute x y := by
  have hpair : ∀ α ∈ ({β, -β} : Set (Fin τ.rank → ℤ)),
      ∀ δ ∈ ({γ, -γ} : Set (Fin τ.rank → ℤ)), ∀ c d : L,
        Commute (pinnedX τ L α c) (pinnedX τ L δ d) := by
    intro α hα δ hδ c d
    have hαr : IsRoot τ α := by
      rcases hα with rfl | rfl
      exacts [hβ, IsRoot.neg hβ]
    have hδr : IsRoot τ δ := by
      rcases hδ with rfl | rfl
      exacts [hγ, IsRoot.neg hγ]
    have h0' : iform α δ = 0 := by
      rcases hα with rfl | rfl <;> rcases hδ with rfl | rfl <;>
        simp [iform_neg_left, iform_neg_right, h0]
    exact (simply_laced_orthogonal_root_commutation τ hτ).2 L α δ hαr hδr
      (by rw [dotProduct_mulVec_eq_iform]; exact h0') _
      (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)
  have hstep : ∀ α ∈ ({β, -β} : Set (Fin τ.rank → ℤ)), ∀ c : L,
      ∀ y ∈ rootSpan τ L {γ, -γ}, Commute (pinnedX τ L α c) y :=
    fun α hα c => commute_of_mem_rootSpan_pair (fun d => hpair α hα γ (Or.inl rfl) c d)
      (fun d => hpair α hα (-γ) (Or.inr rfl) c d)
  intro x hx y hy
  exact (commute_of_mem_rootSpan_pair (fun c => (hstep β (Or.inl rfl) c y hy).symm)
    (fun c => (hstep (-β) (Or.inr rfl) c y hy).symm) x hx).symm

theorem conj_monomial_mem_rootSpan_pair {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    (w : WeylGroup τ) {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hwβ : w • β = γ) :
    ∀ y ∈ rootSpan τ L {β, -β},
      rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w * y *
          (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w)⁻¹ ∈ rootSpan τ L {γ, -γ} := by
  have hle : rootSpan τ L {β, -β} ≤ (rootSpan τ L {γ, -γ}).comap
      (MulAut.conj (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w)).toMonoidHom := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    have hαr : IsRoot τ α := by
      rcases hα with rfl | rfl
      exacts [hβ, IsRoot.neg hβ]
    have hwα : w • α ∈ ({γ, -γ} : Set (Fin τ.rank → ℤ)) := by
      rcases hα with rfl | rfl
      · exact Or.inl hwβ
      · exact Or.inr (by rw [smul_neg, hwβ]; exact Set.mem_singleton _)
    obtain ⟨ε, -, hε⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hαr
    change rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w * pinnedX τ L α c *
      (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w)⁻¹ ∈ rootSpan τ L {γ, -γ}
    have e : rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w * pinnedX τ L α c *
        (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w)⁻¹ =
        rootDiagUnit τ a * (canonicalRep (coxeterSystem τ) L w * pinnedX τ L α c *
          (canonicalRep (coxeterSystem τ) L w)⁻¹) * (rootDiagUnit τ a)⁻¹ := by group
    rw [e, hε, rootDiagUnit_conj_pinnedX a (IsRoot.smul hαr w)]
    exact pinnedX_mem_rootSpan hwα _
  intro y hy
  exact hle hy

end Roots

section Orbit


theorem normalizesRGroup_of_orthogonal_orbit (q : ℕ) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hr : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : ∀ a ∈ E₀, ∀ b ∈ E₀, Commute a b)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {β₁ β₂ β₃ : Fin TwistTag.E6.tag.rank → ℤ} (hβ₁ : IsRoot TwistTag.E6.tag β₁)
    (hβ₂ : IsRoot TwistTag.E6.tag β₂) (hβ₃ : IsRoot TwistTag.E6.tag β₃)
    (hvβ₁ : v • permLattice TwistTag.E6.perm β₁ = -β₁)
    (h12 : iform β₁ β₂ = 0) (h13 : iform β₁ β₃ = 0) (h23 : iform β₂ β₃ = 0)
    {z : twistedE6RootGroup K σ} (hz : z ∈ E₀) (hz3 : z ^ 3 = 1)
    (hz12 : ∀ s ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₁, -β₁},
      (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL TwistTag.E6.tag K) *
          g0) * s *
        (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL TwistTag.E6.tag K) *
          g0)⁻¹ ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₂, -β₂})
    (hz23 : ∀ s ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₂, -β₂},
      (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL TwistTag.E6.tag K) *
          g0) * s *
        (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL TwistTag.E6.tag K) *
          g0)⁻¹ ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₃, -β₃})
    (hfix : ∀ x ∈ E₀, ∃ k : ℕ, ∀ y ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₁, -β₁},
      Commute (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((z ^ k * x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0) y) :
    NormalizesRGroup (ringChar K) E₀ := by
  classical
  haveI : Fact (ringChar K).Prime := ⟨CharP.prime_ringChar K⟩
  have hτ : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
      TwistTag.E6.tag = .E8 := Or.inr (Or.inl rfl)
  obtain ⟨X, Xm, ⟨g, hX, -⟩, hS⟩ :=
    exists_longRootPair_of_negDatum q K σ hK hσ hr Fr hFr v g0 hg0C hg0 hβ₁ hvβ₁
  set ι := baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K)) with hι
  set z' := g0⁻¹ * ι (z : ModGL TwistTag.E6.tag K) * g0 with hz'
  have hXS : ∀ u ∈ X, ∃ y ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₁, -β₁},
      g0 * y * g0⁻¹ = ι (u : ModGL TwistTag.E6.tag K) := fun u hu =>
    Subgroup.mem_map.1 ((hS u).1 (Subgroup.subset_closure (Or.inl hu)))
  have hXne : X ≠ ⊥ := by
    rw [hX]
    intro h
    apply (twE6RootSubgroup_ne_bot σ).1
    rw [eq_bot_iff]
    intro u hu
    have h1 : (MulAut.conj g).toMonoidHom u ∈
        (twE6RootSubgroup K σ e6HighestRoot).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hu
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    simpa using h1
  have hXr : IsPGroup (ringChar K) X := by
    rw [hX]
    exact (TwE6LongRoot.isPGroup_twE6RootSubgroup σ e6HighestRoot).map _
  have hconj : ∀ (j : ℕ) (u : twistedE6RootGroup K σ) (y : ModGL TwistTag.E6.tag _),
      g0 * y * g0⁻¹ = ι (u : ModGL TwistTag.E6.tag K) →
        ι ((z ^ j * u * (z ^ j)⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
          g0 * (z' ^ j * y * (z' ^ j)⁻¹) * g0⁻¹ := by
    intro j u y hyu
    have hzj : ι ((z ^ j : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        g0 * z' ^ j * g0⁻¹ := by
      have h1 : g0 * z' * g0⁻¹ = ι (z : ModGL TwistTag.E6.tag K) := by
        rw [hz']
        group
      have h2 := map_pow (MulAut.conj g0) z' j
      simp only [MulAut.conj_apply] at h2
      rw [Subgroup.coe_pow, map_pow, h2, h1]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, hzj,
      ← hyu]
    group
  have hS2 : ∀ y ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₁, -β₁},
      z' ^ 1 * y * (z' ^ 1)⁻¹ ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₂, -β₂} :=
    fun y hy => by
      rw [pow_one]
      exact hz12 y hy
  have hS3 : ∀ y ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₁, -β₁},
      z' ^ 2 * y * (z' ^ 2)⁻¹ ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₃, -β₃} :=
    fun y hy => by
      have h := hz23 _ (hz12 y hy)
      rwa [show z' * (z' * y * z'⁻¹) * z'⁻¹ = z' ^ 2 * y * (z' ^ 2)⁻¹ by rw [pow_two]; group] at h
  have hcomm : ∀ (i j : ℕ) {γ δ : Fin TwistTag.E6.tag.rank → ℤ},
      (∀ y ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₁, -β₁},
        z' ^ i * y * (z' ^ i)⁻¹ ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {γ, -γ}) →
      (∀ y ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₁, -β₁},
        z' ^ j * y * (z' ^ j)⁻¹ ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {δ, -δ}) →
      (∀ s ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {γ, -γ},
        ∀ t ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {δ, -δ}, Commute s t) →
      ∀ a ∈ X, ∀ b ∈ X, Commute (z ^ i * a * (z ^ i)⁻¹) (z ^ j * b * (z ^ j)⁻¹) := by
    intro i j γ δ hi hj hγδ a ha b hb
    obtain ⟨ya, hya, hyau⟩ := hXS a ha
    obtain ⟨yb, hyb, hybu⟩ := hXS b hb
    have hc := (hγδ _ (hi ya hya) _ (hj yb hyb)).eq
    show z ^ i * a * (z ^ i)⁻¹ * (z ^ j * b * (z ^ j)⁻¹) =
      z ^ j * b * (z ^ j)⁻¹ * (z ^ i * a * (z ^ i)⁻¹)
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    change ι (((z ^ i * a * (z ^ i)⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        ((z ^ j * b * (z ^ j)⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)) =
      ι (((z ^ j * b * (z ^ j)⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        ((z ^ i * a * (z ^ i)⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K))
    rw [map_mul, map_mul, hconj i a ya hyau, hconj j b yb hybu]
    calc g0 * (z' ^ i * ya * (z' ^ i)⁻¹) * g0⁻¹ * (g0 * (z' ^ j * yb * (z' ^ j)⁻¹) * g0⁻¹)
        = g0 * ((z' ^ i * ya * (z' ^ i)⁻¹) * (z' ^ j * yb * (z' ^ j)⁻¹)) * g0⁻¹ := by group
      _ = g0 * ((z' ^ j * yb * (z' ^ j)⁻¹) * (z' ^ i * ya * (z' ^ i)⁻¹)) * g0⁻¹ := by rw [hc]
      _ = g0 * (z' ^ j * yb * (z' ^ j)⁻¹) * g0⁻¹ * (g0 * (z' ^ i * ya * (z' ^ i)⁻¹) * g0⁻¹) := by
          group
  have hS1 : ∀ y ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₁, -β₁},
      z' ^ 0 * y * (z' ^ 0)⁻¹ ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β₁, -β₁} :=
    fun y hy => by simpa using hy
  refine normalizesRGroup_of_conj_orbit E₀ X hXne hXr z hz3 (fun x hx => hE₀ z hz x hx)
    (fun a ha b hb => ?_) (fun a ha b hb => ?_) (fun a ha b hb => ?_) (fun x hx => ?_)
  · have h := hcomm 0 1 hS1 hS2
      (commute_rootSpan_pair_of_iform_eq_zero hτ hβ₁ hβ₂ h12) a ha b hb
    simpa using h
  · have h := hcomm 0 2 hS1 hS3
      (commute_rootSpan_pair_of_iform_eq_zero hτ hβ₁ hβ₃ h13) a ha b hb
    simpa using h
  · have h := hcomm 1 2 hS2 hS3
      (commute_rootSpan_pair_of_iform_eq_zero hτ hβ₂ hβ₃ h23) a ha b hb
    simpa using h
  · obtain ⟨k, hk⟩ := hfix x hx
    refine ⟨k, fun u hu => ?_⟩
    obtain ⟨y, hy, hyu⟩ := hXS u hu
    have hc := (hk y hy).eq
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    change ι (((z ^ k * x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        (u : ModGL TwistTag.E6.tag K) *
        ((z ^ k * x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)⁻¹) =
      ι (u : ModGL TwistTag.E6.tag K)
    rw [map_mul, map_mul, map_inv, ← hyu]
    set c := ι ((z ^ k * x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)
    calc c * (g0 * y * g0⁻¹) * c⁻¹
        = g0 * (g0⁻¹ * c * g0 * y) * (g0⁻¹ * c * g0)⁻¹ * g0⁻¹ := by group
      _ = g0 * (y * (g0⁻¹ * c * g0)) * (g0⁻¹ * c * g0)⁻¹ * g0⁻¹ := by rw [hc]
      _ = g0 * y * g0⁻¹ := by group

end Orbit

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
