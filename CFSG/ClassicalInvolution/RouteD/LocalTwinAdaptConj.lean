module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinAdapt
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakChain
public import CFSG.ClassicalInvolution.RouteD.TypeDChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers ConjInvariant)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)

variable {p f : ℕ} [Fact p.Prime]

theorem exists_adapted_y_of_conj_reach {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}
    (hΩ : ConjInvariant Ω) {Y : LieUniversal} (ψ : Y.K →* locQuot Ω z)
    {n : Fin Y.D.rank → Y.K} {H : Fin Y.D.rank → Subgroup Y.K}
    (hct : IsCTGroupDatum (coxeterMatrix Y.D.isFiniteType).toCoxeterSystem
      (weylAction Y.D.isFiniteType) Y.D.roots Y.D.rootGroup n H)
    {t : G} (ht : t * z * t⁻¹ = z) (v : Fin Y.D.rank → ZMod 2) (k₀ : Y.K)
    (hT : ∀ γ ∈ Y.D.roots,
      (∀ x ∈ (conjSub k₀ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ))).map ψ,
        Gaps.locAut hΩ ht x = x) ↔ charOf v γ = 0)
    {w : Fin Y.D.rank → ZMod 2} (hw : CharReach Y.D.cartan v w)
    {j : Fin Y.D.rank → Subgroup G}
    (hjimg : ∀ a, locImg Ω z (j a) = (rankOne Y.D.rootGroup a).map ψ) :
    ∃ y ∈ locLayer Ω z, ∀ a,
      ((∀ x ∈ locImg Ω z (conjSub y (j a)), Gaps.locAut hΩ ht x = x) ↔ w a = 0) := by
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (ψ k₀)
  let ψ₀ : Y.K →* locQuot Ω z := ψ.comp (MulAut.conj k₀).toMonoidHom
  have hmap : ∀ S : Subgroup Y.K, (conjSub k₀ S).map ψ = S.map ψ₀ := fun S => by
    unfold conjSub
    rw [Subgroup.map_map]
  have hT₀ : ∀ γ ∈ Y.D.roots, (∀ x ∈ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ₀,
      Gaps.locAut hΩ ht x = x) ↔ charOf v γ = 0 := fun γ hγ => by
    rw [← hmap]
    exact hT γ hγ
  have hjimg₀ : ∀ a, locImg Ω z (conjSub (y₀ : G) (j a)) =
      (rankOne Y.D.rootGroup a).map ψ₀ := fun a => by
    rw [Gaps.locImg_conjSub_layer, hjimg a, show Gaps.locMk Ω z y₀ = ψ k₀ from hy₀,
      map_conj_map_hom, hmap]
  obtain ⟨y₁, hy₁, hfix⟩ := exists_adapted_y_of_reach hΩ ψ₀ hct ht v hT₀ hw hjimg₀
  refine ⟨y₁ * (y₀ : G), (locLayer Ω z).mul_mem hy₁ y₀.2, fun a => ?_⟩
  rw [CFSG.ClassicalInvolution.Generic.conjSub_mul]
  exact hfix a

theorem PartnerPatternD.of_toral_conj {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 4 ≤ m)
    {Ω : Set (Subgroup G)} {z : G} {K β : Subgroup G} (c : TCtx p f .POmegaPlus m Ω K z) {t : G}
    (ht : t * z * t⁻¹ = z)
    (e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m)
    {j : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank → Subgroup G}
    (hj : ∀ a, j a ∈ centralizingMembers Ω {z}) (hjK : ∀ a, Commutes K (j a))
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup a).map c.d.ψ)
    (hjc : ∀ a b, a ≠ b → ¬ edgeD m (e a) (e b) → ¬ edgeD m (e b) (e a) → Commutes (j a) (j b))
    (hjp : ∀ a b, edgeD m (e a) (e b) → ∃ W : Subgroup G,
      LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (k₀ : (modelUniv .POmegaPlus m p f Fact.out).K)
    (v : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank → ZMod 2)
    (hT : ∀ γ ∈ (modelUniv .POmegaPlus m p f Fact.out).D.roots,
      (∀ x ∈ (conjSub k₀ ((modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ ⊔
          (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ,
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0)
    (hE : CharReach (modelUniv .POmegaPlus m p f Fact.out).D.cartan v
      (Pi.single (e.symm ⟨0, by omega⟩) 1))
    (hS : ∀ y ∈ locLayer Ω z,
      (∀ b, (∀ x ∈ locImg Ω z (conjSub y (j b)), Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔
        b ≠ e.symm ⟨0, by omega⟩) →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β
        (conjSub y (j (e.symm ⟨0, by omega⟩)))) :
    PartnerPatternD p f m Ω K β t := by
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaPlus m p f := ⟨Fact.out, hf1, by show 4 ≤ m; omega⟩
  obtain ⟨n, H, hct, -⟩ := ModelFacts.hasBruhatDatum .POmegaPlus m p f Fact.out trivial hadm
  obtain ⟨y, hy, hfix⟩ := exists_adapted_y_of_conj_reach c.hΩ.conjInvariant c.d.ψ hct ht v k₀ hT hE
    hjimg
  have hfix' : ∀ b, (∀ x ∈ locImg Ω z (conjSub y (j b)),
      Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ b ≠ e.symm ⟨0, by omega⟩ := fun b => by
    rw [hfix b, Pi.single_apply]
    by_cases h : b = e.symm ⟨0, by omega⟩
    · simp [h]
    · simp [h]
  refine PartnerPatternD.of_locAut c (j := fun a : Fin m => j (e.symm a)) (fun a => hj _)
    (fun a => hjK _) ?_ ?_ hy ht ?_ ?_
  · intro a b hab h1 h2
    exact hjc _ _ (fun hh => hab (e.symm.injective hh)) (by simpa using h1) (by simpa using h2)
  · intro a b h
    exact hjp _ _ (by simpa using h)
  · intro a ha x hx
    refine (hfix' (e.symm a)).mpr (fun h => ?_) x hx
    have := e.symm.injective h
    have := congrArg Fin.val this
    simp only at this
    omega
  · intro a ha
    have h0 : e.symm a = e.symm ⟨0, by omega⟩ := congrArg e.symm (Fin.ext ha)
    show ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j (e.symm a)))
    rw [h0]
    exact hS y hy hfix'

theorem PartnerPatternBPair.of_toral_conj {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 3 ≤ m)
    {Ω : Set (Subgroup G)} {z : G} {K β : Subgroup G} (c : TCtx p f .POmegaOdd m Ω K z) {t : G}
    (ht : t * z * t⁻¹ = z) {j : Fin m → Subgroup G}
    (hjΩ : ∀ a : Fin m, a.val + 1 < m → j a ∈ Ω) (hjY : ∀ a, j a ≤ locLayer Ω z)
    (hjK : ∀ a, Commutes K (j a)) (hjperf : ∀ a, ⁅j a, j a⁆ = j a)
    (hjc : ∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b))
    (hjp : ∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hjsp : ∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m →
      ∃ W, SymplecticBlockPair (GaloisField p f) W (j a) (j b))
    (hjimg : ∀ a : Fin m, locImg Ω z (j a) =
      (rankOne (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup a).map c.d.ψ)
    (k₀ : (modelUniv .POmegaOdd m p f Fact.out).K) (v : Fin m → ZMod 2)
    (hT : ∀ γ ∈ (modelUniv .POmegaOdd m p f Fact.out).D.roots,
      (∀ x ∈ (conjSub k₀ ((modelUniv .POmegaOdd m p f Fact.out).D.rootGroup γ ⊔
          (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ,
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0)
    (hE : CharReach (modelUniv .POmegaOdd m p f Fact.out).D.cartan v
      (Pi.single (⟨0, by omega⟩ : Fin m) 1))
    (hS : ∀ y ∈ locLayer Ω z,
      (∀ b : Fin m, (∀ x ∈ locImg Ω z (conjSub y (j b)),
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ b.val ≠ 0) →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β
        (conjSub y (j ⟨0, by omega⟩))) :
    PartnerPatternBPair p f m Ω K β t := by
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaOdd m p f := ⟨Fact.out, hf1, hm, c.hp2⟩
  obtain ⟨n, H, hct, -⟩ := ModelFacts.hasBruhatDatum .POmegaOdd m p f Fact.out trivial hadm
  obtain ⟨y, hy, hfix⟩ := exists_adapted_y_of_conj_reach c.hΩ.conjInvariant c.d.ψ hct ht v k₀ hT hE
    hjimg
  have hfix' : ∀ b : Fin m, (∀ x ∈ locImg Ω z (conjSub y (j b)),
      Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ b.val ≠ 0 := fun b => by
    rw [hfix b]
    show (Pi.single (⟨0, by omega⟩ : Fin m) (1 : ZMod 2) : Fin m → ZMod 2) b = 0 ↔ b.val ≠ 0
    by_cases h : b = (⟨0, by omega⟩ : Fin m)
    · subst h
      simp
    · have : b.val ≠ 0 := fun h0 => h (Fin.ext h0)
      simp [h, this]
  refine PartnerPatternBPair.of_locAut c.hΩ c.hP1 hjΩ hjY hjK hjperf c.locLayer_le_normalizer hjc
    hjp hjsp hy ht (fun a ha x hx => (hfix' a).mpr (by omega) x hx) ?_
  intro a ha
  have h0 : a = (⟨0, by omega⟩ : Fin m) := Fin.ext ha
  rw [h0]
  exact hS y hy hfix'

end CFSG.ClassicalInvolution.RouteD
