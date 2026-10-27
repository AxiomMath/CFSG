module

public import CFSG.LieType.SpecialLinear.TwoEnd.Fix
public import CFSG.LieType.SpecialLinear.EndNode.CoverType

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Quasithin.SmithCurtis

variable {Ĝ G : Type*} [Group Ĝ] [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*}
  [Group W] {cs : CoxeterSystem M W} {p : ℕ} [Finite Ĝ] [Fact p.Prime]
  {D : CurtisDatum G cs p} {π : Ĝ →* G} {C : CentralCoverData D π p}
  {F : B → Type} [∀ s, Field (F s)] {R : CoverRankOne C F} [Fintype B]

variable {k V V' : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V']

omit [Fintype B] in
theorem heckeT_linearEquiv {ρ : Representation k Ĝ V} {ρ' : Representation k Ĝ V'}
    (e : V ≃ₗ[k] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (s : B) (v : V) :
    e (C.datum.heckeT ρ s v) = C.datum.heckeT ρ' s (e v) := by
  let := Fintype.ofFinite (C.datum.X s)
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply, map_sum]
  exact Finset.sum_congr rfl fun x _ => he ((x : Ĝ) * C.datum.n s) v

omit [Fintype B] in
theorem IsCoverType.of_linearEquiv {ρ : Representation k Ĝ V} {ρ' : Representation k Ĝ V'}
    (e : V ≃ₗ[k] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    {y : V} {χ : Ĝ → k} {J : Finset B} (ht : IsCoverType R ρ y χ J) :
    IsCoverType R ρ' (e y) χ J := by
  obtain ⟨hyU, hy0, hchi, hJ⟩ := ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [CurtisDatum.mem_fixU] at hyU ⊢
    intro u hu
    rw [← he u y, hyU u hu]
  · intro h
    exact hy0 (e.map_eq_zero_iff.mp h)
  · intro h hh
    rw [← he h y, hchi h hh, map_smul]
  · intro s
    rw [hJ s]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← heckeT_linearEquiv e he s y, h2, map_zero]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, e.injective ?_⟩
      rw [heckeT_linearEquiv e he s y, h2, map_zero]

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

namespace CFSG.Quasithin.SmithCurtis

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

theorem IsSimpleRep.of_linearEquiv {ρ : Representation k G V} {ρ' : Representation k G W}
    (e : V ≃ₗ[k] W) (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (hρ : IsSimpleRep ρ) :
    IsSimpleRep ρ' := by
  obtain ⟨hnt, hsimple⟩ := hρ
  refine ⟨?_, fun W' hW' => ?_⟩
  · obtain ⟨⟨x, y, hxy⟩⟩ := hnt
    exact ⟨⟨e x, e y, fun h => hxy (e.injective h)⟩⟩
  · let W₀ : Submodule k V := W'.comap (e : V →ₗ[k] W)
    have hstable : ∀ g : G, ∀ w ∈ W₀, ρ g w ∈ W₀ := by
      intro g w hw
      rw [Submodule.mem_comap] at hw ⊢
      have h := hW' g (e w) hw
      simpa [he g w] using h
    rcases hsimple W₀ hstable with hbot | htop
    · left
      refine eq_bot_iff.mpr fun w hw => ?_
      have hmem : e.symm w ∈ W₀ := by
        rw [Submodule.mem_comap]
        simpa using hw
      rw [hbot, Submodule.mem_bot] at hmem
      rw [Submodule.mem_bot]
      calc w = e (e.symm w) := (e.apply_symm_apply w).symm
        _ = e 0 := by rw [hmem]
        _ = 0 := map_zero e
    · right
      refine eq_top_iff.mpr fun w _ => ?_
      have hmem : e.symm w ∈ W₀ := by
        rw [htop]
        exact Submodule.mem_top
      rw [Submodule.mem_comap] at hmem
      simpa using hmem

end CFSG.Quasithin.SmithCurtis

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

variable (m : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

theorem mem_twoEndFix_of_isCoverType {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m+3)) F) V) {y : V}
    {χ : SpecialLinearGroup (Fin (m+3)) F → k} {J : Finset (Fin (m+2))}
    (ht : IsCoverType (rankOne (m+2) F p) ρ y χ J) :
    y ∈ twoEndFix m F ρ := by
  rw [twoEndFix_eq_firstLast]
  refine Submodule.mem_map.mpr
    ⟨⟨y, mem_firstRowFix_of_isCoverType (m := m+1) (F := F) (p := p) ht⟩, ?_, rfl⟩
  exact mem_lastColFix_of_isCoverType (m := m) (F := F) (p := p)
    (firstNodeRestrict_isCoverType (m := m+1) (F := F) (p := p) ht)

theorem twoEndRestrict_isCoverType {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m+3)) F) V) {y : V}
    {χ : SpecialLinearGroup (Fin (m+3)) F → k} {J : Finset (Fin (m+2))}
    (ht : IsCoverType (rankOne (m+2) F p) ρ y χ J) :
    IsCoverType (rankOne m F p) (twoEndRestrict m F ρ)
      ⟨y, mem_twoEndFix_of_isCoverType (m := m) (F := F) (p := p) ρ ht⟩
      (χ ∘ embedMid m F)
      (Finset.univ.filter fun s : Fin m => s.castSucc.succ ∈ J) := by
  have ht1 := firstNodeRestrict_isCoverType (m := m+1) (F := F) (p := p) ht
  have ht2 := lastNodeRestrict_isCoverType (m := m) (F := F) (p := p) ht1
  have h := IsCoverType.of_linearEquiv
    (R := rankOne m F p) (twoEndEquivFirstLast m F ρ)
    (fun g v => twoEndEquivFirstLast_intertwine m F ρ g v) ht2
  convert h using 2
  · rfl
  · funext s
    rfl
  · simp

theorem twoEndRestrict_isSimple {k : Type} {V : Type} [Field k] [CharP k p]
    [AddCommGroup V] [Module k V] [Algebra F k]
    (ρ : Representation k (SpecialLinearGroup (Fin (m+3)) F) V) (hρ : IsSimpleRep ρ)
    {y : V} {χ : SpecialLinearGroup (Fin (m+3)) F → k} {J : Finset (Fin (m+2))}
    (ht : IsCoverType (rankOne (m+2) F p) ρ y χ J) :
    IsSimpleRep (twoEndRestrict m F ρ) := by
  have ht1 := firstNodeRestrict_isCoverType (m := m+1) (F := F) (p := p) ht
  have h1 : IsSimpleRep (firstNodeRestrict (m+1) F ρ) :=
    firstNodeRestrict_isSimple_of_isCoverType (m := m+1) (F := F) (p := p)
      (k := k) hρ (by simpa using splitOver (m+2) F p k) ht
  have h2 : IsSimpleRep (lastNodeRestrict m F (firstNodeRestrict (m+1) F ρ)) :=
    lastNodeRestrict_isSimple_of_isCoverType (m := m) (F := F) (p := p)
      (k := k) h1 (by simpa using splitOver (m+1) F p k) ht1
  exact IsSimpleRep.of_linearEquiv (twoEndEquivFirstLast m F ρ)
    (fun g v => twoEndEquivFirstLast_intertwine m F ρ g v) h2

end CFSG.LieType.SpecialLinear
