module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.Defs
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

@[expose] def RootInvariantGeneration {G : Type*} [Group G] (N : Subgroup G) (r p : ℕ) : Prop :=
  ∀ A R : Subgroup G, A ≤ N → IsElementaryAbelian p ↥A → p ^ 2 ≤ Nat.card A → R ≤ N →
    IsPGroup r ↥R → R ≠ ⊥ → A ≤ Subgroup.normalizer (R : Set G) →
    (⨆ a ∈ A, ⨆ (_ : a ≠ 1), N ⊓ Subgroup.centralizer ({a} : Set G)) = N

theorem isElementaryAbelian_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {A : Subgroup G}
    (h : IsElemAbelian p A) : IsElementaryAbelian p ↥A :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h

theorem isElemAbelian_comap_of_injective {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    (hf : Function.Injective f) {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := by
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hf
    have h := congrArg Subtype.val ((isMulCommutative_iff.mp hE.1)
      (⟨f (a : G), a.2⟩ : E) ⟨f (b : G), b.2⟩)
    change f ((a : G) * b) = f ((b : G) * a)
    rw [map_mul, map_mul]
    exact h
  · apply hf
    rw [map_pow, map_one]
    exact hE.2 _ hx

theorem closure_commute_eq_top_of_iSup {G : Type*} [Group G] (N : Subgroup G) (E₁ : Subgroup N)
    (h : (⨆ a ∈ E₁.map N.subtype, ⨆ (_ : a ≠ 1), N ⊓ Subgroup.centralizer ({a} : Set G)) = N) :
    Subgroup.closure {k : N | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : (g : G) ∈ ⨆ a ∈ E₁.map N.subtype, ⨆ (_ : a ≠ 1),
      N ⊓ Subgroup.centralizer ({a} : Set G) := by
    rw [h]
    exact g.2
  have hle : (⨆ a ∈ E₁.map N.subtype, ⨆ (_ : a ≠ 1), N ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      (Subgroup.closure {k : N | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k}).map N.subtype := by
    refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
    obtain ⟨x, hx, rfl⟩ := ha
    have hx1 : x ≠ 1 := fun h => ha1 (by rw [h]; rfl)
    intro c hc
    obtain ⟨hcN, hcc⟩ := Subgroup.mem_inf.1 hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hcc
    exact ⟨⟨c, hcN⟩, Subgroup.subset_closure ⟨x, hx, hx1, Subtype.ext hcc⟩, rfl⟩
  obtain ⟨s, hs, hsg⟩ := hle hg
  have hsg' : s = g := Subtype.ext hsg
  rw [← hsg']
  exact hs

theorem planeGen_of_native {C G : Type*} [Group C] [Group G] {N : Subgroup G} (e : C ≃* N)
    (hZ : Subgroup.center N = ⊥) {r p : ℕ} (hgen : RootInvariantGeneration N r p)
    {E : Subgroup (MulAut C)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hin : E ≤ (MulAut.conj : C →* MulAut C).range)
    (hR : ∃ R : Subgroup C, R ≠ ⊥ ∧ IsPGroup r ↥R ∧ ∀ ε ∈ E, R.map ε.toMonoidHom = R) :
    PlaneGen E := by
  obtain ⟨R, hR1, hRp, hRn⟩ := hR
  have hconj : Function.Injective (MulAut.conj : C →* MulAut C) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hmem : e c ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro n
      obtain ⟨c', rfl⟩ := e.surjective n
      rw [← map_mul, ← map_mul]
      congr 1
      have h1 := DFunLike.congr_fun hc c'
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact e.injective (hmem.trans (map_one e).symm)
  set E₀ : Subgroup C := E.comap (MulAut.conj : C →* MulAut C) with hE₀
  have hEmap : E₀.map (MulAut.conj : C →* MulAut C) = E := Subgroup.map_comap_eq_self hin
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [← hcard, ← hEmap, Subgroup.card_map_of_injective hconj]
  have hE₀el : IsElemAbelian p E₀ := isElemAbelian_comap_of_injective _ hconj hE
  let ι : C →* G := N.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιN : ∀ c, ι c ∈ N := fun c => (e c).2
  set A : Subgroup G := E₀.map ι with hA
  set R' : Subgroup G := R.map ι with hR'
  have hAN : A ≤ N := by
    rintro _ ⟨c, -, rfl⟩
    exact hιN c
  have hR'N : R' ≤ N := by
    rintro _ ⟨c, -, rfl⟩
    exact hιN c
  have hAel : IsElementaryAbelian p ↥A :=
    isElementaryAbelian_of_isElemAbelian (elementary_abelian_map p hE₀el ι)
  have hAcard : p ^ 2 ≤ Nat.card A := by
    rw [hA, Subgroup.card_map_of_injective hι, hE₀card]
  have hR'p : IsPGroup r ↥R' :=
    hRp.of_surjective (ι.subgroupMap R) (ι.subgroupMap_surjective R)
  have hR'1 : R' ≠ ⊥ := fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective R hι).mp h)
  have hnormC : ∀ c ∈ E₀, ∀ x : C, x ∈ R ↔ c * x * c⁻¹ ∈ R := by
    intro c hc x
    have hRc : R.map (MulAut.conj c).toMonoidHom = R := hRn _ hc
    constructor
    · intro hx
      rw [← hRc]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hRc] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        have h2 : c * y * c⁻¹ = c * x * c⁻¹ := hyx
        simpa using h2
      rw [← this]
      exact hy
  have hAnorm : A ≤ Subgroup.normalizer (R' : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨c * x * c⁻¹, (hnormC c hc x).mp hx, by simp [map_mul]⟩
    · rintro ⟨y, hy, hyh⟩
      refine ⟨c⁻¹ * y * c, ?_, ?_⟩
      · have := (hnormC c⁻¹ (E₀.inv_mem hc) y).mp hy
        simpa using this
      · have h2 : ι y = ι c * h * (ι c)⁻¹ := hyh
        have h3 : h = (ι c)⁻¹ * ι y * ι c := by
          rw [h2]
          group
        rw [h3]
        simp [map_mul, map_inv]
  have hgenA := hgen A R' hAN hAel hAcard hR'N hR'p hR'1 hAnorm
  set E₁ : Subgroup N := E₀.map e.toMonoidHom with hE₁
  have hE₁A : E₁.map N.subtype = A := by
    rw [hE₁, hA, Subgroup.map_map]
  have hcl := closure_commute_eq_top_of_iSup N E₁ (by rw [hE₁A]; exact hgenA)
  have hclC : Subgroup.closure {k : C | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
    have hmapS : (Subgroup.closure {k : C | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k}).map e.toMonoidHom =
        Subgroup.closure {k : N | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k} := by
      rw [MonoidHom.map_closure]
      congr 1
      ext k'
      constructor
      · rintro ⟨k, ⟨x, hx, hx1, hkx⟩, rfl⟩
        refine ⟨e x, ⟨x, hx, rfl⟩, ?_, ?_⟩
        · intro h
          exact hx1 (e.injective (h.trans (map_one e).symm))
        · show e k * e x = e x * e k
          rw [← map_mul, ← map_mul, hkx]
      · rintro ⟨x', ⟨x, hx, rfl⟩, hx1, hkx⟩
        refine ⟨e.symm k', ⟨x, hx, ?_, ?_⟩, by simp⟩
        · intro h
          apply hx1
          rw [h, map_one]
        · apply e.injective
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
          exact hkx
    rw [hcl] at hmapS
    rw [eq_top_iff]
    intro c _
    have hec : e c ∈ (Subgroup.closure {k : C | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k}).map
        e.toMonoidHom := by
      rw [hmapS]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyc⟩ := hec
    have hyc' : y = c := e.injective hyc
    rw [← hyc']
    exact hy
  have hsub : {k : C | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k} ⊆ {k : C | ∃ ε ∈ E, ε ≠ 1 ∧ ε k = k} := by
    rintro k ⟨x, hx, hx1, hkx⟩
    refine ⟨MulAut.conj x, ?_, ?_, ?_⟩
    · rw [← hEmap]
      exact ⟨x, hx, rfl⟩
    · intro h
      exact hx1 (hconj (h.trans (map_one _).symm))
    · rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
      exact hkx.symm
  unfold PlaneGen planeClosure
  rw [eq_top_iff, ← hclC]
  exact Subgroup.closure_mono hsub

end CFSG.LieType.SeitzGeneration
