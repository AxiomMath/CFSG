module

public import CFSG.LocalAnalysis.ComponentClassification.UGSChainNormalizerSylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCCentral

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

@[expose] noncomputable def qRank (a : X) (J : Subgroup X) : ℕ :=
  pRank 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X) ⊓ coreActionKernel J)

@[expose] def LexMax (a : X) (J : Subgroup X) : Prop :=
  ∀ (a' : X) (J' E' : Subgroup X), Config a' J' E' →
    qRank a' J' < qRank a J ∨ (qRank a' J' = qRank a J ∧ twoPart a' J' ≤ twoPart a J)

theorem Config.index_eq {a : X} {J E : Subgroup X} (h : Config a J E) :
    (pPrimeCore 2 J).index = 2520 := by
  obtain ⟨e7⟩ := h.equiv
  rw [index_eq_card, Nat.card_congr e7.toEquiv, GSThmB.card_alternatingGroup_seven]

theorem wCore_map (φ : X ≃* X) (E : Subgroup X) :
    wCore (E.map φ.toMonoidHom) = (wCore E).map φ.toMonoidHom := by
  have hO : ∀ e : X, (pPrimeCore 2 (centralizer ({φ e} : Set X))).map
      (centralizer ({φ e} : Set X)).subtype = ((pPrimeCore 2 (centralizer ({e} : Set X))).map
      (centralizer ({e} : Set X)).subtype).map φ.toMonoidHom := fun e => by
    rw [UGSChain.map_map_pPrimeCore, UGSChain.map_centralizer_singleton]
  ext y
  rw [mem_map_equiv]
  simp only [wCore, mem_iInf]
  constructor
  · intro hy e he he1
    have h1 := hy (φ e) ⟨e, he, rfl⟩ fun h => he1 (φ.injective (by rw [h, map_one]))
    rw [hO, mem_map_equiv] at h1
    exact h1
  · rintro hy _ ⟨e, he, rfl⟩ he1
    have h1 := hy e he fun h => he1 (by rw [h]; exact map_one _)
    rw [show (φ.toMonoidHom e) = φ e from rfl, hO, mem_map_equiv]
    exact h1

theorem Config.conj {a : X} {J E : Subgroup X} (h : Config a J E) {g : X}
    (hg : g ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X)) :
    Config a J (conjugate E g) := by
  set φ : X ≃* X := MulAut.conj g⁻¹ with hφ
  have hga : g * a = a * g := mem_centralizer_singleton_iff.mp (mem_inf.mp hg).1
  have hJφ : J.map φ.toMonoidHom = J := conjugate_eq_of_mem_normalizer (mem_inf.mp hg).2
  have hφa : φ a = a := by
    rw [hφ, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * a * g = g⁻¹ * (a * g) := by group
      _ = g⁻¹ * (g * a) := by rw [hga]
      _ = a := by group
  have hCφ : (centralizer ({a} : Set X)).map φ.toMonoidHom = centralizer ({a} : Set X) := by
    rw [UGSChain.map_centralizer_singleton, hφa]
  obtain ⟨e4⟩ := h.four
  refine ⟨h.orderOf_eq, h.le_centralizer, h.isPComponent, h.equiv, fun y hy => ?_,
    ⟨(E.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e4⟩, ?_⟩
  · rw [mem_conjugate_iff] at hy
    have h1 := mul_mem (mul_mem (inv_mem hg) (h.le_H hy)) hg
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
  · have hW : centralizer ({a} : Set X) ⊓ wCore (conjugate E g) =
        (centralizer ({a} : Set X) ⊓ wCore E).map φ.toMonoidHom := by
      rw [Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, hCφ]
      exact congrArg _ (wCore_map φ E)
    rw [hW, ← hJφ, ← Subgroup.map_commutator, h.commutator_eq, hJφ]

variable [Finite X]

theorem Config.exists_le_sylow {a : X} {J E : Subgroup X} (h : Config a J E) {S' : Subgroup X}
    (hS' : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S'.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X))) :
    ∃ E' : Subgroup X, Config a J E' ∧ E' ≤ S' := by
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by rw [h.card_eq]; norm_num)
  obtain ⟨g, hg, hgS⟩ := exists_conjugate_le_of_sylow hS' h.le_H hE2
  exact ⟨conjugate E g, h.conj hg, hgS⟩

theorem exists_lexMax_config (h : ∃ (a : X) (J E : Subgroup X), Config a J E) :
    ∃ (a : X) (J E : Subgroup X), Config a J E ∧ LexMax a J := by
  have : Finite (Subgroup X) := Finite.of_injective (fun H : Subgroup X => (H : Set X))
    SetLike.coe_injective
  set s : Set (X × Subgroup X × Subgroup X) := {p | Config p.1 p.2.1 p.2.2} with hs
  obtain ⟨a₀, J₀, E₀, h₀⟩ := h
  obtain ⟨⟨a, J, E⟩, hp, hmax⟩ := Set.exists_max_image s
    (fun p => toLex (qRank p.1 p.2.1, twoPart p.1 p.2.1)) (Set.toFinite s) ⟨(a₀, J₀, E₀), h₀⟩
  refine ⟨a, J, E, hp, fun a' J' E' h' => ?_⟩
  exact Prod.Lex.toLex_le_toLex.mp (hmax (a', J', E') h')

theorem centralLex (hSol : GrSLit.SolomonCommutingCoreInput) {a : X} {J E : Subgroup X}
    (h : Config a J E) (hmax : LexMax a J)
    {S : Subgroup X} (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (hES : E ≤ S) (b : X) (K : Subgroup X) (hb : orderOf b = 2)
    (hbJ : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    (hK : UnbalancedGS.GSIsoCorr a J b K) (hbc : ∀ s ∈ S, s * b = b * s) :
    S ≤ centralizer ({b} : Set X) ⊓ normalizer (K : Set X) ∧
      ∃ P : Sylow 2 ↥(centralizer ({b} : Set X) ⊓ normalizer (K : Set X)),
        (P : Subgroup _) = S.subgroupOf (centralizer ({b} : Set X) ⊓ normalizer (K : Set X)) := by
  have hSb : S ≤ centralizer ({b} : Set X) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hbc s hs)
  obtain ⟨-, -, -, -, -, -, -, -, hS⟩ := isomorphic_correspondence_sylow_growth hK rfl rfl rfl rfl
  obtain ⟨hSHL, hrk, -, hlt, -⟩ := hS S hSH hSsyl hSb
  have hc := config_of_isoCorr hSol h hb hbJ (fun e he => hbc e (hES he)) hK
  rcases hmax b K E hc with hlt' | ⟨-, hle⟩
  · exact absurd hrk (not_le.mpr hlt')
  · refine ⟨hSHL, ?_⟩
    by_contra hns
    exact absurd (hlt hns) (not_lt.mpr hle)

end CFSG.ComponentClassification.GSThmB.CorC
