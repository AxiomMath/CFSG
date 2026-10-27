
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocalCertInputs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Subgroup
open scoped Pointwise

structure LocalParts : Prop where
  quat : quatOK = true
  syl : sylWitOK = true

noncomputable abbrev qt₁ : Equiv.Perm (Fin 42) := wordPerm (tg 35)

noncomputable abbrev qt₂ : Equiv.Perm (Fin 42) := wordPerm (tg 38)

noncomputable abbrev qc : Equiv.Perm (Fin 42) := wordPerm (tg 4)

theorem tabRep_tgT (k : ℕ) : TabRep (tgT k) (wordPerm (tg k)) := tabRep_wordTab _

theorem tabRep_rep_inv {k : ℕ} (hk : k < wReps.length) :
    TabRep (invTab 42 (wordTab (wReps.getD k []))) (wordPerm (wReps.getD k []))⁻¹ := by
  have hk' : k < (wordTabs wReps).size := by rw [size_wordTabs]; exact hk
  have hrep := tabRep_wordTabs wReps hk
  rw [← List.getD_eq_getElem _ [] hk] at hrep
  have h := invsOK_spec parabolicParts.invs hk' hrep
  have he : ((wordTabs wReps).map (invTab 42))[k]! = invTab 42 (wordTab (wReps.getD k [])) := by
    rw [getElem!_pos _ k (by simpa using hk'), Array.getElem_map,
      ← getElem!_pos (wordTabs wReps) k hk', wordTabs_getElem! wReps hk,
      List.getD_eq_getElem _ [] hk]
  rwa [he] at h

theorem tabRep_invTab_of_invOK {x : Tab} {g : Equiv.Perm (Fin 42)} (h : invOK x = true)
    (hx : TabRep x g) : TabRep (invTab 42 x) g⁻¹ := by
  simp only [invOK, Bool.and_eq_true, beq_iff_eq] at h
  exact hx.inv h.1 h.2

theorem tabRep_r4Conj {k : ℕ} (hk : k < wReps.length) :
    TabRep (r4Conj (wordTab (wReps.getD k [])))
      ((wordPerm (wReps.getD k []))⁻¹ * r₄ * wordPerm (wReps.getD k [])) := by
  have hy : TabRep (wordTab (wReps.getD k [])) ((wordPerm (wReps.getD k []))⁻¹)⁻¹ := by
    rw [_root_.inv_inv]
    exact tabRep_wordTab _
  have h := (tabRep_rep_inv hk).conjTab tabRep_r₄ hy
  rw [_root_.inv_inv] at h
  exact h

theorem conj_normalizes_aux {G : Type*} [Group G] {T : Subgroup G} {y b r : G}
    (hbN : b ∈ normalizer (T : Set G))
    (hr : ∀ t ∈ T, (y * b)⁻¹ * (r * (y * b * t * (y * b)⁻¹) * r⁻¹) * (y * b) ∈ T) :
    ∀ t ∈ T, y⁻¹ * r * y * t * (y⁻¹ * r * y)⁻¹ ∈ T := by
  intro t ht
  have h1 := hr _ ((mem_normalizer_iff''.mp hbN t).mp ht)
  refine (mem_normalizer_iff''.mp hbN _).mpr ?_
  have e : b⁻¹ * (y⁻¹ * r * y * t * (y⁻¹ * r * y)⁻¹) * b =
      (y * b)⁻¹ * (r * (y * b * (b⁻¹ * t * b) * (y * b)⁻¹) * r⁻¹) * (y * b) := by group
  rw [e]
  exact h1

theorem conj_iff_aux {G : Type*} [Group G] {T : Subgroup G} {c y b : G}
    (hd : c⁻¹ * y * b ∈ normalizer (T : Set G)) (t : G) :
    (y * b)⁻¹ * t * (y * b) ∈ T ↔ c⁻¹ * t * c ∈ T := by
  rw [mem_normalizer_iff''.mp hd (c⁻¹ * t * c)]
  have e : (c⁻¹ * y * b)⁻¹ * (c⁻¹ * t * c) * (c⁻¹ * y * b) = (y * b)⁻¹ * t * (y * b) := by group
  rw [e]

end CFSG.ComponentClassification.GrSLit.L34Facts
