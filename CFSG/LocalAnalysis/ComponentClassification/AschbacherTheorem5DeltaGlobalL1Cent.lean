module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalL1Comp
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightBenderCase
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixLift
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuasi

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.SignalizerFunctor.Helpers
open CFSG.ComponentClassification.AschbacherTheorem3
open scoped commutatorElement

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

variable {X : Type} [Group X]

theorem le_normalizer_of_iSup {m : ℕ} {K : Fin m → Subgroup X}
    (hKcomm : ∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', x * y = y * x) (l : Fin m) :
    ⨆ l', K l' ≤ Subgroup.normalizer (K l : Set X) := by
  refine iSup_le fun l' => ?_
  by_cases hll : l' = l
  · rw [hll]
    exact Subgroup.le_normalizer
  · intro y hy
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    exact hKcomm l l' (Ne.symm hll) x hx y hy

omit [Group X] in
theorem not_comm_of_component {X : Type} [Group X] {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) : False := by
  apply SectionSix.component_ne_bot hK
  have hc : commutator K = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    exact Subgroup.mem_centralizer_iff.mpr fun y _ => Subtype.ext (hab y y.2 x x.2)
  rw [hK.2.2.1] at hc
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : K) ∈ (⊥ : Subgroup K) := hc ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)

variable [Finite X]

theorem eq_one_of_mem_bender {B : Subgroup X} {n : ℕ} (hB : IsBenderType B n) {z : X}
    (hz : z ∈ B) (hzc : ∀ b ∈ B, z * b = b * z) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hB.isSimpleGroup
  obtain ⟨k, -, hBB, -⟩ := FourEight.exists_benderBorel hB
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 B))
  have hne := (hBB Q).1.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center B) with h | h
  · have hmem : (⟨z, hz⟩ : B) ∈ Subgroup.center B :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2).symm
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    apply hne
    rw [Subgroup.normalizer_eq_top_iff]
    refine ⟨fun x hx g => ?_⟩
    have hg : g ∈ Subgroup.center B := h ▸ Subgroup.mem_top g
    have h1 := Subgroup.mem_center_iff.mp hg x
    rw [← h1]
    simpa using hx

omit [Finite X] in
theorem centralizes_of_normal {G T W : Subgroup X} {m : ℕ} {K : Fin m → Subgroup X}
    (hK : ∀ l, IsComponentOf (K l) ⊤)
    (hKcomm : ∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', x * y = y * x) (hgen : ⨆ l, K l = G)
    (hF : Frame G T) (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hTW : T ≤ W)
    (hGW : G ≤ Subgroup.normalizer (W : Set X)) : ∀ t ∈ T, ∀ g ∈ G, t * g = g * t := by
  set M := ⁅T, G⁆ with hMdef
  have hMW : M ≤ W := Subgroup.commutator_le.mpr fun t ht g hg => by
    rw [commutatorElement_def]
    have h1 : g * t⁻¹ * g⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hGW hg) t⁻¹).mp (W.inv_mem (hTW ht))
    have e : t * g * t⁻¹ * g⁻¹ = t * (g * t⁻¹ * g⁻¹) := by group
    rw [e]
    exact W.mul_mem (hTW ht) h1
  have hMab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := fun x hx y hy => hWab x (hMW hx) y (hMW hy)
  have hMN : G ⊔ T ≤ Subgroup.normalizer (M : Set X) := FourEight.sup_le_normalizer_commutator hF
  have hMG : M ≤ G := by
    rw [hMdef, Subgroup.commutator_comm]
    exact hF.commutator_le
  have hKG : ∀ l, K l ≤ G := fun l => hgen ▸ le_iSup K l
  have hGK : ∀ l, G ≤ Subgroup.normalizer (K l : Set X) := fun l =>
    hgen ▸ le_normalizer_of_iSup hKcomm l
  have hcent : ∀ l, ∀ t ∈ T, ∀ k ∈ K l, k * t = t * k := by
    intro l t ht
    rcases component_le_or_commute (hK l) ((hKG l).trans (le_sup_left.trans hMN))
        (hMG.trans (hGK l)) with hle | hcomm
    · exact (not_comm_of_component (hK l) fun x hx y hy => hMab x (hle hx) y (hle hy)).elim
    · refine comm_of_comm_mem (hK l) hMab hcomm fun k hk => ?_
      have h1 : ⁅k⁻¹, t⁻¹⁆ ∈ ⁅G, T⁆ :=
        Subgroup.commutator_mem_commutator (G.inv_mem (hKG l hk)) (T.inv_mem ht)
      rw [commutatorElement_def, inv_inv, inv_inv, Subgroup.commutator_comm] at h1
      exact h1
  intro t ht g hg
  have hle : G ≤ Subgroup.centralizer ({t} : Set X) := by
    rw [← hgen]
    refine iSup_le fun l k hk => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcent l t ht k hk
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm

theorem centralizes_sylow_of_bender {G T S : Subgroup X} {m : ℕ} {K : Fin m → Subgroup X}
    (hK : ∀ l, IsComponentOf (K l) ⊤)
    (hKcomm : ∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', x * y = y * x) (hgen : ⨆ l, K l = G)
    (h : SylowFrame G T S) (hT2 : ∀ t ∈ T, t ^ 2 = 1) {n : ℕ}
    (hdec : conjugateClosure G T = pCoreOf 2 (conjugateClosure G T) ⊔ ⁅T, G⁆)
    (hcommEB : ⁅pCoreOf 2 (conjugateClosure G T), ⁅T, G⁆⁆ = ⊥)
    (hel : IsElemAbelian 2 (pCoreOf 2 (conjugateClosure G T)))
    (hB : IsBenderType ⁅T, G⁆ n) : ∀ t ∈ T, ∀ s ∈ S ⊓ G, t * s = s * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := h.toFrame
  set B := ⁅T, G⁆ with hBdef
  set Kc := conjugateClosure G T with hKcdef
  set E := pCoreOf 2 Kc with hEdef
  have hBN : G ⊔ T ≤ Subgroup.normalizer (B : Set X) := FourEight.sup_le_normalizer_commutator hF
  have hBG : B ≤ G := by
    rw [hBdef, Subgroup.commutator_comm]
    exact hF.commutator_le
  have hKG : ∀ l, K l ≤ G := fun l => hgen ▸ le_iSup K l
  have hGK : ∀ l, G ≤ Subgroup.normalizer (K l : Set X) := fun l =>
    hgen ▸ le_normalizer_of_iSup hKcomm l
  have hZ : ∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → z = 1 := fun z hz hzc =>
    eq_one_of_mem_bender hB hz hzc
  have hdich : ∀ l, K l ≤ B ∨ ∀ x ∈ K l, ∀ y ∈ B, x * y = y * x := fun l =>
    component_le_or_commute (hK l) ((hKG l).trans (le_sup_left.trans hBN)) (hBG.trans (hGK l))
  have hTK : ∀ l, (∀ x ∈ K l, ∀ y ∈ B, x * y = y * x) → ∀ t ∈ T, ∀ k ∈ K l, k * t = t * k := by
    intro l hl t ht
    refine comm_of_comm_mem_simple hZ hl (hBN (Subgroup.mem_sup_right ht)) fun k hk => ?_
    have h1 : ⁅k⁻¹, t⁻¹⁆ ∈ ⁅G, T⁆ :=
      Subgroup.commutator_mem_commutator (G.inv_mem (hKG l hk)) (T.inv_mem ht)
    rw [commutatorElement_def, inv_inv, inv_inv, Subgroup.commutator_comm] at h1
    exact h1
  set C := ⨆ l, ⨆ (_ : ∀ x ∈ K l, ∀ y ∈ B, x * y = y * x), K l with hCdef
  have hCB : C ≤ Subgroup.centralizer (B : Set X) := iSup_le fun l => iSup_le fun hl x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hl x hx y hy).symm
  have hCT : C ≤ Subgroup.centralizer (T : Set X) := iSup_le fun l => iSup_le fun hl x hx =>
    Subgroup.mem_centralizer_iff.mpr fun t ht => (hTK l hl t ht x hx).symm
  have hCG : C ≤ G := iSup_le fun l => iSup_le fun _ => hKG l
  have hcommBC : ∀ x ∈ B, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hCB hy) x hx
  have hBC : B ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxB, hxC⟩
    exact Subgroup.mem_bot.mpr (hZ x hxB fun b hb => (hcommBC b hb x hxC).symm)
  have hGBC : B ⊔ C = G := by
    refine le_antisymm (sup_le hBG hCG) ?_
    rw [← hgen]
    refine iSup_le fun l => ?_
    rcases hdich l with hle | hl
    · exact hle.trans le_sup_left
    · exact (show K l ≤ C from le_iSup_of_le l (le_iSup_of_le hl le_rfl)).trans le_sup_right
  have hPB : IsSylowOf 2 (S ⊓ B) B := h.sylow.inf_of_le_normalizer (hBG.trans le_sup_left) hBN
  have hCN : G ⊔ T ≤ Subgroup.normalizer (C : Set X) := by
    refine sup_le ?_ ((Subgroup.le_centralizer_iff.mp hCT).trans
      (Subgroup.centralizer_le_normalizer _))
    rw [← hGBC]
    exact sup_le ((Subgroup.le_centralizer_iff.mp hCB).trans
      (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hSC : IsSylowOf 2 (S ⊓ C) C := h.sylow.inf_of_le_normalizer (hCG.trans le_sup_left) hCN
  have hsyl := isSylowOf_sup_of_commute hPB hSC hBC hcommBC
  rw [hGBC] at hsyl
  have hSG : IsSylowOf 2 (S ⊓ G) G :=
    h.sylow.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hF.le_normalizer)
  have heq : S ⊓ G = (S ⊓ B) ⊔ (S ⊓ C) :=
    hsyl.eq_of_le (sup_le (inf_le_inf_left S hBG) (inf_le_inf_left S hCG)) inf_le_right
      hSG.isPGroup
  have hEC : E ≤ Subgroup.centralizer (B : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommEB
  have hE2 : IsPGroup 2 E := LieType.BorelTits.pCoreOf_isPGroup 2 Kc
  have hKcGT : Kc ≤ G ⊔ T := by
    rw [hKcdef, FourEight.conjugateClosure_eq]
    exact sup_le le_sup_right (hBG.trans le_sup_left)
  have hEN : G ⊔ T ≤ Subgroup.normalizer (E : Set X) :=
    (FourEight.sup_le_normalizer_conjugateClosure hF).trans
      (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Kc)
  have hES : E ≤ S := FourEight.le_of_isSylowOf_of_normal h.sylow hE2
    ((LieType.BorelTits.pCoreOf_le 2 Kc).trans hKcGT) hEN
  have hTPB : ∀ t ∈ T, ∀ p ∈ S ⊓ B, t * p = p * t := by
    intro t ht p hp
    have htK : t ∈ E ⊔ B := hdec ▸ FourEight.le_conjugateClosure G T ht
    obtain ⟨e, he, ℓ, hℓ, rfl, hcm⟩ := FourEight.mem_sup_iff_of_le_centralizer hEC htK
    have hℓS : ℓ ∈ S := by
      have h1 := S.mul_mem (S.inv_mem (hES he)) (h.le ht)
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1
    have hℓ2 : ℓ ^ 2 = 1 := by
      have h1 := hT2 _ ht
      have h2 : (e * ℓ) ^ 2 = e ^ 2 * ℓ ^ 2 := Commute.mul_pow hcm 2
      rw [h2, hel.2 e he, one_mul] at h1
      exact h1
    have hℓp := (FourEight.bender_sylow hB hPB).1 ℓ ⟨hℓS, hℓ⟩ hℓ2 p hp
    have hep : e * p = p * e := (Subgroup.mem_centralizer_iff.mp (hEC he) p hp.2).symm
    calc e * ℓ * p = e * (ℓ * p) := by group
      _ = e * (p * ℓ) := by rw [hℓp]
      _ = (e * p) * ℓ := by group
      _ = (p * e) * ℓ := by rw [hep]
      _ = p * (e * ℓ) := by group
  intro t ht s hs
  rw [heq] at hs
  have hle : (S ⊓ B) ⊔ (S ⊓ C) ≤ Subgroup.centralizer ({t} : Set X) := sup_le
    (fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr (hTPB t ht p hp).symm)
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hCT hc.2) t ht).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hs)).symm

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
