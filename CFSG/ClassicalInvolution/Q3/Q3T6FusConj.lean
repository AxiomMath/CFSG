module

public import CFSG.ClassicalInvolution.Q3.Q3T6FusAct
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen610
public import CFSG.ClassicalInvolution.AschTight.Sec7L76C

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

section Conj

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem abelian_of_mem_WSet3 (hΩg : HypOmegaGen (CoreAssembly.conjClass K)) {W : Subgroup G}
    (hW : W ∈ WSet (CoreAssembly.conjClass K)) : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  obtain ⟨η, ⟨S, hS, hinv⟩, hWη⟩ := hW
  rw [hWη]
  exact (Sec6Gen.eta_abelian_of_cyc66 hΩg (Sec6Gen.cyc66 hΩg) hS hinv).1

theorem le_normalizer_of_mem_WSet3 (hΩg : HypOmegaGen (CoreAssembly.conjClass K))
    {W : Subgroup G} (hW : W ∈ WSet (CoreAssembly.conjClass K)) {S₁ : Sylow 2 G}
    (hWS : W ≤ (S₁ : Subgroup G)) {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K))
    (hRS : R ≤ (S₁ : Subgroup G)) : R ≤ Subgroup.normalizer (W : Set G) := by
  obtain ⟨η, hη, hWη⟩ := hW
  have hηS : ∀ U ∈ η, U ≤ (S₁ : Subgroup G) := fun U hU =>
    ((hWη ▸ le_iSup₂_of_le (f := fun U' (_ : U' ∈ η) => U') U hU le_rfl : U ≤ W).trans hWS)
  have h610 := (Sec6Gen.l6_10Gen G _ hΩg S₁ η hη hηS).1
  intro x hx
  rw [mem_normalizer_iff_conjSub_eq, hWη]
  exact Sec7.conjSub_iSup_eq_of_forall_mem (h610 R hR hRS x hx)

theorem exists_conj_eq_t_of_subgroup3 (hΩg : HypOmegaGen (CoreAssembly.conjClass K))
    (hDE : DEdgeless (CoreAssembly.conjClass K)) (hI : IsUniqueInvolution K z)
    (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G))
    {S : Sylow 2 G} {W L : Subgroup G} {t : G} (hW : W ∈ WSet (CoreAssembly.conjClass K))
    (hWS : W ≤ (S : Subgroup G)) (hzW : z ∈ W) (hRK : IsSylow2In ((S : Subgroup G) ⊓ K) K)
    (hL : L ∈ CoreAssembly.conjClass K) (hLt : IsUniqueInvolution L t) (htW : t ∈ W)
    (hzt : t ≠ z) {B : Subgroup G} (hBS : B ≤ (S : Subgroup G))
    (hBR : B ≤ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (hBW : B ≤ Subgroup.centralizer (W : Set G)) (hBL : B ≤ centralizerModOdd ⊤ L) :
    ∃ g : G, (∀ b ∈ B, g * b = b * g) ∧ g * z * g⁻¹ = t := by
  have hWab := abelian_of_mem_WSet3 hΩg hW
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le hWS
  obtain ⟨a, haL⟩ := hL
  subst haL
  have hta : t = a * z * a⁻¹ := ((hI.conj a).eq hLt).symm
  have hKa : conjSub a K ≠ conjSub 1 K := by
    rw [conjSub_one]
    intro h
    apply hzt
    have hmem := (hI.conj a).mem
    rw [h] at hmem
    rw [hta]
    exact (hI.unique _ hmem (hI.conj a).sq).resolve_left (hI.conj a).ne_one
  have htz : t * z = z * t := (hWab t htW z hzW)
  have htN : t ∈ Subgroup.normalizer (K : Set G) :=
    hN (Subgroup.mem_centralizer_singleton_iff.mpr htz)
  have hzN : z ∈ Subgroup.normalizer ((conjSub a K : Subgroup G) : Set G) := by
    refine centralizer_le_normalizer_conj hN a ?_
    rw [← hta, Subgroup.mem_centralizer_singleton_iff]
    exact htz.symm
  have hWN : W ≤ Subgroup.normalizer ((conjSub a K : Subgroup G) : Set G) := by
    intro w hw
    refine centralizer_le_normalizer_conj hN a ?_
    rw [← hta, Subgroup.mem_centralizer_singleton_iff]
    exact hWab w hw t htW
  have hBN : B ≤ Subgroup.normalizer ((conjSub a K : Subgroup G) : Set G) := by
    intro b hb
    refine centralizer_le_normalizer_conj hN a ?_
    rw [← hta, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hBW hb) t htW).symm
  have hRset : (S : Subgroup G) ⊓ K ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) hRK
  have hRN : (S : Subgroup G) ⊓ K ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_of_mem_WSet3 hΩg hW hWS hRset inf_le_left
  have hquatR := Sec6Gen.isQuatSub_of_mem_RSet hΩg hRset
  obtain ⟨r, hrR, hrt⟩ : ∃ r ∈ (S : Subgroup G) ⊓ K, r * t * r⁻¹ ≠ t := by
    by_contra hcon
    push Not at hcon
    refine false_of_le_inf_centralizer3 hΩg hDE hI hN hKa hRK.2.1 hquatR.exists_not_commute
      (by have := hquatR.eight_le; omega) (by rw [conjSub_one]; exact hRK.1) ?_
    intro r hr
    rw [← hta, Subgroup.mem_centralizer_singleton_iff]
    calc r * t = r * t * r⁻¹ * r := by group
      _ = t * r := by rw [hcon r hr]
  have hT2 : IsPGroup 2 ↥(B ⊔ W) := S.isPGroup'.to_le (sup_le hBS hWS)
  have hTL : B ⊔ W ≤ Subgroup.normalizer ((conjSub a K : Subgroup G) : Set G) :=
    sup_le hBN hWN
  obtain ⟨RL, hRL, hTRL⟩ := Asc77.exists_sylow_normalized hT2 hTL
  have hTRL' : B ⊔ W ≤ Subgroup.normalizer (RL : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hTRL w hw)
  have hWRL : W ≤ Subgroup.normalizer (RL : Set G) := le_sup_right.trans hTRL'
  have hP : IsPGroup 2 ↥(W ⊔ RL) := IsPGroup.to_sup_of_normal_right' hW2 hRL.2.1 hWRL
  obtain ⟨S₁, hS₁⟩ := hP.exists_le_sylow
  have hRLset : RL ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In ⟨a, rfl⟩ hRL
  have hRLN : RL ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_of_mem_WSet3 hΩg hW (le_sup_left.trans hS₁) hRLset (le_sup_right.trans hS₁)
  have hquatL := Sec6Gen.isQuatSub_of_mem_RSet hΩg hRLset
  obtain ⟨rL, hrLR, hrLz⟩ : ∃ rL ∈ RL, rL * z * rL⁻¹ ≠ z := by
    by_contra hcon
    push Not at hcon
    refine false_of_le_inf_centralizer3 hΩg hDE hI hN (a := 1) (b := a)
      hKa.symm hRL.2.1 hquatL.exists_not_commute
      (by have := hquatL.eight_le; omega) hRL.1 ?_
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [one_mul, inv_one, mul_one]
    calc r * z = r * z * r⁻¹ * r := by group
      _ = z * r := by rw [hcon r hr]
  have hrK : r ∈ K := hrR.2
  have hrz : r * z * r⁻¹ = z := by
    have hmem : r * z * r⁻¹ ∈ K := K.mul_mem (K.mul_mem hrK hI.mem) (K.inv_mem hrK)
    have hsq : r * z * r⁻¹ * (r * z * r⁻¹) = 1 := by
      calc r * z * r⁻¹ * (r * z * r⁻¹) = r * (z * z) * r⁻¹ := by group
        _ = 1 := by rw [hI.sq]; group
    rcases hI.unique _ hmem hsq with h | h
    · exfalso
      apply hI.ne_one
      calc z = r⁻¹ * (r * z * r⁻¹) * r := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hrt' : r * t * r⁻¹ = t * z := by
    have hrW : r * t * r⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hRN hrR) t).mp htW
    have hcomm : r * t * r⁻¹ * t = t * (r * t * r⁻¹) := hWab _ hrW t htW
    have hu : r * t * r⁻¹ * t⁻¹ ∈ K := by
      have h1 : t * r⁻¹ * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htN r⁻¹).mp (K.inv_mem hrK)
      have h2 : r * (t * r⁻¹ * t⁻¹) ∈ K := K.mul_mem hrK h1
      have e : r * t * r⁻¹ * t⁻¹ = r * (t * r⁻¹ * t⁻¹) := by group
      rwa [e]
    have ht2 : t * t = 1 := hLt.sq
    have hsq : r * t * r⁻¹ * t⁻¹ * (r * t * r⁻¹ * t⁻¹) = 1 := by
      have e1 : r * t * r⁻¹ * t⁻¹ * (r * t * r⁻¹ * t⁻¹) =
          (r * t * r⁻¹) * t⁻¹ * (r * t * r⁻¹) * t⁻¹ := by group
      have e2 : (r * t * r⁻¹) * t⁻¹ * (r * t * r⁻¹) = (r * t * r⁻¹) * (r * t * r⁻¹) * t⁻¹ := by
        have : t⁻¹ * (r * t * r⁻¹) = (r * t * r⁻¹) * t⁻¹ := by
          calc t⁻¹ * (r * t * r⁻¹) = t⁻¹ * (r * t * r⁻¹) * t * t⁻¹ := by group
            _ = t⁻¹ * (t * (r * t * r⁻¹)) * t⁻¹ := by rw [← hcomm]; group
            _ = (r * t * r⁻¹) * t⁻¹ := by group
        calc (r * t * r⁻¹) * t⁻¹ * (r * t * r⁻¹)
            = (r * t * r⁻¹) * (t⁻¹ * (r * t * r⁻¹)) := by group
          _ = (r * t * r⁻¹) * ((r * t * r⁻¹) * t⁻¹) := by rw [this]
          _ = (r * t * r⁻¹) * (r * t * r⁻¹) * t⁻¹ := by group
      have h3 : (r * t * r⁻¹) * (r * t * r⁻¹) = 1 := by
        calc (r * t * r⁻¹) * (r * t * r⁻¹) = r * (t * t) * r⁻¹ := by group
          _ = 1 := by rw [ht2]; group
      rw [e1, e2, h3, one_mul]
      calc t⁻¹ * t⁻¹ = (t * t)⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    rcases hI.unique _ hu hsq with h | h
    · exfalso
      apply hrt
      calc r * t * r⁻¹ = (r * t * r⁻¹ * t⁻¹) * t := by group
        _ = t := by rw [h]; group
    · calc r * t * r⁻¹ = (r * t * r⁻¹ * t⁻¹) * t := by group
        _ = z * t := by rw [h]
        _ = t * z := htz.symm
  have hrLt : rL * t * rL⁻¹ = t := by
    have hrLL : rL ∈ conjSub a K := hRL.1 hrLR
    have hmem : rL * t * rL⁻¹ ∈ conjSub a K :=
      (conjSub a K).mul_mem ((conjSub a K).mul_mem hrLL hLt.mem) ((conjSub a K).inv_mem hrLL)
    have hsq : rL * t * rL⁻¹ * (rL * t * rL⁻¹) = 1 := by
      calc rL * t * rL⁻¹ * (rL * t * rL⁻¹) = rL * (t * t) * rL⁻¹ := by group
        _ = 1 := by rw [hLt.sq]; group
    rcases hLt.unique _ hmem hsq with h | h
    · exfalso
      apply hLt.ne_one
      calc t = rL⁻¹ * (rL * t * rL⁻¹) * rL := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hrLz' : rL * z * rL⁻¹ = t * z := by
    have hrLL : rL ∈ conjSub a K := hRL.1 hrLR
    have hrW : rL * z * rL⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hRLN hrLR) z).mp hzW
    have hcomm : rL * z * rL⁻¹ * z = z * (rL * z * rL⁻¹) := hWab _ hrW z hzW
    have hu : rL * z * rL⁻¹ * z⁻¹ ∈ conjSub a K := by
      have h1 : z * rL⁻¹ * z⁻¹ ∈ conjSub a K :=
        (Subgroup.mem_normalizer_iff.mp hzN rL⁻¹).mp ((conjSub a K).inv_mem hrLL)
      have h2 : rL * (z * rL⁻¹ * z⁻¹) ∈ conjSub a K := (conjSub a K).mul_mem hrLL h1
      have e : rL * z * rL⁻¹ * z⁻¹ = rL * (z * rL⁻¹ * z⁻¹) := by group
      rwa [e]
    have hz2 : z * z = 1 := hI.sq
    have hsq : rL * z * rL⁻¹ * z⁻¹ * (rL * z * rL⁻¹ * z⁻¹) = 1 := by
      have e1 : rL * z * rL⁻¹ * z⁻¹ * (rL * z * rL⁻¹ * z⁻¹) =
          (rL * z * rL⁻¹) * z⁻¹ * (rL * z * rL⁻¹) * z⁻¹ := by group
      have e2 : (rL * z * rL⁻¹) * z⁻¹ * (rL * z * rL⁻¹) =
          (rL * z * rL⁻¹) * (rL * z * rL⁻¹) * z⁻¹ := by
        have : z⁻¹ * (rL * z * rL⁻¹) = (rL * z * rL⁻¹) * z⁻¹ := by
          calc z⁻¹ * (rL * z * rL⁻¹) = z⁻¹ * (rL * z * rL⁻¹) * z * z⁻¹ := by group
            _ = z⁻¹ * (z * (rL * z * rL⁻¹)) * z⁻¹ := by rw [← hcomm]; group
            _ = (rL * z * rL⁻¹) * z⁻¹ := by group
        calc (rL * z * rL⁻¹) * z⁻¹ * (rL * z * rL⁻¹)
            = (rL * z * rL⁻¹) * (z⁻¹ * (rL * z * rL⁻¹)) := by group
          _ = (rL * z * rL⁻¹) * ((rL * z * rL⁻¹) * z⁻¹) := by rw [this]
          _ = (rL * z * rL⁻¹) * (rL * z * rL⁻¹) * z⁻¹ := by group
      have h3 : (rL * z * rL⁻¹) * (rL * z * rL⁻¹) = 1 := by
        calc (rL * z * rL⁻¹) * (rL * z * rL⁻¹) = rL * (z * z) * rL⁻¹ := by group
          _ = 1 := by rw [hz2]; group
      rw [e1, e2, h3, one_mul]
      calc z⁻¹ * z⁻¹ = (z * z)⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    rcases hLt.unique _ hu hsq with h | h
    · exfalso
      apply hrLz
      calc rL * z * rL⁻¹ = (rL * z * rL⁻¹ * z⁻¹) * z := by group
        _ = z := by rw [h]; group
    · calc rL * z * rL⁻¹ = (rL * z * rL⁻¹ * z⁻¹) * z := by group
        _ = t * z := by rw [h]
  have hBr : ∀ b ∈ B, b * r = r * b := fun b hb =>
    (Subgroup.mem_centralizer_iff.mp (hBR hb) r hrR).symm
  have hBrL : ∀ b ∈ B, b * rL = rL * b := fun b hb =>
    S1916.commute_of_mem_centralizerModOdd (hBL hb) hRL.1 hRL.2.1
      (mem_normalizer_iff_conjSub_eq.mpr (hTRL b (Subgroup.mem_sup_left hb))) hrLR
  refine ⟨r⁻¹ * rL, fun b hb => ?_, ?_⟩
  · have hbr := hBr b hb
    have hbr' : b * r⁻¹ = r⁻¹ * b := by
      calc b * r⁻¹ = r⁻¹ * (r * b) * r⁻¹ := by group
        _ = r⁻¹ * (b * r) * r⁻¹ := by rw [hbr]
        _ = r⁻¹ * b := by group
    calc r⁻¹ * rL * b = r⁻¹ * (rL * b) := by group
      _ = r⁻¹ * (b * rL) := by rw [hBrL b hb]
      _ = (r⁻¹ * b) * rL := by group
      _ = (b * r⁻¹) * rL := by rw [hbr']
      _ = b * (r⁻¹ * rL) := by group
  ·
    have hrz' : r⁻¹ * z * r = z := by
      have h := congrArg (fun x => r⁻¹ * x * r) hrz
      calc r⁻¹ * z * r = r⁻¹ * (r * z * r⁻¹) * r := h.symm
        _ = z := by group
    have hrt'' : r⁻¹ * t * r = t * z := by
      have h := congrArg (fun x => r⁻¹ * x * r) hrt'
      have h2 : t = (r⁻¹ * t * r) * z := by
        calc t = r⁻¹ * (r * t * r⁻¹) * r := by group
          _ = r⁻¹ * (t * z) * r := h
          _ = (r⁻¹ * t * r) * (r⁻¹ * z * r) := by group
          _ = (r⁻¹ * t * r) * z := by rw [hrz']
      calc r⁻¹ * t * r = (r⁻¹ * t * r) * (z * z) := by rw [hI.sq, mul_one]
        _ = ((r⁻¹ * t * r) * z) * z := by group
        _ = t * z := by rw [← h2]
    calc r⁻¹ * rL * z * (r⁻¹ * rL)⁻¹ = r⁻¹ * (rL * z * rL⁻¹) * r := by group
      _ = r⁻¹ * (t * z) * r := by rw [hrLz']
      _ = (r⁻¹ * t * r) * (r⁻¹ * z * r) := by group
      _ = (t * z) * z := by rw [hrt'', hrz']
      _ = t := by rw [mul_assoc, hI.sq, mul_one]

theorem exists_conj_eq_t_of_centralizes3 (hΩg : HypOmegaGen (CoreAssembly.conjClass K))
    (hDE : DEdgeless (CoreAssembly.conjClass K)) (hI : IsUniqueInvolution K z)
    (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G))
    {S : Sylow 2 G} {W L : Subgroup G} {t : G} (hW : W ∈ WSet (CoreAssembly.conjClass K))
    (hWS : W ≤ (S : Subgroup G)) (hzW : z ∈ W) (hRK : IsSylow2In ((S : Subgroup G) ⊓ K) K)
    (hL : L ∈ CoreAssembly.conjClass K) (hLt : IsUniqueInvolution L t) (htW : t ∈ W)
    (hzt : t ≠ z) {b : G} (hbS : b ∈ (S : Subgroup G))
    (hbR : b ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (hbW : b ∈ Subgroup.centralizer (W : Set G)) (hbL : b ∈ centralizerModOdd ⊤ L) :
    ∃ g : G, g * b = b * g ∧ g * z * g⁻¹ = t := by
  obtain ⟨g, hg, hgz⟩ := exists_conj_eq_t_of_subgroup3 hΩg hDE hI hN hW hWS hzW hRK hL hLt htW
    hzt (B := Subgroup.zpowers b) (Subgroup.zpowers_le.mpr hbS) (Subgroup.zpowers_le.mpr hbR)
    (Subgroup.zpowers_le.mpr hbW) (Subgroup.zpowers_le.mpr hbL)
  exact ⟨g, hg b (Subgroup.mem_zpowers b), hgz⟩

end Conj

end CFSG.ClassicalInvolution.Q3.Q3T6
