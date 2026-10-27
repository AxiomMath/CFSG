module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.ChainHyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.AutAFacts
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

private def fixMap (t x : G) : G := x⁻¹ * (t * x * t⁻¹)

private theorem fixMap_one (t : G) : fixMap t 1 = 1 := by
  simp [fixMap]

private theorem fixMap_mul (t x y : G) :
    fixMap t (x * y) = y⁻¹ * fixMap t x * y * fixMap t y := by
  simp only [fixMap]
  group

private theorem fixMap_inv (t x : G) :
    fixMap t x⁻¹ = x * (fixMap t x)⁻¹ * x⁻¹ := by
  simp only [fixMap]
  group

private theorem conj_eq_mul_fixMap (t x : G) : t * x * t⁻¹ = x * fixMap t x := by
  rw [fixMap]
  group

private theorem fixMap_conj_t (t x : G) :
    fixMap t (t * x * t⁻¹) = t * fixMap t x * t⁻¹ := by
  simp only [fixMap]
  group

private theorem fixMap_conj_Hn {t n x : G} (hnt : t * n = n * t) :
    fixMap t (n * x * n⁻¹) = n * fixMap t x * n⁻¹ := by
  have hnt' : n⁻¹ * t⁻¹ = t⁻¹ * n⁻¹ := by
    rw [← mul_inv_rev, hnt, mul_inv_rev]
  have h1 : t * (n * x * n⁻¹) * t⁻¹ = n * (t * x * t⁻¹) * n⁻¹ := by
    calc t * (n * x * n⁻¹) * t⁻¹ = (t * n) * x * (n⁻¹ * t⁻¹) := by group
      _ = (n * t) * x * (t⁻¹ * n⁻¹) := by rw [hnt, hnt']
      _ = n * (t * x * t⁻¹) * n⁻¹ := by group
  rw [fixMap, h1]
  rw [fixMap]
  group

private theorem fixMap_mul_conj_self {t x : G} (ht : t * t = 1) :
    fixMap t x * (t * fixMap t x * t⁻¹) = 1 := by
  have htinv2 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
  simp only [fixMap]
  calc (x⁻¹ * (t * x * t⁻¹)) * (t * (x⁻¹ * (t * x * t⁻¹)) * t⁻¹)
      = x⁻¹ * (t * t) * x * (t⁻¹ * t⁻¹) := by group
    _ = 1 := by rw [ht, htinv2]; group

private def layerX (D F : Subgroup G) (t : G) : Subgroup G where
  carrier := {x | x ∈ centralizer (D : Set G) ∧ x ∈ normalizer (F : Set G) ∧
    fixMap t x ∈ F}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, Subgroup.one_mem _, ?_⟩
    simp [fixMap]
  mul_mem' := by
    rintro x y ⟨hxC, hxN, hxF⟩ ⟨hyC, hyN, hyF⟩
    refine ⟨Subgroup.mul_mem _ hxC hyC, Subgroup.mul_mem _ hxN hyN, ?_⟩
    rw [fixMap_mul]
    refine F.mul_mem ?_ hyF
    simpa using (mem_normalizer_iff.1 ((normalizer (F : Set G)).inv_mem hyN)
      (fixMap t x)).1 hxF
  inv_mem' := by
    rintro x ⟨hxC, hxN, hxF⟩
    refine ⟨Subgroup.inv_mem _ hxC, Subgroup.inv_mem _ hxN, ?_⟩
    rw [fixMap_inv]
    exact (mem_normalizer_iff.1 hxN ((fixMap t x)⁻¹)).1 (F.inv_mem hxF)

private theorem mem_layerX {D F : Subgroup G} {t x : G} :
    x ∈ layerX D F t ↔ x ∈ centralizer (D : Set G) ∧ x ∈ normalizer (F : Set G) ∧
      fixMap t x ∈ F := Iff.rfl

private theorem layerX_le_centralizer (D F : Subgroup G) (t : G) :
    layerX D F t ≤ centralizer (D : Set G) := fun _ hx => (mem_layerX.1 hx).1

private theorem layerX_le_normalizer (D F : Subgroup G) (t : G) :
    layerX D F t ≤ normalizer (F : Set G) := fun _ hx => (mem_layerX.1 hx).2.1

private theorem fixMap_mem_of_mem_layerX {D F : Subgroup G} {t x : G}
    (hx : x ∈ layerX D F t) : fixMap t x ∈ F := (mem_layerX.1 hx).2.2

private theorem F_le_layerX {D F : Subgroup G} {t : G} (hF : ChainHyp L A D t F) :
    F ≤ layerX D F t := by
  intro f hf
  rw [mem_layerX]
  refine ⟨hF.le_centralizer hf, Subgroup.le_normalizer hf, ?_⟩
  exact F.mul_mem (F.inv_mem hf) (hF.conj_t_mem f hf)

private theorem layerX_conj_t (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {F : Subgroup G}
    (hF : ChainHyp L A D t F) {x : G} (hx : x ∈ layerX D F t) :
    t * x * t⁻¹ ∈ layerX D F t := by
  rw [mem_layerX] at hx ⊢
  obtain ⟨hxC, hxN, hxF⟩ := hx
  have ht : t * t = 1 := by simpa [sq] using H.sq_t
  have htD : t ∈ normalizer (D : Set G) :=
    le_normalizer_of_conj_mem hD.norm (H.t_mem_normalizer W W2 hD)
  have htF : t ∈ normalizer (F : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · exact hF.conj_t_mem y
    · intro hmem
      have htinv2 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
      have h := hF.conj_t_mem (t * y * t⁻¹) hmem
      rwa [show t * (t * y * t⁻¹) * t⁻¹ = y by
        calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t⁻¹ * t⁻¹) := by group
          _ = y := by rw [ht, htinv2]; group] at h
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_normalizer_iff.1 (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer D htD) x).1 hxC
  · exact (mem_normalizer_iff.1 (Subgroup.le_normalizer htF) x).1 hxN
  · rw [fixMap_conj_t]
    exact hF.conj_t_mem (fixMap t x) hxF

private theorem layerX_conj_Hn (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {F : Subgroup G}
    (hF : ChainHyp L A D t F) {n x : G} (hn : n ∈ L ⊓ normalizer (A : Set G))
    (hx : x ∈ layerX D F t) : n * x * n⁻¹ ∈ layerX D F t := by
  rw [mem_layerX] at hx ⊢
  obtain ⟨hxC, hxN, hxF⟩ := hx
  have hnD : n ∈ L ⊓ normalizer (D : Set G) := by
    rw [H.inf_normalizer_D_eq W W2 hD]
    exact hn
  have hnF : n ∈ normalizer (F : Set G) :=
    le_normalizer_of_conj_mem (N := L ⊓ normalizer (A : Set G)) (D := F) hF.conj_mem hn
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_normalizer_iff.1
      (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer D hnD.2) x).1 hxC
  · exact (mem_normalizer_iff.1 (Subgroup.le_normalizer hnF) x).1 hxN
  · rw [fixMap_conj_Hn (H.comm_of_mem_L hn.1)]
    exact hF.conj_mem n hn (fixMap t x) hxF

private theorem fixMap_mem_It (H : ThCyc G L R t) {F It : Subgroup G}
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1) {x : G}
    (hxF : fixMap t x ∈ F) : fixMap t x ∈ It := by
  have ht : t * t = 1 := by simpa [sq] using H.sq_t
  rw [hIt]
  exact ⟨hxF, fixMap_mul_conj_self ht⟩

private theorem phi_mul_right_mem_F (H : ThCyc G L R t) {F Ft It : Subgroup G}
    (hF : ChainHyp L A D t F) {κ : G → G}
    (hFt : ∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g)
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1)
    (hκ : IsLayer L A Ft It κ) {x f : G} (hx : x ∈ layerX D F t) (hf : f ∈ F) :
    κ (fixMap t (x * f)) = κ (fixMap t x) := by
  have hxN : x ∈ normalizer (F : Set G) := (mem_layerX.1 hx).2.1
  have hxF : fixMap t x ∈ F := (mem_layerX.1 hx).2.2
  have hfIt : fixMap t f ∈ It := hκ.le ((hFt (fixMap t f)).2 ⟨f, hf, rfl⟩)
  have hxFIt : fixMap t x ∈ It := fixMap_mem_It H hIt hxF
  have hfix : fixMap t (x * f) = fixMap t x * fixMap t f := by
    rw [fixMap_mul]
    have hcomm : f⁻¹ * fixMap t x * f = fixMap t x := by
      rw [hF.comm (f⁻¹ * fixMap t x) (F.mul_mem (F.inv_mem hf) hxF) f hf]
      group
    rw [hcomm]
  rw [hfix, hκ.map_mul (fixMap t x) hxFIt (fixMap t f) hfIt,
    (hκ.eq_one_iff (fixMap t f) hfIt).2 ((hFt _).2 ⟨f, hf, rfl⟩), mul_one]

private theorem phi_mul_left_mem_F (H : ThCyc G L R t) {F Ft It : Subgroup G}
    (hF : ChainHyp L A D t F) {κ : G → G}
    (hFt : ∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g)
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1)
    (hκ : IsLayer L A Ft It κ) {x f : G} (hx : x ∈ layerX D F t) (hf : f ∈ F) :
    κ (fixMap t (f * x)) = κ (fixMap t x) := by
  have hxN : x ∈ normalizer (F : Set G) := (mem_layerX.1 hx).2.1
  have hf' : x⁻¹ * f * x ∈ F := by
    simpa using (mem_normalizer_iff.1 ((normalizer (F : Set G)).inv_mem hxN) f).1 hf
  have h : f * x = x * (x⁻¹ * f * x) := by group
  rw [h]
  exact phi_mul_right_mem_F H hF hFt hIt hκ hx hf'

private theorem phi_eq_one_iff (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {F Ft It : Subgroup G}
    (hF : ChainHyp L A D t F) {κ : G → G}
    (hFt : ∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g)
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1)
    (hκ : IsLayer L A Ft It κ) {x : G} (hx : x ∈ layerX D F t) :
    κ (fixMap t x) = 1 ↔ x ∈ F := by
  constructor
  · intro h
    have hxIt : fixMap t x ∈ It := fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hx)
    have hFt_mem : fixMap t x ∈ Ft := (hκ.eq_one_iff _ hxIt).1 h
    obtain ⟨f, hf, hfx⟩ := (hFt _).1 hFt_mem
    have hxC : x ∈ centralizer (D : Set G) := (mem_layerX.1 hx).1
    have hfC : f ∈ centralizer (D : Set G) := hF.le_centralizer hf
    have hmemC : x * f⁻¹ ∈ centralizer (D : Set G) :=
      (centralizer (D : Set G)).mul_mem hxC ((centralizer (D : Set G)).inv_mem hfC)
    have hfix : t * (x * f⁻¹) * t⁻¹ = x * f⁻¹ := by
      calc t * (x * f⁻¹) * t⁻¹
          = (t * x * t⁻¹) * (t * f * t⁻¹)⁻¹ := by group
        _ = (x * fixMap t x) * (t * f * t⁻¹)⁻¹ := by rw [conj_eq_mul_fixMap]
        _ = x * f⁻¹ := by rw [← hfx]; group
    have hmemT : x * f⁻¹ ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h2 : (t * (x * f⁻¹) * t⁻¹) * t = t * (x * f⁻¹) := by group
      have := congrArg (fun w => w * t) hfix
      rw [h2] at this
      exact this.symm
    have hmemAa : x * f⁻¹ ∈ Aa := by
      have h := H.centralizer_D_inf_centralizer_t W W2 hD
      rw [← h]
      exact ⟨hmemC, hmemT⟩
    have hzF : x * f⁻¹ ∈ F := hF.D_le (hD.Aa_le hmemAa)
    have hxeq : x = (x * f⁻¹) * f := by group
    rw [hxeq]
    exact F.mul_mem hzF hf
  · intro hxF
    have hxIt : fixMap t x ∈ It := fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hx)
    exact (hκ.eq_one_iff _ hxIt).2 ((hFt _).2 ⟨x, hxF, rfl⟩)

private theorem phi_inj (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {F Ft It : Subgroup G}
    (hF : ChainHyp L A D t F) {κ : G → G}
    (hFt : ∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g)
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1)
    (hκ : IsLayer L A Ft It κ) {x y : G} (hx : x ∈ layerX D F t)
    (hy : y ∈ layerX D F t) (hφ : κ (fixMap t x) = κ (fixMap t y)) :
    x⁻¹ * y ∈ F := by
  have hxIt : fixMap t x ∈ It := fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hx)
  have hyIt : fixMap t y ∈ It := fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hy)
  have hxInvIt : (fixMap t x)⁻¹ ∈ It := It.inv_mem hxIt
  have hprodIt : (fixMap t x)⁻¹ * fixMap t y ∈ It := It.mul_mem hxInvIt hyIt
  have hk : κ ((fixMap t x)⁻¹ * fixMap t y) = 1 := by
    rw [hκ.map_mul (fixMap t x)⁻¹ hxInvIt (fixMap t y) hyIt, hκ.map_inv hxIt, hφ]
    group
  have hFt_mem : (fixMap t x)⁻¹ * fixMap t y ∈ Ft := (hκ.eq_one_iff _ hprodIt).1 hk
  obtain ⟨f, hf, hfx⟩ := (hFt _).1 hFt_mem
  have hxN : x ∈ normalizer (F : Set G) := (mem_layerX.1 hx).2.1
  have hxF : fixMap t x ∈ F := fixMap_mem_of_mem_layerX hx
  have hxy_fix : fixMap t (x * f) = fixMap t y := by
    rw [fixMap_mul]
    have hcomm : f⁻¹ * fixMap t x * f = fixMap t x := by
      rw [hF.comm (f⁻¹ * fixMap t x) (F.mul_mem (F.inv_mem hf) hxF) f hf]
      group
    rw [hcomm]
    have hfy : fixMap t x * fixMap t f = fixMap t y := by
      rw [show fixMap t f = (fixMap t x)⁻¹ * fixMap t y from hfx]
      group
    exact hfy
  have hfix : t * (x * f * y⁻¹) * t⁻¹ = x * f * y⁻¹ := by
    calc t * (x * f * y⁻¹) * t⁻¹
        = (t * (x * f) * t⁻¹) * (t * y * t⁻¹)⁻¹ := by group
      _ = ((x * f) * fixMap t (x * f)) * (y * fixMap t y)⁻¹ := by
          rw [conj_eq_mul_fixMap, conj_eq_mul_fixMap]
      _ = x * f * y⁻¹ := by rw [hxy_fix]; group
  have hxC : x ∈ centralizer (D : Set G) := (mem_layerX.1 hx).1
  have hyC : y ∈ centralizer (D : Set G) := (mem_layerX.1 hy).1
  have hmemC : x * f * y⁻¹ ∈ centralizer (D : Set G) :=
    (centralizer (D : Set G)).mul_mem
      ((centralizer (D : Set G)).mul_mem hxC (hF.le_centralizer hf))
      ((centralizer (D : Set G)).inv_mem hyC)
  have hmemT : x * f * y⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h2 : (t * (x * f * y⁻¹) * t⁻¹) * t = t * (x * f * y⁻¹) := by group
    have := congrArg (fun w => w * t) hfix
    rw [h2] at this
    exact this.symm
  have hmemAa : x * f * y⁻¹ ∈ Aa := by
    have h := H.centralizer_D_inf_centralizer_t W W2 hD
    rw [← h]
    exact ⟨hmemC, hmemT⟩
  have hzF : x * f * y⁻¹ ∈ F := hF.D_le (hD.Aa_le hmemAa)
  have hxinv_z : x⁻¹ * (x * f * y⁻¹)⁻¹ * x ∈ F := by
    simpa using (mem_normalizer_iff.1 ((normalizer (F : Set G)).inv_mem hxN)
      (x * f * y⁻¹)⁻¹).1 (F.inv_mem hzF)
  have hxy : x⁻¹ * y = (x⁻¹ * (x * f * y⁻¹)⁻¹ * x) * f := by group
  rw [hxy]
  exact F.mul_mem hxinv_z hf


private theorem phi_conj (H : ThCyc G L R t) {F Ft It : Subgroup G}
    (hF : ChainHyp L A D t F) {κ : G → G}
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1)
    (hκ : IsLayer L A Ft It κ) {n x : G}
    (hn : n ∈ L ⊓ normalizer (A : Set G)) (hx : x ∈ layerX D F t) :
    κ (fixMap t (n * x * n⁻¹)) = n * κ (fixMap t x) * n⁻¹ := by
  have hnt : t * n = n * t := H.comm_of_mem_L hn.1
  have hxIt : fixMap t x ∈ It := fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hx)
  rw [fixMap_conj_Hn hnt]
  exact hκ.conj n hn (fixMap t x) hxIt

private theorem phi_mul_fixed_of_fix (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {F Ft It : Subgroup G}
    (hF : ChainHyp L A D t F) {κ : G → G}
    (hFt : ∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g)
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1)
    (hκ : IsLayer L A Ft It κ) {x y : G} (hx : x ∈ layerX D F t)
    (hy : y ∈ layerX D F t) {n : G} (hn : n ∈ L ⊓ normalizer (A : Set G))
    (hnx : n * κ (fixMap t x) * n⁻¹ = κ (fixMap t x))
    (hny : n * κ (fixMap t y) * n⁻¹ = κ (fixMap t y)) :
    n * κ (fixMap t (x * y)) * n⁻¹ = κ (fixMap t (x * y)) := by
  have hxN : x ∈ normalizer (F : Set G) := (mem_layerX.1 hx).2.1
  have hyN : y ∈ normalizer (F : Set G) := (mem_layerX.1 hy).2.1
  have hnxX : n * x * n⁻¹ ∈ layerX D F t := layerX_conj_Hn H W W2 hD hF hn hx
  have hnyX : n * y * n⁻¹ ∈ layerX D F t := layerX_conj_Hn H W W2 hD hF hn hy
  have hphix : κ (fixMap t (n * x * n⁻¹)) = κ (fixMap t x) := by
    rw [phi_conj H hF hIt hκ hn hx, hnx]
  have hphiy : κ (fixMap t (n * y * n⁻¹)) = κ (fixMap t y) := by
    rw [phi_conj H hF hIt hκ hn hy, hny]
  let f := x⁻¹ * (n * x * n⁻¹)
  let g := y⁻¹ * (n * y * n⁻¹)
  have hf : f ∈ F := phi_inj H W W2 hD hF hFt hIt hκ hx hnxX hphix.symm
  have hg : g ∈ F := phi_inj H W W2 hD hF hFt hIt hκ hy hnyX hphiy.symm
  have hxn : n * x * n⁻¹ = x * f := by dsimp [f]; group
  have hyn : n * y * n⁻¹ = y * g := by dsimp [g]; group
  have hf' : y⁻¹ * f * y ∈ F := by
    simpa using (mem_normalizer_iff.1 ((normalizer (F : Set G)).inv_mem hyN) f).1 hf
  have hprod : n * (x * y) * n⁻¹ = (x * y) * (y⁻¹ * f * y * g) := by
    calc n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
      _ = (x * f) * (y * g) := by rw [hxn, hyn]
      _ = (x * y) * (y⁻¹ * f * y * g) := by group
  have hf'' : y⁻¹ * f * y * g ∈ F := F.mul_mem hf' hg
  have hxyX : x * y ∈ layerX D F t := (layerX D F t).mul_mem hx hy
  calc n * κ (fixMap t (x * y)) * n⁻¹
      = κ (fixMap t (n * (x * y) * n⁻¹)) := (phi_conj H hF hIt hκ hn hxyX).symm
    _ = κ (fixMap t ((x * y) * (y⁻¹ * f * y * g))) := by rw [hprod]
    _ = κ (fixMap t (x * y)) := phi_mul_right_mem_F H hF hFt hIt hκ hxyX hf''

private theorem phi_inv_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {F Ft It : Subgroup G}
    (hF : ChainHyp L A D t F) {κ : G → G}
    (hFt : ∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g)
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1)
    (hκ : IsLayer L A Ft It κ) {y : G} (hy : y ∈ layerX D F t) :
    κ (fixMap t y⁻¹) = κ (fixMap t y) := by
  let a' := κ (fixMap t y)
  let v := κ (fixMap t y⁻¹)
  have hyInvX : y⁻¹ ∈ layerX D F t := (layerX D F t).inv_mem hy
  have ha'A : a' ∈ A :=
    hκ.mem _ (fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hy))
  have hvA : v ∈ A :=
    hκ.mem _ (fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hyInvX))
  change v = a'
  have hfix : ∀ n ∈ L ⊓ normalizer (A : Set G), n * a' * n⁻¹ = a' →
      n * a' * n⁻¹ = a' → n * v * n⁻¹ = v := by
    intro n hn hna _
    have hnyX : n * y * n⁻¹ ∈ layerX D F t := layerX_conj_Hn H W W2 hD hF hn hy
    have hphiy : κ (fixMap t (n * y * n⁻¹)) = κ (fixMap t y) := by
      rw [phi_conj H hF hIt hκ hn hy, hna]
    have hf : y⁻¹ * (n * y * n⁻¹) ∈ F :=
      phi_inj H W W2 hD hF hFt hIt hκ hy hnyX hphiy.symm
    have hyN : y ∈ normalizer (F : Set G) := (mem_layerX.1 hy).2.1
    have hf'' : y * (y⁻¹ * (n * y * n⁻¹))⁻¹ * y⁻¹ ∈ F := by
      simpa using (mem_normalizer_iff.1 hyN (y⁻¹ * (n * y * n⁻¹))⁻¹).1 (F.inv_mem hf)
    have hnyInv : n * y⁻¹ * n⁻¹ =
        y⁻¹ * (y * (y⁻¹ * (n * y * n⁻¹))⁻¹ * y⁻¹) := by
      rw [show n * y * n⁻¹ = y * (y⁻¹ * (n * y * n⁻¹)) by group]
      group
    calc n * v * n⁻¹
        = n * κ (fixMap t y⁻¹) * n⁻¹ := rfl
      _ = κ (fixMap t (n * y⁻¹ * n⁻¹)) := (phi_conj H hF hIt hκ hn hyInvX).symm
      _ = κ (fixMap t (y⁻¹ * (y * (y⁻¹ * (n * y * n⁻¹))⁻¹ * y⁻¹))) := by rw [hnyInv]
      _ = κ (fixMap t y⁻¹) := phi_mul_right_mem_F H hF hFt hIt hκ hyInvX hf''
      _ = v := rfl
  have hv_or : v = 1 ∨ v = a' := by
    rcases W.eq_of_forall_conj_eq ha'A ha'A hvA hfix with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
    · left
      rw [h, ← sq, W.A_sq a' ha'A]
  rcases hv_or with h | h
  · have hyInvF : y⁻¹ ∈ F :=
      (phi_eq_one_iff H W W2 hD hF hFt hIt hκ hyInvX).1 h
    have hyF : y ∈ F := by simpa using F.inv_mem hyInvF
    have ha'1 : a' = 1 := (phi_eq_one_iff H W W2 hD hF hFt hIt hκ hy).2 hyF
    rw [h, ha'1]
  · exact h

private theorem phi_sq_eq_one (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {F Ft It : Subgroup G}
    (hF : ChainHyp L A D t F) {κ : G → G}
    (hFt : ∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g)
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1)
    (hκ : IsLayer L A Ft It κ) {y : G} (hy : y ∈ layerX D F t) :
    κ (fixMap t (y * y)) = 1 := by
  let a' := κ (fixMap t y)
  let w := κ (fixMap t (y * y))
  have hyyX : y * y ∈ layerX D F t := (layerX D F t).mul_mem hy hy
  have ha'A : a' ∈ A :=
    hκ.mem _ (fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hy))
  have hwA : w ∈ A :=
    hκ.mem _ (fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hyyX))
  change w = 1
  have hfix : ∀ n ∈ L ⊓ normalizer (A : Set G), n * a' * n⁻¹ = a' →
      n * a' * n⁻¹ = a' → n * w * n⁻¹ = w := by
    intro n hn hna _
    exact phi_mul_fixed_of_fix H W W2 hD hF hFt hIt hκ hy hy hn hna hna
  have hw_a' : w = a' → w = 1 := by
    intro hwa
    change w = 1
    by_cases ha'1 : a' = 1
    · rw [hwa, ha'1]
    · exfalso
      have hwa_eq : κ (fixMap t (y * y)) = κ (fixMap t y) := by
        change w = a'
        rw [hwa]
      have hyInvF : y⁻¹ ∈ F := by
        have h := phi_inj H W W2 hD hF hFt hIt hκ hyyX hy hwa_eq
        rwa [show (y * y)⁻¹ * y = y⁻¹ by group] at h
      have hyF : y ∈ F := by simpa using F.inv_mem hyInvF
      exact ha'1 ((phi_eq_one_iff H W W2 hD hF hFt hIt hκ hy).2 hyF)
  rcases W.eq_of_forall_conj_eq ha'A ha'A hwA hfix with h | h | h | h
  · exact h
  · exact hw_a' h
  · exact hw_a' h
  · rw [h, ← sq, W.A_sq a' ha'A]

private theorem phi_mul (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {F Ft It : Subgroup G}
    (hF : ChainHyp L A D t F) {κ : G → G}
    (hFt : ∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g)
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1)
    (hκ : IsLayer L A Ft It κ) {x y : G} (hx : x ∈ layerX D F t)
    (hy : y ∈ layerX D F t) :
    κ (fixMap t (x * y)) = κ (fixMap t x) * κ (fixMap t y) := by
  let a := κ (fixMap t x)
  let a' := κ (fixMap t y)
  let v := κ (fixMap t (x * y))
  have haA : a ∈ A :=
    hκ.mem _ (fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hx))
  have ha'A : a' ∈ A :=
    hκ.mem _ (fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hy))
  have hxyX : x * y ∈ layerX D F t := (layerX D F t).mul_mem hx hy
  have hvA : v ∈ A :=
    hκ.mem _ (fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hxyX))
  change v = a * a'
  have hv_or : v = 1 ∨ v = a ∨ v = a' ∨ v = a * a' := by
    refine W.eq_of_forall_conj_eq haA ha'A hvA ?_
    intro n hn hna hna'
    exact phi_mul_fixed_of_fix H W W2 hD hF hFt hIt hκ hx hy hn hna hna'
  by_cases ha1 : a = 1
  · have hxF : x ∈ F := (phi_eq_one_iff H W W2 hD hF hFt hIt hκ hx).1 ha1
    have hphi : v = a' := by
      dsimp [v, a']
      exact phi_mul_left_mem_F H hF hFt hIt hκ hy hxF
    rw [hphi, ha1, one_mul]
  · by_cases ha'1 : a' = 1
    · have hyF : y ∈ F := (phi_eq_one_iff H W W2 hD hF hFt hIt hκ hy).1 ha'1
      have hphi : v = a := by
        dsimp [v, a]
        exact phi_mul_right_mem_F H hF hFt hIt hκ hx hyF
      rw [hphi, ha'1, mul_one]
    · by_cases haa' : a = a'
      · have haa_eq : κ (fixMap t x) = κ (fixMap t y) := by
          change a = a'
          rw [haa']
        have hxinv_y : x⁻¹ * y ∈ F :=
          phi_inj H W W2 hD hF hFt hIt hκ hx hy haa_eq
        have hyinv_x : y⁻¹ * x ∈ F := by simpa using F.inv_mem hxinv_y
        have hf' : y⁻¹ * (y⁻¹ * x) * y ∈ F := by
          simpa using (mem_normalizer_iff.1 ((normalizer (F : Set G)).inv_mem
            ((mem_layerX.1 hy).2.1)) (y⁻¹ * x)).1 hyinv_x
        have hxy_eq : x * y = (y * y) * (y⁻¹ * (y⁻¹ * x) * y) := by group
        have hphi : v = 1 := by
          dsimp [v]
          rw [hxy_eq]
          rw [phi_mul_right_mem_F H hF hFt hIt hκ ((layerX D F t).mul_mem hy hy) hf']
          exact phi_sq_eq_one H W W2 hD hF hFt hIt hκ hy
        rw [hphi, haa', ← sq, W.A_sq a' ha'A]
      · rcases hv_or with hv1 | hva | hva' | hvprod
        · exfalso
          have hxyF : x * y ∈ F :=
            (phi_eq_one_iff H W W2 hD hF hFt hIt hκ hxyX).1 hv1
          have hphi : a = a' := by
            dsimp [a, a']
            rw [show x = (x * y) * y⁻¹ by group]
            rw [phi_mul_left_mem_F H hF hFt hIt hκ ((layerX D F t).inv_mem hy) hxyF]
            exact phi_inv_eq H W W2 hD hF hFt hIt hκ hy
          exact haa' hphi
        · exfalso
          have hva_eq : κ (fixMap t (x * y)) = κ (fixMap t x) := by
            change v = a
            rw [hva]
          have hyinvF : y⁻¹ ∈ F := by
            have h := phi_inj H W W2 hD hF hFt hIt hκ hxyX hx hva_eq
            rwa [show (x * y)⁻¹ * x = y⁻¹ by group] at h
          have hyF : y ∈ F := by simpa using F.inv_mem hyinvF
          exact ha'1 ((phi_eq_one_iff H W W2 hD hF hFt hIt hκ hy).2 hyF)
        · exfalso
          have hva'_eq : κ (fixMap t (x * y)) = κ (fixMap t y) := by
            change v = a'
            rw [hva']
          have h := phi_inj H W W2 hD hF hFt hIt hκ hxyX hy hva'_eq
          have h' : y⁻¹ * x⁻¹ * y ∈ F := by
            rwa [show (x * y)⁻¹ * y = y⁻¹ * x⁻¹ * y by group] at h
          have hxinvF : x⁻¹ ∈ F := by
            have hyN : y ∈ normalizer (F : Set G) := (mem_layerX.1 hy).2.1
            have hconj := (mem_normalizer_iff.1 hyN (y⁻¹ * x⁻¹ * y)).1 h'
            rwa [show y * (y⁻¹ * x⁻¹ * y) * y⁻¹ = x⁻¹ by group] at hconj
          have hxF : x ∈ F := by simpa using F.inv_mem hxinvF
          exact ha1 ((phi_eq_one_iff H W W2 hD hF hFt hIt hκ hx).2 hxF)
        · exact hvprod

private theorem phi_surj (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {F Ft It : Subgroup G}
    (hF : ChainHyp L A D t F) {κ : G → G}
    (hFt : ∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g)
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1)
    (hκ : IsLayer L A Ft It κ) {p : G} (hp : p ∈ layerX D F t) (hpF : p ∉ F) :
    ∀ a ∈ A, ∃ x ∈ layerX D F t, κ (fixMap t x) = a := by
  have hpA : κ (fixMap t p) ∈ A :=
    hκ.mem _ (fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hp))
  have hp_ne : κ (fixMap t p) ≠ 1 := fun h =>
    hpF ((phi_eq_one_iff H W W2 hD hF hFt hIt hκ hp).1 h)
  intro a ha
  by_cases ha1 : a = 1
  · subst ha1
    refine ⟨1, F_le_layerX hF F.one_mem, ?_⟩
    rw [fixMap_one, hκ.map_one]
  · obtain ⟨n₁, hn₁L, hn₁A, hn₁z⟩ := W.trans (κ (fixMap t p)) hpA hp_ne
    obtain ⟨n₂, hn₂L, hn₂A, hn₂z⟩ := W.trans a ha ha1
    let n := n₂ * n₁⁻¹
    have hnL : n ∈ L := L.mul_mem hn₂L (L.inv_mem hn₁L)
    have hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A := by
      intro x hx
      have hn₁invN : n₁⁻¹ ∈ normalizer (A : Set G) :=
        mem_iff_conj_of_conj_le A (g := n₁⁻¹) (by simpa using hn₁A)
      have hn₂invN : n₂⁻¹ ∈ normalizer (A : Set G) :=
        mem_iff_conj_of_conj_le A (g := n₂⁻¹) (by simpa using hn₂A)
      have hn₂N : n₂ ∈ normalizer (A : Set G) := by
        simpa using (normalizer (A : Set G)).inv_mem hn₂invN
      have hx1 : n₁⁻¹ * x * n₁ ∈ A := by
        simpa using (mem_normalizer_iff.1 hn₁invN x).1 hx
      have hx2 : n₂ * (n₁⁻¹ * x * n₁) * n₂⁻¹ ∈ A :=
        (mem_normalizer_iff.1 hn₂N (n₁⁻¹ * x * n₁)).1 hx1
      simpa [n, mul_assoc] using hx2
    have hnHn : n ∈ L ⊓ normalizer (A : Set G) :=
      W.mem_inf_normalizer_of_forall_conj_mem hnL hnA
    refine ⟨n * p * n⁻¹, layerX_conj_Hn H W W2 hD hF hnHn hp, ?_⟩
    have hpIt : fixMap t p ∈ It :=
      fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hp)
    have hnt : t * n = n * t := H.comm_of_mem_L hnL
    rw [fixMap_conj_Hn hnt, hκ.conj n hnHn (fixMap t p) hpIt]
    calc n * κ (fixMap t p) * n⁻¹
        = (n₂ * n₁⁻¹) * (n₁ * z * n₁⁻¹) * (n₂ * n₁⁻¹)⁻¹ := by rw [← hn₁z]
      _ = n₂ * z * n₂⁻¹ := by group
      _ = a := hn₂z

theorem ChainHyp.exists_isLayer_of_fix (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {F : Subgroup G} (hF : ChainHyp L A D t F)
    {Ft It : Subgroup G} {κ : G → G}
    (hFt : ∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g)
    (hIt : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1) (hκ : IsLayer L A Ft It κ)
    {p : G} (hpC : p ∈ centralizer (D : Set G)) (hpN : p ∈ normalizer (F : Set G)) (hpF : p ∉ F)
    (hfp : p⁻¹ * (t * p * t⁻¹) ∈ F) :
    ∃ (X : Subgroup G) (φ : G → G), IsLayer L A F X φ ∧ X ≤ centralizer (D : Set G) ∧
      X ≤ normalizer (F : Set G) ∧ ∀ x ∈ X, t * x * t⁻¹ ∈ X := by
  have hpX : p ∈ layerX D F t := by
    rw [mem_layerX]
    exact ⟨hpC, hpN, hfp⟩
  refine ⟨layerX D F t, fun x => κ (fixMap t x), ?_⟩
  refine ⟨?_, layerX_le_centralizer D F t, layerX_le_normalizer D F t, ?_⟩
  · refine ⟨F_le_layerX hF, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun n hn x hx => layerX_conj_Hn H W W2 hD hF hn hx
    · exact fun x hx => hκ.mem _ (fixMap_mem_It H hIt (fixMap_mem_of_mem_layerX hx))
    · exact fun x hx y hy => phi_mul H W W2 hD hF hFt hIt hκ hx hy
    · exact fun x hx => phi_eq_one_iff H W W2 hD hF hFt hIt hκ hx
    · exact phi_surj H W W2 hD hF hFt hIt hκ hpX hpF
    · exact fun n hn x hx => phi_conj H hF hIt hκ hn hx
  · exact fun x hx => layerX_conj_t H W W2 hD hF hx

end CFSG.EvenSporadicStandard.ThStd

end
