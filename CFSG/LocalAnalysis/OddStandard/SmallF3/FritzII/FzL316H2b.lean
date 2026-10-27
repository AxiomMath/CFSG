module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35c

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzl_card_comap {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card f.ker * Nat.card K := by
  let φ : K.comap f →* K :=
    { toFun := fun x => ⟨f x, x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective hφ
  have hker : φ.ker = f.ker.subgroupOf (K.comap f) := by
    ext x
    simp [φ, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subtype.ext_iff]
  have hle : f.ker ≤ K.comap f := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact K.one_mem
  have hker_card : Nat.card φ.ker = Nat.card f.ker := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hker_card] at hcard
  exact hcard.symm

theorem fzl_W_mem_iff {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    ∀ g : G, g ∈ ctxW t x₁ x₂ ↔ ∃ hg : g ∈ fzN2 t x₁ x₂, f ⟨g, hg⟩ = 1 := by
  intro g
  have hW_le_N2 : ctxW t x₁ x₂ ≤ fzN2 t x₁ x₂ := Subgroup.le_normalizer
  constructor
  · intro hg
    refine ⟨hW_le_N2 hg, ?_⟩
    rw [← MonoidHom.mem_ker, hF.ker, Subgroup.mem_subgroupOf]
    exact hg
  · rintro ⟨hg, hfg⟩
    have hmem : (⟨g, hg⟩ : ↥(fzN2 t x₁ x₂)) ∈ f.ker := MonoidHom.mem_ker.mpr hfg
    rw [hF.ker, Subgroup.mem_subgroupOf] at hmem
    exact hmem

theorem fzl_R_mem_iff (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    ∀ g : G, g ∈ fzR t x₁ x₂ ↔ ∃ hg : g ∈ fzN2 t x₁ x₂, f ⟨g, hg⟩ ∈ fzlK8 := by
  have hW_le_N2 : ctxW t x₁ x₂ ≤ fzN2 t x₁ x₂ := Subgroup.le_normalizer
  have hWker : Nat.card f.ker = 32 := by
    rw [hF.ker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_N2).toEquiv]
    exact fzl_card_W h hK
  have hcomap_card : Nat.card (fzlK8.comap f) = 2 ^ 8 := by
    have h := fzl_card_comap f hF.surj fzlK8
    rw [h, hWker, fzl_card_K8]
    norm_num
  have hC_eq : CFSG.pCore 2 ↥(fzN2 t x₁ x₂) = fzlK8.comap f := by
    apply le_antisymm
    · rw [← Subgroup.map_le_iff_le_comap]
      have hle : (CFSG.pCore 2 ↥(fzN2 t x₁ x₂)).map f ≤ CFSG.pCore 2 FzZ2xSigma4 :=
        le_sSup (show (CFSG.pCore 2 ↥(fzN2 t x₁ x₂)).map f ∈
            {K : Subgroup FzZ2xSigma4 | K.Normal ∧ IsPGroup 2 K} from
          ⟨(CFSG.pCore_normal (p := 2) (G := ↥(fzN2 t x₁ x₂))).map f hF.surj,
            (CFSG.pCore_isPGroup (p := 2) (G := ↥(fzN2 t x₁ x₂))).map f⟩)
      rwa [fzl_pCore_eq] at hle
    · refine le_sSup (show fzlK8.comap f ∈
          {K : Subgroup ↥(fzN2 t x₁ x₂) | K.Normal ∧ IsPGroup 2 K} from
        ⟨fzl_K8_normal.comap f, IsPGroup.of_card (n := 8) hcomap_card⟩)
  intro g
  constructor
  · intro hg
    rw [fzR, CFSG.Open.pCoreOf, Subgroup.mem_map] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    refine ⟨x.2, ?_⟩
    have hx' : x ∈ fzlK8.comap f := by rwa [← hC_eq]
    exact Subgroup.mem_comap.mp hx'
  · rintro ⟨hg, hfg⟩
    rw [fzR, CFSG.Open.pCoreOf, Subgroup.mem_map]
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [hC_eq]
    exact Subgroup.mem_comap.mpr hfg

end CFSG.OddStandard.SmallF3.FritzII
