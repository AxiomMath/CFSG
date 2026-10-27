module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
public import CFSG.GroupTheory.SylowIntersectionControl.Selection
public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne
open scoped IsMulCommutative commutatorElement

variable {Ω : Type} [Group Ω]

@[expose] noncomputable def gomiBar (G : Subgroup Ω) : ↥G →* ↥(autOn G (gomiV G)) :=
  CFSG.CGT.PushingUpLit.BHS6.actOnRange (gomiV G) G (gomiV_moduleSetting G).2

@[expose] noncomputable def gomiBarOf (G K : Subgroup Ω) : Subgroup ↥(autOn G (gomiV G)) :=
  (autOn K (gomiV G)).subgroupOf (autOn G (gomiV G))

@[expose] noncomputable def gomiBarPre (G : Subgroup Ω) (M : Subgroup ↥(autOn G (gomiV G))) :
    Subgroup Ω :=
  (M.comap (gomiBar G)).map G.subtype

@[expose] def gomiRegFamily (f : PSubgroupSelection 2 Ω) (G : Subgroup Ω) :
    Set (Subgroup ↥(autOn G (gomiV G))) :=
  {M | M ≠ ⊤ ∧ Odd M.index ∧ f.IsRegular (gomiBarPre G M)}

private theorem mem_gomiBarPre_geb {G : Subgroup Ω} {M : Subgroup ↥(autOn G (gomiV G))}
    {x : Ω} : x ∈ gomiBarPre G M ↔ ∃ hx : x ∈ G, gomiBar G ⟨x, hx⟩ ∈ M := by
  unfold gomiBarPre
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hxM⟩
    exact ⟨⟨x, hx⟩, hxM, rfl⟩

private theorem subgroupOf_closure_subtype_geb {G : Subgroup Ω} {S : Set Ω} (hS : S ⊆ G) :
    (Subgroup.closure S).subgroupOf G = Subgroup.closure (G.subtype ⁻¹' S) := by
  have himg : G.subtype '' (G.subtype ⁻¹' S) = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hS hx⟩, hx, rfl⟩
  apply Subgroup.map_subtype_inj.1
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr ((Subgroup.closure_le G).2 hS),
    MonoidHom.map_closure, himg]

private theorem closure_image_conj_eq_normalClosure_geb {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (φ : G₁ →* G₂) (hφ : Function.Surjective φ) (B : Set G₁) :
    Subgroup.closure (φ '' {x : G₁ | ∃ h : G₁, ∃ b ∈ B, h * b * h⁻¹ = x}) =
      Subgroup.normalClosure (φ '' B) := by
  rw [Subgroup.normalClosure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨h, b, hb, rfl⟩, rfl⟩
    rw [Group.mem_conjugatesOfSet_iff]
    exact ⟨φ b, Set.mem_image_of_mem φ hb, by
      rw [isConj_iff]
      exact ⟨φ h, by rw [map_mul, map_mul, map_inv]⟩⟩
  · intro hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ⟨b, hb, rfl⟩, hc⟩ := hx
    rw [isConj_iff] at hc
    obtain ⟨d, rfl⟩ := hc
    obtain ⟨h, rfl⟩ := hφ d
    exact ⟨h * b * h⁻¹, ⟨h, b, hb, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩

private theorem gomiBar_conj_inv_geb (G : Subgroup Ω) (g : ↥G) {y : Ω} (hy : y ∈ G)
    (hy' : (g : Ω)⁻¹ * y * (g : Ω) ∈ G) :
    gomiBar G ⟨(g : Ω)⁻¹ * y * (g : Ω), hy'⟩ =
      (gomiBar G g)⁻¹ * gomiBar G ⟨y, hy⟩ * (gomiBar G g) := by
  have h : (⟨(g : Ω)⁻¹ * y * (g : Ω), hy'⟩ : ↥G) = g⁻¹ * ⟨y, hy⟩ * g :=
    Subtype.ext rfl
  rw [h, map_mul, map_mul, map_inv]

theorem gomiBar_surjective (G : Subgroup Ω) : Function.Surjective (gomiBar G) :=
  CFSG.CGT.PushingUpLit.BHS6.actOnRange_surjective (gomiV G) G (gomiV_moduleSetting G).2

theorem gomiBar_ker (G : Subgroup Ω) :
    (gomiBar G).ker = (Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf G := by
  rw [show gomiBar G = CFSG.CGT.PushingUpLit.BHS6.actOnRange (gomiV G) G
      (gomiV_moduleSetting G).2 from rfl,
    CFSG.CGT.PushingUpLit.BHS6.ker_actOnRange, Subgroup.inf_subgroupOf_left]

theorem gomiBarOf_eq_map {G K : Subgroup Ω} (hKG : K ≤ G) :
    gomiBarOf G K = (K.subgroupOf G).map (gomiBar G) := by
  ext φ
  rw [gomiBarOf, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · intro hφ
    obtain ⟨x, hx, hxK, hconj⟩ := AutOn.mem_autOn_iff_exists.1 hφ
    refine ⟨⟨x, hKG hxK⟩, hxK, ?_⟩
    apply Subtype.ext
    change conjAct (gomiV G) (Subgroup.inclusion (gomiV_moduleSetting G).2
      ⟨x, hKG hxK⟩) = (φ : MulAut (gomiV G))
    rw [show Subgroup.inclusion (gomiV_moduleSetting G).2 ⟨x, hKG hxK⟩ = ⟨x, hx⟩ from
      Subtype.ext rfl]
    exact hconj
  · rintro ⟨y, hy, rfl⟩
    exact AutOn.conjAct_mem_autOn (Subgroup.inclusion (gomiV_moduleSetting G).2 y) hy

theorem gomiBarOf_gomiBarPre (G : Subgroup Ω) (M : Subgroup ↥(autOn G (gomiV G))) :
    gomiBarOf G (gomiBarPre G M) = M := by
  rw [gomiBarOf_eq_map (show gomiBarPre G M ≤ G from Subgroup.map_subtype_le _)]
  have h : (gomiBarPre G M).subgroupOf G = M.comap (gomiBar G) := by
    unfold gomiBarPre
    exact Subgroup.comap_map_eq_self_of_injective G.subtype_injective _
  rw [h]
  exact Subgroup.map_comap_eq_self_of_surjective (gomiBar_surjective G) M

theorem gomiBarPre_le (G : Subgroup Ω) (M : Subgroup ↥(autOn G (gomiV G))) :
    gomiBarPre G M ≤ G :=
  Subgroup.map_subtype_le _

theorem pCoreOf_le_gomiBarPre (G : Subgroup Ω) (M : Subgroup ↥(autOn G (gomiV G))) :
    pCoreOf 2 G ≤ gomiBarPre G M := by
  have hCV : pCoreOf 2 G ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
    rw [Subgroup.le_centralizer_iff]
    calc gomiV G = omegaOneCenterOf (pCoreOf 2 G) := rfl
      _ ≤ centerOf (pCoreOf 2 G) := (Subgroup.closure_le (centerOf (pCoreOf 2 G))).2
          fun _ hx => hx.1
      _ ≤ Subgroup.centralizer (pCoreOf 2 G) := inf_le_right
  intro x hx
  rw [gomiBarPre, Subgroup.mem_map]
  refine ⟨⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 G hx⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  have hker : ⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 G hx⟩ ∈ (gomiBar G).ker := by
    rw [gomiBar_ker, Subgroup.mem_subgroupOf]
    exact hCV hx
  rw [MonoidHom.mem_ker] at hker
  rw [hker]
  exact M.one_mem

theorem relIndex_gomiBarPre (G : Subgroup Ω) (M : Subgroup ↥(autOn G (gomiV G))) :
    (gomiBarPre G M).relIndex G = M.index := by
  change ((gomiBarPre G M).subgroupOf G).index = M.index
  have h : (gomiBarPre G M).subgroupOf G = M.comap (gomiBar G) := by
    unfold gomiBarPre
    exact Subgroup.comap_map_eq_self_of_injective G.subtype_injective _
  rw [h]
  exact Subgroup.index_comap_of_surjective (f := gomiBar G) (H := M) (gomiBar_surjective G)

theorem gomiBarOf_conjClosure {G B : Subgroup Ω} (hBG : B ≤ G) :
    gomiBarOf G (conjClosure B G) =
      Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) := by
  have hKG : conjClosure B G ≤ G :=
    conjClosure_le fun h hh z hz => G.mul_mem (G.mul_mem hh (hBG hz)) (G.inv_mem hh)
  rw [gomiBarOf_eq_map hKG, gomiBarOf_eq_map hBG]
  have hS : {x : Ω | ∃ h ∈ G, ∃ z ∈ B, h * z * h⁻¹ = x} ⊆ G := by
    rintro x ⟨h, hh, z, hz, rfl⟩
    exact G.mul_mem (G.mul_mem hh (hBG hz)) (G.inv_mem hh)
  have hset : G.subtype ⁻¹' {x : Ω | ∃ h ∈ G, ∃ z ∈ B, h * z * h⁻¹ = x} =
      {x : ↥G | ∃ h : ↥G, ∃ b : ↥G, b ∈ B.subgroupOf G ∧ h * b * h⁻¹ = x} := by
    ext x
    constructor
    · rintro ⟨h, hh, z, hz, hzx⟩
      exact ⟨⟨h, hh⟩, ⟨z, hBG hz⟩, Subgroup.mem_subgroupOf.mpr hz, Subtype.ext hzx⟩
    · rintro ⟨h, b, hb, hbx⟩
      exact ⟨h.1, h.2, b.1, Subgroup.mem_subgroupOf.mp hb, congrArg Subtype.val hbx⟩
  have h1 : (conjClosure B G).subgroupOf G =
      Subgroup.closure {x : ↥G | ∃ h : ↥G, ∃ b : ↥G, b ∈ B.subgroupOf G ∧ h * b * h⁻¹ = x} := by
    rw [conjClosure, subgroupOf_closure_subtype_geb hS, hset]
  rw [h1, MonoidHom.map_closure]
  exact closure_image_conj_eq_normalClosure_geb (gomiBar G) (gomiBar_surjective G)
    (B.subgroupOf G : Set ↥G)

theorem gomiBarPre_map_conj (G : Subgroup Ω) (M : Subgroup ↥(autOn G (gomiV G))) (g : ↥G) :
    gomiBarPre G (M.map (MulAut.conj (gomiBar G g)).toMonoidHom) =
      (gomiBarPre G M).map (MulAut.conj (g : Ω)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [mem_gomiBarPre_geb] at hx
    obtain ⟨hxG, hxM⟩ := hx
    rw [Subgroup.mem_map_equiv, mem_gomiBarPre_geb, MulAut.conj_symm_apply]
    refine ⟨G.mul_mem (G.mul_mem (G.inv_mem g.2) hxG) g.2, ?_⟩
    rw [gomiBar_conj_inv_geb (y := x) G g hxG
      (G.mul_mem (G.mul_mem (G.inv_mem g.2) hxG) g.2)]
    rw [Subgroup.mem_map_equiv] at hxM
    rw [MulAut.conj_symm_apply] at hxM
    exact hxM
  · intro hx
    rw [Subgroup.mem_map_equiv] at hx
    rw [mem_gomiBarPre_geb] at hx
    obtain ⟨hyG, hyM⟩ := hx
    simp only [MulAut.conj_symm_apply] at hyG hyM
    rw [mem_gomiBarPre_geb]
    have hxG : x ∈ G := by
      have h : x = (g : Ω) * ((g : Ω)⁻¹ * x * (g : Ω)) * (g : Ω)⁻¹ := by group
      rw [h]
      exact G.mul_mem (G.mul_mem g.2 hyG) (G.inv_mem g.2)
    refine ⟨hxG, ?_⟩
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [gomiBar_conj_inv_geb (y := x) G g hxG hyG] at hyM
    exact hyM

theorem commutator_le_pCoreOf_of_gomiBarOf {G K L : Subgroup Ω}
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) (hKG : K ≤ G)
    (hLG : L ≤ G) (h : ⁅gomiBarOf G K, gomiBarOf G L⁆ = ⊥) : ⁅K, L⁆ ≤ pCoreOf 2 G := by
  rw [Subgroup.commutator_le]
  intro k hk l hl
  have hkG : k ∈ G := hKG hk
  have hlG : l ∈ G := hLG hl
  have hk' : gomiBar G ⟨k, hkG⟩ ∈ gomiBarOf G K := by
    rw [gomiBarOf_eq_map hKG, Subgroup.mem_map]
    exact ⟨⟨k, hkG⟩, hk, rfl⟩
  have hl' : gomiBar G ⟨l, hlG⟩ ∈ gomiBarOf G L := by
    rw [gomiBarOf_eq_map hLG, Subgroup.mem_map]
    exact ⟨⟨l, hlG⟩, hl, rfl⟩
  have hcomm1 : ⁅gomiBar G ⟨k, hkG⟩, gomiBar G ⟨l, hlG⟩⁆ = 1 := by
    have hmem := Subgroup.commutator_mem_commutator hk' hl'
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  have hcommG : ⁅k, l⁆ ∈ G := by
    rw [commutatorElement_def]
    exact G.mul_mem (G.mul_mem (G.mul_mem hkG hlG) (G.inv_mem hkG)) (G.inv_mem hlG)
  have hker : (⟨⁅k, l⁆, hcommG⟩ : ↥G) ∈ (gomiBar G).ker := by
    rw [MonoidHom.mem_ker]
    have h2 : (⟨⁅k, l⁆, hcommG⟩ : ↥G) =
        ⁅(⟨k, hkG⟩ : ↥G), (⟨l, hlG⟩ : ↥G)⁆ := Subtype.ext rfl
    rw [h2, map_commutatorElement, hcomm1]
  have hcent : ⁅k, l⁆ ∈ Subgroup.centralizer (gomiV G : Set Ω) := by
    have hker' : (⟨⁅k, l⁆, hcommG⟩ : ↥G) ∈
        (Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf G := by
      rw [← gomiBar_ker]
      exact hker
    exact Subgroup.mem_subgroupOf.mp hker'
  have hboth : ⁅k, l⁆ ∈ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := ⟨hcommG, hcent⟩
  rwa [hCQ] at hboth

end CFSG.GroupTheory
