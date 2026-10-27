module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveCen

public section

namespace CFSG.QuasithinUnique.Lin2.Exam

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

section Generic

variable {G : Type*} [Group G]

theorem conjR_centralizer_of_comm {s x : G} (hxs : x * s = s * x) :
    conjR (Subgroup.centralizer ({s} : Set G)) x = Subgroup.centralizer ({s} : Set G) :=
  conjR_eq_of_mem_normalizer
    (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hxs))

theorem conjR_inf_centralizer_of_comm (X : Subgroup G) {s x : G} (hxs : x * s = s * x) :
    conjR (X ⊓ Subgroup.centralizer ({s} : Set G)) x =
      conjR X x ⊓ Subgroup.centralizer ({s} : Set G) := by
  rw [conjR_inf, conjR_centralizer_of_comm hxs]

theorem exam_blockZ_conjR (X : Subgroup G) (g : G) :
    blockZ (conjR X g) = conjR (blockZ X) g :=
  blockZ_map_equiv (MulAut.conj g⁻¹) X

theorem exam_blockU_conj {s x : G} (hxs : x * s = s * x) (L : Subgroup G)
    (hUs : blockU L ⊓ Subgroup.centralizer ({s} : Set G) =
      blockU (L ⊓ Subgroup.centralizer ({s} : Set G))) :
    blockU (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) =
      conjR (blockU L) x ⊓ Subgroup.centralizer ({s} : Set G) := by
  rw [blockU_conjR, ← hUs, conjR_inf_centralizer_of_comm _ hxs]

theorem exam_blockZ_conj {s x : G} (hxs : x * s = s * x) (L : Subgroup G)
    (hZ : blockZ (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      centerOf L ⊓ Subgroup.centralizer ({s} : Set G)) :
    blockZ (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) =
      conjR (centerOf L) x ⊓ Subgroup.centralizer ({s} : Set G) := by
  have h := blockZ_map_equiv (MulAut.conj x⁻¹) (L ⊓ Subgroup.centralizer ({s} : Set G))
  change blockZ (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) =
    conjR (blockZ (L ⊓ Subgroup.centralizer ({s} : Set G))) x at h
  rw [h, hZ, conjR_inf_centralizer_of_comm _ hxs]

end Generic

section Cfg

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem exam_block (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s : G} (hs : s ∈ S)
    (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) (h4 : 4 < 2 ^ n) :
    ∃ m : ℕ, n = 2 * m ∧ 1 < m ∧ IsShort2 (L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
      IsLin2Type (L ⊓ Subgroup.centralizer ({s} : Set G)) m ∧
      blockU L ⊓ Subgroup.centralizer ({s} : Set G) =
        blockU (L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
      pCoreOf 2 (L ⊓ Subgroup.centralizer ({s} : Set G)) =
        blockU L ⊓ Subgroup.centralizer ({s} : Set G) ∧
      IsSylowTwoOf (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G))
        (L ⊓ Subgroup.centralizer ({s} : Set G)) := by
  obtain ⟨hblk, hO, hLs2⟩ := E.block_s hcfg hs hsR hs2
  rcases hblk with ⟨m, hm, hm1, hsh, hlin, hU⟩ | ⟨hn2, -⟩
  · refine ⟨m, hm, hm1, hsh, hlin, hU, hO, ?_⟩
    exact isSylowTwoOf_of_card_eq
      (inf_le_inf_right _ (E.Rsyl hcfg).1)
      (hcfg.S_isPGroup.to_le (inf_le_left.trans (thompsonJ_le_self S))) hLs2.symm
  · exfalso
    subst hn2
    norm_num at h4

theorem exam_blockZ (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s : G} (hs : s ∈ S)
    (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) (hc : centerOf L ≠ ⊥) (h4 : 4 < 2 ^ n) {m : ℕ}
    (hm : n = 2 * m) (hsh : IsShort2 (L ⊓ Subgroup.centralizer ({s} : Set G)))
    (hUs : blockU L ⊓ Subgroup.centralizer ({s} : Set G) =
      blockU (L ⊓ Subgroup.centralizer ({s} : Set G)))
    (hO : pCoreOf 2 (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      blockU L ⊓ Subgroup.centralizer ({s} : Set G)) :
    blockZ (L ⊓ Subgroup.centralizer ({s} : Set G)) =
        centerOf L ⊓ Subgroup.centralizer ({s} : Set G) ∧
      Nat.card (blockZ (L ⊓ Subgroup.centralizer ({s} : Set G))) = 2 ^ m := by
  have hZs : blockZ (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      centerOf (L ⊓ Subgroup.centralizer ({s} : Set G)) :=
    blockZ_eq_centerOf hsh.2.1 (hO.trans hUs)
  have hce := Five.centerOf_Ls_eq E hcfg hs hsR hs2 hc h4
  have hz : lin2Z L (thompsonJ S) = centerOf L := by simp [lin2Z, hc]
  have hcard := E.card_Z_inf_centralizer hcfg (Z := lin2Z L (thompsonJ S)) rfl hs hsR hs2
  rw [hz] at hcard
  refine ⟨hZs.trans hce, ?_⟩
  rw [hZs, hce, hcard]
  congr 1
  omega

theorem exam_Us_ne (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s x : G} (hs : s ∈ S)
    (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) (hc : centerOf L ≠ ⊥) (h4 : 4 < 2 ^ n)
    (hxT : x ∈ T) (hxS : x ∉ S) :
    blockU L ⊓ Subgroup.centralizer ({s} : Set G) ≠
      conjR (blockU L) x ⊓ Subgroup.centralizer ({s} : Set G) := by
  intro heq
  have hsub : blockU L ⊓ Subgroup.centralizer ({s} : Set G) ≤
      centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({s} : Set G) := by
    intro u hu
    have hu1 : u ∈ conjR (blockU L) x ⊓ Subgroup.centralizer ({s} : Set G) := heq ▸ hu
    refine Subgroup.mem_inf.mpr ⟨?_, hu.2⟩
    rw [← (E.RUU hcfg hxT hxS).2]
    exact Subgroup.mem_inf.mpr ⟨hu.1, hu1.1⟩
  have hcard := Subgroup.card_le_of_le hsub
  obtain ⟨h21, h22⟩ := (E.U_s_values hcfg hs hsR hs2 hxT hxS).2 hc
  rw [h21, h22] at hcard
  have h5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
  have hn3 := Five.three_le_of_four_lt_two_pow h4
  omega

theorem exam_Rs_eq_sup (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s x : G} (hs : s ∈ S)
    (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) (hxT : x ∈ T) (hxS : x ∉ S) :
    thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) =
      blockU L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
        conjR (blockU L) x ⊓ Subgroup.centralizer ({s} : Set G) := by
  obtain ⟨-, hset, -⟩ := E.U_s_card hcfg hs hsR hs2 hxT hxS
  have hRU := (E.RUU hcfg hxT hxS).1
  have hUR : blockU L ≤ thompsonJ S := by rw [hRU]; exact le_sup_left
  have hVR : conjR (blockU L) x ≤ thompsonJ S := by rw [hRU]; exact le_sup_right
  apply le_antisymm
  · intro r hr
    have hr' : r ∈ ((blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) *
        ((conjR (blockU L) x ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) := by
      rw [hset]; exact hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr'
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hv)
  · exact sup_le (inf_le_inf_right _ hUR) (inf_le_inf_right _ hVR)

theorem exam_Rs_le_conj (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s x : G}
    (hxT : x ∈ T) (hxs : x * s = s * x) :
    thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) ≤
      conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x := by
  have hRx : conjR (thompsonJ S) x = thompsonJ S := conjR_eq_of_mem_normalizer (E.TnR hcfg hxT)
  have h1 : thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) =
      conjR (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)) x := by
    rw [conjR_inf, hRx, conjR_centralizer_of_comm hxs]
  rw [h1]
  exact conjR_mono (inf_le_inf_right _ (E.Rsyl hcfg).1) x

theorem exam_Rs_le (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s : G} :
    thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) ≤ L ⊓ Subgroup.centralizer ({s} : Set G) :=
  inf_le_inf_right _ (E.Rsyl hcfg).1

theorem exam_conjR_Lsx_of_mem (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s x σ : G}
    (hxT : x ∈ T) (hxs : x * s = s * x) (hσS : σ ∈ S) (hσs : σ * s = s * σ) :
    conjR (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) σ =
      conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x := by
  have hσ' : x * σ * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (E.TnS hcfg hxT) σ).mp hσS
  have hxs' : x⁻¹ * s = s * x⁻¹ := Five.comm_inv_of_comm hxs
  have hσ's : (x * σ * x⁻¹) * s = s * (x * σ * x⁻¹) := by
    calc x * σ * x⁻¹ * s = x * σ * (x⁻¹ * s) := by group
      _ = x * σ * (s * x⁻¹) := by rw [hxs']
      _ = x * (σ * s) * x⁻¹ := by group
      _ = x * (s * σ) * x⁻¹ := by rw [hσs]
      _ = (x * s) * σ * x⁻¹ := by group
      _ = (s * x) * σ * x⁻¹ := by rw [hxs]
      _ = s * (x * σ * x⁻¹) := by group
  rw [conjR_conjR]
  have e : x * σ = (x * σ * x⁻¹) * x := by group
  rw [e, ← conjR_conjR, Five.conjR_Ls_eq hcfg hσ' hσ's]

theorem exam_Ss_le_normalizer_Ls (hcfg : Lin2Cfg G T M H S L n D) {s σ : G} (hσS : σ ∈ S)
    (hσs : σ * s = s * σ) :
    σ ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) :=
  conjR_eq_self_iff.mp (Five.conjR_Ls_eq hcfg hσS hσs)

end Cfg

end CFSG.QuasithinUnique.Lin2.Exam
