module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.GlueLib
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

namespace Std4r1

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem comp_rigid (h : Std4r1 G z S K F) : IsRigidRankOneComp z K := by
  have : K ∈ {K' | IsRigidRankOneComp z K'} := by rw [h.comps]; exact Set.mem_singleton K
  exact this

theorem comp_isPCompIn (h : Std4r1 G z S K F) : IsPCompIn 2 (centralizer ({z} : Set G)) K :=
  h.comp_rigid.1.1.2.2

theorem comp_pRank (h : Std4r1 G z S K F) : pRank 2 ↥K = 1 := h.comp_rigid.2

theorem orderOf_z (h : Std4r1 G z S K F) : orderOf z = 2 := h.classical.1

theorem z_sq (h : Std4r1 G z S K F) : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two h.orderOf_z

theorem z_ne (h : Std4r1 G z S K F) : z ≠ 1 := ne_one_of_orderOf_eq_two h.orderOf_z

theorem rigidProduct_eq (h : Std4r1 G z S K F) : rigidProduct z = K := by
  unfold rigidProduct; rw [h.comps, sSup_singleton]

theorem Pz_eq (h : Std4r1 G z S K F) : Pz S z = S ⊓ K := by
  unfold Pz; rw [h.rigidProduct_eq]

theorem Qz_eq (h : Std4r1 G z S K F) : Qz S z = S ⊓ cSec K := by
  unfold Qz rigidSectionCentralizer; rw [h.rigidProduct_eq]; rfl

theorem Rz_eq (h : Std4r1 G z S K F) : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := by
  unfold Rz; rw [h.Pz_eq, h.Qz_eq]

theorem K_le_C (h : Std4r1 G z S K F) : K ≤ centralizer ({z} : Set G) := h.comp_isPCompIn.1

theorem syl_C (h : Std4r1 G z S K F) : M.Syl2In S (centralizer ({z} : Set G)) :=
  syl2In_of_isSylowOf h.sylow

theorem S_le_C (h : Std4r1 G z S K F) : S ≤ centralizer ({z} : Set G) := h.syl_C.1

theorem S_pgroup (h : Std4r1 G z S K F) : IsPGroup 2 ↥S := h.syl_C.2.1

theorem z_cent (h : Std4r1 G z S K F) {s : G} (hs : s ∈ S) : z * s = s * z :=
  (Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hs)).symm

theorem z_mem_S (h : Std4r1 G z S K F) : z ∈ S := by
  obtain ⟨P', hP', hzP'⟩ := M.exists_syl2In_ge (M.isPGroup_zpowers_of_sq h.z_sq h.z_ne)
    (zpowers_le.2 (M.z_mem_centralizer (z := z)))
  obtain ⟨c, hc, hcP⟩ := h.syl_C.exists_conj hP'
  have hzP : z ∈ P' := hzP' (mem_zpowers z)
  rw [hcP, M.mem_cj] at hzP
  have : c * z * c⁻¹ = z := by rw [M.centralizer_comm hc]; group
  rwa [this] at hzP

theorem S_top (h : Std4r1 G z S K F) : M.Syl2In S ⊤ := by
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  exact sTop_of_clause_d h.syl_C hcl.2.2.2.1

theorem cmap_eq (h : Std4r1 G z S K F) {c : G} (hc : c ∈ centralizer ({z} : Set G)) :
    cmap c K = K := by
  have h1 : IsRigidRankOneComp z (cmap c K) := isRigidRankOneComp_cmap h.comp_rigid hc
  have h2 : cmap c K ∈ {K' | IsRigidRankOneComp z K'} := h1
  rw [h.comps] at h2
  exact h2

theorem S_normalizes (h : Std4r1 G z S K F) {s : G} (hs : s ∈ S) : s ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  have h1 := h.cmap_eq (h.S_le_C (S.inv_mem hs))
  have h2 : x ∈ cmap s⁻¹ K ↔ s⁻¹⁻¹ * x * s⁻¹ ∈ K := mem_cmap
  rw [h1, inv_inv] at h2
  exact h2

theorem P_norm (h : Std4r1 G z S K F) {s : G} (hs : s ∈ S) {p : G} (hp : p ∈ S ⊓ K) :
    s * p * s⁻¹ ∈ S ⊓ K :=
  ⟨S.mul_mem (S.mul_mem hs hp.1) (S.inv_mem hs),
    (mem_normalizer_iff.1 (h.S_normalizes hs) p).1 hp.2⟩

theorem Q_norm (h : Std4r1 G z S K F) {s : G} (hs : s ∈ S) {q : G} (hq : q ∈ S ⊓ cSec K) :
    s * q * s⁻¹ ∈ S ⊓ cSec K :=
  ⟨S.mul_mem (S.mul_mem hs hq.1) (S.inv_mem hs), cSec_conj K (h.S_normalizes hs) hq.2⟩

theorem O_odd_core (_h : Std4r1 G z S K F) : M.IsOddCore K (pPrimeCoreOf 2 K) :=
  isOddCore_pPrimeCoreOf K

theorem S_inf_O (h : Std4r1 G z S K F) : S ⊓ pPrimeCoreOf 2 K = ⊥ :=
  M.inf_eq_bot_of_pgroup_odd h.S_pgroup h.O_odd_core.odd

theorem comm_PQ (h : Std4r1 G z S K F) {p q : G} (hp : p ∈ S ⊓ K) (hq : q ∈ S ⊓ cSec K) :
    p * q = q * p := by
  have hc : ⁅p, q⁆ ∈ pPrimeCoreOf 2 K := hq.2.2.2 p hp.2
  have hS : ⁅p, q⁆ ∈ S := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp.1 hq.1) (inv_mem hp.1)) (inv_mem hq.1)
  have h1 : ⁅p, q⁆ ∈ S ⊓ pPrimeCoreOf 2 K := ⟨hS, hc⟩
  rw [h.S_inf_O, Subgroup.mem_bot, commutatorElement_def] at h1
  calc p * q = (p * q * p⁻¹ * q⁻¹) * (q * p) := by group
    _ = q * p := by rw [h1, one_mul]

theorem inv_zStarK (h : Std4r1 G z S K F) {w : G} (hw : w ∈ zStar K) (hw2 : w * w = 1) :
    w = 1 ∨ w = z := by
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  right
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  have hb : CFSG.ABGLocalTools.IsSylowOf 2 (zpowers z) (zStar K) := by
    have := hcl.2.1
    rwa [h.rigidProduct_eq] at this
  have hb' : M.Syl2In (zpowers z) (zStar K) := syl2In_of_isSylowOf hb
  obtain ⟨W, hW, hwW⟩ := M.exists_syl2In_ge (M.isPGroup_zpowers_of_sq hw2 hw1)
    (zpowers_le.2 hw : zpowers w ≤ zStar K)
  obtain ⟨c, hc, hcW⟩ := hb'.exists_conj hW
  have hcC : c ∈ centralizer ({z} : Set G) := h.K_le_C hc.1
  have hwW' : w ∈ W := hwW (mem_zpowers w)
  rw [hcW, M.cj_zpowers_of_comm h.z_sq (M.centralizer_comm hcC)] at hwW'
  rcases (M.mem_zpowers_of_sq h.z_sq).1 hwW' with h1 | h1
  · exact absurd h1 hw1
  · exact h1

theorem S_inf_zStar (h : Std4r1 G z S K F) (hII : II4_4_4_center) :
    S ⊓ zStar K = zpowers z ∧ z ∈ K := by
  obtain ⟨hcard, -⟩ := hII G h.simple z h.orderOf_z S K h.sylow h.comp_isPCompIn h.comp_pRank
  have hex : ∃ w ∈ S ⊓ zStar K, w ≠ 1 := by
    by_contra hne
    push Not at hne
    have : S ⊓ zStar K = ⊥ := by
      rw [eq_bot_iff]; intro x hx; exact (Subgroup.mem_bot).2 (hne x hx)
    rw [this] at hcard
    simp at hcard
  obtain ⟨w, hw, hw1⟩ := hex
  have hw2 : w * w = 1 := by
    have := pow_card_eq_one' (G := ↥(S ⊓ zStar K)) (x := ⟨w, hw⟩)
    rw [hcard] at this
    have h2 := congrArg Subtype.val this
    simpa [pow_two] using h2
  have hwz : w = z := (h.inv_zStarK hw.2 hw2).resolve_left hw1
  have hzmem : z ∈ S ⊓ zStar K := hwz ▸ hw
  have hle : zpowers z ≤ S ⊓ zStar K := zpowers_le.2 hzmem
  have heq : zpowers z = S ⊓ zStar K := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard, M.card_zpowers_of_sq h.z_sq h.z_ne]
  exact ⟨heq.symm, hzmem.2.1⟩

theorem z_mem_K (h : Std4r1 G z S K F) (hII : II4_4_4_center) : z ∈ K := (h.S_inf_zStar hII).2

theorem z_mem_P (h : Std4r1 G z S K F) (hII : II4_4_4_center) : z ∈ S ⊓ K :=
  ⟨h.z_mem_S, h.z_mem_K hII⟩

theorem z_mem_Q (h : Std4r1 G z S K F) (hII : II4_4_4_center) : z ∈ S ⊓ cSec K := by
  have : z ∈ S ⊓ zStar K := by rw [(h.S_inf_zStar hII).1]; exact mem_zpowers z
  exact ⟨this.1, this.2.2⟩

theorem PQ_inf (h : Std4r1 G z S K F) (hII : II4_4_4_center) {x : G} (hxP : x ∈ S ⊓ K)
    (hxQ : x ∈ S ⊓ cSec K) : x = 1 ∨ x = z := by
  have : x ∈ S ⊓ zStar K := ⟨hxP.1, hxP.2, hxQ.2⟩
  rw [(h.S_inf_zStar hII).1] at this
  exact (M.mem_zpowers_of_sq h.z_sq).1 this

theorem P_inv (h : Std4r1 G z S K F) (hII : II4_4_4_center) {x : G} (hx : x ∈ S ⊓ K)
    (hx2 : x * x = 1) : x = 1 ∨ x = z := by
  have hcomm : x * z = z * x := M.centralizer_comm (h.K_le_C hx.2)
  rcases rk1_of_pRank_one h.comp_pRank x hx.2 z (h.z_mem_K hII) hx2 h.z_sq hcomm with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd h1 h.z_ne
  · exact Or.inr h1

end Std4r1

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
