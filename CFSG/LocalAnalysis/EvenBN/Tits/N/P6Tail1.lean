module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Desc
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Bur

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits.N

variable {G : Type} [Group G] [Finite G]
variable (d : Data G)

theorem star_mem_normalizer_Ws (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) {g : G}
    (hg : g ∈ Hg d) :
    star d g ∈ normalizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) := by
  have hmem : star d g ∈ Hs d := actFun_mem_imgIn hg hg
  refine mem_normalizer_iff.2 fun w => ⟨fun hw => hW _ hmem w hw, fun hw => ?_⟩
  have h1 := hW _ (inv_mem hmem) _ hw
  simpa [mul_assoc] using h1

@[expose] noncomputable def alphaHom (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) :
    ↥(Hg d) →* MulAut ↥(Ws d) :=
  MonoidHom.mk' (fun g => actFun (Ws d) (actFun d.s56V (g : G))) fun a b =>
    alpha_mul a.2 b.2 (star_mem_normalizer_Ws d hW a.2) (star_mem_normalizer_Ws d hW b.2)

theorem mem_Alpha_iff (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) {K : Subgroup G}
    {σ : MulAut ↥(Ws d)} : σ ∈ Alpha d K ↔ ∃ k ∈ K, k ∈ Hg d ∧ alpha d k = σ := by
  constructor
  · intro h
    obtain ⟨a, ha, -, rfl⟩ := (mem_imgIn_iff (Ws d) (img d K)).1 h
    obtain ⟨k, hk, hkN, rfl⟩ := (mem_imgIn_iff d.s56V K).1 ha
    exact ⟨k, hk, hkN, rfl⟩
  · rintro ⟨k, hk, hkH, rfl⟩
    exact actFun_mem_imgIn (actFun_mem_imgIn hk hkH) (star_mem_normalizer_Ws d hW hkH)

theorem alpha_mem_Ialpha (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) {g : G}
    (hg : g ∈ Hg d) : alpha d g ∈ Ialpha d :=
  actFun_mem_imgIn (Subgroup.mem_inf.2 ⟨star_mem_normalizer_Ws d hW hg, actFun_mem_imgIn hg hg⟩)
    (star_mem_normalizer_Ws d hW hg)

theorem exists_alpha_eq_of_mem_Ialpha {i : MulAut ↥(Ws d)} (hi : i ∈ Ialpha d) :
    ∃ g ∈ Hg d, alpha d g = i := by
  obtain ⟨a, ha, -, rfl⟩ := (mem_imgIn_iff (Ws d) (Is d)).1 hi
  obtain ⟨g, -, hgN, rfl⟩ := (mem_imgIn_iff d.s56V (Hg d)).1 (Subgroup.mem_inf.1 ha).2
  exact ⟨g, hgN, rfl⟩

theorem Jg_le_Hg : Jg d ≤ Hg d := Subgroup.map_subtype_le _

theorem Jg_conj_mem {h j : G} (hh : h ∈ Hg d) (hj : j ∈ Jg d) : h * j * h⁻¹ ∈ Jg d := by
  obtain ⟨j', hj', rfl⟩ := hj
  exact ⟨(⟨h, hh⟩ : ↥(Hg d)) * j' * ⟨h, hh⟩⁻¹, Subgroup.normalClosure_normal.conj_mem j' hj' _, rfl⟩

theorem Xg_le_Jg (hX : Xg d ≤ Hg d) : Xg d ≤ Jg d := by
  intro x hx
  exact ⟨⟨x, hX hx⟩, Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem Jg_le_H0 (z₀ : G) (hX : Xg d ≤ H0 d z₀) (hN : ((H0 d z₀).subgroupOf (Hg d)).Normal) :
    Jg d ≤ H0 d z₀ := by
  have h1 : Subgroup.normalClosure (((Xg d).subgroupOf (Hg d) : Subgroup ↥(Hg d)) :
      Set ↥(Hg d)) ≤ (H0 d z₀).subgroupOf (Hg d) :=
    Subgroup.normalClosure_le_normal fun x hx => Subgroup.mem_subgroupOf.2 (hX (Subgroup.mem_subgroupOf.1 hx))
  intro j hj
  obtain ⟨j', hj', rfl⟩ := hj
  exact Subgroup.mem_subgroupOf.1 (h1 hj')

theorem centralizer_le_H0 (z₀ : G) (hZV : Zz d z₀ ≤ d.s56V) :
    centralizer (d.s56V : Set G) ≤ H0 d z₀ := fun c hc =>
  Subgroup.mem_inf.2 ⟨Subgroup.centralizer_le_normalizer _ hc, Subgroup.mem_centralizer_iff.2 fun z hz =>
    Subgroup.mem_centralizer_iff.1 hc z (hZV hz)⟩

theorem x5_mem_H0 (z₀ : G) (hx5H : d.x₅ ∈ Hg d) (hx5 : orderOf d.x₅ = 5)
    (hN : ((H0 d z₀).subgroupOf (Hg d)).Normal) (hidx : (H0 d z₀).relIndex (Hg d) = 2 ∨
      (H0 d z₀).relIndex (Hg d) = 6) : d.x₅ ∈ H0 d z₀ := by
  refine mem_of_pow_mem_of_coprime (a := 5) (b := (H0 d z₀).relIndex (Hg d)) ?_ ?_
    (pow_relIndex_mem_of_normal hx5H)
  · rcases hidx with h | h <;> rw [h] <;> norm_num
  · rw [← hx5, pow_orderOf_eq_one]
    exact (H0 d z₀).one_mem

theorem mem_Jp_iff {g : G} : g ∈ Jp d ↔ g ∈ Hg d ∧ ∃ j ∈ Jg d, j ∈ Hg d ∧ star d j = star d g := by
  constructor
  · intro h
    obtain ⟨hgN, hg⟩ := (mem_preIn_iff d.s56V _).1 h
    obtain ⟨j, hj, hjN, hjg⟩ := (mem_imgIn_iff d.s56V (Jg d)).1 hg
    exact ⟨hgN, j, hj, hjN, hjg⟩
  · rintro ⟨hgH, j, hj, hjN, hjg⟩
    refine (mem_preIn_iff d.s56V _).2 ⟨hgH, ?_⟩
    have h1 := actFun_mem_imgIn (S := d.s56V) hj hjN
    rw [show actFun d.s56V j = actFun d.s56V g from hjg] at h1
    exact h1

theorem Jp_le_Hg : Jp d ≤ Hg d := fun _ h => ((mem_Jp_iff d).1 h).1

theorem Jg_le_Jp : Jg d ≤ Jp d := fun j hj => (mem_Jp_iff d).2 ⟨Jg_le_Hg d hj, j, hj, Jg_le_Hg d hj, rfl⟩

theorem Jp_conj_mem {h g : G} (hh : h ∈ Hg d) (hg : g ∈ Jp d) : h * g * h⁻¹ ∈ Jp d := by
  obtain ⟨hgH, j, hj, hjN, hjg⟩ := (mem_Jp_iff d).1 hg
  refine (mem_Jp_iff d).2 ⟨mul_mem (mul_mem hh hgH) (inv_mem hh), h * j * h⁻¹, Jg_conj_mem d hh hj,
    mul_mem (mul_mem hh hjN) (inv_mem hh), ?_⟩
  show actFun d.s56V (h * j * h⁻¹) = actFun d.s56V (h * g * h⁻¹)
  rw [actFun_conj d.s56V hh hjN, actFun_conj d.s56V hh hgH]
  exact congrArg (fun a => actFun d.s56V h * a * (actFun d.s56V h)⁻¹) hjg

theorem Jp_le_H0 (z₀ : G) (hZV : Zz d z₀ ≤ d.s56V) (hJ : Jg d ≤ H0 d z₀) : Jp d ≤ H0 d z₀ := by
  intro g hg
  obtain ⟨hgH, j, hj, hjN, hjg⟩ := (mem_Jp_iff d).1 hg
  have hc : j⁻¹ * g ∈ centralizer (d.s56V : Set G) :=
    (actFun_eq_iff d.s56V hjN hgH).1 hjg
  have : g = j * (j⁻¹ * g) := by group
  rw [this]
  exact mul_mem (hJ hj) (centralizer_le_H0 d z₀ hZV hc)

theorem alpha_eq_one_of_mem_Wg (z₀ : G) (h19 : img d (Wg d z₀) = Ws d)
    (hWab : IsElemAbelian 2 (Ws d)) {w : G} (hw : w ∈ Wg d z₀) : alpha d w = 1 := by
  have hwN : w ∈ normalizer (d.s56V : Set G) :=
    preIn_le_normalizer d.s56V _ (Subgroup.mem_inf.1 hw).1
  have hmem : star d w ∈ Ws d := h19 ▸ actFun_mem_imgIn hw hwN
  exact actFun_eq_one_of_mem_of_comm (Ws d)
    (fun a ha b hb => P6.mul_comm_of_isElemAbelian hWab ha hb) hmem

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
