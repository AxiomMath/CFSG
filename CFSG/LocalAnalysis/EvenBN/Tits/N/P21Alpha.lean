module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup

variable {G : Type} [Group G] [Finite G]
  {d : Data G}

theorem mem_Ig_iff {g : G} :
    g ∈ Ig d ↔ g ∈ normalizer (d.s56V : Set G) ∧ star d g ∈ Is d :=
  mem_preIn_iff d.s56V (Is d)

theorem Ig_le_Hg (d : Data G) : Ig d ≤ Hg d := fun _ hg => mem_Ig_iff.1 hg |>.1

theorem star_mem_Is {g : G} (hg : g ∈ Ig d) : star d g ∈ Is d := (mem_Ig_iff.1 hg).2

theorem star_mem_normalizer_Ws {g : G} (hg : g ∈ Ig d) :
    star d g ∈ normalizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) :=
  (star_mem_Is hg).1

theorem star_mul_of_mem {g h : G} (hg : g ∈ Hg d) (hh : h ∈ Hg d) :
    star d (g * h) = star d g * star d h :=
  actFun_mul d.s56V hg hh

theorem alpha_one : alpha d 1 = 1 := by
  unfold alpha star
  rw [actFun_one, actFun_one]

theorem alpha_mul {g h : G} (hg : g ∈ Ig d) (hh : h ∈ Ig d) :
    alpha d (g * h) = alpha d g * alpha d h := by
  unfold alpha
  rw [star_mul_of_mem (Ig_le_Hg d hg) (Ig_le_Hg d hh)]
  exact actFun_mul (Ws d) (star_mem_normalizer_Ws hg) (star_mem_normalizer_Ws hh)

theorem alpha_inv {g : G} (hg : g ∈ Ig d) : alpha d g⁻¹ = (alpha d g)⁻¹ := by
  have h1 : alpha d (g * g⁻¹) = alpha d g * alpha d g⁻¹ := alpha_mul hg (inv_mem hg)
  rw [mul_inv_cancel, alpha_one] at h1
  exact (inv_eq_of_mul_eq_one_right h1.symm).symm

theorem alpha_pow {g : G} (hg : g ∈ Ig d) (n : ℕ) : alpha d (g ^ n) = alpha d g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, alpha_one]
  | succ n ih => rw [pow_succ, alpha_mul (pow_mem hg n) hg, ih, pow_succ]

theorem alpha_conj {g h : G} (hg : g ∈ Ig d) (hh : h ∈ Ig d) :
    alpha d (g * h * g⁻¹) = alpha d g * alpha d h * (alpha d g)⁻¹ := by
  rw [alpha_mul (mul_mem hg hh) (inv_mem hg), alpha_mul hg hh, alpha_inv hg]

theorem alpha_mem_Ialpha {g : G} (hg : g ∈ Ig d) : alpha d g ∈ Ialpha d :=
  actFun_mem_imgIn (star_mem_Is hg) (star_mem_normalizer_Ws hg)

theorem exists_alpha_eq {y : MulAut ↥(Ws d)} (hy : y ∈ Ialpha d) : ∃ g ∈ Ig d, alpha d g = y := by
  obtain ⟨k, hkI, hkN, rfl⟩ := (mem_imgIn_iff (Ws d) (Is d)).1 hy
  obtain ⟨-, hkH⟩ := Subgroup.mem_inf.1 hkI
  obtain ⟨g, -, hgN, rfl⟩ := (mem_imgIn_iff d.s56V (Hg d)).1 hkH
  exact ⟨g, mem_Ig_iff.2 ⟨hgN, hkI⟩, rfl⟩

theorem mem_Alpha_iff {K : Subgroup G} (hK : K ≤ Ig d) {y : MulAut ↥(Ws d)} :
    y ∈ Alpha d K ↔ ∃ g ∈ K, alpha d g = y := by
  unfold Alpha img
  rw [mem_imgIn_iff]
  constructor
  · rintro ⟨k, hk, hkN, rfl⟩
    obtain ⟨g, hgK, hgN, rfl⟩ := (mem_imgIn_iff d.s56V K).1 hk
    exact ⟨g, hgK, rfl⟩
  · rintro ⟨g, hgK, rfl⟩
    have hgI := hK hgK
    exact ⟨star d g, actFun_mem_imgIn hgK (mem_Ig_iff.1 hgI).1, star_mem_normalizer_Ws hgI, rfl⟩

theorem Alpha_le_Ialpha {K : Subgroup G} (hK : K ≤ Ig d) : Alpha d K ≤ Ialpha d := by
  intro y hy
  obtain ⟨g, hgK, rfl⟩ := (mem_Alpha_iff hK).1 hy
  exact alpha_mem_Ialpha (hK hgK)

@[expose] noncomputable def alphaHom (d : Data G) : ↥(Ig d) →* ↥(Ialpha d) where
  toFun g := ⟨alpha d g, alpha_mem_Ialpha g.2⟩
  map_one' := Subtype.ext alpha_one
  map_mul' g h := Subtype.ext (alpha_mul g.2 h.2)

theorem alphaHom_coe (g : ↥(Ig d)) :
    ((alphaHom d g : ↥(Ialpha d)) : MulAut ↥(Ws d)) = alpha d g := rfl

theorem alphaHom_surjective (d : Data G) : Function.Surjective (alphaHom d) := by
  rintro ⟨y, hy⟩
  obtain ⟨g, hg, rfl⟩ := exists_alpha_eq hy
  exact ⟨⟨g, hg⟩, rfl⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N
