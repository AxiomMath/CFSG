module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenRes
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.ThompsonSchur

public section

namespace CFSG.GroupTheory.AltSevenModule

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6

variable {V : Type} [CommGroup V]

theorem le_stabW_commV (K : Subgroup (MulAut V)) : K ≤ stabW (commV K) := by
  intro g hg
  rw [mem_stabW]
  intro w
  constructor
  · exact apply_mem_commV_of_mem hg w
  · intro hw
    have h := apply_mem_commV_of_mem (Y := K) (inv_mem hg) (g w) hw
    simpa using h

theorem injective_restrictW_commV {K : Subgroup (MulAut V)} [IsSimpleGroup ↥K]
    (hK : ∃ a b : ↥K, a * b ≠ b * a) :
    Function.Injective ((restrictW (commV K)).comp (Subgroup.inclusion (le_stabW_commV K))) := by
  classical
  let r : ↥K →* MulAut ↥(commV K) :=
    (restrictW (commV K)).comp (Subgroup.inclusion (le_stabW_commV K))
  change Function.Injective r
  have hnr : r.ker.Normal := MonoidHom.normal_ker r
  rcases (haveI := hnr; IsSimpleGroup.eq_bot_or_eq_top_of_normal r.ker) with hbot | htop
  · exact (MonoidHom.ker_eq_bot_iff (f := r)).mp hbot
  · exfalso
    have hfix : ∀ (k : ↥K) {w : V}, w ∈ commV K → (k : MulAut V) w = w := by
      intro k w hw
      have hmem : k ∈ r.ker := by rw [htop]; exact Subgroup.mem_top k
      have hr : r k = 1 := MonoidHom.mem_ker.mp hmem
      have h1 : r k ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [hr]; rfl
      have h2 : ((r k ⟨w, hw⟩ : ↥(commV K)) : V) = w := congrArg Subtype.val h1
      change ((restrictW (commV K) (Subgroup.inclusion (le_stabW_commV K) k) ⟨w, hw⟩ :
        ↥(commV K)) : V) = w at h2
      rw [coe_restrictW] at h2
      simpa using h2
    let δ : ↥K →* (V → V) :=
      { toFun := fun k v => (k : MulAut V) v * v⁻¹
        map_one' := by
          funext v
          simp
        map_mul' := by
          intro a b
          funext v
          have hb : (b : MulAut V) v * v⁻¹ ∈ commV K :=
            Subgroup.subset_closure ⟨(b : MulAut V), b.2, v, rfl⟩
          have ha := hfix a hb
          calc ((a * b : ↥K) : MulAut V) v * v⁻¹
              = (a : MulAut V) ((b : MulAut V) v) * v⁻¹ := rfl
            _ = (a : MulAut V) ((b : MulAut V) v * v⁻¹) *
                  ((a : MulAut V) v * v⁻¹) := by
                rw [map_mul, map_inv]
                group
            _ = ((b : MulAut V) v * v⁻¹) * ((a : MulAut V) v * v⁻¹) := by rw [ha]
            _ = ((a : MulAut V) v * v⁻¹) * ((b : MulAut V) v * v⁻¹) := mul_comm _ _ }
    have hnd : δ.ker.Normal := MonoidHom.normal_ker δ
    rcases (haveI := hnd; IsSimpleGroup.eq_bot_or_eq_top_of_normal δ.ker) with hdbot | hdtop
    · have hinj : Function.Injective δ := (MonoidHom.ker_eq_bot_iff (f := δ)).mp hdbot
      obtain ⟨a, b, hab⟩ := hK
      exact hab (hinj (by rw [map_mul, map_mul, mul_comm]))
    · have htriv : ∀ k : ↥K, k = 1 := by
        intro k
        have hmem : k ∈ δ.ker := by rw [hdtop]; exact Subgroup.mem_top k
        have hk : δ k = 1 := MonoidHom.mem_ker.mp hmem
        have hkv : ∀ v : V, (k : MulAut V) v = v := by
          intro v
          have h := congrFun hk v
          change (k : MulAut V) v * v⁻¹ = 1 at h
          exact mul_inv_eq_one.mp h
        refine Subtype.ext (MulEquiv.ext fun v => hkv v)
      obtain ⟨a, b, hab⟩ := hK
      exact hab (by rw [htriv a, htriv b])

end CFSG.GroupTheory.AltSevenModule
