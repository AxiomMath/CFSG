module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwSetup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5XSwDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwKer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43

private theorem sw_img_gen {Λ : Type} [Group Λ] {τ : Λ →* X₀} {A : Subgroup Λ}
    (hgen : A ≤ Subgroup.closure {a : Λ | a ∈ A ∧ Odd (orderOf a)}) :
    A.map τ ≤ Subgroup.closure {b : X₀ | b ∈ A.map τ ∧ Odd (orderOf b)} := by
  intro b hb
  rw [Subgroup.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  have hcl : a ∈ Subgroup.closure {c : Λ | c ∈ A ∧ Odd (orderOf c)} := hgen ha
  have hmap : τ a ∈ (Subgroup.closure {c : Λ | c ∈ A ∧ Odd (orderOf c)}).map τ :=
    Subgroup.mem_map.mpr ⟨a, hcl, rfl⟩
  rw [MonoidHom.map_closure] at hmap
  exact Subgroup.closure_mono (fun y hy => by
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨Subgroup.mem_map.mpr ⟨c, hc.1, rfl⟩, hc.2.of_dvd_nat (orderOf_map_dvd τ c)⟩) hmap

private theorem sw_img_le_cent {Λ : Type} [Group Λ] {τ : Λ →* X₀} {A : Subgroup Λ} {z : Λ}
    (hz : τ z = xElt) (hcent : A ≤ Subgroup.centralizer ({z} : Set Λ)) :
    A.map τ ≤ SwC := by
  calc A.map τ ≤ (Subgroup.centralizer ({z} : Set Λ)).map τ := Subgroup.map_mono hcent
    _ ≤ Subgroup.centralizer (τ '' ({z} : Set Λ)) :=
        Subgroup.map_centralizer_le_centralizer_image _ τ
    _ = SwC := by rw [Set.image_singleton, hz]

theorem sw_img_conj {Λ : Type} [Group Λ] [Finite Λ] {τ : Λ →* X₀} (hτ : SwCentralTwo τ)
    (hF : SwFinite) {A₁ A₂ : Subgroup Λ} {z : Λ} (S : SwSetup A₁ A₂ z) (hz : τ z = xElt) :
    ∃ c ∈ SwC, CFSG.conjugate (A₁.map τ) c = A₂.map τ := by
  refine hF (A₁.map τ) (A₂.map τ) (Subgroup.mem_map.mpr ⟨z, S.pocket₁.mem, hz⟩)
    (Subgroup.mem_map.mpr ⟨z, S.pocket₂.mem, hz⟩)
    (sw_img_le_cent hz S.pocket₁.le_cent) (sw_img_le_cent hz S.pocket₂.le_cent)
    (sw_img_gen S.pocket₁.gen) (sw_img_gen S.pocket₂.gen) ?_ ?_
  · intro u hu v hv
    rw [Subgroup.mem_map] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    rw [← map_mul, ← map_mul, S.comm a ha b hb]
  · intro o ho hodd
    obtain ⟨õ, hodd', hõ⟩ := hτ.odd_lift hodd
    have hmem : õ ∈ Subgroup.centralizer ({z} : Set Λ) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hτ.odd_comm hodd'
      rw [hõ, hz]
      exact Subgroup.mem_centralizer_singleton_iff.mp ho
    have hjoin : õ ∈ A₁ ⊔ A₂ := S.odd_mem õ hmem hodd'
    rw [← hõ, ← Subgroup.map_sup]
    exact Subgroup.mem_map.mpr ⟨õ, hjoin, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
