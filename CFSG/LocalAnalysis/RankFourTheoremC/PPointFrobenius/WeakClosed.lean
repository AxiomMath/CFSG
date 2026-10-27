module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Ctx

public section

open Subgroup

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_weakly_closed_P (hl : FrobLocal p P M x) {h : G} (hh : h * x * h⁻¹ ∈ (P : Subgroup G)) :
    zpowers (h * x * h⁻¹) = zpowers x := by
  have hg : CFSG.Open.GLBConj h⁻¹ (zpowers x) ≤ (P : Subgroup G) := by
    unfold CFSG.Open.GLBConj
    rw [inv_inv, MonoidHom.map_zpowers, zpowers_le]
    exact hh
  have h1 := hl.weak h⁻¹ hg
  unfold CFSG.Open.GLBConj at h1
  rw [inv_inv, MonoidHom.map_zpowers] at h1
  simpa [MulAut.conj_apply] using h1

theorem fr_weakly_closed [Fact p.Prime] (hl : FrobLocal p P M x) (Q : Sylow p G)
    (hxQ : x ∈ (Q : Subgroup G)) (g : G)
    (hg : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G)) :
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
  have hsylG : ∀ S : Sylow p G, IsSylowOf p (S : Subgroup G) ⊤ := fun S =>
    isSylowOf_iff.2 ⟨le_top, S.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact S.not_dvd_index⟩
  have hQC : (Q : Subgroup G) ≤ centralizer ({x} : Set G) := fun q hq => by
    rw [mem_centralizer_singleton_iff]
    have h := (fr_sylow_abelian hl Q).is_comm.comm ⟨q, hq⟩ ⟨x, hxQ⟩
    have h2 := congrArg Subtype.val h
    exact h2
  obtain ⟨k, hkC, hk⟩ := ((hsylG P).of_le (fr_P_le_centralizer hl) le_top).exists_mem_conj
    ((hsylG Q).of_le hQC le_top)
  have hyQ : g * x * g⁻¹ ∈ (Q : Subgroup G) := by
    have h := hg (mem_map_of_mem (MulAut.conj g).toMonoidHom (mem_zpowers x))
    simpa using h
  have hP : (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ ∈ (P : Subgroup G) := by
    have h := (hk _).mp hyQ
    have he : (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k := by group
    rw [he]
    exact h
  have h1 := fr_weakly_closed_P hl hP
  have hkx : k * x * k⁻¹ = x := by
    rw [mem_centralizer_singleton_iff] at hkC
    rw [hkC, mul_inv_cancel_right]
  have key : ∀ y : G, zpowers (k * y * k⁻¹) = (zpowers y).map (MulAut.conj k).toMonoidHom :=
    fun y => by
      rw [MonoidHom.map_zpowers]
      rfl
  calc (zpowers x).map (MulAut.conj g).toMonoidHom
      = zpowers (k * ((k⁻¹ * g) * x * (k⁻¹ * g)⁻¹) * k⁻¹) := by
        rw [MonoidHom.map_zpowers]
        congr 1
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    _ = (zpowers ((k⁻¹ * g) * x * (k⁻¹ * g)⁻¹)).map (MulAut.conj k).toMonoidHom := key _
    _ = (zpowers x).map (MulAut.conj k).toMonoidHom := by rw [h1]
    _ = zpowers (k * x * k⁻¹) := (key x).symm
    _ = zpowers x := by rw [hkx]

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
