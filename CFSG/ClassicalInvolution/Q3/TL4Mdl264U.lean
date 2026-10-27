module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl264UA
public import CFSG.ClassicalInvolution.Q3.TL4Mdl264R
public import CFSG.LieType.Multipliers.U43

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

namespace U264

theorem card_inf_comap {S G : Type*} [Group S] [Group G] {φ : S →* G}
    (hφ : Function.Injective φ) (C : Subgroup S) {Q : Subgroup G} (hQ : Q ≤ φ.range) :
    Nat.card ↥(C ⊓ Q.comap φ) = Nat.card ↥(C.map φ ⊓ Q) := by
  rw [← Subgroup.card_map_of_injective hφ, Subgroup.map_inf_eq _ _ φ hφ, Subgroup.map_comap_eq,
    inf_of_le_right hQ]

theorem exists_conj_of_mem_range {S G : Type} [Group S] [Group G] (φ : S →* G) {A : Subgroup S}
    {K₀ : Subgroup G} {g h : G} (hg : g ∈ φ.range) (hh : h ∈ φ.range)
    (hK : conjSub g (A.map φ) = K₀) :
    ∃ C ∈ CoreAssembly.conjClass A, C.map φ = conjSub h K₀ := by
  obtain ⟨y, hy⟩ := φ.range.mul_mem hh hg
  refine ⟨conjSub y A, ⟨y, rfl⟩, ?_⟩
  rw [Asc77.AscQuot.map_conjSub, hy, conjSub_mul, hK]

end U264

theorem threeOver2Om3_of_psu43 :
    ∀ (S : Type) [Group S] [Finite S], LieModel S .PSU 4 3 1 → ThreeOver2Om3 S := by
  intro S _ _ hS A B r hA _ _
  obtain ⟨e₀⟩ := LieType.Multipliers.U43.nonempty_mulEquiv_X₀ hS
  set θ : S ≃* ↥P := e₀.trans psiEquiv with hθ
  set φ : S →* Equiv.Perm (Fin 820) := P.subtype.comp θ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Subtype.val_injective.comp θ.injective
  have hφr : φ.range = P := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (θ y).2
    · intro hx
      exact ⟨θ.symm ⟨x, hx⟩, by simp [hφdef]⟩
  have hd := Vtx.ambientQuatDatum_map φ hφ hA
  rw [hφr] at hd
  obtain ⟨g, hgP, hgr, hgK⟩ := exists_conj_K0 hd
  have hu : IsUniqueInvolution K0 r0P := by
    rw [← hgK, ← hgr]
    exact hd.inv.conj g
  obtain ⟨h10, h20, h21, c0, c1, c2⟩ := U264.three_over_P2 hu
  have hg : g ∈ φ.range := by rw [hφr]; exact hgP
  obtain ⟨C₀, hC₀, hC₀K⟩ := U264.exists_conj_of_mem_range φ hg (φ.range.one_mem) hgK
  obtain ⟨C₁, hC₁, hC₁K⟩ := U264.exists_conj_of_mem_range φ hg
    (by rw [hφr]; exact P.inv_mem mem_P.2.2.2.2.2.1) hgK
  obtain ⟨C₂, hC₂, hC₂K⟩ := U264.exists_conj_of_mem_range φ hg
    (by rw [hφr]; exact U264.wP_mem) hgK
  rw [conjSub_one] at hC₀K
  rw [← U264.K1_eq] at hC₁K
  have hC₂K' : C₂.map φ = U264.K2 := hC₂K
  have hP2 : U264.P2 ≤ φ.range := by rw [hφr]; exact U264.P2_le_P
  refine ⟨C₀, hC₀, C₁, hC₁, C₂, hC₂, fun h => h10 ?_, fun h => h20 ?_, fun h => h21 ?_,
    U264.P2.comap φ, U264.isPGroup_P2.comap_of_injective φ hφ, ?_, ?_, ?_⟩
  · rw [← hC₀K, ← hC₁K, h]
  · rw [← hC₀K, ← hC₂K', h]
  · rw [← hC₁K, ← hC₂K', h]
  · rw [U264.card_inf_comap hφ C₀ hP2, hC₀K]
    exact c0
  · rw [U264.card_inf_comap hφ C₁ hP2, hC₁K]
    exact c1
  · rw [U264.card_inf_comap hφ C₂ hP2, hC₂K']
    exact c2

end CFSG.ClassicalInvolution.Q3.TL4
