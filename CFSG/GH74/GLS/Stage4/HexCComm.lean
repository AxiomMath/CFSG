module

public import CFSG.GH74.GLS.Stage4.HexCData
public import CFSG.GH74.GLS.Stage4.HexCV24

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F : Type} [Field F]

structure CommData (D : HexData root F) (a2 a4 : F → F → F) (L : F → F → G) : Prop where
  L_mem : ∀ s t, L s t ∈ root 3
  eq : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = D.p2 (a2 s t) * L s t * D.p4 (a4 s t)

section Comm

variable (R : RGD2 6 H r₁ r₂ U root) (D : HexData root F)

include R in
theorem comm15_mem (s t : F) : ⁅D.p1 s, D.p5 t⁆ ∈ Vsub root 2 4 := by
  have h := rgd2_octComm R 1 5 (by norm_num) (by norm_num) (by norm_num) _ (D.p1_mem s) _
    (D.p5_mem t)
  refine (iSup₂_le (fun k hk => ?_) : (⨆ k ∈ Set.Ioo (1 : ℤ) 5, root k) ≤ Vsub root 2 4) h
  have := Set.mem_Ioo.1 hk
  exact root_le_Vsub (by omega) (by omega)

include R in
theorem exists_commData : ∃ (a2 a4 : F → F → F) (L : F → F → G), CommData D a2 a4 L := by
  classical
  have h : ∀ s t, ∃ a ∈ root 2, ∃ u ∈ root 3, ∃ b ∈ root 4,
      ⁅D.p1 s, D.p5 t⁆ = a * u * b := fun s t => V24_decomp R (comm15_mem R D s t)
  choose a ha u hu b hb he using h
  have hA : ∀ s t, ∃ e, D.p2 e = a s t := fun s t => D.p2_surj _ (ha s t)
  have hB : ∀ s t, ∃ e, D.p4 e = b s t := fun s t => D.p4_surj _ (hb s t)
  choose a2 ha2 using hA
  choose a4 ha4 using hB
  refine ⟨a2, a4, u, ⟨hu, fun s t => ?_⟩⟩
  rw [ha2, ha4]
  exact he s t

end Comm

end CFSG.GH74.GLS.Stage4.Hex
