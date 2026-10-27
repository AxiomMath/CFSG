module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinAut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsS6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19L2pGen

public section

namespace CFSG.QuasithinUnique.Out21.A6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Unc25K1

section Sylow

theorem mem_D_iff (x : P10) : x ∈ P0 ⊓ A6Models.psl29 ↔ code x ∈ Core.dLit := by
  rw [Subgroup.mem_inf, mem_P0_iff, mem_psl29_iff, Core.d_eq, List.mem_filter]
  simp

theorem surj_D : ∀ c ∈ Core.dLit, ∃ x ∈ P0 ⊓ A6Models.psl29, code x = c := by
  intro c hc
  rw [Core.d_eq] at hc
  obtain ⟨x, hx, rfl⟩ := exists_P0_of_code (List.mem_filter.mp hc).1
  exact ⟨x, (mem_D_iff x).mpr (by rw [Core.d_eq]; exact hc), rfl⟩

theorem dLit_nodup : Core.dLit.Nodup := by
  rw [Core.d_eq]
  exact Core.p0_nodup.filter _

theorem dLit_length : Core.dLit.length = 8 := by decide +kernel

theorem card_D : Nat.card ↥(P0 ⊓ A6Models.psl29) = 8 :=
  (card_eq_of_code_mem dLit_nodup mem_D_iff surj_D).trans dLit_length

theorem factorization_360 : (360 : ℕ).factorization 2 = 3 := by norm_num [Nat.factorization]

theorem isSylowTwoOf_D : IsSylowTwoOf (P0 ⊓ A6Models.psl29) A6Models.psl29 := by
  refine isSylowTwoOf_of_card_eq inf_le_right
    (IsPGroup.of_card (n := 3) (by rw [card_D]; norm_num)) ?_
  rw [card_D, twoPart, card_psl29, factorization_360]
  norm_num

end Sylow

section Certificate

@[expose] def inv2 : P10 := A6Models.perm10 [[0, 6], [1, 2], [3, 9], [7, 8]]

@[expose] def inv3 : P10 := A6Models.perm10 [[1, 2], [3, 6], [4, 8], [5, 7]]

@[expose] def inv4 : P10 := A6Models.perm10 [[0, 9], [1, 2], [4, 7], [5, 8]]

@[expose] def g2 : P10 := A6Models.perm10 [[1, 3, 2, 6], [4, 5, 8, 7]]

@[expose] def g17 : P10 := A6Models.perm10 [[0, 6], [1, 8], [2, 7], [4, 5]]

theorem inv2_mem : inv2 ∈ P0 ⊓ A6Models.psl29 := by
  rw [Subgroup.mem_inf, mem_P0_iff, mem_psl29_iff]
  constructor <;> decide +kernel

theorem inv3_mem : inv3 ∈ P0 ⊓ A6Models.psl29 := by
  rw [Subgroup.mem_inf, mem_P0_iff, mem_psl29_iff]
  constructor <;> decide +kernel

theorem inv4_mem : inv4 ∈ P0 ⊓ A6Models.psl29 := by
  rw [Subgroup.mem_inf, mem_P0_iff, mem_psl29_iff]
  constructor <;> decide +kernel

theorem inv2_sq : inv2 * inv2 = 1 := by decide

theorem inv3_sq : inv3 * inv3 = 1 := by decide

theorem inv4_sq : inv4 * inv4 = 1 := by decide

theorem inv2_ne : inv2 ≠ 1 := by decide

theorem inv3_ne : inv3 ≠ 1 := by decide

theorem inv4_ne : inv4 ≠ 1 := by decide

theorem g2_mem : g2 ∈ A6Models.psl29 := by
  rw [mem_psl29_iff]
  decide +kernel

theorem g17_mem : g17 ∈ A6Models.psl29 := by
  rw [mem_psl29_iff]
  decide +kernel

theorem tSq_mem : A6Models.tSq ∈ A6Models.psl29 := by
  rw [mem_psl29_iff]
  decide +kernel

theorem tInv_mem : A6Models.tInv ∈ A6Models.psl29 := by
  rw [mem_psl29_iff]
  decide +kernel

theorem g2_comm : g2 * inv3 = inv3 * g2 := by decide

theorem g17_comm : g17 * inv2 = inv2 * g17 := by decide

theorem tSq_comm : A6Models.tSq * inv3 = inv3 * A6Models.tSq := by decide

theorem tInv_comm : A6Models.tInv * inv4 = inv4 * A6Models.tInv := by decide

theorem tAdd_eq : A6Models.tAdd = g2 * g17 * g2 := by decide

theorem psl29_gen {W : Subgroup P10}
    (hW : ∀ a ∈ P0 ⊓ A6Models.psl29, a ≠ 1 → a * a = 1 →
      A6Models.psl29 ⊓ Subgroup.centralizer ({a} : Set P10) ≤ W) : A6Models.psl29 ≤ W := by
  have m2 : g2 ∈ A6Models.psl29 ⊓ Subgroup.centralizer ({inv3} : Set P10) :=
    Subgroup.mem_inf.mpr ⟨g2_mem, Subgroup.mem_centralizer_singleton_iff.mpr g2_comm⟩
  have m17 : g17 ∈ A6Models.psl29 ⊓ Subgroup.centralizer ({inv2} : Set P10) :=
    Subgroup.mem_inf.mpr ⟨g17_mem, Subgroup.mem_centralizer_singleton_iff.mpr g17_comm⟩
  have mSq : A6Models.tSq ∈ A6Models.psl29 ⊓ Subgroup.centralizer ({inv3} : Set P10) :=
    Subgroup.mem_inf.mpr ⟨tSq_mem, Subgroup.mem_centralizer_singleton_iff.mpr tSq_comm⟩
  have mInv : A6Models.tInv ∈ A6Models.psl29 ⊓ Subgroup.centralizer ({inv4} : Set P10) :=
    Subgroup.mem_inf.mpr ⟨tInv_mem, Subgroup.mem_centralizer_singleton_iff.mpr tInv_comm⟩
  have h2 : g2 ∈ W := hW inv3 inv3_mem inv3_ne inv3_sq m2
  have h17 : g17 ∈ W := hW inv2 inv2_mem inv2_ne inv2_sq m17
  have hSq : A6Models.tSq ∈ W := hW inv3 inv3_mem inv3_ne inv3_sq mSq
  have hInv : A6Models.tInv ∈ W := hW inv4 inv4_mem inv4_ne inv4_sq mInv
  have hAdd : A6Models.tAdd ∈ W := by
    rw [tAdd_eq]
    exact W.mul_mem (W.mul_mem h2 h17) h2
  rw [psl29_eq, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ pslGens := hg
  simp only [pslGens, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl
  · exact hAdd
  · exact hSq
  · exact hInv

end Certificate

section Transport

theorem exists_psl29_equiv : Nonempty (↥A6Models.psl29 ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨ψ, hinj, hev, -⟩ := exists_psl_hom
  let ψ' : ↥A6Models.psl29 →* ↥(alternatingGroup (Fin 6)) := ψ.codRestrict _ hev
  have hinj' : Function.Injective ψ' := fun a b h => hinj (congrArg Subtype.val h)
  have hcard : Nat.card ↥(alternatingGroup (Fin 6)) ≤ Nat.card ↥A6Models.psl29 := by
    rw [card_psl29, card_alternatingGroup_fin_six]
  exact ⟨MulEquiv.ofBijective ψ' (hinj'.bijective_of_nat_card_le hcard)⟩

theorem genStmt_of_sylow_model {A : Type} [Group A] [Finite A] {M Q : Subgroup P10}
    (φ : A ≃* ↥M) (hQ : IsSylowTwoOf Q M)
    (hgen : ∀ W : Subgroup P10, (∀ a ∈ Q, a ≠ 1 → a * a = 1 →
      M ⊓ Subgroup.centralizer ({a} : Set P10) ≤ W) → M ≤ W) : GenStmt A := by
  intro D W hD hW
  have : Finite ↥M := Finite.of_equiv A φ.toEquiv
  have hD1 : IsSylowTwoOf (D.map φ.toMonoidHom) ⊤ := isSylowTwoOf_top_map φ hD
  set D₁ : Subgroup P10 := (D.map φ.toMonoidHom).map M.subtype with hD₁
  have hD₁M : D₁ ≤ M := Subgroup.map_subtype_le _
  have hD₁S : IsSylowTwoOf D₁ M := by
    rw [Unc25Small.isSylowTwoOf_subgroupOf_top_iff hD₁M]
    have hsub : D₁.subgroupOf M = D.map φ.toMonoidHom :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    rw [hsub]
    exact hD1
  obtain ⟨g, hgM, hg⟩ := hQ.exists_conj hD₁S
  set W₁ : Subgroup P10 := (W.map φ.toMonoidHom).map M.subtype with hW₁
  have hW₃ : ∀ a ∈ Q, a ≠ 1 → a * a = 1 →
      M ⊓ Subgroup.centralizer ({a} : Set P10) ≤ W₁.comap (MulAut.conj g).toMonoidHom := by
    intro a haQ ha1 ha2 x hx
    have hd₁ : g * a * g⁻¹ ∈ D₁ := by
      rw [hg]
      exact Subgroup.mem_map.mpr ⟨a, haQ, by simp [MulAut.conj_apply]⟩
    obtain ⟨δ, hδ, hδe⟩ := Subgroup.mem_map.mp hd₁
    obtain ⟨d, hdD, rfl⟩ := Subgroup.mem_map.mp hδ
    have hde : ((φ d : ↥M) : P10) = g * a * g⁻¹ := hδe
    have hd1 : d ≠ 1 := by
      intro h1
      rw [h1, map_one] at hde
      have h2 : (1 : P10) = g * a * g⁻¹ := hde
      apply ha1
      have h3 : a = g⁻¹ * (g * a * g⁻¹) * g := by group
      rw [h3, ← h2]
      group
    have hd2 : d ^ 2 = 1 := by
      apply φ.injective
      apply Subtype.ext
      rw [map_pow, map_one]
      show ((φ d : ↥M) : P10) ^ 2 = 1
      rw [hde, pow_two]
      calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    have hxM : x ∈ M := hx.1
    have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hyM : g * x * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM hxM) (M.inv_mem hgM)
    have hcent : φ.symm ⟨g * x * g⁻¹, hyM⟩ ∈ Subgroup.centralizer ({d} : Set A) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply φ.injective
      apply Subtype.ext
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      show g * x * g⁻¹ * ((φ d : ↥M) : P10) = ((φ d : ↥M) : P10) * (g * x * g⁻¹)
      rw [hde]
      calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
        _ = g * (a * x) * g⁻¹ := by rw [hxa]
        _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
    have hmemW := hW d hdD hd1 hd2 hcent
    show (MulAut.conj g) x ∈ W₁
    rw [MulAut.conj_apply]
    exact Subgroup.mem_map.mpr ⟨⟨g * x * g⁻¹, hyM⟩,
      Subgroup.mem_map.mpr ⟨φ.symm ⟨g * x * g⁻¹, hyM⟩, hmemW, by simp⟩, rfl⟩
  have hM := hgen _ hW₃
  rw [eq_top_iff]
  intro a _
  have haM : ((φ a : ↥M) : P10) ∈ M := (φ a).2
  have hz : g⁻¹ * ((φ a : ↥M) : P10) * g ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hgM) haM) hgM
  have h1 := hM hz
  have h2 : g * (g⁻¹ * ((φ a : ↥M) : P10) * g) * g⁻¹ ∈ W₁ := h1
  have h3 : g * (g⁻¹ * ((φ a : ↥M) : P10) * g) * g⁻¹ = ((φ a : ↥M) : P10) := by group
  rw [h3] at h2
  obtain ⟨δ, hδ, hδe⟩ := Subgroup.mem_map.mp h2
  obtain ⟨w, hwW, rfl⟩ := Subgroup.mem_map.mp hδ
  have : (φ w : ↥M) = φ a := Subtype.ext hδe
  have hwa : w = a := φ.injective this
  rw [← hwa]
  exact hwW

end Transport

theorem a6Gen {G : Type} [Group G] [Finite G] {X D : Subgroup G}
    (e : ↥X ≃* alternatingGroup (Fin 6)) (hD : IsSylowTwoOf D X) {W : Subgroup G}
    (hW : ∀ a ∈ D, a ≠ 1 → a ^ 2 = 1 → X ⊓ Subgroup.centralizer ({a} : Set G) ≤ W) :
    X ≤ W := by
  obtain ⟨ψ⟩ := exists_psl29_equiv
  have hgen : GenStmt ↥X := genStmt_of_sylow_model (e.trans ψ.symm) isSylowTwoOf_D fun _ hW => psl29_gen hW
  have hD' := isSylowTwoOf_top_of_subgroupOf hD
  have hW' : ∀ a ∈ D.subgroupOf X, a ≠ 1 → a ^ 2 = 1 →
      Subgroup.centralizer ({a} : Set ↥X) ≤ W.comap X.subtype := by
    intro a ha ha1 ha2 y hy
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hcomm : (y : G) ∈ X ⊓ Subgroup.centralizer ({(a : G)} : Set G) :=
      ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hy')⟩
    exact hW (a : G) (Subgroup.mem_subgroupOf.mp ha) (fun h => ha1 (Subtype.ext h))
      (by simpa using congrArg Subtype.val ha2) hcomm
  have htop := hgen (D.subgroupOf X) (W.comap X.subtype) hD' hW'
  intro x hx
  have : (⟨x, hx⟩ : ↥X) ∈ W.comap X.subtype := by
    rw [htop]
    exact Subgroup.mem_top _
  exact this

end CFSG.QuasithinUnique.Out21.A6
