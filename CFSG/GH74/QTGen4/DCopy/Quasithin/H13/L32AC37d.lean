module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC50g

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H V₂ : Subgroup G}

theorem not_isS7NaturalSection_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h2 : Lemma14_7_2_F4) (h4 : Lemma14_7_4_two_three_F4)
    (S : Setting147 G T L V H) (hV2 : A6.IsV2 T V V₂) :
    ¬ L32A.IsS7NaturalSection H (conjClosure V H) (fsuV1 T V) := by
  rintro ⟨-, π, β, hπ, hπker, -, hβker, hβ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  have hV1U : fsuV1 T V < conjClosure V H :=
    lt_of_le_of_ne ((inf_le_left : fsuV1 T V ≤ V).trans (le_conjClosure V H)) fun h =>
      hbV (hV2.1 (by rw [h]; exact le_conjClosure V H hb))
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hS2 : IsPGroup 2 (T.subgroupOf H) :=
    hTsyl.2.1.comap_of_injective H.subtype H.subtype_injective
  have hDi : ¬ 2 ∣ Alt7.tsSub.index := by
    have h1 := Alt7.tsSub.card_mul_index
    rw [Alt7.card_tsSub, Alt7.card_perm7] at h1
    rintro ⟨m, hm⟩
    omega
  obtain ⟨σ, hσ⟩ := exists_conj_map_eq_of_sylow π hπ hS2 hTsyl.2.2 Alt7.tsSub_isPGroup hDi
  have hker' : ((MulAut.conj σ⁻¹).toMonoidHom.comp π).ker = CFSG.Open.pCore 2 ↥H := by
    have e : ((MulAut.conj σ⁻¹).toMonoidHom.comp π).ker = π.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      show (MulAut.conj σ⁻¹) (π x) = 1 ↔ π x = 1
      exact MulEquiv.map_eq_one_iff _
    rw [e, hπker]
    unfold pCoreOf Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hrange : ((MulAut.conj σ⁻¹).toMonoidHom.comp π).range = ⊤ :=
    MonoidHom.range_eq_top.mpr ((MulAut.conj σ⁻¹).surjective.comp hπ)
  have hT' : (T.subgroupOf H).map ((MulAut.conj σ⁻¹).toMonoidHom.comp π) = Alt7.tsSub := by
    rw [← Subgroup.map_map]
    exact hσ
  have hβker' : ((G6.coreAct 7 σ⁻¹).toMonoidHom.comp β).ker =
      (fsuV1 T V).subgroupOf (conjClosure V H) := by
    rw [← hβker]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show (G6.coreAct 7 σ⁻¹) (β x) = 1 ↔ β x = 1
    exact MulEquiv.map_eq_one_iff _
  have hcomp : ∀ (p q : Equiv.Perm (Fin 7)) (y : ↥(G6.coreMod 7)),
      G6.coreAct 7 p (G6.coreAct 7 q y) = G6.coreAct 7 (p * q) y := fun p q y => by
    rw [map_mul, MulAut.mul_apply]
  have hβ' : ∀ (h : ↥H) (x x' : ↥(conjClosure V H)), (x' : G) = h * x * (h : G)⁻¹ →
      ((G6.coreAct 7 σ⁻¹).toMonoidHom.comp β) x' =
        G6.coreAct 7 (((MulAut.conj σ⁻¹).toMonoidHom.comp π) h)
          (((G6.coreAct 7 σ⁻¹).toMonoidHom.comp β) x) := by
    intro h x x' hx'
    show G6.coreAct 7 σ⁻¹ (β x') =
      G6.coreAct 7 (MulAut.conj σ⁻¹ (π h)) (G6.coreAct 7 σ⁻¹ (β x))
    rw [hβ h x x' hx', hcomp, hcomp, MulAut.conj_apply,
      show σ⁻¹ * π h * σ⁻¹⁻¹ * σ⁻¹ = σ⁻¹ * π h by group]
  exact false_of_six_F4 h1222 h1332 h1334 h2 h4 S hker' (Or.inl ⟨hrange, hT'⟩) le_rfl hV1U
    S.hz.2.1 hβker' hβ'

end CFSG.Quasithin.H13.L32A.C
