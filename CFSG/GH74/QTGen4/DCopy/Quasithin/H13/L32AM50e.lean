module

public import CFSG.Quasithin.H13.L32AM50e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A5Props
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC38a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open Equiv Equiv.Perm
open scoped IsMulCommutative

@[expose] def Mod50FourCase_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H W K : Subgroup G) (π : ↥H →* Perm (Fin 7))
    (C : Top50 T L V H W K π) [IsMulCommutative ↥(conjClosure V H)],
    H = K ⊔ T → L32A.l1 T L V ≤ K → Nat.card (Hat V H W) = 16 → C.act.range = C.autK →
    ∃ Δ : Finset (Fin 7), Δ.card = 3 ∧ ∀ h : ↥H,
      (h : G) ∈ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) ↔ ∀ i ∈ Δ, π h i ∈ Δ

theorem lemma14_7_50_mod_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK) (h38 : Lemma14_7_38_F4)
    (h48 : Lemma14_7_48_F4) (hIrr : Mod50KIrr) (hFour : Mod50FourCase_F4) : Lemma14_7_50_Mod_F4 := by
  intro G _ _ T L V H S K hK hHKT hl1 hA π hker hA7
  have hF := hypF98_of_F4 h1222 h1332 h1334 hA37 hA38 hA39 S
  obtain ⟨W, hW⟩ := exists_topW S hF
  obtain ⟨K', hcK', -, hUK⟩ := h48 G T L V H S
  have hKK' : K = K' := by
    have := hK
    rw [hcK'] at this
    exact this
  subst hKK'
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    have h1 := cComp_map_mulEquiv (MulAut.conj h) hK
    have e : H.map (MulAut.conj h).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
    rw [e, hcK'] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have C : Top50 T L V H W K π := ⟨hW, hK, hKn, hUK, hA, hker, hA7⟩
  have : IsMulCommutative ↥(conjClosure V H) := C.comm
  obtain ⟨γ, γ', g, s⟩ := hF.exists_F8Setup
  obtain ⟨δ, δ', k, h', N⟩ := L32A.exists_not1471 hF s (h38 G T L V H S γ γ' g s)
  have hQ := (hF.F916_2_aux N.setup N.pos N.le).1
  have hirr := hIrr G T L V H W K π C hHKT hl1 δ δ' k h' N
  refine ⟨W, C.hV₁W, C.hWU, C.hHW, ?_⟩
  rcases C.irrK_cases hirr hQ with ⟨β, hβ⟩ | ⟨h16, hGL⟩
  · exact Or.inr (C.case_six hβ hirr)
  · refine Or.inl ⟨le_antisymm ?_ hA7, hFour G T L V H W K π C hHKT hl1 h16 hGL⟩
    rintro _ ⟨h, rfl⟩
    have h1 : C.act h ∈ C.autK := by
      rw [← hGL]
      exact ⟨h, rfl⟩
    exact (C.act_mem_autK_iff h).mp h1

end CFSG.Quasithin.H13.L32A.C
