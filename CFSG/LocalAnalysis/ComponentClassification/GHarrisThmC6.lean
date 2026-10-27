module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.Walter.AStar.Subnormal
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC4

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.ThmC

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem card_Eu : Nat.card Eu = 16 := by
  rw [Nat.card_congr eEquiv.toEquiv]
  change Nat.card (Fin 4 → ZMod 2) = 16
  rw [Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem card_F4c : Nat.card F4c = 4 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem card_Zu : Nat.card Zu = 4 := by
  rw [← card_F4c]
  refine Nat.card_congr
    { toFun := fun u => (u : UT3 F4c).c
      invFun := fun c => ⟨⟨0, 0, c⟩, mem_Zu.mpr ⟨rfl, rfl⟩⟩
      left_inv := fun u => ?_
      right_inv := fun c => rfl }
  obtain ⟨⟨a, b, c⟩, hu⟩ := u
  obtain ⟨ha, hb⟩ := mem_Zu.mp hu
  change a = 0 at ha
  change b = 0 at hb
  subst ha hb
  rfl

namespace UTSylow

variable {X : Type} [Group X] (D : UTSylow X)

theorem card_E : Nat.card D.E = 16 := by
  rw [card_map_of_injective D.toX_injective, card_Eu]

theorem card_F : Nat.card D.F = 16 := by
  rw [← swap_E, card_E]

theorem card_Z : Nat.card D.Z = 4 := by
  rw [card_map_of_injective D.toX_injective, card_Zu]

theorem T_inf_centralizer_E : (D.T : Subgroup X) ⊓ centralizer (D.E : Set X) = D.E := by
  refine le_antisymm (fun t ht => ?_) (le_inf D.E_le_T D.E_le_centralizer)
  obtain ⟨htT, htC⟩ := mem_inf.mp ht
  obtain ⟨w, rfl⟩ := D.exists_toX htT
  have h := mem_centralizer_iff.mp htC (D.toX ⟨1, 0, 0⟩) (D.toX_mem_E_iff.mpr rfl)
  rw [← map_mul, ← map_mul] at h
  have h' := (ut_mul_comm_iff _ _).mp (D.toX_injective h)
  refine D.toX_mem_E_iff.mpr ?_
  rw [mul_zero, one_mul] at h'
  exact h'

theorem eq_E_or_F [Finite X] {B : Subgroup X} (hBT : B ≤ (D.T : Subgroup X))
    (hB2 : ∀ b ∈ B, b * b = 1) (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b)
    (h16 : Nat.card B = 16) : B = D.E ∨ B = D.F := by
  have hBZ : ¬ B ≤ D.Z := fun h => by
    have := Subgroup.card_le_of_le h
    rw [h16, card_Z] at this
    omega
  obtain ⟨u, huB, huZ⟩ := Set.not_subset.mp hBZ
  obtain ⟨v, rfl⟩ := D.exists_toX (hBT huB)
  have hv : ¬ (v.a = 0 ∧ v.b = 0) := fun h => huZ (D.toX_mem_Z_iff.mpr h)
  have hcomm : ∀ b ∈ B, ∃ w, D.toX w = b ∧ w * v = v * w := fun b hb => by
    obtain ⟨w, rfl⟩ := D.exists_toX (hBT hb)
    exact ⟨w, rfl, D.toX_injective (by rw [map_mul, map_mul]; exact hBc _ hb _ huB)⟩
  have hvv : v * v = 1 := D.toX_injective (by rw [map_mul, map_one]; exact hB2 _ huB)
  rcases (ut_mul_self_eq_one_iff v).mp hvv with ha | hb
  · have hb : v.b ≠ 0 := fun hb => hv ⟨ha, hb⟩
    refine Or.inr (Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [h16, card_F]))
    obtain ⟨w, rfl, hw⟩ := hcomm x hx
    exact D.toX_mem_F_iff.mpr (ut_a_eq_zero_of_comm_F ha hb hw)
  · have ha : v.a ≠ 0 := fun ha => hv ⟨ha, hb⟩
    refine Or.inl (Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [h16, card_E]))
    obtain ⟨w, rfl, hw⟩ := hcomm x hx
    exact D.toX_mem_E_iff.mpr (ut_b_eq_zero_of_comm_E hb ha hw)

variable [Finite X]

theorem centralizer_E_eq (hO : pPrimeCore 2 X = ⊥) (hEn : D.E.Normal) :
    centralizer (D.E : Set X) = D.E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (D.E : Set X) with hC
  have hCn : C.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_le_iff.mp fun x _ => mem_normalizer_fintype fun c hc =>
      D.conj_mem_centralizer ((Subgroup.normalizer_eq_top_iff.mpr hEn).symm ▸ mem_top x) hc)
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal D.T hCn.isSubnormal
  rw [D.T_inf_centralizer_E] at hP
  have hPcen : ∀ x : C, ∀ y ∈ (P : Subgroup C), x * y = y * x := by
    intro x y hy
    have hyE : (y : X) ∈ D.E := hP ▸ mem_map_of_mem C.subtype hy
    exact Subtype.ext (mem_centralizer_iff.mp x.2 _ hyE).symm
  obtain ⟨K, hKn, hK2, hKidx, -, hKchar, -⟩ := CFSG.GroupTheory.burnside_normal_complement P
    (fun x _ => mem_centralizer_iff.mpr fun y hy => (hPcen x y hy).symm)
  have hKX : (K.map C.subtype).Normal := by
    constructor
    rintro _ ⟨k, hk, rfl⟩ g
    let φ : MulAut C := (MulAut.conjNormal g).trans (MulEquiv.refl C)
    refine ⟨φ k, ?_, rfl⟩
    have h1 : φ k ∈ K.map φ.toMonoidHom := mem_map_of_mem _ hk
    rwa [Subgroup.characteristic_iff_map_eq.mp hKchar φ] at h1
  have hKodd : Nat.Coprime 2 (Nat.card (K.map C.subtype)) := by
    rw [card_map_of_injective C.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hK2
  have hKbot : K.map C.subtype = ⊥ := (pPrimeCore_eq_bot_iff.mp hO) _ hKX hKodd
  have hK1 : K = ⊥ := (map_eq_bot_iff_of_injective _ C.subtype_injective).mp hKbot
  have hCP : Nat.card C = Nat.card (P : Subgroup C) := by
    rw [hK1, index_bot] at hKidx
    exact hKidx
  have hPE : Nat.card (P : Subgroup C) = Nat.card D.E := by
    rw [← hP, card_map_of_injective C.subtype_injective]
  refine (Subgroup.eq_of_le_of_card_ge D.E_le_centralizer ?_).symm
  rw [hCP, hPE]

end UTSylow

end CFSG.ComponentClassification.GHarris.ThmC
