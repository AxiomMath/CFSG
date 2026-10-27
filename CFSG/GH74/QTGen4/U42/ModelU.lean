module

public import CFSG.GH74.QTGen4.U42.ModelP1Facts
public import CFSG.GH74.QTGen4.U42.ModelCoordsB
public import CFSG.GH74.QTGen4.U42.U0CoreE

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5
open CFSG.Quasithin.H13.F431.U42 U42F431


theorem model_U_iff (e : ↥P2 ≃* Mof (alternatingGroup (Fin 5)))
    (he1 : ∀ (v : Y) (hv : v ∈ Vsub),
        ((e ⟨v, Vsub_le_P2 hv⟩ : Mof _) : Mc) = SemidirectProduct.inl (pact sigma0 (psiEq ⟨v, hv⟩)))
    (he2 : ∀ g : ↥P2, ((e g : Mof _) : Mc).right = permOf4 g) (g : ↥P2) :
    (g : Y) ∈ pCoreOf 2 P1 ↔ ((e g : Mof _) : Mc) ∈ U0 := by
  classical
  let R : Subgroup Y := pCoreOf 2 P1
  have hSyl : IsSylowTwoOf T P1 := by
    refine ⟨T_le_B0.trans B0_le_P1, isSylow_T.2.1, ?_⟩
    show ¬ 2 ∣ T.relIndex P1
    have h := Subgroup.relIndex_mul_card (H := T) (K := P1)
    rw [inf_eq_left.mpr (T_le_B0.trans B0_le_P1), card_T, card_P1] at h
    have : T.relIndex P1 = 9 := by omega
    rw [this]
    norm_num
  have hRT : R ≤ T := F7.isSylowTwoOf_pCoreOf_le hSyl
  have hRP2 : R ≤ P2 := hRT.trans T_le_P2'
  let f : ↥P2 →* Mc := (Mof (alternatingGroup (Fin 5))).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.coe_injective.comp e.injective
  let X : Subgroup Mc := (R.subgroupOf P2).map f
  have hmem (x : ↥P2) : f x ∈ X ↔ (x : Y) ∈ R := by
    constructor
    · rintro ⟨a, ha, h⟩
      have hax : a = x := hf h
      exact Subgroup.mem_subgroupOf.mp (hax ▸ ha)
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hXcard : Nat.card X = 32 := by
    rw [Subgroup.card_map_of_injective hf]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP2).toEquiv).trans card_pCoreOf_P1
  have hXT : X ≤ Thc := by
    rintro _ ⟨a, ha, rfl⟩
    have hk : InK4 (f a).right := by
      rw [show (f a).right = permOf4 a from he2 a]
      exact (model_T_iff a).mp (hRT ha)
    change InD (f a).right
    rcases hk with h | h | h | h <;> rw [h] <;> decide +kernel
  have hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X := by
    intro b hb x hx
    let bM : Mof (alternatingGroup (Fin 5)) :=
      ⟨b, mem_Mof.mpr (Equiv.Perm.mem_alternatingGroup.mpr hb.1)⟩
    let bP : ↥P2 := e.symm bM
    have hfb : f bP = b := congrArg Subtype.val (e.apply_symm_apply bM)
    have hbP : (bP : Y) ∈ B0 := by
      rw [model_B0_iff, ← he2 bP]
      change (f bP).right 4 = 4
      rw [hfb]
      exact hb.2
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨bP * a * bP⁻¹, ?_, ?_⟩
    · change (bP : Y) * (a : Y) * (bP : Y)⁻¹ ∈ pCoreOf 2 P1
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P1 (B0_le_P1 hbP)) (a : Y)).mp ha
    · simp only [map_mul, map_inv, hfb]
  have hXW : ¬ Wc ≤ X := by
    intro hWX
    apply not_Vsub_le_pCoreOf_P1
    intro v hv
    apply (hmem ⟨v, Vsub_le_P2 hv⟩).mp
    apply hWX
    change ((e ⟨v, Vsub_le_P2 hv⟩ : Mof _) : Mc) ∈ Wc
    rw [he1 v hv]
    exact ⟨_, rfl⟩
  have hX : X = U0 := U0_unique hXT hXcard hXB hXW
  change (g : Y) ∈ R ↔ f g ∈ U0
  rw [← hmem g, hX]

end CFSG.GH74.QTGen4.U42
