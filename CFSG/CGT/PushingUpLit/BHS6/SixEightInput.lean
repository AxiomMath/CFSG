module

public import CFSG.CGT.PushingUpLit.BHS6.NestedSym
public import CFSG.CGT.PushingUpLit.BHS6.SixEightSetup

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}

theorem exists_altSetup (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) {m : ℕ}
    (hm : 1 ≤ m) (hn : IsNaturalAltModule ↥E m) :
    ∃ (M : AltSetup E (2 * m + 1)) (S : ↥(baum T) →* Equiv.Perm (Fin (2 * m + 1)))
      (T' : Set (Equiv.Perm (Fin (2 * m + 1)))),
      M.W = pCoreOf 2 E ∧
      (∀ (y : ↥(baum T)) (w : ↥M.W) (hw : (y : Γ) * w * (y : Γ)⁻¹ ∈ M.W),
        M.βe ⟨(y : Γ) * w * (y : Γ)⁻¹, hw⟩ = coreAct (2 * m + 1) (S y) (M.βe w)) ∧
      (∀ t ∈ T', t.IsSwap) ∧ (∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) ∧ T'.Nonempty ∧
      (∀ y : ↥(baum T), S y ∈ Subgroup.closure T') ∧
      (∀ t ∈ T', ∃ y₀ : ↥(baum T), S y₀ = t) ∧
      (∀ π ∈ alternatingGroup (Fin (2 * m + 1)), ∃ e : ↥E, M.Ψ e = π) ∧
      (∀ e : ↥E, M.Ψ e ∈ alternatingGroup (Fin (2 * m + 1))) := by
  classical
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  obtain ⟨D, ψ, hψβ, hβbij, hψbij, -, -, k₀, hk₀1, -, hswap, -, -⟩ :=
    block_structure_symm hG hT hE hm hn hWdef hWe
  have hn3 : 3 ≤ 2 * m + 1 := by omega
  let βe : ↥W ≃* ↥(coreMod (2 * m + 1)) := MulEquiv.ofBijective D.β hβbij
  have hψ' : ∀ (a : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))) (w : ↥W),
      βe ((a : MulAut ↥W) w) = coreAct (2 * m + 1) (ψ a) (βe w) := fun a w => hψβ a w
  have hψinj : Function.Injective ψ := hψbij.1
  have hcharE : CharTwo E := charTwo_of_isBTBlock hG hT hE
  have hNE : ∀ e : ↥E, actOn W E hEW e ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    fun e => actOn_mem_normalizer (le_refl E) hEW e
  have hNB : ∀ y : ↥(baum T),
      actOn W (baum T) hBW y ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) := fun y =>
    autOn_le_normalizer_autOn hBW hBN (by
      rw [← range_actOn W (baum T) hBW]
      exact ⟨y, rfl⟩)
  let M : AltSetup E (2 * m + 1) :=
    { W := W
      hWE := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E
      hEW := hEW
      hWab := hE.elemAbelian.1
      hW2 := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 E
      hn3 := hn3
      βe := βe
      Ψ := modelHom (le_refl E) hEW ψ
      hΨ := fun e w hw => by
        have h1 := hψ' ⟨actOn W E hEW e, hNE e⟩ w
        have h3 : (⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ : ↥W) = (actOn W E hEW e : MulAut ↥W) w :=
          (Subtype.ext (actOn_apply_coe hEW e w)).symm
        rw [h3]
        exact h1
      hker := fun e he => by
        have h1 : ψ ⟨actOn W E hEW e, hNE e⟩ = 1 := he
        have h2 : (⟨actOn W E hEW e, hNE e⟩ :
            ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))) = 1 :=
          hψinj (h1.trans (map_one ψ).symm)
        have h4 : e ∈ (actOn W E hEW).ker := congrArg Subtype.val h2
        rw [ker_actOn, Subgroup.mem_subgroupOf] at h4
        exact hcharE h4 }
  obtain ⟨T', hs', hc', hcard', hB⟩ := hswap
  let S : ↥(baum T) →* Equiv.Perm (Fin (2 * m + 1)) :=
    ψ.comp ((actOn W (baum T) hBW).codRestrict
      (Subgroup.normalizer (autOn E W : Set (MulAut ↥W))) hNB)
  have hS : ∀ (y : ↥(baum T)) (w : ↥W) (hw : (y : Γ) * w * (y : Γ)⁻¹ ∈ W),
      βe ⟨(y : Γ) * w * (y : Γ)⁻¹, hw⟩ = coreAct (2 * m + 1) (S y) (βe w) := by
    intro y w hw
    have h1 := hψ' ⟨actOn W (baum T) hBW y, hNB y⟩ w
    have h3 : (⟨(y : Γ) * w * (y : Γ)⁻¹, hw⟩ : ↥W) = (actOn W (baum T) hBW y : MulAut ↥W) w :=
      (Subtype.ext (actOn_apply_coe hBW y w)).symm
    rw [h3]
    exact h1
  have hSY : ∀ y : ↥(baum T), S y ∈ Subgroup.closure T' := by
    intro y
    rw [← hB]
    exact ⟨⟨actOn W (baum T) hBW y, hNB y⟩, Subgroup.mem_subgroupOf.mpr (by
      rw [← range_actOn W (baum T) hBW]
      exact ⟨y, rfl⟩), rfl⟩
  have hy₀ : ∀ t ∈ T', ∃ y₀ : ↥(baum T), S y₀ = t := by
    intro t ht
    have ht' : t ∈ Subgroup.closure T' := Subgroup.subset_closure ht
    rw [← hB] at ht'
    obtain ⟨a, ha, rfl⟩ := ht'
    have ha' : (a : MulAut ↥W) ∈ autOn (baum T) W := Subgroup.mem_subgroupOf.mp ha
    rw [← range_actOn W (baum T) hBW] at ha'
    obtain ⟨b, hb⟩ := ha'
    refine ⟨b, ?_⟩
    have : (⟨actOn W (baum T) hBW b, hNB b⟩ :
        ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))) = a := Subtype.ext hb
    show ψ ⟨actOn W (baum T) hBW b, hNB b⟩ = ψ a
    rw [this]
  have hsurj : ∀ π ∈ alternatingGroup (Fin (2 * m + 1)), ∃ e : ↥E, M.Ψ e = π := by
    intro π hπ
    obtain ⟨g, hg, hgE, hN, hgπ⟩ := exists_lift_of_mem_alt hWe hn3 D ψ hψβ hπ
    exact ⟨⟨g, hgE⟩, hgπ⟩
  have hpar : ∀ e : ↥E, M.Ψ e ∈ alternatingGroup (Fin (2 * m + 1)) := by
    intro e
    let a : ↥(autOn E W) := ⟨actOn W E hEW e, by
      rw [← range_actOn W E hEW]
      exact ⟨e, rfl⟩⟩
    have h1 : ψ ⟨actOn W E hEW e, hNE e⟩ = ((D.θ a : ↥(alternatingGroup (Fin (2 * m + 1)))) :
        Equiv.Perm (Fin (2 * m + 1))) := by
      refine D.perm_unique hn3 fun w => ?_
      exact (hψβ ⟨actOn W E hEW e, hNE e⟩ w).symm.trans (D.equivar a w)
    show ψ ⟨actOn W E hEW e, hNE e⟩ ∈ alternatingGroup (Fin (2 * m + 1))
    rw [h1]
    exact (D.θ a).2
  have hne : T'.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  exact ⟨M, S, T', rfl, hS, hs', hc', hne, hSY, hy₀, hsurj, hpar⟩

end CFSG.CGT.PushingUpLit.BHS6
