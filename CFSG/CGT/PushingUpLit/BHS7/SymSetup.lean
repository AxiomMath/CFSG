module

public import CFSG.CGT.PushingUpLit.BHS7.SymMax
public import CFSG.CGT.PushingUpLit.BHS6.NestedSym
public import CFSG.CGT.PushingUpLit.BHS6.SixEightSetup

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem exists_unique_fixed_of_ncard {m : ℕ} {T' : Set (Equiv.Perm (Fin (2 * m + 1)))}
    (hs : ∀ t ∈ T', t.IsSwap) (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t)
    (hcard : T'.ncard = m) :
    ∃ c, (∀ t ∈ T', t c = c) ∧ ∀ x, (∀ t ∈ T', t x = x) → x = c := by
  classical
  have hfin : T'.Finite := Set.toFinite T'
  set U : Finset (Fin (2 * m + 1)) := hfin.toFinset.biUnion Equiv.Perm.support with hU
  have hd : (↑hfin.toFinset : Set (Equiv.Perm (Fin (2 * m + 1)))).PairwiseDisjoint
      Equiv.Perm.support := by
    intro t ht t' ht' hne
    have ht1 := hfin.mem_toFinset.1 ht
    have ht2 := hfin.mem_toFinset.1 ht'
    exact disjoint_support_of_commute (hs t ht1) (hs t' ht2) (hc t ht1 t' ht2) hne
  have hUcard : U.card = 2 * m := by
    rw [hU, Finset.card_biUnion hd]
    have h2 : ∑ t ∈ hfin.toFinset, t.support.card = ∑ t ∈ hfin.toFinset, 2 :=
      Finset.sum_congr rfl fun t ht =>
        Equiv.Perm.card_support_eq_two.2 (hs t (hfin.mem_toFinset.1 ht))
    rw [h2, Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card T' hfin, hcard]
    ring
  have hUc : Uᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin, hUcard]
    omega
  obtain ⟨c, hcU⟩ := Finset.card_eq_one.1 hUc
  have hcmem : c ∈ Uᶜ := by rw [hcU]; exact Finset.mem_singleton_self c
  have hfix : ∀ x, x ∈ Uᶜ ↔ ∀ t ∈ T', t x = x := by
    intro x
    rw [Finset.mem_compl, hU, Finset.mem_biUnion]
    constructor
    · intro hx t ht
      by_contra hne
      exact hx ⟨t, hfin.mem_toFinset.2 ht, Equiv.Perm.mem_support.2 hne⟩
    · rintro hx ⟨t, ht, hxt⟩
      exact (Equiv.Perm.mem_support.1 hxt) (hx t (hfin.mem_toFinset.1 ht))
  refine ⟨c, (hfix c).1 hcmem, fun x hx => ?_⟩
  have : x ∈ Uᶜ := (hfix x).2 hx
  rw [hcU, Finset.mem_singleton] at this
  exact this

section Finite

variable [Finite Γ] {G T E : Subgroup Γ}

theorem exists_altSetup_card (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) {m : ℕ}
    (hm : 1 ≤ m) (hn : IsNaturalAltModule ↥E m) :
    ∃ (M : AltSetup E (2 * m + 1)) (S : ↥(baum T) →* Equiv.Perm (Fin (2 * m + 1)))
      (T' : Set (Equiv.Perm (Fin (2 * m + 1)))) (k : ℕ),
      M.W = pCoreOf 2 E ∧
      (∀ (y : ↥(baum T)) (w : ↥M.W) (hw : (y : Γ) * w * (y : Γ)⁻¹ ∈ M.W),
        M.βe ⟨(y : Γ) * w * (y : Γ)⁻¹, hw⟩ = coreAct (2 * m + 1) (S y) (M.βe w)) ∧
      (∀ t ∈ T', t.IsSwap) ∧ (∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) ∧ T'.Nonempty ∧
      (∀ y : ↥(baum T), S y ∈ Subgroup.closure T') ∧
      (∀ t ∈ T', ∃ y₀ : ↥(baum T), S y₀ = t) ∧
      (∀ π ∈ alternatingGroup (Fin (2 * m + 1)), ∃ e : ↥E, M.Ψ e = π) ∧
      (∀ e : ↥E, M.Ψ e ∈ alternatingGroup (Fin (2 * m + 1))) ∧
      1 ≤ k ∧ 2 * k ≤ 2 * m + 1 ∧ T'.ncard = k ∧
      Nat.card ↥(autOn (baum T) (pCoreOf 2 E)) = 2 ^ k := by
  classical
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  obtain ⟨D, ψ, hψβ, hβbij, hψbij, -, -, k₀, hk₀1, hk₀2, hswap, hcard, -⟩ :=
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
  exact ⟨M, S, T', k₀, rfl, hS, hs', hc', hne, hSY, hy₀, hsurj, hpar, hk₀1, hk₀2, hcard', hcard⟩

structure SymModel (G T E : Subgroup Γ) (m : ℕ) where
  M : AltSetup E (2 * m + 1)
  S : ↥(baum T) →* Equiv.Perm (Fin (2 * m + 1))
  T' : Set (Equiv.Perm (Fin (2 * m + 1)))
  c : Fin (2 * m + 1)
  hMW : M.W = pCoreOf 2 E
  hS : ∀ (y : ↥(baum T)) (w : ↥M.W) (hw : (y : Γ) * w * (y : Γ)⁻¹ ∈ M.W),
    M.βe ⟨(y : Γ) * w * (y : Γ)⁻¹, hw⟩ = coreAct (2 * m + 1) (S y) (M.βe w)
  hs : ∀ t ∈ T', t.IsSwap
  hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t
  hne : T'.Nonempty
  hSY : ∀ y : ↥(baum T), S y ∈ Subgroup.closure T'
  hy₀ : ∀ t ∈ T', ∃ y₀ : ↥(baum T), S y₀ = t
  hsurj : ∀ π ∈ alternatingGroup (Fin (2 * m + 1)), ∃ e : ↥E, M.Ψ e = π
  hpar : ∀ e : ↥E, M.Ψ e ∈ alternatingGroup (Fin (2 * m + 1))
  hcfix : ∀ t ∈ T', t c = c
  hcuniq : ∀ x, (∀ t ∈ T', t x = x) → x = c

theorem nonempty_symModel (h : MinCex G T) (hE : IsBTBlock G T E) (hn : ¬ E ≤ cStarIn G T)
    {m : ℕ} (hm : 1 ≤ m) (hnat : IsNaturalAltModule ↥E m) : Nonempty (SymModel G T E m) := by
  obtain ⟨M, S, T', k, hMW, hS, hs, hc, hne, hSY, hy₀, hsurj, hpar, hk1, hk2, hcard', hcard⟩ :=
    exists_altSetup_card h.charTwo h.sylow hE hm hnat
  have hkm : k = m := by
    by_cases hm1 : m = 1
    · omega
    · have h3 := card_autOn_baum_of_isBTBlock h hE hn (by omega) hnat
      rw [hcard] at h3
      exact Nat.pow_right_injective le_rfl h3
  rw [hkm] at hcard'
  obtain ⟨c, hcfix, hcuniq⟩ := exists_unique_fixed_of_ncard hs hc hcard'
  exact ⟨⟨M, S, T', c, hMW, hS, hs, hc, hne, hSY, hy₀, hsurj, hpar, hcfix, hcuniq⟩⟩

end Finite

end CFSG.CGT.PushingUpLit.BHS7
