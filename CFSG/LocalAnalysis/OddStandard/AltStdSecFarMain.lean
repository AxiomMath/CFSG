module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarNear
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarExcl

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal CFSG.Permutation.SymmetricCoxeter

@[expose] def ShapeTwoCentDoubleAt (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (z u : G)
    (_ : Setting G L n), Cyc L Q z → ShapeTwo L Q z u → ∀ e : L ≃* alternatingGroup (Fin n),
      ∀ S₀ : Finset (Fin n), (S₀.card = 3 ∨ S₀.card = 4) → S₀.card + 7 ≤ n → CaseIIAt e z S₀ →
        ∀ (w : G) (hw : w ∈ L),
          ((e ⟨w, hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2} →
            Nat.card (centralizer ({w} : Set G)) ≤ 8 * (n - 2).factorial

section Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem cycleType_mul_swap {e₁ e₂ : Perm α} (h₁ : e₁.IsSwap) (h₂ : e₂.IsSwap) (hne : e₁ ≠ e₂)
    (hc : e₁ * e₂ = e₂ * e₁) : (e₁ * e₂).cycleType = {2, 2} := by
  have hd : e₁.Disjoint e₂ := by
    intro x
    by_cases hx : e₁ x = x
    · exact Or.inl hx
    · exact Or.inr (fixes_of_comm_swap h₁ h₂ hc.symm hne.symm hx)
  rw [hd.cycleType_mul, isSwap_iff_cycleType.1 h₁, isSwap_iff_cycleType.1 h₂]
  rfl

theorem nat_card_centralizer_of_cycleType_two_two {σ : Perm α} (h : σ.cycleType = {2, 2}) :
    Nat.card (centralizer ({σ} : Set (Perm α))) = 8 * (Fintype.card α - 4).factorial := by
  rw [nat_card_centralizer, h]
  have h1 : ({2, 2} : Multiset ℕ).sum = 4 := rfl
  have h2 : ({2, 2} : Multiset ℕ).prod = 4 := rfl
  have h3 : ({2, 2} : Multiset ℕ).toFinset = {2} := by decide
  have h4 : ({2, 2} : Multiset ℕ).count 2 = 2 := by decide
  rw [h1, h2, h3, Finset.prod_singleton, h4]
  simp [Nat.factorial]
  ring

end Perm

section Conj

variable {G : Type*} [Group G]

theorem nat_card_centralizer_conj (g w : G) :
    Nat.card (centralizer ({g * w * g⁻¹} : Set G)) = Nat.card (centralizer ({w} : Set G)) := by
  refine Nat.card_congr ⟨fun x => ⟨g⁻¹ * x * g, ?_⟩, fun y => ⟨g * y * g⁻¹, ?_⟩, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    have hx := mem_centralizer_singleton_iff.1 x.2
    calc g⁻¹ * x * g * w = g⁻¹ * ((x : G) * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * x) * g := by rw [hx]
      _ = w * (g⁻¹ * x * g) := by group
  · rw [mem_centralizer_singleton_iff]
    have hy := mem_centralizer_singleton_iff.1 y.2
    calc g * y * g⁻¹ * (g * w * g⁻¹) = g * ((y : G) * w) * g⁻¹ := by group
      _ = g * (w * y) * g⁻¹ := by rw [hy]
      _ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
  · intro x; ext; simp [mul_assoc]
  · intro y; ext; simp [mul_assoc]

end Conj

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem swapIota_mem_of_even (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {σ : Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n)) :
    ∃ hw : (swapIota h d T e σ : G) ∈ L,
      ((e ⟨swapIota h d T e σ, hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = σ := by
  set l : L := e.symm ⟨σ, hσ⟩ with hl
  have hlC : (l : G) ∈ centralizer ({z} : Set G) := le_centralizer_single h d l.2
  have hlS : (l : G) ∈ L ⊔ zpowers u := mem_sup_left l.2
  have hperm : permOf h d e hlC = σ := by
    rw [permOf_of_mem h d e hlC l.2]
    simp [hl]
  have hι : (swapIota h d T e σ : G) = l := by
    have h1 : swapIota h d T e (rhoSwap h d T.cent e ⟨l, hlS⟩) = ⟨l, hlS⟩ :=
      swapIota_rhoSwap h d T e ⟨l, hlS⟩
    have h2 : rhoSwap h d T.cent e ⟨l, hlS⟩ = σ := hperm
    rw [h2] at h1
    exact congrArg Subtype.val h1
  refine ⟨hι ▸ l.2, ?_⟩
  have : (⟨swapIota h d T e σ, hι ▸ l.2⟩ : L) = l := Subtype.ext hι
  rw [this, hl, MulEquiv.apply_symm_apply]

theorem isSwap_permOf_of_centDoubleAt (h47 : ShapeTwoCentDoubleAt n) (h : Setting G L n)
    (d : Cyc L Q z) (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n)
    {S₀ : Finset (Fin n)} (hS₀ : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hII : CaseIIAt e z S₀) {a : G}
    (ha : a ∈ centralizer ({z} : Set G)) (hP : a ∈ Partners z) :
    (permOf h d e ha).IsSwap := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨u₀, T₀, htw⟩ := exists_untwisted h d T e hS₀ hkn hII
  set D := nearData_of_untwisted h d T₀ e hS₀ hkn hII htw with hD
  obtain ⟨M, eM, hC, hz, hcompat, hconj⟩ := exists_symmetric_overgroup_near (by omega) D
  have h47' : ∀ e₁ e₂ : Perm (Fin (m + 3)), e₁.IsSwap → e₂.IsSwap → e₁ ≠ e₂ →
      e₁ * e₂ = e₂ * e₁ → centralizer ({(eM (e₁ * e₂) : G)} : Set G) ≤ M := by
    intro e₁ e₂ h₁ h₂ hne hc
    set σ₀ : Perm (Fin (m + 1)) := swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩
      with hσ₀
    have hs1 : (swap (⟨0, by omega⟩ : Fin (m + 1)) ⟨1, by omega⟩).IsSwap :=
      ⟨_, _, by simp [Fin.ext_iff], rfl⟩
    have hs2 : (swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩).IsSwap :=
      ⟨_, _, by simp [Fin.ext_iff], rfl⟩
    have hne0 : swap (⟨0, by omega⟩ : Fin (m + 1)) ⟨1, by omega⟩ ≠
        swap ⟨2, by omega⟩ ⟨3, by omega⟩ := by
      intro h'
      have := DFunLike.congr_fun h' ⟨0, by omega⟩
      rw [swap_apply_left, swap_apply_of_ne_of_ne (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff])] at this
      simp [Fin.ext_iff] at this
    have hc0 : swap (⟨0, by omega⟩ : Fin (m + 1)) ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩
        = swap ⟨2, by omega⟩ ⟨3, by omega⟩ * swap ⟨0, by omega⟩ ⟨1, by omega⟩ :=
      swap_mul_swap_comm_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    have hct0 : σ₀.cycleType = {2, 2} := cycleType_mul_swap hs1 hs2 hne0 hc0
    have heven : σ₀ ∈ alternatingGroup (Fin (m + 1)) := by
      rw [mem_alternatingGroup, hσ₀, map_mul, hs1.sign_eq, hs2.sign_eq]
      rfl
    obtain ⟨hwL, hew⟩ := swapIota_mem_of_even h d T₀ e heven
    have hcard0 := h47 G L Q z u₀ h d T₀ e S₀ hS₀ hkn hII _ hwL (by rw [hew]; exact hct0)
    have hct : (e₁ * e₂).cycleType = {2, 2} := cycleType_mul_swap h₁ h₂ hne hc
    have hct' : (inclPerm m σ₀).cycleType = {2, 2} := by
      have hi1 := inclPerm_isSwap (m := m) hs1
      have hi2 := inclPerm_isSwap (m := m) hs2
      rw [hσ₀, map_mul]
      refine cycleType_mul_swap hi1 hi2 (fun h' => hne0 (Perm.extendDomainHom_injective _ h'))
        (by rw [← map_mul, ← map_mul, hc0])
    obtain ⟨γ, hγ⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (hct'.trans hct.symm))
    have hw : (eM (e₁ * e₂) : G) = (eM γ : G) * (swapIota h d T₀ e σ₀ : G) * (eM γ : G)⁻¹ := by
      rw [← hγ, coe_eM_mul, coe_eM_mul, map_inv, hcompat]
      rfl
    have hcard : Nat.card (centralizer ({(eM (e₁ * e₂) : G)} : Set G)) ≤
        8 * (m + 1 - 2).factorial := by
      rw [hw, nat_card_centralizer_conj]; exact hcard0
    set K : Subgroup G := (centralizer ({e₁ * e₂} : Set (Perm (Fin (m + 3))))).map
      (M.subtype.comp eM.toMonoidHom) with hK
    have hKle : K ≤ centralizer ({(eM (e₁ * e₂) : G)} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ centralizer ({e₁ * e₂} : Set (Perm (Fin (m + 3)))) := hx
      show (eM x : G) ∈ _
      rw [mem_centralizer_singleton_iff] at hx' ⊢
      exact eM_comm eM hx'
    have hKcard : Nat.card K = 8 * (m + 1 - 2).factorial := by
      rw [hK, Subgroup.card_map_of_injective (Subtype.coe_injective.comp eM.injective),
        nat_card_centralizer_of_cycleType_two_two hct, Fintype.card_fin]
      congr 2
    have hKeq : K = centralizer ({(eM (e₁ * e₂) : G)} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hKle (by rw [hKcard]; exact hcard)
    rw [← hKeq]
    rintro _ ⟨x, -, rfl⟩
    exact (eM x).2
  have hsw := isSwap_π_of_partner (by omega) D eM hC hz hcompat hconj h47' hP
  exact hsw

theorem caseII_of_centDoubleAt (h47 : ShapeTwoCentDoubleAt n) (h : Setting G L n)
    (d : Cyc L Q z) (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n)
    {S₀ : Finset (Fin n)} (hS₀ : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hII : CaseIIAt e z S₀) :
    CaseII e h.hn (L ⊔ zpowers u) z ∨ CaseII e h.hn (L ⊔ zpowers (u * z)) z := by
  have hz2 : z * z = 1 := d.mul_self
  have hsw : ∀ (a : G) (ha : a ∈ centralizer ({z} : Set G)), a ∈ Partners z →
      (permOf h d e ha).IsSwap := fun a ha hP =>
    isSwap_permOf_of_centDoubleAt h47 h d T e hn hS₀ hkn hII ha hP
  obtain ⟨c, hc, htw⟩ := caseII_twist h d T e hS₀ hkn hII
  rcases hc with hc | hc
  · left
    rw [hc] at htw
    exact caseII_of_untwisted h d T e hsw (fun τ hτ => by simpa using htw τ hτ)
  · right
    rw [hc] at htw
    obtain ⟨hcent', hout', hsq'⟩ := shapeTwo_mul_z d T.cent T.outer T.sq
    have T' : ShapeTwo L Q z (u * z) := ⟨T.card, hcent', hout', hsq'⟩
    refine caseII_of_untwisted h d T' e hsw ?_
    intro τ hτ
    obtain ⟨h1, h2⟩ := htw τ hτ
    rw [hz2, one_mul] at h2
    have h3 := eq_swapIota_or h d T e (swapIota_mem_centralizer h d T' e τ)
    rw [permOf_swapIota h d T' e τ] at h3
    rcases h3 with h3 | h3
    · exact absurd h3 (swapIota_mul_z_ne h d T T' e hτ.sign_eq)
    · rw [h3, ← mul_assoc, hz2, one_mul]
      exact ⟨h1, h2⟩

end Main

end CFSG.OddStandard.AltStdSec
