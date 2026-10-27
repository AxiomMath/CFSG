module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Fix
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Aut
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Char

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

section Main

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 in
theorem cf67_U3_char_std (hp : p ≠ 2) (hcen : Subgroup.center (hypPSU h 1 1) = ⊥)
    {V Z : Subgroup (MulAut (hypPSU h 1 1))} (h2 : N2Cfg (hypPSU h 1 1) p V Z)
    (h3 : N3Full (hypPSU h 1 1) V Z) {g₀ : hypSU h 1 1} (hg₀ : g₀ ∈ hypUnitriangular h 1 1)
    (hg₀1 : hypProj h 1 1 g₀ ≠ 1) (hvV : MulAut.conj (hypProj h 1 1 g₀) ∈ V) : False := by
  classical
  have hpp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hpp⟩
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have h2s := h2
  obtain ⟨-, -, -, -, -, -, -, -, hVZ⟩ := h2
  set x : hypPSU h 1 1 := hypProj h 1 1 g₀ with hx
  obtain ⟨α₀, β₀, hαβ, hg₀M⟩ := exists_uMat_of_mem g₀ hg₀
  have hnt : α₀ ≠ 0 ∨ β₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hg₀1
    have : g₀ = 1 := Subtype.ext (Units.ext (by rw [hg₀M, hcon.1, hcon.2, uMat_zero_zero]; rfl))
    rw [hx, this, map_one]
  have hinj := mulAut_conj_injective_of_center_bot hcen
  have hconjx : MulAut.conj x ≠ 1 := fun h1 => hg₀1 (hinj (h1.trans (map_one _).symm))
  obtain ⟨-, -, -, -, ⟨SP, hSP⟩, -, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have hP : IsPGroup p ↥(hypProjUnitriangular h 1 1) := by
    rw [← hSP]
    exact SP.isPGroup'
  have hxP : x ∈ hypProjUnitriangular h 1 1 := ⟨g₀, hg₀, rfl⟩
  have hzx : ∀ z ∈ Z, z x = x := by
    intro z hz
    have h1 := hVZ _ hvV z hz
    have h2' := mulAut_conj_conj z x
    apply hinj
    rw [← h2', ← h1, mul_inv_cancel_right]
  have hcomm : ∀ c ∈ Subgroup.centralizer ({x} : Set (hypPSU h 1 1)), x * c = c * x :=
    fun c hc => Subgroup.mem_centralizer_iff.mp hc x (Set.mem_singleton x)
  have hmemQ : ∀ c ∈ hypProjUnitriangular h 1 1, x * c = c * x →
      c ∈ hypProjUnitriangular h 1 1 ⊓ Subgroup.centralizer ({x} : Set (hypPSU h 1 1)) := by
    intro c hc hcx
    refine ⟨hc, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
    rw [Set.mem_singleton_iff.mp hm]
    exact hcx
  refine false_of_rstep (Q := hypProjUnitriangular h 1 1 ⊓
    Subgroup.centralizer ({x} : Set (hypPSU h 1 1))) hcen h2s h3 hvV hconjx ?_ ?_ ?_ ?_
  · intro c hc
    rw [mem_fixSub, MulAut.conj_apply, hcomm c hc.2, mul_inv_cancel_right]
  · exact hP.to_le inf_le_left
  · intro z hz c hc
    have hzx' := hzx z hz
    have hzP := u3_preserves_P hp hg₀ hg₀M hnt hzx'
    refine hmemQ _ (hzP c hc.1) ?_
    have := congrArg z (hcomm c hc.2)
    rw [map_mul, map_mul, hzx'] at this
    exact this
  · intro z hodd hcop hzfix
    have hcen' : ∀ g : hypSU h 1 1, g ∈ hypUnitriangular h 1 1 → ∀ β : K,
        ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = u3Mat h 0 β →
          z (hypProj h 1 1 g) = hypProj h 1 1 g := by
      intro g hg β hgM
      refine hzfix _ (hmemQ _ ⟨g, hg, rfl⟩ ?_)
      have hgg : g₀ * g = g * g₀ := by
        apply Subtype.ext
        apply Units.ext
        simp only [Subgroup.coe_mul, Units.val_mul]
        rw [hg₀M, hgM]
        exact (uMat_zero_comm β α₀ β₀).symm
      rw [hx, ← map_mul, ← map_mul, hgg]
    by_cases hα₀ : α₀ = 0
    · have hβ₀ : β₀ ≠ 0 := hnt.resolve_left (not_not.mpr hα₀)
      have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp)
      have hβ₁ : (-(2 : K)⁻¹) + h.bar (-(2 : K)⁻¹) = -((1 : K) * h.bar 1) := by
        rw [map_neg, map_inv₀, map_ofNat, map_one, mul_one, ← neg_add, ← two_mul,
          mul_inv_cancel₀ h2K]
      obtain ⟨g₁, hg₁, hg₁M⟩ := exists_mem_of_uMat (h := h) hβ₁
      refine u3_aut_eq_one hp hodd hcop hcen' one_ne_zero hg₁ hg₁M
        (hzfix _ (hmemQ _ ⟨g₁, hg₁, rfl⟩ ?_))
      have hgg : g₀ * g₁ = g₁ * g₀ := by
        apply Subtype.ext
        apply Units.ext
        simp only [Subgroup.coe_mul, Units.val_mul]
        rw [hg₀M, hg₁M, hα₀]
        exact uMat_zero_comm β₀ 1 _
      rw [hx, ← map_mul, ← map_mul, hgg]
    · exact u3_aut_eq_one hp hodd hcop hcen' hα₀ hg₀ hg₀M
        (hzfix _ (hmemQ _ hxP rfl))

end Main

section General

theorem cf67_U3_char_Y (hp : p ≠ 2) (hcen : Subgroup.center (hypPSU h 1 1) = ⊥)
    {V Z : Subgroup (MulAut (hypPSU h 1 1))} (h2 : N2Cfg (hypPSU h 1 1) p V Z)
    (h3 : N3Full (hypPSU h 1 1) V Z) : False := by
  classical
  have hpp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hpp⟩
  have : Finite K := h.finite
  have h2s := h2
  obtain ⟨-, -, hVe, hVc, -⟩ := h2
  obtain ⟨v, hvV, hv1, g, hgp, hvg⟩ := u3_exists_inner_of_elem h hp hVe hVc
  have hinj := mulAut_conj_injective_of_center_bot hcen
  set x : hypPSU h 1 1 := hypProj h 1 1 g with hx
  have hx1 : x ≠ 1 := fun h1 => hv1 (by rw [← hvg, h1, map_one])
  obtain ⟨-, -, -, -, ⟨SP, hSP⟩, -, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have hxp : x ^ p = 1 := by rw [hx, ← map_pow, hgp, map_one]
  have hzp : IsPGroup p ↥(Subgroup.zpowers x) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one hxp).isPGroup p _
  obtain ⟨R, hR⟩ := hzp.exists_le_sylow
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq (hypPSU h 1 1) R SP
  have hxs : s * x * s⁻¹ ∈ hypProjUnitriangular h 1 1 := by
    rw [← hSP, ← hs, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hR (Subgroup.mem_zpowers x), rfl⟩
  obtain ⟨g₀, hg₀, hg₀x⟩ := hxs
  set κ : MulAut (hypPSU h 1 1) := MulAut.conj s with hκ
  have hκx : κ x = hypProj h 1 1 g₀ := by
    rw [hg₀x, hκ, MulAut.conj_apply]
  have h2' := N2Cfg.map_mulEquiv (MulAut.congr κ) h2s
  have h3' := N3Full.map_mulEquiv κ h3
  have hconj : MulAut.congr κ (MulAut.conj x) = MulAut.conj (κ x) := by
    ext y
    simp [MulAut.conj_apply, MulAut.congr_apply]
  refine cf67_U3_char_std hp hcen h2' h3' hg₀ ?_ ?_
  · rw [← hκx]
    intro h1
    apply hx1
    exact κ.injective (h1.trans (map_one κ).symm)
  · rw [← hκx, ← hconj]
    exact ⟨MulAut.conj x, by rw [hvg]; exact hvV, rfl⟩

omit [Field K] in
theorem u3_center_eq_bot_of_simple {G : Type} [Group G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  obtain ⟨a₀, b₀, hab₀⟩ := hn
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
  · exact h1
  · exfalso
    apply hab₀
    have ha : a₀ ∈ Subgroup.center G := h1 ▸ Subgroup.mem_top a₀
    exact (Subgroup.mem_center_iff.mp ha b₀).symm

theorem cf67_U3_char (hp : p ≠ 2) {G : Type} [Group G] (e : G ≃* hypPSU h 1 1)
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) {V Z : Subgroup (MulAut G)}
    (h2 : N2Cfg G p V Z) (h3 : N3Full G V Z) : False := by
  have hsY : IsSimpleGroup (hypPSU h 1 1) := MulEquiv.isSimpleGroup e.symm
  obtain ⟨a, b, hab⟩ := hn
  have hcenY : Subgroup.center (hypPSU h 1 1) = ⊥ :=
    u3_center_eq_bot_of_simple hsY ⟨e a, e b, fun h1 => hab (e.injective (by simpa using h1))⟩
  exact cf67_U3_char_Y hp hcenY (h2.map_mulEquiv (MulAut.congr e)) (h3.map_mulEquiv e)

end General

end Char

end CFSG.GH74.GLS.Stage2.Bender.Thm1
