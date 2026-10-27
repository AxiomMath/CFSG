module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Quasithin.H13.A7NatFusion

public section
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped Pointwise

section Fusion

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7NatPre.exists_conj_of_conj_F4 (h331 : Stmt3_3_1_F4) (hyp : Hyp1223 G T L V)
    (h : A7NatPre T L V ψ) {u w : V} {g : G} (hg : (w : G) = g * u * g⁻¹) :
    ∃ l ∈ L, (w : G) = l * u * l⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hu : u = 1
  · refine ⟨1, one_mem _, ?_⟩
    rw [hg, hu]
    simp
  obtain ⟨ψ', h', hcent⟩ := h.exists_aligned_central hyp.sylow
  have hwt : ∀ x : V, x ≠ 1 →
      hammingNorm (vec ψ' x) = 2 ∨ hammingNorm (vec ψ' x) = 4 ∨ hammingNorm (vec ψ' x) = 6 :=
    fun x hx => weight_of_mem_evenWeight _ (vec_mem ψ' x) (by rwa [ne_eq, vec_eq_zero_iff])
  have hw : w ≠ 1 := by
    intro hw1
    apply hu
    apply Subtype.ext
    have h1 : g * (u : G) * g⁻¹ = 1 := by rw [← hg, hw1]; rfl
    calc (u : G) = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨x, hx, hxc⟩ := hcent _ (hwt u hu)
  obtain ⟨y, hy, hyc⟩ := hcent _ (hwt w hw)
  obtain ⟨l₁, -, hl₁x⟩ := h'.exists_conj_of_weight (u := u) (w := x) hx.symm
  obtain ⟨l₂, -, hl₂y⟩ := h'.exists_conj_of_weight (u := w) (w := y) hy.symm
  set k := l₂ * g * l₁⁻¹ with hk
  have hyx : (y : G) = k * x * k⁻¹ := by
    rw [hl₂y, hg, hl₁x, hk]
    group
  obtain ⟨Ts, hTs⟩ : ∃ Ts : Sylow 2 G, (Ts : Subgroup G) = T :=
    ⟨_, IsPGroup.toSylow_coe hyp.sylow.1 hyp.sylow.2⟩
  have hxc' : (x : G) ∈ centralizer ((Ts : Subgroup G) : Set G) := by rw [hTs]; exact hxc
  have hyc' : k⁻¹⁻¹ * x * k⁻¹ ∈ centralizer ((Ts : Subgroup G) : Set G) := by
    rw [inv_inv, ← hyx, hTs]
    exact hyc
  obtain ⟨n, hn, hnx⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer Ts (x : G) k⁻¹ hxc' hyc'
  rw [inv_inv, ← hyx] at hnx
  have hnM : n ∈ normalizer (L : Set G) := by
    obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
    obtain ⟨-, -, -, hNT, -⟩ := h331B L hyp.maximal hyp.quasisimple
    rw [hyp.conjClosure_eq] at hNT
    exact hNT (by rw [← hTs]; exact hn)
  have hy1 : y ≠ 1 := by
    intro hy1
    rw [hy1, vec_one] at hy
    rcases hwt w hw with h2 | h2 | h2 <;> rw [← hy] at h2 <;> simp at h2
  have hnV : n ∈ normalizer (V : Set G) := by
    rcases h'.TI n hnM with hVn | hVn
    · exact mem_normalizer_of_conjugate_eq hVn
    · exfalso
      have hmem : (y : G) ∈ V ⊓ CFSG.conjugate V n := by
        refine ⟨y.2, ?_⟩
        show (y : G) ∈ CFSG.conjugate V n
        rw [mem_conjugate_iff_mem, hnx]
        have : n * (n⁻¹ * (x : G) * n) * n⁻¹ = x := by group
        rw [this]
        exact x.2
      rw [hVn, mem_bot] at hmem
      exact hy1 (Subtype.ext hmem)
  obtain ⟨τ, hτ⟩ := h'.Nact _ (inv_mem hnV)
  have hτxy := hτ x y (by rw [hnx, inv_inv])
  have hwt_eq : hammingNorm (vec ψ' u) = hammingNorm (vec ψ' w) := by
    rw [← hx, ← hy, hτxy, hammingNorm_permAct7]
  exact h'.exists_conj_of_weight hwt_eq

end Fusion

end CFSG.Quasithin.H13.A7
