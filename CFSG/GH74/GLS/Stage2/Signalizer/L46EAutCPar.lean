module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharInv
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section ParData

structure ParData (G₀ : Type) [Group G₀] (p : ℕ) (P₀ : Subgroup G₀) : Prop where
  syl : ∃ U : Sylow p G₀, normalizer ((U : Subgroup G₀) : Set G₀) ≤ P₀
  ne_top : P₀ ≠ ⊤
  max : ∀ Q : Subgroup G₀, P₀ ≤ Q → Q ≠ ⊤ → Q = P₀

variable {A : Type} [Group A] {K P : Subgroup A} {p : ℕ}

theorem parData_of_isMaxParabolicP (h : IsMaxParabolicP p K P) : ParData ↥K p (P.subgroupOf K) := by
  obtain ⟨⟨hPK, U, ⟨Q, hQ⟩, hUP⟩, hne, hmax⟩ := h
  refine ⟨⟨Q, fun k hk => ?_⟩, ?_, ?_⟩
  ·
    have hkU : (k : A) ∈ normalizer (U : Set A) := by
      rw [← hQ]
      exact le_normalizer_map K.subtype ⟨k, hk, rfl⟩
    exact hUP ⟨k.2, hkU⟩
  · intro htop
    apply hne
    refine le_antisymm hPK ?_
    intro x hx
    have : (⟨x, hx⟩ : ↥K) ∈ P.subgroupOf K := by rw [htop]; exact mem_top _
    exact this
  · intro Q₀ hQ₀ hQ₀top
    have hPmap : (P.subgroupOf K).map K.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPK
    have hQK : Q₀.map K.subtype ≤ K := Subgroup.map_subtype_le _
    have hpar : IsParabolicP p K (Q₀.map K.subtype) := by
      refine ⟨hQK, U, ⟨Q, hQ⟩, ?_⟩
      refine hUP.trans ?_
      rw [← hPmap]
      exact Subgroup.map_mono hQ₀
    have hne' : Q₀.map K.subtype ≠ K := by
      intro heq
      apply hQ₀top
      rw [eq_top_iff]
      intro x _
      have hx : (x : A) ∈ Q₀.map K.subtype := by rw [heq]; exact x.2
      obtain ⟨q, hq, hqx⟩ := hx
      have : q = x := Subtype.ext hqx
      exact this ▸ hq
    have := hmax _ hpar hne' (by rw [← hPmap]; exact Subgroup.map_mono hQ₀)
    rw [← hPmap] at this
    exact Subgroup.map_injective K.subtype_injective this

end ParData

section Quotient

variable {G₀ H : Type} [Group G₀] [Group H] {p : ℕ}

theorem conj_le_of_image [Finite G₀] [Fact p.Prime] {φ : G₀ →* H} (hker : φ.ker ≤ Subgroup.center G₀) (U : Sylow p G₀) {k : G₀}
    (hk : φ k ∈ normalizer (((U : Subgroup G₀).map φ : Subgroup H) : Set H)) :
    (U : Subgroup G₀).map (MulAut.conj k).toMonoidHom ≤ (U : Subgroup G₀) := by
  set N : Subgroup G₀ := (U : Subgroup G₀) ⊔ φ.ker with hN
  have hNeq : N = ((U : Subgroup G₀).map φ).comap φ := (Subgroup.comap_map_eq φ _).symm
  have hNnorm : N ≤ normalizer ((U : Subgroup G₀) : Set G₀) := by
    refine sup_le Subgroup.le_normalizer ?_
    exact hker.trans (Subgroup.center_le_normalizer _)
  have hkN : ∀ x : G₀, x ∈ N → k * x * k⁻¹ ∈ N := by
    intro x hx
    rw [hNeq, Subgroup.mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hk (φ x)).mp hx
  set V : Subgroup G₀ := (U : Subgroup G₀).map (MulAut.conj k).toMonoidHom with hV
  have hVN : V ≤ N := by
    rintro _ ⟨u, hu, rfl⟩
    exact hkN u (Subgroup.mem_sup_left hu)
  have hVp : IsPGroup p ↥V := U.isPGroup'.map _
  have hsup : IsPGroup p ↥(V ⊔ (U : Subgroup G₀)) :=
    hVp.to_sup_of_normal_right' U.isPGroup' (hVN.trans hNnorm)
  have := U.is_maximal' hsup le_sup_right
  rw [← this]
  exact le_sup_left

theorem map_mem_maximalParabolics [Finite G₀] [Fact p.Prime] {φ : G₀ →* H} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G₀) {P₀ : Subgroup G₀} (h : ParData G₀ p P₀) :
    P₀.map φ ∈ maximalParabolics H p := by
  obtain ⟨U, hUP⟩ := h.syl
  have hkerP : φ.ker ≤ P₀ := hker.trans ((Subgroup.center_le_normalizer _).trans hUP)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro htop
    apply h.ne_top
    rw [← Subgroup.comap_map_eq_self hkerP, htop, Subgroup.comap_top]
  · intro M hM
    by_contra hMtop
    have hle : P₀ ≤ M.comap φ := (Subgroup.le_comap_map φ P₀).trans (Subgroup.comap_mono hM.le)
    have hQtop : M.comap φ ≠ ⊤ := by
      intro h'
      apply hMtop
      rw [← Subgroup.map_comap_eq_self_of_surjective hφ M, h', Subgroup.map_top_of_surjective φ hφ]
    have heq := h.max _ hle hQtop
    apply hM.ne
    rw [← heq, Subgroup.map_comap_eq_self_of_surjective hφ]
  · refine ⟨normalizer (((Sylow.mapSurjective hφ U : Sylow p H) : Subgroup H) : Set H),
      ⟨Sylow.mapSurjective hφ U, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨k, rfl⟩ := hφ x
    have hk : φ k ∈ normalizer (((U : Subgroup G₀).map φ : Subgroup H) : Set H) := by
      rw [Sylow.coe_mapSurjective] at hx
      exact hx
    have h1 := conj_le_of_image hker U hk
    have hk' : φ k⁻¹ ∈ normalizer (((U : Subgroup G₀).map φ : Subgroup H) : Set H) := by
      rw [map_inv]
      exact inv_mem hk
    have h2 := conj_le_of_image hker U hk'
    have hknorm : k ∈ normalizer ((U : Subgroup G₀) : Set G₀) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hxU
        have := h1 (Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hxU)
        simpa [MulAut.conj_apply] using this
      · intro hxU
        have := h2 (Subgroup.mem_map_of_mem (MulAut.conj k⁻¹).toMonoidHom hxU)
        simpa [MulAut.conj_apply, mul_assoc] using this
    exact Subgroup.mem_map_of_mem φ (hUP hknorm)

end Quotient

section Std

variable {F : Type} [Field F]

theorem vPlus_eq_span : vPlus F = Submodule.span F {(Pi.single 2 1 : Fin 3 → F)} := by
  ext v
  rw [Submodule.mem_span_singleton, mem_vPlus]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨v 2, ?_⟩
    funext i
    fin_cases i
    · simpa using h0.symm
    · simpa using h1.symm
    · simp
  · rintro ⟨c, rfl⟩
    simp

theorem finrank_vPlus : Module.finrank F (vPlus F) = 1 := by
  rw [vPlus_eq_span]
  exact finrank_span_singleton (by
    intro h
    have := congrFun h 2
    simp at this)

theorem vMinus_eq_ker : vMinus F = LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 2) := by
  ext v
  rw [mem_vMinus, LinearMap.mem_ker]
  rfl

theorem finrank_vMinus : Module.finrank F (vMinus F) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 2)
  have hr : LinearMap.range (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 2) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨Pi.single 2 c, by simp⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun, ← vMinus_eq_ker] at h
  omega

theorem exists_conj_std [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {M : Subgroup (projectiveSL 3 F)} (hM : M ∈ maximalParabolics (projectiveSL 3 F) p) :
    ∃ h : projectiveSL 3 F, M.map (MulAut.conj h).toMonoidHom = projStabilizer (vPlus F) ∨
      M.map (MulAut.conj h).toMonoidHom = projStabilizer (vMinus F) := by
  rw [(maximal_parabolics (K := F) (n := 3) p (by norm_num)).1] at hM
  obtain ⟨W, ⟨h0, htop⟩, rfl⟩ := hM
  obtain ⟨hd1, hd3⟩ := one_le_finrank_and_lt h0 htop
  have hcases : Module.finrank F W = 1 ∨ Module.finrank F W = 2 := by omega
  rcases hcases with h1 | h2
  · obtain ⟨g, hg⟩ := exists_map_eq_of_finrank_eq (W := W) (W' := vPlus F)
      (by rw [h1, finrank_vPlus])
    exact ⟨proj 3 F g, Or.inl ((projStabilizer_map_conj g W).trans (by rw [hg]))⟩
  · obtain ⟨g, hg⟩ := exists_map_eq_of_finrank_eq (W := W) (W' := vMinus F)
      (by rw [h2, finrank_vMinus])
    exact ⟨proj 3 F g, Or.inr ((projStabilizer_map_conj g W).trans (by rw [hg]))⟩

end Std

end CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC
