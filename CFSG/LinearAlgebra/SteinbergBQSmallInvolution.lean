module

public import CFSG.LinearAlgebra.SteinbergBQShearGroup
public import CFSG.ClassicalGroups.Alternating.Transvections

public noncomputable section

namespace CFSG.LinearAlgebra.SteinbergBQ

open Module
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup mem_bilinIsometryGroup)
open CFSG.ClassicalGroups.Alternating (symplecticTransvection symplecticTransvection_apply)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem bilin_symm_of_isAlt {b : LinearMap.BilinForm (ZMod 2) V} (halt : b.IsAlt) (x y : V) :
    b x y = b y x := by
  rw [← halt.neg_eq, zmod2_neg]

theorem symplecticTransvection_one_apply {b : LinearMap.BilinForm (ZMod 2) V} (halt : b.IsAlt)
    (u x : V) : (symplecticTransvection b halt u 1 : V →ₗ[ZMod 2] V) x = x + b x u • u := by
  rw [symplecticTransvection_apply, one_mul]

end CFSG.LinearAlgebra.SteinbergBQ

namespace CFSG.LinearAlgebra

open Module SteinbergBQ
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup mem_bilinIsometryGroup)
open CFSG.ClassicalGroups.Alternating (symplecticTransvection)

theorem binary_symplectic_small_nonalternating_involution {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (b : LinearMap.BilinForm (ZMod 2) V)
    (hb : b.Nondegenerate) (halt : b.IsAlt) (T : LinearMap.GeneralLinearGroup (ZMod 2) V)
    (hT : T ∈ bilinIsometryGroup b) (hT2 : T ^ 2 = 1)
    (hrk : finrank (ZMod 2) (LinearMap.range ((T : V →ₗ[ZMod 2] V) - LinearMap.id)) ≤ 2)
    {a : V} (ha : a ≠ 0) (hfun : ∀ x, b x ((T : V →ₗ[ZMod 2] V) x - x) = b x a) :
    Xor
      (finrank (ZMod 2) (LinearMap.range ((T : V →ₗ[ZMod 2] V) - LinearMap.id)) = 1 ∧
        T = symplecticTransvection b halt a 1)
      (finrank (ZMod 2) (LinearMap.range ((T : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2 ∧
        ∃ u v : V, LinearIndependent (ZMod 2) ![u, v] ∧ b u v = 0 ∧ a = u + v ∧
          T = symplecticTransvection b halt u 1 * symplecticTransvection b halt v 1 ∧
          symplecticTransvection b halt u 1 * symplecticTransvection b halt v 1 =
            symplecticTransvection b halt v 1 * symplecticTransvection b halt u 1 ∧
          LinearMap.range ((T : V →ₗ[ZMod 2] V) - LinearMap.id) =
            Submodule.span (ZMod 2) {u, v}) ∧
    (∀ x ∈ LinearMap.range ((T : V →ₗ[ZMod 2] V) - LinearMap.id),
      ∀ y ∈ LinearMap.range ((T : V →ₗ[ZMod 2] V) - LinearMap.id), b x y = 0) ∧
    (finrank (ZMod 2) (LinearMap.range ((T : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2 →
      4 ≤ finrank (ZMod 2) V) := by
  classical
  set N : V →ₗ[ZMod 2] V := (T : V →ₗ[ZMod 2] V) - LinearMap.id with hNdef
  have hN : ∀ x, N x = (T : V →ₗ[ZMod 2] V) x - x := fun x => rfl
  have hTT : ∀ x, (T : V →ₗ[ZMod 2] V) ((T : V →ₗ[ZMod 2] V) x) = x := fun x => by
    have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
      (g : V →ₗ[ZMod 2] V) x) hT2
    simpa [pow_two] using h
  have hiso := mem_bilinIsometryGroup.1 hT
  have hsym := bilin_symm_of_isAlt halt
  have hsa : ∀ x y, b (N x) y = b x (N y) := fun x y => by
    have h := hiso x ((T : V →ₗ[ZMod 2] V) y)
    rw [hTT] at h
    rw [hN, hN, map_sub, LinearMap.sub_apply, map_sub, h]
  have hNN : ∀ x, N (N x) = 0 := fun x => by
    rw [hN, hN, map_sub, hTT]
    have e : x - (T : V →ₗ[ZMod 2] V) x - ((T : V →ₗ[ZMod 2] V) x - x) =
        (2 : ZMod 2) • (x - (T : V →ₗ[ZMod 2] V) x) := by module
    rw [e, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hU : ∀ x y, b (N x) (N y) = 0 := fun x y => by rw [hsa, hNN, map_zero]
  have hker : ∀ x, (∀ y, b x (N y) = 0) → N x = 0 := fun x hx =>
    hb.1 (N x) fun y => by rw [hsa]; exact hx y
  have hiso_range : ∀ x ∈ LinearMap.range N, ∀ y ∈ LinearMap.range N, b x y = 0 := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hU x y
  have hdim : finrank (ZMod 2) (LinearMap.range N) = 2 → 4 ≤ finrank (ZMod 2) V := by
    intro h2
    have hle : LinearMap.range N ≤ b.orthogonal (LinearMap.range N) := fun w hw =>
      LinearMap.BilinForm.mem_orthogonal_iff.2 fun n hn => hiso_range n hn w hw
    have h1 := Submodule.finrank_mono hle
    rw [LinearMap.BilinForm.finrank_orthogonal hb, h2] at h1
    omega
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, b x₀ a = 1 := by
    by_contra hcon
    exact ha (hb.2 a fun x => (zmod2_eq_zero_or_one _).resolve_right fun h => hcon ⟨x, h⟩)
  set u := N x₀ with hudef
  have hux₀ : b u x₀ = 1 := by
    rw [hsym, ← hx₀]
    exact hfun x₀
  have hu0 : u ≠ 0 := fun h => by
    rw [h, map_zero, LinearMap.zero_apply] at hux₀
    exact zero_ne_one hux₀
  have hNx₀ : ∀ x, b (N x) x₀ = b x u := fun x => hsa x x₀
  have huU : u ∈ LinearMap.range N := LinearMap.mem_range_self N x₀
  have ha_of : ∀ c : V, (∀ x, b x (N x) = b x c) → a = c := fun c hc => by
    have h : a - c = 0 := hb.2 (a - c) fun x => by
      rw [map_sub, ← hfun x, ← hc x]
      exact sub_self _
    exact sub_eq_zero.1 h
  have hpos : 0 < finrank (ZMod 2) (LinearMap.range N) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨u, huU⟩, fun h => hu0 (congrArg Subtype.val h)⟩
  rcases (by omega : finrank (ZMod 2) (LinearMap.range N) = 1 ∨
      finrank (ZMod 2) (LinearMap.range N) = 2) with h1 | h2
  ·
    have hspan : Submodule.span (ZMod 2) {u} = LinearMap.range N :=
      Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 huU)
        (by rw [finrank_span_singleton hu0, h1])
    have hrep : ∀ x, N x = b x u • u := fun x => by
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 (hspan ▸ LinearMap.mem_range_self N x)
      have h := hNx₀ x
      rw [← hs, LinearMap.map_smul₂, smul_eq_mul, hux₀, mul_one] at h
      rw [← hs, h]
    have hau : a = u := ha_of u fun x => by
      rw [hrep, map_smul, smul_eq_mul, zmod2_mul_self]
    refine ⟨Or.inl ⟨⟨h1, Units.ext (LinearMap.ext fun x => ?_)⟩,
      fun h => by have := h.1; omega⟩, hiso_range, hdim⟩
    rw [symplecticTransvection_one_apply, hau, ← hrep x, hN]
    abel
  ·
    have hlt : Submodule.span (ZMod 2) {u} < LinearMap.range N := by
      refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).2 huU) fun h => ?_
      rw [← h, finrank_span_singleton hu0] at h2
      exact absurd h2 (by norm_num)
    obtain ⟨w, hwU, hwu⟩ := IsConcreteLE.exists_of_lt hlt
    obtain ⟨yw, rfl⟩ := LinearMap.mem_range.1 hwU
    set yv := yw - b (N yw) x₀ • x₀ with hyvdef
    set v := N yv with hvdef
    have hv : v = N yw - b (N yw) x₀ • u := by rw [hvdef, hyvdef, map_sub, map_smul]
    have hvx₀ : b v x₀ = 0 := by
      rw [hv, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hux₀,
        smul_eq_mul, mul_one, sub_self]
    have hv0 : v ≠ 0 := fun h => by
      apply hwu
      have : N yw = b (N yw) x₀ • u := by
        rw [hv, sub_eq_zero] at h
        exact h
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    have hvU : v ∈ LinearMap.range N := LinearMap.mem_range_self N yv
    have hli : LinearIndependent (ZMod 2) ![u, v] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h := congrArg (fun z => b z x₀) hst
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hux₀, hvx₀,
        smul_eq_mul, mul_one, mul_zero, add_zero, map_zero, LinearMap.zero_apply] at h
      subst h
      rw [zero_smul, zero_add] at hst
      exact ⟨rfl, (smul_eq_zero.1 hst).resolve_right hv0⟩
    have hspan : Submodule.span (ZMod 2) {u, v} = LinearMap.range N := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_span_pair hli, h2])
      rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact huU
      · exact hvU
    have hpair : ∀ x, ∃ s t : ZMod 2, s • u + t • v = N x := fun x =>
      Submodule.mem_span_pair.1 (hspan ▸ LinearMap.mem_range_self N x)
    have huyv : b u yv = 0 := by rw [hudef, hsa, ← hvdef, hsym, hvx₀]
    have hvyv : b v yv = 1 := by
      by_contra hcon
      have h0 : b v yv = 0 := (zmod2_eq_zero_or_one _).resolve_right hcon
      apply hv0
      refine hker yv fun z => ?_
      obtain ⟨s, t, hst⟩ := hpair z
      rw [← hst, map_add, map_smul, map_smul, hsym yv u, huyv, hsym yv v, h0, smul_zero,
        smul_zero, add_zero]
    have hrep : ∀ x, N x = b x u • u + b x v • v := fun x => by
      obtain ⟨s, t, hst⟩ := hpair x
      have hs := hNx₀ x
      rw [← hst, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, hux₀, hvx₀, smul_eq_mul, smul_eq_mul, mul_one, mul_zero,
        add_zero] at hs
      have ht := hsa x yv
      rw [← hst, ← hvdef, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, huyv, hvyv, smul_eq_mul, smul_eq_mul, mul_zero, mul_one,
        zero_add] at ht
      rw [← hst, hs, ht]
    have huv : b u v = 0 := hU x₀ yv
    have hτ : ∀ x, ((symplecticTransvection b halt u 1 * symplecticTransvection b halt v 1 :
        LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x =
          x + b x u • u + b x v • v := fun x => by
      rw [Units.val_mul, Module.End.mul_apply, symplecticTransvection_one_apply,
        symplecticTransvection_one_apply, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, hsym v u, huv, smul_zero, add_zero]
      abel
    have hτ' : ∀ x, ((symplecticTransvection b halt v 1 * symplecticTransvection b halt u 1 :
        LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x =
          x + b x u • u + b x v • v := fun x => by
      rw [Units.val_mul, Module.End.mul_apply, symplecticTransvection_one_apply,
        symplecticTransvection_one_apply, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, huv, smul_zero, add_zero]
    have hT' : ∀ x, (T : V →ₗ[ZMod 2] V) x = x + b x u • u + b x v • v := fun x => by
      have := hrep x
      rw [hN] at this
      rw [add_assoc, ← this]
      abel
    have hauv : a = u + v := ha_of (u + v) fun x => by
      rw [hrep, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, zmod2_mul_self,
        zmod2_mul_self, map_add]
    refine ⟨Or.inr ⟨⟨h2, u, v, hli, huv, hauv, Units.ext (LinearMap.ext fun x => ?_),
      Units.ext (LinearMap.ext fun x => ?_), hspan.symm⟩, fun h => by have := h.1; omega⟩,
      hiso_range, hdim⟩
    · rw [hT', hτ]
    · rw [hτ, hτ']

end CFSG.LinearAlgebra
