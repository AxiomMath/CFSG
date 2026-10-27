module

public import CFSG.Quasithin.H13.L32NLem1442d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L1442

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4
open CFSG.Quasithin.H13.L1442.Ctx_F4

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx_F4 G T L V V₂ g a D)
include C

theorem no_pair_F4 {x y : D.V ≃ₗ[ZMod 2] D.V} (hxΓ : x ∈ D.img (l32nH T V))
    (hyΓ : y ∈ D.img (l32nH T V)) (hxv : x (D.π a) = D.π a) (hyv : y (D.π a) = D.π a)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : Commute x y) (hx1 : x ≠ 1)
    (hyx : ∀ n : ℕ, x ^ n ≠ y) : False := by
  have := L14332.finite_linearEquiv D
  obtain ⟨P, hP9, hPc, hP3, hPe⟩ := exists_E9_of_pair hx3 hy3 hxy hx1 hyx
  refine C.no_E9_F4 (fun u hu => ?_) hP9 hPc hP3 fun u hu => ?_
  · obtain ⟨m, n, rfl⟩ := hPe u hu
    exact (D.img _).mul_mem ((D.img _).pow_mem hxΓ m) ((D.img _).pow_mem hyΓ n)
  · obtain ⟨m, n, rfl⟩ := hPe u hu
    rw [LinearEquiv.mul_apply, pow_fix hyv n, pow_fix hxv m]

theorem false_of_concl12_F4
    (h12 : G112Concl12 (D.img (l32nH T V)) (D.img (CFSG.conjugate (l32nW T V V₂) g))) :
    False := by
  classical
  obtain ⟨-, x, L', hxX, hLΓ, -, hLL, hcomm, hcompl, ⟨φ, ψ, hψ⟩, -, -⟩ := h12
  set L'' := L'.map (MulAut.conj x).toMonoidHom with hL''

  have hinv : ∀ l ∈ L', ∀ w ∈ commSpanOf L'', l w ∈ commSpanOf L'' := by
    intro l hl w hw
    rw [commSpanOf] at hw ⊢
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, hm, z, rfl⟩ := hw
      apply Submodule.subset_span
      refine ⟨m, hm, l z, ?_⟩
      have hlm : l * m = m * l := hcomm l hl m hm
      rw [map_sub]
      congr 1
      calc l (m z) = (l * m) z := rfl
        _ = (m * l) z := by rw [hlm]
        _ = m (l z) := rfl
    | zero => simp
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    | smul c w _ h => rw [map_smul]; exact Submodule.smul_mem _ c h
  have htriv : ∀ l ∈ L', ∀ w ∈ commSpanOf L'', l w = w := by
    intro l hl w hw
    have h1 : l w - w ∈ commSpanOf L' := Submodule.subset_span ⟨l, hl, w, rfl⟩
    have h2 : l w - w ∈ commSpanOf L'' := Submodule.sub_mem _ (hinv l hl w hw) hw
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hcompl.disjoint _ h1 h2)

  have hmem : D.π a ∈ commSpanOf L' ⊔ commSpanOf L'' := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, u', hu', hv⟩ := Submodule.mem_sup.mp hmem

  obtain ⟨σ, hσA, hσ3, hσ1, hσu⟩ := exists_fix5 (ψ ⟨u, hu⟩ : Fin 5 → ZMod 2)
  set s : ↥(alternatingGroup (Fin 5)) := ⟨σ, hσA⟩ with hs
  set t : D.V ≃ₗ[ZMod 2] D.V := ((φ.symm s : ↥L') : D.V ≃ₗ[ZMod 2] D.V) with ht
  have htL : t ∈ L' := (φ.symm s).2
  have htu : t u = u := by
    have htuA : t u ∈ commSpanOf L' := by
      have h1 : t u - u ∈ commSpanOf L' := Submodule.subset_span ⟨t, htL, u, rfl⟩
      have := Submodule.add_mem _ h1 hu
      rwa [sub_add_cancel] at this
    have h1 := hψ (φ.symm s) ⟨u, hu⟩ ⟨t u, htuA⟩ rfl
    rw [MulEquiv.apply_symm_apply, show (s : Equiv.Perm (Fin 5)) = σ from rfl, hσu] at h1
    have h2 : ψ ⟨t u, htuA⟩ = ψ ⟨u, hu⟩ := Subtype.ext h1
    exact congrArg Subtype.val (ψ.injective h2)
  have htv : t (D.π a) = D.π a := by
    rw [← hv, map_add, htu, htriv t htL u' hu']

  have hxv : x (D.π a) = D.π a := C.g111.X_fixes x hxX
  have hxv' : x⁻¹ (D.π a) = D.π a := by
    conv_lhs => rw [← hxv]
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  set t' : D.V ≃ₗ[ZMod 2] D.V := x * t * x⁻¹ with ht'
  have ht'L : t' ∈ L'' := ⟨t, htL, rfl⟩
  have ht'v : t' (D.π a) = D.π a := by
    rw [ht', LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxv', htv, hxv]
  have hxΓ := C.X_le_F4 hxX
  have htΓ : t ∈ D.img (l32nH T V) := hLΓ htL
  have ht'Γ : t' ∈ D.img (l32nH T V) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hxΓ htΓ) (Subgroup.inv_mem _ hxΓ)
  have hs3 : s ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hσ3)
  have ht3 : t ^ 3 = 1 := by
    rw [ht, ← Subgroup.coe_pow, ← map_pow, hs3, map_one, Subgroup.coe_one]
  have ht'3 : t' ^ 3 = 1 := by rw [ht', conj_pow, ht3, mul_one, mul_inv_cancel]
  have ht1 : t ≠ 1 := by
    intro h1
    apply hσ1
    have h2 : φ.symm s = 1 := Subtype.ext h1
    have h3 : s = 1 := by simpa using congrArg φ h2
    exact congrArg Subtype.val h3
  have hcomm' : Commute t t' := hcomm t htL t' ht'L
  have hind : ∀ n : ℕ, t ^ n ≠ t' := by
    intro n hn
    apply ht1
    have h1 : t' ∈ L' ⊓ L'' := ⟨hn ▸ L'.pow_mem htL n, ht'L⟩
    rw [hLL, Subgroup.mem_bot, ht'] at h1
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  exact C.no_pair_F4 htΓ ht'Γ htv ht'v ht3 ht'3 hcomm' ht1 hind

end Ctx_F4

end L1442

end CFSG.Quasithin.H13
