module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Lin
public import CFSG.GH74.Generic.S45.LOddPSU
public import CFSG.GH74.Generic.S45.LLinSel

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.IVK
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem ivk714_psu_ge_five {n p f : ℕ} (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Ivk714Empty (fun X _ => LieModel X .PSU n p f) := by
  intro K _ _ hs hK z hz h
  have hZ : center K = ⊥ := center_eq_bot_of_simple_of_nonab hs h.nonabelian
  obtain ⟨L, hLW, hL, hq, hodd⟩ := h.exists_inner_component hZ
  have hCW := centralizer_inner_eq_bot_of_center_eq_bot hZ
  let e : K ≃* ↥(inner K) := MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)
  have hWs : IsSimpleGroup ↥(inner K) := e.symm.isSimpleGroup
  have hWnab : ∃ x y : ↥(inner K), x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := h.nonabelian
    refine ⟨e a, e b, fun h' => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h'
  exact CFSG.ComponentClassification.OddClassSelector.su_family_false (A := MulAut K)
    (W := inner K) hWs hWnab hCW hz hLW hL (Or.inr (Or.inl ⟨hq, hodd⟩)) hp hp2 hf hn
    (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hK)

theorem ivk714_u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 →
    Ivk714Empty (fun X _ => LieModel X .PSU 5 p f) := by
  intro p f hp hf hmod
  refine ivk714_psu_ge_five (by norm_num) hp ?_ hf
  rintro rfl
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  omega

end CFSG.GH74.GLS.IVK.Proofs2
