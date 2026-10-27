module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndSetting
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PBase
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem exists_closure_four_of_le_H {P : Subgroup X} (hP : P ≤ centralizer ({t} : Set X))
    (hP2 : IsPGroup 2 P) : ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowOf_ge hP2 hP
  obtain ⟨k, -, hk⟩ := hD.hs.sylow.exists_mem_conj hQ
  have hPS : P.map (MulAut.conj k⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := (hk x).mp (hPQ hx)
    simpa [MulAut.conj_apply] using h1
  obtain ⟨s, hs, hsc⟩ := Standing.Setup42.exists_closure_card_le_four hD.hs.setup hPS
  refine ⟨s.image (MulAut.conj k), Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image]
  calc closure (⇑(MulAut.conj k) '' (s : Set X))
      = closure ((MulAut.conj k).toMonoidHom '' (s : Set X)) := rfl
    _ = (closure (s : Set X)).map (MulAut.conj k).toMonoidHom := (MonoidHom.map_closure _ _).symm
    _ = (P.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj k).toMonoidHom := by rw [hsc]
    _ = P := by
      rw [map_map]
      convert map_id P
      ext x
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
      group

theorem alpha_mul_alpha : α * α = 1 := by
  obtain ⟨g, hgα, -, -⟩ := hD.fd.α_conj
  rw [← hgα, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, hD.t_mul_t]
  group

theorem exists_closure_four_of_le_alpha {P : Subgroup X} (hP : P ≤ centralizer ({α} : Set X))
    (hP2 : IsPGroup 2 P) : ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  classical
  obtain ⟨g, hgα, -, -⟩ := hD.fd.α_conj
  have hPH : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : x * α = α * x := mem_centralizer_singleton_iff.mp (hP hx)
    rw [← hgα] at h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [h1]
      _ = t * (g⁻¹ * x * g) := by group
  obtain ⟨s, hs, hsc⟩ := hD.exists_closure_four_of_le_H hPH (hP2.map _)
  refine ⟨s.image (MulAut.conj g), Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image]
  calc closure (⇑(MulAut.conj g) '' (s : Set X))
      = closure ((MulAut.conj g).toMonoidHom '' (s : Set X)) := rfl
    _ = (closure (s : Set X)).map (MulAut.conj g).toMonoidHom := (MonoidHom.map_closure _ _).symm
    _ = (P.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by rw [hsc]
    _ = P := by
      rw [map_map]
      convert map_id P
      ext x
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
      group

theorem alpha_mem_F : α ∈ centralizer ({z₁} : Set X) := (mem_inf.mp hD.fd.α_mem).2

theorem exists_closure_four_alphaF {P : Subgroup (MBar z₁)}
    (hP : P ≤ centralizer {(QuotientGroup.mk ⟨α, hD.alpha_mem_F⟩ : MBar z₁)})
    (hP2 : IsPGroup 2 P) :
    ∃ s : Finset (MBar z₁), s.card ≤ 4 ∧ closure (s : Set (MBar z₁)) = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := centralizer ({z₁} : Set X)
  let a : ↥F := ⟨α, hD.alpha_mem_F⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥F)
  have ha2 : a * a = 1 := Subtype.ext hD.alpha_mul_alpha
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥F)) := GSThmB.OddQuot.odd_card_pPrimeCore
  have hCmap : (centralizer ({a} : Set ↥F)).map π = centralizer {π a} :=
    map_centralizer_eq hodd ha2
  have hP' : P ≤ (centralizer ({a} : Set ↥F)).map π := by
    rw [hCmap]
    exact hP
  have hQmap := GSThmB.OddQuot.map_inf_comap_eq hP'
  obtain ⟨Q₂, hQ₂⟩ := exists_isSylowOf 2 (centralizer ({a} : Set ↥F) ⊓ P.comap π)
  obtain ⟨R', hR'⟩ := GSThmB.OddQuot.exists_sylow_map π hQ₂.le hQ₂.exists_sylow_eq_subgroupOf
  have hC2 : IsPGroup 2 ↥((centralizer ({a} : Set ↥F) ⊓ P.comap π).map π) := by
    rw [hQmap]
    exact hP2
  have hQ₂P : Q₂.map π = P := by
    refine le_antisymm ((map_mono hQ₂.le).trans hQmap.le) fun x hx => ?_
    rw [← hQmap] at hx
    have htop : (⊤ : Subgroup ↥((centralizer ({a} : Set ↥F) ⊓ P.comap π).map π)) = R' :=
      R'.3 (IsPGroup.of_equiv hC2 Subgroup.topEquiv.symm) le_top
    have h1 : (⟨x, hx⟩ : ↥((centralizer ({a} : Set ↥F) ⊓ P.comap π).map π)) ∈
        (R' : Subgroup _) := by rw [← htop]; trivial
    rw [hR'] at h1
    exact h1
  have hQ₂C : Q₂.map F.subtype ≤ centralizer ({α} : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x * a = a * x := mem_centralizer_singleton_iff.mp (mem_inf.mp (hQ₂.le hx)).1
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val h1
  obtain ⟨s, hs, hsc⟩ := hD.exists_closure_four_of_le_alpha hQ₂C (hQ₂.isPGroup.map _)
  obtain ⟨s', hs', hs'c⟩ := exists_finset_closure_eq_of_map F.subtype_injective hsc
  refine ⟨s'.image π, Finset.card_image_le.trans (hs'.trans hs), ?_⟩
  rw [Finset.coe_image, ← hQ₂P, ← hs'c]
  exact (MonoidHom.map_closure _ _).symm

end Data415B

end CFSG.ComponentClassification.HarrisLit
