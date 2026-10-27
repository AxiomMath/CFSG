module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSSpecial

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0

theorem s0 :
    StepS0 := by
  intro G _ _ L t E W z hb
  obtain ⟨T₀, hzP, hstd⟩ := zas_std_Q_explicit
  obtain ⟨-, hL, -⟩ := hb.setting
  have hLcard : Nat.card ↥L = 44352000 := card_eq_of_isSporadic_hs hL
  obtain ⟨e₀⟩ := hL
  let σ : ↥L ≃* ↥hs100P := (e₀ : ↥L ≃* NativeSporadic.HS).trans hs100Equiv
  have hY : IsSporadic ↥hs100P .HS := ⟨hs100Equiv.symm⟩
  have hzL : z ∈ L := hb.E_le hb.z_mem
  set z' : ↥L := ⟨z, hzL⟩ with hz'
  have hz2' : z * z = 1 := by
    have := hb.E_ab.2 z hb.z_mem
    rwa [pow_two] at this
  have hz1 : z ≠ 1 := by
    intro h1
    have hc := hb.z_class
    have : L ⊓ Cen z = L := by
      ext g
      simp [mem_Cen, h1]
    rw [this, hLcard] at hc
    omega
  have hzord : orderOf z' = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      simpa [pow_two] using hz2'
    · intro h
      exact hz1 (congrArg Subtype.val h)
  have hcz' : Nat.card ↥(centralizer ({z'} : Set ↥L)) = 7680 :=
    (card_cent_L z').trans hb.z_class
  have hcert := Certificates.certificate117041
  obtain ⟨hbs, hcl, -, -, -, -⟩ := s0_parts hcert
  obtain ⟨-, -, hZP, hZ2, hZ1, -⟩ := basic_spec hbs
  obtain ⟨hcZ, -, -, -, -⟩ := classes_spec hbs hcl
  set z₀ : ↥hs100P := ⟨Zp, hZP⟩ with hz₀
  have hz₀eq : z₀ = ⟨zasZ0, hzP⟩ := rfl
  have hz₀2 : orderOf z₀ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      simpa [pow_two] using hZ2
    · intro h
      exact hZ1 (congrArg Subtype.val h)
  have hcz₀ : Nat.card ↥(centralizer ({z₀} : Set ↥hs100P)) = 7680 :=
    (s0_card_cent_subtype hs100P z₀).trans hcZ
  have hσz2 : orderOf (σ z') = 2 := by rw [MulEquiv.orderOf_eq]; exact hzord
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_card_centralizer_eq_hs hY (σ z') z₀ hσz2 hz₀2
    ((card_centralizer_equiv σ z').trans (hcz'.trans hcz₀.symm)))
  let σ1 : ↥L ≃* ↥hs100P := σ.trans (MulAut.conj c)
  have hσ1z : σ1 z' = z₀ := by
    show c * σ z' * c⁻¹ = z₀
    exact hc
  have hspecL : IsSpecialIn L z E := ⟨hb.E_le, hb.z_mem, hb.E_ab, hb.E_card, hb.E_S6, hb.E_trans⟩
  have hsp1 := (isSpecialIn_iff hzL hb.E_le).1 hspecL
  have hsp2 := hsp1.map σ1
  rw [hσ1z] at hsp2
  obtain ⟨E1, hE1eq, -, hE1spec⟩ := zas_special_spec_ext
  have hE1 : E1 = E0 := hE1eq
  rw [hE1] at hE1spec
  have hE0P : E0 ≤ hs100P := hE1spec.1
  have hsp0 := (isSpecialIn_iff hzP hE0P).1 hE1spec
  have adm : ∀ {F : Subgroup ↥hs100P}, IsSpecialElem z₀ F → AdmZ z₀ F := by
    intro F hF
    obtain ⟨hzF, hab, hcard, -, htr⟩ := hF
    exact ⟨hab, hcard, hzF, fun e he he1 => by
      obtain ⟨a, -, ha⟩ := htr e he he1
      exact ⟨a, ha⟩⟩
  obtain ⟨c₂, hc₂, hceq⟩ := exists_conj_of_core hstd.pgroup hstd.index hstd.comm
    (Adm := AdmZ z₀) (fun F h => h.isPGroup_le) (fun F c hc h => h.conj hc)
    (fun F₁ F₂ f₁ f₂ b₁ b₂ => hstd.core F₁ F₂ f₁ f₂ b₁.1 b₂.1 b₁.2.1 b₂.2.1 b₁.2.2.1 b₂.2.2.1
      b₁.2.2.2 b₂.2.2.2) (adm hsp2) (adm hsp0)
  let σ2 : ↥L ≃* ↥hs100P := σ1.trans (MulAut.conj c₂)
  have hσ2z : σ2 z' = z₀ := by
    show c₂ * σ1 z' * c₂⁻¹ = z₀
    rw [hσ1z]
    have := mem_centralizer_singleton_iff.1 hc₂
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hσ2E : (E.subgroupOf L).map σ2.toMonoidHom = E0.subgroupOf hs100P := by
    rw [← hceq]
    show _ = ((E.subgroupOf L).map σ1.toMonoidHom).map (MulAut.conj c₂).toMonoidHom
    rw [Subgroup.map_map]
    rfl
  obtain ⟨pm⟩ := model_PA0
  have d := S0D.ofPA0 pm hE0P hzP
  let φ : ↥hs100P →* G := L.subtype.comp σ2.symm.toMonoidHom
  have hφ : Function.Injective φ := L.subtype_injective.comp σ2.symm.injective
  have hrange : φ.range = L := by
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      exact (σ2.symm a).2
    · intro hg
      exact ⟨σ2 ⟨g, hg⟩, by simp [φ]⟩
  have hEmap : (E0.subgroupOf hs100P).map φ = E := by
    rw [← hσ2E, Subgroup.map_map]
    have : φ.comp σ2.toMonoidHom = L.subtype := by
      ext x
      simp [φ]
    rw [this]
    exact Subgroup.map_subgroupOf_eq_of_le hb.E_le
  have hzmap : φ z₀ = z := by
    rw [← hσ2z]
    show ((σ2.symm (σ2 z') : ↥L) : G) = z
    rw [MulEquiv.symm_apply_apply]
  have pa := d.toPA0 hφ t
  rw [hrange, hEmap] at pa
  have hz₀' : φ ⟨Zp, hZP⟩ = z := hzmap
  rw [hz₀'] at pa
  exact ⟨pa⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
