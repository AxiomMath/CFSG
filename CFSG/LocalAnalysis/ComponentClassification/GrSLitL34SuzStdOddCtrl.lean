module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlNormal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlLift
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlSuz

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

theorem centralizer_le_normalizer_of_conj_sup_eq {G : Type*} [Group G] {A K : Subgroup G}
    {u : G} (hN : centralizer ({u} : Set G) ≤ normalizer (K : Set G))
    (hv : ∃ v ∈ K, v * v = 1 ∧ v ≠ 1)
    (hgen : ∀ v ∈ K, v * v = 1 → v ≠ 1 →
      ∃ a : G, a * u * a⁻¹ = u * v ∧ K ⊔ K.map (MulAut.conj a).toMonoidHom = A) :
    centralizer ({u} : Set G) ≤ normalizer (A : Set G) := by
  obtain ⟨v, hvK, hv2, hv1⟩ := hv
  obtain ⟨a, ha, hA⟩ := hgen v hvK hv2 hv1
  intro g hg
  have hgu : u * g = g * u := (mem_centralizer_singleton_iff.1 hg).symm
  have hgK : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hN hg)
  set v' := g * v * g⁻¹ with hv'
  have hv'K : v' ∈ K := (mem_normalizer_iff.1 (hN hg) v).1 hvK
  have hv'2 : v' * v' = 1 := by
    rw [hv']
    calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  have hv'1 : v' ≠ 1 := by
    intro h
    apply hv1
    calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
      _ = 1 := by rw [← hv', h]; group
  obtain ⟨a', ha', hA'⟩ := hgen v' hv'K hv'2 hv'1
  have hh : a'⁻¹ * g * a ∈ centralizer ({u} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e1 : g * (u * v) * g⁻¹ = u * v' := by
      rw [hv']
      calc g * (u * v) * g⁻¹ = (g * u) * v * g⁻¹ := by group
        _ = (u * g) * v * g⁻¹ := by rw [hgu]
        _ = u * (g * v * g⁻¹) := by group
    have e2 : a'⁻¹ * (u * v') * a' = u := by
      rw [← ha']; group
    symm
    calc u * (a'⁻¹ * g * a) = a'⁻¹ * (a' * u * a'⁻¹) * g * a := by group
      _ = a'⁻¹ * (u * v') * g * a := by rw [ha']
      _ = a'⁻¹ * (g * (u * v) * g⁻¹) * g * a := by rw [e1]
      _ = a'⁻¹ * g * (a * u * a⁻¹) * a := by rw [ha]; group
      _ = a'⁻¹ * g * a * u := by group
  have hhK : K.map (MulAut.conj (a'⁻¹ * g * a)).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hN hh)
  have hcomp : ∀ x z : G, (MulAut.conj x).toMonoidHom.comp (MulAut.conj z).toMonoidHom =
      (MulAut.conj (x * z)).toMonoidHom := by
    intro x z
    ext w
    simp [mul_assoc]
  have key : (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj a').toMonoidHom := by
    rw [Subgroup.map_map, hcomp, show g * a = a' * (a'⁻¹ * g * a) by group, ← hcomp,
      ← Subgroup.map_map, hhK]
  refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
  show A.map (MulAut.conj g).toMonoidHom = A
  calc A.map (MulAut.conj g).toMonoidHom
      = (K ⊔ K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj g).toMonoidHom := by rw [hA]
    _ = K ⊔ K.map (MulAut.conj a').toMonoidHom := by rw [Subgroup.map_sup, hgK, key]
    _ = A := hA'

theorem l34SuzOddNormalizerControl_of_inputs :
    L34SuzOddNormalizerControl := by
  intro G _ _ A V K t y hS hD u hu hu1 hK
  refine centralizer_le_normalizer_of_conj_sup_eq
    (centralizer_le_normalizer_K_of_l34SuzOdd hS hD hu hK)
    (exists_involution_mem_of_l34SuzOddData hD) fun v hv hv2 hv1 => ?_
  obtain ⟨a, -, ha, hgen⟩ := exists_conj_mul_sup_eq_of_l34SuzOddData
    suzTwoBFusionGeneration_holds (isPerfect_of_l34SuzOddSetting hS) hS.suz
    hS.odd_card_center hD hu hu1 hv hv2 hv1
  exact ⟨a, ha, hgen⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
