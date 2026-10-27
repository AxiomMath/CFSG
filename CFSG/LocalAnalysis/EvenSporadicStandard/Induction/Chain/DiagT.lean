module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Orbit

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem commutator_mul_central_of_commute {d₁ d₂ z₁ z₂ : H} (h₂ : Commute z₁ d₂)
    (h₃ : Commute z₂ d₁) (h₅ : Commute z₁ z₂) :
    d₁ * z₁ * (d₂ * z₂) * (d₁ * z₁)⁻¹ * (d₂ * z₂)⁻¹ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := by
  calc d₁ * z₁ * (d₂ * z₂) * (d₁ * z₁)⁻¹ * (d₂ * z₂)⁻¹
      = d₁ * (z₁ * d₂) * z₂ * z₁⁻¹ * d₁⁻¹ * z₂⁻¹ * d₂⁻¹ := by group
    _ = d₁ * (d₂ * z₁) * z₂ * z₁⁻¹ * d₁⁻¹ * z₂⁻¹ * d₂⁻¹ := by rw [h₂.eq]
    _ = d₁ * d₂ * (z₁ * z₂ * z₁⁻¹) * d₁⁻¹ * z₂⁻¹ * d₂⁻¹ := by group
    _ = d₁ * d₂ * z₂ * d₁⁻¹ * z₂⁻¹ * d₂⁻¹ := by rw [h₅.eq]; group
    _ = d₁ * d₂ * (z₂ * d₁⁻¹) * z₂⁻¹ * d₂⁻¹ := by group
    _ = d₁ * d₂ * (d₁⁻¹ * z₂) * z₂⁻¹ * d₂⁻¹ := by rw [h₃.inv_right.eq]
    _ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := by group

variable {R N₀ A : Subgroup H}

theorem orbit_swap_case (hA : IsCompIn A (centralizer (R : Set H)))
    (hN : N₀ ≤ normalizer (R : Set H)) {t : H} (htR : t ∈ centralizer (R : Set H))
    (htN : t ∈ centralizer (N₀ : Set H))
    (hAt : A.map (MulAut.conj t).toMonoidHom ∉ orbitSet N₀ A) {D : Subgroup H}
    (hDE : D ≤ orbitSup N₀ A) :
    ∀ a ∈ D, ∀ b ∈ D.map (MulAut.conj t).toMonoidHom, a * b = b * a := by
  have hBt : ∀ B : ↥(orbitSet N₀ A), (B : Subgroup H).map (MulAut.conj t).toMonoidHom ∉
      orbitSet N₀ A := by
    intro B hB
    obtain ⟨g, hg, hBg⟩ := B.2
    obtain ⟨h, hh, hBh⟩ := hB
    apply hAt
    have htg : t * g = g * t := (Subgroup.mem_centralizer_iff.1 htN g hg).symm
    have h1 : (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        A.map (MulAut.conj h).toMonoidHom := by
      calc (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom
          = A.map (MulAut.conj (g * t)).toMonoidHom := map_conj_map A t g
        _ = A.map (MulAut.conj (t * g)).toMonoidHom := by rw [htg]
        _ = (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj t).toMonoidHom :=
            (map_conj_map A g t).symm
        _ = (B : Subgroup H).map (MulAut.conj t).toMonoidHom := by rw [hBg]
        _ = A.map (MulAut.conj h).toMonoidHom := hBh
    have h2 : A.map (MulAut.conj t).toMonoidHom =
        A.map (MulAut.conj (g⁻¹ * h)).toMonoidHom := by
      calc A.map (MulAut.conj t).toMonoidHom
          = (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj (1 : H)).toMonoidHom :=
            (map_conj_one _).symm
        _ = (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj (g⁻¹ * g)).toMonoidHom := by
            rw [inv_mul_cancel]
        _ = ((A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj g⁻¹).toMonoidHom := (map_conj_map _ g g⁻¹).symm
        _ = (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by rw [h1]
        _ = A.map (MulAut.conj (g⁻¹ * h)).toMonoidHom := map_conj_map A h g⁻¹
    exact ⟨g⁻¹ * h, N₀.mul_mem (N₀.inv_mem hg) hh, h2⟩
  have hcentE : ∀ B : ↥(orbitSet N₀ A),
      (B : Subgroup H).map (MulAut.conj t).toMonoidHom ≤ centralizer (orbitSup N₀ A : Set H) := by
    intro B y hy
    have hcomp : IsCompIn ((B : Subgroup H).map (MulAut.conj t).toMonoidHom)
        (centralizer (R : Set H)) := (orbitSet_isCompIn hA hN B.2).map_conj htR
    have hle : orbitSup N₀ A ≤ centralizer ({y} : Set H) := orbitSup_le fun B' b hb => by
      have hne : (B : Subgroup H).map (MulAut.conj t).toMonoidHom ≠ B' := fun h =>
        hBt B (by rw [h]; exact B'.2)
      exact Subgroup.mem_centralizer_singleton_iff.2
        (hcomp.commute_of_ne (orbitSet_isCompIn hA hN B'.2) hne y hy b hb).symm
    refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)
  have hDt : D.map (MulAut.conj t).toMonoidHom ≤ centralizer (orbitSup N₀ A : Set H) := by
    refine le_trans (Subgroup.map_mono hDE) ?_
    rw [map_orbitSup]
    exact iSup_le hcentE
  intro a ha b hb
  exact Subgroup.mem_centralizer_iff.1 (hDt hb) a (hDE ha)

theorem orbit_stable_case (hA : IsCompIn A (centralizer (R : Set H)))
    (hN : N₀ ≤ normalizer (R : Set H))
    (hS : ∀ s ∈ N₀, A.map (MulAut.conj s).toMonoidHom = A → ∀ x ∈ A, s * x * s⁻¹ = x)
    [Group.IsPerfect ↥A] {t : H} (htN : t ∈ centralizer (N₀ : Set H))
    (hAt : A.map (MulAut.conj t).toMonoidHom ∈ orbitSet N₀ A) :
    (orbitNorm hA hN).range.map (MulAut.conj t).toMonoidHom = (orbitNorm hA hN).range := by
  set ν := orbitNorm hA hN with hν
  set D := ν.range with hD
  set E := orbitSup N₀ A with hE
  set Z : Subgroup H := E ⊓ centralizer (E : Set H) with hZdef
  set F : Subgroup H := E ⊓ centralizer (N₀ : Set H) with hF
  have hDE : D ≤ E := by
    rintro _ ⟨x, rfl⟩
    exact orbitNorm_mem hA hN x
  have hDN : D ≤ centralizer (N₀ : Set H) := fun d hd =>
    Subgroup.mem_centralizer_iff.2 fun n hn => (orbitNorm_commute hA hN hS hn d hd).symm
  have hDF : D ≤ F := le_inf hDE hDN
  have hEt : E.map (MulAut.conj t).toMonoidHom ≤ E := by
    rw [hE, map_orbitSup]
    refine iSup_le fun B => ?_
    obtain ⟨g, hg, hBg⟩ := B.2
    have htg : t * g = g * t := (Subgroup.mem_centralizer_iff.1 htN g hg).symm
    have hB' : (B : Subgroup H).map (MulAut.conj t).toMonoidHom =
        (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [hBg, map_conj_map, map_conj_map, htg]
    have hmem : (B : Subgroup H).map (MulAut.conj t).toMonoidHom ∈ orbitSet N₀ A := by
      rw [hB']
      exact orbitSet_map hg hAt
    exact le_orbitSup (⟨_, hmem⟩ : ↥(orbitSet N₀ A))
  have hFt : ∀ f ∈ F, t * f * t⁻¹ ∈ F := by
    intro f hf
    refine ⟨hEt ⟨f, hf.1, rfl⟩, ?_⟩
    exact (centralizer (N₀ : Set H)).mul_mem
      ((centralizer (N₀ : Set H)).mul_mem htN hf.2) ((centralizer (N₀ : Set H)).inv_mem htN)
  have hAC : ∀ a ∈ A, ∀ c ∈ centralizer (A : Set H), a * c = c * a := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.1 hc a ha
  have hBA : ∀ B : ↥(orbitSet N₀ A),
      (B : Subgroup H) ≤ prodSub A (centralizer (A : Set H)) hAC := by
    intro B y hy
    by_cases hBeq : (B : Subgroup H) = A
    · exact mem_prodSub.2 ⟨y, by rw [← hBeq]; exact hy, 1, (centralizer (A : Set H)).one_mem,
        by simp⟩
    · exact mem_prodSub.2 ⟨1, A.one_mem, y, Subgroup.mem_centralizer_iff.2 fun a ha =>
        ((orbitSet_isCompIn hA hN B.2).commute_of_ne hA hBeq y hy a ha).symm, by simp⟩
  have hEAC : E ≤ prodSub A (centralizer (A : Set H)) hAC := orbitSup_le hBA
  have hfac : ∀ f ∈ F, ∃ d ∈ D, ∃ z ∈ Z, f = d * z := by
    intro f hf
    obtain ⟨a, ha, c, hc, hfa⟩ := mem_prodSub.1 (hEAC hf.1)
    let B₀ : ↥(orbitSet N₀ A) := ⟨A, self_mem_orbitSet N₀ A⟩
    obtain ⟨c', hc', -, hd⟩ := orbitNorm_factor hA hN B₀ ⟨a, ha⟩
    have hmap : ((orbitMap N₀ A B₀ ⟨a, ha⟩ : ↥(B₀ : Subgroup H)) : H) = a := by
      rw [orbitMap_coe]
      exact hS _ (orbitRep_mem _ _ _) (map_orbitRep N₀ A B₀) a ha
    rw [hmap] at hd
    have hdD : ν ⟨a, ha⟩ ∈ D := ⟨_, rfl⟩
    have hca : a * c' = c' * a := Subgroup.mem_centralizer_iff.1 hc' a ha
    have hhA : (ν ⟨a, ha⟩)⁻¹ * f = c'⁻¹ * c := by
      rw [hd, hfa]
      have h1 : c'⁻¹ * a = a * c'⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hca]
        group
      calc (c' * a)⁻¹ * (a * c) = a⁻¹ * (c'⁻¹ * a) * c := by group
        _ = a⁻¹ * (a * c'⁻¹) * c := by rw [h1]
        _ = c'⁻¹ * c := by group
    have hhC : (ν ⟨a, ha⟩)⁻¹ * f ∈ centralizer (A : Set H) := by
      rw [hhA]
      exact (centralizer (A : Set H)).mul_mem ((centralizer (A : Set H)).inv_mem hc') hc
    have hhN : (ν ⟨a, ha⟩)⁻¹ * f ∈ centralizer (N₀ : Set H) :=
      (centralizer (N₀ : Set H)).mul_mem ((centralizer (N₀ : Set H)).inv_mem (hDN hdD)) hf.2
    have hhE : (ν ⟨a, ha⟩)⁻¹ * f ∈ E := E.mul_mem (E.inv_mem (hDE hdD)) hf.1
    have hle : E ≤ centralizer ({(ν ⟨a, ha⟩)⁻¹ * f} : Set H) := by
      refine orbitSup_le fun B b hb => ?_
      obtain ⟨g, hg, hBg⟩ := B.2
      have hb' : b ∈ A.map (MulAut.conj g).toMonoidHom := by rw [← hBg]; exact hb
      obtain ⟨a', ha', rfl⟩ := hb'
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h1 : (ν ⟨a, ha⟩)⁻¹ * f * g = g * ((ν ⟨a, ha⟩)⁻¹ * f) :=
        (Subgroup.mem_centralizer_iff.1 hhN g hg).symm
      have h2 : a' * ((ν ⟨a, ha⟩)⁻¹ * f) = ((ν ⟨a, ha⟩)⁻¹ * f) * a' :=
        Subgroup.mem_centralizer_iff.1 hhC a' ha'
      show g * a' * g⁻¹ * ((ν ⟨a, ha⟩)⁻¹ * f) = ((ν ⟨a, ha⟩)⁻¹ * f) * (g * a' * g⁻¹)
      calc g * a' * g⁻¹ * ((ν ⟨a, ha⟩)⁻¹ * f)
          = g * a' * (g⁻¹ * ((ν ⟨a, ha⟩)⁻¹ * f)) := by group
        _ = g * a' * (((ν ⟨a, ha⟩)⁻¹ * f) * g⁻¹) := by
            congr 1
            rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1]
            group
        _ = g * (a' * ((ν ⟨a, ha⟩)⁻¹ * f)) * g⁻¹ := by group
        _ = g * (((ν ⟨a, ha⟩)⁻¹ * f) * a') * g⁻¹ := by rw [h2]
        _ = (g * ((ν ⟨a, ha⟩)⁻¹ * f)) * a' * g⁻¹ := by group
        _ = (((ν ⟨a, ha⟩)⁻¹ * f) * g) * a' * g⁻¹ := by rw [← h1]
        _ = ((ν ⟨a, ha⟩)⁻¹ * f) * (g * a' * g⁻¹) := by group
    have hhcent : (ν ⟨a, ha⟩)⁻¹ * f ∈ centralizer (E : Set H) :=
      Subgroup.mem_centralizer_iff.2 fun e he =>
        Subgroup.mem_centralizer_singleton_iff.1 (hle he)
    exact ⟨ν ⟨a, ha⟩, hdD, (ν ⟨a, ha⟩)⁻¹ * f, ⟨hhE, hhcent⟩, by group⟩
  have hDcomm : ⁅D, D⁆ = D := by
    have h1 : ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ = ⊤ := by
      have := Group.isPerfect_def.1 ‹Group.IsPerfect ↥A›
      rwa [_root_.commutator_def] at this
    have h2 := Subgroup.map_commutator ⊤ ⊤ ν
    rw [h1, ← MonoidHom.range_eq_map] at h2
    exact h2.symm
  have hDt_comm : D.map (MulAut.conj t).toMonoidHom =
      ⁅D.map (MulAut.conj t).toMonoidHom, D.map (MulAut.conj t).toMonoidHom⁆ := by
    have h3 := Subgroup.map_commutator D D (MulAut.conj t).toMonoidHom
    rw [hDcomm] at h3
    exact h3
  have hDt_le : D.map (MulAut.conj t).toMonoidHom ≤ D := by
    rw [hDt_comm]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨d₁, hd₁, rfl⟩ := ha
    obtain ⟨d₂, hd₂, rfl⟩ := hb
    obtain ⟨e₁, he₁, z₁, hz₁, h₁⟩ := hfac _ (hFt d₁ (hDF hd₁))
    obtain ⟨e₂, he₂, z₂, hz₂, h₂⟩ := hfac _ (hFt d₂ (hDF hd₂))
    have hcz : ∀ (z : H) (hz : z ∈ Z) (e : H), e ∈ E → Commute z e := fun z hz e he =>
      (Subgroup.mem_centralizer_iff.1 hz.2 e he).symm
    show (t * d₁ * t⁻¹) * (t * d₂ * t⁻¹) * (t * d₁ * t⁻¹)⁻¹ * (t * d₂ * t⁻¹)⁻¹ ∈ D
    rw [h₁, h₂, commutator_mul_central_of_commute (hcz z₁ hz₁ e₂ (hDE he₂))
      (hcz z₂ hz₂ e₁ (hDE he₁)) (hcz z₁ hz₁ z₂ hz₂.1)]
    have := Subgroup.commutator_mem_commutator he₁ he₂
    rw [hDcomm] at this
    exact this
  exact Subgroup.eq_of_le_of_card_ge hDt_le (by
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective])

end CFSG.EvenSporadicStandard.Induction
