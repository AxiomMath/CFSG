module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionLevi

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms

section Elementary

variable {G : Type*} [Group G]

theorem mem_centralizer_singleton_mul {x a b : G} (ha : x ∈ centralizer ({a} : Set G))
    (hb : x ∈ centralizer ({b} : Set G)) : x ∈ centralizer ({a * b} : Set G) := by
  rw [mem_centralizer_singleton_iff] at ha hb ⊢
  rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]

theorem mem_centralizer_singleton_of_mul {x a b : G} (hab : x ∈ centralizer ({a * b} : Set G))
    (hb : x ∈ centralizer ({b} : Set G)) : x ∈ centralizer ({a} : Set G) := by
  rw [mem_centralizer_singleton_iff] at hab hb ⊢
  calc x * a = x * a * b * b⁻¹ := by group
    _ = a * b * x * b⁻¹ := by rw [mul_assoc x a b, hab]
    _ = a * (b * x) * b⁻¹ := by group
    _ = a * (x * b) * b⁻¹ := by rw [hb]
    _ = a * x := by group

theorem conjugate_le_centralizer {L : Subgroup G} {t : G} (htC : t ∈ centralizer (L : Set G))
    (g : G) : CFSG.conjugate L g ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h := mem_centralizer_iff.1 htC l hl
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc g⁻¹ * l * g * (g⁻¹ * t * g) = g⁻¹ * (l * t) * g := by group
    _ = g⁻¹ * (t * l) * g := by rw [h]
    _ = g⁻¹ * t * g * (g⁻¹ * l * g) := by group

theorem range_subtype_comp_symm {C : Type*} [Group C] {L : Subgroup G} (e : L ≃* C) :
    (L.subtype.comp e.symm.toMonoidHom).range = L := by
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    exact (e.symm c).2
  · intro hg
    exact ⟨e ⟨g, hg⟩, by simp⟩

end Elementary

section LemmaB


theorem exists_mulEquiv_le_centralizer_of_conj_eq_mul {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    {K : Type} [Field K] (e : L ≃* adjointGroup .F4 K)
    (hF2 : FactF2 K) (hF3 : FactF3 K) (hF3p : FactF3Perfect K) (hLS : FactLeviSimple K)
    (hF5 : FactF5 K) (hF6 : FactF6 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((rootSL2 K rootR).map e.symm.toMonoidHom).map L.subtype)
    {g z : G} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hg : g⁻¹ * t * g = t * z) :
    ∃ κ : TwoCentral, yRep K κ ≠ 1 ∧ ∃ P : Subgroup G,
      P ≤ centralizer (X : Set G) ⊓ centralizer ({t * (e.symm (yRep K κ) : G)} : Set G) ∧
      Nonempty (P ≃* C3Levi K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup .F4 K) := Finite.of_equiv _ e.toEquiv
  set φ : adjointGroup .F4 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := range_subtype_comp_symm e
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  obtain ⟨U, hU⟩ := hzU
  set zC : adjointGroup .F4 K := e ⟨z, hzL⟩ with hzC
  have hφz : φ zC = z := by simp [hφdef, hzC]
  have hzC1 : zC ≠ 1 := by
    intro h
    apply hz1
    rw [← hφz, h, map_one]
  have hUtop : (U : Subgroup L) ≤ (e.symm.toMonoidHom).range := by
    rw [MonoidHom.range_eq_top.2 e.symm.surjective]
    exact le_top
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  set UC : Sylow 2 (adjointGroup .F4 K) := U.comapOfInjective e.symm.toMonoidHom hinj hUtop
    with hUC
  have hmemUC : ∀ c, c ∈ (UC : Subgroup (adjointGroup .F4 K)) ↔ e.symm c ∈ (U : Subgroup L) := by
    intro c
    rw [hUC, Sylow.coe_comapOfInjective, mem_comap]
    rfl
  have hzCU : zC ∈ centralizer ((UC : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) := by
    rw [mem_centralizer_iff]
    intro c hc
    have h := hU _ ((hmemUC c).1 hc)
    apply hφ
    rw [map_mul, map_mul, hφz]
    exact h
  obtain ⟨κ, c, hc⟩ := hF2 UC zC hzCU hzC1
  have hyκ1 : yRep K κ ≠ 1 := by
    intro h
    apply hzC1
    rw [h] at hc
    have : zC = c⁻¹ * (c * zC * c⁻¹) * c := by group
    rw [this, hc]
    group
  set y : G := φ (yRep K κ) with hydef
  have hyL : y ∈ L := hφr ▸ ⟨yRep K κ, rfl⟩
  have hy1 : y ≠ 1 := by
    intro h
    apply hyκ1
    apply hφ
    rw [map_one]
    exact h
  have hy : y = φ c * z * (φ c)⁻¹ := by
    rw [hydef, ← hc, map_mul, map_mul, map_inv, hφz]
  have hcL : φ c ∈ L := hφr ▸ ⟨c, rfl⟩
  set g₁ := g * (φ c)⁻¹ with hg₁def
  have hg₁ : g₁⁻¹ * t * g₁ = t * y := by
    have htc : φ c * t = t * φ c := (mem_centralizer_singleton_iff.1 (hLt hcL))
    calc g₁⁻¹ * t * g₁ = φ c * (g⁻¹ * t * g) * (φ c)⁻¹ := by rw [hg₁def]; group
      _ = φ c * t * z * (φ c)⁻¹ := by rw [hg, mul_assoc (φ c) t z]
      _ = t * (φ c * z * (φ c)⁻¹) := by rw [htc]; group
      _ = t * y := by rw [hy]
  set Λ := (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).map φ with hΛdef
  have hΛeq : Λ = L ⊓ centralizer ({y} : Set G) := by
    rw [hΛdef, map_centralizer_singleton hφ, hφr]
  have hΛperf : ⁅Λ, Λ⁆ = Λ := by rw [hΛdef, ← map_commutator, hF3p κ]
  have hΛt : Λ ≤ centralizer ({t} : Set G) := hΛeq ▸ inf_le_left.trans hLt
  have hΛy : Λ ≤ centralizer ({y} : Set G) := hΛeq ▸ inf_le_right
  have hΛt' : Λ ≤ centralizer ({g₁⁻¹ * t * g₁} : Set G) := by
    rw [hg₁]
    exact fun x hx => mem_centralizer_singleton_mul (hΛt hx) (hΛy hx)
  have hΛL' : Λ ≤ L ⊓ CFSG.conjugate L g₁ :=
    std_perfect_le_inf_conjugate hset hOut htC ht g₁ hΛperf hΛt hΛt'
  set φ'₀ : adjointGroup .F4 K →* G := (MulAut.conj g₁⁻¹).toMonoidHom.comp φ with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  have hyΛ : y ∈ Λ := hΛeq ▸ ⟨hyL, mem_centralizer_singleton_iff.2 rfl⟩
  obtain ⟨w, hw⟩ : y ∈ φ'₀.range := hφ'₀r ▸ (hΛL' hyΛ).2
  set W₁ := (UC : Subgroup (adjointGroup .F4 K)).map (MulAut.conj c).toMonoidHom with hW₁def
  have hW₁y : ∀ a ∈ W₁, a * yRep K κ = yRep K κ * a := by
    rintro _ ⟨u, hu, rfl⟩
    have h := mem_centralizer_iff.1 hzCU u hu
    rw [← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * u * c⁻¹ * (c * zC * c⁻¹) = c * (u * zC) * c⁻¹ := by group
      _ = c * (zC * u) * c⁻¹ := by rw [h]
      _ = c * zC * c⁻¹ * (c * u * c⁻¹) := by group
  set U₀ := W₁.map φ with hU₀def
  have hU₀Λ : U₀ ≤ Λ := by
    rw [hΛeq]
    rintro _ ⟨a, ha, rfl⟩
    refine mem_inf.2 ⟨hφr ▸ ⟨a, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff, hydef, ← map_mul, ← map_mul, hW₁y a ha]
  have hU₀L' : U₀ ≤ φ'₀.range := hφ'₀r ▸ hU₀Λ.trans (hΛL'.trans inf_le_right)
  set W := U₀.comap φ'₀ with hWdef
  have hWcard : Nat.card W = Nat.card (UC : Subgroup (adjointGroup .F4 K)) := by
    have h1 : W.map φ'₀ = U₀ := map_comap_eq_self hU₀L'
    rw [← card_map_of_injective hφ'₀, h1, hU₀def, card_map_of_injective hφ, hW₁def,
      card_map_of_injective (MulAut.conj c).injective]
  have hWp : IsPGroup 2 W := by
    obtain ⟨k, hk⟩ := UC.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (hWcard.trans hk)
  have hWidx : ¬ 2 ∣ W.index := by
    have h1 := W.card_mul_index
    have h2 := (UC : Subgroup (adjointGroup .F4 K)).card_mul_index
    rw [hWcard] at h1
    have hpos : 0 < Nat.card (UC : Subgroup (adjointGroup .F4 K)) := Nat.card_pos
    have h3 : W.index = (UC : Subgroup (adjointGroup .F4 K)).index :=
      Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [h3]
    exact UC.not_dvd_index
  set WS : Sylow 2 (adjointGroup .F4 K) := hWp.toSylow hWidx with hWS
  have hwW : w ∈ centralizer ((WS : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) := by
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : φ'₀ a ∈ U₀ := ha
    have h := mem_centralizer_singleton_iff.1 (hΛy (hU₀Λ ha'))
    apply hφ'₀
    rw [map_mul, map_mul, hw]
    exact h
  have hw1 : w ≠ 1 := by
    intro h
    apply hy1
    rw [← hw, h, map_one]
  obtain ⟨κ', c', hc'⟩ := hF2 WS w hwW hw1
  set φ' : adjointGroup .F4 K →* G := φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom with hφ'def
  have hφ' : Function.Injective φ' := hφ'₀.comp (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g₁ := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  have hφ'y : φ' (yRep K κ') = y := by
    rw [hφ'def, MonoidHom.comp_apply, ← hc', ← hw]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hΛ' : (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).map φ =
      (centralizer ({yRep K κ'} : Set (adjointGroup .F4 K))).map φ' := by
    have hR : (centralizer ({yRep K κ'} : Set (adjointGroup .F4 K))).map φ' =
        CFSG.conjugate L g₁ ⊓ centralizer ({y} : Set G) := by
      rw [map_centralizer_singleton hφ', hφ'r, hφ'y]
    rw [← hΛdef, hR]
    apply le_antisymm
    · exact le_inf (hΛL'.trans inf_le_right) hΛy
    · have hperf' : ⁅(centralizer ({yRep K κ'} : Set (adjointGroup .F4 K))).map φ',
          (centralizer ({yRep K κ'} : Set (adjointGroup .F4 K))).map φ'⁆ =
          (centralizer ({yRep K κ'} : Set (adjointGroup .F4 K))).map φ' := by
        rw [← map_commutator, hF3p κ']
      have ht' : (centralizer ({yRep K κ'} : Set (adjointGroup .F4 K))).map φ' ≤
          centralizer ({t} : Set G) := by
        rw [hR]
        intro x hx
        have h1 := conjugate_le_centralizer htC g₁ hx.1
        rw [hg₁] at h1
        exact mem_centralizer_singleton_of_mul h1 hx.2
      have hle := std_perfect_le hset hOut htC ht hperf' ht'
      rw [hR] at hle
      rw [hΛeq]
      exact fun x hx => ⟨hle hx, hx.2⟩
  have hXJ' : X ≤ (rootSL2 K rootR).map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  obtain ⟨P, hP, hPiso⟩ := exists_le_centralizer_mulEquiv_of_two_levi hF3 hF3p hLS hF5 hF6
    hφ hφ' hΛ' hXodd hXJ'
  refine ⟨κ, hyκ1, P, le_inf (hP.trans inf_le_right) ?_, hPiso⟩
  have h := (hP.trans inf_le_left).trans (hφ'r ▸ conjugate_le_centralizer htC g₁)
  rwa [hg₁] at h

end LemmaB

end CFSG.SeitzReduction.F4Pilot
