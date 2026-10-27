module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma25
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate

public section

namespace CFSG.GF2Type.Aschbacher1976Common

open Subgroup CFSG

variable {G : Type*} [Group G] [Finite G]

@[expose] def conjugatesIn (A S : Subgroup G) : Set (Subgroup G) :=
  {B | ∃ g : G, B = conjugate A g ∧ B ≤ S}

theorem card_conjugate_eq (A : Subgroup G) (g : G) : Nat.card (conjugate A g) = Nat.card A := by
  unfold conjugate
  exact Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulEquiv.injective (MulAut.conj g⁻¹))

theorem exists_sq_ne_one_of_cyclic {A : Subgroup G} (hA : IsCyclic A) (hA4 : 4 ≤ Nat.card A) :
    ∃ a ∈ A, a ^ 2 ≠ 1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥A)
  refine ⟨(a : G), a.2, fun h => ?_⟩
  have hle := orderOf_le_of_pow_eq_one (by norm_num : 0 < 2) h
  rw [Subgroup.orderOf_coe, ha] at hle
  omega

theorem conjugate_comm_of_isCyclic {A : Subgroup G} (hA : IsCyclic A) {g x y : G}
    (hx : x ∈ conjugate A g) (hy : y ∈ conjugate A g) : x * y = y * x := by
  have hx' : g * x * g⁻¹ ∈ A :=
    CFSG.LocalAnalysis.GorensteinLyons.mem_conjugate_iff_conj_mem.mp hx
  have hy' : g * y * g⁻¹ ∈ A :=
    CFSG.LocalAnalysis.GorensteinLyons.mem_conjugate_iff_conj_mem.mp hy
  have hc : (⟨g * x * g⁻¹, hx'⟩ : ↥A) * ⟨g * y * g⁻¹, hy'⟩ =
      ⟨g * y * g⁻¹, hy'⟩ * ⟨g * x * g⁻¹, hx'⟩ := mul_comm' _ _
  have hc' : (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹) :=
    congrArg Subtype.val hc
  calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [hc']
    _ = y * x := by group

theorem tiFamily_conjugates {A S : Subgroup G} (hA : IsCyclic A) (hA2 : IsPGroup 2 A)
    (hA4 : 4 ≤ Nat.card A) (hTI : ∀ g : G, conjugate A g = A ∨ A ⊓ conjugate A g = ⊥)
    (hS : IsPGroup 2 S) : CFSG.ComponentClassification.Asc76X.TIFamily S (conjugatesIn A S) := by
  refine
    { pGroup := hS
      le_S := ?_
      conj_mem := ?_
      card_eq := ?_
      frattini_ne := ?_
      inf_eq_bot := ?_ }
  · intro R hR
    obtain ⟨g, -, hgS⟩ := hR
    exact hgS
  · intro R hR s hs
    obtain ⟨g, rfl, hgS⟩ := hR
    refine ⟨g * s, CFSG.LocalAnalysis.GorensteinLyons.conjugate_conjugate A g s, ?_⟩
    intro x hx
    have hx : x ∈ conjugate (conjugate A g) s := hx
    rw [CFSG.LocalAnalysis.GorensteinLyons.mem_conjugate_iff_conj_mem] at hx
    have h1 : s * x * s⁻¹ ∈ S := hgS hx
    have h2 := S.mul_mem (S.mul_mem (S.inv_mem hs) h1) hs
    have h3 : s⁻¹ * (s * x * s⁻¹) * s = x := by group
    rw [h3] at h2
    exact h2
  · intro R hR T hT
    obtain ⟨g, rfl, -⟩ := hR
    obtain ⟨h, rfl, -⟩ := hT
    rw [card_conjugate_eq, card_conjugate_eq]
  · intro R hR hbot
    obtain ⟨g, rfl, -⟩ := hR
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (IsPGroup 2 (conjugate A g)) := ⟨hA2.map (MulAut.conj g⁻¹).toMonoidHom⟩
    obtain ⟨a, ha, ha2⟩ := exists_sq_ne_one_of_cyclic hA hA4
    have hmem : g⁻¹ * a * g ∈ conjugate A g :=
      CFSG.LocalAnalysis.GorensteinLyons.inv_mul_mul_mem_conjugate ha
    have h1 := CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (R := conjugate A g)
      ⟨g⁻¹ * a * g, hmem⟩
    rw [hbot, Subgroup.mem_bot] at h1
    apply ha2
    have h2 : (g⁻¹ * a * g) ^ 2 = 1 := by simpa using congrArg Subtype.val h1
    have e : (g⁻¹ * a * g) ^ 2 = g⁻¹ * (a * a) * g := by
      rw [sq]
      group
    rw [e] at h2
    calc a ^ 2 = g * (g⁻¹ * (a * a) * g) * g⁻¹ := by
          rw [sq]
          group
      _ = 1 := by
          rw [h2]
          group
  · intro R hR T hT hRT
    obtain ⟨g, rfl, -⟩ := hR
    obtain ⟨h, rfl, -⟩ := hT
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxg, hxh⟩ := hx
    rcases hTI (h * g⁻¹) with hcase | hcase
    · exfalso
      apply hRT
      have h1 : conjugate A h = conjugate (conjugate A (h * g⁻¹)) g := by
        rw [CFSG.LocalAnalysis.GorensteinLyons.conjugate_conjugate, show h * g⁻¹ * g = h by group]
      rw [hcase] at h1
      exact h1.symm
    · have hxg' : x ∈ conjugate A g := hxg
      have hxh' : x ∈ conjugate A h := hxh
      have hmem : h * g⁻¹ * (g * x * g⁻¹) * (h * g⁻¹)⁻¹ ∈ A := by
        have e : h * g⁻¹ * (g * x * g⁻¹) * (h * g⁻¹)⁻¹ = h * x * h⁻¹ := by group
        rw [e]
        exact CFSG.LocalAnalysis.GorensteinLyons.mem_conjugate_iff_conj_mem.mp hxh'
      have hy : g * x * g⁻¹ ∈ A ⊓ conjugate A (h * g⁻¹) :=
        ⟨CFSG.LocalAnalysis.GorensteinLyons.mem_conjugate_iff_conj_mem.mp hxg',
          CFSG.LocalAnalysis.GorensteinLyons.mem_conjugate_iff_conj_mem.mpr hmem⟩
      rw [hcase, Subgroup.mem_bot] at hy
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by simp [hy]

theorem commute_of_conjugate_le {A S : Subgroup G} (hA : IsCyclic A) (hA2 : IsPGroup 2 A)
    (hA4 : 4 ≤ Nat.card A) (hTI : ∀ g : G, conjugate A g = A ∨ A ⊓ conjugate A g = ⊥)
    (hS : IsPGroup 2 S) {g h : G} (hg : conjugate A g ≤ S) (hh : conjugate A h ≤ S) :
    ∀ x ∈ conjugate A g, ∀ y ∈ conjugate A h, x * y = y * x := by
  by_cases hgh : conjugate A g = conjugate A h
  · intro x hx y hy
    rw [hgh] at hx
    exact conjugate_comm_of_isCyclic hA hx hy
  · exact CFSG.ComponentClassification.Asc76X.TIFamily.commutes
      (tiFamily_conjugates hA hA2 hA4 hTI hS) (conjugate A g) ⟨g, rfl, hg⟩ (conjugate A h)
      ⟨h, rfl, hh⟩ hgh

theorem commute_of_mem_iSup_conjugate {A S : Subgroup G} (hA : IsCyclic A) (hA2 : IsPGroup 2 A)
    (hA4 : 4 ≤ Nat.card A) (hTI : ∀ g : G, conjugate A g = A ∨ A ⊓ conjugate A g = ⊥)
    (hS : IsPGroup 2 S) :
    ∀ x ∈ ⨆ B ∈ conjugatesIn A S, B, ∀ y ∈ ⨆ B ∈ conjugatesIn A S, B, x * y = y * x := by
  have hpair : ∀ B ∈ conjugatesIn A S, ∀ C ∈ conjugatesIn A S,
      ∀ x ∈ B, ∀ y ∈ C, x * y = y * x := by
    rintro B ⟨g, rfl, hg⟩ C ⟨h, rfl, hh⟩ x hx y hy
    exact commute_of_conjugate_le hA hA2 hA4 hTI hS hg hh x hx y hy
  have hK1 : ∀ B ∈ conjugatesIn A S,
      (⨆ C ∈ conjugatesIn A S, C) ≤ Subgroup.centralizer (B : Set G) := by
    intro B hB
    refine iSup₂_le fun C hC => ?_
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hpair B hB C hC b hb c hc
  have hKK : (⨆ B ∈ conjugatesIn A S, B) ≤
      Subgroup.centralizer ((⨆ B ∈ conjugatesIn A S, B : Subgroup G) : Set G) := by
    refine iSup₂_le fun B hB => ?_
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkB : k ∈ Subgroup.centralizer (B : Set G) := hK1 B hB hk
    rw [Subgroup.mem_centralizer_iff] at hkB
    exact (hkB b hb).symm
  intro x hx y hy
  have hxc := hKK hx
  rw [Subgroup.mem_centralizer_iff] at hxc
  exact (hxc y hy).symm

end CFSG.GF2Type.Aschbacher1976Common
