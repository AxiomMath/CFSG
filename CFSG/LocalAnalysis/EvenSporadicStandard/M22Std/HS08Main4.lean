module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Main3
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08FinalB

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open scoped Classical

@[expose] def hs08InnerOne (Y : Type*) [Group Y] (J : Subgroup (MulAut Y)) : Set (MulAut Y) :=
  ((J ⊓ innerImage Y ⊤ : Subgroup (MulAut Y)) : Set (MulAut Y)) \ {1}

theorem ncard_hs08InnerOne {Y : Type*} [Group Y] {S J : Subgroup (MulAut Y)} (A : AutHyp Y S J) :
    (hs08InnerOne Y J).ncard = 15 := by
  unfold hs08InnerOne
  rw [Set.ncard_sdiff_singleton_of_mem (J ⊓ innerImage Y ⊤).one_mem]
  have : ((J ⊓ innerImage Y ⊤ : Subgroup (MulAut Y)) : Set (MulAut Y)).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact A.data.card_inner
  omega

theorem hs08_mem_or_iff {Y : Type*} [Group Y] {J : Subgroup (MulAut Y)} {R6 R10 : Set (MulAut Y)}
    (hU : R6 ∪ R10 = {x | x ∈ J ∧ x ∉ innerImage Y ⊤}) (a : MulAut Y) :
    (a ∈ hs08InnerOne Y J ∨ a ∈ R6 ∨ a ∈ R10) ↔ (a ∈ J ∧ a ≠ 1) := by
  constructor
  · rintro (h | h | h)
    · exact ⟨h.1.1, h.2⟩
    · have : a ∈ R6 ∪ R10 := Or.inl h
      rw [hU] at this
      exact ⟨this.1, fun h1 => this.2 (by rw [h1]; exact (innerImage Y ⊤).one_mem)⟩
    · have : a ∈ R6 ∪ R10 := Or.inr h
      rw [hU] at this
      exact ⟨this.1, fun h1 => this.2 (by rw [h1]; exact (innerImage Y ⊤).one_mem)⟩
  · rintro ⟨hJ, h1⟩
    by_cases hin : a ∈ innerImage Y ⊤
    · exact Or.inl ⟨⟨hJ, hin⟩, h1⟩
    · have : a ∈ R6 ∪ R10 := by rw [hU]; exact ⟨hJ, hin⟩
      rcases this with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

theorem hs08_disjoint_innerOne {Y : Type*} [Group Y] {J : Subgroup (MulAut Y)}
    {R : Set (MulAut Y)} (hR : ∀ x ∈ R, x ∉ innerImage Y ⊤) : Disjoint (hs08InnerOne Y J) R := by
  rw [Set.disjoint_left]
  intro x hx hxR
  exact hR x hxR hx.1.2

namespace MainCtx

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {Y : Type} [Group Y]
  {S J : Subgroup (MulAut Y)} (C : MainCtx G L t Y S J) [Finite G] [Fintype G]
include C

theorem finalData_of {R6 R10 : Set (MulAut Y)}
    (hU : R6 ∪ R10 = {x | x ∈ J ∧ x ∉ innerImage Y ⊤}) (hdisj : Disjoint R6 R10)
    (hc6 : R6.ncard = 6) (hc10 : R10.ncard = 10)
    (hn6 : ∀ d ∈ normalizer (J : Set (MulAut Y)), ∀ x ∈ R6, d * x * d⁻¹ ∈ R6)
    (ht6 : ∀ x ∈ R6, ∀ y ∈ R6, ∃ d ∈ normalizer (J : Set (MulAut Y)), d * x * d⁻¹ = y)
    (ht10 : ∀ x ∈ R10, ∀ y ∈ R10, ∃ d ∈ normalizer (J : Set (MulAut Y)), d * x * d⁻¹ = y)
    (hnonfixed : ∃ n ∈ normalizer ((C.pre J : Subgroup G) : Set G), n * t * n⁻¹ ≠ t) :
    FinalData (C.pre J) (normalizer ((C.pre J : Subgroup G) : Set G)) t
      (C.pset (hs08InnerOne Y J)) (C.pset R6) (C.pset R10) := by
  have hR6 : ∀ x ∈ R6, x ∉ innerImage Y ⊤ := fun x hx => by
    have : x ∈ R6 ∪ R10 := Or.inl hx
    rw [hU] at this
    exact this.2
  have hR10 : ∀ x ∈ R10, x ∉ innerImage Y ⊤ := fun x hx => by
    have : x ∈ R6 ∪ R10 := Or.inr hx
    rw [hU] at this
    exact this.2
  refine
    { card_E := C.card_E
      sq := fun x hx => C.E_sq hx
      comm := fun x hx y hy => C.E_comm hx hy
      t_mem := C.t_mem_pre
      t_ne := C.t_ne
      E_le := Subgroup.le_normalizer
      norm := fun n hn x hx => (Subgroup.mem_normalizer_iff.1 hn x).1 hx
      cent := fun n _ hc => C.E_cent hc
      card_N0 := C.card_N0
      mem_F := ?_
      disj12 := C.disjoint_pset (hs08_disjoint_innerOne hR6)
      disj13 := C.disjoint_pset (hs08_disjoint_innerOne hR10)
      disj23 := C.disjoint_pset hdisj
      card1 := by rw [C.card_pset, ncard_hs08InnerOne C.A]
      card2 := by rw [C.card_pset, hc6]
      card3 := by rw [C.card_pset, hc10]
      tmul1 := fun x hx => C.tmul_pset _ hx
      tmul2 := fun x hx => C.tmul_pset _ hx
      tmul3 := fun x hx => C.tmul_pset _ hx
      trans1 := C.trans_pset fun x hx y hy =>
        C.A.data.trans_inner x hx.1 hx.2 y hy.1 hy.2
      trans2 := C.trans_pset ht6
      trans3 := C.trans_pset ht10
      fix2 := fun n _ hnt hfix =>
        C.fix_pset (fun α hα => C.A.mem_of_centralizes_R6 hU hc6 hn6 hα) hnt hfix
      odd1 := ?_
      nonfixed := hnonfixed
      outer := ?_ }
  · intro x
    constructor
    · intro hx
      obtain ⟨h, rfl, hh⟩ : ∃ h : ↥(centralizer ({t} : Set G)), (h : G) = x ∧
          (C.π h ∈ hs08InnerOne Y J ∨ C.π h ∈ R6 ∨ C.π h ∈ R10) := by
        rcases hx with hx | hx | hx
        · obtain ⟨h, rfl, hB⟩ := C.mem_pset.1 hx
          exact ⟨h, rfl, Or.inl hB⟩
        · obtain ⟨h, rfl, hB⟩ := C.mem_pset.1 hx
          exact ⟨h, rfl, Or.inr (Or.inl hB)⟩
        · obtain ⟨h, rfl, hB⟩ := C.mem_pset.1 hx
          exact ⟨h, rfl, Or.inr (Or.inr hB)⟩
      obtain ⟨hJ, h1⟩ := (hs08_mem_or_iff hU _).1 hh
      refine ⟨(C.mem_pre_coe h).2 hJ, fun hx1 => h1 ?_, fun hxt => h1 ?_⟩
      · rw [show h = 1 from Subtype.ext hx1, map_one]
      · rw [show h = MainCtx.tH from Subtype.ext hxt, C.pi_tH]
    · rintro ⟨hxE, hx1, hxt⟩
      obtain ⟨h, hJ, rfl⟩ := C.mem_pre.1 hxE
      have h1 : C.π h ≠ 1 := by
        intro h1
        rcases (C.hπ.ker h).1 h1 with rfl | rfl
        · exact hx1 rfl
        · exact hxt rfl
      rcases (hs08_mem_or_iff hU _).2 ⟨hJ, h1⟩ with h2 | h2 | h2
      · exact Or.inl ((C.mem_pset_coe _ h).2 h2)
      · exact Or.inr (Or.inl ((C.mem_pset_coe _ h).2 h2))
      · exact Or.inr (Or.inr ((C.mem_pset_coe _ h).2 h2))
  · obtain ⟨z, hzJ, hzin, hz1, hodd1, hodd2⟩ := C.exists_odd_orbits
    exact ⟨z, (C.mem_pset_coe _ z).2 ⟨⟨hzJ, hzin⟩, hz1⟩, hodd1, hodd2⟩
  · intro n hn hne
    have hE : n * t * n⁻¹ ∈ C.pre J := (Subgroup.mem_normalizer_iff.1 hn t).1 C.t_mem_pre
    obtain ⟨h, hJ, hh⟩ := C.mem_pre.1 hE
    have hnL := C.not_mem_L_of_conj hne
    have hinn : C.π h ∉ innerImage Y ⊤ := fun hin => hnL (hh ▸ (C.hL h).1 hin)
    have h2 : C.π h ∈ R6 ∪ R10 := by rw [hU]; exact ⟨hJ, hinn⟩
    rcases h2 with h6 | h10
    · exact Or.inl (hh ▸ (C.mem_pset_coe _ h).2 h6)
    · exact Or.inr (hh ▸ (C.mem_pset_coe _ h).2 h10)

omit [Fintype G] in
theorem isolated : ∀ g : G, g * t * g⁻¹ ∈ centralizer ({t} : Set G) → g * t * g⁻¹ = t := by
  have : Fintype G := Fintype.ofFinite G
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hgH, hgt⟩ := hcon
  obtain ⟨R6, R10, hU, hdisj, hc6, hc10, hn6, -, ht6, ht10⟩ := C.A.data.outer_orbits
  have hnonfixed : ∃ n ∈ normalizer ((C.pre J : Subgroup G) : Set G), n * t * n⁻¹ ≠ t := by
    have hnL := C.not_mem_L_of_conj hgt
    set h : ↥(centralizer ({t} : Set G)) := ⟨g * t * g⁻¹, hgH⟩ with hh
    have hinn : C.π h ∉ innerImage Y ⊤ := fun hin => hnL ((C.hL h).1 hin)
    have hsq : C.π h * C.π h = 1 := by
      rw [← map_mul]
      have : h * h = 1 := Subtype.ext (by
        show g * t * g⁻¹ * (g * t * g⁻¹) = 1
        calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
          _ = 1 := by rw [C.t_sq]; group)
      rw [this, map_one]
    obtain ⟨a, ha⟩ := C.A.data.outer_involution (C.π h) hsq hinn
    obtain ⟨n₀, rfl⟩ := C.hπ.surj a
    have hs'E : (n₀ : G) * g * t * ((n₀ : G) * g)⁻¹ ∈ C.pre J := by
      have : (n₀ : G) * g * t * ((n₀ : G) * g)⁻¹ =
          ((n₀ * h * n₀⁻¹ : ↥(centralizer ({t} : Set G))) : G) := by
        show _ = (n₀ : G) * (g * t * g⁻¹) * (n₀ : G)⁻¹
        group
      rw [this, C.mem_pre_coe, map_mul, map_mul, map_inv]
      exact ha
    obtain ⟨n, hn, hnt⟩ := C.exists_fusion hs'E
    refine ⟨n, Subgroup.mem_normalizer_iff.2 hn, ?_⟩
    rw [hnt]
    intro hcontra
    apply hgt
    have hn₀t : (n₀ : G) * t = t * n₀ := Subgroup.mem_centralizer_singleton_iff.1 n₀.2
    calc g * t * g⁻¹ = (n₀ : G)⁻¹ * ((n₀ * g) * t * (n₀ * g)⁻¹) * n₀ := by group
      _ = (n₀ : G)⁻¹ * t * n₀ := by rw [hcontra]
      _ = (n₀ : G)⁻¹ * (t * n₀) := by group
      _ = t := by rw [← hn₀t]; group
  exact (C.finalData_of hU hdisj hc6 hc10 hn6 ht6 ht10 hnonfixed).false

end MainCtx

end CFSG.EvenSporadicStandard.M22Std
