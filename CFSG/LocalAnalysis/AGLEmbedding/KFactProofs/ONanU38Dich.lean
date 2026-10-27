module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Inner
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Elem

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem mem_centralizer_of_actOn_eq_one {X : Type*} [Group X] (K : Subgroup X) [K.Normal]
    {G : Type*} [Group G] (e : K ≃* G) {x : X} (hx : actOn K e x = 1) :
    x ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 := coe_actOn_symm K e x (e ⟨k, hk⟩)
  rw [hx, MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
  have h2 : k = x * k * x⁻¹ := h1
  calc k * x = x * k * x⁻¹ * x := by rw [← h2]
    _ = x * k := by group

theorem isElemAbelian_range {A H : Type*} [Group A] [Group H] (hcomm : ∀ a b : A, a * b = b * a)
    (hexp : ∀ a : A, a ^ 3 = 1) (f : A →* H) : CFSG.Open.IsElemAbelian 3 f.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : H) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hexp, map_one]

theorem false_of_inner_psu {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (e : K ≃* unitaryPSU hU 3) (hC : ∀ c ∈ Subgroup.centralizer (K : Set X), c = 1)
    (E : Subgroup X) (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : 27 ≤ Nat.card E)
    (hin : ∀ x ∈ E, actOn K e x ∈ (psuConj hU).range) : False := by
  set ψ : E →* MulAut (unitaryPSU hU 3) := (actOn K e).comp E.subtype with hψdef
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hC _ (mem_centralizer_of_actOn_eq_one K e hx))
  have hBr : ψ.range ≤ (psuConj hU).range := by
    rintro _ ⟨x, rfl⟩
    exact hin x x.2
  have hB : CFSG.Open.IsElemAbelian 3 ψ.range :=
    isElemAbelian_range (fun a b => hE.1.is_comm.comm a b) (fun a => Subtype.ext (hE.2 a a.2)) ψ
  have h1 := card_le_nine_psu ψ.range hBr hB
  have h2 : Nat.card ψ.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  omega

theorem false_of_inner_su {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (e : K ≃* SU) (hCK : ∀ c ∈ Subgroup.centralizer (K : Set X), c ∈ K)
    (E : Subgroup X) (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : 27 ≤ Nat.card E)
    (hin : ∀ x ∈ E, actOn K e x ∈ (suConj hU).range) : False := by
  classical
  set δ : E →* GF64ˣ := deltaOn (actOn K e) E hin with hδdef
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hrange : Nat.card δ.range ≤ 3 := by
    calc Nat.card δ.range ≤ Nat.card (rootsOfUnity 3 GF64) := by
          apply Subgroup.card_le_of_le
          rintro _ ⟨x, rfl⟩
          obtain ⟨h, hh⟩ := hin x x.2
          rw [mem_rootsOfUnity]
          show deltaOn (actOn K e) E hin x ^ 3 = 1
          rw [deltaOn_eq x h hh.symm]
          exact deltaGU_cube h
      _ ≤ 3 := card_rootsOfUnity GF64 3
  have hker : 9 ≤ Nat.card δ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range δ
    by_contra hlt
    push Not at hlt
    have : Nat.card δ.ker * Nat.card δ.range ≤ 8 * 3 := Nat.mul_le_mul (by omega) hrange
    omega
  have hkerK : ∀ x : E, δ x = 1 → (x : X) ∈ K := by
    intro x hx
    obtain ⟨h, hh⟩ := hin x x.2
    have hδ : deltaGU h = 1 := by
      rw [← deltaOn_eq x h hh.symm]
      exact hx
    obtain ⟨g, hg⟩ := exists_conj_of_delta_eq_one h hδ
    have h1 : actOn K e ((e.symm g : K) : X) = actOn K e (x : X) := by
      rw [actOn_coe K e (e.symm g), MulEquiv.apply_symm_apply, ← hg, ← hh]
    have h2 : actOn K e ((x : X) * ((e.symm g : K) : X)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel]
    have h3 := hCK _ (mem_centralizer_of_actOn_eq_one K e h2)
    have h4 : (x : X) = ((x : X) * ((e.symm g : K) : X)⁻¹) * ((e.symm g : K) : X) := by group
    rw [h4]
    exact K.mul_mem h3 (e.symm g).2
  by_cases hall : ∀ x : E, δ x = 1
  ·
    have hEK : E ≤ K := fun x hx => hkerK ⟨x, hx⟩ (hall ⟨x, hx⟩)
    set ι : E →* SU := e.toMonoidHom.comp (Subgroup.inclusion hEK) with hι
    have hιinj : Function.Injective ι :=
      e.injective.comp (Subgroup.inclusion_injective hEK)
    have hT : CFSG.Open.IsElemAbelian 3 ι.range :=
      isElemAbelian_range (fun a b => hE.1.is_comm.comm a b) (fun a => Subtype.ext (hE.2 a a.2)) ι
    have h1 := card_le_nine_elem_su ι.range hT
    have h2 : Nat.card ι.range = Nat.card E :=
      (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm
    omega
  · push Not at hall
    obtain ⟨x₀, hx₀⟩ := hall
    have hex : ∃ y : δ.ker, e ⟨(y.1 : E).1, hkerK y.1 (MonoidHom.mem_ker.1 y.2)⟩ ∉
        unitaryScalars hU 3 := by
      by_contra hno
      push Not at hno
      have hinj : Function.Injective (fun y : δ.ker =>
          (⟨e ⟨(y.1 : E).1, hkerK y.1 (MonoidHom.mem_ker.1 y.2)⟩, hno y⟩ :
            unitaryScalars hU 3)) := by
        intro s t hst
        have h1 := e.injective (congrArg (fun u : unitaryScalars hU 3 => (u : SU)) hst)
        have h2 := congrArg Subtype.val h1
        exact Subtype.ext (Subtype.ext h2)
      have := Nat.card_le_card_of_injective _ hinj
      rw [card_scalars] at this
      omega
    obtain ⟨⟨y₀, hy₀k⟩, hy₀⟩ := hex
    obtain ⟨h, hh⟩ := hin x₀ x₀.2
    set yK : K := ⟨(y₀ : X), hkerK y₀ (MonoidHom.mem_ker.1 hy₀k)⟩ with hyK
    set a : SU := e yK with ha
    refine false_of_commuting_outer (h := (h : GL (Fin 3) GF64)) (a := (a : GL (Fin 3) GF64))
      h.2 a.2 ?_ ?_ ?_ ?_ ?_
    · intro hmem
      apply hy₀
      rw [unitaryScalars_eq hU (by norm_num), Subgroup.mem_subgroupOf]
      exact hmem
    · have h1 : yK ^ 3 = 1 := Subtype.ext (hE.2 y₀ y₀.2)
      have h2 : a ^ 3 = 1 := by rw [ha, ← map_pow, h1, map_one]
      simpa using congrArg (fun s : SU => (s : GL (Fin 3) GF64)) h2
    · have h1 : suConj hU (h ^ 3) = 1 := by
        rw [map_pow, hh, ← map_pow, hE.2 x₀ x₀.2, map_one]
      exact (suConj_eq_one_iff (h ^ 3)).1 h1
    · intro hd
      apply hx₀
      rw [show δ x₀ = deltaGU h from deltaOn_eq x₀ h hh.symm]
      exact Units.ext (by rw [coe_deltaGU, hd]; rfl)
    · have h1 : actOn K e (x₀ : X) a = a := by
        apply e.symm.injective
        apply Subtype.ext
        rw [coe_actOn_symm]
        have : e.symm a = yK := by rw [ha]; exact e.symm_apply_apply yK
        rw [this]
        show (x₀ : X) * (y₀ : X) * (x₀ : X)⁻¹ = (y₀ : X)
        rw [hEcomm _ x₀.2 _ y₀.2]
        group
      have h2 : ((suConj hU h a : SU) : GL (Fin 3) GF64) = (a : GL (Fin 3) GF64) := by
        rw [hh]
        exact congrArg (fun s : SU => (s : GL (Fin 3) GF64)) h1
      rw [coe_suConj, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm

end CFSG.AGLEmbedding.ChevOuter.U38
