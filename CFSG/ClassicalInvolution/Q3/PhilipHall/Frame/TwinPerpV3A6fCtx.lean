module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fVec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eSides
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Hx
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Sym
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

theorem stable_symmDiff {π : Equiv.Perm (Fin 8)} (hππ : ∀ z, π (π z) = z) (S : Finset (Fin 8))
    (z : Fin 8) :
    π z ∈ symmDiff S (S.map π.toEmbedding) ↔ z ∈ symmDiff S (S.map π.toEmbedding) := by
  have hs : ∀ w, π.symm w = π w := fun w => by
    apply π.injective
    rw [Equiv.apply_symm_apply, hππ]
  simp only [Finset.mem_symmDiff, Finset.mem_map_equiv, hs, hππ]
  tauto

theorem moved_of_mem_symmDiff {π : Equiv.Perm (Fin 8)} (hππ : ∀ z, π (π z) = z)
    (S : Finset (Fin 8)) {z : Fin 8} (hz : z ∈ symmDiff S (S.map π.toEmbedding)) : π z ≠ z := by
  intro h
  have hs : π.symm z = z := by
    apply π.injective
    rw [Equiv.apply_symm_apply, h]
  simp only [Finset.mem_symmDiff, Finset.mem_map_equiv, hs] at hz
  tauto

theorem fpf_of_union {π : Equiv.Perm (Fin 8)} (hππ : ∀ z, π (π z) = z)
    (hsign : Equiv.Perm.sign π = 1) {A B : Finset (Fin 8)} (hA : ∀ z ∈ A, π z ≠ z)
    (hB : ∀ z ∈ B, π z ≠ z) (hcard : 6 ≤ (A ∪ B).card) : ∀ z, π z ≠ z := by
  have hpow : π ^ 2 = 1 := by
    ext z
    simp [sq, Equiv.Perm.mul_apply, hππ]
  have hsg := Equiv.Perm.sign_of_pow_two_eq_one hpow
  set F : Finset (Fin 8) := Finset.univ.filter (fun z => π z = z) with hF
  have hFsub : F ⊆ (A ∪ B)ᶜ := by
    intro z hz
    rw [Finset.mem_compl, Finset.mem_union]
    rintro (h | h)
    · exact hA z h (Finset.mem_filter.mp hz).2
    · exact hB z h (Finset.mem_filter.mp hz).2
  have hFcard : F.card ≤ 2 := by
    have h1 := Finset.card_le_card hFsub
    rw [Finset.card_compl] at h1
    simp only [Fintype.card_fin] at h1
    omega
  have hcardfp : Fintype.card (Function.fixedPoints π) = F.card := by
    rw [hF, ← Fintype.card_subtype]
    rfl
  rw [hcardfp, hsign] at hsg
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz⟩ := hcon
  have hpos : 0 < F.card := Finset.card_pos.mpr ⟨z, by simp [hF, hz]⟩
  have hc : F.card = 1 ∨ F.card = 2 := by omega
  rcases hc with hc | hc <;> rw [hc] at hsg <;> simp at hsg <;> revert hsg <;> decide

theorem exists_comm_of_mem_commutator {Y : Type} [Group Y] {D : Subgroup Y} {x : Y}
    (hD : ∀ d ∈ D, d * d = 1) (hx : x * x = 1) (hnorm : ∀ d ∈ D, x * d * x⁻¹ ∈ D) {c : Y}
    (hc : c ∈ ⁅D, Subgroup.zpowers x⁆) : ∃ d ∈ D, c = ⁅d, x⁆ := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    have h1 := hD (a * b) (D.mul_mem ha hb)
    have h2 := hD a ha
    have h3 := hD b hb
    calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
      _ = (a * a) * b * a * (b * b) := by group
      _ = b * a := by rw [h2, h3]; group
  have hinv : ∀ d ∈ D, d⁻¹ = d := fun d hd => inv_eq_of_mul_eq_one_right (hD d hd)
  have hnorm' : ∀ d ∈ D, x * d * x ∈ D := fun d hd => by
    have := hnorm d hd
    rwa [hxinv] at this
  have hcomm : ∀ d ∈ D, ⁅d, x⁆ = d * (x * d * x) := by
    intro d hd
    rw [commutatorElement_def, hinv d hd, hxinv]
    group
  let Rg : Subgroup Y :=
    { carrier := {c | ∃ d ∈ D, c = ⁅d, x⁆}
      mul_mem' := by
        rintro _ _ ⟨d₁, hd₁, rfl⟩ ⟨d₂, hd₂, rfl⟩
        refine ⟨d₁ * d₂, D.mul_mem hd₁ hd₂, ?_⟩
        rw [hcomm _ hd₁, hcomm _ hd₂, hcomm _ (D.mul_mem hd₁ hd₂)]
        have e₁ := hnorm' d₁ hd₁
        have e₂ := hnorm' d₂ hd₂
        have h12 : x * (d₁ * d₂) * x = (x * d₁ * x) * (x * d₂ * x) := by
          calc x * (d₁ * d₂) * x = x * d₁ * (x * x) * d₂ * x := by rw [hx]; group
            _ = (x * d₁ * x) * (x * d₂ * x) := by group
        rw [h12]
        calc d₁ * (x * d₁ * x) * (d₂ * (x * d₂ * x))
            = d₁ * ((x * d₁ * x) * d₂) * (x * d₂ * x) := by group
          _ = d₁ * (d₂ * (x * d₁ * x)) * (x * d₂ * x) := by rw [hDab _ e₁ _ hd₂]
          _ = (d₁ * d₂) * ((x * d₁ * x) * (x * d₂ * x)) := by group
      one_mem' := ⟨1, D.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨d, hd, rfl⟩
        refine ⟨d⁻¹, D.inv_mem hd, ?_⟩
        rw [hcomm _ (D.inv_mem hd), hcomm _ hd, hinv d hd]
        have e := hnorm' d hd
        calc (d * (x * d * x))⁻¹ = (x * d * x)⁻¹ * d⁻¹ := by group
          _ = (x * d * x) * d := by rw [hinv _ e, hinv d hd]
          _ = d * (x * d * x) := hDab _ e _ hd }
  have hle : ⁅D, Subgroup.zpowers x⁆ ≤ Rg := by
    rw [Subgroup.commutator_le]
    intro d hd g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hk : x ^ k = 1 ∨ x ^ k = x := by
      have hxo : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
      obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
      · left
        rw [hm, zpow_mul, hxo, one_zpow]
      · right
        rw [hm, zpow_add, zpow_mul, hxo, one_zpow, one_mul, zpow_one]
    rcases hk with hk | hk
    · rw [hk]
      exact ⟨1, D.one_mem, by simp⟩
    · rw [hk]
      exact ⟨d, hd, rfl⟩
  exact hle hc

section Pkg

variable {Y : Type} [Group Y] {I D : Subgroup Y} (P : E8Pkg I D)

theorem ph_comm_vq {d x : Y} (hd : d ∈ D) (hx : x ∈ I) {S : Finset (Fin 8)} (hS : P.ph d = vq S) :
    P.ph ⁅d, x⁆ = vq (symmDiff S (S.map (P.rho x).toEmbedding)) := by
  have hdI := P.le hd
  have hdx : P.ph ⁅d, x⁆ = P.ph d * P.ph x * (P.ph d)⁻¹ * (P.ph x)⁻¹ := by
    rw [commutatorElement_def,
      P.ph_mul (I.mul_mem (I.mul_mem hdI hx) (I.inv_mem hdI)) (I.inv_mem hx),
      P.ph_mul (I.mul_mem hdI hx) (I.inv_mem hdI), P.ph_mul hdI hx, P.ph_inv hdI, P.ph_inv hx]
  rw [hdx, hS, vq_inv]
  have e : vq S * P.ph x * vq S * (P.ph x)⁻¹ = vq S * (P.ph x * vq S * (P.ph x)⁻¹) := by group
  rw [e, conj_vq, vq_mul]
  rfl

end Pkg

theorem card_union_cross : ∀ a ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin 8)),
    ∀ β ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin 8)), (a ∩ β).card = 2 →
      6 ≤ (a ∪ β).card ∧ 6 ≤ (a ∪ βᶜ).card ∧ 6 ≤ (aᶜ ∪ β).card ∧ 6 ≤ (aᶜ ∪ βᶜ).card := by
  decide +kernel

section Datum

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
  (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y)

include C in
theorem exists_beta : ∃ (a β : Finset (Fin 8)), a.card = 4 ∧ C.P.ph t = vq a ∧ β.card = 4 ∧
    (a ∩ β).card = 2 ∧ C.P.ph (y * t * y⁻¹) = vq β := by
  obtain ⟨a, ha, b₁, b₂, b₃, b₄, ht, hK, hK', hK₃, hK₄⟩ := C.sides
  have fr := C.fr
  obtain ⟨hne12, -, -, -, -, hne34⟩ := C.twins_ne
  have hq1 : a₁ * a₁ = t := Asc77.sq_eq_of_orderOf_four (C.uniq C.hKt) fr.h₁.1 fr.o₁
  have hq2 : a₂ * a₂ = t := Asc77.sq_eq_of_orderOf_four (C.uniq C.hK't) fr.h₂.1 fr.o₂
  have hq3 : a₃ * a₃ = t := Asc77.sq_eq_of_orderOf_four (C.uniq C.hK₃t) fr.h₃.1 fr.o₃
  have hq4 : a₄ * a₄ = t := Asc77.sq_eq_of_orderOf_four (C.uniq C.hK₄t) fr.h₄.1 fr.o₄
  obtain ⟨h12a, h12b⟩ := C.kk_ne C.hKt C.hK't hne12 fr.h₁.1 fr.h₂.1 hq1 hq2
  obtain ⟨h34a, h34b⟩ := C.kk_ne C.hK₃t C.hK₄t hne34 fr.h₃.1 fr.h₄.1 hq3 hq4
  have hu : a₁ * a₂ ∈ ae6D Ω[R] W (u₁ * u₂) := by rw [fr.hu]; exact C.u_mem_D
  have h34D : a₃ * a₄ ∈ ae6D Ω[R] W (u₁ * u₂) := by
    have e : a₃ * a₄ = (a₁ * a₂)⁻¹ * (y * t * y⁻¹) := by rw [fr.hy]; group
    rw [e]
    exact (ae6D Ω[R] W (u₁ * u₂)).mul_mem ((ae6D Ω[R] W (u₁ * u₂)).inv_mem hu) C.tau_mem_D
  have htI : t ∈ C.I := C.t_mem_I
  have ha₁I : a₁ ∈ C.I := C.twin_le_I C.hKt fr.h₁.1
  have ha₂I : a₂ ∈ C.I := C.twin_le_I C.hK't fr.h₂.1
  have ha₃I : a₃ ∈ C.I := C.twin_le_I C.hK₃t fr.h₃.1
  have ha₄I : a₄ ∈ C.I := C.twin_le_I C.hK₄t fr.h₄.1
  have h12I : a₁ * a₂ ∈ C.I := C.I.mul_mem ha₁I ha₂I
  have h34I : a₃ * a₄ ∈ C.I := C.I.mul_mem ha₃I ha₄I
  have hnea12 : C.P.ph (a₁ * a₂) ≠ vq a := fun h =>
    h12b (C.P.ph_inj h12I htI (by rw [h, ht]))
  have hnea34 : C.P.ph (a₃ * a₄) ≠ vq aᶜ := fun h =>
    h34b (C.P.ph_inj h34I htI (by rw [h, vq_compl, ht]))
  obtain ⟨S₁, hS₁a, hS₁c, hS₁⟩ := C.P.w2 (C.twin_le_I C.hKt) (C.twin_le_I C.hK't) hK hK'
    fr.h₁.1 fr.h₂.1 hu h12a hnea12
  obtain ⟨S₂, hS₂a, hS₂c, hS₂⟩ := C.P.w2 (C.twin_le_I C.hK₃t) (C.twin_le_I C.hK₄t) hK₃ hK₄
    fr.h₃.1 fr.h₄.1 h34D h34a hnea34
  have hdisjA : Disjoint S₂ a := Finset.disjoint_of_subset_left hS₂a disjoint_compl_left
  have hdisj : Disjoint S₁ S₂ := (Finset.disjoint_of_subset_right hS₁a hdisjA).symm
  have hsd : symmDiff S₁ S₂ = S₁ ∪ S₂ := hdisj.symmDiff_eq_sup
  refine ⟨a, symmDiff S₁ S₂, ha, ht, ?_, ?_, ?_⟩
  · rw [hsd, Finset.card_union_of_disjoint hdisj, hS₁c, hS₂c]
  · rw [hsd, Finset.inter_union_distrib_left, Finset.inter_eq_right.mpr hS₁a,
      Finset.disjoint_iff_inter_eq_empty.mp hdisjA.symm, Finset.union_empty, hS₁c]
  · rw [fr.hy, mul_assoc, C.P.ph_mul h12I h34I, hS₁, hS₂, vq_mul]

include C in
theorem ae6P_le_I : ae6P Ω[R] t ≤ C.I :=
  iSup₂_le fun _ hJ => C.twin_le_I ⟨hJ.1, t, C.H.ex.1.datum.hz, hJ.2⟩

include C in
theorem exists_cent_conj {h : Y} (hx : AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h) :
    ∃ j ∈ C.I, j * (h * (y * t * y⁻¹) * h⁻¹) * j⁻¹ = h * (y * t * y⁻¹) * h⁻¹ ∧
      j * t * j⁻¹ = y * t * y⁻¹ := by
  obtain ⟨hhC, hxD, hcomm⟩ := hx
  have hinv := conjInvariant_conjClass (tightCore R)
  set τ := y * t * y⁻¹ with hτ
  set x := h * τ * h⁻¹ with hxdef
  set P := C.P with hP
  have hhc : h * t * h⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hhC
    rw [hhC, mul_inv_cancel_right]
  obtain ⟨-, hτP⟩ := A6Hx.t_tau_mem_ae6P C.H C.fr
  have hxP : x ∈ ae6P Ω[R] t := A6Hx.conj_mem_ae6P hinv hhc hτP
  have hxI : x ∈ C.I := ae6P_le_I C hxP
  have htt : t * t = 1 := C.H.ex.1.datum.hz.sq
  have hττ : τ * τ = 1 := by
    rw [hτ]
    calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hxx : x * x = 1 := by
    rw [hxdef]
    calc h * τ * h⁻¹ * (h * τ * h⁻¹) = h * (τ * τ) * h⁻¹ := by group
      _ = 1 := by rw [hττ]; group
  have hnormD : ∀ d ∈ ae6D Ω[R] W (u₁ * u₂), x * d * x⁻¹ ∈ ae6D Ω[R] W (u₁ * u₂) :=
    fun d hd => P.conj_mem_D hxI hd
  have hcl : ∀ c ∈ ({t, τ} : Set Y), c ∈ ⁅ae6D Ω[R] W (u₁ * u₂), Subgroup.zpowers x⁆ := by
    intro c hc
    rw [hcomm]
    exact Subgroup.subset_closure hc
  obtain ⟨d₁, hd₁, hd₁t⟩ := exists_comm_of_mem_commutator C.hDsq hxx hnormD (hcl t (by simp))
  obtain ⟨d₂, hd₂, hd₂τ⟩ := exists_comm_of_mem_commutator C.hDsq hxx hnormD (hcl τ (by simp))
  obtain ⟨a, β, ha, hta, hβ, haβ, hτβ⟩ := exists_beta C
  obtain ⟨S₁, -, hS₁⟩ := P.vec_of_mem_D hd₁
  obtain ⟨S₂, -, hS₂⟩ := P.vec_of_mem_D hd₂
  set π := P.rho x with hπ
  have hππ : ∀ z, π (π z) = z := by
    intro z
    have h1 : π * π = 1 := by
      rw [hπ, ← P.rho_mul hxI hxI, hxx, P.rho_one]
    have := congrArg (fun σ : Equiv.Perm (Fin 8) => σ z) h1
    simpa [Equiv.Perm.mul_apply] using this
  have hsign : Equiv.Perm.sign π = 1 := P.sign_rho hxI
  have e₁ : vq a = vq (symmDiff S₁ (S₁.map π.toEmbedding)) := by
    rw [← hta]
    exact (congrArg P.ph hd₁t).trans (ph_comm_vq P hd₁ hxI hS₁)
  have e₂ : vq β = vq (symmDiff S₂ (S₂.map π.toEmbedding)) := by
    rw [← hτβ]
    exact (congrArg P.ph hd₂τ).trans (ph_comm_vq P hd₂ hxI hS₂)
  have c₁ := vq_eq_iff.mp e₁
  have c₂ := vq_eq_iff.mp e₂
  have hpa : ∀ z, π z ∈ a ↔ z ∈ a := by
    intro z
    rcases c₁ with h | h
    · rw [← h]; exact stable_symmDiff hππ S₁ z
    · have := stable_symmDiff hππ S₁ z
      rw [h, Finset.mem_compl, Finset.mem_compl] at this
      exact not_iff_not.mp this
  have hpβ : ∀ z, π z ∈ β ↔ z ∈ β := by
    intro z
    rcases c₂ with h | h
    · rw [← h]; exact stable_symmDiff hππ S₂ z
    · have := stable_symmDiff hππ S₂ z
      rw [h, Finset.mem_compl, Finset.mem_compl] at this
      exact not_iff_not.mp this
  have hcard6 : 6 ≤ (symmDiff S₁ (S₁.map π.toEmbedding) ∪ symmDiff S₂ (S₂.map π.toEmbedding)).card := by
    have key := card_union_cross a (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ha⟩) β
      (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hβ⟩) haβ
    rcases c₁ with h | h <;> rcases c₂ with h' | h' <;> rw [h, h'] <;> omega
  have hfix : ∀ z, π z ≠ z :=
    fpf_of_union hππ hsign (fun z hz => moved_of_mem_symmDiff hππ S₁ hz)
      (fun z hz => moved_of_mem_symmDiff hππ S₂ hz) hcard6
  have hXX : P.ph x * P.ph x = 1 := by
    rw [← P.ph_mul hxI hxI, hxx, P.ph_one]
  obtain ⟨J, hJ, hJX, hJa⟩ := exists_cent_vq (P.ph_mem hxI) hXX ha hβ haβ hfix hpa hpβ
  have hJr : J ∈ P.φ.range := by rw [P.range_eq]; exact hJ
  obtain ⟨j, hj⟩ := hJr
  have hjph : P.ph (j : Y) = J := by rw [P.ph_of_mem j.2]; exact hj
  have hjI : (j : Y) ∈ C.I := j.2
  have htI : t ∈ C.I := C.t_mem_I
  have hτI : τ ∈ C.I := P.le C.tau_mem_D
  refine ⟨j, hjI, ?_, ?_⟩
  · apply P.ph_inj (C.I.mul_mem (C.I.mul_mem hjI hxI) (C.I.inv_mem hjI)) hxI
    rw [P.ph_mul (C.I.mul_mem hjI hxI) (C.I.inv_mem hjI), P.ph_mul hjI hxI, P.ph_inv hjI, hjph]
    calc J * P.ph x * J⁻¹ = P.ph x * J * J⁻¹ := by rw [hJX]
      _ = P.ph x := by group
  · apply P.ph_inj (C.I.mul_mem (C.I.mul_mem hjI htI) (C.I.inv_mem hjI)) hτI
    rw [P.ph_mul (C.I.mul_mem hjI htI) (C.I.inv_mem hjI), P.ph_mul hjI htI, P.ph_inv hjI, hjph,
      hta, hτβ]
    exact hJa

end Datum

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f
