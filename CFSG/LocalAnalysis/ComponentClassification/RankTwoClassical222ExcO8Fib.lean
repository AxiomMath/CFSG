module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8EInputs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAut
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Multiplier
public import CFSG.RankThree.PerfectCover.HopfCentralCoversLift

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcO8E

open Subgroup CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.EvenSmallLie.OmegaEight.Cover CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier

@[expose] def pairHom : Equiv.Perm (Fin 240) × Equiv.Perm (Fin 240) →* Equiv.Perm (Fin 480) :=
  (Equiv.permCongrHom finSumFinEquiv).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin 240) (Fin 240))

theorem pairHom_injective : Function.Injective pairHom :=
  (Equiv.permCongrHom finSumFinEquiv).injective.comp Equiv.Perm.sumCongrHom_injective

theorem pairHom_apply (x : Equiv.Perm (Fin 240) × Equiv.Perm (Fin 240)) (y : Fin 480) :
    pairHom x y = finSumFinEquiv (Sum.map x.1 x.2 (finSumFinEquiv.symm y)) := rfl

theorem pairHom_apply_lt (x : Equiv.Perm (Fin 240) × Equiv.Perm (Fin 240)) {j : ℕ} (hj : j < 240) :
    (pairHom x ⟨j, by omega⟩ : ℕ) = (x.1 ⟨j, hj⟩ : ℕ) := by
  have e : finSumFinEquiv.symm (⟨j, by omega⟩ : Fin 480) =
      (Sum.inl ⟨j, hj⟩ : Fin 240 ⊕ Fin 240) := by
    rw [show (⟨j, by omega⟩ : Fin 480) = Fin.castAdd 240 (⟨j, hj⟩ : Fin 240) from rfl,
      finSumFinEquiv_symm_apply_castAdd]
  rw [pairHom_apply, e, Sum.map_inl, finSumFinEquiv_apply_left, Fin.val_castAdd]

theorem pairHom_apply_ge (x : Equiv.Perm (Fin 240) × Equiv.Perm (Fin 240)) {j : ℕ} (hj : j < 480)
    (hj' : 240 ≤ j) :
    (pairHom x ⟨j, hj⟩ : ℕ) = (x.2 ⟨j - 240, by omega⟩ : ℕ) + 240 := by
  have e : finSumFinEquiv.symm (⟨j, hj⟩ : Fin 480) =
      (Sum.inr ⟨j - 240, by omega⟩ : Fin 240 ⊕ Fin 240) := by
    have e1 : (⟨j, hj⟩ : Fin 480) = Fin.natAdd 240 (⟨j - 240, by omega⟩ : Fin 240) := by
      ext
      simp only [Fin.val_natAdd]
      omega
    rw [e1, finSumFinEquiv_symm_apply_natAdd]
  rw [pairHom_apply, e, Sum.map_inr, finSumFinEquiv_apply_right, Fin.val_natAdd]
  omega

theorem rep_pairA {t u : Array ℕ} {a b : Equiv.Perm (Fin 240)} (ht : Rep 240 t a)
    (hu : Rep 240 u b) : Rep 480 (pairA t u) (pairHom (a, b)) := by
  intro x
  rw [pairA, getElem!_ofFn_nat _ x.2]
  dsimp only
  by_cases hx : (x : ℕ) < 240
  · simp only [hx, ↓reduceIte]
    rw [ht.apply hx]
    have := pairHom_apply_lt (a, b) hx
    rw [show (⟨(x : ℕ), by omega⟩ : Fin 480) = x from rfl] at this
    rw [this]
  · simp only [hx, ↓reduceIte]
    rw [hu.apply (by omega)]
    have := pairHom_apply_ge (a, b) x.2 (by omega)
    rw [show (⟨(x : ℕ), x.2⟩ : Fin 480) = x from rfl] at this
    rw [this]

section Fib

@[expose] def eFib : Subgroup (wPlus × wPlus) :=
  (pHat.comp (MonoidHom.fst wPlus wPlus)).eqLocus
    ((triality.comp pHat).comp (MonoidHom.snd wPlus wPlus))

theorem mem_eFib {x : wPlus × wPlus} : x ∈ eFib ↔ pHat x.1 = triality (pHat x.2) := Iff.rfl

@[expose] def qE : eFib →* omegaT := (pHat.comp (MonoidHom.fst wPlus wPlus)).comp eFib.subtype

theorem qE_apply (x : eFib) : qE x = pHat (x : wPlus × wPlus).1 := rfl

theorem qE_surjective : Function.Surjective qE := by
  intro g
  obtain ⟨a, ha⟩ := pHat_surjective g
  obtain ⟨b, hb⟩ := pHat_surjective (triality (triality g))
  refine ⟨⟨(a, b), ?_⟩, ha⟩
  rw [mem_eFib]
  change pHat a = triality (pHat b)
  rw [ha, hb, triality_cube]

theorem pHat_eq_one_iff {a : wPlus} : pHat a = 1 ↔ a = 1 ∨ a = zPlus := by
  have h := pHat_eq_iff (x := 1) (y := a)
  rw [map_one, one_mul] at h
  exact ⟨fun ha => h.1 ha.symm, fun ha => (h.2 ha).symm⟩

theorem triality_eq_one_iff {g : omegaT} : triality g = 1 ↔ g = 1 := by
  constructor
  · intro h
    apply triality_injective
    rw [h, map_one]
  · rintro rfl
    exact map_one _

theorem mem_ker_qE {x : eFib} : x ∈ qE.ker ↔
    ((x : wPlus × wPlus).1 = 1 ∨ (x : wPlus × wPlus).1 = zPlus) ∧
      ((x : wPlus × wPlus).2 = 1 ∨ (x : wPlus × wPlus).2 = zPlus) := by
  rw [MonoidHom.mem_ker, qE_apply]
  have hx := mem_eFib.1 x.2
  constructor
  · intro h
    refine ⟨pHat_eq_one_iff.1 h, pHat_eq_one_iff.1 ?_⟩
    rw [h] at hx
    exact triality_eq_one_iff.1 hx.symm
  · rintro ⟨h1, -⟩
    exact pHat_eq_one_iff.2 h1

theorem zPlus_central (g : wPlus) : g * zPlus = zPlus * g :=
  mem_center_iff.1 zPlus_mem_center g

theorem ker_qE_le_center : qE.ker ≤ center eFib := by
  intro x hx
  rw [mem_center_iff]
  intro g
  obtain ⟨h1, h2⟩ := mem_ker_qE.1 hx
  apply Subtype.ext
  change (g : wPlus × wPlus) * (x : wPlus × wPlus) = (x : wPlus × wPlus) * (g : wPlus × wPlus)
  refine Prod.ext ?_ ?_
  · change (g : wPlus × wPlus).1 * (x : wPlus × wPlus).1 =
      (x : wPlus × wPlus).1 * (g : wPlus × wPlus).1
    rcases h1 with h | h <;> rw [h]
    · rw [mul_one, one_mul]
    · exact zPlus_central _
  · change (g : wPlus × wPlus).2 * (x : wPlus × wPlus).2 =
      (x : wPlus × wPlus).2 * (g : wPlus × wPlus).2
    rcases h2 with h | h <;> rw [h]
    · rw [mul_one, one_mul]
    · exact zPlus_central _

theorem pHat_zPlus : pHat zPlus = 1 := pHat_eq_one_iff.2 (Or.inr rfl)

@[expose] def zElt (a b : Bool) : eFib :=
  ⟨(if a then zPlus else 1, if b then zPlus else 1), by
    rw [mem_eFib]
    cases a <;> cases b <;> simp [pHat_zPlus]⟩

theorem zElt_mem_ker (a b : Bool) : zElt a b ∈ qE.ker := by
  rw [mem_ker_qE]
  cases a <;> cases b <;> simp [zElt]

theorem zElt_injective : Function.Injective (fun p : Bool × Bool => zElt p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h' := congrArg (fun x : eFib => (x : wPlus × wPlus)) h
  simp only [zElt, Prod.mk.injEq] at h'
  have hz : zPlus ≠ 1 := zPlus_ne_one
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [eq_comm]

theorem card_ker_qE : Nat.card qE.ker = 4 := by
  have hsurj : Function.Surjective (fun p : Bool × Bool => (⟨zElt p.1 p.2, zElt_mem_ker _ _⟩ :
      qE.ker)) := by
    rintro ⟨x, hx⟩
    obtain ⟨h1, h2⟩ := mem_ker_qE.1 hx
    refine ⟨((x : wPlus × wPlus).1 = zPlus, (x : wPlus × wPlus).2 = zPlus), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hz : zPlus ≠ 1 := zPlus_ne_one
    simp only [zElt]
    refine Prod.ext ?_ ?_
    · rcases h1 with h | h <;> simp [h, hz.symm]
    · rcases h2 with h | h <;> simp [h, hz.symm]
  have hinj : Function.Injective (fun p : Bool × Bool => (⟨zElt p.1 p.2, zElt_mem_ker _ _⟩ :
      qE.ker)) := fun p q h => zElt_injective (congrArg Subtype.val h)
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)]
  simp

theorem card_eFib : Nat.card eFib = 696729600 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup qE.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective qE qE_surjective).toEquiv,
    card_omegaT, card_ker_qE] at h1
  rw [h1]

@[expose] def wElt (i : ℕ) : wPlus := if h : i < 8 then ⟨omLift i, omLift_mem h⟩ else 1

@[expose] def eEltPair (i : ℕ) : wPlus × wPlus := (wElt (rhoPerm.getD i 0), wElt i)

theorem eEltPair_mem {i : ℕ} (hi : i < 8) : eEltPair i ∈ eFib := by
  rw [mem_eFib]
  have hr := rhoPerm_lt hi
  simp only [eEltPair, wElt, hi, hr, ↓reduceDIte]
  rw [pHat_omLift hr, pHat_omLift hi]
  apply Subtype.ext
  rw [coe_triality]
  exact (conj_gen_rho hi).symm

@[expose] def eElt (i : ℕ) : eFib := if h : i < 8 then ⟨eEltPair i, eEltPair_mem h⟩ else 1

theorem map_commutator_qE : (commutator eFib).map qE = ⊤ := by
  have := isPerfect_omegaT
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 qE_surjective, ← commutator_def]
  exact Group.IsPerfect.commutator_eq_top

theorem exists_mul_ker (x : eFib) : ∃ c ∈ commutator eFib, ∃ k ∈ qE.ker, x = c * k := by
  have hx : qE x ∈ (commutator eFib).map qE := by rw [map_commutator_qE]; trivial
  obtain ⟨c, hc, hcx⟩ := hx
  refine ⟨c, hc, c⁻¹ * x, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]

theorem eq_zElt_of_mem_ker {k : eFib} (hk : k ∈ qE.ker) : ∃ a b, k = zElt a b := by
  obtain ⟨h1, h2⟩ := mem_ker_qE.1 hk
  have hz : zPlus ≠ 1 := zPlus_ne_one
  refine ⟨decide ((k : wPlus × wPlus).1 = zPlus), decide ((k : wPlus × wPlus).2 = zPlus), ?_⟩
  apply Subtype.ext
  simp only [zElt]
  refine Prod.ext ?_ ?_
  · rcases h1 with h | h <;> simp [h, hz.symm]
  · rcases h2 with h | h <;> simp [h, hz.symm]

theorem sq_eq_one_of_mem_ker {k : eFib} (hk : k ∈ qE.ker) : k ^ 2 = 1 := by
  obtain ⟨a, b, rfl⟩ := eq_zElt_of_mem_ker hk
  have hzz : zPlus * zPlus = 1 := Subtype.ext zPerm_mul_self
  apply Subtype.ext
  change ((zElt a b : wPlus × wPlus) * (zElt a b : wPlus × wPlus)) = 1
  simp only [zElt]
  refine Prod.ext ?_ ?_ <;> cases a <;> cases b <;> simp [hzz]

theorem sq_mem_commutator (x : eFib) : x ^ 2 ∈ commutator eFib := by
  obtain ⟨c, hc, k, hk, rfl⟩ := exists_mul_ker x
  have hkc : c * k = k * c := mem_center_iff.1 (ker_qE_le_center hk) c
  rw [(show Commute c k from hkc).mul_pow, sq_eq_one_of_mem_ker hk, mul_one]
  exact pow_mem hc 2

theorem zElt_mul : zElt true false * zElt false true = zElt true true := by
  apply Subtype.ext
  change ((zElt true false : wPlus × wPlus) * (zElt false true : wPlus × wPlus)) = _
  simp [zElt]

theorem isPerfect_eFib (h04 : (eElt 0 * eElt 4) ^ 2 = zElt false true)
    (h46 : (eElt 4 * eElt 6) ^ 2 = zElt true false) : Group.IsPerfect eFib := by
  have hz1 : zElt true false ∈ commutator eFib := h46 ▸ sq_mem_commutator _
  have hz2 : zElt false true ∈ commutator eFib := h04 ▸ sq_mem_commutator _
  have hz : ∀ a b, zElt a b ∈ commutator eFib := by
    intro a b
    cases a <;> cases b
    · have : zElt false false = 1 := by
        apply Subtype.ext
        simp [zElt]
      rw [this]
      exact one_mem _
    · exact hz2
    · exact hz1
    · rw [← zElt_mul]
      exact mul_mem hz1 hz2
  refine ⟨eq_top_iff.2 fun x _ => ?_⟩
  obtain ⟨c, hc, k, hk, rfl⟩ := exists_mul_ker x
  obtain ⟨a, b, rfl⟩ := eq_zElt_of_mem_ker hk
  exact mul_mem hc (hz a b)

theorem exists_mulEquiv_eFib (hE : Group.IsPerfect eFib)
    {H : Type} [Group H] [Finite H] (hH : Group.IsPerfect H) (hZ : Nat.card (center H) = 4)
    (hL : CFSG.Blueprint.LieModel (H ⧸ center H) .POmegaPlus 4 2 1) :
    ∃ θ : H ≃* eFib, (center H).map θ.toMonoidHom = qE.ker := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hL
  set p : H →* omegaT := e.toMonoidHom.comp (QuotientGroup.mk' (center H)) with hpdef
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : p.ker = center H := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center H) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h2 : IsPGroup 2 p.ker := by
    rw [hker]
    exact IsPGroup.of_card (n := 2) (by rw [hZ]; norm_num)
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier omegaT) = Nat.card qE.ker * 1 := by
    rw [card_ker_qE, mul_one]
    exact card_ker_piU
  obtain ⟨α, hα, hpα⟩ := CFSG.RankThree.PerfectCover.exists_lift_of_odd_index hE hH qE
    qE_surjective ker_qE_le_center p hp hker.le h2 1 odd_one hM
  have hcard : Nat.card eFib = Nat.card H := by
    rw [card_eFib, Subgroup.card_eq_card_quotient_mul_card_subgroup (center H), hZ,
      Nat.card_congr e.toEquiv, card_omegaT]
  have hbij : Function.Bijective α := hα.bijective_of_nat_card_le hcard.le
  set θ := (MulEquiv.ofBijective α hbij).symm with hθ
  refine ⟨θ, ?_⟩
  have hmap : qE.ker.map α ≤ center H := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← hker, MonoidHom.mem_ker]
    have := DFunLike.congr_fun hpα k
    rw [MonoidHom.comp_apply] at this
    rw [this]
    exact hk
  have hmapc : qE.ker.map α = center H := by
    refine Subgroup.eq_of_le_of_card_ge hmap ?_
    rw [hZ, Subgroup.card_map_of_injective hbij.1, card_ker_qE]
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [← hmapc] at hh
    obtain ⟨k, hk, rfl⟩ := hh
    change (MulEquiv.ofBijective α hbij).symm (MulEquiv.ofBijective α hbij k) ∈ qE.ker
    rw [MulEquiv.symm_apply_apply]
    exact hk
  · intro hx
    refine ⟨α x, ?_, ?_⟩
    · rw [← hmapc]
      exact ⟨x, hx, rfl⟩
    · change (MulEquiv.ofBijective α hbij).symm (MulEquiv.ofBijective α hbij x) = x
      rw [MulEquiv.symm_apply_apply]

@[expose] def eHom : eFib →* Equiv.Perm (Fin 480) :=
  pairHom.comp ((wPlus.subtype.prodMap wPlus.subtype).comp eFib.subtype)

theorem eHom_injective : Function.Injective eHom := by
  intro x y h
  have h1 := pairHom_injective h
  apply Subtype.ext
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact congrArg Prod.fst h1
  · exact congrArg Prod.snd h1

@[expose] def e480 : Subgroup (Equiv.Perm (Fin 480)) := eHom.range

@[expose] def eEquiv : eFib ≃* e480 := MonoidHom.ofInjective eHom_injective

theorem card_e480 : Nat.card e480 = 696729600 := by
  rw [← Nat.card_congr eEquiv.toEquiv, card_eFib]

end Fib

end CFSG.ComponentClassification.RankTwoClassical.ExcO8E
