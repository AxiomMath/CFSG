module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathNorm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup

variable {X : Type} [Group X] [Finite X] {t : X} {A K : Subgroup X}

private theorem conj_mul_conj_split (s a b : X) :
    s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by
  group

private theorem conj_conj_eq {s t k : X} (hst : s * t = t * s) :
    s * (t * k * t⁻¹) * s⁻¹ = t * (s * k * s⁻¹) * t⁻¹ := by
  have hsinv : t⁻¹ * s⁻¹ = s⁻¹ * t⁻¹ := by
    simpa [mul_inv_rev] using congrArg (fun x : X => x⁻¹) hst
  calc s * (t * k * t⁻¹) * s⁻¹
      = s * t * k * (t⁻¹ * s⁻¹) := by simp only [mul_assoc]
    _ = t * s * k * (t⁻¹ * s⁻¹) := by rw [hst]
    _ = t * s * k * (s⁻¹ * t⁻¹) := by rw [hsinv]
    _ = t * (s * k * s⁻¹) * t⁻¹ := by simp only [mul_assoc]

private theorem conj_inv_conj_eq {s t k : X} (hst : s * t = t * s) :
    s * (t⁻¹ * k * t) * s⁻¹ = t⁻¹ * (s * k * s⁻¹) * t := by
  have hstinv : s * t⁻¹ = t⁻¹ * s := by
    have h1 : t * (s * t⁻¹) = s := by
      rw [← mul_assoc, hst.symm, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : t * (t⁻¹ * s) = s := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    exact mul_left_cancel (h1.trans h2.symm)
  have htsinv : t * s⁻¹ = s⁻¹ * t := by
    have h1 : s * (t * s⁻¹) = t := by
      rw [← mul_assoc, hst, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : s * (s⁻¹ * t) = t := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    exact mul_left_cancel (h1.trans h2.symm)
  calc s * (t⁻¹ * k * t) * s⁻¹
      = s * t⁻¹ * k * (t * s⁻¹) := by simp only [mul_assoc]
    _ = t⁻¹ * s * k * (t * s⁻¹) := by rw [hstinv]
    _ = t⁻¹ * s * k * (s⁻¹ * t) := by rw [htsinv]
    _ = t⁻¹ * (s * k * s⁻¹) * t := by simp only [mul_assoc]

private theorem conj_diag_eq {s t k : X} (hst : s * t = t * s) :
    s * (k * (t * k * t⁻¹)) * s⁻¹ =
      (s * k * s⁻¹) * (t * (s * k * s⁻¹) * t⁻¹) := by
  rw [conj_mul_conj_split s k (t * k * t⁻¹), conj_conj_eq hst]

theorem WreathK.card_inf_centralizer_eq_diag (hK : WreathK t A K) {s : X}
    (hs : s ∈ normalizer (K : Set X)) (hst : s * t = t * s) :
    Nat.card ↥(K ⊓ centralizer ({s} : Set X)) = Nat.card ↥(A ⊓ centralizer ({s} : Set X)) := by
  let f : ↥(K ⊓ centralizer ({s} : Set X)) → ↥(A ⊓ centralizer ({s} : Set X)) := fun k => by
    have hks : k.1 * s = s * k.1 :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp k.2).2
    refine ⟨k.1 * (t * k.1 * t⁻¹), Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
    · change k.1 * (t * k.1 * t⁻¹) ∈ (A : Set X)
      rw [hK.diag]
      exact ⟨k.1, (Subgroup.mem_inf.mp k.2).1, rfl⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hconj : s * (k.1 * (t * k.1 * t⁻¹)) * s⁻¹ = k.1 * (t * k.1 * t⁻¹) := by
        rw [conj_diag_eq hst]
        have hsk : s * k.1 * s⁻¹ = k.1 := by rw [← hks]; group
        rw [hsk]
      have hcomm : s * (k.1 * (t * k.1 * t⁻¹)) = (k.1 * (t * k.1 * t⁻¹)) * s := by
        have h := congrArg (fun y => y * s) hconj
        simpa [mul_assoc] using h
      exact hcomm.symm
  have hinj : Function.Injective f := by
    intro a b hab
    have hab' : a.1 * (t * a.1 * t⁻¹) = b.1 * (t * b.1 * t⁻¹) := congrArg Subtype.val hab
    have ha' : t * a.1 * t⁻¹ ∈ conjSub t K := by
      refine mem_conjSub_iff.mpr ?_
      have h : t⁻¹ * (t * a.1 * t⁻¹) * t = a.1 := by group
      rw [h]
      exact (Subgroup.mem_inf.mp a.2).1
    have hb' : t * b.1 * t⁻¹ ∈ conjSub t K := by
      refine mem_conjSub_iff.mpr ?_
      have h : t⁻¹ * (t * b.1 * t⁻¹) * t = b.1 := by group
      rw [h]
      exact (Subgroup.mem_inf.mp b.2).1
    exact Subtype.ext (hK.eq_of_mul_eq (Subgroup.mem_inf.mp a.2).1 (Subgroup.mem_inf.mp b.2).1
      ha' hb' hab').1
  have hsurj : Function.Surjective f := by
    intro b
    have hbA : b.1 ∈ A := (Subgroup.mem_inf.mp b.2).1
    change b.1 ∈ (A : Set X) at hbA
    rw [hK.diag] at hbA
    obtain ⟨k, hkK, hk_eq⟩ := hbA
    have hbs : b.1 * s = s * b.1 :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp b.2).2
    have hsk : s * k * s⁻¹ = k := by
      have hbconj : s * b.1 * s⁻¹ = b.1 := by rw [← hbs]; group
      have hEq : (s * k * s⁻¹) * (t * (s * k * s⁻¹) * t⁻¹) = k * (t * k * t⁻¹) := by
        rw [← conj_diag_eq hst, ← hk_eq, hbconj]
      have h1 : s * k * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hs k).mp hkK
      have h2 : t * (s * k * s⁻¹) * t⁻¹ ∈ conjSub t K := by
        refine mem_conjSub_iff.mpr ?_
        have h : t⁻¹ * (t * (s * k * s⁻¹) * t⁻¹) * t = s * k * s⁻¹ := by group
        rw [h]
        exact h1
      have h3 : t * k * t⁻¹ ∈ conjSub t K := by
        refine mem_conjSub_iff.mpr ?_
        have h : t⁻¹ * (t * k * t⁻¹) * t = k := by group
        rw [h]
        exact hkK
      exact (hK.eq_of_mul_eq h1 hkK h2 h3 hEq).1
    have hks : k * s = s * k := by
      have h := congrArg (fun y => y * s) hsk
      have h' : s * k = k * s := by simpa [mul_assoc] using h
      exact h'.symm
    refine ⟨⟨k, Subgroup.mem_inf.mpr ⟨hkK, Subgroup.mem_centralizer_singleton_iff.mpr hks⟩⟩, ?_⟩
    exact Subtype.ext hk_eq.symm
  exact Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩

theorem WreathK.card_conjSub_inf_centralizer (hK : WreathK t A K) {s : X} (hst : s * t = t * s) :
    Nat.card ↥(conjSub t K ⊓ centralizer ({s} : Set X)) =
      Nat.card ↥(K ⊓ centralizer ({s} : Set X)) := by
  refine Nat.card_congr
    { toFun := fun k' => ⟨t⁻¹ * k'.1 * t, mem_conjSub_iff.mp (Subgroup.mem_inf.mp k'.2).1, ?_⟩
      invFun := fun k => ⟨t * k.1 * t⁻¹, ?_, ?_⟩
      left_inv := fun k' => Subtype.ext (by group)
      right_inv := fun k => Subtype.ext (by group) }
  · have hk' : k'.1 * s = s * k'.1 :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp k'.2).2
    have hsk' : s * k'.1 * s⁻¹ = k'.1 := by rw [← hk']; group
    have hconj : s * (t⁻¹ * k'.1 * t) * s⁻¹ = t⁻¹ * k'.1 * t := by
      rw [conj_inv_conj_eq hst, hsk']
    have hcomm : s * (t⁻¹ * k'.1 * t) = (t⁻¹ * k'.1 * t) * s := by
      have h := congrArg (fun y => y * s) hconj
      simpa [mul_assoc] using h
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  · refine mem_conjSub_iff.mpr ?_
    have h : t⁻¹ * (t * k.1 * t⁻¹) * t = k.1 := by group
    rw [h]
    exact (Subgroup.mem_inf.mp k.2).1
  · have hk : k.1 * s = s * k.1 :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp k.2).2
    have hsk : s * k.1 * s⁻¹ = k.1 := by rw [← hk]; group
    have hconj : s * (t * k.1 * t⁻¹) * s⁻¹ = t * k.1 * t⁻¹ := by
      rw [conj_conj_eq hst, hsk]
    have hcomm : s * (t * k.1 * t⁻¹) = (t * k.1 * t⁻¹) * s := by
      have h := congrArg (fun y => y * s) hconj
      simpa [mul_assoc] using h
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm

theorem WreathK.card_layer_inf_centralizer_inner (hK : WreathK t A K) {s : X}
    (hs : s ∈ normalizer (K : Set X)) :
    Nat.card ↥(CFSG.layer X ⊓ centralizer ({s} : Set X)) =
      Nat.card ↥(K ⊓ centralizer ({s} : Set X)) *
        Nat.card ↥(conjSub t K ⊓ centralizer ({s} : Set X)) := by
  let C : Subgroup X := centralizer ({s} : Set X)
  change Nat.card ↥(CFSG.layer X ⊓ C) =
    Nat.card ↥(K ⊓ C) * Nat.card ↥(conjSub t K ⊓ C)
  have hsn : s ∈ normalizer (conjSub t K : Set X) := hK.mem_normalizer_conjSub hs
  let f : ↥(K ⊓ C) × ↥(conjSub t K ⊓ C) → ↥(CFSG.layer X ⊓ C) := fun p => by
    refine ⟨p.1.1 * p.2.1, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
    · exact mul_mem (hK.le_layer (Subgroup.mem_inf.mp p.1.2).1)
        (hK.conjSub_le_layer (Subgroup.mem_inf.mp p.2.2).1)
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h1 : p.1.1 * s = s * p.1.1 :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp p.1.2).2
      have h2 : p.2.1 * s = s * p.2.1 :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp p.2.2).2
      calc (p.1.1 * p.2.1) * s = p.1.1 * (p.2.1 * s) := by rw [mul_assoc]
        _ = p.1.1 * (s * p.2.1) := by rw [h2]
        _ = (p.1.1 * s) * p.2.1 := by rw [mul_assoc]
        _ = (s * p.1.1) * p.2.1 := by rw [h1]
        _ = s * (p.1.1 * p.2.1) := by rw [mul_assoc]
  have hinj : Function.Injective f := by
    intro p q hpq
    have hval : p.1.1 * p.2.1 = q.1.1 * q.2.1 := congrArg Subtype.val hpq
    have h := hK.eq_of_mul_eq (Subgroup.mem_inf.mp p.1.2).1 (Subgroup.mem_inf.mp q.1.2).1
      (Subgroup.mem_inf.mp p.2.2).1 (Subgroup.mem_inf.mp q.2.2).1 hval
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  have hsurj : Function.Surjective f := by
    intro g
    have hg : g.1 ∈ CFSG.layer X := (Subgroup.mem_inf.mp g.2).1
    have hgs : g.1 * s = s * g.1 :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).2
    rw [hK.mem_layer_iff] at hg
    obtain ⟨k, hkK, k', hk'K, hk_eq⟩ := hg
    have hgconj : s * g.1 * s⁻¹ = g.1 := by rw [← hgs]; group
    have hEq : (s * k * s⁻¹) * (s * k' * s⁻¹) = k * k' := by
      rw [← conj_mul_conj_split s k k', ← hk_eq, hgconj]
    have h1 : s * k * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hs k).mp hkK
    have h2 : s * k' * s⁻¹ ∈ conjSub t K := (Subgroup.mem_normalizer_iff.mp hsn k').mp hk'K
    have h := hK.eq_of_mul_eq h1 hkK h2 hk'K hEq
    have hks : k * s = s * k := by
      have hconj := congrArg (fun y => y * s) h.1
      have h' : s * k = k * s := by simpa [mul_assoc] using hconj
      exact h'.symm
    have hk's : k' * s = s * k' := by
      have hconj := congrArg (fun y => y * s) h.2
      have h' : s * k' = k' * s := by simpa [mul_assoc] using hconj
      exact h'.symm
    refine ⟨(⟨k, Subgroup.mem_inf.mpr ⟨hkK, Subgroup.mem_centralizer_singleton_iff.mpr hks⟩⟩,
      ⟨k', Subgroup.mem_inf.mpr ⟨hk'K, Subgroup.mem_centralizer_singleton_iff.mpr hk's⟩⟩), ?_⟩
    exact Subtype.ext hk_eq.symm
  rw [← Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩, Nat.card_prod]

theorem WreathK.card_layer_inf_centralizer_commuting (hK : WreathK t A K) {s : X}
    (hs : s ∈ normalizer (K : Set X)) (hst : s * t = t * s) :
    Nat.card ↥(CFSG.layer X ⊓ centralizer ({s} : Set X)) =
      Nat.card ↥(A ⊓ centralizer ({s} : Set X)) * Nat.card ↥(A ⊓ centralizer ({s} : Set X)) := by
  rw [hK.card_layer_inf_centralizer_inner hs, hK.card_conjSub_inf_centralizer hst,
    hK.card_inf_centralizer_eq_diag hs hst]

end CFSG.OddStandard.AltStdSec.SwapPattern
