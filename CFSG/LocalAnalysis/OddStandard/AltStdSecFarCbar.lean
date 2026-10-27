module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarSecTri
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRoot

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm

section Four

abbrev kA4 : Perm (Fin 4) := swap 0 1 * swap 2 3

abbrev dEight : Subgroup (Perm (Fin 4)) := centralizer ({kA4} : Set (Perm (Fin 4)))

theorem mem_dEight_iff {x : Perm (Fin 4)} : x ∈ dEight ↔ x * kA4 = kA4 * x :=
  mem_centralizer_singleton_iff

theorem dEight_cases (x : Perm (Fin 4)) (hx : x * kA4 = kA4 * x) :
    x = 1 ∨ x = swap 0 1 ∨ x = swap 0 1 * kA4 ∨ x = kA4 ∨ x = swap 0 2 * swap 1 3 ∨
      x = swap 0 2 * swap 1 3 * kA4 ∨ x = swap 0 3 * swap 0 1 * swap 0 2 ∨
        x = swap 0 3 * swap 0 1 * swap 0 2 * kA4 := by
  revert x
  decide

theorem dEight_sq (x : Perm (Fin 4)) (hx : x * kA4 = kA4 * x) : x * x = 1 ∨ x * x = kA4 := by
  revert x
  decide

end Four

section Emb

variable {N : ℕ}

theorem emb4_swap (hN : 4 ≤ N) (a b : Fin 4) :
    emb4 hN (swap a b) = swap ⟨a, by omega⟩ ⟨b, by omega⟩ := by
  apply Equiv.ext
  intro x
  change (swap a b).extendDomain (fin4Equiv hN) x = _
  by_cases hx : (x : ℕ) < 4
  · rw [Perm.extendDomain_apply_subtype (swap a b) (fin4Equiv hN) (b := x) hx]
    set y := (fin4Equiv hN).symm ⟨x, hx⟩ with hy
    have hxy : x = ((fin4Equiv hN y : {i : Fin N // (i : ℕ) < 4}) : Fin N) := by
      rw [hy, Equiv.apply_symm_apply]
    have hinj : Function.Injective (fun i : Fin 4 =>
        ((fin4Equiv hN i : {i : Fin N // (i : ℕ) < 4}) : Fin N)) := by
      intro i j h
      simp only [fin4Equiv, Equiv.coe_fn_mk, Fin.mk.injEq] at h
      exact Fin.ext h
    have h1 := hinj.swap_apply a b y
    rw [hxy]
    exact h1.symm
  · rw [Perm.extendDomain_apply_not_subtype (swap a b) (fin4Equiv hN) (b := x) hx]
    have ha : x ≠ ⟨a, by omega⟩ := fun h => hx (by rw [h]; exact a.2)
    have hb : x ≠ ⟨b, by omega⟩ := fun h => hx (by rw [h]; exact b.2)
    rw [swap_apply_of_ne_of_ne ha hb]

theorem emb4_injective (hN : 4 ≤ N) : Function.Injective (emb4 hN) :=
  Perm.extendDomainHom_injective _

theorem emb4_apply_of_four_le (hN : 4 ≤ N) (x : Perm (Fin 4)) {i : Fin N} (hi : 4 ≤ (i : ℕ)) :
    emb4 hN x i = i :=
  emb4_mem_fixSub hN x i (by simp [mem_fourSet]; omega)

theorem exists_emb4_eq (hN : 4 ≤ N) {σ : Perm (Fin N)} (hσ : σ ∈ fixSub (fourSet N)ᶜ) :
    ∃ x : Perm (Fin 4), emb4 hN x = σ := by
  have hfix : ∀ i : Fin N, ¬ (i : ℕ) < 4 → σ i = i := fun i hi =>
    hσ i (by simp [mem_fourSet]; omega)
  have hp : ∀ i : Fin N, (σ i : ℕ) < 4 ↔ (i : ℕ) < 4 := by
    intro i
    constructor
    · intro h
      by_contra hi
      rw [hfix i hi] at h
      exact hi h
    · intro hi
      by_contra h
      have := hfix (σ i) h
      rw [σ.injective this] at h
      exact h hi
  set τ : Perm {i : Fin N // (i : ℕ) < 4} := σ.subtypePerm hp with hτ
  refine ⟨(fin4Equiv hN).permCongr.symm τ, ?_⟩
  apply Equiv.ext
  intro x
  change (((fin4Equiv hN).permCongr.symm τ).extendDomain (fin4Equiv hN)) x = σ x
  by_cases hx : (x : ℕ) < 4
  · rw [Perm.extendDomain_apply_subtype _ (fin4Equiv hN) (b := x) hx]
    simp [Equiv.permCongr_apply, hτ]
  · rw [Perm.extendDomain_apply_not_subtype _ (fin4Equiv hN) (b := x) hx, hfix x hx]

end Emb

section Near

variable {G : Type*} [Group G] {z : G} {m : ℕ} (O : OverData G z m)

theorem not_isConj_φ {r : Perm (Fin (m + 3))}
    (h1 : r ⟨m + 1, by omega⟩ = ⟨m + 1, by omega⟩) (h2 : r ⟨m + 2, by omega⟩ = ⟨m + 2, by omega⟩)
    (hsupp : r.support.card + 7 ≤ m + 1) (hns : ¬ r.IsSwap) (hr1 : r ≠ 1) :
    ¬ IsConj z (O.φ r) := by
  classical
  intro hconj
  obtain ⟨r', hr'⟩ := exists_inclPerm_eq h1 h2
  have hφr : O.φ r = O.D.ι r' := by rw [← hr', OverData.φ_apply, O.hcompat]
  have hmemC : O.φ r ∈ centralizer ({z} : Set G) := by
    rw [hφr]; exact O.D.ι_mem r'
  have hr'1 : r' ≠ 1 := fun h => hr1 (by rw [← hr', h, map_one])
  have hne : O.φ r ≠ z := by
    intro h
    have hπ := O.D.π_ι r'
    have : O.D.π ⟨O.D.ι r', O.D.le (O.D.ι r').2⟩ = O.D.π ⟨z, NearData.self_mem_centralizer z⟩ :=
      congrArg O.D.π (Subtype.ext (hφr.symm.trans h))
    rw [hπ, O.D.π_z] at this
    exact hr'1 this
  have hP : O.φ r ∈ Partners z := ⟨hconj, hne, mem_centralizer_singleton_iff.1 hmemC⟩
  have hπ : O.D.π ⟨O.φ r, hmemC⟩ = r' := by
    have : (⟨O.φ r, hmemC⟩ : centralizer ({z} : Set G)) = ⟨O.D.ι r', O.D.ι_mem r'⟩ :=
      Subtype.ext hφr
    rw [this, O.D.π_ι]
  have hsupp' : r'.support.card + 7 ≤ m + 1 := by
    have := Perm.card_support_extend_domain (finIncl m) (g := r')
    rw [show r'.extendDomain (finIncl m) = r from hr'] at this
    omega
  have hns' : ¬ r'.IsSwap := fun h => hns (by rw [← hr']; exact inclPerm_isSwap h)
  have hnear : IsNearPerm (O.D.π ⟨O.φ r, hmemC⟩) := by
    rw [hπ]
    have := NearData.fixFin_card_add_support_card r'
    constructor <;> omega
  have := (O.D.near _ hP hnear).1
  rw [hπ] at this
  exact hns' this

end Near

section TwoSecLift

variable {G : Type} [Group G]

theorem exists_conj_of_isConj_mk {x : G} (hx : x * x = 1) {a b : ↥(centralizer ({x} : Set G))}
    (h : IsConj (QuotientGroup.mk a : TwoSec x) (QuotientGroup.mk b)) :
    ∃ c : ↥(centralizer ({x} : Set G)),
      (c : G) * a * (c : G)⁻¹ = b ∨ (c : G) * a * (c : G)⁻¹ = b * x := by
  obtain ⟨cb, hc⟩ := isConj_iff.1 h
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cb
  have h1 : (QuotientGroup.mk (c * a * c⁻¹) : TwoSec x) = QuotientGroup.mk b := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hc
  have h2 := (mem_zpowers_selfC_iff hx).1 (QuotientGroup.eq.1 h1)
  refine ⟨c, ?_⟩
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  rcases h2 with h2 | h2
  · left
    have h3 : ((c : G) * a * (c : G)⁻¹)⁻¹ * b = 1 := by simpa using h2
    exact (inv_mul_eq_one.1 h3)
  · right
    have h3 : ((c : G) * a * (c : G)⁻¹)⁻¹ * b = x := by simpa using h2
    calc (c : G) * a * (c : G)⁻¹ = b * (((c : G) * a * (c : G)⁻¹)⁻¹ * b)⁻¹ := by group
      _ = b * x := by rw [h3, hxi]

theorem eq_or_of_mk_eq {x : G} (hx : x * x = 1) {g b : ↥(centralizer ({x} : Set G))}
    (h : (QuotientGroup.mk g : TwoSec x) = QuotientGroup.mk b) : (g : G) = b ∨ (g : G) = b * x := by
  have h2 := (mem_zpowers_selfC_iff hx).1 (QuotientGroup.eq.1 h)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  rcases h2 with h2 | h2
  · left
    have h3 : (g : G)⁻¹ * b = 1 := by simpa using h2
    exact inv_mul_eq_one.1 h3
  · right
    have h3 : (g : G)⁻¹ * b = x := by simpa using h2
    calc (g : G) = b * ((g : G)⁻¹ * b)⁻¹ := by group
      _ = b * x := by rw [h3, hxi]

theorem conj_eq_or_of_comm_mk {x : G} (hx : x * x = 1) {a c : ↥(centralizer ({x} : Set G))}
    (h : (QuotientGroup.mk c : TwoSec x) * QuotientGroup.mk a =
      QuotientGroup.mk a * QuotientGroup.mk c) :
    (c : G) * a * (c : G)⁻¹ = a ∨ (c : G) * a * (c : G)⁻¹ = a * x := by
  have h1 : (QuotientGroup.mk (c * a * c⁻¹) : TwoSec x) = QuotientGroup.mk a := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h]
    group
  exact eq_or_of_mk_eq hx h1

end TwoSecLift

section Cbar

variable {G : Type} [Group G] {z : G} {m : ℕ} (O : OverData G z m) (h4 : 4 ≤ m + 3)

@[expose] noncomputable def Φ4 : Perm (Fin 4) →* G := O.φ.comp (emb4 h4)

theorem Φ4_apply (x : Perm (Fin 4)) : Φ4 O h4 x = O.φ (emb4 h4 x) := rfl

theorem Φ4_injective : Function.Injective (Φ4 O h4) := O.φ_injective.comp (emb4_injective _)

noncomputable abbrev wA : G := Φ4 O h4 kA4

theorem wA_mul_self : wA O h4 * wA O h4 = 1 := by
  rw [← map_mul, show kA4 * kA4 = 1 by decide, map_one]

theorem wA_ne_one : wA O h4 ≠ 1 := by
  intro h
  rw [← map_one (Φ4 O h4)] at h
  exact absurd (Φ4_injective O h4 h) (by decide)

abbrev Cbar : Type := TwoSec (wA O h4)

theorem Φ4_mem_centralizer {x : Perm (Fin 4)} (hx : x ∈ dEight) :
    Φ4 O h4 x ∈ centralizer ({wA O h4} : Set G) := by
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_dEight_iff.1 hx]

@[expose] noncomputable def psi4 : dEight →* Cbar O h4 :=
  (QuotientGroup.mk' _).comp
    (((Φ4 O h4).comp dEight.subtype).codRestrict _ (fun x => Φ4_mem_centralizer O h4 x.2))

theorem psi4_apply (x : dEight) :
    psi4 O h4 x = QuotientGroup.mk ⟨Φ4 O h4 x, Φ4_mem_centralizer O h4 x.2⟩ := rfl

theorem psi4_congr {d : dEight} {x : Perm (Fin 4)} (hx : x ∈ dEight)
    (h : (d : Perm (Fin 4)) = x) : psi4 O h4 d = psi4 O h4 ⟨x, hx⟩ :=
  congrArg _ (Subtype.ext h)

theorem psi4_kA4 : psi4 O h4 ⟨kA4, mem_dEight_iff.2 rfl⟩ = 1 := by
  rw [psi4_apply]
  apply (QuotientGroup.eq_one_iff _).2
  exact (mem_zpowers_selfC_iff (wA_mul_self O h4)).2 (Or.inr rfl)

theorem psi4_mul_kA4 {x : Perm (Fin 4)} (hx : x ∈ dEight) (hx' : x * kA4 ∈ dEight) :
    psi4 O h4 ⟨x * kA4, hx'⟩ = psi4 O h4 ⟨x, hx⟩ := by
  have : (⟨x * kA4, hx'⟩ : dEight) = ⟨x, hx⟩ * ⟨kA4, mem_dEight_iff.2 rfl⟩ := rfl
  rw [this, map_mul, psi4_kA4, mul_one]

noncomputable abbrev ebar : Cbar O h4 := psi4 O h4 ⟨swap 0 1, mem_dEight_iff.2 (by decide)⟩

noncomputable abbrev fbar : Cbar O h4 := psi4 O h4 ⟨swap 0 2 * swap 1 3, mem_dEight_iff.2 (by decide)⟩

noncomputable abbrev ybar : Cbar O h4 :=
  psi4 O h4 ⟨swap 0 3 * swap 0 1 * swap 0 2, mem_dEight_iff.2 (by decide)⟩

@[expose] noncomputable def kbar : Subgroup (Cbar O h4) := (psi4 O h4).range

theorem mem_kbar_iff {x : Cbar O h4} :
    x ∈ kbar O h4 ↔ x = 1 ∨ x = ebar O h4 ∨ x = fbar O h4 ∨ x = ybar O h4 := by
  constructor
  · rintro ⟨d, rfl⟩
    rcases dEight_cases d (mem_dEight_iff.1 d.2) with h | h | h | h | h | h | h | h
    · left; rw [show d = 1 from Subtype.ext h, map_one]
    · right; left; exact psi4_congr O h4 _ h
    · right; left
      rw [psi4_congr O h4 (mem_dEight_iff.2 (by decide)) h, psi4_mul_kA4]
    · left; rw [psi4_congr O h4 (mem_dEight_iff.2 (by decide)) h, psi4_kA4]
    · right; right; left; exact psi4_congr O h4 _ h
    · right; right; left
      rw [psi4_congr O h4 (mem_dEight_iff.2 (by decide)) h, psi4_mul_kA4]
    · right; right; right; exact psi4_congr O h4 _ h
    · right; right; right
      rw [psi4_congr O h4 (mem_dEight_iff.2 (by decide)) h, psi4_mul_kA4]
  · rintro (h | h | h | h) <;> rw [h]
    · exact one_mem _
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

noncomputable abbrev e1G : G := Φ4 O h4 (swap 0 1)

noncomputable abbrev fG : G := Φ4 O h4 (swap 0 2 * swap 1 3)

noncomputable abbrev yG : G := Φ4 O h4 (swap 0 3 * swap 0 1 * swap 0 2)

theorem emb4_swap01 : emb4 h4 (swap 0 1) = swap ⟨0, by omega⟩ ⟨1, by omega⟩ := emb4_swap h4 0 1

theorem isConj_z_e1G : IsConj z (e1G O h4) := by
  have := O.hconj (emb4 h4 (swap 0 1)) ⟨_, _, by simp, emb4_swap01 h4⟩
  exact this

theorem not_isConj_Φ4 (hm : 10 ≤ m) {x : Perm (Fin 4)} (hx : x.support.card = 4) :
    ¬ IsConj z (Φ4 O h4 x) := by
  have hx1 : x ≠ 1 := fun h => by rw [h] at hx; simp at hx
  refine not_isConj_φ O (emb4_apply_of_four_le h4 x (by simp; omega))
    (emb4_apply_of_four_le h4 x (by simp; omega)) ?_ ?_ ?_
  · have := Perm.card_support_extend_domain (fin4Equiv h4) (g := x)
    change (emb4 h4 x).support.card = x.support.card at this
    omega
  · intro hsw
    have h2 := Perm.card_support_eq_two.2 hsw
    have := Perm.card_support_extend_domain (fin4Equiv h4) (g := x)
    change (emb4 h4 x).support.card = x.support.card at this
    omega
  · intro h
    exact hx1 (emb4_injective h4 (by rw [h, map_one]))

theorem e1G_mem : e1G O h4 ∈ centralizer ({wA O h4} : Set G) :=
  Φ4_mem_centralizer O h4 (mem_dEight_iff.2 (by decide))

theorem fG_mem : fG O h4 ∈ centralizer ({wA O h4} : Set G) :=
  Φ4_mem_centralizer O h4 (mem_dEight_iff.2 (by decide))

theorem yG_mem : yG O h4 ∈ centralizer ({wA O h4} : Set G) :=
  Φ4_mem_centralizer O h4 (mem_dEight_iff.2 (by decide))

theorem ebar_eq : ebar O h4 = QuotientGroup.mk ⟨e1G O h4, e1G_mem O h4⟩ := rfl
theorem fbar_eq : fbar O h4 = QuotientGroup.mk ⟨fG O h4, fG_mem O h4⟩ := rfl
theorem ybar_eq : ybar O h4 = QuotientGroup.mk ⟨yG O h4, yG_mem O h4⟩ := rfl

theorem psi4_ne_one {x : Perm (Fin 4)} (hx : x ∈ dEight) (h1 : x ≠ 1) (h2 : x ≠ kA4) :
    psi4 O h4 ⟨x, hx⟩ ≠ 1 := by
  intro h
  rw [psi4_apply] at h
  rcases (mem_zpowers_selfC_iff (wA_mul_self O h4)).1 ((QuotientGroup.eq_one_iff _).1 h) with h' | h'
  · exact h1 (Φ4_injective O h4 (h'.trans (map_one _).symm))
  · exact h2 (Φ4_injective O h4 h')

theorem eq_of_isConj_of_mem_kbar (hm : 10 ≤ m) {t k : Cbar O h4} (ht : t ∈ kbar O h4)
    (hk : k ∈ kbar O h4) (h : IsConj t k) : t = k := by
  have hw2 := wA_mul_self O h4
  have hef : ¬ IsConj (ebar O h4) (fbar O h4) := by
    intro hc
    rw [ebar_eq, fbar_eq] at hc
    obtain ⟨c, hc'⟩ := exists_conj_of_isConj_mk hw2 hc
    have hz := isConj_z_e1G O h4
    have hs1 : (swap (0 : Fin 4) 2 * swap 1 3).support.card = 4 := by decide
    have hs2 : (swap (0 : Fin 4) 2 * swap 1 3 * kA4).support.card = 4 := by decide
    rcases hc' with hc' | hc'
    · have h1 : IsConj (e1G O h4) (fG O h4) := isConj_iff.2 ⟨c, hc'⟩
      exact not_isConj_Φ4 O h4 hm hs1 (hz.trans h1)
    · have e : fG O h4 * wA O h4 = Φ4 O h4 (swap 0 2 * swap 1 3 * kA4) := (map_mul _ _ _).symm
      have h1 : IsConj (e1G O h4) (Φ4 O h4 (swap 0 2 * swap 1 3 * kA4)) :=
        isConj_iff.2 ⟨c, hc'.trans e⟩
      exact not_isConj_Φ4 O h4 hm hs2 (hz.trans h1)
  have hy : ∀ a : ↥(centralizer ({wA O h4} : Set G)), (a : G) * a = 1 →
      ¬ IsConj (QuotientGroup.mk a : Cbar O h4) (ybar O h4) := by
    intro a ha hc
    rw [ybar_eq] at hc
    obtain ⟨c, hc'⟩ := exists_conj_of_isConj_mk hw2 hc
    have hsq : ((c : G) * a * (c : G)⁻¹) * ((c : G) * a * (c : G)⁻¹) = 1 := by
      calc ((c : G) * a * (c : G)⁻¹) * ((c : G) * a * (c : G)⁻¹) = (c : G) * (a * a) * (c : G)⁻¹ := by
            group
        _ = 1 := by rw [ha]; group
    have hwne := wA_ne_one O h4
    rcases hc' with hc' | hc'
    · rw [hc'] at hsq
      apply hwne
      rw [← hsq]
      change Φ4 O h4 kA4 = Φ4 O h4 _ * Φ4 O h4 _
      rw [← map_mul, show swap (0 : Fin 4) 3 * swap 0 1 * swap 0 2 *
        (swap 0 3 * swap 0 1 * swap 0 2) = kA4 by decide]
    · rw [hc'] at hsq
      apply hwne
      rw [← hsq]
      change Φ4 O h4 kA4 = Φ4 O h4 _ * Φ4 O h4 kA4 * (Φ4 O h4 _ * Φ4 O h4 kA4)
      rw [← map_mul, ← map_mul, show swap (0 : Fin 4) 3 * swap 0 1 * swap 0 2 * kA4 *
        (swap 0 3 * swap 0 1 * swap 0 2 * kA4) = kA4 by decide]
  have hey : ¬ IsConj (ebar O h4) (ybar O h4) := by
    rw [ebar_eq]
    exact hy ⟨e1G O h4, e1G_mem O h4⟩ (by
      change Φ4 O h4 _ * Φ4 O h4 _ = 1
      rw [← map_mul, show swap (0 : Fin 4) 1 * swap 0 1 = 1 by decide, map_one])
  have hfy : ¬ IsConj (fbar O h4) (ybar O h4) := by
    rw [fbar_eq]
    exact hy ⟨fG O h4, fG_mem O h4⟩ (by
      change Φ4 O h4 _ * Φ4 O h4 _ = 1
      rw [← map_mul, show swap (0 : Fin 4) 2 * swap 1 3 * (swap 0 2 * swap 1 3) = 1 by decide,
        map_one])
  have he1 : ebar O h4 ≠ 1 := psi4_ne_one O h4 _ (by decide) (by decide)
  have hf1 : fbar O h4 ≠ 1 := psi4_ne_one O h4 _ (by decide) (by decide)
  have hy1 : ybar O h4 ≠ 1 := psi4_ne_one O h4 _ (by decide) (by decide)
  rcases (mem_kbar_iff O h4).1 ht with rfl | rfl | rfl | rfl <;>
    rcases (mem_kbar_iff O h4).1 hk with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (isConj_one_right.1 h) he1
  · exact absurd (isConj_one_right.1 h) hf1
  · exact absurd (isConj_one_right.1 h) hy1
  · exact absurd (isConj_one_left.1 h) he1
  · rfl
  · exact absurd h hef
  · exact absurd h hey
  · exact absurd (isConj_one_left.1 h) hf1
  · exact absurd h.symm hef
  · rfl
  · exact absurd h hfy
  · exact absurd (isConj_one_left.1 h) hy1
  · exact absurd h.symm hey
  · exact absurd h.symm hfy
  · rfl

end Cbar

section Norm

variable {G : Type} [Group G] {z : G} {m : ℕ} (O : OverData G z m) (h4 : 4 ≤ m + 3)

theorem Φ4_eq_of {a b : Perm (Fin 4)} (h : a = b) : Φ4 O h4 a = Φ4 O h4 b := congrArg _ h

theorem emb4_kA4_apply_ne {i : Fin (m + 3)} (hi : (i : ℕ) < 4) : emb4 h4 kA4 i ≠ i := by
  have h := emb4_apply_image h4 kA4 ⟨i, hi⟩
  have hi' : (⟨((⟨(i : ℕ), hi⟩ : Fin 4) : ℕ), by omega⟩ : Fin (m + 3)) = i := Fin.ext rfl
  rw [hi'] at h
  rw [h]
  intro h'
  have hfp : ∀ j : Fin 4, kA4 j ≠ j := by decide
  exact hfp ⟨i, hi⟩ (Fin.ext (show ((kA4 ⟨i, hi⟩ : Fin 4) : ℕ) = i from congrArg Fin.val h'))

theorem mem_fourSet_iff_of_comm {x : Perm (Fin (m + 3))}
    (hx : x * emb4 h4 kA4 = emb4 h4 kA4 * x) (i : Fin (m + 3)) :
    i ∈ fourSet (m + 3) ↔ x i ∈ fourSet (m + 3) := by
  have key : ∀ y : Perm (Fin (m + 3)), y * emb4 h4 kA4 = emb4 h4 kA4 * y →
      ∀ i, i ∈ fourSet (m + 3) → y i ∈ fourSet (m + 3) := by
    intro y hy i hi
    rw [mem_fourSet] at hi ⊢
    by_contra h
    have h1 : emb4 h4 kA4 (y i) = y i := emb4_apply_of_four_le h4 kA4 (by omega)
    have h2 : y (emb4 h4 kA4 i) = emb4 h4 kA4 (y i) := by
      have := DFunLike.congr_fun hy i
      simpa only [Perm.mul_apply] using this
    rw [h1] at h2
    exact emb4_kA4_apply_ne h4 hi (y.injective h2)
  refine ⟨key x hx i, fun h => ?_⟩
  have hx' : x⁻¹ * emb4 h4 kA4 = emb4 h4 kA4 * x⁻¹ := by
    calc x⁻¹ * emb4 h4 kA4 = x⁻¹ * (emb4 h4 kA4 * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * emb4 h4 kA4) * x⁻¹ := by rw [hx]
      _ = emb4 h4 kA4 * x⁻¹ := by group
  have := key x⁻¹ hx' (x i) h
  simpa using this

theorem conj_mem_altSub_compl_of_comm {x l : Perm (Fin (m + 3))}
    (hx : x * emb4 h4 kA4 = emb4 h4 kA4 * x) (hl : l ∈ altSub (fourSet (m + 3))ᶜ) :
    x * l * x⁻¹ ∈ altSub (fourSet (m + 3))ᶜ := by
  have hN : x ∈ normalizer ((altSub (fourSet (m + 3))ᶜ : Subgroup (Perm (Fin (m + 3)))) :
      Set (Perm (Fin (m + 3)))) :=
    mem_normalizer_altSub (fun i => by
      simp only [Finset.mem_compl]
      exact not_congr (mem_fourSet_iff_of_comm h4 hx i))
  exact (mem_normalizer_iff.1 hN l).1 hl

theorem φ_altSub_mem {l : Perm (Fin (m + 3))} (hl : l ∈ altSub (fourSet (m + 3))ᶜ) :
    O.φ l ∈ centralizer ({wA O h4} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  change O.φ l * O.φ (emb4 h4 kA4) = O.φ (emb4 h4 kA4) * O.φ l
  rw [O.φ_comm_iff]
  exact (comm_fixSub_compl (emb4_mem_fixSub h4 kA4) (altSub_compl_le hl)).symm

@[expose] noncomputable def psiL : altSub (fourSet (m + 3))ᶜ →* Cbar O h4 :=
  (QuotientGroup.mk' _).comp ((O.φ.comp (altSub (fourSet (m + 3))ᶜ).subtype).codRestrict _
    (fun l => φ_altSub_mem O h4 l.2))

theorem psiL_apply (l : altSub (fourSet (m + 3))ᶜ) :
    psiL O h4 l = QuotientGroup.mk ⟨O.φ l, φ_altSub_mem O h4 l.2⟩ := rfl

@[expose] noncomputable def L0bar : Subgroup (Cbar O h4) := (psiL O h4).range

theorem mk_mem_normalizer_L0bar {c : ↥(centralizer ({wA O h4} : Set G))}
    (hc : ∀ l ∈ altSub (fourSet (m + 3))ᶜ, ∃ l' ∈ altSub (fourSet (m + 3))ᶜ,
      (c : G) * O.φ l * (c : G)⁻¹ = O.φ l')
    (hc' : ∀ l ∈ altSub (fourSet (m + 3))ᶜ, ∃ l' ∈ altSub (fourSet (m + 3))ᶜ,
      (c : G)⁻¹ * O.φ l * (c : G) = O.φ l') :
    (QuotientGroup.mk c : Cbar O h4) ∈ normalizer (L0bar O h4 : Set (Cbar O h4)) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨⟨l, hl⟩, rfl⟩
    obtain ⟨l', hl', he⟩ := hc l hl
    refine ⟨⟨l', hl'⟩, ?_⟩
    rw [psiL_apply, psiL_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext he.symm)
  · rintro ⟨⟨l, hl⟩, hle⟩
    obtain ⟨l', hl', he⟩ := hc' l hl
    refine ⟨⟨l', hl'⟩, ?_⟩
    have hx : x = (QuotientGroup.mk c : Cbar O h4)⁻¹ * psiL O h4 ⟨l, hl⟩ *
        (QuotientGroup.mk c : Cbar O h4) := by
      rw [hle]; group
    rw [hx, psiL_apply, psiL_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext he.symm)

theorem exists_φ_of_comm_ebar {c : ↥(centralizer ({wA O h4} : Set G))}
    (hc : (QuotientGroup.mk c : Cbar O h4) * ebar O h4 = ebar O h4 * QuotientGroup.mk c) :
    ∃ x : Perm (Fin (m + 3)), O.φ x = c ∧ x * emb4 h4 kA4 = emb4 h4 kA4 * x := by
  rw [ebar_eq] at hc
  have h := conj_eq_or_of_comm_mk (wA_mul_self O h4) hc
  obtain ⟨γ, hγ⟩ := isConj_iff.1 (isConj_swap (α := Fin (m + 3)) (w := ⟨m + 1, by omega⟩)
    (x := ⟨m + 2, by omega⟩) (y := ⟨0, by omega⟩) (z := ⟨1, by omega⟩) (by simp) (by simp))
  have hγ' : γ * OverData.tau m * γ⁻¹ = emb4 h4 (swap 0 1) := by
    rw [emb4_swap01]; exact hγ
  have hCe : centralizer ({e1G O h4} : Set G) ≤ O.M := by
    have := O.centralizer_φ_conj_le γ
    rwa [hγ'] at this
  have hcM : (c : G) ∈ O.M := by
    rcases h with h | h
    · apply hCe
      rw [mem_centralizer_singleton_iff]
      calc (c : G) * e1G O h4 = ((c : G) * e1G O h4 * (c : G)⁻¹) * c := by group
        _ = e1G O h4 * c := by rw [h]
    · have hf : fG O h4 * (e1G O h4 * wA O h4) * (fG O h4)⁻¹ = e1G O h4 := by
        change Φ4 O h4 _ * (Φ4 O h4 _ * Φ4 O h4 _) * (Φ4 O h4 _)⁻¹ = Φ4 O h4 _
        simp only [← map_mul, ← map_inv]
        exact Φ4_eq_of O h4 (by decide)
      have h1 : fG O h4 * (c : G) ∈ centralizer ({e1G O h4} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        calc fG O h4 * (c : G) * e1G O h4 =
            fG O h4 * ((c : G) * e1G O h4 * (c : G)⁻¹) * c := by group
          _ = fG O h4 * (e1G O h4 * wA O h4) * c := by rw [h]
          _ = fG O h4 * (e1G O h4 * wA O h4) * (fG O h4)⁻¹ * (fG O h4 * c) := by group
          _ = e1G O h4 * (fG O h4 * c) := by rw [hf]
      have h2 := hCe h1
      have h3 := mul_mem (inv_mem (O.φ_mem (emb4 h4 (swap 0 2 * swap 1 3)))) h2
      have e : (O.φ (emb4 h4 (swap 0 2 * swap 1 3)))⁻¹ * (fG O h4 * (c : G)) = c := by
        change (fG O h4)⁻¹ * (fG O h4 * (c : G)) = c
        group
      rwa [e] at h3
  obtain ⟨x, hx⟩ := O.exists_eq_φ hcM
  refine ⟨x, hx, ?_⟩
  have hcw : (c : G) * wA O h4 = wA O h4 * c := mem_centralizer_singleton_iff.1 c.2
  rw [← hx] at hcw
  exact O.φ_comm_iff.1 hcw

theorem comm_ebar_mem_normalizer {c : ↥(centralizer ({wA O h4} : Set G))}
    (hc : (QuotientGroup.mk c : Cbar O h4) * ebar O h4 = ebar O h4 * QuotientGroup.mk c) :
    (QuotientGroup.mk c : Cbar O h4) ∈ normalizer (L0bar O h4 : Set (Cbar O h4)) := by
  obtain ⟨x, hx, hxk⟩ := exists_φ_of_comm_ebar O h4 hc
  have hxk' : x⁻¹ * emb4 h4 kA4 = emb4 h4 kA4 * x⁻¹ := by
    calc x⁻¹ * emb4 h4 kA4 = x⁻¹ * (emb4 h4 kA4 * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * emb4 h4 kA4) * x⁻¹ := by rw [hxk]
      _ = emb4 h4 kA4 * x⁻¹ := by group
  refine mk_mem_normalizer_L0bar O h4 (fun l hl => ?_) (fun l hl => ?_)
  · refine ⟨x * l * x⁻¹, conj_mem_altSub_compl_of_comm h4 hxk hl, ?_⟩
    rw [← hx, map_mul, map_mul, map_inv]
  · refine ⟨x⁻¹ * l * x⁻¹⁻¹, conj_mem_altSub_compl_of_comm h4 hxk' hl, ?_⟩
    rw [← hx]
    simp only [map_mul, map_inv, inv_inv]

theorem emb4_comm_kA4 {x : Perm (Fin 4)} (hx : x * kA4 = kA4 * x) :
    emb4 h4 x * emb4 h4 kA4 = emb4 h4 kA4 * emb4 h4 x := by
  rw [← map_mul, ← map_mul, hx]

theorem conj_L0_of_mul {c c' : G} {s : Perm (Fin (m + 3))}
    (hs : s * emb4 h4 kA4 = emb4 h4 kA4 * s) (hcc : c' = O.φ s * c)
    (h : ∀ l ∈ altSub (fourSet (m + 3))ᶜ, ∃ l' ∈ altSub (fourSet (m + 3))ᶜ,
      c' * O.φ l * c'⁻¹ = O.φ l') :
    ∀ l ∈ altSub (fourSet (m + 3))ᶜ, ∃ l' ∈ altSub (fourSet (m + 3))ᶜ,
      c * O.φ l * c⁻¹ = O.φ l' := by
  have hs' : s⁻¹ * emb4 h4 kA4 = emb4 h4 kA4 * s⁻¹ := by
    calc s⁻¹ * emb4 h4 kA4 = s⁻¹ * (emb4 h4 kA4 * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * emb4 h4 kA4) * s⁻¹ := by rw [hs]
      _ = emb4 h4 kA4 * s⁻¹ := by group
  intro l hl
  obtain ⟨l', hl', he⟩ := h l hl
  refine ⟨s⁻¹ * l' * s⁻¹⁻¹, conj_mem_altSub_compl_of_comm h4 hs' hl', ?_⟩
  have hc : c = (O.φ s)⁻¹ * c' := by rw [hcc]; group
  rw [hc]
  calc (O.φ s)⁻¹ * c' * O.φ l * ((O.φ s)⁻¹ * c')⁻¹ =
      (O.φ s)⁻¹ * (c' * O.φ l * c'⁻¹) * O.φ s := by group
    _ = (O.φ s)⁻¹ * O.φ l' * O.φ s := by rw [he]
    _ = O.φ (s⁻¹ * l' * s⁻¹⁻¹) := by simp only [map_mul, map_inv, inv_inv]

theorem mem_centralizer_secP_klein {c : G} (hw : c * wA O h4 = wA O h4 * c)
    (hf : c * fG O h4 = fG O h4 * c) :
    c ∈ centralizer (secP O (kleinR h4) : Set G) := by
  have : secP O (kleinR h4) = closure {wA O h4, fG O h4} := by
    rw [secP, kleinR, MonoidHom.map_closure, Set.image_pair]
    rfl
  rw [this, centralizer_closure, mem_centralizer_iff]
  rintro g (rfl | rfl)
  · exact hw.symm
  · exact hf.symm

theorem mem_centralizer_secP_cyc {c : G} (hy : c * yG O h4 = yG O h4 * c) :
    c ∈ centralizer (secP O (cycR h4) : Set G) := by
  have : secP O (cycR h4) = zpowers (yG O h4) := by
    rw [secP, cycR, MonoidHom.map_zpowers]
    rfl
  rw [this, mem_centralizer_iff]
  intro g hg
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
  exact ((Commute.zpow_left (show Commute (yG O h4) c from hy.symm) k)).eq

theorem comm_fbar_conj (hNE : L0Normal O (kleinR h4)) {c : ↥(centralizer ({wA O h4} : Set G))}
    (hc : (QuotientGroup.mk c : Cbar O h4) * fbar O h4 = fbar O h4 * QuotientGroup.mk c) :
    ∀ l ∈ altSub (fourSet (m + 3))ᶜ, ∃ l' ∈ altSub (fourSet (m + 3))ᶜ,
      (c : G) * O.φ l * (c : G)⁻¹ = O.φ l' := by
  rw [fbar_eq] at hc
  have hcw : (c : G) * wA O h4 = wA O h4 * c := mem_centralizer_singleton_iff.1 c.2
  rcases conj_eq_or_of_comm_mk (wA_mul_self O h4) hc with h | h
  · have hcf : (c : G) * fG O h4 = fG O h4 * c := by
      calc (c : G) * fG O h4 = ((c : G) * fG O h4 * (c : G)⁻¹) * c := by group
        _ = fG O h4 * c := by rw [h]
    intro l hl
    exact hNE _ (mem_centralizer_secP_klein O h4 hcw hcf) l hl
  · have he : e1G O h4 * (fG O h4 * wA O h4) * (e1G O h4)⁻¹ = fG O h4 := by
      change Φ4 O h4 _ * (Φ4 O h4 _ * Φ4 O h4 _) * (Φ4 O h4 _)⁻¹ = Φ4 O h4 _
      simp only [← map_mul, ← map_inv]
      exact Φ4_eq_of O h4 (by decide)
    have hew : e1G O h4 * wA O h4 = wA O h4 * e1G O h4 :=
      mem_centralizer_singleton_iff.1 (e1G_mem O h4)
    have hc'w : e1G O h4 * (c : G) * wA O h4 = wA O h4 * (e1G O h4 * c) := by
      rw [mul_assoc, hcw, ← mul_assoc, hew, mul_assoc]
    have hc'f : e1G O h4 * (c : G) * fG O h4 = fG O h4 * (e1G O h4 * c) := by
      calc e1G O h4 * (c : G) * fG O h4 =
          e1G O h4 * ((c : G) * fG O h4 * (c : G)⁻¹) * (e1G O h4)⁻¹ * (e1G O h4 * c) := by group
        _ = e1G O h4 * (fG O h4 * wA O h4) * (e1G O h4)⁻¹ * (e1G O h4 * c) := by rw [h]
        _ = fG O h4 * (e1G O h4 * c) := by rw [he]
    exact conj_L0_of_mul O h4 (emb4_comm_kA4 h4 (by decide)) rfl
      (fun l hl => hNE _ (mem_centralizer_secP_klein O h4 hc'w hc'f) l hl)

theorem comm_ybar_conj (hNy : L0Normal O (cycR h4)) {c : ↥(centralizer ({wA O h4} : Set G))}
    (hc : (QuotientGroup.mk c : Cbar O h4) * ybar O h4 = ybar O h4 * QuotientGroup.mk c) :
    ∀ l ∈ altSub (fourSet (m + 3))ᶜ, ∃ l' ∈ altSub (fourSet (m + 3))ᶜ,
      (c : G) * O.φ l * (c : G)⁻¹ = O.φ l' := by
  rw [ybar_eq] at hc
  rcases conj_eq_or_of_comm_mk (wA_mul_self O h4) hc with h | h
  · have hcy : (c : G) * yG O h4 = yG O h4 * c := by
      calc (c : G) * yG O h4 = ((c : G) * yG O h4 * (c : G)⁻¹) * c := by group
        _ = yG O h4 * c := by rw [h]
    intro l hl
    exact hNy _ (mem_centralizer_secP_cyc O h4 hcy) l hl
  · have he : e1G O h4 * (yG O h4 * wA O h4) * (e1G O h4)⁻¹ = yG O h4 := by
      change Φ4 O h4 _ * (Φ4 O h4 _ * Φ4 O h4 _) * (Φ4 O h4 _)⁻¹ = Φ4 O h4 _
      simp only [← map_mul, ← map_inv]
      exact Φ4_eq_of O h4 (by decide)
    have hc'y : e1G O h4 * (c : G) * yG O h4 = yG O h4 * (e1G O h4 * c) := by
      calc e1G O h4 * (c : G) * yG O h4 =
          e1G O h4 * ((c : G) * yG O h4 * (c : G)⁻¹) * (e1G O h4)⁻¹ * (e1G O h4 * c) := by group
        _ = e1G O h4 * (yG O h4 * wA O h4) * (e1G O h4)⁻¹ * (e1G O h4 * c) := by rw [h]
        _ = yG O h4 * (e1G O h4 * c) := by rw [he]
    exact conj_L0_of_mul O h4 (emb4_comm_kA4 h4 (by decide)) rfl
      (fun l hl => hNy _ (mem_centralizer_secP_cyc O h4 hc'y) l hl)

theorem mk_mem_normalizer_of_conj {c : ↥(centralizer ({wA O h4} : Set G))}
    (H : ∀ c' : ↥(centralizer ({wA O h4} : Set G)), (c' = c ∨ c' = c⁻¹) →
      ∀ l ∈ altSub (fourSet (m + 3))ᶜ, ∃ l' ∈ altSub (fourSet (m + 3))ᶜ,
        (c' : G) * O.φ l * (c' : G)⁻¹ = O.φ l') :
    (QuotientGroup.mk c : Cbar O h4) ∈ normalizer (L0bar O h4 : Set (Cbar O h4)) := by
  refine mk_mem_normalizer_L0bar O h4 (H c (Or.inl rfl)) (fun l hl => ?_)
  obtain ⟨l', hl', he⟩ := H c⁻¹ (Or.inr rfl) l hl
  refine ⟨l', hl', ?_⟩
  simpa only [Subgroup.coe_inv, inv_inv] using he

theorem centralizer_le_normalizer_L0bar (hNE : L0Normal O (kleinR h4))
    (hNy : L0Normal O (cycR h4)) {t : Cbar O h4} (ht : t ∈ kbar O h4) (ht1 : t ≠ 1) :
    centralizer ({t} : Set (Cbar O h4)) ≤ normalizer (L0bar O h4 : Set (Cbar O h4)) := by
  intro q hq
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  have hq' : (QuotientGroup.mk c : Cbar O h4) * t = t * QuotientGroup.mk c :=
    mem_centralizer_singleton_iff.1 hq
  have hinv : ∀ {u : Cbar O h4}, (QuotientGroup.mk c : Cbar O h4) * u = u * QuotientGroup.mk c →
      (QuotientGroup.mk c⁻¹ : Cbar O h4) * u = u * QuotientGroup.mk c⁻¹ := by
    intro u hu
    rw [QuotientGroup.mk_inv]
    calc (QuotientGroup.mk c : Cbar O h4)⁻¹ * u =
        (QuotientGroup.mk c : Cbar O h4)⁻¹ * (u * QuotientGroup.mk c) *
          (QuotientGroup.mk c : Cbar O h4)⁻¹ := by group
      _ = (QuotientGroup.mk c : Cbar O h4)⁻¹ * (QuotientGroup.mk c * u) *
          (QuotientGroup.mk c : Cbar O h4)⁻¹ := by rw [hu]
      _ = u * (QuotientGroup.mk c : Cbar O h4)⁻¹ := by group
  rcases (mem_kbar_iff O h4).1 ht with rfl | rfl | rfl | rfl
  · exact absurd rfl ht1
  · exact comm_ebar_mem_normalizer O h4 hq'
  · refine mk_mem_normalizer_of_conj O h4 (fun c' hc' => ?_)
    rcases hc' with rfl | rfl
    · exact comm_fbar_conj O h4 hNE hq'
    · exact comm_fbar_conj O h4 hNE (hinv hq')
  · refine mk_mem_normalizer_of_conj O h4 (fun c' hc' => ?_)
    rcases hc' with rfl | rfl
    · exact comm_ybar_conj O h4 hNy hq'
    · exact comm_ybar_conj O h4 hNy (hinv hq')

theorem kbar_le_centralizer : kbar O h4 ≤ centralizer (L0bar O h4 : Set (Cbar O h4)) := by
  rintro _ ⟨d, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨l, rfl⟩
  rw [psi4_apply, psiL_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  change O.φ l * O.φ (emb4 h4 d) = O.φ (emb4 h4 d) * O.φ l
  rw [O.φ_comm_iff]
  exact (comm_fixSub_compl (emb4_mem_fixSub h4 d) (altSub_compl_le l.2)).symm

theorem mem_kbar_of_comm_ebar (hm : 5 ≤ m) {q : Cbar O h4} (hq : q * ebar O h4 = ebar O h4 * q)
    (hJ : q ∈ centralizer (L0bar O h4 : Set (Cbar O h4))) : q ∈ kbar O h4 := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, hx, hxk⟩ := exists_φ_of_comm_ebar O h4 hq
  have hxc : ∀ l ∈ altSub (fourSet (m + 3))ᶜ, l * x = x * l := by
    intro l hl
    have h1 := mem_centralizer_iff.1 hJ (psiL O h4 ⟨l, hl⟩) ⟨_, rfl⟩
    rw [psiL_apply] at h1
    have hxl := conj_mem_altSub_compl_of_comm h4 hxk hl
    rcases conj_eq_or_of_comm_mk (wA_mul_self O h4) h1.symm with h2 | h2
    · have h3 : O.φ (x * l * x⁻¹) = O.φ l := by
        rw [map_mul, map_mul, map_inv, hx]; exact h2
      have h4' := O.φ_injective h3
      calc l * x = (x * l * x⁻¹) * x := by rw [h4']
        _ = x * l := by group
    · exfalso
      have h3 : O.φ (x * l * x⁻¹) = O.φ (l * emb4 h4 kA4) := by
        rw [map_mul, map_mul, map_inv, hx, map_mul]; exact h2
      have h4' := O.φ_injective h3
      have h5 : emb4 h4 kA4 = l⁻¹ * (x * l * x⁻¹) := by rw [h4']; group
      have h6 : emb4 h4 kA4 ∈ fixSub (fourSet (m + 3)) := by
        rw [h5]; exact mul_mem (inv_mem (altSub_compl_le hl)) (altSub_compl_le hxl)
      exact emb4_kA4_apply_ne h4 (i := ⟨0, by omega⟩) (by simp)
        (h6 _ (by simp [mem_fourSet]))
  have hcard : 4 ≤ ((fourSet (m + 3))ᶜ).card := by
    rw [card_fourSet_compl (by omega)]; omega
  have hfix := (mem_centralizer_altSub_iff hcard).1 (mem_centralizer_iff.2 hxc)
  obtain ⟨x₄, hx₄⟩ := exists_emb4_eq h4 (σ := x) (fun i hi => hfix i hi)
  have hx4k : x₄ * kA4 = kA4 * x₄ := emb4_injective h4 (by
    rw [map_mul (emb4 h4) x₄ kA4, map_mul (emb4 h4) kA4 x₄, hx₄]; exact hxk)
  refine ⟨⟨x₄, mem_dEight_iff.2 hx4k⟩, ?_⟩
  rw [psi4_apply]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  change Φ4 O h4 x₄ = c
  rw [Φ4_apply, hx₄, hx]

theorem mul_self_of_mem_kbar {k : Cbar O h4} (hk : k ∈ kbar O h4) : k * k = 1 := by
  obtain ⟨d, rfl⟩ := hk
  rw [← map_mul]
  rcases dEight_sq d (mem_dEight_iff.1 d.2) with h | h
  · rw [show d * d = 1 from Subtype.ext h, map_one]
  · rw [psi4_congr O h4 (mem_dEight_iff.2 rfl)
      (show ((d * d : dEight) : Perm (Fin 4)) = kA4 from h), psi4_kA4]

end Norm

end CFSG.OddStandard.AltStdSec
