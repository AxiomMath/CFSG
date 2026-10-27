module

public import CFSG.CGT.Timmesfeld75.Involutions
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G]

@[expose, instance_reducible] def conjSMul (E T : Subgroup G)
    (hEN : E ≤ Subgroup.normalizer (T : Set G)) : SMul E T :=
  ⟨fun e t => ⟨(e : G) * t * (e : G)⁻¹, conj_mem_of_mem_normalizer (hEN e.2) t.2⟩⟩

@[expose, instance_reducible] def conjAction (E T : Subgroup G)
    (hEN : E ≤ Subgroup.normalizer (T : Set G)) : MulAction E T :=
  { conjSMul E T hEN with
    one_smul := fun t => Subtype.ext (by
      show ((1 : E) : G) * (t : G) * ((1 : E) : G)⁻¹ = t
      simp)
    mul_smul := fun a b t => Subtype.ext (by
      show ((a * b : E) : G) * (t : G) * ((a * b : E) : G)⁻¹ =
        (a : G) * ((b : G) * (t : G) * (b : G)⁻¹) * (a : G)⁻¹
      simp [mul_assoc]) }

theorem card_fixed_eq_four [Finite G] {T : Subgroup G} (hT : IsElemAbelian 2 T)
    (hTc : Nat.card T = 8) {e : G} (he : e ∈ Subgroup.normalizer (T : Set G)) (he2 : e * e = 1)
    (hne : ∃ t ∈ T, e * t ≠ t * e) :
    Nat.card {t : T // e * t * e⁻¹ = t} = 4 := by
  have ha : e ^ 2 = 1 := by rw [pow_two]; exact he2
  have h1 := card_commSub_mul_card_centralizer hT ha he
  have h2 := commSub_le hT ha he
  have hKC := Subgroup.card_le_of_le h2
  have hCT : T ⊓ Subgroup.centralizer ({e} : Set G) ≤ T := inf_le_left
  have hCdvd : Nat.card ↥(T ⊓ Subgroup.centralizer ({e} : Set G)) ∣ 8 :=
    hTc ▸ Subgroup.card_dvd_of_le hCT
  have hCne : T ⊓ Subgroup.centralizer ({e} : Set G) ≠ T := by
    intro hCT'
    obtain ⟨t, ht, hnc⟩ := hne
    apply hnc
    have : t ∈ T ⊓ Subgroup.centralizer ({e} : Set G) := by rw [hCT']; exact ht
    exact Subgroup.mem_centralizer_iff.1 this.2 e (Set.mem_singleton e)
  have hClt : Nat.card ↥(T ⊓ Subgroup.centralizer ({e} : Set G)) < 8 := by
    rcases lt_or_eq_of_le (Nat.le_of_dvd (by norm_num) hCdvd) with h | h
    · exact h
    · exfalso
      exact hCne (Subgroup.eq_of_le_of_card_ge hCT (by rw [h, hTc]))
  have hC4 : Nat.card ↥(T ⊓ Subgroup.centralizer ({e} : Set G)) = 4 := by
    have h8 : 8 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({e} : Set G)) *
        Nat.card ↥(T ⊓ Subgroup.centralizer ({e} : Set G)) := by
      calc 8 = Nat.card ↥(commSub e T) *
            Nat.card ↥(T ⊓ Subgroup.centralizer ({e} : Set G)) := by rw [h1, hTc]
        _ ≤ _ := Nat.mul_le_mul_right _ hKC
    generalize Nat.card ↥(T ⊓ Subgroup.centralizer ({e} : Set G)) = c at hCdvd hClt h8 ⊢
    interval_cases c <;> simp_all
  rw [← hC4]
  refine Nat.card_congr
    { toFun := fun t => ⟨(t.1 : G), t.1.2, Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have := t.2
        calc h * (t.1 : G) = h * (t.1 : G) * h⁻¹ * h := by group
          _ = (t.1 : G) * h := by rw [this]⟩
      invFun := fun c => ⟨⟨c, c.2.1⟩, by
        have := Subgroup.mem_centralizer_iff.1 c.2.2 e (Set.mem_singleton e)
        show e * (c : G) * e⁻¹ = c
        rw [this]; group⟩
      left_inv := fun t => Subtype.ext (Subtype.ext rfl)
      right_inv := fun c => Subtype.ext rfl }

theorem exists_centralizes_of_card_ge_eight [Finite G] {T E : Subgroup G}
    (hT : IsElemAbelian 2 T) (hTc : Nat.card T = 8) (hE : IsElemAbelian 2 E)
    (hEN : E ≤ Subgroup.normalizer (T : Set G)) (hEc : 8 ≤ Nat.card E) :
    ∃ k ∈ E, k ≠ 1 ∧ ∀ t ∈ T, k * t = t * k := by
  classical
  by_contra hcon
  push Not at hcon
  let _ : MulAction E T := conjAction E T hEN
  have : Fintype E := Fintype.ofFinite E
  have : Fintype T := Fintype.ofFinite T
  have : ∀ g : E, Fintype (MulAction.fixedBy T g) := fun g => Fintype.ofFinite _
  have : Fintype (Quotient (MulAction.orbitRel E T)) := Fintype.ofFinite _
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group E T
  have hsmul : ∀ (a : E) (t : T), ((a • t : T) : G) = (a : G) * t * (a : G)⁻¹ := fun _ _ => rfl
  have hfixcard : ∀ a : E, Fintype.card (MulAction.fixedBy T a) =
      Nat.card {t : T // (a : G) * t * (a : G)⁻¹ = t} := by
    intro a
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
    rw [MulAction.mem_fixedBy, Subtype.ext_iff, hsmul]
  have hfix1 : Fintype.card (MulAction.fixedBy T (1 : E)) = 8 := by
    rw [hfixcard, ← hTc]
    refine Nat.card_congr (Equiv.subtypeUnivEquiv fun t => ?_)
    simp
  have hfix : ∀ a : E, a ≠ 1 → Fintype.card (MulAction.fixedBy T a) = 4 := by
    intro a ha1
    rw [hfixcard]
    refine card_fixed_eq_four hT hTc (hEN a.2) ?_ ?_
    · have h2 : (a : G) ^ 2 = 1 := hE.2 a a.2
      rw [← pow_two]; exact h2
    · exact hcon a a.2 (fun h => ha1 (Subtype.ext h))
  have hsum : ∑ a : E, Fintype.card (MulAction.fixedBy T a) =
      4 * Fintype.card E + 4 := by
    have : ∀ a : E, Fintype.card (MulAction.fixedBy T a) = 4 + if a = 1 then 4 else 0 := by
      intro a
      by_cases ha : a = 1
      · subst ha; rw [hfix1]; simp
      · rw [hfix a ha]; simp [ha]
    rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_add_distrib]
    simp [mul_comm]
  have hdvd : Fintype.card E ∣ 4 := by
    have h1 : Fintype.card E ∣ 4 * Fintype.card E + 4 := by
      rw [← hsum, hburn]
      exact dvd_mul_left _ _
    exact (Nat.dvd_add_right (dvd_mul_left _ _)).1 h1
  have h4 := Nat.le_of_dvd (by norm_num) hdvd
  rw [Fintype.card_eq_nat_card] at h4
  omega

end CFSG.CGT.T75R
