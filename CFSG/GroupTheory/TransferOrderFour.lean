module

public import CFSG.GroupTheory.TransferOrderFourStmt
public import CFSG.GroupTheory.TransferOrderFourCount

public section

namespace CFSG.GroupTheory.TransferOrderFour

open MulAction Subgroup

section Ext

variable {G : Type*} [Group G] {T : Subgroup G} {A : Type*} [CommGroup A] (ψ : T →* A)

open scoped Classical in
noncomputable def extOne (g : G) : A := if h : g ∈ T then ψ ⟨g, h⟩ else 1

variable {ψ}

theorem extOne_of_mem {g : G} (hg : g ∈ T) : extOne ψ g = ψ ⟨g, hg⟩ := dif_pos hg

theorem extOne_of_not_mem {g : G} (hg : g ∉ T) : extOne ψ g = 1 := dif_neg hg

theorem extOne_conj {t : G} (ht : t ∈ T) (g : G) : extOne ψ (t⁻¹ * g * t) = extOne ψ g := by
  by_cases hg : g ∈ T
  · have hg' : t⁻¹ * g * t ∈ T := T.mul_mem (T.mul_mem (T.inv_mem ht) hg) ht
    rw [extOne_of_mem hg, extOne_of_mem hg']
    have : (⟨t⁻¹ * g * t, hg'⟩ : T) = ⟨t, ht⟩⁻¹ * ⟨g, hg⟩ * ⟨t, ht⟩ := rfl
    rw [this, map_mul, map_mul, map_inv, inv_mul_cancel_comm]
  · have hg' : t⁻¹ * g * t ∉ T := fun h' => hg (by
      simpa [mul_assoc] using T.mul_mem (T.mul_mem ht h') (T.inv_mem ht))
    rw [extOne_of_not_mem hg, extOne_of_not_mem hg']

end Ext

section C1

variable {G : Type*} [Group G] {k : G} {T : Subgroup G} {A : Type*} [CommGroup A]

abbrev C1 (ψ : T →* A) (k : G) : Prop :=
  ∀ (u : G) (hu : u ∈ T), IsConj (k ^ 2) u →
    ψ ⟨u, hu⟩ = 1 ∨ 4 ∣ Nat.card (MulAction.orbit (ConjAct T) (⟨u, hu⟩ : T))

variable {ψ : T →* A}

theorem Core.ψ_sq_eq_one (h : Core k T) (hC1 : C1 ψ k) : extOne ψ (k ^ 2) = 1 := by
  rw [extOne_of_mem h.sq_mem]
  rcases hC1 (k ^ 2) h.sq_mem (IsConj.refl _) with h1 | h4
  · exact h1
  · exfalso
    have hfix : (⟨k ^ 2, h.sq_mem⟩ : T) ∈ fixedPoints (ConjAct T) T := by
      rw [MulAction.mem_fixedPoints]
      intro g
      rw [ConjAct.smul_def]
      apply Subtype.ext
      have hc : (↑(ConjAct.ofConjAct g) : G) * k ^ 2 = k ^ 2 * ↑(ConjAct.ofConjAct g) :=
        mem_Cz.mp (h.le (ConjAct.ofConjAct g).2)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hc]
      group
    have h1 : Nat.card (orbit (ConjAct T) (⟨k ^ 2, h.sq_mem⟩ : T)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨(Set.subsingleton_coe _).mpr (subsingleton_orbit_iff_mem_fixedPoints.mpr hfix),
        (nonempty_orbit _).to_subtype⟩
    rw [h1] at h4
    omega

theorem Core.ψ_k_sq (h : Core k T) (hz : extOne ψ (k ^ 2) = 1) : ψ ⟨k, h.mem⟩ ^ 2 = 1 := by
  rw [← map_pow]
  have : (⟨k, h.mem⟩ : T) ^ 2 = ⟨k ^ 2, h.sq_mem⟩ := Subtype.ext (by simp)
  rwa [this, ← extOne_of_mem h.sq_mem]

theorem Core.extOne_conj_of_mem_Cz (h : Core k T) (hz : extOne ψ (k ^ 2) = 1) {x : G}
    (hx : x ∈ Cz k) : extOne ψ (x⁻¹ * k * x) = ψ ⟨k, h.mem⟩ := by
  rcases h.conj_eq_or_of_mem_Cz hx with h1 | h1
  · rw [h1, extOne_of_mem h.mem]
  · have hm : k⁻¹ ∈ T := T.inv_mem h.mem
    rw [h1, extOne_of_mem hm]
    have : (⟨k⁻¹, hm⟩ : T) = ⟨k, h.mem⟩⁻¹ := rfl
    rw [this, map_inv]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h.ψ_k_sq hz)

end C1

section Decomp

variable {G : Type*} [Group G] [Fintype G] {k : G} {T : Subgroup G} {A : Type*} [CommGroup A]

open scoped Classical in
theorem transfer_eq_prod (hk : orderOf k = 4) (ψ : T →* A) :
    ψ.transfer k =
      (∏ c : G ⧸ T with k • c = c, extOne ψ (c.out⁻¹ * k * c.out)) *
      ∏ q : orbitRel.Quotient (zpowers k) (G ⧸ T)
        with ¬ k • q.out = q.out ∧ k ^ 2 • q.out = q.out,
        extOne ψ (q.out.out⁻¹ * k ^ 2 * q.out.out) := by
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  have key : ∀ q : orbitRel.Quotient (zpowers k) (G ⧸ T),
      ψ ⟨q.out.out⁻¹ * k ^ Function.minimalPeriod (k • ·) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem T k q.out⟩ =
      if k • q.out = q.out then extOne ψ (q.out.out⁻¹ * k * q.out.out)
      else if k ^ 2 • q.out = q.out then extOne ψ (q.out.out⁻¹ * k ^ 2 * q.out.out) else 1 := by
    intro q
    rw [← extOne_of_mem (QuotientGroup.out_conj_pow_minimalPeriod_mem T k q.out)]
    have h4 := (minimalPeriod_dvd_iff k q.out 4).mpr (by rw [pow_four_eq_one hk, one_smul])
    have h1 := minimalPeriod_dvd_iff k q.out 1
    have h2 := minimalPeriod_dvd_iff k q.out 2
    generalize Function.minimalPeriod (k • ·) q.out = n at h4 h1 h2 ⊢
    by_cases hc1 : k • q.out = q.out
    · rw [if_pos hc1, Nat.dvd_one.mp (h1.mpr (by rwa [pow_one])), pow_one]
    · rw [if_neg hc1]
      by_cases hc2 : k ^ 2 • q.out = q.out
      · have hn : n = 1 ∨ n = 2 := (Nat.dvd_prime Nat.prime_two).mp (h2.mpr hc2)
        rcases hn with rfl | rfl
        · exact absurd (by simpa using h1.mp (dvd_refl 1)) hc1
        · rw [if_pos hc2]
      · rw [if_neg hc2, nat_eq_four_of_dvd h4 (fun h => hc2 (h2.mp h)), pow_four_eq_one hk,
          mul_one, inv_mul_cancel, extOne_of_mem T.one_mem]
        exact map_one ψ
  rw [Finset.prod_congr rfl (fun q _ => key q), Finset.prod_ite, Finset.prod_ite,
    Finset.prod_const_one, mul_one, Finset.filter_filter]
  congr 1
  refine Finset.prod_nbij' (fun q => q.out)
    (fun c => Quotient.mk (orbitRel (zpowers k) (G ⧸ T)) c) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simpa using hq
  · intro c hc
    have hc' : k • c = c := by simpa using hc
    simpa [out_mk_of_smul_eq hc'] using hc'
  · intro q _
    exact Quotient.out_eq q
  · intro c hc
    exact out_mk_of_smul_eq (by simpa using hc)
  · intro q _
    rfl

end Decomp

section Conjugates

variable {G : Type*} [Group G] {k : G} {T : Subgroup G}

def Xs (k : G) (T : Subgroup G) : Set (Subgroup G) :=
  {X | (∃ g : G, X = zpowers (g⁻¹ * k * g)) ∧ X ≤ T ∧ X ≠ zpowers k}

theorem Core.fk_mem_Xs_iff (h : Core k T) (x : G) :
    fk k x ∈ Xs k T ↔ x⁻¹ * k * x ∈ T ∧ x⁻¹ * k * x ∉ zpowers k := by
  unfold Xs fk
  simp only [Set.mem_setOf_eq, Subgroup.zpowers_le]
  refine ⟨fun ⟨_, h1, h2⟩ => ⟨h1, fun hy => h2 ?_⟩,
    fun ⟨h1, h2⟩ => ⟨⟨x, rfl⟩, h1, fun h3 => h2 ?_⟩⟩
  · exact h.zpowers_conj_eq (h.mem_Cz_iff.mpr hy)
  · rw [← h3]; exact mem_zpowers _

end Conjugates

section CountOne

variable {G : Type*} [Group G] [Fintype G] {k : G} {T : Subgroup G} {A : Type*} [CommGroup A]

open scoped Classical

theorem Core.card_filter_Cz (h : Core k T) :
    (Finset.univ.filter fun c : G ⧸ T => k • c = c ∧ c.out ∈ Cz k).card =
      T.relIndex (Cz k) := by
  rw [card_filter_eq_nat_card]
  have h1 := card_cosets (Cz k) T h.le (fz k) fz_eq_iff ({k ^ 2} : Set G)
    (by rintro _ rfl; exact ⟨1, by simp [fz]⟩)
    (by
      intro x t ht hx
      rw [Set.mem_singleton_iff] at hx ⊢
      rw [fz_mul_right, hx]
      have := mem_Cz.mp (h.le ht)
      calc t⁻¹ * k ^ 2 * t = t⁻¹ * (k ^ 2 * t) := by group
        _ = t⁻¹ * (t * k ^ 2) := by rw [this]
        _ = k ^ 2 := by group)
  simp only [Nat.card_unique, one_mul] at h1
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  have hz : fz k c.out = k ^ 2 ↔ c.out ∈ Cz k := by
    have := fz_eq_iff (k := k) c.out 1
    simpa [fz] using this
  rw [Set.mem_singleton_iff, hz]
  exact ⟨fun hc => hc.2, fun hc => ⟨h.smul_eq_of_mem_Cz hc, hc⟩⟩

theorem Core.card_filter_X (h : Core k T) :
    (Finset.univ.filter fun c : G ⧸ T => k • c = c ∧ c.out ∉ Cz k).card =
      Nat.card (Xs k T) * T.relIndex (Cz k) := by
  rw [card_filter_eq_nat_card]
  have h1 := card_cosets (Cz k) T h.le (fk k) h.fk_eq_iff (Xs k T)
    (fun X hX => by obtain ⟨g, hg⟩ := hX.1; exact ⟨g, hg.symm⟩)
    (by
      intro x t ht hx
      rw [h.fk_mem_Xs_iff] at hx ⊢
      have e : (x * t)⁻¹ * k * (x * t) = t⁻¹ * (x⁻¹ * k * x) * t := by group
      rw [e, conj_mem_iff_of_mem ht,
        ← (Subgroup.mem_normalizer_iff''.mp (h.normalizes (h.le ht)) (x⁻¹ * k * x))]
      exact hx)
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  rw [h.fk_mem_Xs_iff, smul_eq_iff_out, h.mem_Cz_iff]

variable {ψ : T →* A}

theorem Core.prod_fixed (h : Core k T) (hz : extOne ψ (k ^ 2) = 1) {c₀ : A} (hc₀ : c₀ ^ 2 = 1)
    (hC2 : ∀ (g : G) (hg : g⁻¹ * k * g ∈ T), g⁻¹ * k * g ∉ zpowers k → ψ ⟨_, hg⟩ = c₀)
    (hX : Even (Nat.card (Xs k T))) (hodd : Odd (T.relIndex (Cz k))) :
    ∏ c : G ⧸ T with k • c = c, extOne ψ (c.out⁻¹ * k * c.out) = ψ ⟨k, h.mem⟩ := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter fun c : G ⧸ T => k • c = c)
    (fun c => c.out ∈ Cz k), Finset.filter_filter, Finset.filter_filter]
  have e1 : ∏ c ∈ Finset.univ.filter (fun c : G ⧸ T => k • c = c ∧ c.out ∈ Cz k),
      extOne ψ (c.out⁻¹ * k * c.out) = ψ ⟨k, h.mem⟩ ^ T.relIndex (Cz k) := by
    rw [Finset.prod_congr rfl (fun c hc =>
      h.extOne_conj_of_mem_Cz hz (Finset.mem_filter.mp hc).2.2), Finset.prod_const,
      h.card_filter_Cz]
  have e2 : ∏ c ∈ Finset.univ.filter (fun c : G ⧸ T => k • c = c ∧ ¬ c.out ∈ Cz k),
      extOne ψ (c.out⁻¹ * k * c.out) = c₀ ^ (Nat.card (Xs k T) * T.relIndex (Cz k)) := by
    rw [Finset.prod_congr rfl (fun c hc => ?_), Finset.prod_const, h.card_filter_X]
    obtain ⟨hc1, hc2⟩ := (Finset.mem_filter.mp hc).2
    have hm := (smul_eq_iff_out k c).mp hc1
    rw [extOne_of_mem hm]
    exact hC2 _ hm (fun hy => hc2 (h.mem_Cz_iff.mpr hy))
  rw [e1, e2, pow_of_odd_of_sq (h.ψ_k_sq hz) hodd, pow_of_even_of_sq hc₀ (hX.mul_right _),
    mul_one]

end CountOne

section CountTwo

variable {G : Type*} [Group G] [Fintype G] {k : G} {T : Subgroup G} {A : Type*} [CommGroup A]
  {ψ : T →* A}

open scoped Classical

def Q2 (ψ : T →* A) (k : G) (a : A) (x : G) : Prop :=
  x⁻¹ * k ^ 2 * x ∈ T ∧ x⁻¹ * k * x ∉ T ∧ extOne ψ (x⁻¹ * k ^ 2 * x) = a

theorem Core.Q2_mul_left (h : Core k T) (a : A) {c : G} (hc : c ∈ Cz k) (x : G) :
    Q2 ψ k a (c * x) ↔ Q2 ψ k a x := by
  have hz : (c * x)⁻¹ * k ^ 2 * (c * x) = x⁻¹ * k ^ 2 * x := fz_mul_left hc x
  unfold Q2
  rw [hz, h.conj_mem_iff_mul hc]

theorem Q2_mul_right (a : A) (x : G) {t : G} (ht : t ∈ T) :
    Q2 ψ k a (x * t) ↔ Q2 ψ k a x := by
  have e1 : (x * t)⁻¹ * k ^ 2 * (x * t) = t⁻¹ * (x⁻¹ * k ^ 2 * x) * t := by group
  have e2 : (x * t)⁻¹ * k * (x * t) = t⁻¹ * (x⁻¹ * k * x) * t := by group
  unfold Q2
  rw [e1, e2, conj_mem_iff_of_mem ht, conj_mem_iff_of_mem ht, extOne_conj ht]

theorem Core.Q2_out_smul (h : Core k T) (a : A) {g : G} (hg : g ∈ Cz k) (c : G ⧸ T) :
    Q2 ψ k a (g • c).out ↔ Q2 ψ k a c.out := by
  have e : g • c = QuotientGroup.mk (g * c.out) := by
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨t, ht, e'⟩ := exists_out_eq_mul (T := T) (g * c.out)
  rw [e, e', Q2_mul_right a _ ht, h.Q2_mul_left a hg]

def SA (ψ : T →* A) (k : G) (a : A) : Set G := {u | ∃ x, fz k x = u ∧ Q2 ψ k a x}

theorem Core.fz_mem_SA_iff (h : Core k T) (a : A) (x : G) :
    fz k x ∈ SA ψ k a ↔ Q2 ψ k a x := by
  constructor
  · rintro ⟨y, hy, hQ⟩
    have hc : x * y⁻¹ ∈ Cz k := by
      simpa using inv_mem ((fz_eq_iff y x).mp hy)
    have e : x = (x * y⁻¹) * y := by group
    rw [e]
    exact (h.Q2_mul_left a hc y).mpr hQ
  · intro hQ
    exact ⟨x, rfl, hQ⟩

theorem SA_subset (a : A) : SA ψ k a ⊆ T := by
  rintro _ ⟨x, rfl, hQ, _⟩
  exact hQ

theorem Core.SA_conj (h : Core k T) (a : A) {s : G} (hs : s ∈ T) {u : G} (hu : u ∈ SA ψ k a) :
    s * u * s⁻¹ ∈ SA ψ k a := by
  obtain ⟨x, rfl, hQ⟩ := hu
  have e : s * fz k x * s⁻¹ = fz k (x * s⁻¹) := by rw [fz_mul_right, inv_inv]
  rw [e, h.fz_mem_SA_iff]
  exact (Q2_mul_right a x (T.inv_mem hs)).mpr hQ

theorem Core.four_dvd_SA (h : Core k T) (hC1 : C1 ψ k) {a : A} (ha : a ≠ 1) :
    4 ∣ Nat.card (SA ψ k a) := by
  refine dvd_card_of_conj_stable T (SA ψ k a) (SA_subset a)
    (fun s hs u hu => h.SA_conj a hs hu) 4 ?_
  intro u hu huS
  obtain ⟨x, rfl, hQ⟩ := huS
  have hconj : IsConj (k ^ 2) (fz k x) := isConj_iff.mpr ⟨x⁻¹, by simp [fz]⟩
  rcases hC1 _ hu hconj with h1 | h4
  · exact absurd (hQ.2.2.symm.trans ((extOne_of_mem hu).trans h1)) ha
  · exact h4

theorem Core.four_dvd_card_filter_Q2 (h : Core k T) (hC1 : C1 ψ k) {a : A} (ha : a ≠ 1) :
    4 ∣ (Finset.univ.filter fun c : G ⧸ T => Q2 ψ k a c.out).card := by
  rw [card_filter_eq_nat_card]
  have h1 := card_cosets (Cz k) T h.le (fz k) fz_eq_iff (SA ψ k a)
    (fun u ⟨x, hx, _⟩ => ⟨x, hx⟩)
    (fun x t ht hx => by
      rw [h.fz_mem_SA_iff] at hx ⊢
      exact (Q2_mul_right a x ht).mpr hx)
  have h2 : Nat.card {c : G ⧸ T // Q2 ψ k a c.out} =
      Nat.card {c : G ⧸ T // fz k c.out ∈ SA ψ k a} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun c => (h.fz_mem_SA_iff a c.out).symm)
  rw [h2, h1]
  exact Dvd.dvd.mul_right (h.four_dvd_SA hC1 ha) _

theorem Q2_out_iff (a : A) (q : orbitRel.Quotient (zpowers k) (G ⧸ T)) :
    Q2 ψ k a q.out.out ↔ ¬ k • q.out = q.out ∧ k ^ 2 • q.out = q.out ∧
      extOne ψ (q.out.out⁻¹ * k ^ 2 * q.out.out) = a := by
  unfold Q2
  rw [smul_eq_iff_out, smul_eq_iff_out]
  tauto

theorem Core.card_filter_Q2_eq (h : Core k T) (a : A) :
    (Finset.univ.filter fun c : G ⧸ T => Q2 ψ k a c.out).card =
      2 * (Finset.univ.filter fun q : orbitRel.Quotient (zpowers k) (G ⧸ T) =>
        ¬ k • q.out = q.out ∧ k ^ 2 • q.out = q.out ∧
          extOne ψ (q.out.out⁻¹ * k ^ 2 * q.out.out) = a).card := by
  have hkC : k ∈ Cz k := mem_Cz.mpr (Commute.self_pow k 2).eq
  have hF : ∀ (g : zpowers k) (c : G ⧸ T),
      (if Q2 ψ k a (g • c).out then 1 else 0 : ℕ) = if Q2 ψ k a c.out then 1 else 0 := by
    intro g c
    have hg : (g : G) ∈ Cz k := (Subgroup.zpowers_le.mpr hkC) g.2
    have : Q2 ψ k a (g • c).out ↔ Q2 ψ k a c.out := h.Q2_out_smul a hg c
    simp only [this]
  have h1 := sum_eq_sum_orbits (K := zpowers k)
    (fun c : G ⧸ T => if Q2 ψ k a c.out then 1 else 0) hF
  rw [Finset.sum_boole] at h1
  simp only [Nat.cast_id] at h1
  rw [h1, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : Q2 ψ k a q.out.out
  · have hq' := (Q2_out_iff a q).mp hq
    rw [if_pos hq, if_pos hq', card_orbit_eq_two hq'.1 hq'.2.1]
  · have hq' := fun h' => hq ((Q2_out_iff a q).mpr h')
    rw [if_neg hq, if_neg hq']
    simp

theorem Core.prod_two (h : Core k T) (hC1 : C1 ψ k) :
    ∏ q : orbitRel.Quotient (zpowers k) (G ⧸ T)
      with ¬ k • q.out = q.out ∧ k ^ 2 • q.out = q.out,
      extOne ψ (q.out.out⁻¹ * k ^ 2 * q.out.out) = 1 := by
  set s := Finset.univ.filter (fun q : orbitRel.Quotient (zpowers k) (G ⧸ T) =>
    ¬ k • q.out = q.out ∧ k ^ 2 • q.out = q.out) with hs
  set g : orbitRel.Quotient (zpowers k) (G ⧸ T) → A :=
    fun q => extOne ψ (q.out.out⁻¹ * k ^ 2 * q.out.out) with hg
  have hg2 : ∀ q, g q ^ 2 = 1 := by
    intro q
    by_cases hm : q.out.out⁻¹ * k ^ 2 * q.out.out ∈ T
    · simp only [hg]
      rw [extOne_of_mem hm, ← map_pow]
      have : (⟨_, hm⟩ : T) ^ 2 = 1 := Subtype.ext (by
        have e : (k ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact pow_four_eq_one h.order
        show (q.out.out⁻¹ * k ^ 2 * q.out.out) ^ 2 = 1
        rw [inv_mul_mul_pow, e]
        group)
      rw [this, map_one]
    · simp only [hg]
      rw [extOne_of_not_mem hm, one_pow]
  have hprod : ∏ q ∈ s, g q = ∏ a ∈ s.image g, a ^ (s.filter (fun q => g q = a)).card :=
    Finset.prod_comp id g
  rw [hprod]
  refine Finset.prod_eq_one fun a ha => ?_
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
  by_cases h1 : g q = 1
  · rw [h1, one_pow]
  · refine pow_of_even_of_sq (hg2 q) ?_
    have h4 := h.four_dvd_card_filter_Q2 hC1 h1
    rw [h.card_filter_Q2_eq] at h4
    have e : s.filter (fun q' => g q' = g q) = Finset.univ.filter (fun q' :
        orbitRel.Quotient (zpowers k) (G ⧸ T) => ¬ k • q'.out = q'.out ∧ k ^ 2 • q'.out = q'.out ∧
          extOne ψ (q'.out.out⁻¹ * k ^ 2 * q'.out.out) = g q) := by
      rw [hs, Finset.filter_filter]
      simp only [hg, and_assoc]
    rw [e, Nat.even_iff]
    omega

end CountTwo

theorem transferCoreStmt_holds : TransferCoreStmt := by
  intro G _ _ A _ k hk hN T _ hTle hodd hkT ψ hC1 c hc hC2 hX
  haveI := Fintype.ofFinite G
  have h : Core k T := ⟨hk, hN, hTle, hkT⟩
  have hz := h.ψ_sq_eq_one hC1
  rw [transfer_eq_prod hk, h.prod_fixed hz hc hC2 hX hodd, h.prod_two hC1, mul_one]

end CFSG.GroupTheory.TransferOrderFour
