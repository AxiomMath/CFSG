module

public import CFSG.GroupTheory.ThreeTranspositions.Basic
public import CFSG.Blueprint.FischerDefs

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.Blueprint.Fischer

variable {Q : Type} [Group Q] [Finite Q]

private lemma sq_eq_one_of_isConj {t d : Q} (ht2 : t ^ 2 = 1) (hd : IsConj t d) : d ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hd
  rw [conj_pow, ht2, mul_one, mul_inv_cancel]

private lemma cube_eq_one_of_isConj_of_not_commute {t d e : Q} (ht2 : t ^ 2 = 1)
    (h : ∀ a : Q, (t * (a * t * a⁻¹)) ^ 2 = 1 ∨ (t * (a * t * a⁻¹)) ^ 3 = 1)
    (hd : IsConj t d) (he : IsConj t e) (hne : d * e ≠ e * d) : (d * e) ^ 3 = 1 := by
  rcases sq_or_cube_of_isConj h hd he with h2 | h3
  · exfalso
    apply hne
    have hd2 : d ^ 2 = 1 := sq_eq_one_of_isConj ht2 hd
    have he2 : e ^ 2 = 1 := sq_eq_one_of_isConj ht2 he
    have hde : d * e = (d * e)⁻¹ :=
      mul_eq_one_iff_eq_inv.mp (by simpa [pow_two] using h2)
    have hd' : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hd2)
    have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using he2)
    rw [hde, mul_inv_rev, hd', he']
  · exact h3

private lemma exists_mem_normalClosure_conj_eq_of_isConj_of_not_commute {t d e : Q}
    (ht2 : t ^ 2 = 1)
    (h : ∀ a : Q, (t * (a * t * a⁻¹)) ^ 2 = 1 ∨ (t * (a * t * a⁻¹)) ^ 3 = 1)
    (hd : IsConj t d) (he : IsConj t e) (hne : d * e ≠ e * d) :
    ∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * d * n⁻¹ = e := by
  have hd2 : d ^ 2 = 1 := sq_eq_one_of_isConj ht2 hd
  have he2 : e ^ 2 = 1 := sq_eq_one_of_isConj ht2 he
  have h3 : (d * e) ^ 3 = 1 := cube_eq_one_of_isConj_of_not_commute ht2 h hd he hne
  have hdA : d ∈ Subgroup.normalClosure ({t} : Set Q) :=
    Subgroup.conjugatesOfSet_subset_normalClosure
      (Group.mem_conjugatesOfSet_iff.mpr ⟨t, rfl, hd⟩)
  have heA : e ∈ Subgroup.normalClosure ({t} : Set Q) :=
    Subgroup.conjugatesOfSet_subset_normalClosure
      (Group.mem_conjugatesOfSet_iff.mpr ⟨t, rfl, he⟩)
  exact ⟨d * e, (Subgroup.normalClosure ({t} : Set Q)).mul_mem hdA heA,
    (mul_mul_inv_eq_of_involutions hd2 he2 h3).2⟩

theorem exists_noncommuting_conj_of_pPrimeCore_eq_bot (hO : CFSG.pPrimeCore 3 Q = ⊥) {t : Q}
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ a b : Q, IsConj t a ∧ IsConj t b ∧ a * b ≠ b * a := by
  by_contra hconj
  have hcomm : ∀ a b : Q, IsConj t a → IsConj t b → a * b = b * a := by
    intro a b ha hb
    by_contra hab
    exact hconj ⟨a, b, ha, hb, hab⟩
  have hScomm : (Group.conjugatesOfSet ({t} : Set Q)).Pairwise Commute := by
    intro a ha b hb _
    have ha' : IsConj t a := by
      obtain ⟨c, hc, hca⟩ := Group.mem_conjugatesOfSet_iff.mp ha
      rw [Set.mem_singleton_iff] at hc
      subst c
      exact hca
    have hb' : IsConj t b := by
      obtain ⟨c, hc, hcb⟩ := Group.mem_conjugatesOfSet_iff.mp hb
      rw [Set.mem_singleton_iff] at hc
      subst c
      exact hcb
    exact (commute_iff_eq a b).mpr (hcomm a b ha' hb')
  haveI hNcomm : IsMulCommutative (Subgroup.normalClosure ({t} : Set Q)) :=
    show IsMulCommutative (Subgroup.closure (Group.conjugatesOfSet ({t} : Set Q))) from
      Subgroup.isMulCommutative_closure hScomm
  have hcommN : ∀ a b : Subgroup.normalClosure ({t} : Set Q), a * b = b * a :=
    fun a b => mul_comm' a b
  have hN2Q : ∀ y : Q, y ∈ Subgroup.normalClosure ({t} : Set Q) → y ^ 2 = 1 := by
    intro y hy
    have hy' : y ∈ Subgroup.closure (Group.conjugatesOfSet ({t} : Set Q)) := hy
    refine Subgroup.closure_induction (p := fun z _ => z ^ 2 = 1) ?_ ?_ ?_ ?_ hy'
    · intro z hz
      obtain ⟨c, hc, hcz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
      rw [Set.mem_singleton_iff] at hc
      subst c
      obtain ⟨g, rfl⟩ := isConj_iff.mp hcz
      rw [conj_pow, ht2, mul_one, mul_inv_cancel]
    · simp
    · intro x y hx hy ihx ihy
      have hxy : x * y = y * x :=
        congrArg Subtype.val
          (hcommN ⟨x, show x ∈ Subgroup.normalClosure ({t} : Set Q) from hx⟩
            ⟨y, show y ∈ Subgroup.normalClosure ({t} : Set Q) from hy⟩)
      have hsq : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
        calc (x * y) ^ 2 = (x * y) * (x * y) := by rw [pow_two]
          _ = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [← hxy]
          _ = x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group
      rw [hsq, ihx, ihy, one_mul]
    · intro x hx ihx
      rw [inv_pow, ihx, inv_one]
  have hN2 : ∀ x : Subgroup.normalClosure ({t} : Set Q), x ^ 2 = 1 :=
    fun x => Subtype.ext (hN2Q (x : Q) x.2)
  have h3not : ¬ 3 ∣ Nat.card (Subgroup.normalClosure ({t} : Set Q)) := by
    intro hdvd
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
      (G := Subgroup.normalClosure ({t} : Set Q)) 3 hdvd
    have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (hN2 x)
    rw [hx] at hdvd2
    norm_num at hdvd2
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.normalClosure ({t} : Set Q))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3not
  have hle : Subgroup.normalClosure ({t} : Set Q) ≤ CFSG.pPrimeCore 3 Q :=
    le_sSup (show Subgroup.normalClosure ({t} : Set Q) ∈
        {K : Subgroup Q | K.Normal ∧ Nat.Coprime 3 (Nat.card K)} from
      ⟨inferInstance, hcop⟩)
  rw [hO] at hle
  exact ht1 (Subgroup.mem_bot.mp (hle (Subgroup.subset_normalClosure rfl)))

theorem exists_mem_normalClosure_conj_eq_of_not_hasE9 (hX : ¬ HasE9 Q) {t : Q} (ht2 : t ^ 2 = 1)
    (h : ∀ a : Q, (t * (a * t * a⁻¹)) ^ 2 = 1 ∨ (t * (a * t * a⁻¹)) ^ 3 = 1)
    (hnc : ∃ a b : Q, IsConj t a ∧ IsConj t b ∧ a * b ≠ b * a) {y : Q} (hy : IsConj t y) :
    ∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * t * n⁻¹ = y := by
  by_contra hty
  obtain ⟨a, b, ha, hb, hab⟩ := hnc
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  let t' : Q := g⁻¹ * b * g
  have ht' : IsConj t t' :=
    hb.trans (isConj_iff.mpr ⟨g⁻¹, by
      show g⁻¹ * b * (g⁻¹)⁻¹ = g⁻¹ * b * g
      group⟩)
  have htt' : t * t' ≠ t' * t := by
    intro hcomm
    have ht'conj : g * t' * g⁻¹ = b := by
      show g * (g⁻¹ * b * g) * g⁻¹ = b
      group
    have hsplit₁ : g * (t * t') * g⁻¹ = (g * t * g⁻¹) * (g * t' * g⁻¹) := by group
    have hsplit₂ : g * (t' * t) * g⁻¹ = (g * t' * g⁻¹) * (g * t * g⁻¹) := by group
    have h1 : g * (t * t') * g⁻¹ = a * b := by rw [hsplit₁, hg, ht'conj]
    have h2 : g * (t' * t) * g⁻¹ = b * a := by rw [hsplit₂, ht'conj, hg]
    have hc := congrArg (fun z => g * z * g⁻¹) hcomm
    rw [h1, h2] at hc
    exact hab hc
  obtain ⟨k, hk⟩ := isConj_iff.mp hy
  let y' : Q := k * t' * k⁻¹
  have hy' : IsConj t y' := ht'.trans (isConj_iff.mpr ⟨k, rfl⟩)
  have hyy' : y * y' ≠ y' * y := by
    intro hcomm
    have hk1 : k⁻¹ * y * k = t := by rw [← hk]; group
    have hk2 : k⁻¹ * y' * k = t' := by
      show k⁻¹ * (k * t' * k⁻¹) * k = t'
      group
    have hsplit₁ : k⁻¹ * (y * y') * k = (k⁻¹ * y * k) * (k⁻¹ * y' * k) := by group
    have hsplit₂ : k⁻¹ * (y' * y) * k = (k⁻¹ * y' * k) * (k⁻¹ * y * k) := by group
    have hc := congrArg (fun z => k⁻¹ * z * k) hcomm
    rw [hsplit₁, hsplit₂, hk1, hk2] at hc
    exact htt' hc
  have hrel_tt' : ∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * t * n⁻¹ = t' :=
    exists_mem_normalClosure_conj_eq_of_isConj_of_not_commute ht2 h (IsConj.refl t) ht' htt'
  have hrel_yy' : ∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * y * n⁻¹ = y' :=
    exists_mem_normalClosure_conj_eq_of_isConj_of_not_commute ht2 h hy hy' hyy'
  have hsymm : ∀ ⦃u v : Q⦄, (∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * u * n⁻¹ = v) →
      ∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * v * n⁻¹ = u := by
    rintro u v ⟨n, hn, hn'⟩
    exact ⟨n⁻¹, (Subgroup.normalClosure ({t} : Set Q)).inv_mem hn, by rw [← hn']; group⟩
  have htrans : ∀ ⦃u v w : Q⦄,
      (∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * u * n⁻¹ = v) →
      (∃ m ∈ Subgroup.normalClosure ({t} : Set Q), m * v * m⁻¹ = w) →
      ∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * u * n⁻¹ = w := by
    rintro u v w ⟨n, hn, hn'⟩ ⟨m, hm, hm'⟩
    refine ⟨m * n, (Subgroup.normalClosure ({t} : Set Q)).mul_mem hm hn, ?_⟩
    rw [show (m * n) * u * (m * n)⁻¹ = m * (n * u * n⁻¹) * m⁻¹ by group, hn', hm']
  have hclaim : ∀ u v : Q, IsConj t u → IsConj t v →
      (¬ ∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * u * n⁻¹ = v) → u * v = v * u := by
    intro u v hu hv hnrel
    by_contra huv
    exact hnrel (exists_mem_normalClosure_conj_eq_of_isConj_of_not_commute ht2 h hu hv huv)
  have hnrel_t_y' : ¬ ∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * t * n⁻¹ = y' := by
    intro hrel
    exact hty (htrans hrel (hsymm hrel_yy'))
  have hnrel_t'_y : ¬ ∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * t' * n⁻¹ = y := by
    intro hrel
    exact hty (htrans hrel_tt' hrel)
  have hnrel_t'_y' : ¬ ∃ n ∈ Subgroup.normalClosure ({t} : Set Q), n * t' * n⁻¹ = y' := by
    intro hrel
    exact hnrel_t'_y (htrans hrel (hsymm hrel_yy'))
  have hty_comm : t * y = y * t := hclaim t y (IsConj.refl t) hy hty
  have hty'_comm : t * y' = y' * t := hclaim t y' (IsConj.refl t) hy' hnrel_t_y'
  have ht'y_comm : t' * y = y * t' := hclaim t' y ht' hy hnrel_t'_y
  have ht'y'_comm : t' * y' = y' * t' := hclaim t' y' ht' hy' hnrel_t'_y'
  have ht'2 : t' ^ 2 = 1 := sq_eq_one_of_isConj ht2 ht'
  have hy2 : y ^ 2 = 1 := sq_eq_one_of_isConj ht2 hy
  have hy'2 : y' ^ 2 = 1 := sq_eq_one_of_isConj ht2 hy'
  have htt'3 : (t * t') ^ 3 = 1 :=
    cube_eq_one_of_isConj_of_not_commute ht2 h (IsConj.refl t) ht' htt'
  have hyy'3 : (y * y') ^ 3 = 1 := cube_eq_one_of_isConj_of_not_commute ht2 h hy hy' hyy'
  exact hX (hasE9_of_commuting_pairs (d := t) (e := t') (b := y) (c := y')
    ht2 ht'2 hy2 hy'2 htt'3 hyy'3 htt' hyy' hty_comm hty'_comm ht'y_comm ht'y'_comm)

theorem pair_normalClosure_of_sq_or_cube (hX : ¬ HasE9 Q) {t : Q} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1)
    (h : ∀ a : Q, (t * (a * t * a⁻¹)) ^ 2 = 1 ∨ (t * (a * t * a⁻¹)) ^ 3 = 1)
    (hnc : ∃ a b : Q, IsConj t a ∧ IsConj t b ∧ a * b ≠ b * a) :
    Pair ↥(Subgroup.normalClosure ({t} : Set Q))
      {x : ↥(Subgroup.normalClosure ({t} : Set Q)) | IsConj t (x : Q)} := by
  classical
  let A : Subgroup Q := Subgroup.normalClosure ({t} : Set Q)
  let E : Set A := {x : A | IsConj t (x : Q)}
  change Pair A E
  unfold Pair
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · refine ⟨⟨t, Subgroup.subset_normalClosure rfl⟩, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn, hn'⟩ := exists_mem_normalClosure_conj_eq_of_not_hasE9 hX ht2 h hnc hx
      exact isConj_iff.mpr ⟨⟨n, hn⟩, Subtype.ext (by simpa using hn')⟩
    · intro hconj
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      refine isConj_iff.mpr ⟨(c : Q), ?_⟩
      show ((c * ⟨t, Subgroup.subset_normalClosure rfl⟩ * c⁻¹ : A) : Q) = (x : Q)
      exact congrArg Subtype.val hc
  · intro e he
    obtain ⟨g, hg⟩ := isConj_iff.mp he
    have htord : orderOf t = 2 := by
      haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
      exact orderOf_eq_prime ht2 ht1
    calc orderOf e = orderOf (e : Q) := (Subgroup.orderOf_coe e).symm
      _ = orderOf (g * t * g⁻¹) := by rw [hg]
      _ = orderOf t := by
            simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g) t
      _ = 2 := htord
  · intro e he f hf
    have hord : orderOf (e * f) = orderOf ((e : Q) * (f : Q)) :=
      (Subgroup.orderOf_coe (e * f)).symm
    rcases sq_or_cube_of_isConj h he hf with h2 | h3
    · have hdvd : orderOf ((e : Q) * (f : Q)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
      rw [← hord] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
      · simp [h1]
      · simp [h2']
    · have hdvd : orderOf ((e : Q) * (f : Q)) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
      rw [← hord] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
      · simp [h1]
      · simp [h3']
  · rw [eq_top_iff]
    intro x _
    have hmap : (Subgroup.closure E).map A.subtype = A := by
      apply le_antisymm
      · intro z hz
        obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
        rw [← hwz]
        exact w.2
      · change Subgroup.closure (Group.conjugatesOfSet ({t} : Set Q)) ≤
          (Subgroup.closure E).map A.subtype
        rw [Subgroup.closure_le]
        intro z hz
        obtain ⟨c, hc, hcz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
        rw [Set.mem_singleton_iff] at hc
        subst c
        obtain ⟨g, rfl⟩ := isConj_iff.mp hcz
        have hzA : g * t * g⁻¹ ∈ A :=
          Subgroup.conjugatesOfSet_subset_normalClosure
            (Group.mem_conjugatesOfSet_iff.mpr ⟨t, rfl, hcz⟩)
        have hzE : (⟨g * t * g⁻¹, hzA⟩ : A) ∈ E := hcz
        exact Subgroup.mem_map.mpr
          ⟨⟨g * t * g⁻¹, hzA⟩, Subgroup.subset_closure hzE, rfl⟩
    have hxmap : (x : Q) ∈ (Subgroup.closure E).map A.subtype := by
      rw [hmap]
      exact x.2
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hxmap
    rw [Subtype.ext hwx] at hw
    exact hw

end CFSG.GroupTheory.ThreeTranspositions
