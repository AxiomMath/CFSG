module

public import CFSG.RankThree.Transfer.FixedPoints
import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.ClassicalInvolution.Q8P.Asc77.Tr34

open MulAction Subgroup CFSG.RankThree.Transfer

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {A : Type} [CommGroup A]

noncomputable def cv (ϕ : H →* A) (g : G) (X : G ⧸ H) : A :=
  open Classical in
  if h : (Quotient.out X)⁻¹ * g * Quotient.out X ∈ H then ϕ ⟨_, h⟩ else 1

theorem cv_of_mem (ϕ : H →* A) {g : G} {X : G ⧸ H}
    (h : (Quotient.out X)⁻¹ * g * Quotient.out X ∈ H) : cv ϕ g X = ϕ ⟨_, h⟩ := by
  unfold cv
  simp only [h, ↓reduceDIte]

theorem cv_of_not_mem (ϕ : H →* A) {g : G} {X : G ⧸ H}
    (h : ¬ (Quotient.out X)⁻¹ * g * Quotient.out X ∈ H) : cv ϕ g X = 1 := by
  unfold cv
  rw [dif_neg h]

theorem cv_coe (ϕ : H →* A) {g x : G} (hx : x⁻¹ * g * x ∈ H) :
    cv ϕ g (x : G ⧸ H) = ϕ ⟨_, hx⟩ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H x
  have hmem : (Quotient.out (x : G ⧸ H))⁻¹ * g * Quotient.out (x : G ⧸ H) ∈ H := by
    rw [hh]
    have : (x * h)⁻¹ * g * (x * h) = (h : G)⁻¹ * (x⁻¹ * g * x) * h := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem h.2) hx) h.2
  unfold cv
  simp only [hmem, ↓reduceDIte]
  have : (⟨_, hmem⟩ : H) = h⁻¹ * ⟨_, hx⟩ * h := by
    apply Subtype.ext
    simp only [hh, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [this, map_mul, map_mul, mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one,
    one_mul]

theorem factor_eq_aux (ϕ : H →* A) (y : G) (hy4 : y ^ 4 = 1)
    (h1 : ∀ g : G, ∀ hg : g⁻¹ * y * g ∈ H, ϕ ⟨g⁻¹ * y * g, hg⟩ = 1) (X₀ : G ⧸ H) (m : ℕ)
    (hmdef : Function.minimalPeriod (fun x => y • x) X₀ = m)
    (hmem : (Quotient.out X₀)⁻¹ * y ^ m * Quotient.out X₀ ∈ H) :
    ϕ ⟨(Quotient.out X₀)⁻¹ * y ^ m * Quotient.out X₀, hmem⟩ = cv ϕ (y ^ 2) X₀ := by
  classical
  have hm : m ∣ 4 := by
    have := minimalPeriod_dvd_orderOf y X₀
    rw [hmdef] at this
    exact this.trans (orderOf_dvd_of_pow_eq_one hy4)
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp (show m ∣ 2 ^ 2 by simpa using hm) with
    ⟨k, hk, rfl⟩
  interval_cases k
  ·
    have hfix : Function.IsFixedPt (fun x => y • x) X₀ :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mp (by simpa using hmdef)
    have hy : (Quotient.out X₀)⁻¹ * y * Quotient.out X₀ ∈ H := smul_eq_self_iff_out.mp hfix
    have hy2 : (Quotient.out X₀)⁻¹ * y ^ 2 * Quotient.out X₀ ∈ H := by
      have : (Quotient.out X₀)⁻¹ * y ^ 2 * Quotient.out X₀ =
          ((Quotient.out X₀)⁻¹ * y * Quotient.out X₀) ^ 2 := by
        rw [pow_two, pow_two]; group
      rw [this]; exact H.pow_mem hy 2
    rw [cv_of_mem ϕ hy2]
    have e1 : ϕ ⟨(Quotient.out X₀)⁻¹ * y ^ 2 ^ 0 * Quotient.out X₀, hmem⟩ =
        ϕ ⟨(Quotient.out X₀)⁻¹ * y * Quotient.out X₀, hy⟩ := by simp
    rw [e1, h1 _ hy]
    have e2 : (⟨(Quotient.out X₀)⁻¹ * y ^ 2 * Quotient.out X₀, hy2⟩ : H) =
        ⟨(Quotient.out X₀)⁻¹ * y * Quotient.out X₀, hy⟩ ^ 2 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow]
      rw [pow_two, pow_two]; group
    rw [e2, map_pow, h1 _ hy, one_pow]
  ·
    have hy2 : (Quotient.out X₀)⁻¹ * y ^ 2 * Quotient.out X₀ ∈ H := by simpa using hmem
    rw [cv_of_mem ϕ hy2]
    simp
  ·
    have hn : ¬ ((Quotient.out X₀)⁻¹ * y ^ 2 * Quotient.out X₀ ∈ H) := by
      intro hy2
      have hfix2 : y ^ 2 • X₀ = X₀ := smul_eq_self_iff_out.mpr hy2
      have hper : Function.IsPeriodicPt (fun x => y • x) 2 X₀ := by
        show (fun x => y • x)^[2] X₀ = X₀
        rw [smul_iterate]; exact hfix2
      have := hper.minimalPeriod_dvd
      rw [hmdef] at this
      omega
    have hy4' : (Quotient.out X₀)⁻¹ * y ^ 2 ^ 2 * Quotient.out X₀ = 1 := by
      have : y ^ 2 ^ 2 = 1 := by simpa using hy4
      rw [this]; group
    have e : (⟨(Quotient.out X₀)⁻¹ * y ^ 2 ^ 2 * Quotient.out X₀, hmem⟩ : H) = 1 :=
      Subtype.ext hy4'
    rw [e, map_one]
    unfold cv
    rw [dif_neg hn]

theorem factor_eq (ϕ : H →* A) (y : G) (hy4 : y ^ 4 = 1)
    (h1 : ∀ g : G, ∀ hg : g⁻¹ * y * g ∈ H, ϕ ⟨g⁻¹ * y * g, hg⟩ = 1) (X₀ : G ⧸ H) :
    ϕ ⟨(Quotient.out X₀)⁻¹ * y ^ Function.minimalPeriod (fun x => y • x) X₀ * Quotient.out X₀,
        QuotientGroup.out_conj_pow_minimalPeriod_mem H y X₀⟩ = cv ϕ (y ^ 2) X₀ :=
  factor_eq_aux ϕ y hy4 h1 X₀ _ rfl _



theorem cv_coe_of_not (ϕ : H →* A) {g x : G} (hx : ¬ x⁻¹ * g * x ∈ H) :
    cv ϕ g (x : G ⧸ H) = 1 := by
  unfold cv
  have : ¬ (Quotient.out (x : G ⧸ H))⁻¹ * g * Quotient.out (x : G ⧸ H) ∈ H := by
    intro h
    exact hx (smul_coe_eq_iff.mp (smul_eq_self_iff_out.mpr h))
  rw [dif_neg this]

theorem cv_smul_of_commute (ϕ : H →* A) {c w : G} (hc : c * w = w * c) (X : G ⧸ H) :
    cv ϕ w (c • X) = cv ϕ w X := by
  induction X using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    have e : (c * g)⁻¹ * w * (c * g) = g⁻¹ * w * g := by
      have : c⁻¹ * w * c = w := by
        rw [mul_assoc, ← hc, inv_mul_cancel_left]
      calc (c * g)⁻¹ * w * (c * g) = g⁻¹ * (c⁻¹ * w * c) * g := by group
        _ = g⁻¹ * w * g := by rw [this]
    by_cases hg : g⁻¹ * w * g ∈ H
    · have hg' : (c * g)⁻¹ * w * (c * g) ∈ H := by rw [e]; exact hg
      rw [cv_coe ϕ hg', cv_coe ϕ hg]
      exact congrArg ϕ (Subtype.ext e)
    · have hg' : ¬ (c * g)⁻¹ * w * (c * g) ∈ H := by rw [e]; exact hg
      rw [cv_coe_of_not ϕ hg', cv_coe_of_not ϕ hg]



theorem cv_of_fixed (ϕ : H →* A) {y : G}
    (h1 : ∀ g : G, ∀ hg : g⁻¹ * y * g ∈ H, ϕ ⟨g⁻¹ * y * g, hg⟩ = 1) {X : G ⧸ H}
    (hX : y • X = X) : cv ϕ (y ^ 2) X = 1 := by
  have hy : (Quotient.out X)⁻¹ * y * Quotient.out X ∈ H := smul_eq_self_iff_out.mp hX
  have hy2 : (Quotient.out X)⁻¹ * y ^ 2 * Quotient.out X ∈ H := by
    have : (Quotient.out X)⁻¹ * y ^ 2 * Quotient.out X =
        ((Quotient.out X)⁻¹ * y * Quotient.out X) ^ 2 := by
      rw [pow_two, pow_two]; group
    rw [this]; exact H.pow_mem hy 2
  rw [cv_of_mem ϕ hy2]
  have e2 : (⟨(Quotient.out X)⁻¹ * y ^ 2 * Quotient.out X, hy2⟩ : H) =
      ⟨(Quotient.out X)⁻¹ * y * Quotient.out X, hy⟩ ^ 2 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow]
    rw [pow_two, pow_two]; group
  rw [e2, map_pow, h1 _ hy, one_pow]

theorem minimalPeriod_eq_two (ϕ : H →* A) {y : G} {ε : A} (hε1 : ε ≠ 1)
    (h1 : ∀ g : G, ∀ hg : g⁻¹ * y * g ∈ H, ϕ ⟨g⁻¹ * y * g, hg⟩ = 1) {X : G ⧸ H}
    (hX : cv ϕ (y ^ 2) X = ε) :
    Function.minimalPeriod (fun x => y • x) X = 2 := by
  have hfix2 : y ^ 2 • X = X := by
    by_contra h
    apply hε1
    rw [← hX]
    unfold cv
    rw [dif_neg (fun hh => h (smul_eq_self_iff_out.mpr hh))]
  have hdvd : Function.minimalPeriod (fun x => y • x) X ∣ 2 := by
    refine Function.IsPeriodicPt.minimalPeriod_dvd ?_
    show (fun x => y • x)^[2] X = X
    rw [smul_iterate]; exact hfix2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exfalso
    apply hε1
    rw [← hX]
    exact cv_of_fixed ϕ h1 (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h)
  · exact h



theorem cv_orbit (ϕ : H →* A) {y : G} {X Y : G ⧸ H}
    (hXY : Y ∈ orbit (zpowers y) X) :
    cv ϕ (y ^ 2) Y = cv ϕ (y ^ 2) X := by
  obtain ⟨⟨c, hc⟩, rfl⟩ := hXY
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hcomm : y ^ n * y ^ 2 = y ^ 2 * y ^ n := by
    have : Commute (y ^ n) (y ^ 2) := (Commute.refl y).zpow_left n |>.pow_right 2
    exact this.eq
  exact cv_smul_of_commute ϕ hcomm X



theorem card_eps (ϕ : H →* A) {y : G} {ε : A} (hε1 : ε ≠ 1)
    (h1 : ∀ g : G, ∀ hg : g⁻¹ * y * g ∈ H, ϕ ⟨g⁻¹ * y * g, hg⟩ = 1) :
    Nat.card {X : G ⧸ H // cv ϕ (y ^ 2) X = ε} =
      2 * Nat.card {q : Quotient (orbitRel (zpowers y) (G ⧸ H)) //
        cv ϕ (y ^ 2) q.out = ε} := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  haveI : Fintype (Quotient (orbitRel (zpowers y) (G ⧸ H))) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  have hmaps : Set.MapsTo
      (fun X : G ⧸ H => (Quotient.mk'' X : Quotient (orbitRel (zpowers y) (G ⧸ H))))
      ↑(Finset.univ.filter (fun X : G ⧸ H => cv ϕ (y ^ 2) X = ε))
      ↑(Finset.univ.filter (fun q : Quotient (orbitRel (zpowers y) (G ⧸ H)) =>
        cv ϕ (y ^ 2) q.out = ε)) := by
    intro X hX
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hX ⊢
    have hout : (Quotient.mk'' X : Quotient (orbitRel (zpowers y) (G ⧸ H))).out ∈
        orbit (zpowers y) X := by
      have := Quotient.mk_out (s := orbitRel (zpowers y) (G ⧸ H)) X
      exact MulAction.orbitRel_apply.mp this
    rw [cv_orbit ϕ hout, hX]
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_const_nat (m := 2), mul_comm]
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  have hper := minimalPeriod_eq_two ϕ hε1 h1 hq
  haveI : Fintype ↑(orbit (zpowers y) q.out) := Fintype.ofFinite _
  have hcard := MulAction.minimalPeriod_eq_card y q.out
  rw [hper] at hcard
  have hfib : ({a ∈ Finset.univ.filter (fun X : G ⧸ H => cv ϕ (y ^ 2) X = ε) |
      (Quotient.mk'' a : Quotient (orbitRel (zpowers y) (G ⧸ H))) = q} : Finset (G ⧸ H)) =
      (orbit (zpowers y) q.out).toFinset := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    constructor
    · rintro ⟨-, hX⟩
      have : (Quotient.mk'' X : Quotient (orbitRel (zpowers y) (G ⧸ H))) =
          Quotient.mk'' q.out := by rw [hX]; exact (Quotient.out_eq q).symm
      exact MulAction.orbitRel_apply.mp (Quotient.exact' this)
    · intro hX
      refine ⟨?_, ?_⟩
      · rw [cv_orbit ϕ hX, hq]
      · have : orbitRel (zpowers y) (G ⧸ H) X q.out := MulAction.orbitRel_apply.mpr hX
        have h2 : (Quotient.mk'' X : Quotient (orbitRel (zpowers y) (G ⧸ H))) =
            Quotient.mk'' q.out := Quotient.sound' this
        rw [h2]; exact Quotient.out_eq q
  rw [hfib, Set.toFinset_card]
  exact hcard.symm



theorem transfer_eq_one_of_four (ϕ : H →* A) (y : G) (ε : A) (hε2 : ε ^ 2 = 1) (hε1 : ε ≠ 1)
    (hy4 : y ^ 4 = 1)
    (h1 : ∀ g : G, ∀ hg : g⁻¹ * y * g ∈ H, ϕ ⟨g⁻¹ * y * g, hg⟩ = 1)
    (h2 : ∀ X : G ⧸ H, cv ϕ (y ^ 2) X = 1 ∨ cv ϕ (y ^ 2) X = ε)
    (h4 : 4 ∣ Nat.card {X : G ⧸ H // cv ϕ (y ^ 2) X = ε}) :
    ϕ.transfer y = 1 := by
  classical
  haveI : Fintype (Quotient (orbitRel (zpowers y) (G ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  have hcv : ∀ q : Quotient (orbitRel (zpowers y) (G ⧸ H)),
      ϕ ⟨(Quotient.out q.out)⁻¹ * y ^ Function.minimalPeriod (fun x => y • x) q.out *
        Quotient.out q.out, QuotientGroup.out_conj_pow_minimalPeriod_mem H y q.out⟩ =
      if cv ϕ (y ^ 2) q.out = ε then ε else 1 := by
    intro q
    rw [factor_eq ϕ y hy4 h1 q.out]
    rcases h2 q.out with h | h
    · rw [h, if_neg (fun h' => hε1 h'.symm)]
    · rw [h, if_pos rfl]
  rw [Finset.prod_congr rfl (fun q _ => hcv q), ← Finset.prod_filter, Finset.prod_const]
  have hc := card_eps ϕ hε1 h1
  rw [Nat.card_eq_fintype_card (α := {q : Quotient (orbitRel (zpowers y) (G ⧸ H)) //
    cv ϕ (y ^ 2) q.out = ε}), Fintype.card_subtype] at hc
  obtain ⟨k, hk⟩ := h4
  rw [hk] at hc
  have hev : (Finset.univ.filter (fun q : Quotient (orbitRel (zpowers y) (G ⧸ H)) =>
      cv ϕ (y ^ 2) q.out = ε)).card = 2 * k := by omega
  rw [hev, pow_mul, hε2, one_pow]


theorem four_dvd_card_of_orbits {S Y : Type*} [Group S] [Finite S] [MulAction S Y] [Finite Y]
    (hS : IsPGroup 2 S) (hno : ∀ y : Y, 2 < (orbit S y).ncard) : 4 ∣ Nat.card Y := by
  classical
  haveI : Fintype Y := Fintype.ofFinite Y
  haveI : Fintype (Quotient (orbitRel S Y)) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits S Y), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  obtain ⟨n, hn⟩ := hS.card_orbit (ω.out)
  have h2 := hno ω.out
  rw [← Nat.card_coe_set_eq, hn] at h2
  rw [hn]
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases n <;> omega
  exact (Nat.pow_dvd_pow 2 hn2 : 2 ^ 2 ∣ 2 ^ n)



theorem four_dvd_card_zEps (S : Subgroup G) (hS : IsPGroup 2 S) (ϕ : S →* A) (z w : G) (ε : A)
    (hε1 : ε ≠ 1) (hSz : ∀ s ∈ S, s * z = z * s) (hwS : w ∈ S)
    (hw2 : ∀ B : Subgroup S, B.index ≤ 2 → (⟨w, hwS⟩ : S) ∈ B)
    (hw : ∀ g : G, g⁻¹ * w * g ∈ S → ∀ hg : g⁻¹ * z * g ∈ S, ϕ ⟨g⁻¹ * z * g, hg⟩ ≠ ε) :
    4 ∣ Nat.card {X : G ⧸ S // cv ϕ z X = ε} := by
  classical
  let Zm : SubMulAction S (G ⧸ S) :=
    { carrier := {X | cv ϕ z X = ε}
      smul_mem' := fun c X hX => by
        have hc : (c : G) * z = z * (c : G) := hSz c c.2
        have := cv_smul_of_commute ϕ hc X
        show cv ϕ z ((c : G) • X) = ε
        rw [this]; exact hX }
  have hcard : Nat.card {X : G ⧸ S // cv ϕ z X = ε} = Nat.card Zm :=
    Nat.card_congr (Equiv.refl _)
  rw [hcard]
  haveI : Finite S := inferInstance
  refine four_dvd_card_of_orbits (S := S) (Y := Zm) hS ?_
  intro y
  by_contra hle
  push Not at hle
  have hidx : (MulAction.stabilizer S y).index ≤ 2 := by
    rw [MulAction.index_stabilizer]; exact hle
  have hmem := hw2 _ hidx
  have hfix : (⟨w, hwS⟩ : S) • y = y := MulAction.mem_stabilizer_iff.mp hmem
  obtain ⟨X, hX⟩ := y
  induction X using QuotientGroup.induction_on with
  | H g =>
    have hfix' : (w : G) • (g : G ⧸ S) = (g : G ⧸ S) := congrArg Subtype.val hfix
    have hwg : g⁻¹ * w * g ∈ S := smul_coe_eq_iff.mp hfix'
    have hX' : cv ϕ z (g : G ⧸ S) = ε := hX
    have hzg : g⁻¹ * z * g ∈ S := by
      by_contra hn
      apply hε1
      rw [← hX', cv_coe_of_not ϕ hn]
    rw [cv_coe ϕ hzg] at hX'
    exact hw g hwg hzg hX'


theorem commutator_mem_of_index_le_two {S : Type*} [Group S] [Finite S] (B : Subgroup S)
    (hB : B.index ≤ 2) (a b : S) : a * b * a⁻¹ * b⁻¹ ∈ B := by
  have h0 : B.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h12 : B.index = 1 ∨ B.index = 2 := by omega
  rcases h12 with h | h
  · rw [Subgroup.index_eq_one.mp h]; exact Subgroup.mem_top _
  · haveI : B.Normal := Subgroup.normal_of_index_eq_two h
    haveI : Fact (Nat.Prime (Nat.card (S ⧸ B))) := ⟨by rw [← Subgroup.index, h]; exact Nat.prime_two⟩
    haveI : IsCyclic (S ⧸ B) := isCyclic_of_prime_card (p := Nat.card (S ⧸ B)) rfl
    letI := IsCyclic.commGroup (α := S ⧸ B)
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm (a : S ⧸ B) b]
    group

end CFSG.ClassicalInvolution.Q8P.Asc77.Tr34
