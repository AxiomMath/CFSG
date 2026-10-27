module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.GL83PartI.I_24_3.InnerPGroup
import CFSG.Quasithin.Background.A1cRank
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Lift
import CFSG.LocalAnalysis.GLTheoremA.Lemma48

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open CFSG.Open

theorem le_normalizer_of_forall_conj_mem {X : Type} [Group X] {Z A E : Subgroup X}
    (hZA : Z ≤ A) (hEA : ∀ e ∈ E, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ Z) :
    E ≤ Subgroup.normalizer (Z : Set X) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    have hd := hEA e he c (hZA hc)
    have hcd : e * c * e⁻¹ = (e * c * e⁻¹ * c⁻¹) * c := by group
    rw [hcd]
    exact Z.mul_mem hd hc
  · intro hc
    have hd := hEA e⁻¹ (E.inv_mem he) (e * c * e⁻¹) (hZA hc)
    have hcz : e⁻¹ * (e * c * e⁻¹) * (e⁻¹)⁻¹ = c := by group
    rw [hcz] at hd
    have h1 : c = (c * (e * c * e⁻¹)⁻¹) * (e * c * e⁻¹) := by group
    rw [h1]
    exact Z.mul_mem hd hc

theorem exists_inv_conj_of_mem_of_inverting {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Type} [Group X] {Z A : Subgroup X} {z a : X} (hZA : Z ≤ A)
    (hA : IsElemAbelian p A) (hzZ : ∀ c ∈ Z, z * c = c * z)
    (hzA : ∀ x ∈ A, z * x * z⁻¹ * x ∈ Z) (ha : a ∈ A) :
    ∃ b ∈ A, a⁻¹ * b ∈ Z ∧ z * b * z⁻¹ = b⁻¹ := by
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  let c : X := z * a * z⁻¹ * a
  have hcZ : c ∈ Z := hzA a ha
  have hcA : c ∈ A := hZA hcZ
  have hcp : c ^ p = 1 := hA.2 c hcA
  have hza : z * a * z⁻¹ = c * a⁻¹ := by
    change z * a * z⁻¹ = (z * a * z⁻¹ * a) * a⁻¹
    group
  have hzcm : z * c ^ m * z⁻¹ = c ^ m := by
    rw [((commute_iff_eq z c).mpr (hzZ c hcZ)).pow_right m |>.eq, mul_assoc, mul_inv_cancel,
      mul_one]
  have hcinv : (c ^ m)⁻¹ = c ^ (m + 1) := by
    have h1 : c ^ (m + 1) * c ^ m = 1 := by
      rw [← pow_add, show m + 1 + m = 2 * m + 1 by omega, ← hm, hcp]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  have hinv_ac : (c ^ m)⁻¹ * a⁻¹ = a⁻¹ * (c ^ m)⁻¹ := by
    have h := ((commute_iff_eq a c).mpr (hA.comm ha hcA)).pow_right m |>.inv_left.inv_right
    exact h.symm.eq
  refine ⟨a * c ^ m, A.mul_mem ha (A.pow_mem hcA m), ?_, ?_⟩
  · show a⁻¹ * (a * c ^ m) ∈ Z
    rw [show a⁻¹ * (a * c ^ m) = c ^ m by group]
    exact Z.pow_mem hcZ m
  · have hbinv : (a * c ^ m)⁻¹ = a⁻¹ * c ^ (m + 1) := by
      rw [mul_inv_rev, hinv_ac, hcinv]
    rw [hbinv]
    calc z * (a * c ^ m) * z⁻¹ = (z * a * z⁻¹) * (z * c ^ m * z⁻¹) := by group
      _ = (c * a⁻¹) * c ^ m := by rw [hza, hzcm]
      _ = a⁻¹ * c ^ (m + 1) := by
        rw [show c * a⁻¹ = a⁻¹ * c from
          ((commute_iff_eq c a).mpr (hA.comm hcA ha)).inv_right.eq, mul_assoc, ← pow_succ']

theorem eq_of_inv_conj_of_mem_of_inverting {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Type} [Group X] {Z A : Subgroup X} {z b b' : X} (hZA : Z ≤ A)
    (hA : IsElemAbelian p A) (hzZ : ∀ c ∈ Z, z * c = c * z)
    (hb : b ∈ A) (hb' : b' ∈ A) (hbinv : z * b * z⁻¹ = b⁻¹)
    (hb'inv : z * b' * z⁻¹ = b'⁻¹) (hw : b⁻¹ * b' ∈ Z) : b = b' := by
  have hzw : z * (b⁻¹ * b') * z⁻¹ = b⁻¹ * b' := by
    rw [hzZ (b⁻¹ * b') hw, mul_assoc, mul_inv_cancel, mul_one]
  have hb1 : z * b⁻¹ * z⁻¹ = b := by
    calc z * b⁻¹ * z⁻¹ = (z * b * z⁻¹)⁻¹ := by group
      _ = (b⁻¹)⁻¹ := by rw [hbinv]
      _ = b := inv_inv b
  have hzw' : z * (b⁻¹ * b') * z⁻¹ = (b⁻¹ * b')⁻¹ := by
    calc z * (b⁻¹ * b') * z⁻¹ = (z * b⁻¹ * z⁻¹) * (z * b' * z⁻¹) := by group
      _ = b * b'⁻¹ := by rw [hb1, hb'inv]
      _ = b'⁻¹ * b := ((commute_iff_eq b b').mpr (hA.comm hb hb')).inv_right.eq
      _ = (b⁻¹ * b')⁻¹ := by rw [mul_inv_rev, inv_inv]
  have hww : (b⁻¹ * b') * (b⁻¹ * b') = 1 := by
    have h : b⁻¹ * b' = (b⁻¹ * b')⁻¹ := hzw.symm.trans hzw'
    nth_rewrite 1 [h]
    exact inv_mul_cancel _
  have hw1 : b⁻¹ * b' = 1 := by
    have hd2 : orderOf (b⁻¹ * b') ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hww
    have hdp : orderOf (b⁻¹ * b') ∣ p := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hA.2 (b⁻¹ * b') (hZA hw)
    have hcop : Nat.Coprime 2 p := by
      rw [Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)]
      exact fun h => hp2 h.symm
    have hgcd : Nat.gcd 2 p = 1 := hcop
    have hd1 : orderOf (b⁻¹ * b') ∣ 1 := hgcd ▸ Nat.dvd_gcd hd2 hdp
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)
  have hb_eq : b' = b := by
    calc b' = b * (b⁻¹ * b') := by group
      _ = b * 1 := by rw [hw1]
      _ = b := mul_one b
  exact hb_eq.symm

theorem le_centralizer_of_inverting {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Type} [Group X] [Finite X] {Z A E : Subgroup X} {z : X}
    (hZ : Nat.card Z = p) (hZA : Z ≤ A) (hA : IsElemAbelian p A)
    (hzZ : ∀ c ∈ Z, z * c = c * z) (hzA : ∀ a ∈ A, z * a * z⁻¹ * a ∈ Z)
    (hE : IsPGroup p E) (hEz : ∀ e ∈ E, e * z = z * e)
    (hEA : ∀ e ∈ E, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ Z) :
    E ≤ Subgroup.centralizer (A : Set X) := by
  have hEZ : E ≤ Subgroup.centralizer (Z : Set X) :=
    CFSG.LocalAnalysis.GLTheoremA.le_centralizer_of_isPGroup_of_card_eq (p := p) (Fact.out) hE hZ
      (le_normalizer_of_forall_conj_mem hZA hEA)
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨b, hbA, hainvb, hbinv⟩ := exists_inv_conj_of_mem_of_inverting hp2 hZA hA hzZ hzA ha
  have hc'Z : (a⁻¹ * b)⁻¹ ∈ Z := Z.inv_mem hainvb
  have haeq : a = b * (a⁻¹ * b)⁻¹ := by group
  have hebA : e * b * e⁻¹ ∈ A := by
    have hdA : e * b * e⁻¹ * b⁻¹ ∈ A := hZA (hEA e he b hbA)
    have hdb : e * b * e⁻¹ = (e * b * e⁻¹ * b⁻¹) * b := by group
    rw [hdb]
    exact A.mul_mem hdA hbA
  have hebinv : z * (e * b * e⁻¹) * z⁻¹ = (e * b * e⁻¹)⁻¹ := by
    have hez : z * e = e * z := (hEz e he).symm
    have hezi : z⁻¹ * e⁻¹ = e⁻¹ * z⁻¹ := by
      rw [← mul_inv_rev, ← hez, mul_inv_rev]
    calc z * (e * b * e⁻¹) * z⁻¹ = (z * e) * b * (e⁻¹ * z⁻¹) := by group
      _ = (e * z) * b * (z⁻¹ * e⁻¹) := by rw [hez, hezi]
      _ = e * (z * b * z⁻¹) * e⁻¹ := by group
      _ = e * b⁻¹ * e⁻¹ := by rw [hbinv]
      _ = (e * b * e⁻¹)⁻¹ := by group
  have hwbZ : b⁻¹ * (e * b * e⁻¹) ∈ Z := by
    set d : X := e * b * e⁻¹ * b⁻¹ with hddef
    have hdZ : d ∈ Z := hEA e he b hbA
    have hdA : d ∈ A := hZA hdZ
    have hdb : e * b * e⁻¹ = d * b := by rw [hddef]; group
    have hcomm : b * d = d * b := hA.comm hbA hdA
    have hcalc : b⁻¹ * (e * b * e⁻¹) = d := by
      rw [hdb, ← hcomm]
      group
    rw [hcalc]
    exact hdZ
  have heb : e * b * e⁻¹ = b :=
    (eq_of_inv_conj_of_mem_of_inverting hp2 hZA hA hzZ hbA hebA hbinv hebinv hwbZ).symm
  have hec : e * (a⁻¹ * b)⁻¹ * e⁻¹ = (a⁻¹ * b)⁻¹ := by
    have hcomm := Subgroup.mem_centralizer_iff.mp (hEZ he) (a⁻¹ * b)⁻¹ hc'Z
    rw [← hcomm]
    group
  have hconj : e * a * e⁻¹ = a := by
    calc e * a * e⁻¹ = e * (b * (a⁻¹ * b)⁻¹) * e⁻¹ := by rw [← haeq]
      _ = (e * b * e⁻¹) * (e * (a⁻¹ * b)⁻¹ * e⁻¹) := by group
      _ = b * (a⁻¹ * b)⁻¹ := by rw [heb, hec]
      _ = a := by rw [← haeq]
  calc a * e = (e * a * e⁻¹) * e := by rw [hconj]
    _ = e * a := by group

theorem inf_le_of_inverting {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Type} [Group X] {Z A E : Subgroup X} {z : X} (hZA : Z ≤ A)
    (hA : IsElemAbelian p A) (hzA : ∀ a ∈ A, z * a * z⁻¹ * a ∈ Z)
    (hEz : ∀ e ∈ E, e * z = z * e) : E ⊓ A ≤ Z := by
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  intro e he
  have heE : e ∈ E := he.1
  have heA : e ∈ A := he.2
  have hez : z * e * z⁻¹ = e := by
    rw [← hEz e heE]
    group
  have he2Z : e ^ 2 ∈ Z := by
    rw [pow_two]
    have h := hzA e heA
    rwa [hez] at h
  have hep : e ^ p = 1 := hA.2 e heA
  have heq : (e ^ 2) ^ (m + 1) = e := by
    rw [← pow_mul, show 2 * (m + 1) = p + 1 by omega, pow_succ, hep, one_mul]
  rw [← heq]
  exact Z.pow_mem he2Z (m + 1)

theorem four_le_pRank_of_inverting {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type} [Group X]
    [Finite X] {Z A E : Subgroup X} {z : X} (hZ : Nat.card Z = p) (hZA : Z ≤ A)
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 3)
    (hzZ : ∀ c ∈ Z, z * c = c * z) (hzA : ∀ a ∈ A, z * a * z⁻¹ * a ∈ Z)
    (hE : IsPGroup p E) (hEc : ¬ IsCyclic E) (hEz : ∀ e ∈ E, e * z = z * e)
    (hEA : ∀ e ∈ E, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ Z) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have hEA' : E ≤ Subgroup.centralizer (A : Set X) :=
    le_centralizer_of_inverting hp2 hZ hZA hA hzZ hzA hE hEz hEA
  obtain ⟨F, hFE, hF, hFcard⟩ :=
    GL83.I243.Inner.exists_isElemAbelian_card_sq_of_not_isCyclic hp2 hE hEc
  have hFZ : ¬ F ≤ Z := by
    intro h
    have hle : Nat.card F ≤ Nat.card Z := Subgroup.card_le_of_le h
    rw [hFcard, hZ] at hle
    have h21 : 2 ≤ 1 :=
      (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp (by simpa using hle)
    omega
  obtain ⟨e, heF, heZ⟩ : ∃ e ∈ F, e ∉ Z := by
    by_contra h
    push Not at h
    exact hFZ fun x hx => h x hx
  have hep : e ^ p = 1 := hF.2 e heF
  have he1 : e ≠ 1 := by
    rintro rfl
    exact heZ Z.one_mem
  have heA : e ∉ A := by
    intro heA'
    exact heZ (inf_le_of_inverting hp2 hZA hA hzA hEz ⟨hFE heF, heA'⟩)
  have hcomm : ∀ a ∈ A, Commute a e := by
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp (hEA' (hFE heF)) a ha
  have hord : orderOf e = p := orderOf_eq_prime hep he1
  obtain ⟨hAel, hAcard⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hA hord hcomm heA
  exact CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt le_top hAel
    (by rw [hAcard, hAc]; ring)

theorem map_comap_inf_centralizer_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type} {G : Type*}
    [Group X] [Finite X] [Group G] (ρ : X →* G) (hρ : IsPGroup p ρ.ker) {z : X} {a : ℕ}
    (hz : z ^ 2 ^ a = 1) {E : Subgroup G} (hEρ : E ≤ ρ.range)
    (hEz : ∀ e ∈ E, e * ρ z = ρ z * e) :
    (E.comap ρ ⊓ Subgroup.centralizer {z}).map ρ = E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · calc (E.comap ρ ⊓ Subgroup.centralizer {z}).map ρ
        ≤ (E.comap ρ).map ρ := Subgroup.map_mono inf_le_left
      _ = ρ.range ⊓ E := Subgroup.map_comap_eq ρ E
      _ = E := inf_eq_right.mpr hEρ
  · intro e he
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (hEρ he)
    have hker : y⁻¹ * (z * y * z⁻¹) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hy, ← hEz e he]
      group
    have h2 : ¬ 2 ∣ Nat.card ρ.ker := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hρ
      rw [hk]
      exact (Odd.pow (n := k) ((Fact.out : p.Prime).odd_of_ne_two hp2)).not_two_dvd_nat
    obtain ⟨n, hn, hcomm⟩ :=
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.exists_mul_comm_of_coprime
        (p := 2) (N := ρ.ker) h2 hz hker
    refine ⟨y * n, ⟨?_, ?_⟩, ?_⟩
    · change ρ (y * n) ∈ E
      rw [map_mul, MonoidHom.mem_ker.mp hn, mul_one, hy]
      exact he
    · change y * n ∈ Subgroup.centralizer {z}
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm.symm
    · rw [map_mul, MonoidHom.mem_ker.mp hn, mul_one]
      exact hy

theorem bar_one_of_additive {X W : Type*} [Group X] [AddCommGroup W] {D : Subgroup X}
    {bar : X → W} (hbar_mul : ∀ a ∈ D, ∀ b ∈ D, bar (a * b) = bar a + bar b) :
    bar 1 = 0 := by
  have h1 := hbar_mul 1 D.one_mem 1 D.one_mem
  rw [mul_one] at h1
  exact add_left_cancel (by rw [add_zero]; exact h1.symm)

theorem bar_inv_of_additive {X W : Type*} [Group X] [AddCommGroup W] {D : Subgroup X}
    {bar : X → W} (hbar_mul : ∀ a ∈ D, ∀ b ∈ D, bar (a * b) = bar a + bar b)
    {a : X} (ha : a ∈ D) : bar a⁻¹ = -bar a := by
  have h1 := hbar_mul a ha a⁻¹ (D.inv_mem ha)
  rw [mul_inv_cancel, bar_one_of_additive hbar_mul] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

theorem exists_two_pow_order_neg_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Type} [Group X] [Finite X] {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (B : LinearMap.BilinForm (ZMod p) W) (ρ : X →* (Module.End (ZMod p) W)ˣ)
    (hneg : -1 ∈ ρ.range) {Z : Subgroup X}
    (hiso : ∀ x : X, (∀ u v : W, B ((ρ x : Module.End (ZMod p) W) u)
      ((ρ x : Module.End (ZMod p) W) v) = B u v) → ∀ c ∈ Z, x * c = c * x) :
    ∃ z : X, ∃ a : ℕ, ρ z = -1 ∧ z ^ 2 ^ a = 1 ∧ ∀ c ∈ Z, z * c = c * z := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hneg
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hzρ : ρ (x ^ m) = -1 := by
    rw [map_pow, hx]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    exact Odd.neg_one_pow hm
  refine ⟨x ^ m, a, hzρ, ?_, ?_⟩
  · rw [← pow_mul, Nat.mul_comm m (2 ^ a), ← hord, pow_orderOf_eq_one]
  · have hisom : ∀ u v : W, B ((ρ (x ^ m) : Module.End (ZMod p) W) u)
        ((ρ (x ^ m) : Module.End (ZMod p) W) v) = B u v := by
      intro u v
      rw [hzρ]
      have hneg1 : (↑(-1 : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) = -1 := by
        rw [Units.val_neg, Units.val_one]
      rw [hneg1]
      change B (-u) (-v) = B u v
      rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg]
    exact hiso (x ^ m) hisom

theorem exists_sympPlane {p : ℕ} [Fact p.Prime] {X : Type} [Group X] {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W] {D Z : Subgroup X} (hZD : Z ≤ D)
    (hD : ∀ d ∈ D, d ^ p = 1) (bar : X → W)
    (hbar_mul : ∀ a ∈ D, ∀ b ∈ D, bar (a * b) = bar a + bar b)
    (hbar_ker : ∀ d ∈ D, bar d = 0 ↔ d ∈ Z)
    (B : LinearMap.BilinForm (ZMod p) W)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, B (bar a) (bar b) = 0 → a * b = b * a)
    {π : Submodule (ZMod p) W} (hπB : ∀ u ∈ π, ∀ v ∈ π, B u v = 0) :
    ∃ A : Subgroup X, Z ≤ A ∧ A ≤ D ∧ (∀ x ∈ A, bar x ∈ π) ∧
      (∀ d, d ∈ A ↔ d ∈ D ∧ bar d ∈ π) ∧ CFSG.Open.IsElemAbelian p A := by
  have hbar_one : bar 1 = 0 := bar_one_of_additive hbar_mul
  have hbar_inv : ∀ d ∈ D, bar d⁻¹ = - bar d := fun d hd => bar_inv_of_additive hbar_mul hd
  let A : Subgroup X :=
    { carrier := {d | d ∈ D ∧ bar d ∈ π}
      one_mem' := ⟨D.one_mem, by rw [hbar_one]; exact π.zero_mem⟩
      mul_mem' := by
        intro a b ha hb
        exact ⟨D.mul_mem ha.1 hb.1, by
          rw [hbar_mul a ha.1 b hb.1]; exact π.add_mem ha.2 hb.2⟩
      inv_mem' := by
        intro a ha
        exact ⟨D.inv_mem ha.1, by
          rw [hbar_inv a ha.1]; exact π.neg_mem ha.2⟩ }
  have hZA : Z ≤ A := by
    intro c hc
    exact ⟨hZD hc, by rw [(hbar_ker c (hZD hc)).mpr hc]; exact π.zero_mem⟩
  have hAcomm : IsMulCommutative A :=
    ⟨{ comm := fun a b => Subtype.ext
        (hcomm a.1 a.2.1 b.1 b.2.1 (hπB (bar a.1) a.2.2 (bar b.1) b.2.2)) }⟩
  have hA : IsElemAbelian p A := ⟨hAcomm, fun x hx => hD x hx.1⟩
  exact ⟨A, hZA, fun x hx => hx.1, fun x hx => hx.2, fun _ => Iff.rfl, hA⟩

theorem exists_barA_sympPlane {p : ℕ} [Fact p.Prime] {X : Type} [Group X] {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W] {D Z : Subgroup X} (hZD : Z ≤ D) (bar : X → W)
    (hbar_mul : ∀ a ∈ D, ∀ b ∈ D, bar (a * b) = bar a + bar b)
    (hbar_ker : ∀ d ∈ D, bar d = 0 ↔ d ∈ Z)
    (hbar_surj : ∀ w : W, ∃ d ∈ D, bar d = w)
    {π : Submodule (ZMod p) W} {A : Subgroup X} (hchar : ∀ d, d ∈ A ↔ d ∈ D ∧ bar d ∈ π) :
    ∃ barA : A →* Multiplicative π, barA.ker = Z.subgroupOf A ∧ barA.range = ⊤ := by
  have hbar_one : bar 1 = 0 := bar_one_of_additive hbar_mul
  have hdom : ∀ a : A, a.1 ∈ D := fun a => ((hchar a.1).mp a.2).1
  have hmem : ∀ a : A, bar a.1 ∈ π := fun a => ((hchar a.1).mp a.2).2
  let barA : A →* Multiplicative π :=
    { toFun := fun a => Multiplicative.ofAdd (⟨bar a.1, hmem a⟩ : π)
      map_one' := by
        have h : (⟨bar (1 : A).1, hmem 1⟩ : π) = 0 :=
          Subtype.ext (by show bar 1 = 0; exact hbar_one)
        exact congrArg Multiplicative.ofAdd h
      map_mul' := by
        intro a b
        have h : (⟨bar (a * b).1, hmem (a * b)⟩ : π) =
            (⟨bar a.1, hmem a⟩ : π) + ⟨bar b.1, hmem b⟩ :=
          Subtype.ext (by
            show bar (a.1 * b.1) = bar a.1 + bar b.1
            exact hbar_mul a.1 (hdom a) b.1 (hdom b))
        exact congrArg Multiplicative.ofAdd h }
  refine ⟨barA, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : (⟨bar x.1, hmem x⟩ : π) = 0 := Multiplicative.ofAdd.injective h
      exact (hbar_ker x.1 (hdom x)).mp (congrArg Subtype.val h')
    · intro h
      change Multiplicative.ofAdd (⟨bar x.1, hmem x⟩ : π) = 1
      have h0 : (⟨bar x.1, hmem x⟩ : π) = 0 := Subtype.ext ((hbar_ker x.1 (hdom x)).mpr h)
      rw [h0]
      rfl
  · rw [MonoidHom.range_eq_top]
    intro w
    obtain ⟨w0, hw0⟩ := Multiplicative.ofAdd.surjective w
    obtain ⟨d, hdD, hdbar⟩ := hbar_surj w0.1
    have hdA : d ∈ A := (hchar d).mpr ⟨hdD, by rw [hdbar]; exact w0.2⟩
    refine ⟨⟨d, hdA⟩, ?_⟩
    rw [← hw0]
    exact congrArg Multiplicative.ofAdd (Subtype.ext hdbar)

theorem card_sympPlane {p : ℕ} [Fact p.Prime] {X : Type} [Group X] {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W] {D Z : Subgroup X}
    (hZD : Z ≤ D) (hZ : Nat.card Z = p) (bar : X → W)
    (hbar_mul : ∀ a ∈ D, ∀ b ∈ D, bar (a * b) = bar a + bar b)
    (hbar_ker : ∀ d ∈ D, bar d = 0 ↔ d ∈ Z)
    (hbar_surj : ∀ w : W, ∃ d ∈ D, bar d = w)
    {π : Submodule (ZMod p) W} (hπ : Module.finrank (ZMod p) π = 2)
    {A : Subgroup X} (hchar : ∀ d, d ∈ A ↔ d ∈ D ∧ bar d ∈ π) :
    Nat.card A = p ^ 3 := by
  obtain ⟨barA, hker, hrange⟩ :=
    exists_barA_sympPlane hZD bar hbar_mul hbar_ker hbar_surj hchar
  have hZA : Z ≤ A := by
    intro c hc
    rw [hchar c]
    exact ⟨hZD hc, by rw [(hbar_ker c (hZD hc)).mpr hc]; exact π.zero_mem⟩
  have hcardZ : Nat.card (Z.subgroupOf A) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv, hZ]
  have hcardπ : Nat.card π = p ^ 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := π)
    rwa [Nat.card_zmod, hπ] at h
  have h := Subgroup.card_ker_mul_card_range barA
  rw [hker, hrange, Subgroup.card_top] at h
  have hmult : Nat.card (Multiplicative π) = p ^ 2 := by
    rw [show Nat.card (Multiplicative π) = Nat.card π from rfl, hcardπ]
  rw [hcardZ, hmult] at h
  rw [← h]
  ring

theorem exists_elemAbelian_card_of_sympModel {p : ℕ} [Fact p.Prime]
    {X : Type} [Group X] {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    [Module.Finite (ZMod p) W] {D Z : Subgroup X} (hZD : Z ≤ D)
    (hZ : Nat.card Z = p) (hD : ∀ d ∈ D, d ^ p = 1) (bar : X → W)
    (hbar_mul : ∀ a ∈ D, ∀ b ∈ D, bar (a * b) = bar a + bar b)
    (hbar_ker : ∀ d ∈ D, bar d = 0 ↔ d ∈ Z)
    (hbar_surj : ∀ w : W, ∃ d ∈ D, bar d = w)
    (B : LinearMap.BilinForm (ZMod p) W)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, B (bar a) (bar b) = 0 → a * b = b * a)
    {π : Submodule (ZMod p) W} (hπ : Module.finrank (ZMod p) π = 2)
    (hπB : ∀ u ∈ π, ∀ v ∈ π, B u v = 0) :
    ∃ A : Subgroup X, Z ≤ A ∧ A ≤ D ∧ (∀ x ∈ A, bar x ∈ π) ∧
      CFSG.Open.IsElemAbelian p A ∧ Nat.card A = p ^ 3 := by
  obtain ⟨A, hZA, hAD, hAbar, hchar, hA⟩ :=
    exists_sympPlane hZD hD bar hbar_mul hbar_ker B hcomm hπB
  exact ⟨A, hZA, hAD, hAbar, hA, card_sympPlane hZD hZ bar hbar_mul hbar_ker hbar_surj hπ hchar⟩

theorem exists_isPGroup_not_isCyclic_comap_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Type} {G : Type*} [Group X] [Finite X] [Group G] (ρ : X →* G) (hρ : IsPGroup p ρ.ker)
    {z : X} {a : ℕ} (hz : z ^ 2 ^ a = 1) {E : Subgroup G} (hEρ : E ≤ ρ.range)
    (hEz : ∀ e ∈ E, e * ρ z = ρ z * e) (hEel : CFSG.Open.IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) :
    ∃ E₁ : Subgroup X, IsPGroup p E₁ ∧ ¬ IsCyclic E₁ ∧
      E₁ ≤ Subgroup.centralizer {z} ∧ E₁.map ρ = E := by
  haveI : Finite E :=
    (Nat.card_pos_iff.mp (by rw [hEc]; exact pow_pos (Fact.out : p.Prime).pos 2)).2
  haveI : CFSG.IsElementaryAbelian p E := hEel.isElementaryAbelian
  have hEncyc : ¬ IsCyclic E := CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEc
  refine ⟨E.comap ρ ⊓ Subgroup.centralizer {z}, ?_, ?_, inf_le_right, ?_⟩
  · exact (IsPGroup.comap_of_ker_isPGroup hEel.isPGroup ρ hρ).to_le inf_le_left
  · intro hcyc
    have hmap := map_comap_inf_centralizer_eq hp2 ρ hρ hz hEρ hEz
    have hcyc' : IsCyclic ↥((E.comap ρ ⊓ Subgroup.centralizer {z}).map ρ) := by
      letI : IsCyclic ↥(E.comap ρ ⊓ Subgroup.centralizer {z}) := hcyc
      let f : ↥(E.comap ρ ⊓ Subgroup.centralizer {z}) →*
          ↥((E.comap ρ ⊓ Subgroup.centralizer {z}).map ρ) :=
        (ρ.comp (E.comap ρ ⊓ Subgroup.centralizer {z}).subtype).codRestrict _
          (fun x => Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩)
      exact isCyclic_of_surjective f (by
        intro y
        obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp y.2
        exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩)
    rw [hmap] at hcyc'
    exact hEncyc hcyc'
  · exact map_comap_inf_centralizer_eq hp2 ρ hρ hz hEρ hEz

theorem four_le_pRank_of_sympModel {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type} [Group X]
    [Finite X] {W : Type*} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (B : LinearMap.BilinForm (ZMod p) W) (ρ : X →* (Module.End (ZMod p) W)ˣ)
    (hρ : IsPGroup p ρ.ker) {D Z : Subgroup X} [D.Normal] (hZD : Z ≤ D) (hZ : Nat.card Z = p)
    (hD : ∀ d ∈ D, d ^ p = 1) (bar : X → W)
    (hbar_mul : ∀ a ∈ D, ∀ b ∈ D, bar (a * b) = bar a + bar b)
    (hbar_ker : ∀ d ∈ D, bar d = 0 ↔ d ∈ Z) (hbar_surj : ∀ w : W, ∃ d ∈ D, bar d = w)
    (hbar_conj : ∀ x : X, ∀ d ∈ D, bar (x * d * x⁻¹) = (ρ x : Module.End (ZMod p) W) (bar d))
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, B (bar a) (bar b) = 0 → a * b = b * a)
    (hiso : ∀ x : X, (∀ u v : W, B ((ρ x : Module.End (ZMod p) W) u)
      ((ρ x : Module.End (ZMod p) W) v) = B u v) → ∀ c ∈ Z, x * c = c * x)
    (hneg : -1 ∈ ρ.range) {E : Subgroup (Module.End (ZMod p) W)ˣ} (hEρ : E ≤ ρ.range)
    (hE : CFSG.Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    {π : Submodule (ZMod p) W} (hπ : Module.finrank (ZMod p) π = 2)
    (hπB : ∀ u ∈ π, ∀ v ∈ π, B u v = 0)
    (hEπ : ∀ e ∈ E, ∀ u ∈ π, (e : Module.End (ZMod p) W) u = u) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨z, a, hzρ, hz2, hzZ⟩ :=
    exists_two_pow_order_neg_one hp2 B ρ hneg hiso
  obtain ⟨A, hZA, hAD, hAbar, hA, hAc⟩ :=
    exists_elemAbelian_card_of_sympModel hZD hZ hD bar hbar_mul hbar_ker hbar_surj B hcomm hπ hπB
  have hzA : ∀ x ∈ A, z * x * z⁻¹ * x ∈ Z := by
    intro x hx
    have hxD : x ∈ D := hAD hx
    have hconjD : z * x * z⁻¹ ∈ D := (inferInstance : D.Normal).conj_mem x hxD z
    rw [← hbar_ker (z * x * z⁻¹ * x) (D.mul_mem hconjD hxD)]
    rw [hbar_mul (z * x * z⁻¹) hconjD x hxD]
    rw [hbar_conj z x hxD]
    have hnegz : (ρ z : Module.End (ZMod p) W) (bar x) = - bar x := by
      rw [hzρ]
      have hneg1 : (↑(-1 : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) = -1 := by
        rw [Units.val_neg, Units.val_one]
      rw [hneg1]
      simpa using LinearMap.neg_apply (1 : Module.End (ZMod p) W) (bar x)
    rw [hnegz]
    abel
  have hEz : ∀ e ∈ E, e * ρ z = ρ z * e := by
    intro e he
    rw [hzρ, mul_neg_one, neg_one_mul]
  obtain ⟨E₁, hE₁p, hE₁ncyc, hE₁z, hE₁map⟩ :=
    exists_isPGroup_not_isCyclic_comap_centralizer hp2 ρ hρ hz2 hEρ hEz hE hEc
  have hE₁A : ∀ e ∈ E₁, ∀ x ∈ A, e * x * e⁻¹ * x⁻¹ ∈ Z := by
    intro e he x hx
    have hxD : x ∈ D := hAD hx
    have hexD : e * x * e⁻¹ ∈ D := (inferInstance : D.Normal).conj_mem x hxD e
    have hρe : ρ e ∈ E := by
      rw [← hE₁map]
      exact Subgroup.mem_map.mpr ⟨e, he, rfl⟩
    rw [← hbar_ker (e * x * e⁻¹ * x⁻¹) (D.mul_mem hexD (D.inv_mem hxD))]
    rw [hbar_mul (e * x * e⁻¹) hexD x⁻¹ (D.inv_mem hxD)]
    rw [hbar_conj e x hxD]
    rw [bar_inv_of_additive hbar_mul hxD]
    have hfix : (ρ e : Module.End (ZMod p) W) (bar x) = bar x :=
      hEπ (ρ e) hρe (bar x) (hAbar x hx)
    rw [hfix]
    abel
  have hE₁z' : ∀ e ∈ E₁, e * z = z * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hE₁z he)
  exact four_le_pRank_of_inverting hp2 hZ hZA hA hAc hzZ hzA hE₁p hE₁ncyc hE₁z' hE₁A

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
