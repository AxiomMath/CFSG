module

public import CFSG.ClassicalGroups.Unitary.SUnThreeLocalDefs
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ClassicalGroups.SUnThreeLocal

open Matrix CFSG.Open CFSG.LieType.Universal.Unitary

variable {L : Type} [Field L] {n : ℕ} {σ : L ≃+* L}

private theorem le_pRank_of_pi_zpowers {G : Type*} [Group G] [Finite G] {M : Type*}
    [CommGroup M] {p : ℕ} [Fact p.Prime] {t : M} (ht : orderOf t = p) {k : ℕ} {H : Subgroup G}
    (f : (Fin k → Subgroup.zpowers t) →* G) (hf : Function.Injective f) (hH : f.range ≤ H) :
    k ≤ pRank p H := by
  refine CFSG.SectionRank.le_pRank_of_injective (Fact.out : p.Prime).one_lt
    (fun a b => mul_comm a b) (fun a => ?_) ?_ f hf hH
  · funext i
    have h := pow_card_eq_one' (G := Subgroup.zpowers t) (x := a i)
    rwa [Nat.card_zpowers, ht] at h
  · rw [Nat.card_pi]
    simp [Nat.card_zpowers, ht]

private def conjInv (σ : L ≃+* L) : Lˣ →* Lˣ :=
  invMonoidHom.comp (Units.map (σ : L →* L))

private theorem coe_conjInv (y : Lˣ) : ((conjInv σ y : Lˣ) : L) = (σ (y : L))⁻¹ := by
  simp [conjInv]

private def normHom (σ : L ≃+* L) : (Fin 3 → Lˣ) →* Lˣ where
  toFun y := ∏ i, (y i * conjInv σ (y i))
  map_one' := by simp
  map_mul' y y' := by
    simp only [Pi.mul_apply, map_mul]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_mul_mul_comm _ _ _ _

private theorem normHom_eq (y : Fin 3 → Lˣ) :
    normHom σ y = (∏ i, y i) * conjInv σ (∏ i, y i) := by
  show ∏ i, (y i * conjInv σ (y i)) = _
  rw [Finset.prod_mul_distrib, map_prod]

private theorem σ_normHom (hσ : ∀ c, σ (σ c) = c) (y : Fin 3 → Lˣ) :
    σ ((normHom σ y : Lˣ) : L) * ((normHom σ y : Lˣ) : L) = 1 := by
  have h : ((normHom σ y : Lˣ) : L) = ∏ i, ((y i : L) * (σ (y i : L))⁻¹) := by
    simp [normHom, Units.coe_prod, coe_conjInv]
  rw [h, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  have h0 : (y i : L) ≠ 0 := Units.ne_zero _
  have h1 : σ (y i : L) ≠ 0 := by simpa using h0
  rw [map_mul, map_inv₀, hσ]
  field_simp

private def dvec (hn : n = 6 ∨ n = 7) (σ : L ≃+* L) (y : Fin 3 → Lˣ) (a : Fin n) : Lˣ :=
  if h : a.val < 3 then y ⟨a.val, h⟩
  else if h' : n ≤ a.val + 3 then conjInv σ (y ⟨n - 1 - a.val, by have := a.isLt; omega⟩)
  else (normHom σ y)⁻¹

private theorem dvec_mul (hn : n = 6 ∨ n = 7) (y y' : Fin 3 → Lˣ) (a : Fin n) :
    dvec hn σ (y * y') a = dvec hn σ y a * dvec hn σ y' a := by
  unfold dvec
  split_ifs
  · rfl
  · simp [map_mul]
  · rw [map_mul, mul_inv]

private theorem dvec_one (hn : n = 6 ∨ n = 7) (a : Fin n) : dvec hn σ 1 a = 1 := by
  unfold dvec
  split_ifs <;> simp

private def dvecHom (hn : n = 6 ∨ n = 7) (σ : L ≃+* L) : (Fin 3 → Lˣ) →* (Fin n → Lˣ) where
  toFun y := dvec hn σ y
  map_one' := funext (dvec_one hn)
  map_mul' y y' := funext (dvec_mul hn y y')

private theorem dvec_pos (hn : n = 6 ∨ n = 7) (y : Fin 3 → Lˣ) (i : Fin 3) :
    dvec hn σ y (pos hn i) = y i := by
  have h : (pos hn i).val < 3 := i.isLt
  simp [dvec, h, pos]

private theorem dvec_rev_pos (hn : n = 6 ∨ n = 7) (y : Fin 3 → Lˣ) (i : Fin 3) :
    dvec hn σ y (Fin.rev (pos hn i)) = conjInv σ (y i) := by
  have hi := i.isLt
  have h1 : ¬ (Fin.rev (pos hn i)).val < 3 := by
    simp only [pos, Fin.val_rev]
    omega
  have h2 : n ≤ (Fin.rev (pos hn i)).val + 3 := by
    simp only [pos, Fin.val_rev]
    omega
  rw [dvec, dif_neg h1, dif_pos h2]
  exact congrArg (fun k => conjInv σ (y k)) (Fin.ext (by simp only [pos, Fin.val_rev]; omega))

private theorem dvec_mid (hn : n = 6 ∨ n = 7) (y : Fin 3 → Lˣ) {a : Fin n} (h1 : 3 ≤ a.val)
    (h2 : a.val + 3 < n) : dvec hn σ y a = (normHom σ y)⁻¹ := by
  unfold dvec
  rw [dif_neg (by omega), dif_neg (by omega)]

private theorem dvec_unitary (hσ : ∀ c, σ (σ c) = c) (hn : n = 6 ∨ n = 7) (y : Fin 3 → Lˣ)
    (a : Fin n) : σ (dvec hn σ y a : L) * (dvec hn σ y (Fin.rev a) : L) = 1 := by
  rcases pos_cases hn a with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨h1, h2⟩
  · rw [dvec_pos, dvec_rev_pos, coe_conjInv]
    exact mul_inv_cancel₀ (by simpa using Units.ne_zero (y i))
  · rw [dvec_rev_pos, Fin.rev_rev, dvec_pos, coe_conjInv, map_inv₀, hσ]
    exact inv_mul_cancel₀ (Units.ne_zero (y i))
  · have h1' : 3 ≤ (Fin.rev a).val := by simp only [Fin.val_rev]; omega
    have h2' : (Fin.rev a).val + 3 < n := by simp only [Fin.val_rev]; omega
    rw [dvec_mid hn y h1 h2, dvec_mid hn y h1' h2', Units.val_inv_eq_inv_val, map_inv₀,
      ← mul_inv, σ_normHom hσ y, inv_one]

private theorem prod_dvec_seven (hn : n = 6 ∨ n = 7) (h7 : n = 7) (y : Fin 3 → Lˣ) :
    ∏ a, dvec hn σ y a = 1 := by
  subst h7
  have e0 : dvec hn σ y 0 = y 0 := dvec_pos hn y 0
  have e1 : dvec hn σ y 1 = y 1 := dvec_pos hn y 1
  have e2 : dvec hn σ y 2 = y 2 := dvec_pos hn y 2
  have e3 : dvec hn σ y 3 = (normHom σ y)⁻¹ := dvec_mid hn y (by decide) (by decide)
  have e4 : dvec hn σ y 4 = conjInv σ (y 2) := dvec_rev_pos hn y 2
  have e5 : dvec hn σ y 5 = conjInv σ (y 1) := dvec_rev_pos hn y 1
  have e6 : dvec hn σ y 6 = conjInv σ (y 0) := dvec_rev_pos hn y 0
  have hN : normHom σ y =
      y 0 * conjInv σ (y 0) * (y 1 * conjInv σ (y 1)) * (y 2 * conjInv σ (y 2)) := by
    simp [normHom, Fin.prod_univ_three]
  rw [Fin.prod_univ_seven, e0, e1, e2, e3, e4, e5, e6]
  calc y 0 * y 1 * y 2 * (normHom σ y)⁻¹ * conjInv σ (y 2) * conjInv σ (y 1) * conjInv σ (y 0)
      = normHom σ y * (normHom σ y)⁻¹ := by
        rw [hN]
        ac_rfl
    _ = 1 := mul_inv_cancel _

private theorem prod_dvec_six (hn : n = 6 ∨ n = 7) (h6 : n = 6) (y : Fin 3 → Lˣ) :
    ∏ a, dvec hn σ y a = normHom σ y := by
  subst h6
  have e0 : dvec hn σ y 0 = y 0 := dvec_pos hn y 0
  have e1 : dvec hn σ y 1 = y 1 := dvec_pos hn y 1
  have e2 : dvec hn σ y 2 = y 2 := dvec_pos hn y 2
  have e3 : dvec hn σ y 3 = conjInv σ (y 2) := dvec_rev_pos hn y 2
  have e4 : dvec hn σ y 4 = conjInv σ (y 1) := dvec_rev_pos hn y 1
  have e5 : dvec hn σ y 5 = conjInv σ (y 0) := dvec_rev_pos hn y 0
  have hN : normHom σ y =
      y 0 * conjInv σ (y 0) * (y 1 * conjInv σ (y 1)) * (y 2 * conjInv σ (y 2)) := by
    simp [normHom, Fin.prod_univ_three]
  rw [Fin.prod_univ_six, e0, e1, e2, e3, e4, e5, hN]
  ac_rfl

private theorem diagGL_dvec_mem (hσ : ∀ c, σ (σ c) = c) (hn : n = 6 ∨ n = 7)
    (y : Fin 3 → Lˣ) (hy : n = 7 ∨ normHom σ y = 1) : diagGL L n (dvec hn σ y) ∈ SU σ n := by
  refine diagGL_mem_SU _ (dvec_unitary hσ hn y) ?_
  rcases hy with h7 | hy
  · exact prod_dvec_seven hn h7 y
  · rcases hn with h6 | h7
    · rw [prod_dvec_six (Or.inl h6) h6, hy]
    · exact prod_dvec_seven (Or.inr h7) h7 y

private def torusSU (hσ : ∀ c, σ (σ c) = c) (hn : n = 6 ∨ n = 7) (h7 : n = 7) :
    (Fin 3 → Lˣ) →* SU σ n :=
  ((diagGL L n).comp (dvecHom hn σ)).codRestrict (SU σ n) fun y =>
    diagGL_dvec_mem hσ hn y (Or.inl h7)

private theorem torusSU_injective (hσ : ∀ c, σ (σ c) = c) (hn : n = 6 ∨ n = 7) (h7 : n = 7) :
    Function.Injective (torusSU hσ hn h7) := by
  intro y y' h
  have h1 := congrArg (fun g : SU σ n => (g : GL (Fin n) L)) h
  have h2 := diagGL_injective h1
  funext i
  have h3 := congrFun h2 (pos hn i)
  simpa [dvecHom, dvec_pos] using h3

private theorem commute_diagGL_c₀ (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) (d : Fin n → Lˣ)
    (hd : diagGL L n d ∈ SU σ n) (v : Multiplicative (Fin 3 → ZMod 3)) :
    Commute (⟨diagGL L n d, hd⟩ : SU σ n) (c₀ ζ hn v) := by
  show (⟨diagGL L n d, hd⟩ : SU σ n) * c₀ ζ hn v = c₀ ζ hn v * ⟨diagGL L n d, hd⟩
  apply Subtype.ext
  exact ((Commute.all d fun a => ζ.pow (wt n (Multiplicative.toAdd v) a)).map
    (diagGL L n)).eq

private def parHom (t : Lˣ) : (Fin 2 → Subgroup.zpowers t) →* (Fin 3 → Lˣ) where
  toFun a := ![((a 0 : Subgroup.zpowers t) : Lˣ), ((a 1 : Subgroup.zpowers t) : Lˣ),
    (((a 0 : Subgroup.zpowers t) : Lˣ) * ((a 1 : Subgroup.zpowers t) : Lˣ))⁻¹]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' a b := by
    funext i
    fin_cases i
    · simp
    · simp
    · simp [mul_inv, mul_mul_mul_comm]
      exact mul_comm _ _

private theorem parHom_injective (t : Lˣ) : Function.Injective (parHom t) := by
  intro a b h
  funext i
  apply Subtype.ext
  fin_cases i
  · simpa [parHom] using congrFun h 0
  · simpa [parHom] using congrFun h 1

private theorem normHom_parHom (σ : L ≃+* L) (t : Lˣ) (a : Fin 2 → Subgroup.zpowers t) :
    normHom σ (parHom t a) = 1 := by
  have h : ∏ i, (parHom t a) i = 1 := by
    simp [Fin.prod_univ_three, parHom]
  rw [normHom_eq, h, map_one, mul_one]

private def rankTwoHom (hσ : ∀ c, σ (σ c) = c) (hn : n = 6 ∨ n = 7) (t : Lˣ) :
    (Fin 2 → Subgroup.zpowers t) →* SU σ n :=
  ((diagGL L n).comp ((dvecHom hn σ).comp (parHom t))).codRestrict (SU σ n) fun a =>
    diagGL_dvec_mem hσ hn _ (Or.inr (normHom_parHom σ t a))

theorem two_le_pRank_centralizer_range_of_dvd_card_sub_one [Finite L] (hσ : ∀ c, σ (σ c) = c)
    (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card L - 1) :
    2 ≤ pRank p (Subgroup.centralizer ((c₀ ζ hn).range : Set (SU σ n))) := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Lˣ) p (by rwa [Nat.card_units])
  refine le_pRank_of_pi_zpowers ht (rankTwoHom hσ hn t) ?_ ?_
  · intro a b h
    have h1 := congrArg (fun g : SU σ n => (g : GL (Fin n) L)) h
    have h2 := diagGL_injective h1
    apply parHom_injective t
    funext i
    have h3 := congrFun h2 (pos hn i)
    simpa [dvecHom, dvec_pos] using h3
  · rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, rfl⟩
    exact (commute_diagGL_c₀ ζ hn _ _ v).symm.eq

theorem three_le_pRank_centralizer_range_of_dvd_card_sub_one [Finite L]
    (hσ : ∀ c, σ (σ c) = c) (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) (h7 : n = 7) {p : ℕ}
    [Fact p.Prime] (hp : p ∣ Nat.card L - 1) :
    3 ≤ pRank p (Subgroup.centralizer ((c₀ ζ hn).range : Set (SU σ n))) := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Lˣ) p (by rwa [Nat.card_units])
  refine le_pRank_of_pi_zpowers ht
    ((torusSU hσ hn h7).comp (MonoidHom.compLeft (Subgroup.zpowers t).subtype (Fin 3)))
    ((torusSU_injective hσ hn h7).comp fun a b h => funext fun i =>
      Subtype.ext (congrFun h i)) ?_
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨v, rfl⟩
  exact (commute_diagGL_c₀ ζ hn _ _ v).symm.eq

private theorem dvd_card_sub_one_of_dvd {q p : ℕ} {L : Type} [Field L] [Finite L]
    (hL : Nat.card L = q ^ 2) (hp : p ∣ q - 1 ∨ p ∣ q + 1) : p ∣ Nat.card L - 1 := by
  have hq : 1 ≤ q := by
    have h : 0 < Nat.card L := Nat.card_pos
    rw [hL] at h
    exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at h
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [hL, hsq]
  rcases hp with hp | hp
  · exact Dvd.dvd.mul_right hp _
  · exact Dvd.dvd.mul_left hp _

theorem two_le_pRank_centralizer_range_of_dvd_sub_one [Finite L] (hσ : ∀ c, σ (σ c) = c)
    (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) {q p : ℕ} [Fact p.Prime]
    (hL : Nat.card L = q ^ 2) (hp : p ∣ q - 1) :
    2 ≤ pRank p (Subgroup.centralizer ((c₀ ζ hn).range : Set (SU σ n))) :=
  two_le_pRank_centralizer_range_of_dvd_card_sub_one hσ ζ hn
    (dvd_card_sub_one_of_dvd hL (Or.inl hp))

theorem two_le_pRank_centralizer_range_of_dvd_add_one [Finite L] (hσ : ∀ c, σ (σ c) = c)
    (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) {q p : ℕ} [Fact p.Prime]
    (hL : Nat.card L = q ^ 2) (hp : p ∣ q + 1) :
    2 ≤ pRank p (Subgroup.centralizer ((c₀ ζ hn).range : Set (SU σ n))) :=
  two_le_pRank_centralizer_range_of_dvd_card_sub_one hσ ζ hn
    (dvd_card_sub_one_of_dvd hL (Or.inr hp))

theorem three_le_pRank_centralizer_range_of_dvd_add_one [Finite L] (hσ : ∀ c, σ (σ c) = c)
    (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) (h7 : n = 7) {q p : ℕ} [Fact p.Prime]
    (hL : Nat.card L = q ^ 2) (hp : p ∣ q + 1) :
    3 ≤ pRank p (Subgroup.centralizer ((c₀ ζ hn).range : Set (SU σ n))) :=
  three_le_pRank_centralizer_range_of_dvd_card_sub_one hσ ζ hn h7
    (dvd_card_sub_one_of_dvd hL (Or.inr hp))

end CFSG.ClassicalGroups.SUnThreeLocal
