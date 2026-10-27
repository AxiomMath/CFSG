module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Local.NormalSubgroupCentralPrimeTorsion
import CFSG.FeitThompson.Foundations.CentralExtensionNilpotent
import CFSG.FeitThompson.Foundations.HallLiftThroughNormalPi

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p a d n : ℕ} {P : Type*} [Group P]

def torsionBy {G : Type*} [Group G] (H : Subgroup G) [IsMulCommutative H] (n : ℕ) : Subgroup G where
  carrier := {x | x ∈ H ∧ x ^ n = 1}
  one_mem' := ⟨one_mem H, one_pow n⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    rw [Commute.mul_pow (setLike_mul_comm ha.1 hb.1), ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

@[simp]
theorem mem_torsionBy {H : Subgroup P} [IsMulCommutative H] {x : P} :
    x ∈ torsionBy H n ↔ x ∈ H ∧ x ^ n = 1 := (Iff.rfl)

theorem torsionBy_le (H : Subgroup P) [IsMulCommutative H] (n : ℕ) : torsionBy H n ≤ H :=
  fun _ hx => (mem_torsionBy.mp hx).1

theorem pow_eq_one_of_mem_torsionBy {H : Subgroup P} [IsMulCommutative H] {x : P}
    (hx : x ∈ torsionBy H n) : x ^ n = 1 := (mem_torsionBy.mp hx).2

theorem isMulCommutative_of_le {A B : Subgroup P} [IsMulCommutative A] (h : B ≤ A) :
    IsMulCommutative B :=
  ⟨⟨fun x y => Subtype.ext (setLike_mul_comm (h x.2) (h y.2))⟩⟩

instance isMulCommutative_torsionBy (H : Subgroup P) [IsMulCommutative H] (n : ℕ) :
    IsMulCommutative (torsionBy H n) := isMulCommutative_of_le (torsionBy_le H n)

instance torsionBy_normal (H : Subgroup P) [IsMulCommutative H] [H.Normal] (n : ℕ) :
    (torsionBy H n).Normal where
  conj_mem x hx g := by
    refine mem_torsionBy.mpr ⟨‹H.Normal›.conj_mem x (mem_torsionBy.mp hx).1 g, ?_⟩
    rw [conj_pow, (mem_torsionBy.mp hx).2, mul_one, mul_inv_cancel]

theorem torsionBy_mono {H K : Subgroup P} [IsMulCommutative H] [IsMulCommutative K] (h : H ≤ K)
    (n : ℕ) : torsionBy H n ≤ torsionBy K n :=
  fun _ hx => mem_torsionBy.mpr ⟨h (mem_torsionBy.mp hx).1, (mem_torsionBy.mp hx).2⟩

theorem le_torsionBy {H K : Subgroup P} [IsMulCommutative H] (hHK : K ≤ H)
    (hexp : ∀ x ∈ K, x ^ n = 1) : K ≤ torsionBy H n :=
  fun _ hx => mem_torsionBy.mpr ⟨hHK hx, hexp _ hx⟩

theorem natCard_of_mulEquiv_pi {E : Subgroup P}
    (e : ↥E ≃* (Fin d → Multiplicative (ZMod p))) : Nat.card E = p ^ d := by
  rw [Nat.card_congr e.toEquiv, card_pi_multiplicative_zmod]

theorem pow_eq_one_of_mulEquiv_pi {E : Subgroup P}
    (e : ↥E ≃* (Fin d → Multiplicative (ZMod p))) {x : P} (hx : x ∈ E) : x ^ p = 1 := by
  have h : (⟨x, hx⟩ : ↥E) ^ p = 1 :=
    e.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
  exact congrArg E.subtype h

theorem nonempty_mulEquiv_pi_of_le_of_card {A B : Subgroup P} [IsMulCommutative A] (hp : p.Prime)
    (hBA : B ≤ A) (hexp : ∀ x ∈ B, x ^ p = 1) (hcard : Nat.card B = p ^ d) :
    Nonempty (↥B ≃* (Fin d → Multiplicative (ZMod p))) := by
  have := isMulCommutative_of_le hBA
  let _ : CommGroup ↥B := IsMulCommutative.instCommGroup
  exact nonempty_mulEquiv_pi_of_exponent hp (fun x => Subtype.ext (hexp x.1 x.2)) hcard

theorem exists_controlled_normal_plane (hp : p.Prime) (hP : Nat.card P = p ^ a) (A : Subgroup P)
    [A.Normal] [IsMulCommutative A] (hself : centralizer (A : Set P) = A)
    (hA : 2 ∈ elementaryAbelianRanks p ↥A) :
    ∃ B : Subgroup P, B ≤ A ∧ B.Normal ∧
      Nonempty (↥B ≃* (Fin 2 → Multiplicative (ZMod p))) ∧
      (B ≤ torsionBy (center P) p ∨
        (Nat.card (torsionBy (center P) p) = p ∧ torsionBy (center P) p ≤ B)) := by
  have hfp : Fact p.Prime := ⟨hp⟩
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  have hcenterA : center P ≤ A := hself ▸ center_le_centralizer (A : Set P)
  have hZD : torsionBy (center P) p ≤ torsionBy A p := torsionBy_mono hcenterA p
  have hDA : torsionBy A p ≤ A := torsionBy_le A p
  have hDexp : ∀ x ∈ torsionBy A p, x ^ p = 1 := fun _ hx => (mem_torsionBy.mp hx).2
  obtain ⟨E, ⟨e⟩⟩ := mem_elementaryAbelianRanks.mp hA
  have hED : map A.subtype E ≤ torsionBy A p := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact mem_torsionBy.mpr ⟨y.2, congrArg A.subtype (pow_eq_one_of_mulEquiv_pi e hy)⟩
  have hsqD : p ^ 2 ∣ Nat.card (torsionBy A p) := by
    refine dvd_trans ?_ (card_dvd_of_le hED)
    rw [card_map_of_injective A.subtype_injective, natCard_of_mulEquiv_pi e]
  have hsqle : p ^ 2 ≤ Nat.card (torsionBy A p) := Nat.le_of_dvd Nat.card_pos hsqD
  have hZne : torsionBy (center P) p ≠ ⊥ := by
    have hnt : (⊤ : Subgroup P) ≠ ⊥ := by
      intro h
      have hD : torsionBy A p = ⊥ := le_bot_iff.mp (h ▸ (le_top : torsionBy A p ≤ ⊤))
      rw [hD, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩] at hsqle
      nlinarith [hp.two_le]
    obtain ⟨Q, hQle, hQcard⟩ := exists_le_inf_center_natCard_eq (⊤ : Subgroup P) hp hP hnt
    have hQZ : Q ≤ torsionBy (center P) p := by
      intro x hx
      refine mem_torsionBy.mpr ⟨(mem_inf.mp (hQle hx)).2, ?_⟩
      have hx1 : (⟨x, hx⟩ : ↥Q) ^ Nat.card Q = 1 := pow_card_eq_one'
      rw [hQcard] at hx1
      exact congrArg Q.subtype hx1
    intro h
    rw [h, le_bot_iff] at hQZ
    rw [hQZ, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩] at hQcard
    exact hp.one_lt.ne hQcard
  obtain ⟨k, hk⟩ := ((IsPGroup.of_card hP).to_subgroup (torsionBy (center P) p)).exists_card_eq
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hk, h, pow_zero])) hZne
    · exact h
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  ·
    have hZcard : Nat.card (torsionBy (center P) p) = p := by
      have hk' : k = 1 := by omega
      rw [hk, hk', pow_one]
    set Z := torsionBy (center P) p with hZdef
    set f := QuotientGroup.mk' Z with hfdef
    have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective Z
    have hker : f.ker = Z := QuotientGroup.ker_mk' Z
    have hDbarne : map f (torsionBy A p) ≠ ⊥ := by
      intro h
      rw [Subgroup.map_eq_bot_iff, hker] at h
      have hle : Nat.card (torsionBy A p) ≤ Nat.card Z :=
        Nat.le_of_dvd Nat.card_pos (card_dvd_of_le h)
      rw [hZcard] at hle
      nlinarith [hp.two_le]
    have hquotcard : Nat.card (P ⧸ Z) = p ^ (a - 1) := by
      have h1 : Nat.card P = Nat.card (P ⧸ Z) * Nat.card Z :=
        card_eq_card_quotient_mul_card_subgroup Z
      have ha1 : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · rw [h, pow_zero] at hP
          have hZle : Nat.card Z ≤ 1 := hP ▸ Nat.le_of_dvd Nat.card_pos Z.card_subgroup_dvd_card
          rw [hZcard] at hZle
          exact absurd hZle (by simpa using hp.one_lt)
        · exact h
      rw [hZcard, hP] at h1
      have hpow : p ^ a = p ^ (a - 1) * p := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow] at h1
      exact (Nat.eq_of_mul_eq_mul_right hp.pos h1).symm
    obtain ⟨Qbar, hQle, hQcard⟩ := exists_le_inf_center_natCard_eq (map f (torsionBy A p))
      hp hquotcard hDbarne
    have hQcen : Qbar ≤ center (P ⧸ Z) := fun _ hx => (mem_inf.mp (hQle hx)).2
    have hQD : Qbar ≤ map f (torsionBy A p) := fun _ hx => (mem_inf.mp (hQle hx)).1
    have hBD : comap f Qbar ≤ torsionBy A p :=
      calc comap f Qbar ≤ comap f (map f (torsionBy A p)) := comap_mono hQD
        _ = torsionBy A p := comap_map_eq_self (by rw [hker]; exact hZD)
    refine ⟨comap f Qbar, hBD.trans hDA, (normal_of_le_center hQcen).comap f, ?_,
      Or.inr ⟨hZcard, ?_⟩⟩
    · refine nonempty_mulEquiv_pi_of_le_of_card (A := A) hp (hBD.trans hDA)
        (fun x hx => hDexp x (hBD hx)) ?_
      rw [natCard_comap_of_surjective hfsurj, hQcard, hker, hZcard, sq]
    · intro x hx
      exact mem_comap.mpr (by rw [MonoidHom.mem_ker.mp (hker.ge hx)]; exact one_mem _)
  ·
    obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(torsionBy (center P) p)) p
      (n := 2) (by rw [hk]; exact pow_dvd_pow p hk2)
    refine ⟨map (torsionBy (center P) p).subtype K,
      (map_subtype_le K).trans ((torsionBy_le (center P) p).trans hcenterA),
      normal_of_le_center ((map_subtype_le K).trans (torsionBy_le (center P) p)), ?_,
      Or.inl (map_subtype_le K)⟩
    refine nonempty_mulEquiv_pi_of_le_of_card (A := A) hp
      ((map_subtype_le K).trans ((torsionBy_le (center P) p).trans hcenterA))
      (fun x hx => hDexp x (hZD ((map_subtype_le K) hx))) ?_
    rw [card_map_of_injective (torsionBy (center P) p).subtype_injective, hKcard]

theorem exists_controlled_normal_plane' (hp : p.Prime) (hP : Nat.card P = p ^ a) (A : Subgroup P)
    [A.Normal] [IsMulCommutative A] (hself : centralizer (A : Set P) = A)
    (hA : 2 ∈ elementaryAbelianRanks p ↥A) :
    ∃ B : Subgroup P, B ≤ A ∧ B.Normal ∧ Nat.card B = p ^ 2 ∧ (∀ x ∈ B, x ^ p = 1) ∧
      (B ≤ torsionBy (center P) p ∨
        (Nat.card (torsionBy (center P) p) = p ∧ torsionBy (center P) p ≤ B)) := by
  obtain ⟨B, hBA, hBnormal, ⟨e⟩, hcases⟩ := exists_controlled_normal_plane hp hP A hself hA
  exact ⟨B, hBA, hBnormal, natCard_of_mulEquiv_pi e,
    fun _ hx => pow_eq_one_of_mulEquiv_pi e hx, hcases⟩

end

end CFSG.FeitThompson
