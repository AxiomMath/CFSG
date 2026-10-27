module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Centralizers

public noncomputable section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace CenterQuotient

theorem eq_one_of_two_pow_of_odd {H : Type*} [Group H] {x : H} {k n : ℕ}
    (htwo : x ^ (2 ^ k) = 1) (hodd : Odd n) (hn : x ^ n = 1) : x = 1 := by
  have hcop : (orderOf x).Coprime n :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one htwo)
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hn))

variable {G : Type*} [Group G]

@[expose] def quotientSubgroup (D : Subgroup G) : Subgroup (G ⧸ Subgroup.center G) :=
  D.map (QuotientGroup.mk' (Subgroup.center G))

@[expose] def restriction (D : Subgroup G) : D →* quotientSubgroup D :=
  (QuotientGroup.mk' (Subgroup.center G)).subgroupMap D

theorem restriction_surjective (D : Subgroup G) : Function.Surjective (restriction D) :=
  MonoidHom.subgroupMap_surjective _ D

theorem mem_ker_restriction (D : Subgroup G) (d : D) :
    d ∈ (restriction D).ker ↔ d.val ∈ Subgroup.center G := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' : QuotientGroup.mk' (Subgroup.center G) d.val = 1 := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).mp h'
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)

theorem subtype_comp_restriction (D : Subgroup G) :
    (quotientSubgroup D).subtype.comp (restriction D) =
      (QuotientGroup.mk' (Subgroup.center G)).comp D.subtype := rfl

theorem mk_mem_center_of_mem_core_sup_center (D : Subgroup G) (d : D)
    (hd : d.val ∈ aschbacherThm5Core D ⊔ Subgroup.center G) :
    QuotientGroup.mk' (aschbacherThm5OddCore D) d ∈
      Subgroup.center (D ⧸ aschbacherThm5OddCore D) := by
  obtain ⟨o, ho, z, hz, hoz⟩ := Subgroup.mem_sup_of_normal_right.mp hd
  have hoD : o ∈ D := core_le D ho
  have hzD : z ∈ D := by
    have hzeq : z = o⁻¹ * d.val := by rw [← hoz]; group
    rw [hzeq]
    exact D.mul_mem (D.inv_mem hoD) d.2
  have hone : QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨o, hoD⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ((mem_core_iff D ⟨o, hoD⟩).mp ho)
  have hmk : QuotientGroup.mk' (aschbacherThm5OddCore D) d =
      QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨z, hzD⟩ := by
    have hdeq : d = ⟨o, hoD⟩ * ⟨z, hzD⟩ := Subtype.ext hoz.symm
    rw [hdeq, map_mul, hone, one_mul]
  rw [hmk, Subgroup.mem_center_iff]
  intro y
  obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_center_iff.mp hz e.val)

theorem comap_normalizer_center_quotient (D : Subgroup G) (r : ℕ) (hr : 1 ≤ r)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) → g ∈ Subgroup.normalizer (D : Set G)) :
    (Subgroup.normalizer (quotientSubgroup D : Set (G ⧸ Subgroup.center G))).comap
        (QuotientGroup.mk' (Subgroup.center G)) = Subgroup.normalizer (D : Set G) := by
  rw [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
    quotientSubgroup, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  exact normalizer_adjoin_center D r hr Abar hii

variable [Finite G]

theorem map_oddCore_le (D : Subgroup G) :
    (aschbacherThm5OddCore D).map (restriction D) ≤
      aschbacherThm5OddCore (quotientSubgroup D) :=
  le_sSup ⟨(aschbacherThm5OddCore_normal D).map _ (restriction_surjective D),
    (oddCore_odd D).of_dvd_nat (Subgroup.card_map_dvd _ _)⟩

@[expose] def factorMap (D : Subgroup G) :
    D ⧸ aschbacherThm5OddCore D →*
      quotientSubgroup D ⧸ aschbacherThm5OddCore (quotientSubgroup D) :=
  QuotientGroup.map _ _ (restriction D) (Subgroup.map_le_iff_le_comap.mp (map_oddCore_le D))

@[expose] def quotientFactors (D : Subgroup G) {r : ℕ}
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    Fin r → Subgroup (quotientSubgroup D ⧸ aschbacherThm5OddCore (quotientSubgroup D)) :=
  fun i => (Abar i).map (factorMap D)

theorem quotientFactors_apply (D : Subgroup G) {r : ℕ}
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) (i : Fin r) :
    quotientFactors D Abar i = (Abar i).map (factorMap D) := rfl

theorem factorMap_mk (D : Subgroup G) (d : D) :
    factorMap D (QuotientGroup.mk' (aschbacherThm5OddCore D) d) =
      QuotientGroup.mk' (aschbacherThm5OddCore (quotientSubgroup D)) (restriction D d) :=
  QuotientGroup.map_mk' _ _ _ _ d

theorem factorMap_surjective (D : Subgroup G) : Function.Surjective (factorMap D) := by
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨d, rfl⟩ := restriction_surjective D y
  exact ⟨_, factorMap_mk D d⟩

theorem comap_le_oddCore_sup_ker (D : Subgroup G) (M : Subgroup (quotientSubgroup D))
    [M.Normal] (hodd : Odd (Nat.card M)) :
    M.comap (restriction D) ≤ aschbacherThm5OddCore D ⊔ (restriction D).ker := by
  set N := M.comap (restriction D)
  have : N.Normal := Subgroup.Normal.comap inferInstance (restriction D)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : ∀ x : N, (∃ k : ℕ, x ^ (2 ^ k) = 1) → (x : D) ∈ (restriction D).ker := by
    rintro x ⟨k, hk⟩
    rw [MonoidHom.mem_ker]
    have hk' : restriction D x ^ (2 ^ k) = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, hk, Subgroup.coe_one, map_one]
    exact eq_one_of_two_pow_of_odd hk' hodd
      (orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard M x.2))
  obtain ⟨P⟩ : Nonempty (Sylow 2 N) := inferInstance
  have hPker : ∀ x ∈ (P : Subgroup N), (x : D) ∈ (restriction D).ker := by
    intro x hx
    apply htwo x
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hP : Subgroup.normalizer (P : Set N) ≤ Subgroup.centralizer (P : Set N) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hz := (mem_ker_restriction D _).mp (hPker x hx)
    exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.mp hz _).symm)
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
  have hKodd : Odd (Nat.card (MonoidHom.transferSylow P hP).ker) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (MonoidHom.not_dvd_card_ker_transferSylow P hP))
  have hKcore : (MonoidHom.transferSylow P hP).ker ≤ aschbacherThm5OddCore N :=
    le_sSup ⟨inferInstance, hKodd⟩
  have hNcore : (aschbacherThm5OddCore N).map N.subtype = N ⊓ aschbacherThm5OddCore D :=
    OddCore.normal_intersection D N
  intro n hn
  have hmem : (⟨n, hn⟩ : N) ∈ (MonoidHom.transferSylow P hP).ker ⊔ (P : Subgroup N) := by
    rw [hcompl.sup_eq_top]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, p, hp, hkp⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  have hneq : n = (k : D) * (p : D) := (congrArg Subtype.val hkp).symm
  rw [hneq]
  apply Subgroup.mul_mem_sup _ (hPker p hp)
  have hkmap : (k : D) ∈ (aschbacherThm5OddCore N).map N.subtype :=
    Subgroup.mem_map_of_mem N.subtype (hKcore hk)
  rw [hNcore] at hkmap
  exact hkmap.2

end CenterQuotient

open CenterQuotient

theorem oddCore_center_quotient {G : Type*} [Group G] [Finite G] (D : Subgroup G) :
    aschbacherThm5OddCore (quotientSubgroup D) =
      (aschbacherThm5OddCore D).map (restriction D) := by
  apply le_antisymm _ (map_oddCore_le D)
  apply sSup_le
  rintro M ⟨hMnormal, hModd⟩ y hy
  have := hMnormal
  obtain ⟨d, rfl⟩ := restriction_surjective D y
  have hd : d ∈ aschbacherThm5OddCore D ⊔ (restriction D).ker :=
    comap_le_oddCore_sup_ker D M hModd hy
  rw [← Subgroup.comap_map_eq] at hd
  exact hd

namespace CenterQuotient

variable {G : Type*} [Group G] [Finite G]

theorem core_center_quotient (D : Subgroup G) :
    aschbacherThm5Core (quotientSubgroup D) =
      (aschbacherThm5Core D).map (QuotientGroup.mk' (Subgroup.center G)) := by
  simp only [aschbacherThm5Core]
  rw [oddCore_center_quotient, Subgroup.map_map, Subgroup.map_map, subtype_comp_restriction]

theorem preimage_center_quotient (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    aschbacherThm5Preimage (quotientSubgroup D) (Abar.map (factorMap D)) =
      (aschbacherThm5Preimage D Abar).map (QuotientGroup.mk' (Subgroup.center G)) := by
  have hcomap : (Abar.map (factorMap D)).comap
      (QuotientGroup.mk' (aschbacherThm5OddCore (quotientSubgroup D))) =
      (Abar.comap (QuotientGroup.mk' (aschbacherThm5OddCore D))).map (restriction D) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨d, rfl⟩ := restriction_surjective D y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
      rw [factorMap_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, oddCore_center_quotient] at hxy
      obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.mp hxy
      refine ⟨a * o, ?_, ?_⟩
      · have hone : QuotientGroup.mk' (aschbacherThm5OddCore D) o = 1 :=
          (QuotientGroup.eq_one_iff o).mpr ho
        change QuotientGroup.mk' (aschbacherThm5OddCore D) (a * o) ∈ Abar
        rw [map_mul, hone, mul_one]
        exact hx
      · rw [map_mul, hoeq, mul_inv_cancel_left]
    · rintro y ⟨d, hd, rfl⟩
      change QuotientGroup.mk' (aschbacherThm5OddCore (quotientSubgroup D)) (restriction D d) ∈
        Abar.map (factorMap D)
      rw [← factorMap_mk]
      exact Subgroup.mem_map_of_mem _ hd
  simp only [aschbacherThm5Preimage]
  rw [hcomap, Subgroup.map_map, Subgroup.map_map, subtype_comp_restriction]

theorem ker_factorMap_le_center (D : Subgroup G) :
    (factorMap D).ker ≤ Subgroup.center (D ⧸ aschbacherThm5OddCore D) := by
  intro x hx
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [MonoidHom.mem_ker, factorMap_mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    oddCore_center_quotient, ← Subgroup.mem_comap, Subgroup.comap_map_eq] at hx
  apply mk_mem_center_of_mem_core_sup_center
  obtain ⟨o, ho, z, hz, hoz⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  rw [← hoz]
  exact Subgroup.mul_mem_sup ((mem_core_iff D o).mpr ho) ((mem_ker_restriction D z).mp hz)

end CenterQuotient

end CFSG.ComponentClassification.AschbacherTheorem5
