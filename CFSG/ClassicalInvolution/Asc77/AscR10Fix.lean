module

public import CFSG.ClassicalInvolution.AschTight.S1911P3b
public import CFSG.ClassicalInvolution.AschTight.S1911P3c

public section

namespace CFSG.ClassicalInvolution.Asc77.R10

open CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open MulAction in
set_option linter.style.haveILetI false in
theorem r_exists_conj_centralizes_of_odd {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    [hNn : N.Normal] (hN : Odd (Nat.card N)) {Q : Subgroup Y} (hQ : IsPGroup 2 Q) {t : Y}
    (ht : t * t = 1) (hQt : ∀ q ∈ Q, t⁻¹ * (q * t * q⁻¹) ∈ N) :
    ∃ v ∈ N, ∀ q ∈ Q, q * (v * t * v⁻¹) = (v * t * v⁻¹) * q := by
  classical
  set T : Set Y := {x | x * x = 1 ∧ t⁻¹ * x ∈ N} with hT
  have hQT : ∀ q ∈ Q, ∀ x ∈ T, q * x * q⁻¹ ∈ T := by
    intro q hq x hx
    refine ⟨?_, ?_⟩
    · calc q * x * q⁻¹ * (q * x * q⁻¹) = q * (x * x) * q⁻¹ := by group
        _ = 1 := by rw [hx.1]; group
    · have h1 := hQt q hq
      have h2 := hNn.conj_mem (t⁻¹ * x) hx.2 q
      have e : t⁻¹ * (q * x * q⁻¹) = (t⁻¹ * (q * t * q⁻¹)) * (q * (t⁻¹ * x) * q⁻¹) := by group
      rw [e]
      exact N.mul_mem h1 h2
  have hNT : ∀ v ∈ N, ∀ x ∈ T, v * x * v⁻¹ ∈ T := by
    intro v hv x hx
    refine ⟨?_, ?_⟩
    · calc v * x * v⁻¹ * (v * x * v⁻¹) = v * (x * x) * v⁻¹ := by group
        _ = 1 := by rw [hx.1]; group
    · have h1 : t⁻¹ * v * t ∈ N := by
        have := hNn.conj_mem v hv t⁻¹
        rwa [inv_inv] at this
      have h2 := hNn.conj_mem (t⁻¹ * x) hx.2 v
      have e : t⁻¹ * (v * x * v⁻¹) = (t⁻¹ * v * t * v⁻¹) * (v * (t⁻¹ * x) * v⁻¹) := by group
      rw [e]
      exact N.mul_mem (N.mul_mem h1 (N.inv_mem hv)) h2
  have htT : t ∈ T := ⟨ht, by simp⟩
  letI instQ : MulAction Q T :=
    { smul := fun q x => ⟨q * x * q⁻¹, hQT q q.2 x x.2⟩
      one_smul := fun x => by
        apply Subtype.ext
        show ((1 : Q) : Y) * (x : Y) * ((1 : Q) : Y)⁻¹ = x
        simp
      mul_smul := fun a b x => by
        apply Subtype.ext
        show ((a * b : Q) : Y) * (x : Y) * ((a * b : Q) : Y)⁻¹ =
          (a : Y) * ((b : Y) * (x : Y) * (b : Y)⁻¹) * (a : Y)⁻¹
        simp [mul_assoc] }
  letI instN : MulAction N T :=
    { smul := fun v x => ⟨v * x * v⁻¹, hNT v v.2 x x.2⟩
      one_smul := fun x => by
        apply Subtype.ext
        show ((1 : N) : Y) * (x : Y) * ((1 : N) : Y)⁻¹ = x
        simp
      mul_smul := fun a b x => by
        apply Subtype.ext
        show ((a * b : N) : Y) * (x : Y) * ((a * b : N) : Y)⁻¹ =
          (a : Y) * ((b : Y) * (x : Y) * (b : Y)⁻¹) * (a : Y)⁻¹
        simp [mul_assoc] }
  haveI hpre : IsPretransitive N T := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨v, hv, hvxy⟩ :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.S1911.exists_conj_eq_of_mul_mem_odd
        (O := N) hN x.2.1 y.2.1 (by
          have e : (x : Y)⁻¹ * y = (t⁻¹ * x)⁻¹ * (t⁻¹ * y) := by group
          rw [e]
          exact N.mul_mem (N.inv_mem x.2.2) y.2.2)
    refine ⟨⟨v⁻¹, N.inv_mem hv⟩, ?_⟩
    apply Subtype.ext
    show (v⁻¹ : Y) * (x : Y) * (v⁻¹ : Y)⁻¹ = y
    rw [inv_inv]
    exact hvxy
  have hodd : ¬ 2 ∣ Nat.card T := by
    have h1 : (stabilizer N (⟨t, htT⟩ : T)).index = Nat.card T :=
      index_stabilizer_of_transitive N (⟨t, htT⟩ : T)
    have h2 : (stabilizer N (⟨t, htT⟩ : T)).index ∣ Nat.card N := Subgroup.index_dvd_card _
    rw [← h1]
    intro h2'
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr (h2'.trans h2))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨x, hx⟩, hfix⟩ := hQ.nonempty_fixed_point_of_prime_not_dvd_card T hodd
  obtain ⟨v, hv, hvx⟩ :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S1911.exists_conj_eq_of_mul_mem_odd
      (O := N) hN ht hx.1 hx.2
  refine ⟨v⁻¹, N.inv_mem hv, fun q hq => ?_⟩
  have h1 : (⟨q, hq⟩ : Q) • (⟨x, hx⟩ : T) = ⟨x, hx⟩ := by
    exact mem_fixedPoints.mp hfix _
  have h2 : q * x * q⁻¹ = x := congrArg Subtype.val h1
  have e : v⁻¹ * t * v⁻¹⁻¹ = x := by rw [inv_inv]; exact hvx
  rw [e]
  calc q * x = q * x * q⁻¹ * q := by group
    _ = x * q := by rw [h2]



theorem r_exists_lift_pgroup {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN : Odd (Nat.card N)) {K : Subgroup Y} {P : Subgroup (Y ⧸ N)} (hP : IsPGroup 2 P)
    (hPK : P ≤ K.map (QuotientGroup.mk' N)) :
    ∃ Q : Subgroup Y, Q ≤ K ∧ IsPGroup 2 Q ∧ Q.map (QuotientGroup.mk' N) = P := by
  set H : Subgroup Y := K ⊓ P.comap (QuotientGroup.mk' N) with hH
  let f : ↥H →* ↥P := ((QuotientGroup.mk' N).comp H.subtype).codRestrict P (fun x => x.2.2)
  have hfy : ∀ x : ↥H, ((f x : ↥P) : Y ⧸ N) = QuotientGroup.mk' N (x : Y) := fun x => rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk, hky⟩ := hPK hy
    exact ⟨⟨k, hk, by show QuotientGroup.mk' N k ∈ P; rw [hky]; exact hy⟩, Subtype.ext hky⟩
  have hker : Odd (Nat.card f.ker) := by
    have h1 : f.ker.map H.subtype ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      have : QuotientGroup.mk' N (x : Y) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        simpa [hfy] using this
      exact (QuotientGroup.eq_one_iff _).mp this
    have h2 : Nat.card ↥(f.ker.map H.subtype) = Nat.card f.ker :=
      (Nat.card_congr (Subgroup.equivMapOfInjective f.ker H.subtype
        H.subtype_injective).toEquiv).symm
    rw [← h2]
    exact hN.of_dvd_nat (Subgroup.card_dvd_of_le h1)
  obtain ⟨T, hT2, hTb⟩ := exists_pGroup_bijective f hsurj hker hP
  refine ⟨T.map H.subtype, ?_, hT2.map _, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2.1
  · ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact (f x).2
    · intro hy
      obtain ⟨⟨x, hx⟩, hxy⟩ := hTb.2 ⟨y, hy⟩
      refine ⟨(x : Y), ⟨x, hx, rfl⟩, ?_⟩
      have := congrArg Subtype.val hxy
      simpa [hfy] using this

end CFSG.ClassicalInvolution.Asc77.R10
