module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveS

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal

open Subgroup JankoTwelve

variable {G : Type} [Group G]

theorem le_of_commutator_mem [Finite G] {U A : Subgroup G} {z : G} (hz : z * z = 1)
    (hAU : A ≤ U) (hA : Odd (Nat.card A)) (hzA : z ∈ normalizer (A : Set G))
    (hcomm : ∀ u ∈ U, u⁻¹ * z⁻¹ * u * z ∈ A)
    (hfix : U ⊓ centralizer ({z} : Set G) ≤ A) : U ≤ A := by
  classical
  intro u hu
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hmem : ∀ v : {v : G // u⁻¹ * v ∈ A}, u⁻¹ * (z⁻¹ * v.1 * z) ∈ A := fun v => by
    have h2 : z⁻¹ * (u⁻¹ * v.1) * z ∈ A := by
      have := (mem_normalizer_iff.mp hzA (u⁻¹ * v.1)).mp v.2
      rw [hzinv] at this ⊢
      exact this
    have : u⁻¹ * (z⁻¹ * v.1 * z) = (u⁻¹ * z⁻¹ * u * z) * (z⁻¹ * (u⁻¹ * v.1) * z) := by group
    rw [this]
    exact A.mul_mem (hcomm u hu) h2
  let f : {v : G // u⁻¹ * v ∈ A} → {v : G // u⁻¹ * v ∈ A} := fun v => ⟨z⁻¹ * v.1 * z, hmem v⟩
  have hf : Function.Involutive f := fun v => by
    apply Subtype.ext
    change z⁻¹ * (z⁻¹ * v.1 * z) * z = v.1
    rw [hzinv]
    simp only [← mul_assoc, hz, one_mul]
    rw [mul_assoc, hz, mul_one]
  let e : {v : G // u⁻¹ * v ∈ A} ≃ A :=
    { toFun := fun v => ⟨u⁻¹ * v.1, v.2⟩
      invFun := fun a => ⟨u * a.1, by simp [a.2]⟩
      left_inv := fun v => by ext; simp
      right_inv := fun a => by ext; simp }
  have : Fintype {v : G // u⁻¹ * v ∈ A} := Fintype.ofFinite _
  have hcard : ¬ 2 ∣ Fintype.card {v : G // u⁻¹ * v ∈ A} := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
    have := Nat.odd_iff.mp hA
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hcard
    (σ := hf.toPerm f) (by
      ext w
      simp [sq, hf w])
  have hv' : z⁻¹ * v.1 * z = v.1 := congrArg Subtype.val hv
  have hvU : v.1 ∈ U := by
    have := U.mul_mem hu (hAU v.2)
    rwa [mul_inv_cancel_left] at this
  have hvz : v.1 ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc v.1 * z = z * (z⁻¹ * v.1 * z) := by group
      _ = z * v.1 := by rw [hv']
  have hvA : v.1 ∈ A := hfix ⟨hvU, hvz⟩
  have := A.mul_mem hvA (A.inv_mem v.2)
  rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this

def trivOn (I S : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ normalizer (I : Set G) ∧ g ∈ normalizer (S : Set G) ∧
    ∀ x ∈ I, g * x * g⁻¹ * x⁻¹ ∈ S}
  mul_mem' {a b} ha hb := ⟨mul_mem ha.1 hb.1, mul_mem ha.2.1 hb.2.1, fun x hx => by
    have h1 := (mem_normalizer_iff.mp ha.2.1 _).mp (hb.2.2 x hx)
    have := mul_mem h1 (ha.2.2 x hx)
    convert this using 1
    group⟩
  one_mem' := ⟨one_mem _, one_mem _, fun x _ => by simp⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, inv_mem ha.2.1, fun x hx => by
    have hy : a⁻¹ * x * a ∈ I := by
      have := (mem_normalizer_iff.mp (inv_mem ha.1) x).mp hx
      rwa [inv_inv] at this
    have := inv_mem (ha.2.2 _ hy)
    convert this using 1
    group⟩

theorem conj_mem_trivOn {I S : Subgroup G} {c g : G} (hc : c ∈ trivOn I S)
    (hgI : g ∈ normalizer (I : Set G)) (hgS : g ∈ normalizer (S : Set G)) :
    g * c * g⁻¹ ∈ trivOn I S := by
  refine ⟨mul_mem (mul_mem hgI hc.1) (inv_mem hgI), mul_mem (mul_mem hgS hc.2.1) (inv_mem hgS),
    fun x hx => ?_⟩
  have hy : g⁻¹ * x * g ∈ I := by
    have := (mem_normalizer_iff.mp (inv_mem hgI) x).mp hx
    rwa [inv_inv] at this
  have := (mem_normalizer_iff.mp hgS _).mp (hc.2.2 _ hy)
  convert this using 1
  group

theorem mem_normalizer_trivOn {I S : Subgroup G} {g : G} (hgI : g ∈ normalizer (I : Set G))
    (hgS : g ∈ normalizer (S : Set G)) : g ∈ normalizer ((trivOn I S : Subgroup G) : Set G) := by
  refine mem_normalizer_iff.mpr fun c => ⟨fun hc => conj_mem_trivOn hc hgI hgS, fun hc => ?_⟩
  have := conj_mem_trivOn hc (inv_mem hgI) (inv_mem hgS)
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

section Frame

variable [Finite G] {z : G} {fr : JankoFrame G z}

omit [Finite G] in
theorem E_le_I : fr.E ≤ fr.I := le_sup_left

theorem S_le_I (h : Hyp fr) : fr.S ≤ fr.I := h.S_le_ZN.trans le_sup_right

theorem z_conj_mul_inv_mem_S (h : Hyp fr) {x : G} (hx : x ∈ fr.I) :
    z * x * z⁻¹ * x⁻¹ ∈ fr.S := by
  rw [h.I_eq_E_sup_S] at hx
  obtain ⟨e, he, s, hs, rfl⟩ := exists_mul_of_mem_sup h.E_le_normalizer_S hx
  have hze : z * e * z⁻¹ = e := by
    have := mem_centralizer_singleton_iff.mp (fr.E_le he)
    rw [← this, mul_inv_cancel_right]
  have hzs : z * s * z⁻¹ = s⁻¹ := h.z_inv_of_mem_S hs
  have : z * (e * s) * z⁻¹ * (e * s)⁻¹ = e * (s⁻¹ * s⁻¹) * e⁻¹ := by
    calc z * (e * s) * z⁻¹ * (e * s)⁻¹ = (z * e * z⁻¹) * (z * s * z⁻¹) * s⁻¹ * e⁻¹ := by group
      _ = e * (s⁻¹ * s⁻¹) * e⁻¹ := by rw [hze, hzs]; group
  rw [this]
  exact (mem_normalizer_iff.mp (h.E_le_normalizer_S he) _).mp
    (fr.S.mul_mem (fr.S.inv_mem hs) (fr.S.inv_mem hs))

theorem z_mem_trivOn (h : Hyp fr) (p12 : JankoProp12 fr) : z ∈ trivOn fr.I fr.S :=
  ⟨h.z_mem_normalizer_I, p12.K_le_normalizer_S h.z_mem_K, fun _ hx => z_conj_mul_inv_mem_S h hx⟩

theorem E_le_trivOn (h : Hyp fr) : fr.E ≤ trivOn fr.I fr.S := fun e he =>
  ⟨le_normalizer_of_commute (fun a ha b hb => h.p11.I_comm a (E_le_I ha) b hb) he,
    h.E_le_normalizer_S he, fun x hx => by
      rw [h.p11.I_comm e (E_le_I he) x hx, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _⟩

theorem U_le_normalizer_S (h : Hyp fr) : fr.U ≤ normalizer (fr.S : Set G) :=
  le_normalizer_of_commute fun _ hu s hs =>
    ((mem_centralizer_iff.mp (h.U_le_centralizer_S hu)) s hs).symm

theorem U_le_trivOn (h : Hyp fr) (p12 : JankoProp12 fr) : fr.U ≤ trivOn fr.I fr.S := by
  have hzT := z_mem_trivOn h p12
  have hle : fr.U ≤ fr.U ⊓ trivOn fr.I fr.S := by
    refine le_of_commutator_mem h.z_mul_z inf_le_left
      (Odd.of_dvd_nat h.odd_card_U (card_dvd_of_le inf_le_left))
      (inf_mem_normalizer h.z_mem_normalizer_U (mem_normalizer_trivOn hzT.1 hzT.2.1))
      (fun u hu => ⟨?_, ?_⟩) ?_
    · have := mul_mem (inv_mem hu) ((mem_normalizer_iff.mp (inv_mem h.z_mem_normalizer_U) u).mp hu)
      simpa [mul_assoc] using this
    · have := conj_mem_trivOn (inv_mem hzT) (p12.U_le_normalizer_I (inv_mem hu))
        (U_le_normalizer_S h (inv_mem hu))
      simpa [mul_assoc] using mul_mem this hzT
    · rw [p12.U_inf_centralizer_z]
      exact le_inf (h.E_le_N.trans h.N_le_U) (E_le_trivOn h)
  exact fun u hu => (hle hu).2

theorem comm_mem_S (h : Hyp fr) (p12 : JankoProp12 fr) {x u : G} (hx : x ∈ fr.I)
    (hu : u ∈ fr.U) : u * x * u⁻¹ * x⁻¹ ∈ fr.S :=
  (U_le_trivOn h p12 hu).2.2 x hx

end Frame

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal
