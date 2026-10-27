module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5Count
public import CFSG.HardMathSupport.Solomon.Proving.TorusLift

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.Proving

variable {L S : Type*} [Group L] [Group S]

@[expose] def autFix (β : MulAut L) : Subgroup L where
  carrier := {x | β x = x}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := map_one β
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_autFix {β : MulAut L} {x : L} : x ∈ autFix β ↔ β x = x := Iff.rfl

section Lift

variable {Γ : L →* S} (hΓ : Function.Surjective Γ) (hZ : Γ.ker ≤ Subgroup.center L)
  {β : MulAut L} {b : MulAut S} (hβ : ∀ x, Γ (β x) = b (Γ x))
include hΓ hZ hβ

theorem mem_map_autFix_of_two [Finite L] (hodd : Odd (Nat.card Γ.ker)) {g : S} (hg : b g = g)
    {e : ℕ} (hge : g ^ 2 ^ e = 1) : g ∈ (autFix β).map Γ := by
  classical
  obtain ⟨m, hm⟩ := hodd
  have hkm : ∀ w ∈ Γ.ker, w ^ (2 * m + 1) = 1 := by
    intro w hw
    have := pow_card_eq_one' (G := Γ.ker) (x := ⟨w, hw⟩)
    rw [hm] at this
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (2 * m + 1) (orderOf g) :=
    (Nat.Coprime.pow_right e (Odd.coprime_two_right ⟨m, rfl⟩)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hge)
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
  obtain ⟨u, rfl⟩ := hΓ g
  set v := u ^ ((2 * m + 1) * c) with hv
  have hΓv : Γ v = Γ u := by rw [hv, map_pow, pow_mul, hc]
  have hv2 : v ^ 2 ^ e = 1 := by
    have h1 : u ^ 2 ^ e ∈ Γ.ker := by rw [MonoidHom.mem_ker, map_pow, hge]
    calc v ^ 2 ^ e = ((u ^ 2 ^ e) ^ (2 * m + 1)) ^ c := by
          rw [hv, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [hkm _ h1, one_pow]
  refine ⟨v, ?_, hΓv⟩
  have hz : v⁻¹ * β v ∈ Γ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβ, hΓv, hg, inv_mul_cancel]
  set z := v⁻¹ * β v with hzdef
  have hzc : ∀ y : L, z * y = y * z := fun y => (Subgroup.mem_center_iff.1 (hZ hz) y).symm
  have hβv : β v = v * z := by rw [hzdef, mul_inv_cancel_left]
  have hz2 : z ^ 2 ^ e = 1 := by
    have h1 : (v * z) ^ 2 ^ e = v ^ 2 ^ e * z ^ 2 ^ e :=
      (show Commute v z from (hzc v).symm).mul_pow _
    have h2 : (β v) ^ 2 ^ e = 1 := by rw [← map_pow, hv2, map_one]
    rw [hβv, h1, hv2, one_mul] at h2
    exact h2
  have hz1 : z = 1 := by
    have hd1 : orderOf z ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hz2
    have hd2 : orderOf z ∣ 2 * m + 1 := orderOf_dvd_of_pow_eq_one (hkm z hz)
    have hcop' : Nat.Coprime (2 ^ e) (2 * m + 1) :=
      Nat.Coprime.pow_left e (Odd.coprime_two_left ⟨m, rfl⟩)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop' hd1 hd2)
  show β v = v
  rw [hβv, hz1, mul_one]

theorem mem_map_autFix_of_commutator {x y : S} (hx : b x = x) (hy : b y = y) :
    x * y * x⁻¹ * y⁻¹ ∈ (autFix β).map Γ := by
  obtain ⟨u, rfl⟩ := hΓ x
  obtain ⟨w, rfl⟩ := hΓ y
  refine ⟨u * w * u⁻¹ * w⁻¹, ?_, by simp⟩
  have h1 : u⁻¹ * β u ∈ Γ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβ, hx, inv_mul_cancel]
  have h2 : w⁻¹ * β w ∈ Γ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβ, hy, inv_mul_cancel]
  set z₁ := u⁻¹ * β u with hz₁
  set z₂ := w⁻¹ * β w with hz₂
  have hc1 : ∀ g : L, z₁ * g = g * z₁ := fun g => (Subgroup.mem_center_iff.1 (hZ h1) g).symm
  have hc2 : ∀ g : L, z₂ * g = g * z₂ := fun g => (Subgroup.mem_center_iff.1 (hZ h2) g).symm
  have hu : β u = u * z₁ := by rw [hz₁, mul_inv_cancel_left]
  have hw : β w = w * z₂ := by rw [hz₂, mul_inv_cancel_left]
  show β (u * w * u⁻¹ * w⁻¹) = u * w * u⁻¹ * w⁻¹
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hu, hw]
  have k1 : ∀ g t : L, z₁ * (g * t) = g * (z₁ * t) := fun g t => by
    rw [← mul_assoc, hc1 g, mul_assoc]
  have k2 : ∀ g t : L, z₂ * (g * t) = g * (z₂ * t) := fun g t => by
    rw [← mul_assoc, hc2 g, mul_assoc]
  simp only [mul_inv_rev, mul_assoc]
  rw [k1 w, k1 z₂, mul_inv_cancel_left, k2 u⁻¹, mul_inv_cancel_left]

end Lift

section Torus

variable [Finite L] {p r : ℕ} [NeZero r] {Γ : L →* S}

theorem hasCentTorus_of_torusData (hp : p.Prime) (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center L) (hodd : Odd (Nat.card (Subgroup.center L)))
    (D : TorusData (Fin r) p S) (hcard : Nat.card (Subgroup.closure (Set.range D.X)) = p ^ r)
    {T : S} (hT1 : T ≠ 1) (hT2 : ∃ e : ℕ, T ^ 2 ^ e = 1) (hTX : ∀ i, Commute T (D.X i))
    (hTS : ∀ i, Commute T (D.Sw i)) : HasCentTorus p r L := by
  obtain ⟨E, U, hE, hEker, hEmap, hU1, hU2, hEU⟩ := exists_cover_torus_two hp D Γ hΓ hker.le
    (by rw [hker]; exact hodd) hT1 hT2 hTX hTS
  refine ⟨E, U, hE, ?_, by rw [← hker]; exact hEker, hU1, hU2, hEU⟩
  have hinj : Function.Injective (Γ.domRestrict E) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : L) ∈ E ⊓ Γ.ker := ⟨x.2, hx⟩
    rw [hEker, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  rw [← hcard, ← hEmap, ← MonoidHom.domRestrict_range]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv

omit [Finite L] [NeZero r] in
theorem HasCentTorus.hasTorusFixed_one {K : Type*} [Group K] (h : HasCentTorus p r K) :
    HasTorusFixed p r K 1 := by
  obtain ⟨E, U, hE, hEc, hEZ, hU1, hU2, hEU⟩ := h
  exact ⟨E, U, hE, hEc, hEZ, hU1, hU2, hEU.trans (Subgroup.centralizer_le_normalizer _),
    fun x _ => rfl, fun u hu => hu⟩

theorem hasTorusFixed_of_fixData (hp : p.Prime) (hker : Γ.ker = Subgroup.center L)
    (hodd : Odd (Nat.card (Subgroup.center L))) (β : MulAut L)
    (D : TorusData (Fin r) p ↥((autFix β).map Γ))
    (hcard : Nat.card (Subgroup.closure (Set.range D.X)) = p ^ r)
    {T : ↥((autFix β).map Γ)} (hT1 : T ≠ 1) (hT2 : ∃ e : ℕ, T ^ 2 ^ e = 1)
    (hTX : ∀ i, Commute T (D.X i)) (hTS : ∀ i, Commute T (D.Sw i)) :
    HasTorusFixed p r L β := by
  classical
  let Γ' : ↥(autFix β) →* ↥((autFix β).map Γ) :=
    (Γ.comp (autFix β).subtype).codRestrict ((autFix β).map Γ) (fun x => ⟨x, x.2, rfl⟩)
  have hΓ'apply : ∀ x : ↥(autFix β), ((Γ' x : ↥((autFix β).map Γ)) : S) = Γ x := fun x => rfl
  have hΓ's : Function.Surjective Γ' := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker' : ∀ x : ↥(autFix β), x ∈ Γ'.ker ↔ (x : L) ∈ Γ.ker := by
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hΓ'apply]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hZ' : Γ'.ker ≤ Subgroup.center ↥(autFix β) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxZ : (x : L) ∈ Subgroup.center L := hker ▸ (hker' x).1 hx
    exact Subgroup.mem_center_iff.1 hxZ y
  have hodd' : Odd (Nat.card Γ'.ker) := by
    have hle : (Γ'.ker.map (autFix β).subtype) ≤ Subgroup.center L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hker ▸ (hker' x).1 hx
    have hdvd : Nat.card Γ'.ker ∣ Nat.card (Subgroup.center L) := by
      rw [← Subgroup.card_map_of_injective (autFix β).subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact Odd.of_dvd_nat hodd hdvd
  obtain ⟨E, U, hE, hEker, hEmap, hU1, hU2, hEU⟩ :=
    exists_cover_torus_two hp D Γ' hΓ's hZ' hodd' hT1 hT2 hTX hTS
  have hEcen : E.map (autFix β).subtype ≤
      Subgroup.centralizer ((U.map (autFix β).subtype : Subgroup L) : Set L) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (hEU hx) u hu)
  refine ⟨E.map (autFix β).subtype, U.map (autFix β).subtype, ?_, ?_, ?_, ?_, hU2.map _,
    hEcen.trans (Subgroup.centralizer_le_normalizer _), ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      show (x : L) * y = y * x
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      exact congrArg Subtype.val this
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  · have hinj : Function.Injective (Γ'.domRestrict E) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : (x : ↥(autFix β)) ∈ E ⊓ Γ'.ker := ⟨x.2, hx⟩
      rw [hEker, Subgroup.mem_bot] at hx'
      exact Subtype.ext hx'
    have h1 : Nat.card (E.map Γ') = Nat.card E := by
      have h2 : (Γ'.domRestrict E).range = E.map Γ' := MonoidHom.domRestrict_range (K := E) Γ'
      have h3 := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      rwa [h2] at h3
    rw [hEmap, hcard] at h1
    rw [Subgroup.card_map_of_injective (autFix β).subtype_injective, ← h1]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hxZ⟩
    have hxk : x ∈ Γ'.ker := (hker' x).2 (by rw [hker]; exact hxZ)
    have : x ∈ E ⊓ Γ'.ker := ⟨hx, hxk⟩
    rw [hEker, Subgroup.mem_bot] at this
    rw [this]
    rfl
  · intro h
    apply hU1
    exact (Subgroup.map_eq_bot_iff_of_injective U (autFix β).subtype_injective).1 h
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨u, hu, rfl⟩
    have : β (u : L) = u := u.2
    show β (u : L) ∈ _
    rw [this]
    exact ⟨u, hu, rfl⟩

end Torus

end CFSG.HardMathSupport.Solomon.Coordinator
