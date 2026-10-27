module

public import CFSG.GH74.Uniqueness.Prop37
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma312

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

@[expose] def IsZStar (H : Type*) [Group H] (z : H) : Prop :=
  ∀ g : H, g * z * g⁻¹ * z⁻¹ ∈ pPrimeCore 2 H

theorem pPrimeCore_sup_centralizer_eq_top {H : Type} [Group H] [Finite H] {z : H}
    (hz : orderOf z = 2) (h : IsZStar H z) :
    pPrimeCore 2 H ⊔ centralizer ({z} : Set H) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := H))
  have : (pPrimeCore 2 H).Normal := pPrimeCore_normal
  have hzN : z ∈ normalizer ((pPrimeCore 2 H : Subgroup H) : Set H) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top z
  rw [eq_top_iff]
  intro g _
  obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_centralizer hz (le_top : pPrimeCore 2 H ≤ ⊤) hzN
    hodd (fun a _ => h a) (Subgroup.mem_top g)
  exact Subgroup.mul_mem_sup hn (Subgroup.mem_inf.mp hc).2

section Lemma311

variable {H : Type} [Group H] [Finite H] {Ψ : Type*} [MulAction H Ψ]
  [MulAction.IsPretransitive H Ψ]

theorem lemma311 {z : H} (hz : orderOf z = 2) (hZ : IsZStar H z) (Y : Subgroup H) (α : Ψ)
    (hY : MulAction.stabilizer H α = Y) (hYtop : Y ≠ ⊤)
    (hcent : centralizer ({z} : Set H) ≤ Y) :
    ∃ R : Subgroup H, ∃ r : ℕ, r.Prime ∧ Odd r ∧ IsPGroup r R ∧
      Nat.card (MulAction.orbit R α) = r ∧
      z ∈ normalizer (R : Set H) ∧ (∀ β ∈ MulAction.orbit R α, z • β ∈ MulAction.orbit R α) ∧
      (IsCyclic R ∧ ∀ q ∈ R, z * q * z⁻¹ = q⁻¹) ∧
      (∀ β ∈ MulAction.orbit R α, ∀ γ ∈ MulAction.orbit R α, β ≠ γ →
        ∃ τ ∈ R ⊔ zpowers z, orderOf τ = 2 ∧ τ • β = γ ∧ τ • γ = β) ∧
      (∀ β ∈ MulAction.orbit R α, ∀ γ ∈ MulAction.orbit R α, β ≠ γ →
        ∀ x : H, x • β = β → x • γ = γ → ∀ δ ∈ MulAction.orbit R α, x • δ = δ) := by
  have : Finite Ψ := Finite.of_surjective (fun g : H => g • α)
    (fun β => by obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H α β; exact ⟨g, hg⟩)
  have hz2 : z * z = 1 := mul_self_of_orderOf_eq_two hz
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hinv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution z :=
    ⟨hz1, by rw [pow_two]; exact hz2⟩
  have hzY : z ∈ Y := hcent (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hfactor := pPrimeCore_sup_centralizer_eq_top hz hZ
  obtain ⟨R, Γ, rfl, ⟨r, hr, hodd, hRp, hcard⟩, hcyc, hinvR, hzR, hzΓ, he, -⟩ :=
    CFSG.BenderSuzuki.lemma_3_11 Y z α hY hYtop hzY hinv hcent hfactor
  refine ⟨R, r, hr, hodd, hRp, hcard, hzR, hzΓ, ⟨hcyc, hinvR⟩, ?_,
    fun β hβ γ hγ hβγ => he hβ hγ hβγ⟩
  intro β hβ γ hγ hβγ
  obtain ⟨a', rfl⟩ := MulAction.mem_orbit_iff.mp hβ
  obtain ⟨b', rfl⟩ := MulAction.mem_orbit_iff.mp hγ
  have haR : (a' : H) ∈ R := a'.2
  have hbR : (b' : H) ∈ R := b'.2
  let _ : CommGroup R := IsCyclic.commGroup
  have hab : (a' : H) * b' = b' * a' := congrArg Subtype.val (mul_comm a' b')
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzα : z • α = α := MulAction.mem_stabilizer_iff.mp (hY ▸ hzY)
  have hzq : ∀ q ∈ R, z * q = q⁻¹ * z := fun q hq => by
    have := hinvR q hq
    calc z * q = (z * q * z⁻¹) * z := by group
      _ = q⁻¹ * z := by rw [this]
  set a : H := (a' : H) with ha
  set b : H := (b' : H) with hb
  set q : H := (a * b)⁻¹ with hq
  have hqR : q ∈ R := R.inv_mem (R.mul_mem haR hbR)
  have hq' : q = a⁻¹ * b⁻¹ := by rw [hq, hab, mul_inv_rev]
  refine ⟨z * q, mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    (Subgroup.mem_sup_left hqR), ?_, ?_, ?_⟩
  ·
    have hsq : (z * q) * (z * q) = 1 := by
      calc (z * q) * (z * q) = (z * q * z⁻¹) * q := by rw [hzi]; group
        _ = q⁻¹ * q := by rw [hinvR q hqR]
        _ = 1 := inv_mul_cancel q
    have hne : z * q ≠ 1 := by
      intro h1
      have hzR' : z ∈ R := by
        have : z = q⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact R.inv_mem hqR
      have hr2 : r ≠ 2 := fun h2 => (Nat.not_even_iff_odd.mpr hodd) (h2 ▸ even_two)
      have := odd_orderOf_of_isPGroup hr hr2 hRp hzR'
      rw [hz] at this
      exact absurd this (by decide)
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  ·
    show (z * q) • (a • α) = b • α
    rw [← mul_smul]
    have e : z * q * a = b * z := by
      calc z * q * a = z * (q * a) := by rw [mul_assoc]
        _ = z * b⁻¹ := by rw [hq]; group
        _ = (b⁻¹)⁻¹ * z := hzq b⁻¹ (R.inv_mem hbR)
        _ = b * z := by rw [inv_inv]
    rw [e, mul_smul, hzα]
  ·
    show (z * q) • (b • α) = a • α
    rw [← mul_smul]
    have e : z * q * b = a * z := by
      calc z * q * b = z * (q * b) := by rw [mul_assoc]
        _ = z * a⁻¹ := by rw [hq']; group
        _ = (a⁻¹)⁻¹ * z := hzq a⁻¹ (R.inv_mem haR)
        _ = a * z := by rw [inv_inv]
    rw [e, mul_smul, hzα]

end Lemma311

section Lemma312

theorem lemma312 {H : Type*} [Group H] [Finite H] (hsolv : Group.IsSolvable H) {Y : Subgroup H}
    (hY : IsStronglyEmbedded Y) {z : H} (hzY : z ∈ Y) (hz : orderOf z = 2)
    (hfixed : ∀ y ∈ Y, y ≠ 1 → z * y * z⁻¹ = y⁻¹ → ∃! ω : H ⧸ Y, y • ω = ω) :
    Y = centralizer ({z} : Set H) ∧ ∀ y ∈ Y, orderOf y = 2 → y = z := by
  have hnat : CFSG.BenderSuzuki.IsStronglyEmbedded Y :=
    CFSG.BenderSuzuki.isStronglyEmbedded_of_parity Y
      (isStronglyEmbeddedOrder_of_isStronglyEmbedded hY)
  have hEven : Even (Nat.card H) :=
    even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hY.2.1) (Subgroup.card_subgroup_dvd_card Y))
  have hinv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp hz).2, (orderOf_eq_prime_iff.mp hz).1⟩
  obtain ⟨h1, h2⟩ := CFSG.BenderSuzuki.lemma_3_12 Y hsolv hEven hnat hzY hinv hfixed
  exact ⟨h1, fun y hy hord => h2 y hy ⟨(orderOf_eq_prime_iff.mp hord).2,
    (orderOf_eq_prime_iff.mp hord).1⟩⟩

end Lemma312

end CFSG.GH74.Uniqueness
