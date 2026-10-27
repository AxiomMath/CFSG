module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut

public section

open scoped MatrixGroups

open CFSG.GH74.GLS.IVK.Lifted (pPrimeCore_two_sl2_five pPrimeCore_two_sl2_three)

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

theorem pPrimeCore_two_sl2_odd {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) :
    pPrimeCore 2 SL(2, K) = ⊥ := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  by_cases h3 : Nat.card K = 3
  · exact pPrimeCore_two_sl2_three h3
  · refine pPrimeCore_two_sl2_five hodd ?_
    obtain ⟨k, hk⟩ := hodd
    omega

theorem commute_of_normal_coprime_of_pPrimeCore_bot {Y : Type} [Group Y] {Q : Type} [Group Q]
    {K N : Subgroup Y} [K.Normal] [N.Normal] (e : ↥K ≃* Q) (hQ : pPrimeCore 2 Q = ⊥)
    (hN : Nat.Coprime 2 (Nat.card N)) {n a : Y} (hn : n ∈ N) (ha : a ∈ K) :
    n * a = a * n := by
  have hM : Nat.Coprime 2 (Nat.card (N.subgroupOf K)) :=
    Nat.Coprime.of_dvd_right
      (Subgroup.card_comap_dvd_of_injective N K.subtype K.subtype_injective) hN
  have hMQ : Nat.Coprime 2 (Nat.card ((N.subgroupOf K).map e.toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  have hbot := pPrimeCore_eq_bot_iff.mp hQ _
    (Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective) hMQ
  have hcK : n * a * n⁻¹ * a⁻¹ ∈ K :=
    K.mul_mem (Subgroup.Normal.conj_mem ‹K.Normal› a ha n) (K.inv_mem ha)
  have hcN : n * a * n⁻¹ * a⁻¹ ∈ N := by
    rw [show n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) by group]
    exact N.mul_mem hn (Subgroup.Normal.conj_mem ‹N.Normal› n⁻¹ (N.inv_mem hn) a)
  have hmem : e ⟨n * a * n⁻¹ * a⁻¹, hcK⟩ ∈ (N.subgroupOf K).map e.toMonoidHom :=
    ⟨⟨n * a * n⁻¹ * a⁻¹, hcK⟩, hcN, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 : (⟨n * a * n⁻¹ * a⁻¹, hcK⟩ : ↥K) = 1 := e.injective (hmem.trans (map_one e).symm)
  have h2 : n * a * n⁻¹ * a⁻¹ = 1 := congrArg Subtype.val h1
  have h3 : n * a * n⁻¹ = a := mul_inv_eq_one.mp h2
  calc n * a = n * a * n⁻¹ * n := by group
    _ = a * n := by rw [h3]

theorem sq_eq_one_of_forall_commute_sl2 {Y : Type} [Group Y] {F : Type} [Field F] {K : Subgroup Y}
    (e : ↥K ≃* SL(2, F)) {z : Y} (hzK : z ∈ K) (hz : e ⟨z, hzK⟩ = -1) (hzz : z * z = 1)
    {a : Y} (ha : a ∈ K) (hc : ∀ x ∈ K, a * x = x * a) : a * a = 1 := by
  have hcen : e ⟨a, ha⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro X
    obtain ⟨x, rfl⟩ := e.surjective X
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc x x.2).symm
  rcases eq_one_or_neg_one_of_mem_center hcen with h | h
  · have h1 : (⟨a, ha⟩ : ↥K) = 1 := e.injective (h.trans (map_one e).symm)
    have ha1 : a = 1 := congrArg Subtype.val h1
    rw [ha1]
    exact mul_one 1
  · have h1 : (⟨a, ha⟩ : ↥K) = ⟨z, hzK⟩ := e.injective (h.trans hz.symm)
    have haz : a = z := congrArg Subtype.val h1
    rw [haz]
    exact hzz

theorem mem_or_inv_mul_mem_of_sup_zpowers_eq_top {Y : Type} [Group Y] {J : Subgroup Y} [J.Normal]
    {t : Y} (ht : t * t = 1) (hgen : J ⊔ Subgroup.zpowers t = ⊤) (y : Y) :
    y ∈ J ∨ y⁻¹ * t ∈ J := by
  have hmem : QuotientGroup.mk' J y ∈ Subgroup.zpowers (QuotientGroup.mk' J t) := by
    have h1 : y ∈ J ⊔ Subgroup.zpowers t := by rw [hgen]; exact Subgroup.mem_top y
    have h2 := Subgroup.mem_map_of_mem (QuotientGroup.mk' J) h1
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq, MonoidHom.map_zpowers] at h2
  have hsq : QuotientGroup.mk' J t * QuotientGroup.mk' J t = 1 := by
    rw [← map_mul, ht, map_one]
  rcases mem_zpowers_of_sq hsq hmem with h | h
  · exact Or.inl ((QuotientGroup.eq_one_iff y).mp h)
  · exact Or.inr (QuotientGroup.eq.mp h)

theorem Shape.pPrimeCore_eq_bot {Y : Type} [Group Y] [Finite Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Finite F₁] [Finite F₂] (S : Shape Y F₁ F₂) (h₁ : Odd (Nat.card F₁)) (h₂ : Odd (Nat.card F₂)) :
    pPrimeCore 2 Y = ⊥ := by
  have hI₁ : S.I₁.Normal := S.normal₁
  have hI₂ : S.I₂.Normal := S.normal₂
  rw [pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have hc₁ : ∀ n ∈ N, ∀ a ∈ S.I₁, n * a = a * n := fun n hn a ha =>
    commute_of_normal_coprime_of_pPrimeCore_bot S.e₁ (pPrimeCore_two_sl2_odd h₁) hcop hn ha
  have hc₂ : ∀ n ∈ N, ∀ b ∈ S.I₂, n * b = b * n := fun n hn b hb =>
    commute_of_normal_coprime_of_pPrimeCore_bot S.e₂ (pPrimeCore_two_sl2_odd h₂) hcop hn hb
  have hnt : S.t ∉ S.I₁ ⊔ Subgroup.centralizer (S.I₁ : Set Y) :=
    S.act₁.t_not_mem_sup (L := Subgroup.centralizer (S.I₁ : Set Y))
      (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp hb) a ha) S.ns₁
  have hI₂L : S.I₂ ≤ Subgroup.centralizer (S.I₁ : Set Y) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => S.comm a ha b hb
  have hJ : (S.I₁ ⊔ S.I₂).Normal := inferInstance
  have hnJ : ∀ n ∈ N, n ∈ S.I₁ ⊔ S.I₂ := by
    intro n hn
    rcases mem_or_inv_mul_mem_of_sup_zpowers_eq_top (J := S.I₁ ⊔ S.I₂) S.t_sq S.gen n with h | h
    · exact h
    · exfalso
      apply hnt
      have hnL : n ∈ Subgroup.centralizer (S.I₁ : Set Y) :=
        Subgroup.mem_centralizer_iff.mpr fun a ha => (hc₁ n hn a ha).symm
      have hJle : S.I₁ ⊔ S.I₂ ≤ S.I₁ ⊔ Subgroup.centralizer (S.I₁ : Set Y) :=
        sup_le le_sup_left (hI₂L.trans le_sup_right)
      have ht : S.t = n * (n⁻¹ * S.t) := by group
      rw [ht]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hnL) (hJle h)
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute S.comm (hnJ n hn)
  have hcomm_ab : b * a = a * b := (S.comm a ha b hb).symm
  have ha₁ : a * a = 1 := by
    refine sq_eq_one_of_forall_commute_sl2 S.e₁ S.z_mem₁ S.e₁_z S.z_sq ha fun x hx => ?_
    have h1 := hc₁ (a * b) hn x hx
    have h2 : b * x = x * b := (S.comm x hx b hb).symm
    have h3 : a * x * b = x * a * b := by
      calc a * x * b = a * (x * b) := by rw [mul_assoc]
        _ = a * (b * x) := by rw [h2]
        _ = a * b * x := by rw [mul_assoc]
        _ = x * (a * b) := h1
        _ = x * a * b := by rw [mul_assoc]
    exact mul_right_cancel h3
  have hb₁ : b * b = 1 := by
    refine sq_eq_one_of_forall_commute_sl2 S.e₂ S.z_mem₂ S.e₂_z S.z_sq hb fun x hx => ?_
    have h1 := hc₂ (a * b) hn x hx
    have h2 : a * x = x * a := S.comm a ha x hx
    have h3 : a * (b * x) = a * (x * b) := by
      calc a * (b * x) = a * b * x := by rw [mul_assoc]
        _ = x * (a * b) := h1
        _ = x * a * b := by rw [mul_assoc]
        _ = a * x * b := by rw [h2]
        _ = a * (x * b) := by rw [mul_assoc]
    exact mul_left_cancel h3
  have hn2 : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm_ab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha₁, hb₁, mul_one]
  have h2 : orderOf (a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hn2)
  have h3 : orderOf (a * b) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
  have h4 : orderOf (a * b) ∣ Nat.gcd 2 (Nat.card N) := Nat.dvd_gcd h2 h3
  rw [hcop] at h4
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
