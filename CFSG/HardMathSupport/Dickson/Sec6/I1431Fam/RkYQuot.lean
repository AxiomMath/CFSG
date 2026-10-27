module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open

theorem RkY.card_le_quotient {Y : Type} [Group Y] [Finite Y] (h : RkY Y)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center Y)) {U E : Subgroup (Y ⧸ Subgroup.center Y)}
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hE : E ≤ Subgroup.normalizer (U : Set (Y ⧸ Subgroup.center Y)))
    (hEa : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπZ : ∀ y, π y = 1 → y ∈ Subgroup.center Y := fun y hy => (QuotientGroup.eq_one_iff y).1 hy
  set Ut : Subgroup Y := U.comap π with hUt
  set Et : Subgroup Y := E.comap π with hEt
  haveI hUnil : Group.IsNilpotent U := hU2.isNilpotent
  have hnil : Group.IsNilpotent Ut := by
    refine Subgroup.isNilpotent_of_ker_le_center ((π.comp Ut.subtype).codRestrict U (fun x => x.2)) ?_
    intro x hx
    have h1 : π (x : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 := Subgroup.mem_center_iff.1 (hπZ _ h1)
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (h2 (g : Y))
  obtain ⟨P⟩ : Nonempty (Sylow 2 Ut) := inferInstance
  haveI : (P : Subgroup Ut).Normal := inferInstance
  haveI : Unique (Sylow 2 Ut) := Sylow.unique_of_normal P inferInstance
  have hPiff : ∀ x : Ut, x ∈ (P : Subgroup Ut) ↔ ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    · rintro ⟨k, hk⟩
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
      have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
        IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers]; exact hj)
      obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
      have hQP : Q = P := Subsingleton.elim _ _
      subst hQP
      exact hQ (Subgroup.mem_zpowers x)
  let U₂ : Subgroup Y := (P : Subgroup Ut).map Ut.subtype
  have hU₂mem : ∀ y : Y, y ∈ U₂ ↔ y ∈ Ut ∧ ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := (hPiff x).1 hx
      exact ⟨x.2, k, by simpa using congrArg Subtype.val hk⟩
    · rintro ⟨hy, k, hk⟩
      exact ⟨⟨y, hy⟩, (hPiff ⟨y, hy⟩).2 ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩
  have hU₂p : IsPGroup 2 U₂ := P.isPGroup'.map Ut.subtype
  have hdvd : Nat.card U ∣ Nat.card Ut := by
    have h1 := Subgroup.card_map_dvd (H := Ut) π
    rwa [Subgroup.map_comap_eq_self_of_surjective hπ] at h1
  have h2U : 2 ∣ Nat.card U := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (Subgroup.eq_bot_of_card_eq U (by rw [hk]; rfl)) hU
    · rw [hk]; exact dvd_pow_self 2 hk0.ne'
  have hP2 : 2 ∣ Nat.card P := by
    have h1 : 2 ^ 1 ∣ Nat.card Ut := by simpa using h2U.trans hdvd
    simpa using P.pow_dvd_card_of_pow_dvd_card h1
  have hU₂ne : U₂ ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card U₂ = Nat.card P := Subgroup.card_map_of_injective Ut.subtype_injective
    rw [hbot, Subgroup.card_bot] at h1
    rw [← h1] at hP2
    exact absurd (Nat.le_of_dvd one_pos hP2) (by norm_num)
  have hEtU : ∀ g ∈ Et, ∀ y : Y, y ∈ Ut → g * y * g⁻¹ ∈ Ut := by
    intro g hg y hy
    have hg' : π g ∈ E := hg
    have hy' : π y ∈ U := hy
    have := (Subgroup.mem_normalizer_iff.1 (hE hg') (π y)).1 hy'
    change π (g * y * g⁻¹) ∈ U
    simpa [map_mul, map_inv] using this
  have hconj2 : ∀ g ∈ Et, ∀ y ∈ U₂, g * y * g⁻¹ ∈ U₂ := by
    intro g hg y hy
    obtain ⟨hyU, k, hk⟩ := (hU₂mem y).1 hy
    refine (hU₂mem _).2 ⟨hEtU g hg y hyU, k, ?_⟩
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  have hEtnorm : Et ≤ Subgroup.normalizer (U₂ : Set Y) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => hconj2 g hg y hy
    · intro hy
      have := hconj2 g⁻¹ (Et.inv_mem hg) _ hy
      simpa [mul_assoc] using this
  obtain ⟨R⟩ : Nonempty (Sylow 3 Et) := inferInstance
  let E₃ : Subgroup Y := (R : Subgroup Et).map Et.subtype
  have hE₃p : IsPGroup 3 E₃ := R.isPGroup'.map Et.subtype
  have hE₃le : E₃ ≤ Et := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have htriv : ∀ s ∈ E₃, s ∈ Subgroup.center Y → s = 1 := by
    intro s hs hsZ
    obtain ⟨n, hn⟩ := hE₃p ⟨s, hs⟩
    have hn' : s ^ (3 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have h1 : orderOf s ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn'
    have h2 : orderOf s ∣ Nat.card (Subgroup.center Y) := by
      have := orderOf_dvd_natCard (⟨s, hsZ⟩ : Subgroup.center Y)
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    by_contra hs1
    have hne : orderOf s ≠ 1 := fun h1 => hs1 (orderOf_eq_one_iff.1 h1)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hj)
    exact hZ ((dvd_pow_self 3 hj0).trans (hj ▸ h2))
  have hE₃π : ∀ x ∈ E₃, π x ∈ E := fun x hx => hE₃le hx
  have hE₃comm : ∀ s ∈ E₃, ∀ t ∈ E₃, s * t = t * s := by
    intro s hs t ht
    have hc : s * t * s⁻¹ * t⁻¹ ∈ E₃ :=
      E₃.mul_mem (E₃.mul_mem (E₃.mul_mem hs ht) (E₃.inv_mem hs)) (E₃.inv_mem ht)
    have h1 : π (s * t * s⁻¹ * t⁻¹) = 1 := by
      have : π s * π t = π t * π s :=
        congrArg Subtype.val (hEa.1.is_comm.comm ⟨π s, hE₃π s hs⟩ ⟨π t, hE₃π t ht⟩)
      simp only [map_mul, map_inv]
      rw [this]
      group
    have h2 := htriv _ hc (hπZ _ h1)
    calc s * t = s * t * s⁻¹ * t⁻¹ * (t * s) := by group
      _ = t * s := by rw [h2, one_mul]
  have hE₃exp : ∀ s ∈ E₃, s ^ 3 = 1 := by
    intro s hs
    refine htriv _ (E₃.pow_mem hs 3) (hπZ _ ?_)
    rw [map_pow]
    exact hEa.2 _ (hE₃π s hs)
  have hE₃ea : IsElemAbelian 3 E₃ :=
    ⟨⟨⟨fun a b => Subtype.ext (hE₃comm a a.2 b b.2)⟩⟩, hE₃exp⟩
  have hE₃bot : E₃ ⊓ Subgroup.center Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    exact fun x hx => htriv x hx.1 hx.2
  have h3 := (h U₂ hU₂ne hU₂p E₃ (hE₃le.trans hEtnorm) hE₃ea).2 hE₃bot
  have hdvdE : Nat.card E ∣ Nat.card Et := by
    have h1 := Subgroup.card_map_dvd (H := Et) π
    rwa [Subgroup.map_comap_eq_self_of_surjective hπ] at h1
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEa.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have hR : 3 ^ k ∣ Nat.card R := R.pow_dvd_card_of_pow_dvd_card (hk ▸ hdvdE)
  have hE₃card : Nat.card E₃ = Nat.card R := Subgroup.card_map_of_injective Et.subtype_injective
  rw [hk]
  exact (Nat.le_of_dvd Nat.card_pos hR).trans (hE₃card ▸ h3)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
