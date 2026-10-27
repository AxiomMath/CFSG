module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open MulAction

@[expose] def IsZSharp {K : Type*} [Group K] (Q : Subgroup K) (w : K) : Prop :=
  w ∈ Q ∧ (∀ x ∈ Q, x * w = w * x) ∧ w ≠ 1

structure SzSetting (K : Type*) [Group K] [Finite K] (q : ℕ) : Prop where
  three_le : 3 ≤ q
  card : Nat.card K = q ^ 2 * (q ^ 2 + 1) * (q - 1)
  syl_card : ∀ Q : Sylow 2 K, Nat.card (Q : Subgroup K) = q ^ 2
  ne_top : ∀ Q : Sylow 2 K, Subgroup.normalizer (Q : Set K) ≠ ⊤
  odd_inter : ∀ Q Q' : Sylow 2 K, Q ≠ Q' →
    Odd (Nat.card ↥(Subgroup.normalizer (Q : Set K) ⊓ Subgroup.normalizer (Q' : Set K)))
  inv_central : ∀ (Q : Sylow 2 K) (x : K), x ∈ (Q : Subgroup K) → x * x = 1 →
    ∀ y ∈ (Q : Subgroup K), x * y = y * x
  card_zsharp : ∀ Q : Sylow 2 K, Nat.card {w : K // IsZSharp (Q : Subgroup K) w} = q - 1
  trans : ∀ (Q : Sylow 2 K) (x y : K), IsZSharp (Q : Subgroup K) x → IsZSharp (Q : Subgroup K) y →
    ∃ g ∈ Subgroup.normalizer (Q : Set K), g * x * g⁻¹ = y
  cent_le : ∀ (Q : Sylow 2 K) (t : K), t ∈ (Q : Subgroup K) → t * t = 1 → t ≠ 1 →
    Subgroup.centralizer ({t} : Set K) ≤ Subgroup.normalizer (Q : Set K)

section Helper

variable {K : Type*} [Group K]

theorem card_mul_card_stab {H : Subgroup K} {S : Set K} {u : K}
    (hS : ∀ h ∈ H, ∀ x ∈ S, h * x * h⁻¹ ∈ S) (hu : u ∈ S)
    (htr : ∀ x ∈ S, ∃ h ∈ H, h * u * h⁻¹ = x) :
    Nat.card ↥S * Nat.card ↥(H ⊓ Subgroup.centralizer ({u} : Set K)) = Nat.card ↥H := by
  classical
  let _ : MulAction ↥H ↥S :=
    { smul := fun h x => ⟨h * x * h⁻¹, hS h h.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : ↥H) : K) * (x : K) * ((1 : ↥H) : K)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change ((a * b : ↥H) : K) * (x : K) * ((a * b : ↥H) : K)⁻¹ =
          (a : K) * ((b : K) * (x : K) * (b : K)⁻¹) * (a : K)⁻¹
        simp [mul_assoc]) }
  let x₀ : ↥S := ⟨u, hu⟩
  have hpre : IsPretransitive ↥H ↥S := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨h₁, hh₁, e₁⟩ := htr x x.2
    obtain ⟨h₂, hh₂, e₂⟩ := htr y y.2
    refine ⟨⟨h₂ * h₁⁻¹, H.mul_mem hh₂ (H.inv_mem hh₁)⟩, Subtype.ext ?_⟩
    change h₂ * h₁⁻¹ * (x : K) * (h₂ * h₁⁻¹)⁻¹ = y
    rw [← e₁, ← e₂]
    group
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥H x₀)
  rw [MulAction.index_stabilizer_of_transitive ↥H x₀] at h1
  have hst : Nat.card ↥(MulAction.stabilizer ↥H x₀) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({u} : Set K)) := by
    refine Nat.card_congr
      { toFun := fun h => ⟨(h.1 : K), Subgroup.mem_inf.2 ⟨h.1.2, ?_⟩⟩
        invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, ?_⟩
        left_inv := fun h => rfl
        right_inv := fun x => rfl }
    · have := h.2
      rw [MulAction.mem_stabilizer_iff] at this
      have h2 : (h.1 : K) * u * (h.1 : K)⁻¹ = u := congrArg Subtype.val this
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc (h.1 : K) * u = (h.1 * u * (h.1 : K)⁻¹) * h.1 := by group
        _ = u * h.1 := by rw [h2]
    · rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2
      change (x.1 : K) * u * (x.1 : K)⁻¹ = u
      calc x.1 * u * x.1⁻¹ = (u * x.1) * x.1⁻¹ := by rw [this]
        _ = u := by group
  rw [hst] at h1
  rw [mul_comm] at h1
  exact h1

end Helper

section Main

variable {K : Type*} [Group K] [Finite K] {q : ℕ} (H : SzSetting K q)

local notation "Nq" Q => Subgroup.normalizer ((Q : Subgroup K) : Set K)

include H in
theorem eq_one_of_mem_normalizer {Q Q' : Sylow 2 K} (h : Q ≠ Q') {u : K}
    (hu : u ∈ (Q : Subgroup K)) (hu' : u ∈ Nq Q') : u = 1 := by
  have huN : u ∈ Nq Q := Subgroup.le_normalizer hu
  have hmem : u ∈ (Nq Q) ⊓ (Nq Q') := ⟨huN, hu'⟩
  have hodd := H.odd_inter Q Q' h
  have h1 : orderOf u ∣ Nat.card ↥((Nq Q) ⊓ (Nq Q')) := Subgroup.orderOf_dvd_natCard _ hmem
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 Q.isPGroup') ⟨u, hu⟩
  have h2 : orderOf u = 2 ^ k := by simpa using hk
  have h3 : Odd (orderOf u) := Odd.of_dvd_nat hodd h1
  rw [h2] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    have h4 : Even (2 ^ k) := Nat.even_pow.2 ⟨even_two, hk0⟩
    exact (Nat.not_even_iff_odd.2 h3) h4
  rw [hk0] at h2
  exact orderOf_eq_one_iff.1 (by simpa using h2)

include H in
theorem exists_ne_sylow (Q : Sylow 2 K) : ∃ Q' : Sylow 2 K, Q' ≠ Q := by
  by_contra hcon
  have hall : ∀ Q' : Sylow 2 K, Q' = Q := fun Q' => by
    by_contra h
    exact hcon ⟨Q', h⟩
  apply H.ne_top Q
  rw [eq_top_iff]
  intro g _
  rw [← Sylow.smul_eq_iff_mem_normalizer]
  exact hall _

include H in
theorem card_sylow_ge (Q : Sylow 2 K) : q ^ 2 + 1 ≤ Nat.card (Sylow 2 K) := by
  classical
  obtain ⟨Q₁, hQ₁⟩ := exists_ne_sylow H Q
  let g : Option ↥(Q : Subgroup K) → Sylow 2 K :=
    fun o => o.elim Q (fun u => (u : K) • Q₁)
  have hinj : Function.Injective g := by
    intro a b hab
    rcases a with _ | u <;> rcases b with _ | u'
    · rfl
    · exfalso
      have h1 : Q = (u' : K) • Q₁ := hab
      have h2 : Q₁ = ((u' : K)⁻¹) • Q := by
        calc Q₁ = ((u' : K)⁻¹) • ((u' : K) • Q₁) := (inv_smul_smul _ _).symm
          _ = ((u' : K)⁻¹) • Q := by rw [← h1]
      apply hQ₁
      rw [h2]
      exact Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.inv_mem _ (Subgroup.le_normalizer u'.2))
    · exfalso
      have h1 : (u : K) • Q₁ = Q := hab
      have h2 : Q₁ = ((u : K)⁻¹) • Q := by
        calc Q₁ = ((u : K)⁻¹) • ((u : K) • Q₁) := (inv_smul_smul _ _).symm
          _ = ((u : K)⁻¹) • Q := by rw [h1]
      apply hQ₁
      rw [h2]
      exact Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.inv_mem _ (Subgroup.le_normalizer u.2))
    · have h1 : (u : K) • Q₁ = (u' : K) • Q₁ := hab
      have h2 : ((u : K)⁻¹ * u') • Q₁ = Q₁ := by
        rw [mul_smul, ← h1, inv_smul_smul]
      have h3 := eq_one_of_mem_normalizer H (Q := Q) (Q' := Q₁) hQ₁.symm
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ u.2) u'.2)
        (Sylow.smul_eq_iff_mem_normalizer.1 h2)
      have h4 : (u : K) = u' := by
        rw [inv_mul_eq_one] at h3
        exact h3
      rw [Subtype.ext h4]
  have := Nat.card_le_card_of_injective g hinj
  have hopt : Nat.card (Option ↥(Q : Subgroup K)) = Nat.card ↥(Q : Subgroup K) + 1 := by
    have := Fintype.ofFinite ↥(Q : Subgroup K)
    simp [Nat.card_eq_fintype_card, Fintype.card_option]
  rwa [hopt, H.syl_card Q] at this

omit H in
theorem card_sylow_mul_card_normalizer (Q : Sylow 2 K) :
    Nat.card (Sylow 2 K) * Nat.card ↥(Nq Q) = Nat.card K := by
  rw [Sylow.card_eq_index_normalizer Q, mul_comm]
  exact Subgroup.card_mul_index _

omit [Finite K] H in
theorem conj_isZSharp {Q : Sylow 2 K} {h x : K} (hh : h ∈ Nq Q)
    (hx : IsZSharp (Q : Subgroup K) x) : IsZSharp (Q : Subgroup K) (h * x * h⁻¹) := by
  obtain ⟨hxQ, hxc, hx1⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.1 hh x).1 hxQ, fun y hy => ?_, ?_⟩
  · have hy' : h⁻¹ * y * h ∈ (Q : Subgroup K) :=
      (Subgroup.mem_normalizer_iff.1 hh (h⁻¹ * y * h)).2 (by simpa [mul_assoc] using hy)
    have hc := hxc _ hy'
    calc y * (h * x * h⁻¹) = h * ((h⁻¹ * y * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * y * h)) * h⁻¹ := by rw [hc]
      _ = (h * x * h⁻¹) * y := by group
  · intro h1
    apply hx1
    have h2 : h⁻¹ * (h * x * h⁻¹) * h = 1 := by rw [h1]; group
    simpa [mul_assoc] using h2

include H in
theorem card_normalizer_cent (Q : Sylow 2 K) :
    Nat.card ↥(Nq Q) = q ^ 2 * (q - 1) ∧ Nat.card (Sylow 2 K) = q ^ 2 + 1 ∧
      ∀ u, IsZSharp (Q : Subgroup K) u →
        (Nq Q) ⊓ Subgroup.centralizer ({u} : Set K) = (Q : Subgroup K) := by
  have hq3 := H.three_le
  have hZ := H.card_zsharp Q
  have hQcard := H.syl_card Q
  have key : ∀ u, IsZSharp (Q : Subgroup K) u →
      (q - 1) * Nat.card ↥((Nq Q) ⊓ Subgroup.centralizer ({u} : Set K)) = Nat.card ↥(Nq Q) := by
    intro u hu
    have := card_mul_card_stab (H := Nq Q) (S := {w | IsZSharp (Q : Subgroup K) w}) (u := u)
      (fun h hh x hx => conj_isZSharp hh hx) hu (fun x hx => H.trans Q u x hu hx)
    have hS : Nat.card ↥{w | IsZSharp (Q : Subgroup K) w} = q - 1 := hZ
    rw [hS] at this
    exact this
  have hQle : ∀ u, IsZSharp (Q : Subgroup K) u →
      (Q : Subgroup K) ≤ (Nq Q) ⊓ Subgroup.centralizer ({u} : Set K) := by
    intro u hu x hx
    refine ⟨Subgroup.le_normalizer hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact hu.2.1 x hx
  have hCge : ∀ u, IsZSharp (Q : Subgroup K) u →
      q ^ 2 ≤ Nat.card ↥((Nq Q) ⊓ Subgroup.centralizer ({u} : Set K)) := by
    intro u hu
    rw [← hQcard]
    exact Subgroup.card_le_of_le (hQle u hu)
  have hpos : 0 < Nat.card {w : K // IsZSharp (Q : Subgroup K) w} := by rw [hZ]; omega
  obtain ⟨⟨u₀, hu₀⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  have hNge : q ^ 2 * (q - 1) ≤ Nat.card ↥(Nq Q) := by
    have h2 : (q - 1) * q ^ 2 ≤ (q - 1) *
        Nat.card ↥((Nq Q) ⊓ Subgroup.centralizer ({u₀} : Set K)) :=
      Nat.mul_le_mul_left _ (hCge u₀ hu₀)
    rw [mul_comm]
    exact h2.trans (key u₀ hu₀).le
  have hmul := card_sylow_mul_card_normalizer (K := K) Q
  have hge := card_sylow_ge H Q
  have hNle : Nat.card ↥(Nq Q) ≤ q ^ 2 * (q - 1) := by
    have h1 : (q ^ 2 + 1) * Nat.card ↥(Nq Q) ≤ Nat.card (Sylow 2 K) * Nat.card ↥(Nq Q) :=
      Nat.mul_le_mul_right _ hge
    rw [hmul, H.card] at h1
    have h2 : (q ^ 2 + 1) * Nat.card ↥(Nq Q) ≤ (q ^ 2 + 1) * (q ^ 2 * (q - 1)) := by
      calc (q ^ 2 + 1) * Nat.card ↥(Nq Q) ≤ q ^ 2 * (q ^ 2 + 1) * (q - 1) := h1
        _ = (q ^ 2 + 1) * (q ^ 2 * (q - 1)) := by ring
    exact Nat.le_of_mul_le_mul_left h2 (by positivity)
  have hN : Nat.card ↥(Nq Q) = q ^ 2 * (q - 1) := le_antisymm hNle hNge
  have hqm : 0 < q ^ 2 * (q - 1) := by
    have : 0 < q - 1 := by omega
    positivity
  refine ⟨hN, ?_, ?_⟩
  · rw [hN, H.card] at hmul
    have h2 : Nat.card (Sylow 2 K) * (q ^ 2 * (q - 1)) = (q ^ 2 + 1) * (q ^ 2 * (q - 1)) := by
      rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_right hqm h2
  · intro u hu
    have h1 := key u hu
    rw [hN] at h1
    have h2 : Nat.card ↥((Nq Q) ⊓ Subgroup.centralizer ({u} : Set K)) = q ^ 2 := by
      have : (q - 1) * Nat.card ↥((Nq Q) ⊓ Subgroup.centralizer ({u} : Set K)) =
          (q - 1) * q ^ 2 := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    symm
    exact Subgroup.eq_of_le_of_card_ge (hQle u hu) (by rw [h2, hQcard])

include H in
theorem card_ne_sylow (Q : Sylow 2 K) : Nat.card {P : Sylow 2 K // P ≠ Q} = q ^ 2 := by
  classical
  have h1 := (card_normalizer_cent H Q).2.1
  have : Fintype (Sylow 2 K) := Fintype.ofFinite _
  have h2 : Nat.card {P : Sylow 2 K // P ≠ Q} = Nat.card (Sylow 2 K) - 1 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  omega

include H in
theorem exists_smul_eq_of_ne {Q Q₁ Q₂ : Sylow 2 K} (h₁ : Q₁ ≠ Q) (h₂ : Q₂ ≠ Q) :
    ∃ u ∈ (Q : Subgroup K), u • Q₁ = Q₂ := by
  classical
  have hne : ∀ u : ↥(Q : Subgroup K), (u : K) • Q₁ ≠ Q := fun u h => h₁ (by
    have h3 : Q₁ = ((u : K)⁻¹) • Q := by
      calc Q₁ = ((u : K)⁻¹) • ((u : K) • Q₁) := (inv_smul_smul _ _).symm
        _ = ((u : K)⁻¹) • Q := by rw [h]
    rw [h3]
    exact Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.inv_mem _ (Subgroup.le_normalizer u.2)))
  let f : ↥(Q : Subgroup K) → {P : Sylow 2 K // P ≠ Q} := fun u => ⟨(u : K) • Q₁, hne u⟩
  have hinj : Function.Injective f := by
    intro u u' h
    have h1 : (u : K) • Q₁ = (u' : K) • Q₁ := congrArg Subtype.val h
    have h2 : ((u : K)⁻¹ * u') • Q₁ = Q₁ := by
      rw [mul_smul, ← h1, inv_smul_smul]
    have h3 := eq_one_of_mem_normalizer H (Q := Q) (Q' := Q₁) h₁.symm
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ u.2) u'.2)
      (Sylow.smul_eq_iff_mem_normalizer.1 h2)
    rw [inv_mul_eq_one] at h3
    exact Subtype.ext h3
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [card_ne_sylow H Q, H.syl_card Q])
  obtain ⟨u, hu⟩ := hbij.2 ⟨Q₂, h₂⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

include H in
theorem eq_one_of_fixes_three {Q₀ Q₁ Q₂ : Sylow 2 K} (h01 : Q₁ ≠ Q₀) (h02 : Q₂ ≠ Q₀)
    (h12 : Q₁ ≠ Q₂) {y : K} (hy₀ : y ∈ Nq Q₀) (hy₁ : y ∈ Nq Q₁) (hy₂ : y ∈ Nq Q₂) : y = 1 := by
  obtain ⟨u, hu, huQ⟩ := exists_smul_eq_of_ne H h01 h02
  have hyu : y * u * y⁻¹ ∈ (Q₀ : Subgroup K) := (Subgroup.mem_normalizer_iff.1 hy₀ u).1 hu
  have hc : u⁻¹ * (y * u * y⁻¹) ∈ (Q₀ : Subgroup K) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hyu
  have hy₁s : y • Q₁ = Q₁ := Sylow.smul_eq_iff_mem_normalizer.2 hy₁
  have hy₂s : y • Q₂ = Q₂ := Sylow.smul_eq_iff_mem_normalizer.2 hy₂
  have hyinv : y⁻¹ • Q₁ = Q₁ := by
    rw [inv_smul_eq_iff]; exact hy₁s.symm
  have h1 : (y * u * y⁻¹) • Q₁ = Q₂ := by
    rw [mul_smul, mul_smul, hyinv, huQ, hy₂s]
  have hcQ : (u⁻¹ * (y * u * y⁻¹)) • Q₁ = Q₁ := by
    rw [mul_smul, h1, ← huQ, inv_smul_smul]
  have hc1 : u⁻¹ * (y * u * y⁻¹) = 1 :=
    eq_one_of_mem_normalizer H (Q := Q₀) (Q' := Q₁) h01.symm hc
      (Sylow.smul_eq_iff_mem_normalizer.1 hcQ)
  have hyu' : y * u * y⁻¹ = u := by
    rw [inv_mul_eq_one] at hc1
    exact hc1.symm
  have hcomm : y * u = u * y := by
    calc y * u = (y * u * y⁻¹) * y := by group
      _ = u * y := by rw [hyu']
  have hu1 : u ≠ 1 := fun h => h12 (by rw [h, one_smul] at huQ; exact huQ)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 Q₀.isPGroup') ⟨u, hu⟩
  have hk' : orderOf u = 2 ^ k := by simpa using hk
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      apply hu1
      rw [h0] at hk'
      exact orderOf_eq_one_iff.1 (by simpa using hk')
    · exact h0
  have hdvd : 2 ^ (k - 1) ∣ orderOf u := by
    rw [hk']
    exact pow_dvd_pow 2 (Nat.sub_le k 1)
  have hu₁ord : orderOf (u ^ (2 ^ (k - 1))) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hk',
      Nat.pow_div (Nat.sub_le k 1) (by norm_num)]
    have : k - (k - 1) = 1 := by omega
    rw [this]
  have hu₁sq : u ^ (2 ^ (k - 1)) * u ^ (2 ^ (k - 1)) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hu₁ord]
  have hu₁ne : u ^ (2 ^ (k - 1)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu₁ord
    exact absurd hu₁ord (by norm_num)
  have hu₁Q : u ^ (2 ^ (k - 1)) ∈ (Q₀ : Subgroup K) := Subgroup.pow_mem _ hu _
  have hz : IsZSharp (Q₀ : Subgroup K) (u ^ (2 ^ (k - 1))) :=
    ⟨hu₁Q, fun x hx => (H.inv_central Q₀ _ hu₁Q hu₁sq x hx).symm, hu₁ne⟩
  have hyc : y ∈ Subgroup.centralizer ({u ^ (2 ^ (k - 1))} : Set K) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    exact ((Commute.pow_right (show Commute y u from hcomm) (2 ^ (k - 1)))).eq
  have hyQ : y ∈ (Q₀ : Subgroup K) := by
    have := (card_normalizer_cent H Q₀).2.2 _ hz
    rw [← this]
    exact ⟨hy₀, hyc⟩
  exact eq_one_of_mem_normalizer H (Q := Q₀) (Q' := Q₁) h01.symm hyQ hy₁

include H in
theorem exists_swap {Q₀ Q₁ : Sylow 2 K} (h : Q₀ ≠ Q₁) :
    ∃ g : K, g • Q₀ = Q₁ ∧ g • Q₁ = Q₀ := by
  obtain ⟨g₁, hg₁⟩ := exists_smul_eq K Q₀ Q₁
  have hne : g₁ • Q₁ ≠ Q₁ := by
    intro h2
    have h3 : g₁⁻¹ • Q₁ = Q₁ := by rw [inv_smul_eq_iff]; exact h2.symm
    apply h
    calc Q₀ = g₁⁻¹ • (g₁ • Q₀) := (inv_smul_smul _ _).symm
      _ = g₁⁻¹ • Q₁ := by rw [hg₁]
      _ = Q₁ := h3
  obtain ⟨u, hu, huQ⟩ := exists_smul_eq_of_ne H (Q := Q₁) (Q₁ := g₁ • Q₁) (Q₂ := Q₀) hne h
  refine ⟨u * g₁, ?_, ?_⟩
  · rw [mul_smul, hg₁]
    exact Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hu)
  · rw [mul_smul]
    exact huQ

include H in
theorem exists_swap_involution {Q₀ Q₁ : Sylow 2 K} (h : Q₀ ≠ Q₁) :
    ∃ w : K, w * w = 1 ∧ w • Q₀ = Q₁ ∧ w • Q₁ = Q₀ := by
  obtain ⟨g, hg₀, hg₁⟩ := exists_swap H h
  have hsq₀ : (g * g) • Q₀ = Q₀ := by rw [mul_smul, hg₀, hg₁]
  have hsq₁ : (g * g) • Q₁ = Q₁ := by rw [mul_smul, hg₁, hg₀]
  have hN₀ : g * g ∈ Nq Q₀ := Sylow.smul_eq_iff_mem_normalizer.1 hsq₀
  have hN₁ : g * g ∈ Nq Q₁ := Sylow.smul_eq_iff_mem_normalizer.1 hsq₁
  have hodd := H.odd_inter Q₀ Q₁ h
  have hordodd : Odd (orderOf (g * g)) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ ⟨hN₀, hN₁⟩)
  obtain ⟨j, hj⟩ := hordodd
  have hpow : g ^ orderOf (g * g) = (g * g) ^ j * g := by
    rw [hj, pow_succ, pow_mul, pow_two]
  have hj₀ : ((g * g) ^ j) • Q₀ = Q₀ :=
    Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.pow_mem _ hN₀ j)
  have hj₁ : ((g * g) ^ j) • Q₁ = Q₁ :=
    Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.pow_mem _ hN₁ j)
  refine ⟨g ^ orderOf (g * g), ?_, ?_, ?_⟩
  · rw [← pow_add, ← two_mul, pow_mul, pow_two, pow_orderOf_eq_one]
  · rw [hpow, mul_smul, hg₀, hj₁]
  · rw [hpow, mul_smul, hg₁, hj₀]

omit [Finite K] H in
theorem isPGroup_two_zpowers_of_mul_self {b : K} (hb : b * b = 1) :
    IsPGroup 2 (Subgroup.zpowers b) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hb2 : b ^ 2 = 1 := by rw [pow_two]; exact hb
  rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hb2]

include H in
theorem exists_inverted_pair {Q₀ Q₁ : Sylow 2 K} (h : Q₀ ≠ Q₁) :
    ∃ y w : K, y ∈ (Nq Q₀) ∧ y ∈ (Nq Q₁) ∧ y ≠ 1 ∧ w * w = 1 ∧ w * y * w⁻¹ = y⁻¹ := by
  classical
  have hq3 := H.three_le
  obtain ⟨w, hww, hw₀, hw₁⟩ := exists_swap_involution H h
  have hwinv₀ : w⁻¹ • Q₀ = Q₁ := by rw [inv_smul_eq_iff]; exact hw₁.symm
  have hwinv₁ : w⁻¹ • Q₁ = Q₀ := by rw [inv_smul_eq_iff]; exact hw₀.symm
  have hY : ∃ y₀ ∈ (Nq Q₀) ⊓ (Nq Q₁), y₀ ≠ 1 := by
    by_contra hcon
    have hall : ∀ y ∈ (Nq Q₀) ⊓ (Nq Q₁), y = 1 := fun y hy => by
      by_contra hne
      exact hcon ⟨y, hy, hne⟩
    have hne : ∀ n : ↥(Nq Q₀), (n : K) • Q₁ ≠ Q₀ := fun n hn => h (by
      have h3 : Q₁ = ((n : K)⁻¹) • Q₀ := by
        calc Q₁ = ((n : K)⁻¹) • ((n : K) • Q₁) := (inv_smul_smul _ _).symm
          _ = ((n : K)⁻¹) • Q₀ := by rw [hn]
      have h4 : ((n : K)⁻¹) • Q₀ = Q₀ :=
        Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.inv_mem _ n.2)
      rw [h3, h4])
    let f : ↥(Nq Q₀) → {P : Sylow 2 K // P ≠ Q₀} := fun n => ⟨(n : K) • Q₁, hne n⟩
    have hinj : Function.Injective f := by
      intro n n' hnn
      have h1 : (n : K) • Q₁ = (n' : K) • Q₁ := congrArg Subtype.val hnn
      have h2 : ((n : K)⁻¹ * n') • Q₁ = Q₁ := by rw [mul_smul, ← h1, inv_smul_smul]
      have h3 := hall _ ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ n.2) n'.2,
        Sylow.smul_eq_iff_mem_normalizer.1 h2⟩
      rw [inv_mul_eq_one] at h3
      exact Subtype.ext h3
    have hle := Nat.card_le_card_of_injective f hinj
    rw [(card_normalizer_cent H Q₀).1, card_ne_sylow H Q₀] at hle
    have : 0 < q ^ 2 := by positivity
    have h5 : 2 * q ^ 2 ≤ q ^ 2 * (q - 1) := by
      have : 2 ≤ q - 1 := by omega
      nlinarith
    omega
  obtain ⟨y₀, hy₀mem, hy₀ne⟩ := hY
  obtain ⟨hy₀₀, hy₀₁⟩ := hy₀mem
  have hy₀s₀ : y₀ • Q₀ = Q₀ := Sylow.smul_eq_iff_mem_normalizer.2 hy₀₀
  have hy₀s₁ : y₀ • Q₁ = Q₁ := Sylow.smul_eq_iff_mem_normalizer.2 hy₀₁
  have hwc₀ : (w * y₀ * w⁻¹) ∈ Nq Q₀ := by
    apply Sylow.smul_eq_iff_mem_normalizer.1
    rw [mul_smul, mul_smul, hwinv₀, hy₀s₁, hw₁]
  have hwc₁ : (w * y₀ * w⁻¹) ∈ Nq Q₁ := by
    apply Sylow.smul_eq_iff_mem_normalizer.1
    rw [mul_smul, mul_smul, hwinv₁, hy₀s₀, hw₀]
  have hnc : w * y₀ * w⁻¹ ≠ y₀ := by
    intro heq
    have hcomm : y₀ * w = w * y₀ := by
      calc y₀ * w = (w * y₀ * w⁻¹) * w := by rw [heq]
        _ = w * y₀ := by group
    have hw1 : w ≠ 1 := by
      intro h1
      rw [h1, one_smul] at hw₀
      exact h hw₀
    obtain ⟨Qw, hQw⟩ := (isPGroup_two_zpowers_of_mul_self hww).exists_le_sylow
    have hwQ : w ∈ (Qw : Subgroup K) := hQw (Subgroup.mem_zpowers w)
    have hy₀w : y₀ ∈ Nq Qw := H.cent_le Qw w hwQ hww hw1
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm)
    have hQw₀ : Qw ≠ Q₀ := by
      intro hh
      rw [hh] at hwQ
      have := Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hwQ)
      rw [hw₀] at this
      exact h this.symm
    have hQw₁ : Q₁ ≠ Qw := by
      intro hh
      rw [← hh] at hwQ
      have := Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hwQ)
      rw [hw₁] at this
      exact h this
    exact hy₀ne (eq_one_of_fixes_three H (Q₀ := Q₀) (Q₁ := Q₁) (Q₂ := Qw) h.symm hQw₀ hQw₁
      hy₀₀ hy₀₁ hy₀w)
  refine ⟨y₀ * (w * y₀ * w⁻¹)⁻¹, w, ?_, ?_, ?_, hww, ?_⟩
  · exact Subgroup.mul_mem _ hy₀₀ (Subgroup.inv_mem _ hwc₀)
  · exact Subgroup.mul_mem _ hy₀₁ (Subgroup.inv_mem _ hwc₁)
  · intro h1
    apply hnc
    have : y₀ = w * y₀ * w⁻¹ := by
      calc y₀ = (y₀ * (w * y₀ * w⁻¹)⁻¹) * (w * y₀ * w⁻¹) := by group
        _ = w * y₀ * w⁻¹ := by rw [h1, one_mul]
    exact this.symm
  · have e1 : w * (w * y₀ * w⁻¹)⁻¹ * w⁻¹ = y₀⁻¹ := by
      calc w * (w * y₀ * w⁻¹)⁻¹ * w⁻¹ = (w * w) * y₀⁻¹ * (w * w)⁻¹ := by group
        _ = y₀⁻¹ := by rw [hww]; group
    calc w * (y₀ * (w * y₀ * w⁻¹)⁻¹) * w⁻¹
        = (w * y₀ * w⁻¹) * (w * (w * y₀ * w⁻¹)⁻¹ * w⁻¹) := by group
      _ = (w * y₀ * w⁻¹) * y₀⁻¹ := by rw [e1]
      _ = (y₀ * (w * y₀ * w⁻¹)⁻¹)⁻¹ := by group

end Main

end CFSG.CGT.PushingUpLit.T2KR
