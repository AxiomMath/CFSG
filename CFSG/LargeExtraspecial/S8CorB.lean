module

public import CFSG.LargeExtraspecial.S4EightG
public import CFSG.LargeExtraspecial.S6Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

section Ambient

variable {Y : Type*} [Group Y]

theorem mem_sup_zpowers_iff {O : Subgroup Y} {t : Y} (htt : t * t = 1)
    (htO : ∀ o ∈ O, t * o * t⁻¹ ∈ O) {y : Y} :
    y ∈ O ⊔ zpowers t ↔ y ∈ O ∨ y * t ∈ O := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  let T : Subgroup Y :=
    { carrier := {y | y ∈ O ∨ y * t ∈ O}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (O.mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact O.mul_mem ha hb)
        · right
          have h1 := htO _ hb
          have e : a * b * t = (a * t) * (t * b * t⁻¹) := by
            calc a * b * t = a * (t * t) * b * t := by rw [htt, mul_one]
              _ = (a * t) * (t * b * t⁻¹) := by rw [hti]; group
          rw [e]
          exact O.mul_mem ha h1
        · left
          have h1 := htO _ hb
          have e : a * b = (a * t) * (t * (b * t) * t⁻¹) := by
            rw [hti]
            calc a * b = a * (t * t) * b * (t * t) := by rw [htt, mul_one, mul_one]
              _ = a * t * (t * (b * t) * t) := by group
          rw [e]
          exact O.mul_mem ha h1
      one_mem' := Or.inl O.one_mem
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (O.inv_mem ha)
        · right
          have h1 := htO _ (O.inv_mem ha)
          have e : a⁻¹ * t = t * (a * t)⁻¹ * t⁻¹ := by rw [hti]; group
          rw [e]
          exact h1 }
  constructor
  · intro hy
    have hle : O ⊔ zpowers t ≤ T := sup_le (fun o ho => Or.inl ho) (by
      rw [zpowers_le]
      exact Or.inr (by rw [htt]; exact O.one_mem))
    exact hle hy
  · rintro (hy | hy)
    · exact mem_sup_left hy
    · have e : y = (y * t) * t := by rw [mul_assoc, htt, mul_one]
      rw [e]
      exact mul_mem (mem_sup_left hy) (mem_sup_right (mem_zpowers t))

theorem inv_or_centralizes {O : Subgroup Y} [Finite O] (hO3 : Nat.card O ∣ 3) {l : Y}
    (hll : l * l = 1) (hlO : ∀ o ∈ O, l * o * l⁻¹ ∈ O) :
    (∀ o ∈ O, l * o * l⁻¹ = o⁻¹) ∨ (∀ o ∈ O, l * o * l⁻¹ = o) := by
  have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right hll
  have hcomm : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a := by
    intro a ha b hb
    rcases (Nat.dvd_prime Nat.prime_three).mp hO3 with h | h
    · have hbot : O = ⊥ := (Subgroup.eq_bot_iff_card O).mpr h
      rw [hbot, Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic O := isCyclic_of_prime_card h
      have := (IsCyclic.isMulCommutative (α := O)).is_comm
      exact congrArg Subtype.val (this.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set F := O ⊓ centralizer ({l} : Set Y) with hF
  have hFO : F ≤ O := inf_le_left
  have : Finite F := Finite.Set.subset (O : Set Y) hFO
  have hFcard : Nat.card F ∣ 3 := (Subgroup.card_dvd_of_le hFO).trans hO3
  rcases (Nat.dvd_prime Nat.prime_three).mp hFcard with h1 | h3
  · left
    intro o ho
    have hfix : o * (l * o * l⁻¹) ∈ F := by
      refine ⟨O.mul_mem ho (hlO o ho), mem_centralizer_singleton_iff.mpr ?_⟩
      have e1 : l * (o * (l * o * l⁻¹)) * l⁻¹ = (l * o * l⁻¹) * o := by
        rw [hli]
        calc l * (o * (l * o * l)) * l = l * o * l * o * (l * l) := by group
          _ = l * o * l * o := by rw [hll, mul_one]
      calc o * (l * o * l⁻¹) * l = (l * l) * (o * (l * o * l⁻¹)) * l := by rw [hll, one_mul]
        _ = l * (l * (o * (l * o * l⁻¹)) * l⁻¹) := by rw [hli]; group
        _ = l * ((l * o * l⁻¹) * o) := by rw [e1]
        _ = l * (o * (l * o * l⁻¹)) := by rw [hcomm _ (hlO o ho) _ ho]
    have hF1 : F = ⊥ := (Subgroup.eq_bot_iff_card F).mpr h1
    have := hF1 ▸ hfix
    rw [Subgroup.mem_bot] at this
    exact eq_inv_of_mul_eq_one_right this
  · right
    have hFeq : F = O := Subgroup.eq_of_le_of_card_ge hFO (by
      have : Nat.card O ≤ 3 := Nat.le_of_dvd (by norm_num) hO3
      omega)
    intro o ho
    have h2 : o ∈ centralizer ({l} : Set Y) := (hFeq ▸ ho : o ∈ F).2
    rw [mem_centralizer_singleton_iff] at h2
    rw [← h2, mul_inv_cancel_right]

theorem not_mem_of_orderOf_two {O : Subgroup Y} [Finite O] (hO3 : Nat.card O ∣ 3) {y : Y}
    (hy : orderOf y = 2) : y ∉ O := by
  intro hyO
  have h1 : orderOf y ∣ 3 := (Subgroup.orderOf_dvd_natCard O hyO).trans hO3
  rw [hy] at h1
  exact absurd h1 (by norm_num)

theorem eq_one_of_sq_of_mem {O : Subgroup Y} [Finite O] (hO3 : Nat.card O ∣ 3) {o : Y}
    (ho : o ∈ O) (ho2 : o * o = 1) : o = 1 := by
  have h1 : orderOf o ∣ 3 := (Subgroup.orderOf_dvd_natCard O ho).trans hO3
  have h2 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ho2)
  have h3 : orderOf o ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
  rw [show Nat.gcd 3 2 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

variable [Finite Y]

theorem le_zpowers_of_conj_mem {X : Subgroup Y} {t : Y} (htX : t ∈ X) (htt : t * t = 1)
    (ht1 : t ≠ 1) (hO2 : ∀ P : Subgroup Y, IsSubnormal P X → IsPGroup 2 P → P = ⊥)
    {O : Subgroup Y} (hOX : O ≤ X) (hOn : ∀ x ∈ X, ∀ o ∈ O, x * o * x⁻¹ ∈ O)
    (hO3 : Nat.card O ∣ 3) (hconj : ∀ x ∈ X, x * t * x⁻¹ ∈ O ⊔ zpowers t)
    {L : Subgroup Y} (hLX : L ≤ X) (hLc : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a)
    (hL2 : ∀ l ∈ L, l * l = 1) (htL : t ∈ L) {R N : Subgroup Y}
    (hRgen : R ≤ sSup {Z | ∃ x ∈ X, Z = L.map (MulAut.conj x).toMonoidHom ∧ t ∈ Z})
    (hRcont : ∀ x ∈ X, t ∈ L.map (MulAut.conj x).toMonoidHom →
      L.map (MulAut.conj x).toMonoidHom ≤ R)
    (hNR : N ≤ R) (hNn : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hN2 : IsPGroup 2 N)
    (htN : t ∈ N) : N ≤ zpowers t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have htO : ∀ o ∈ O, t * o * t⁻¹ ∈ O := hOn t htX
  have hform : ∀ x ∈ X, x * t * x⁻¹ * t ∈ O := by
    intro x hx
    rcases (mem_sup_zpowers_iff htt htO).mp (hconj x hx) with h | h
    · exfalso
      refine not_mem_of_orderOf_two hO3 ?_ h
      have := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective t
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rw [this, hto]
    · exact h
  have hnc : ∃ x ∈ X, x * t * x⁻¹ ≠ t := by
    by_contra hall
    push Not at hall
    have hsub : IsSubnormal (zpowers t) X := by
      refine IsSubnormal.step (zpowers_le.mpr htX) ⟨fun n hn x => ?_⟩ (IsSubnormal.refl X)
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
      change (x : Y) * n * (x : Y)⁻¹ ∈ zpowers t
      rw [← hk, ← conj_zpow, hall x x.2]
      exact zpow_mem (mem_zpowers t) k
    have h2 : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto, pow_one])
    have hbot := hO2 _ hsub h2
    exact ht1 (by
      have : t ∈ zpowers t := mem_zpowers t
      rwa [hbot, Subgroup.mem_bot] at this)
  obtain ⟨x₀, hx₀X, hx₀⟩ := hnc
  have ho₀ := hform x₀ hx₀X
  have ho₀1 : x₀ * t * x₀⁻¹ * t ≠ 1 := fun h => hx₀ (by
    have := eq_inv_of_mul_eq_one_left h
    rwa [hti] at this)
  have htinv : ∀ o ∈ O, t * o * t⁻¹ = o⁻¹ := by
    rcases inv_or_centralizes hO3 htt htO with h | h
    · exact h
    · exfalso
      apply ho₀1
      set o := x₀ * t * x₀⁻¹ * t with ho
      have e : x₀ * t * x₀⁻¹ = o * t := by rw [ho, mul_assoc (x₀ * t * x₀⁻¹) t t, htt, mul_one]
      have hsq : (x₀ * t * x₀⁻¹) * (x₀ * t * x₀⁻¹) = 1 := by
        calc (x₀ * t * x₀⁻¹) * (x₀ * t * x₀⁻¹) = x₀ * (t * t) * x₀⁻¹ := by group
          _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
      rw [e] at hsq
      have hot : t * o = o * t := by
        have := h o ho₀
        calc t * o = t * o * t⁻¹ * t := by group
          _ = o * t := by rw [this]
      have : o * o = 1 := by
        calc o * o = o * t * (o * t) * (t * t) := by
              rw [htt, mul_one, mul_assoc o t (o * t), ← mul_assoc t o t, hot]
              calc o * o = o * o * (t * t) := by rw [htt, mul_one]
                _ = o * (o * t * t) := by group
          _ = 1 := by rw [hsq, htt, mul_one]
      exact eq_one_of_sq_of_mem hO3 ho₀ this
  have hO1 : ∀ c ∈ centralizer (O : Set Y), c ≠ t := by
    intro c hc hct
    rw [hct] at hc
    have h1 := htinv _ ho₀
    have h2 : t * (x₀ * t * x₀⁻¹ * t) * t⁻¹ = x₀ * t * x₀⁻¹ * t := by
      rw [← mem_centralizer_iff.mp hc _ ho₀, mul_inv_cancel_right]
    rw [h2] at h1
    exact ho₀1 (eq_one_of_sq_of_mem hO3 ho₀ (by
      calc (x₀ * t * x₀⁻¹ * t) * (x₀ * t * x₀⁻¹ * t) =
          (x₀ * t * x₀⁻¹ * t) * (x₀ * t * x₀⁻¹ * t)⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel _))
  set L₁ := L ⊓ centralizer (O : Set Y) with hL₁
  have hsplit : ∀ l ∈ L, l ∈ L₁ ∨ t * l ∈ L₁ := by
    intro l hl
    rcases inv_or_centralizes hO3 (hL2 l hl) (hOn l (hLX hl)) with h | h
    · right
      refine ⟨mul_mem htL hl, mem_centralizer_iff.mpr fun o ho => ?_⟩
      have e : t * l * o * (t * l)⁻¹ = o := by
        have h2 := htinv o ho
        calc t * l * o * (t * l)⁻¹ = t * (l * o * l⁻¹) * t⁻¹ := by group
          _ = t * o⁻¹ * t⁻¹ := by rw [h o ho]
          _ = (t * o * t⁻¹)⁻¹ := by group
          _ = o := by rw [h2, inv_inv]
      calc o * (t * l) = t * l * o * (t * l)⁻¹ * (t * l) := by rw [e]
        _ = t * l * o := by group
    · left
      refine ⟨hl, mem_centralizer_iff.mpr fun o ho => ?_⟩
      calc o * l = l * o * l⁻¹ * l := by rw [h o ho]
        _ = l * o := by group
  set U₀ := O ⊔ zpowers t with hU₀
  have hU₀n : ∀ x ∈ X, ∀ u ∈ U₀, x * u * x⁻¹ ∈ U₀ := by
    intro x hx u hu
    have hle : U₀ ≤ U₀.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun o ho => mem_sup_left (hOn x hx o ho)) ?_
      rw [zpowers_le]
      exact hconj x hx
    exact hle hu
  have hL₁C : ∀ l ∈ L₁, ∀ u ∈ U₀, u * l = l * u := by
    intro l hl u hu
    have hle : U₀ ≤ centralizer ({l} : Set Y) := by
      refine sup_le (fun o ho => ?_) ?_
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hl.2 o ho)
      · rw [zpowers_le]
        exact mem_centralizer_singleton_iff.mpr (hLc l hl.1 t htL).symm
    exact mem_centralizer_singleton_iff.mp (hle hu)
  set D₀ := closure {y | ∃ x ∈ X, ∃ l ∈ L₁, y = x * l * x⁻¹} with hD₀
  have hD₀C : ∀ d ∈ D₀, ∀ u ∈ U₀, u * d = d * u := by
    intro d hd
    refine closure_induction (fun y hy => ?_) (fun u _ => by rw [mul_one, one_mul])
      (fun a b _ _ ha hb u hu => by rw [← mul_assoc, ha u hu, mul_assoc, hb u hu, mul_assoc])
      (fun a _ ha u hu => ?_) hd
    · obtain ⟨x, hx, l, hl, rfl⟩ := hy
      intro u hu
      have hu' : x⁻¹ * u * x⁻¹⁻¹ ∈ U₀ := hU₀n _ (inv_mem hx) u hu
      rw [inv_inv] at hu'
      calc u * (x * l * x⁻¹) = x * ((x⁻¹ * u * x) * l) * x⁻¹ := by group
        _ = x * (l * (x⁻¹ * u * x)) * x⁻¹ := by rw [hL₁C l hl _ hu']
        _ = x * l * x⁻¹ * u := by group
    · calc u * a⁻¹ = a⁻¹ * (a * u) * a⁻¹ := by group
        _ = a⁻¹ * (u * a) * a⁻¹ := by rw [ha u hu]
        _ = a⁻¹ * u := by group
  have hD₀X : D₀ ≤ X := by
    rw [hD₀, closure_le]
    rintro _ ⟨x, hx, l, hl, rfl⟩
    exact mul_mem (mul_mem hx (hLX hl.1)) (inv_mem hx)
  have hD₀n : ∀ x ∈ X, ∀ d ∈ D₀, x * d * x⁻¹ ∈ D₀ := by
    intro x hx d hd
    have hle : D₀ ≤ D₀.comap (MulAut.conj x).toMonoidHom := by
      rw [hD₀, closure_le]
      rintro _ ⟨y, hy, l, hl, rfl⟩
      exact subset_closure ⟨x * y, mul_mem hx hy, l, hl, by simp [mul_assoc]⟩
    exact hle hd
  have hRle : R ≤ D₀ ⊔ zpowers t := by
    refine hRgen.trans (sSup_le ?_)
    rintro Z ⟨x, hx, rfl, htZ⟩
    rintro _ ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨l', hl', hl't⟩ := htZ
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hl't
    have hgen : ∀ m ∈ L₁, x * m * x⁻¹ ∈ D₀ := fun m hm => subset_closure ⟨x, hx, m, hm, rfl⟩
    have hxt : x * t * x⁻¹ ∈ D₀ ⊔ zpowers t := by
      rcases hsplit l' hl' with h | h
      · exact absurd hl't (hO1 _ (mem_centralizer_iff.mpr fun o ho =>
          hD₀C _ (hgen l' h) o (mem_sup_left ho)))
      · have e : x * t * x⁻¹ = (x * (t * l') * x⁻¹) * (x * l' * x⁻¹) := by
          calc x * t * x⁻¹ = x * t * (l' * l') * x⁻¹ := by rw [hL2 l' hl', mul_one]
            _ = (x * (t * l') * x⁻¹) * (x * l' * x⁻¹) := by group
        rw [hl't] at e
        rw [e]
        exact mul_mem (mem_sup_left (hgen _ h)) (mem_sup_right (mem_zpowers t))
    rcases hsplit l hl with h | h
    · exact mem_sup_left (hgen l h)
    · have e : x * l * x⁻¹ = (x * t * x⁻¹) * (x * (t * l) * x⁻¹) := by
        calc x * l * x⁻¹ = x * (t * t) * l * x⁻¹ := by rw [htt, mul_one]
          _ = (x * t * x⁻¹) * (x * (t * l) * x⁻¹) := by group
      rw [e]
      exact mul_mem hxt (mem_sup_left (hgen _ h))
  have hD₀R : D₀ ≤ R := by
    rw [hD₀, closure_le]
    rintro _ ⟨x, hx, l, hl, rfl⟩
    obtain ⟨o, ho⟩ : ∃ o, o = x * t * x⁻¹ * t := ⟨_, rfl⟩
    have hoO : o ∈ O := ho ▸ hform x hx
    have hxt : x * t * x⁻¹ = o * t := by rw [ho, mul_assoc (x * t * x⁻¹) t t, htt, mul_one]
    have ho3 : o * o * o = 1 := by
      have h1 : orderOf o ∣ 3 := (Subgroup.orderOf_dvd_natCard O hoO).trans hO3
      have := pow_eq_one_iff_modEq.mpr (show 3 ≡ 0 [MOD orderOf o] from
        (Nat.modEq_zero_iff_dvd.mpr h1))
      rwa [pow_three, ← mul_assoc] at this
    have hyX : o * x ∈ X := mul_mem (hOX hoO) hx
    have hinv : t * o⁻¹ * t⁻¹ = o := by
      rw [show t * o⁻¹ * t⁻¹ = (t * o * t⁻¹)⁻¹ by group, htinv o hoO, inv_inv]
    have hyt : (o * x) * t * (o * x)⁻¹ = t := by
      calc (o * x) * t * (o * x)⁻¹ = o * (x * t * x⁻¹) * o⁻¹ := by group
        _ = o * (o * t) * o⁻¹ := by rw [hxt]
        _ = o * o * (t * o⁻¹ * t⁻¹) * t := by group
        _ = o * o * o * t := by rw [hinv]
        _ = t := by rw [ho3, one_mul]
    have htZ : t ∈ L.map (MulAut.conj (o * x)).toMonoidHom :=
      ⟨t, htL, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; exact hyt⟩
    refine hRcont (o * x) hyX htZ ⟨l, hl.1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc := hD₀C _ (subset_closure ⟨x, hx, l, hl, rfl⟩) o (mem_sup_left hoO)
    calc o * x * l * (o * x)⁻¹ = o * (x * l * x⁻¹) * o⁻¹ := by group
      _ = x * l * x⁻¹ * o * o⁻¹ := by rw [← hc]
      _ = x * l * x⁻¹ := by group
  have hP : N ⊓ D₀ = ⊥ := by
    refine hO2 _ ?_ (hN2.to_le inf_le_left)
    refine IsSubnormal.step inf_le_right ⟨fun n hn d => ?_⟩
      (IsSubnormal.step hD₀X ⟨fun n hn x => ?_⟩ (IsSubnormal.refl X))
    · rw [mem_subgroupOf] at hn ⊢
      have hd : (d : Y) ∈ D₀ := d.2
      have hn2 : (n : Y) ∈ D₀ := hn.2
      exact ⟨hNn _ (hD₀R hd) _ hn.1, D₀.mul_mem (D₀.mul_mem hd hn2) (D₀.inv_mem hd)⟩
    · rw [mem_subgroupOf] at hn ⊢
      exact hD₀n _ x.2 _ hn
  intro n hn
  have htD : ∀ d ∈ D₀, t * d * t⁻¹ ∈ D₀ := hD₀n t htX
  rcases (mem_sup_zpowers_iff htt htD).mp (hRle (hNR hn)) with h | h
  · have : n ∈ N ⊓ D₀ := ⟨hn, h⟩
    rw [hP, Subgroup.mem_bot] at this
    rw [this]
    exact one_mem _
  · have : n * t ∈ N ⊓ D₀ := ⟨mul_mem hn htN, h⟩
    rw [hP, Subgroup.mem_bot] at this
    rw [eq_inv_of_mul_eq_one_left this, hti]
    exact mem_zpowers t


end Ambient

end CFSG.LargeExtraspecial.S8
