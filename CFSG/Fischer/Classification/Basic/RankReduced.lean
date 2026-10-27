module

public import CFSG.Fischer.Classification.Basic.Reduced

public section

open CFSG.Blueprint.Fischer CFSG.Fischer
open scoped commutatorElement

namespace CFSG.Fischer.Classification

variable {X : Type} [Group X] {E : Set X}

theorem Pair.mem_center_of_isPGroup (hP : Pair X E) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {N : Subgroup X} (hN : N.Normal) (hNp : IsPGroup p N) {n : X} (hn : n ∈ N) :
    n ∈ Subgroup.center X := by
  have := Fact.mk hp
  refine (Pair.mem_center_iff hP).2 fun e he => ?_
  have hmem : e * (n * e * n⁻¹) ∈ N := by
    have h1 := hN.conj_mem n hn e
    rw [Pair.inv_eq hP he] at h1
    have := N.mul_mem h1 (N.inv_mem hn)
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hNp) ⟨_, hmem⟩
  rw [Subgroup.orderOf_mk] at hk
  have hord := Pair.orderOf_mul_mem hP he (Pair.conj_mem hP he n)
  rw [hk] at hord
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hord
  have hk0 : k = 0 := by
    by_contra hk0
    have : p ≤ p ^ k := Nat.le_self_pow hk0 p
    omega
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  have h2 : n * e * n⁻¹ = e := by
    have := eq_inv_of_mul_eq_one_right hk
    rwa [Pair.inv_eq hP he] at this
  calc e * n = n * e * n⁻¹ * n := by rw [h2]
    _ = n * e := by group

theorem Pair.eq_bot_of_isPGroup (hP : Pair X E) (hZ : Subgroup.center X = ⊥) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {N : Subgroup X} (hN : N.Normal) (hNp : IsPGroup p N) :
    N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [← hZ]
  exact Pair.mem_center_of_isPGroup hP hp hp5 hN hNp hn

theorem Pair.eq_of_forall_commute_iff_of_two (hP : Pair X E)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) {x y : X} (hx : x ∈ E)
    (hy : y ∈ E) (h : ∀ w ∈ E, w * x = x * w ↔ w * y = y * w) : x = y := by
  have := Pair.finite hP
  let R : X → X → Prop := fun a b => ∀ w ∈ E, (w * a = a * w ↔ w * b = b * w)
  have hrefl : ∀ a ∈ E, R a a := fun _ _ _ _ => Iff.rfl
  have hsymm : ∀ a ∈ E, ∀ b ∈ E, R a b → R b a := fun _ _ _ _ hab w hw => (hab w hw).symm
  have htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, R a b → R b c → R a c :=
    fun _ _ _ _ _ _ hab hbc w hw => (hab w hw).trans (hbc w hw)
  have hconj : ∀ g : X, ∀ a ∈ E, ∀ b ∈ E, R a b → R (g * a * g⁻¹) (g * b * g⁻¹) := by
    intro g a _ b _ hab w hw
    have hw' : g⁻¹ * w * g ∈ E := by simpa using Pair.conj_mem hP hw g⁻¹
    rw [commute_conj_iff, commute_conj_iff]
    exact hab _ hw'
  obtain ⟨K, hKn, hK⟩ := Pair.exists_normal_of_conj_rel hP R hrefl hsymm htrans hconj
  have hmulK : ∀ a ∈ E, ∀ b ∈ E, R a b → a * b ∈ K := by
    intro a ha b hb hab
    rw [hK]
    intro c hc
    by_cases hca : c * a = a * c
    · rw [mul_conj_eq_self hca ((hab c hc).1 hca)]
      exact hrefl c hc
    · have hcb : c * b ≠ b * c := fun h' => hca ((hab c hc).2 h')
      have := hconj (a * c) a ha b hb hab
      rwa [Pair.mul_conj_eq hP ha hc hca, Pair.mul_conj_eq_conj hP ha hb hc hcb] at this
  let V : Set X := {u | u ∈ E ∧ R u x}
  have hVcomm : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u := fun u hu v hv =>
    (htrans u hu.1 x hx v hv.1 hu.2 (hsymm v hv.1 x hx hv.2) u hu.1).1 rfl
  let Q : Subgroup X := Subgroup.closure {g | ∃ u ∈ V, ∃ v ∈ V, u * v = g}
  have hQK : Q ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨u, hu, v, hv, rfl⟩
    exact hmulK u hu.1 v hv.1 (htrans u hu.1 x hx v hv.1 hu.2 (hsymm v hv.1 x hx hv.2))
  have hQV : Q ≤ Subgroup.closure V := by
    rw [Subgroup.closure_le]
    rintro _ ⟨u, hu, v, hv, rfl⟩
    exact mul_mem (Subgroup.subset_closure hu) (Subgroup.subset_closure hv)
  have hcommV : ∀ g ∈ Subgroup.closure V, ∀ v ∈ V, g * v = v * g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem u hu => exact fun v hv => hVcomm u hu v hv
    | one => exact fun v _ => by rw [one_mul, mul_one]
    | mul a b _ _ iha ihb =>
      exact fun v hv => by rw [mul_assoc, ihb v hv, ← mul_assoc, iha v hv, mul_assoc]
    | inv a _ iha =>
      intro v hv
      exact (Commute.inv_left (iha v hv : Commute a v)).eq
  have hcomm2 : ∀ g ∈ Subgroup.closure V, ∀ g' ∈ Subgroup.closure V, g * g' = g' * g := by
    intro g hg g' hg'
    induction hg' using Subgroup.closure_induction with
    | mem v hv => exact hcommV g hg v hv
    | one => rw [one_mul, mul_one]
    | mul a b _ _ iha ihb => rw [← mul_assoc, iha, mul_assoc, ihb, ← mul_assoc]
    | inv a _ iha => exact (Commute.inv_right (iha : Commute g a)).eq
  have hsq : ∀ g ∈ Subgroup.closure V, g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem v hv => exact Pair.mul_self hP hv.1
    | one => rw [one_mul]
    | mul a b ha hb iha ihb =>
      rw [show a * b * (a * b) = a * (b * a) * b by simp only [mul_assoc], ← hcomm2 a ha b hb,
        show a * (a * b) * b = a * a * (b * b) by simp only [mul_assoc], iha, ihb, one_mul]
    | inv a _ iha => rw [← mul_inv_rev, iha, inv_one]
  have hKQ : ∀ k ∈ K, ∀ g ∈ Q, k * g * k⁻¹ ∈ Q := by
    intro k hk g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨u, hu, v, hv, rfl⟩ := hg
      have hmemV : ∀ w ∈ V, k * w * k⁻¹ ∈ V := fun w hw =>
        ⟨Pair.conj_mem hP hw.1 k, htrans _ (Pair.conj_mem hP hw.1 k) w hw.1 x hx
          (hsymm w hw.1 _ (Pair.conj_mem hP hw.1 k) ((hK k).1 hk w hw.1)) hw.2⟩
      refine Subgroup.subset_closure ⟨_, hmemV u hu, _, hmemV v hv, ?_⟩
      group
    | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
    | mul a b _ _ iha ihb =>
      rw [show k * (a * b) * k⁻¹ = k * a * k⁻¹ * (k * b * k⁻¹) by group]
      exact mul_mem iha ihb
    | inv a _ iha =>
      rw [show k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ by group]
      exact inv_mem iha
  have hQn : (Q.subgroupOf K).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hKQ k k.2 n hn⟩
  have hQp : IsPGroup 2 (Q.subgroupOf K) := fun g => ⟨1, by
    rw [pow_one]
    refine Subtype.ext (Subtype.ext ?_)
    have hg : ((g : K) : X) ∈ Q := Subgroup.mem_subgroupOf.1 g.2
    simpa [sq] using hsq _ (hQV hg)⟩
  have hle : Q.subgroupOf K ≤ CFSG.pCore 2 K := le_sSup ⟨hQn, hQp⟩
  have : K.Normal := hKn
  have hNn : ((CFSG.pCore 2 K).map K.subtype).Normal := inferInstance
  have hNbot := h2 _ hNn ((CFSG.pCore_isPGroup (p := 2) (G := K)).map _)
  have hxyQ : x * y ∈ Q :=
    Subgroup.subset_closure ⟨x, ⟨hx, hrefl x hx⟩, y, ⟨hy, hsymm x hx y hy h⟩, rfl⟩
  have hxyN : x * y ∈ (CFSG.pCore 2 K).map K.subtype :=
    ⟨⟨x * y, hQK hxyQ⟩, hle (Subgroup.mem_subgroupOf.2 hxyQ), rfl⟩
  rw [hNbot, Subgroup.mem_bot] at hxyN
  rw [← Pair.inv_eq hP hy]
  exact eq_inv_of_mul_eq_one_left hxyN

theorem Pair.exists_ne_commute_of_three (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) :
    ∃ d ∈ E, ∃ e ∈ E, d ≠ e ∧ d * e = e * d := by
  by_contra! hall
  have := Pair.finite hP
  let := Fintype.ofFinite X
  obtain ⟨d, hd⟩ := Pair.nonempty hP
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar X d (Pair.ne_one hP hd)
    (Pair.mul_self hP hd) fun g hg => by
      by_contra hne
      exact hall _ (Pair.conj_mem hP hd g) d hd hne hg
  have := hNn
  have hEN : ∀ e ∈ E, ∀ f ∈ E, f * e⁻¹ ∈ N := by
    intro e he f hf
    obtain ⟨a, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd he)
    obtain ⟨b, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd hf)
    have := N.mul_mem (hN b) (N.inv_mem (hN a))
    rwa [show b * d * b⁻¹ * d⁻¹ * (a * d * a⁻¹ * d⁻¹)⁻¹ = b * d * b⁻¹ * (a * d * a⁻¹)⁻¹ by
      group] at this
  have hle := Pair.commutator_le_of_forall hP hEN
  have hsolN : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have hne : commutator X ≠ ⊥ := by
    intro h
    have hdZ : d ∈ Subgroup.center X := by
      refine (Pair.mem_center_iff hP).2 fun e _ => ?_
      have hc : ⁅e, d⁆ ∈ commutator X := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top e) (Subgroup.mem_top d)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  obtain ⟨M, hMn, hMle, hMne, hMmin⟩ :=
    CFSG.exists_minimal_normal_le (commutator X) inferInstance hne
  have : M.Normal := hMn
  have : CFSG.IsMinimalNormal M := ⟨fun K _ hKle => by
    by_cases hK : K = ⊥
    · exact Or.inl hK
    · exact Or.inr (hMmin K inferInstance hKle hK)⟩
  have hMN := hMle.trans hle
  have : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hMN) (Subgroup.inclusion_injective hMN)
  obtain ⟨p, hp, hpM⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian M
  have hMp : IsPGroup p M := CFSG.IsElementaryAbelian.isPGroup p M
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hcard1 : Nat.card M ≠ 1 := fun h => hMne (Subgroup.card_eq_one.1 h)
    have hdvd : 2 ∣ Nat.card M := by
      have := Fact.mk hp
      exact (hMp.card_eq_or_dvd).resolve_left hcard1
    have hodd : Odd (Nat.card M) := Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hMN)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hMne (h3 M hMn hMp)
  have hp4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  exact hMne (Pair.eq_bot_of_isPGroup hP hZ hp hp5 hMn hMp)

end CFSG.Fischer.Classification
