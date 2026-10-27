module

public import CFSG.Open.GeneratedCore

public section

namespace CFSG.AGLEmbedding.KFactProofs.L34Local

open CFSG.Open

structure LocalData (G : Type*) [Group G] (P : Subgroup G) : Prop where
  card_eq : Nat.card P = 9
  card_normalizer : Nat.card (Subgroup.normalizer (P : Set G)) = 72
  centralizer_le : ∀ t ∈ P, t ≠ 1 → ∀ g : G, g * t = t * g → g ∈ P
  trans : ∀ x ∈ P, x ≠ 1 → ∀ y ∈ P, y ≠ 1 →
    ∃ n ∈ Subgroup.normalizer (P : Set G), n * x * n⁻¹ = y
  aut : ∀ f : MulAut G, (∀ t ∈ P, f t = t) →
    ∃ t ∈ P, ∀ n ∈ Subgroup.normalizer (P : Set G), f n = t * n * t⁻¹

namespace LocalData

section Transport

variable {G G' : Type*} [Group G] [Group G'] {P : Subgroup G} {P' : Subgroup G'}

theorem map (e : G ≃* G') (hP : ∀ g, g ∈ P ↔ e g ∈ P') (h : LocalData G P) :
    LocalData G' P' := by
  have hP' : ∀ y, y ∈ P' ↔ e.symm y ∈ P := fun y => by simpa using (hP (e.symm y)).symm
  have hnorm : ∀ n : G, n ∈ Subgroup.normalizer (P : Set G) ↔
      e n ∈ Subgroup.normalizer (P' : Set G') := by
    intro n
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hn y
      rw [hP' y, hP' (e n * y * (e n)⁻¹)]
      simpa using hn (e.symm y)
    · intro hn x
      have h1 := hn (e x)
      have e1 : e n * e x * (e n)⁻¹ = e (n * x * n⁻¹) := by simp
      rw [e1, ← hP, ← hP] at h1
      exact h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.card_eq]
    refine Nat.card_congr (Equiv.symm ?_)
    exact
      { toFun := fun x => ⟨e x, (hP x).1 x.2⟩
        invFun := fun y => ⟨e.symm y, (hP' y).1 y.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
  · rw [← h.card_normalizer]
    refine Nat.card_congr (Equiv.symm ?_)
    exact
      { toFun := fun x => ⟨e x, (hnorm x).1 x.2⟩
        invFun := fun y => ⟨e.symm y, (hnorm _).2 (by simp)⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
  · intro t' ht' ht1 g' hg
    have ht : e.symm t' ∈ P := (hP' t').1 ht'
    have h1 : e.symm t' ≠ 1 := fun h1 => ht1 (by simpa using congrArg e h1)
    have h2 : e.symm g' * e.symm t' = e.symm t' * e.symm g' := by
      rw [← map_mul, ← map_mul, hg]
    exact (hP' g').2 (h.centralizer_le _ ht h1 _ h2)
  · intro x' hx' hx1 y' hy' hy1
    have hx : e.symm x' ∈ P := (hP' x').1 hx'
    have hy : e.symm y' ∈ P := (hP' y').1 hy'
    have hx1' : e.symm x' ≠ 1 := fun h1 => hx1 (by simpa using congrArg e h1)
    have hy1' : e.symm y' ≠ 1 := fun h1 => hy1 (by simpa using congrArg e h1)
    obtain ⟨n, hn, hnxy⟩ := h.trans _ hx hx1' _ hy hy1'
    refine ⟨e n, (hnorm n).1 hn, ?_⟩
    simpa using congrArg e hnxy
  · intro f' hf'
    let f : MulAut G := e.trans (f'.trans e.symm)
    have hf : ∀ t ∈ P, f t = t := by
      intro t ht
      show e.symm (f' (e t)) = t
      rw [hf' (e t) ((hP t).1 ht)]
      simp
    obtain ⟨t, ht, hconj⟩ := h.aut f hf
    refine ⟨e t, (hP t).1 ht, fun n' hn' => ?_⟩
    have h1 := hconj (e.symm n') ((hnorm _).2 (by simpa using hn'))
    have h2 : f (e.symm n') = e.symm (f' n') := by
      show e.symm (f' (e (e.symm n'))) = _
      simp
    rw [h2] at h1
    simpa using congrArg e h1

end Transport

section Conclusion

variable {G : Type*} [Group G] {P : Subgroup G}

theorem ne_bot_of_one_le_pRank [Finite G] {p : ℕ} (hp : 2 ≤ p) {Q : Subgroup G}
    (h : 1 ≤ pRank p Q) : Q ≠ ⊥ := by
  rintro rfl
  have h0 : pRank p (⊥ : Subgroup G) ≤ 0 := by
    refine csSup_le' ?_
    rintro k ⟨E, hE, -, hcard⟩
    rw [le_bot_iff.1 hE, Subgroup.card_bot] at hcard
    by_contra hk
    have : 1 < p ^ k := Nat.one_lt_pow (by omega) (by omega)
    omega
  omega

theorem commute_of_card_eq (h : LocalData G P) : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx y hy
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := P)
    (by rw [h.card_eq]; norm_num)
  exact congrArg Subtype.val (this.is_comm.comm (⟨x, hx⟩ : P) ⟨y, hy⟩)

theorem glbCore_le [Finite G] (h : LocalData G P) :
    GLBCore 3 1 (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G) := by
  have hcomm := commute_of_card_eq h
  have key : ∀ Q : Subgroup G, Q ≤ P → Q ≠ ⊥ → ∀ g ∈ Subgroup.normalizer (Q : Set G),
      ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro Q hQP hQ g hg x hx
    obtain ⟨q, hq⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ
    have hq' : g * (q : G) * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hg q).1 q.2
    refine h.centralizer_le (g * q * g⁻¹) (hQP hq') ?_ _ ?_
    · intro h1
      apply hq
      have : (q : G) = 1 := by
        have h2 : g⁻¹ * (g * (q : G) * g⁻¹) * g = g⁻¹ * 1 * g := by rw [h1]
        simpa [mul_assoc] using h2
      exact Subtype.ext this
    · have hqP : (q : G) ∈ P := hQP q.2
      have := hcomm x hx q hqP
      calc g * x * g⁻¹ * (g * q * g⁻¹) = g * (x * q) * g⁻¹ := by group
        _ = g * (q * x) * g⁻¹ := by rw [this]
        _ = g * q * g⁻¹ * (g * x * g⁻¹) := by group
  unfold GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQP, hQ, rfl⟩
  have hQ' : Q ≠ ⊥ := ne_bot_of_one_le_pRank (by norm_num) hQ
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key Q hQP hQ' g hg x
  · intro hx
    have := key Q hQP hQ' g⁻¹ (Subgroup.inv_mem _ hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem exists_complement [Finite G] (h : LocalData G P) :
    ∃ T₀ : Subgroup G, T₀ ≤ Subgroup.normalizer (P : Set G) ∧ Nat.Coprime 3 (Nat.card T₀) ∧
      P ⊓ Subgroup.centralizer (T₀ : Set G) = ⊥ := by
  have hcomm := commute_of_card_eq h
  set N := Subgroup.normalizer (P : Set G) with hN
  have hdvd : 2 ^ 3 ∣ Nat.card N := by rw [h.card_normalizer]; norm_num
  obtain ⟨T₀, hT₀, -, hT₀N⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := ⊥) (L := N) (n := 3) (by simp) hdvd bot_le
  refine ⟨T₀, hT₀N, by rw [hT₀]; norm_num, ?_⟩
  rw [eq_bot_iff]
  rintro t ⟨htP, htC⟩
  rw [Subgroup.mem_bot]
  by_contra ht1
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hsup : P ⊔ T₀ = N := by
    have h1 : Nat.card P ∣ Nat.card ↥(P ⊔ T₀) := Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card T₀ ∣ Nat.card ↥(P ⊔ T₀) := Subgroup.card_dvd_of_le le_sup_right
    have h3 : Nat.card ↥(P ⊔ T₀) ≤ Nat.card N :=
      Subgroup.card_le_of_le (sup_le hPN hT₀N)
    have h4 : 0 < Nat.card ↥(P ⊔ T₀) := Nat.card_pos
    rw [h.card_eq] at h1
    rw [hT₀] at h2
    rw [h.card_normalizer] at h3
    refine Subgroup.eq_of_le_of_card_ge (sup_le hPN hT₀N) ?_
    rw [h.card_normalizer]
    omega
  have hcent : N ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [← hsup]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm x hx t htP
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 htC x hx
  obtain ⟨n, hnN, hn⟩ := h.trans t htP ht1 t⁻¹ (P.inv_mem htP) (inv_ne_one.2 ht1)
  have hnt : n * t = t * n := Subgroup.mem_centralizer_singleton_iff.1 (hcent hnN)
  have h1 : t = t⁻¹ := by
    rw [hnt] at hn
    simpa using hn
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [h1]
    exact inv_mul_cancel t
  have ht9 : t ^ 9 = 1 := by
    have h9 := pow_card_eq_one' (G := P) (x := (⟨t, htP⟩ : P))
    rw [h.card_eq] at h9
    simpa using congrArg Subtype.val h9
  have h3 : orderOf t ∣ Nat.gcd 9 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ht9) (orderOf_dvd_of_pow_eq_one ht2)
  have : orderOf t = 1 := Nat.dvd_one.1 (by simpa using h3)
  exact ht1 (orderOf_eq_one_iff.1 this)

theorem conclusion [Finite G] (h : LocalData G P) :
    (∃ T₀ : Subgroup G, T₀ ≤ Subgroup.normalizer (P : Set G) ∧ Nat.Coprime 3 (Nat.card T₀) ∧
      P ⊓ Subgroup.centralizer (T₀ : Set G) = ⊥) ∧
    ∀ V : Subgroup G, V ≤ P → V ≠ ⊥ →
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (V : Set G) →
      ∀ f : MulAut G, (∀ v ∈ V, f v = v) →
        ∃ t ∈ P, ∀ k ∈ GLBCore 3 1 (P : Subgroup G), f k = t * k * t⁻¹ := by
  refine ⟨exists_complement h, ?_⟩
  intro V hVP hV1 hN f hf
  have hVP' : V = P := by
    obtain ⟨v, hv⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV1
    have hv1 : (v : G) ≠ 1 := fun h1 => hv (Subtype.ext h1)
    refine le_antisymm hVP fun y hy => ?_
    by_cases hy1 : y = 1
    · rw [hy1]
      exact V.one_mem
    · obtain ⟨n, hn, hnvy⟩ := h.trans v (hVP v.2) hv1 y hy hy1
      have := (Subgroup.mem_normalizer_iff.1 (hN hn) v).1 v.2
      rwa [hnvy] at this
  subst hVP'
  obtain ⟨t, htV, ht⟩ := h.aut f hf
  exact ⟨t, htV, fun k hk => ht k (h.glbCore_le hk)⟩

end Conclusion

end LocalData

end CFSG.AGLEmbedding.KFactProofs.L34Local
