module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open

variable {G : Type*} [Group G] {p : ℕ}

theorem le_normalizer_of_comm {E A B : Subgroup G} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hA : A ≤ E) (hB : B ≤ E) : A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [hcomm a (hA ha) b (hB hb), mul_inv_cancel_right]
    exact hb
  · intro hb
    have hc : a * b * a⁻¹ * a = a * (a * b * a⁻¹) := hcomm _ (hB hb) a (hA ha)
    have h1 : a⁻¹ * (a * b * a⁻¹) * a = a * b * a⁻¹ := by
      rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : b = a⁻¹ * (a * b * a⁻¹) * a := by group
    rw [h2, h1]
    exact hb

theorem exists_mul_of_mem_sup {E A B : Subgroup G} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hA : A ≤ E) (hB : B ≤ E) {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right A B (le_normalizer_of_comm hcomm hA hB)] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_of_pow_mem_of_lt (hp : p.Prime) {x : G} (hxp : x ^ p = 1) {H : Subgroup G} {i : ℕ}
    (hi0 : 0 < i) (hip : i < p) (h : x ^ i ∈ H) : x ∈ H := by
  have hcop : Nat.Coprime i p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    exact absurd (Nat.le_of_dvd hi0 hdvd) (not_le.mpr hip)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hx : x ^ (i * m) = x := by
    conv_lhs => rw [← Nat.mod_add_div (i * m) p, hm]
    rw [pow_add, pow_one, pow_mul, hxp, one_pow, mul_one]
  rw [← hx, pow_mul]
  exact H.pow_mem h m

variable [Finite G]

theorem exists_elemAbelian_le_inf_eq_bot (hp : p.Prime) {E E₀ : Subgroup G}
    (hE : IsElemAbelian p E) (hE₀ : E₀ ≤ E) (k : ℕ) (hk : p ^ k * Nat.card E₀ ≤ Nat.card E) :
    ∃ D : Subgroup G, D ≤ E ∧ IsElemAbelian p D ∧ Nat.card D = p ^ k ∧ D ⊓ E₀ = ⊥ := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsub : ∀ {D : Subgroup G}, D ≤ E → IsElemAbelian p D := fun {D} hD =>
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (hD a.2) _ (hD b.2))⟩⟩, fun x hx => hE.2 x (hD hx)⟩
  induction k with
  | zero => exact ⟨⊥, bot_le, hsub bot_le, by simp, bot_inf_eq _⟩
  | succ k ih =>
    have hk' : p ^ k * Nat.card E₀ ≤ Nat.card E :=
      le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (Nat.le_succ k))) hk
    obtain ⟨D, hDE, -, hDc, hDE₀⟩ := ih hk'
    have hcardsup : Nat.card (D ⊔ E₀ : Subgroup G) ≤ Nat.card D * Nat.card E₀ := by
      let f : D × E₀ → (D ⊔ E₀ : Subgroup G) := fun ab =>
        ⟨(ab.1 : G) * ab.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left ab.1.2)
          (Subgroup.mem_sup_right ab.2.2)⟩
      have hf : Function.Surjective f := by
        rintro ⟨x, hx⟩
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hDE hE₀ hx
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
      calc Nat.card (D ⊔ E₀ : Subgroup G) ≤ Nat.card (D × E₀) :=
            Nat.card_le_card_of_surjective f hf
        _ = Nat.card D * Nat.card E₀ := Nat.card_prod _ _
    have hlt : Nat.card (D ⊔ E₀ : Subgroup G) < Nat.card E := by
      have hpos : 0 < Nat.card E₀ := Nat.card_pos
      calc Nat.card (D ⊔ E₀ : Subgroup G) ≤ p ^ k * Nat.card E₀ := by rw [← hDc]; exact hcardsup
        _ < p ^ (k + 1) * Nat.card E₀ :=
            Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self k)) hpos
        _ ≤ Nat.card E := hk
    obtain ⟨x, hxE, hxnot⟩ : ∃ x ∈ E, x ∉ D ⊔ E₀ := by
      by_contra hcon
      push Not at hcon
      exact absurd (Subgroup.card_le_of_le (fun y hy => hcon y hy : E ≤ D ⊔ E₀)) (not_le.mpr hlt)
    have hxp : x ^ p = 1 := hE.2 x hxE
    have hxZ : Subgroup.zpowers x ≤ E := Subgroup.zpowers_le.mpr hxE
    have hrepr : ∀ y ∈ D ⊔ Subgroup.zpowers x, ∃ i : ℕ, i < p ∧ ∃ d ∈ D, y = x ^ i * d := by
      intro y hy
      rw [sup_comm] at hy
      obtain ⟨z, hz, d, hd, rfl⟩ := exists_mul_of_mem_sup hcomm hxZ hDE hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      refine ⟨(j % (p : ℤ)).toNat, ?_, d, hd, ?_⟩
      · have h1 : j % (p : ℤ) < p := Int.emod_lt_of_pos j (by exact_mod_cast hp.pos)
        have h2 : 0 ≤ j % (p : ℤ) := Int.emod_nonneg j hp0
        omega
      · congr 1
        rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg j hp0)]
        conv_lhs => rw [← Int.emod_add_mul_ediv j p]
        rw [zpow_add, zpow_mul, zpow_natCast x p, hxp, one_zpow, mul_one]
    have huniq : ∀ i j : ℕ, i < p → j < p → ∀ d ∈ D, ∀ d' ∈ D, x ^ i * d = x ^ j * d' → i = j := by
      intro i j hi hj d hd d' hd' h
      by_contra hij
      rcases Nat.lt_or_gt_of_ne hij with hlt' | hlt'
      ·
        have hmem : x ^ (j - i) ∈ D := by
          have h1 : x ^ (j - i) = d * d'⁻¹ := by
            have h2 : x ^ j = x ^ i * x ^ (j - i) := by rw [← pow_add]; congr 1; omega
            rw [h2, mul_assoc] at h
            have h3 := mul_left_cancel h
            rw [eq_mul_inv_iff_mul_eq, ← h3]
          rw [h1]
          exact D.mul_mem hd (D.inv_mem hd')
        exact hxnot (Subgroup.mem_sup_left
          (mem_of_pow_mem_of_lt hp hxp (by omega) (by omega) hmem))
      · have hmem : x ^ (i - j) ∈ D := by
          have h1 : x ^ (i - j) = d' * d⁻¹ := by
            have h2 : x ^ i = x ^ j * x ^ (i - j) := by rw [← pow_add]; congr 1; omega
            rw [h2, mul_assoc] at h
            have h3 := (mul_left_cancel h).symm
            rw [eq_mul_inv_iff_mul_eq, ← h3]
          rw [h1]
          exact D.mul_mem hd' (D.inv_mem hd)
        exact hxnot (Subgroup.mem_sup_left
          (mem_of_pow_mem_of_lt hp hxp (by omega) (by omega) hmem))
    set D' := D ⊔ Subgroup.zpowers x with hD'
    have hD'E : D' ≤ E := sup_le hDE hxZ
    refine ⟨D', hD'E, hsub hD'E, ?_, ?_⟩
    ·
      let f : Fin p × D → D' := fun id =>
        ⟨x ^ (id.1 : ℕ) * id.2, D'.mul_mem (Subgroup.mem_sup_right
          (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)) (Subgroup.mem_sup_left id.2.2)⟩
      have hf : Function.Bijective f := by
        constructor
        · rintro ⟨i, d⟩ ⟨j, d'⟩ h
          have h1 : x ^ (i : ℕ) * d = x ^ (j : ℕ) * d' := congrArg Subtype.val h
          have hij := huniq i j i.2 j.2 d d.2 d' d'.2 h1
          have hij' : i = j := Fin.ext hij
          subst hij'
          have hdd : (d : G) = d' := mul_left_cancel h1
          exact Prod.ext rfl (Subtype.ext hdd)
        · rintro ⟨y, hy⟩
          obtain ⟨i, hi, d, hd, rfl⟩ := hrepr y hy
          exact ⟨(⟨i, hi⟩, ⟨d, hd⟩), rfl⟩
      rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_eq_fintype_card,
        Fintype.card_fin, hDc, pow_succ, mul_comm]
    · rw [eq_bot_iff]
      rintro y ⟨hyD', hyE₀⟩
      obtain ⟨i, hi, d, hd, rfl⟩ := hrepr y hyD'
      rw [Subgroup.mem_bot]
      by_cases hi0 : i = 0
      · subst hi0
        rw [pow_zero, one_mul] at hyE₀ ⊢
        have : d ∈ D ⊓ E₀ := ⟨hd, hyE₀⟩
        rw [hDE₀] at this
        exact this
      · exfalso
        have hxi : x ^ i ∈ D ⊔ E₀ := by
          have : x ^ i = x ^ i * d * d⁻¹ := by group
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hyE₀)
            (Subgroup.mem_sup_left (D.inv_mem hd))
        exact hxnot (mem_of_pow_mem_of_lt hp hxp (Nat.pos_of_ne_zero hi0) hi hxi)

theorem pRank_le_pRank_add_of_forall_inf_ne_bot (hp : p.Prime) (N : Subgroup G) (k : ℕ)
    (h : ∀ D : Subgroup G, IsElemAbelian p D → Nat.card D = p ^ (k + 1) → D ⊓ N ≠ ⊥) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ CFSG.Open.pRank p N + k := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup G)
  set m := CFSG.Open.pRank p (⊤ : Subgroup G)
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE₀ : IsElemAbelian p (E ⊓ N) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommE _ (Subgroup.mem_inf.mp a.2).1 _
      (Subgroup.mem_inf.mp b.2).1)⟩⟩, fun x hx => hE.2 x (Subgroup.mem_inf.mp hx).1⟩
  have hp0 : IsPGroup p ↥(E ⊓ N) := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hE₀.2 g g.2)⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hp0
  have hjN : j ≤ CFSG.Open.pRank p N := CFSG.SectionRank.le_pRank hp.one_lt inf_le_right hE₀ hj
  by_contra hcon
  push Not at hcon
  have hk : p ^ (k + 1) * Nat.card (E ⊓ N : Subgroup G) ≤ Nat.card E := by
    rw [hj, hcard, ← pow_add]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  obtain ⟨D, hDE, hD, hDc, hDE₀⟩ := exists_elemAbelian_le_inf_eq_bot hp hE inf_le_left (k + 1) hk
  apply h D hD hDc
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyD, hyN⟩ := Subgroup.mem_inf.mp hy
  have : y ∈ D ⊓ (E ⊓ N) := Subgroup.mem_inf.mpr ⟨hyD, Subgroup.mem_inf.mpr ⟨hDE hyD, hyN⟩⟩
  rw [hDE₀] at this
  exact this

end CFSG.HardMathSupport.Timmesfeld.Coordinator
