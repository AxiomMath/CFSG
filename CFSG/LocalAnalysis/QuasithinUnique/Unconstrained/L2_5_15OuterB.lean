module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Setup
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_le {p : ℕ} {E E' : Subgroup G} (h : CFSG.Assembly.IsElemAbelian p E')
    (hle : E ≤ E') : CFSG.Assembly.IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (isElemAbelian_mul_comm h (hle a.2) (hle b.2))⟩⟩,
    fun x hx => h.2 x (hle hx)⟩

omit [Finite G] in
theorem isElemAbelian_map_conj {p : ℕ} {E : Subgroup G} (h : CFSG.Assembly.IsElemAbelian p E)
    (g : G) : CFSG.Assembly.IsElemAbelian p (E.map (MulAut.conj g).toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map h _

theorem witt_step {t : G} {A F : Subgroup G} (htA : t ∉ A) (ht2 : t * t = 1)
    (hAt : ∀ a ∈ A, a * t = t * a)
    (hGt : ∀ g : G, g * t = t * g → ∃ c ∈ Subgroup.zpowers t, ∃ a ∈ A, g = c * a)
    (he8 : ∀ F' : Subgroup G, F' ≤ A → CFSG.Assembly.IsElemAbelian 2 F' → Nat.card F' = 8 →
      ∃ a ∈ A, CFSG.conjugate F a = F')
    (hQel : CFSG.Assembly.IsElemAbelian 2 (F ⊔ Subgroup.zpowers t))
    (hQcard : Nat.card ↥(F ⊔ Subgroup.zpowers t) = 16) {g : G}
    (hg : g⁻¹ * t * g ∈ F ⊔ Subgroup.zpowers t) :
    ∃ n ∈ Subgroup.normalizer ((F ⊔ Subgroup.zpowers t : Subgroup G) : Set G),
      g⁻¹ * t * g = n⁻¹ * t * n := by
  set Q : Subgroup G := F ⊔ Subgroup.zpowers t with hQ
  set Q' : Subgroup G := Q.map (MulAut.conj g).toMonoidHom with hQ'
  have happ : ∀ x : G, (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := fun x => rfl
  have htQ' : t ∈ Q' := ⟨g⁻¹ * t * g, hg, by rw [happ]; group⟩
  have hQ'el : CFSG.Assembly.IsElemAbelian 2 Q' := isElemAbelian_map_conj hQel g
  have hQ'card : Nat.card ↥Q' = 16 := by
    rw [hQ', Subgroup.card_map_of_injective (MulAut.conj g).injective, hQcard]
  have hQ'c : ∀ q ∈ Q', q * t = t * q := fun q hq => isElemAbelian_mul_comm hQ'el hq htQ'
  have hzQ' : Subgroup.zpowers t ≤ Q' := Subgroup.zpowers_le.mpr htQ'
  set F' : Subgroup G := Q' ⊓ A with hF'
  have hQ'eq : Q' = Subgroup.zpowers t ⊔ F' := by
    apply le_antisymm
    · intro q hq
      obtain ⟨c, hc, a, ha, rfl⟩ := hGt q (hQ'c q hq)
      have haQ' : a ∈ Q' := by
        have : c⁻¹ * (c * a) ∈ Q' := Q'.mul_mem (Q'.inv_mem (hzQ' hc)) hq
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right ⟨haQ', ha⟩)
    · exact sup_le hzQ' inf_le_left
  have hcommtF' : ∀ x ∈ Subgroup.zpowers t, ∀ y ∈ F', x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (show Commute t y from (hAt y hy.2).symm) m)).eq
  have hinf : Subgroup.zpowers t ⊓ F' = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    rw [Subgroup.mem_bot]
    rcases mem_zpowers_involution ht2 hy1 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hy2.2) htA
  have hzcard : Nat.card (Subgroup.zpowers t) = 2 := by
    have ht1 : t ≠ 1 := by
      intro h1
      exact htA (h1 ▸ A.one_mem)
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact ht2) ht1]
  have hF'card : Nat.card F' = 8 := by
    have h1 := BenderBranch.card_sup_of_commute_of_inf_eq_bot hcommtF' hinf
    rw [← hQ'eq, hQ'card, hzcard] at h1
    omega
  have hF'el : CFSG.Assembly.IsElemAbelian 2 F' := isElemAbelian_of_le hQ'el inf_le_left
  obtain ⟨a, haA, hconj⟩ := he8 F' inf_le_right hF'el hF'card
  have hQ'conj : ∀ q ∈ Q', a * q * a⁻¹ ∈ Q := by
    intro q hq
    rw [hQ'eq] at hq
    obtain ⟨c, hc, f, hf, rfl⟩ := mem_sup_of_commute hcommtF' hq
    have hca : a * c = c * a := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      exact ((Commute.zpow_right (show Commute a t from hAt a haA) m)).eq
    have hfF : a * f * a⁻¹ ∈ F := by
      rw [← hconj] at hf
      exact BenderBranch.mem_conjugate_iff.mp hf
    have hcF : c * (a * f * a⁻¹) ∈ Q := by
      rw [hQ, sup_comm]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hfF)
    have hcalc : a * (c * f) * a⁻¹ = c * (a * f * a⁻¹) := by
      calc a * (c * f) * a⁻¹ = (a * c) * f * a⁻¹ := by group
        _ = (c * a) * f * a⁻¹ := by rw [hca]
        _ = c * (a * f * a⁻¹) := by group
    rw [hcalc]
    exact hcF
  refine ⟨a * g, ?_, ?_⟩
  · apply Subgroup.mem_normalizer_fintype
    intro q hq
    have h1 : g * q * g⁻¹ ∈ Q' := ⟨q, hq, happ q⟩
    have h2 := hQ'conj _ h1
    have e : a * g * q * (a * g)⁻¹ = a * (g * q * g⁻¹) * a⁻¹ := by group
    rw [e]
    exact h2
  · have hat : a⁻¹ * t * a = t := by
      calc a⁻¹ * t * a = a⁻¹ * (t * a) := by group
        _ = a⁻¹ * (a * t) := by rw [hAt a haA]
        _ = t := by group
    calc g⁻¹ * t * g = g⁻¹ * (a⁻¹ * t * a) * g := by rw [hat]
      _ = (a * g)⁻¹ * t * (a * g) := by group

end Generic

section Config

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs) {t zK : G}

theorem isAutPair_of_outer (h : Lv2513 N t zK) (F : K33Facts N.K) {y : G} (hyS : y ∈ N.S)
    (hyo : ¬ Ch1.InducesInner y N.K) (hy2 : y * y ∈ N.K) :
    IsAutPair N.K (N.K ⊔ Subgroup.zpowers y) := by
  have hKH := H_le_normalizer_K N h F
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hZK : ∀ x ∈ N.K, (∀ w ∈ N.K, x * w = w * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have hyN : y ∈ Subgroup.normalizer (N.K : Set G) := N.S_le_normalizer_K hKH hyS
  have hyK : y ∉ N.K := fun hy => hyo (Ch1.InducesInner.of_mem hy)
  have hcov : ∀ a ∈ N.K ⊔ Subgroup.zpowers y, ∃ i : Fin 2, ∃ c ∈ N.K, a = c * (![1, y] i) := by
    intro a ha
    obtain ⟨k, hk, b, hb, rfl⟩ := mem_sup_of_le_normalizer (Subgroup.zpowers_le.mpr hyN) ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' m
    · refine ⟨0, k * (y * y) ^ j, N.K.mul_mem hk (Subgroup.zpow_mem _ hy2 j), ?_⟩
      simp only [Matrix.cons_val_zero, mul_one]
      rw [hj, zpow_mul, zpow_two]
    · refine ⟨1, k * (y * y) ^ j, N.K.mul_mem hk (Subgroup.zpow_mem _ hy2 j), ?_⟩
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hj, zpow_add_one, zpow_mul, zpow_two, mul_assoc]
  have hg : ∀ i : Fin 2, (![1, y] i) ∈ N.K ⊔ Subgroup.zpowers y := by
    rw [Fin.forall_fin_two]
    exact ⟨by simp, by simpa using Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩
  have hAle : N.K ≤ N.K ⊔ Subgroup.zpowers y := le_sup_left
  have hcardle : Nat.card ↥(N.K ⊔ Subgroup.zpowers y) ≤ 2 * Nat.card ↥N.K :=
    card_le_mul_of_cover hAle ![1, y] hg hcov
  have hne : N.K ⊔ Subgroup.zpowers y ≠ N.K := by
    intro heq
    apply hyK
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hge : 2 * Nat.card ↥N.K ≤ Nat.card ↥(N.K ⊔ Subgroup.zpowers y) := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hAle
    have hKpos : 0 < Nat.card ↥N.K := Nat.card_pos
    have hm0 : m ≠ 0 := by
      rintro rfl
      have := Nat.card_pos (α := ↥(N.K ⊔ Subgroup.zpowers y))
      omega
    have hm1 : m ≠ 1 := by
      rintro rfl
      apply hne
      symm
      exact Subgroup.eq_of_le_of_card_ge hAle (by omega)
    have : 2 ≤ m := by omega
    calc 2 * Nat.card ↥N.K ≤ m * Nat.card ↥N.K := Nat.mul_le_mul_right _ this
      _ = Nat.card ↥(N.K ⊔ Subgroup.zpowers y) := by rw [hm, mul_comm]
  refine ⟨hAle, le_antisymm hcardle hge, ?_⟩
  rw [eq_bot_iff]
  rintro a ⟨haA, haC⟩
  rw [Subgroup.mem_bot]
  have haC' : ∀ x ∈ N.K, x * a = a * x := fun x hx => Subgroup.mem_centralizer_iff.mp haC x hx
  obtain ⟨i, c, hc, hai⟩ := hcov a haA
  fin_cases i
  · simp at hai
    subst hai
    exact hZK _ hc fun w hw => (haC' w hw).symm
  · exfalso
    simp at hai
    apply hyo
    refine ⟨c⁻¹, N.K.inv_mem hc, fun x hx => ?_⟩
    have hy : y = c⁻¹ * a := by rw [hai]; group
    have hcx : c * x * c⁻¹ ∈ N.K := N.K.mul_mem (N.K.mul_mem hc hx) (N.K.inv_mem hc)
    have h1 := haC' _ hcx
    calc y⁻¹ * x * y = (c⁻¹ * a)⁻¹ * x * (c⁻¹ * a) := by rw [← hy]
      _ = a⁻¹ * (c * x * c⁻¹) * a := by group
      _ = a⁻¹ * (a * (c * x * c⁻¹)) := by rw [mul_assoc, ← h1]
      _ = (c⁻¹)⁻¹ * x * c⁻¹ := by group

end Config

end CFSG.QuasithinUnique.Unc25K1
