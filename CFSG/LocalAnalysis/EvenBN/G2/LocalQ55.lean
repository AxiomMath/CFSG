module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQ52

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

theorem ElemModulo.mono {N N' E : Subgroup G} (h : ElemModulo N E) (hNN' : N ≤ N') :
    ElemModulo N' E := fun x hx y hy => ⟨hNN' (h x hx y hy).1, hNN' (h x hx y hy).2⟩

theorem ElemModulo.anti {N E E' : Subgroup G} (h : ElemModulo N E) (hE : E' ≤ E) :
    ElemModulo N E' := fun x hx y hy => h x (hE hx) y (hE hy)

theorem normalizer_le_normalizer_of_characteristic_subgroupOf {X H : Subgroup G} (hXH : X ≤ H)
    (hc : (X.subgroupOf H).Characteristic) :
    normalizer (H : Set G) ≤ normalizer (X : Set G) := by
  haveI := hc
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (X.subgroupOf H)
  rwa [Subgroup.map_subgroupOf_eq_of_le hXH] at h1

theorem le_normalizer_of_elemModulo {N E : Subgroup G} (hNE : N ≤ E) (h : ElemModulo N E) :
    E ≤ normalizer (N : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  have key : ∀ a ∈ E, ∀ n ∈ N, a * n * a⁻¹ ∈ N := fun a ha n hn => by
    have h2 := (h a ha n (hNE hn)).2
    rw [commutatorElement_def] at h2
    have := mul_mem h2 hn
    rwa [show a * n * a⁻¹ * n⁻¹ * n = a * n * a⁻¹ by group] at this
  intro n
  refine ⟨key a ha n, fun hn => ?_⟩
  have := key a⁻¹ (inv_mem ha) _ hn
  rwa [show a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n by group] at this

theorem elemModulo_map_conj' {N E : Subgroup G} {g : G} (hgN : g ∈ normalizer (N : Set G))
    (hE : ElemModulo N E) : ElemModulo N (E.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨h1, h2⟩ := hE x hx y hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨?_, ?_⟩
  · rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group]
    exact (mem_normalizer_iff.1 hgN _).1 h1
  · rw [commutatorElement_def] at h2 ⊢
    rw [show g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ =
      g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ by group]
    exact (mem_normalizer_iff.1 hgN _).1 h2

theorem elemModulo_sup_of_normalizes {N A B : Subgroup G} (hNA : N ≤ A) (hNB : N ≤ B)
    (hAB : A ⊓ B ≤ N) (hA : A ≤ normalizer (B : Set G)) (hB : B ≤ normalizer (A : Set G))
    (hEA : ElemModulo N A) (hEB : ElemModulo N B) : ElemModulo N (A ⊔ B) := by
  have hAN := le_normalizer_of_elemModulo hNA hEA
  have hBN := le_normalizer_of_elemModulo hNB hEB
  have hXN : A ⊔ B ≤ normalizer (N : Set G) := sup_le hAN hBN
  have hconj : ∀ x ∈ A ⊔ B, ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun x hx n hn =>
    (mem_normalizer_iff.1 (hXN hx) n).1 hn
  have hAB' : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ N := fun a ha b hb => by
    apply hAB
    refine ⟨?_, ?_⟩
    · have h1 : b * a⁻¹ * b⁻¹ ∈ A := (mem_normalizer_iff.1 (hB hb) a⁻¹).1 (inv_mem ha)
      have := mul_mem ha h1
      rwa [show a * (b * a⁻¹ * b⁻¹) = ⁅a, b⁆ by simp [commutatorElement_def, mul_assoc]] at this
    · have h1 : a * b * a⁻¹ ∈ B := (mem_normalizer_iff.1 (hA ha) b).1 hb
      have := mul_mem h1 (inv_mem hb)
      rwa [show a * b * a⁻¹ * b⁻¹ = ⁅a, b⁆ by simp [commutatorElement_def]] at this
  have hBA' : ∀ b ∈ B, ∀ a ∈ A, ⁅b, a⁆ ∈ N := fun b hb a ha => by
    have := inv_mem (hAB' a ha b hb)
    rwa [commutatorElement_inv] at this
  have hfac := Common.exists_mul_of_le_normalizer' hA
  have hAy : ∀ a ∈ A, ∀ y ∈ A ⊔ B, ⁅a, y⁆ ∈ N := fun a ha y hy => by
    obtain ⟨a', ha', b', hb', rfl⟩ := hfac y hy
    have e : ⁅a, a' * b'⁆ = ⁅a, a'⁆ * (a' * ⁅a, b'⁆ * a'⁻¹) := by
      simp [commutatorElement_def]; group
    rw [e]
    exact mul_mem (hEA a ha a' ha').2 (hconj a' (mem_sup_left ha') _ (hAB' a ha b' hb'))
  have hBy : ∀ b ∈ B, ∀ y ∈ A ⊔ B, ⁅b, y⁆ ∈ N := fun b hb y hy => by
    obtain ⟨a', ha', b', hb', rfl⟩ := hfac y hy
    have e : ⁅b, a' * b'⁆ = ⁅b, a'⁆ * (a' * ⁅b, b'⁆ * a'⁻¹) := by
      simp [commutatorElement_def]; group
    rw [e]
    exact mul_mem (hBA' b hb a' ha') (hconj a' (mem_sup_left ha') _ (hEB b hb b' hb').2)
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hfac x hx
  refine ⟨?_, ?_⟩
  ·
    have e : a * b * (a * b) = (a * ⁅b, a⁆ * a⁻¹) * (a * a) * (b * b) := by
      simp [commutatorElement_def]; group
    rw [e]
    exact mul_mem (mul_mem (hconj a (mem_sup_left ha) _ (hBA' b hb a ha)) (hEA a ha a ha).1)
      (hEB b hb b hb).1
  · have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp [commutatorElement_def]; group
    rw [e]
    exact mul_mem (hconj a (mem_sup_left ha) _ (hBy b hb y hy)) (hAy a ha y hy)

theorem normalizer_of_le_commutator_sup {P M D F J : Subgroup G}
    (hFM : F ≤ M) (hPF : P ≤ normalizer (F : Set G)) (hJM : J ≤ normalizer (M : Set G))
    (hPMD : ∀ p ∈ P, ∃ m ∈ M, ∃ d ∈ D, p = m * d) (hDJ : ∀ j ∈ J, ∀ d ∈ D, ⁅j, d⁆ ∈ F)
    (hM : M ≤ ⁅J, P⁆ ⊔ F) : P ≤ normalizer (M : Set G) := by
  have h1 : ⁅J, P⁆ ≤ M := by
    refine commutator_le.2 fun j hj p hp => ?_
    obtain ⟨m, hm, d, hd, rfl⟩ := hPMD p hp
    have e : ⁅j, m * d⁆ = ⁅j, m⁆ * (m * ⁅j, d⁆ * m⁻¹) := by
      simp [commutatorElement_def]; group
    rw [e]
    refine mul_mem ?_ (mul_mem (mul_mem hm (hFM (hDJ j hj d hd))) (inv_mem hm))
    have := (mem_normalizer_iff.1 (hJM hj) m).1 hm
    exact mul_mem this (inv_mem hm)
  have hQ : M = ⁅J, P⁆ ⊔ F := le_antisymm hM (sup_le h1 hFM)
  have h2 : ∀ p ∈ P, ∀ q ∈ ⁅J, P⁆ ⊔ F, p * q * p⁻¹ ∈ ⁅J, P⁆ ⊔ F := by
    intro p hp
    have hle : ⁅J, P⁆ ⊔ F ≤ ((⁅J, P⁆ ⊔ F).comap (MulAut.conj p).toMonoidHom) := by
      refine sup_le (commutator_le.2 fun j hj x hx => ?_) fun f hf => ?_
      · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have e : p * ⁅j, x⁆ * p⁻¹ = (⁅j, p⁆)⁻¹ * ⁅j, p * x⁆ := by
          simp [commutatorElement_def]; group
        rw [e]
        exact mul_mem (inv_mem (mem_sup_left (commutator_mem_commutator hj hp)))
          (mem_sup_left (commutator_mem_commutator hj (mul_mem hp hx)))
      · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_right ((mem_normalizer_iff.1 (hPF hp) f).1 hf)
    intro q hq
    exact hle hq
  have hP : ∀ p ∈ P, ∀ q ∈ M, p * q * p⁻¹ ∈ M := fun p hp q hq => by
    rw [hQ] at hq ⊢
    exact h2 p hp q hq
  intro p hp
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hP p hp x, fun hx => ?_⟩
  have := hP p⁻¹ (inv_mem hp) _ hx
  rwa [show p⁻¹ * (p * x * p⁻¹) * p⁻¹⁻¹ = x by group] at this

theorem le_commutator_sup_of_forall_fixed [Finite G] {J M F : Subgroup G} (hFM : F ≤ M)
    (hMabel : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ F) (hJM : J ≤ normalizer (M : Set G))
    (hJF : J ≤ normalizer (F : Set G)) (hsolv : Group.IsSolvable M)
    (hcop : (Nat.card J).Coprime (Nat.card M))
    (hfix : ∀ c ∈ M ⊓ centralizer (J : Set G), c ∈ F) : M ≤ ⁅J, M⁆ ⊔ F := by
  set Q : Subgroup G := ⁅J, M⁆ ⊔ F with hQdef
  have hcM : ⁅J, M⁆ ≤ M := commutator_le.2 fun j hj m hm => by
    have := (mem_normalizer_iff.1 (hJM hj) m).1 hm
    exact mul_mem this (inv_mem hm)
  have hQM : Q ≤ M := sup_le hcM hFM
  have hMQ : M ≤ normalizer (Q : Set G) := by
    intro m hm
    rw [mem_normalizer_iff]
    have key : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := fun m hm q hq => by
      have h2 := hMabel m hm q (hQM hq)
      have : ⁅m, q⁆ * q ∈ Q := mul_mem (mem_sup_right h2) hq
      rwa [show ⁅m, q⁆ * q = m * q * m⁻¹ by simp [commutatorElement_def]] at this
    intro x
    refine ⟨key m hm x, fun hx => ?_⟩
    have := key m⁻¹ (inv_mem hm) _ hx
    rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at this
  have hJQ : J ≤ normalizer (Q : Set G) := by
    intro j hj
    rw [mem_normalizer_iff]
    have key : ∀ j ∈ J, ∀ q ∈ Q, j * q * j⁻¹ ∈ Q := fun j hj q hq => by
      have hle : Q ≤ Q.comap (MulAut.conj j).toMonoidHom := by
        refine sup_le (commutator_le.2 fun j' hj' m hm => ?_) fun f hf => ?_
        · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          have e : j * ⁅j', m⁆ * j⁻¹ = ⁅j * j' * j⁻¹, j * m * j⁻¹⁆ := by
            simp [commutatorElement_def]; group
          rw [e]
          exact mem_sup_left (commutator_mem_commutator (mul_mem (mul_mem hj hj') (inv_mem hj))
            ((mem_normalizer_iff.1 (hJM hj) m).1 hm))
        · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact mem_sup_right ((mem_normalizer_iff.1 (hJF hj) f).1 hf)
      exact hle hq
    intro x
    refine ⟨key j hj x, fun hx => ?_⟩
    have := key j⁻¹ (inv_mem hj) _ hx
    rwa [show j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x by group] at this
  intro m hm
  have hfixm : ∀ j ∈ J, m⁻¹ * (j * m * j⁻¹) ∈ Q := fun j hj => by
    have h1 : ⁅j, m⁻¹⁆ ∈ ⁅J, M⁆ := commutator_mem_commutator hj (inv_mem hm)
    have e : m⁻¹ * (j * m * j⁻¹) = (⁅j, m⁻¹⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact inv_mem (mem_sup_left h1)
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime hQM hMQ hJM hJQ
    hsolv hcop hm hfixm
  exact mul_mem (mem_sup_right (hfix c hc)) hn

theorem zpow_eq_one_or_eq_of_mul_self_eq_one {t : G} (ht2 : t * t = 1) (k : ℤ) :
    t ^ k = 1 ∨ t ^ k = t := by
  have ht : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, ht, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, ht, one_zpow, one_mul]

theorem mem_of_mem_sup_zpowers_of_mul_self_eq_one {A B : Subgroup G} {t : G} (ht2 : t * t = 1)
    (htA : t ∈ normalizer (A : Set G)) (hAB : A ≤ B) (htB : t ∉ B) {a : G}
    (ha : a ∈ A ⊔ zpowers t) (haB : a ∈ B) : a ∈ A := by
  obtain ⟨x, hx, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer
    ((zpowers_le).2 htA) a ha
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
  rcases zpow_eq_one_or_eq_of_mul_self_eq_one ht2 k with hk | hk
  · rw [hk, mul_one]
    exact hx
  · exfalso
    rw [hk] at haB
    exact htB (by simpa using mul_mem (inv_mem (hAB hx)) haB)

theorem mem_normalizer_sup_zpowers [Finite G] {U : Subgroup G} {t a : G} (ht2 : t * t = 1)
    (htU : t ∈ normalizer (U : Set G)) (haU : a ∈ normalizer (U : Set G))
    (hat : t * a * t * a⁻¹ ∈ U) : a ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun z hz => ?_
  obtain ⟨v, hv, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htU) z hz
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
  have hu : a * t * a⁻¹ = t * (t * a * t * a⁻¹) := by
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ht2, one_mul]
  have e : a * (v * t ^ k) * a⁻¹ = (a * v * a⁻¹) * (a * t * a⁻¹) ^ k := by
    rw [conj_zpow]
    group
  rw [e, hu]
  refine mul_mem (mem_sup_left ((mem_normalizer_iff.1 haU v).1 hv)) (zpow_mem ?_ k)
  exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hat)

theorem mem_normalizer_inf_centralizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((X ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (X : Set G), ∀ z ∈ X ⊓ centralizer (X : Set G),
      g * z * g⁻¹ ∈ X ⊓ centralizer (X : Set G) := fun g hg z hz => by
    refine ⟨(mem_normalizer_iff.1 hg z).1 hz.1, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ X := by
      have := (mem_normalizer_iff.1 (inv_mem hg) y).1 hy
      simpa using this
    have := mem_centralizer_iff.1 hz.2 _ hy'
    calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = g * z * g⁻¹ * y := by group
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem mem_map_upperCentralSeries_succ {P : Subgroup G} {n : ℕ} {x : G} :
    x ∈ (Subgroup.upperCentralSeries P (n + 1)).map P.subtype ↔
      x ∈ P ∧ ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ (Subgroup.upperCentralSeries P n).map P.subtype := by
  constructor
  · rintro ⟨⟨x, hxP⟩, hx, rfl⟩
    refine ⟨hxP, fun y hy => ?_⟩
    have := (Subgroup.mem_upperCentralSeries_succ_iff.1 hx) ⟨y, hy⟩
    exact ⟨_, this, by simp [commutatorElement_def]⟩
  · rintro ⟨hxP, hx⟩
    refine ⟨⟨x, hxP⟩, Subgroup.mem_upperCentralSeries_succ_iff.2 fun y => ?_, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hx y y.2
    have : z = ⟨x * y * x⁻¹ * y⁻¹, by
      exact mul_mem (mul_mem (mul_mem hxP y.2) (inv_mem hxP)) (inv_mem y.2)⟩ :=
      Subtype.ext hzy
    rwa [this] at hz

theorem isSolvable_of_isPGroup_two [Finite G] {H : Subgroup G} (hp : IsPGroup 2 H) :
    Group.IsSolvable H := by
  have : Group.IsNilpotent H := hp.isNilpotent
  infer_instance

theorem ncard_mul_set_mul_card_inf (A B : Subgroup G) :
    ((A : Set G) * (B : Set G)).ncard * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient B (A : Set G)
  have himg : Nat.card ↥((A : Set G).image ((↑) : G → G ⧸ B)) = B.relIndex A := by
    have horb : MulAction.orbit ↥A ((1 : G) : G ⧸ B) = (A : Set G).image ((↑) : G → G ⧸ B) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(a : G), a.2, by simp [Subgroup.smul_def]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, by simp [Subgroup.smul_def]⟩
    have hstab : MulAction.stabilizer ↥A ((1 : G) : G ⧸ B) = B.subgroupOf A := by
      ext a
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have : (a • ((1 : G) : G ⧸ B)) = ((a : G) : G ⧸ B) := by
        simp [Subgroup.smul_def]
      rw [this, QuotientGroup.eq]
      constructor
      · intro h
        simpa using B.inv_mem h
      · intro h
        simpa using B.inv_mem h
    have := MulAction.index_stabilizer ↥A ((1 : G) : G ⧸ B)
    rw [hstab] at this
    rw [← horb, Nat.card_coe_set_eq, ← this]
    rfl
  have h2 := Subgroup.relIndex_mul_card B A
  rw [inf_comm B A] at h2
  rw [← Nat.card_coe_set_eq, h1, himg]
  calc Nat.card ↥B * B.relIndex A * Nat.card ↥(A ⊓ B)
      = Nat.card ↥B * (B.relIndex A * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h2]; ring

theorem card_mul_card_eq_of_card_quotient_eq {A B C D : Subgroup G} (hBA : B ≤ A) (hDC : D ≤ C)
    (h : Nat.card (↥A ⧸ B.subgroupOf A) = Nat.card (↥C ⧸ D.subgroupOf C)) :
    Nat.card A * Nat.card D = Nat.card C * Nat.card B := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf C)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv] at h2
  rw [h1, h2, h]
  ring

theorem mem_of_map_upperCentralSeries_succ {P Z Z' : Subgroup G} {n : ℕ}
    (hZ : (Subgroup.upperCentralSeries P n).map P.subtype = Z)
    (hZ' : (Subgroup.upperCentralSeries P (n + 1)).map P.subtype = Z') {x : G} :
    x ∈ Z' ↔ x ∈ P ∧ ∀ g ∈ P, x * g * x⁻¹ * g⁻¹ ∈ Z := by
  have hmem : ∀ y : P, y ∈ Subgroup.upperCentralSeries P n ↔ (y : G) ∈ Z := fun y => by
    rw [← hZ]
    exact (mem_map_iff_mem P.subtype_injective).symm
  rw [← hZ']
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_upperCentralSeries_succ_iff] at hy
    refine ⟨y.2, fun g hg => ?_⟩
    have := (hmem _).1 (hy ⟨g, hg⟩)
    simpa [commutatorElement_def] using this
  · rintro ⟨hxP, hx⟩
    refine ⟨⟨x, hxP⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_upperCentralSeries_succ_iff]
    intro g
    rw [hmem]
    simpa [commutatorElement_def] using hx g g.2

theorem mem_normalizer_centralizerModulo [Finite G] {Q P : Subgroup G} {g : G}
    (hQ : g ∈ normalizer (Q : Set G)) (hP : g ∈ normalizer (P : Set G)) :
    g ∈ normalizer ((centralizerModulo Q P : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun m hm => ?_
  refine ⟨mul_mem (mul_mem hQ hm.1) (inv_mem hQ), fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g ∈ P := by
    have := (mem_normalizer_iff.1 (inv_mem hP) x).1 hx
    rwa [inv_inv] at this
  have h1 := (mem_normalizer_iff.1 hQ _).1 (hm.2 _ hx')
  rwa [show g * (m * (g⁻¹ * x * g) * m⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ =
    g * m * g⁻¹ * x * (g * m * g⁻¹)⁻¹ * x⁻¹ by group] at h1

theorem mem_normalizer_inf_centralizer_of_mem {X N : Subgroup G} {g : G}
    (hX : g ∈ normalizer (X : Set G)) (hN : g ∈ normalizer (N : Set G)) :
    g ∈ normalizer ((X ⊓ centralizer (N : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (X : Set G) → g ∈ normalizer (N : Set G) →
      ∀ z ∈ X ⊓ centralizer (N : Set G), g * z * g⁻¹ ∈ X ⊓ centralizer (N : Set G) := by
    intro g hgX hgN z hz
    obtain ⟨hzX, hzC⟩ := Subgroup.mem_inf.1 hz
    refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hgX z).1 hzX,
      mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ N := by
      have := (mem_normalizer_iff.1 (inv_mem hgN) y).1 hy
      rwa [inv_inv] at this
    have h1 := mem_centralizer_iff.1 hzC _ hy'
    calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * y := by group
  rw [mem_normalizer_iff]
  intro z
  exact ⟨key g hX hN z, fun hz => by
    have := key g⁻¹ (inv_mem hX) (inv_mem hN) _ hz
    rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at this⟩

theorem commutator_mul_of_comm {A : Subgroup G} {t : G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (htA : t ∈ normalizer (A : Set G))
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : ⁅t, a * b⁆ = ⁅t, a⁆ * ⁅t, b⁆ := by
  have hu : t * b * t⁻¹ ∈ A := (mem_normalizer_iff.1 htA b).1 hb
  have hc : (t * b * t⁻¹ * b⁻¹) * a⁻¹ = a⁻¹ * (t * b * t⁻¹ * b⁻¹) :=
    hA _ (mul_mem hu (inv_mem hb)) _ (inv_mem ha)
  calc ⁅t, a * b⁆ = (t * a * t⁻¹) * ((t * b * t⁻¹ * b⁻¹) * a⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = (t * a * t⁻¹) * (a⁻¹ * (t * b * t⁻¹ * b⁻¹)) := by rw [hc]
    _ = ⁅t, a⁆ * ⁅t, b⁆ := by simp only [commutatorElement_def]; group

theorem commutator_inv_of_comm {A : Subgroup G} {t : G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (htA : t ∈ normalizer (A : Set G))
    {a : G} (ha : a ∈ A) : ⁅t, a⁻¹⁆ = ⁅t, a⁆⁻¹ := by
  have hu : t * a⁻¹ * t⁻¹ ∈ A := (mem_normalizer_iff.1 htA a⁻¹).1 (inv_mem ha)
  have hc : (t * a⁻¹ * t⁻¹) * a = a * (t * a⁻¹ * t⁻¹) := hA _ hu _ ha
  calc ⁅t, a⁻¹⁆ = (t * a⁻¹ * t⁻¹) * a := by simp only [commutatorElement_def]; group
    _ = a * (t * a⁻¹ * t⁻¹) := hc
    _ = ⁅t, a⁆⁻¹ := by simp only [commutatorElement_def]; group

theorem eq_or_eq_of_commutator_section {A Y V B : Subgroup G} {t : G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (htA : t ∈ normalizer (A : Set G))
    (hYV : Y ≤ V) (hVA : V ≤ A) (hker : A ⊓ centralizer ({t} : Set G) = Y)
    (hκ : ∀ a ∈ A, ⁅t, a⁆ ∈ Y) (hBt : B ≤ centralizer ({t} : Set G))
    (hBV : B ≤ normalizer (V : Set G))
    (hirr : ∀ E : Subgroup G, E ≤ Y → B ≤ normalizer (E : Set G) → E = ⊥ ∨ E = Y) :
    V = Y ∨ V = A := by
  let E : Subgroup G :=
    { carrier := {z | ∃ v ∈ V, z = ⁅t, v⁆}
      one_mem' := ⟨1, one_mem _, by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro _ _ ⟨v₁, hv₁, rfl⟩ ⟨v₂, hv₂, rfl⟩
        exact ⟨v₁ * v₂, mul_mem hv₁ hv₂,
          (commutator_mul_of_comm hA htA (hVA hv₁) (hVA hv₂)).symm⟩
      inv_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨v⁻¹, inv_mem hv, (commutator_inv_of_comm hA htA (hVA hv)).symm⟩ }
  have hmemE : ∀ v ∈ V, ⁅t, v⁆ ∈ E := fun v hv => ⟨v, hv, rfl⟩
  have hEY : E ≤ Y := by
    rintro _ ⟨v, hv, rfl⟩
    exact hκ v (hVA hv)
  have hBE : B ≤ normalizer (E : Set G) := by
    have key : ∀ l ∈ B, ∀ z ∈ E, l * z * l⁻¹ ∈ E := by
      rintro l hl _ ⟨v, hv, rfl⟩
      refine ⟨l * v * l⁻¹, (mem_normalizer_iff.1 (hBV hl) v).1 hv, ?_⟩
      have hlt : l * t = t * l := mem_centralizer_singleton_iff.1 (hBt hl)
      have hlt' : l * t * l⁻¹ = t := by rw [hlt]; group
      calc l * ⁅t, v⁆ * l⁻¹ =
          (l * t * l⁻¹) * (l * v * l⁻¹) * (l * t * l⁻¹)⁻¹ * (l * v * l⁻¹)⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = ⁅t, l * v * l⁻¹⁆ := by rw [hlt']; rfl
    intro l hl
    rw [mem_normalizer_iff]
    intro z
    exact ⟨key l hl z, fun hz => by
      have := key l⁻¹ (inv_mem hl) _ hz
      rwa [show l⁻¹ * (l * z * l⁻¹) * l⁻¹⁻¹ = z by group] at this⟩
  have hker' : ∀ v ∈ A, ⁅t, v⁆ = 1 → v ∈ Y := fun v hv h1 => by
    rw [← hker]
    exact Subgroup.mem_inf.2 ⟨hv, mem_centralizer_singleton_iff.2
      (commutatorElement_eq_one_iff_mul_comm.1 h1).symm⟩
  rcases hirr E hEY hBE with hE | hE
  · left
    refine le_antisymm (fun v hv => hker' v (hVA hv) ?_) hYV
    have : ⁅t, v⁆ ∈ E := hmemE v hv
    rw [hE] at this
    exact Subgroup.mem_bot.1 this
  · right
    refine le_antisymm hVA (fun a ha => ?_)
    have h1 : ⁅t, a⁆ ∈ E := by rw [hE]; exact hκ a ha
    obtain ⟨v, hv, hva⟩ := h1
    have h2 : ⁅t, a * v⁻¹⁆ = 1 := by
      rw [commutator_mul_of_comm hA htA ha (inv_mem (hVA hv)),
        commutator_inv_of_comm hA htA (hVA hv), ← hva, mul_inv_cancel]
    have h3 : a * v⁻¹ ∈ Y := hker' _ (mul_mem ha (inv_mem (hVA hv))) h2
    have := mul_mem (hYV h3) hv
    rwa [inv_mul_cancel_right] at this

theorem commutator_mul_mem_iff_of_mem_normalizer {Z : Subgroup G} {j a z : G}
    (hjZ : j ∈ normalizer (Z : Set G)) (haZ : a ∈ normalizer (Z : Set G)) (hz : z ∈ Z) :
    ⁅j, a * z⁆ ∈ Z ↔ ⁅j, a⁆ ∈ Z := by
  have h1 : j * z * j⁻¹ * z⁻¹ ∈ Z := mul_mem ((mem_normalizer_iff.1 hjZ z).1 hz) (inv_mem hz)
  have h2 : a * (j * z * j⁻¹ * z⁻¹) * a⁻¹ ∈ Z := (mem_normalizer_iff.1 haZ _).1 h1
  have e : ⁅j, a * z⁆ = ⁅j, a⁆ * (a * (j * z * j⁻¹ * z⁻¹) * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem_cancel_right Z h2

theorem commutator_mem_of_mem_sup_of_forall {T Z : Subgroup G} {j : G}
    (hjZ : j ∈ normalizer (Z : Set G)) (hTZ : T ≤ normalizer (Z : Set G))
    (hT : ∀ a ∈ T, ⁅j, a⁆ ∈ Z) : ∀ y ∈ T ⊔ Z, ⁅j, y⁆ ∈ Z := by
  intro y hy
  obtain ⟨a, ha, z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer' hTZ y hy
  exact (commutator_mul_mem_iff_of_mem_normalizer hjZ (hTZ ha) hz).2 (hT a ha)

theorem commutator_mem_of_series_elemModulo [Finite G] {A B Z J : Subgroup G} (hZB : Z ≤ B)
    (hBA : B ≤ A) (hA : ElemModulo Z A) (hJA : J ≤ normalizer (A : Set G))
    (hJZ : J ≤ normalizer (Z : Set G))
    (hcop : (Nat.card J).Coprime (Nat.card A))
    (h1 : ∀ j ∈ J, ∀ x ∈ A, ⁅j, x⁆ ∈ B) (h2 : ∀ j ∈ J, ∀ y ∈ B, ⁅j, y⁆ ∈ Z) :
    ∀ j ∈ J, ∀ x ∈ A, ⁅j, x⁆ ∈ Z := by
  have hZA : Z ≤ A := hZB.trans hBA
  have key : ∀ g ∈ A, ∀ w ∈ Z, g * w * g⁻¹ ∈ Z := fun g hg w hw => by
    have := mul_mem (hA g hg w (hZA hw)).2 hw
    rwa [commutatorElement_def, inv_mul_cancel_right] at this
  have hAZ : A ≤ normalizer (Z : Set G) := fun g hg => by
    refine mem_normalizer_iff.2 fun z => ⟨key g hg z, fun hz => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ hz
    rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at this
  intro j hj x hx
  refine mem_of_mem_commutator_of_forall hZA hAZ (fun x hx y hy => (hA x hx y hy).2) hJA hJZ hcop
    ?_ ?_
  · rw [← commutatorElement_inv x j]
    exact inv_mem (Subgroup.commutator_mem_commutator hx hj)
  · intro j' hj'
    have hcB := h1 j hj x hx
    have h3 := h2 j' hj' _ hcB
    have h4 := key _ (inv_mem (hBA hcB)) _ h3
    have e : ⁅j, x⁆⁻¹ * ⁅j', ⁅j, x⁆⁆ * ⁅j, x⁆⁻¹⁻¹ = ⁅j, x⁆⁻¹ * (j' * ⁅j, x⁆ * j'⁻¹) := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h4

end Generic

section ModelLevi

variable {K : Type} [Field K]

theorem Model.leviA_le_sup_conj :
    Model.leviA K ≤ Model.S K ⊔ (Model.S K).map (MulAut.conj (Model.wa K)).toMonoidHom := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact mem_sup_left (xUnit_mem_posUnipotent g2ir c)
  · refine mem_sup_right ⟨xUnit .G2 K g2ir (-c), xUnit_mem_posUnipotent g2ir (-c), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Model.wa]
    exact (yUnit_eq_conj g2ir c).symm

end ModelLevi

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem map_wa_map_wa (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (X : Subgroup G) :
    (X.map (MulAut.conj d.wa).toMonoidHom).map (MulAut.conj d.wa).toMonoidHom = X := by
  have hwa : d.wa * d.wa = 1 := (d.yamada_3_7_G (hK ▸ h.four_le)).2.2.1
  ext x
  rw [mem_map_conj_iff, mem_map_conj_iff, inv_eq_of_mul_eq_one_right hwa]
  have : d.wa * (d.wa * x * d.wa) * d.wa = x := by
    calc d.wa * (d.wa * x * d.wa) * d.wa = (d.wa * d.wa) * x * (d.wa * d.wa) := by group
      _ = x := by rw [hwa]; group
  rw [this]

theorem yamadaD₁_le_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaD₁ d t ≤ yamadaD₇ d t := by
  obtain ⟨hjoin, -, hinf⟩ := h.yamada_5_54_1 hW d hK hQ
  calc yamadaD₁ d t = yamadaD₃ d t ⊓ (yamadaD₃ d t).map (MulAut.conj d.wa).toMonoidHom :=
        hinf.symm
    _ ≤ yamadaD₃ d t := inf_le_left
    _ ≤ yamadaD₃ d t ⊔ (yamadaD₃ d t).map (MulAut.conj d.wa).toMonoidHom := le_sup_left
    _ = yamadaD₇ d t := hjoin.symm

theorem wa_mem_normalizer_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.wa ∈ normalizer (yamadaD₇ d t : Set G) := by
  obtain ⟨hjoin, -, -⟩ := h.yamada_5_54_1 hW d hK hQ
  refine mem_normalizer_of_map_conj_eq ?_
  rw [hjoin, Subgroup.map_sup, map_wa_map_wa h d hK, sup_comm]

theorem yamadaC₁_le_yamadaCstar (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaC₁ d t ≤ yamadaCstar d t := by
  obtain ⟨⟨-, -, hC₁inf⟩, -⟩ := h.yamada_5_19 d hK hD
  rw [← hC₁inf]
  exact inf_le_left

theorem inf_normalizer_U_le_normalizer_yamadaC₇ (h : Setup G L f t) (d : G2Data L K) :
    L ⊓ normalizer (d.U : Set G) ≤ normalizer (yamadaC₇ d t : Set G) := fun n hn =>
  LieType.BorelTits.le_normalizer_pCoreOf 2 _ (h.inf_normalizer_U_le_normalizer_yamadaC₁ d hn)

theorem card_yamadaD₁_of_doubling (h : Setup G L f t) (d : G2Data L K) (hD : h.DoublingFacts d) :
    Nat.card (yamadaD₁ d t) = Nat.card K ^ 6 := by
  have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaU₁ d t) (B := d.D)
    (fun x hx => Subgroup.centralizer_le_normalizer _ (hD.D_le_centralizer hx))
  rw [sup_comm, ← hD.D₁_eq, hD.inf_D, hD.card_eq, d.cards.1, d.cards.2.2.2.2.2.1] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [h1]
  ring

theorem card_yamadaC₁_six (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    Nat.card (yamadaC₁ d t) = 2 * Nat.card K ^ 6 := by
  obtain ⟨_, φ, -, -⟩ := h.yamada_5_3_4 d hK
  have htN : zpowers t ≤ normalizer (d.D : Set G) := (zpowers_le).2
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun m hm =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hm))))
  have h2 := Common.card_sup_mul_card_inf_eq htN
  rw [inf_comm, h.zpowers_inf_L (E := d.D) (d.image_le _), Subgroup.card_bot, mul_one,
    h.card_zpowers_t] at h2
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((d.D ⊔ zpowers t).subgroupOf (yamadaC₁ d t))
  rw [Nat.card_congr φ.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (h.tD_le_yamadaC₁ d hK)).toEquiv, h2,
    d.cards.1, d.cards.2.2.2.2.2.1] at h1
  rw [h1]
  ring

theorem card_yamadaC₇ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hQ : h.QFacts d) : Nat.card (yamadaC₇ d t) = 2 * Nat.card K ^ 10 := by
  have hD := hQ.doubling
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -, -, -, -⟩ := d.inclusions
  have hC₁C₇ : yamadaC₁ d t ≤ yamadaCstar d t :=
    (h.yamadaCstar_eq d hK hD) ▸ h.yamadaC₁_le_yamadaV d hK hD
  have hUD : d.U ≤ d.D := hUY.trans (hYX.trans (hXF.trans hFD))
  obtain ⟨_, _, φ, -, -⟩ := h.yamada_5_19_4 d hK hD
  have hcard := card_mul_card_eq_of_card_quotient_eq hC₁C₇ hUD (Nat.card_congr φ.toEquiv)
  rw [h.card_yamadaC₁_six d hK, d.cards.1, d.cards.2.2.2.2.2.1] at hcard
  have hq : 0 < Nat.card K := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  show Nat.card (yamadaCstar d t) * Nat.card K = _
  rw [hcard]
  ring

theorem card_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (yamadaD₇ d t) = Nat.card K ^ 10 := by
  obtain ⟨-, -, ⟨hsup, htN, htD⟩⟩ := h.yamada_5_51 hW d hK hQ
  have h1 := h.card_sup_zpowers htN htD
  rw [hsup, h.card_yamadaC₇ d hK hQ] at h1
  omega

theorem M_le_yamadaM₆ (_hW : CFSG.Walter.WalterOrderForm) (_h : Setup G L f t) (d : G2Data L K)
    (_hK : Nat.card K = 2 ^ f) (_hQ : _h.QFacts d) : d.M ≤ yamadaM₆ d t :=
  (Q44.M_le_M₅ d t).trans (yamadaM₅_le_yamadaM₆ d t)

theorem yamadaF₅_le_yamadaM₆ (_hW : CFSG.Walter.WalterOrderForm) (_h : Setup G L f t)
    (d : G2Data L K) (_hK : Nat.card K = 2 ^ f) (_hQ : _h.QFacts d) :
    yamadaF₅ d t ≤ yamadaM₆ d t :=
  (Q44.F₅_le_M₅ d t).trans (yamadaM₅_le_yamadaM₆ d t)

theorem yamadaY₂_le_yamadaM₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaY₂ d t ≤ yamadaM₆ d t :=
  (Q44.Y₂_le_F₅ d t).trans (yamadaF₅_le_yamadaM₆ hW h d hK hQ)

theorem yamadaM₂_le_yamadaM₆ (_hW : CFSG.Walter.WalterOrderForm) (_h : Setup G L f t)
    (d : G2Data L K) (_hK : Nat.card K = 2 ^ f) (_hQ : _h.QFacts d) :
    yamadaM₂ d t ≤ yamadaM₆ d t :=
  (Q44.M₂_le_M₅ d t).trans (yamadaM₅_le_yamadaM₆ d t)

theorem yamadaW₃_le_yamadaM₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaW₃ d t ≤ yamadaM₆ d t :=
  (Q44.W₃_le_F₅ d t).trans (yamadaF₅_le_yamadaM₆ hW h d hK hQ)

theorem yamadaM₆_le_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ≤ yamadaL₆ d t :=
  Q44.M₆_le_L₆ hW h d hK hQ

theorem yamadaF₅_le_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaF₅ d t ≤ yamadaD₇ d t := by
  obtain ⟨-, -, -, hS₅S₆, hS₆P, -⟩ := h.yamadaP_facts hW d hK hQ
  exact le_inf (((Q44.F₅_le_S₅ d t).trans hS₅S₆).trans hS₆P) (Q44.F₅_le_Cstar hW h d hK hQ)

theorem yamadaM₆_le_yamadaP (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ≤ yamadaP d t := by
  obtain ⟨-, -, -, -, hS₆P, -⟩ := h.yamadaP_facts hW d hK hQ
  exact (yamadaM₆_le_yamadaS₆ d t).trans hS₆P

theorem yamadaM₆_inf_yamadaR₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ⊓ yamadaR₅ d t = yamadaM₅ d t := by
  have htt := h.t_mul_t
  obtain ⟨-, -, ⟨hL₅M, hM₅N, -⟩, -⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨⟨hM₆L₆, -, htM₆⟩, -⟩ := h.yamada_5_44_1 hW d hK hQ
  refine le_antisymm (fun x hx => ?_) (le_inf (yamadaM₅_le_yamadaM₆ d t)
    ((Q44.M₅_le_L₅ hW h d hK hQ).trans (Q44.L₅_le_R₅ hW h d hK hQ)))
  obtain ⟨hxM₆, hxR₅⟩ := Subgroup.mem_inf.1 hx
  have hxL₆ : x ∈ yamadaL₆ d t := by
    rw [← hM₆L₆]
    exact mem_sup_left hxM₆
  have hxL₅ : x ∈ yamadaL₅ d t := by
    rw [h.yamada_5_40_4 hW d hK hQ]
    exact Subgroup.mem_inf.2 ⟨hxL₆, hxR₅⟩
  rw [← hL₅M] at hxL₅
  rcases (mem_sup_zpowers_iff_of htt hM₅N).1 hxL₅ with h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    apply htM₆
    have := mul_mem (inv_mem (yamadaM₅_le_yamadaM₆ d t ha)) hxM₆
    rwa [inv_mul_cancel_left] at this

theorem yamadaD₇_inf_yamadaR₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaD₇ d t ⊓ yamadaR₅ d t = yamadaD₅ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, hS₅S₆, hS₆P, hPR₅, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨⟨hS₅, -, hD₅⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  have hF₅D₇ := h.yamadaF₅_le_yamadaD₇ hW d hK hQ
  have hDD₇ : d.D ≤ yamadaD₇ d t :=
    le_inf ((hDS.trans (Q44.S_le_S₅ d t)).trans (hS₅S₆.trans hS₆P))
      (h.D_le_yamadaCstar d hK hD)
  refine le_antisymm (fun x hx => ?_) (le_inf ?_ ?_)
  · obtain ⟨hxD₇, hxR₅⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hxD₇
    have hxS₅ : x ∈ yamadaS₅ d t := by
      rw [← hPR₅]
      exact Subgroup.mem_inf.2 ⟨hxP, hxR₅⟩
    rw [hS₅, sup_comm] at hxS₅
    obtain ⟨a, ha, s, hs, rfl⟩ :=
      Common.exists_mul_of_le_normalizer (Q44.S_le_normalizer_F₅ hW h d hK hQ) _ hxS₅
    have hsC : s ∈ yamadaCstar d t := by
      have := mul_mem (inv_mem (Q44.F₅_le_Cstar hW h d hK hQ ha)) hxC
      rwa [inv_mul_cancel_left] at this
    have hsD : s ∈ d.D := h.S_inf_yamadaCstar_le_D hW d hK hD (Subgroup.mem_inf.2 ⟨hs, hsC⟩)
    rw [hD₅]
    exact mul_mem (mem_sup_right ha) (mem_sup_left hsD)
  · rw [hD₅]
    exact sup_le hDD₇ hF₅D₇
  · have hD₅S₅ : yamadaD₅ d t ≤ yamadaS₅ d t := by
      rw [hD₅, hS₅]
      exact sup_le_sup_right hDS _
    exact hD₅S₅.trans (Q44.S₅_le_R₅ hW h d hK hQ)

theorem yamadaM₆_inf_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ⊓ yamadaD₇ d t = yamadaF₅ d t := by
  have htt := h.t_mul_t
  obtain ⟨-, -, ⟨-, -, htM₅⟩, -, ⟨hE₅, hF₅N, -⟩⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨⟨hM₆L₆, -, -⟩, -⟩ := h.yamada_5_44_1 hW d hK hQ
  obtain ⟨-, -, -, -, -, hR₆R₇, -⟩ := h.yamada_5_49_2 hW d hK hQ
  refine le_antisymm (fun x hx => ?_) (le_inf (h.yamadaF₅_le_yamadaM₆ hW d hK hQ)
    (h.yamadaF₅_le_yamadaD₇ hW d hK hQ))
  obtain ⟨hxM₆, hxD₇⟩ := Subgroup.mem_inf.1 hx
  have hxC : x ∈ yamadaCstar d t := (Subgroup.mem_inf.1 hxD₇).2
  have hxL₆ : x ∈ yamadaL₆ d t := by
    rw [← hM₆L₆]
    exact mem_sup_left hxM₆
  have hxR₆ : x ∈ yamadaR₆ d t := (le_sup_left : yamadaL₆ d t ≤ yamadaL₆ d t ⊔ d.S) hxL₆
  have hxR₇ : x ∈ yamadaR₇ d t :=
    (le_sup_left : yamadaCstar d t ≤ yamadaCstar d t ⊔ d.S) hxC
  have hxR₅ : x ∈ yamadaR₅ d t := by
    rw [← hR₆R₇]
    exact Subgroup.mem_inf.2 ⟨hxR₆, hxR₇⟩
  have hxM₅ : x ∈ yamadaM₅ d t := by
    rw [← h.yamadaM₆_inf_yamadaR₅ hW d hK hQ]
    exact Subgroup.mem_inf.2 ⟨hxM₆, hxR₅⟩
  have hxE₅ : x ∈ yamadaE₅ d t :=
    Subgroup.mem_inf.2 ⟨Q44.M₅_le_L₅ hW h d hK hQ hxM₅, Subgroup.mem_inf.2 ⟨hxR₅, hxC⟩⟩
  rw [← hE₅] at hxE₅
  rcases (mem_sup_zpowers_iff_of htt hF₅N).1 hxE₅ with h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    apply htM₅
    have := mul_mem (inv_mem (Q44.F₅_le_M₅ d t ha)) hxM₅
    rwa [inv_mul_cancel_left] at this

theorem card_yamadaR₈ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (yamadaR₈ d t) = 2 * Nat.card K ^ 12 := by
  obtain ⟨hR₅R₆, -, hR₆R₈, -⟩ := h.yamada_5_49_2 hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, -, hDS, -, -⟩ := d.inclusions
  obtain ⟨_, _, φ, -, -⟩ := h.yamada_5_49_3 hW d hK hQ
  have hcard := card_mul_card_eq_of_card_quotient_eq (hR₅R₆.trans hR₆R₈) (hFD.trans hDS)
    (Nat.card_congr φ.toEquiv)
  obtain ⟨hR₅, -⟩ := h.card_yamada_five_six hW d hK hQ
  rw [hR₅, d.cards.2.2.2.2.1, d.cards.2.2.2.2.2.2.2] at hcard
  have hq : 0 < Nat.card K ^ 4 := pow_pos Nat.card_pos 4
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [hcard]
  ring

theorem card_yamadaP (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (yamadaP d t) = Nat.card K ^ 12 := by
  obtain ⟨⟨hsup, htN, htP⟩, -⟩ := h.yamada_5_51 hW d hK hQ
  have h1 := h.card_sup_zpowers htN htP
  rw [hsup, h.card_yamadaR₈ hW d hK hQ] at h1
  omega

theorem yamadaP_eq_mul (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaP d t : Set G) = (yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G) := by
  have hq : 0 < Nat.card K ^ 8 := pow_pos Nat.card_pos 8
  have hsub : (yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G) ⊆ (yamadaP d t : Set G) := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_mem (h.yamadaM₆_le_yamadaP hW d hK hQ hx) (yamadaD₇_le_yamadaP d t hy)
  have hmul := ncard_mul_set_mul_card_inf (yamadaM₆ d t) (yamadaD₇ d t)
  obtain ⟨-, -, -, hF₅, -, -, hM₆, -, -⟩ := h.card_yamada_five_six hW d hK hQ
  rw [h.yamadaM₆_inf_yamadaD₇ hW d hK hQ, hF₅, hM₆, h.card_yamadaD₇ hW d hK hQ] at hmul
  have hprod : ((yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G)).ncard = Nat.card K ^ 12 := by
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [hmul]
    ring
  symm
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  rw [hprod, ← Nat.card_coe_set_eq]
  exact (h.card_yamadaP hW d hK hQ).le

theorem D_le_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.D ≤ yamadaD₇ d t :=
  (le_sup_right : d.D ≤ yamadaD₁ d t).trans (h.yamadaD₁_le_yamadaD₇ hW d hK hQ)

theorem yamadaU₁_le_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaU₁ d t ≤ yamadaD₇ d t :=
  hQ.doubling.le_D₁.trans (h.yamadaD₁_le_yamadaD₇ hW d hK hQ)

theorem yamadaW₃_le_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaW₃ d t ≤ yamadaD₇ d t := by
  rw [(h.yamada_5_54_2 hW d hK hQ).1]
  exact le_sup_left

theorem yamadaY₂_le_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaY₂ d t ≤ yamadaD₇ d t :=
  ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans
    (h.yamadaW₃_facts hW d hK hQ.doubling).2.2.2.1).trans
    (h.yamadaW₃_le_yamadaD₇ hW d hK hQ)

theorem J_le_normalizer_yamadaP (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (yamadaP d t : Set G) := fun j hj =>
  mem_normalizer_commutator ((h.yamadaP_facts hW d hK hQ).1 hj) (Subgroup.le_normalizer hj)

theorem S_le_yamadaR₈ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.S ≤ yamadaR₈ d t := by
  obtain ⟨-, -, hR₆R₈, -⟩ := h.yamada_5_49_2 hW d hK hQ
  exact (le_sup_right : d.S ≤ yamadaR₆ d t).trans hR₆R₈

theorem S_le_normalizer_yamadaP (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.S ≤ normalizer (yamadaP d t : Set G) :=
  (h.S_le_yamadaR₈ hW d hK hQ).trans (h.yamadaP_facts hW d hK hQ).2.2.1

theorem S_le_normalizer_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.S ≤ normalizer (yamadaD₇ d t : Set G) := fun s hs =>
  Common.mem_normalizer_inf (h.S_le_normalizer_yamadaP hW d hK hQ hs)
    (h.inf_normalizer_U_le_normalizer_yamadaC₇ d (h.S_le_inf_normalizer_U d hs))

theorem J_le_normalizer_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (yamadaD₇ d t : Set G) := fun j hj =>
  Common.mem_normalizer_inf (h.J_le_normalizer_yamadaP hW d hK hQ hj)
    (h.inf_normalizer_U_le_normalizer_yamadaC₇ d (d.J_le_inf_normalizer_U hj))

omit [Finite K] in
theorem leviA_le_sup_conj (d : G2Data L K) :
    d.leviA ≤ d.S ⊔ d.S.map (MulAut.conj d.wa).toMonoidHom := by
  have h1 := d.image_mono (Model.leviA_le_sup_conj (K := K))
  rwa [d.image_sup (Model.S_le_adjointGroup K)
      (G2Data.conj_le_adjointGroup (Model.S_le_adjointGroup K) (Model.wa_mem_adjointGroup K)),
    d.image_map_conj ⟨Model.wa K, Model.wa_mem_adjointGroup K⟩ (Model.S K)] at h1

theorem leviA_le_normalizer_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.leviA ≤ normalizer (yamadaD₇ d t : Set G) := by
  have hS := h.S_le_normalizer_yamadaD₇ hW d hK hQ
  have hwa := h.wa_mem_normalizer_yamadaD₇ hW d hK hQ
  refine (leviA_le_sup_conj d).trans (sup_le hS ?_)
  rintro _ ⟨s, hs, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact mul_mem (mul_mem hwa (hS hs)) (inv_mem hwa)

theorem normalizer_L_inf_U_le_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    L ⊓ normalizer (d.U : Set G) ≤ normalizer (yamadaD₇ d t : Set G) := by
  rw [d.yamada_3_13_2_G.1]
  have hJ₃ : d.J₃ ≤ d.J := d.image_mono inf_le_left
  exact sup_le ((h.D_le_yamadaD₇ hW d hK hQ).trans Subgroup.le_normalizer)
    (sup_le (h.leviA_le_normalizer_yamadaD₇ hW d hK hQ)
      (hJ₃.trans (h.J_le_normalizer_yamadaD₇ hW d hK hQ)))

theorem eq_yamadaC₁_or_eq_yamadaC₇ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) (h4 : 4 ≤ Nat.card K) {A : Subgroup G}
    (hC₁A : yamadaC₁ d t ≤ A) (hAC : A ≤ yamadaC₇ d t)
    (hA : L ⊓ normalizer (d.U : Set G) ≤ normalizer (A : Set G)) :
    A = yamadaC₁ d t ∨ A = yamadaC₇ d t := by
  obtain ⟨hN₁, hN₂, φ, -, hφ⟩ := h.yamada_5_19_4 d hK hD
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hUD : d.U ≤ d.D := hUY.trans (hYX.trans (hXF.trans hFD))
  let E : Subgroup G :=
    { carrier := {δ | ∃ hδ : δ ∈ d.D, ∃ x : yamadaCstar d t, (x : G) ∈ A ∧
        φ (QuotientGroup.mk x) = QuotientGroup.mk (⟨δ, hδ⟩ : d.D)}
      mul_mem' := by
        rintro a b ⟨ha, x, hxA, hx⟩ ⟨hb, y, hyA, hy⟩
        refine ⟨mul_mem ha hb, x * y, mul_mem hxA hyA, ?_⟩
        rw [QuotientGroup.mk_mul, map_mul, hx, hy]
        rfl
      one_mem' := ⟨one_mem _, 1, one_mem _, by
        rw [QuotientGroup.mk_one, map_one]
        rfl⟩
      inv_mem' := by
        rintro a ⟨ha, x, hxA, hx⟩
        refine ⟨inv_mem ha, x⁻¹, inv_mem hxA, ?_⟩
        rw [QuotientGroup.mk_inv, map_inv, hx]
        rfl }
  have hmemE : ∀ δ : d.D, (δ : G) ∈ E ↔ ∃ x : yamadaCstar d t, (x : G) ∈ A ∧
      φ (QuotientGroup.mk x) = QuotientGroup.mk δ := fun δ =>
    ⟨fun ⟨_, x, hxA, hx⟩ => ⟨x, hxA, hx⟩, fun ⟨x, hxA, hx⟩ => ⟨δ.2, x, hxA, hx⟩⟩
  have hUE : d.U ≤ E := fun u hu => ⟨hUD hu, 1, one_mem _, by
    rw [QuotientGroup.mk_one, map_one]
    exact ((QuotientGroup.eq_one_iff (⟨u, hUD hu⟩ : d.D)).2 (mem_subgroupOf.2 hu)).symm⟩
  have hED : E ≤ d.D := fun δ hδ => hδ.1
  have hNE : L ⊓ normalizer (d.U : Set G) ≤ normalizer (E : Set G) := by
    intro n hn
    refine mem_normalizer_of_conj_mem fun δ hδ => ?_
    obtain ⟨hδD, x, hxA, hx⟩ := hδ
    obtain ⟨hnx, hnδ, he⟩ := hφ n ⟨h.L_le_centralizer hn.1, hn.2⟩ x ⟨δ, hδD⟩ hx
    refine ⟨hnδ, ⟨_, hnx⟩, ?_, he⟩
    exact (mem_normalizer_iff.1 (hA hn) x).1 hxA
  rcases (d.yamada_3_16_1_G h4 hUE hED).1 hNE with hEU | hED'
  · left
    refine le_antisymm (fun x hxA => ?_) hC₁A
    have hxC : x ∈ yamadaCstar d t := hAC hxA
    obtain ⟨δ, hδ⟩ :=
      QuotientGroup.mk_surjective (φ (QuotientGroup.mk (⟨x, hxC⟩ : yamadaCstar d t)))
    have hδE : (δ : G) ∈ E := (hmemE δ).2 ⟨⟨x, hxC⟩, hxA, hδ.symm⟩
    rw [hEU] at hδE
    have h1 : (QuotientGroup.mk δ : d.D ⧸ d.U.subgroupOf d.D) = 1 :=
      (QuotientGroup.eq_one_iff δ).2 (mem_subgroupOf.2 hδE)
    rw [h1] at hδ
    have h2 := φ.injective (hδ.symm.trans (map_one φ).symm)
    have h3 := (QuotientGroup.eq_one_iff _).1 h2
    exact mem_subgroupOf.1 h3
  · right
    refine le_antisymm hAC (fun x hxC => ?_)
    obtain ⟨δ, hδ⟩ :=
      QuotientGroup.mk_surjective (φ (QuotientGroup.mk (⟨x, hxC⟩ : yamadaCstar d t)))
    have hδE : (δ : G) ∈ E := by
      rw [hED']
      exact δ.2
    obtain ⟨y, hyA, hy⟩ := (hmemE δ).1 hδE
    have h1 : (QuotientGroup.mk y : yamadaCstar d t ⧸ (yamadaC₁ d t).subgroupOf (yamadaCstar d t)) =
        QuotientGroup.mk ⟨x, hxC⟩ := φ.injective (hy.trans hδ)
    have h2 := QuotientGroup.eq.1 h1
    have h3 : (y : G)⁻¹ * x ∈ yamadaC₁ d t := mem_subgroupOf.1 h2
    have h4' : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [h4']
    exact mul_mem hyA (hC₁A h3)

theorem not_yamadaY₂_le_yamadaR₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) (hQ : h.QFacts d) : ¬ yamadaY₂ d t ≤ yamadaR₁ d t := by
  intro hle
  have h1 := h.yamadaY₂_inf_yamadaR₁ d hK hD
  rw [inf_of_le_left hle] at h1
  have hc : Nat.card (yamadaY₂ d t) = Nat.card (yamadaY₁ d t) := by rw [h1]
  rw [h.card_yamadaY₂ d hK hD, h.card_yamadaY₁ d hK hD] at hc
  have hq : 1 < Nat.card K := hQ.one_lt
  exact absurd hc (Nat.pow_lt_pow_right hq (by norm_num : 3 < 4)).ne'

theorem not_closure_sq_yamadaD₇_le_D (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ¬ closure {z | ∃ g ∈ yamadaD₇ d t, z = g ^ 2} ≤ d.D := by
  intro hle
  have hD := hQ.doubling
  have hsq : ∀ g ∈ yamadaD₇ d t, g * g ∈ d.D := fun g hg => by
    rw [← sq]
    exact hle (subset_closure ⟨g, hg, rfl⟩)
  have hDD₇ : d.D ≤ yamadaD₇ d t := h.D_le_yamadaD₇ hW d hK hQ
  have hY : yamadaY₂ d t ≤ normalizer (d.D : Set G) := by
    intro y hy
    refine mem_normalizer_of_conj_mem fun δ hδ => ?_
    have hyD₇ := h.yamadaY₂_le_yamadaD₇ hW d hK hQ hy
    have h1 := hsq (y * δ) (mul_mem hyD₇ (hDD₇ hδ))
    have h2 := hsq y hyD₇
    have e : y * δ * y⁻¹ = (y * δ * (y * δ)) * δ⁻¹ * (y * y)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem h1 (inv_mem hδ)) (inv_mem h2)
  have hR₁ : yamadaY₂ d t ≤ yamadaR₁ d t := by
    rw [← (h.yamada_5_8_6 d hK).2]
    exact le_inf (h.yamadaY₂_le_yamadaR₂ d hK hD) hY
  exact h.not_yamadaY₂_le_yamadaR₁ d hK hD hQ hR₁

theorem commutator_mem_yamadaU₁_of_mem_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ x ∈ yamadaD₇ d t, ∀ y ∈ yamadaD₇ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaU₁ d t := by
  have hD := hQ.doubling
  have h4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨hZ, hZ2⟩ := h.yamada_5_52 hW d hK hQ
  obtain ⟨-, htD₇N, htD₇⟩ := (h.yamada_5_51 hW d hK hQ).2.2
  have hD₇P : yamadaD₇ d t ≤ yamadaP d t := yamadaD₇_le_yamadaP d t
  have hD₇C : yamadaD₇ d t ≤ yamadaC₇ d t := yamadaD₇_le_yamadaC₇ d t
  have hC₁C₇ := h.yamadaC₁_le_yamadaCstar d hK hD
  have htC₁ := h.t_mem_yamadaC₁ d hK
  have hZ' : yamadaP d t ⊓ centralizer (yamadaP d t : Set G) = yamadaU₁ d t := by
    rw [← map_upperCentralSeries_one]
    exact hZ
  have hU₁c : ∀ u ∈ yamadaU₁ d t, ∀ g ∈ yamadaP d t, g * u = u * g := fun u hu g hg => by
    have : u ∈ yamadaP d t ⊓ centralizer (yamadaP d t : Set G) := by
      rw [hZ']
      exact hu
    exact mem_centralizer_iff.1 this.2 g hg
  have hPU₁ : yamadaP d t ≤ normalizer (yamadaU₁ d t : Set G) := fun g hg =>
    mem_normalizer_of_conj_mem fun u hu => by
      rw [show g * u * g⁻¹ = u by rw [hU₁c u hu g hg]; group]
      exact hu
  have hmemY₂ := fun x => mem_of_map_upperCentralSeries_succ hZ hZ2 (x := x)
  set Z : Subgroup G := yamadaD₇ d t ⊓ centralizerModulo (yamadaU₁ d t) (yamadaD₇ d t) with hZdef
  have hZD₇ : Z ≤ yamadaD₇ d t := inf_le_left
  have hD₁Z : yamadaD₁ d t ≤ Z := fun x hx => ⟨h.yamadaD₁_le_yamadaD₇ hW d hK hQ hx,
    ((h.yamadaD₁_le_yamadaC₁ d hK).trans (hD.yamadaC₁_le_normalizer hK)) hx, fun y hy => by
      have := ((h.yamada_5_19 d hK hD).2.2.1) y (hD₇C hy) x hx
      have := inv_mem this
      rwa [show (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ by group] at this⟩
  have hY₂Z : yamadaY₂ d t ≤ Z := fun x hx => by
    obtain ⟨hxP, hxc⟩ := (hmemY₂ x).1 hx
    exact ⟨h.yamadaY₂_le_yamadaD₇ hW d hK hQ hx, hPU₁ hxP, fun y hy => hxc y (hD₇P hy)⟩
  have hNZ : ∀ g ∈ normalizer (yamadaD₇ d t : Set G),
      g ∈ normalizer (yamadaU₁ d t : Set G) → g ∈ normalizer (Z : Set G) := fun g hg hgU =>
    Common.mem_normalizer_inf hg (mem_normalizer_centralizerModulo hgU hg)
  have htZ : t ∈ normalizer (Z : Set G) :=
    hNZ t htD₇N (hD.yamadaC₁_le_normalizer hK htC₁)
  have hC₁A : yamadaC₁ d t ≤ Z ⊔ zpowers t := by
    rw [(h.yamada_5_8_1 d hK).2.1]
    exact sup_le_sup_right hD₁Z _
  have hAC : Z ⊔ zpowers t ≤ yamadaC₇ d t :=
    sup_le (hZD₇.trans hD₇C) (zpowers_le.2 (hC₁C₇ htC₁))
  have hNA : L ⊓ normalizer (d.U : Set G) ≤ normalizer ((Z ⊔ zpowers t : Subgroup G) : Set G) := by
    intro n hn
    refine mem_normalizer_sup (hNZ n (h.normalizer_L_inf_U_le_yamadaD₇ hW d hK hQ hn)
      (hD.inf_normalizer_U_le_normalizer hK hn)) ?_
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    have hc : Commute n t := mem_centralizer_singleton_iff.1 (h.L_le_centralizer hn.1)
    rw [show n * t ^ k * n⁻¹ = t ^ k by
      have := (hc.zpow_right k).eq
      rw [this]
      group]
    exact zpow_mem (mem_zpowers t) k
  rcases h.eq_yamadaC₁_or_eq_yamadaC₇ d hK hD h4 hC₁A hAC hNA with hA | hA
  · exfalso
    exact h.not_yamadaY₂_le_yamadaR₁ d hK hD hQ
      ((hY₂Z.trans (le_sup_left.trans hA.le)).trans (le_sup_left : yamadaC₁ d t ≤ yamadaR₁ d t))
  · intro x hx y hy
    have hxA : x ∈ Z ⊔ zpowers t := by
      rw [hA]
      exact hD₇C hx
    rcases (mem_sup_zpowers_iff_of h.t_mul_t htZ).1 hxA with hxZ | ⟨a, ha, rfl⟩
    · exact hxZ.2.2 y hy
    · exfalso
      refine htD₇ ?_
      have := mul_mem (inv_mem (hZD₇ ha)) hx
      rwa [inv_mul_cancel_left] at this

theorem exists_mul_self_eq_commutator_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ g ∈ yamadaD₇ d t, ∃ a ∈ yamadaD₇ d t, ∃ b ∈ yamadaD₇ d t, g * g = a * b * a⁻¹ * b⁻¹ := by
  obtain ⟨hjoin, hset, -⟩ := h.yamada_5_54_2 hW d hK hQ
  have hWe := (h.yamada_5_33_3_uniform hW d hK hQ.doubling).1
  have hW₃D := h.yamadaW₃_le_yamadaD₇ hW d hK hQ
  have hconjD : (yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom ≤ yamadaD₇ d t := by
    rw [hjoin]
    exact le_sup_right
  intro g hg
  have hg' : g ∈ (yamadaD₇ d t : Set G) := hg
  rw [hset] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg'
  have hbD : b ∈ yamadaD₇ d t := hconjD hb
  obtain ⟨b', hb', rfl⟩ := hb
  have hae : a * a = 1 := by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := yamadaW₃ d t) a ha
  have hbe : b' * b' = 1 := by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := yamadaW₃ d t) b' hb'
  refine ⟨a, hW₃D ha, _, hbD, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [inv_eq_of_mul_eq_one_right hae]
  have e : d.wa * b' * d.wa⁻¹ * (d.wa * b' * d.wa⁻¹) = 1 := by
    rw [show d.wa * b' * d.wa⁻¹ * (d.wa * b' * d.wa⁻¹) = d.wa * (b' * b') * d.wa⁻¹ by group, hbe]
    group
  rw [inv_eq_of_mul_eq_one_right e]
  group

theorem mul_self_mem_yamadaU₁_of_mem_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ g ∈ yamadaD₇ d t, g * g ∈ yamadaU₁ d t := fun g hg => by
  obtain ⟨a, ha, b, hb, he⟩ := h.exists_mul_self_eq_commutator_yamadaD₇ hW d hK hQ g hg
  rw [he]
  exact h.commutator_mem_yamadaU₁_of_mem_yamadaD₇ hW d hK hQ a ha b hb

theorem yamada_5_55_1_D (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ElemModulo (yamadaU₁ d t) (yamadaD₇ d t) ∧
      closure {z | ∃ g ∈ yamadaD₇ d t, z = g ^ 2} = yamadaU₁ d t ∧
      ⁅yamadaD₇ d t, yamadaD₇ d t⁆ = yamadaU₁ d t := by
  have hD := hQ.doubling
  have hcomm := h.commutator_mem_yamadaU₁_of_mem_yamadaD₇ hW d hK hQ
  have hsq := h.mul_self_mem_yamadaU₁_of_mem_yamadaD₇ hW d hK hQ
  have hV : closure {z | ∃ g ∈ yamadaD₇ d t, z = g ^ 2} = yamadaU₁ d t := by
    have hVU₁ : closure {z | ∃ g ∈ yamadaD₇ d t, z = g ^ 2} ≤ yamadaU₁ d t := by
      rw [closure_le]
      rintro z ⟨g, hg, rfl⟩
      rw [sq]
      exact hsq g hg
    have hUV : d.U ≤ closure {z | ∃ g ∈ yamadaD₇ d t, z = g ^ 2} := by
      rw [← (d.yamada_3_12_mho hQ.four_le).1]
      exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, h.D_le_yamadaD₇ hW d hK hQ hg, e⟩
    have hJ₃ : d.J₃ ≤ d.J := d.image_mono inf_le_left
    rcases h.eq_or_eq_of_le_yamadaU₁ d hK hD hUV hVU₁ (fun j hj =>
      mem_normalizer_closure_sq_of_mem_normalizer
        (h.J_le_normalizer_yamadaD₇ hW d hK hQ (hJ₃ hj))) with hVU | hVU
    · exfalso
      refine h.not_closure_sq_yamadaD₇_le_D hW d hK hQ ?_
      rw [hVU]
      obtain ⟨hUY, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
      exact hUY.trans (hYX.trans (hXF.trans hFD))
    · exact hVU
  refine ⟨fun x hx y hy => ⟨hsq x hx, hcomm x hx y hy⟩, hV, le_antisymm ?_ ?_⟩
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact hcomm x hx y hy
  · rw [← hV, closure_le]
    rintro z ⟨g, hg, rfl⟩
    obtain ⟨a, ha, b, hb, he⟩ := h.exists_mul_self_eq_commutator_yamadaD₇ hW d hK hQ g hg
    rw [sq, he]
    exact Subgroup.commutator_mem_commutator ha hb

theorem elemModulo_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ElemModulo (yamadaU₁ d t) (yamadaD₇ d t) :=
  (h.yamada_5_55_1_D hW d hK hQ).1

theorem wb_mem_normalizer_yamadaM₆ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) : d.wb ∈ normalizer (yamadaM₆ d t : Set G) := by
  refine mem_normalizer_of_map_conj_eq ?_
  show (yamadaM₅ d t ⊔ (yamadaM₅ d t).map (MulAut.conj d.wb).toMonoidHom).map
    (MulAut.conj d.wb).toMonoidHom =
      yamadaM₅ d t ⊔ (yamadaM₅ d t).map (MulAut.conj d.wb).toMonoidHom
  rw [Subgroup.map_sup, Q44.map_wb_map_wb h d hK, sup_comm]

theorem S_le_normalizer_yamadaM₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.S ≤ normalizer (yamadaM₆ d t : Set G) :=
  Q44.S_le_normalizer_M₆ hW h d hK hQ

theorem J_le_normalizer_yamadaM₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (yamadaM₆ d t : Set G) :=
  Q44.J_le_normalizer_M₆ hW h d hK hQ

theorem leviB_le_normalizer_yamadaM₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.leviB ≤ normalizer (yamadaM₆ d t : Set G) := by
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hS := S_le_normalizer_yamadaM₆ hW h d hK hQ
  have hw := wb_mem_normalizer_yamadaM₆ h d hK
  have hSb : d.rootGroup g2a ≤ d.S := by
    obtain ⟨-, -, -, -, haD, -, -, -, -⟩ := d.yamada_defs
    exact (le_sup_left.trans haD.le).trans d.inclusions.2.2.2.2.2.2.2.1
  have hpre : Model.leviB K ≤
      d.preimage (normalizer (yamadaM₆ d t : Set G) ⊓ L) := by
    rw [Model.leviB, g2RankOne_a_eq]
    refine (Subgroup.closure_le _).2 ?_
    have hx0 : ∀ c : K, d.emb ⟨pinnedX .G2 K g2a c, pinnedX_mem_adjointGroup g2a c⟩ ∈
        d.image (rootSubgroup .G2 K g2a) := fun c =>
      d.emb_mem_image (mem_rootSubgroup.2 ⟨c, rfl⟩)
    have hx : ∀ c : K, d.emb ⟨pinnedX .G2 K g2a c, pinnedX_mem_adjointGroup g2a c⟩ ∈
        normalizer (yamadaM₆ d t : Set G) := fun c => hS (hSb (hx0 c))
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact d.mem_preimage.2 (Subgroup.mem_inf.2 ⟨hx c, d.emb_mem _⟩)
    · refine d.mem_preimage (g := ⟨pinnedX .G2 K g2na c, pinnedX_mem_adjointGroup g2na c⟩) |>.2
        (Subgroup.mem_inf.2 ⟨?_, d.emb_mem _⟩)
      have h1 := (d.yamada_3_7_G hK4).2.2.2.2.2 (s := g2a) isRoot_g2a c
      have h2 : d.emb ⟨pinnedX .G2 K g2na c, pinnedX_mem_adjointGroup g2na c⟩ =
          d.emb ⟨pinnedX .G2 K (reflect .G2 g2ia g2a) c, pinnedX_mem_adjointGroup _ _⟩ :=
        congrArg d.emb (Subtype.ext (by rw [reflect_a_a]))
      have h3 : d.wb * d.emb ⟨pinnedX .G2 K g2a c, pinnedX_mem_adjointGroup g2a c⟩ * d.wb =
          d.wb * d.emb ⟨pinnedX .G2 K g2a c, pinnedX_mem_adjointGroup g2a c⟩ * d.wb⁻¹ := by
        rw [Q44.wb_inv h d hK]
      rw [h2, ← h1, h3]
      exact mul_mem (mul_mem hw (hx c)) (inv_mem hw)
  calc d.leviB = d.image (Model.leviB K) := rfl
    _ ≤ d.image (d.preimage (normalizer (yamadaM₆ d t : Set G) ⊓ L)) := d.image_mono hpre
    _ = normalizer (yamadaM₆ d t : Set G) ⊓ L := d.image_preimage inf_le_right
    _ ≤ normalizer (yamadaM₆ d t : Set G) := inf_le_left

theorem normalizer_L_inf_Y_le_yamadaM₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    L ⊓ normalizer (d.Y : Set G) ≤ normalizer (yamadaM₆ d t : Set G) := by
  rw [d.yamada_3_13_3_G.1]
  exact sup_le ((M_le_yamadaM₆ hW h d hK hQ).trans Subgroup.le_normalizer)
    (sup_le (leviB_le_normalizer_yamadaM₆ hW h d hK hQ)
      ((h.J₄_facts d hK).1.trans (J_le_normalizer_yamadaM₆ hW h d hK hQ)))

theorem yamadaM₄_le_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₄ d t ≤ yamadaL₆ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, ⟨hL₄eq, -⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  exact ((le_sup_left : yamadaM₄ d t ≤ yamadaM₄ d t ⊔ zpowers t).trans hL₄eq.le).trans
    ((le_sup_right : yamadaL₄ d t ≤ yamadaL₅ d t).trans (Q44.L₅_le_L₆ hW h d hK hQ))

theorem yamadaX₄_le_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaX₄ d t ≤ yamadaL₆ d t :=
  (le_sup_left : yamadaX₄ d t ≤ yamadaM₄ d t).trans (yamadaM₄_le_yamadaL₆ hW h d hK hQ)

theorem L₆_le_normalizer_yamadaM₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₆ d t ≤ normalizer (yamadaM₄ d t : Set G) :=
  le_normalizer_of_forall_commutator_mem (Q44.commutator_mem_M₂ hW h d hK hQ)
    (le_sup_right : yamadaM₂ d t ≤ yamadaM₄ d t) le_rfl (yamadaM₄_le_yamadaL₆ hW h d hK hQ)

theorem L₆_le_normalizer_yamadaX₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₆ d t ≤ normalizer (yamadaX₄ d t : Set G) := by
  have hD := hQ.doubling
  have hX₄eq := yamadaX₄_eq_inf_centralizer hW h d hK hQ
  have hM₄R₄ : yamadaM₄ d t ≤ yamadaR₄ d t := by
    obtain ⟨-, -, -, ⟨hL₄eq, -⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
    exact ((le_sup_left : yamadaM₄ d t ≤ yamadaM₄ d t ⊔ zpowers t).trans hL₄eq.le).trans
      (h.yamadaL₄_facts hW d hK hD).2.2.2.2.1
  have hX₄eq : yamadaX₄ d t = yamadaM₄ d t ⊓ centralizer (yamadaX₂ d t : Set G) :=
    le_antisymm (le_inf (le_sup_left : yamadaX₄ d t ≤ yamadaM₄ d t) (hX₄eq.le.trans inf_le_right))
      fun x hx => hX₄eq.ge (Subgroup.mem_inf.2 ⟨hM₄R₄ (Subgroup.mem_inf.1 hx).1,
        (Subgroup.mem_inf.1 hx).2⟩)
  intro g hg
  have := mem_normalizer_inf_centralizer_of_mem
    (L₆_le_normalizer_yamadaM₄ hW h d hK hQ hg)
    ((le_sup_left : yamadaL₆ d t ≤ yamadaR₆ d t).trans
      (h.yamadaR₆_le_normalizer_yamadaX₂ hW d hK hQ) hg)
  rwa [← hX₄eq] at this

theorem L₆_le_normalizer_yamadaW₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₆ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
  ((le_sup_left : yamadaL₆ d t ≤ yamadaR₆ d t).trans
    (h.yamadaR₆_le_normalizer_yamadaL₂ d)).trans
    ((h.yamada_5_41_4 hW d hK hQ).1.le.trans
      (h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ hW d hK hQ))

theorem L₆_le_normalizer_yamadaF₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₆ d t ≤ normalizer (yamadaF₅ d t : Set G) := by
  obtain ⟨-, -, hFWX, -, -, -⟩ := h.yamada_5_46_1 hW d hK hQ
  intro g hg
  rw [← hFWX]
  exact mem_normalizer_sup (L₆_le_normalizer_yamadaW₃ hW h d hK hQ hg)
    (L₆_le_normalizer_yamadaX₄ hW h d hK hQ hg)

theorem L₆_le_normalizer_map_wb_yamadaF₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₆ d t ≤
      normalizer ((yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom : Set G) := fun x hx =>
  Q44.mem_normalizer_map_conj (L₆_le_normalizer_yamadaF₅ hW h d hK hQ
    (Q44.inv_conj_mem (Q44.wb_mem_normalizer_L₆ h d) hx))

theorem yamadaM₆_eq_sup_X₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t =
      yamadaX₄ d t ⊔ (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom := by
  obtain ⟨hM₆eq, -, -⟩ := h.yamada_5_44_2 hW d hK hQ
  obtain ⟨-, -, hFWX, -, -, -⟩ := h.yamada_5_46_1 hW d hK hQ
  have hW₃ : (yamadaW₃ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaW₃ d t :=
    map_conj_eq_of_mem_normalizer (Q44.wb_mem_normalizer_W₃ hW h d hK hQ)
  have hW₃F : yamadaW₃ d t ≤ (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom :=
    hW₃.symm.le.trans (Subgroup.map_mono (Q44.W₃_le_F₅ d t))
  refine le_antisymm ?_ (sup_le ((Q44.X₄_le_F₅ d t).trans (yamadaF₅_le_yamadaM₆ hW h d hK hQ))
    ((le_sup_right : _ ≤ yamadaF₅ d t ⊔ (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom).trans
      hM₆eq.ge))
  rw [hM₆eq]
  exact sup_le (hFWX.symm.le.trans (sup_le (hW₃F.trans le_sup_right) le_sup_left)) le_sup_right

theorem elemModulo_yamadaM₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ElemModulo (yamadaY₂ d t) (yamadaM₆ d t) := by
  have hD := hQ.doubling
  obtain ⟨-, hY₂X₄, -, hWX, hF₅, -⟩ := h.yamada_5_46_1 hW d hK hQ
  obtain ⟨hM₆eq, -, hFF⟩ := h.yamada_5_44_2 hW d hK hQ
  have hwY₂ := Q44.wb_mem_normalizer_Y₂ h d hK hD
  have hY₂F : (yamadaY₂ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaY₂ d t :=
    map_conj_eq_of_mem_normalizer hwY₂
  have hFwL₆ : (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom ≤ yamadaL₆ d t :=
    ((le_sup_right : _ ≤ yamadaF₅ d t ⊔ (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom).trans
      hM₆eq.ge).trans (yamadaM₆_le_yamadaL₆ hW h d hK hQ)
  rw [yamadaM₆_eq_sup_X₄ hW h d hK hQ]
  refine elemModulo_sup_of_normalizes hY₂X₄ (hY₂F.symm.le.trans (Subgroup.map_mono
    (Q44.Y₂_le_F₅ d t))) ?_ ((yamadaX₄_le_yamadaL₆ hW h d hK hQ).trans
      (L₆_le_normalizer_map_wb_yamadaF₅ hW h d hK hQ))
    (hFwL₆.trans (L₆_le_normalizer_yamadaX₄ hW h d hK hQ))
    (fun x hx y hy => hF₅ x (Q44.X₄_le_F₅ d t hx) y (Q44.X₄_le_F₅ d t hy))
    (elemModulo_map_conj' hwY₂ hF₅)
  intro x hx
  obtain ⟨hxX, hxF⟩ := Subgroup.mem_inf.1 hx
  exact hWX.le (Subgroup.mem_inf.2 ⟨hFF.le (Subgroup.mem_inf.2 ⟨Q44.X₄_le_F₅ d t hxX, hxF⟩), hxX⟩)

theorem Y_le_yamadaM₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.Y ≤ yamadaM₁ d t := by
  obtain ⟨hUY, hYX, hYW, hXF, hWF, hFD, hFM, hDS, hMS, hSL⟩ := d.inclusions
  have hYS : d.Y ≤ d.S := hYX.trans (hXF.trans (hFD.trans hDS))
  exact le_inf (le_inf ((h.Y_le_yamadaY₂ d hK hD).trans (h.yamadaY₂_le_yamadaL₂ d hK hD))
    (hYS.trans (le_sup_right : d.S ≤ yamadaR₁ d t)))
    (hYS.trans (le_sup_left : d.S ≤ yamadaS₁ d t))

theorem commutator_yamadaM₆_ne_Y (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ⁅yamadaM₆ d t, yamadaM₆ d t⁆ ≠ d.Y := by
  intro hY
  have hD := hQ.doubling
  have hYM₁ := Y_le_yamadaM₁ h d hK hD
  have hM₁M₆ : yamadaM₁ d t ≤ yamadaM₆ d t :=
    (h.yamadaM₁_le_yamadaM₂ d hK hD).trans (yamadaM₂_le_yamadaM₆ hW h d hK hQ)
  have hM₅N : yamadaM₅ d t ≤ normalizer (yamadaM₁ d t : Set G) := fun x hx => by
    refine mem_normalizer_of_conj_mem fun m hm => ?_
    have hc : x * m * x⁻¹ * m⁻¹ ∈ ⁅yamadaM₆ d t, yamadaM₆ d t⁆ :=
      Subgroup.commutator_mem_commutator (yamadaM₅_le_yamadaM₆ d t hx) (hM₁M₆ hm)
    rw [hY] at hc
    have e : x * m * x⁻¹ = (x * m * x⁻¹ * m⁻¹) * m := by group
    rw [e]
    exact mul_mem (hYM₁ hc) hm
  have hM₅R₅ : yamadaM₅ d t ≤ yamadaR₅ d t :=
    (Q44.M₅_le_S₅ d t).trans (Q44.S₅_le_R₅ hW h d hK hQ)
  have hM₅R₂ : yamadaM₅ d t ≤ yamadaR₂ d t := by
    rw [← (h.yamada_5_28 hW d hK hD).2.2]
    exact le_inf hM₅R₅ hM₅N
  have hW₃W₂ : yamadaW₃ d t ≤ yamadaW₂ d t := fun w hw =>
    Q44.W₃_inf_R₂_le hW h d hK hQ
      (Subgroup.mem_inf.2 ⟨hw, hM₅R₂ (Q44.F₅_le_M₅ d t (Q44.W₃_le_F₅ d t hw))⟩)
  have h1 := Subgroup.card_le_of_le hW₃W₂
  rw [(h.yamadaW₃_facts hW d hK hD).2.2.2.2.2.2, h.card_yamadaW₂ d hK hD] at h1
  have : Nat.card K ^ 5 < Nat.card K ^ 6 := Nat.pow_lt_pow_right hQ.one_lt (by norm_num)
  omega

theorem commutator_yamadaM₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ⁅yamadaM₆ d t, yamadaM₆ d t⁆ = yamadaY₂ d t := by
  have hD := hQ.doubling
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hE := elemModulo_yamadaM₆ hW h d hK hQ
  have hle : ⁅yamadaM₆ d t, yamadaM₆ d t⁆ ≤ yamadaY₂ d t :=
    Subgroup.commutator_le.2 fun a ha b hb => (hE a ha b hb).2
  have hYM : d.Y ≤ ⁅yamadaM₆ d t, yamadaM₆ d t⁆ := by
    have := Subgroup.commutator_mono (M_le_yamadaM₆ hW h d hK hQ) (M_le_yamadaM₆ hW h d hK hQ)
    rwa [(d.yamada_3_12_commutators hK4).2.1] at this
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htA : t ∈ normalizer (yamadaY₂ d t : Set G) :=
    h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂
  have hlev := leviB_le_normalizer_yamadaM₆ hW h d hK hQ
  rcases eq_or_eq_of_commutator_section (A := yamadaY₂ d t) (Y := d.Y)
      (V := ⁅yamadaM₆ d t, yamadaM₆ d t⁆) (B := d.leviB) (t := t)
      (fun a ha b hb => h.yamadaY₂_mul_comm d hK hD ha hb) htA hYM hle
      (h.yamadaY₂_inf_centralizer d hK hD)
      (fun a ha => by
        have h1 := inv_mem (h.commutator_t_mem_Y_of_mem_yamadaL₂ d hK
          (h.yamadaY₂_le_yamadaL₂ d hK hD ha))
        rwa [commutatorElement_inv] at h1)
      ((h.leviB_le_centralizer_inf_normalizer_Y d).trans inf_le_left)
      (fun l hl => mem_normalizer_commutator (hlev hl) (hlev hl))
      (fun E hEY hEN => (d.yamada_3_16_2_G hEN).1 hEY) with h1 | h1
  · exact absurd h1 (commutator_yamadaM₆_ne_Y hW h d hK hQ)
  · exact h1

theorem yamada_5_55_1_M (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ElemModulo (yamadaY₂ d t) (yamadaM₆ d t) ∧
      closure {z | ∃ g ∈ yamadaM₆ d t, z = g ^ 2} = yamadaY₂ d t ∧
      ⁅yamadaM₆ d t, yamadaM₆ d t⁆ = yamadaY₂ d t := by
  have hE := elemModulo_yamadaM₆ hW h d hK hQ
  refine ⟨hE, le_antisymm ((closure_le _).2 ?_) ?_, commutator_yamadaM₆ hW h d hK hQ⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [sq]
    exact (hE g hg g hg).1
  · rw [← (h.yamada_5_35_3 hW d hK hQ).2.2.2]
    exact closure_mono fun z ⟨g, hg, e⟩ =>
      ⟨g, (yamadaM₅_le_yamadaM₆ d t) ((le_sup_left : yamadaM₃ d t ≤ yamadaM₅ d t) hg), e⟩

namespace JWeight

theorem Y₂_le_F₅ (d : G2Data L K) (t : G) : yamadaY₂ d t ≤ yamadaF₅ d t :=
  (le_sup_right : yamadaY₂ d t ≤ yamadaF₂ d t).trans
    ((le_sup_right : yamadaF₂ d t ≤ yamadaF₃ d t).trans
      (le_sup_left : yamadaF₃ d t ≤ yamadaF₅ d t))

theorem U₁_le_F₅ (d : G2Data L K) (t : G) : yamadaU₁ d t ≤ yamadaF₅ d t :=
  (yamadaU₁_le_yamadaY₂ d t).trans (Y₂_le_F₅ d t)

theorem F_le_F₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : d.F ≤ yamadaF₅ d t :=
  (yamadaS₅_eq_sup hW h d hK hQ).2.1.ge.trans inf_le_right

theorem F₅_le_R₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaF₅ d t ≤ yamadaR₅ d t :=
  (h.yamada_5_46_4 hW d hK hQ).1.1

theorem J_le_normalizer_R₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (yamadaR₅ d t : Set G) := by
  have hD := hQ.doubling
  intro j hj
  have := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₅star d hK hD
    (h.J_le_centralizer_inf_normalizer_S d hj)
  rwa [← h.yamada_5_27_3 hW d hK hD] at this

theorem J_le_normalizer_F₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (yamadaF₅ d t : Set G) := by
  obtain ⟨⟨hF₅R₅, -, -, -⟩, hF₅c, -, -, -⟩ := h.yamada_5_46_4 hW d hK hQ
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((yamadaF₅ d t).subgroupOf (yamadaR₅ d t))
  rw [subgroupOf_map_subtype, inf_of_le_left hF₅R₅] at h1
  exact (J_le_normalizer_R₅ hW h d hK hQ).trans h1

theorem J_le_normalizer_F (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (d.F : Set G) := fun j hj =>
  h.centralizer_inf_normalizer_S_le_normalizer_F d hK hQ.doubling
    (h.J_le_centralizer_inf_normalizer_S d hj)

theorem J_le_normalizer_D (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (d.D : Set G) := by
  obtain ⟨-, -, -, -, haD, -, -, -, -⟩ := d.yamada_defs
  rw [← haD]
  exact fun j hj => mem_normalizer_sup (J_le_normalizer_rootGroup d isRoot_g2a hj)
    (J_le_normalizer_F hW h d hK hQ hj)

theorem J_le_normalizer_M (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (d.M : Set G) := by
  obtain ⟨-, -, -, -, -, haM, -, -, -⟩ := d.yamada_defs
  rw [← haM]
  exact fun j hj => mem_normalizer_sup (J_le_normalizer_rootGroup d isRoot_g2r hj)
    (J_le_normalizer_F hW h d hK hQ hj)

theorem S_inf_centralizer_J₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.S ⊓ centralizer (d.J₃ : Set G) = d.rootGroup g2r :=
  S_inf_centralizer_Ji_of_four_le d (hK ▸ h.four_le) 2 (Or.inr (by decide))

theorem S_inf_centralizer_J₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    d.S ⊓ centralizer (d.J₄ : Set G) = d.rootGroup g2a :=
  S_inf_centralizer_Ji_of_four_le d (hK ▸ h.four_le) 3 (Or.inl h8)

theorem commutator_J₄_mem_F_of_mem_D (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ j ∈ d.J₄, ∀ a ∈ d.D, ⁅j, a⁆ ∈ d.F := by
  intro j hj a ha
  obtain ⟨-, -, -, -, haD, -, -, -, -⟩ := d.yamada_defs
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  have hJ₄J : d.J₄ ≤ d.J := d.image_mono inf_le_left
  have hSb : ∀ b ∈ d.rootGroup g2a, j * b = b * j := fun b hb =>
    mem_centralizer_iff.1 (Q44.rootGroup_yamadaRoot_le_centralizer_Ji d 3 hb) j hj
  have hbN : d.rootGroup g2a ≤ normalizer (d.F : Set G) := fun b hb =>
    d.S_le_normalizers.2.2.2.2.1 ((le_sup_left.trans haD.le |>.trans hDS) hb)
  rw [← haD] at ha
  refine commutator_mem_of_mem_sup_of_forall (J_le_normalizer_F hW h d hK hQ (hJ₄J hj)) hbN
    (fun b hb => ?_) a ha
  rw [commutatorElement_def, show j * b * j⁻¹ * b⁻¹ = 1 by rw [hSb b hb]; group]
  exact one_mem _

theorem commutator_J₃_mem_F_of_mem_M (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ j ∈ d.J₃, ∀ a ∈ d.M, ⁅j, a⁆ ∈ d.F := by
  intro j hj a ha
  obtain ⟨-, -, -, -, -, haM, -, -, -⟩ := d.yamada_defs
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  have hJ₃J : d.J₃ ≤ d.J := d.image_mono inf_le_left
  have hSa : ∀ b ∈ d.rootGroup g2r, j * b = b * j := fun b hb => by
    have hb' := hb
    rw [← S_inf_centralizer_J₃ hW h d hK hQ] at hb'
    exact mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb').2 j hj
  have hbN : d.rootGroup g2r ≤ normalizer (d.F : Set G) := fun b hb =>
    d.S_le_normalizers.2.2.2.2.1 ((le_sup_left.trans haM.le |>.trans hMS) hb)
  rw [← haM] at ha
  refine commutator_mem_of_mem_sup_of_forall (J_le_normalizer_F hW h d hK hQ (hJ₃J hj)) hbN
    (fun b hb => ?_) a ha
  rw [commutatorElement_def, show j * b * j⁻¹ * b⁻¹ = 1 by rw [hSa b hb]; group]
  exact one_mem _

theorem commutator_mem_R₅_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {c x s y : G}
    (hc : c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) (hx : x ∈ yamadaR₈ d t)
    (hs : s ∈ d.S) (hy : y ∈ yamadaF₅ d t) (hxt : x * t * x⁻¹ = t * s * y) :
    c * x * c⁻¹ ∈ yamadaR₈ d t ∧ (⁅c, x⁆ ∈ yamadaR₅ d t ↔ ⁅c, s⁆ ∈ d.F) := by
  obtain ⟨hN, hFN, φ, hφ, hφc⟩ := h.yamada_5_49_3 hW d hK hQ
  have hX : φ (QuotientGroup.mk (⟨x, hx⟩ : yamadaR₈ d t)) = QuotientGroup.mk (⟨s, hs⟩ : d.S) :=
    hφ ⟨x, hx⟩ ⟨s, hs⟩ y hy hxt
  obtain ⟨hx', hs', he⟩ := hφc c hc ⟨x, hx⟩ ⟨s, hs⟩ hX
  refine ⟨hx', ?_⟩
  have hcx : c * x * c⁻¹ * x⁻¹ ∈ yamadaR₈ d t := mul_mem hx' (inv_mem hx)
  have hcs : c * s * c⁻¹ * s⁻¹ ∈ d.S := mul_mem hs' (inv_mem hs)
  have e1 : (⟨c * x * c⁻¹ * x⁻¹, hcx⟩ : yamadaR₈ d t) = ⟨c * x * c⁻¹, hx'⟩ * ⟨x, hx⟩⁻¹ := rfl
  have e2 : (⟨c * s * c⁻¹ * s⁻¹, hcs⟩ : d.S) = ⟨c * s * c⁻¹, hs'⟩ * ⟨s, hs⟩⁻¹ := rfl
  have key : φ (QuotientGroup.mk (⟨c * x * c⁻¹ * x⁻¹, hcx⟩ : yamadaR₈ d t)) =
      QuotientGroup.mk (⟨c * s * c⁻¹ * s⁻¹, hcs⟩ : d.S) := by
    rw [e1, e2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, map_inv, he, hX]
  constructor
  · intro hR
    have h1 : (QuotientGroup.mk (⟨c * x * c⁻¹ * x⁻¹, hcx⟩ : yamadaR₈ d t) :
        yamadaR₈ d t ⧸ (yamadaR₅ d t).subgroupOf (yamadaR₈ d t)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hR)
    rw [h1, map_one] at key
    exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 key.symm)
  · intro hF
    have h1 : (QuotientGroup.mk (⟨c * s * c⁻¹ * s⁻¹, hcs⟩ : d.S) :
        d.S ⧸ d.F.subgroupOf d.S) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hF)
    rw [h1, ← map_one φ] at key
    exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 (φ.injective key))

theorem mem_R₅_iff_of_crossed (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x s y : G}
    (hx : x ∈ yamadaR₈ d t) (hs : s ∈ d.S) (hy : y ∈ yamadaF₅ d t)
    (hxt : x * t * x⁻¹ = t * s * y) : x ∈ yamadaR₅ d t ↔ s ∈ d.F := by
  obtain ⟨hN, hFN, φ, hφ, -⟩ := h.yamada_5_49_3 hW d hK hQ
  have hX : φ (QuotientGroup.mk (⟨x, hx⟩ : yamadaR₈ d t)) = QuotientGroup.mk (⟨s, hs⟩ : d.S) :=
    hφ ⟨x, hx⟩ ⟨s, hs⟩ y hy hxt
  constructor
  · intro hR
    have h1 : (QuotientGroup.mk (⟨x, hx⟩ : yamadaR₈ d t) :
        yamadaR₈ d t ⧸ (yamadaR₅ d t).subgroupOf (yamadaR₈ d t)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hR)
    rw [h1, map_one] at hX
    exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hX.symm)
  · intro hF
    have h1 : (QuotientGroup.mk (⟨s, hs⟩ : d.S) : d.S ⧸ d.F.subgroupOf d.S) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hF)
    rw [h1, ← map_one φ] at hX
    exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 (φ.injective hX))

theorem exists_crossed_D₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaD₇ d t) :
    ∃ a ∈ d.D, ∃ u ∈ yamadaF₅ d t, x * t * x⁻¹ = t * a * u := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  obtain ⟨δ, hδ, hxt⟩ := (h.yamada_5_19 d hK hD).2.1.1 x (yamadaD₇_le_yamadaC₇ d t hx)
  rw [hD.D₁_eq] at hδ
  obtain ⟨a, ha, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer'
    (fun s hs => h.S_le_normalizer_yamadaU₁ d hK hD (hDS hs)) δ hδ
  exact ⟨a, ha, u, U₁_le_F₅ d t hu, by rw [hxt, mul_assoc]⟩

theorem exists_crossed_L₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaL₆ d t) :
    ∃ m ∈ d.M, ∃ y ∈ yamadaF₅ d t, x * t * x⁻¹ = t * m * y := by
  have hD := hQ.doubling
  have hκ : t * x * t * x⁻¹ ∈ yamadaM₂ d t :=
    h.crossed_mem_yamadaM₂ d hK hD (yamadaL₆_le d t hx)
  obtain ⟨m, hm, y, hy, hmy⟩ := Common.exists_mul_of_le_normalizer
    (h.yamadaY₂_le_normalizer_M d hK hD) _ hκ
  refine ⟨m, hm, y, Y₂_le_F₅ d t hy, ?_⟩
  rw [h.conj_t_eq_mul_crossed x, hmy]
  group

theorem commutator_mem_F₅_aux (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {X T A : Subgroup G}
    (hXR₈ : X ≤ yamadaR₈ d t) (hAJ : A ≤ d.J) (hTS : T ≤ d.S)
    (hXR₅ : X ⊓ yamadaR₅ d t = T ⊔ yamadaF₅ d t) (hel : ElemModulo (yamadaF₅ d t) X)
    (hAX : A ≤ normalizer (X : Set G))
    (hcross : ∀ x ∈ X, ∃ s ∈ T, ∃ y ∈ yamadaF₅ d t, x * t * x⁻¹ = t * s * y)
    (hAT : ∀ j ∈ A, ∀ s ∈ T, ⁅j, s⁆ ∈ d.F) :
    ∀ j ∈ A, ∀ x ∈ X, ⁅j, x⁆ ∈ yamadaF₅ d t := by
  have hF₅A : A ≤ normalizer (yamadaF₅ d t : Set G) := fun j hj =>
    J_le_normalizer_F₅ hW h d hK hQ (hAJ hj)
  have hTN : T ≤ normalizer (yamadaF₅ d t : Set G) :=
    hTS.trans (Q44.S_le_normalizer_F₅ hW h d hK hQ)
  have hX2 : IsPGroup 2 X :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 _ : IsPGroup 2 (yamadaR₈ d t)).to_le hXR₈
  have hcop : (Nat.card A).Coprime (Nat.card X) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hAJ) (coprime_card_J d hX2)
  refine commutator_mem_of_series_elemModulo (A := X) (B := T ⊔ yamadaF₅ d t)
    (Z := yamadaF₅ d t) (J := A) le_sup_right ?_ hel hAX hF₅A hcop ?_ ?_
  · rw [← hXR₅]
    exact inf_le_left
  · intro j hj x hx
    obtain ⟨s, hs, y, hy, hxt⟩ := hcross x hx
    have hjC := h.J_le_centralizer_inf_normalizer_S d (hAJ hj)
    obtain ⟨-, hiff⟩ := commutator_mem_R₅_iff hW h d hK hQ hjC (hXR₈ hx) (hTS hs) hy hxt
    have hR₅ : ⁅j, x⁆ ∈ yamadaR₅ d t := hiff.2 (hAT j hj s hs)
    have hXm : ⁅j, x⁆ ∈ X := by
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.1 (hAX hj) x).1 hx) (inv_mem hx)
    rw [← hXR₅]
    exact Subgroup.mem_inf.2 ⟨hXm, hR₅⟩
  · intro j hj y hy
    exact commutator_mem_of_mem_sup_of_forall (hF₅A hj) hTN
      (fun a ha => F_le_F₅ hW h d hK hQ (hAT j hj a ha)) y hy

theorem mem_F₅_aux (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {X T A : Subgroup G}
    (hXR₈ : X ≤ yamadaR₈ d t) (hAJ : A ≤ d.J) (hTS : T ≤ d.S) (hFT : d.F ≤ T)
    (hTF₅ : T ⊓ yamadaF₅ d t = d.F) (hAT : A ≤ normalizer (T : Set G))
    (hTC : T ⊓ centralizer (A : Set G) ≤ d.F)
    (hXR₅ : X ⊓ yamadaR₅ d t = T ⊔ yamadaF₅ d t)
    (hcross : ∀ x ∈ X, ∃ s ∈ T, ∃ y ∈ yamadaF₅ d t, x * t * x⁻¹ = t * s * y) :
    ∀ x ∈ X, (∀ j ∈ A, ⁅j, x⁆ ∈ yamadaF₅ d t) → x ∈ yamadaF₅ d t := by
  have hF₅A : A ≤ normalizer (yamadaF₅ d t : Set G) := fun j hj =>
    J_le_normalizer_F₅ hW h d hK hQ (hAJ hj)
  have hTN : T ≤ normalizer (yamadaF₅ d t : Set G) :=
    hTS.trans (Q44.S_le_normalizer_F₅ hW h d hK hQ)
  have hTNF : T ≤ normalizer (d.F : Set G) := hTS.trans d.S_le_normalizers.2.2.2.2.1
  have hAF : A ≤ normalizer (d.F : Set G) := fun j hj =>
    J_le_normalizer_F hW h d hK hQ (hAJ hj)
  have hT2 : IsPGroup 2 T := d.isSylowOf_S.isPGroup.to_le hTS
  have fpf : ∀ a ∈ T, (∀ j ∈ A, ⁅j, a⁆ ∈ yamadaF₅ d t) → a ∈ d.F := by
    intro a ha hfa
    have hfix' : ∀ j ∈ A, a⁻¹ * (j * a * j⁻¹) ∈ d.F := by
      intro j hj
      have h0 : ⁅j, a⁆ ∈ T := by
        rw [commutatorElement_def]
        exact mul_mem ((mem_normalizer_iff.1 (hAT hj) a).1 ha) (inv_mem ha)
      have h1 : ⁅j, a⁆ ∈ T ⊓ yamadaF₅ d t := Subgroup.mem_inf.2 ⟨h0, hfa j hj⟩
      rw [hTF₅] at h1
      have h2 := (mem_normalizer_iff.1 (hTNF (inv_mem ha)) _).1 h1
      rwa [show a⁻¹ * ⁅j, a⁆ * a⁻¹⁻¹ = a⁻¹ * (j * a * j⁻¹) by
        simp only [commutatorElement_def]; group] at h2
    obtain ⟨c, hc, n, hn, hac⟩ := exists_centralizer_mul_of_le_J d hAJ hFT hTNF hAT hAF hT2 ha
      hfix'
    rw [hac]
    exact mul_mem (hTC hc) hn
  intro x hx hfix
  obtain ⟨s, hs, y, hy, hxt⟩ := hcross x hx
  have hsF : s ∈ d.F := fpf s hs (fun j hj => by
    have hjC := h.J_le_centralizer_inf_normalizer_S d (hAJ hj)
    obtain ⟨-, hiff⟩ := commutator_mem_R₅_iff hW h d hK hQ hjC (hXR₈ hx) (hTS hs) hy hxt
    exact F_le_F₅ hW h d hK hQ (hiff.1 (F₅_le_R₅ hW h d hK hQ (hfix j hj))))
  have hxR₅ : x ∈ yamadaR₅ d t :=
    (mem_R₅_iff_of_crossed hW h d hK hQ (hXR₈ hx) (hTS hs) hy hxt).2 hsF
  have hx' : x ∈ T ⊔ yamadaF₅ d t := by
    rw [← hXR₅]
    exact Subgroup.mem_inf.2 ⟨hx, hxR₅⟩
  obtain ⟨a, ha, z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer' hTN x hx'
  have haF : a ∈ d.F := fpf a ha (fun j hj =>
    (commutator_mul_mem_iff_of_mem_normalizer (hF₅A hj) (hTN ha) hz).1 (hfix j hj))
  exact mul_mem (F_le_F₅ hW h d hK hQ haF) hz

end JWeight

open JWeight in

theorem commutator_J₄_yamadaD₇_le_yamadaF₅ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ j ∈ d.J₄, ∀ x ∈ yamadaD₇ d t, ⁅j, x⁆ ∈ yamadaF₅ d t := by
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  have hJ₄J : d.J₄ ≤ d.J := d.image_mono inf_le_left
  refine commutator_mem_F₅_aux hW h d hK hQ (X := yamadaD₇ d t) (T := d.D) (A := d.J₄)
    ((yamadaD₇_le_yamadaP d t).trans hPR₈) hJ₄J hDS
    ((yamadaD₇_inf_yamadaR₅ hW h d hK hQ).trans (yamadaS₅_eq_sup hW h d hK hQ).1.2.2)
    (fun x hx y hy => ⟨U₁_le_F₅ d t ((elemModulo_yamadaD₇ hW h d hK hQ) x hx y hy).1,
      U₁_le_F₅ d t ((elemModulo_yamadaD₇ hW h d hK hQ) x hx y hy).2⟩)
    (fun j hj => J_le_normalizer_yamadaD₇ hW h d hK hQ (hJ₄J hj)) ?_
    (commutator_J₄_mem_F_of_mem_D hW h d hK hQ)
  intro x hx
  obtain ⟨a, ha, u, hu, hxt⟩ := exists_crossed_D₇ hW h d hK hQ hx
  exact ⟨a, ha, u, hu, hxt⟩

open JWeight in

theorem commutator_J₃_yamadaM₆_le_yamadaF₅ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ j ∈ d.J₃, ∀ x ∈ yamadaM₆ d t, ⁅j, x⁆ ∈ yamadaF₅ d t := by
  obtain ⟨-, hPR₈, -, -, hS₆P, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  have hJ₃J : d.J₃ ≤ d.J := d.image_mono inf_le_left
  refine commutator_mem_F₅_aux hW h d hK hQ (X := yamadaM₆ d t) (T := d.M) (A := d.J₃)
    ((yamadaM₆_le_yamadaS₆ d t).trans (hS₆P.trans hPR₈)) hJ₃J hMS
    ((yamadaM₆_inf_yamadaR₅ hW h d hK hQ).trans (yamadaS₅_eq_sup hW h d hK hQ).1.2.1)
    (fun x hx y hy => ⟨Y₂_le_F₅ d t ((elemModulo_yamadaM₆ hW h d hK hQ) x hx y hy).1,
      Y₂_le_F₅ d t ((elemModulo_yamadaM₆ hW h d hK hQ) x hx y hy).2⟩)
    (fun j hj => J_le_normalizer_yamadaM₆ hW h d hK hQ (hJ₃J hj)) ?_
    (commutator_J₃_mem_F_of_mem_M hW h d hK hQ)
  intro x hx
  obtain ⟨m, hm, y, hy, hxt⟩ := exists_crossed_L₆ hW h d hK hQ
    (yamadaM₆_le_yamadaL₆ hW h d hK hQ hx)
  exact ⟨m, hm, y, hy, hxt⟩

open JWeight in

theorem mem_yamadaF₅_of_fixed_J₄_yamadaM₆ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ x ∈ yamadaM₆ d t, (∀ j ∈ d.J₄, ⁅j, x⁆ ∈ yamadaF₅ d t) → x ∈ yamadaF₅ d t := by
  obtain ⟨-, hPR₈, -, -, hS₆P, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, -, -, hDMF, -⟩ := d.yamada_defs
  obtain ⟨-, -, -, -, -, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  have hJ₄J : d.J₄ ≤ d.J := d.image_mono inf_le_left
  refine mem_F₅_aux hW h d hK hQ (X := yamadaM₆ d t) (T := d.M) (A := d.J₄)
    ((yamadaM₆_le_yamadaS₆ d t).trans (hS₆P.trans hPR₈)) hJ₄J hMS hFM
    (yamadaS₅_eq_sup hW h d hK hQ).2.2.1 (fun j hj => J_le_normalizer_M hW h d hK hQ (hJ₄J hj))
    ?_ ((yamadaM₆_inf_yamadaR₅ hW h d hK hQ).trans (yamadaS₅_eq_sup hW h d hK hQ).1.2.1) ?_
  · intro c hc
    obtain ⟨hcM, hcC⟩ := Subgroup.mem_inf.1 hc
    have hcS : c ∈ d.S ⊓ centralizer (d.J₄ : Set G) := Subgroup.mem_inf.2 ⟨hMS hcM, hcC⟩
    have hcD : c ∈ d.D := Q44.S_inf_centralizer_J₄_le_D h d hK hQ hcS
    rw [← hDMF]
    exact Subgroup.mem_inf.2 ⟨hcD, hcM⟩
  · intro x hx
    obtain ⟨m, hm, y, hy, hxt⟩ := exists_crossed_L₆ hW h d hK hQ
      (yamadaM₆_le_yamadaL₆ hW h d hK hQ hx)
    exact ⟨m, hm, y, hy, hxt⟩

open JWeight in

theorem mem_yamadaF₅_of_fixed_J₃_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ x ∈ yamadaD₇ d t, (∀ j ∈ d.J₃, ⁅j, x⁆ ∈ yamadaF₅ d t) → x ∈ yamadaF₅ d t := by
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, haM, -, hDMF, -⟩ := d.yamada_defs
  obtain ⟨-, -, -, -, -, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  have hJ₃J : d.J₃ ≤ d.J := d.image_mono inf_le_left
  refine mem_F₅_aux hW h d hK hQ (X := yamadaD₇ d t) (T := d.D) (A := d.J₃)
    ((yamadaD₇_le_yamadaP d t).trans hPR₈) hJ₃J hDS hFD
    (yamadaS₅_eq_sup hW h d hK hQ).2.2.2 (fun j hj => J_le_normalizer_D hW h d hK hQ (hJ₃J hj))
    ?_ ((yamadaD₇_inf_yamadaR₅ hW h d hK hQ).trans (yamadaS₅_eq_sup hW h d hK hQ).1.2.2) ?_
  · intro c hc
    obtain ⟨hcD, hcC⟩ := Subgroup.mem_inf.1 hc
    have hcS : c ∈ d.S ⊓ centralizer (d.J₃ : Set G) := Subgroup.mem_inf.2 ⟨hDS hcD, hcC⟩
    rw [S_inf_centralizer_J₃ hW h d hK hQ] at hcS
    have hcM : c ∈ d.M := by
      rw [← haM]
      exact mem_sup_left hcS
    rw [← hDMF]
    exact Subgroup.mem_inf.2 ⟨hcD, hcM⟩
  · intro x hx
    obtain ⟨a, ha, u, hu, hxt⟩ := exists_crossed_D₇ hW h d hK hQ hx
    exact ⟨a, ha, u, hu, hxt⟩

theorem J_le_normalizer_yamadaR₅ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaR₅ d t : Set G) := fun j hj =>
  (LieType.BorelTits.le_normalizer_pCoreOf 2 (normalizer (yamadaR₂ d t : Set G)))
    ((h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).1
      (h.J_le_centralizer_inf_normalizer_S d hj))

theorem J₃_le_J (d : G2Data L K) : d.J₃ ≤ d.J := d.image_mono inf_le_left

theorem J₄_le_J (d : G2Data L K) : d.J₄ ≤ d.J := d.image_mono inf_le_left

theorem coprime_card_J_pow (d : G2Data L K) (m : ℕ) :
    (Nat.card d.J₃).Coprime (Nat.card K ^ m) ∧ (Nat.card d.J₄).Coprime (Nat.card K ^ m) := by
  have key : ∀ n : ℕ, n = Nat.card K - 1 → n.Coprime (Nat.card K ^ m) := by
    intro n hn
    have hq : 0 < Nat.card K := Nat.card_pos
    have h1 : n.Coprime (Nat.card K) := by
      have : Nat.card K = n + 1 := by omega
      rw [this]
      exact (Nat.coprime_self_add_right.2 (Nat.coprime_one_right n))
    exact h1.pow_right m
  exact ⟨key _ (d.yamada_3_9_1_G 2).2, key _ (d.yamada_3_9_1_G 3).2⟩

theorem commutator_eq_one_of_mem_centralizer {J : Subgroup G} {j c : G}
    (hj : j ∈ J) (hc : c ∈ centralizer (J : Set G)) : ⁅j, c⁆ = 1 := by
  have := mem_centralizer_iff.1 hc j hj
  rw [commutatorElement_def, this]
  group

theorem isPGroup_yamadaP (h : Setup G L f t) (d : G2Data L K)
    (hP : yamadaP d t ≤ yamadaR₈ d t) : IsPGroup 2 (yamadaP d t) :=
  IsPGroup.to_le (LieType.BorelTits.pCoreOf_isPGroup 2 _) hP

theorem yamadaP_le_normalizer_D₇_M₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaP d t ≤ normalizer (yamadaD₇ d t : Set G) ∧
      yamadaP d t ≤ normalizer (yamadaM₆ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨⟨hFR₅, -, -, -⟩, hFchar, -, -, -⟩ := h.yamada_5_46_4 hW d hK hQ
  have hNF := normalizer_le_normalizer_of_characteristic_subgroupOf hFR₅ hFchar
  have hPF : yamadaP d t ≤ normalizer (yamadaF₅ d t : Set G) :=
    hPR₈.trans ((yamadaR₈_le d t).trans hNF)
  have hJF : d.J ≤ normalizer (yamadaF₅ d t : Set G) :=
    (h.J_le_normalizer_yamadaR₅ d hK hD).trans hNF
  have hP2 := isPGroup_yamadaP h d hPR₈
  have hY₂F₅ : yamadaY₂ d t ≤ yamadaF₅ d t := by
    obtain ⟨hY₂W, -, hWX, -⟩ := h.yamada_5_46_1 hW d hK hQ
    exact hY₂W.trans (hWX ▸ le_sup_left)
  have hU₁Y₂ : yamadaU₁ d t ≤ yamadaY₂ d t := le_sup_left
  have hD₇P : yamadaD₇ d t ≤ yamadaP d t := inf_le_left
  have hM₆P := h.yamadaM₆_le_yamadaP hW d hK hQ
  have hP : ∀ p ∈ yamadaP d t, ∃ m ∈ yamadaM₆ d t, ∃ d' ∈ yamadaD₇ d t, p = m * d' := by
    intro p hp
    have : p ∈ ((yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G)) := by
      rw [← h.yamadaP_eq_mul hW d hK hQ]
      exact hp
    obtain ⟨m, hm, d', hd', rfl⟩ := Set.mem_mul.1 this
    exact ⟨m, hm, d', hd', rfl⟩
  have hP' : ∀ p ∈ yamadaP d t, ∃ d' ∈ yamadaD₇ d t, ∃ m ∈ yamadaM₆ d t, p = d' * m := by
    intro p hp
    obtain ⟨m, hm, d', hd', he⟩ := hP p⁻¹ (inv_mem hp)
    refine ⟨d'⁻¹, inv_mem hd', m⁻¹, inv_mem hm, ?_⟩
    have : p = (m * d')⁻¹ := by rw [← he, inv_inv]
    rw [this, mul_inv_rev]
  have hcopD := (coprime_card_J_pow d 10).1
  have hcopM := (coprime_card_J_pow d 10).2
  refine ⟨?_, ?_⟩
  ·
    have hFM := h.yamadaF₅_le_yamadaD₇ hW d hK hQ
    have hJM : d.J₃ ≤ normalizer (yamadaD₇ d t : Set G) :=
      (J₃_le_J d).trans (h.J_le_normalizer_yamadaD₇ hW d hK hQ)
    have hJF₃ : d.J₃ ≤ normalizer (yamadaF₅ d t : Set G) := (J₃_le_J d).trans hJF
    have hsolv : Group.IsSolvable (yamadaD₇ d t) :=
      isSolvable_of_isPGroup_two (IsPGroup.to_le hP2 hD₇P)
    have hab : ∀ x ∈ yamadaD₇ d t, ∀ y ∈ yamadaD₇ d t, ⁅x, y⁆ ∈ yamadaF₅ d t := fun x hx y hy =>
      hU₁Y₂.trans hY₂F₅ ((h.yamada_5_55_1_D hW d hK hQ).1 x hx y hy).2
    have hcop' : (Nat.card d.J₃).Coprime (Nat.card (yamadaD₇ d t)) := by
      rw [h.card_yamadaD₇ hW d hK hQ]
      exact hcopD
    have hfix : ∀ c ∈ yamadaD₇ d t ⊓ centralizer (d.J₃ : Set G), c ∈ yamadaF₅ d t := fun c hc =>
      h.mem_yamadaF₅_of_fixed_J₃_yamadaD₇ hW d hK hQ c hc.1 fun j hj => by
        rw [commutator_eq_one_of_mem_centralizer hj hc.2]
        exact one_mem _
    have hM := (le_commutator_sup_of_forall_fixed hFM hab hJM hJF₃ hsolv hcop' hfix).trans
      (sup_le_sup_right (commutator_mono le_rfl hD₇P) _)
    exact normalizer_of_le_commutator_sup hFM hPF hJM hP'
      (h.commutator_J₃_yamadaM₆_le_yamadaF₅ hW d hK hQ) hM
  ·
    have hFM := h.yamadaF₅_le_yamadaM₆ hW d hK hQ
    have hJM : d.J₄ ≤ normalizer (yamadaM₆ d t : Set G) :=
      (J₄_le_J d).trans (h.J_le_normalizer_yamadaM₆ hW d hK hQ)
    have hJF₄ : d.J₄ ≤ normalizer (yamadaF₅ d t : Set G) := (J₄_le_J d).trans hJF
    have hsolv : Group.IsSolvable (yamadaM₆ d t) :=
      isSolvable_of_isPGroup_two (IsPGroup.to_le hP2 hM₆P)
    have hab : ∀ x ∈ yamadaM₆ d t, ∀ y ∈ yamadaM₆ d t, ⁅x, y⁆ ∈ yamadaF₅ d t := fun x hx y hy =>
      hY₂F₅ ((h.yamada_5_55_1_M hW d hK hQ).1 x hx y hy).2
    have hcop' : (Nat.card d.J₄).Coprime (Nat.card (yamadaM₆ d t)) := by
      rw [(h.card_yamada_five_six hW d hK hQ).2.2.2.2.2.2.1]
      exact hcopM
    have hfix : ∀ c ∈ yamadaM₆ d t ⊓ centralizer (d.J₄ : Set G), c ∈ yamadaF₅ d t := fun c hc =>
      h.mem_yamadaF₅_of_fixed_J₄_yamadaM₆ hW d hK hQ c hc.1 fun j hj => by
        rw [commutator_eq_one_of_mem_centralizer hj hc.2]
        exact one_mem _
    have hM := (le_commutator_sup_of_forall_fixed hFM hab hJM hJF₄ hsolv hcop' hfix).trans
      (sup_le_sup_right (commutator_mono le_rfl hM₆P) _)
    exact normalizer_of_le_commutator_sup hFM hPF hJM hP
      (h.commutator_J₄_yamadaD₇_le_yamadaF₅ hW d hK hQ) hM

theorem commutator_yamadaF₅_yamadaP_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ x ∈ yamadaF₅ d t, ∀ y ∈ yamadaP d t, ⁅x, y⁆ ∈ yamadaY₂ d t := by
  intro x hx y hy
  have hM₆ := h.yamada_5_55_1_M hW d hK hQ
  have hD₇ := h.yamada_5_55_1_D hW d hK hQ
  have hU₁Y₂ : yamadaU₁ d t ≤ yamadaY₂ d t := le_sup_left
  have hM₆N : yamadaM₆ d t ≤ normalizer (yamadaY₂ d t : Set G) :=
    le_normalizer_of_elemModulo (h.yamadaY₂_le_yamadaM₆ hW d hK hQ) hM₆.1
  have hFM := h.yamadaF₅_le_yamadaM₆ hW d hK hQ
  have hFD := h.yamadaF₅_le_yamadaD₇ hW d hK hQ
  have : y ∈ ((yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G)) := by
    rw [← h.yamadaP_eq_mul hW d hK hQ]
    exact hy
  obtain ⟨m, hm, d', hd', rfl⟩ := Set.mem_mul.1 this
  have e : ⁅x, m * d'⁆ = ⁅x, m⁆ * (m * ⁅x, d'⁆ * m⁻¹) := by
    simp [commutatorElement_def]; group
  rw [e]
  exact mul_mem (hM₆.1 x (hFM hx) m hm).2 ((mem_normalizer_iff.1 (hM₆N hm) _).1
    (hU₁Y₂ (hD₇.1 x (hFD hx) d' hd').2))

theorem normalizer_L_le_yamadaD₇_M₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    L ⊓ normalizer (d.U : Set G) ≤ normalizer (yamadaD₇ d t : Set G) ∧
      L ⊓ normalizer (d.Y : Set G) ≤ normalizer (yamadaM₆ d t : Set G) :=
  ⟨h.normalizer_L_inf_U_le_yamadaD₇ hW d hK hQ, h.normalizer_L_inf_Y_le_yamadaM₆ hW d hK hQ⟩

theorem yamada_5_55_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (closure {z | ∃ g ∈ yamadaD₇ d t, z = g ^ 2} = yamadaU₁ d t ∧
      ⁅yamadaD₇ d t, yamadaD₇ d t⁆ = yamadaU₁ d t) ∧
    (closure {z | ∃ g ∈ yamadaM₆ d t, z = g ^ 2} = yamadaY₂ d t ∧
      ⁅yamadaM₆ d t, yamadaM₆ d t⁆ = yamadaY₂ d t) :=
  ⟨(h.yamada_5_55_1_D hW d hK hQ).2, (h.yamada_5_55_1_M hW d hK hQ).2⟩

theorem yamada_5_55_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (E : Subgroup G) :
    (Maximal (fun E' : Subgroup G => yamadaU₁ d t ≤ E' ∧ E' ≤ yamadaC₇ d t ∧
        ElemModulo (yamadaU₁ d t) E') E ↔ E = yamadaD₇ d t ∨ E = yamadaC₁ d t) ∧
    (Maximal (fun E' : Subgroup G => yamadaY₂ d t ≤ E' ∧ E' ≤ yamadaL₆ d t ∧
        ElemModulo (yamadaY₂ d t) E') E ↔ E = yamadaM₆ d t ∨ E = yamadaL₂ d t) := by
  have hD := hQ.doubling
  have ht2 := h.t_mul_t
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨-, -, hC₇, htN₇, htD₇⟩ := h.yamada_5_51 hW d hK hQ
    obtain ⟨hC₁eq, hD₁lt⟩ := (h.yamada_5_8_1 d hK).2
    have hD₁C₁ := h.yamadaD₁_le_yamadaC₁ d hK
    have htU₁ := (h.t_mem_normalizer_yamadaU₁ d hK hD).1
    have htD₁ : t ∈ normalizer (yamadaD₁ d t : Set G) :=
      (h.normalizer_yamadaC₁_le d hK hD).1 (Subgroup.le_normalizer (h.t_mem_yamadaC₁ d hK))
    have key := maximal_elemModulo_iff_sup_zpowers (N := yamadaU₁ d t) (A := yamadaD₇ d t)
      (C := yamadaD₁ d t) (t := t) (h.yamadaU₁_le_yamadaD₇ hW d hK hQ)
      (h.yamadaD₁_le_yamadaD₇ hW d hK hQ) ht2 htD₇ htN₇ htU₁
      (h.yamada_5_55_1_D hW d hK hQ).1 ?_ ?_ E
    · rw [hC₇, ← hC₁eq] at key
      exact key
    · intro a ha
      constructor
      · intro haD₁
        have haC₁ : a ∈ yamadaC₁ d t := hD₁C₁ haD₁
        have hmem : a * t * a⁻¹ ∈ {x | ∃ c ∈ yamadaC₁ d t, c * t * c⁻¹ = x} := ⟨a, haC₁, rfl⟩
        rw [h.yamada_5_3_2 d hK] at hmem
        obtain ⟨u, hu, hut⟩ := hmem
        have : t * a * t * a⁻¹ = u := by
          calc t * a * t * a⁻¹ = t * (a * t * a⁻¹) := by group
            _ = t * (t * u) := by rw [← hut]
            _ = u := by rw [← mul_assoc, ht2, one_mul]
        rw [this]
        exact hD.U_le hu
      · intro hat
        have haC₇ : a ∈ yamadaC₇ d t := (inf_le_right : yamadaD₇ d t ≤ yamadaC₇ d t) ha
        have haN₁ : a ∈ normalizer (yamadaC₁ d t : Set G) := LieType.BorelTits.pCoreOf_le 2 _ haC₇
        have haU₁ : a ∈ normalizer (yamadaU₁ d t : Set G) :=
          (h.normalizer_yamadaC₁_le d hK hD).2 ((h.normalizer_yamadaC₁_le d hK hD).1 haN₁)
        have ha1 := mem_normalizer_sup_zpowers ht2 htU₁ haU₁ hat
        rw [h.yamada_5_17_1 d hK hD] at ha1
        have haC₁ : a ∈ yamadaC₁ d t := by
          rw [← (h.yamada_5_19 d hK hD).1.2.2]
          exact ⟨haC₇, ha1⟩
        rw [hC₁eq] at haC₁
        exact mem_of_mem_sup_zpowers_of_mul_self_eq_one ht2 htD₁
          (h.yamadaD₁_le_yamadaD₇ hW d hK hQ) htD₇ haC₁ ha
    · by_contra hne
      push Not at hne
      have : yamadaY₂ d t ≤ yamadaR₁ d t := fun y hy =>
        (le_sup_left : yamadaC₁ d t ≤ yamadaR₁ d t)
          (hD₁C₁ (hne y (h.yamadaY₂_le_yamadaD₇ hW d hK hQ hy)))
      exact h.not_yamadaY₂_le_yamadaR₁ d hK hD hQ this
  ·
    obtain ⟨⟨hL₆, htN₆, htM₆⟩, -⟩ := h.yamada_5_44_1 hW d hK hQ
    have hL₂eq := (h.yamada_5_13_1 d hK hD).2.2.2.1
    have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
    have htY₂ : t ∈ normalizer (yamadaY₂ d t : Set G) :=
      h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂
    have htM₂ : t ∈ normalizer (yamadaM₂ d t : Set G) :=
      (h.normalizer_yamadaL₂_le d hK hD).1 (Subgroup.le_normalizer htL₂)
    have hM₂M₆ := h.yamadaM₂_le_yamadaM₆ hW d hK hQ
    have key := maximal_elemModulo_iff_sup_zpowers (N := yamadaY₂ d t) (A := yamadaM₆ d t)
      (C := yamadaM₂ d t) (t := t) (h.yamadaY₂_le_yamadaM₆ hW d hK hQ) hM₂M₆ ht2 htM₆ htN₆ htY₂
      (h.yamada_5_55_1_M hW d hK hQ).1 ?_ ?_ E
    · rw [hL₆, ← hL₂eq] at key
      exact key
    · intro a ha
      constructor
      · intro haM₂
        have haL₂ : a ∈ yamadaL₂ d t := h.yamadaM₂_le_yamadaL₂ d hK hD haM₂
        have hmem : a * t * a⁻¹ ∈ {x | ∃ c ∈ yamadaL₂ d t, c * t * c⁻¹ = x} := ⟨a, haL₂, rfl⟩
        rw [h.yamada_5_5_2 d hK] at hmem
        obtain ⟨y, hy, hyt⟩ := hmem
        have : t * a * t * a⁻¹ = y := by
          calc t * a * t * a⁻¹ = t * (a * t * a⁻¹) := by group
            _ = t * (t * y) := by rw [← hyt]
            _ = y := by rw [← mul_assoc, ht2, one_mul]
        rw [this]
        exact h.Y_le_yamadaY₂ d hK hD hy
      · intro hat
        have haL₆ : a ∈ yamadaL₆ d t := hL₆ ▸ (le_sup_left : yamadaM₆ d t ≤ _) ha
        have haN : a ∈ normalizer (yamadaY₂ d t : Set G) :=
          (h.normalizer_yamadaL₂_le d hK hD).2 (yamadaL₆_le d t haL₆)
        have ha1 := mem_normalizer_sup_zpowers ht2 htY₂ haN hat
        rw [h.yamada_5_17_2 hW d hK hD] at ha1
        have haL₂ : a ∈ yamadaL₂ d t := yamadaL₆_inf_le d t ⟨haL₆, ha1⟩
        rw [hL₂eq] at haL₂
        exact mem_of_mem_sup_zpowers_of_mul_self_eq_one ht2 htM₂ hM₂M₆ htM₆ haL₂ ha
    · by_contra hne
      push Not at hne
      have hle : yamadaM₆ d t ≤ yamadaM₂ d t := fun a ha => hne a ha
      have h1 := Subgroup.card_le_of_le hle
      rw [(h.card_yamada_five_six hW d hK hQ).2.2.2.2.2.2.1, h.card_yamadaM₂ d hK hD] at h1
      have h3 : 1 < Nat.card K := by
        have := h.four_le
        omega
      have : Nat.card K ^ 7 < Nat.card K ^ 10 := Nat.pow_lt_pow_right h3 (by norm_num)
      omega

theorem yamada_5_55_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (normalizer (yamadaC₇ d t : Set G) = normalizer (yamadaC₁ d t : Set G) ∧
      normalizer (yamadaC₁ d t : Set G) ≤ normalizer (yamadaD₇ d t : Set G)) ∧
    (normalizer (yamadaL₆ d t : Set G) = normalizer (yamadaL₂ d t : Set G) ∧
      normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaM₆ d t : Set G)) := by
  have hD := hQ.doubling
  have hq : 1 < Nat.card K := by
    have := h.four_le
    omega
  refine ⟨?_, ?_⟩
  ·
    have hC₁C₇ : normalizer (yamadaC₁ d t : Set G) ≤ normalizer (yamadaC₇ d t : Set G) :=
      LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hmain : ∀ g ∈ normalizer (yamadaC₇ d t : Set G),
        g ∈ normalizer (yamadaD₇ d t : Set G) ∧ g ∈ normalizer (yamadaC₁ d t : Set G) := by
      intro g hg
      have hgD₁ : g ∈ normalizer (yamadaD₁ d t : Set G) := by
        have := normalizer_le_normalizer_closure_sq (yamadaC₇ d t) hg
        rwa [h.yamada_5_53 hW d hK hQ] at this
      have hgU₁ := (h.normalizer_yamadaC₁_le d hK hD).2 hgD₁
      have h55 := h.yamada_5_55_2 hW d hK hQ
      have hmaxD := ((h55 (yamadaD₇ d t)).1).2 (Or.inl rfl)
      have hmaxC := ((h55 (yamadaC₁ d t)).1).2 (Or.inr rfl)
      have hD' := (((h55 _).1).1 (maximal_map_conj hgU₁ hg hmaxD))
      have hC' := (((h55 _).1).1 (maximal_map_conj hgU₁ hg hmaxC))
      have hcD : Nat.card (yamadaD₇ d t) = Nat.card K ^ 10 := h.card_yamadaD₇ hW d hK hQ
      have hcC : Nat.card (yamadaC₁ d t) = 2 * Nat.card K ^ 6 := by
        rw [h.card_yamadaC₁ d hK, h.card_yamadaD₁_of_doubling d hD]
      have hlt : 2 * Nat.card K ^ 6 < Nat.card K ^ 10 := by
        have h1 : Nat.card K ^ 6 * 2 < Nat.card K ^ 6 * Nat.card K ^ 4 := by
          apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
          calc 2 ≤ Nat.card K := hq
            _ < Nat.card K ^ 2 := by nlinarith
            _ ≤ Nat.card K ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
        calc 2 * Nat.card K ^ 6 = Nat.card K ^ 6 * 2 := by ring
          _ < Nat.card K ^ 6 * Nat.card K ^ 4 := h1
          _ = Nat.card K ^ 10 := by ring
      have hcC' : ∀ g' : G, Nat.card ((yamadaC₁ d t).map (MulAut.conj g').toMonoidHom) =
          2 * Nat.card K ^ 6 := fun g' => (card_map_conj _ _).trans hcC
      have hcD' : ∀ g' : G, Nat.card ((yamadaD₇ d t).map (MulAut.conj g').toMonoidHom) =
          Nat.card K ^ 10 := fun g' => (card_map_conj _ _).trans hcD
      rcases hD' with e1 | e1
      · rcases hC' with e2 | e2
        · exfalso
          have := hcC' g
          rw [e2, hcD] at this
          omega
        · exact ⟨mem_normalizer_of_map_conj_eq e1, mem_normalizer_of_map_conj_eq e2⟩
      · exfalso
        have := hcD' g
        rw [e1, hcC] at this
        omega
    refine ⟨le_antisymm (fun g hg => (hmain g hg).2) hC₁C₇, fun g hg => (hmain g (hC₁C₇ hg)).1⟩
  ·
    have hL₂L₆ : normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaL₆ d t : Set G) :=
      le_normalizer_yamadaL₆ d t
    have hmain : ∀ g ∈ normalizer (yamadaL₆ d t : Set G),
        g ∈ normalizer (yamadaM₆ d t : Set G) ∧ g ∈ normalizer (yamadaL₂ d t : Set G) := by
      intro g hg
      have hgM₂ : g ∈ normalizer (yamadaM₂ d t : Set G) := by
        have := normalizer_le_normalizer_closure_sq (yamadaL₆ d t) hg
        rwa [h.yamada_5_41_2 hW d hK hQ] at this
      have hgY₂ : g ∈ normalizer (yamadaY₂ d t : Set G) := by
        have := mem_normalizer_inf_centralizer hgM₂
        rwa [(h.yamada_5_13_1 d hK hD).2.1] at this
      have h55 := h.yamada_5_55_2 hW d hK hQ
      have hmaxM := ((h55 (yamadaM₆ d t)).2).2 (Or.inl rfl)
      have hmaxL := ((h55 (yamadaL₂ d t)).2).2 (Or.inr rfl)
      have hM' := (((h55 _).2).1 (maximal_map_conj hgY₂ hg hmaxM))
      have hL' := (((h55 _).2).1 (maximal_map_conj hgY₂ hg hmaxL))
      have hcM : Nat.card (yamadaM₆ d t) = Nat.card K ^ 10 :=
        (h.card_yamada_five_six hW d hK hQ).2.2.2.2.2.2.1
      have hcL : Nat.card (yamadaL₂ d t) = 2 * Nat.card K ^ 7 := h.card_yamadaL₂ d hK
      have hlt : 2 * Nat.card K ^ 7 < Nat.card K ^ 10 := by
        have h1 : Nat.card K ^ 7 * 2 < Nat.card K ^ 7 * Nat.card K ^ 3 := by
          apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
          calc 2 ≤ Nat.card K := hq
            _ < Nat.card K ^ 2 := by nlinarith
            _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
        calc 2 * Nat.card K ^ 7 = Nat.card K ^ 7 * 2 := by ring
          _ < Nat.card K ^ 7 * Nat.card K ^ 3 := h1
          _ = Nat.card K ^ 10 := by ring
      rcases hM' with e1 | e1
      · rcases hL' with e2 | e2
        · exfalso
          have := card_map_conj (yamadaL₂ d t) g
          rw [e2, hcM, hcL] at this
          omega
        · exact ⟨mem_normalizer_of_map_conj_eq e1, mem_normalizer_of_map_conj_eq e2⟩
      · exfalso
        have := card_map_conj (yamadaM₆ d t) g
        rw [e1, hcL, hcM] at this
        omega
    refine ⟨le_antisymm (fun g hg => (hmain g hg).2) hL₂L₆, fun g hg => (hmain g (hL₂L₆ hg)).1⟩

theorem yamada_5_56 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaD₇ d t ≤ yamadaR₈ d t ∧ yamadaR₈ d t ≤ normalizer (yamadaD₇ d t : Set G)) ∧
      (yamadaM₆ d t ≤ yamadaR₈ d t ∧ yamadaR₈ d t ≤ normalizer (yamadaM₆ d t : Set G)) := by
  obtain ⟨hPD, hPM⟩ := h.yamadaP_le_normalizer_D₇_M₆ hW d hK hQ
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨⟨hR₈, -, -⟩, -, ⟨-, htND, -⟩⟩ := h.yamada_5_51 hW d hK hQ
  have htNM := ((h.yamada_5_44_1 hW d hK hQ).1).2.1
  refine ⟨⟨(inf_le_left : yamadaD₇ d t ≤ yamadaP d t).trans hPR₈, ?_⟩,
    ⟨(h.yamadaM₆_le_yamadaP hW d hK hQ).trans hPR₈, ?_⟩⟩
  · rw [← hR₈]
    exact sup_le hPD ((zpowers_le).2 htND)
  · rw [← hR₈]
    exact sup_le hPM ((zpowers_le).2 htNM)

theorem yamada_5_57_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (Subgroup.upperCentralSeries (yamadaP d t) 1).map (yamadaP d t).subtype = yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaP d t) 2).map (yamadaP d t).subtype = yamadaY₂ d t ∧
      (Subgroup.upperCentralSeries (yamadaP d t) 3).map (yamadaP d t).subtype =
        yamadaF₅ d t := by
  have hD := hQ.doubling
  obtain ⟨hZ1, hZ2⟩ := h.yamada_5_52 hW d hK hQ
  obtain ⟨⟨hFR₅, hMR₅, hDR₅, hSR₅⟩, hFchar, -, -, -⟩ := h.yamada_5_46_4 hW d hK hQ
  obtain ⟨-, hPR₈, -, hS₅S₆, hS₆P, hPR₅, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨⟨hS₅eq, -, -⟩, hSF₅, -, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  have hS₅P : yamadaS₅ d t ≤ yamadaP d t := hS₅S₆.trans hS₆P
  have hFS₅ : yamadaF₅ d t ≤ yamadaS₅ d t := hS₅eq ▸ le_sup_right
  refine ⟨hZ1, hZ2, le_antisymm (fun x hx => ?_) (fun x hx => ?_)⟩
  ·
    obtain ⟨hxP, hx2⟩ := mem_map_upperCentralSeries_succ.1 hx
    rw [hZ2] at hx2
    have hY₂F₅ : yamadaY₂ d t ≤ yamadaF₅ d t := by
      obtain ⟨hY₂W, -, hWX, -⟩ := h.yamada_5_46_1 hW d hK hQ
      exact hY₂W.trans (hWX ▸ le_sup_left)
    have hSS₅ : d.S ≤ yamadaS₅ d t := hS₅eq ▸ le_sup_left
    have hS₂S₅ : yamadaS₂ d t ≤ yamadaS₅ d t := sup_le hSS₅ (hY₂F₅.trans hFS₅)
    have hxS₂ : x ∈ normalizer (yamadaS₂ d t : Set G) := by
      refine mem_normalizer_fintype fun y hy => ?_
      have h1 := hx2 y (hS₅P (hS₂S₅ hy))
      have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by simp [commutatorElement_def]
      rw [e]
      exact mul_mem ((le_sup_right : yamadaY₂ d t ≤ yamadaS₂ d t) h1) hy
    have hxR₅ : x ∈ yamadaR₅ d t := by
      have := (h.normalizer_inf_yamadaR₈ hW d hK hQ).2
      rw [← this]
      exact ⟨hPR₈ hxP, hxS₂⟩
    have hxS₅ : x ∈ yamadaS₅ d t := by
      have : x ∈ yamadaP d t ⊓ yamadaR₅ d t := ⟨hxP, hxR₅⟩
      rwa [hPR₅] at this
    have hSN : d.S ≤ normalizer (yamadaF₅ d t : Set G) :=
      (hSS₅.trans hSR₅).trans ((Subgroup.le_normalizer).trans
        (normalizer_le_normalizer_of_characteristic_subgroupOf hFR₅ hFchar))
    rw [hS₅eq] at hxS₅
    obtain ⟨s, hs, f, hf, rfl⟩ := Common.exists_mul_of_le_normalizer' hSN x hxS₅
    refine mul_mem ?_ hf
    have hK4 : 4 ≤ Nat.card K := hQ.four_le
    have hZS := d.yamada_3_12_upperCentralSeries hK4
    have hSL : d.S ≤ L := (d.inclusions).2.2.2.2.2.2.2.2.2
    have hsF : s ∈ d.F := by
      rw [← hZS.2.2]
      refine mem_map_upperCentralSeries_succ.2 ⟨hs, fun y hy => ?_⟩
      rw [hZS.2.1]
      have hyP : y ∈ yamadaP d t := hS₅P (hSS₅ hy)
      have h1 : ⁅s * f, y⁆ ∈ yamadaY₂ d t := hx2 y hyP
      have h2 : ⁅f, y⁆ ∈ yamadaY₂ d t :=
        h.commutator_yamadaF₅_yamadaP_le hW d hK hQ f hf y hyP
      have e : ⁅s, y⁆ = (s * ⁅f, y⁆ * s⁻¹)⁻¹ * ⁅s * f, y⁆ := by
        simp [commutatorElement_def]; group
      have hsN : s ∈ normalizer (yamadaY₂ d t : Set G) := h.S_le_normalizer_yamadaY₂ d hK hD hs
      have h3 : ⁅s, y⁆ ∈ yamadaY₂ d t := by
        rw [e]
        exact mul_mem (inv_mem ((mem_normalizer_iff.1 hsN _).1 h2)) h1
      have hSt : ⁅s, y⁆ ∈ centralizer ({t} : Set G) :=
        h.L_le_centralizer (hSL (mul_mem (mul_mem (mul_mem hs hy) (inv_mem hs)) (inv_mem hy)))
      rw [← (h.yamada_5_13_1 d hK hD).2.2.1]
      exact ⟨h3, hSt⟩
    exact (hSF₅ ▸ (inf_le_right : d.S ⊓ yamadaF₅ d t ≤ yamadaF₅ d t)) hsF
  ·
    refine mem_map_upperCentralSeries_succ.2 ⟨hS₅P (hFS₅ hx), fun y hy => ?_⟩
    rw [hZ2]
    exact h.commutator_yamadaF₅_yamadaP_le hW d hK hQ x hx y hy

theorem yamada_5_57_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaF₅ d t ≤ yamadaM₆ d t ∧ yamadaF₅ d t ≤ yamadaD₇ d t ∧
      yamadaM₆ d t ≤ yamadaP d t ∧ yamadaD₇ d t ≤ yamadaP d t ∧
      yamadaM₆ d t ⊔ yamadaD₇ d t = yamadaP d t ∧ yamadaM₆ d t ⊓ yamadaD₇ d t = yamadaF₅ d t ∧
      ElemModulo (yamadaF₅ d t) (yamadaP d t) := by
  have hFM := h.yamadaF₅_le_yamadaM₆ hW d hK hQ
  have hFD := h.yamadaF₅_le_yamadaD₇ hW d hK hQ
  have hM₆P := h.yamadaM₆_le_yamadaP hW d hK hQ
  have hD₇P : yamadaD₇ d t ≤ yamadaP d t := inf_le_left
  have hinf := h.yamadaM₆_inf_yamadaD₇ hW d hK hQ
  obtain ⟨hPD, hPM⟩ := h.yamadaP_le_normalizer_D₇_M₆ hW d hK hQ
  have hY₂F₅ : yamadaY₂ d t ≤ yamadaF₅ d t := by
    obtain ⟨hY₂W, -, hWX, -⟩ := h.yamada_5_46_1 hW d hK hQ
    exact hY₂W.trans (hWX ▸ le_sup_left)
  have hU₁Y₂ : yamadaU₁ d t ≤ yamadaY₂ d t := le_sup_left
  have hsup : yamadaM₆ d t ⊔ yamadaD₇ d t = yamadaP d t := by
    refine le_antisymm (sup_le hM₆P hD₇P) fun p hp => ?_
    have : p ∈ ((yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G)) := by
      rw [← h.yamadaP_eq_mul hW d hK hQ]
      exact hp
    obtain ⟨m, hm, d', hd', rfl⟩ := Set.mem_mul.1 this
    exact mul_mem (mem_sup_left hm) (mem_sup_right hd')
  refine ⟨hFM, hFD, hM₆P, hD₇P, hsup, hinf, ?_⟩
  rw [← hsup]
  exact elemModulo_sup_of_normalizes hFM hFD hinf.le (hM₆P.trans hPD) (hD₇P.trans hPM)
    ((h.yamada_5_55_1_M hW d hK hQ).1.mono hY₂F₅)
    ((h.yamada_5_55_1_D hW d hK hQ).1.mono (hU₁Y₂.trans hY₂F₅))

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
