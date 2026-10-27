module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs47C
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma46W

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type} [Group G]

omit [Group G] in
theorem commute_of_commutatorElement_eq_one {G : Type} [Group G] {d g : G}
    (h : d⁻¹ * g⁻¹ * d * g = 1) : d * g = g * d := by
  calc d * g = g * d * (d⁻¹ * g⁻¹ * d * g) := by group
    _ = g * d := by rw [h, mul_one]

theorem card_le_two_mul_card_inf_centralizer [Finite G] {D : Subgroup G} {g a : G}
    (haD : ∀ d ∈ D, a * d = d * a)
    (hD : ∀ d ∈ D, d⁻¹ * g⁻¹ * d * g = 1 ∨ d⁻¹ * g⁻¹ * d * g = a) :
    Nat.card D ≤ 2 * Nat.card ↥(D ⊓ centralizer ({g} : Set G)) := by
  classical
  set H : Subgroup G := D ⊓ centralizer ({g} : Set G) with hH
  by_cases hle : D ≤ H
  · have := card_le_of_le hle
    omega
  obtain ⟨d₀, hd₀D, hd₀H⟩ := Set.not_subset.mp hle
  have hd₀g : d₀⁻¹ * g⁻¹ * d₀ * g = a := by
    rcases hD d₀ hd₀D with h1 | h1
    · exact absurd (mem_inf.mpr ⟨hd₀D, mem_centralizer_singleton_iff.mpr
        (commute_of_commutatorElement_eq_one h1)⟩) hd₀H
    · exact h1
  have hsub : (D : Set G) ⊆ (H : Set G) ∪ (fun h => d₀ * h) '' (H : Set G) := by
    intro d hd
    by_cases hdH : d ∈ H
    · exact Or.inl hdH
    right
    have hdg : d⁻¹ * g⁻¹ * d * g = a := by
      rcases hD d hd with h1 | h1
      · exact absurd (mem_inf.mpr ⟨hd, mem_centralizer_singleton_iff.mpr
          (commute_of_commutatorElement_eq_one h1)⟩) hdH
      · exact h1
    refine ⟨d₀⁻¹ * d, mem_inf.mpr ⟨mul_mem (inv_mem hd₀D) hd, ?_⟩, by group⟩
    rw [mem_centralizer_singleton_iff]
    have e1 : g⁻¹ * d * g = d * a := by rw [← hdg]; group
    have e2 : g⁻¹ * d₀ * g = d₀ * a := by rw [← hd₀g]; group
    have hcomm := haD (d₀⁻¹ * d) (mul_mem (inv_mem hd₀D) hd)
    have e3 : g⁻¹ * (d₀⁻¹ * d) * g = d₀⁻¹ * d := by
      calc g⁻¹ * (d₀⁻¹ * d) * g = (g⁻¹ * d₀ * g)⁻¹ * (g⁻¹ * d * g) := by group
        _ = (d₀ * a)⁻¹ * (d * a) := by rw [e1, e2]
        _ = a⁻¹ * (d₀⁻¹ * d) * a := by group
        _ = a⁻¹ * (a * (d₀⁻¹ * d)) := by rw [mul_assoc, ← hcomm]
        _ = d₀⁻¹ * d := by group
    calc d₀⁻¹ * d * g = g * (g⁻¹ * (d₀⁻¹ * d) * g) := by group
      _ = g * (d₀⁻¹ * d) := by rw [e3]
  have h1 : Nat.card D = (D : Set G).ncard := (Nat.card_coe_set_eq _)
  have h2 : Nat.card H = (H : Set G).ncard := (Nat.card_coe_set_eq _)
  rw [h1, h2]
  calc (D : Set G).ncard ≤ ((H : Set G) ∪ (fun h => d₀ * h) '' (H : Set G)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (H : Set G).ncard + ((fun h => d₀ * h) '' (H : Set G)).ncard :=
        Set.ncard_union_le _ _
    _ = 2 * (H : Set G).ncard := by
        rw [Set.ncard_image_of_injective _ (mul_right_injective d₀)]
        ring

theorem exists_eq_sup_of_eight [Finite G] {A : Subgroup G} (hA : IsEightGroup A) {a : G}
    (haA : a ∈ A) (ha1 : a ≠ 1) : ∃ a₁ ∈ A, ∃ a₂ ∈ A, A = zpowers a ⊔ zpowers a₁ ⊔ zpowers a₂ := by
  have ha2 : a * a = 1 := hA.1.2 a haA
  have hz2 : Nat.card (zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have hnot1 : ¬ A ≤ zpowers a := fun h => by
    have := card_le_of_le h
    rw [hA.2, hz2] at this
    omega
  obtain ⟨a₁, ha₁A, ha₁⟩ := Set.not_subset.mp hnot1
  obtain ⟨hV, hVc⟩ := isElemTwo_sup_zpowers (isElemTwo_zpowers ha2) (hA.1.2 a₁ ha₁A) ha₁
    fun e he => hA.1.1 e ((zpowers_le.mpr haA) he) a₁ ha₁A
  have hVA : zpowers a ⊔ zpowers a₁ ≤ A := sup_le (zpowers_le.mpr haA) (zpowers_le.mpr ha₁A)
  have hnot2 : ¬ A ≤ zpowers a ⊔ zpowers a₁ := fun h => by
    have := card_le_of_le h
    rw [hA.2, hVc, hz2] at this
    omega
  obtain ⟨a₂, ha₂A, ha₂⟩ := Set.not_subset.mp hnot2
  obtain ⟨-, hWc⟩ := isElemTwo_sup_zpowers hV (hA.1.2 a₂ ha₂A) ha₂
    fun e he => hA.1.1 e (hVA he) a₂ ha₂A
  refine ⟨a₁, ha₁A, a₂, ha₂A, (eq_of_le_of_card_ge (sup_le hVA (zpowers_le.mpr ha₂A)) ?_).symm⟩
  rw [hA.2, hWc, hVc, hz2]

theorem commute_zpowers_right {x y : G} (h : x * y = y * x) :
    ∀ w ∈ zpowers y, x * w = w * x := by
  intro w hw
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  exact (Commute.zpow_right (show Commute x y from h) k).eq

theorem commute_sup_zpowers {x y : G} {H : Subgroup G} (hH : ∀ w ∈ H, x * w = w * x)
    (hy : x * y = y * x) : ∀ w ∈ H ⊔ zpowers y, x * w = w * x := by
  have h1 : H ⊔ zpowers y ≤ centralizer ({x} : Set G) := sup_le
    (fun w hw => mem_centralizer_singleton_iff.mpr (hH w hw).symm)
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hy.symm))
  exact fun w hw => (mem_centralizer_singleton_iff.mp (h1 hw)).symm

theorem commutatorElement_mul_of_commute_left_right {e u q : G} (h1 : Commute e q)
    (h2 : Commute u q) : e⁻¹ * (u * q)⁻¹ * e * (u * q) = e⁻¹ * u⁻¹ * e * u := by
  have cx : Commute (e⁻¹ * u⁻¹ * e * u) q :=
    (((h1.inv_left).mul_left h2.inv_left).mul_left h1).mul_left h2
  have c3 : e⁻¹ * q⁻¹ = q⁻¹ * e⁻¹ := (h1.inv_inv).eq
  calc e⁻¹ * (u * q)⁻¹ * e * (u * q) = e⁻¹ * q⁻¹ * (u⁻¹ * e * u) * q := by group
    _ = q⁻¹ * e⁻¹ * (u⁻¹ * e * u) * q := by rw [c3]
    _ = q⁻¹ * ((e⁻¹ * u⁻¹ * e * u) * q) := by group
    _ = q⁻¹ * (q * (e⁻¹ * u⁻¹ * e * u)) := by rw [cx.eq]
    _ = e⁻¹ * u⁻¹ * e * u := by group

theorem card_sup_zpowers_eq_four [Finite G] {u v : G} (hu : u * u = 1) (hv : v * v = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hc : u * v = v * u) :
    Nat.card ↥(zpowers u ⊔ zpowers v) = 4 := by
  have hvu : v ∉ zpowers u := fun hm => by
    rcases eq_one_or_eq_of_mem_zpowers hu hm with h | h
    · exact hv1 h
    · exact huv h.symm
  obtain ⟨-, hc'⟩ := isElemTwo_sup_zpowers (isElemTwo_zpowers hu) hv hvu fun e he => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute u v from hc) i).eq
  rw [hc', Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hu) hu1]

theorem card_inf_le_four [Finite G] {B P : Subgroup G} (hB : Nat.card B = 8) (hBP : ¬ B ≤ P) :
    Nat.card ↥(B ⊓ P) ≤ 4 := by
  have hdvd : Nat.card ↥(B ⊓ P) ∣ 8 := hB ▸ card_dvd_of_le inf_le_left
  have hne : Nat.card ↥(B ⊓ P) ≠ 8 := fun h => hBP (by
    have := eq_of_le_of_card_ge (inf_le_left : B ⊓ P ≤ B) (by rw [h, hB])
    rw [← this]
    exact inf_le_right)
  have h8 : Nat.card ↥(B ⊓ P) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card ↥(B ⊓ P) <;> omega

structure Conn47Data (P Q Z A₀ : Subgroup G) (a z : G) : Prop where
  comm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p
  inf_eq : P ⊓ Q = Z
  z_mem : z ∈ Z
  z_sq : z * z = a
  a_sq : a * a = 1
  a_ne : a ≠ 1
  inv_Z : ∀ w ∈ Z, w * w = 1 → w = 1 ∨ w = a
  card_Z : Nat.card Z = 4
  A_le : A₀ ≤ P
  A_eight : IsEightGroup A₀
  a_mem_A : a ∈ A₀
  A_comm : ∀ c ∈ A₀, ∀ p ∈ P, c⁻¹ * p⁻¹ * c * p ∈ zpowers a
  sq_P : ∀ u ∈ P, u * u ∈ Z → u * u * (u * u) = 1
  E_fact : ∀ X : Subgroup G, X ≤ P → (∀ u ∈ X, ∀ v ∈ X, u⁻¹ * v⁻¹ * u * v ∈ Z) →
    (∀ u ∈ X, u * u ∈ Z) → ∃ E : Subgroup G, E ≤ P ∧ A₀ ≤ E ∧ Z ≤ E ∧ X ≤ E ∧
      Nat.card E = 64 ∧ (∀ u ∈ E, ∀ v ∈ E, u⁻¹ * v⁻¹ * u * v ∈ zpowers a) ∧
      ∀ u ∈ E, u * u ∈ zpowers a

namespace Conn47Data

variable {P Q Z A₀ : Subgroup G} {a z : G}

theorem Z_le_P (h : Conn47Data P Q Z A₀ a z) : Z ≤ P := h.inf_eq ▸ inf_le_left

theorem Z_le_Q (h : Conn47Data P Q Z A₀ a z) : Z ≤ Q := h.inf_eq ▸ inf_le_right

theorem a_mem_Z (h : Conn47Data P Q Z A₀ a z) : a ∈ Z := h.z_sq ▸ mul_mem h.z_mem h.z_mem

theorem zpowers_a_le (h : Conn47Data P Q Z A₀ a z) : zpowers a ≤ Z :=
  zpowers_le.mpr h.a_mem_Z

theorem central (h : Conn47Data P Q Z A₀ a z) {w : G} (hw : w ∈ Z) {y : G} (hy : y ∈ P ⊔ Q) :
    w * y = y * w := by
  have h1 : P ⊔ Q ≤ centralizer ({w} : Set G) := sup_le
    (fun p hp => mem_centralizer_singleton_iff.mpr (h.comm p hp w (h.Z_le_Q hw)))
    (fun q hq => mem_centralizer_singleton_iff.mpr (h.comm w (h.Z_le_P hw) q hq).symm)
  exact (mem_centralizer_singleton_iff.mp (h1 hy)).symm

theorem exists_mul (h : Conn47Data P Q Z A₀ a z) {y : G} (hy : y ∈ P ⊔ Q) :
    ∃ u ∈ P, ∃ v ∈ Q, y = u * v := by
  have hPN : P ≤ normalizer (Q : Set G) := fun p hp =>
    mem_normalizer_of_forall_commute fun q hq => h.comm p hp q hq
  have hy' : y ∈ (P : Set G) * (Q : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right P Q hPN]
    exact hy
  obtain ⟨u, hu, v, hv, huv⟩ := hy'
  exact ⟨u, hu, v, hv, huv.symm⟩

theorem comm_A (h : Conn47Data P Q Z A₀ a z) {c : G} (hc : c ∈ A₀) {y : G} (hy : y ∈ P ⊔ Q) :
    c⁻¹ * y⁻¹ * c * y ∈ zpowers a := by
  obtain ⟨u, hu, v, hv, rfl⟩ := h.exists_mul hy
  have hcP : c ∈ P := h.A_le hc
  have hw : c⁻¹ * u⁻¹ * c * u ∈ P :=
    mul_mem (mul_mem (mul_mem (inv_mem hcP) (inv_mem hu)) hcP) hu
  have e2 := h.comm c hcP v hv
  have hv' : ∀ p ∈ P, v⁻¹ * p * v = p := fun p hp => by
    have := h.comm p hp v hv
    calc v⁻¹ * p * v = v⁻¹ * (p * v) := by group
      _ = v⁻¹ * (v * p) := by rw [this]
      _ = p := by group
  have e2' : c⁻¹ * v⁻¹ = v⁻¹ * c⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, e2]
  have key : c⁻¹ * (u * v)⁻¹ * c * (u * v) = c⁻¹ * u⁻¹ * c * u := by
    calc c⁻¹ * (u * v)⁻¹ * c * (u * v) = (c⁻¹ * v⁻¹) * u⁻¹ * c * u * v := by group
      _ = (v⁻¹ * c⁻¹) * u⁻¹ * c * u * v := by rw [e2']
      _ = v⁻¹ * (c⁻¹ * u⁻¹ * c * u) * v := by group
      _ = c⁻¹ * u⁻¹ * c * u := hv' _ hw
  rw [key]
  exact h.A_comm c hc u hu

theorem connectedIn_of_commute [Finite G] {S B C : Subgroup G} (hBS : B ≤ S) (hCS : C ≤ S)
    (hB : IsEightGroup B) (hC : IsEightGroup C) (hBC : ∀ u ∈ B, ∀ v ∈ C, u * v = v * u) :
    AbelianConnectedIn S 3 B C :=
  ⟨hBS, hB.1.isAbelianTwoOfRank (by rw [hB.2]), Relation.ReflTransGen.single
    ⟨hCS, hC.1.isAbelianTwoOfRank (by rw [hC.2]), hBC⟩⟩

theorem connected_of_centralizing [Finite G] (h : Conn47Data P Q Z A₀ a z) {B : Subgroup G}
    (hBS : B ≤ P ⊔ Q) (hB : IsEightGroup B) (haB : a ∈ B) (hBP : ¬ B ≤ P)
    {c : G} (hcB : c ∈ B) (hca : c ∉ zpowers a) (hcA : ∀ d ∈ A₀, c * d = d * c) :
    AbelianConnectedIn (P ⊔ Q) 3 B A₀ := by
  have hAS : A₀ ≤ P ⊔ Q := h.A_le.trans le_sup_left
  set B₁ : Subgroup G := B ⊓ centralizer (A₀ : Set G) with hB₁
  by_cases hBc : B ≤ centralizer (A₀ : Set G)
  · exact connectedIn_of_commute hBS hAS hB h.A_eight fun u hu v hv =>
      ((mem_centralizer_iff.mp (hBc hu)) v hv).symm
  have ha1 : a ∈ B₁ := mem_inf.mpr ⟨haB, mem_centralizer_iff.mpr fun d hd =>
    (h.central h.a_mem_Z (hAS hd)).symm⟩
  have hc1 : c ∈ B₁ := mem_inf.mpr ⟨hcB, mem_centralizer_iff.mpr fun d hd => (hcA d hd).symm⟩
  have ha_ne : a ≠ c := fun hac => hca (hac ▸ mem_zpowers a)
  have hB₁4 : 4 ≤ Nat.card B₁ := by
    have := card_sup_zpowers_eq_four (hB.1.2 a haB) (hB.1.2 c hcB) h.a_ne
      (fun h1 => hca (h1 ▸ one_mem _)) ha_ne (hB.1.1 a haB c hcB)
    rw [← this]
    exact card_le_of_le (sup_le (zpowers_le.mpr ha1) (zpowers_le.mpr hc1))
  have hB₁ne : B₁ ≠ B := fun heq => hBc (heq ▸ inf_le_right)
  obtain ⟨b₀, hb₀B, hb₀B₁⟩ : ∃ b₀ ∈ B, b₀ ∉ B₁ := by
    by_contra hno
    push Not at hno
    exact hB₁ne (le_antisymm inf_le_left fun x hx => hno x hx)
  have hB₁8 : Nat.card B₁ = 4 := by
    have hdvd : Nat.card B₁ ∣ 8 := hB.2 ▸ card_dvd_of_le inf_le_left
    have hlt : Nat.card B₁ ≠ 8 := fun h8 => hB₁ne (eq_of_le_of_card_ge inf_le_left (by
      rw [h8, hB.2]))
    have hle : Nat.card B₁ ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hk : Nat.card B₁ <;> omega
  have hBeq : B = B₁ ⊔ zpowers b₀ := by
    obtain ⟨-, hc⟩ := isElemTwo_sup_zpowers (hB.1.mono inf_le_left) (hB.1.2 b₀ hb₀B) hb₀B₁
      fun e he => hB.1.1 e (mem_inf.mp he).1 b₀ hb₀B
    exact (eq_of_le_of_card_ge (sup_le inf_le_left (zpowers_le.mpr hb₀B))
      (by rw [hc, hB₁8, hB.2])).symm
  set A₁ : Subgroup G := A₀ ⊓ centralizer (B : Set G) with hA₁
  have hA₁eq : A₀ ⊓ centralizer ({b₀} : Set G) ≤ A₁ := by
    intro d hd
    refine mem_inf.mpr ⟨(mem_inf.mp hd).1, ?_⟩
    rw [mem_centralizer_iff]
    intro w hw
    rw [hBeq] at hw
    have hdb : d * b₀ = b₀ * d := mem_centralizer_singleton_iff.mp (mem_inf.mp hd).2
    have hdB₁ : ∀ e ∈ B₁, d * e = e * d := fun e he =>
      ((mem_centralizer_iff.mp (mem_inf.mp he).2) d (mem_inf.mp hd).1)
    exact (commute_sup_zpowers hdB₁ hdb w hw).symm
  have hA₁4 : 4 ≤ Nat.card A₁ := by
    have h2 := card_le_two_mul_card_inf_centralizer (D := A₀) (g := b₀) (a := a)
      (fun d hd => h.central h.a_mem_Z (hAS hd)) (fun d hd => by
        have := h.comm_A hd (hBS hb₀B)
        exact eq_one_or_eq_of_mem_zpowers h.a_sq this)
    rw [h.A_eight.2] at h2
    exact (by omega : 4 ≤ Nat.card ↥(A₀ ⊓ centralizer ({b₀} : Set G))).trans (card_le_of_le hA₁eq)
  have hA₁B₁ : IsElemTwo (A₁ ⊔ B₁) := (h.A_eight.1.mono inf_le_left).sup
    (hB.1.mono inf_le_left) fun u hu v hv =>
      ((mem_centralizer_iff.mp (mem_inf.mp hu).2) v (mem_inf.mp hv).1).symm
  have hXS : A₁ ⊔ B₁ ≤ P ⊔ Q := sup_le (inf_le_left.trans hAS) (inf_le_left.trans hBS)
  by_cases h8 : 8 ≤ Nat.card ↥(A₁ ⊔ B₁)
  ·
    have hXr : IsAbelianTwoOfRank 3 (A₁ ⊔ B₁) := hA₁B₁.isAbelianTwoOfRank h8
    refine ⟨hBS, hB.1.isAbelianTwoOfRank (by rw [hB.2]), ?_⟩
    refine (Relation.ReflTransGen.single ⟨hXS, hXr, ?_⟩).tail
      ⟨hAS, h.A_eight.1.isAbelianTwoOfRank (by rw [h.A_eight.2]), ?_⟩
    · intro u hu v hv
      have h1 : A₁ ⊔ B₁ ≤ centralizer ({v} : Set G) := sup_le
        (fun w hw => mem_centralizer_singleton_iff.mpr
          (h.A_eight.1.1 w (mem_inf.mp hw).1 v hv))
        (fun w hw => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (mem_inf.mp hw).2) v hv).symm)
      exact mem_centralizer_singleton_iff.mp (h1 hu)
    · intro u hu v hv
      have h1 : A₁ ⊔ B₁ ≤ centralizer ({u} : Set G) := sup_le
        (fun w hw => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (mem_inf.mp hw).2) u hu).symm)
        (fun w hw => mem_centralizer_singleton_iff.mpr (hB.1.1 w (mem_inf.mp hw).1 u hu))
      exact (mem_centralizer_singleton_iff.mp (h1 hv)).symm
  have hA₁B₁4 : Nat.card ↥(A₁ ⊔ B₁) ≤ 4 := by
    obtain ⟨k, hk⟩ := hA₁B₁.isPGroup.exists_card_eq
    rw [hk] at h8 ⊢
    rcases k with _ | _ | _ | k
    · norm_num
    · norm_num
    · norm_num
    · exact absurd (by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)) h8
  have hB₁A₁ : B₁ ≤ A₁ := by
    have hle : B₁ ≤ A₁ ⊔ B₁ := le_sup_right
    have heq : A₁ = A₁ ⊔ B₁ := eq_of_le_of_card_ge le_sup_left (by omega)
    rw [heq]
    exact hle
  have hB₁P : B₁ ≤ P := hB₁A₁.trans (inf_le_left.trans h.A_le)
  obtain ⟨b, hbB, hbP⟩ := Set.not_subset.mp hBP
  have hbB₁ : b ∉ B₁ := fun hb => hbP (hB₁P hb)
  obtain ⟨u, hu, v, hv, rfl⟩ := h.exists_mul (hBS hbB)
  have huv := h.comm u hu v hv
  have hb2 : u * v * (u * v) = 1 := hB.1.2 _ hbB
  have hu2 : u * u = (v * v)⁻¹ := by
    have h1 : u * v * (u * v) = u * u * (v * v) := by
      calc u * v * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [huv]
        _ = u * u * (v * v) := by group
    rw [h1] at hb2
    exact eq_inv_of_mul_eq_one_left hb2
  have huuZ : u * u ∈ Z := by
    rw [← h.inf_eq]
    refine mem_inf.mpr ⟨mul_mem hu hu, ?_⟩
    rw [hu2]
    exact inv_mem (mul_mem hv hv)
  have hu4 := h.sq_P u hu huuZ
  have hvvZ : v * v ∈ Z := by
    have : (u * u)⁻¹ = v * v := by rw [hu2, inv_inv]
    rw [← this]
    exact inv_mem huuZ
  have hvv2 : v * v * (v * v) = 1 := by
    have : (u * u * (u * u))⁻¹ = v * v * (v * v) := by
      rw [mul_inv_rev, hu2, inv_inv]
    rw [← this, hu4, inv_one]
  obtain ⟨v₁, hv₁Q, hv₁2, hv₁v⟩ : ∃ v₁ ∈ Q, v₁ * v₁ = 1 ∧ v₁ * v⁻¹ ∈ Z := by
    rcases h.inv_Z _ hvvZ hvv2 with h1 | h1
    · exact ⟨v, hv, h1, by rw [mul_inv_cancel]; exact one_mem _⟩
    · refine ⟨z * v, mul_mem (h.Z_le_Q h.z_mem) hv, ?_, by
        rw [mul_inv_cancel_right]; exact h.z_mem⟩
      have hzv := h.comm z (h.Z_le_P h.z_mem) v hv
      calc z * v * (z * v) = z * z * (v * v) := by
            calc z * v * (z * v) = z * (v * z) * v := by group
              _ = z * (z * v) * v := by rw [← hzv]
              _ = z * z * (v * v) := by group
        _ = 1 := by rw [h.z_sq, h1, h.a_sq]
  have hv₁P : v₁ ∉ P := fun hv₁ => hbP (by
    have hvP : v ∈ P := by
      have := mul_mem (inv_mem (h.Z_le_P hv₁v)) hv₁
      rwa [show (v₁ * v⁻¹)⁻¹ * v₁ = v by group] at this
    exact mul_mem hu hvP)
  have hA₁P : A₁ ≤ P := inf_le_left.trans h.A_le
  obtain ⟨hXe, hXc⟩ := isElemTwo_sup_zpowers (h.A_eight.1.mono inf_le_left) hv₁2
    (fun hv₁ => hv₁P (hA₁P hv₁)) fun e he => h.comm e (hA₁P he) v₁ hv₁Q
  have hA₁4' : Nat.card A₁ = 4 := le_antisymm
    ((card_le_of_le (le_sup_left : A₁ ≤ A₁ ⊔ B₁)).trans hA₁B₁4) hA₁4
  have hX8 : IsEightGroup (A₁ ⊔ zpowers v₁) := ⟨hXe, by rw [hXc, hA₁4']⟩
  have hXS' : A₁ ⊔ zpowers v₁ ≤ P ⊔ Q :=
    sup_le (hA₁P.trans le_sup_left) (zpowers_le.mpr (mem_sup_right hv₁Q))
  have hv₁u : v₁ * u = u * v₁ := (h.comm u hu v₁ hv₁Q).symm
  have hv₁v' : v₁ * v = v * v₁ := by
    have hc := h.central hv₁v (mem_sup_right hv)
    calc v₁ * v = (v₁ * v⁻¹) * v * v := by group
      _ = v * (v₁ * v⁻¹) * v := by rw [hc]
      _ = v * v₁ := by group
  have hv₁b : v₁ * (u * v) = u * v * v₁ := by
    rw [← mul_assoc, hv₁u, mul_assoc, hv₁v', ← mul_assoc]
  have hBeq' : B = B₁ ⊔ zpowers (u * v) := by
    obtain ⟨-, hc⟩ := isElemTwo_sup_zpowers (hB.1.mono inf_le_left) (hB.1.2 _ hbB) hbB₁
      fun e he => hB.1.1 e (mem_inf.mp he).1 _ hbB
    exact (eq_of_le_of_card_ge (sup_le inf_le_left (zpowers_le.mpr hbB))
      (by rw [hc, hB₁8, hB.2])).symm
  have hv₁B : ∀ w ∈ B, v₁ * w = w * v₁ := by
    intro w hw
    rw [hBeq'] at hw
    have hB₁v : ∀ e ∈ B₁, v₁ * e = e * v₁ := fun e he =>
      (h.comm e (hB₁P he) v₁ hv₁Q).symm
    exact commute_sup_zpowers hB₁v hv₁b w hw
  refine ⟨hBS, hB.1.isAbelianTwoOfRank (by rw [hB.2]), ?_⟩
  refine (Relation.ReflTransGen.single ⟨hXS', hX8.1.isAbelianTwoOfRank (by rw [hX8.2]), ?_⟩).tail
    ⟨hAS, h.A_eight.1.isAbelianTwoOfRank (by rw [h.A_eight.2]), ?_⟩
  · intro w hw d hd
    have hdA₁ : ∀ e ∈ A₁, d * e = e * d := fun e he =>
      h.A_eight.1.1 d hd e (mem_inf.mp he).1
    exact (commute_sup_zpowers hdA₁ (h.comm d (h.A_le hd) v₁ hv₁Q) w hw).symm
  · intro x hx w hw
    have hxA₁ : ∀ e ∈ A₁, x * e = e * x := fun e he =>
      (mem_centralizer_iff.mp (mem_inf.mp he).2) x hx
    exact commute_sup_zpowers hxA₁ (hv₁B x hx).symm w hw

theorem pPart_of_le_sup (h : Conn47Data P Q Z A₀ a z) {B : Subgroup G} (hBS : B ≤ P ⊔ Q)
    (hB : IsElemTwo B) :
    (∀ u ∈ P ⊓ (B ⊔ Q), ∀ v ∈ P ⊓ (B ⊔ Q), u⁻¹ * v⁻¹ * u * v ∈ Z) ∧
      (∀ u ∈ P ⊓ (B ⊔ Q), u * u ∈ Z) ∧ ∀ b ∈ B, ∃ u ∈ P ⊓ (B ⊔ Q), ∃ q ∈ Q, b = u * q := by
  have hBN : B ≤ normalizer (Q : Set G) := fun b hb => by
    obtain ⟨u, hu, v, hv, rfl⟩ := h.exists_mul (hBS hb)
    exact mul_mem (mem_normalizer_of_forall_commute fun q hq => h.comm u hu q hq)
      (le_normalizer hv)
  have hdec : ∀ u ∈ B ⊔ Q, ∃ b ∈ B, ∃ q ∈ Q, u = b * q := by
    intro u hu
    have hu' : u ∈ (B : Set G) * (Q : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right B Q hBN]
      exact hu
    obtain ⟨b, hb, q, hq, huq⟩ := hu'
    exact ⟨b, hb, q, hq, huq.symm⟩
  refine ⟨fun u hu v hv => ?_, fun u hu => ?_, fun b hb => ?_⟩
  · obtain ⟨huP, huBQ⟩ := mem_inf.mp hu
    obtain ⟨hvP, hvBQ⟩ := mem_inf.mp hv
    obtain ⟨b, hb, q, hq, rfl⟩ := hdec u huBQ
    obtain ⟨b', hb', q', hq', rfl⟩ := hdec v hvBQ
    have hbb := hB.1 b hb b' hb'
    rw [← h.inf_eq]
    refine mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem (inv_mem huP) (inv_mem hvP)) huP) hvP, ?_⟩
    have hxq' : b * q * q'⁻¹ = q'⁻¹ * (b * q) := h.comm _ huP q'⁻¹ (inv_mem hq')
    have hyq : b' * q' * q⁻¹ = q⁻¹ * (b' * q') := h.comm _ hvP q⁻¹ (inv_mem hq)
    have e : b * q * (b' * q') * (q⁻¹ * q'⁻¹) = b' * q' * (b * q) * (q'⁻¹ * q⁻¹) := by
      calc b * q * (b' * q') * (q⁻¹ * q'⁻¹) = b * q * (b' * q' * q⁻¹) * q'⁻¹ := by group
        _ = b * q * (q⁻¹ * (b' * q')) * q'⁻¹ := by rw [hyq]
        _ = b * b' := by group
        _ = b' * b := hbb
        _ = b' * q' * (q'⁻¹ * (b * q)) * q⁻¹ := by group
        _ = b' * q' * (b * q * q'⁻¹) * q⁻¹ := by rw [hxq']
        _ = b' * q' * (b * q) * (q'⁻¹ * q⁻¹) := by group
    have e' : b * q * (b' * q') = b' * q' * (b * q) * (q'⁻¹ * q⁻¹) * (q⁻¹ * q'⁻¹)⁻¹ := by
      rw [← e]; group
    have key : (b * q)⁻¹ * (b' * q')⁻¹ * (b * q) * (b' * q') = q'⁻¹ * q⁻¹ * q' * q := by
      calc (b * q)⁻¹ * (b' * q')⁻¹ * (b * q) * (b' * q') =
            (b' * q' * (b * q))⁻¹ * (b * q * (b' * q')) := by group
        _ = (b' * q' * (b * q))⁻¹ *
            (b' * q' * (b * q) * (q'⁻¹ * q⁻¹) * (q⁻¹ * q'⁻¹)⁻¹) := by rw [← e']
        _ = q'⁻¹ * q⁻¹ * q' * q := by group
    rw [key]
    exact mul_mem (mul_mem (mul_mem (inv_mem hq') (inv_mem hq)) hq') hq
  · obtain ⟨huP, huBQ⟩ := mem_inf.mp hu
    obtain ⟨b, hb, q, hq, rfl⟩ := hdec u huBQ
    rw [← h.inf_eq]
    refine mem_inf.mpr ⟨mul_mem huP huP, ?_⟩
    have hb2 := hB.2 b hb
    have hcq : b * q * q⁻¹ = q⁻¹ * (b * q) := h.comm _ huP q⁻¹ (inv_mem hq)
    have this : (b * q) * (b * q) = q * q := by
      have h1 : (b * q) * (b * q) * (q⁻¹ * q⁻¹) = 1 := by
        calc (b * q) * (b * q) * (q⁻¹ * q⁻¹) = (b * q) * ((b * q) * q⁻¹) * q⁻¹ := by group
          _ = (b * q) * (q⁻¹ * (b * q)) * q⁻¹ := by rw [hcq]
          _ = b * b := by group
          _ = 1 := hb2
      calc (b * q) * (b * q) = (b * q) * (b * q) * (q⁻¹ * q⁻¹) * (q * q) := by group
        _ = q * q := by rw [h1, one_mul]
    rw [this]
    exact mul_mem hq hq
  · obtain ⟨u, hu, q, hq, rfl⟩ := h.exists_mul (hBS hb)
    refine ⟨u, mem_inf.mpr ⟨hu, ?_⟩, q, hq, rfl⟩
    have := mul_mem (mem_sup_left hb : u * q ∈ B ⊔ Q) (mem_sup_right (inv_mem hq))
    rwa [mul_inv_cancel_right] at this

theorem exists_centralizing_involution [Finite G] (h : Conn47Data P Q Z A₀ a z)
    {B : Subgroup G} (hBS : B ≤ P ⊔ Q) (hB : IsEightGroup B) (haB : a ∈ B) (hBP : ¬ B ≤ P) :
    ∃ c ∈ P ⊔ Q, c ∉ Z ∧ c * c = 1 ∧ (∀ d ∈ A₀, c * d = d * c) ∧ ∀ d ∈ B, c * d = d * c := by
  classical
  obtain ⟨hXc, hXs, hdec⟩ := h.pPart_of_le_sup hBS hB.1
  set X : Subgroup G := P ⊓ (B ⊔ Q) with hXdef
  obtain ⟨E, hEP, hA₀E, hZE, hXE, hE64, hEc, hEs⟩ := h.E_fact X inf_le_left hXc hXs
  have hES : E ≤ P ⊔ Q := hEP.trans le_sup_left
  have hEB : ∀ e ∈ E, ∀ b ∈ B, e⁻¹ * b⁻¹ * e * b ∈ zpowers a := by
    intro e he b hb
    obtain ⟨u, hu, q, hq, rfl⟩ := hdec b hb
    have h1 : Commute e q := h.comm e (hEP he) q hq
    have h2 : Commute u q := h.comm u (hEP (hXE hu)) q hq
    have key := commutatorElement_mul_of_commute_left_right h1 h2
    rw [key]
    exact hEc e he u (hXE hu)
  have hBN : B ≤ normalizer (E : Set G) := fun b hb => by
    obtain ⟨u, hu, q, hq, rfl⟩ := hdec b hb
    refine mul_mem (le_normalizer (hXE hu)) ?_
    exact mem_normalizer_of_forall_commute fun e he => (h.comm e (hEP he) q hq).symm
  set D : Subgroup G := B ⊔ E with hDdef
  have hDS : D ≤ P ⊔ Q := sup_le hBS hES
  have hcard := card_sup_mul_inf_eq_mul_of_normalizes hBN
  have hBE : Nat.card ↥(B ⊓ E) ≤ 4 :=
    (card_le_of_le (inf_le_inf_left B hEP)).trans (card_inf_le_four hB.2 hBP)
  have hD128 : 128 ≤ Nat.card D := by
    rw [hB.2, hE64] at hcard
    have hpos : 0 < Nat.card ↥(B ⊓ E) := Nat.card_pos
    nlinarith
  obtain ⟨c₁, hc₁, c₂, hc₂, hA₀eq⟩ := exists_eq_sup_of_eight h.A_eight h.a_mem_A h.a_ne
  obtain ⟨b₁, hb₁, b₂, hb₂, hBeq⟩ := exists_eq_sup_of_eight hB haB h.a_ne
  have hDdec : ∀ d ∈ D, ∃ b ∈ B, ∃ e ∈ E, d = b * e := by
    intro d hd
    have hd' : d ∈ (B : Set G) * (E : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right B E hBN]
      exact hd
    obtain ⟨b, hb, e, he, hbe⟩ := hd'
    exact ⟨b, hb, e, he, hbe.symm⟩
  have hcA : ∀ g ∈ A₀, ∀ d ∈ D, d⁻¹ * g⁻¹ * d * g = 1 ∨ d⁻¹ * g⁻¹ * d * g = a := by
    intro g hg d hd
    have h1 := h.comm_A hg (hDS hd)
    have h2 : d⁻¹ * g⁻¹ * d * g = (g⁻¹ * d⁻¹ * g * d)⁻¹ := by group
    rw [h2]
    exact eq_one_or_eq_of_mem_zpowers h.a_sq (inv_mem h1)
  have hcB : ∀ g ∈ B, ∀ d ∈ D, d⁻¹ * g⁻¹ * d * g = 1 ∨ d⁻¹ * g⁻¹ * d * g = a := by
    intro g hg d hd
    obtain ⟨b, hb, e, he, rfl⟩ := hDdec d hd
    have hbg := hB.1.1 b hb g hg
    have key : (b * e)⁻¹ * g⁻¹ * (b * e) * g = e⁻¹ * g⁻¹ * e * g := by
      have hbg' : g⁻¹ * b = b * g⁻¹ := ((show Commute b g from hbg).inv_right).eq.symm
      calc (b * e)⁻¹ * g⁻¹ * (b * e) * g = e⁻¹ * b⁻¹ * (g⁻¹ * b) * e * g := by group
        _ = e⁻¹ * b⁻¹ * (b * g⁻¹) * e * g := by rw [hbg']
        _ = e⁻¹ * g⁻¹ * e * g := by group
    rw [key]
    exact eq_one_or_eq_of_mem_zpowers h.a_sq (hEB e he g hg)
  have hacen : ∀ d ∈ D, a * d = d * a := fun d hd => h.central h.a_mem_Z (hDS hd)
  set D₁ : Subgroup G := D ⊓ centralizer ({c₁} : Set G) with hD₁
  set D₂ : Subgroup G := D₁ ⊓ centralizer ({c₂} : Set G) with hD₂
  set D₃ : Subgroup G := D₂ ⊓ centralizer ({b₁} : Set G) with hD₃
  set D₄ : Subgroup G := D₃ ⊓ centralizer ({b₂} : Set G) with hD₄
  have hD₁D : D₁ ≤ D := inf_le_left
  have hD₂D : D₂ ≤ D := inf_le_left.trans hD₁D
  have hD₃D : D₃ ≤ D := inf_le_left.trans hD₂D
  have k1 : Nat.card D ≤ 2 * Nat.card D₁ :=
    card_le_two_mul_card_inf_centralizer (D := D) (g := c₁) hacen
    (fun d hd => hcA c₁ hc₁ d hd)
  have k2 : Nat.card D₁ ≤ 2 * Nat.card D₂ :=
    card_le_two_mul_card_inf_centralizer (D := D₁) (g := c₂)
    (fun d hd => hacen d (hD₁D hd)) (fun d hd => hcA c₂ hc₂ d (hD₁D hd))
  have k3 : Nat.card D₂ ≤ 2 * Nat.card D₃ :=
    card_le_two_mul_card_inf_centralizer (D := D₂) (g := b₁)
    (fun d hd => hacen d (hD₂D hd)) (fun d hd => hcB b₁ hb₁ d (hD₂D hd))
  have k4 : Nat.card D₃ ≤ 2 * Nat.card D₄ :=
    card_le_two_mul_card_inf_centralizer (D := D₃) (g := b₂)
    (fun d hd => hacen d (hD₃D hd)) (fun d hd => hcB b₂ hb₂ d (hD₃D hd))
  have hD₄8 : 8 ≤ Nat.card D₄ := by omega
  have hnot : ¬ D₄ ≤ Z := fun hle => by
    have := card_le_of_le hle
    rw [h.card_Z] at this
    omega
  obtain ⟨c, hcD₄, hcZ⟩ := Set.not_subset.mp hnot
  have hcD : c ∈ D := (inf_le_left.trans hD₃D) hcD₄
  have hcc₁ : c * c₁ = c₁ * c :=
    mem_centralizer_singleton_iff.mp (mem_inf.mp (inf_le_left.trans (inf_le_left.trans
      (inf_le_left : D₂ ≤ D₁)) hcD₄)).2
  have hcc₂ : c * c₂ = c₂ * c :=
    mem_centralizer_singleton_iff.mp (mem_inf.mp (inf_le_left.trans
      (inf_le_left : D₃ ≤ D₂) hcD₄)).2
  have hcb₁ : c * b₁ = b₁ * c :=
    mem_centralizer_singleton_iff.mp (mem_inf.mp ((inf_le_left : D₄ ≤ D₃) hcD₄)).2
  have hcb₂ : c * b₂ = b₂ * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hcD₄).2
  have hca : c * a = a * c := (hacen c hcD).symm
  have hcenA : ∀ x : G, x * a = a * x → x * c₁ = c₁ * x → x * c₂ = c₂ * x →
      ∀ d ∈ A₀, x * d = d * x := by
    intro x h0 h1 h2 d hd
    rw [hA₀eq] at hd
    have hx0 : ∀ w ∈ zpowers a, x * w = w * x := commute_zpowers_right h0
    have hx1 := commute_sup_zpowers hx0 h1
    exact commute_sup_zpowers hx1 h2 d hd
  have hcenB : ∀ x : G, x * a = a * x → x * b₁ = b₁ * x → x * b₂ = b₂ * x →
      ∀ d ∈ B, x * d = d * x := by
    intro x h0 h1 h2 d hd
    rw [hBeq] at hd
    have hx0 : ∀ w ∈ zpowers a, x * w = w * x := commute_zpowers_right h0
    have hx1 := commute_sup_zpowers hx0 h1
    exact commute_sup_zpowers hx1 h2 d hd
  have hc2 : c * c = 1 ∨ c * c = a := by
    obtain ⟨b, hb, e, he, rfl⟩ := hDdec c hcD
    have hb2 := hB.1.2 b hb
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have h1 := hEB e he b hb
    have he2 := hEs e he
    have hcomm : e⁻¹ * b⁻¹ * e * b ∈ zpowers a := h1
    have key : b * e * (b * e) = e * (e⁻¹ * b⁻¹ * e * b) * e := by
      rw [hbinv]; group
    have hwc : (e⁻¹ * b⁻¹ * e * b) * e = e * (e⁻¹ * b⁻¹ * e * b) :=
      h.central (h.zpowers_a_le hcomm) (hES he)
    rw [key, mul_assoc, hwc, ← mul_assoc]
    exact eq_one_or_eq_of_mem_zpowers h.a_sq (mul_mem he2 hcomm)
  rcases hc2 with hc2 | hc2
  · exact ⟨c, hDS hcD, hcZ, hc2, hcenA c hca hcc₁ hcc₂, hcenB c hca hcb₁ hcb₂⟩
  ·
    have hzS : z ∈ P ⊔ Q := mem_sup_left (h.Z_le_P h.z_mem)
    have hzc := fun y (hy : y ∈ P ⊔ Q) => h.central h.z_mem hy
    refine ⟨c * z, mul_mem (hDS hcD) hzS, fun hm => hcZ (by
      have := mul_mem hm (inv_mem h.z_mem)
      rwa [mul_inv_cancel_right] at this), ?_, ?_, ?_⟩
    · calc c * z * (c * z) = c * c * (z * z) := by
            calc c * z * (c * z) = c * (z * c) * z := by group
              _ = c * (c * z) * z := by rw [hzc c (hDS hcD)]
              _ = c * c * (z * z) := by group
        _ = 1 := by rw [hc2, h.z_sq, h.a_sq]
    · intro d hd
      have h1 := hcenA c hca hcc₁ hcc₂ d hd
      have h2 := hzc d (h.A_le hd |> mem_sup_left)
      calc c * z * d = c * (z * d) := by group
        _ = c * (d * z) := by rw [h2]
        _ = d * c * z := by rw [← mul_assoc, h1]
        _ = d * (c * z) := by group
    · intro d hd
      have h1 := hcenB c hca hcb₁ hcb₂ d hd
      have h2 := hzc d (hBS hd)
      calc c * z * d = c * (z * d) := by group
        _ = c * (d * z) := by rw [h2]
        _ = d * c * z := by rw [← mul_assoc, h1]
        _ = d * (c * z) := by group

theorem connectedIn_head [Finite G] {S B C A : Subgroup G} (hBS : B ≤ S) (hCS : C ≤ S)
    (hB : IsEightGroup B) (hC : IsEightGroup C) (hBC : ∀ u ∈ B, ∀ v ∈ C, u * v = v * u)
    (h : AbelianConnectedIn S 3 C A) : AbelianConnectedIn S 3 B A :=
  (connectedIn_of_commute hBS hCS hB hC hBC).trans h

theorem connected_of_not_le_of_mem [Finite G] (h : Conn47Data P Q Z A₀ a z) {B : Subgroup G}
    (hBS : B ≤ P ⊔ Q) (hB : IsEightGroup B) (haB : a ∈ B) (hBP : ¬ B ≤ P) :
    AbelianConnectedIn (P ⊔ Q) 3 B A₀ := by
  obtain ⟨c, hcS, hcZ, hc2, hcA, hcB⟩ := h.exists_centralizing_involution hBS hB haB hBP
  have hca : c ∉ zpowers a := fun hm => hcZ (h.zpowers_a_le hm)
  obtain ⟨b, hbB, hbP⟩ := Set.not_subset.mp hBP
  by_cases hcab : c ∈ zpowers a ⊔ zpowers b
  · have hcB' : c ∈ B := sup_le (zpowers_le.mpr haB) (zpowers_le.mpr hbB) hcab
    exact h.connected_of_centralizing hBS hB haB hBP hcB' hca hcA
  ·
    have hb1 : b ≠ 1 := fun h1 => hbP (h1 ▸ one_mem _)
    have hab : a ≠ b := fun h1 => hbP (h1 ▸ h.A_le h.a_mem_A)
    have hV4 := card_sup_zpowers_eq_four h.a_sq (hB.1.2 b hbB) h.a_ne hb1 hab
      (hB.1.1 a haB b hbB)
    have hVe : IsElemTwo (zpowers a ⊔ zpowers b) := hB.1.mono
      (sup_le (zpowers_le.mpr haB) (zpowers_le.mpr hbB))
    obtain ⟨hB₂e, hB₂c⟩ := isElemTwo_sup_zpowers hVe hc2 hcab fun e he =>
      (hcB e (sup_le (zpowers_le.mpr haB) (zpowers_le.mpr hbB) he)).symm
    have hB₂8 : IsEightGroup (zpowers a ⊔ zpowers b ⊔ zpowers c) := ⟨hB₂e, by rw [hB₂c, hV4]⟩
    have hB₂S : zpowers a ⊔ zpowers b ⊔ zpowers c ≤ P ⊔ Q := sup_le
      (sup_le (zpowers_le.mpr (hBS haB)) (zpowers_le.mpr (hBS hbB))) (zpowers_le.mpr hcS)
    have hB₂P : ¬ zpowers a ⊔ zpowers b ⊔ zpowers c ≤ P := fun hle =>
      hbP (hle (mem_sup_left (mem_sup_right (mem_zpowers b))))
    have haB₂ : a ∈ zpowers a ⊔ zpowers b ⊔ zpowers c :=
      mem_sup_left (mem_sup_left (mem_zpowers a))
    have hcB₂ : c ∈ zpowers a ⊔ zpowers b ⊔ zpowers c := mem_sup_right (mem_zpowers c)
    have h₂ := h.connected_of_centralizing hB₂S hB₂8 haB₂ hB₂P hcB₂ hca hcA
    refine connectedIn_head hBS hB₂S hB hB₂8 (fun u hu v hv => ?_) h₂
    have hu' : ∀ w ∈ zpowers a ⊔ zpowers b, u * w = w * u := fun w hw =>
      hB.1.1 u hu w (sup_le (zpowers_le.mpr haB) (zpowers_le.mpr hbB) hw)
    exact commute_sup_zpowers hu' (hcB u hu).symm v hv

theorem exists_four_le_eight [Finite G] {B : Subgroup G} (hB : IsEightGroup B) {x : G}
    (hxB : x ∈ B) (hx1 : x ≠ 1) :
    ∃ x' ∈ B, IsElemTwo (zpowers x ⊔ zpowers x') ∧ Nat.card ↥(zpowers x ⊔ zpowers x') = 4 := by
  have hx2 : x * x = 1 := hB.1.2 x hxB
  have hz2 : Nat.card (zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hnot : ¬ B ≤ zpowers x := fun hle => by
    have := card_le_of_le hle
    rw [hB.2, hz2] at this
    omega
  obtain ⟨x', hx'B, hx'⟩ := Set.not_subset.mp hnot
  have hx'1 : x' ≠ 1 := fun h1 => hx' (h1 ▸ one_mem _)
  have hxx' : x ≠ x' := fun h1 => hx' (h1 ▸ mem_zpowers x)
  exact ⟨x', hx'B, hB.1.mono (sup_le (zpowers_le.mpr hxB) (zpowers_le.mpr hx'B)),
    card_sup_zpowers_eq_four hx2 (hB.1.2 x' hx'B) hx1 hx'1 hxx' (hB.1.1 x hxB x' hx'B)⟩

theorem connected_of_not_le [Finite G] (h : Conn47Data P Q Z A₀ a z) {B : Subgroup G}
    (hBS : B ≤ P ⊔ Q) (hB : IsEightGroup B) (hBP : ¬ B ≤ P) :
    AbelianConnectedIn (P ⊔ Q) 3 B A₀ := by
  by_cases haB : a ∈ B
  · exact h.connected_of_not_le_of_mem hBS hB haB hBP
  obtain ⟨b, hbB, hbP⟩ := Set.not_subset.mp hBP
  have hb1 : b ≠ 1 := fun h1 => hbP (h1 ▸ one_mem _)
  obtain ⟨b', hb'B, hVe, hV4⟩ := exists_four_le_eight hB hbB hb1
  have hVB : zpowers b ⊔ zpowers b' ≤ B := sup_le (zpowers_le.mpr hbB) (zpowers_le.mpr hb'B)
  have haV : a ∉ zpowers b ⊔ zpowers b' := fun hm => haB (hVB hm)
  obtain ⟨hB'e, hB'c⟩ := isElemTwo_sup_zpowers hVe h.a_sq haV fun e he =>
    (h.central h.a_mem_Z (hBS (hVB he))).symm
  have hB'8 : IsEightGroup (zpowers b ⊔ zpowers b' ⊔ zpowers a) := ⟨hB'e, by rw [hB'c, hV4]⟩
  have hB'S : zpowers b ⊔ zpowers b' ⊔ zpowers a ≤ P ⊔ Q :=
    sup_le (hVB.trans hBS) (zpowers_le.mpr (mem_sup_left (h.Z_le_P h.a_mem_Z)))
  have hB'P : ¬ zpowers b ⊔ zpowers b' ⊔ zpowers a ≤ P := fun hle =>
    hbP (hle (mem_sup_left (mem_sup_left (mem_zpowers b))))
  have h₂ := h.connected_of_not_le_of_mem hB'S hB'8 (mem_sup_right (mem_zpowers a)) hB'P
  refine connectedIn_head hBS hB'S hB hB'8 (fun u hu v hv => ?_) h₂
  have hu' : ∀ w ∈ zpowers b ⊔ zpowers b', u * w = w * u := fun w hw => hB.1.1 u hu w (hVB hw)
  exact commute_sup_zpowers hu' (h.central h.a_mem_Z (hBS hu)).symm v hv

theorem isThreeConnected [Finite G] (h : Conn47Data P Q Z A₀ a z) {y : G} (hyQ : y ∈ Q)
    (hy2 : y * y = 1) (hyZ : y ∉ Z) : IsThreeConnected (P ⊔ Q) := by
  have hyP : y ∉ P := fun hm => hyZ (h.inf_eq ▸ mem_inf.mpr ⟨hm, hyQ⟩)
  have hAS : A₀ ≤ P ⊔ Q := h.A_le.trans le_sup_left
  have height : ∀ B : Subgroup G, B ≤ P ⊔ Q → IsEightGroup B →
      AbelianConnectedIn (P ⊔ Q) 3 B A₀ := by
    intro B hBS hB
    by_cases hBP : B ≤ P
    · obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B, x ≠ 1 := by
        by_contra hno
        push Not at hno
        have : B ≤ ⊥ := fun w hw => (mem_bot).mpr (hno w hw)
        have h1 := card_le_of_le this
        rw [hB.2, card_bot] at h1
        omega
      obtain ⟨x', hx'B, hVe, hV4⟩ := exists_four_le_eight hB hxB hx1
      have hVB : zpowers x ⊔ zpowers x' ≤ B := sup_le (zpowers_le.mpr hxB) (zpowers_le.mpr hx'B)
      have hyV : y ∉ zpowers x ⊔ zpowers x' := fun hm => hyP (hBP (hVB hm))
      obtain ⟨hB'e, hB'c⟩ := isElemTwo_sup_zpowers hVe hy2 hyV fun e he =>
        h.comm e (hBP (hVB he)) y hyQ
      have hB'8 : IsEightGroup (zpowers x ⊔ zpowers x' ⊔ zpowers y) := ⟨hB'e, by rw [hB'c, hV4]⟩
      have hB'S : zpowers x ⊔ zpowers x' ⊔ zpowers y ≤ P ⊔ Q :=
        sup_le (hVB.trans hBS) (zpowers_le.mpr (mem_sup_right hyQ))
      have hB'P : ¬ zpowers x ⊔ zpowers x' ⊔ zpowers y ≤ P := fun hle =>
        hyP (hle (mem_sup_right (mem_zpowers y)))
      refine connectedIn_head hBS hB'S hB hB'8 (fun u hu v hv => ?_)
        (h.connected_of_not_le hB'S hB'8 hB'P)
      have hu' : ∀ w ∈ zpowers x ⊔ zpowers x', u * w = w * u := fun w hw =>
        hB.1.1 u hu w (hVB hw)
      exact commute_sup_zpowers hu' (h.comm u (hBP hu) y hyQ) v hv
    · exact h.connected_of_not_le hBS hB hBP
  have habel : ∀ X : Subgroup G, X ≤ P ⊔ Q → IsAbelianTwoOfRank 3 X →
      AbelianConnectedIn (P ⊔ Q) 3 X A₀ := by
    intro X hXS hX
    obtain ⟨X₀, hX₀X, hX₀, hX₀8⟩ := exists_isElemTwo_eight hX
    have hX₀8' : IsEightGroup X₀ := ⟨hX₀, hX₀8⟩
    exact (show AbelianConnectedIn (P ⊔ Q) 3 X X₀ from ⟨hXS, hX, Relation.ReflTransGen.single
      ⟨hX₀X.trans hXS, hX₀.isAbelianTwoOfRank (by rw [hX₀8]), fun u hu v hv =>
        hX.2.1 u hu v (hX₀X hv)⟩⟩).trans (height X₀ (hX₀X.trans hXS) hX₀8')
  intro X Y hXS hYS hX hY
  exact (habel X hXS hX).trans (habel Y hYS hY).symm

end Conn47Data

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4

theorem l34Lemma47ConnectStep_of_inputs (hSq : L34NoSquareRootFact)
    (hCyc : L34CyclicCenterSylowFact) : L34Lemma47ConnectStep := by
  intro G _ _ a x J S A hset _ hZc hZ4 y hyQ hy2 hyZ
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  set P : Subgroup G := S ⊓ J with hPdef
  set Q : Subgroup G := S ⊓ coreActionKernel J with hQdef
  set Z : Subgroup G := S ⊓ zStarIn J with hZdef
  have hP : IsSylowTwoIn P J := isSylowTwoIn_inf hS
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : P ⊓ zStarIn J = Z := by rw [hPdef, inf_assoc, inf_eq_right.mpr hZJ]
  have hzK : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  have hPQZ : P ⊓ Q = Z := by
    rw [hPdef, hQdef, hZdef, hzK]
    ext w
    simp only [mem_inf]
    tauto
  obtain ⟨z', hgen⟩ := hZc.exists_generator
  have hzo : orderOf z' = 4 := by rw [← hZ4]; exact orderOf_eq_card_of_forall_mem_zpowers hgen
  set z : G := (z' : G) with hzdef
  have hzo' : orderOf z = 4 := by rw [hzdef, Subgroup.orderOf_coe, hzo]
  set a₀ : G := z * z with ha₀
  have ha₀2 : a₀ * a₀ = 1 := by
    rw [ha₀, show z * z * (z * z) = z ^ 4 by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two], ← hzo', pow_orderOf_eq_one]
  have ha₀1 : a₀ ≠ 1 := by
    intro h1
    have : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    rw [hzo'] at this
    exact absurd this (by norm_num)
  have ha₀o : orderOf a₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha₀2) ha₀1
  have hzZ : z ∈ Z := z'.2
  have ha₀Z : a₀ ∈ Z := mul_mem hzZ hzZ
  have hinv : ∀ w ∈ Z, w * w = 1 → w = 1 ∨ w = a₀ := by
    intro w hw hw2
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hgen ⟨w, hw⟩)
    have hwk : w = z ^ k := by
      have := congrArg Subtype.val hk
      simpa [hzdef] using this.symm
    have h2k : z ^ (2 * k) = 1 := by
      rw [zpow_mul, show (z ^ (2 : ℤ)) ^ k = (z ^ k) ^ (2 : ℤ) by
        rw [← zpow_mul, ← zpow_mul, mul_comm], ← hwk, zpow_two, hw2]
    have h4 : (4 : ℤ) ∣ 2 * k := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr h2k
      rw [hzo'] at this
      exact_mod_cast this
    obtain ⟨m, hm⟩ : (2 : ℤ) ∣ k := by omega
    have hw' : w ∈ zpowers a₀ := by
      rw [hwk, hm, zpow_mul, zpow_two]
      exact zpow_mem (mem_zpowers _) m
    exact eq_one_or_eq_of_mem_zpowers ha₀2 hw'
  have hZcP : IsCyclic ↥(P ⊓ zStarIn J) := by rwa [hZP]
  have hZ4P : Nat.card ↥(P ⊓ zStarIn J) = 4 := by rw [hZP]; exact hZ4
  obtain ⟨A₀, hA₀P, hA₀8, ha₀A₀, hA₀c, hEf⟩ :=
    hCyc G J P hJper hL34 hP hZcP hZ4P a₀ (hZP ▸ ha₀Z) ha₀o
  have hdata : Conn47Data P Q Z A₀ a₀ z :=
    { comm := fun p hp q hq => commute_of_mem_coreActionKernel hS2 hp hq
      inf_eq := hPQZ
      z_mem := hzZ
      z_sq := rfl
      a_sq := ha₀2
      a_ne := ha₀1
      inv_Z := hinv
      card_Z := hZ4
      A_le := hA₀P
      A_eight := hA₀8
      a_mem_A := ha₀A₀
      A_comm := hA₀c
      sq_P := fun u hu huZ => by
        have h4 := hSq G J P hJper hL34 hP hZcP hZ4P u hu (mem_inf.mp huZ).2
        rw [show u * u * (u * u) = u ^ 4 by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two], h4]
      E_fact := fun X hXP hXc hXs => by
        obtain ⟨E, hEP, hA₀E, hZE, hXE, hE64, hEc, hEs⟩ := hEf X hXP
          (fun u hu v hv => (mem_inf.mp (hXc u hu v hv)).2)
          (fun u hu => (mem_inf.mp (hXs u hu)).2)
        exact ⟨E, hEP, hA₀E, hZP ▸ hZE, hXE, hE64, hEc, hEs⟩ }
  have hyZ' : y ∉ Z := fun hm => hyZ (mem_inf.mp hm).2
  have h3 := hdata.isThreeConnected hyQ hy2 hyZ'
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  have hWN : withKernel J ≤ normalizer (J : Set G) := withKernel_le_normalizer J
  have hNW : normalizer (J : Set G) ≤ normalizer ((withKernel J : Subgroup G) : Set G) :=
    fun n hn => mem_normalizer_of_map_le_self (map_conj_withKernel_le hn)
  have hSyl := isSylowTwoIn_withKernel hS
  have hle : P ⊔ Q ≤ S ⊓ withKernel J := le_inf (sup_le inf_le_left inf_le_left)
    (sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right))
  have heq := hSyl.eq_of_le hle inf_le_right (hS2.to_le inf_le_left)
  rw [heq]
  exact h3

end CFSG.ComponentClassification.GrSLit
