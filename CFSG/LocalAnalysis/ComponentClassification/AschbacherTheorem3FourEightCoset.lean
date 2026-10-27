module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightRankThree
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightPNormal

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

@[expose] def cosetSub (A : Subgroup X) (w : X) (hw2 : w ^ 2 = 1)
    (hwA : ∀ a ∈ A, a * w = w * a) : Subgroup X where
  carrier := {x | x ∈ A ∨ w⁻¹ * x ∈ A}
  mul_mem' := by
    intro x x' hx hx'
    have hww : w * w = 1 := by rw [← pow_two, hw2]
    change x ∈ A ∨ w⁻¹ * x ∈ A at hx
    change x' ∈ A ∨ w⁻¹ * x' ∈ A at hx'
    change x * x' ∈ A ∨ w⁻¹ * (x * x') ∈ A
    rcases hx with hx | hx <;> rcases hx' with hx' | hx'
    · exact Or.inl (A.mul_mem hx hx')
    · right
      obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, x' = w * a := ⟨w⁻¹ * x', hx', by group⟩
      have h1 : w⁻¹ * (x * (w * a)) = w⁻¹ * (x * w) * a := by group
      rw [h1, hwA x hx]
      have h2 : w⁻¹ * (w * x) * a = x * a := by group
      rw [h2]
      exact A.mul_mem hx ha
    · right
      rw [← mul_assoc]
      exact A.mul_mem hx hx'
    · left
      obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, x = w * a := ⟨w⁻¹ * x, hx, by group⟩
      obtain ⟨a', ha', rfl⟩ : ∃ a' ∈ A, x' = w * a' := ⟨w⁻¹ * x', hx', by group⟩
      have h1 : w * a * (w * a') = w * (a * w) * a' := by group
      rw [h1, hwA a ha]
      have h2 : w * (w * a) * a' = (w * w) * a * a' := by group
      rw [h2, hww, one_mul]
      exact A.mul_mem ha ha'
  one_mem' := Or.inl A.one_mem
  inv_mem' := by
    intro x hx
    change x ∈ A ∨ w⁻¹ * x ∈ A at hx
    change x⁻¹ ∈ A ∨ w⁻¹ * x⁻¹ ∈ A
    rcases hx with hx | hx
    · exact Or.inl (A.inv_mem hx)
    · right
      have hw' : w⁻¹ = w := Elem47.inv_eq_of_sq hw2
      have hww : w * w = 1 := by rw [← pow_two, hw2]
      obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, x = w * a := ⟨w⁻¹ * x, hx, by group⟩
      have hc : a⁻¹ * w = w * a⁻¹ := hwA _ (A.inv_mem ha)
      have h1 : w⁻¹ * (w * a)⁻¹ = a⁻¹ := by
        calc w⁻¹ * (w * a)⁻¹ = w⁻¹ * a⁻¹ * w⁻¹ := by group
          _ = w * a⁻¹ * w := by rw [hw']
          _ = a⁻¹ * w * w := by rw [← hc]
          _ = a⁻¹ := by rw [mul_assoc, hww, mul_one]
      rw [h1]
      exact A.inv_mem ha

omit [Finite X] in
theorem mem_cosetSub {A : Subgroup X} {w : X} {hw2 : w ^ 2 = 1} {hwA : ∀ a ∈ A, a * w = w * a}
    {x : X} : x ∈ cosetSub A w hw2 hwA ↔ x ∈ A ∨ w⁻¹ * x ∈ A :=
  Iff.rfl

omit [Finite X] in
theorem le_cosetSub {A : Subgroup X} {w : X} (hw2 : w ^ 2 = 1) (hwA : ∀ a ∈ A, a * w = w * a) :
    A ≤ cosetSub A w hw2 hwA :=
  fun _ ha => Or.inl ha

omit [Finite X] in
theorem mem_cosetSub_self {A : Subgroup X} {w : X} (hw2 : w ^ 2 = 1)
    (hwA : ∀ a ∈ A, a * w = w * a) : w ∈ cosetSub A w hw2 hwA :=
  Or.inr (by rw [inv_mul_cancel]; exact A.one_mem)

omit [Finite X] in
theorem cosetSub_comm {A : Subgroup X} {w : X} (hw2 : w ^ 2 = 1) (hwA : ∀ a ∈ A, a * w = w * a)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ a ∈ cosetSub A w hw2 hwA, ∀ b ∈ cosetSub A w hw2 hwA, a * b = b * a := by
  have key : ∀ x ∈ cosetSub A w hw2 hwA, ∃ a ∈ A, x = a ∨ x = w * a := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨x, hx, Or.inl rfl⟩
    · exact ⟨w⁻¹ * x, hx, Or.inr (by group)⟩
  intro x hx x' hx'
  obtain ⟨a, ha, hxa⟩ := key x hx
  obtain ⟨a', ha', hxa'⟩ := key x' hx'
  rcases hxa with hxa | hxa <;> rcases hxa' with hxa' | hxa' <;> rw [hxa, hxa']
  · exact hA a ha a' ha'
  · calc a * (w * a') = (a * w) * a' := by group
      _ = w * (a * a') := by rw [hwA a ha]; group
      _ = w * (a' * a) := by rw [hA a ha a' ha']
      _ = w * a' * a := by group
  · calc w * a * a' = w * (a * a') := by group
      _ = w * (a' * a) := by rw [hA a ha a' ha']
      _ = (w * a') * a := by group
      _ = a' * (w * a) := by rw [← hwA a' ha']; group
  · calc w * a * (w * a') = w * (a * w) * a' := by group
      _ = w * w * (a * a') := by rw [hwA a ha]; group
      _ = w * w * (a' * a) := by rw [hA a ha a' ha']
      _ = w * (a' * w) * a := by rw [hwA a' ha']; group
      _ = w * a' * (w * a) := by group

omit [Finite X] in
theorem card_cosetSub {A : Subgroup X} {w : X} (hw2 : w ^ 2 = 1) (hwA : ∀ a ∈ A, a * w = w * a)
    (hw : w ∉ A) : Nat.card (cosetSub A w hw2 hwA) = 2 * Nat.card A := by
  set E := cosetSub A w hw2 hwA with hE
  have hAE : A ≤ E := le_cosetSub hw2 hwA
  have hww : w * w = 1 := by rw [← pow_two, hw2]
  have hidx : (A.subgroupOf E).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨w, mem_cosetSub_self hw2 hwA⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul]
    by_cases hb : (b : X) ∈ A
    · have hbw : (b : X) * w ∉ A := fun h => hw (by simpa using A.mul_mem (A.inv_mem hb) h)
      exact Or.inr ⟨hb, hbw⟩
    · have hb' : w⁻¹ * (b : X) ∈ A := (b.2.resolve_left hb)
      have hbw : (b : X) * w ∈ A := by
        have h1 : (b : X) * w = w * ((w⁻¹ * b) * w) := by group
        rw [h1, hwA _ hb']
        have h2 : w * (w * (w⁻¹ * (b : X))) = (w * w) * (w⁻¹ * b) := by group
        rw [h2, hww, one_mul]
        exact hb'
      exact Or.inl ⟨hbw, hb⟩
  have h1 := Subgroup.card_mul_index (A.subgroupOf E)
  rw [hidx] at h1
  have h2 : Nat.card (A.subgroupOf E) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv
  rw [h2] at h1
  omega

omit [Finite X] in
theorem sq_eq_one_of_mem_rightConjugate {U : Subgroup X} (hU : ∀ u ∈ U, u ^ 2 = 1) {h u : X}
    (hu : u ∈ rightConjugate U h) : u ^ 2 = 1 := by
  rw [mem_rightConjugate_iff] at hu
  have h1 := hU _ hu
  have h2 : u ^ 2 = h⁻¹ * (h * u * h⁻¹) ^ 2 * h := by rw [pow_two, pow_two]; group
  rw [h2, h1]
  group

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {D R : Subgroup X}
    (hD : IsPGroup p D) (hRD : R ≤ D) (hne : ¬ D ≤ R) :
    ∃ d ∈ D, d ∉ R ∧ d ∈ Subgroup.normalizer (R : Set X) := by
  have : Group.IsNilpotent D := hD.isNilpotent
  set R' := R.subgroupOf D with hR'
  have hlt : R' < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne fun x hx => ?_
    have : (⟨x, hx⟩ : D) ∈ R' := htop ▸ Subgroup.mem_top _
    exact this
  obtain ⟨d, hdN, hdR⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent R' hlt)
  refine ⟨d, d.2, hdR, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hdN ⟨x, hRD hx⟩).mp hx
    exact h1
  · intro hx
    have hxD : x ∈ D := by
      have := D.mul_mem (D.mul_mem (D.inv_mem d.2) (hRD hx)) d.2
      simpa [mul_assoc] using this
    exact (Subgroup.mem_normalizer_iff.mp hdN ⟨x, hxD⟩).mpr hx

namespace ElemCtx

theorem mem_A_of_comm (c : ElemCtx G T S Q H g y) {u : X} (huS : u ∈ S)
    (huW : u ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) {z : X}
    (hz : z ∈ (T ⊔ rightConjugate T g) ⊓ G) (hzu : z * u = u * z) :
    z ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) :=
  ⟨hz, Subgroup.mem_centralizer_iff.mpr fun _ hp => (c.comm_P_of_comm_w huS huW hz hzu hp).symm⟩

omit [Finite X] in
theorem A_comm {a s : X} (ha : a ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X))
    (hs : s ∈ S) : a * s = s * a :=
  (Subgroup.mem_centralizer_iff.mp ha.2 s hs).symm

theorem comm_mem_A (c : ElemCtx G T S Q H g y) {u : X} (huS : u ∈ S) (huG : u ∈ G)
    (huW : u ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hu2 : u ^ 2 = 1) {s : X}
    (hs : s ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G) :
    s⁻¹ * (u⁻¹ * s * u) ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) := by
  have hc := comm_mem_Z_of_mem_G c.elem huS huG huW hs.1 hs.2
  refine c.mem_A_of_comm huS huW hc ?_
  have h := conj_comm_eq hu2 (sq_Z c.elem hc)
  calc s⁻¹ * (u⁻¹ * s * u) * u = u * (u⁻¹ * (s⁻¹ * (u⁻¹ * s * u)) * u) := by group
    _ = u * (s⁻¹ * (u⁻¹ * s * u)) := by rw [h]

theorem conj_mem_coset (c : ElemCtx G T S Q H g y) {u : X} (huS : u ∈ S) (huG : u ∈ G)
    (huW : u ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hu2 : u ^ 2 = 1) {p : X}
    (hp : p ∈ S ⊓ G) :
    u⁻¹ * (p * u * p⁻¹) ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) := by
  have e := c.elem
  have hu' : u⁻¹ = u := Elem47.inv_eq_of_sq hu2
  have hR : ∀ r ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G,
      u⁻¹ * (r * u * r⁻¹) ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) := by
    intro r hr
    have hr' : r⁻¹ ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G := Subgroup.inv_mem _ hr
    have hb := c.comm_mem_A huS huG huW hu2 hr'
    have h1 : u⁻¹ * (r * u * r⁻¹) = u * (r⁻¹⁻¹ * (u⁻¹ * r⁻¹ * u)) * u⁻¹ := by
      have h3 : u * (r⁻¹⁻¹ * (u⁻¹ * r⁻¹ * u)) * u⁻¹ = u * r * u⁻¹ * r⁻¹ := by group
      rw [h3, hu']; group
    rw [h1, ← A_comm hb huS]
    have h2 : r⁻¹⁻¹ * (u⁻¹ * r⁻¹ * u) * u * u⁻¹ = r⁻¹⁻¹ * (u⁻¹ * r⁻¹ * u) := by group
    rw [h2]
    exact hb
  by_cases hpW : p ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)
  · exact hR p ⟨hpW, hp.2⟩
  · have hr : p * u⁻¹ ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G :=
      ⟨mul_inv_mem_W e huS hp.1 huW hpW, G.mul_mem hp.2 (G.inv_mem huG)⟩
    have h1 : p * u * p⁻¹ = (p * u⁻¹) * u * (p * u⁻¹)⁻¹ := by
      rw [hu']; group
    rw [h1]
    exact hR _ hr

theorem le_normalizer_cosetSub (c : ElemCtx G T S Q H g y) {u : X} (huS : u ∈ S) (huG : u ∈ G)
    (huW : u ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hu2 : u ^ 2 = 1)
    (huA : ∀ a ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X),
      a * u = u * a) :
    S ⊓ G ≤ Subgroup.normalizer
      (cosetSub ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) u hu2 huA :
        Set X) := by
  set A := (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) with hAdef
  have hconj : ∀ p ∈ S ⊓ G, ∀ x ∈ cosetSub A u hu2 huA, p * x * p⁻¹ ∈ cosetSub A u hu2 huA := by
    intro p hp x hx
    rcases hx with hx | hx
    · left
      rw [← A_comm hx hp.1]
      simpa using hx
    · right
      obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, x = u * a := ⟨u⁻¹ * x, hx, by group⟩
      have h1 : u⁻¹ * (p * (u * a) * p⁻¹) = (u⁻¹ * (p * u * p⁻¹)) * (p * a * p⁻¹) := by group
      rw [h1, ← A_comm ha hp.1]
      have h2 : a * p * p⁻¹ = a := by group
      rw [h2]
      exact A.mul_mem (c.conj_mem_coset huS huG huW hu2 hp) ha
  intro p hp
  exact mem_normalizer_of_conj_le (hconj p hp)
    (by simpa using hconj p⁻¹ (Subgroup.inv_mem _ hp))

theorem le_normalizer_of_elem (c : ElemCtx G T S Q H g y)
    (hk : Nat.card ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) ≤
      2 * Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) :
        Subgroup X))
    {U : Subgroup X} (hUP : U ≤ S ⊓ G) (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hUcard : 2 * Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) :
        Subgroup X) ≤ Nat.card U) :
    S ⊓ G ≤ Subgroup.normalizer (U : Set X) := by
  have e := c.elem
  set A := (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) with hAdef
  by_cases hUW : U ≤ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)
  ·
    have hUZ : U ≤ (T ⊔ rightConjugate T g) ⊓ G := fun u hu =>
      mem_Z_of_sq e (hUW hu) (hUP hu).2 (hU2 u hu)
    have heq : U = (T ⊔ rightConjugate T g) ⊓ G :=
      Subgroup.eq_of_le_of_card_ge hUZ (hk.trans hUcard)
    rw [heq]
    exact inf_le_left.trans (S_le_normalizer_Z e)
  · obtain ⟨u₀, hu₀U, hu₀W⟩ := Set.not_subset.mp hUW
    have hu₀S := (hUP hu₀U).1
    have hu₀G := (hUP hu₀U).2
    have hu₀2 := hU2 u₀ hu₀U
    have hA : ∀ a ∈ A, a * u₀ = u₀ * a := fun a ha => A_comm ha hu₀S
    have hUR : ∀ u ∈ U, u ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) → u ∈ A := by
      intro u hu huW
      exact c.mem_A_of_comm hu₀S hu₀W (mem_Z_of_sq e huW (hUP hu).2 (hU2 u hu))
        (hUab u hu u₀ hu₀U)
    have hle : U ≤ cosetSub A u₀ hu₀2 hA := by
      intro u hu
      by_cases huW : u ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)
      · exact Or.inl (hUR u hu huW)
      · right
        have h1 : u₀⁻¹ * u = u * u₀⁻¹ := by
          have := hUab u hu u₀ hu₀U
          calc u₀⁻¹ * u = u₀⁻¹ * (u * u₀) * u₀⁻¹ := by group
            _ = u₀⁻¹ * (u₀ * u) * u₀⁻¹ := by rw [this]
            _ = u * u₀⁻¹ := by group
        rw [h1]
        exact hUR _ (U.mul_mem hu (U.inv_mem hu₀U))
          (mul_inv_mem_W e hu₀S (hUP hu).1 hu₀W huW)
    have hu₀A : u₀ ∉ A := fun h => hu₀W (Subgroup.mem_sup_right h.1.1)
    have heq : U = cosetSub A u₀ hu₀2 hA :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_cosetSub hu₀2 hA hu₀A]; exact hUcard)
    rw [heq]
    exact c.le_normalizer_cosetSub hu₀S hu₀G hu₀W hu₀2 hA

theorem normalizer_R_le (c : ElemCtx G T S Q H g y) :
    Subgroup.normalizer
        (((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G : Subgroup X) : Set X) ≤
      Subgroup.normalizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) := by
  have e := c.elem
  have hconj : ∀ n ∈ Subgroup.normalizer
      (((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G : Subgroup X) : Set X),
      ∀ z ∈ (T ⊔ rightConjugate T g) ⊓ G, n * z * n⁻¹ ∈ (T ⊔ rightConjugate T g) ⊓ G := by
    intro n hn z hz
    have hzR : z ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G :=
      ⟨Subgroup.mem_sup_right hz.1, hz.2⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hn z).mp hzR
    refine mem_Z_of_sq e h1.1 h1.2 ?_
    have h2 : (n * z * n⁻¹) ^ 2 = n * z ^ 2 * n⁻¹ := by rw [pow_two, pow_two]; group
    rw [h2, sq_Z e hz]
    group
  intro n hn
  exact mem_normalizer_of_conj_le (hconj n hn)
    (by simpa using hconj n⁻¹ (Subgroup.inv_mem _ hn))

theorem normalizer_P_le_R (c : ElemCtx G T S Q H g y) :
    G ⊓ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) ≤
      Subgroup.normalizer
        (((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G : Subgroup X) : Set X) := by
  have hF := c.frame
  have hne : G ⊓ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) ≠ G :=
    fun h => c.false_of_normal_P (h.symm.le.trans inf_le_right)
  have hTP : T ≤ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (c.sylowFrame.le ht), hF.le_normalizer ht⟩
  have hTN : T ≤ Subgroup.normalizer
      ((G ⊓ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) : Subgroup X) : Set X) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hF.le_normalizer ht, Subgroup.le_normalizer (hTP ht)⟩
  have hPC : S ⊓ G ≤ G ⊓ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) :=
    le_inf inf_le_right Subgroup.le_normalizer
  exact c.le_normalizer_R (C := G ⊓ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X))
    inf_le_left hne hTN hPC inf_le_right

theorem normalizer_P_le (c : ElemCtx G T S Q H g y) :
    G ⊓ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) ≤
      Subgroup.normalizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) :=
  c.normalizer_P_le_R.trans c.normalizer_R_le

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
