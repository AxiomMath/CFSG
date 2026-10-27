module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Harada
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructAux
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Walter.TwoRank
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG CFSG.Blueprint CFSG.LocalCores

variable {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}

namespace Local27

theorem isSimpleGroup_X (c : Local27 N X t) : IsSimpleGroup ↥X := by
  obtain ⟨e⟩ := c.exists_equiv_alt
  exact e.isSimpleGroup

theorem not_isPGroup_X (c : Local27 N X t) : ¬ IsPGroup 2 ↥X := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_card_eq
  rw [c.card_eq_sixty] at hn
  have h5 : 5 ∣ 2 ^ n := by rw [← hn]; norm_num
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5
  omega

theorem inf_eq_bot_of_normal_two (c : Local27 N X t) {M : Subgroup N}
    (hM : ∀ d ∈ centralizer ({t} : Set N), ∀ m ∈ M, d * m * d⁻¹ ∈ M) (hM2 : IsPGroup 2 M) :
    M ⊓ X = ⊥ := by
  have : IsSimpleGroup ↥X := c.isSimpleGroup_X
  have hn : ((M ⊓ X).subgroupOf X).Normal := by
    refine ⟨fun y hy x => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    refine ⟨?_, ?_⟩
    · exact hM x (c.X_le_centralizer_t x.2) y hy.1
    · exact X.mul_mem (X.mul_mem x.2 hy.2) (X.inv_mem x.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M ⊓ X).subgroupOf X) with h | h
  · rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hy.2⟩ : X) ∈ (M ⊓ X).subgroupOf X := hy
    rw [h, mem_bot] at this
    exact mem_bot.2 (congrArg Subtype.val this)
  · exfalso
    apply c.not_isPGroup_X
    refine hM2.to_le (H := X) ?_
    intro x hx
    have : (⟨x, hx⟩ : X) ∈ (M ⊓ X).subgroupOf X := by rw [h]; trivial
    exact this.1

theorem le_zpowers_of_normal_two (c : Local27 N X t) {M : Subgroup N}
    (hMD : M ≤ centralizer ({t} : Set N))
    (hM : ∀ d ∈ centralizer ({t} : Set N), ∀ m ∈ M, d * m * d⁻¹ ∈ M) (hM2 : IsPGroup 2 M) :
    M ≤ zpowers t := by
  have hbot := c.inf_eq_bot_of_normal_two hM hM2
  intro m hm
  have hmD := hMD hm
  have hmX : m ∈ centralizer (X : Set N) := by
    rw [mem_centralizer_iff]
    intro x hx
    have hXD := c.X_le_centralizer_t hx
    have h1 : m * (x * m⁻¹ * x⁻¹) ∈ M := M.mul_mem hm (hM x hXD m⁻¹ (M.inv_mem hm))
    have h2 : (m * x * m⁻¹) * x⁻¹ ∈ X := X.mul_mem (c.X_normal m hmD x hx) (X.inv_mem hx)
    have heq : m * (x * m⁻¹ * x⁻¹) = (m * x * m⁻¹) * x⁻¹ := by group
    have h3 : m * (x * m⁻¹ * x⁻¹) ∈ M ⊓ X := ⟨h1, heq ▸ h2⟩
    rw [hbot, mem_bot] at h3
    have h4 : m * x * m⁻¹ * x⁻¹ = 1 := by rw [← heq]; exact h3
    calc x * m = (m * x * m⁻¹ * x⁻¹)⁻¹ * (m * x) := by group
      _ = m * x := by rw [h4]; simp
  exact c.mem_zpowers_of_isPGroup ⟨hmD, hmX⟩ (hM2.to_le (zpowers_le.2 hm))

end Local27

omit [Finite N] in
private theorem inf_centralizer_invariant {Q : Subgroup N} [Q.Normal] :
    ∀ d ∈ centralizer ({t} : Set N), ∀ m ∈ Q ⊓ centralizer ({t} : Set N),
      d * m * d⁻¹ ∈ Q ⊓ centralizer ({t} : Set N) := by
  intro d hd m hm
  exact ⟨Normal.conj_mem inferInstance m hm.1 d,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hd hm.2) (Subgroup.inv_mem _ hd)⟩

theorem O2_bot27 (c : Local27 N X t) {Q : Subgroup N} [Q.Normal]
    (hQ : IsPGroup 2 Q) : Q = ⊥ := by
  by_contra hQne
  have htt := c.t_mul_t
  have ht1 : t ≠ 1 := by
    intro h1
    have := c.t_order
    rw [h1, orderOf_one] at this
    omega
  have hzt : IsPGroup 2 (zpowers t) := isPGroup_zpowers_of_mul_self htt
  have hM2 : IsPGroup 2 ↥(Q ⊓ centralizer ({t} : Set N)) := hQ.to_le inf_le_left
  have htQ : t ∈ Q := by
    have hP : IsPGroup 2 ↥(Q ⊔ zpowers t) := hQ.to_sup_of_normal_left hzt
    have : Group.IsNilpotent ↥(Q ⊔ zpowers t) := hP.isNilpotent
    have hne : Q.subgroupOf (Q ⊔ zpowers t) ≠ ⊥ := by
      intro h
      apply hQne
      rw [eq_bot_iff]
      intro q hq
      have : (⟨q, mem_sup_left hq⟩ : ↥(Q ⊔ zpowers t)) ∈ Q.subgroupOf (Q ⊔ zpowers t) := hq
      rw [h, mem_bot] at this
      exact mem_bot.2 (congrArg Subtype.val this)
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    have hzQ : z.1.1 ∈ Q := (mem_inf.1 z.2).1
    have hzc := mem_center_iff.1 (mem_inf.1 z.2).2
    have htP : t ∈ Q ⊔ zpowers t := mem_sup_right (mem_zpowers t)
    have hcomm : z.1.1 * t = t * z.1.1 := (congrArg Subtype.val (hzc ⟨t, htP⟩)).symm
    have hzM : z.1.1 ∈ Q ⊓ centralizer ({t} : Set N) :=
      ⟨hzQ, mem_centralizer_singleton_iff.2 hcomm⟩
    have hzt' := c.le_zpowers_of_normal_two inf_le_right inf_centralizer_invariant hM2 hzM
    have hz1' : z.1.1 ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt hzt' with h | h
    · exact absurd h hz1'
    · rw [← h]; exact hzQ
  have hQc : ∀ q ∈ Q, q * t = t * q := by
    have : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQne
    have : Group.IsNilpotent ↥Q := hQ.isNilpotent
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.center_ne_bot ↥Q)
    have hwc := mem_center_iff.1 w.2
    have hwt : (w.1 : N) * t = t * (w.1 : N) := (congrArg Subtype.val (hwc ⟨t, htQ⟩)).symm
    have hwM : (w.1 : N) ∈ Q ⊓ centralizer ({t} : Set N) :=
      ⟨w.1.2, mem_centralizer_singleton_iff.2 hwt⟩
    have hw1' : (w.1 : N) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt
        (c.le_zpowers_of_normal_two inf_le_right inf_centralizer_invariant hM2 hwM) with h | h
    · exact absurd h hw1'
    · intro q hq
      have h2 : q * (w.1 : N) = (w.1 : N) * q := congrArg Subtype.val (hwc ⟨q, hq⟩)
      rw [h] at h2
      exact h2
  have hcen : ∀ n : N, n * t = t * n := by
    intro n
    have hu : n * t * n⁻¹ ∈ Q := Normal.conj_mem inferInstance t htQ n
    have hu' : t * (n * t * n⁻¹) = (n * t * n⁻¹) * t := by
      have hv : n⁻¹ * t * n ∈ Q := by
        simpa using Normal.conj_mem inferInstance t htQ n⁻¹
      have := hQc (n⁻¹ * t * n) hv
      calc t * (n * t * n⁻¹) = n * ((n⁻¹ * t * n) * t) * n⁻¹ := by group
        _ = n * (t * (n⁻¹ * t * n)) * n⁻¹ := by rw [this]
        _ = (n * t * n⁻¹) * t := by group
    have huM : n * t * n⁻¹ ∈ Q ⊓ centralizer ({t} : Set N) :=
      ⟨hu, mem_centralizer_singleton_iff.2 hu'.symm⟩
    have hu1 : n * t * n⁻¹ ≠ 1 := by
      intro h
      apply ht1
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = n⁻¹ * 1 * n := by rw [h]
        _ = 1 := by group
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt
        (c.le_zpowers_of_normal_two inf_le_right inf_centralizer_invariant hM2 huM) with h | h
    · exact absurd h hu1
    · calc n * t = n * t * n⁻¹ * n := by group
        _ = t * n := by rw [h]
  have htop : centralizer ({t} : Set N) = ⊤ := by
    rw [eq_top_iff]
    intro n _
    exact mem_centralizer_singleton_iff.2 (hcen n)
  have := c.not_sylow
  rw [htop, Subgroup.card_top] at this
  exact lt_irrefl _ this

theorem fitting_eq_bot27 (c : Local27 N X t) :
    fittingSubgroup N = ⊥ := by
  have key : ∀ q : ℕ, q.Prime → pCore q N = ⊥ := by
    intro q hq
    have : Fact q.Prime := ⟨hq⟩
    by_cases h2 : q = 2
    · subst h2
      exact O2_bot27 c (Q := pCore 2 N) (pCore_isPGroup (p := 2) (G := N))
    · have hnorm : (pCore q N).Normal := pCore_normal
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := q) (G := N)).exists_card_eq
      have hodd : Odd (Nat.card (pCore q N)) := by
        rw [hn]; exact (hq.odd_of_ne_two h2).pow
      have hle : pCore q N ≤ oddCore N := le_sSup ⟨hnorm, hodd⟩
      rw [c.oddCore_bot, le_bot_iff] at hle
      exact hle
  rw [fitting_eq_sup_pCore, iSup_eq_bot]
  intro p
  exact key p.1.1 (Nat.prime_of_mem_primeFactors p.1.2)

theorem center_layer_eq_bot27 (c : Local27 N X t) :
    center ↥(layer N) = ⊥ := by
  have hchar : (layer N).Characteristic := layer_characteristic
  have hn : ((center ↥(layer N)).map (layer N).subtype).Normal := inferInstance
  have : Group.IsNilpotent ↥((center ↥(layer N)).map (layer N).subtype) :=
    Group.nilpotent_of_mulEquiv
      ((center ↥(layer N)).equivMapOfInjective (layer N).subtype (layer N).subtype_injective)
  have hle : (center ↥(layer N)).map (layer N).subtype ≤ fittingSubgroup N :=
    le_sSup ⟨hn, inferInstance⟩
  rw [fitting_eq_bot27 c, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ (layer N).subtype_injective).mp hle

theorem centralizer_layer_eq_bot27 (c : Local27 N X t) :
    centralizer ((layer N : Subgroup N) : Set N) = ⊥ := by
  have h1 : centralizer (generalizedFitting N : Set N) ≤ generalizedFitting N :=
    centralizer_generalizedFitting_le N
  have hgf : generalizedFitting N = layer N := by
    rw [generalizedFitting, fitting_eq_bot27 c, bot_sup_eq]
  rw [hgf] at h1
  rw [eq_bot_iff]
  intro g hg
  have hgE : g ∈ layer N := h1 hg
  have hz : (⟨g, hgE⟩ : ↥(layer N)) ∈ center ↥(layer N) := by
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (mem_centralizer_iff.1 hg x x.2)
  rw [center_layer_eq_bot27 c, mem_bot] at hz
  exact mem_bot.2 (congrArg Subtype.val hz)

theorem component_center_eq_bot27 (c : Local27 N X t)
    {K : Subgroup N} (hK : IsComponent K) : center ↥K = ⊥ := by
  have h := center_component_le_center_layer hK
  rw [center_layer_eq_bot27 c, Subgroup.map_bot, le_bot_iff] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp h

theorem component_simple27 (c : Local27 N X t)
    {K : Subgroup N} (hK : IsComponent K) :
    IsSimpleGroup ↥K ∧ ∃ a b : ↥K, a * b ≠ b * a := by
  have hZ := component_center_eq_bot27 c hK
  obtain ⟨-, hs, a, b, hab⟩ := hK.1
  let e : ↥K ≃* (↥K ⧸ center ↥K) :=
    (QuotientGroup.quotientBot (G := ↥K)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact ⟨e.isSimpleGroup, e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem component_commute27 {A B : Subgroup N} (hA : IsComponent A) (hB : IsComponent B)
    (hAB : A ≠ B) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  rcases distinct_components_commute hA hB with h | h
  · exact absurd h hAB
  · intro a ha b hb
    have := commutator_eq_bot_iff_le_centralizer.mp h ha
    exact (mem_centralizer_iff.1 this b hb).symm

theorem inf_component_eq_bot27 (c : Local27 N X t) {K D : Subgroup N}
    (hK : IsComponent K) (hD : D ≤ centralizer (K : Set N)) : D ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  intro x ⟨hxD, hxK⟩
  have hz : (⟨x, hxK⟩ : ↥K) ∈ center ↥K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (mem_centralizer_iff.1 (hD hxD) k k.2)
  rw [component_center_eq_bot27 c hK, mem_bot] at hz
  exact mem_bot.2 (congrArg Subtype.val hz)

omit [Finite N] in
theorem elemAb_sup {A B : Subgroup N} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAs : ∀ x ∈ A, x * x = 1) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hBs : ∀ x ∈ B, x * x = 1) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    (∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x) ∧ (∀ x ∈ A ⊔ B, x * x = 1) := by
  constructor
  · intro x hx y hy
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := (mem_sup_iff_of_commute hAB x).1 hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := (mem_sup_iff_of_commute hAB y).1 hy
    have hbb : Commute b₁ b₂ := hBc b₁ hb₁ b₂ hb₂
    have hab₁ : Commute a₁ b₂ := hAB a₁ ha₁ b₂ hb₂
    have hba₂ : Commute b₁ a₂ := (hAB a₂ ha₂ b₁ hb₁).symm
    have haa : Commute a₁ a₂ := hAc a₁ ha₁ a₂ ha₂
    exact ((haa.mul_right hab₁).mul_left (hba₂.mul_right hbb)).eq
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hAB x).1 hx
    have hba : Commute b a := (hAB a ha b hb).symm
    calc a * b * (a * b) = (a * a) * (b * b) := hba.mul_mul_mul_comm a b
      _ = 1 := by rw [hAs a ha, hBs b hb, one_mul]

theorem exists_elemAbelian_of_two_le_twoRank {K : Type} [Group K] [Finite K]
    (h : 2 ≤ CFSG.Assembly.twoRank K) :
    ∃ E : Subgroup K, CFSG.Assembly.IsElemAbelian 2 E ∧ 4 ≤ Nat.card E := by
  unfold CFSG.Assembly.twoRank CFSG.Assembly.pRank at h
  set s : Set ℕ := {k | ∃ E : Subgroup K, E ≤ ⊤ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧
    Nat.card E = 2 ^ k} with hs
  have hbdd : BddAbove s := ⟨Nat.card K, fun k ⟨E, _, _, hk⟩ =>
    (Nat.lt_two_pow_self).le.trans (hk ▸ Subgroup.card_le_card_group E)⟩
  have hne : s.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at h
    simp at h
  obtain ⟨E, -, hE, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨E, hE, ?_⟩
  rw [hcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ sSup s := Nat.pow_le_pow_right (by norm_num) h

theorem exists_elemAbelian_of_component (c : Local27 N X t)
    {K : Subgroup N} (hK : IsComponent K) :
    ∃ E : Subgroup N, E ≤ K ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧
      4 ≤ Nat.card E := by
  obtain ⟨hs, a, b, hab⟩ := component_simple27 c hK
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even
    ⟨a, b, hab⟩).1
  have h2 := CFSG.Walter.two_le_twoRank ↥K ⟨a, b, hab⟩ heven
  obtain ⟨E', hE', h4⟩ := exists_elemAbelian_of_two_le_twoRank h2
  refine ⟨E'.map K.subtype, Subgroup.map_subtype_le E', ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg (fun z : ↥E' => ((z : ↥K) : N)) (hE'.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · rintro _ ⟨x, hx, rfl⟩
    have h := hE'.2 x hx
    rw [pow_two] at h
    exact congrArg Subtype.val h
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact h4

theorem not_three_components
    (hHar : ComponentClassification.HSFLit.HaradaInput) (c : Local27 N X t)
    {K₁ K₂ K₃ : Subgroup N} (h₁ : IsComponent K₁) (h₂ : IsComponent K₂) (h₃ : IsComponent K₃)
    (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃) : False := by
  obtain ⟨E₁, hE₁K, hc₁, hs₁, h₁4⟩ := exists_elemAbelian_of_component c h₁
  obtain ⟨E₂, hE₂K, hc₂, hs₂, h₂4⟩ := exists_elemAbelian_of_component c h₂
  obtain ⟨E₃, hE₃K, hc₃, hs₃, h₃4⟩ := exists_elemAbelian_of_component c h₃
  have hK12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := component_commute27 h₁ h₂ h12
  have hK13 : ∀ a ∈ K₁, ∀ b ∈ K₃, a * b = b * a := component_commute27 h₁ h₃ h13
  have hK23 : ∀ a ∈ K₂, ∀ b ∈ K₃, a * b = b * a := component_commute27 h₂ h₃ h23
  have hC12 : K₂ ≤ centralizer (K₁ : Set N) := fun b hb =>
    mem_centralizer_iff.2 fun a ha => hK12 a ha b hb
  have hD12 : E₁ ⊓ E₂ = ⊥ := by
    have := inf_component_eq_bot27 c h₁ (D := K₂) hC12
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ K₂ ⊓ K₁ := ⟨hE₂K hx.2, hE₁K hx.1⟩
    rw [inf_component_eq_bot27 c h₁ hC12, mem_bot] at this
    exact mem_bot.2 this
  have hcard12 := card_sup_of_commute (fun a ha b hb => hK12 a (hE₁K ha) b (hE₂K hb)) hD12
  obtain ⟨hc12, hs12⟩ := elemAb_sup hc₁ hs₁ hc₂ hs₂
    (fun a ha b hb => hK12 a (hE₁K ha) b (hE₂K hb))
  have hE12K : E₁ ⊔ E₂ ≤ K₁ ⊔ K₂ := sup_le_sup hE₁K hE₂K
  have hC3 : K₁ ⊔ K₂ ≤ centralizer (K₃ : Set N) := by
    refine sup_le (fun a ha => mem_centralizer_iff.2 fun b hb => (hK13 a ha b hb).symm)
      (fun a ha => mem_centralizer_iff.2 fun b hb => (hK23 a ha b hb).symm)
  have hD123 : (E₁ ⊔ E₂) ⊓ E₃ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ (K₁ ⊔ K₂) ⊓ K₃ := ⟨hE12K hx.1, hE₃K hx.2⟩
    rw [inf_component_eq_bot27 c h₃ hC3, mem_bot] at this
    exact mem_bot.2 this
  have hcomm123 : ∀ x ∈ E₁ ⊔ E₂, ∀ y ∈ E₃, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute
      (fun a ha b hb => hK12 a (hE₁K ha) b (hE₂K hb)) x).1 hx
    have h1 : a * y = y * a := hK13 a (hE₁K ha) y (hE₃K hy)
    have h2 : b * y = y * b := hK23 b (hE₂K hb) y (hE₃K hy)
    calc a * b * y = a * (b * y) := mul_assoc _ _ _
      _ = a * (y * b) := by rw [h2]
      _ = (a * y) * b := (mul_assoc _ _ _).symm
      _ = (y * a) * b := by rw [h1]
      _ = y * (a * b) := mul_assoc _ _ _
  have hcard123 := card_sup_of_commute hcomm123 hD123
  obtain ⟨hc123, hs123⟩ := elemAb_sup hc12 hs12 hc₃ hs₃ hcomm123
  have hbig : 2 ^ 4 < Nat.card ↥(E₁ ⊔ E₂ ⊔ E₃) := by
    rw [hcard123, hcard12]
    have : 4 * 4 * 4 ≤ Nat.card E₁ * Nat.card E₂ * Nat.card E₃ :=
      Nat.mul_le_mul (Nat.mul_le_mul h₁4 h₂4) h₃4
    omega
  have h2g : IsPGroup 2 ↥(E₁ ⊔ E₂ ⊔ E₃) := fun g => ⟨1, by
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_two]
    exact hs123 g g.2⟩
  obtain ⟨s, hs4, hsE⟩ := harada27 hHar c _ h2g
  exact not_closure_of_card_gt (E₁ ⊔ E₂ ⊔ E₃) hc123 hs123 4 hbig ⟨s, hs4, hsE⟩

end CFSG.OddStandard.Seitz77
