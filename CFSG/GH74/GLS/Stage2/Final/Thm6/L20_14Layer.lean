module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Pair

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

variable {G : Type} [Group G]


variable {G : Type} [Group G]

theorem le_layer_of_isPComponent {C : Subgroup G} (h4a : pLayerOf 2 C = Em C) {J : Subgroup ↥C}
    (hJ : IsPComponent 2 J) : J ≤ layer ↥C := by
  have h1 : IsPCompIn 2 C (J.map C.subtype) :=
    ⟨Subgroup.map_subtype_le J, by
      have : (J.map C.subtype).subgroupOf C = J := Subgroup.comap_map_eq_self_of_injective C.subtype_injective J
      rw [this]; exact hJ⟩
  have h2 : J.map C.subtype ≤ pLayerOf 2 C := le_sSup h1
  rw [h4a] at h2
  have h3 : J.map C.subtype ≤ (layer ↥C).map C.subtype := h2
  exact (Subgroup.map_le_map_iff_of_injective C.subtype_injective).mp h3


structure CompData [Finite G] (z : G) (K₁ K₂ : Subgroup G) (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop where
  le₁ : K₁ ≤ Cen z
  le₂ : K₂ ≤ Cen z
  bar₁ : barOf z K₁ = L₁
  bar₂ : barOf z K₂ = L₂
  perf₁ : ⁅K₁, K₁⁆ = K₁
  quasi₁ : IsQuasisimple ↥K₁
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  layer : Em (Cen z) = K₁ ⊔ K₂
  odd_norm : ∀ x ∈ Cen z, Odd (orderOf x) →
    (∀ a ∈ K₁, x * a * x⁻¹ ∈ K₁) ∧ (∀ b ∈ K₂, x * b * x⁻¹ ∈ K₂)
  odd_mem : ∀ x ∈ Cen z, Odd (orderOf x) → (∀ a ∈ K₁, x * a = a * x) → (∀ b ∈ K₂, x * b = b * x) →
    x ∈ OddCore z
  perfect : ∀ P : Subgroup G, P ≤ Cen z → ⁅P, P⁆ = P → P ≤ Em (Cen z)
  oddcomm : ∀ a ∈ OddCore z, ∀ l ∈ Em (Cen z), a * l = l * a
  swap : ∀ (t : G) (ht : t ∈ Cen z), cj (toBar z ⟨t, ht⟩) L₁ = L₂ →
    (∀ a ∈ K₁, t * a * t⁻¹ ∈ K₂) ∧ (∀ b ∈ K₂, t * b * t⁻¹ ∈ K₁)
  mem_layer : ∀ (u : G) (hu : u ∈ Cen z), u * u = 1 → toBar z ⟨u, hu⟩ ∈ L₁ ⊔ L₂ → u ∈ Em (Cen z)


theorem odd_orderOf_of_mem_pPrimeCore {X : Type} [Group X] [Finite X] {a : X}
    (ha : a ∈ pPrimeCore 2 X) : Odd (orderOf a) := by
  have hd : orderOf (⟨a, ha⟩ : ↥(pPrimeCore 2 X)) ∣ Nat.card ↥(pPrimeCore 2 X) := orderOf_dvd_natCard _
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 X)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X))
  have h1 := Odd.of_dvd_nat hodd hd
  rwa [Subgroup.orderOf_mk] at h1

theorem mem_layer_of_sq_one {X : Type} [Group X] [Finite X] {L₁ L₂ : Subgroup (X ⧸ pPrimeCore 2 X)}
    {Γ₁ Γ₂ : Subgroup X} (T : TwoComps L₁ L₂ Γ₁ Γ₂) {u : X} (hu2 : u * u = 1)
    (hu : QuotientGroup.mk' (pPrimeCore 2 X) u ∈ L₁ ⊔ L₂) : u ∈ layer X := by
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  rw [← T.map_layer] at hu
  obtain ⟨l, hl, hlu⟩ := hu
  set a := u * l⁻¹ with ha
  have haA : a ∈ pPrimeCore 2 X := by
    have h1 : π a = 1 := by rw [ha, map_mul, map_inv, hlu, mul_inv_cancel]
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hcomm : Commute a l := layer_comm_pPrimeCore a haA l hl
  have hu' : u = a * l := by rw [ha]; group
  obtain ⟨m, hm⟩ := odd_orderOf_of_mem_pPrimeCore haA
  have hupow : u ^ (2 * m + 1) = u := by
    rw [pow_succ, pow_mul, sq, hu2, one_pow, one_mul]
  have hpow : u ^ (2 * m + 1) = l ^ (2 * m + 1) := by
    rw [← hm, hu', hcomm.mul_pow, pow_orderOf_eq_one, one_mul]
  rw [← hupow, hpow]
  exact (layer X).pow_mem hl _

theorem mem_map_subtype_iff {C : Subgroup G} {Γ : Subgroup ↥C} {x : G} :
    x ∈ Γ.map C.subtype ↔ ∃ h : x ∈ C, (⟨x, h⟩ : ↥C) ∈ Γ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem barOf_map_subtype (z : G) (Γ : Subgroup ↥(Cen z)) :
    barOf z (Γ.map (Cen z).subtype) = Γ.map (toBar z) := by
  unfold barOf
  have : (Γ.map (Cen z).subtype).subgroupOf (Cen z) = Γ :=
    Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective Γ
  rw [this]

theorem exists_compData [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (h : Stage1Pair G z S q L₁ L₂)
    (h4a : pLayerOf 2 (Cen z) = Em (Cen z)) : ∃ K₁ K₂ : Subgroup G, CompData z K₁ K₂ L₁ L₂ := by
  have hP := PairShape.of_stage1Pair h
  have hlift : ∀ J : Subgroup ↥(Cen z), IsPComponent 2 J → J ≤ layer ↥(Cen z) :=
    fun J hJ => le_layer_of_isPComponent h4a hJ
  obtain ⟨Γ₁, Γ₂, c₁, c₂, m₁, m₂, hall, hne, hcomm⟩ :=
    exists_two_components hlift hP.c₁ hP.c₂ hP.ne hP.comps
  have T : TwoComps L₁ L₂ Γ₁ Γ₂ := ⟨c₁, c₂, m₁, m₂, hall, hne, hcomm⟩
  have hinj := (Cen z).subtype_injective
  have hperf : ∀ Γ : Subgroup ↥(Cen z), Group.IsPerfect ↥Γ → ⁅Γ.map (Cen z).subtype, Γ.map (Cen z).subtype⁆ = Γ.map (Cen z).subtype := by
    intro Γ hΓ
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hΓ]
  have hcommE : ∀ a ∈ Γ₁.map (Cen z).subtype, ∀ b ∈ Γ₂.map (Cen z).subtype, a * b = b * a := by
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := ha
    obtain ⟨y', hy', rfl⟩ := hb
    have := Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hy) y' hy'
    exact congrArg Subtype.val this.symm
  refine ⟨Γ₁.map (Cen z).subtype, Γ₂.map (Cen z).subtype, ⟨Subgroup.map_subtype_le _, Subgroup.map_subtype_le _,
    (barOf_map_subtype z Γ₁).trans m₁, (barOf_map_subtype z Γ₂).trans m₂, hperf Γ₁ c₁.1.1,
    isQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective Γ₁ (Cen z).subtype hinj) c₁.1, hcommE, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩⟩
  ·
    rw [Em_eq, T.layer_eq, Subgroup.map_sup]
  ·
    intro x hx hodd
    set x' : ↥(Cen z) := ⟨x, hx⟩ with hx'
    have hodd' : Odd (orderOf x') := by rwa [hx', Subgroup.orderOf_mk]
    obtain ⟨h1, h2⟩ := T.cj_fix_of_odd hP hodd'
    constructor
    · intro a ha
      obtain ⟨hC, ha'⟩ := mem_map_subtype_iff.mp ha
      have hm : x' * ⟨a, hC⟩ * x'⁻¹ ∈ cj x' Γ₁ := ⟨_, ha', rfl⟩
      rw [h1] at hm
      exact ⟨_, hm, rfl⟩
    · intro b hb
      obtain ⟨hC, hb'⟩ := mem_map_subtype_iff.mp hb
      have hm : x' * ⟨b, hC⟩ * x'⁻¹ ∈ cj x' Γ₂ := ⟨_, hb', rfl⟩
      rw [h2] at hm
      exact ⟨_, hm, rfl⟩
  ·
    intro x hx hodd h1 h2
    set x' : ↥(Cen z) := ⟨x, hx⟩ with hx'
    have hodd' : Odd (orderOf x') := by rwa [hx', Subgroup.orderOf_mk]
    have := T.mem_odd_of_centralizes hP hodd'
      (fun a ha => Subtype.ext (h1 (a : G) ⟨a, ha, rfl⟩))
      (fun a ha => Subtype.ext (h2 (a : G) ⟨a, ha, rfl⟩))
    exact ⟨x', this, rfl⟩
  ·
    intro P hPC hP2
    set P' : Subgroup ↥(Cen z) := P.subgroupOf (Cen z) with hP'
    have hmap : P'.map (Cen z).subtype = P := Subgroup.map_subgroupOf_eq_of_le hPC
    have hperfP' : ⁅P', P'⁆ = P' := by
      apply Subgroup.map_injective hinj
      rw [Subgroup.map_commutator, hmap, hP2]
    have := T.perfect_le hP hperfP'
    rw [Em_eq, ← hmap]
    exact Subgroup.map_mono this
  ·
    intro a ha l hl
    obtain ⟨a', ha', rfl⟩ := ha
    rw [Em_eq] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    exact congrArg Subtype.val (layer_comm_pPrimeCore a' ha' l' hl')
  ·
    intro t ht hswap
    have hs : cj (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)) ⟨t, ht⟩) L₁ = L₂ := hswap
    obtain ⟨h1, h2⟩ := T.cj_swap hP hs
    constructor
    · intro a ha
      obtain ⟨hC, ha'⟩ := mem_map_subtype_iff.mp ha
      have hm : (⟨t, ht⟩ : ↥(Cen z)) * ⟨a, hC⟩ * ⟨t, ht⟩⁻¹ ∈ cj ⟨t, ht⟩ Γ₁ := ⟨_, ha', rfl⟩
      rw [h1] at hm
      exact ⟨_, hm, rfl⟩
    · intro b hb
      obtain ⟨hC, hb'⟩ := mem_map_subtype_iff.mp hb
      have hm : (⟨t, ht⟩ : ↥(Cen z)) * ⟨b, hC⟩ * ⟨t, ht⟩⁻¹ ∈ cj ⟨t, ht⟩ Γ₂ := ⟨_, hb', rfl⟩
      rw [h2] at hm
      exact ⟨_, hm, rfl⟩
  ·
    intro u hu hu2 hbar
    have h1 : (⟨u, hu⟩ : ↥(Cen z)) * ⟨u, hu⟩ = 1 := Subtype.ext hu2
    have := mem_layer_of_sq_one T h1 hbar
    rw [Em_eq]
    exact ⟨_, this, rfl⟩

theorem inv_mul_mem_of_relIndex_two {R S : Subgroup G} (h2 : R.relIndex S = 2) {x y : G}
    (hxS : x ∈ S) (hyS : y ∈ S) (hx : x ∉ R) (hy : y ∉ R) : x⁻¹ * y ∈ R := by
  have h2' : (R.subgroupOf S).index = 2 := h2
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp h2'
  have hn : (R.subgroupOf S).Normal := Subgroup.normal_of_index_eq_two h2'
  have hxR : ¬ (⟨x, hxS⟩ : ↥S) ∈ R.subgroupOf S := fun h => hx h
  have hyR : ¬ (⟨y, hyS⟩ : ↥S) ∈ R.subgroupOf S := fun h => hy h
  have h1 : (⟨x, hxS⟩ : ↥S) * a ∈ R.subgroupOf S := by
    rcases ha ⟨x, hxS⟩ with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hxR
  have h1' : (⟨y, hyS⟩ : ↥S) * a ∈ R.subgroupOf S := by
    rcases ha ⟨y, hyS⟩ with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hyR
  have h3 : (⟨x, hxS⟩ : ↥S)⁻¹ * ⟨y, hyS⟩ ∈ R.subgroupOf S := by
    have := (R.subgroupOf S).mul_mem ((R.subgroupOf S).inv_mem h1) h1'
    have h4 : (⟨x, hxS⟩ * a)⁻¹ * (⟨y, hyS⟩ * a) = a⁻¹ * ((⟨x, hxS⟩ : ↥S)⁻¹ * ⟨y, hyS⟩) * a := by group
    rw [h4] at this
    have := hn.conj_mem _ this a
    simpa [mul_assoc] using this
  exact h3



theorem PairShape.cj_fix_of_mem_sup {Q : Type} [Group Q] [Finite Q] {L₁ L₂ : Subgroup Q}
    (h : PairShape L₁ L₂) {r : Q} (hr : r ∈ L₁ ⊔ L₂) : cj r L₁ = L₁ := by
  rw [cj_eq_iff]
  have hle : L₁ ⊔ L₂ ≤ normalizer (L₁ : Set Q) := by
    refine sup_le Subgroup.le_normalizer (fun b hb => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : b * x * b⁻¹ = x := by rw [← h.comm x hx b hb]; group
      rw [this]; exact hx
    · intro hx'
      have h1 : (b * x * b⁻¹) * b = b * (b * x * b⁻¹) := h.comm _ hx' b hb
      have : x = b * x * b⁻¹ := by
        calc x = b⁻¹ * ((b * x * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [h1]
          _ = b * x * b⁻¹ := by group
      rw [this]; exact hx'
  exact hle hr


theorem exists_swap_of_mem_S [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G} (h : Stage1Pair G z S q L₁ L₂)
    (hK : CompData z K₁ K₂ L₁ L₂) (hSC : S ≤ Cen z) (hidx : (RC S z).relIndex S = 2) {y : G}
    (hyS : y ∈ S) (hyswap : Swaps z y L₁ L₂) (h12b : ∀ u ∈ Em (Cen z), IsConj z u → u = z)
    {t : G} (htS : t ∈ S) (htz : IsConj z t) (hne : t ≠ z) (ht2 : t * t = 1) :
    ∃ ht : t ∈ Cen z, cj (toBar z ⟨t, ht⟩) L₁ = L₂ := by
  have hP := PairShape.of_stage1Pair h
  have hsup : LBar z = L₁ ⊔ L₂ := h.prod.1.symm
  have hbarLC : ∀ (u : G) (hu : u ∈ Cen z), u ∈ LC z → toBar z ⟨u, hu⟩ ∈ L₁ ⊔ L₂ := by
    intro u hu hLC
    rw [← hsup]
    exact ⟨⟨u, hu⟩, hLC, rfl⟩
  have htC : t ∈ Cen z := hSC htS
  have hyC : y ∈ Cen z := hSC hyS
  obtain ⟨hyC', hy1, hy2⟩ := hyswap
  have htLC : t ∉ LC z := fun hLC => hne (h12b t (hK.mem_layer t htC ht2 (hbarLC t htC hLC)) htz)
  have hyLC : y ∉ LC z := by
    intro hLC
    have hyb := hbarLC y hyC hLC
    have := hP.cj_fix_of_mem_sup ((L₁ ⊔ L₂).inv_mem hyb)
    exact hP.ne (this.symm.trans hy1)
  have hRt : t ∉ RC S z := fun hR => htLC hR.2
  have hRy : y ∉ RC S z := fun hR => hyLC hR.2
  have hrel := inv_mul_mem_of_relIndex_two hidx hyS htS hRy hRt
  have hrLC : y⁻¹ * t ∈ LC z := hrel.2
  have hrC : y⁻¹ * t ∈ Cen z := (Cen z).mul_mem ((Cen z).inv_mem hyC) htC
  have hrb := hbarLC _ hrC hrLC
  refine ⟨htC, ?_⟩
  have hty : (⟨t, htC⟩ : ↥(Cen z)) = ⟨y, hyC⟩ * ⟨y⁻¹ * t, hrC⟩ := by
    apply Subtype.ext; simp
  have h1 : cj (toBar z ⟨y, hyC⟩) L₁ = L₂ := by
    rw [← hy2]
    show cj _ (cj _ L₂) = L₂
    rw [cj_cj, mul_inv_cancel, cj_one]
  rw [hty, map_mul, ← cj_cj, hP.cj_fix_of_mem_sup hrb, h1]


end CFSG.GH74.GLS.Stage2.Final.Thm6.L20
