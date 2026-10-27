module

public import CFSG.LargeExtraspecial.S8CBF3D4Grp
public import CFSG.LargeExtraspecial.S8CBF3D4Sect
public import CFSG.RankThree.PartTwo.Census.Carrier.D4EvenLevi
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement Pointwise

section Projection

variable {G : Type*} [Group G] {C Q L : Subgroup G}

theorem exists_proj_of_mul_eq [(Q.subgroupOf C).Normal]
    (hC : (C : Set G) = (Q : Set G) * (L : Set G))
    (hLC : L ≤ C) (hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) (hQL : Q ⊓ L = ⊥) :
    ∃ p : C →* L, (∀ x : C, p x = 1 ↔ (x : G) ∈ Q) ∧ ∀ l : L, p (inclusion hLC l) = l := by
  obtain ⟨e, he⟩ := exists_mulEquiv_quotient_of_mul_eq hC hLC hQn hQL
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' _), fun x => ?_, fun l => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← he l]
    exact e.symm_apply_apply l

@[expose] def projImage (p : C →* L) (H : Subgroup G) : Subgroup G :=
  ((H.subgroupOf C).map p).map L.subtype

variable (p : C →* L)

theorem projImage_le (H : Subgroup G) : projImage p H ≤ L := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_projImage_of_mem {H : Subgroup G} {x : G} (hx : x ∈ H) (hxC : x ∈ C) :
    ((p ⟨x, hxC⟩ : L) : G) ∈ projImage p H :=
  ⟨p ⟨x, hxC⟩, ⟨⟨x, hxC⟩, mem_subgroupOf.2 hx, rfl⟩, rfl⟩

theorem projImage_mono {H H' : Subgroup G} (h : H ≤ H') : projImage p H ≤ projImage p H' :=
  map_mono (map_mono fun _ hx => mem_subgroupOf.2 (h (mem_subgroupOf.1 hx)))

theorem projImage_perfect {H : Subgroup G} (hHC : H ≤ C) (hH : ⁅H, H⁆ = H) :
    ⁅projImage p H, projImage p H⁆ = projImage p H := by
  have h1 : ⁅H.subgroupOf C, H.subgroupOf C⁆ = H.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hHC, hH]
  rw [projImage, ← map_commutator, ← map_commutator, h1]

theorem projImage_isPGroup {ℓ : ℕ} {H : Subgroup G} (hH : IsPGroup ℓ H) :
    IsPGroup ℓ (projImage p H) :=
  ((hH.comap_subtype (K := C)).map _).map _

theorem projImage_conj_mem {M H : Subgroup G}
    (hMH : ∀ m ∈ M, ∀ h ∈ H, m * h * m⁻¹ ∈ H) :
    ∀ m ∈ projImage p M, ∀ h ∈ projImage p H, m * h * m⁻¹ ∈ projImage p H := by
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩ _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, mem_subgroupOf] at hm hh
  have hmh : m * h * m⁻¹ ∈ H.subgroupOf C := by
    rw [mem_subgroupOf]
    simpa using hMH m hm h hh
  refine ⟨p (m * h * m⁻¹), ⟨_, hmh, rfl⟩, ?_⟩
  simp

theorem le_of_projImage_eq_bot (hp : ∀ x : C, p x = 1 ↔ (x : G) ∈ Q) {H : Subgroup G}
    (hHC : H ≤ C) (h : projImage p H = ⊥) : H ≤ Q := by
  intro x hx
  have hm := mem_projImage_of_mem p hx (hHC hx)
  rw [h, mem_bot] at hm
  exact (hp ⟨x, hHC hx⟩).1 (Subtype.ext hm)

theorem card_projImage_mul (hp : ∀ x : C, p x = 1 ↔ (x : G) ∈ Q) {H : Subgroup G}
    (hHC : H ≤ C) : Nat.card (projImage p H) * Nat.card ↥(H ⊓ Q) = Nat.card H := by
  set f : H.subgroupOf C →* L := p.comp (H.subgroupOf C).subtype with hf
  have hrange : Nat.card (projImage p H) = Nat.card f.range := by
    rw [projImage, Subgroup.card_map_of_injective L.subtype_injective, MonoidHom.range_comp,
      range_subtype]
  have hker : Nat.card f.ker = Nat.card ↥(H ⊓ Q) := by
    refine Nat.card_congr ⟨fun x => ⟨((x : H.subgroupOf C) : G), ?_⟩,
      fun y => ⟨⟨⟨y, hHC (mem_inf.1 y.2).1⟩, mem_subgroupOf.2 (mem_inf.1 y.2).1⟩, ?_⟩,
      fun x => ?_, fun y => ?_⟩
    · refine mem_inf.2 ⟨mem_subgroupOf.1 (x : H.subgroupOf C).2, ?_⟩
      exact (hp _).1 (MonoidHom.mem_ker.1 x.2)
    · exact MonoidHom.mem_ker.2 ((hp _).2 (mem_inf.1 y.2).2)
    · rfl
    · rfl
  have h1 := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hker] at h1
  rw [hrange, ← h1]
  exact Nat.card_congr (subgroupOfEquivOfLe hHC).toEquiv

end Projection

theorem eq_bot_of_perfect_of_isPGroup {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : ⁅B, B⁆ = B) (hB2 : IsPGroup 2 B) : B = ⊥ := by
  have := Fact.mk Nat.prime_two
  have : Group.IsNilpotent B := hB2.isNilpotent
  have htop : commutator B = ⊤ := by
    apply map_injective B.subtype_injective
    rw [map_subtype_commutator, hB, ← MonoidHom.range_eq_map, range_subtype]
  have hder : ∀ n, derivedSeries B n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, htop]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := B)
  rw [hder] at hn
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈ (⊥ : Subgroup B) := hn ▸ mem_top _
  rw [mem_bot] at hx' ⊢
  exact congrArg Subtype.val hx'

section LeviRoot

variable {τ : Tag} {K : Type} [Field K]

theorem commutator_parabolicLevi_le_leviRoot
    (A : Set (Fin τ.rank)) :
    ⁅parabolicLevi τ K A, parabolicLevi τ K A⁆ ≤ leviRoot K A := by
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨b, l, hl, rfl⟩ := exists_eq_rootDiagUnit_mul hx
  obtain ⟨b', l', hl', rfl⟩ := exists_eq_rootDiagUnit_mul hy
  set d := rootDiagUnit τ b with hd
  set d' := rootDiagUnit τ b' with hd'
  have hdd : d * d' = d' * d := by
    rw [hd, hd', ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hconj : ∀ (e : Fin τ.rank → Kˣ), ∀ z ∈ leviRoot K A,
      rootDiagUnit τ e * z * (rootDiagUnit τ e)⁻¹ ∈ leviRoot K A := fun e z hz =>
    (mem_normalizer_iff.1 (rootDiagUnit_mem_normalizer e A) z).1 hz
  have hu : l * (d' * (l' * l⁻¹) * d'⁻¹) ∈ leviRoot K A :=
    mul_mem hl (hconj b' _ (mul_mem hl' (inv_mem hl)))
  have hv : d' * l'⁻¹ * d'⁻¹ ∈ leviRoot K A := hconj b' _ (inv_mem hl')
  have e1 : d'⁻¹ * d⁻¹ * d' = d⁻¹ := by
    calc d'⁻¹ * d⁻¹ * d' = d'⁻¹ * (d⁻¹ * d') := by group
      _ = d'⁻¹ * (d' * d⁻¹) := by
          rw [show d⁻¹ * d' = d' * d⁻¹ by
            calc d⁻¹ * d' = d⁻¹ * (d' * d) * d⁻¹ := by group
              _ = d⁻¹ * (d * d') * d⁻¹ := by rw [hdd]
              _ = d' * d⁻¹ := by group]
      _ = d⁻¹ := by group
  have key : ⁅d * l, d' * l'⁆ =
      (d * (l * (d' * (l' * l⁻¹) * d'⁻¹)) * d⁻¹) * (d' * l'⁻¹ * d'⁻¹) := by
    rw [commutatorElement_def]
    calc d * l * (d' * l') * (d * l)⁻¹ * (d' * l')⁻¹
        = d * l * d' * l' * l⁻¹ * (d'⁻¹ * d⁻¹ * d') * l'⁻¹ * d'⁻¹ := by rw [e1]; group
      _ = (d * (l * (d' * (l' * l⁻¹) * d'⁻¹)) * d⁻¹) * (d' * l'⁻¹ * d'⁻¹) := by group
  rw [key]
  exact mul_mem (hconj b _ hu) hv

theorem odd_card_units_of_charTwo [Finite K] [CharP K 2] : Odd (Nat.card Kˣ) := by
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ Nat.card Kˣ := Nat.dvd_of_mod_eq_zero (by omega)
  have := Fact.mk Nat.prime_two
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 2 h2
  have hu2 : ((u : K)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    exact congrArg Units.val this |>.trans Units.val_one
  have hu1 : (u : K) = 1 := eq_one_of_sq_eq_one hu2
  have : u = 1 := Units.ext hu1
  rw [this, orderOf_one] at hu
  exact absurd hu (by norm_num)

theorem mem_leviRoot_of_orderOf
    [Finite K] [CharP K 2] {A : Set (Fin τ.rank)} {x : ModGL τ K}
    (hx : x ∈ parabolicLevi τ K A) {e : ℕ} (hxe : orderOf x = 2 ^ e) : x ∈ leviRoot K A := by
  obtain ⟨b, l, hl, rfl⟩ := exists_eq_rootDiagUnit_mul hx
  set d := rootDiagUnit τ b with hd
  have hconj : ∀ z ∈ leviRoot K A, d⁻¹ * z * d⁻¹⁻¹ ∈ leviRoot K A := fun z hz => by
    have h := (mem_normalizer_iff.1 (rootDiagUnit_mem_normalizer b⁻¹ A) z).1 hz
    rw [inv_inv]
    rwa [← CFSG.LieType.Chevalley.rootDiagUnit_inv, ← hd, inv_inv] at h
  have hpow : ∀ n : ℕ, d⁻¹ ^ n * (d * l) ^ n ∈ leviRoot K A := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e2 : d⁻¹ ^ (n + 1) * (d * l) ^ (n + 1) =
          (d⁻¹ * (d⁻¹ ^ n * (d * l) ^ n) * d⁻¹⁻¹) * l := by
        rw [pow_succ', pow_succ]
        group
      rw [e2]
      exact mul_mem (hconj _ ih) hl
  set m := Nat.card Kˣ with hm
  have hdm : d ^ m = 1 := by
    change rootDiagUnitHom τ K b ^ m = 1
    rw [← map_pow, show b ^ m = 1 by
      funext i
      exact pow_card_eq_one', map_one]
  have hxm : (d * l) ^ m ∈ leviRoot K A := by
    have h := hpow m
    rwa [inv_pow, hdm, inv_one, one_mul] at h
  have hcop : m.Coprime (orderOf (d * l)) := by
    rw [hxe]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 odd_card_units_of_charTwo)
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hk]
  exact pow_mem hxm k

end LeviRoot

theorem eq_bot_of_injective_sl2 {G : Type*} [Group G] {K : Type*} [Field K] [Finite K]
    [CharP K 2] {H : Subgroup G} (ι : H →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hι : Function.Injective ι) {R T : Subgroup G} (hRH : R ≤ H) (hTR : T ≤ R)
    (hR : ⁅R, R⁆ = R) (hT2 : IsPGroup 2 T) (hRT : ∀ r ∈ R, ∀ t ∈ T, r * t * r⁻¹ ∈ T) :
    T = ⊥ := by
  set R' := (R.subgroupOf H).map ι with hR'
  set T' := (T.subgroupOf H).map ι with hT'
  have h1 : ⁅R.subgroupOf H, R.subgroupOf H⁆ = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hRH, hR]
  have hR'p : ⁅R', R'⁆ = R' := by rw [hR', ← map_commutator, h1]
  have hT'2 : IsPGroup 2 T' := (hT2.comap_subtype (K := H)).map _
  have hRT' : ∀ g ∈ R', ∀ t ∈ T', g * t * g⁻¹ ∈ T' := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hr ht
    refine ⟨r * t * r⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_subgroupOf]
    simpa using hRT _ hr _ ht
  by_contra hT
  have hT' : T' ≠ ⊥ := by
    intro hbot
    apply hT
    rw [eq_bot_iff]
    intro x hx
    have hxT : ι ⟨x, hRH (hTR hx)⟩ ∈ T' := ⟨⟨x, hRH (hTR hx)⟩, mem_subgroupOf.2 hx, rfl⟩
    rw [hbot, mem_bot, ← map_one ι] at hxT
    have := congrArg Subtype.val (hι hxT)
    rw [mem_bot]
    exact this
  have hRbot := sl2_eq_bot_of_perfect_of_normalizes R' T' hR'p hT'2 hRT' hT'
  apply hT'
  rw [eq_bot_iff, ← hRbot]
  exact map_mono fun x hx => mem_subgroupOf.2 (hTR (mem_subgroupOf.1 hx))

local notation "ν" n:max => (⟨n, by decide⟩ : Fin TwistTag.D4.tag.rank)

theorem orbitUnion_subset_of_ne_univ {J : Set (Fin TwistTag.D4.foldedTag.rank)}
    (hJ : J ≠ Set.univ) :
    TwistTag.D4.orbitUnion J ⊆ {ν 2} ∨ TwistTag.D4.orbitUnion J ⊆ outerSet := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  have horb₀ : ∀ i : Fin TwistTag.D4.tag.rank, i ∈ TwistTag.D4.orbit ⟨0, by decide⟩ →
      i = ν 0 ∨ i = ν 1 ∨ i = ν 3 := by decide
  have horb₁ : ∀ i : Fin TwistTag.D4.tag.rank, i ∈ TwistTag.D4.orbit ⟨1, by decide⟩ →
      i = ν 2 := by decide
  fin_cases a
  · left
    intro i hi
    obtain ⟨c, hcJ, hic⟩ := (TwistTag.mem_orbitUnion _).1 hi
    fin_cases c
    · exact absurd hcJ ha
    · exact horb₁ i hic
  · right
    intro i hi
    obtain ⟨c, hcJ, hic⟩ := (TwistTag.mem_orbitUnion _).1 hi
    fin_cases c
    · exact horb₀ i hic
    · exact absurd hcJ ha

theorem exists_graphFixedParabolic_proj
    {K : Type} [Field K] (σ : K ≃+* K) (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    ∃ hLP : graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J ≤
        graphFixedParabolic TwistTag.D4 K σ.toRingHom J,
      ∃ p : graphFixedParabolic TwistTag.D4 K σ.toRingHom J →*
          graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J,
        (∀ x, p x = 1 ↔ (x : ModGL TwistTag.D4.tag K) ∈
          graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J) ∧
        ∀ l, p (inclusion hLP l) = l := by
  obtain ⟨-, -, -, -, -, -, hQL, -, hQP, hQn, hLP, huniq, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ J
  set P := graphFixedParabolic TwistTag.D4 K σ.toRingHom J
  set Q := graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J
  set L := graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J
  have hC : (P : Set (ModGL TwistTag.D4.tag K)) =
      (Q : Set (ModGL TwistTag.D4.tag K)) * (L : Set (ModGL TwistTag.D4.tag K)) := by
    ext g
    constructor
    · intro hg
      obtain ⟨qm, ⟨hq, hm, rfl⟩, -⟩ := huniq g hg
      exact ⟨qm.1, hq, qm.2, hm, rfl⟩
    · rintro ⟨q, hq, m, hm, rfl⟩
      exact mul_mem (hQP hq) (hLP hm)
  have hQn' : ∀ c ∈ P, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun c hc q hq => by
    have h := hQn.conj_mem ⟨q, hQP hq⟩ (mem_subgroupOf.2 hq) ⟨c, hc⟩
    exact mem_subgroupOf.1 h
  have hQL' : Q ⊓ L = ⊥ := eq_bot_iff.2 fun g hg => by
    rw [← hQL]
    exact mem_inf.2 ⟨(mem_inf.1 hg).1, mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hg).2).1,
      graphFixedRootGroup_le _ _ _ (mem_inf.1 (mem_inf.1 hg).2).2⟩⟩
  obtain ⟨p, hp, hpl⟩ := exists_proj_of_mul_eq hC hLP hQn' hQL'
  exact ⟨hLP, p, hp, hpl⟩

theorem projImage_le_leviRoot
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    {J : Set (Fin TwistTag.D4.foldedTag.rank)}
    (p : graphFixedParabolic TwistTag.D4 K σ.toRingHom J →*
      graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J)
    {R T : Subgroup (ModGL TwistTag.D4.tag K)}
    (hRP : R ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom J) (hR : ⁅R, R⁆ = R)
    (hT2 : IsPGroup 2 T) :
    projImage p R ≤ leviRoot K (TwistTag.D4.orbitUnion J) ∧
      projImage p T ≤ leviRoot K (TwistTag.D4.orbitUnion J) := by
  have hLM : graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J ≤
      parabolicLevi TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) := inf_le_left
  refine ⟨?_, fun x hx => ?_⟩
  · rw [← projImage_perfect p hRP hR]
    exact (commutator_mono ((projImage_le p R).trans hLM) ((projImage_le p R).trans hLM)).trans
      (commutator_parabolicLevi_le_leviRoot _)
  · have := Fact.mk Nat.prime_two
    obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.1 (projImage_isPGroup p hT2)) ⟨x, hx⟩
    rw [orderOf_mk] at he
    exact mem_leviRoot_of_orderOf (hLM (projImage_le p T hx)) he

theorem le_graphFixedParabolicRadical_of_perfect
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ)
    {R T : Subgroup (ModGL TwistTag.D4.tag K)}
    (hRP : R ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom J) (hTR : T ≤ R)
    (hR : ⁅R, R⁆ = R) (hT2 : IsPGroup 2 T) (hRT : ∀ r ∈ R, ∀ t ∈ T, r * t * r⁻¹ ∈ T) :
    T ≤ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J := by
  obtain ⟨-, p, hp, -⟩ := exists_graphFixedParabolic_proj σ J
  obtain ⟨hRA, hTA⟩ := projImage_le_leviRoot σ p hRP hR hT2
  have hTR' := projImage_mono p hTR
  have hR' := projImage_perfect p hRP hR
  have hT2' := projImage_isPGroup p hT2
  have hRT' := projImage_conj_mem p hRT
  have hLΓ : ∀ H : Subgroup (ModGL TwistTag.D4.tag K), projImage p H ≤
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := fun H =>
    (projImage_le p H).trans (inf_le_right.trans (graphFixedRootGroup_le _ _ _))
  refine le_of_projImage_eq_bot p hp ((hTR.trans hRP)) ?_
  rcases orbitUnion_subset_of_ne_univ hJ with hA | hA
  ·
    have hle : leviRoot K (TwistTag.D4.orbitUnion J) ≤
        (rankOneHom TwistTag.D4 K (ν 2)).range := by
      rw [rankOneHom_range, ← leviRoot_singleton]
      exact leviRoot_mono hA
    exact eq_bot_of_injective_sl2
      (MonoidHom.ofInjective (rankOneHom_injective K (ν 2))).symm.toMonoidHom
      (MulEquiv.injective _) (hRA.trans hle) hTR' hR' hT2' hRT'
  ·
    have hle : projImage p R ≤ leviRoot K outerSet ⊓
        twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
      le_inf (hRA.trans (leviRoot_mono hA)) (hLΓ R)
    exact eq_bot_of_injective_sl2 (outerFirst K σ.toRingHom)
      (outerFirst_injective K σ.toRingHom) hle hTR' hR' hT2' hRT'

end CFSG.LargeExtraspecial.S8
