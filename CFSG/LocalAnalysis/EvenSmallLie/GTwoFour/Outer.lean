module

public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Inner
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.CanonicalLifts

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.GTwoFour

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.Chevalley.G2FieldFour
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

@[expose] noncomputable def frobEquiv (K : Type) [Field K] [Finite K] [CharP K 2] : K ≃+* K :=
  RingEquiv.ofBijective (frobenius K 2)
    ⟨(frobenius K 2).injective, Finite.surjective_of_injective (frobenius K 2).injective⟩

theorem frobEquiv_apply (K : Type) [Field K] [Finite K] [CharP K 2] (c : K) :
    frobEquiv K c = c ^ 2 :=
  frobenius_def 2 c

theorem fix_commutator {M X : Type*} [Group M] [Group X] {π : M →* X}
    (hker : ∀ k, π k = 1 → k ∈ center M) (κ : M ≃* M) {Q : Subgroup M}
    (hQ : ∀ q ∈ Q, π (κ q) = π q) : ∀ d ∈ ⁅Q, Q⁆, κ d = d := by
  have hle : ⁅Q, Q⁆ ≤ MonoidHom.eqLocus κ.toMonoidHom (MonoidHom.id M) := by
    rw [commutator_le]
    intro a ha b hb
    change κ ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement]
    exact LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq π hker (hQ a ha) (hQ b hb)
  exact fun d hd => hle hd

theorem commutator_commutator_comap {M X : Type*} [Group M] [Group X] {π : M →* X}
    (hπ : Function.Surjective π) (hker : ∀ k, π k = 1 → k ∈ center M) {Z : Subgroup X}
    (hZ : ⁅Z, Z⁆ = Z) :
    ⁅⁅Z.comap π, Z.comap π⁆, ⁅Z.comap π, Z.comap π⁆⁆ = ⁅Z.comap π, Z.comap π⁆ := by
  set D := ⁅Z.comap π, Z.comap π⁆ with hD
  have hDmap : D.map π = Z := by
    rw [hD, map_commutator, map_comap_eq_self_of_surjective hπ, hZ]
  refine le_antisymm (commutator_le_self _) ?_
  rw [hD, commutator_le]
  intro a ha b hb
  have ha' : π a ∈ D.map π := hDmap ▸ ha
  have hb' : π b ∈ D.map π := hDmap ▸ hb
  obtain ⟨a', ha'D, ha'a⟩ := ha'
  obtain ⟨b', hb'D, hb'b⟩ := hb'
  rw [LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq π hker ha'a.symm hb'b.symm]
  exact commutator_mem_commutator ha'D hb'D

namespace SeitzSetup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  (S : SeitzSetup G L K)

@[expose] noncomputable def conjL {y : G} (hy : y ∈ centralizer ({S.t} : Set G)) : L ≃* L where
  toFun m := ⟨y * m * y⁻¹, S.conj_mem_L hy m.2⟩
  invFun m := ⟨y⁻¹ * m * y⁻¹⁻¹, S.conj_mem_L (inv_mem hy) m.2⟩
  left_inv m := Subtype.ext (by simp only; group)
  right_inv m := Subtype.ext (by simp only; group)
  map_mul' m m' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjL {y : G} (hy : y ∈ centralizer ({S.t} : Set G)) (m : L) :
    ((S.conjL hy m : L) : G) = y * m * y⁻¹ := rfl

variable [CharP K 2]

theorem mem_sup_of_isConj
    {y : G} (hyt : y ∈ centralizer ({S.t} : Set G)) (hy : IsConj S.t y) :
    y ∈ L ⊔ centralizer (L : Set G) := by
  have := S.finite_field
  have := S.isPerfect
  by_contra hyLR
  obtain ⟨c, hc⟩ := isConj_iff.1 hy
  have hy2 : y * y = 1 := by
    rw [← hc, show c * S.t * c⁻¹ * (c * S.t * c⁻¹) = c * (S.t * S.t) * c⁻¹ by group, S.t_mul_t,
      mul_one, mul_inv_cancel]
  set yC : centralizer ({S.t} : Set G) := ⟨y, hyt⟩ with hyC
  set α := S.act yC with hα
  have hout : α ∉ inner (adjointGroup .G2 K) := fun h => hyLR ((S.act_mem_inner_iff yC).1 h)
  have hα2 : α * α = 1 := by
    rw [hα, ← map_mul, show yC * yC = 1 from Subtype.ext hy2, map_one]
  have hα1 : α ≠ 1 := fun h => hout (h ▸ one_mem _)
  have hαord : orderOf α = 2 := orderOf_eq_prime (by rw [sq, hα2]) hα1
  set σ := frobEquiv K with hσdef
  have hσ : ∀ c, σ c = c ^ 2 := frobEquiv_apply K
  obtain ⟨x, hx⟩ := exists_conj_eq_frobenius S.card_field σ.toRingHom hσ hαord hout
  obtain ⟨l, hl⟩ := S.π_surjective x
  set y₁ := (l : G) * y * (l : G)⁻¹ with hy₁
  have hy₁t : y₁ ∈ centralizer ({S.t} : Set G) :=
    mul_mem (mul_mem (S.le_centralizer_t l.2) hyt) (inv_mem (S.le_centralizer_t l.2))
  have hact : S.act ⟨y₁, hy₁t⟩ = MulAut.conj x * α * (MulAut.conj x)⁻¹ := by
    have hyl : (⟨y₁, hy₁t⟩ : centralizer ({S.t} : Set G)) =
        ⟨l, S.le_centralizer_t l.2⟩ * yC * (⟨l, S.le_centralizer_t l.2⟩)⁻¹ := Subtype.ext rfl
    rw [hyl, map_mul, map_mul, map_inv, S.act_of_mem l, hl]
  have hπy₁ : ∀ m : L, (S.π (S.conjL hy₁t m) : ModGL .G2 K) =
      Units.map (entrywiseHom σ.toRingHom) (S.π m) := fun m => by
    have h := S.act_π ⟨y₁, hy₁t⟩ m (S.conj_mem_L hy₁t m.2)
    rw [hact] at h
    rw [← hx (S.π m), h]
    rfl
  have hy₁2 : y₁ * y₁ = 1 := by
    rw [hy₁, show (l : G) * y * (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) =
      (l : G) * (y * y) * (l : G)⁻¹ by group, hy2, mul_one, mul_inv_cancel]
  have hy₁inv : y₁⁻¹ = y₁ := inv_eq_of_mul_eq_one_right hy₁2
  set κ := S.conjL hy₁t with hκ
  have hκ2 : ∀ m, κ (κ m) = m := fun m => Subtype.ext (by
    rw [hκ, coe_conjL, coe_conjL, hy₁inv]
    calc y₁ * (y₁ * (m : G) * y₁) * y₁ = (y₁ * y₁) * m * (y₁ * y₁) := by group
      _ = m := by rw [hy₁2, one_mul, mul_one])
  obtain ⟨Ĉ, hĈπ, hĈadd, hĈcomm, hĈκ⟩ := exists_canonical_lifts S.card_field S.π_surjective
    S.ker_le_center S.tL_ne_one S.π_eq_one_iff_tL
  have hκC : ∀ s, κ (Ĉ s) = Ĉ (s ^ 2) := hĈκ σ hσ κ hπy₁ hκ2
  obtain ⟨ω, -, -, hωsq⟩ := exists_unit_ne_one (K := K) S.card_field
  have hC0 : Ĉ 0 = 1 := by
    have h := hĈadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hCinv : ∀ s, (Ĉ s)⁻¹ = Ĉ s := fun s =>
    inv_eq_of_mul_eq_one_right (by rw [← hĈadd, CharTwo.add_self_eq_zero, hC0])
  have h1ω : (ω : K) + (ω : K) ^ 2 = 1 := by
    linear_combination hωsq - CharTwo.two_eq_zero (R := K)
  have hκx : y₁ * ((Ĉ ω : L) : G) * y₁⁻¹ = ((Ĉ ((ω : K) ^ 2) : L) : G) :=
    congrArg Subtype.val (hκC ω)
  have hconj : ((Ĉ ω : L) : G) * y₁ * ((Ĉ ω : L) : G)⁻¹ = ((Ĉ 1 : L) : G) * y₁ := by
    calc ((Ĉ ω : L) : G) * y₁ * ((Ĉ ω : L) : G)⁻¹
        = ((Ĉ ω : L) : G) * (y₁ * ((Ĉ ω : L) : G) * y₁⁻¹)⁻¹ * y₁ := by group
      _ = ((Ĉ ω : L) : G) * ((Ĉ ((ω : K) ^ 2) : L) : G)⁻¹ * y₁ := by rw [hκx]
      _ = ((Ĉ ω : L) : G) * ((Ĉ ((ω : K) ^ 2) : L) : G) * y₁ := by
          rw [← Subgroup.coe_inv, hCinv]
      _ = ((Ĉ 1 : L) : G) * y₁ := by rw [← Subgroup.coe_mul, ← hĈadd, h1ω]
  set S₂X := (longF2 K).subgroupOf (adjointGroup .G2 K) with hS₂X
  have hS₂perf : ⁅S₂X, S₂X⁆ = S₂X :=
    commutator_subgroupOf_eq longF2_le_adjointGroup commutator_longF2
  set Q := S₂X.comap S.π with hQ
  obtain ⟨ea, hea⟩ := S.π_surjective (rootX rootA 1)
  obtain ⟨eb, heb⟩ := S.π_surjective (rootX rootB 1)
  have heaQ : ea ∈ Q := by
    rw [hQ, mem_comap, hea]
    exact mem_subgroupOf.2 (pinnedX_mem_longF2 g2a_mem_g2LongRoots)
  have hebQ : eb ∈ Q := by
    rw [hQ, mem_comap, heb]
    exact mem_subgroupOf.2 (pinnedX_mem_longF2 g2b_mem_g2LongRoots)
  have heD : Ĉ 1 ∈ ⁅Q, Q⁆ := by
    rw [← hĈcomm ea eb hea heb]
    exact commutator_mem_commutator heaQ hebQ
  have hDperf : ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆ = ⁅Q, Q⁆ :=
    commutator_commutator_comap S.π_surjective S.ker_le_center hS₂perf
  have hκQ : ∀ q ∈ Q, S.π (κ q) = S.π q := fun q hq => Subtype.ext (by
    rw [hπy₁ q]
    exact entrywise_eq_of_mem_longF2 σ (mem_subgroupOf.1 (mem_comap.1 hq)))
  have hDfix : ∀ d ∈ ⁅Q, Q⁆, κ d = d := fix_commutator S.ker_le_center κ hκQ
  set c₁ := (l : G) * c with hc₁
  have hc₁t : c₁ * S.t * c₁⁻¹ = y₁ := by rw [hc₁, hy₁, ← hc]; group
  set DG := (⁅Q, Q⁆.map L.subtype).map (MulAut.conj c₁⁻¹).toMonoidHom with hDG
  have hDGperf : ⁅DG, DG⁆ = DG := by
    rw [hDG, ← map_commutator, ← map_commutator, hDperf]
  have hDGt : DG ≤ centralizer {S.t} := by
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h : y₁ * (d : G) * y₁⁻¹ = d := congrArg Subtype.val (hDfix d hd)
    have h' : (d : G) * y₁ = y₁ * d := by
      calc (d : G) * y₁ = y₁ * d * y₁⁻¹ * y₁ := by rw [h]
        _ = y₁ * d := by group
    change c₁⁻¹ * (d : G) * c₁⁻¹⁻¹ * S.t = S.t * (c₁⁻¹ * d * c₁⁻¹⁻¹)
    rw [inv_inv]
    calc c₁⁻¹ * (d : G) * c₁ * S.t = c₁⁻¹ * ((d : G) * (c₁ * S.t * c₁⁻¹)) * c₁ := by group
      _ = c₁⁻¹ * ((c₁ * S.t * c₁⁻¹) * d) * c₁ := by rw [hc₁t, h']
      _ = S.t * (c₁⁻¹ * d * c₁) := by group
  have he₁ : c₁⁻¹ * ((Ĉ 1 : L) : G) * c₁ ∈ L := by
    have hmem : (MulAut.conj c₁⁻¹).toMonoidHom (L.subtype (Ĉ 1)) ∈ DG :=
      ⟨_, ⟨Ĉ 1, heD, rfl⟩, rfl⟩
    have hpow : ((MulAut.conj c₁⁻¹).toMonoidHom (L.subtype (Ĉ 1))) ^ (2 ^ 1) = 1 := by
      rw [← map_pow, ← map_pow, pow_one, sq, ← hĈadd, CharTwo.add_self_eq_zero, hC0, map_one,
        map_one]
    have h := S.mem_L_of_perfect hDGt hDGperf hmem hpow
    simpa [MulAut.conj_apply] using h
  set w := c₁⁻¹ * (((Ĉ ω : L) : G) * y₁ * ((Ĉ ω : L) : G)⁻¹) * c₁ with hw
  have hwform : w = c₁⁻¹ * ((Ĉ 1 : L) : G) * c₁ * S.t := by
    rw [hw, hconj, ← hc₁t]; group
  have hwL : w ∈ L := by
    rw [hwform]
    exact mul_mem he₁ S.t_mem
  have hwt : IsConj S.t w :=
    isConj_iff.2 ⟨c₁⁻¹ * ((Ĉ ω : L) : G) * c₁, by rw [hw, ← hc₁t]; group⟩
  have hw' := S.eq_t_of_isConj hwL hwt
  rw [hwform] at hw'
  have he1 : c₁⁻¹ * ((Ĉ 1 : L) : G) * c₁ = 1 := mul_eq_right.1 hw'
  have he1' : ((Ĉ 1 : L) : G) = 1 := by
    have h := congrArg (fun g => c₁ * g * c₁⁻¹) he1
    simpa [mul_assoc] using h
  have h := hĈπ 1
  rw [show Ĉ 1 = 1 from Subtype.ext he1', map_one, ← rootX_zero rootC] at h
  exact one_ne_zero (rootX_injective rootC h).symm

end SeitzSetup

end CFSG.EvenSmallLie.GTwoFour
