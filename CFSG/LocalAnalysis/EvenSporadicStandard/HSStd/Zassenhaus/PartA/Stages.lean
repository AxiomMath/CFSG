module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerE1Assembly

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath Open
open scoped commutatorElement

inductive DCase
  | d8
  | e4
  deriving DecidableEq

section PAB

variable {G : Type} [Group G] [Finite G]

structure PAB (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G)
    (z : G) : Prop where
  setting : HSLemma21Setting G L
  t_cent : t ∈ centralizer (L : Set G)
  t_ord : orderOf t = 2
  inner : centralizer ({t} : Set G) = L ⊔ zpowers t
  E_le : E ≤ L
  z_mem : z ∈ E
  z_class : Nat.card ↥(L ⊓ Cen z) = 7680
  E_ab : IsElemAbelian 2 E
  E_card : Nat.card E = 16
  E_S6 : ∃ φ : ↥(normalizer (E : Set G) ⊓ L) →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
    φ.ker = E.subgroupOf (normalizer (E : Set G) ⊓ L)
  E_trans : ∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e
  E_fuse : ∀ e ∈ E, ∃ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), m * t * m⁻¹ = t * e
  W_inv : ∀ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), ∀ w ∈ W, m * w * m⁻¹ ∈ W
  W_le : W ≤ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)
  E_le_W : E ≤ W
  t_nmem_W : t ∉ W
  W_ab : IsElemAbelian 2 W
  W_card : Nat.card W = 256
  N_card : Nat.card (normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)) = 16 * 23040
  cent_tE : centralizer ((zpowers t ⊔ E : Subgroup G) : Set G) = zpowers t ⊔ E

theorem PAB.of_hyps
    {L : Subgroup G} (hset : HSLemma21Setting G L) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n) {E : Subgroup G} (hEL : E ≤ L) (hzE : z ∈ E)
    (hEab : IsElemAbelian 2 E) (hE16 : Nat.card E = 16)
    (hφ : ∃ φ : ↥(normalizer (E : Set G) ⊓ L) →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
      φ.ker = E.subgroupOf (normalizer (E : Set G) ⊓ L))
    (htr : ∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e)
    (hfus : ∀ e ∈ E, ∃ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G),
      m * t * m⁻¹ = t * e)
    {W : Subgroup G} (hWN : W ≤ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G))
    (hWn : ∀ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), ∀ w ∈ W, m * w * m⁻¹ ∈ W)
    (hEW : E ≤ W) (htW : t ∉ W) (hWab : IsElemAbelian 2 W) (hW : Nat.card W = 256)
    (hN : Nat.card (normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)) = 16 * 23040)
    (hC : centralizer ((zpowers t ⊔ E : Subgroup G) : Set G) = zpowers t ⊔ E) :
    PAB G L t E W z where
  setting := hset
  t_cent := htL
  t_ord := ht2
  inner := hin
  E_le := hEL
  z_mem := hzE
  z_class := card_inf_centralizer_z hset.2.1 htL ht2 hin hf
  E_ab := hEab
  E_card := hE16
  E_S6 := hφ
  E_trans := htr
  E_fuse := hfus
  W_inv := hWn
  W_le := hWN
  E_le_W := hEW
  t_nmem_W := htW
  W_ab := hWab
  W_card := hW
  N_card := hN
  cent_tE := hC

theorem PAB.t_mul_t {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G} (hb : PAB G L t E W z) :
    t * t = 1 := by
  have := pow_orderOf_eq_one t
  rw [hb.t_ord, pow_two] at this
  exact this

end PAB

section Stages

variable {G : Type} [Group G] [Finite G]

structure PA0 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) where
  y : G
  u : G
  K₀ : Subgroup G
  Abar : Subgroup G
  eK₀ : ↥K₀ ≃* Equiv.Perm (Fin 5)
  eAbar : ↥Abar ≃* MulAut (alternatingGroup (Fin 6))
  y_mem : y ∈ normalizer (E : Set G) ⊓ L
  y_ord : orderOf y = 3
  zy : y * z = z * y
  card_Ey : Nat.card ↥(E ⊓ Cen y) = 4
  K₀_le : K₀ ≤ L ⊓ Cen y
  K₀_y : L ⊓ Cen y = zpowers y ⊔ K₀
  K₀_disj : Disjoint (zpowers y) K₀
  u_mem : u ∈ K₀
  u_swap : (eK₀ ⟨u, u_mem⟩).IsSwap
  card_Lu : Nat.card ↥(L ⊓ Cen u) = 2880
  Abar_le : Abar ≤ L ⊓ Cen u
  Abar_comp : L ⊓ Cen u = zpowers u ⊔ Abar
  Abar_disj : Disjoint (zpowers u) Abar
  y_J : y ∈ derivedIn Abar
  C_L_J : L ⊓ centralizer ((derivedIn Abar : Subgroup G) : Set G) = zpowers u
  tab_inner : ∀ x (hx : x ∈ Abar), x * x = 1 → x ≠ 1 → eAbar ⟨x, hx⟩ ∈ innR →
    Nat.card ↥(L ⊓ Cen x) = 7680 ∧ Nat.card ↥(L ⊓ Cen (u * x)) = 2880
  tab_S6 : ∀ x (hx : x ∈ Abar), x * x = 1 → x ≠ 1 → eAbar ⟨x, hx⟩ ∉ innR →
    (∃ a : alternatingGroup (Fin 6), orderOf a = 3 ∧ eAbar ⟨x, hx⟩ a = a) →
    (Nat.card ↥(L ⊓ Cen x) = 7680 ∧ Nat.card ↥(L ⊓ Cen (u * x)) = 2880) ∨
      (Nat.card ↥(L ⊓ Cen x) = 2880 ∧ Nat.card ↥(L ⊓ Cen (u * x)) = 7680)
  tab_PGL : ∀ x (hx : x ∈ Abar), x * x = 1 → x ≠ 1 → eAbar ⟨x, hx⟩ ∉ innR →
    (∀ a : alternatingGroup (Fin 6), orderOf a = 3 → eAbar ⟨x, hx⟩ a ≠ a) →
    Nat.card ↥(L ⊓ Cen x) = 2880 ∧ Nat.card ↥(L ⊓ Cen (u * x)) = 2880

structure PA2 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA0 L t E z where
  t_cy : t ∈ Cen y
  y_O : y ∈ fusionOddCoreOf (Cen y)
  O_cent_t : fusionOddCoreOf (Cen y) ⊓ Cen t = zpowers y
  O_inv : ∀ o ∈ fusionOddCoreOf (Cen y), t * o * t⁻¹ * o ∈ zpowers y
  O_comm : ∀ o₁ ∈ fusionOddCoreOf (Cen y), ∀ o₂ ∈ fusionOddCoreOf (Cen y),
    ⁅o₁, o₂⁆ ∈ zpowers y
  oddcore_D : fusionOddCore (OQuot (Cen y)) = ⊥
  zstar_D : fusionZStar (OQuot (Cen y)) = ⊥
  Kbar_cent : centralizer ({oMk (Cen y) ⟨t, t_cy⟩} : Set (OQuot (Cen y))) =
    zpowers (oMk (Cen y) ⟨t, t_cy⟩) ⊔ (K₀.subgroupOf (Cen y)).map (oMk (Cen y))
  Kbar_disj : Disjoint (zpowers (oMk (Cen y) ⟨t, t_cy⟩))
    ((K₀.subgroupOf (Cen y)).map (oMk (Cen y)))
  Kbar_card : Nat.card ↥((K₀.subgroupOf (Cen y)).map (oMk (Cen y))) = 120
  rank4_D : ∃ A : Subgroup (OQuot (Cen y)), IsElemAbelian 2 A ∧ Nat.card A = 16

structure PA3 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA2 L t E z where
  ι : OQuot (Cen y) →* Wr2 (Equiv.Perm (Fin 5))
  ι_inj : Function.Injective ι
  ι_t : ι (oMk (Cen y) ⟨t, t_cy⟩) = tau
  ι_alt : ∀ a b : alternatingGroup (Fin 5),
    base (a : Equiv.Perm (Fin 5)) (b : Equiv.Perm (Fin 5)) ∈ ι.range
  ι_range : ι.range = ⊤ ∨ ι.range = DE4
  ι_u : ∃ σ : Equiv.Perm (Fin 5), σ.IsSwap ∧
    (ι (oMk (Cen y) ⟨u, (K₀_le u_mem).2⟩) = base σ σ ∨
      ι (oMk (Cen y) ⟨u, (K₀_le u_mem).2⟩) = base σ σ * tau)

structure PA4 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA3 L t E z where
  K₁ : Subgroup G
  eK₁ : ↥K₁ ≃* alternatingGroup (Fin 5)
  K₁_le : K₁ ≤ Cen y
  K₁_O : Cm K₁ (fusionOddCoreOf (Cen y))
  K₁_K₁t : Cm K₁ (conjSub t K₁)
  K₁_inf : K₁ ⊓ conjSub t K₁ = ⊥
  K₁_ι : ∀ a (ha : a ∈ K₁), ∃ σ : alternatingGroup (Fin 5),
    ι (oMk (Cen y) ⟨a, K₁_le ha⟩) = base (σ : Equiv.Perm (Fin 5)) 1
  K₁_onto : ∀ σ : alternatingGroup (Fin 5), ∃ a, ∃ ha : a ∈ K₁,
    ι (oMk (Cen y) ⟨a, K₁_le ha⟩) = base (σ : Equiv.Perm (Fin 5)) 1
  P₁_eq : {g | ∃ hg : g ∈ Cen y, ∃ a b : alternatingGroup (Fin 5),
      ι (oMk (Cen y) ⟨g, hg⟩) = base (a : Equiv.Perm (Fin 5)) (b : Equiv.Perm (Fin 5))} ⊆
    ((fusionOddCoreOf (Cen y) ⊔ K₁ ⊔ conjSub t K₁ : Subgroup G) : Set G)
  O_inf : fusionOddCoreOf (Cen y) ⊓ (K₁ ⊔ conjSub t K₁) = ⊥

structure PA5 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA4 L t E z where
  ub : G
  ub_cases : ub = u ∨ ub = t * u
  ub_ord : orderOf ub = 2
  ub_cy : ub ∈ Cen y
  ub_base : ∃ σ : Equiv.Perm (Fin 5), σ.IsSwap ∧ ι (oMk (Cen y) ⟨ub, ub_cy⟩) = base σ σ
  ub_nconj : ¬ IsConj t ub
  dcase : DCase
  dcase_iff : dcase = DCase.d8 ↔ ι.range = ⊤
  F₀ : Subgroup G
  u₁ : G
  F₀_e4 : dcase = DCase.e4 → F₀ = zpowers ub ∧ ¬ IsConj t (t * ub)
  d8_props : dcase = DCase.d8 → orderOf u₁ = 2 ∧ u₁ ∈ Cen ub ∧
    u₁ ∈ centralizer ((derivedIn Abar : Subgroup G) : Set G) ∧ t * u₁ * t⁻¹ = ub * u₁ ∧
    F₀ = zpowers ub ⊔ zpowers u₁ ∧ u₁ ∉ zpowers ub ∧
    ∃ σ : Equiv.Perm (Fin 5), σ.IsSwap ∧ ∃ hc : u₁ ∈ Cen y,
      (ι (oMk (Cen y) ⟨u₁, hc⟩) = base σ 1 ∨ ι (oMk (Cen y) ⟨u₁, hc⟩) = base 1 σ)
  F₀_card : dcase = DCase.d8 → Nat.card F₀ = 4

structure PA6 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA5 L t E z where
  Z_solv : Group.IsSolvable ↥(centralizer ((derivedIn Abar : Subgroup G) : Set G))
  Z_two : (Nat.card ↥(centralizer ((derivedIn Abar : Subgroup G) : Set G))).factorization 2 ≤ 3
  F_card : Nat.card ↥(pCoreOf 2 (Cen ub)) ≤ (if dcase = DCase.d8 then 4 else 2)
  ub_F : ub ∈ pCoreOf 2 (Cen ub)
  J_F : derivedIn Abar ≤ centralizer ((pCoreOf 2 (Cen ub) : Subgroup G) : Set G)
  CPE : Cen ub ⊓ centralizer ((GorensteinWalter.componentLayerOf (Cen ub) : Subgroup G) : Set G) ≤
    pCoreOf 2 (Cen ub)

structure PA7 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA6 L t E z where
  E₁ : Subgroup G
  E₁_le : E₁ ≤ GorensteinWalter.componentLayerOf (Cen ub)
  E₁_perf : ⁅E₁, E₁⁆ = E₁
  J_E₁ : derivedIn Abar ≤ E₁
  E₁_cent_F₀ : E₁ ≤ centralizer (F₀ : Set G)
  E₁_cover : ∃ f : ↥E₁ →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6),
    Function.Surjective f ∧ f.ker ≤ center ↥E₁
  E₁_swap : conjSub t E₁ = E₁
  M₁ : Subgroup G
  M₁_le : M₁ ≤ E₁
  M₁_perf : ⁅M₁, M₁⁆ = M₁
  M₁_cover : ∃ f : ↥M₁ →* alternatingGroup (Fin 6), Function.Surjective f ∧ f.ker ≤ center ↥M₁
  M₁_comm : ∀ a ∈ M₁, ∀ b ∈ M₁, Commute a (t * b * t⁻¹)

structure PA8 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA7 L t E z where
  L₁ : Subgroup G
  L₁_comp : GorensteinWalter.IsComponentOf L₁ (Cen ub)
  L₁_ne : conjSub t L₁ ≠ L₁
  L₁_comm : ∀ a ∈ L₁, ∀ b ∈ L₁, Commute a (t * b * t⁻¹)
  E_eq : GorensteinWalter.componentLayerOf (Cen ub) = L₁ ⊔ conjSub t L₁
  L₁_A6 : Nonempty (↥L₁ ⧸ center ↥L₁ ≃* alternatingGroup (Fin 6))
  Z_le : (center ↥L₁).map L₁.subtype ≤ zpowers ub
  perm : ∀ p ∈ Cen ub, L₁.map (MulAut.conj p).toMonoidHom = L₁ ∨
    L₁.map (MulAut.conj p).toMonoidHom = conjSub t L₁
  J_le : derivedIn Abar ≤ L₁ ⊔ conjSub t L₁
  CPE_eq : Cen ub ⊓ centralizer ((L₁ ⊔ conjSub t L₁ : Subgroup G) : Set G) = F₀
  u₁_CPE : dcase = DCase.d8 → u₁ ∈ centralizer (L₁ : Set G) ⊓
    centralizer ((conjSub t L₁ : Subgroup G) : Set G)

structure PA9 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA8 L t E z where
  ub_eq : ub = u

structure PA10 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA9 L t E z where
  d8_case : dcase = DCase.d8

structure PA11 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA10 L t E z where
  x : G
  x_mem : x ∈ L₁
  x_ord : orderOf x = 3
  x_y : y = x * (t * x * t⁻¹)
  x_O : x ∈ fusionOddCoreOf (Cen y)
  O_eq : fusionOddCoreOf (Cen y) = zpowers x ⊔ zpowers (t * x * t⁻¹)
  card_Cy : Nat.card ↥(Cen y) = 259200
  X : Subgroup G
  X_le : X ≤ L₁ ⊓ Cen x
  X_card : Nat.card X = 9
  X_three : ∀ g ∈ L₁ ⊓ Cen x, orderOf g = 3 → g ∈ X

structure PA12 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA11 L t E z where
  c₃ : G
  k : G
  c₃_K₁ : c₃ ∈ K₁
  c₃_L₁ : c₃ ∈ L₁
  c₃_ord : orderOf c₃ = 3
  c₃_x : c₃ * x = x * c₃
  c₃_nx : c₃ ∉ zpowers x
  k_K₁ : k ∈ K₁
  k_ord : orderOf k = 2
  k_u : k * u = u * k
  k_norm : k ∈ normalizer (L₁ : Set G)
  k_outer : ∀ l ∈ L₁, ∃ a ∈ L₁, k * a * k⁻¹ ≠ l * a * l⁻¹
  k_L₁t : ∀ l ∈ L₁, k * (t * l * t⁻¹) = (t * l * t⁻¹) * k
  K₁_x : ∀ a ∈ K₁, a * x = x * a
  K₁_xt : ∀ a ∈ K₁, a * (t * x * t⁻¹) = (t * x * t⁻¹) * a
  u₁_norm : u₁ ∈ normalizer (K₁ : Set G)
  u₁_S5 : Nonempty (↥(K₁ ⊔ zpowers u₁) ≃* Equiv.Perm (Fin 5))
  u₁_K₁t : ∀ b ∈ K₁, u₁ * (t * b * t⁻¹) = (t * b * t⁻¹) * u₁
  cent_x_xt : Cen x ⊓ Cen (t * x * t⁻¹) =
    (zpowers x ⊔ zpowers (t * x * t⁻¹)) ⊔ (K₁ ⊔ zpowers u₁) ⊔ conjSub t (K₁ ⊔ zpowers u₁)

structure PA14 (L : Subgroup G) (t : G) (E : Subgroup G) (z : G) extends PA12 L t E z where
  Z_triv : center ↥L₁ = ⊥
  eL₁ : ↥L₁ ≃* alternatingGroup (Fin 6)

end Stages

section Derived

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA5.comm_t_ub (hb : PAB G L t E W z) (a : PA5 L t E z) : a.ub * t = t * a.ub := by
  have hu : a.u ∈ L := (a.K₀_le a.u_mem).1
  have hut : a.u * t = t * a.u := mem_centralizer_iff.1 hb.t_cent a.u hu
  rcases a.ub_cases with h | h
  · rw [h]
    exact hut
  · rw [h]
    calc t * a.u * t = t * (a.u * t) := mul_assoc _ _ _
      _ = t * (t * a.u) := by rw [hut]

theorem PA8.pairData (hb : PAB G L t E W z) (a : PA8 L t E z) :
    PairData (Cen a.ub) a.L₁ t where
  t_mem := mem_Cen.2 (PA5.comm_t_ub hb a.toPA7.toPA6.toPA5).symm
  t_sq := hb.t_mul_t
  K_le := a.L₁_comp.1
  ne := a.L₁_ne
  comm := a.L₁_comm
  perm := a.perm

end Derived

@[expose] def StepS0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → Nonempty (PA0 L t E z)

@[expose] def StepS2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → PA0 L t E z → Nonempty (PA2 L t E z)

@[expose] def StepS3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → PA2 L t E z → Nonempty (PA3 L t E z)

@[expose] def StepS4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → PA3 L t E z → Nonempty (PA4 L t E z)

@[expose] def StepS5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → PA4 L t E z → Nonempty (PA5 L t E z)

@[expose] def StepS6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → PA5 L t E z → Nonempty (PA6 L t E z)

@[expose] def StepS7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    CFSG.EvenSporadicStandard.Induction.Balance.UHered G → PAB G L t E W z → PA6 L t E z →
      Nonempty (PA7 L t E z)

@[expose] def StepS8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → PA7 L t E z → Nonempty (PA8 L t E z)

@[expose] def StepS9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → PA8 L t E z → Nonempty (PA9 L t E z)

@[expose] def StepS10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → PA9 L t E z → Nonempty (PA10 L t E z)

@[expose] def StepS11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → PA10 L t E z → Nonempty (PA11 L t E z)

@[expose] def StepS12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → PA11 L t E z → Nonempty (PA12 L t E z)

@[expose] def StepS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → PA12 L t E z → Nonempty (PA14 L t E z)

@[expose] def StepS15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → ∀ a : PA14 L t E z, ∀ b : MulAut ↥a.L₁, b * b = 1 → b ≠ 1 →
      ∃ x ∈ L, x ∈ centralizer ({a.u} : Set G) ∧ x * x = 1 ∧
        ((∃ hx : x ∈ normalizer (a.L₁ : Set G), conjAutOf a.L₁ hx = b) ∨
          ∃ hx : x * t ∈ normalizer (a.L₁ : Set G), conjAutOf a.L₁ hx = b)

section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

omit [Finite G] in
theorem centralizer_sup_eq_inf (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) =
      centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
      (centralizer_le (SetLike.coe_subset_coe.2 le_sup_right))
  · rintro g ⟨hA, hB⟩
    have hsup : A ⊔ B ≤ centralizer ({g} : Set G) := by
      refine sup_le (fun h hh => ?_) (fun h hh => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.1 hA h hh
      · rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.1 hB h hh
    rw [mem_centralizer_iff]
    intro h hh
    exact mem_centralizer_singleton_iff.1 (hsup hh)

theorem PA14.nonempty_configC (hb : PAB G L t E W z) (a : PA14 L t E z)
    (hdiag : ∀ b : MulAut ↥a.L₁, b * b = 1 → b ≠ 1 →
      ∃ x ∈ L, x ∈ centralizer ({a.u} : Set G) ∧ x * x = 1 ∧
        ((∃ hx : x ∈ normalizer (a.L₁ : Set G), conjAutOf a.L₁ hx = b) ∨
          ∃ hx : x * t ∈ normalizer (a.L₁ : Set G), conjAutOf a.L₁ hx = b)) :
    Nonempty (InnerD8ConfigC L t) := by
  have hub : a.ub = a.u := a.ub_eq
  have hd8 : a.dcase = DCase.d8 := a.d8_case
  have huL : a.u ∈ L := (a.K₀_le a.u_mem).1
  have hut : a.u * t = t * a.u := mem_centralizer_iff.1 hb.t_cent a.u huL
  have hu2 : orderOf a.u = 2 := hub ▸ a.ub_ord
  obtain ⟨hu₁ord, hu₁Cub, -, hu₁conj, hF₀, -, -⟩ := a.d8_props hd8
  rw [hub] at hu₁Cub hu₁conj hF₀
  have hu₁sq : a.u₁ * a.u₁ = 1 := by
    have := pow_orderOf_eq_one a.u₁
    rwa [hu₁ord, pow_two] at this
  have hpair : PairData (centralizer ({a.u} : Set G)) a.L₁ t := by
    have := PA8.pairData hb a.toPA9.toPA8
    rw [hub] at this
    exact this
  have hF : centralizer ({a.u} : Set G) ⊓ centralizer (a.L₁ : Set G) ⊓
      centralizer ((conjSub t a.L₁ : Subgroup G) : Set G) = a.F₀ := by
    rw [← a.CPE_eq, centralizer_sup_eq_inf, hub, inf_assoc]
  refine ⟨
    { u := a.u
      u₁ := a.u₁
      L₁ := a.L₁
      x := a.x
      eL₁ := a.eL₁
      u_mem := huL
      u_ord := hu2
      card_centralizer_u := a.card_Lu
      pair := hpair
      u₁_mem := ⟨⟨hu₁Cub, (a.u₁_CPE hd8).1⟩, (a.u₁_CPE hd8).2⟩
      u₁_ord := hu₁ord
      u₁_conj := hu₁conj
      card_F := by rw [hF]; exact a.F₀_card hd8
      t_conj_tu := by
        refine isConj_iff.2 ⟨a.u₁, ?_⟩
        have h1 : t * a.u₁ = a.u * a.u₁ * t := by
          have := hu₁conj
          rw [mul_inv_eq_iff_eq_mul] at this
          exact this
        have h2 : a.u₁ * a.u = a.u * a.u₁ := mem_centralizer_singleton_iff.1 hu₁Cub
        calc a.u₁ * t * a.u₁⁻¹ = a.u₁ * t * a.u₁ := by
              rw [inv_eq_of_mul_eq_one_right hu₁sq]
          _ = a.u₁ * (t * a.u₁) := by rw [mul_assoc]
          _ = a.u₁ * (a.u * a.u₁ * t) := by rw [h1]
          _ = (a.u₁ * a.u) * a.u₁ * t := by simp only [mul_assoc]
          _ = (a.u * a.u₁) * a.u₁ * t := by rw [h2]
          _ = a.u * (a.u₁ * a.u₁) * t := by simp only [mul_assoc]
          _ = a.u * t := by rw [hu₁sq, mul_one]
          _ = t * a.u := hut
      diag := hdiag
      x_mem := a.x_mem
      x_ord := a.x_ord
      card_centralizer_y := by rw [← a.x_y]; exact a.card_Cy
      K₁ := a.K₁
      eK₁ := a.eK₁
      K₁_comm_x := a.K₁_x
      K₁_comm_xt := a.K₁_xt
      K₁_comm_K₁t := fun p hp q hq =>
        (mem_centralizer_iff.1 (a.K₁_K₁t hp) (t * q * t⁻¹) ⟨q, hq, rfl⟩).symm
      u₁_norm_K₁ := a.u₁_norm
      u₁_S₅ := a.u₁_S5
      u₁_comm_K₁t := a.u₁_K₁t
      centralizer_x_xt := a.cent_x_xt
      c₃ := a.c₃
      c₃_mem_K₁ := a.c₃_K₁
      c₃_mem_L₁ := a.c₃_L₁
      c₃_ord := a.c₃_ord
      c₃_comm_x := a.c₃_x
      c₃_not_mem := a.c₃_nx
      k := a.k
      k_mem := a.k_K₁
      k_ord := a.k_ord
      k_comm_u := a.k_u
      k_norm := a.k_norm
      k_outer := by
        intro l hl
        obtain ⟨b, hb', hne⟩ := a.k_outer l l.2
        apply hne
        have := congrArg (fun f : MulAut ↥a.L₁ => ((f ⟨b, hb'⟩ : ↥a.L₁) : G)) hl
        simpa [conjAutOf_apply, MulAut.conj_apply] using this
      k_comm_L₁t := a.k_L₁t }⟩

end Assembly

theorem hsInnerPartA_of_steps
    (h0 : StepS0) (h2 : StepS2) (h3 : StepS3) (h4 : StepS4)
    (h5 : StepS5) (h6 : StepS6) (h7 : StepS7) (h8 : StepS8) (h9 : StepS9) (h10 : StepS10)
    (h11 : StepS11) (h12 : StepS12) (h14 : StepS14) (h15 : StepS15) : HSInnerPartA := by
  intro G _ _ L hset _ hHiS t htL ht2 hin S z n hf E hEL hzE hEab hE16 hφ htr hfus W _ hWN hWn
    hEW htW hWab hW hN hC
  have hb : PAB G L t E W z :=
    PAB.of_hyps hset htL ht2 hin hf hEL hzE hEab hE16 hφ htr hfus hWN hWn hEW htW hWab hW hN hC
  obtain ⟨a0⟩ := h0 G L t E W z hb
  obtain ⟨a2⟩ := h2 G L t E W z hb a0
  obtain ⟨a3⟩ := h3 G L t E W z hb a2
  obtain ⟨a4⟩ := h4 G L t E W z hb a3
  obtain ⟨a5⟩ := h5 G L t E W z hb a4
  obtain ⟨a6⟩ := h6 G L t E W z hb a5
  obtain ⟨a7⟩ := h7 G L t E W z hHiS.uHered hb a6
  obtain ⟨a8⟩ := h8 G L t E W z hb a7
  obtain ⟨a9⟩ := h9 G L t E W z hb a8
  obtain ⟨a10⟩ := h10 G L t E W z hb a9
  obtain ⟨a11⟩ := h11 G L t E W z hb a10
  obtain ⟨a12⟩ := h12 G L t E W z hb a11
  obtain ⟨a14⟩ := h14 G L t E W z hb a12
  exact PA14.nonempty_configC hb a14 (h15 G L t E W z hb a14)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
