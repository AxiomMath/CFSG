module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductN1Center
public import CFSG.LocalAnalysis.EvenBN.Common.SL2Module
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFive
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.LocalAnalysis.EvenBN.Common.CosetFactorization

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  map_conj_inv_map_conj_inv mem_centerMod_iff mem_centralizerMod_iff)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf card_sup_mul_card_inf_eq)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace ProductN1DecompAux

section Generic

variable {G : Type*} [Group G]

theorem mem_conjg_iff {X : Subgroup G} {g x : G} : x ∈ Xᵍ[g] ↔ g * x * g⁻¹ ∈ X :=
  CFSG.LocalAnalysis.EvenBN.Common.mem_map_conj_inv_iff

theorem conjg_inf (X Y : Subgroup G) (g : G) : (X ⊓ Y)ᵍ[g] = Xᵍ[g] ⊓ Yᵍ[g] :=
  Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective

theorem conjg_sup (X Y : Subgroup G) (g : G) : (X ⊔ Y)ᵍ[g] = Xᵍ[g] ⊔ Yᵍ[g] :=
  Subgroup.map_sup _ _ _

theorem card_conjg (X : Subgroup G) (g : G) : Nat.card ↥(Xᵍ[g]) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjg_mono {X Y : Subgroup G} (h : X ≤ Y) (g : G) : Xᵍ[g] ≤ Yᵍ[g] :=
  Subgroup.map_mono h

theorem conjg_commutator (X Y : Subgroup G) (g : G) : ⁅X, Y⁆ᵍ[g] = ⁅Xᵍ[g], Yᵍ[g]⁆ :=
  Subgroup.map_commutator _ _ _

theorem le_normalizer_of_commutator_le [Finite G] {X Y : Subgroup G} (h : ⁅X, Y⁆ ≤ X) :
    Y ≤ normalizer (X : Set G) := fun b hb => by
  refine mem_normalizer_fintype fun x hx => ?_
  have h1 : ⁅x, b⁆ ∈ X := h (commutator_mem_commutator hx hb)
  have : b * x * b⁻¹ = (⁅x, b⁆)⁻¹ * x := by
    rw [commutatorElement_def]
    group
  rw [this]
  exact mul_mem (inv_mem h1) hx

theorem mem_normalizer_conjg_iff {X : Subgroup G} {g h : G} :
    g ∈ normalizer ((Xᵍ[h] : Subgroup G) : Set G) ↔ h * g * h⁻¹ ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro H x
    have := H (h⁻¹ * x * h)
    rw [mem_conjg_iff, mem_conjg_iff] at this
    have e1 : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    have e2 : h * (g * (h⁻¹ * x * h) * g⁻¹) * h⁻¹ = h * g * h⁻¹ * x * (h * g * h⁻¹)⁻¹ := by group
    rwa [e1, e2] at this
  · intro H y
    rw [mem_conjg_iff, mem_conjg_iff]
    have := H (h * y * h⁻¹)
    have e2 : h * (g * y * g⁻¹) * h⁻¹ = h * g * h⁻¹ * (h * y * h⁻¹) * (h * g * h⁻¹)⁻¹ := by group
    rwa [e2]

theorem mem_normalizer_sup {X Y : Subgroup G} {g : G} (hX : g ∈ normalizer (X : Set G))
    (hY : g ∈ normalizer (Y : Set G)) : g ∈ normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ normalizer (X : Set G) → g' ∈ normalizer (Y : Set G) →
      X ⊔ Y ≤ (X ⊔ Y).comap (MulAut.conj g').toMonoidHom := fun g' hX' hY' =>
    sup_le (fun a ha => mem_sup_left ((mem_normalizer_iff.mp hX' a).mp ha))
      (fun b hb => mem_sup_right ((mem_normalizer_iff.mp hY' b).mp hb))
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hX hY hx, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hX) (inv_mem hY) hx
  simpa [mul_assoc] using this

theorem mem_normalizer_commutator [Finite G] {X Y : Subgroup G} {g : G}
    (hX : g ∈ normalizer (X : Set G)) (hY : g ∈ normalizer (Y : Set G)) :
    g ∈ normalizer ((⁅X, Y⁆ : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  have h : (⁅X, Y⁆).map (MulAut.conj g).toMonoidHom = ⁅X, Y⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hX,
      map_conj_eq_of_mem_normalizer hY]
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem le_normalizer_of_le_centralizer {N U : Subgroup G} (hU : U ≤ centralizer (N : Set G)) :
    N ≤ normalizer (U : Set G) := fun n hn => by
  have hc : ∀ m ∈ N, ∀ u ∈ U, m * u * m⁻¹ = u := fun m hm u hu => by
    rw [mem_centralizer_iff.1 (hU hu) m hm]
    group
  rw [mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rwa [hc n hn u hu]
  · intro hu
    have h1 := hc n⁻¹ (N.inv_mem hn) _ hu
    have h2 : n⁻¹ * (n * u * n⁻¹) * n⁻¹⁻¹ = u := by group
    rw [h2] at h1
    rw [h1]
    exact hu

theorem mem_sup_iff_mul {X Y : Subgroup G} (h : X ≤ normalizer (Y : Set G)) {x : G} :
    x ∈ X ⊔ Y ↔ ∃ a ∈ X, ∃ b ∈ Y, a * b = x := by
  have h1 := Subgroup.coe_mul_of_left_le_normalizer_right X Y h
  constructor
  · intro hx
    have hx' : x ∈ (X : Set G) * (Y : Set G) := by
      rw [← h1]
      exact hx
    exact Set.mem_mul.1 hx'
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem_sup ha hb

theorem commutator_self_le (X : Subgroup G) : ⁅X, X⁆ ≤ X := by
  rw [commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)

theorem commutator_sup_central_le {N X Z : Subgroup G} (hXN : X ≤ N) (hZN : Z ≤ N)
    (hZ : Z ≤ centralizer (N : Set G)) : ⁅X ⊔ Z, X ⊔ Z⁆ ≤ ⁅X, X⁆ := by
  have hcom : ∀ n ∈ N, ∀ z ∈ Z, n * z = z * n := fun n hn z hz =>
    mem_centralizer_iff.1 (hZ hz) n hn
  have hc : ∀ n ∈ N, ∀ z ∈ Z, n * z * n⁻¹ = z := fun n hn z hz => by
    rw [hcom n hn z hz]
    group
  have hXZ : X ≤ normalizer (Z : Set G) := fun x hx => by
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rwa [hc x (hXN hx) z hz]
    · intro hz
      have h1 := hc x⁻¹ (N.inv_mem (hXN hx)) _ hz
      have h2 : x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z := by group
      rw [h2] at h1
      rw [h1]
      exact hz
  rw [commutator_le]
  intro g hg g' hg'
  obtain ⟨x, hx, z, hz, rfl⟩ := (mem_sup_iff_mul hXZ).1 hg
  obtain ⟨x', hx', z', hz', rfl⟩ := (mem_sup_iff_mul hXZ).1 hg'
  have h1 : ⁅x * z, x' * z'⁆ = x * ⁅z, x' * z'⁆ * x⁻¹ * ⁅x, x' * z'⁆ := by
    simp only [commutatorElement_def]
    group
  have h2 : ⁅x, x' * z'⁆ = ⁅x, x'⁆ * (x' * ⁅x, z'⁆ * x'⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hz1 : ⁅z, x' * z'⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2
      (hcom (x' * z') (N.mul_mem (hXN hx') (hZN hz')) z hz).symm
  have hz2 : ⁅x, z'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hcom x (hXN hx) z' hz')
  rw [h1, h2, hz1, hz2]
  simp only [mul_one, one_mul, mul_inv_cancel, mul_inv_cancel_right]
  exact commutator_mem_commutator hx hx'

theorem perfect_of_sup_central {N B Z : Subgroup G} (hBN : ⁅B, B⁆ ≤ N) (hZN : Z ≤ N)
    (hZ : Z ≤ centralizer (N : Set G)) (hB : ⁅B, B⁆ ⊔ Z = B) : ⁅⁅B, B⁆, ⁅B, B⁆⁆ = ⁅B, B⁆ := by
  refine le_antisymm (commutator_self_le _) ?_
  calc ⁅B, B⁆ = ⁅⁅B, B⁆ ⊔ Z, ⁅B, B⁆ ⊔ Z⁆ := by rw [hB]
    _ ≤ ⁅⁅B, B⁆, ⁅B, B⁆⁆ := commutator_sup_central_le hBN hZN hZ

theorem eq_sup_of_perfect_central {N X Y Z : Subgroup G} (hXN : X ≤ N) (hYN : Y ≤ N)
    (hX : ⁅X, X⁆ = X) (hY : ⁅Y, Y⁆ = Y) (hZN : Z ≤ N) (hZ : Z ≤ centralizer (N : Set G))
    (hNXYZ : N ≤ X ⊔ Y ⊔ Z) (hZ' : Z ≤ ⁅N, N⁆) : N = X ⊔ Y := by
  have hXY : ⁅X ⊔ Y, X ⊔ Y⁆ = X ⊔ Y := by
    refine le_antisymm (commutator_self_le _) (sup_le ?_ ?_)
    · calc X = ⁅X, X⁆ := hX.symm
        _ ≤ ⁅X ⊔ Y, X ⊔ Y⁆ := commutator_mono le_sup_left le_sup_left
    · calc Y = ⁅Y, Y⁆ := hY.symm
        _ ≤ ⁅X ⊔ Y, X ⊔ Y⁆ := commutator_mono le_sup_right le_sup_right
  have hN' : N = (X ⊔ Y) ⊔ Z := le_antisymm hNXYZ (sup_le (sup_le hXN hYN) hZN)
  have hNN : ⁅N, N⁆ ≤ X ⊔ Y := by
    calc ⁅N, N⁆ = ⁅(X ⊔ Y) ⊔ Z, (X ⊔ Y) ⊔ Z⁆ := by rw [← hN']
      _ ≤ ⁅X ⊔ Y, X ⊔ Y⁆ := commutator_sup_central_le (sup_le hXN hYN) hZN hZ
      _ = X ⊔ Y := hXY
  exact le_antisymm (hN'.le.trans (sup_le le_rfl (hZ'.trans hNN))) (sup_le hXN hYN)

theorem conj_conj_of_mul_self {t : G} (ht : t * t = 1) (v : G) : t * (t * v * t⁻¹) * t⁻¹ = v := by
  have : t * (t * v * t⁻¹) * t⁻¹ = (t * t) * v * (t * t)⁻¹ := by group
  rw [this, ht]
  group

end Generic

structure Ctx (F : Type) [Field F] [Finite F] [CharP F 2] {G : Type} [Group G] (t : G)
    (N K D U A D₁ J : Subgroup G) : Prop where
  four_le : 4 ≤ Nat.card F
  t_mul_t : t * t = 1
  D_le_K : D ≤ K
  K_le_N : K ≤ N
  sup_eq : K ⊔ Kᵍ[t] = N
  inf_eq : K ⊓ Kᵍ[t] = D
  comm_le : ⁅K, Kᵍ[t]⁆ ≤ D
  quot : IsQuotientIso K D SL(2, F)
  U_le_D : U ≤ D
  U_central : U ≤ centralizer (N : Set G)
  U_conj : Uᵍ[t] = U
  D_comm : ⁅D, D⁆ = U
  D_pgroup : IsPGroup 2 D
  V_lt : U < centerMod U K
  V_inf : centerMod U K ⊓ centerMod U (Kᵍ[t]) = U
  CD : ∀ x ∈ N, (∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ U) → x ∈ D
  A_le_K : A ≤ K
  K_eq : A ⊔ D = K
  A_inf_D : A ⊓ D = ⊥
  A_comm : ⁅A, Aᵍ[t]⁆ = ⊥
  D₁_le_D : D₁ ≤ D
  U_le_D₁ : U ≤ D₁
  D₁_fix : ∀ x ∈ D₁, x * t * x⁻¹ * t⁻¹ ∈ U
  fix : ∀ x ∈ D, x * t * x⁻¹ * t⁻¹ ∈ U → x ∈ D₁
  card_D₁ : Nat.card D * Nat.card U = Nat.card D₁ ^ 2
  irr : ∀ X : Subgroup G, U ≤ X → N ≤ normalizer (X : Set G) → J ≤ normalizer (X : Set G) →
    X ⊓ D₁ = U ∨ D₁ ≤ X
  J_K : J ≤ normalizer (K : Set G)
  J_U : J ≤ normalizer (U : Set G)
  J_t : J ≤ centralizer ({t} : Set G)

namespace Ctx

section Basic

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2] {t : G}
  {N K D U A D₁ J : Subgroup G} (c : Ctx F t N K D U A D₁ J)

include c

theorem Kt_conj : (Kᵍ[t])ᵍ[t] = K := map_conj_inv_map_conj_inv c.t_mul_t K

theorem D_conj : Dᵍ[t] = D := by
  rw [← c.inf_eq, conjg_inf, c.Kt_conj, inf_comm]

theorem N_conj : Nᵍ[t] = N := by
  rw [← c.sup_eq, conjg_sup, c.Kt_conj, sup_comm]

theorem D_le_Kt : D ≤ Kᵍ[t] := c.inf_eq ▸ inf_le_right

theorem Kt_le_N : Kᵍ[t] ≤ N := c.sup_eq ▸ le_sup_right

theorem Kt_le_normalizer_K : Kᵍ[t] ≤ normalizer (K : Set G) :=
  le_normalizer_of_commutator_le (c.comm_le.trans c.D_le_K)

theorem K_le_normalizer_Kt : K ≤ normalizer ((Kᵍ[t] : Subgroup G) : Set G) :=
  le_normalizer_of_commutator_le (X := Kᵍ[t]) (Y := K) (by
    rw [commutator_comm]
    exact c.comm_le.trans c.D_le_Kt)

theorem N_le_normalizer_K : N ≤ normalizer (K : Set G) :=
  c.sup_eq ▸ sup_le le_normalizer c.Kt_le_normalizer_K

theorem N_le_normalizer_Kt : N ≤ normalizer ((Kᵍ[t] : Subgroup G) : Set G) :=
  c.sup_eq ▸ sup_le c.K_le_normalizer_Kt le_normalizer

theorem N_le_normalizer_D : N ≤ normalizer (D : Set G) := by
  intro g hg
  rw [← c.inf_eq]
  exact CFSG.LocalAnalysis.EvenBN.Common.mem_normalizer_inf (c.N_le_normalizer_K hg)
    (c.N_le_normalizer_Kt hg)

theorem U_comm {n u : G} (hn : n ∈ N) (hu : u ∈ U) : n * u = u * n :=
  mem_centralizer_iff.1 (c.U_central hu) n hn

theorem conj_U {n u : G} (hn : n ∈ N) (hu : u ∈ U) : n * u * n⁻¹ = u := by
  rw [c.U_comm hn hu]
  group

theorem N_le_normalizer_U : N ≤ normalizer (U : Set G) :=
  le_normalizer_of_le_centralizer c.U_central

theorem conj_t_mem_N {n : G} (hn : n ∈ N) : t * n * t⁻¹ ∈ N := by
  have := mem_conjg_iff (X := N) (g := t) (x := n)
  rw [c.N_conj] at this
  exact this.1 hn

theorem conj_t_mem_U_iff {u : G} : u ∈ U ↔ t * u * t⁻¹ ∈ U := by
  have := mem_conjg_iff (X := U) (g := t) (x := u)
  rw [c.U_conj] at this
  exact this

theorem U_le_K : U ≤ K := c.U_le_D.trans c.D_le_K

theorem D_le_N : D ≤ N := c.D_le_K.trans c.K_le_N

theorem comm_mem_U {x y : G} (hx : x ∈ D) (hy : y ∈ D) : x * y * x⁻¹ * y⁻¹ ∈ U := by
  have := commutator_mem_commutator hx hy
  rw [c.D_comm, commutatorElement_def] at this
  exact this

theorem mem_V {x : G} : x ∈ centerMod U K ↔ x ∈ K ∧ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ U := by
  rw [mem_centerMod_iff c.U_le_K]
  constructor
  · rintro ⟨hx, -, hc⟩
    exact ⟨hx, fun k hk => hc k hk (c.N_le_normalizer_U (c.K_le_N hk))⟩
  · rintro ⟨hx, hc⟩
    exact ⟨hx, c.N_le_normalizer_U (c.K_le_N hx), fun k hk _ => hc k hk⟩

theorem V_le_D : centerMod U K ≤ D := by
  intro x hx
  obtain ⟨hxK, hc⟩ := c.mem_V.1 hx
  obtain ⟨φ, hφs, hφk⟩ := c.quot
  have hcen : φ ⟨x, hxK⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := hφs g
    have h1 : (⟨x * k * x⁻¹ * k⁻¹, K.mul_mem (K.mul_mem (K.mul_mem hxK k.2) (K.inv_mem hxK))
        (K.inv_mem k.2)⟩ : ↥K) ∈ φ.ker := by
      rw [hφk, Subgroup.mem_subgroupOf]
      exact c.U_le_D (hc k k.2)
    rw [MonoidHom.mem_ker] at h1
    have h2 : φ ⟨x, hxK⟩ * φ k * (φ ⟨x, hxK⟩)⁻¹ * (φ k)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h1
    calc φ k * φ ⟨x, hxK⟩
        = (φ ⟨x, hxK⟩ * φ k * (φ ⟨x, hxK⟩)⁻¹ * (φ k)⁻¹)⁻¹ * (φ ⟨x, hxK⟩ * φ k) := by group
      _ = φ ⟨x, hxK⟩ * φ k := by rw [h2]; simp
  rw [CFSG.LocalAnalysis.EvenBN.Common.center_sl2_eq_bot_of_charTwo, Subgroup.mem_bot] at hcen
  have : (⟨x, hxK⟩ : ↥K) ∈ φ.ker := hcen
  rw [hφk, Subgroup.mem_subgroupOf] at this
  exact this

theorem U_le_V : U ≤ centerMod U K := fun u hu =>
  c.mem_V.2 ⟨c.U_le_K hu, fun k hk => by
    have h : u * k = k * u := (c.U_comm (c.K_le_N hk) hu).symm
    have e : u * k * u⁻¹ * k⁻¹ = 1 := by rw [h]; group
    rw [e]
    exact one_mem U⟩

theorem conj_mem_V {g x : G} (hgK : g ∈ normalizer (K : Set G))
    (hgU : g ∈ normalizer (U : Set G)) (hx : x ∈ centerMod U K) :
    g * x * g⁻¹ ∈ centerMod U K := by
  obtain ⟨hxK, hc⟩ := c.mem_V.1 hx
  refine c.mem_V.2 ⟨(mem_normalizer_iff.1 hgK x).1 hxK, fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ K := by
    have := (mem_normalizer_iff.1 (inv_mem hgK) k).1 hk
    simpa using this
  have h1 := hc _ hk'
  have h2 : g * (x * (g⁻¹ * k * g) * x⁻¹ * (g⁻¹ * k * g)⁻¹) * g⁻¹ ∈ U :=
    (mem_normalizer_iff.1 hgU _).1 h1
  have e : g * (x * (g⁻¹ * k * g) * x⁻¹ * (g⁻¹ * k * g)⁻¹) * g⁻¹ =
      g * x * g⁻¹ * k * (g * x * g⁻¹)⁻¹ * k⁻¹ := by group
  rwa [e] at h2

theorem mem_normalizer_V {g : G} (hgK : g ∈ normalizer (K : Set G))
    (hgU : g ∈ normalizer (U : Set G)) : g ∈ normalizer ((centerMod U K : Subgroup G) : Set G) :=
  mem_normalizer_fintype fun x hx => c.conj_mem_V hgK hgU hx

theorem N_le_normalizer_V : N ≤ normalizer ((centerMod U K : Subgroup G) : Set G) := fun n hn =>
  c.mem_normalizer_V (c.N_le_normalizer_K hn) (c.N_le_normalizer_U hn)

theorem J_le_normalizer_V : J ≤ normalizer ((centerMod U K : Subgroup G) : Set G) := fun j hj =>
  c.mem_normalizer_V (c.J_K hj) (c.J_U hj)

theorem Vt_eq : centerMod U (Kᵍ[t]) = (centerMod U K)ᵍ[t] := by
  have hUKt : U ≤ Kᵍ[t] := c.U_le_D.trans c.D_le_Kt
  ext x
  rw [mem_centerMod_iff hUKt, mem_conjg_iff (X := centerMod U K) (g := t), c.mem_V]
  constructor
  · rintro ⟨hx, -, hc⟩
    refine ⟨mem_conjg_iff.1 hx, fun k hk => ?_⟩
    have hk' : t⁻¹ * k * t ∈ Kᵍ[t] := by
      rw [mem_conjg_iff, show t * (t⁻¹ * k * t) * t⁻¹ = k by group]
      exact hk
    have h1 := hc _ hk' (c.N_le_normalizer_U (c.Kt_le_N hk'))
    have h2 := c.conj_t_mem_U_iff.1 h1
    have e : t * (x * (t⁻¹ * k * t) * x⁻¹ * (t⁻¹ * k * t)⁻¹) * t⁻¹ =
        t * x * t⁻¹ * k * (t * x * t⁻¹)⁻¹ * k⁻¹ := by group
    rwa [e] at h2
  · rintro ⟨hx, hc⟩
    refine ⟨mem_conjg_iff.2 hx, c.N_le_normalizer_U (c.Kt_le_N (mem_conjg_iff.2 hx)),
      fun a ha _ => ?_⟩
    have ha' : t * a * t⁻¹ ∈ K := mem_conjg_iff.1 ha
    have h1 := hc _ ha'
    have e : t * (x * a * x⁻¹ * a⁻¹) * t⁻¹ =
        t * x * t⁻¹ * (t * a * t⁻¹) * (t * x * t⁻¹)⁻¹ * (t * a * t⁻¹)⁻¹ := by group
    refine c.conj_t_mem_U_iff.2 ?_
    rw [e]
    exact h1

theorem W_le_D : (centerMod U K)ᵍ[t] ≤ D := by
  intro x hx
  have h1 : t * x * t⁻¹ ∈ D := c.V_le_D (mem_conjg_iff.1 hx)
  have h2 : x ∈ Dᵍ[t] := mem_conjg_iff.2 h1
  rwa [c.D_conj] at h2

theorem U_le_W : U ≤ (centerMod U K)ᵍ[t] := fun u hu =>
  mem_conjg_iff.2 (c.U_le_V (c.conj_t_mem_U_iff.1 hu))

theorem V_inf_W : centerMod U K ⊓ (centerMod U K)ᵍ[t] = U := by
  have := c.V_inf
  rwa [c.Vt_eq] at this

theorem W_conj : ((centerMod U K)ᵍ[t])ᵍ[t] = centerMod U K :=
  map_conj_inv_map_conj_inv c.t_mul_t _

theorem N_le_normalizer_W : N ≤ normalizer (((centerMod U K)ᵍ[t] : Subgroup G) : Set G) :=
  fun n hn => mem_normalizer_conjg_iff.2 (c.N_le_normalizer_V (c.conj_t_mem_N hn))

theorem conj_t_of_mem_J {j : G} (hj : j ∈ J) : t * j * t⁻¹ = j := by
  have h : j * t = t * j := mem_centralizer_singleton_iff.1 (c.J_t hj)
  rw [← h]
  group

theorem J_le_normalizer_W : J ≤ normalizer (((centerMod U K)ᵍ[t] : Subgroup G) : Set G) :=
  fun j hj => by
    refine mem_normalizer_conjg_iff.2 ?_
    rw [c.conj_t_of_mem_J hj]
    exact c.J_le_normalizer_V hj

theorem comm_W_V_le_U : ⁅(centerMod U K)ᵍ[t], centerMod U K⁆ ≤ U := by
  rw [commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact c.comm_mem_U (c.W_le_D hx) (c.V_le_D hy)

theorem W_le_normalizer_V :
    (centerMod U K)ᵍ[t] ≤ normalizer ((centerMod U K : Subgroup G) : Set G) :=
  le_normalizer_of_commutator_le (X := centerMod U K) (Y := (centerMod U K)ᵍ[t]) (by
    rw [commutator_comm]
    exact c.comm_W_V_le_U.trans c.U_le_V)

theorem theta_mem {v : G} (hv : v ∈ (centerMod U K)ᵍ[t]) : v * (t * v * t⁻¹) ∈ D₁ := by
  have hw : t * v * t⁻¹ ∈ centerMod U K := mem_conjg_iff.1 hv
  refine c.fix _ (mul_mem (c.W_le_D hv) (c.V_le_D hw)) ?_
  have htw := conj_conj_of_mul_self c.t_mul_t v
  have h1 : t * (t * v * t⁻¹)⁻¹ * t⁻¹ = v⁻¹ := by
    have := congrArg (fun x => x⁻¹) htw
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
  have h2 : t * v⁻¹ * t⁻¹ = (t * v * t⁻¹)⁻¹ := by group
  have e : v * (t * v * t⁻¹) * t * (v * (t * v * t⁻¹))⁻¹ * t⁻¹ =
      v * (t * v * t⁻¹) * v⁻¹ * (t * v * t⁻¹)⁻¹ := by
    calc v * (t * v * t⁻¹) * t * (v * (t * v * t⁻¹))⁻¹ * t⁻¹
        = v * (t * v * t⁻¹) * (t * (t * v * t⁻¹)⁻¹ * t⁻¹) * (t * v⁻¹ * t⁻¹) := by group
      _ = _ := by rw [h1, h2]
  rw [e]
  exact c.comm_mem_U (c.W_le_D hv) (c.V_le_D hw)

theorem mem_U_of_theta_mem_U {v : G} (hv : v ∈ (centerMod U K)ᵍ[t])
    (h : v * (t * v * t⁻¹) ∈ U) : v ∈ U := by
  have hw : t * v * t⁻¹ ∈ centerMod U K := mem_conjg_iff.1 hv
  have h1 : v ∈ centerMod U K := by
    have h3 : v = (v * (t * v * t⁻¹)) * (t * v * t⁻¹)⁻¹ := by group
    rw [h3]
    exact mul_mem (c.U_le_V h) (inv_mem hw)
  have h4 : v ∈ centerMod U K ⊓ (centerMod U K)ᵍ[t] := ⟨h1, hv⟩
  rwa [c.V_inf_W] at h4

theorem M_dichotomy {M : Subgroup G} (hUM : U ≤ M) (hMW : M ≤ (centerMod U K)ᵍ[t])
    (hN : N ≤ normalizer (M : Set G)) (hJ : J ≤ normalizer (M : Set G)) :
    M = U ∨ ((centerMod U K)ᵍ[t] ≤ M ∧ D₁ ≤ M ⊔ Mᵍ[t]) := by
  have hX_N : N ≤ normalizer ((M ⊔ Mᵍ[t] : Subgroup G) : Set G) := fun n hn =>
    mem_normalizer_sup (hN hn) (mem_normalizer_conjg_iff.2 (hN (c.conj_t_mem_N hn)))
  have hX_J : J ≤ normalizer ((M ⊔ Mᵍ[t] : Subgroup G) : Set G) := fun j hj =>
    mem_normalizer_sup (hJ hj) (mem_normalizer_conjg_iff.2 (by
      rw [c.conj_t_of_mem_J hj]
      exact hJ hj))
  have hmem : ∀ v ∈ M, t * v * t⁻¹ ∈ Mᵍ[t] := fun v hv => by
    rw [mem_conjg_iff, conj_conj_of_mul_self c.t_mul_t v]
    exact hv
  rcases c.irr (M ⊔ Mᵍ[t]) (hUM.trans le_sup_left) hX_N hX_J with h | h
  · left
    refine le_antisymm (fun v hv => ?_) hUM
    have hvX : v * (t * v * t⁻¹) ∈ (M ⊔ Mᵍ[t]) ⊓ D₁ :=
      ⟨mul_mem (mem_sup_left hv) (mem_sup_right (hmem v hv)), c.theta_mem (hMW hv)⟩
    rw [h] at hvX
    exact c.mem_U_of_theta_mem_U (hMW hv) hvX
  · right
    refine ⟨fun v hv => ?_, h⟩
    have hMW' : Mᵍ[t] ≤ centerMod U K := by
      have := conjg_mono hMW t
      rwa [c.W_conj] at this
    have hUM' : U ≤ Mᵍ[t] := fun u hu => mem_conjg_iff.2 (hUM (c.conj_t_mem_U_iff.1 hu))
    have hnorm : M ≤ normalizer ((Mᵍ[t] : Subgroup G) : Set G) := by
      refine le_normalizer_of_commutator_le (X := Mᵍ[t]) (Y := M) ?_
      refine le_trans ?_ hUM'
      rw [commutator_le]
      intro x hx y hy
      rw [commutatorElement_def]
      exact c.comm_mem_U (c.V_le_D (hMW' hx)) (c.W_le_D (hMW hy))
    obtain ⟨m, hm, n, hn, hmn⟩ := (mem_sup_iff_mul hnorm).1 (h (c.theta_mem hv))
    have hvW := hv
    have hw : t * v * t⁻¹ ∈ centerMod U K := mem_conjg_iff.1 hv
    generalize t * v * t⁻¹ = w at hmn hw
    have h5 : m⁻¹ * v = n * w⁻¹ := by
      have : v = m * n * w⁻¹ := by rw [hmn]; group
      rw [this]
      group
    have h8 : m⁻¹ * v ∈ centerMod U K := by
      rw [h5]
      exact mul_mem (hMW' hn) (inv_mem hw)
    have h9 : m⁻¹ * v ∈ (centerMod U K)ᵍ[t] := mul_mem (inv_mem (hMW hm)) hvW
    have h6 : m⁻¹ * v ∈ centerMod U K ⊓ (centerMod U K)ᵍ[t] := ⟨h8, h9⟩
    rw [c.V_inf_W] at h6
    have h7 : v = m * (m⁻¹ * v) := by group
    rw [h7]
    exact mul_mem hm (hUM h6)

theorem D₁_le_W_sup_V : D₁ ≤ (centerMod U K)ᵍ[t] ⊔ centerMod U K := by
  rcases c.M_dichotomy (M := (centerMod U K)ᵍ[t]) c.U_le_W le_rfl c.N_le_normalizer_W
    c.J_le_normalizer_W with h | ⟨-, h⟩
  · exfalso
    have : centerMod U K = U := by
      rw [← c.W_conj, h, c.U_conj]
    exact c.V_lt.ne' this
  · rwa [c.W_conj] at h

theorem card_W_eq_card_D₁ :
    Nat.card ((centerMod U K)ᵍ[t] : Subgroup G) = Nat.card D₁ := by
  set V := centerMod U K with hVdef
  set W : Subgroup G := Vᵍ[t] with hWdef
  have hD₁N : D₁ ≤ normalizer (U : Set G) := fun x hx =>
    c.N_le_normalizer_U (c.D_le_N (c.D₁_le_D hx))
  haveI hnormU : (U.subgroupOf D₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.U_le_D₁).2 hD₁N
  have hmem : ∀ v : W, (v : G) * (t * v * t⁻¹) ∈ D₁ := fun v => c.theta_mem v.2
  let ψ : W →* D₁ ⧸ U.subgroupOf D₁ :=
    MonoidHom.mk' (fun v => QuotientGroup.mk ⟨(v : G) * (t * v * t⁻¹), hmem v⟩) (by
      intro v v'
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hwV : t * (v : G) * t⁻¹ ∈ V := mem_conjg_iff.1 v.2
      have hw'V : t * (v' : G) * t⁻¹ ∈ V := mem_conjg_iff.1 v'.2
      have hcomm := c.comm_mem_U (inv_mem (c.V_le_D hwV)) (inv_mem (c.W_le_D v'.2))
      have hconj := c.conj_U (n := (t * (v' : G) * t⁻¹)⁻¹)
        (inv_mem (c.D_le_N (c.V_le_D hw'V))) hcomm
      have e : ((v : G) * v' * (t * ((v : G) * v') * t⁻¹))⁻¹ *
          (((v : G) * (t * v * t⁻¹)) * ((v' : G) * (t * v' * t⁻¹))) =
          (t * (v' : G) * t⁻¹)⁻¹ * ((t * (v : G) * t⁻¹)⁻¹ * (v' : G)⁻¹ *
            ((t * (v : G) * t⁻¹)⁻¹)⁻¹ * ((v' : G)⁻¹)⁻¹) * ((t * (v' : G) * t⁻¹)⁻¹)⁻¹ := by
        group
      show ((v : G) * v' * (t * ((v : G) * v') * t⁻¹))⁻¹ *
          (((v : G) * (t * v * t⁻¹)) * ((v' : G) * (t * v' * t⁻¹))) ∈ U
      rw [e, hconj]
      exact hcomm)
  have hker : ψ.ker = U.subgroupOf W := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk _ : D₁ ⧸ U.subgroupOf D₁) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact c.mem_U_of_theta_mem_U v.2 h
    · intro h
      have hw : t * (v : G) * t⁻¹ ∈ U := c.conj_t_mem_U_iff.1 h
      exact mul_mem h hw
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, hb, a, ha, hba⟩ := (mem_sup_iff_mul c.W_le_normalizer_V).1 (c.D₁_le_W_sup_V hx)
    refine ⟨⟨b, hb⟩, ?_⟩
    show (QuotientGroup.mk ⟨b * (t * b * t⁻¹), hmem ⟨b, hb⟩⟩ : D₁ ⧸ U.subgroupOf D₁) =
      QuotientGroup.mk ⟨x, hx⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (b * (t * b * t⁻¹))⁻¹ * x ∈ U
    have hfix := c.D₁_fix x hx
    subst hba
    have hwV : t * b * t⁻¹ ∈ V := mem_conjg_iff.1 hb
    have ha'W : t * a * t⁻¹ ∈ W := by
      rw [mem_conjg_iff, conj_conj_of_mul_self c.t_mul_t a]
      exact ha
    have hu₀ : b * a * (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹)⁻¹ ∈ U := by
      have e : b * a * t * (b * a)⁻¹ * t⁻¹ =
          b * a * (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹)⁻¹ := by group
      rwa [e] at hfix
    have hc := c.comm_mem_U (c.W_le_D ha'W) (inv_mem (c.V_le_D ha))
    have hcw := c.conj_U (n := t * b * t⁻¹) (c.D_le_N (c.V_le_D hwV)) hc
    have hpq : (b * (t * a * t⁻¹)⁻¹) * (a * (t * b * t⁻¹)⁻¹) ∈ U := by
      have e : (b * (t * a * t⁻¹)⁻¹) * (a * (t * b * t⁻¹)⁻¹) =
          (b * a * (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹)⁻¹) *
            ((t * b * t⁻¹) * ((t * a * t⁻¹) * a⁻¹ * (t * a * t⁻¹)⁻¹ * (a⁻¹)⁻¹) *
              (t * b * t⁻¹)⁻¹) := by group
      rw [e, hcw]
      exact mul_mem hu₀ hc
    have hpW : b * (t * a * t⁻¹)⁻¹ ∈ W := mul_mem hb (inv_mem ha'W)
    have hqV : a * (t * b * t⁻¹)⁻¹ ∈ V := mul_mem ha (inv_mem hwV)
    have hqW : a * (t * b * t⁻¹)⁻¹ ∈ W := by
      have e : a * (t * b * t⁻¹)⁻¹ = (b * (t * a * t⁻¹)⁻¹)⁻¹ *
          ((b * (t * a * t⁻¹)⁻¹) * (a * (t * b * t⁻¹)⁻¹)) := by group
      rw [e]
      exact mul_mem (inv_mem hpW) (c.U_le_W hpq)
    have hqU : a * (t * b * t⁻¹)⁻¹ ∈ U := by
      have : a * (t * b * t⁻¹)⁻¹ ∈ V ⊓ W := ⟨hqV, hqW⟩
      rwa [c.V_inf_W] at this
    have h1 := c.conj_U (n := (t * b * t⁻¹)⁻¹) (inv_mem (c.D_le_N (c.V_le_D hwV))) hqU
    have e2 : (b * (t * b * t⁻¹))⁻¹ * (b * a) =
        (t * b * t⁻¹)⁻¹ * (a * (t * b * t⁻¹)⁻¹) * ((t * b * t⁻¹)⁻¹)⁻¹ := by group
    rw [e2, h1]
    exact hqU
  have c1 : Nat.card W = Nat.card (W ⧸ ψ.ker) * Nat.card ψ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have c2 : Nat.card D₁ = Nat.card (D₁ ⧸ U.subgroupOf D₁) * Nat.card (U.subgroupOf D₁) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have c3 : Nat.card (W ⧸ ψ.ker) = Nat.card (D₁ ⧸ U.subgroupOf D₁) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).toEquiv
  have c4 : Nat.card ψ.ker = Nat.card U := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.U_le_W).toEquiv
  have c5 : Nat.card (U.subgroupOf D₁) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.U_le_D₁).toEquiv
  rw [c1, c2, c3, c4, c5]

theorem D_eq_sup : D = centerMod U K ⊔ (centerMod U K)ᵍ[t] := by
  have hXD : centerMod U K ⊔ (centerMod U K)ᵍ[t] ≤ D := sup_le c.V_le_D c.W_le_D
  refine (Subgroup.eq_of_le_of_card_ge hXD ?_).symm
  have h1 := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq c.W_le_normalizer_V
  rw [c.V_inf_W, card_conjg] at h1
  have h2 := c.card_W_eq_card_D₁
  rw [card_conjg] at h2
  have h3 := c.card_D₁
  have hU : 0 < Nat.card U := Nat.card_pos
  apply Nat.le_of_mul_le_mul_right _ hU
  rw [h1, h2, h3, sq]

theorem A_le_N : A ≤ N := c.A_le_K.trans c.K_le_N

theorem A_le_normalizer_D : A ≤ normalizer (D : Set G) := fun a ha =>
  c.N_le_normalizer_D (c.A_le_N ha)

theorem nonempty_mulEquiv_A : Nonempty (A ≃* SL(2, F)) := by
  obtain ⟨φ, hφs, hφk⟩ := c.quot
  let φA : A →* SL(2, F) := φ.comp (Subgroup.inclusion c.A_le_K)
  have hinj : Function.Injective φA := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (⟨(a : G), c.A_le_K a.2⟩ : ↥K) ∈ φ.ker := ha
    rw [hφk, Subgroup.mem_subgroupOf] at h1
    have h2 : (a : G) ∈ A ⊓ D := ⟨a.2, h1⟩
    rw [c.A_inf_D, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective φA := by
    intro g
    obtain ⟨k, rfl⟩ := hφs g
    have hk : (k : G) ∈ A ⊔ D := by
      rw [c.K_eq]
      exact k.2
    obtain ⟨a, ha, d, hd, had⟩ := (mem_sup_iff_mul c.A_le_normalizer_D).1 hk
    refine ⟨⟨a, ha⟩, ?_⟩
    have hdK : (⟨d, c.D_le_K hd⟩ : ↥K) ∈ φ.ker := by
      rw [hφk, Subgroup.mem_subgroupOf]
      exact hd
    have hk' : (⟨a, c.A_le_K ha⟩ : ↥K) * ⟨d, c.D_le_K hd⟩ = k := Subtype.ext had
    show φ ⟨a, c.A_le_K ha⟩ = φ k
    rw [← hk', map_mul, MonoidHom.mem_ker.1 hdK, mul_one]
  exact ⟨MulEquiv.ofBijective φA ⟨hinj, hsurj⟩⟩

theorem A_perfect : ⁅A, A⁆ = A := by
  obtain ⟨e⟩ := c.nonempty_mulEquiv_A
  haveI : Group.IsPerfect SL(2, F) := CFSG.LinearGroups.special_linear_dimension_two_perfect
    (CFSG.LocalAnalysis.EvenBN.Common.exists_finset_card_four c.four_le)
  haveI : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  exact (CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq A).1 this

theorem A_simple : IsSimpleGroup A := by
  obtain ⟨e⟩ := c.nonempty_mulEquiv_A
  haveI := CFSG.LocalAnalysis.EvenBN.Common.sl2_isSimpleGroup_of_charTwo c.four_le
  exact e.isSimpleGroup

theorem A_ne_bot : A ≠ ⊥ := by
  haveI := c.A_simple
  exact (Subgroup.nontrivial_iff_ne_bot A).1 inferInstance

theorem A_not_pgroup : ¬ IsPGroup 2 A := by
  intro hp
  haveI := c.A_simple
  haveI : Group.IsNilpotent A := hp.isNilpotent
  have hperf : Group.IsPerfect A :=
    (CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq A).2 c.A_perfect
  exact Group.IsPerfect.not_isNilpotent A inferInstance

theorem comm_K_V {x v : G} (hx : x ∈ K) (hv : v ∈ centerMod U K) : x * v * x⁻¹ * v⁻¹ ∈ U := by
  have h := (c.mem_V.1 hv).2 x hx
  have e : x * v * x⁻¹ * v⁻¹ = (v * x * v⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h

theorem comm_Kt_W {x w : G} (hx : x ∈ Kᵍ[t]) (hw : w ∈ (centerMod U K)ᵍ[t]) :
    w * x * w⁻¹ * x⁻¹ ∈ U := by
  rw [← c.Vt_eq] at hw
  have hUKt : U ≤ Kᵍ[t] := c.U_le_D.trans c.D_le_Kt
  obtain ⟨-, -, h⟩ := (mem_centerMod_iff hUKt).1 hw
  exact h x hx (c.N_le_normalizer_U (c.Kt_le_N hx))

theorem W_le_of_comm_le {Q : Subgroup G} (hUQ : U ≤ Q) (hN : N ≤ normalizer (Q : Set G))
    (hJ : J ≤ normalizer (Q : Set G)) (hAW : ⁅A, (centerMod U K)ᵍ[t]⁆ ≤ Q) :
    (centerMod U K)ᵍ[t] ≤ Q := by
  rcases c.M_dichotomy (M := Q ⊓ (centerMod U K)ᵍ[t]) (le_inf hUQ c.U_le_W) inf_le_right
      (fun n hn => mem_normalizer_inf (hN hn) (c.N_le_normalizer_W hn))
      (fun j hj => mem_normalizer_inf (hJ hj) (c.J_le_normalizer_W hj)) with h | ⟨h1, -⟩
  · exfalso
    apply c.A_ne_bot
    rw [eq_bot_iff]
    intro x hx
    have hxD : x ∈ D := by
      refine c.CD x (c.A_le_N hx) fun d hd => ?_
      have hd' : d ∈ (centerMod U K)ᵍ[t] ⊔ centerMod U K := by
        rw [sup_comm, ← c.D_eq_sup]
        exact hd
      obtain ⟨w, hw, v, hv, rfl⟩ := (mem_sup_iff_mul c.W_le_normalizer_V).1 hd'
      have hxw : x * w * x⁻¹ * w⁻¹ ∈ U := by
        have h2 : x * w * x⁻¹ * w⁻¹ ∈ Q := by
          have := hAW (commutator_mem_commutator hx hw)
          rwa [commutatorElement_def] at this
        have h3 : x * w * x⁻¹ * w⁻¹ ∈ (centerMod U K)ᵍ[t] := by
          have hxn := c.N_le_normalizer_W (c.A_le_N hx)
          exact mul_mem ((mem_normalizer_iff.1 hxn w).1 hw) (inv_mem hw)
        have h4 : x * w * x⁻¹ * w⁻¹ ∈ Q ⊓ (centerMod U K)ᵍ[t] := ⟨h2, h3⟩
        rwa [h] at h4
      have hxv : x * v * x⁻¹ * v⁻¹ ∈ U := c.comm_K_V (c.A_le_K hx) hv
      have hwN : w ∈ N := c.D_le_N (c.W_le_D hw)
      have e : x * (w * v) * x⁻¹ * (w * v)⁻¹ =
          (x * w * x⁻¹ * w⁻¹) * (w * (x * v * x⁻¹ * v⁻¹) * w⁻¹) := by group
      rw [e]
      exact mul_mem hxw (by rw [c.conj_U hwN hxv]; exact hxv)
    have : x ∈ A ⊓ D := ⟨hx, hxD⟩
    rw [c.A_inf_D] at this
    exact this
  · exact h1.trans inf_le_left

theorem U_le_comm : U ≤ ⁅K, K⁆ := by
  have := commutator_mono c.D_le_K c.D_le_K
  rwa [c.D_comm] at this

theorem A_le_comm : A ≤ ⁅K, K⁆ := by
  calc A = ⁅A, A⁆ := c.A_perfect.symm
    _ ≤ ⁅K, K⁆ := commutator_mono c.A_le_K c.A_le_K

theorem U_le_AW : U ≤ A ⊔ (centerMod U K)ᵍ[t] := c.U_le_W.trans le_sup_right

theorem AW_le_K : A ⊔ (centerMod U K)ᵍ[t] ≤ K :=
  sup_le c.A_le_K (c.W_le_D.trans c.D_le_K)

theorem K_decomp {k : G} (hk : k ∈ K) :
    ∃ b ∈ A ⊔ (centerMod U K)ᵍ[t], ∃ v ∈ centerMod U K, k = b * v := by
  have hk' : k ∈ A ⊔ D := by
    rw [c.K_eq]
    exact hk
  obtain ⟨a, ha, d, hd, rfl⟩ := (mem_sup_iff_mul c.A_le_normalizer_D).1 hk'
  have hd' : d ∈ (centerMod U K)ᵍ[t] ⊔ centerMod U K := by
    rw [sup_comm, ← c.D_eq_sup]
    exact hd
  obtain ⟨w, hw, v, hv, rfl⟩ := (mem_sup_iff_mul c.W_le_normalizer_V).1 hd'
  exact ⟨a * w, mul_mem_sup ha hw, v, hv, by group⟩

theorem comm_K_le : ⁅K, K⁆ ≤ A ⊔ (centerMod U K)ᵍ[t] := by
  rw [commutator_le]
  intro k hk k' hk'
  obtain ⟨b, hb, v, hv, rfl⟩ := c.K_decomp hk
  obtain ⟨b', hb', v', hv', rfl⟩ := c.K_decomp hk'
  have hbK : b ∈ K := c.AW_le_K hb
  have hb'K : b' ∈ K := c.AW_le_K hb'
  have hvK : v ∈ K := c.V_le_D hv |> c.D_le_K
  have hv'K : v' ∈ K := c.V_le_D hv' |> c.D_le_K
  have hbN : b ∈ N := c.K_le_N hbK
  have hb'N : b' ∈ N := c.K_le_N hb'K
  have h1 : ⁅v, b' * v'⁆ ∈ U := by
    rw [commutatorElement_def]
    exact (c.mem_V.1 hv).2 _ (mul_mem hb'K hv'K)
  have h2 : ⁅b, v'⁆ ∈ U := by
    have := c.comm_K_V hbK hv'
    rwa [← commutatorElement_def] at this
  have e : ⁅b * v, b' * v'⁆ =
      (b * ⁅v, b' * v'⁆ * b⁻¹) * (⁅b, b'⁆ * (b' * ⁅b, v'⁆ * b'⁻¹)) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine mul_mem ?_ (mul_mem ?_ ?_)
  · rw [c.conj_U hbN h1]
    exact c.U_le_AW h1
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hb hb') (inv_mem hb)) (inv_mem hb')
  · rw [c.conj_U hb'N h2]
    exact c.U_le_AW h2

theorem comm_K_eq : ⁅K, K⁆ = A ⊔ (centerMod U K)ᵍ[t] := by
  refine le_antisymm c.comm_K_le (sup_le c.A_le_comm ?_)
  exact c.W_le_of_comm_le (Q := ⁅K, K⁆) c.U_le_comm
    (fun n hn => mem_normalizer_commutator (c.N_le_normalizer_K hn) (c.N_le_normalizer_K hn))
    (fun j hj => mem_normalizer_commutator (c.J_K hj) (c.J_K hj))
    (commutator_mono c.A_le_K (c.W_le_D.trans c.D_le_K))

theorem W_le_comm : (centerMod U K)ᵍ[t] ≤ ⁅K, K⁆ := by
  rw [c.comm_K_eq]
  exact le_sup_right

theorem comm_comm_sup : ⁅⁅K, K⁆, ⁅K, K⁆⁆ ⊔ U = ⁅K, K⁆ := by
  have hBN : ∀ g ∈ N, g ∈ normalizer ((⁅K, K⁆ : Subgroup G) : Set G) := fun n hn =>
    mem_normalizer_commutator (c.N_le_normalizer_K hn) (c.N_le_normalizer_K hn)
  have hBJ : ∀ g ∈ J, g ∈ normalizer ((⁅K, K⁆ : Subgroup G) : Set G) := fun j hj =>
    mem_normalizer_commutator (c.J_K hj) (c.J_K hj)
  refine le_antisymm (sup_le ?_ c.U_le_comm) ?_
  · rw [commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  · calc ⁅K, K⁆ = A ⊔ (centerMod U K)ᵍ[t] := c.comm_K_eq
      _ ≤ ⁅⁅K, K⁆, ⁅K, K⁆⁆ ⊔ U := by
        refine sup_le ?_ ?_
        · refine le_trans ?_ (le_sup_left : ⁅⁅K, K⁆, ⁅K, K⁆⁆ ≤ ⁅⁅K, K⁆, ⁅K, K⁆⁆ ⊔ U)
          calc A = ⁅A, A⁆ := c.A_perfect.symm
            _ ≤ ⁅⁅K, K⁆, ⁅K, K⁆⁆ := commutator_mono c.A_le_comm c.A_le_comm
        · refine c.W_le_of_comm_le (Q := ⁅⁅K, K⁆, ⁅K, K⁆⁆ ⊔ U) le_sup_right
            (fun n hn => mem_normalizer_sup
              (mem_normalizer_commutator (hBN n hn) (hBN n hn)) (c.N_le_normalizer_U hn))
            (fun j hj => mem_normalizer_sup
              (mem_normalizer_commutator (hBJ j hj) (hBJ j hj)) (c.J_U hj))
            (le_trans (commutator_mono c.A_le_comm c.W_le_comm) le_sup_left)

theorem Bt_eq : ⁅K, K⁆ᵍ[t] = Aᵍ[t] ⊔ centerMod U K := by
  rw [c.comm_K_eq, conjg_sup, c.W_conj]

theorem At_le_N : Aᵍ[t] ≤ N := (conjg_mono c.A_le_K t).trans c.Kt_le_N

theorem At_inf_D : Aᵍ[t] ⊓ D = ⊥ := by
  have h := conjg_inf A D t
  rw [c.A_inf_D, c.D_conj, Subgroup.map_bot] at h
  exact h.symm

theorem comm_inf : ⁅K, K⁆ ⊓ ⁅K, K⁆ᵍ[t] = U := by
  rw [c.Bt_eq]
  have hA : A ≤ normalizer (((centerMod U K)ᵍ[t] : Subgroup G) : Set G) := fun a ha =>
    c.N_le_normalizer_W (c.A_le_N ha)
  have hAt : Aᵍ[t] ≤ normalizer ((centerMod U K : Subgroup G) : Set G) := fun a ha =>
    c.N_le_normalizer_V (c.At_le_N ha)
  refine le_antisymm ?_ (le_inf (c.U_le_comm) (c.U_le_V.trans le_sup_right))
  rintro x ⟨hx1, hx2⟩
  rw [c.comm_K_eq] at hx1
  obtain ⟨a, ha, w, hw, rfl⟩ := (mem_sup_iff_mul hA).1 hx1
  obtain ⟨a', ha', v, hv, hx'⟩ := (mem_sup_iff_mul hAt).1 hx2
  have hwD := c.W_le_D hw
  have hvD := c.V_le_D hv
  have h1 : a⁻¹ * a' = w * v⁻¹ := by
    have : a' = a * w * v⁻¹ := by rw [← hx']; group
    rw [this]
    group
  have ha'K : a' ∈ K := by
    have : a' = a * (w * v⁻¹) := by rw [← mul_assoc, ← hx']; group
    rw [this]
    exact mul_mem (c.A_le_K ha) (c.D_le_K (mul_mem hwD (inv_mem hvD)))
  have ha'Kt : a' ∈ Kᵍ[t] := conjg_mono c.A_le_K t ha'
  have ha'D : a' ∈ D := by
    rw [← c.inf_eq]
    exact ⟨ha'K, ha'Kt⟩
  have ha'1 : a' = 1 := by
    have : a' ∈ Aᵍ[t] ⊓ D := ⟨ha', ha'D⟩
    rw [c.At_inf_D] at this
    exact this
  have haD : a ∈ D := by
    have h2 : a⁻¹ ∈ D := by
      have := h1
      rw [ha'1, mul_one] at this
      rw [this]
      exact mul_mem hwD (inv_mem hvD)
    simpa using inv_mem h2
  have ha1 : a = 1 := by
    have : a ∈ A ⊓ D := ⟨ha, haD⟩
    rw [c.A_inf_D] at this
    exact this
  subst ha1
  subst ha'1
  have hwv : w = v := by simpa using hx'.symm
  have : w ∈ centerMod U K ⊓ (centerMod U K)ᵍ[t] := ⟨hwv ▸ hv, hw⟩
  rw [c.V_inf_W] at this
  simpa using this

theorem comm_comm_t : ⁅⁅K, K⁆, ⁅K, K⁆ᵍ[t]⁆ ≤ U := by
  rw [c.Bt_eq]
  have hA : A ≤ normalizer (((centerMod U K)ᵍ[t] : Subgroup G) : Set G) := fun a ha =>
    c.N_le_normalizer_W (c.A_le_N ha)
  have hAt : Aᵍ[t] ≤ normalizer ((centerMod U K : Subgroup G) : Set G) := fun a ha =>
    c.N_le_normalizer_V (c.At_le_N ha)
  rw [commutator_le]
  intro b hb b' hb'
  rw [c.comm_K_eq] at hb
  obtain ⟨a, ha, w, hw, rfl⟩ := (mem_sup_iff_mul hA).1 hb
  obtain ⟨a', ha', v, hv, rfl⟩ := (mem_sup_iff_mul hAt).1 hb'
  have haK : a ∈ K := c.A_le_K ha
  have ha'Kt : a' ∈ Kᵍ[t] := conjg_mono c.A_le_K t ha'
  have haN : a ∈ N := c.A_le_N ha
  have ha'N : a' ∈ N := c.At_le_N ha'
  have h1 : ⁅w, a'⁆ ∈ U := by
    rw [commutatorElement_def]
    exact c.comm_Kt_W ha'Kt hw
  have h2 : ⁅w, v⁆ ∈ U := by
    rw [commutatorElement_def]
    exact c.comm_mem_U (c.W_le_D hw) (c.V_le_D hv)
  have h3 : ⁅a, a'⁆ = 1 := by
    have : ⁅a, a'⁆ ∈ ⁅A, Aᵍ[t]⁆ := commutator_mem_commutator ha ha'
    rwa [c.A_comm, Subgroup.mem_bot] at this
  have h4 : ⁅a, v⁆ ∈ U := by
    rw [commutatorElement_def]
    exact c.comm_K_V haK hv
  have e : ⁅a * w, a' * v⁆ = (a * (⁅w, a'⁆ * (a' * ⁅w, v⁆ * a'⁻¹)) * a⁻¹) *
      (⁅a, a'⁆ * (a' * ⁅a, v⁆ * a'⁻¹)) := by
    simp only [commutatorElement_def]
    group
  rw [e, h3, one_mul]
  refine mul_mem ?_ ?_
  · rw [c.conj_U haN (mul_mem h1 (by rw [c.conj_U ha'N h2]; exact h2))]
    exact mul_mem h1 (by rw [c.conj_U ha'N h2]; exact h2)
  · rw [c.conj_U ha'N h4]
    exact h4

theorem comm_le_K : ⁅K, K⁆ ≤ K := c.comm_K_eq.le.trans c.AW_le_K

theorem V_le_Bt : centerMod U K ≤ ⁅K, K⁆ᵍ[t] := by
  rw [c.Bt_eq]
  exact le_sup_right

theorem N_eq : N = ⁅K, K⁆ ⊔ ⁅K, K⁆ᵍ[t] := by
  have hD : D ≤ ⁅K, K⁆ ⊔ ⁅K, K⁆ᵍ[t] := by
    calc D = centerMod U K ⊔ (centerMod U K)ᵍ[t] := c.D_eq_sup
      _ ≤ _ := sup_le (c.V_le_Bt.trans le_sup_right) (c.W_le_comm.trans le_sup_left)
  have hAt : Aᵍ[t] ≤ ⁅K, K⁆ᵍ[t] := conjg_mono c.A_le_comm t
  have hK : K ≤ ⁅K, K⁆ ⊔ ⁅K, K⁆ᵍ[t] := by
    calc K = A ⊔ D := c.K_eq.symm
      _ ≤ _ := sup_le (c.A_le_comm.trans le_sup_left) hD
  have hKt : Kᵍ[t] ≤ ⁅K, K⁆ ⊔ ⁅K, K⁆ᵍ[t] := by
    calc Kᵍ[t] = Aᵍ[t] ⊔ D := by rw [← c.K_eq, conjg_sup, c.D_conj]
      _ ≤ _ := sup_le (hAt.trans le_sup_right) hD
  refine le_antisymm ?_ (sup_le (c.comm_le_K.trans c.K_le_N)
    ((conjg_mono c.comm_le_K t).trans c.Kt_le_N))
  calc N = K ⊔ Kᵍ[t] := c.sup_eq.symm
    _ ≤ _ := sup_le hK hKt

theorem W_eq_pCore :
    (centerMod U K)ᵍ[t] = pCoreOf 2 (A ⊔ (centerMod U K)ᵍ[t]) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWp : IsPGroup 2 ((centerMod U K)ᵍ[t] : Subgroup G) := c.D_pgroup.to_le c.W_le_D
  have hAnW : A ≤ normalizer (((centerMod U K)ᵍ[t] : Subgroup G) : Set G) := fun a ha =>
    c.N_le_normalizer_W (c.A_le_N ha)
  have hBnW : A ⊔ (centerMod U K)ᵍ[t] ≤ normalizer (((centerMod U K)ᵍ[t] : Subgroup G) : Set G) :=
    sup_le hAnW le_normalizer
  refine le_antisymm
    (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hBnW hWp) ?_
  set O := pCoreOf 2 (A ⊔ (centerMod U K)ᵍ[t]) with hO
  have hOB : O ≤ A ⊔ (centerMod U K)ᵍ[t] := LieType.BorelTits.pCoreOf_le 2 _
  have hOn : A ⊔ (centerMod U K)ᵍ[t] ≤ normalizer (O : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hOp : IsPGroup 2 O := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRp : IsPGroup 2 ↥(O ⊔ (centerMod U K)ᵍ[t]) :=
    hOp.to_sup_of_normal_right' hWp (hOB.trans hBnW)
  have hBR : A ⊔ (centerMod U K)ᵍ[t] ≤
      normalizer ((O ⊔ (centerMod U K)ᵍ[t] : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_sup (hOn hg) (hBnW hg)
  have hTn : ((A ⊓ (O ⊔ (centerMod U K)ᵍ[t])).subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact fun a ha => mem_normalizer_inf (le_normalizer ha) (hBR (Subgroup.mem_sup_left ha))
  haveI := c.A_simple
  have hT : A ⊓ (O ⊔ (centerMod U K)ᵍ[t]) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((A ⊓ (O ⊔ (centerMod U K)ᵍ[t])).subgroupOf A) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.1⟩ : ↥A) ∈ (A ⊓ (O ⊔ (centerMod U K)ᵍ[t])).subgroupOf A := hx
      rw [h, Subgroup.mem_bot] at this
      simpa using congrArg Subtype.val this
    · exfalso
      apply c.A_not_pgroup
      refine hRp.to_le (fun a ha => ?_)
      have : (⟨a, ha⟩ : ↥A) ∈ (A ⊓ (O ⊔ (centerMod U K)ᵍ[t])).subgroupOf A := by
        rw [h]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 this).2
  intro q hq
  obtain ⟨a, ha, w, hw, rfl⟩ := (mem_sup_iff_mul hAnW).1 (hOB hq)
  have ha' : a ∈ A ⊓ (O ⊔ (centerMod U K)ᵍ[t]) := by
    refine ⟨ha, ?_⟩
    have : a = (a * w) * w⁻¹ := by group
    rw [this]
    have hqO : a * w ∈ O ⊔ (centerMod U K)ᵍ[t] := mem_sup_left hq
    have hwO : w ∈ O ⊔ (centerMod U K)ᵍ[t] := mem_sup_right hw
    exact (O ⊔ (centerMod U K)ᵍ[t]).mul_mem hqO ((O ⊔ (centerMod U K)ᵍ[t]).inv_mem hwO)
  rw [hT, Subgroup.mem_bot] at ha'
  subst ha'
  simpa using hw

theorem derived₂_le_N : derived₂ K ≤ N :=
  (commutator_self_le _).trans (c.comm_le_K.trans c.K_le_N)

theorem K''_perfect : ⁅derived₂ K, derived₂ K⁆ = derived₂ K :=
  perfect_of_sup_central (B := ⁅K, K⁆) c.derived₂_le_N (c.U_le_D.trans c.D_le_N) c.U_central
    c.comm_comm_sup

theorem N_eq_K'' : N = derived₂ K ⊔ (derived₂ K)ᵍ[t] := by
  have hUN : U ≤ N := c.U_le_D.trans c.D_le_N
  have hB : derived₂ K ⊔ U = ⁅K, K⁆ := c.comm_comm_sup
  have hBt : (derived₂ K)ᵍ[t] ⊔ U = ⁅K, K⁆ᵍ[t] := by
    calc (derived₂ K)ᵍ[t] ⊔ U = (derived₂ K)ᵍ[t] ⊔ Uᵍ[t] := by rw [c.U_conj]
      _ = (derived₂ K ⊔ U)ᵍ[t] := (conjg_sup _ _ _).symm
      _ = ⁅K, K⁆ᵍ[t] := by rw [hB]
  have hYN : (derived₂ K)ᵍ[t] ≤ N := by
    have := conjg_mono c.derived₂_le_N t
    rwa [c.N_conj] at this
  have hY : ⁅(derived₂ K)ᵍ[t], (derived₂ K)ᵍ[t]⁆ = (derived₂ K)ᵍ[t] := by
    rw [← conjg_commutator, c.K''_perfect]
  have hNXYZ : N ≤ derived₂ K ⊔ (derived₂ K)ᵍ[t] ⊔ U := by
    rw [c.N_eq]
    refine sup_le (hB.symm.le.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      (hBt.symm.le.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  have hUNN : U ≤ ⁅N, N⁆ := by
    have := commutator_mono c.D_le_N c.D_le_N
    rwa [c.D_comm] at this
  exact eq_sup_of_perfect_central c.derived₂_le_N hYN c.K''_perfect hY hUN c.U_central hNXYZ hUNN

theorem main :
    (N = derivedMod U K ⊔ (derivedMod U K)ᵍ[t] ∧
      derivedMod U K ⊓ (derivedMod U K)ᵍ[t] = U ∧
      ⁅derivedMod U K, (derivedMod U K)ᵍ[t]⁆ ≤ U ∧
      derivedMod U (derivedMod U K) = derivedMod U K ∧
      derivedMod U K = A ⊔ centerMod U (Kᵍ[t]) ∧
      centerMod U (Kᵍ[t]) = pCoreOf 2 (derivedMod U K) ∧
      centerMod U K ⊔ centerMod U (Kᵍ[t]) = D ∧
      centerMod U K ⊓ centerMod U (Kᵍ[t]) = U) ∧
    (N = derived₁ K ⊔ (derived₁ K)ᵍ[t] ∧
      N = derived₂ K ⊔ (derived₂ K)ᵍ[t] ∧
      ⁅derived₂ K, derived₂ K⁆ = derived₂ K ∧
      derived₁ K ⊓ (derived₁ K)ᵍ[t] = U) := by
  have e1 : derivedMod U K = ⁅K, K⁆ := sup_eq_left.2 c.U_le_comm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, c.V_inf⟩, c.N_eq, c.N_eq_K'', c.K''_perfect,
    c.comm_inf⟩
  · rw [e1]
    exact c.N_eq
  · rw [e1]
    exact c.comm_inf
  · rw [e1]
    exact c.comm_comm_t
  · rw [e1]
    exact c.comm_comm_sup
  · rw [e1, c.Vt_eq]
    exact c.comm_K_eq
  · rw [e1, c.Vt_eq, c.comm_K_eq]
    exact c.W_eq_pCore
  · rw [c.Vt_eq]
    exact c.D_eq_sup.symm

end Basic

end Ctx

end ProductN1DecompAux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamada_7_9 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) :
    (yamadaN₁ d t = derivedMod (yamadaU₁ d t) Λ₁ ⊔ (derivedMod (yamadaU₁ d t) Λ₁)ᵍ[t] ∧
      derivedMod (yamadaU₁ d t) Λ₁ ⊓ (derivedMod (yamadaU₁ d t) Λ₁)ᵍ[t] = yamadaU₁ d t ∧
      ⁅derivedMod (yamadaU₁ d t) Λ₁, (derivedMod (yamadaU₁ d t) Λ₁)ᵍ[t]⁆ ≤ yamadaU₁ d t ∧
      derivedMod (yamadaU₁ d t) (derivedMod (yamadaU₁ d t) Λ₁) =
        derivedMod (yamadaU₁ d t) Λ₁ ∧
      derivedMod (yamadaU₁ d t) Λ₁ =
        leviFactor₁ d Λ₁ ⊔ centerMod (yamadaU₁ d t) (Λ₁ᵍ[t]) ∧
      centerMod (yamadaU₁ d t) (Λ₁ᵍ[t]) = pCoreOf 2 (derivedMod (yamadaU₁ d t) Λ₁) ∧
      centerMod (yamadaU₁ d t) Λ₁ ⊔ centerMod (yamadaU₁ d t) (Λ₁ᵍ[t]) = yamadaD₇ d t ∧
      centerMod (yamadaU₁ d t) Λ₁ ⊓ centerMod (yamadaU₁ d t) (Λ₁ᵍ[t]) = yamadaU₁ d t) ∧
    (yamadaN₁ d t = derived₁ Λ₁ ⊔ (derived₁ Λ₁)ᵍ[t] ∧
      yamadaN₁ d t = derived₂ Λ₁ ⊔ (derived₂ Λ₁)ᵍ[t] ∧
      ⁅derived₂ Λ₁, derived₂ Λ₁⁆ = derived₂ Λ₁ ∧
      derived₁ Λ₁ ⊓ (derived₁ Λ₁)ᵍ[t] = yamadaU₁ d t) := by
  have hfac := hL.fac₁
  have h76 := yamada_7_6 hW h d hK hQ hp hfac
  have h78 := yamada_7_8 hW h d hK hQ hp hL
  have hDF := hQ.doubling
  have ht2 := h.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hUD : yamadaU₁ d t ≤ yamadaD₇ d t := h.yamadaU₁_le_yamadaD₇ hW d hK hQ
  have hDN : yamadaD₇ d t ≤ yamadaN₁ d t := yamadaD₇_le_yamadaN₁ d t
  have hUc : yamadaU₁ d t ≤ centralizer (yamadaN₁ d t : Set G) := fun u hu =>
    (Subgroup.mem_inf.1 (h76.2.1.1 ▸ hu : u ∈ zc (yamadaN₁ d t))).2
  have hNU : yamadaN₁ d t ≤ normalizer (yamadaU₁ d t : Set G) :=
    ProductN1DecompAux.le_normalizer_of_le_centralizer hUc
  have htU : t ∈ normalizer (yamadaU₁ d t : Set G) := (h.t_mem_normalizer_yamadaU₁ d hK hDF).1
  have hPD : IsPGroup 2 (yamadaP d t) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ((CFSG.ABGLocalTools.isSylowOf_iff).1 hp.sylow₁).2.1
  have hDp : IsPGroup 2 (yamadaD₇ d t) := hPD.to_le (yamadaD₇_le_yamadaP d t)
  have hfix : ∀ x ∈ yamadaD₇ d t, x * t * x⁻¹ * t⁻¹ ∈ yamadaU₁ d t → x ∈ yamadaD₁ d t := by
    intro x hx hxt
    have hxC : x ∈ yamadaCstar d t := yamadaD₇_le_yamadaC₇ d t hx
    have hxV : x ∈ h.yamadaV d hK hDF := (h.yamadaCstar_eq d hK hDF) ▸ hxC
    have e : (x * t * x⁻¹ * t⁻¹)⁻¹ = t * x * t * x⁻¹ := by
      have : (x * t * x⁻¹ * t⁻¹)⁻¹ = t * x * t⁻¹ * x⁻¹ := by group
      rw [this, hti]
    have hx' : t * x * t * x⁻¹ ∈ yamadaU₁ d t := by
      rw [← e]
      exact inv_mem hxt
    exact Setup.Q52.yamadaC₁_inf_yamadaD₇_le hW h d hK hQ
      ⟨h.mem_yamadaC₁_of_crossed_mem d hK hDF hxV hx', hx⟩
  have hD₁fix : ∀ x ∈ yamadaD₁ d t, x * t * x⁻¹ * t⁻¹ ∈ yamadaU₁ d t := by
    intro x hx
    have htC : t ∈ yamadaCstar d t := by
      rw [h.yamadaCstar_eq d hK hDF]
      exact h.yamadaC₁_le_yamadaV d hK hDF (h.t_mem_yamadaC₁ d hK)
    have h1 := ((h.yamada_5_19 d hK hDF).2.2.1) t htC x hx
    have e : x * t * x⁻¹ * t⁻¹ = (t * x * t⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have hcard : Nat.card (yamadaD₇ d t) * Nat.card (yamadaU₁ d t) = Nat.card (yamadaD₁ d t) ^ 2 := by
    rw [h.card_yamadaD₇ hW d hK hQ, hDF.card_eq, h.card_yamadaD₁_of_doubling d hDF]
    ring
  have hKN : yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G) :=
    (ProductN1DecompAux.commutator_self_le _).trans
      (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).1
  have hN₁D : yamadaN₁ d t ≤ normalizer (yamadaD₇ d t : Set G) :=
    yamadaN₁_le_normalizer d t hKN
  obtain ⟨hcompl, hcinf, hleviA⟩ := hp.compl₁
  have hΛN : Λ₁ ≤ yamadaN₁ d t := hfac.le
  have hA_Ast : leviFactor₁ d Λ₁ ≤ yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G) := fun a ha =>
    ⟨hΛN (Subgroup.mem_inf.1 ha).1, (Subgroup.mem_inf.1 ha).2⟩
  have hKeq : leviFactor₁ d Λ₁ ⊔ yamadaD₇ d t = Λ₁ := by
    refine le_antisymm (sup_le inf_le_left hfac.X_le) ?_
    intro k hk
    have hk' : k ∈ (yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)) ⊔ yamadaD₇ d t := by
      rw [← hcompl]
      exact hΛN hk
    obtain ⟨a, ha, δ, hδ, rfl⟩ := (ProductN1DecompAux.mem_sup_iff_mul
      (X := yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)) (Y := yamadaD₇ d t)
      (fun g hg => hN₁D hg.1)).1 hk'
    have haΛ : a ∈ Λ₁ := by
      have : a = (a * δ) * δ⁻¹ := by group
      rw [this]
      exact Λ₁.mul_mem hk (Λ₁.inv_mem (hfac.X_le hδ))
    exact mul_mem_sup (show a ∈ leviFactor₁ d Λ₁ from ⟨haΛ, ha.2⟩) hδ
  have hAD : leviFactor₁ d Λ₁ ⊓ yamadaD₇ d t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have : x ∈ (yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)) ⊓ yamadaD₇ d t :=
      ⟨hA_Ast hx.1, hx.2⟩
    rw [hcinf] at this
    exact this
  have hJ₃t : d.J₃ ≤ centralizer ({t} : Set G) := fun j hj =>
    h.L_le_centralizer (d.image_le _ hj)
  have hAt_Ast : (leviFactor₁ d Λ₁)ᵍ[t] ≤ yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G) := by
    intro x hx
    have hx' : t * x * t⁻¹ ∈ leviFactor₁ d Λ₁ := ProductN1DecompAux.mem_conjg_iff.1 hx
    refine ⟨?_, ?_⟩
    · have hxΛ : x ∈ Λ₁ᵍ[t] := ProductN1DecompAux.conjg_mono inf_le_left t hx
      have : Λ₁ᵍ[t] ≤ yamadaN₁ d t := hfac.sup ▸ le_sup_right
      exact this hxΛ
    · show x ∈ centralizer (d.J₃ : Set G)
      rw [mem_centralizer_iff]
      intro j hj
      have hc1 : Commute j t := mem_centralizer_singleton_iff.1 (hJ₃t hj)
      have hc2 : Commute j (t * x * t⁻¹) := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx').2 j hj
      have hx_eq : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      have hc3 : Commute j x := by
        rw [hx_eq]
        exact ((hc1.inv_right).mul_right hc2).mul_right hc1
      exact hc3
  have hAcomm : ⁅leviFactor₁ d Λ₁, (leviFactor₁ d Λ₁)ᵍ[t]⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h1 : x ∈ yamadaD₇ d t :=
      hfac.comm (commutator_mono inf_le_left (ProductN1DecompAux.conjg_mono inf_le_left t) hx)
    have h2 : x ∈ yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G) :=
      ((commutator_mono hA_Ast hAt_Ast).trans (ProductN1DecompAux.commutator_self_le _)) hx
    have : x ∈ (yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)) ⊓ yamadaD₇ d t := ⟨h2, h1⟩
    rw [hcinf] at this
    exact this
  have hJ₃D₇ : d.J₃ ≤ normalizer (yamadaD₇ d t : Set G) := fun j hj =>
    h.J_le_normalizer_yamadaD₇ hW d hK hQ (Setup.J₃_le_J d hj)
  have hJ₃A : d.J₃ ≤ normalizer ((leviFactor₁ d Λ₁ : Subgroup G) : Set G) := fun j hj => by
    have hjA : j ∈ centralizer ((leviFactor₁ d Λ₁ : Subgroup G) : Set G) :=
      mem_centralizer_iff.2 fun a ha => (mem_centralizer_iff.1 (Subgroup.mem_inf.1 ha).2 j hj).symm
    exact Subgroup.centralizer_le_normalizer _ hjA
  have hJK : d.J₃ ≤ normalizer (Λ₁ : Set G) := fun j hj => by
    have := ProductN1DecompAux.mem_normalizer_sup (hJ₃A hj) (hJ₃D₇ hj)
    rwa [hKeq] at this
  have hirr : ∀ X : Subgroup G, yamadaU₁ d t ≤ X → yamadaN₁ d t ≤ normalizer (X : Set G) →
      d.J₃ ≤ normalizer (X : Set G) → X ⊓ yamadaD₁ d t = yamadaU₁ d t ∨ yamadaD₁ d t ≤ X := by
    intro X hUX hNX hJX
    obtain ⟨hUY, hYX, -, hXF, -, hFD, -, -, -, -⟩ := d.inclusions
    have hUD₀ : d.U ≤ d.D := hUY.trans (hYX.trans (hXF.trans hFD))
    have hDD : d.D ≤ yamadaD₇ d t := h.D_le_yamadaD₇ hW d hK hQ
    have hUE : d.U ≤ d.D ⊓ X := le_inf hUD₀ (hDF.U_le.trans hUX)
    have hLU := (d.yamada_3_13_2_G).1
    have hLD := (d.yamada_3_13_2_G).2.1
    have hLevi : d.leviA ≤ normalizer (d.D : Set G) := by
      have : d.leviA ≤ L ⊓ normalizer (d.D : Set G) := by
        rw [hLD]
        exact (le_sup_left : d.leviA ≤ d.leviA ⊔ d.J₃).trans le_sup_right
      exact this.trans inf_le_right
    have hJD₀ : d.J₃ ≤ normalizer (d.D : Set G) := by
      have : d.J₃ ≤ L ⊓ normalizer (d.D : Set G) := by
        rw [hLD]
        exact (le_sup_right : d.J₃ ≤ d.leviA ⊔ d.J₃).trans le_sup_right
      exact this.trans inf_le_right
    have hnorm : L ⊓ normalizer (d.U : Set G) ≤ normalizer ((d.D ⊓ X : Subgroup G) : Set G) := by
      rw [hLU]
      refine sup_le (fun δ hδ => ?_) (sup_le (fun a ha => ?_) (fun j hj => ?_))
      · exact mem_normalizer_inf (Subgroup.le_normalizer hδ) (hNX (hDN (hDD hδ)))
      · exact mem_normalizer_inf (hLevi ha) (hNX (hleviA ha).1)
      · exact mem_normalizer_inf (hJD₀ hj) (hJX hj)
    rcases (d.yamada_3_16_1_G hQ.four_le hUE inf_le_left).1 hnorm with hE | hE
    · left
      refine le_antisymm ?_ (le_inf hUX hDF.le_D₁)
      rintro x ⟨hxX, hxD₁⟩
      rw [hDF.D₁_eq] at hxD₁
      have hDU : d.D ≤ normalizer (yamadaU₁ d t : Set G) := fun g hg =>
        Subgroup.centralizer_le_normalizer _ (hDF.D_le_centralizer hg)
      obtain ⟨δ, hδ, u, hu, rfl⟩ := (ProductN1DecompAux.mem_sup_iff_mul hDU).1 hxD₁
      have hδX : δ ∈ X := by
        have := X.mul_mem hxX (X.inv_mem (hUX hu))
        rwa [mul_inv_cancel_right] at this
      have hδU : δ ∈ d.D ⊓ X := ⟨hδ, hδX⟩
      rw [hE] at hδU
      exact (yamadaU₁ d t).mul_mem (hDF.U_le hδU) hu
    · right
      rw [hDF.D₁_eq]
      refine sup_le ?_ hUX
      calc d.D = d.D ⊓ X := hE.symm
        _ ≤ X := inf_le_right
  have hctx : ProductN1DecompAux.Ctx K t (yamadaN₁ d t) Λ₁ (yamadaD₇ d t) (yamadaU₁ d t)
      (leviFactor₁ d Λ₁) (yamadaD₁ d t) d.J₃ :=
    { four_le := hQ.four_le
      t_mul_t := ht2
      D_le_K := hfac.X_le
      K_le_N := hfac.le
      sup_eq := hfac.sup
      inf_eq := hfac.inf
      comm_le := hfac.comm
      quot := hfac.quot
      U_le_D := hUD
      U_central := hUc
      U_conj := by
        ext x
        rw [ProductN1DecompAux.mem_conjg_iff]
        exact (mem_normalizer_iff.1 htU x).symm
      D_comm := (h.yamada_5_55_1 hW d hK hQ).1.2
      D_pgroup := hDp
      V_lt := h78
      V_inf := h76.2.2.2.2
      CD := fun x hx hxd => by
        have : x ∈ yamadaN₁ d t ⊓ centralizerMod (yamadaU₁ d t) (yamadaD₇ d t) :=
          ⟨hx, (mem_centralizerMod_iff).2 ⟨hNU hx, fun b hb _ => hxd b hb⟩⟩
        rw [h76.2.1.2.2] at this
        exact this
      A_le_K := inf_le_left
      K_eq := hKeq
      A_inf_D := hAD
      A_comm := hAcomm
      D₁_le_D := h.yamadaD₁_le_yamadaD₇ hW d hK hQ
      U_le_D₁ := hDF.le_D₁
      D₁_fix := hD₁fix
      fix := hfix
      card_D₁ := hcard
      irr := hirr
      J_K := hJK
      J_U := fun j hj => h.J_le_normalizer_yamadaU₁ d hK hDF (Setup.J₃_le_J d hj)
      J_t := hJ₃t }
  exact hctx.main

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
