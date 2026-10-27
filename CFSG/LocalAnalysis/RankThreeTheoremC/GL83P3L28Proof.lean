module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28PartsS
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28ThreeProved
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVYoshida
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVCube
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2FusionFocal3
import CFSG.LocalAnalysis.GL83PartI.I_28_3_S3
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3Rest
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Comm
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Eigen
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Lift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43W
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3HF
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3FusionLines

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

@[expose] def ThreeSolvableChain {G : Type} [Group G] (W : Subgroup G) : Prop :=
  ∃ (N₀ : Subgroup G) (H : Type) (_ : Group H) (f : ↥W →* H), N₀ ≤ W ∧
    (N₀.subgroupOf W).Normal ∧ ¬ 3 ∣ Nat.card N₀ ∧ Group.IsSolvable H ∧
    ∀ w : ↥W, f w = 1 → ∃ n : ℕ, (w : G) ^ 3 ^ n ∈ N₀

structure L28ClosedConfig (G : Type) [Group G] [Finite G] (M P : Subgroup G) (x k : G) : Prop where
  kgroup : CatalogSimpleSections ↥M
  sylow : IsSylowOf 3 P M
  focal : P ≤ ⁅M, M⁆
  shape : L28Shape 3 P
  x_mem : x ∈ L28Z P
  x_ne : x ≠ 1
  k_mem : k ∈ P
  k_order : orderOf k = 9
  k_norm : P ≤ normalizer (zpowers k : Set G)
  k_cube : k ^ 3 ∈ L28Z P
  x_not : x ∉ zpowers k
  swap : ∃ n ∈ M, n ∈ normalizer (P : Set G) ∧ n * x * n⁻¹ ∈ zpowers (k ^ 3)
  invert : ∃ ι ∈ M, ι * x * ι⁻¹ = x ∧ ι * k ^ 3 * ι⁻¹ = (k ^ 3)⁻¹
  z_card : Nat.card (L28Z P) = 3 ^ 2
  fusion : ∀ g ∈ M, g * x * g⁻¹ ∈ P → g * x * g⁻¹ ∈ L28Z P
  solv : ThreeSolvableChain (M ⊓ centralizer ({x} : Set G))

@[expose] def KFactL28Closed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M P : Subgroup G) (x k : G), L28ClosedConfig G M P x k →
    ∃ N : Subgroup G, GLBPrimeCore 3 M < N ∧ N ≤ M ∧ M ≤ normalizer (N : Set G) ∧
      ∀ g ∈ N, ∃ n : ℕ, g ^ 3 ^ n ∈ GLBPrimeCore 3 M

@[expose] def KFactL28Endgame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M F U R₀ : Subgroup G) (x : G),
    CatalogSimpleSections ↥H → IsSylowOf 3 F H → ¬ IsMulCommutative F → Nat.card F = 3 ^ 3 →
    F ≤ M → U ≤ F → IsElemAbelian 3 U → Nat.card U = 3 ^ 2 → (∀ f ∈ F, f ^ 3 = 1 → f ∈ U) →
    x ∈ U → x ≠ 1 → (∀ f ∈ F, f * x = x * f) →
    (∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ⊓ H ≤ M) →
    IsPGroup 2 R₀ → R₀ ≤ H → U ≤ normalizer (R₀ : Set G) → R₀ ≤ GLBPrimeCore 3 M →
    R₀ ≤ GLBPrimeCore 3 H

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Aux

variable {G : Type} [Group G] [Finite G]

section CaseOne

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin
  CFSG.Quasithin.F53Push CFSG.ABGLocalTools Subgroup
open scoped Pointwise commutatorElement

omit [Finite G] in
theorem comm_eq_bot_of_centralizes {X : Subgroup G} {u : G} (hX : IsElemAbelian 2 X)
    (huX : u ∈ normalizer (X : Set G)) (hu3 : u ^ 3 = 1)
    (hc : ⁅X, zpowers u⁆ ≤ centralizer ({u} : Set G)) : ⁅X, zpowers u⁆ = ⊥ := by
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb => by
    have := hX.1
    exact setLike_mul_comm (s := X) ha hb
  have hsq : ∀ a ∈ X, a * a = 1 := fun a ha => by rw [← pow_two]; exact hX.2 a ha
  have hconj : ∀ a ∈ X, u * a * u⁻¹ ∈ X := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp huX a).mp ha
  have hinv : ∀ a ∈ X, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hsq a ha)
  have hu3' : u * u * u = 1 := by
    rw [show u * u * u = u ^ 3 by rw [pow_succ, pow_succ, pow_one]]
    exact hu3
  have hX1 : ∀ x ∈ X, u * x * u⁻¹ = x := by
    intro x hx
    have hb := hconj x hx
    have hd := hconj _ hb
    have hcm : ⁅x, u⁆ ∈ ⁅X, zpowers u⁆ := Subgroup.commutator_mem_commutator hx (mem_zpowers u)
    have hcu := Subgroup.mem_centralizer_singleton_iff.mp (hc hcm)
    have hc1 : ⁅x, u⁆ = x * (u * x * u⁻¹) := by
      rw [commutatorElement_def]
      calc x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
        _ = x * (u * x * u⁻¹) := by
          have : u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by group
          rw [this, hinv _ hb]
    have hcc : u * ⁅x, u⁆ * u⁻¹ = ⁅x, u⁆ := by
      calc u * ⁅x, u⁆ * u⁻¹ = (⁅x, u⁆ * u) * u⁻¹ := by rw [← hcu]
        _ = ⁅x, u⁆ := by group
    rw [hc1] at hcc
    have hd' : u * (u * x * u⁻¹) * u⁻¹ = u * u * x * u⁻¹ * u⁻¹ := by group
    have e1 : u * (x * (u * x * u⁻¹)) * u⁻¹ =
        (u * x * u⁻¹) * (u * (u * x * u⁻¹) * u⁻¹) := by group
    rw [e1] at hcc
    have hxd : x = u * (u * x * u⁻¹) * u⁻¹ := by
      have h2 : (u * x * u⁻¹) * (u * (u * x * u⁻¹) * u⁻¹) = x * (u * x * u⁻¹) := hcc
      have h3 : (u * x * u⁻¹) * x = (u * x * u⁻¹) * (u * (u * x * u⁻¹) * u⁻¹) := by
        calc (u * x * u⁻¹) * x = x * (u * x * u⁻¹) := hcomm _ hb _ hx
          _ = _ := h2.symm
      exact mul_left_cancel h3
    have hx3 : u * x * u⁻¹ = x := by
      calc u * x * u⁻¹ = u * (u * (u * x * u⁻¹) * u⁻¹) * u⁻¹ := by rw [← hxd]
        _ = (u * u * u) * x * (u * u * u)⁻¹ := by group
        _ = x := by rw [hu3']; group
    exact hx3
  rw [eq_bot_iff]
  rw [Subgroup.commutator_le]
  intro x hx w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hxu : ∀ x ∈ X, x * u = u * x := fun x hx => by
    have := hX1 x hx
    calc x * u = (u * x * u⁻¹) * u := by rw [this]
      _ = u * x := by group
  have hcentral : Commute x u := hxu x hx
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
  exact Commute.zpow_right hcentral k

omit [Finite G] in
theorem isElemAbelian_of_le {p : ℕ} {A B : Subgroup G} (h : IsElemAbelian p A) (hBA : B ≤ A) :
    IsElemAbelian p B := by
  have := h.1
  exact ⟨⟨⟨fun a b => Subtype.ext (setLike_mul_comm (hBA a.2) (hBA b.2))⟩⟩,
    fun a ha => h.2 a (hBA ha)⟩

omit [Finite G] in
theorem le_normalizer_of_comm {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ normalizer (B : Set G) := fun a ha => by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : a * h * a⁻¹ = h := by rw [hcomm a ha h hh]; group
    rw [this]
    exact hh
  · intro hh
    have hc : a⁻¹ * (a * h * a⁻¹) = (a * h * a⁻¹) * a⁻¹ := hcomm a⁻¹ (A.inv_mem ha) _ hh
    have : h = a * h * a⁻¹ := by
      calc h = a⁻¹ * (a * h * a⁻¹) * a := by group
        _ = ((a * h * a⁻¹) * a⁻¹) * a := by rw [hc]
        _ = a * h * a⁻¹ := by group
    rw [this]
    exact hh

omit [Finite G] in
theorem isElemAbelian_sup {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian p (A ⊔ B) := by
  have hA' := hA.1
  have hB' := hB.1
  have hAB : A ≤ normalizer (B : Set G) := le_normalizer_of_comm hcomm
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hAB
  have hmem : ∀ z ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, z = a * b := by
    intro z hz
    have : z ∈ (A : Set G) * (B : Set G) := by rw [← hset]; exact hz
    obtain ⟨a, ha, b, hb, rfl⟩ := this
    exact ⟨a, ha, b, hb, rfl⟩
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨a, ha, b, hb, hx⟩ := hmem x x.2
    obtain ⟨a', ha', b', hb', hy⟩ := hmem y y.2
    apply Subtype.ext
    show (x : G) * y = y * x
    rw [hx, hy]
    have h1 : a * b' = b' * a := hcomm a ha b' hb'
    have h2 : a' * b = b * a' := hcomm a' ha' b hb
    have h3 : a * a' = a' * a := setLike_mul_comm ha ha'
    have h4 : b * b' = b' * b := setLike_mul_comm hb hb'
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← h2]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [h3, h4]
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [h1]
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem z hz
    have hab : Commute a b := hcomm a ha b hb
    rw [hab.mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

omit [Finite G] in
theorem commutator_le_of_mem_normalizer {X : Subgroup G} {u : G} (hu : u ∈ normalizer (X : Set G)) :
    ⁅X, zpowers u⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx w hw
  have hw' : w ∈ normalizer (X : Set G) := (Subgroup.zpowers_le.mpr hu) hw
  have h1 : w * x⁻¹ * w⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hw' x⁻¹).mp (X.inv_mem hx)
  have : ⁅x, w⁆ = x * (w * x⁻¹ * w⁻¹) := by rw [commutatorElement_def]; group
  rw [this]
  exact X.mul_mem hx h1

omit [Finite G] in
theorem no_cube_action {X P : Subgroup G} {u : G} (hX : IsElemAbelian 2 X)
    (hPX : P ≤ normalizer (X : Set G)) (huP : u ∈ P) (hu3 : u ^ 3 = 1)
    (hcen : ∀ p ∈ P, p * u = u * p) (hcube : ∃ a ∈ P, a ^ 3 = u)
    (h4 : Nat.card (⁅X, zpowers u⁆ : Subgroup G) = 4) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V : Subgroup G := ⁅X, zpowers u⁆ with hV
  have hunorm : u ∈ normalizer (X : Set G) := hPX huP
  have hVX : V ≤ X := commutator_le_of_mem_normalizer hunorm
  have hnt : ∃ v ∈ V, u * v * u⁻¹ ≠ v := by
    by_contra hall
    push Not at hall
    have hc : ⁅X, zpowers u⁆ ≤ centralizer ({u} : Set G) := fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mpr (by
        have := hall v hv
        calc v * u = (u * v * u⁻¹) * u := by rw [this]
          _ = u * v := by group)
    have hbot := comm_eq_bot_of_centralizes hX hunorm hu3 hc
    rw [← hV] at hbot
    rw [hbot, Subgroup.card_bot] at h4
    omega
  have hPV : P ≤ normalizer (V : Set G) := by
    intro p hp
    have hpX : p ∈ normalizer (X : Set G) := hPX hp
    have hX' : X.map (MulAut.conj p).toMonoidHom = X := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hpX z).mp hz
      · intro hy
        refine ⟨p⁻¹ * y * p, ?_, by simp [MulAut.conj_apply]; group⟩
        have := (Subgroup.mem_normalizer_iff.mp ((normalizer (X : Set G)).inv_mem hpX) y).mp hy
        simpa using this
    have hz' : (zpowers u).map (MulAut.conj p).toMonoidHom = zpowers u := by
      rw [MonoidHom.map_zpowers]
      have : (MulAut.conj p).toMonoidHom u = u := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hcen p hp]; group
      rw [this]
    have hmap : V.map (MulAut.conj p).toMonoidHom = V := by
      rw [hV, Subgroup.map_commutator, hX', hz']
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hmap]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← hmap] at hh
      obtain ⟨y, hy, hyh⟩ := hh
      have : y = h := by
        have := (MulAut.conj p).injective
          (by simpa using hyh : (MulAut.conj p) y = (MulAut.conj p) h)
        exact this
      rw [← this]
      exact hy
  let c : ↥P →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hPV)
  obtain ⟨a, haP, ha3⟩ := hcube
  have hc3 : (c ⟨a, haP⟩) ^ 3 = c ⟨u, huP⟩ := by
    rw [← map_pow]
    congr 1
    exact Subtype.ext (by simpa using ha3)
  have hcu3 : (c ⟨u, huP⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨u, huP⟩ : ↥P) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
    rw [this, map_one]
  have hcu1 : c ⟨u, huP⟩ ≠ 1 := by
    obtain ⟨v, hv, hne⟩ := hnt
    intro h1
    apply hne
    have h2 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h1
    simpa [c, Subgroup.normalizerMonoidHom_apply_apply_coe] using h2
  have hord : orderOf (c ⟨a, haP⟩) = 9 := by
    have h := orderOf_eq_prime_pow (p := 3) (n := 1) (x := c ⟨a, haP⟩)
      (by rw [pow_one, hc3]; exact hcu1) (by
        rw [show 3 ^ (1 + 1) = 3 * 3 by norm_num, pow_mul, hc3, hcu3])
    simpa using h
  have hVc : Nat.card V = 4 := h4
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype V := Fintype.ofFinite _
  have htoPerm : Function.Injective (MulAut.toPerm (M := ↥V)) := by
    intro α β hαβ
    refine MulEquiv.ext fun x => ?_
    exact congrArg (fun σ : Equiv.Perm ↥V => σ x) hαβ
  have hdvd : Nat.card (MulAut ↥V) ∣ Nat.card (Equiv.Perm ↥V) :=
    Subgroup.card_dvd_of_injective (MulAut.toPerm (M := ↥V)) htoPerm
  have hperm : Nat.card (Equiv.Perm ↥V) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hVc]
    rfl
  have h9 : 9 ∣ Nat.card (MulAut ↥V) := hord ▸ orderOf_dvd_natCard _
  have := h9.trans hdvd
  rw [hperm] at this
  omega

structure CoreData (G : Type) [Group G] [Finite G] (M O Z P U : Subgroup G) (x : G) : Prop where
  O_le : O ≤ M
  O_norm : M ≤ normalizer (O : Set G)
  O_cop : ¬ 3 ∣ Nat.card O
  O₂_le : pCoreOf 2 M ≤ O
  O₂_ne : pCoreOf 2 M ≠ ⊥
  charTwo : CharTwo M
  Z_le : Z ≤ M
  Z_el : IsElemAbelian 3 Z
  Z_card : Nat.card Z = 9
  Z_norm : M ≤ normalizer ((Z ⊔ O : Subgroup G) : Set G)
  x_mem : x ∈ Z
  x_ne : x ≠ 1
  U_le : U ≤ M
  U_el : IsElemAbelian 3 U
  U_card : Nat.card U = 9
  xU : x ∈ U
  U_inf_Z : U ⊓ Z = zpowers x
  U_comm : ∀ a ∈ U, ∀ z ∈ Z, a * z = z * a
  P_le : P ≤ M
  Z_le_P : Z ≤ P
  P_cen : ∀ z ∈ Z, ∀ p ∈ P, p * z = z * p
  Z_cube : ∀ z ∈ Z, ∃ a ∈ P, a ^ 3 = z
  D1 : ∀ Y₀ : Subgroup G, Y₀ ≠ ⊥ → IsPGroup 2 Y₀ →
    3 ≤ CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M) → normalizer (Y₀ : Set G) ≤ M

theorem CoreData.false_of_small {M O Z P U : Subgroup G} {x : G} (h : CoreData G M O Z P U x)
    {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M) (hYO : IsSylowOf 2 (Y ⊓ O) O)
    (hUY : U ≤ normalizer (Y : Set G))
    (hsmall : ∀ Y₀ : Subgroup G, Y₀ ≤ Y → Y₀ ≠ ⊥ → (Y₀.subgroupOf Y).Characteristic →
      CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M) < 3) : False := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZO : Z ≤ normalizer (O : Set G) := h.Z_le.trans h.O_norm
  have hZ3 : ∀ k ∈ Z, k ^ 3 = 1 := h.Z_el.2
  have hYO' : Y ≤ normalizer (O : Set G) := hYM.trans h.O_norm
  have hYB : Y ≤ normalizer ((Z ⊔ O : Subgroup G) : Set G) := hYM.trans h.Z_norm
  have hBO : (Z ⊔ O : Subgroup G) ≤ normalizer (O : Set G) :=
    sup_le hZO Subgroup.le_normalizer
  have hBM : (Z ⊔ O : Subgroup G) ≤ M := sup_le h.Z_le h.O_le
  have hYB_O : Y ⊓ (Z ⊔ O) ≤ O := e9_inf_sup_le hZO hZ3 hY2
  have hxB : x ∈ Z ⊔ O := mem_sup_left h.x_mem
  have hrankE : ∀ E : Subgroup G, IsElemAbelian 3 E → Nat.card E = 27 →
      ∀ Y₀ : Subgroup G, Y₀ ≤ Y → Y₀ ≠ ⊥ → (Y₀.subgroupOf Y).Characteristic →
        ¬ E ≤ (normalizer (Y₀ : Set G) ⊓ M) ⊔ O := by
    intro E hEel hE27 Y₀ hle hne hch hEle
    have h3 := l43_three_le_pRank_of_le_sup (H := normalizer (Y₀ : Set G) ⊓ M) (O := O)
      (E := E) (inf_le_right.trans h.O_norm) h.O_cop hEel hE27 hEle
    exact absurd h3 (not_le.mpr (hsmall Y₀ hle hne hch))
  have hUZ : U ≤ normalizer (Z : Set G) := le_normalizer_of_comm h.U_comm
  have hUZcard : Nat.card (U ⊔ Z : Subgroup G) = 27 := by
    have hc := e9_card_sup_mul_card_inf hUZ
    rw [h.U_inf_Z, Nat.card_zpowers, orderOf_eq_prime (h.Z_el.2 x h.x_mem) h.x_ne, h.U_card,
      h.Z_card] at hc
    omega
  have hUZel : IsElemAbelian 3 (U ⊔ Z) := isElemAbelian_sup h.U_el h.Z_el h.U_comm
  have hO₂Y : pCoreOf 2 M ≤ Y ⊓ O :=
    e9_le_of_normal h.O₂_le
      (h.O_le.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M) hYO
  have hYne : Y ≠ ⊥ := by
    intro hY
    apply h.O₂_ne
    rw [eq_bot_iff]
    intro g hg
    have := (hO₂Y hg).1
    rw [hY] at this
    exact this
  have hYchar : (Y.subgroupOf Y).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hYx : ∀ y ∈ Y, y * x * y⁻¹ * x⁻¹ ∈ O := by
    intro y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ Y := by
      have e : x * y * x⁻¹ * y⁻¹ = (x * y * x⁻¹) * y⁻¹ := rfl
      rw [e]
      exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hUY h.xU) y).mp hy) (Y.inv_mem hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ Z ⊔ O := by
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact (Z ⊔ O).mul_mem hxB
        ((Subgroup.mem_normalizer_iff.mp (hYB hy) x⁻¹).mp ((Z ⊔ O).inv_mem hxB))
    have h3 := hYB_O ⟨h1, h2⟩
    have := O.inv_mem h3
    have e : (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
    rwa [e] at this
  by_cases hact : ∃ y ∈ Y, ∃ z ∈ Z, y * z * y⁻¹ * z⁻¹ ∉ O
  swap
  ·
    push Not at hact
    obtain ⟨T, hST, hTB, hYT, hTO, hTsup⟩ := l43_exists_lift (O := O) (B := Z ⊔ O) (Y := Y)
      le_sup_right hBO hYB hYO' hY2 h.O_cop
      (fun b hb => e9_pow_three_mem_sup hZO hZ3 hb) hYO
    have hcomm := e9_comm_mem_sup hZO hYO' hact
    have hTY : ∀ t ∈ T, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := by
      intro t ht y hy
      have h1 : y * t * y⁻¹ * t⁻¹ ∈ O := hcomm y hy t (hTB ht)
      have h2 : t * y * t⁻¹ * y⁻¹ ∈ O := by
        have := O.inv_mem h1
        have e : (y * t * y⁻¹ * t⁻¹)⁻¹ = t * y * t⁻¹ * y⁻¹ := by group
        rwa [e] at this
      have h3 : t * y * t⁻¹ * y⁻¹ ∈ T := by
        have e : t * y * t⁻¹ * y⁻¹ = t * (y * t⁻¹ * y⁻¹) := by group
        rw [e]
        exact T.mul_mem ht ((mem_normalizer_iff.mp (hYT hy) t⁻¹).mp (T.inv_mem ht))
      have h4 : t * y * t⁻¹ * y⁻¹ ∈ Y ⊓ O := hTO ▸ ⟨h3, h2⟩
      have e : t * y * t⁻¹ = (t * y * t⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact Y.mul_mem h4.1 hy
    have hTN : T ≤ normalizer (Y : Set G) := by
      intro t ht
      rw [mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hTY t ht y hy, fun hy => ?_⟩
      have := hTY t⁻¹ (T.inv_mem ht) _ hy
      have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
      rwa [e] at this
    refine hrankE (U ⊔ Z) hUZel hUZcard Y le_rfl hYne hYchar (sup_le ?_ ?_)
    · exact le_sup_of_le_left (le_inf hUY h.U_le)
    · calc Z ≤ Z ⊔ O := le_sup_left
        _ = T ⊔ O := hTsup.symm
        _ ≤ (normalizer (Y : Set G) ⊓ M) ⊔ O :=
          sup_le_sup_right (le_inf hTN (hTB.trans hBM)) O
  · obtain ⟨y₀, hy₀, k₀, hk₀, hnt⟩ := hact
    obtain ⟨U₂, hU₂K, hU₂card, hU₂ℓ, hYU₂, y₁, hy₁, b₁, hb₁, hnt'⟩ :=
      l43_exists_eigenline hZO hYO' h.O_cop hY2 h.Z_el h.Z_card hYB h.x_mem h.x_ne hYx
        ⟨y₀, hy₀, k₀, hk₀, hnt⟩
    have hU₂3 : ∀ k ∈ U₂, k ^ 3 = 1 := fun k hk => hZ3 k (hU₂K hk)
    have hU₂O : U₂ ≤ normalizer (O : Set G) := hU₂K.trans hZO
    have hB₂O : (U₂ ⊔ O : Subgroup G) ≤ normalizer (O : Set G) :=
      sup_le hU₂O Subgroup.le_normalizer
    have hB₂M : (U₂ ⊔ O : Subgroup G) ≤ M := sup_le (hU₂K.trans h.Z_le) h.O_le
    obtain ⟨T₂, hST₂, hT₂B, hYT₂, hT₂O, hT₂sup⟩ := l43_exists_lift (O := O) (B := U₂ ⊔ O)
      (Y := Y) le_sup_right hB₂O hYU₂ hYO' hY2 h.O_cop
      (fun b hb => e9_pow_three_mem_sup hU₂O hU₂3 hb) hYO
    have hT₂M : T₂ ≤ M := hT₂B.trans hB₂M
    have hT₂N : T₂ ≤ normalizer (O : Set G) := hT₂B.trans hB₂O
    have hT₂S : T₂ ≤ normalizer ((Y ⊓ O : Subgroup G) : Set G) := by
      have := e9_le_normalizer_inf (A := T₂) (C := O) Subgroup.le_normalizer hT₂N
      rwa [hT₂O] at this
    have hYS : Y ≤ normalizer ((Y ⊓ O : Subgroup G) : Set G) :=
      e9_le_normalizer_inf Subgroup.le_normalizer hYO'
    have hU₂O' : U₂ ⊓ O = ⊥ := e9_inf_eq_bot hU₂3 h.O_cop
    have hcard1 := e9_card_sup_mul_card_inf hU₂O
    rw [hU₂O', Subgroup.card_bot, hU₂card, mul_one] at hcard1
    have hcard2 := e9_card_sup_mul_card_inf hT₂N
    rw [hT₂sup, hT₂O, hcard1] at hcard2
    have hOpos : 0 < Nat.card O := Nat.card_pos
    have hT₃ : Nat.card T₂ = 3 * Nat.card (Y ⊓ O : Subgroup G) := by
      apply Nat.eq_of_mul_eq_mul_right hOpos
      rw [← hcard2]
      ring
    have hnt₂ : ∃ y ∈ Y, ∃ t ∈ T₂, y * t * y⁻¹ * t⁻¹ ∉ Y ⊓ O := by
      have hb₁' : b₁ ∈ (T₂ : Set G) * (O : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right T₂ O hT₂N]
        rw [hT₂sup]
        exact hb₁
      obtain ⟨t, ht, o, ho, hto⟩ := hb₁'
      have hb₁eq : b₁ = t * o := hto.symm
      refine ⟨y₁, hy₁, t, ht, fun hmem => hnt' ?_⟩
      have hc : y₁ * t * y₁⁻¹ * t⁻¹ ∈ O := hmem.2
      have e : y₁ * b₁ * y₁⁻¹ * b₁⁻¹ =
          (y₁ * t * y₁⁻¹ * t⁻¹) * (t * (y₁ * o * y₁⁻¹ * o⁻¹) * t⁻¹) := by
        rw [hb₁eq]
        group
      rw [e]
      have hyo : y₁ * o * y₁⁻¹ * o⁻¹ ∈ O :=
        O.mul_mem ((mem_normalizer_iff.mp (hYO' hy₁) o).mp ho) (O.inv_mem ho)
      exact O.mul_mem hc ((mem_normalizer_iff.mp (hT₂N ht) _).mp hyo)
    obtain ⟨hWsyl, hWcard, hWq⟩ := l43_wStructure hY2 inf_le_left hST₂ hT₂S hYS hYT₂ hT₃ hnt₂
    have hWM : T₂ ⊔ Y ≤ M := sup_le hT₂M hYM
    have hO₂W : pCoreOf 2 M ≤ T₂ ⊔ Y := hO₂Y.trans (inf_le_left.trans le_sup_right)
    have hF : CharTwo (T₂ ⊔ Y) := charTwo_of_core_le h.charTwo hO₂W hWM
    have hO₂ : pCoreOf 2 M ≤ pCoreOf 2 (T₂ ⊔ Y) :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (pCoreOf 2 M) (T₂ ⊔ Y) hO₂W
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hO₂W).mpr
          (hWM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)))
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    have hUU₂comm : ∀ a ∈ U, ∀ z ∈ U₂, a * z = z * a := fun a ha z hz =>
      h.U_comm a ha z (hU₂K hz)
    have hU₂el : IsElemAbelian 3 U₂ := isElemAbelian_of_le h.Z_el hU₂K
    have hUU₂el : IsElemAbelian 3 (U ⊔ U₂) := isElemAbelian_sup h.U_el hU₂el hUU₂comm
    have hUU₂inf : U ⊓ U₂ = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have hgZ : g ∈ U ⊓ Z := ⟨hg.1, hU₂K hg.2⟩
      rw [h.U_inf_Z] at hgZ
      have : g ∈ zpowers x ⊓ U₂ := ⟨hgZ, hg.2⟩
      rw [hU₂ℓ] at this
      exact this
    have hUU₂card : Nat.card (U ⊔ U₂ : Subgroup G) = 27 := by
      have hc := e9_card_sup_mul_card_inf (le_normalizer_of_comm hUU₂comm)
      rw [hUU₂inf, Subgroup.card_bot, h.U_card, hU₂card] at hc
      omega
    have hnc : NoCharNormal Y (T₂ ⊔ Y) := by
      intro C hCY hC1 hCch hWC
      refine hrankE (U ⊔ U₂) hUU₂el hUU₂card C hCY hC1 hCch (sup_le ?_ ?_)
      · exact le_sup_of_le_left (le_inf (fun g hg =>
          l43_normalizer_le_of_characteristic hCY hCch (hUY hg)) h.U_le)
      · have hT₂H : T₂ ≤ normalizer (C : Set G) ⊓ M := le_inf (le_sup_left.trans hWC) hT₂M
        calc U₂ ≤ T₂ ⊔ O := by rw [hT₂sup]; exact le_sup_left
          _ ≤ _ := sup_le_sup_right hT₂H O
    have h3T₂ : 3 ∣ Nat.card T₂ := ⟨Nat.card (Y ⊓ O : Subgroup G), hT₃⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3T₂
    have huG : orderOf (u : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hu
    have hu3 : (u : G) ^ 3 = 1 := by rw [← huG]; exact pow_orderOf_eq_one _
    have hu1 : (u : G) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at huG
      omega
    have huW : (u : G) ∈ T₂ ⊔ Y := mem_sup_left u.2
    have h4 := GL83.baumann_niles_s3 hWsyl hF hWq hnc huW hu3 hu1
    have hX := l43_card_commutator_omegaOneCenter hWM huW hu3 hu1 h.charTwo hO₂ h4
    have huB : (u : G) ∈ Z ⊔ O := sup_le_sup_right hU₂K O (hT₂B u.2)
    have hZp : IsPGroup 3 Z :=
      CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 3 Z h.Z_el
    have hZsyl : IsSylowOf 3 Z (Z ⊔ O) := by
      refine isSylowOf_iff.mpr ⟨le_sup_left, hZp, ?_⟩
      have hc := e9_card_sup_mul_card_inf hZO
      rw [e9_inf_eq_bot hZ3 h.O_cop, Subgroup.card_bot, h.Z_card, mul_one] at hc
      have hrel := Subgroup.relIndex_mul_card (H := Z) (K := Z ⊔ O)
      rw [inf_of_le_left le_sup_left, h.Z_card, hc] at hrel
      have : Z.relIndex (Z ⊔ O) = Nat.card O := by omega
      rw [this]
      exact h.O_cop
    obtain ⟨k, hkB, hk⟩ : ∃ k ∈ Z ⊔ O, k⁻¹ * (u : G) * k ∈ Z := by
      have hzp : IsPGroup 3 ((zpowers (u : G)).subgroupOf (Z ⊔ O)) := by
        have : IsPGroup 3 (zpowers (u : G)) :=
          IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huG]; simp)
        exact this.comap_subtype
      obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
      have hQs : IsSylowOf 3 (Q.map (Z ⊔ O).subtype) (Z ⊔ O) := ⟨Q, rfl⟩
      obtain ⟨k, hkB, hkk⟩ := hZsyl.exists_mem_conj hQs
      refine ⟨k, hkB, (hkk (u : G)).mp ?_⟩
      exact ⟨⟨u, huB⟩, hQ (Subgroup.mem_subgroupOf.mpr (mem_zpowers _)), rfl⟩
    have hu₂1 : k⁻¹ * (u : G) * k ≠ 1 := by
      intro h1
      apply hu1
      have : (u : G) = k * (k⁻¹ * (u : G) * k) * k⁻¹ := by group
      rw [this, h1]
      group
    have hXN : M ≤ normalizer ((omegaOneCenterOf (pCoreOf 2 M) : Subgroup G) : Set G) :=
      l43_normalizer_omegaOneCenter
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)
    have hk4 : Nat.card (⁅omegaOneCenterOf (pCoreOf 2 M), zpowers (k⁻¹ * (u : G) * k)⁆ :
        Subgroup G) = 4 := by
      have := l43_card_commutator_conj hXN (m := k⁻¹) (u := (u : G)) (M.inv_mem (hBM hkB))
      rw [inv_inv] at this
      rw [this]
      exact hX
    exact no_cube_action (X := omegaOneCenterOf (pCoreOf 2 M)) (P := P)
      (l43_isElemAbelian_omegaOneCenter
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M))
      (h.P_le.trans hXN) (h.Z_le_P hk) (hZ3 _ hk) (h.P_cen _ hk) (h.Z_cube _ hk) hk4

theorem CoreData.normalizer_le {M O Z P U : Subgroup G} {x : G} (h : CoreData G M O Z P U x)
    {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M) (hYO : IsSylowOf 2 (Y ⊓ O) O)
    (hUY : U ≤ normalizer (Y : Set G)) : normalizer (Y : Set G) ≤ M := by
  by_cases hbig : ∃ Y₀ : Subgroup G, Y₀ ≤ Y ∧ Y₀ ≠ ⊥ ∧ (Y₀.subgroupOf Y).Characteristic ∧
      3 ≤ CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M)
  · obtain ⟨Y₀, hle, hne, hch, hr⟩ := hbig
    exact (l43_normalizer_le_of_characteristic hle hch).trans (h.D1 Y₀ hne (hY2.to_le hle) hr)
  · push Not at hbig
    exact (h.false_of_small hY2 hYM hYO hUY hbig).elim

end CaseOne

section Structure

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

omit [Finite G] in
theorem mem_L28Z_iff {P : Subgroup G} {z : G} :
    z ∈ L28Z P ↔ z ∈ P ∧ ∀ p ∈ P, p * z = z * p := by
  unfold L28Z
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun p hp => ?_⟩
    have := Subgroup.mem_center_iff.mp hc ⟨p, hp⟩
    exact congrArg Subtype.val this
  · rintro ⟨hz, hc⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2), rfl⟩

omit [Finite G] in
theorem L28Z_le {P : Subgroup G} : L28Z P ≤ P := fun _ hz => (mem_L28Z_iff.mp hz).1

theorem l28shape_facts {P : Subgroup G} (h : L28Shape 3 P) :
    IsElemAbelian 3 (L28Z P) ∧ (∀ z ∈ L28Z P, ∃ a ∈ P, a ^ 3 = z) ∧
      ∃ y ∈ P, y ^ 3 = 1 ∧ y ∉ L28Z P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPc, Q₀, hQ₀P, -, ⟨e⟩, ⟨C, hCP, hQC, hQCP⟩, -, hZ⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ((hZ a).mp ha).2⟩
    exact ((mem_L28Z_iff.mp a.2).2 b (L28Z_le b.2)).symm
  · intro z hz
    obtain ⟨hzQ, hz3⟩ := (hZ z).mp hz
    have hcube : ∀ α : Multiplicative (ZMod (3 ^ 2)), α ^ 3 = 1 → ∃ β, β ^ 3 = α := by
      decide
    have hq3 : (⟨z, hzQ⟩ : ↥Q₀) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    have he3 : (e ⟨z, hzQ⟩) ^ 3 = 1 := by rw [← map_pow, hq3, map_one]
    obtain ⟨β₁, hβ₁⟩ := hcube (e ⟨z, hzQ⟩).1 (by
      have := congrArg Prod.fst he3
      simpa using this)
    obtain ⟨β₂, hβ₂⟩ := hcube (e ⟨z, hzQ⟩).2 (by
      have := congrArg Prod.snd he3
      simpa using this)
    refine ⟨((e.symm (β₁, β₂) : ↥Q₀) : G), hQ₀P.le (e.symm (β₁, β₂)).2, ?_⟩
    have : (e.symm (β₁, β₂)) ^ 3 = ⟨z, hzQ⟩ := by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply]
      ext <;> simp [hβ₁, hβ₂]
    simpa using congrArg Subtype.val this
  ·
    have hCne : C ≠ ⊥ := by
      intro hC
      rw [hC, sup_bot_eq] at hQCP
      exact hQ₀P.ne hQCP
    have hCp : IsPGroup 3 C := by
      have : IsPGroup 3 P := IsPGroup.of_card (n := 5) (by simpa using hPc)
      exact this.to_le hCP
    obtain ⟨n, hn⟩ := hCp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hCne
      exact Subgroup.eq_bot_of_card_eq C (by simpa using hn)
    have h3C : 3 ∣ Nat.card C := by
      rw [hn]
      exact dvd_pow_self 3 hn0
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3C
    have huG : orderOf (u : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hu
    have hu3 : (u : G) ^ 3 = 1 := by rw [← huG]; exact pow_orderOf_eq_one _
    refine ⟨u, hCP u.2, hu3, fun hyZ => ?_⟩
    have hyQ : (u : G) ∈ Q₀ := ((hZ _).mp hyZ).1
    have : (u : G) ∈ Q₀ ⊓ C := ⟨hyQ, u.2⟩
    rw [hQC, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at huG
    omega

omit [Finite G] in
theorem isElemAbelian_zpowers {a : G} (ha : a ^ 3 = 1) : IsElemAbelian 3 (zpowers a) := by
  refine ⟨inferInstance, fun g hg => ?_⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]

theorem l28_plane_exists {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hR : L28Prop34 3 P J x)
    (hsh : L28Shape 3 (P : Subgroup G)) : ∃ U : Subgroup G, L28InV 3 P x U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := hgen
  obtain ⟨hPC, -, -, -, -⟩ := hR
  have hxZ : x ∈ L28Z (P : Subgroup G) :=
    mem_L28Z_iff.mpr ⟨hxP, fun p hp => mem_centralizer_singleton_iff.mp (hPC hp)⟩
  obtain ⟨-, -, y, hyP, hy3, hyZ⟩ := l28shape_facts hsh
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hy1 : y ≠ 1 := fun h => hyZ (h ▸ one_mem _)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hxyc : Commute x y := ((mem_L28Z_iff.mp hxZ).2 y hyP).symm
  have hcomm : ∀ a ∈ zpowers x, ∀ b ∈ zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact (hxyc.zpow_zpow i j).eq
  have hxy : zpowers x ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    by_contra hg1
    have hg1' : g ≠ 1 := fun h => hg1 (h ▸ one_mem _)
    have hgx : g ^ 3 = 1 := (isElemAbelian_zpowers hx3).2 g hg.1
    have h1 : zpowers g = zpowers x := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg.1)
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hgx hg1', hxo]
    have h2 : zpowers g = zpowers y := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg.2)
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hgx hg1', hyo]
    apply hyZ
    have : y ∈ zpowers x := by rw [← h1, h2]; exact mem_zpowers y
    exact (Subgroup.zpowers_le.mpr hxZ) this
  refine ⟨zpowers x ⊔ zpowers y, sup_le (zpowers_le.mpr ⟨hxP, hPC hxP⟩)
    (zpowers_le.mpr ⟨hyP, hPC hyP⟩), isElemAbelian_sup (isElemAbelian_zpowers hx3)
    (isElemAbelian_zpowers hy3) hcomm, ?_, mem_sup_left (mem_zpowers x), ?_⟩
  · have hc := e9_card_sup_mul_card_inf (le_normalizer_of_comm hcomm)
    rw [hxy, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, hxo, hyo] at hc
    omega
  · intro hU
    exact hyZ (hU ▸ mem_sup_right (mem_zpowers y))

theorem l28_exists_swap (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hR : L28Prop34 3 P J x) :
    ∃ k : G, (P : Subgroup G) ⊓ J = zpowers k ∧ orderOf k = 9 ∧
      ∃ n ∈ normalizer ((P : Subgroup G) : Set G), n * x * n⁻¹ ∈ zpowers (k ^ 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t₀, hT, ht₀⟩ := l28iv_T_cyclic hS hU0 l28Three_proved hp hM hgen hJ
  obtain ⟨hxP, hxLO, hQsyl, -⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  obtain ⟨hPC, hZc, hZ, hfus, hout⟩ := hR
  have hu9 : t₀ ^ 9 = 1 := by rw [← ht₀]; exact pow_orderOf_eq_one t₀
  have hu3 : (t₀ ^ 3) ^ 3 = 1 := by rw [← pow_mul]; exact hu9
  have hu1 : t₀ ^ 3 ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num : 0 < 3) h
    omega
  have huT : t₀ ^ 3 ∈ (P : Subgroup G) ⊓ J := by rw [hT]; exact pow_mem (mem_zpowers t₀) 3
  have huZ : t₀ ^ 3 ∈ L28Z (P : Subgroup G) := hZ _ huT hu3
  have hTcyc : IsCyclic ↥((P : Subgroup G) ⊓ J) := by rw [hT]; infer_instance
  obtain ⟨g, hgP, hgx⟩ : ∃ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G) ⊓ centralizer ({x} : Set G) ∧ g * x * g⁻¹ ∉ zpowers x := by
    by_contra hno
    push Not at hno
    exact l28iv_false_of_wc hS hU0 l28Three_proved hp hM hgen hJ hno
  have hgP' : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) :=
    hgP.trans inf_le_left
  have hy₀mem : g * x * g⁻¹ ∈ (zpowers x).map (MulAut.conj g).toMonoidHom :=
    ⟨x, mem_zpowers x, by simp [MulAut.conj_apply]⟩
  have hgJ : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ J := by
    rcases hfus g hgP' with h | h
    · exact absurd (h ▸ hy₀mem) hgx
    · exact h
  have hy₀T : g * x * g⁻¹ ∈ (P : Subgroup G) ⊓ J := ⟨hgP' hy₀mem, hgJ hy₀mem⟩
  have hy₀3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hy₀u : g * x * g⁻¹ ∈ zpowers (t₀ ^ 3) :=
    mem_zpowers_of_isCyclic_of_pow_three hTcyc huT hy₀T hu1 hu3 hy₀3
  have hy₀cen : ∀ a ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G),
      a * (g * x * g⁻¹) = (g * x * g⁻¹) * a := by
    intro a ha
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy₀u
    rw [← hk]
    exact (Commute.zpow_right ((mem_L28Z_iff.mp huZ).2 a ha.1) k).eq
  obtain ⟨n, hnN, hnx⟩ := l28iv_exists_normalizer_conj hQsyl hy₀cen
  rw [inf_eq_left.mpr hPC] at hnN
  exact ⟨t₀, hT, ht₀, n, hnN, hnx ▸ hy₀u⟩

end Structure

section Main

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
open scoped Pointwise

theorem mem_l34Img_iff {x : G} {J A : Subgroup G} {z : L34Quot x J} :
    z ∈ l34Img x J A ↔
      ∃ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ A ∧ l34Hom x J c = z := by
  unfold l34Img
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, Subgroup.mem_subgroupOf.mp hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, Subgroup.mem_subgroupOf.mpr hc, rfl⟩

theorem mem_glbPrimeCore_of_mem_primeComplementCore {C : Subgroup G} {c : ↥C}
    (h : c ∈ primeComplementCore (G := C) 3) : (c : G) ∈ GLBPrimeCore 3 C := by
  rw [← glbPrimeCore_subgroupOf 3 C] at h
  exact Subgroup.mem_subgroupOf.mp h

theorem l34Hom_eq_one_of_mem {x : G} {J : Subgroup G} {c : ↥(centralizer ({x} : Set G))}
    (h : (c : G) ∈ GLBPrimeCore 3 (centralizer ({x} : Set G))) : l34Hom x J c = 1 := by
  have h1 : c ∈ primeComplementCore (G := centralizer ({x} : Set G)) 3 := by
    rw [← glbPrimeCore_subgroupOf 3 (centralizer ({x} : Set G))]
    exact Subgroup.mem_subgroupOf.mpr h
  show QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore
    (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c) = 1
  have h2 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c = 1 :=
    (QuotientGroup.eq_one_iff c).mpr h1
  rw [h2, map_one]

omit [Finite G] in
theorem inf_eq_bot_of_pGroup_of_coprime {T N : Subgroup G} (hT : IsPGroup 3 T)
    (hN : ¬ 3 ∣ Nat.card N) : T ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgT, hgN⟩
  obtain ⟨k, hk⟩ := hT ⟨g, hgT⟩
  have hord : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  have hord2 : orderOf g ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨g, hgN⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
  by_cases hi0 : i = 0
  · subst hi0
    simp only [pow_zero] at hgi
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hgi)
  · exact absurd ((hgi ▸ dvd_pow_self 3 hi0).trans hord2) hN

theorem l28_lift_normalizer (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    {kt : L34Quot x J} (hkK : kt ∈ l34Img x J J)
    (hkN : kt ∈ normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
      Set (L34Quot x J))) :
    ∃ (j : G) (hjC : j ∈ centralizer ({x} : Set G)), j ∈ J ∧
      j ∈ normalizer (((P : Subgroup G) ⊓ J : Subgroup G) : Set G) ∧
      l34Hom x J ⟨j, hjC⟩ = kt := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJC := hJ.le_centralizer
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set T : Subgroup G := (P : Subgroup G) ⊓ J with hT
  obtain ⟨-, hTinj, hTcard⟩ := l28_T_data hS hU0 l28Three_proved hp hM hgen hJ
  set N' : Subgroup G := J ⊓ GLBPrimeCore 3 C with hN'
  have hN'cop : ¬ 3 ∣ Nat.card N' := by
    intro hd
    have h1 := hd.trans (Subgroup.card_dvd_of_le (inf_le_right : N' ≤ GLBPrimeCore 3 C))
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 C) h1
  have hJN' : J ≤ normalizer (N' : Set G) :=
    e9_le_normalizer_inf Subgroup.le_normalizer (hJC.trans (le_normalizer_glbPrimeCore 3 C))
  have hTJ : T ≤ J := inf_le_right
  have hTN' : T ≤ normalizer (N' : Set G) := hTJ.trans hJN'
  have hT3 : IsPGroup 3 T := P.isPGroup'.to_inf_left
  have hTcard' : Nat.card T = 9 := hTcard.trans (by norm_num)
  have hTN'bot : T ⊓ N' = ⊥ := inf_eq_bot_of_pGroup_of_coprime hT3 hN'cop
  have hN'ker : ∀ c : ↥C, (c : G) ∈ J → l34Hom x J c = 1 → (c : G) ∈ N' := fun c hcJ h1 =>
    ⟨hcJ, mem_glbPrimeCore_of_mem_primeComplementCore (l28_mem_of_ker_of_mem_J hJ c hcJ h1)⟩
  have hN'one : ∀ c : ↥C, (c : G) ∈ N' → l34Hom x J c = 1 := fun c hc =>
    l34Hom_eq_one_of_mem hc.2
  set R : Subgroup G := T ⊔ N' with hR
  have hRcard : Nat.card R = 9 * Nat.card N' := by
    have hc := e9_card_sup_mul_card_inf hTN'
    rw [hTN'bot, Subgroup.card_bot, hTcard', mul_one] at hc
    exact hc
  have hRT : IsSylowOf 3 T R := by
    refine isSylowOf_iff.mpr ⟨le_sup_left, hT3, ?_⟩
    have hrel := Subgroup.relIndex_mul_card (H := T) (K := R)
    rw [inf_of_le_left le_sup_left, hTcard', hRcard] at hrel
    have : T.relIndex R = Nat.card N' := by omega
    rw [this]
    exact hN'cop
  obtain ⟨j₀, hj₀J, hj₀φ⟩ := mem_l34Img_iff.mp hkK
  have hj₀C : (j₀ : G) ∈ C := j₀.2
  set T' : Subgroup G := T.map (MulAut.conj (j₀ : G)).toMonoidHom with hT'
  have hT'R : T' ≤ R := by
    rintro _ ⟨t, ht, rfl⟩
    have htC : t ∈ C := hJC (hTJ ht)
    have hφt : l34Hom x J ⟨t, htC⟩ ∈ l34Img x J T :=
      mem_l34Img_iff.mpr ⟨⟨t, htC⟩, ht, rfl⟩
    have hconj : l34Hom x J (j₀ * ⟨t, htC⟩ * j₀⁻¹) ∈ l34Img x J T := by
      rw [map_mul, map_mul, hj₀φ, map_inv, hj₀φ]
      have := (Subgroup.mem_normalizer_iff.mp hkN _).mp hφt
      exact this
    obtain ⟨c, hcT, hc⟩ := mem_l34Img_iff.mp hconj
    have hcJ : (c : G) ∈ J := hTJ hcT
    have hn1 : l34Hom x J (c⁻¹ * (j₀ * ⟨t, htC⟩ * j₀⁻¹)) = 1 := by
      rw [map_mul, map_inv, hc, inv_mul_cancel]
    have hnJ : ((c⁻¹ * (j₀ * ⟨t, htC⟩ * j₀⁻¹) : ↥C) : G) ∈ J := by
      have : ((c⁻¹ * (j₀ * ⟨t, htC⟩ * j₀⁻¹) : ↥C) : G) =
          (c : G)⁻¹ * ((j₀ : G) * t * (j₀ : G)⁻¹) := rfl
      rw [this]
      exact J.mul_mem (J.inv_mem hcJ) (J.mul_mem (J.mul_mem hj₀J ((hTJ ht))) (J.inv_mem hj₀J))
    have hn := hN'ker _ hnJ hn1
    have : (j₀ : G) * t * (j₀ : G)⁻¹ = (c : G) * ((c : G)⁻¹ * ((j₀ : G) * t * (j₀ : G)⁻¹)) := by
      group
    show (MulAut.conj (j₀ : G)).toMonoidHom t ∈ R
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [this]
    exact R.mul_mem (mem_sup_left hcT) (mem_sup_right hn)
  have hT'card : Nat.card T' = 9 := by
    rw [hT', Subgroup.card_map_of_injective (MulAut.conj (j₀ : G)).injective, hTcard']
  have hRT' : IsSylowOf 3 T' R := by
    refine isSylowOf_iff.mpr ⟨hT'R, hT3.map _, ?_⟩
    have hrel := Subgroup.relIndex_mul_card (H := T') (K := R)
    rw [inf_of_le_left hT'R, hT'card, hRcard] at hrel
    have : T'.relIndex R = Nat.card N' := by omega
    rw [this]
    exact hN'cop
  obtain ⟨r, hrR, hr⟩ := hRT.exists_mem_conj hRT'
  obtain ⟨t', ht', n', hn', hrtn⟩ : ∃ t' ∈ T, ∃ n' ∈ N', r = t' * n' := by
    have : r ∈ (T : Set G) * (N' : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T N' hTN']
      exact hrR
    obtain ⟨t', ht', n', hn', h⟩ := this
    exact ⟨t', ht', n', hn', h.symm⟩
  have hRJ : R ≤ J := sup_le hTJ inf_le_left
  have hrJ : r ∈ J := hRJ hrR
  have ht'C : t' ∈ C := hJC (hTJ ht')
  have hn'C : n' ∈ C := hJC hn'.1
  have hg : r⁻¹ * (j₀ : G) ∈ normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 : (j₀ : G) * y * (j₀ : G)⁻¹ ∈ T' := ⟨y, hy, by simp [MulAut.conj_apply]⟩
      have h2 := (hr _).mp h1
      have e : r⁻¹ * (j₀ : G) * y * (r⁻¹ * (j₀ : G))⁻¹ = r⁻¹ * ((j₀ : G) * y * (j₀ : G)⁻¹) * r := by
        group
      rw [e]
      exact h2
    · intro hy
      have e : r⁻¹ * (j₀ : G) * y * (r⁻¹ * (j₀ : G))⁻¹ = r⁻¹ * ((j₀ : G) * y * (j₀ : G)⁻¹) * r := by
        group
      rw [e] at hy
      have h3 : r * (r⁻¹ * ((j₀ : G) * y * (j₀ : G)⁻¹) * r) * r⁻¹ ∈ T' := by
        apply (hr _).mpr
        have e2 : r⁻¹ * (r * (r⁻¹ * ((j₀ : G) * y * (j₀ : G)⁻¹) * r) * r⁻¹) * r =
            r⁻¹ * ((j₀ : G) * y * (j₀ : G)⁻¹) * r := by group
        rw [e2]
        exact hy
      have e3 : r * (r⁻¹ * ((j₀ : G) * y * (j₀ : G)⁻¹) * r) * r⁻¹ = (j₀ : G) * y * (j₀ : G)⁻¹ := by
        group
      rw [e3] at h3
      obtain ⟨t, ht, hty⟩ := h3
      have : t = y := by
        have h4 : (MulAut.conj (j₀ : G)) t = (MulAut.conj (j₀ : G)) y := by
          simpa [MulAut.conj_apply] using hty
        exact (MulAut.conj (j₀ : G)).injective h4
      rw [← this]
      exact ht
  have hjC : t' * (r⁻¹ * (j₀ : G)) ∈ C :=
    C.mul_mem ht'C (C.mul_mem (C.inv_mem (hJC hrJ)) hj₀C)
  refine ⟨t' * (r⁻¹ * (j₀ : G)), hjC,
    J.mul_mem (hTJ ht') (J.mul_mem (J.inv_mem hrJ) hj₀J),
    (normalizer (T : Set G)).mul_mem (Subgroup.le_normalizer ht') hg, ?_⟩
  have : (⟨t' * (r⁻¹ * (j₀ : G)), hjC⟩ : ↥C) =
      ⟨t', ht'C⟩ * ((⟨n', hn'C⟩ : ↥C)⁻¹ * (⟨t', ht'C⟩ : ↥C)⁻¹ * j₀) :=
    Subtype.ext (by
      show t' * (r⁻¹ * (j₀ : G)) = t' * ((n'⁻¹ * t'⁻¹) * (j₀ : G))
      rw [hrtn]
      group)
  rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hN'one ⟨n', hn'C⟩ hn', hj₀φ]
  simp

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer' {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg z).mp hz
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by simp [MulAut.conj_apply]; group⟩
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (H : Set G)).inv_mem hg) y).mp hy
    simpa using this

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      have h4 : (MulAut.conj g) z = (MulAut.conj g) y := by simpa [MulAut.conj_apply] using hzy
      exact (MulAut.conj g).injective h4
    rw [← this]
    exact hz

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer' hA, map_conj_eq_of_mem_normalizer' hB]

theorem l28_mem_M_of_normalizer (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hR : L28Prop34 3 P J x) {k : G} (hk : (P : Subgroup G) ⊓ J = zpowers k)
    (hk9 : orderOf k = 9) (hk3 : k ^ 3 ∈ L28Z (P : Subgroup G)) {j : G} (hjJ : j ∈ J)
    (hjN : j ∈ normalizer (((P : Subgroup G) ⊓ J : Subgroup G) : Set G)) : j ∈ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := id hgen
  have hPC := hR.1
  have hxJ : x ∉ J := l28_x_not_mem_J hS hU0 hp hM hgen hJ
  have hxZ : x ∈ L28Z (P : Subgroup G) :=
    mem_L28Z_iff.mpr ⟨hxP, fun p hp => mem_centralizer_singleton_iff.mp (hPC hp)⟩
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hk3o : orderOf (k ^ 3) = 3 := by
    rw [orderOf_pow' k (by norm_num : (3 : ℕ) ≠ 0), hk9]
    norm_num
  have hk33 : (k ^ 3) ^ 3 = 1 := by
    rw [← pow_mul, show 3 * 3 = 9 from rfl, ← hk9]
    exact pow_orderOf_eq_one k
  have hk31 : k ^ 3 ≠ 1 := fun h => by rw [h, orderOf_one] at hk3o; omega
  have hT : zpowers (k ^ 3) ≤ (P : Subgroup G) ⊓ J := by
    rw [hk]
    exact zpowers_le.mpr (pow_mem (mem_zpowers k) 3)
  have hcomm : ∀ a ∈ zpowers x, ∀ b ∈ zpowers (k ^ 3), a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hb
    have hc : Commute x (k ^ 3) := ((mem_L28Z_iff.mp hxZ).2 _ (L28Z_le hk3)).symm
    exact (hc.zpow_zpow i l).eq
  have hinf : zpowers x ⊓ zpowers (k ^ 3) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    by_contra hg1
    have hg1' : g ≠ 1 := fun h => hg1 (h ▸ one_mem _)
    have hgx : g ^ 3 = 1 := (isElemAbelian_zpowers hx3).2 g hg.1
    have h1 : zpowers g = zpowers x := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg.1)
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hgx hg1', hxo]
    have h2 : zpowers g = zpowers (k ^ 3) := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg.2)
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hgx hg1', hk3o]
    apply hxJ
    have : x ∈ zpowers (k ^ 3) := by rw [← h2, h1]; exact mem_zpowers x
    exact (hT.trans inf_le_right) this
  have hEel : IsElemAbelian 3 (zpowers x ⊔ zpowers (k ^ 3)) :=
    isElemAbelian_sup (isElemAbelian_zpowers hx3) (isElemAbelian_zpowers hk33) hcomm
  have hEcard : Nat.card (zpowers x ⊔ zpowers (k ^ 3) : Subgroup G) = 3 ^ 2 := by
    have hc := e9_card_sup_mul_card_inf (le_normalizer_of_comm hcomm)
    rw [hinf, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, hxo, hk3o] at hc
    omega
  set R₂ : Subgroup G := zpowers x ⊔ (P : Subgroup G) ⊓ J with hR₂
  have hR₂P : R₂ ≤ (P : Subgroup G) := sup_le (zpowers_le.mpr hxP) inf_le_left
  have hER₂ : zpowers x ⊔ zpowers (k ^ 3) ≤ R₂ := sup_le_sup_left hT _
  have hrank : 2 ≤ CFSG.Open.pRank 3 R₂ := le_pRank_of_elemAbelian_card hER₂ hEel hEcard
  have hjC : j ∈ centralizer ({x} : Set G) := hJ.le_centralizer hjJ
  have hjx : j ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    apply mem_normalizer_of_map_conj_eq
    rw [MonoidHom.map_zpowers]
    have : (MulAut.conj j).toMonoidHom x = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [mem_centralizer_singleton_iff.mp hjC]; group
    rw [this]
  have hjR₂ : j ∈ normalizer (R₂ : Set G) := mem_normalizer_sup hjx hjN
  have hΓ : normalizer (R₂ : Set G) ≤ M := by
    refine le_trans ?_ (hU0 3 hp P M hM)
    unfold rankThreeGamma CFSG.Open.GLBCore
    exact le_sSup ⟨R₂, hR₂P, hrank, rfl⟩
  exact hΓ hjR₂

omit [Finite G] in
theorem mem_normalizer_subgroupOf_iff {X : Type*} [Group X] {K T : Subgroup X} (hTK : T ≤ K)
    (k : ↥K) :
    k ∈ normalizer ((T.subgroupOf K : Subgroup ↥K) : Set ↥K) ↔
      (k : X) ∈ normalizer (T : Set X) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    constructor
    · intro hy
      have := (h ⟨y, hTK hy⟩).mp (Subgroup.mem_subgroupOf.mpr hy)
      exact Subgroup.mem_subgroupOf.mp this
    · intro hy
      have hyK : y ∈ K := by
        have h1 : (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * (k : X) ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem k.2) (hTK hy)) k.2
        have e : (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * (k : X) = y := by group
        rwa [e] at h1
      have := (h ⟨y, hyK⟩).mpr (Subgroup.mem_subgroupOf.mpr hy)
      exact Subgroup.mem_subgroupOf.mp this
  · intro h y
    have := h (y : X)
    constructor
    · intro hy
      exact Subgroup.mem_subgroupOf.mpr (this.mp (Subgroup.mem_subgroupOf.mp hy))
    · intro hy
      exact Subgroup.mem_subgroupOf.mpr (this.mpr (Subgroup.mem_subgroupOf.mp hy))

theorem l28_img_ne (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) :
    l34Img x J J ≠ l34Img x J (M ⊓ J) := by
  intro h
  apply hJ.not_le
  intro j hj
  have hjC := hJ.le_centralizer hj
  have hmem : l34Hom x J ⟨j, hjC⟩ ∈ l34Img x J J := mem_l34Img_iff.mpr ⟨⟨j, hjC⟩, hj, rfl⟩
  rw [h] at hmem
  obtain ⟨c, hcMJ, hc⟩ := mem_l34Img_iff.mp hmem
  have h1 : l34Hom x J (⟨j, hjC⟩ * c⁻¹) = 1 := by
    rw [map_mul, map_inv, hc, mul_inv_cancel]
  have h2 : ((⟨j, hjC⟩ * c⁻¹ : ↥(centralizer ({x} : Set G))) : G) ∈ J :=
    J.mul_mem hj (J.inv_mem hcMJ.2)
  have h3 := mem_glbPrimeCore_of_mem_primeComplementCore
    (l28_mem_of_ker_of_mem_J hJ (⟨j, hjC⟩ * c⁻¹) h2 h1)
  have hOM : GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M :=
    (glbPrimeCore_le_pPrimeCoreIn 3 _).trans (pPrimeCoreIn_centralizer_le hS hp hM hgen.2.2.2.ge)
  have h4 : ((⟨j, hjC⟩ * c⁻¹ : ↥(centralizer ({x} : Set G))) : G) ∈ M := hOM h3
  have h5 : j = ((⟨j, hjC⟩ * c⁻¹ : ↥(centralizer ({x} : Set G))) : G) * (c : G) := by
    show j = j * (c : G)⁻¹ * (c : G)
    group
  rw [h5]
  exact M.mul_mem h4 hcMJ.1

theorem l28_img_MJ (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hR : L28Prop34 3 P J x) {k : G} (hk : (P : Subgroup G) ⊓ J = zpowers k)
    (hk9 : orderOf k = 9) (hk3 : k ^ 3 ∈ L28Z (P : Subgroup G)) :
    l34Img x J (M ⊓ J) = l34Img x J J ⊓
      normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
        Set (L34Quot x J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hge : l34Img x J J ⊓ normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) :
      Subgroup (L34Quot x J)) : Set (L34Quot x J)) ≤ l34Img x J (M ⊓ J) := by
    rintro z ⟨hzK, hzN⟩
    obtain ⟨j, hjC, hjJ, hjN, hjz⟩ := l28_lift_normalizer hS hU0 hp hM hgen hJ hzK hzN
    have hjM := l28_mem_M_of_normalizer hS hU0 hp hM hgen hJ hR hk hk9 hk3 hjJ hjN
    exact mem_l34Img_iff.mpr ⟨⟨j, hjC⟩, ⟨hjM, hjJ⟩, hjz⟩
  refine le_antisymm ?_ hge
  intro z hz
  have hzK : z ∈ l34Img x J J := by
    obtain ⟨c, hc, rfl⟩ := mem_l34Img_iff.mp hz
    exact mem_l34Img_iff.mpr ⟨c, hc.2, rfl⟩
  refine ⟨hzK, ?_⟩
  obtain ⟨hKn, hKc, hKL⟩ := l28_quot_data hS hU0 hp hM hgen hJ
  obtain ⟨hTsyl, -, -⟩ := l28_T_data hS hU0 l28Three_proved hp hM hgen hJ
  obtain ⟨Tsyl, hTsylEq⟩ := hTsyl.exists_sylow_eq_subgroupOf
  have hTK : l34Img x J ((P : Subgroup G) ⊓ J) ≤ l34Img x J J := hTsyl.le
  have hmax := (l28Three_proved ↥(l34Img x J J) hKL Tsyl).2
    ((l34Img x J (M ⊓ J)).subgroupOf (l34Img x J J)) ?_
  · rcases hmax with h | h
    · have : (⟨z, hzK⟩ : ↥(l34Img x J J)) ∈ normalizer ((Tsyl : Subgroup ↥(l34Img x J J)) :
          Set ↥(l34Img x J J)) := h ▸ Subgroup.mem_subgroupOf.mpr hz
      rw [hTsylEq] at this
      exact (mem_normalizer_subgroupOf_iff hTK ⟨z, hzK⟩).mp this
    · exfalso
      apply l28_img_ne hS hU0 hp hM hgen hJ
      apply le_antisymm
      · intro w hw
        have : (⟨w, hw⟩ : ↥(l34Img x J J)) ∈ (l34Img x J (M ⊓ J)).subgroupOf (l34Img x J J) := by
          rw [h]; trivial
        exact Subgroup.mem_subgroupOf.mp this
      · intro w hw
        obtain ⟨c, hc, rfl⟩ := mem_l34Img_iff.mp hw
        exact mem_l34Img_iff.mpr ⟨c, hc.2, rfl⟩
  · intro k hk'
    rw [hTsylEq] at hk'
    have := (mem_normalizer_subgroupOf_iff hTK k).mp hk'
    exact Subgroup.mem_subgroupOf.mpr (hge ⟨k.2, this⟩)

theorem isSolvable_of_card_dvd_54 {H : Type} [Group H] [Finite H] (h : Nat.card H ∣ 54) :
    Group.IsSolvable H := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 H) := inferInstance
  have hnil : Group.IsNilpotent ↥(P : Subgroup H) := P.isPGroup'.isNilpotent
  have hidx : (P : Subgroup H).index ∣ 2 := by
    have h1 : (P : Subgroup H).index ∣ 54 := (Subgroup.index_dvd_card _).trans h
    have hcop : Nat.Coprime (P : Subgroup H).index 27 := by
      have := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr P.not_dvd_index).symm
      simpa using this.pow_right 3
    exact hcop.dvd_of_dvd_mul_right (by simpa using h1 : (P : Subgroup H).index ∣ 2 * 27)
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h2
  · have htop : (P : Subgroup H) = ⊤ := Subgroup.index_eq_one.mp h1
    have : Function.Surjective (P : Subgroup H).subtype := by
      intro y
      exact ⟨⟨y, htop ▸ Subgroup.mem_top y⟩, rfl⟩
    exact Group.isSolvable_of_surjective this
  · have : (P : Subgroup H).Normal := Subgroup.normal_of_index_eq_two h2
    have hq : Group.IsSolvable (H ⧸ (P : Subgroup H)) := by
      have hc : IsCyclic (H ⧸ (P : Subgroup H)) := by
        apply isCyclic_of_card_dvd_prime (p := 2)
        rw [← Subgroup.index_eq_card, h2]
      infer_instance
    exact Group.isSolvable_of_ker_le_range (P : Subgroup H).subtype
      (QuotientGroup.mk' (P : Subgroup H))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem card_normalizer_dvd_54 {X : Type} [Group X] [Finite X] {K D : Subgroup X} [K.Normal]
    (hKc : centralizer (K : Set X) = ⊥) (hKL : IsRankThreeL28 ↥K) (hDK : D ≤ K)
    (hD : ∃ Tsyl : Sylow 3 ↥K, D.subgroupOf K = normalizer ((Tsyl : Subgroup ↥K) : Set ↥K)) :
    Nat.card ↥(normalizer (D : Set X)) ∣ 54 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Tsyl, hDeq⟩ := hD
  have hconj : Function.Injective (MulAut.conjNormal : X →* MulAut ↥K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have : g ∈ centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := congrArg (fun φ : MulAut ↥K => ((φ ⟨h, hh⟩ : ↥K) : X)) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc h * g = (g * h * g⁻¹) * g := by rw [this]
        _ = g * h := by group
    rwa [hKc, Subgroup.mem_bot] at this
  have hXd : Nat.card X ∣ 1512 :=
    (Subgroup.card_dvd_of_injective _ hconj).trans (l28m_card_mulAut hKL).dvd
  have hKc504 : Nat.card ↥K = 504 := l28m_card hKL
  have hidx : K.index ∣ 3 := by
    have h1 := K.index_mul_card
    rw [hKc504] at h1
    have : K.index * 504 ∣ 3 * 504 := by
      rw [h1]
      simpa using hXd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  have hDsimple := l28m_simple hKL
  have hD18 : Nat.card (D.subgroupOf K) = 18 := by
    rw [hDeq]
    exact l28m_card_normalizer hKL Tsyl
  have hself : normalizer ((D.subgroupOf K : Subgroup ↥K) : Set ↥K) = D.subgroupOf K := by
    have hle : D.subgroupOf K ≤ normalizer ((D.subgroupOf K : Subgroup ↥K) : Set ↥K) :=
      Subgroup.le_normalizer
    have hmax := (l28Three_proved ↥K hKL Tsyl).2 (normalizer ((D.subgroupOf K : Subgroup ↥K) :
      Set ↥K)) (by rw [← hDeq]; exact hle)
    rcases hmax with h | h
    · exact h.trans hDeq.symm
    · exfalso
      have hnormal : (D.subgroupOf K).Normal := Subgroup.normalizer_eq_top_iff.mp h
      haveI := hDsimple
      haveI := hnormal
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.subgroupOf K) with h0 | h1
      · rw [h0, Subgroup.card_bot] at hD18
        omega
      · rw [h1, Subgroup.card_top, hKc504] at hD18
        omega
  set S : Subgroup X := normalizer (D : Set X) with hS
  have hSK : (S ⊓ K).subgroupOf K = D.subgroupOf K := by
    rw [← hself]
    ext k
    rw [Subgroup.mem_subgroupOf, mem_normalizer_subgroupOf_iff hDK]
    exact ⟨fun h => h.1, fun h => ⟨h, k.2⟩⟩
  have hSK18 : Nat.card ↥(S ⊓ K) = 18 := by
    rw [← hD18, ← hSK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  have hrel := Subgroup.relIndex_mul_card (H := K) (K := S)
  rw [inf_comm, hSK18] at hrel
  have hrd : K.relIndex S ∣ 3 := (Subgroup.relIndex_dvd_index_of_normal K S).trans hidx
  calc Nat.card ↥S = K.relIndex S * 18 := hrel.symm
    _ ∣ 3 * 18 := Nat.mul_dvd_mul_right hrd 18

theorem l28_N_le_sup {M P N : Subgroup G} (hsylP : IsSylowOf 3 P M) (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set G)) (hON : GLBPrimeCore 3 M ≤ N)
    (hN3 : ∀ g ∈ N, ∃ n : ℕ, g ^ 3 ^ n ∈ GLBPrimeCore 3 M) :
    N ≤ (P ⊓ N) ⊔ GLBPrimeCore 3 M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := GLBPrimeCore 3 M with hO
  have hMO : M ≤ normalizer (O : Set G) := le_normalizer_glbPrimeCore 3 M
  have hOcop : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 M)
  have hPN : IsSylowOf 3 (P ⊓ N) N := hsylP.inf_of_le_normalizer hNM hMN
  have hnorm : (O.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hON).mpr (hNM.trans hMO)
  have hqp : IsPGroup 3 (↥N ⧸ O.subgroupOf N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨n, hn⟩ := hN3 (g : G) g.2
      refine ⟨n, ?_⟩
      have : g ^ 3 ^ n ∈ O.subgroupOf N := Subgroup.mem_subgroupOf.mpr (by simpa using hn)
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr this
  obtain ⟨a, ha⟩ := hqp.exists_card_eq
  have hNcard : Nat.card N = 3 ^ a * Nat.card O := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf N)
    rw [ha, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hON).toEquiv] at h1
    exact h1
  have hfact : (Nat.card N).factorization 3 = a := by
    have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
    rw [hNcard, Nat.factorization_mul (pow_ne_zero a (by norm_num)) hO0]
    simp [Nat.Prime.factorization_pow Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd hOcop]
  have hPNcard : Nat.card ↥(P ⊓ N) = 3 ^ a := by
    rw [hPN.card_eq, hfact]
  have hPNO : P ⊓ N ≤ normalizer (O : Set G) := inf_le_left.trans (hsylP.le.trans hMO)
  have hinf : (P ⊓ N) ⊓ O = ⊥ := inf_eq_bot_of_pGroup_of_coprime
    (hPN.isPGroup) hOcop
  have hsupcard : Nat.card ↥((P ⊓ N) ⊔ O) = Nat.card N := by
    have hc := e9_card_sup_mul_card_inf hPNO
    rw [hinf, Subgroup.card_bot, mul_one, hPNcard, mul_comm] at hc
    rw [hc, hNcard, mul_comm]
  have hle : (P ⊓ N) ⊔ O ≤ N := sup_le inf_le_right hON
  have := Subgroup.eq_of_le_of_card_ge hle (by rw [hsupcard])
  rw [this]

theorem zpowers_inf_eq_bot {a b : G} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : a ∉ zpowers b) : zpowers a ⊓ zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  by_contra hg1
  have hg1' : g ≠ 1 := fun h => hg1 (h ▸ one_mem _)
  have hg3 : g ^ 3 = 1 := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg.1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ha]
    simp
  have h1 : zpowers g = zpowers a := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg.1)
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hg3 hg1', ha]
  have h2 : zpowers g = zpowers b := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg.2)
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hg3 hg1', hb]
  apply hab
  rw [← h2, h1]
  exact mem_zpowers a

theorem mem_of_mem_zpowers_of_ne_one {e u : G} {N : Subgroup G} (he : e ^ 3 = 1) (he1 : e ≠ 1)
    (hu : u ∈ zpowers e) (hu1 : u ≠ 1) (hN : u ∈ N) : e ∈ N := by
  have hu3 : u ^ 3 = 1 := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
  have : e ∈ zpowers u :=
    mem_zpowers_of_isCyclic_of_pow_three (Z := zpowers e) inferInstance hu (mem_zpowers e) hu1 hu3
      he
  exact (zpowers_le.mpr hN) this

theorem eq_one_of_mul_self_eq_one {e u : G} (he : e ^ 3 = 1) (hu : u ∈ zpowers e)
    (h : u * u = 1) : u = 1 := by
  have hu3 : u ^ 3 = 1 := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
  calc u = u ^ 3 * (u * u)⁻¹ := by
        rw [show u ^ 3 = u * u * u by rw [pow_succ, pow_succ, pow_one]]
        group
    _ = 1 := by rw [hu3, h]; simp

theorem l28_Z_decomp {P : Subgroup G} {x w : G} (hZel : IsElemAbelian 3 (L28Z P))
    (hxZ : x ∈ L28Z P) (hx1 : x ≠ 1) (hwZ : w ∈ L28Z P) (hw1 : w ≠ 1) (hxw : x ∉ zpowers w)
    (hZc : Nat.card (L28Z P) = 3 ^ 2) : ∀ z ∈ L28Z P, ∃ a b : ℤ, z = x ^ a * w ^ b := by
  have hZP : L28Z P ≤ P := L28Z_le
  have hxo : orderOf x = 3 := orderOf_eq_prime (hZel.2 x hxZ) hx1
  have hwo : orderOf w = 3 := orderOf_eq_prime (hZel.2 w hwZ) hw1
  have hxwc : Commute x w := (mem_L28Z_iff.mp hwZ).2 x (hZP hxZ)
  have hinfxw : zpowers x ⊓ zpowers w = ⊥ := zpowers_inf_eq_bot hxo hwo hxw
  have hcommxw : ∀ a ∈ zpowers x, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact (hxwc.zpow_zpow i j).eq
  have hZeq : zpowers x ⊔ zpowers w = L28Z P := by
    have hle : zpowers x ⊔ zpowers w ≤ L28Z P := sup_le (zpowers_le.mpr hxZ) (zpowers_le.mpr hwZ)
    apply Subgroup.eq_of_le_of_card_ge hle
    have hc := e9_card_sup_mul_card_inf (le_normalizer_of_comm hcommxw)
    rw [hinfxw, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, hxo, hwo] at hc
    rw [hZc]
    omega
  intro z hz
  rw [← hZeq] at hz
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers x) (zpowers w)
    (le_normalizer_of_comm hcommxw)
  have : z ∈ (zpowers x : Set G) * (zpowers w : Set G) := by rw [← hset]; exact hz
  obtain ⟨a', ha', b', hb', hab⟩ := this
  obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp ha'
  obtain ⟨b, rfl⟩ := mem_zpowers_iff.mp hb'
  exact ⟨a, b, hab.symm⟩

theorem l28_Z_normal_of_core {M P N : Subgroup G} {x k : G} (hsylP : IsSylowOf 3 P M)
    (hZel : IsElemAbelian 3 (L28Z P)) (hxZ : x ∈ L28Z P) (hx1 : x ≠ 1) (hk9 : orderOf k = 9)
    (hkw : k ^ 3 ∈ L28Z P) (hxk : x ∉ zpowers k) (hZc : Nat.card (L28Z P) = 3 ^ 2)
    (hswap : ∃ n ∈ M, n ∈ normalizer (P : Set G) ∧ n * x * n⁻¹ ∈ zpowers (k ^ 3))
    (hinv : ∃ ι ∈ M, ι * x * ι⁻¹ = x ∧ ι * k ^ 3 * ι⁻¹ = (k ^ 3)⁻¹)
    (hfus : ∀ g ∈ M, g * x * g⁻¹ ∈ P → g * x * g⁻¹ ∈ L28Z P)
    (hNO : GLBPrimeCore 3 M < N) (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set G))
    (hN3 : ∀ g ∈ N, ∃ n : ℕ, g ^ 3 ^ n ∈ GLBPrimeCore 3 M) :
    M ≤ normalizer ((L28Z P ⊔ GLBPrimeCore 3 M : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := GLBPrimeCore 3 M with hO
  set Z := L28Z P with hZ
  set w := k ^ 3 with hw
  have hPM : P ≤ M := hsylP.le
  have hMO : M ≤ normalizer (O : Set G) := le_normalizer_glbPrimeCore 3 M
  have hOM : O ≤ M := glbPrimeCore_le 3 M
  have hZP : Z ≤ P := L28Z_le
  have hx3 : x ^ 3 = 1 := hZel.2 x hxZ
  have hw3 : w ^ 3 = 1 := hZel.2 w hkw
  have hw1 : w ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num : 0 < 3) (show k ^ 3 = 1 from h)
    omega
  have hxnw : x ∉ zpowers w := fun h =>
    hxk ((zpowers_le.mpr (pow_mem (mem_zpowers k) 3)) h)
  have hZmem := l28_Z_decomp hZel hxZ hx1 hkw hw1 hxnw hZc
  have hxwc : Commute x w := (mem_L28Z_iff.mp hkw).2 x (hZP hxZ)
  have hPN : IsSylowOf 3 (P ⊓ N) N := hsylP.inf_of_le_normalizer hNM hMN
  have hPNne : P ⊓ N ≠ ⊥ := by
    intro hbot
    have hcop : Nat.Coprime 3 (Nat.card N) := by
      have h := hPN.card_eq
      rw [hbot, Subgroup.card_bot] at h
      have h0 : (Nat.card N).factorization 3 = 0 := by
        by_contra hne
        have : 3 ^ (Nat.card N).factorization 3 ≥ 3 :=
          Nat.le_self_pow hne 3
        omega
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun hd => ?_
      have : (Nat.card N).factorization 3 ≠ 0 :=
        (Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hd).ne'
      exact this h0
    exact hNO.not_ge (le_glbPrimeCore hNM hMN hcop)
  have hPnil : Group.IsNilpotent ↥P := hsylP.isPGroup.isNilpotent
  have hHn : ((P ⊓ N).subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (e9_le_normalizer_inf Subgroup.le_normalizer (hPM.trans hMN))
  have hH0 : (P ⊓ N).subgroupOf P ≠ ⊥ := by
    intro hb
    apply hPNne
    rw [eq_bot_iff]
    intro g hg
    have : (⟨g, hg.1⟩ : ↥P) ∈ (P ⊓ N).subgroupOf P := hg
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH0)
  have hzN : ((c : ↥P) : G) ∈ N := (Subgroup.mem_subgroupOf.mp c.2.1).2
  have hzZ : ((c : ↥P) : G) ∈ Z := mem_L28Z_iff.mpr ⟨(c : ↥P).2, fun p hp => by
    have := Subgroup.mem_center_iff.mp c.2.2 ⟨p, hp⟩
    exact congrArg Subtype.val this⟩
  have hz1 : ((c : ↥P) : G) ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  obtain ⟨ι, hιM, hιx, hιw⟩ := hinv
  obtain ⟨n, hnM, hnP, hnx⟩ := hswap
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hnx
  have hnx1 : n * x * n⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have : x = n⁻¹ * (n * x * n⁻¹) * n := by group
    rw [this, h]
    group
  have hxN_or : x ∈ N ∨ w ∈ N := by
    obtain ⟨a, b, hab⟩ := hZmem _ hzZ
    set z : G := ((c : ↥P) : G) with hzdef
    have e1 : ι * z * ι⁻¹ = x ^ a * (w ^ b)⁻¹ := by
      rw [hab]
      calc ι * (x ^ a * w ^ b) * ι⁻¹ = (ι * x ^ a * ι⁻¹) * (ι * w ^ b * ι⁻¹) := by group
        _ = (ι * x * ι⁻¹) ^ a * (ι * w * ι⁻¹) ^ b := by rw [conj_zpow, conj_zpow]
        _ = x ^ a * (w ^ b)⁻¹ := by rw [hιx, hιw, inv_zpow]
    have hιzN : ι * z * ι⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hMN hιM) z).mp hzN
    have hc : x ^ a * w ^ b = w ^ b * x ^ a := (hxwc.zpow_zpow a b).eq
    have hA : (x ^ a) * (x ^ a) ∈ N := by
      have h1 : z * (ι * z * ι⁻¹) ∈ N := N.mul_mem hzN hιzN
      have e : z * (ι * z * ι⁻¹) = (x ^ a) * (x ^ a) := by
        rw [e1, hab]
        calc x ^ a * w ^ b * (x ^ a * (w ^ b)⁻¹) = x ^ a * (w ^ b * x ^ a) * (w ^ b)⁻¹ := by group
          _ = x ^ a * (x ^ a * w ^ b) * (w ^ b)⁻¹ := by rw [← hc]
          _ = (x ^ a) * (x ^ a) := by group
      rwa [e] at h1
    have hB : (w ^ b) * (w ^ b) ∈ N := by
      have h1 : z * (ι * z * ι⁻¹)⁻¹ ∈ N := N.mul_mem hzN (N.inv_mem hιzN)
      have hc2 : x ^ a * (w ^ b * w ^ b) = (w ^ b * w ^ b) * x ^ a := by
        calc x ^ a * (w ^ b * w ^ b) = (x ^ a * w ^ b) * w ^ b := by group
          _ = (w ^ b * x ^ a) * w ^ b := by rw [hc]
          _ = w ^ b * (x ^ a * w ^ b) := by group
          _ = w ^ b * (w ^ b * x ^ a) := by rw [hc]
          _ = (w ^ b * w ^ b) * x ^ a := by group
      have e : z * (ι * z * ι⁻¹)⁻¹ = (w ^ b) * (w ^ b) := by
        rw [e1, hab]
        calc x ^ a * w ^ b * (x ^ a * (w ^ b)⁻¹)⁻¹ = x ^ a * (w ^ b * w ^ b) * (x ^ a)⁻¹ := by
              group
          _ = w ^ b * w ^ b := mul_inv_eq_iff_eq_mul.mpr hc2
      rwa [e] at h1
    by_cases hxa : (x ^ a) * (x ^ a) = 1
    · by_cases hwb : (w ^ b) * (w ^ b) = 1
      · exfalso
        apply hz1
        rw [hab, eq_one_of_mul_self_eq_one hx3 (mem_zpowers_iff.mpr ⟨a, rfl⟩) hxa,
          eq_one_of_mul_self_eq_one hw3 (mem_zpowers_iff.mpr ⟨b, rfl⟩) hwb, one_mul]
      · exact Or.inr (mem_of_mem_zpowers_of_ne_one hw3 hw1
          (mul_mem (mem_zpowers_iff.mpr ⟨b, rfl⟩) (mem_zpowers_iff.mpr ⟨b, rfl⟩)) hwb hB)
    · exact Or.inl (mem_of_mem_zpowers_of_ne_one hx3 hx1
        (mul_mem (mem_zpowers_iff.mpr ⟨a, rfl⟩) (mem_zpowers_iff.mpr ⟨a, rfl⟩)) hxa hA)
  have hnxN : n * x * n⁻¹ ∈ N ↔ x ∈ N := by
    constructor
    · intro h
      have := (Subgroup.mem_normalizer_iff.mp (hMN ((M).inv_mem hnM)) (n * x * n⁻¹)).mp h
      have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
      rwa [e] at this
    · intro h
      exact (Subgroup.mem_normalizer_iff.mp (hMN hnM) x).mp h
  have hwj1 : w ^ j ≠ 1 := by rw [hj]; exact hnx1
  have hxwN : x ∈ N ∧ w ∈ N := by
    rcases hxN_or with hxN | hwN
    · refine ⟨hxN, ?_⟩
      have h1 : w ^ j ∈ N := by rw [hj]; exact hnxN.mpr hxN
      exact mem_of_mem_zpowers_of_ne_one hw3 hw1 (mem_zpowers_iff.mpr ⟨j, rfl⟩) hwj1 h1
    · refine ⟨?_, hwN⟩
      have h1 : w ^ j ∈ N := zpow_mem hwN j
      rw [hj] at h1
      exact hnxN.mp h1
  have hNsup := l28_N_le_sup hsylP hNM hMN hNO.le hN3
  have hPNO : P ⊓ N ≤ normalizer (O : Set G) := inf_le_left.trans (hPM.trans hMO)
  have hconjx : ∀ g ∈ M, g * x * g⁻¹ ∈ Z ⊔ O := by
    intro g hg
    set u : G := g * x * g⁻¹ with hu
    have huN : u ∈ N := (Subgroup.mem_normalizer_iff.mp (hMN hg) x).mp hxwN.1
    have hu3 : u ^ 3 = 1 := by rw [hu, conj_pow, hx3, mul_one, mul_inv_cancel]
    have hu1 : u ≠ 1 := by
      intro h
      apply hx1
      have : x = g⁻¹ * u * g := by rw [hu]; group
      rw [this, h]
      group
    have huo : orderOf u = 3 := orderOf_eq_prime hu3 hu1
    have hzp : IsPGroup 3 ((zpowers u).subgroupOf N) := by
      have : IsPGroup 3 (zpowers u) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huo]; simp)
      exact this.comap_subtype
    obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
    have hQs : IsSylowOf 3 (Q.map N.subtype) N := ⟨Q, rfl⟩
    obtain ⟨c, hcN, hc⟩ := hPN.exists_mem_conj hQs
    have hcu : c⁻¹ * u * c ∈ P ⊓ N :=
      (hc u).mp ⟨⟨u, huN⟩, hQ (Subgroup.mem_subgroupOf.mpr (mem_zpowers _)), rfl⟩
    have hz' : c⁻¹ * u * c ∈ Z := by
      have := hfus (c⁻¹ * g) (M.mul_mem (M.inv_mem (hNM hcN)) hg) (by
        have e : c⁻¹ * g * x * (c⁻¹ * g)⁻¹ = c⁻¹ * u * c := by rw [hu]; group
        rw [e]
        exact hcu.1)
      have e : c⁻¹ * g * x * (c⁻¹ * g)⁻¹ = c⁻¹ * u * c := by rw [hu]; group
      rwa [e] at this
    have hcmem : c ∈ ((P ⊓ N : Subgroup G) : Set G) * (O : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (P ⊓ N) O hPNO]
      exact hNsup hcN
    obtain ⟨p, hp, o, ho, hpo⟩ := hcmem
    have hp' : p ∈ P ⊓ N := hp
    have ho' : o ∈ O := ho
    have hpo' : p * o = c := hpo
    set z' : G := c⁻¹ * u * c with hz'def
    have hzz'P : z' ∈ P := hZP hz'
    have hu' : u = c * z' * c⁻¹ := by rw [hz'def]; group
    have hpcen : p * z' = z' * p := (mem_L28Z_iff.mp hz').2 p hp'.1
    have hz'M : z' ∈ M := hPM hzz'P
    have h1 : z'⁻¹ * o * z'⁻¹⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hMO (M.inv_mem hz'M)) o).mp ho'
    have hoo : z'⁻¹ * o * z' * o⁻¹ ∈ O := by
      have := O.mul_mem h1 (O.inv_mem ho')
      simpa using this
    have hpO : p * (z'⁻¹ * o * z' * o⁻¹) * p⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hMO (hNM hp'.2)) _).mp hoo
    have hpz' : p * z' * p⁻¹ = z' := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hpcen
    have hueq : u = z' * (p * (z'⁻¹ * o * z' * o⁻¹) * p⁻¹) := by
      calc u = c * z' * c⁻¹ := hu'
        _ = (p * o) * z' * (p * o)⁻¹ := by rw [hpo']
        _ = p * (z' * (z'⁻¹ * o * z' * o⁻¹)) * p⁻¹ := by group
        _ = (p * z' * p⁻¹) * (p * (z'⁻¹ * o * z' * o⁻¹) * p⁻¹) := by group
        _ = z' * (p * (z'⁻¹ * o * z' * o⁻¹) * p⁻¹) := by rw [hpz']
    rw [hueq]
    exact mul_mem (mem_sup_left hz') (mem_sup_right hpO)
  have hconjw : ∀ g ∈ M, g * w * g⁻¹ ∈ Z ⊔ O := by
    intro g hg
    have hnxo : (n * x * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
    have hwmem : w ∈ zpowers (n * x * n⁻¹) :=
      mem_of_mem_zpowers_of_ne_one hw3 hw1 hnx hnx1 (mem_zpowers _)
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hwmem
    have e : g * w * g⁻¹ = ((g * n) * x * (g * n)⁻¹) ^ i := by
      rw [← hi]
      calc g * (n * x * n⁻¹) ^ i * g⁻¹ = (g * (n * x * n⁻¹) * g⁻¹) ^ i := (conj_zpow).symm
        _ = ((g * n) * x * (g * n)⁻¹) ^ i := by congr 1; group
    rw [e]
    exact zpow_mem (hconjx (g * n) (M.mul_mem hg hnM)) i
  have hSM : ∀ m ∈ M, ∀ h ∈ Z ⊔ O, m * h * m⁻¹ ∈ Z ⊔ O := by
    intro m hm h hh
    have hZle : Z ≤ (Z ⊔ O).comap (MulAut.conj m).toMonoidHom := by
      intro z hz
      obtain ⟨a, b, rfl⟩ := hZmem z hz
      have hx' : m * x * m⁻¹ ∈ Z ⊔ O := hconjx m hm
      have hw' : m * w * m⁻¹ ∈ Z ⊔ O := hconjw m hm
      show (MulAut.conj m).toMonoidHom (x ^ a * w ^ b) ∈ Z ⊔ O
      rw [map_mul, map_zpow, map_zpow]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (Z ⊔ O).mul_mem (zpow_mem hx' a) (zpow_mem hw' b)
    have hOle : O ≤ (Z ⊔ O).comap (MulAut.conj m).toMonoidHom := fun o ho => by
      simpa [MulAut.conj_apply] using
        mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hMO hm) o).mp ho)
    have := sup_le hZle hOle hh
    simpa [MulAut.conj_apply] using this
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hSM m hm h, fun hh => ?_⟩
  have := hSM m⁻¹ (M.inv_mem hm) _ hh
  have e : m⁻¹ * (m * h * m⁻¹) * m⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem l28_exists_invert (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hR : L28Prop34 3 P J x) {k : G} (hk : (P : Subgroup G) ⊓ J = zpowers k)
    (hk9 : orderOf k = 9) (hk3 : k ^ 3 ∈ L28Z (P : Subgroup G)) :
    ∃ ι ∈ M, ι * x * ι⁻¹ = x ∧ ι * k ^ 3 * ι⁻¹ = (k ^ 3)⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKn, hKc, hKL⟩ := l28_quot_data hS hU0 hp hM hgen hJ
  obtain ⟨hTsyl, hTinj, -⟩ := l28_T_data hS hU0 l28Three_proved hp hM hgen hJ
  obtain ⟨Tsyl, hTsylEq⟩ := hTsyl.exists_sylow_eq_subgroupOf
  obtain ⟨m, hmN, -, hm⟩ := l28m_sylow_inv hKL Tsyl
  have hTK := hTsyl.le
  have hmN' : (m : L34Quot x J) ∈ normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) :
      Subgroup (L34Quot x J)) : Set (L34Quot x J)) := by
    rw [hTsylEq] at hmN
    exact (mem_normalizer_subgroupOf_iff hTK m).mp hmN
  obtain ⟨j, hjC, hjJ, hjN, hjm⟩ := l28_lift_normalizer hS hU0 hp hM hgen hJ m.2 hmN'
  have hjM := l28_mem_M_of_normalizer hS hU0 hp hM hgen hJ hR hk hk9 hk3 hjJ hjN
  refine ⟨j, hjM, ?_, ?_⟩
  · have := mem_centralizer_singleton_iff.mp hjC
    rw [this]
    group
  · have hk3T : k ^ 3 ∈ (P : Subgroup G) ⊓ J := by rw [hk]; exact pow_mem (mem_zpowers k) 3
    have hC := hJ.le_centralizer
    have h1 : j * k ^ 3 * j⁻¹ ∈ (P : Subgroup G) ⊓ J :=
      (Subgroup.mem_normalizer_iff.mp hjN _).mp hk3T
    have h2 : (k ^ 3)⁻¹ ∈ (P : Subgroup G) ⊓ J := ((P : Subgroup G) ⊓ J).inv_mem hk3T
    have hk3C : k ^ 3 ∈ centralizer ({x} : Set G) := hC hk3T.2
    have h1C : j * k ^ 3 * j⁻¹ ∈ centralizer ({x} : Set G) := hC h1.2
    have h2C : (k ^ 3)⁻¹ ∈ centralizer ({x} : Set G) := hC h2.2
    have hφk : l34Hom x J ⟨k ^ 3, hk3C⟩ ∈ l34Img x J ((P : Subgroup G) ⊓ J) :=
      mem_l34Img_iff.mpr ⟨_, hk3T, rfl⟩
    have hφmem : (⟨l34Hom x J ⟨k ^ 3, hk3C⟩, hTK hφk⟩ : ↥(l34Img x J J)) ∈
        (Tsyl : Subgroup ↥(l34Img x J J)) := by
      rw [hTsylEq]
      exact Subgroup.mem_subgroupOf.mpr hφk
    have hinv := congrArg Subtype.val (hm _ hφmem)
    have hφ1 : l34Hom x J ⟨j * k ^ 3 * j⁻¹, h1C⟩ = l34Hom x J ⟨(k ^ 3)⁻¹, h2C⟩ := by
      have e1 : (⟨j * k ^ 3 * j⁻¹, h1C⟩ : ↥(centralizer ({x} : Set G))) =
          ⟨j, hjC⟩ * ⟨k ^ 3, hk3C⟩ * ⟨j, hjC⟩⁻¹ := rfl
      have e2 : (⟨(k ^ 3)⁻¹, h2C⟩ : ↥(centralizer ({x} : Set G))) = ⟨k ^ 3, hk3C⟩⁻¹ := rfl
      rw [e1, e2, map_mul, map_mul, map_inv, map_inv, hjm]
      simpa using hinv
    have h3 : (⟨(k ^ 3)⁻¹, h2C⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * ⟨j * k ^ 3 * j⁻¹, h1C⟩ = 1 := by
      apply hTinj
      · exact ((P : Subgroup G) ⊓ J).mul_mem (((P : Subgroup G) ⊓ J).inv_mem h2) h1
      · rw [map_mul, map_inv, hφ1, inv_mul_cancel]
    have h4 : (⟨j * k ^ 3 * j⁻¹, h1C⟩ : ↥(centralizer ({x} : Set G))) =
        ⟨(k ^ 3)⁻¹, h2C⟩ := by
      have := congrArg (fun c => (⟨(k ^ 3)⁻¹, h2C⟩ : ↥(centralizer ({x} : Set G))) * c) h3
      simpa using this
    exact congrArg Subtype.val h4

theorem l28_solvable (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hR : L28Prop34 3 P J x) {k : G} (hk : (P : Subgroup G) ⊓ J = zpowers k)
    (hk9 : orderOf k = 9) (hk3 : k ^ 3 ∈ L28Z (P : Subgroup G)) :
    ThreeSolvableChain (M ⊓ centralizer ({x} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set W : Subgroup G := M ⊓ C with hW
  have hWC : W ≤ C := inf_le_right
  set Φ : ↥W →* L34Quot x J := (l34Hom x J).comp (Subgroup.inclusion hWC) with hΦ
  obtain ⟨hKn, hKc, hKL⟩ := l28_quot_data hS hU0 hp hM hgen hJ
  obtain ⟨hTsyl, -, -⟩ := l28_T_data hS hU0 l28Three_proved hp hM hgen hJ
  obtain ⟨Tsyl, hTsylEq⟩ := hTsyl.exists_sylow_eq_subgroupOf
  have hTK := hTsyl.le
  have hOM : GLBPrimeCore 3 C ≤ M :=
    (glbPrimeCore_le_pPrimeCoreIn 3 _).trans (pPrimeCoreIn_centralizer_le hS hp hM hgen.2.2.2.ge)
  have hN₀W : GLBPrimeCore 3 C ≤ W := le_inf hOM (glbPrimeCore_le 3 C)
  have hDimg := l28_img_MJ hS hU0 hp hM hgen hJ hR hk hk9 hk3
  set D : Subgroup (L34Quot x J) := l34Img x J (M ⊓ J) with hD
  have hDK : D ≤ l34Img x J J := by rw [hDimg]; exact inf_le_left
  have hrange : Φ.range ≤ normalizer (D : Set (L34Quot x J)) := by
    rintro _ ⟨w, rfl⟩
    have hwC : (w : G) ∈ C := hWC w.2
    have hconj : ∀ w' : ↥W, ∀ z ∈ D, Φ w' * z * (Φ w')⁻¹ ∈ D := by
      intro w' z hz
      obtain ⟨c, hc, rfl⟩ := mem_l34Img_iff.mp hz
      have hw'C : (w' : G) ∈ C := hWC w'.2
      have hmem : (w' : G) * (c : G) * (w' : G)⁻¹ ∈ M ⊓ J :=
        ⟨M.mul_mem (M.mul_mem w'.2.1 hc.1) (M.inv_mem w'.2.1),
          (Subgroup.mem_normalizer_iff.mp (hJ.centralizer_le hw'C) (c : G)).mp hc.2⟩
      refine mem_l34Img_iff.mpr ⟨⟨(w' : G) * (c : G) * (w' : G)⁻¹, ?_⟩, hmem, ?_⟩
      · exact C.mul_mem (C.mul_mem hw'C c.2) (C.inv_mem hw'C)
      · show l34Hom x J (⟨(w' : G), hw'C⟩ * c * ⟨(w' : G), hw'C⟩⁻¹) = _
        rw [map_mul, map_mul, map_inv]
        rfl
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hconj w z hz
    · intro hz
      have := hconj w⁻¹ _ hz
      simpa [map_inv, mul_assoc] using this
  have hcard : Nat.card ↥Φ.range ∣ 54 := by
    refine (Subgroup.card_dvd_of_le hrange).trans ?_
    refine card_normalizer_dvd_54 (K := l34Img x J J) (D := D) hKc hKL hDK ⟨Tsyl, ?_⟩
    ext z
    rw [hTsylEq, Subgroup.mem_subgroupOf, hDimg, Subgroup.mem_inf]
    constructor
    · intro hz
      exact (mem_normalizer_subgroupOf_iff hTK z).mpr hz.2
    · intro hz
      exact ⟨z.2, (mem_normalizer_subgroupOf_iff hTK z).mp hz⟩
  refine ⟨GLBPrimeCore 3 C, ↥Φ.range, inferInstance, Φ.rangeRestrict, hN₀W, ?_, ?_,
    isSolvable_of_card_dvd_54 hcard, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀W).mpr
      (hWC.trans (le_normalizer_glbPrimeCore 3 C))
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 C)
  · intro w hw
    have hΦ1 : Φ w = 1 := by
      have := congrArg Subtype.val hw
      simpa using this
    have hDp := l28_reducedCentralizer_isPGroup hS hU0 hp hM hgen hJ
    have hDn := l28_reducedCentralizer_normal hJ
    set c : ↥C := ⟨(w : G), hWC w.2⟩ with hc
    have hφc : l34Hom x J c = 1 := hΦ1
    have hmem : QuotientGroup.mk' (primeComplementCore (G := C) 3) c ∈
        reducedCentralizerOfJ x J := by
      have h : QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore
          (QuotientGroup.mk' (primeComplementCore (G := C) 3) c) = 1 := hφc
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.normalCore_eq_self] at h
      exact h
    obtain ⟨n, hn⟩ := hDp ⟨_, hmem⟩
    refine ⟨n, ?_⟩
    have h1 : (QuotientGroup.mk' (primeComplementCore (G := C) 3) c) ^ 3 ^ n = 1 :=
      congrArg Subtype.val hn
    have h2 : c ^ 3 ^ n ∈ primeComplementCore (G := C) 3 := by
      have h3 : QuotientGroup.mk' (primeComplementCore (G := C) 3) (c ^ 3 ^ n) = 1 := by
        rw [map_pow]
        exact h1
      exact (QuotientGroup.eq_one_iff _).mp h3
    exact mem_glbPrimeCore_of_mem_primeComplementCore h2

theorem l28_closedConfig (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hR : L28Prop34 3 P J x) (hsh : L28Shape 3 (P : Subgroup G)) :
    ∃ k : G, L28ClosedConfig G M (P : Subgroup G) x k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hS.simple
  obtain ⟨k, hkT, hk9, n, hnN, hnx⟩ := l28_exists_swap hS hU0 hp hM hgen hJ hR
  obtain ⟨hxP, hxLO, hQsyl, -⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  obtain ⟨hPC, hZc, hZ, hfus, hout⟩ := hR
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hMtop : M ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hM.1.1
  have hxJ : x ∉ J := l28_x_not_mem_J hS hU0 hp hM hgen hJ
  have hkT' : k ∈ (P : Subgroup G) ⊓ J := by rw [hkT]; exact mem_zpowers k
  have hk3 : (k ^ 3) ^ 3 = 1 := by
    rw [← pow_mul, show 3 * 3 = 9 from rfl, ← hk9]
    exact pow_orderOf_eq_one k
  have hk3T : k ^ 3 ∈ (P : Subgroup G) ⊓ J := by rw [hkT]; exact pow_mem (mem_zpowers k) 3
  refine ⟨k, ?_⟩
  have hxZ : x ∈ L28Z (P : Subgroup G) :=
    mem_L28Z_iff.mpr ⟨hxP, fun p hp => mem_centralizer_singleton_iff.mp (hPC hp)⟩
  have hTJ : zpowers k ≤ J := by rw [← hkT]; exact inf_le_right
  have hSylTop : IsSylowOf 3 (P : Subgroup G) ⊤ :=
    isSylowOf_iff.mpr ⟨le_top, P.isPGroup', by
      rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
  refine
    { kgroup := catalogSimpleSections_of_isKProper hS.kProper M hMtop
      sylow := hSylTop.of_le hPM le_top
      focal := sylow_le_commutator_of_gamma_two hS hp hM (hU0 3 hp P M hM)
      shape := hsh
      x_mem := hxZ
      x_ne := hx1
      k_mem := hkT'.1
      k_order := hk9
      k_norm := ?_
      k_cube := hZ _ hk3T hk3
      x_not := fun h => hxJ (hTJ h)
      z_card := by simpa using hZc
      swap := ⟨n, normalizer_sylow_le hS hp hM hnN, hnN, hnx⟩
      invert := l28_exists_invert hS hU0 hp hM hgen hJ ⟨hPC, hZc, hZ, hfus, hout⟩ hkT hk9
        (hZ _ hk3T hk3)
      fusion := ?_
      solv := l28_solvable hS hU0 hp hM hgen hJ ⟨hPC, hZc, hZ, hfus, hout⟩ hkT hk9
        (hZ _ hk3T hk3) }
  · rw [← hkT]
    exact e9_le_normalizer_inf Subgroup.le_normalizer (hPC.trans hJ.centralizer_le)
  · intro g hg hgP
    have hmap : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) := by
      rw [MonoidHom.map_zpowers, zpowers_le]
      simpa [MulAut.conj_apply] using hgP
    have hy3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
    have hymem : g * x * g⁻¹ ∈ (zpowers x).map (MulAut.conj g).toMonoidHom :=
      ⟨x, mem_zpowers x, by simp [MulAut.conj_apply]⟩
    rcases hfus g hmap with h | h
    · rw [h] at hymem
      exact (zpowers_le.mpr hxZ) hymem
    · exact hZ _ ⟨hgP, h hymem⟩ hy3

theorem l28_Z_normal (hS : Setting G) (hU0 : FullCoreLocal G) (hKA : KFactL28Closed)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hR : L28Prop34 3 P J x) (hsh : L28Shape 3 (P : Subgroup G)) :
    M ≤ normalizer ((L28Z (P : Subgroup G) ⊔ GLBPrimeCore 3 M : Subgroup G) : Set G) := by
  obtain ⟨k, hk⟩ := l28_closedConfig hS hU0 hp hM hgen hJ hR hsh
  obtain ⟨N, hNO, hNM, hMN, hN3⟩ := hKA G M P x k hk
  exact l28_Z_normal_of_core hk.sylow (l28shape_facts hk.shape).1 hk.x_mem hk.x_ne hk.k_order
    hk.k_cube hk.x_not hk.z_card hk.swap hk.invert hk.fusion hNO hNM hMN hN3

theorem l28_lemma43_of_closed (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hKA : KFactL28Closed) : GL83GenericPrimeThreeL28Lemma43S G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34S
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ : IsL28Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  obtain ⟨hR, hsh⟩ := h34S
  obtain ⟨U, hV⟩ := l28_plane_exists hgen hR hsh
  refine ⟨U, hV, fun Y hY2 hYM hUY hYO => ?_⟩
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hxP : x ∈ (P : Subgroup G) := hgen.1
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hxZ : x ∈ L28Z (P : Subgroup G) :=
    mem_L28Z_iff.mpr ⟨hxP, fun p hp => mem_centralizer_singleton_iff.mp (hR.1 hp)⟩
  have hZnorm := l28_Z_normal hS hU0 hKA hp hM hgen hJ hR hsh
  have hdata : CoreData G M (GLBPrimeCore 3 M) (L28Z (P : Subgroup G)) (P : Subgroup G) U x :=
    { O_le := glbPrimeCore_le 3 M
      O_norm := le_normalizer_glbPrimeCore 3 M
      O_cop := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 M)
      O₂_le := pCoreOf_le_glbPrimeCore Nat.prime_two (by norm_num) M
      O₂_ne := by
        obtain ⟨S, hSne, hS2, hSM⟩ := hM.1.1
        have hSleM : S ≤ M := by rw [hSM]; exact Subgroup.le_normalizer
        intro hbot
        apply hSne
        rw [eq_bot_iff]
        have := normal_pGroup_le_pCoreOf 2 S M hSleM
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hSleM).mpr hSM.le) hS2
        exact this.trans hbot.le
      charTwo := hS.charTwo M hM.1.1
      Z_le := L28Z_le.trans hPM
      Z_el := (l28shape_facts hsh).1
      Z_card := by simpa using hR.2.1
      Z_norm := hZnorm
      x_mem := hxZ
      x_ne := hx1
      U_le := hV.1.trans (inf_le_left.trans hPM)
      U_el := hV.2.1
      U_card := by simpa using hV.2.2.1
      xU := hV.2.2.2.1
      U_inf_Z := l28plane_inf_center hgen hR hV
      U_comm := fun a ha z hz => (mem_L28Z_iff.mp hz).2 a (hV.1 ha).1
      P_le := hPM
      Z_le_P := L28Z_le
      P_cen := fun z hz p hp => (mem_L28Z_iff.mp hz).2 p hp
      Z_cube := (l28shape_facts hsh).2.1
      D1 := fun Y₀ hne h2 hr =>
        le_of_three_le_pRank_inf hD1 hp hM ⟨Y₀, hne, h2, rfl⟩ hr }
  exact hdata.normalizer_le hY2 hYM hYO hUY

omit [Finite G] in
theorem l28shape_K {P : Subgroup G} (h : L28Shape 3 P) :
    ∃ K : Subgroup G, K ≤ P ∧ (∀ R : Subgroup G, K < R → R ≤ P → R = P) ∧
      P ≤ normalizer (K : Set G) ∧ (∀ a ∈ K, ∀ b ∈ K, a * b = b * a) ∧
      (∀ a ∈ K, a ^ 9 = 1) ∧ Nat.card K = 3 ^ 4 ∧
      ∀ a : G, a ∈ L28Z P ↔ a ∈ K ∧ a ^ 3 = 1 := by
  obtain ⟨-, K, hKP, hKmax, ⟨e⟩, -, ⟨A, B, -, -, -, hABK, hAn, hBn⟩, hZ⟩ := h
  have hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    have h1 := e.injective (show e (⟨a, ha⟩ * ⟨b, hb⟩) = e (⟨b, hb⟩ * ⟨a, ha⟩) by
      rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h1
  have hm : ∀ m : Multiplicative (ZMod (3 ^ 2)), m ^ (3 ^ 2) = 1 := fun m => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hKexp : ∀ a ∈ K, a ^ 9 = 1 := by
    intro a ha
    have h1 : e ((⟨a, ha⟩ : ↥K) ^ 9) = 1 := by
      rw [map_pow]
      exact Prod.ext (hm _) (hm _)
    have h2 := e.injective (h1.trans (map_one e).symm)
    simpa using congrArg Subtype.val h2
  have hKc : Nat.card K = 3 ^ 4 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod]
    ring
  have hPK : P ≤ normalizer (K : Set G) := fun g hg => by
    rw [← hABK]
    exact mem_normalizer_sup (hAn hg) (hBn hg)
  exact ⟨K, hKP.le, hKmax, hPK, hKab, hKexp, hKc, hZ⟩

omit [Finite G] in
theorem l28_cube_formula {P K : Subgroup G} (hKP : K ≤ P) (hPK : P ≤ normalizer (K : Set G))
    (hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hK9 : ∀ a ∈ K, a ^ 9 = 1)
    (hZ : ∀ a : G, a ∈ L28Z P ↔ a ∈ K ∧ a ^ 3 = 1) {w q : G} (hw : w ∈ P) (hw3 : w ^ 3 = 1)
    (hq : q ∈ K) : (w * q) ^ 3 = q ^ 3 := by
  set d : G := w * q * w⁻¹ * q⁻¹ with hd
  have hq' : w * q * w⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hPK hw) q).mp hq
  have hdK : d ∈ K := K.mul_mem hq' (K.inv_mem hq)
  have hq3Z : q ^ 3 ∈ L28Z P := by
    refine (hZ _).mpr ⟨K.pow_mem hq 3, ?_⟩
    rw [← pow_mul]
    exact hK9 q hq
  have hq3c : w * q ^ 3 = q ^ 3 * w := (mem_L28Z_iff.mp hq3Z).2 w hw
  have hd3 : d ^ 3 = 1 := by
    have hcomm : Commute (w * q * w⁻¹) q⁻¹ := hKab _ hq' _ (K.inv_mem hq)
    have h1 : d ^ 3 = (w * q * w⁻¹) ^ 3 * (q⁻¹) ^ 3 := hcomm.mul_pow 3
    have h2 : (w * q * w⁻¹) ^ 3 = q ^ 3 := by
      have : (w * q * w⁻¹) ^ 3 = w * q ^ 3 * w⁻¹ := conj_pow
      rw [this, hq3c]
      group
    rw [h1, h2, inv_pow, mul_inv_cancel]
  have hdZ : d ∈ L28Z P := (hZ _).mpr ⟨hdK, hd3⟩
  have hdw : w * d = d * w := (mem_L28Z_iff.mp hdZ).2 w hw
  have hdq : q * d = d * q := (mem_L28Z_iff.mp hdZ).2 q (hKP hq)
  have e1 : w * q * w⁻¹ = d * q := by rw [hd]; group
  have hw' : w * w * w = 1 := by
    rw [show w * w * w = w ^ 3 by rw [pow_succ, pow_succ, pow_one]]
    exact hw3
  have e2 : w * w * q * w⁻¹ * w⁻¹ = d * d * q := by
    calc w * w * q * w⁻¹ * w⁻¹ = w * (w * q * w⁻¹) * w⁻¹ := by group
      _ = w * (d * q) * w⁻¹ := by rw [e1]
      _ = (w * d * w⁻¹) * (w * q * w⁻¹) := by group
      _ = d * (d * q) := by
        rw [e1, show w * d * w⁻¹ = d by rw [hdw]; group]
      _ = d * d * q := by group
  have e3 : (w * q) ^ 3 = (w * q * w⁻¹) * (w * w * q * w⁻¹ * w⁻¹) * (w * w * w) * q := by
    rw [pow_three']
    group
  rw [e3, e1, e2, hw', mul_one]
  calc d * q * (d * d * q) * q = d * (q * d) * d * q * q := by group
    _ = d * (d * q) * d * q * q := by rw [hdq]
    _ = d * d * (q * d) * q * q := by group
    _ = d * d * (d * q) * q * q := by rw [hdq]
    _ = (d * d * d) * (q * q * q) := by group
    _ = d ^ 3 * q ^ 3 := by rw [pow_three', pow_three']
    _ = q ^ 3 := by rw [hd3, one_mul]

omit [Finite G] in
theorem l28_omega1_comm {P : Subgroup G} (h : L28Shape 3 P) {a u : G} (ha : a ∈ P) (hu : u ∈ P)
    (ha3 : a ^ 3 = 1) (hu3 : u ^ 3 = 1) : a * u = u * a := by
  obtain ⟨K, hKP, hKmax, hPK, hKab, hK9, -, hZ⟩ := l28shape_K h
  by_cases huK : u ∈ K
  · exact (mem_L28Z_iff.mp ((hZ u).mpr ⟨huK, hu3⟩)).2 a ha
  ·
    have hPeq : zpowers u ⊔ K = P := by
      have h1 : K ≤ zpowers u ⊔ K := le_sup_right
      refine hKmax _ (lt_of_le_of_ne h1 fun h' => huK ?_) (sup_le (zpowers_le.mpr hu) hKP)
      rw [h']
      exact mem_sup_left (mem_zpowers u)
    have hzn : zpowers u ≤ normalizer (K : Set G) := zpowers_le.mpr (hPK hu)
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers u) K hzn
    have : a ∈ (zpowers u : Set G) * (K : Set G) := by
      rw [← hset, hPeq]
      exact ha
    obtain ⟨w, hw, q, hq, hwq⟩ := this
    have hwq' : w * q = a := hwq
    have hwP : w ∈ P := (zpowers_le.mpr hu) hw
    have hw3 : w ^ 3 = 1 := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]
    have hq3 : q ^ 3 = 1 := by
      have := l28_cube_formula hKP hPK hKab hK9 hZ hwP hw3 hq
      rw [hwq', ha3] at this
      exact this.symm
    have hqZ : q ∈ L28Z P := (hZ q).mpr ⟨hq, hq3⟩
    have hqu : u * q = q * u := (mem_L28Z_iff.mp hqZ).2 u hu
    have hwu : w * u = u * w := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
      exact ((Commute.refl u).zpow_left i).eq
    rw [← hwq']
    calc w * q * u = w * (q * u) := by group
      _ = w * (u * q) := by rw [← hqu]
      _ = (w * u) * q := by group
      _ = (u * w) * q := by rw [hwu]
      _ = u * (w * q) := by group


omit [Finite G] in
theorem zpowers_three_cases {x y : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy : y ∈ zpowers x)
    (hy1 : y ≠ 1) : y = x ∨ y = x⁻¹ := by
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  have h : x ^ (i % 3) = x ^ i := by
    have := zpow_mod_orderOf x i
    rw [hxo] at this
    simpa using this
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h0 | h1 | h2
  · rw [h0, zpow_zero] at h
    exact absurd h.symm hy1
  · rw [h1, zpow_one] at h
    exact Or.inl h.symm
  · rw [h2] at h
    right
    rw [← h, zpow_two]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_three', hx3])

omit [Finite G] in
theorem commute_of_weaklyClosed {x f : G} {U : Subgroup G} (hxU : x ∈ U) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hwc : LineWeaklyClosed x U) (hfU : f ∈ normalizer (U : Set G)) {n : ℕ}
    (hf : f ^ 3 ^ n = 1) : f * x = x * f := by
  have hmap : (zpowers x).map (MulAut.conj f).toMonoidHom ≤ U := by
    rintro _ ⟨z, hz, rfl⟩
    have hzU : z ∈ U := (zpowers_le.mpr hxU) hz
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hfU z).mp hzU
  have hy : f * x * f⁻¹ ∈ zpowers x := by
    have hmem : f * x * f⁻¹ ∈ (zpowers x).map (MulAut.conj f).toMonoidHom :=
      ⟨x, mem_zpowers x, by simp [MulAut.conj_apply]⟩
    rwa [hwc f hmap] at hmem
  have hy1 : f * x * f⁻¹ ≠ 1 := fun h => hx1 (by
    have : x = f⁻¹ * (f * x * f⁻¹) * f := by group
    rw [this, h]
    group)
  rcases zpowers_three_cases hx3 hx1 hy hy1 with h | h
  · calc f * x = (f * x * f⁻¹) * f := by group
      _ = x * f := by rw [h]
  · exfalso
    have hfx : f * x = x⁻¹ * f := by
      calc f * x = (f * x * f⁻¹) * f := by group
        _ = x⁻¹ * f := by rw [h]
    have h1 : f * x⁻¹ * f⁻¹ = x := by
      have : f * x⁻¹ * f⁻¹ = (f * x * f⁻¹)⁻¹ := by group
      rw [this, h, inv_inv]
    have hfx' : f * x⁻¹ = x * f := by
      calc f * x⁻¹ = (f * x⁻¹ * f⁻¹) * f := by group
        _ = x * f := by rw [h1]
    have hf2 : f ^ 2 * x = x * f ^ 2 := by
      rw [pow_two]
      calc f * f * x = f * (f * x) := by group
        _ = f * (x⁻¹ * f) := by rw [hfx]
        _ = (f * x⁻¹) * f := by group
        _ = (x * f) * f := by rw [hfx']
        _ = x * (f * f) := by group
    obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
    have hfm : (f ^ 2) ^ (m + 1) = f := by
      rw [← pow_mul, show 2 * (m + 1) = 3 ^ n + 1 by omega, pow_succ, hf, one_mul]
    have hc : Commute f x := by
      have : Commute (f ^ 2) x := hf2
      rw [← hfm]
      exact this.pow_left (m + 1)
    have h2 : f * x * f⁻¹ = x := by rw [hc.eq]; group
    rw [h2] at h
    have hxx : x * x = 1 := by
      calc x * x = x * x⁻¹ := congrArg (x * ·) h
        _ = 1 := mul_inv_cancel x
    apply hx1
    have : x ^ 3 = x * (x * x) := pow_three x
    rw [hxx, mul_one] at this
    rw [← this]
    exact hx3

omit [Finite G] in
theorem exists_mem_conj_le_sylow {p : ℕ} [Fact p.Prime] [Finite G] {P K X : Subgroup G}
    (hP : IsSylowOf p P K) (hXK : X ≤ K) (hX : IsPGroup p X) :
    ∃ k ∈ K, ∀ y ∈ X, k⁻¹ * y * k ∈ P := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', hQ'⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨c, c.2, fun y hy => ?_⟩
  have hy' : (⟨y, hXK hy⟩ : K) ∈ ((c • Q : Sylow p K) : Subgroup K) := hQ' hy
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  exact ⟨_, hy', by simp [MulAut.inv_apply]⟩


theorem card_le_nine_of_cube {B : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h9 : ∀ b ∈ B, b ^ 9 = 1)
    (h3 : ∀ b ∈ B, b ^ 3 = 1 → b ∈ zpowers x) : Nat.card B ≤ 9 := by
  let φ : ↥B →* ↥B := MonoidHom.mk' (fun b => b ^ 3) (fun a b => by
    apply Subtype.ext
    show ((a : G) * (b : G)) ^ 3 = (a : G) ^ 3 * (b : G) ^ 3
    exact Commute.mul_pow (hcomm a a.2 b b.2) 3)
  have key : ∀ S : Subgroup ↥B, (∀ s ∈ S, ((s : B) : G) ∈ zpowers x) → Nat.card S ≤ 3 := by
    intro S hS
    have hinj : Function.Injective
        (fun s : ↥S => (⟨((s : B) : G), hS s s.2⟩ : ↥(zpowers x))) := by
      intro s t hst
      have h1 := congrArg Subtype.val hst
      exact Subtype.ext (Subtype.ext h1)
    calc Nat.card S ≤ Nat.card (zpowers x) := Nat.card_le_card_of_injective _ hinj
      _ = orderOf x := Nat.card_zpowers x
      _ ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx3)
  have hker : Nat.card φ.ker ≤ 3 := key _ (fun s hs => by
    have h1 : (s ^ 3 : ↥B) = 1 := hs
    have h2 : ((s : B) : G) ^ 3 = 1 := by simpa using congrArg Subtype.val h1
    exact h3 _ s.2 h2)
  have hrange : Nat.card φ.range ≤ 3 := key _ (fun s hs => by
    obtain ⟨b, rfl⟩ := hs
    exact h3 _ (B.pow_mem b.2 3) (by
      show (((b : B) : G) ^ 3) ^ 3 = 1
      rw [← pow_mul]
      exact h9 b b.2))
  have hc := Subgroup.card_ker_mul_card_range φ
  calc Nat.card B = Nat.card φ.ker * Nat.card φ.range := hc.symm
    _ ≤ 3 * 3 := Nat.mul_le_mul hker hrange


omit [Finite G] in
theorem conj_inv_cube {a g : G} (h : a ^ 3 = 1) : (g⁻¹ * a * g) ^ 3 = 1 := by
  have e : g⁻¹ * a * g = g⁻¹ * a * g⁻¹⁻¹ := by rw [inv_inv]
  rw [e, conj_pow, h]
  group

omit [Finite G] in
theorem conj_inv_pow {a g : G} {n : ℕ} : (g⁻¹ * a * g) ^ n = g⁻¹ * a ^ n * g := by
  have e : g⁻¹ * a * g = g⁻¹ * a * g⁻¹⁻¹ := by rw [inv_inv]
  rw [e, conj_pow, inv_inv]

omit [Finite G] in
theorem isElemAbelian_map {p : ℕ} {A : Subgroup G} (h : IsElemAbelian p A) (f : G →* G) :
    IsElemAbelian p (A.map f) := by
  have := h.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨u, hu, hua⟩ := a.2
    obtain ⟨v, hv, hvb⟩ := b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← hua, ← hvb, ← map_mul, ← map_mul, setLike_mul_comm hu hv]
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, h.2 u hu, map_one]

theorem l28_conj_plane_ne (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hR : L28Prop34 3 P J x) (hsh : L28Shape 3 (P : Subgroup G)) {U : Subgroup G}
    (hV : L28InV 3 P x U) {c : G} (hc : c ∈ centralizer ({x} : Set G)) :
    ¬ U ≤ (L28Z (P : Subgroup G)).map (MulAut.conj c).toMonoidHom := by
  intro hle
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, hk9, -⟩ := l28_exists_swap hS hU0 hp hM hgen hJ hR
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := id hgen
  obtain ⟨hPC, hZc, hZ3, -, -⟩ := hR
  obtain ⟨hUQ, -, hUc, -, hUZ⟩ := hV
  have hxZ : x ∈ L28Z (P : Subgroup G) :=
    mem_L28Z_iff.mpr ⟨hxP, fun p hp => mem_centralizer_singleton_iff.mp (hPC hp)⟩
  have hk3T : k ^ 3 ∈ (P : Subgroup G) ⊓ J := by rw [hk]; exact pow_mem (mem_zpowers k) 3
  have hk33 : (k ^ 3) ^ 3 = 1 := by
    rw [← pow_mul, show 3 * 3 = 9 from rfl, ← hk9]
    exact pow_orderOf_eq_one k
  have hk31 : k ^ 3 ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num : 0 < 3) h
    omega
  have hkw : k ^ 3 ∈ L28Z (P : Subgroup G) := hZ3 _ hk3T hk33
  have hxJ : x ∉ J := l28_x_not_mem_J hS hU0 hp hM hgen hJ
  have hxk : x ∉ zpowers k := fun h => hxJ ((by rw [← hk]; exact inf_le_right :
    zpowers k ≤ J) h)
  have hZel := (l28shape_facts hsh).1
  have hxnw : x ∉ zpowers (k ^ 3) := fun h =>
    hxk ((zpowers_le.mpr (pow_mem (mem_zpowers k) 3)) h)
  have hdec := l28_Z_decomp hZel hxZ hx1 hkw hk31 hxnw hZc
  set Zc : Subgroup G := (L28Z (P : Subgroup G)).map (MulAut.conj c).toMonoidHom with hZc'
  have hZccard : Nat.card Zc = 3 ^ 2 := by
    rw [hZc', Subgroup.card_map_of_injective (MulAut.conj c).injective, hZc]
  have hUZc : U = Zc := Subgroup.eq_of_le_of_card_ge hle (by rw [hUc, hZccard])
  have hckP : c * k ^ 3 * c⁻¹ ∈ (P : Subgroup G) := by
    have hmem : c * k ^ 3 * c⁻¹ ∈ Zc := ⟨k ^ 3, hkw, by simp [MulAut.conj_apply]⟩
    rw [← hUZc] at hmem
    exact (hUQ.trans inf_le_left) hmem
  have hckJ : c * k ^ 3 * c⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (hJ.centralizer_le hc) (k ^ 3)).mp hk3T.2
  have hckT : c * k ^ 3 * c⁻¹ ∈ (P : Subgroup G) ⊓ J := ⟨hckP, hckJ⟩
  have hTcyc : IsCyclic ↥((P : Subgroup G) ⊓ J) := by rw [hk]; infer_instance
  have hck3 : (c * k ^ 3 * c⁻¹) ^ 3 = 1 := by rw [conj_pow, hk33]; group
  have hckZ : c * k ^ 3 * c⁻¹ ∈ zpowers (k ^ 3) :=
    mem_zpowers_of_isCyclic_of_pow_three hTcyc hk3T hckT hk31 hk33 hck3
  have hckZ' : c * k ^ 3 * c⁻¹ ∈ L28Z (P : Subgroup G) := (zpowers_le.mpr hkw) hckZ
  have hcxc : c * x * c⁻¹ = x := by
    rw [mem_centralizer_singleton_iff.mp hc]
    group
  have hZcle : Zc ≤ L28Z (P : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨a, b, rfl⟩ := hdec z hz
    have hφ : ∀ y : G, (MulAut.conj c).toMonoidHom y = c * y * c⁻¹ := fun y => by
      simp [MulAut.conj_apply]
    have : (MulAut.conj c).toMonoidHom (x ^ a * (k ^ 3) ^ b) =
        x ^ a * (c * k ^ 3 * c⁻¹) ^ b := by
      rw [map_mul, map_zpow, map_zpow, hφ x, hφ (k ^ 3), hcxc]
    rw [this]
    exact (L28Z (P : Subgroup G)).mul_mem (zpow_mem hxZ a) (zpow_mem hckZ' b)
  have hUle : U ≤ L28Z (P : Subgroup G) := hUZc ▸ hZcle
  exact hUZ (Subgroup.eq_of_le_of_card_ge hUle (by rw [hUc, hZc]))


theorem l28_endgame_structure (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hR : L28Prop34 3 P J x) (hsh : L28Shape 3 (P : Subgroup G)) {U : Subgroup G}
    (hV : L28InV 3 P x U) {F : Subgroup G} (hFp : IsPGroup 3 F) (hUF : U ≤ F) (hFM : F ≤ M)
    (hrkF : CFSG.Open.pRank 3 F ≤ 2) :
    F ≤ normalizer (U : Set G) ∧ (∀ f ∈ F, f * x = x * f) ∧ (∀ f ∈ F, f ^ 3 = 1 → f ∈ U) ∧
      Nat.card F ≤ 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV0 := hV
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := id hgen
  have hPC := hR.1
  have hxZ : x ∈ L28Z (P : Subgroup G) :=
    mem_L28Z_iff.mpr ⟨hxP, fun p hp => mem_centralizer_singleton_iff.mp (hPC hp)⟩
  obtain ⟨hUQ, hUel, hUc, hxU, hUZ⟩ := hV
  have hwc : LineWeaklyClosed x U := l28plane_wc hgen hR hV0
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hcentU : ∀ f ∈ F, f ∈ normalizer (U : Set G) → f * x = x * f := by
    intro f hf hfU
    obtain ⟨n, hn⟩ := hFp ⟨f, hf⟩
    exact commute_of_weaklyClosed hxU hx3 hx1 hwc hfU (n := n)
      (by simpa using congrArg Subtype.val hn)
  set Kx : Subgroup G := M ⊓ centralizer ({x} : Set G) with hKx
  have hPKx : (P : Subgroup G) ≤ Kx := le_inf hPM hPC
  have hSylTop : IsSylowOf 3 (P : Subgroup G) ⊤ :=
    isSylowOf_iff.mpr ⟨le_top, P.isPGroup', by
      rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
  have hSylKx : IsSylowOf 3 (P : Subgroup G) Kx := hSylTop.of_le hPKx le_top
  set F₁ : Subgroup G := F ⊓ normalizer (U : Set G) with hF₁
  have hF₁Kx : F₁ ≤ Kx := fun f hf =>
    ⟨hFM hf.1, mem_centralizer_singleton_iff.mpr (hcentU f hf.1 hf.2)⟩
  have hF₁p : IsPGroup 3 F₁ := hFp.to_le inf_le_left
  obtain ⟨c, hcKx, hc⟩ := exists_mem_conj_le_sylow hSylKx hF₁Kx hF₁p
  have hcC : c ∈ centralizer ({x} : Set G) := hcKx.2
  have hΩcomm : ∀ a ∈ F₁, ∀ b ∈ F₁, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a := by
    intro a ha b hb ha3 hb3
    have h1 := l28_omega1_comm hsh (hc a ha) (hc b hb) (conj_inv_cube ha3) (conj_inv_cube hb3)
    calc a * b = c * ((c⁻¹ * a * c) * (c⁻¹ * b * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * b * c) * (c⁻¹ * a * c)) * c⁻¹ := by rw [h1]
      _ = b * a := by group
  have hΩU : ∀ f ∈ F₁, f ^ 3 = 1 → f ∈ U := by
    intro f hf hf3
    by_contra hfU
    exact u3hf_inf_card_le hf3 hf.1 hfU
      (fun t ht => hΩcomm t ⟨hUF ht, Subgroup.le_normalizer ht⟩ f hf (hUel.2 t ht) hf3)
      hUel.2 hrkF U (le_inf hUF le_rfl) hUc
  have hFF₁ : F ≤ normalizer (U : Set G) := by
    by_contra hnot
    have hlt : F₁.subgroupOf F < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hnot
      intro f hf
      have : (⟨f, hf⟩ : ↥F) ∈ F₁.subgroupOf F := by rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
    haveI : Group.IsNilpotent ↥F := hFp.isNilpotent
    obtain ⟨f, hfN, hfnot⟩ := SetLike.exists_of_lt
      ((Group.normalizerCondition_of_isNilpotent (G := ↥F)) _ hlt)
    have hfF₁N : ∀ g ∈ F₁, (f : G) * g * (f : G)⁻¹ ∈ F₁ := by
      intro g hg
      have := (Subgroup.mem_normalizer_iff.mp hfN ⟨g, hg.1⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
      exact Subgroup.mem_subgroupOf.mp this
    have hfF₁N' : ∀ g ∈ F₁, (f : G)⁻¹ * g * (f : G) ∈ F₁ := by
      intro g hg
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer _).inv_mem hfN) ⟨g, hg.1⟩).mp
        (Subgroup.mem_subgroupOf.mpr hg)
      simpa using Subgroup.mem_subgroupOf.mp this
    have hfU : (f : G) ∈ normalizer (U : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        have h1 := hfF₁N u ⟨hUF hu, Subgroup.le_normalizer hu⟩
        exact hΩU _ h1 (by rw [conj_pow, hUel.2 u hu]; group)
      · intro hu
        have hv₁ : (f : G) * u * (f : G)⁻¹ ∈ F₁ := ⟨hUF hu, Subgroup.le_normalizer hu⟩
        have h2 := hfF₁N' _ hv₁
        have e : (f : G)⁻¹ * ((f : G) * u * (f : G)⁻¹) * (f : G) = u := by group
        rw [e] at h2
        refine hΩU _ h2 ?_
        have hv3 : ((f : G) * u * (f : G)⁻¹) ^ 3 = 1 := hUel.2 _ hu
        have h3 : (f : G) * u ^ 3 * (f : G)⁻¹ = 1 := by rw [← conj_pow]; exact hv3
        calc u ^ 3 = (f : G)⁻¹ * ((f : G) * u ^ 3 * (f : G)⁻¹) * (f : G) := by group
          _ = 1 := by rw [h3]; group
    exact hfnot (Subgroup.mem_subgroupOf.mpr ⟨f.2, hfU⟩)
  have hFΩ : ∀ f ∈ F, f ^ 3 = 1 → f ∈ U := fun f hf hf3 => hΩU f ⟨hf, hFF₁ hf⟩ hf3
  refine ⟨hFF₁, fun f hf => hcentU f hf (hFF₁ hf), hFΩ, ?_⟩
  have hc' : ∀ y ∈ F, c⁻¹ * y * c ∈ (P : Subgroup G) := fun y hy => hc y ⟨hy, hFF₁ hy⟩
  set A : Subgroup G := F.map (MulAut.conj c⁻¹).toMonoidHom with hA
  have hφ : ∀ y : G, (MulAut.conj c⁻¹).toMonoidHom y = c⁻¹ * y * c := fun y => by
    simp [MulAut.conj_apply]
  have hAP : A ≤ (P : Subgroup G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hφ]
    exact hc' y hy
  have hAcard : Nat.card A = Nat.card F :=
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  obtain ⟨K, hKP, hKmax, hPK, hKab, hK9, hKc, hZ⟩ := l28shape_K hsh
  set U' : Subgroup G := U.map (MulAut.conj c⁻¹).toMonoidHom with hU'
  have hU'A : U' ≤ A := Subgroup.map_mono hUF
  have hU'V : L28InV 3 P x U' := by
    refine ⟨le_inf (hU'A.trans hAP) ?_, isElemAbelian_map hUel _, ?_, ?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      rw [hφ]
      exact (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem
        ((centralizer ({x} : Set G)).inv_mem hcC) (hUQ hu).2) hcC
    · rw [hU', Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hUc]
    · refine ⟨x, hxU, ?_⟩
      rw [hφ]
      have h1 : c * x = x * c := mem_centralizer_singleton_iff.mp hcC
      calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
        _ = c⁻¹ * (c * x) := by rw [h1]
        _ = x := by group
    · intro h
      refine l28_conj_plane_ne hS hU0 hp hM hgen hJ hR hsh hV0 hcC (fun u hu => ?_)
      have hmem : c⁻¹ * u * c ∈ L28Z (P : Subgroup G) := by
        rw [← h]
        exact ⟨u, hu, by rw [hφ]⟩
      exact ⟨c⁻¹ * u * c, hmem, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hZU' : U' ⊓ L28Z (P : Subgroup G) = zpowers x := l28plane_inf_center hgen hR hU'V
  have hB3 : ∀ b ∈ A ⊓ K, b ^ 3 = 1 → b ∈ zpowers x := by
    rintro b ⟨hbA, hbK⟩ hb3
    obtain ⟨y, hy, hyb⟩ := hbA
    have hyb' : c⁻¹ * y * c = b := by rw [← hφ]; exact hyb
    have hy3 : y ^ 3 = 1 := by
      have h1 : (c⁻¹ * y * c) ^ 3 = c⁻¹ * y ^ 3 * c := conj_inv_pow
      rw [hyb', hb3] at h1
      calc y ^ 3 = c * (c⁻¹ * y ^ 3 * c) * c⁻¹ := by group
        _ = 1 := by rw [← h1]; group
    have hyU : y ∈ U := hFΩ y hy hy3
    have hbU' : b ∈ U' := ⟨y, hyU, hyb⟩
    have hbZ : b ∈ L28Z (P : Subgroup G) := (hZ b).mpr ⟨hbK, hb3⟩
    rw [← hZU']
    exact ⟨hbU', hbZ⟩
  have hB0 : Nat.card ↥(A ⊓ K) ≤ 9 :=
    card_le_nine_of_cube hx3 (fun a ha b hb => hKab a ha.2 b hb.2) (fun b hb => hK9 b hb.2) hB3
  have hAK : A ≤ normalizer (K : Set G) := hAP.trans hPK
  have hc2 := e9_card_sup_mul_card_inf hAK
  have hAKP : A ⊔ K ≤ (P : Subgroup G) := sup_le hAP hKP
  have hPc : Nat.card (P : Subgroup G) = 3 ^ 5 := hsh.1
  have h1 : Nat.card ↥(A ⊔ K) ≤ 3 ^ 5 := hPc ▸ Subgroup.card_le_of_le hAKP
  rw [hKc] at hc2
  have h2 : Nat.card A * 3 ^ 4 ≤ 3 ^ 5 * 9 := by
    calc Nat.card A * 3 ^ 4 = Nat.card ↥(A ⊔ K) * Nat.card ↥(A ⊓ K) := hc2.symm
      _ ≤ 3 ^ 5 * 9 := Nat.mul_le_mul h1 hB0
  have h27 : Nat.card A ≤ 27 := by norm_num at h2; omega
  calc Nat.card F = Nat.card A := hAcard.symm
    _ ≤ 27 := h27
    _ = 3 ^ 3 := by norm_num

theorem l28_nonab_of_kfact (hS : Setting G) (hU0 : FullCoreLocal G) (hKB : KFactL28Endgame) :
    GL83Generic4_9BNonabS G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34S U hV hC
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ : IsL28Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  obtain ⟨hR, hsh⟩ := h34S
  intro S R₀ F hS2 hSne hUS hesc hR₀2 hR₀O hR₀S hUR₀ hR₀n hFH hUF hFM hrkF
  by_contra hnc
  have hxU : x ∈ U := hV.2.2.2.1
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  have hUel : IsElemAbelian 3 U := hV.2.1
  have hUc : Nat.card U = 3 ^ 2 := hV.2.2.1
  obtain ⟨-, hFx, hFΩ, hFc⟩ := l28_endgame_structure hS hU0 hp hM hgen hJ hR hsh hV hFH.isPGroup
    hUF hFM hrkF
  obtain ⟨n, hn⟩ := hFH.isPGroup.exists_card_eq
  have h9 : 3 ^ 2 ∣ 3 ^ n := by
    rw [← hn, ← hUc]
    exact Subgroup.card_dvd_of_le hUF
  have hn2 : 2 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h9
  have hn3 : n ≤ 3 := by
    by_contra h
    have h4 : 3 ^ 4 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 3 ^ 4 ≤ 3 ^ 3 := by rw [← hn] at h4; exact h4.trans hFc
    norm_num at h5
  have hF27 : Nat.card F = 3 ^ 3 := by
    rcases (by omega : n = 2 ∨ n = 3) with rfl | rfl
    · exfalso
      have hFU : U = F := Subgroup.eq_of_le_of_card_ge hUF (by rw [hn, hUc])
      apply hnc
      rw [← hFU]
      exact hUel.1
    · exact hn
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hHtop : normalizer (S : Set G) ≠ ⊤ := by
    intro htop
    have hnormal : S.Normal := normalizer_eq_top_iff.mp htop
    have := hS.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
    · exact hSne h
    · obtain ⟨k, hk⟩ := hS2 ⟨x, h ▸ mem_top x⟩
      have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h1 := orderOf_dvd_of_pow_eq_one hxk
      rw [hxo] at h1
      have h3 : 3 ∣ 2 ^ k := h1
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  have hHK : CatalogSimpleSections ↥(normalizer (S : Set G)) :=
    catalogSimpleSections_of_isKProper hS.kProper _ hHtop
  exact hR₀n (hKB G (normalizer (S : Set G)) M F U R₀ x hHK hFH hnc hF27 hFM hUF hUel hUc hFΩ hxU
    hx1 hFx (fun u hu hux => inf_le_left.trans (hC u hu hux)) hR₀2 hR₀S hUR₀ hR₀O)

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Aux

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem gl83P3L28_residues {G : Type} [Group G] [Finite G] (hS : Setting G) (hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) (hKA : KFactL28Closed) (hKB : KFactL28Endgame) :
    GL83GenericPrimeThreeL28Lemma43S G ∧ GL83Generic4_9BNonabS G :=
  ⟨GL83P3L28Aux.l28_lemma43_of_closed hS hD1 hU0 hKA, GL83P3L28Aux.l28_nonab_of_kfact hS hU0 hKB⟩

theorem gl83P3L28_holds (hKA : KFactL28Closed) (hKB : KFactL28Endgame) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
      GL83GenericPrimeThreeL28Lemma43S G ∧ GL83Generic4_9BNonabS G :=
  fun _ _ _ hS hD1 hU0 => gl83P3L28_residues hS hD1 hU0 hKA hKB

end CFSG.LocalAnalysis.RankThreeTheoremC
