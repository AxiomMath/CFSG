module

public import CFSG.CGT.PushingUpLit.SolKAb.Vocab
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Basic
import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma24
import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.CGT.PushingUpLit.SolKAb (IsCommSubgroup)

variable {G : Type} [Group G]

structure TIPair (R T : Subgroup G) : Prop where
  two_R : IsPGroup 2 R
  two_T : IsPGroup 2 T
  T_ne : T ≠ ⊥
  T_norm : T ≤ Subgroup.normalizer (R : Set G)
  inf_eq : T ⊓ R = ⊥
  comm_T : IsCommSubgroup T
  ti : ∀ x ∈ R ⊔ T, T ⊓ rightConjugate T x ≠ ⊥ → rightConjugate T x = T

structure BData (R T W : Subgroup G) : Prop extends TIPair R T where
  hW : W = (R ⊔ T) ⊓ Subgroup.normalizer (T : Set G)
  normal : R ⊔ T ≤ Subgroup.normalizer (W : Set G)
  card_N : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) = Nat.card ↥T

namespace TIPair

variable {R T : Subgroup G} (P : TIPair R T)
include P

theorem exists_mul {x : G} (hx : x ∈ R ⊔ T) : ∃ r ∈ R, ∃ t ∈ T, x = r * t :=
  CFSG.RankThree.GF2n.exists_mul_of_mem_sup P.T_norm hx

theorem two_S : IsPGroup 2 (R ⊔ T : Subgroup G) :=
  P.two_R.to_sup_of_normal_left' P.two_T P.T_norm

theorem S_le_normalizer : R ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
  sup_le Subgroup.le_normalizer P.T_norm

theorem inf_normalizer_eq :
    R ⊓ Subgroup.normalizer (T : Set G) = R ⊓ Subgroup.centralizer (T : Set G) :=
  CFSG.ComponentClassification.Asc76.Sec5.inf_normalizer_eq_inf_centralizer P.T_norm
    (by rw [inf_comm]; exact P.inf_eq)

theorem N_comm {n t : G} (hn : n ∈ R ⊓ Subgroup.normalizer (T : Set G)) (ht : t ∈ T) :
    n * t = t * n := by
  rw [P.inf_normalizer_eq] at hn
  exact (Subgroup.mem_centralizer_iff.mp hn.2 t ht).symm

end TIPair

namespace BData

variable {R T W : Subgroup G} (B : BData R T W)
include B

theorem mem_W {x : G} : x ∈ W ↔ x ∈ R ⊔ T ∧ x ∈ Subgroup.normalizer (T : Set G) := by
  rw [B.hW, Subgroup.mem_inf]

theorem T_le_W : T ≤ W := fun _ ht =>
  B.mem_W.mpr ⟨Subgroup.mem_sup_right ht, Subgroup.le_normalizer ht⟩

theorem inf_R : W ⊓ R = R ⊓ Subgroup.normalizer (T : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, B.mem_W]
  constructor
  · rintro ⟨⟨_, hN⟩, hR⟩
    exact ⟨hR, hN⟩
  · rintro ⟨hR, hN⟩
    exact ⟨⟨Subgroup.mem_sup_left hR, hN⟩, hR⟩

theorem N_normal {s n : G} (hs : s ∈ R ⊔ T) (hn : n ∈ R ⊓ Subgroup.normalizer (T : Set G)) :
    s * n * s⁻¹ ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
  have hn' : n ∈ W ⊓ R := by rw [B.inf_R]; exact hn
  rw [← B.inf_R]
  exact ⟨(Subgroup.mem_normalizer_iff.mp (B.normal hs) n).mp hn'.1,
    (Subgroup.mem_normalizer_iff.mp (B.S_le_normalizer hs) n).mp hn'.2⟩

theorem S_le_normalizer_N :
    R ⊔ T ≤ Subgroup.normalizer ((R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => B.N_normal hs hn, fun hn => ?_⟩
  have := B.N_normal ((R ⊔ T).inv_mem hs) hn
  simpa [mul_assoc] using this

theorem not_mem_normalizer {y : G} (hy : y ∈ R ⊔ T) (hyW : y ∉ W) :
    y ∉ Subgroup.normalizer (T : Set G) := fun h => hyW (B.mem_W.mpr ⟨hy, h⟩)

theorem inf_rightConjugate_eq_bot {y : G} (hy : y ∈ R ⊔ T) (hyW : y ∉ W) :
    T ⊓ rightConjugate T y = ⊥ := by
  by_contra hne
  exact B.not_mem_normalizer hy hyW ((rightConjugate_eq_self_iff T y).mp (B.ti y hy hne))

theorem comm_mem_R' {y t : G} (hy : y ∈ R ⊔ T) (ht : t ∈ T) : t * y * t⁻¹ * y⁻¹ ∈ R := by
  obtain ⟨r, hr, t₀, ht₀, rfl⟩ := B.exists_mul hy
  have e : t₀ * t⁻¹ * t₀⁻¹ = t⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul, B.comm_T t₀ ht₀ t⁻¹ (T.inv_mem ht)]
  have h1 : t * (r * t₀) * t⁻¹ * (r * t₀)⁻¹ = (t * r * t⁻¹) * r⁻¹ := by
    calc t * (r * t₀) * t⁻¹ * (r * t₀)⁻¹ = t * r * (t₀ * t⁻¹ * t₀⁻¹) * r⁻¹ := by group
      _ = (t * r * t⁻¹) * r⁻¹ := by rw [e]
  rw [h1]
  exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp (B.T_norm ht) r).mp hr) (R.inv_mem hr)

theorem comm_mem_W {y t : G} (hy : y ∈ R ⊔ T) (ht : t ∈ T) : t * y * t⁻¹ * y⁻¹ ∈ W := by
  have h1 : y * t⁻¹ * y⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (B.normal hy) t⁻¹).mp (W.inv_mem (B.T_le_W ht))
  have : t * y * t⁻¹ * y⁻¹ = t * (y * t⁻¹ * y⁻¹) := by group
  rw [this]
  exact W.mul_mem (B.T_le_W ht) h1

theorem commutator_mem {y t : G} (hy : y ∈ R ⊔ T) (ht : t ∈ T) :
    t * y * t⁻¹ * y⁻¹ ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
  rw [← B.inf_R]
  exact ⟨B.comm_mem_W hy ht, B.comm_mem_R' hy ht⟩

theorem commutator_inj {y t₁ t₂ : G} (hy : y ∈ R ⊔ T) (hyW : y ∉ W) (h₁ : t₁ ∈ T)
    (h₂ : t₂ ∈ T) (h : t₁ * y * t₁⁻¹ * y⁻¹ = t₂ * y * t₂⁻¹ * y⁻¹) : t₁ = t₂ := by
  have h1 : t₁ * y * t₁⁻¹ = t₂ * y * t₂⁻¹ := mul_right_cancel h
  have hc : (t₂⁻¹ * t₁) * y * (t₂⁻¹ * t₁)⁻¹ = y := by
    calc (t₂⁻¹ * t₁) * y * (t₂⁻¹ * t₁)⁻¹ = t₂⁻¹ * (t₁ * y * t₁⁻¹) * t₂ := by group
      _ = t₂⁻¹ * (t₂ * y * t₂⁻¹) * t₂ := by rw [h1]
      _ = y := by group
  have hcy : (t₂⁻¹ * t₁) * y = y * (t₂⁻¹ * t₁) := mul_inv_eq_iff_eq_mul.mp hc
  have hmem : t₂⁻¹ * t₁ ∈ T ⊓ rightConjugate T y := by
    refine ⟨T.mul_mem (T.inv_mem h₂) h₁, (mem_rightConjugate_iff T y _).mpr ?_⟩
    have : y * (t₂⁻¹ * t₁) * y⁻¹ = t₂⁻¹ * t₁ := by rw [← hcy]; group
    rw [this]
    exact T.mul_mem (T.inv_mem h₂) h₁
  rw [B.inf_rightConjugate_eq_bot hy hyW, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem).symm

variable [Finite G]

theorem exists_commutator_eq {y n : G} (hy : y ∈ R ⊔ T) (hyW : y ∉ W)
    (hn : n ∈ R ⊓ Subgroup.normalizer (T : Set G)) : ∃ t ∈ T, t * y * t⁻¹ * y⁻¹ = n := by
  classical
  let f : ↥T → ↥(R ⊓ Subgroup.normalizer (T : Set G)) := fun t =>
    ⟨t * y * t⁻¹ * y⁻¹, B.commutator_mem hy t.2⟩
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (B.commutator_inj hy hyW a.2 b.2 (congrArg Subtype.val hab))
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [B.card_N])
  obtain ⟨t, ht⟩ := hbij.2 ⟨n, hn⟩
  exact ⟨t, t.2, congrArg Subtype.val ht⟩

theorem sq_mem {y : G} (hy : y ∈ R ⊔ T) : y ^ 2 ∈ W := by
  classical
  by_contra hy2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2S : y ^ 2 ∈ R ⊔ T := Subgroup.pow_mem _ hy 2
  let F : ↥(R ⊓ Subgroup.normalizer (T : Set G)) → ↥(R ⊓ Subgroup.normalizer (T : Set G)) :=
    fun h => ⟨h * (y * h * y⁻¹), Subgroup.mul_mem _ h.2 (B.N_normal hy h.2)⟩
  have hFsurj : Function.Surjective F := by
    intro n
    obtain ⟨t, ht, hn⟩ := B.exists_commutator_eq hy2S hy2 n.2
    refine ⟨⟨t * y * t⁻¹ * y⁻¹, B.commutator_mem hy ht⟩, Subtype.ext ?_⟩
    show (t * y * t⁻¹ * y⁻¹) * (y * (t * y * t⁻¹ * y⁻¹) * y⁻¹) = n
    rw [← hn, pow_two]
    group
  have hFinj : Function.Injective F := Finite.injective_iff_surjective.mpr hFsurj
  have hNne : (R ⊓ Subgroup.normalizer (T : Set G)) ≠ ⊥ := fun h =>
    B.T_ne (Subgroup.eq_bot_of_card_eq _ (by rw [← B.card_N, h, Subgroup.card_bot]))
  have hU : (R ⊓ Subgroup.normalizer (T : Set G)) ⊓
      ((R ⊔ T) ⊓ Subgroup.centralizer ((R ⊔ T : Subgroup G) : Set G)) ≠ ⊥ :=
    CFSG.ComponentClassification.Asc76X.inf_center_ne_bot' B.two_S
      (inf_le_left.trans le_sup_left) B.S_le_normalizer_N hNne
  have hU2 : IsPGroup 2 ↥((R ⊓ Subgroup.normalizer (T : Set G)) ⊓
      ((R ⊔ T) ⊓ Subgroup.centralizer ((R ⊔ T : Subgroup G) : Set G))) :=
    B.two_S.to_le (inf_le_right.trans inf_le_left)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hU (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
  have h2 : 2 ∣ Nat.card ↥((R ⊓ Subgroup.normalizer (T : Set G)) ⊓
      ((R ⊔ T) ⊓ Subgroup.centralizer ((R ⊔ T : Subgroup G) : Set G))) := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have huN : (u : G) ∈ R ⊓ Subgroup.normalizer (T : Set G) := u.2.1
  have huS : (u : G) ∈ (R ⊔ T) ⊓ Subgroup.centralizer ((R ⊔ T : Subgroup G) : Set G) := u.2.2
  have hord : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have hu2 : (u : G) * (u : G) = 1 := by
    rw [← pow_two, ← hord]
    exact pow_orderOf_eq_one _
  have hyu : y * (u : G) * y⁻¹ = (u : G) := by
    have := Subgroup.mem_centralizer_iff.mp huS.2 y hy
    rw [this]
    group
  have hFu : F ⟨u, huN⟩ = F 1 := by
    apply Subtype.ext
    show (u : G) * (y * (u : G) * y⁻¹) = 1 * (y * 1 * y⁻¹)
    rw [hyu, hu2]
    group
  have hu1 : (u : G) = 1 := congrArg Subtype.val (hFinj hFu)
  rw [hu1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem sq_mem_R {x : G} (hx : x ∈ R) : x * x ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
  have h2 := B.sq_mem (Subgroup.mem_sup_left hx)
  rw [← B.inf_R]
  exact ⟨by simpa [sq] using h2, R.mul_mem hx hx⟩

theorem comm_mem_R {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    x * y * x⁻¹ * y⁻¹ ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
  have h1 := B.sq_mem_R (R.mul_mem hx hy)
  have h2 := B.sq_mem_R hx
  have h3 := B.sq_mem_R hy
  have h4 := B.N_normal (Subgroup.mem_sup_left (R.inv_mem hy)) (Subgroup.inv_mem _ h2)
  have e : x * y * x⁻¹ * y⁻¹ =
      (x * y * (x * y)) * ((y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹) * (y * y)⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 (Subgroup.mul_mem _ h4 (Subgroup.inv_mem _ h3))

theorem inv_of_mem_R {y n : G} (hy : y ∈ R) (hyN : y ∉ R ⊓ Subgroup.normalizer (T : Set G))
    (hn : n ∈ R ⊓ Subgroup.normalizer (T : Set G)) : y * n * y⁻¹ = n⁻¹ := by
  have hyW : y ∉ W := fun h => hyN (by rw [← B.inf_R]; exact ⟨h, hy⟩)
  obtain ⟨t, ht, rfl⟩ := B.exists_commutator_eq (Subgroup.mem_sup_left hy) hyW hn
  have hm := B.N_comm (B.sq_mem_R hy) (T.inv_mem ht)
  have h2 : t⁻¹ * (y⁻¹ * y⁻¹) = (y⁻¹ * y⁻¹) * t⁻¹ := by
    calc t⁻¹ * (y⁻¹ * y⁻¹) = (y * y)⁻¹ * ((y * y) * t⁻¹) * (y * y)⁻¹ := by group
      _ = (y * y)⁻¹ * (t⁻¹ * (y * y)) * (y * y)⁻¹ := by rw [hm]
      _ = (y⁻¹ * y⁻¹) * t⁻¹ := by group
  calc y * (t * y * t⁻¹ * y⁻¹) * y⁻¹ = y * t * y * (t⁻¹ * (y⁻¹ * y⁻¹)) := by group
    _ = y * t * y * ((y⁻¹ * y⁻¹) * t⁻¹) := by rw [h2]
    _ = (t * y * t⁻¹ * y⁻¹)⁻¹ := by group

theorem nonempty_mulEquiv {y : G} (hy : y ∈ R ⊔ T) (hyW : y ∉ W) :
    Nonempty (↥T ≃* ↥(R ⊓ Subgroup.normalizer (T : Set G))) := by
  classical
  let f : ↥T → ↥(R ⊓ Subgroup.normalizer (T : Set G)) := fun t =>
    ⟨t * y * t⁻¹ * y⁻¹, B.commutator_mem hy t.2⟩
  have h1 : ∀ s t : G, s ∈ T → t ∈ T →
      (s * t) * y * (s * t)⁻¹ * y⁻¹ = (t * y * t⁻¹ * y⁻¹) * (s * y * s⁻¹ * y⁻¹) := by
    intro s t hs ht
    have hns := B.N_comm (B.commutator_mem hy ht) hs
    have hc : s * (t * y * t⁻¹ * y⁻¹) * s⁻¹ = t * y * t⁻¹ * y⁻¹ := by
      rw [← hns]
      group
    calc (s * t) * y * (s * t)⁻¹ * y⁻¹
        = s * (t * y * t⁻¹ * y⁻¹) * s⁻¹ * (s * y * s⁻¹ * y⁻¹) := by group
      _ = (t * y * t⁻¹ * y⁻¹) * (s * y * s⁻¹ * y⁻¹) := by rw [hc]
  have hmul : ∀ a b : ↥T, f (a * b) = f a * f b := by
    intro a b
    apply Subtype.ext
    have hab : (a : G) * b = b * a := B.comm_T a a.2 b b.2
    show ((a : G) * b) * y * ((a : G) * b)⁻¹ * y⁻¹ =
      ((a : G) * y * (a : G)⁻¹ * y⁻¹) * ((b : G) * y * (b : G)⁻¹ * y⁻¹)
    calc ((a : G) * b) * y * ((a : G) * b)⁻¹ * y⁻¹ = ((b : G) * a) * y * ((b : G) * a)⁻¹ * y⁻¹ := by
          rw [hab]
      _ = ((a : G) * y * (a : G)⁻¹ * y⁻¹) * ((b : G) * y * (b : G)⁻¹ * y⁻¹) := h1 b a b.2 a.2
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (B.commutator_inj hy hyW a.2 b.2 (congrArg Subtype.val hab))
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [B.card_N])
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' f hmul) hbij⟩


theorem mul_mem_N_of_not_mem
    (hex : ∃ n ∈ R ⊓ Subgroup.normalizer (T : Set G), n * n ≠ 1) {x y : G} (hx : x ∈ R)
    (hy : y ∈ R) (hxN : x ∉ R ⊓ Subgroup.normalizer (T : Set G))
    (hyN : y ∉ R ⊓ Subgroup.normalizer (T : Set G)) :
    x * y ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
  by_contra hxy
  obtain ⟨n, hn, hn2⟩ := hex
  apply hn2
  have h1 := B.inv_of_mem_R (R.mul_mem hx hy) hxy hn
  have h2 := B.inv_of_mem_R hy hyN hn
  have h3 := B.inv_of_mem_R hx hxN (Subgroup.inv_mem _ hn)
  have h4 : (x * y) * n * (x * y)⁻¹ = n := by
    calc (x * y) * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      _ = x * n⁻¹ * x⁻¹ := by rw [h2]
      _ = n := by rw [h3]; group
  rw [h4] at h1
  exact mul_eq_one_iff_eq_inv.mpr h1

theorem relIndex_eq_two (hex : ∃ n ∈ R ⊓ Subgroup.normalizer (T : Set G), n * n ≠ 1)
    (hR : ∃ y ∈ R, y ∉ R ⊓ Subgroup.normalizer (T : Set G)) :
    (R ⊓ Subgroup.normalizer (T : Set G)).relIndex R = 2 := by
  obtain ⟨x₀, hx₀, hx₀N⟩ := hR
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨x₀, hx₀⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hb : (b : G) ∈ R ⊓ Subgroup.normalizer (T : Set G)
  · right
    refine ⟨hb, fun h => hx₀N ?_⟩
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h
    simpa using this
  · left
    exact ⟨B.mul_mem_N_of_not_mem hex b.2 hx₀ hb hx₀N, hb⟩

theorem N_comm_of_exists (hR : ∃ y ∈ R, y ∉ R ⊓ Subgroup.normalizer (T : Set G)) {a b : G}
    (ha : a ∈ R ⊓ Subgroup.normalizer (T : Set G)) (hb : b ∈ R ⊓ Subgroup.normalizer (T : Set G)) :
    a * b = b * a := by
  obtain ⟨y, hy, hyN⟩ := hR
  have h1 := B.inv_of_mem_R hy hyN ha
  have h2 := B.inv_of_mem_R hy hyN hb
  have h3 := B.inv_of_mem_R hy hyN (Subgroup.mul_mem _ ha hb)
  have h4 : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
  rw [h3, h1, h2, mul_inv_rev] at h4
  have h5 := congrArg (fun z => z⁻¹) h4
  simpa using h5

theorem N_mul_self (hel : ∀ t ∈ T, t * t = 1) {y : G} (hy : y ∈ R ⊔ T) (hyW : y ∉ W) {n : G}
    (hn : n ∈ R ⊓ Subgroup.normalizer (T : Set G)) : n * n = 1 := by
  obtain ⟨e⟩ := B.nonempty_mulEquiv hy hyW
  obtain ⟨t, ht⟩ := e.surjective ⟨n, hn⟩
  have h1 : e (t * t) = 1 := by
    have : t * t = 1 := Subtype.ext (hel t t.2)
    rw [this, map_one]
  rw [map_mul, ht] at h1
  exact congrArg Subtype.val h1

theorem N_central (hel : ∀ t ∈ T, t * t = 1)
    (hR : ∃ y ∈ R, y ∉ R ⊓ Subgroup.normalizer (T : Set G)) {n r : G}
    (hn : n ∈ R ⊓ Subgroup.normalizer (T : Set G)) (hr : r ∈ R) : n * r = r * n := by
  obtain ⟨y₀, hy₀, hy₀N⟩ := hR
  have hy₀W : y₀ ∉ W := fun h => hy₀N (by rw [← B.inf_R]; exact ⟨h, hy₀⟩)
  have hel' : ∀ m ∈ R ⊓ Subgroup.normalizer (T : Set G), m * m = 1 := fun m hm =>
    B.N_mul_self hel (Subgroup.mem_sup_left hy₀) hy₀W hm
  by_cases hrN : r ∈ R ⊓ Subgroup.normalizer (T : Set G)
  · exact B.N_comm_of_exists ⟨y₀, hy₀, hy₀N⟩ hn hrN
  · have h1 := B.inv_of_mem_R hr hrN hn
    have h2 : n⁻¹ = n := (mul_eq_one_iff_eq_inv.mp (hel' n hn)).symm
    rw [h2] at h1
    calc n * r = (r * n * r⁻¹) * r := by rw [h1]
      _ = r * n := by group

theorem relIndex_le_card {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) :
    (R ⊓ Subgroup.normalizer (T : Set G)).relIndex R ≤
      Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) := by
  classical
  have hSR : ∀ y ∈ R, y ∈ R ⊔ T := fun y hy => Subgroup.mem_sup_left hy
  have key : ∀ y : G, y ∈ R → t₀ * y * t₀⁻¹ * y⁻¹ ∈ R ⊓ Subgroup.normalizer (T : Set G) :=
    fun y hy => B.commutator_mem (hSR y hy) ht₀
  let g : ↥R ⧸ (R ⊓ Subgroup.normalizer (T : Set G)).subgroupOf R →
      ↥(R ⊓ Subgroup.normalizer (T : Set G)) :=
    Quotient.lift (fun y : ↥R => (⟨t₀ * y * t₀⁻¹ * y⁻¹, key y y.2⟩ :
        ↥(R ⊓ Subgroup.normalizer (T : Set G)))) (by
      intro a b hab
      have hab' := QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_subgroupOf] at hab'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hab'
      apply Subtype.ext
      show t₀ * (a : G) * t₀⁻¹ * (a : G)⁻¹ = t₀ * (b : G) * t₀⁻¹ * (b : G)⁻¹
      have hnt : ((a : G)⁻¹ * b) * t₀ = t₀ * ((a : G)⁻¹ * b) := by
        have := B.N_comm hab' ht₀
        simpa using this
      have hb : (b : G) = (a : G) * ((a : G)⁻¹ * b) := by group
      calc t₀ * (a : G) * t₀⁻¹ * (a : G)⁻¹
          = t₀ * (a : G) * (((a : G)⁻¹ * b) * t₀⁻¹ * ((a : G)⁻¹ * b)⁻¹) * (a : G)⁻¹ := by
            have hc : ((a : G)⁻¹ * b) * t₀⁻¹ * ((a : G)⁻¹ * b)⁻¹ = t₀⁻¹ := by
              have h2 := B.N_comm hab' (T.inv_mem ht₀)
              rw [mul_inv_eq_iff_eq_mul]
              exact h2
            rw [hc]
        _ = t₀ * (b : G) * t₀⁻¹ * (b : G)⁻¹ := by rw [hb]; group)
  have hinj : Function.Injective g := by
    intro q₁ q₂ hq
    induction q₁ using Quotient.inductionOn with | _ a => ?_
    induction q₂ using Quotient.inductionOn with | _ b => ?_
    apply Quotient.sound
    refine QuotientGroup.leftRel_apply.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have h1 : t₀ * (a : G) * t₀⁻¹ * (a : G)⁻¹ = t₀ * (b : G) * t₀⁻¹ * (b : G)⁻¹ :=
      congrArg Subtype.val hq
    have h2 : (a : G) * t₀⁻¹ * (a : G)⁻¹ = (b : G) * t₀⁻¹ * (b : G)⁻¹ := by
      have := mul_left_cancel (a := t₀) (by simpa [mul_assoc] using h1)
      simpa [mul_assoc] using this
    set c : G := (a : G)⁻¹ * b with hcdef
    have h4 : t₀⁻¹ * c = c * t₀⁻¹ := by
      have e1 : t₀⁻¹ * c = (a : G)⁻¹ * ((a : G) * t₀⁻¹ * (a : G)⁻¹) * b := by
        rw [hcdef]; group
      have e2 : c * t₀⁻¹ = (a : G)⁻¹ * ((b : G) * t₀⁻¹ * (b : G)⁻¹) * b := by
        rw [hcdef]; group
      rw [e1, e2, h2]
    have hc : c * t₀ = t₀ * c := by
      calc c * t₀ = t₀ * (t₀⁻¹ * c) * t₀ := by group
        _ = t₀ * (c * t₀⁻¹) * t₀ := by rw [h4]
        _ = t₀ * c := by group
    have hcR : c ∈ R := R.mul_mem (R.inv_mem a.2) b.2
    have hcS : c ∈ R ⊔ T := Subgroup.mem_sup_left hcR
    have hmem : t₀ ∈ T ⊓ rightConjugate T c := by
      refine ⟨ht₀, (mem_rightConjugate_iff T c _).mpr ?_⟩
      have : c * t₀ * c⁻¹ = t₀ := by rw [hc]; group
      rw [this]
      exact ht₀
    have hne : T ⊓ rightConjugate T c ≠ ⊥ := by
      intro h
      rw [h, Subgroup.mem_bot] at hmem
      exact ht₀1 hmem
    exact ⟨hcR, (rightConjugate_eq_self_iff T c).mp (B.ti c hcS hne)⟩
  have hfin : Finite ↥(R ⊓ Subgroup.normalizer (T : Set G)) := inferInstance
  exact Nat.card_le_card_of_injective g hinj

end BData

end CFSG.CGT.PushingUpLit.SolKNA
