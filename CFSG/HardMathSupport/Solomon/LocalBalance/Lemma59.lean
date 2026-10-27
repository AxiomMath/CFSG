module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements2
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma58Main
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43One
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma59Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

@[expose] def InputONSylow : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsHatON X → ∀ P : Sylow 3 X,
    Nat.card (P : Subgroup X) = 3 ^ 5 ∧ (∀ g ∈ (P : Subgroup X), g ^ 3 = 1) ∧
      (∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), ⁅x, y⁆ ∈ Subgroup.center X) ∧
      (∀ z ∈ (P : Subgroup X), (∀ g ∈ (P : Subgroup X), g * z = z * g) → z ∈ Subgroup.center X)

@[expose] def InputONAut : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsHatON X → ∀ A : Subgroup (MulAut X),
    IsPGroup 3 A → Nat.card A ≤ 3 ^ 4

@[expose] def Input20_29 : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group) →
    ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      ∃ T : Subgroup K, T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set K)

@[expose] def InputONSimple : Prop :=
  IsSimpleGroup (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group ∧
    ∃ a b : (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group, a * b ≠ b * a

@[expose] def InputONTypes : Prop :=
  ∀ (K : Type) [Group K],
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group) →
    ¬ IsExtremalType K ∧ ¬ IsLThreeFour K

@[expose] def Input19_1_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → ∀ p : ℕ, p.Prime → ∀ B : Subgroup G, IsElemAbelian p B → ∀ k : ℕ, 1 ≤ k →
      ∀ D : Subgroup G, IsEkIn p k B D → ∀ b ∈ B, b ≠ 1 →
        ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
          IsCompLocallyBalanced p k B L →
            ⁅L, GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf p L

variable {G : Type} [Group G] [Finite G]

structure MidData (b : G) (R₀ R₁ B : Subgroup G) : Prop where
  elem : IsElemAbelian 3 B
  card_B : Nat.card B = 3 ^ 4
  b_mem : b ∈ B
  b_ne : b ≠ 1
  max : ∀ E : Subgroup G, IsElemAbelian 3 E → B ≤ E → E = B
  card_R0 : Nat.card R₀ = 3 ^ 5
  exp_R0 : ∀ g ∈ R₀, g ^ 3 = 1
  b_R0 : b ∈ R₀
  central_b : ∀ g ∈ R₀, g * b = b * g
  center_R0 : ∀ z ∈ R₀, (∀ g ∈ R₀, g * z = z * g) → z ∈ Subgroup.zpowers b
  comm_R0 : ∀ x ∈ R₀, ∀ y ∈ R₀, ⁅x, y⁆ ∈ Subgroup.zpowers b
  comm_R0R1 : ∀ x ∈ R₀, ∀ y ∈ R₁, x * y = y * x
  inf_R0R1 : ∀ x ∈ R₀, x ∈ R₁ → x ∈ Subgroup.zpowers b
  b_R1 : b ∈ R₁
  B_le : ∀ g ∈ B, ∃ r₀ ∈ R₀, ∃ r₁ ∈ R₁, g = r₀ * r₁
  card_B_R1 : Nat.card ↥(B ⊓ R₁) = 3

@[expose] def MidRank (B R₁ : Subgroup G) : Prop :=
  ∀ E : Subgroup G, IsElemAbelian 3 E → E ≤ B ⊔ R₁ → Nat.card E ≤ 3 ^ 4

theorem card_sup_mul_card_inf_of_normal {S : Type*} [Group S] [Finite S] (H N : Subgroup S)
    [N.Normal] :
    Nat.card ↥(H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card H * Nat.card N := by
  have h1 := Subgroup.relIndex_sup_right (H := H) (K := N)
  have e1 : Nat.card N * N.relIndex (H ⊔ N) = Nat.card ↥(H ⊔ N) := by
    have := Subgroup.card_mul_index (N.subgroupOf (H ⊔ N))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv] at this
  have e2 : Nat.card ↥(H ⊓ N) * N.relIndex H = Nat.card H := by
    have := Subgroup.card_mul_index (N.subgroupOf H)
    have hc : Nat.card ↥(N.subgroupOf H) = Nat.card ↥(H ⊓ N) := by
      rw [inf_comm, ← Subgroup.subgroupOf_map_subtype N H,
        Subgroup.card_map_of_injective H.subtype_injective]
    rwa [hc] at this
  rw [← e1, ← e2, h1]
  ring

theorem card_sup_mul_card_inf {G' : Type*} [Group G'] [Finite G'] {H K : Subgroup G'} (hHK : H ≤ Subgroup.normalizer (K : Set G')) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  set S : Subgroup G' := H ⊔ K with hS
  have hH : H ≤ S := le_sup_left
  have hK : K ≤ S := le_sup_right
  have hSn : S ≤ Subgroup.normalizer (K : Set G') :=
    sup_le hHK (Subgroup.le_normalizer)
  have : (K.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hK).2 hSn
  have h := card_sup_mul_card_inf_of_normal (H.subgroupOf S) (K.subgroupOf S)
  have e1 : H.subgroupOf S ⊔ K.subgroupOf S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hH hK, ← hS, Subgroup.subgroupOf_self]
  have e2 : H.subgroupOf S ⊓ K.subgroupOf S = (H ⊓ K).subgroupOf S := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [e1, e2, Subgroup.card_top] at h
  have c : ∀ X : Subgroup G', X ≤ S → Nat.card ↥(X.subgroupOf S) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  rw [c H hH, c K hK, c (H ⊓ K) (inf_le_left.trans hH)] at h
  exact h

section ClassTwo

variable {Q : Type*} [Group Q]

theorem conj_of_central {K : Subgroup Q} (hK : ∀ k ∈ K, ∀ g : Q, g * k = k * g) {k : Q}
    (hk : k ∈ K) (g : Q) : g * k * g⁻¹ = k := by
  rw [hK k hk g]; group

theorem comm_mul_left_of_central {K : Subgroup Q} (hK : ∀ k ∈ K, ∀ g : Q, g * k = k * g)
    (hc : ∀ x y : Q, ⁅x, y⁆ ∈ K) (x y z : Q) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have h1 : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
    simp only [commutatorElement_def]; group
  rw [h1, conj_of_central hK (hc y z) x]
  exact hK _ (hc x z) _

theorem comm_mul_right_of_central {K : Subgroup Q} (hK : ∀ k ∈ K, ∀ g : Q, g * k = k * g)
    (hc : ∀ x y : Q, ⁅x, y⁆ ∈ K) (x y z : Q) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have h1 : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [h1, conj_of_central hK (hc x z) y]

@[expose] def commHomL {K : Subgroup Q} (hK : ∀ k ∈ K, ∀ g : Q, g * k = k * g)
    (hc : ∀ x y : Q, ⁅x, y⁆ ∈ K) (x : Q) : Q →* K where
  toFun g := ⟨⁅g, x⁆, hc g x⟩
  map_one' := by ext; simp
  map_mul' g h := by
    ext
    simp only [Subgroup.coe_mul]
    exact comm_mul_left_of_central hK hc g h x

@[expose] def commHomR {K : Subgroup Q} (hK : ∀ k ∈ K, ∀ g : Q, g * k = k * g)
    (hc : ∀ x y : Q, ⁅x, y⁆ ∈ K) (g : Q) : Q →* K where
  toFun w := ⟨⁅g, w⁆, hc g w⟩
  map_one' := by ext; simp
  map_mul' u w := by
    ext
    simp only [Subgroup.coe_mul]
    exact comm_mul_right_of_central hK hc g u w

theorem commHomL_apply {K : Subgroup Q} (hK : ∀ k ∈ K, ∀ g : Q, g * k = k * g)
    (hc : ∀ x y : Q, ⁅x, y⁆ ∈ K) (x g : Q) : (commHomL hK hc x g : Q) = ⁅g, x⁆ := rfl

theorem commHomR_apply {K : Subgroup Q} (hK : ∀ k ∈ K, ∀ g : Q, g * k = k * g)
    (hc : ∀ x y : Q, ⁅x, y⁆ ∈ K) (g w : Q) : (commHomR hK hc g w : Q) = ⁅g, w⁆ := rfl

theorem central_le_normalizer {K : Subgroup Q} (hK : ∀ k ∈ K, ∀ g : Q, g * k = k * g) (g : Q) :
    g ∈ Subgroup.normalizer (K : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh; rw [conj_of_central hK hh g]; exact hh
  · intro hh
    have h2 := conj_of_central hK hh g⁻¹
    have h3 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [h3] at h2
    rw [h2]
    exact hh

theorem mem_normalizer_of_forall_commute {K' : Subgroup Q} {g : Q}
    (h : ∀ k ∈ K', g * k = k * g) : g ∈ Subgroup.normalizer (K' : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have : g * k * g⁻¹ = k := by rw [h k hk]; group
    rw [this]; exact hk
  · intro hk
    have h1 := h _ hk
    have h2 : k = g * k * g⁻¹ := by
      calc k = g⁻¹ * (g * k * g⁻¹) * g := by group
        _ = g⁻¹ * ((g * k * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * k * g⁻¹)) := by rw [← h1]
        _ = g * k * g⁻¹ := by group
    rw [h2]; exact hk

theorem card_inf_eq_one_of_card_three [Finite Q] {H K' : Subgroup Q} (hH : Nat.card H = 3)
    (hn : ¬ H ≤ K') : Nat.card ↥(H ⊓ K') = 1 := by
  have hd : Nat.card ↥(H ⊓ K') ∣ 3 := hH ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
  · exact h
  · exfalso
    apply hn
    have : H ⊓ K' = H := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hH])
    rw [← this]
    exact inf_le_right

theorem exists_central_of_card_eq_81 [Finite Q] {β : Q} (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (hcard : Nat.card Q = 81) (hexp : ∀ x : Q, x ^ 3 = 1)
    (hc : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.zpowers β) (hcen : ∀ g : Q, g * β = β * g) :
    ∃ y : Q, y ∉ Subgroup.zpowers β ∧ ∀ g : Q, g * y = y * g := by
  by_contra hno
  push Not at hno
  set K := Subgroup.zpowers β with hKdef
  have hK : ∀ k ∈ K, ∀ g : Q, g * k = k * g := by
    intro k hk g
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact ((Commute.zpow_right (hcen g) n)).eq
  have hKcard : Nat.card K = 3 := by
    rw [hKdef, Nat.card_zpowers, orderOf_eq_prime hβ hβ1]
  have hKQ : Nat.card ↥K = 3 := hKcard
  obtain ⟨x, hx⟩ : ∃ x : Q, x ∉ K := by
    by_contra h
    push Not at h
    have : K = ⊤ := eq_top_iff.2 fun x _ => h x
    rw [this, Subgroup.card_top, hcard] at hKcard
    omega
  have hx1 : x ≠ 1 := fun h => hx (h ▸ K.one_mem)
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hexp x) hx1]
  have hzx : ¬ Subgroup.zpowers x ≤ K := fun h => hx (h (Subgroup.mem_zpowers x))
  set A : Subgroup Q := Subgroup.zpowers x ⊔ K with hA
  have hAcard : Nat.card A = 9 := by
    have h := card_sup_mul_card_inf (H := Subgroup.zpowers x) (K := K)
      (fun g _ => central_le_normalizer hK g)
    rw [card_inf_eq_one_of_card_three hxcard hzx, hxcard, hKcard, ← hA] at h
    omega
  have hkerx : Nat.card (commHomL hK hc x).ker * Nat.card (commHomL hK hc x).range = 81 := by
    rw [Subgroup.card_ker_mul_card_range, hcard]
  have hrangex : Nat.card (commHomL hK hc x).range ≤ 3 :=
    (Subgroup.card_le_card_group _).trans hKQ.le
  have hrange_pos : 0 < Nat.card (commHomL hK hc x).range := Nat.card_pos
  have hCcard : 27 ≤ Nat.card (commHomL hK hc x).ker := by nlinarith
  obtain ⟨y, hyC, hyA⟩ : ∃ y ∈ (commHomL hK hc x).ker, y ∉ A := by
    by_contra h
    push Not at h
    have h1 : (commHomL hK hc x).ker ≤ A := h
    have h2 := Subgroup.card_le_of_le h1
    omega
  have hyx : ⁅y, x⁆ = 1 := by
    have h1 := (MonoidHom.mem_ker).1 hyC
    have h2 := congrArg Subtype.val h1
    simpa [commHomL_apply] using h2
  have hyx' : y * x = x * y := by
    exact commutatorElement_eq_one_iff_mul_comm.1 hyx
  have hy1 : y ≠ 1 := fun h => hyA (h ▸ A.one_mem)
  have hycard : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hexp y) hy1]
  have hzy : ¬ Subgroup.zpowers y ≤ A := fun h => hyA (h (Subgroup.mem_zpowers y))
  have hAy : A ≤ Subgroup.centralizer ({y} : Set Q) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hyx'.symm
    · intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hK k hk y).symm
  have hAn : A ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup Q) : Set Q) := by
    intro g hg
    have hgy : y * g = g * y := (Subgroup.mem_centralizer_singleton_iff.1 (hAy hg)).symm
    apply mem_normalizer_of_forall_commute
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((Commute.zpow_left (show Commute y g from hgy) n).eq).symm
  have hWcard : Nat.card ↥(A ⊔ Subgroup.zpowers y) = 27 := by
    have h := card_sup_mul_card_inf (H := A) (K := Subgroup.zpowers y) hAn
    rw [inf_comm, card_inf_eq_one_of_card_three hycard hzy, hAcard, hycard] at h
    omega
  have hWx : A ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({x} : Set Q) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    · intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hK k hk x).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hyx'
  have hWy : A ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({y} : Set Q) :=
    sup_le hAy (by rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff])
  let ψ : Q →* K × K := (commHomL hK hc x).prod (commHomL hK hc y)
  have hWker : A ⊔ Subgroup.zpowers y ≤ ψ.ker := by
    intro w hw
    rw [MonoidHom.mem_ker]
    have h1 : w * x = x * w := by
      have := Subgroup.mem_centralizer_singleton_iff.1 (hWx hw); exact this
    have h2 : w * y = y * w := by
      have := Subgroup.mem_centralizer_singleton_iff.1 (hWy hw); exact this
    ext
    · simp [ψ, commHomL_apply, commutatorElement_eq_one_iff_mul_comm.2 h1]
    · simp [ψ, commHomL_apply, commutatorElement_eq_one_iff_mul_comm.2 h2]
  have hkerψ : Nat.card ψ.ker * Nat.card ψ.range = 81 := by
    rw [Subgroup.card_ker_mul_card_range, hcard]
  have hker27 : 27 ≤ Nat.card ψ.ker := by
    have := Subgroup.card_le_of_le hWker
    omega
  have hrangeψ : Nat.card ψ.range ≤ 3 := by
    have : 0 < Nat.card ψ.range := Nat.card_pos
    nlinarith
  obtain ⟨v, hv⟩ := hno x hx
  have hβ1' : commHomL hK hc x v ≠ 1 := by
    intro h
    apply hv
    have := congrArg Subtype.val h
    exact commutatorElement_eq_one_iff_mul_comm.1 (by simpa [commHomL_apply] using this)
  have hKexp : ∀ z : K, z ^ 3 = 1 := fun z => Subtype.ext (by simpa using hexp (z : Q))
  have hψv1 : ψ v ≠ 1 := by
    intro h
    exact hβ1' (by simpa [ψ] using congrArg Prod.fst h)
  have hψv3 : (ψ v) ^ 3 = 1 := by
    rw [← map_pow, hexp v, map_one]
  have hψvcard : Nat.card (Subgroup.zpowers (ψ v)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hψv3 hψv1]
  have hψeq : Subgroup.zpowers (ψ v) = ψ.range := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (by omega)
    rw [Subgroup.zpowers_le]
    exact ⟨v, rfl⟩
  have hβ1card : Nat.card (Subgroup.zpowers (commHomL hK hc x v)) = Nat.card K := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hKexp _) hβ1', hKQ]
  have hKtop : Subgroup.zpowers (commHomL hK hc x v) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ hβ1card
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (commHomL hK hc x v) ^ k = commHomL hK hc y v := by
    have : commHomL hK hc y v ∈ Subgroup.zpowers (commHomL hK hc x v) := by
      rw [hKtop]; trivial
    exact Subgroup.mem_zpowers_iff.1 this
  have hz : ∀ g : Q, g * (y * x ^ (-k)) = (y * x ^ (-k)) * g := by
    intro g
    have hg : ψ g ∈ Subgroup.zpowers (ψ v) := by rw [hψeq]; exact ⟨g, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hn1 : (commHomL hK hc x v) ^ n = commHomL hK hc x g := by
      have := congrArg Prod.fst hn
      simpa [ψ] using this
    have hn2 : (commHomL hK hc y v) ^ n = commHomL hK hc y g := by
      have := congrArg Prod.snd hn
      simpa [ψ] using this
    have key : commHomR hK hc g (y * x ^ (-k)) = 1 := by
      rw [map_mul, map_zpow]
      have e1 : commHomR hK hc g y = commHomL hK hc y g := rfl
      have e2 : commHomR hK hc g x = commHomL hK hc x g := rfl
      rw [e1, e2, ← hn1, ← hn2, ← hk, ← zpow_mul, ← zpow_mul, ← zpow_add]
      have : k * n + n * (-k) = 0 := by ring
      rw [this, zpow_zero]
    have := congrArg Subtype.val key
    have h3 : ⁅g, y * x ^ (-k)⁆ = 1 := by rw [← commHomR_apply hK hc]; exact this
    exact (commutatorElement_eq_one_iff_mul_comm.1 h3)
  have hzK : y * x ^ (-k) ∈ K := by
    by_contra hnot
    obtain ⟨g, hg⟩ := hno _ hnot
    exact hg (hz g)
  apply hyA
  have : y = (y * x ^ (-k)) * x ^ k := by group
  rw [this]
  exact A.mul_mem ((show K ≤ A from le_sup_right) hzK)
    ((show Subgroup.zpowers x ≤ A from le_sup_left) (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k))



theorem no_abelian_index_three [Finite Q] {β : Q} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (hcard : Nat.card Q = 243)
    (hc : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.zpowers β) (hcen : ∀ g : Q, g * β = β * g)
    (hZ : ∀ z : Q, (∀ g : Q, g * z = z * g) → z ∈ Subgroup.zpowers β)
    (B' : Subgroup Q) (hB'c : ∀ a ∈ B', ∀ a' ∈ B', a * a' = a' * a) (hB'card : Nat.card B' = 81) :
    False := by
  set K := Subgroup.zpowers β with hKdef
  have hK : ∀ k ∈ K, ∀ g : Q, g * k = k * g := by
    intro k hk g
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact ((Commute.zpow_right (hcen g) n)).eq
  have hKcard : Nat.card K = 3 := by
    rw [hKdef, Nat.card_zpowers, orderOf_eq_prime hβ3 hβ1]
  obtain ⟨x, hx⟩ : ∃ x : Q, x ∉ B' := by
    by_contra hh
    push Not at hh
    have : B' = ⊤ := eq_top_iff.2 fun x _ => hh x
    rw [this, Subgroup.card_top, hcard] at hB'card
    omega
  have hdvd1 : Nat.card B' ∣ Nat.card ↥(B' ⊔ Subgroup.zpowers x) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hdvd2 : Nat.card ↥(B' ⊔ Subgroup.zpowers x) ∣ 243 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  have hne : B' ≠ B' ⊔ Subgroup.zpowers x := fun hh =>
    hx (hh ▸ (show Subgroup.zpowers x ≤ B' ⊔ Subgroup.zpowers x from le_sup_right)
      (Subgroup.mem_zpowers x))
  have hcardE : Nat.card ↥(B' ⊔ Subgroup.zpowers x) = 243 := by
    have hle : Nat.card B' ≤ Nat.card ↥(B' ⊔ Subgroup.zpowers x) :=
      Subgroup.card_le_of_le le_sup_left
    have hne' : Nat.card ↥(B' ⊔ Subgroup.zpowers x) ≠ 81 := by
      intro h81
      exact hne (Subgroup.eq_of_le_of_card_ge le_sup_left (by omega))
    have hmem : Nat.card ↥(B' ⊔ Subgroup.zpowers x) ∈ Nat.divisors 243 :=
      Nat.mem_divisors.2 ⟨hdvd2, by norm_num⟩
    have : Nat.divisors 243 = {1, 3, 9, 27, 81, 243} := by decide
    rw [this] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h <;> omega
  have hEtop : B' ⊔ Subgroup.zpowers x = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hcardE, hcard])
  let g : B' →* K := (commHomL hK hc x).comp B'.subtype
  have hker : Nat.card g.ker * Nat.card g.range = 81 := by
    rw [Subgroup.card_ker_mul_card_range, hB'card]
  have hrange : Nat.card g.range ≤ 3 := (Subgroup.card_le_card_group _).trans hKcard.le
  have hpos : 0 < Nat.card g.range := Nat.card_pos
  have hker27 : 27 ≤ Nat.card g.ker := by nlinarith
  have hkerK : g.ker.map B'.subtype ≤ K := by
    intro z hz
    obtain ⟨⟨z, hzB⟩, hzk, rfl⟩ := hz
    apply hZ
    intro q
    have h1 : z * x = x * z := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hzk)
      exact commutatorElement_eq_one_iff_mul_comm.1 (by simpa [g, commHomL_apply] using this)
    have hq : q ∈ B' ⊔ Subgroup.zpowers x := by rw [hEtop]; trivial
    have hle : B' ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({z} : Set Q) := by
      refine sup_le ?_ ?_
      · intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hB'c a ha z hzB
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact h1.symm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hq)
    exact this
  have := Subgroup.card_le_of_le hkerK
  rw [Subgroup.card_map_of_injective B'.subtype_injective] at this
  omega

end ClassTwo

theorem exists_mul_zpow_of_mem_sup {A : Subgroup G} {x : G} (hc : ∀ a ∈ A, a * x = x * a)
    {z : G} (hz : z ∈ A ⊔ Subgroup.zpowers x) : ∃ a ∈ A, ∃ n : ℤ, z = a * x ^ n := by
  have hcomm : ∀ (m : A) (n : Subgroup.zpowers x),
      Commute (A.subtype m) ((Subgroup.zpowers x).subtype n) := by
    intro m n
    obtain ⟨k, hk⟩ := n.2
    show (m : G) * (n : G) = (n : G) * m
    rw [← hk]
    exact ((Commute.zpow_right (hc m m.2 : (m : G) * x = x * m) k)).eq
  have hrange : (MonoidHom.noncommCoprod A.subtype (Subgroup.zpowers x).subtype hcomm).range =
      A ⊔ Subgroup.zpowers x := by
    rw [MonoidHom.noncommCoprod_range]
    simp
  rw [← hrange] at hz
  obtain ⟨⟨m, n⟩, rfl⟩ := hz
  obtain ⟨k, hk⟩ := n.2
  exact ⟨m, m.2, k, by simp [hk]⟩

theorem isElemAbelian_sup_of_commute {A A' : Subgroup G} (hA : IsElemAbelian 3 A)
    (hA' : IsElemAbelian 3 A') (hc : ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a) :
    IsElemAbelian 3 (A ⊔ A') := by
  have hmem : ∀ z ∈ A ⊔ A', ∃ a ∈ A, ∃ a' ∈ A', z = a * a' := fun z hz =>
    exists_mul_of_mem_sup_of_commute hc hz
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAc' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA'.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨⟨⟨fun ⟨u, hu⟩ ⟨v, hv⟩ => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨a, ha, a', ha', rfl⟩ := hmem u hu
    obtain ⟨c, hc1, c', hc', rfl⟩ := hmem v hv
    apply Subtype.ext
    show a * a' * (c * c') = c * c' * (a * a')
    have h1 : a' * c = c * a' := (hc c hc1 a' ha').symm
    calc a * a' * (c * c') = a * (a' * c) * c' := by group
      _ = a * (c * a') * c' := by rw [h1]
      _ = (a * c) * (a' * c') := by group
      _ = (c * a) * (c' * a') := by rw [hAc a ha c hc1, hAc' a' ha' c' hc']
      _ = c * (a * c') * a' := by group
      _ = c * (c' * a) * a' := by rw [hc a ha c' hc']
      _ = c * c' * (a * a') := by group
  · obtain ⟨a, ha, a', ha', rfl⟩ := hmem z hz
    have hcom : Commute a a' := hc a ha a' ha'
    rw [hcom.mul_pow, hA.2 a ha, hA'.2 a' ha', one_mul]

@[expose] def commHomSub (H K : Subgroup G) (hK : ∀ k ∈ K, ∀ g ∈ H, g * k = k * g)
    (hKc : ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k) (x : G) (hc : ∀ g ∈ H, ⁅g, x⁆ ∈ K) : H →* K where
  toFun g := ⟨⁅(g : G), x⁆, hc g g.2⟩
  map_one' := by ext; simp
  map_mul' g g' := by
    ext
    simp only [Subgroup.coe_mul]
    have h1 : ⁅(g : G) * g', x⁆ = g * ⁅(g' : G), x⁆ * (g : G)⁻¹ * ⁅(g : G), x⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    have h2 : (g : G) * ⁅(g' : G), x⁆ * (g : G)⁻¹ = ⁅(g' : G), x⁆ := by
      rw [hK _ (hc g' g'.2) g g.2]; group
    rw [h2]
    exact hKc _ (hc g' g'.2) _ (hc g g.2)

theorem commHomSub_apply (H K : Subgroup G) (hK : ∀ k ∈ K, ∀ g ∈ H, g * k = k * g)
    (hKc : ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k) (x : G) (hc : ∀ g ∈ H, ⁅g, x⁆ ∈ K) (g : H) :
    ((commHomSub H K hK hKc x hc g : K) : G) = ⁅(g : G), x⁆ := rfl

namespace MidData

variable {b : G} {R₀ R₁ B : Subgroup G} (h : MidData b R₀ R₁ B)
include h

theorem b_cube : b ^ 3 = 1 := h.elem.2 b h.b_mem

theorem orderOf_b : orderOf b = 3 := orderOf_eq_prime h.b_cube h.b_ne

theorem card_zpowers_b : Nat.card (Subgroup.zpowers b) = 3 := by
  rw [Nat.card_zpowers, h.orderOf_b]

theorem R1_comm_b (y : G) (hy : y ∈ R₁) : y * b = b * y := (h.comm_R0R1 b h.b_R0 y hy).symm

theorem B_comm (g g' : G) (hg : g ∈ B) (hg' : g' ∈ B) : g * g' = g' * g :=
  congrArg Subtype.val (h.elem.1.is_comm.comm ⟨g, hg⟩ ⟨g', hg'⟩)

theorem conj_R1 {g : G} (hg : g ∈ B) {r : G} (hr : r ∈ R₁) : g * r * g⁻¹ ∈ R₁ := by
  obtain ⟨r₀, hr₀, r₁, hr₁, rfl⟩ := h.B_le g hg
  have h1 : r₀ * (r₁ * r * r₁⁻¹) = (r₁ * r * r₁⁻¹) * r₀ :=
    h.comm_R0R1 r₀ hr₀ _ (R₁.mul_mem (R₁.mul_mem hr₁ hr) (R₁.inv_mem hr₁))
  have h2 : r₀ * r₁ * r * (r₀ * r₁)⁻¹ = r₁ * r * r₁⁻¹ := by
    calc r₀ * r₁ * r * (r₀ * r₁)⁻¹ = r₀ * (r₁ * r * r₁⁻¹) * r₀⁻¹ := by group
      _ = (r₁ * r * r₁⁻¹) * r₀ * r₀⁻¹ := by rw [h1]
      _ = r₁ * r * r₁⁻¹ := by group
  rw [h2]
  exact R₁.mul_mem (R₁.mul_mem hr₁ hr) (R₁.inv_mem hr₁)

theorem B_le_normalizer : B ≤ Subgroup.normalizer (R₁ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h.conj_R1 hg hx, fun hx => ?_⟩
  have := h.conj_R1 (B.inv_mem hg) hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rw [e] at this
  exact this

theorem coe_sup : ((B ⊔ R₁ : Subgroup G) : Set G) = (B : Set G) * (R₁ : Set G) :=
  Subgroup.coe_mul_of_left_le_normalizer_right B R₁ h.B_le_normalizer

theorem mem_sup {a : G} : a ∈ B ⊔ R₁ ↔ ∃ g ∈ B, ∃ r ∈ R₁, a = g * r := by
  have : a ∈ ((B ⊔ R₁ : Subgroup G) : Set G) ↔ a ∈ (B : Set G) * (R₁ : Set G) := by rw [h.coe_sup]
  rw [SetLike.mem_coe, Set.mem_mul] at this
  rw [this]
  constructor
  · rintro ⟨g, hg, r, hr, rfl⟩; exact ⟨g, hg, r, hr, rfl⟩
  · rintro ⟨g, hg, r, hr, rfl⟩; exact ⟨g, hg, r, hr, rfl⟩

theorem r0_mem {g r₀ r₁ : G} (hg : g ∈ B) (hr₀ : r₀ ∈ R₀) (hr₁ : r₁ ∈ R₁) (e : g = r₀ * r₁) :
    r₀ ∈ R₀ ⊓ (B ⊔ R₁) := by
  refine ⟨hr₀, ?_⟩
  have : r₀ = g * r₁⁻¹ := by rw [e]; group
  rw [this]
  exact (B ⊔ R₁).mul_mem (Subgroup.mem_sup_left hg) ((B ⊔ R₁).inv_mem (Subgroup.mem_sup_right hr₁))

theorem b_mem_B0 : b ∈ R₀ ⊓ (B ⊔ R₁) := ⟨h.b_R0, Subgroup.mem_sup_left h.b_mem⟩

theorem B0_sup : (R₀ ⊓ (B ⊔ R₁)) ⊔ R₁ = B ⊔ R₁ := by
  apply le_antisymm
  · exact sup_le inf_le_right le_sup_right
  · refine sup_le ?_ le_sup_right
    intro g hg
    obtain ⟨r₀, hr₀, r₁, hr₁, e⟩ := h.B_le g hg
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (h.r0_mem hg hr₀ hr₁ e))
      (Subgroup.mem_sup_right hr₁)

theorem B0_inf : (R₀ ⊓ (B ⊔ R₁)) ⊓ R₁ = Subgroup.zpowers b := by
  apply le_antisymm
  · intro x hx
    exact h.inf_R0R1 x hx.1.1 hx.2
  · exact le_inf ((Subgroup.zpowers_le).2 h.b_mem_B0) ((Subgroup.zpowers_le).2 h.b_R1)

theorem card_B0 : Nat.card ↥(R₀ ⊓ (B ⊔ R₁)) = 3 ^ 4 := by
  have hB₀N : (R₀ ⊓ (B ⊔ R₁)) ≤ Subgroup.normalizer (R₁ : Set G) := fun x hx =>
    mem_normalizer_of_forall_commute fun k hk => h.comm_R0R1 x hx.1 k hk
  have e1 := card_sup_mul_card_inf h.B_le_normalizer
  have e2 := card_sup_mul_card_inf hB₀N
  rw [h.B0_sup, h.B0_inf, h.card_zpowers_b] at e2
  rw [h.card_B_R1, h.card_B] at e1
  have hpos : 0 < Nat.card R₁ := Nat.card_pos
  have : Nat.card ↥(R₀ ⊓ (B ⊔ R₁)) * Nat.card R₁ = 3 ^ 4 * Nat.card R₁ := by omega
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem exists_not_le_R0 : ∃ g ∈ B, g ∉ R₀ := by
  by_contra hno
  push Not at hno
  let β : R₀ := ⟨b, h.b_R0⟩
  have hzp : ∀ z : R₀, z ∈ Subgroup.zpowers β ↔ (z : G) ∈ Subgroup.zpowers b := by
    intro z
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨n, by simp [β]⟩
    · rintro ⟨n, hn⟩; exact ⟨n, Subtype.ext (by simpa [β] using hn)⟩
  have hβ3 : β ^ 3 = 1 := Subtype.ext (by simpa [β] using h.b_cube)
  have hβ1 : β ≠ 1 := fun e => h.b_ne (by simpa [β] using congrArg Subtype.val e)
  have hBR₀ : B ≤ R₀ := hno
  refine no_abelian_index_three (Q := R₀) (β := β) hβ3 hβ1 ?_ (fun x y => (hzp _).2 (h.comm_R0 x x.2 y y.2))
    (fun g => Subtype.ext (h.central_b g g.2))
    (fun z hz => (hzp z).2 (h.center_R0 z z.2 fun g hg => congrArg Subtype.val (hz ⟨g, hg⟩)))
    (B.subgroupOf R₀) ?_ ?_
  · rw [h.card_R0]; norm_num
  · intro a ha a' ha'
    exact Subtype.ext (h.B_comm a a' ha ha')
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBR₀).toEquiv, h.card_B]; norm_num

theorem comm_r1 {g g' r₀ r₁ : G} (hg : g ∈ B) (hg' : g' ∈ B) (hr₀ : r₀ ∈ R₀) (_hr₁ : r₁ ∈ R₁)
    (e : g = r₀ * r₁) : ⁅g', r₁⁆ ∈ Subgroup.zpowers b := by
  obtain ⟨r₀', hr₀', r₁', hr₁', e'⟩ := h.B_le g' hg'
  have hcomm : g * g' = g' * g := h.B_comm g g' hg hg'
  have h1 : g * g'⁻¹ = g'⁻¹ * g := by
    have : Commute g g' := hcomm
    exact (this.inv_right).eq
  have hr1 : r₁ = r₀⁻¹ * g := by rw [e]; group
  have h2 : ⁅g', r₁⁆ = g' * r₀⁻¹ * g'⁻¹ * r₀ := by
    rw [hr1]
    simp only [commutatorElement_def, mul_inv_rev, inv_inv]
    calc g' * (r₀⁻¹ * g) * g'⁻¹ * (g⁻¹ * r₀) = g' * r₀⁻¹ * (g * g'⁻¹) * g⁻¹ * r₀ := by group
      _ = g' * r₀⁻¹ * (g'⁻¹ * g) * g⁻¹ * r₀ := by rw [h1]
      _ = g' * r₀⁻¹ * g'⁻¹ * r₀ := by group
  have h3 : r₁' * r₀⁻¹ = r₀⁻¹ * r₁' := (h.comm_R0R1 _ (R₀.inv_mem hr₀) r₁' hr₁').symm
  have h4 : g' * r₀⁻¹ * g'⁻¹ * r₀ = ⁅r₀', r₀⁻¹⁆ := by
    rw [e', commutatorElement_def]
    calc r₀' * r₁' * r₀⁻¹ * (r₀' * r₁')⁻¹ * r₀ = r₀' * (r₁' * r₀⁻¹) * r₁'⁻¹ * r₀'⁻¹ * r₀ := by group
      _ = r₀' * (r₀⁻¹ * r₁') * r₁'⁻¹ * r₀'⁻¹ * r₀ := by rw [h3]
      _ = r₀' * r₀⁻¹ * r₀'⁻¹ * r₀ := by group
      _ = r₀' * r₀⁻¹ * r₀'⁻¹ * r₀⁻¹⁻¹ := by group
  rw [h2, h4]
  exact h.comm_R0 _ hr₀' _ (R₀.inv_mem hr₀)

end MidData

theorem mid_exists_U {b : G} {R₀ R₁ B : Subgroup G} (h : MidData b R₀ R₁ B) :
    ∃ U : Subgroup G, U ≤ R₁ ∧ IsElemAbelian 3 U ∧ Nat.card U = 9 ∧ b ∈ U ∧
      ∀ g ∈ B, ∀ u ∈ U, ⁅g, u⁆ ∈ Subgroup.zpowers b := by
  obtain ⟨g, hg, hgR₀⟩ := h.exists_not_le_R0
  obtain ⟨r₀, hr₀, r₁, hr₁, e⟩ := h.B_le g hg
  have hv : r₁ ∉ Subgroup.zpowers b := by
    intro hh
    apply hgR₀
    rw [e]
    exact R₀.mul_mem hr₀ ((Subgroup.zpowers_le).2 h.b_R0 hh)
  have hv1 : r₁ ≠ 1 := fun e1 => hv (e1 ▸ Subgroup.one_mem _)
  have hv3 : r₁ ^ 3 = 1 := by
    have hc : Commute r₀ r₁ := h.comm_R0R1 r₀ hr₀ r₁ hr₁
    have h1 : g ^ 3 = 1 := h.elem.2 g hg
    rw [e, hc.mul_pow, h.exp_R0 r₀ hr₀, one_mul] at h1
    exact h1
  have hbc : ∀ a ∈ Subgroup.zpowers b, a * r₁ = r₁ * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (show Commute b r₁ from (h.R1_comm_b r₁ hr₁).symm) n).eq
  have hvcard : Nat.card (Subgroup.zpowers r₁) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hv3 hv1]
  have hnle : ¬ Subgroup.zpowers r₁ ≤ Subgroup.zpowers b := fun hh => hv (hh (Subgroup.mem_zpowers _))
  refine ⟨Subgroup.zpowers b ⊔ Subgroup.zpowers r₁, ?_, ?_, ?_, Subgroup.mem_sup_left (Subgroup.mem_zpowers b), ?_⟩
  · exact sup_le ((Subgroup.zpowers_le).2 h.b_R1) ((Subgroup.zpowers_le).2 hr₁)
  · exact isElemAbelian_sup_zpowers (isElemAbelian_mono h.elem ((Subgroup.zpowers_le).2 h.b_mem))
      hv3 hbc
  · have hn : Subgroup.zpowers b ≤ Subgroup.normalizer ((Subgroup.zpowers r₁ : Subgroup G) : Set G) := by
      intro a ha
      apply mem_normalizer_of_forall_commute
      intro k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact (Commute.zpow_right (show Commute a r₁ from hbc a ha) n).eq
    have hh := card_sup_mul_card_inf hn
    rw [inf_comm, card_inf_eq_one_of_card_three hvcard hnle, h.card_zpowers_b, hvcard] at hh
    omega
  · intro g' hg' u hu
    obtain ⟨a, ha, n, rfl⟩ := exists_mul_zpow_of_mem_sup hbc hu
    set c := ⁅g', r₁⁆ with hcdef
    have hc1 : c ∈ Subgroup.zpowers b := h.comm_r1 hg hg' hr₀ hr₁ e
    have ha' : g' * a = a * g' :=
      h.B_comm g' a hg' ((Subgroup.zpowers_le).2 h.b_mem ha)
    have hcr : Commute c r₁ := hbc c hc1
    have hconj : g' * r₁ * g'⁻¹ = c * r₁ := by
      rw [hcdef, commutatorElement_def]; group
    have hconjn : g' * r₁ ^ n * g'⁻¹ = c ^ n * r₁ ^ n := by
      rw [← conj_zpow, hconj, hcr.mul_zpow]
    have hac : Commute a (c ^ n) := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hc1
      rw [← hj, ← zpow_mul]
      exact Commute.zpow_zpow_self b i (j * n)
    have : ⁅g', a * r₁ ^ n⁆ = c ^ n := by
      calc ⁅g', a * r₁ ^ n⁆ = (g' * a * g'⁻¹) * (g' * r₁ ^ n * g'⁻¹) * (r₁ ^ n)⁻¹ * a⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = a * (c ^ n * r₁ ^ n) * (r₁ ^ n)⁻¹ * a⁻¹ := by
            rw [hconjn, show g' * a * g'⁻¹ = a by rw [ha']; group]
        _ = a * c ^ n * a⁻¹ := by group
        _ = c ^ n := by rw [hac.eq]; group
    rw [this]
    exact Subgroup.zpow_mem _ hc1 n


theorem mid_B0 {b : G} {R₀ R₁ B : Subgroup G} (h : MidData b R₀ R₁ B) :
    Nat.card ↥(R₀ ⊓ (B ⊔ R₁)) = 3 ^ 4 ∧
    (∀ a ∈ B ⊔ R₁, ∃ x ∈ R₀ ⊓ (B ⊔ R₁), x⁻¹ * a ∈ R₁) ∧
    (∀ x ∈ R₀ ⊓ (B ⊔ R₁), ∀ y ∈ R₀ ⊓ (B ⊔ R₁), ⁅x, y⁆ ∈ Subgroup.zpowers b) ∧
    (∀ x ∈ R₀ ⊓ (B ⊔ R₁), x ^ 3 = 1) ∧ b ∈ R₀ ⊓ (B ⊔ R₁) := by
  refine ⟨h.card_B0, ?_, ?_, ?_, h.b_mem_B0⟩
  · intro a ha
    obtain ⟨g, hg, r, hr, rfl⟩ := (h.mem_sup).1 ha
    obtain ⟨r₀, hr₀, r₁, hr₁, e⟩ := h.B_le g hg
    refine ⟨r₀, h.r0_mem hg hr₀ hr₁ e, ?_⟩
    rw [e]
    have : r₀⁻¹ * (r₀ * r₁ * r) = r₁ * r := by group
    rw [this]; exact R₁.mul_mem hr₁ hr
  · intro x hx y hy; exact h.comm_R0 x hx.1 y hy.1
  · intro x hx; exact h.exp_R0 x hx.1

theorem mid_exists_y {b : G} {R₀ R₁ B : Subgroup G} (h : MidData b R₀ R₁ B) :
    ∃ y ∈ B ⊓ R₀, y ∉ Subgroup.zpowers b := by
  obtain ⟨hcard, -, hcomm, hexp, hbB0⟩ := mid_B0 h
  set B₀ := R₀ ⊓ (B ⊔ R₁) with hB₀
  let β : B₀ := ⟨b, hbB0⟩
  have hzp : ∀ z : B₀, z ∈ Subgroup.zpowers β ↔ (z : G) ∈ Subgroup.zpowers b := by
    intro z
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨n, by simp [β]⟩
    · rintro ⟨n, hn⟩; exact ⟨n, Subtype.ext (by simpa [β] using hn)⟩
  have hβ3 : β ^ 3 = 1 := Subtype.ext (by simpa [β] using h.b_cube)
  have hβ1 : β ≠ 1 := fun e => h.b_ne (by simpa [β] using congrArg Subtype.val e)
  have hcard' : Nat.card B₀ = 81 := by rw [hcard]; norm_num
  obtain ⟨y', hy'1, hy'c⟩ := exists_central_of_card_eq_81 (Q := B₀) hβ3 hβ1 hcard'
    (fun x => Subtype.ext (hexp x x.2))
    (fun x y => (hzp _).2 (hcomm x x.2 y y.2))
    (fun g => Subtype.ext (h.central_b g (g.2.1)))
  have hyR₀ : (y' : G) ∈ R₀ := y'.2.1
  have hyb : (y' : G) ∉ Subgroup.zpowers b := fun hh => hy'1 ((hzp y').2 hh)
  have hy3 : (y' : G) ^ 3 = 1 := hexp y' y'.2
  have hcB : ∀ g ∈ B, g * (y' : G) = (y' : G) * g := by
    intro g hg
    obtain ⟨r₀, hr₀, r₁, hr₁, e⟩ := h.B_le g hg
    have h1 : r₀ * (y' : G) = (y' : G) * r₀ :=
      congrArg Subtype.val (hy'c ⟨r₀, h.r0_mem hg hr₀ hr₁ e⟩)
    have h2 : r₁ * (y' : G) = (y' : G) * r₁ := (h.comm_R0R1 _ hyR₀ r₁ hr₁).symm
    rw [e]
    calc r₀ * r₁ * (y' : G) = r₀ * ((y' : G) * r₁) := by rw [mul_assoc, h2]
      _ = (r₀ * (y' : G)) * r₁ := by rw [mul_assoc]
      _ = (y' : G) * (r₀ * r₁) := by rw [h1]; group
  have hE := isElemAbelian_sup_zpowers h.elem hy3 hcB
  have hEB : B ⊔ Subgroup.zpowers (y' : G) = B := h.max _ hE le_sup_left
  refine ⟨(y' : G), ⟨?_, hyR₀⟩, hyb⟩
  rw [← hEB]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)


theorem MidData.card_centralizer_ge {b : G} {R₀ R₁ B : Subgroup G} (h : MidData b R₀ R₁ B)
    {U : Subgroup G} (hUe : IsElemAbelian 3 U) (hU9 : Nat.card U = 9) (hbU : b ∈ U)
    (hUc : ∀ g ∈ B, ∀ u ∈ U, ⁅g, u⁆ ∈ Subgroup.zpowers b) :
    27 ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (U : Set G)) := by
  have hbB : Subgroup.zpowers b ≤ B := (Subgroup.zpowers_le).2 h.b_mem
  have hUcomm : ∀ a ∈ U, ∀ a' ∈ U, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  obtain ⟨u₀, hu₀U, hu₀b⟩ : ∃ u₀ ∈ U, u₀ ∉ Subgroup.zpowers b := by
    by_contra hh
    push Not at hh
    have : U ≤ Subgroup.zpowers b := hh
    have := Subgroup.card_le_of_le this
    rw [h.card_zpowers_b] at this
    omega
  have hu₀1 : u₀ ≠ 1 := fun e1 => hu₀b (e1 ▸ Subgroup.one_mem _)
  have hu₀3 : u₀ ^ 3 = 1 := hUe.2 u₀ hu₀U
  have hu₀card : Nat.card (Subgroup.zpowers u₀) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu₀3 hu₀1]
  have hnle : ¬ Subgroup.zpowers u₀ ≤ Subgroup.zpowers b := fun hh =>
    hu₀b (hh (Subgroup.mem_zpowers _))
  have hUeq : Subgroup.zpowers b ⊔ Subgroup.zpowers u₀ = U := by
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers u₀ ≤ U :=
      sup_le ((Subgroup.zpowers_le).2 hbU) ((Subgroup.zpowers_le).2 hu₀U)
    have hn : Subgroup.zpowers b ≤ Subgroup.normalizer ((Subgroup.zpowers u₀ : Subgroup G) : Set G) := by
      intro a ha
      apply mem_normalizer_of_forall_commute
      intro k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      exact (Commute.zpow_zpow (show Commute b u₀ from hUcomm b hbU u₀ hu₀U) m n).eq
    have hh := card_sup_mul_card_inf hn
    rw [inf_comm, card_inf_eq_one_of_card_three hu₀card hnle, h.card_zpowers_b, hu₀card] at hh
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hKc : ∀ k ∈ Subgroup.zpowers b, ∀ k' ∈ Subgroup.zpowers b, k * k' = k' * k := by
    intro k hk k' hk'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk'
    exact (Commute.zpow_zpow_self b n m).eq
  have hK : ∀ k ∈ Subgroup.zpowers b, ∀ g ∈ B, g * k = k * g := fun k hk g hg =>
    (h.B_comm g k hg (hbB hk))
  let f := commHomSub B (Subgroup.zpowers b) hK hKc u₀ (fun g hg => hUc g hg u₀ hu₀U)
  have hker : Nat.card f.ker * Nat.card f.range = 81 := by
    rw [Subgroup.card_ker_mul_card_range, h.card_B]; norm_num
  have hKcard : Nat.card ↥(Subgroup.zpowers b) = 3 := h.card_zpowers_b
  have hrange : Nat.card f.range ≤ 3 := (Subgroup.card_le_card_group _).trans hKcard.le
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hker27 : 27 ≤ Nat.card f.ker := by nlinarith
  have hle : f.ker.map B.subtype ≤ B ⊓ Subgroup.centralizer (U : Set G) := by
    intro z hz
    obtain ⟨⟨z, hzB⟩, hzk, rfl⟩ := hz
    refine ⟨hzB, ?_⟩
    show z ∈ Subgroup.centralizer (U : Set G)
    have h1 : z * u₀ = u₀ * z := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hzk)
      exact commutatorElement_eq_one_iff_mul_comm.1 (by simpa [f, commHomSub_apply] using this)
    have hle2 : U ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [← hUeq]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (h.B_comm z b hzB h.b_mem).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact h1.symm
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle2 hu)
    exact this
  have := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective B.subtype_injective] at this
  omega

theorem card_sup_zpowers_of_card_three {A : Subgroup G} {y : G} (hA : Nat.card A = 9)
    (hy3 : y ^ 3 = 1) (hy : y ∉ A) (hc : ∀ a ∈ A, a * y = y * a) :
    Nat.card ↥(A ⊔ Subgroup.zpowers y) = 27 := by
  have hy1 : y ≠ 1 := fun e1 => hy (e1 ▸ A.one_mem)
  have hycard : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  have hzy : ¬ Subgroup.zpowers y ≤ A := fun h => hy (h (Subgroup.mem_zpowers y))
  have hn : A ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_of_forall_commute
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact (Commute.zpow_right (show Commute g y from hc g hg) n).eq
  have hh := card_sup_mul_card_inf hn
  rw [inf_comm, card_inf_eq_one_of_card_three hycard hzy, hA, hycard] at hh
  omega

theorem card_zpowers_sup_zpowers {x y : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1)
    (hy : y ∉ Subgroup.zpowers x) (hc : x * y = y * x) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
  have hy1 : y ≠ 1 := fun e1 => hy (e1 ▸ Subgroup.one_mem _)
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hycard : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  have hzy : ¬ Subgroup.zpowers y ≤ Subgroup.zpowers x := fun h => hy (h (Subgroup.mem_zpowers y))
  have hn : Subgroup.zpowers x ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_of_forall_commute
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (Commute.zpow_zpow (show Commute x y from hc) m n).eq
  have hh := card_sup_mul_card_inf hn
  rw [inf_comm, card_inf_eq_one_of_card_three hycard hzy, hxcard, hycard] at hh
  omega

theorem mid_starA {b : G} {R₀ R₁ B : Subgroup G} (h : MidData b R₀ R₁ B) (hr : MidRank B R₁)
    {U : Subgroup G} (hU : U ≤ R₁) (hUe : IsElemAbelian 3 U) (hU9 : Nat.card U = 9) (hbU : b ∈ U)
    (hUc : ∀ g ∈ B, ∀ u ∈ U, ⁅g, u⁆ ∈ Subgroup.zpowers b) :
    ∃ Bs : Subgroup G, IsElemAbelian 3 Bs ∧ Nat.card Bs = 81 ∧ Bs ≤ B ⊔ R₁ ∧
      Nat.card ↥(B ⊓ Bs) = 27 ∧ U ≤ Bs ∧ Bs ⊓ R₁ = U ∧ b ∈ Bs ∧
      (∀ y ∈ B, y ∈ R₀ → y ∈ Bs) := by
  set C := B ⊓ Subgroup.centralizer (U : Set G) with hC
  have hB81 : Nat.card B = 81 := by rw [h.card_B]; norm_num
  have hC27 : 27 ≤ Nat.card C := h.card_centralizer_ge hUe hU9 hbU hUc
  have hCB : C ≤ B := inf_le_left
  have hCU : ∀ c ∈ C, ∀ u ∈ U, c * u = u * c := fun c hc u hu =>
    (Subgroup.mem_centralizer_iff.1 hc.2 u hu).symm
  have hCe : IsElemAbelian 3 C := isElemAbelian_mono h.elem hCB
  have hbC : b ∈ C := by
    refine ⟨h.b_mem, ?_⟩
    show b ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val (hUe.1.is_comm.comm ⟨u, hu⟩ ⟨b, hbU⟩)
  have hBR1 : B ⊓ R₁ = Subgroup.zpowers b :=
    (Subgroup.eq_of_le_of_card_ge (le_inf ((Subgroup.zpowers_le).2 h.b_mem)
      ((Subgroup.zpowers_le).2 h.b_R1)) (by rw [h.card_B_R1, h.card_zpowers_b])).symm
  have hCUcard : Nat.card ↥(C ⊓ U) = 3 := by
    have h1 : Subgroup.zpowers b ≤ C ⊓ U := (Subgroup.zpowers_le).2 ⟨hbC, hbU⟩
    have h2 : C ⊓ U ≤ B ⊓ R₁ := inf_le_inf hCB hU
    have a1 := Subgroup.card_le_of_le h1
    have a2 := Subgroup.card_le_of_le h2
    rw [h.card_zpowers_b] at a1
    rw [h.card_B_R1] at a2
    omega
  set Bs := C ⊔ U with hBs
  have hBse : IsElemAbelian 3 Bs := isElemAbelian_sup_of_commute hCe hUe hCU
  have hBsBR : Bs ≤ B ⊔ R₁ := sup_le (hCB.trans le_sup_left) (hU.trans le_sup_right)
  have hBscard : Nat.card Bs = 3 * Nat.card C := by
    have hn : C ≤ Subgroup.normalizer (U : Set G) := fun c hc =>
      mem_normalizer_of_forall_commute fun u hu => hCU c hc u hu
    have hh := card_sup_mul_card_inf hn
    rw [hCUcard, hU9, ← hBs] at hh
    omega
  have hBsle : Nat.card Bs ≤ 81 := by
    have := hr Bs hBse hBsBR
    simpa using this
  have hBs81 : Nat.card Bs = 81 := by
    have : 81 ≤ Nat.card Bs := by rw [hBscard]; omega
    exact le_antisymm hBsle this
  have hC27' : Nat.card C = 27 := by omega
  have hUBs : U ≤ Bs := le_sup_right
  have hBBs : Nat.card ↥(B ⊓ Bs) = 3 ^ 3 := by
    have h1 : C ≤ B ⊓ Bs := le_inf hCB le_sup_left
    have a1 := Subgroup.card_le_of_le h1
    have hd : Nat.card ↥(B ⊓ Bs) ∣ 81 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : B ⊓ Bs ≤ B)
      rwa [hB81] at this
    have hne : Nat.card ↥(B ⊓ Bs) ≠ 81 := by
      intro h81
      have hBeq : B ⊓ Bs = B := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h81, hB81])
      have hBleBs : B ≤ Bs := hBeq ▸ inf_le_right
      have hBsB : B = Bs := Subgroup.eq_of_le_of_card_ge hBleBs (by rw [hBs81, hB81])
      have hUB : U ≤ B ⊓ R₁ := le_inf (hBsB ▸ hUBs) hU
      have := Subgroup.card_le_of_le hUB
      rw [h.card_B_R1, hU9] at this
      omega
    have hmem : Nat.card ↥(B ⊓ Bs) ∈ Nat.divisors 81 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
    have : Nat.divisors 81 = {1, 3, 9, 27, 81} := by decide
    rw [this] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h' | h' | h' <;> omega
  have hBBs' : Nat.card ↥(B ⊓ Bs) = 27 := by rw [hBBs]; norm_num
  have hbBs : b ∈ Bs := (show C ≤ Bs from le_sup_left) hbC
  have hBsmem : ∀ g ∈ Bs, ∃ c ∈ C, ∃ u ∈ U, g = c * u := fun g hg =>
    exists_mul_of_mem_sup_of_commute hCU hg
  have hBsR1 : Bs ⊓ R₁ = U := by
    apply le_antisymm
    · intro g hg
      obtain ⟨c, hc, u, hu, rfl⟩ := hBsmem g hg.1
      have hcR1 : c ∈ R₁ := by
        have : c = (c * u) * u⁻¹ := by group
        rw [this]; exact R₁.mul_mem hg.2 (R₁.inv_mem (hU hu))
      have : c ∈ Subgroup.zpowers b := hBR1 ▸ ⟨hCB hc, hcR1⟩
      exact U.mul_mem ((Subgroup.zpowers_le).2 hbU this) hu
    · exact le_inf hUBs hU
  refine ⟨Bs, hBse, hBs81, hBsBR, hBBs', hUBs, hBsR1, hbBs, ?_⟩
  intro y hyB hyR₀
  have hyC : y ∈ C := by
    refine ⟨hyB, ?_⟩
    show y ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (h.comm_R0R1 y hyR₀ u (hU hu)).symm
  exact (show C ≤ Bs from le_sup_left) hyC

theorem mid_star {b : G} {R₀ R₁ B : Subgroup G} (h : MidData b R₀ R₁ B) (hr : MidRank B R₁)
    {U : Subgroup G} (hU : U ≤ R₁) (hUe : IsElemAbelian 3 U) (hU9 : Nat.card U = 9) (hbU : b ∈ U)
    (hUc : ∀ g ∈ B, ∀ u ∈ U, ⁅g, u⁆ ∈ Subgroup.zpowers b) :
    ∃ Bs B0 : Subgroup G, IsElemAbelian 3 Bs ∧ Nat.card Bs = 3 ^ 4 ∧ Bs ≤ B ⊔ R₁ ∧
      Nat.card ↥(B ⊓ Bs) = 3 ^ 3 ∧ U ≤ Bs ∧
      B0 ≤ Bs ⊓ R₀ ∧ IsElemAbelian 3 B0 ∧ Nat.card B0 = 3 ^ 3 := by
  obtain ⟨Bs, hBse, hBs81, hBsBR, hBBs, hUBs, hBsR1, hbBs, hyBs⟩ :=
    mid_starA h hr hU hUe hU9 hbU hUc
  have hBsR1card : Nat.card ↥(Bs ⊓ R₁) = 9 := by rw [hBsR1, hU9]
  have hBsN : Bs ≤ Subgroup.normalizer (R₁ : Set G) :=
    hBsBR.trans (sup_le h.B_le_normalizer Subgroup.le_normalizer)
  have hS1 := card_sup_mul_card_inf hBsN
  rw [hBsR1card, hBs81] at hS1
  obtain ⟨-, hdec, -, -, -⟩ := mid_B0 h
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Subgroup G, B₀ = R₀ ⊓ (Bs ⊔ R₁) := ⟨_, rfl⟩
  have hb₀ : b ∈ B₀ := hB₀ ▸ ⟨h.b_R0, Subgroup.mem_sup_left hbBs⟩
  have hB₀R₀ : B₀ ≤ R₀ := hB₀ ▸ inf_le_left
  have hB₀le : B₀ ≤ B ⊔ R₁ := hB₀ ▸ ((inf_le_right : R₀ ⊓ (Bs ⊔ R₁) ≤ Bs ⊔ R₁).trans
    (sup_le hBsBR le_sup_right))
  have hB₀sup : B₀ ⊔ R₁ = Bs ⊔ R₁ := by
    apply le_antisymm
    · exact sup_le (hB₀ ▸ inf_le_right) le_sup_right
    · refine sup_le ?_ le_sup_right
      intro g hg
      obtain ⟨x, hx, hxg⟩ := hdec g (hBsBR hg)
      have hxB₀ : x ∈ B₀ := by
        refine hB₀ ▸ ⟨hx.1, ?_⟩
        have : x = g * (x⁻¹ * g)⁻¹ := by group
        rw [this]
        exact (Bs ⊔ R₁).mul_mem (Subgroup.mem_sup_left hg)
          ((Bs ⊔ R₁).inv_mem (Subgroup.mem_sup_right hxg))
      have : g = x * (x⁻¹ * g) := by group
      rw [this]
      exact (B₀ ⊔ R₁).mul_mem (Subgroup.mem_sup_left hxB₀) (Subgroup.mem_sup_right hxg)
  have hB₀inf : B₀ ⊓ R₁ = Subgroup.zpowers b := by
    apply le_antisymm
    · intro x hx
      exact h.inf_R0R1 x (hB₀R₀ hx.1) hx.2
    · exact le_inf ((Subgroup.zpowers_le).2 hb₀) ((Subgroup.zpowers_le).2 h.b_R1)
  have hB₀N : B₀ ≤ Subgroup.normalizer (R₁ : Set G) := fun x hx =>
    mem_normalizer_of_forall_commute fun k hk => h.comm_R0R1 x (hB₀R₀ hx) k hk
  have hS2 := card_sup_mul_card_inf hB₀N
  rw [hB₀sup, hB₀inf, h.card_zpowers_b] at hS2
  have hB₀card : Nat.card B₀ = 27 := by
    have hpos : 0 < Nat.card R₁ := Nat.card_pos
    have : Nat.card B₀ * Nat.card R₁ = 27 * Nat.card R₁ := by omega
    exact Nat.eq_of_mul_eq_mul_right hpos this
  obtain ⟨y, ⟨hyB, hyR₀⟩, hyb⟩ := mid_exists_y h
  have hy₀ : y ∈ B₀ := hB₀ ▸ ⟨hyR₀, Subgroup.mem_sup_left (hyBs y hyB hyR₀)⟩
  have hy3 : y ^ 3 = 1 := h.elem.2 y hyB
  have hyc : ∀ x ∈ R₀ ⊓ (B ⊔ R₁), x * y = y * x := by
    intro x hx
    obtain ⟨g, hg, r, hr, rfl⟩ := (h.mem_sup).1 hx.2
    have h1 : g * y = y * g := h.B_comm g y hg hyB
    have h2 : r * y = y * r := (h.comm_R0R1 y hyR₀ r hr).symm
    calc g * r * y = g * (r * y) := by rw [mul_assoc]
      _ = g * (y * r) := by rw [h2]
      _ = (g * y) * r := by rw [mul_assoc]
      _ = y * (g * r) := by rw [h1, mul_assoc]
  have hbc : ∀ x ∈ R₀ ⊓ (B ⊔ R₁), x * b = b * x := fun x hx => h.central_b x hx.1
  have hyb' : y * b = b * y := h.central_b y hyR₀
  have hW : ∀ w ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers y, ∀ x ∈ R₀ ⊓ (B ⊔ R₁), w * x = x * w := by
    intro w hw x hx
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (hbc x hx).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (hyc x hx).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hw)
  have hWcard : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers y) = 9 :=
    card_zpowers_sup_zpowers h.b_cube h.b_ne hy3 hyb hyb'.symm
  have hWB₀ : Subgroup.zpowers b ⊔ Subgroup.zpowers y ≤ B₀ :=
    sup_le ((Subgroup.zpowers_le).2 hb₀) ((Subgroup.zpowers_le).2 hy₀)
  have hbz : Subgroup.zpowers b ≤ B := (Subgroup.zpowers_le).2 h.b_mem
  have hWe : IsElemAbelian 3 (Subgroup.zpowers b ⊔ Subgroup.zpowers y) := by
    refine isElemAbelian_sup_zpowers (isElemAbelian_mono h.elem hbz) hy3 ?_
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (show Commute b y from hyb'.symm) n).eq
  obtain ⟨s, hsB₀, hsW⟩ : ∃ s ∈ B₀, s ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers y := by
    by_contra hh
    push Not at hh
    have : B₀ ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers y := hh
    have := Subgroup.card_le_of_le this
    omega
  have hs' : s ∈ R₀ ⊓ (B ⊔ R₁) := ⟨hB₀R₀ hsB₀, hB₀le hsB₀⟩
  have hs3 : s ^ 3 = 1 := h.exp_R0 s (hB₀R₀ hsB₀)
  have hWs : ∀ w ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers y, w * s = s * w := fun w hw =>
    hW w hw s hs'
  have hS'card := card_sup_zpowers_of_card_three hWcard hs3 hsW hWs
  have hS'eq : (Subgroup.zpowers b ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers s = B₀ :=
    Subgroup.eq_of_le_of_card_ge (sup_le hWB₀ ((Subgroup.zpowers_le).2 hsB₀))
      (by rw [hS'card, hB₀card])
  have hB₀e : IsElemAbelian 3 B₀ := by
    rw [← hS'eq]
    exact isElemAbelian_sup_zpowers hWe hs3 hWs
  have hBsB₀ : ∀ g ∈ Bs, ∀ x ∈ B₀, g * x = x * g := by
    intro g hg x hx
    have hg' : g ∈ B₀ ⊔ R₁ := hB₀sup ▸ Subgroup.mem_sup_left hg
    obtain ⟨x', hx', r, hr, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun a ha a' ha' => h.comm_R0R1 a (hB₀R₀ ha) a' ha') hg'
    have h1 : r * x = x * r := (h.comm_R0R1 x (hB₀R₀ hx) r hr).symm
    have h2 : x' * x = x * x' := congrArg Subtype.val (hB₀e.1.is_comm.comm ⟨x', hx'⟩ ⟨x, hx⟩)
    calc x' * r * x = x' * (r * x) := by rw [mul_assoc]
      _ = x' * (x * r) := by rw [h1]
      _ = (x' * x) * r := by rw [mul_assoc]
      _ = (x * x') * r := by rw [h2]
      _ = x * (x' * r) := by rw [mul_assoc]
  have hEe : IsElemAbelian 3 (Bs ⊔ B₀) := isElemAbelian_sup_of_commute hBse hB₀e hBsB₀
  have hEle : Bs ⊔ B₀ ≤ B ⊔ R₁ := sup_le hBsBR hB₀le
  have hEcard : Nat.card ↥(Bs ⊔ B₀) ≤ 81 := by
    have := hr _ hEe hEle
    simpa using this
  have hEeq : Bs ⊔ B₀ = Bs :=
    (Subgroup.eq_of_le_of_card_ge (le_sup_left : Bs ≤ Bs ⊔ B₀) (by omega)).symm
  have hB₀Bs : B₀ ≤ Bs := hEeq ▸ le_sup_right
  refine ⟨Bs, B₀, hBse, by rw [hBs81]; norm_num, hBsBR, by rw [hBBs]; norm_num, hUBs, le_inf hB₀Bs hB₀R₀, hB₀e,
    by rw [hB₀card]; norm_num⟩

theorem inf_eq_bot_of_pGroup_coprime {P N : Subgroup G} (hP : IsPGroup 3 P)
    (hN : Nat.Coprime 3 (Nat.card N)) : P ⊓ N = ⊥ := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have h1 : Nat.card ↥(P ⊓ N) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_right
  have h2 : Nat.card ↥(P ⊓ N) ∣ 3 ^ k := hk ▸ Subgroup.card_dvd_of_le inf_le_left
  have h3 : Nat.card ↥(P ⊓ N) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hN.pow_left k) h2 h1
  exact Subgroup.eq_bot_of_card_eq _ h3

theorem card_oPrime_coprime (L : Subgroup G) : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 L)) := by
  rw [GLAPPrimeCoreOf, Subgroup.card_map_of_injective L.subtype_injective]
  exact coprime_card_gLAPPrimeCore_aux 3 L

theorem card_inf_eq_of_sylow {R L C : Subgroup G} (hLC : L ≤ C) (hRC : R ≤ C)
    (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hR : Nat.card R = 3 ^ (Nat.card C).factorization 3) :
    Nat.card ↥(R ⊓ L) = 3 ^ (Nat.card L).factorization 3 := by
  have hprod := card_sup_mul_card_inf hRN
  have hRL : R ⊔ L ≤ C := sup_le hRC hLC
  have hd1 : Nat.card ↥(R ⊔ L) ∣ Nat.card C := Subgroup.card_dvd_of_le hRL
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hRL0 : Nat.card ↥(R ⊔ L) ≠ 0 := Nat.card_pos.ne'
  have hRL0' : Nat.card ↥(R ⊓ L) ≠ 0 := Nat.card_pos.ne'
  have hR0 : Nat.card R ≠ 0 := Nat.card_pos.ne'
  have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hv1 : (Nat.card ↥(R ⊔ L)).factorization 3 ≤ (Nat.card C).factorization 3 :=
    (Nat.factorization_le_iff_dvd hRL0 hC0).2 hd1 3
  have hvR : (Nat.card R).factorization 3 = (Nat.card C).factorization 3 := by
    rw [hR, Nat.Prime.factorization_pow Nat.prime_three]; simp
  have hv := congrArg (fun n => n.factorization 3) hprod
  rw [Nat.factorization_mul hRL0 hRL0', Nat.factorization_mul hR0 hL0] at hv
  simp only [Finsupp.add_apply] at hv
  have hk : (Nat.card L).factorization 3 ≤ (Nat.card ↥(R ⊓ L)).factorization 3 := by omega
  have hd : Nat.card ↥(R ⊓ L) ∣ 3 ^ (Nat.card C).factorization 3 :=
    hR ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  have hjv : (Nat.card ↥(R ⊓ L)).factorization 3 = j := by
    rw [hjeq, Nat.Prime.factorization_pow Nat.prime_three]; simp
  have hdvdL : 3 ^ j ∣ Nat.card L := hjeq ▸ Subgroup.card_dvd_of_le inf_le_right
  have hjle : j ≤ (Nat.card L).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hL0).1 hdvdL
  rw [hjeq]
  congr 1
  omega

section Transfer

@[expose] noncomputable def phiL (L : Subgroup G) : ↥L →* barOf 3 L :=
  QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)

theorem phiL_eq_one_iff {L : Subgroup G} {x : G} (hx : x ∈ L) :
    phiL L ⟨x, hx⟩ = 1 ↔ x ∈ GLAPPrimeCoreOf 3 L := by
  rw [phiL, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h; exact ⟨⟨x, hx⟩, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    exact this ▸ hy

theorem phiL_surjective (L : Subgroup G) : Function.Surjective (phiL L) :=
  QuotientGroup.mk'_surjective _

theorem eq_one_of_mem_oPrime {L R₀ : Subgroup G} (hR : IsPGroup 3 R₀) {x : G} (hxR : x ∈ R₀)
    (hxO : x ∈ GLAPPrimeCoreOf 3 L) : x = 1 := by
  have h := inf_eq_bot_of_pGroup_coprime hR (card_oPrime_coprime L)
  have : x ∈ R₀ ⊓ GLAPPrimeCoreOf 3 L := ⟨hxR, hxO⟩
  rw [h] at this
  simpa using this

theorem eq_of_phiL_eq {L R₀ : Subgroup G} (hR : IsPGroup 3 R₀) (hRL : R₀ ≤ L) {x y : G}
    (hxR : x ∈ R₀) (hyR : y ∈ R₀)
    (h : phiL L ⟨x, hRL hxR⟩ = phiL L ⟨y, hRL hyR⟩) : x = y := by
  have h1 : phiL L ⟨x⁻¹ * y, hRL (R₀.mul_mem (R₀.inv_mem hxR) hyR)⟩ = 1 := by
    have : (⟨x⁻¹ * y, hRL (R₀.mul_mem (R₀.inv_mem hxR) hyR)⟩ : ↥L) =
        ⟨x, hRL hxR⟩⁻¹ * ⟨y, hRL hyR⟩ := rfl
    rw [this, map_mul, map_inv, h, inv_mul_cancel]
  have h2 := (phiL_eq_one_iff _).1 h1
  have := eq_one_of_mem_oPrime hR (R₀.mul_mem (R₀.inv_mem hxR) hyR) h2
  exact (inv_mul_eq_one.1 this)

theorem mem_zpowers_of_phiL_central {L R₀ : Subgroup G} {b : G} (hL : IsHatON (barOf 3 L))
    (hR : IsPGroup 3 R₀) (hRL : R₀ ≤ L) (hbR : b ∈ R₀) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hbc : ∀ ℓ ∈ L, ℓ * b = b * ℓ) {u : G} (hu : u ∈ R₀)
    (hz : phiL L ⟨u, hRL hu⟩ ∈ Subgroup.center (barOf 3 L)) : u ∈ Subgroup.zpowers b := by
  set φb : barOf 3 L := phiL L ⟨b, hRL hbR⟩ with hφb
  have hbX : φb ∈ Subgroup.center (barOf 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨ℓ, rfl⟩ := phiL_surjective L w
    rw [hφb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hbc ℓ ℓ.2)
  have hφb1 : φb ≠ 1 := by
    intro h
    exact hb1 (eq_one_of_mem_oPrime hR hbR ((phiL_eq_one_iff _).1 h))
  have hφb3 : φb ^ 3 = 1 := by
    rw [hφb, ← map_pow]
    have : (⟨b, hRL hbR⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  have hcard : Nat.card (Subgroup.zpowers φb) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hφb3 hφb1]
  have hle : Subgroup.zpowers φb ≤ Subgroup.center (barOf 3 L) :=
    (Subgroup.zpowers_le).2 hbX
  have heq : Subgroup.zpowers φb = Subgroup.center (barOf 3 L) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hL.2.1])
  rw [← heq] at hz
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hbn : b ^ n ∈ R₀ := R₀.zpow_mem hbR n
  have : phiL L ⟨b ^ n, hRL hbn⟩ = phiL L ⟨u, hRL hu⟩ := by
    rw [← hn, hφb, ← map_zpow]
    congr 1
  have := eq_of_phiL_eq hR hRL hbn hu this
  rw [← this]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) n

theorem card_barOf_factorization (L : Subgroup G) :
    (Nat.card (barOf 3 L)).factorization 3 = (Nat.card L).factorization 3 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥L)
  have hcop := coprime_card_gLAPPrimeCore_aux 3 ↥L
  have h0 : Nat.card (barOf 3 L) ≠ 0 := Nat.card_pos.ne'
  have h1 : Nat.card (GLAPPrimeCore 3 ↥L) ≠ 0 := Nat.card_pos.ne'
  have hz : (Nat.card (GLAPPrimeCore 3 ↥L)).factorization 3 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    exact Nat.prime_three.ne_one (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 3) hd)
  have := congrArg (fun n => n.factorization 3) h
  rw [Nat.factorization_mul h0 h1] at this
  simp only [Finsupp.add_apply, hz, add_zero] at this
  exact this.symm

theorem R0_midfields (hSyl : InputONSylow) {L R₀ : Subgroup G} {b : G}
    (hL : IsHatON (barOf 3 L))
    (hR : IsPGroup 3 R₀) (hRL : R₀ ≤ L) (hcard : Nat.card R₀ = 3 ^ (Nat.card L).factorization 3)
    (hbR : b ∈ R₀) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) (hbc : ∀ ℓ ∈ L, ℓ * b = b * ℓ) :
    Nat.card R₀ = 3 ^ 5 ∧ (∀ g ∈ R₀, g ^ 3 = 1) ∧
      (∀ z ∈ R₀, (∀ g ∈ R₀, g * z = z * g) → z ∈ Subgroup.zpowers b) ∧
      (∀ x ∈ R₀, ∀ y ∈ R₀, ⁅x, y⁆ ∈ Subgroup.zpowers b) := by
  let ψ : ↥R₀ →* barOf 3 L := (phiL L).comp (Subgroup.inclusion hRL)
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    exact Subtype.ext (eq_of_phiL_eq hR hRL x.2 y.2 hxy)
  have hPcard : Nat.card ψ.range = Nat.card R₀ :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hsyl : Nat.card ψ.range = 3 ^ (Nat.card (barOf 3 L)).factorization 3 := by
    rw [hPcard, hcard, card_barOf_factorization]
  obtain ⟨hc5, hexp, hcomm, hcen⟩ := hSyl (barOf 3 L) hL (Sylow.ofCard ψ.range hsyl)
  have hmemP : ∀ x : R₀, ψ x ∈ ψ.range := fun x => ⟨x, rfl⟩
  have hψ : ∀ x : R₀, ψ x = phiL L ⟨x, hRL x.2⟩ := fun x => rfl
  have h3 : ∀ g ∈ R₀, g ^ 3 = 1 := by
    intro g hg
    have h1 := hexp (ψ ⟨g, hg⟩) (hmemP _)
    rw [← map_pow] at h1
    have h2 : phiL L ⟨g ^ 3, hRL (R₀.pow_mem hg 3)⟩ = 1 := by
      have : (⟨g ^ 3, hRL (R₀.pow_mem hg 3)⟩ : ↥L) = (⟨g, hRL hg⟩ : ↥L) ^ 3 := rfl
      rw [this, map_pow]
      exact h1
    exact eq_one_of_mem_oPrime hR (R₀.pow_mem hg 3) ((phiL_eq_one_iff _).1 h2)
  refine ⟨?_, h3, ?_, ?_⟩
  · rw [← hPcard]; exact hc5
  · intro z hz hzc
    apply mem_zpowers_of_phiL_central hL hR hRL hbR hb1 hb3 hbc hz
    apply hcen (ψ ⟨z, hz⟩) (hmemP _)
    rintro _ ⟨g, rfl⟩
    have := hzc g g.2
    show ψ g * ψ ⟨z, hz⟩ = ψ ⟨z, hz⟩ * ψ g
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext this)
  · intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ R₀ := by
      rw [commutatorElement_def]
      exact R₀.mul_mem (R₀.mul_mem (R₀.mul_mem hx hy) (R₀.inv_mem hx)) (R₀.inv_mem hy)
    apply mem_zpowers_of_phiL_central hL hR hRL hbR hb1 hb3 hbc hxy
    have := hcomm (ψ ⟨x, hx⟩) (hmemP _) (ψ ⟨y, hy⟩) (hmemP _)
    have e : phiL L ⟨⁅x, y⁆, hRL hxy⟩ = ⁅ψ ⟨x, hx⟩, ψ ⟨y, hy⟩⁆ := by
      have : (⟨⁅x, y⁆, hRL hxy⟩ : ↥L) = ⁅(⟨x, hRL hx⟩ : ↥L), ⟨y, hRL hy⟩⁆ := rfl
      rw [this, map_commutatorElement]
      rfl
    rw [e]
    exact this

theorem conj_mem_oPrime {p : ℕ} {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) {y : G} (hy : y ∈ GLAPPrimeCoreOf p J) :
    g * y * g⁻¹ ∈ GLAPPrimeCoreOf p J := by
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨J.normalizerMonoidHom ⟨g, hg⟩ y',
    map_gLAPPrimeCore_le p (J.normalizerMonoidHom ⟨g, hg⟩) ⟨y', hy', rfl⟩, ?_⟩
  rfl

theorem mem_centralizerQuot_iff_barAut_aux (p : ℕ) {J : Subgroup G}
    (g : ↥(Subgroup.normalizer (J : Set G))) :
    (g : G) ∈ centralizerQuot J (GLAPPrimeCoreOf p J) ↔ barAut p J g = 1 := by
  have hs : ∀ y : ↥J, ((J.normalizerMonoidHom g y : ↥J) : G) = g * y * (g : G)⁻¹ := fun _ => rfl
  constructor
  · rintro ⟨-, -, hc⟩
    ext z
    induction z using QuotientGroup.induction_on with | H y => ?_
    rw [barAut_mk, MulAut.one_apply, eq_comm, QuotientGroup.eq]
    have := hc (y : G)⁻¹ (J.inv_mem y.2)
    refine (Subgroup.mem_map_iff_mem J.subtype_injective).1
      (?_ : J.subtype _ ∈ GLAPPrimeCoreOf p J)
    simpa [mul_assoc, hs] using this
  · intro h
    refine ⟨g.2, ?_, fun x hx => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => conj_mem_oPrime g.2 hy, fun hy => ?_⟩
      have := conj_mem_oPrime (inv_mem g.2) hy
      simpa [mul_assoc] using this
    · have h1 := congrArg (fun φ => φ (QuotientGroup.mk (⟨x, hx⟩⁻¹ : ↥J))) h
      simp only [barAut_mk, MulAut.one_apply] at h1
      rw [eq_comm, QuotientGroup.eq] at h1
      have h2 : J.subtype _ ∈ GLAPPrimeCoreOf p J := Subgroup.mem_map_of_mem J.subtype h1
      simpa [mul_assoc, hs] using h2

theorem oPrime_le {L : Subgroup G} : GLAPPrimeCoreOf 3 L ≤ L := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem normalizer_le_normalizer_oPrime {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((GLAPPrimeCoreOf 3 L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_oPrime hg hy, fun hy => ?_⟩
  have := conj_mem_oPrime (inv_mem hg) hy
  simpa [mul_assoc] using this

theorem phiL_central_of_cq {L : Subgroup G} {x : G} (hx : x ∈ L)
    (h : ∀ ℓ ∈ L, ℓ * x * ℓ⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 L) :
    phiL L ⟨x, hx⟩ ∈ Subgroup.center (barOf 3 L) := by
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨ℓ, rfl⟩ := phiL_surjective L w
  have h1 := (phiL_eq_one_iff (L.mul_mem (L.mul_mem (L.mul_mem ℓ.2 hx) (L.inv_mem ℓ.2))
    (L.inv_mem hx))).2 (h ℓ ℓ.2)
  have e : (⟨(ℓ : G) * x * (ℓ : G)⁻¹ * x⁻¹, L.mul_mem (L.mul_mem (L.mul_mem ℓ.2 hx)
      (L.inv_mem ℓ.2)) (L.inv_mem hx)⟩ : ↥L) = ℓ * ⟨x, hx⟩ * ℓ⁻¹ * ⟨x, hx⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem R_eq_mul (hAut : InputONAut) {L R : Subgroup G} {b : G}
    (hL : IsHatON (barOf 3 L)) (hR3 : IsPGroup 3 R)
    (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hR0card : Nat.card ↥(R ⊓ L) = 3 ^ 5)
    (hinf : ∀ x ∈ R ⊓ L, x ∈ R ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L) →
      x ∈ Subgroup.zpowers b)
    (hb3 : Nat.card (Subgroup.zpowers b) = 3) :
    ∀ r ∈ R, ∃ r₀ ∈ R ⊓ L, ∃ r₁ ∈ R ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L), r = r₀ * r₁ := by
  let ρ : ↥R →* MulAut (barOf 3 L) := (barAut 3 L).comp (Subgroup.inclusion hRN)
  have hρ : ∀ r : ↥R, ρ r = 1 ↔ (r : G) ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L) := fun r =>
    (mem_centralizerQuot_iff_barAut_aux 3 (J := L) ⟨r, hRN r.2⟩).symm
  have hrange3 : IsPGroup 3 ρ.range :=
    hR3.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hcardρ : Nat.card ρ.range ≤ 3 ^ 4 := hAut _ hL _ hrange3
  let ρ₀ : ↥(R ⊓ L) →* MulAut (barOf 3 L) := ρ.comp (Subgroup.inclusion inf_le_left)
  have hker : Nat.card ρ₀.ker ≤ 3 := by
    have hle : ρ₀.ker.map (R ⊓ L).subtype ≤ Subgroup.zpowers b := by
      intro z hz
      obtain ⟨⟨z, hzRL⟩, hzk, rfl⟩ := hz
      apply hinf z hzRL
      exact ⟨hzRL.1, (hρ ⟨z, hzRL.1⟩).1 (MonoidHom.mem_ker.1 hzk)⟩
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (R ⊓ L).subtype_injective, hb3] at this
  have hkr : Nat.card ρ₀.ker * Nat.card ρ₀.range = 3 ^ 5 := by
    rw [Subgroup.card_ker_mul_card_range, hR0card]
  have hrange0 : 3 ^ 4 ≤ Nat.card ρ₀.range := by
    have : 0 < Nat.card ρ₀.range := Nat.card_pos
    nlinarith
  have hle : ρ₀.range ≤ ρ.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion inf_le_left x, rfl⟩
  have heq : ρ₀.range = ρ.range := Subgroup.eq_of_le_of_card_ge hle (by omega)
  intro r hr
  have hmem : ρ ⟨r, hr⟩ ∈ ρ₀.range := by rw [heq]; exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  refine ⟨(x : G), x.2, (x : G)⁻¹ * r, ⟨R.mul_mem (R.inv_mem (x.2.1)) hr, ?_⟩, by group⟩
  have h1 : ρ ⟨(x : G)⁻¹ * r, R.mul_mem (R.inv_mem (x.2.1)) hr⟩ = 1 := by
    have : (⟨(x : G)⁻¹ * r, R.mul_mem (R.inv_mem (x.2.1)) hr⟩ : ↥R) =
        (Subgroup.inclusion inf_le_left x)⁻¹ * ⟨r, hr⟩ := rfl
    rw [this, map_mul, map_inv]
    have hx' : ρ (Subgroup.inclusion inf_le_left x) = ρ ⟨r, hr⟩ := hx
    rw [hx', inv_mul_cancel]
  exact (hρ _).1 h1

theorem transfer (hSyl : InputONSylow) (hAut : InputONAut) {L B R C : Subgroup G} {b : G}
    (hL : IsHatON (barOf 3 L)) (hbL : b ∈ L)
    (hLC : L ≤ Subgroup.centralizer ({b} : Set G)) (hLC' : L ≤ C)
    (hR3 : IsPGroup 3 R) (hRC : R ≤ C)
    (hRsyl : Nat.card R = 3 ^ (Nat.card C).factorization 3)
    (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hBR : B ≤ R) (hBel : IsElemAbelian 3 B) (hBcard : Nat.card B = 3 ^ 4) (hbB : b ∈ B)
    (hb1 : b ≠ 1)
    (hBmax : ∀ E : Subgroup G, IsElemAbelian 3 E → B ≤ E → E = B)
    (h27 : (centralizerQuot L (GLAPPrimeCoreOf 3 L)).relIndex
      (B ⊓ Subgroup.normalizer (L : Set G)) = 27) :
    MidData b (R ⊓ L) (R ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L)) B := by
  have hLb : ∀ ℓ ∈ L, ℓ * b = b * ℓ := fun ℓ hℓ =>
    Subgroup.mem_centralizer_singleton_iff.1 (hLC hℓ)
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have hbR : b ∈ R ⊓ L := ⟨hBR hbB, hbL⟩
  have hR₀3 : IsPGroup 3 ↥(R ⊓ L) := hR3.to_le inf_le_left
  have hR₀card := card_inf_eq_of_sylow hLC' hRC hRN hRsyl
  obtain ⟨hc5, hexp, hcen, hcomm⟩ := R0_midfields hSyl hL hR₀3 inf_le_right hR₀card hbR hb1 hb3 hLb
  have hbCQ : b ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
    refine ⟨Subgroup.le_normalizer hbL, normalizer_le_normalizer_oPrime (Subgroup.le_normalizer hbL),
      fun x hx => ?_⟩
    have : x * b * x⁻¹ * b⁻¹ = 1 := by rw [hLb x hx]; group
    rw [this]; exact one_mem _
  have hcommRR : ∀ x ∈ R ⊓ L, ∀ y ∈ R ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L), x * y = y * x := by
    intro x hx y hy
    have hc := hy.2.2.2 x hx.2
    have hcR : x * y * x⁻¹ * y⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (R.mul_mem hx.1 hy.1) (R.inv_mem hx.1)) (R.inv_mem hy.1)
    have h1 := eq_one_of_mem_oPrime hR3 hcR hc
    exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h1)
  have hzb3 : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hinf : ∀ x ∈ R ⊓ L, x ∈ R ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L) →
      x ∈ Subgroup.zpowers b := by
    intro x hx hxCQ
    apply mem_zpowers_of_phiL_central hL hR₀3 inf_le_right hbR hb1 hb3 hLb hx
    exact phiL_central_of_cq hx.2 hxCQ.2.2.2
  have hBle := R_eq_mul hAut hL hR3 hRN (by rw [hR₀card] at *; exact hc5) hinf hzb3
  have hBN : B ⊓ Subgroup.normalizer (L : Set G) = B := inf_of_le_left (hBR.trans hRN)
  have hBR1 : Nat.card ↥(B ⊓ (R ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L))) = 3 := by
    have hrw : B ⊓ (R ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L)) =
        B ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hBR h.1, h.2⟩⟩
    rw [hrw]
    rw [hBN, Subgroup.relIndex] at h27
    have h2 := Subgroup.card_mul_index
      ((centralizerQuot L (GLAPPrimeCoreOf 3 L)).subgroupOf B)
    rw [h27, hBcard] at h2
    have hc : Nat.card ↥((centralizerQuot L (GLAPPrimeCoreOf 3 L)).subgroupOf B) =
        Nat.card ↥(B ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L)) := by
      rw [inf_comm, ← Subgroup.subgroupOf_map_subtype _ B,
        Subgroup.card_map_of_injective B.subtype_injective]
    rw [hc] at h2
    omega
  exact
    { elem := hBel
      card_B := hBcard
      b_mem := hbB
      b_ne := hb1
      max := hBmax
      card_R0 := hc5
      exp_R0 := hexp
      b_R0 := hbR
      central_b := fun g hg => hLb g hg.2
      center_R0 := hcen
      comm_R0 := hcomm
      comm_R0R1 := hcommRR
      inf_R0R1 := fun x hx hx1 => hinf x hx hx1
      b_R1 := ⟨hBR hbB, hbCQ⟩
      B_le := fun g hg => hBle g (hBR hg)
      card_B_R1 := hBR1 }

end Transfer

theorem pCore_le_center (hsimple : InputONSimple) {X : Type} [Group X] [Finite X]
    (hX : IsHatON X) : CFSG.pCore 3 X ≤ Subgroup.center X := by
  obtain ⟨e⟩ := hX.2.2
  have hSimp : IsSimpleGroup (X ⧸ Subgroup.center X) := by
    have := hsimple.1
    exact e.isSimpleGroup
  have hN : (CFSG.pCore 3 X).Normal := CFSG.pCore_normal
  have hq : Function.Surjective (QuotientGroup.mk' (Subgroup.center X)) :=
    QuotientGroup.mk'_surjective _
  have hM : ((CFSG.pCore 3 X).map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
    hN.map _ hq
  rcases Subgroup.Normal.eq_bot_or_eq_top ((CFSG.pCore 3 X).map (QuotientGroup.mk' (Subgroup.center X)))
    with h | h
  · intro x hx
    have : QuotientGroup.mk' (Subgroup.center X) x ∈
        (CFSG.pCore 3 X).map (QuotientGroup.mk' (Subgroup.center X)) := ⟨x, hx, rfl⟩
    rw [h] at this
    exact (QuotientGroup.eq_one_iff _).1 (by simpa using this)
  · exfalso
    have hpg : IsPGroup 3 (X ⧸ Subgroup.center X) := by
      refine (CFSG.pCore_isPGroup (p := 3) (G := X)).of_surjective
        ((QuotientGroup.mk' (Subgroup.center X)).comp (CFSG.pCore 3 X).subtype) ?_
      intro y
      have : y ∈ (CFSG.pCore 3 X).map (QuotientGroup.mk' (Subgroup.center X)) := by rw [h]; trivial
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨⟨x, hx⟩, rfl⟩
    have hnt : Nontrivial (X ⧸ Subgroup.center X) := hSimp.toNontrivial
    have hcn := hpg.center_nontrivial
    have hcen : Subgroup.center (X ⧸ Subgroup.center X) = ⊤ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (X ⧸ Subgroup.center X)) with h' | h'
      · exfalso
        rw [h'] at hcn
        exact (not_nontrivial_iff_subsingleton.2 (inferInstance : Subsingleton (⊥ : Subgroup _))) hcn
      · exact h'
    obtain ⟨a, b, hab⟩ := hsimple.2
    apply hab
    have hc : ∀ g : X ⧸ Subgroup.center X, g ∈ Subgroup.center (X ⧸ Subgroup.center X) := by
      intro g; rw [hcen]; trivial
    have := Subgroup.mem_center_iff.1 (hc (e.symm a)) (e.symm b)
    have h2 := congrArg e this
    simpa using h2.symm

theorem center_le_pCore {X : Type} [Group X] [Finite X] (hX : IsHatON X) :
    Subgroup.center X ≤ CFSG.pCore 3 X := by
  have hpg : IsPGroup 3 (Subgroup.center X) :=
    IsPGroup.of_card (n := 1) (by rw [hX.2.1]; norm_num)
  have hN : (Subgroup.center X).Normal := inferInstance
  exact le_sSup ⟨hN, hpg⟩

theorem quot_oPrimeP_equiv (hsimple : InputONSimple) {L : Subgroup G} (hL : IsHatON (barOf 3 L)) :
    Nonempty ((↥L ⧸ oPrimeP 3 ↥L) ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group) := by
  have hcore : CFSG.pCore 3 (barOf 3 L) = Subgroup.center (barOf 3 L) :=
    le_antisymm (pCore_le_center hsimple hL) (center_le_pCore hL)
  obtain ⟨e⟩ := hL.2.2
  let f : ↥L →* (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) :=
    (QuotientGroup.mk' (Subgroup.center (barOf 3 L))).comp (phiL L)
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp (phiL_surjective L)
  have hker : f.ker = oPrimeP 3 ↥L := by
    rw [oPrimeP, hcore]
    ext x
    simp [f, phiL, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)).trans e⟩

theorem card_comap_mk {X : Type*} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (T : Subgroup (X ⧸ Z)) :
    Nat.card ↥(T.comap (QuotientGroup.mk' Z)) = Nat.card T * Nat.card Z := by
  have hq : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have h1 := Subgroup.card_mul_index (T.comap (QuotientGroup.mk' Z))
  have h2 := Subgroup.card_mul_index T
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  rw [Subgroup.index_comap_of_surjective _ hq] at h1
  have hpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have : Nat.card ↥(T.comap (QuotientGroup.mk' Z)) * T.index = (Nat.card T * Nat.card Z) * T.index := by
    rw [h1, h3, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem exists_two_of_central {X : Type*} [Group X] [Finite X] {Z : Subgroup X} [Z.Normal]
    (hZc : ∀ z ∈ Z, ∀ g : X, g * z = z * g) (hZ3 : Nat.card Z = 3) {E : Subgroup X}
    {T : Subgroup (X ⧸ Z)} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hET : E.map (QuotientGroup.mk' Z) ≤ Subgroup.normalizer (T : Set (X ⧸ Z))) :
    ∃ S : Subgroup X, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup X := T.comap (QuotientGroup.mk' Z) with hQ
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hk1 : k ≠ 0 := by
    intro h0
    apply hT
    rw [h0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  have hZQ : Z ≤ Q := fun z hz => by
    show QuotientGroup.mk' Z z ∈ T
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz]; exact T.one_mem
  have hQcard : Nat.card Q = 3 * 2 ^ k := by
    rw [hQ, card_comap_mk, hk, hZ3]; ring
  have hEQ : E ≤ Subgroup.normalizer (Q : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := (Subgroup.mem_normalizer_iff.1 (hET ⟨g, hg, rfl⟩)) (QuotientGroup.mk' Z y)
    show QuotientGroup.mk' Z y ∈ T ↔ QuotientGroup.mk' Z (g * y * g⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact h1
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥Q) := inferInstance
  have hPcard : Nat.card (P : Subgroup ↥Q) = 2 ^ k := by
    rw [Sylow.card_eq_multiplicity, hQcard]
    have : (3 * 2 ^ k).factorization 2 = k := by
      rw [Nat.factorization_mul (by norm_num) (by positivity), Nat.Prime.factorization_pow
        Nat.prime_two]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]
    rw [this]
  set Z' : Subgroup ↥Q := Z.subgroupOf Q with hZ'
  have hZ'n : Z'.Normal := inferInstance
  have hZ'card : Nat.card Z' = 3 := by
    rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv, hZ3]
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have hPZ : (P : Subgroup ↥Q) ⊓ Z' = ⊥ := by
    have h1 : Nat.card ↥((P : Subgroup ↥Q) ⊓ Z') ∣ 2 ^ k := hPcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥((P : Subgroup ↥Q) ⊓ Z') ∣ 3 := hZ'card ▸ Subgroup.card_dvd_of_le inf_le_right
    exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hPsup : (P : Subgroup ↥Q) ⊔ Z' = ⊤ := by
    have hn : (P : Subgroup ↥Q) ≤ Subgroup.normalizer (Z' : Set ↥Q) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hZ'n]; exact le_top
    have h := card_sup_mul_card_inf hn
    rw [hPZ, Subgroup.card_bot, hPcard, hZ'card] at h
    apply Subgroup.eq_top_of_card_eq
    have : Nat.card ↥Q = Nat.card ↥((P : Subgroup ↥Q) ⊔ Z') := by
      rw [hQcard]; omega
    exact this.symm
  have hPnormal : (P : Subgroup ↥Q).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ (P : Subgroup ↥Q) ⊔ Z' := by rw [hPsup]; trivial
    obtain ⟨p, hp, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg
    have hzc : ∀ m : ↥Q, z * m = m * z := fun m =>
      Subtype.ext (hZc _ hz m).symm
    have : p * z * n * (p * z)⁻¹ = p * n * p⁻¹ := by
      calc p * z * n * (p * z)⁻¹ = p * (z * n) * z⁻¹ * p⁻¹ := by group
        _ = p * (n * z) * z⁻¹ * p⁻¹ := by rw [hzc n]
        _ = p * n * p⁻¹ := by group
    rw [this]
    exact (P : Subgroup ↥Q).mul_mem ((P : Subgroup ↥Q).mul_mem hp hn) ((P : Subgroup ↥Q).inv_mem hp)
  have : Unique (Sylow 2 ↥Q) := Sylow.unique_of_normal P hPnormal
  refine ⟨(P : Subgroup ↥Q).map Q.subtype, ?_, ?_, ?_⟩
  · intro h0
    have h1 : Nat.card ↥((P : Subgroup ↥Q).map Q.subtype) = 2 ^ k := by
      rw [Subgroup.card_map_of_injective Q.subtype_injective, hPcard]
    rw [h0, Subgroup.card_bot] at h1
    exact hk1 (Nat.pow_eq_one.1 h1.symm |>.resolve_left (by norm_num))
  · exact IsPGroup.of_card (n := k) (by rw [Subgroup.card_map_of_injective Q.subtype_injective, hPcard])
  · intro g hg
    have hgQ : g ∈ Subgroup.normalizer (Q : Set X) := hEQ hg
    set S₂ : Subgroup X := (P : Subgroup ↥Q).map Q.subtype with hS₂
    have hconj : S₂.map (MulAut.conj g).toMonoidHom = S₂ := by
      let P' : Subgroup ↥Q := (S₂.map (MulAut.conj g).toMonoidHom).subgroupOf Q
      have hle : S₂.map (MulAut.conj g).toMonoidHom ≤ Q := by
        rintro _ ⟨y, ⟨y', hy', rfl⟩, rfl⟩
        have := (Subgroup.mem_normalizer_iff.1 hgQ y').1 y'.2
        simpa [MulAut.conj_apply] using this
      have hP'card : Nat.card P' = 2 ^ k := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
          Subgroup.card_map_of_injective (MulAut.conj g).injective, hS₂,
          Subgroup.card_map_of_injective Q.subtype_injective, hPcard]
      have hsyl : Nat.card P' = 2 ^ (Nat.card ↥Q).factorization 2 := by
        rw [hP'card, hQcard]
        congr 1
        rw [Nat.factorization_mul (by norm_num) (by positivity), Nat.Prime.factorization_pow
          Nat.prime_two]
        simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]
      have heq : (Sylow.ofCard P' hsyl) = P := Subsingleton.elim _ _
      have : (P' : Subgroup ↥Q) = (P : Subgroup ↥Q) := congrArg (fun R : Sylow 2 ↥Q => (R : Subgroup ↥Q)) heq
      have h2 : P'.map Q.subtype = S₂ := by rw [this]
      exact (Subgroup.map_subgroupOf_eq_of_le hle).symm.trans h2
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← hconj]
      exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
    · intro hy
      rw [← hconj] at hy
      obtain ⟨y', hy', hyy⟩ := hy
      have : y' = y := by simpa [MulAut.conj_apply] using hyy
      rwa [← this]

theorem phiL_conj {L : Subgroup G} {x a : G} (hx : x ∈ L) (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hc : x⁻¹ * a ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L)) {y : G} (hy : y ∈ L) :
    phiL L ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.1 ha y).1 hy⟩ =
      phiL L ⟨x, hx⟩ * phiL L ⟨y, hy⟩ * (phiL L ⟨x, hx⟩)⁻¹ := by
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hx
  have hcN : x⁻¹ * a ∈ Subgroup.normalizer (L : Set G) := hc.1
  have h1 : barAut 3 L ⟨x⁻¹ * a, hcN⟩ = 1 :=
    (mem_centralizerQuot_iff_barAut_aux 3 (J := L) ⟨x⁻¹ * a, hcN⟩).1 hc
  have h2 : (⟨a, ha⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨x, hxN⟩ * ⟨x⁻¹ * a, hcN⟩ := by
    ext; simp
  have h3 : barAut 3 L ⟨a, ha⟩ = barAut 3 L ⟨x, hxN⟩ := by
    rw [h2, map_mul, h1, mul_one]
  have e1 := barAut_mk 3 L ⟨a, ha⟩ ⟨y, hy⟩
  have e2 := barAut_mk 3 L ⟨x, hxN⟩ ⟨y, hy⟩
  rw [h3, e2] at e1
  have hL1 : (L.normalizerMonoidHom ⟨a, ha⟩ ⟨y, hy⟩ : ↥L) = ⟨a * y * a⁻¹, _⟩ := rfl
  have hL2 : (L.normalizerMonoidHom ⟨x, hxN⟩ ⟨y, hy⟩ : ↥L) =
      (⟨x, hx⟩ : ↥L) * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ := rfl
  rw [hL1, hL2] at e1
  have : phiL L ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.1 ha y).1 hy⟩ =
      QuotientGroup.mk (⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.1 ha y).1 hy⟩ : ↥L) := rfl
  rw [this, ← e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rfl

theorem isPGroup_of_exp_three {B0 : Subgroup G} (h : ∀ x ∈ B0, x ^ 3 = 1) : IsPGroup 3 B0 := by
  intro x
  exact ⟨1, by simpa using Subtype.ext (by simpa using h x x.2)⟩

theorem lift_two (h2029 : Input20_29) {L A B0 : Subgroup G} {b : G}
    (hL : IsHatON (barOf 3 L)) (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hB0L : B0 ≤ L) (hB0card : Nat.card B0 = 3 ^ 4) (hB0exp : ∀ x ∈ B0, x ^ 3 = 1)
    (hB0comm : ∀ x ∈ B0, ∀ y ∈ B0, ⁅x, y⁆ ∈ Subgroup.zpowers b) (hbB0 : b ∈ B0) (hb1 : b ≠ 1)
    (hbc : ∀ ℓ ∈ L, ℓ * b = b * ℓ)
    (hAact : ∀ a ∈ A, ∃ x ∈ B0, x⁻¹ * a ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L)) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set G) := by
  have hB03 : IsPGroup 3 B0 := isPGroup_of_exp_three hB0exp
  have hb3 : b ^ 3 = 1 := hB0exp b hbB0
  set Z : Subgroup (barOf 3 L) := Subgroup.center (barOf 3 L) with hZ
  have hZc : ∀ z ∈ Z, ∀ g : barOf 3 L, g * z = z * g := fun z hz g => Subgroup.mem_center_iff.1 hz g
  let ψ : ↥B0 →* barOf 3 L := (phiL L).comp (Subgroup.inclusion hB0L)
  let ψ' : ↥B0 →* (barOf 3 L ⧸ Z) := (QuotientGroup.mk' Z).comp ψ
  have hφb : phiL L ⟨b, hB0L hbB0⟩ ∈ Z := by
    apply phiL_central_of_cq (hB0L hbB0)
    intro ℓ hℓ
    have : ℓ * b * ℓ⁻¹ * b⁻¹ = 1 := by rw [hbc ℓ hℓ]; group
    rw [this]; exact one_mem _
  have hker : ψ'.ker = Subgroup.zpowers (⟨b, hbB0⟩ : ↥B0) := by
    ext x
    constructor
    · intro hx
      have hxZ : phiL L ⟨x, hB0L x.2⟩ ∈ Z := by
        have := MonoidHom.mem_ker.1 hx
        exact (QuotientGroup.eq_one_iff _).1 this
      have := mem_zpowers_of_phiL_central hL hB03 hB0L hbB0 hb1 hb3 hbc x.2 hxZ
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 this
      exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [MonoidHom.mem_ker, map_zpow]
      have : ψ' ⟨b, hbB0⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hφb
      rw [this, one_zpow]
  have hkercard : Nat.card ψ'.ker = 3 := by
    rw [hker, Nat.card_zpowers]
    have : (⟨b, hbB0⟩ : ↥B0) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    have h1 : (⟨b, hbB0⟩ : ↥B0) ≠ 1 := fun e => hb1 (by simpa using congrArg Subtype.val e)
    exact orderOf_eq_prime this h1
  have hE27 : Nat.card ψ'.range = 3 ^ 3 := by
    have := Subgroup.card_ker_mul_card_range ψ'
    rw [hkercard, hB0card] at this
    omega
  have hEe : IsElemAbelian 3 ψ'.range := by
    refine ⟨⟨⟨fun ⟨u, hu⟩ ⟨v, hv⟩ => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨x, rfl⟩ := hu
      obtain ⟨y, rfl⟩ := hv
      apply Subtype.ext
      show ψ' x * ψ' y = ψ' y * ψ' x
      have hxy : ⁅x, y⁆ ∈ ψ'.ker := by
        rw [hker]
        have := hB0comm x x.2 y y.2
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 this
        refine Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext ?_⟩
        show b ^ n = ⁅(x : G), (y : G)⁆
        exact hn
      have h1 := MonoidHom.mem_ker.1 hxy
      rw [map_commutatorElement] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    · obtain ⟨x, rfl⟩ := hz
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (by simpa using hB0exp x x.2)
      rw [this, map_one]
  obtain ⟨e⟩ := hL.2.2
  have hKfin : Finite (barOf 3 L ⧸ Z) := inferInstance
  obtain ⟨T, hT, hT2, hET⟩ := h2029 (barOf 3 L ⧸ Z) ⟨e⟩ ψ'.range hEe hE27
  have hψrange : ψ'.range = ψ.range.map (QuotientGroup.mk' Z) := MonoidHom.range_comp _ _
  obtain ⟨S, hS, hS2, hES⟩ := exists_two_of_central (X := barOf 3 L) (Z := Z) hZc hL.2.1
    (E := ψ.range) hT hT2 (by rw [← hψrange]; exact hET)
  set Y : Subgroup G := (S.comap (phiL L)).map L.subtype with hY
  have hYcard : Nat.card Y = Nat.card S * Nat.card (GLAPPrimeCore 3 ↥L) := by
    rw [hY, Subgroup.card_map_of_injective L.subtype_injective]
    exact card_comap_mk (GLAPPrimeCore 3 ↥L) S
  have hScard : ∃ j : ℕ, Nat.card S = 2 ^ j := hS2.exists_card_eq
  obtain ⟨j, hj⟩ := hScard
  have hj0 : j ≠ 0 := by
    intro h0
    apply hS
    rw [h0, pow_zero] at hj
    exact Subgroup.eq_bot_of_card_eq _ hj
  have hcop : ¬ 3 ∣ Nat.card Y := by
    rw [hYcard, hj]
    intro hd
    have hcopN := coprime_card_gLAPPrimeCore_aux 3 ↥L
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    · exact Nat.prime_three.ne_one (Nat.eq_one_of_dvd_coprimes hcopN (dvd_refl 3) h)
  have heven : Even (Nat.card Y) := by
    rw [hYcard, hj]
    exact (Nat.even_mul).2 (Or.inl ((Nat.even_pow).2 ⟨even_two, hj0⟩))
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
    have hfwd : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y := by
      intro a haA y hy
      obtain ⟨x, hxB0, hxc⟩ := hAact a haA
      obtain ⟨y', hy', rfl⟩ := hy
      have hyL : (y' : G) ∈ L := y'.2
      have h1 := phiL_conj (hB0L hxB0) (hAL haA) hxc hyL
      refine ⟨⟨(a : G) * y' * a⁻¹, (Subgroup.mem_normalizer_iff.1 (hAL haA) y').1 hyL⟩, ?_, rfl⟩
      show phiL L ⟨(a : G) * y' * a⁻¹, _⟩ ∈ S
      rw [h1]
      have hφx : phiL L ⟨x, hB0L hxB0⟩ ∈ Subgroup.normalizer (S : Set (barOf 3 L)) :=
        hES ⟨⟨x, hxB0⟩, rfl⟩
      have := (Subgroup.mem_normalizer_iff.1 hφx (phiL L y')).1 hy'
      exact this
    intro a haA
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hfwd a haA y hy, fun hy => ?_⟩
    have := hfwd a⁻¹ (A.inv_mem haA) _ hy
    simpa [mul_assoc] using this
  exact exists_twoGroup_normalized_of_coprime_even Nat.prime_three (by norm_num) hA hAY hcop heven
    |>.elim fun T ⟨hT0, _, hT2, hAT⟩ => ⟨T, hT0, hT2, hAT⟩

theorem barX_ne_bot_aux {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L) :
    barX p X L ≠ ⊥ := by
  intro h
  have h3 := hL.2.2.1
  have hb : ((L.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))) = ⊥ := h
  rw [hb] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

theorem comp_mem_of_le_sSup {p : ℕ} (_hp : p.Prime) {X L : Subgroup G} (S : Set (Subgroup G))
    (hS : ∀ J ∈ S, GLAPComponent p X J) (hL : GLAPComponent p X L) (hle : L ≤ sSup S) :
    L ∈ S := by
  by_contra hnot
  set bL := barX p X L with hbL
  have hcomm : ∀ J ∈ S, ⁅bL, barX p X J⁆ = ⊥ := by
    intro J hJ
    have hne : L ≠ J := fun h => hnot (h ▸ hJ)
    have hbar : barX p X L ≠ barX p X J := fun h => hne (glaPComponent_uniqueAux hL (hS J hJ) h)
    exact CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL.2.2.1 (hS J hJ).2.2.1 hbar
  set C' : Subgroup G := ((Subgroup.centralizer (bL : Set (↥X ⧸ GLAPPrimeCore p ↥X))).comap
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype with hC'
  have hSC : sSup S ≤ C' := by
    refine sSup_le fun J hJ => ?_
    intro y hy
    have hyX : y ∈ X := (hS J hJ).1 hy
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ ∈ barX p X J :=
      ⟨⟨y, hyX⟩, (Subgroup.mem_subgroupOf).2 hy, rfl⟩
    show _ ∈ Subgroup.centralizer (bL : Set (↥X ⧸ GLAPPrimeCore p ↥X))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := Subgroup.mem_centralizer_iff.1
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm J hJ)) hx) _ hmem
    exact this.symm
  have hLC : L ≤ C' := hle.trans hSC
  have hbarle : bL ≤ Subgroup.centralizer (bL : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨y, hy, hyc⟩ := hLC ((Subgroup.mem_subgroupOf).1 hc)
    have hyc' : y = c := Subtype.ext hyc
    subst hyc'
    exact hy
  have hperf : ⁅bL, bL⁆ = bL := Subgroup.isPerfect_iff.1 ⟨hL.2.2.1.2.2.1⟩
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2 hbarle] at hperf
  exact barX_ne_bot_aux hL hperf.symm

theorem inducesFieldAut_of_mem_cq {J : Subgroup G} {x : G}
    (hx : x ∈ centralizerQuot J (GLAPPrimeCoreOf 3 J)) : InducesFieldAut 3 J x :=
  ⟨hx.1, Or.inl ((mem_centralizerQuot_iff_barAut_aux 3 (J := J) ⟨x, hx.1⟩).1 hx)⟩

theorem inducesFieldAut_of_ne {X J L : Subgroup G} (hJ : GLAPComponent 3 X J)
    (hL : GLAPComponent 3 X L) (hne : J ≠ L) {x : G} (hx : x ∈ L) : InducesFieldAut 3 J x :=
  inducesFieldAut_of_mem_cq (mem_centralizerQuot_of_ne Nat.prime_three hJ hL hne hx)

theorem not_alt_b (h1910 : Input19_10) (h193 : Input19_1_3) (hty : InputONTypes)
    (hsimple : InputONSimple) {m : ℕ} (hS : GLStanding G m 3) {B' : Subgroup G}
    (hB' : IsElemAbelian 3 B') (hrank : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 B')
    {b : G} (hb : b ∈ B') (hb1 : b ≠ 1) {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) (hON : IsHatON (barOf 3 L)) :
    ∀ D : Subgroup G, IsEkIn 3 2 B' D →
      ⁅L, GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf 3 L := by
  intro D hD
  have := hS.simple
  have hX : Subgroup.centralizer ({b} : Set G) ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hb1
  have hB'X : B' ≤ Subgroup.centralizer ({b} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hB'.1.is_comm.comm ⟨g, hg⟩ ⟨b, hb⟩)
  have hrk : GLATwoLocalRank 3 ↥(Subgroup.centralizer ({b} : Set G)) ≤ CFSG.Open.pRank 3 B' :=
    (glaTwoLocalRank_subgroup_le Nat.prime_three _).trans hrank
  have h4 : 4 ≤ GLATwoLocalRank 3 G := by rw [hS.rank_eq]; exact hS.four_le
  have h2 : 2 ≤ CFSG.Open.pRank 3 B' := by omega
  obtain ⟨-, -, h3⟩ := h1910 G hS.nonabelian hS.kProper 3 Nat.prime_three (by norm_num)
    (Subgroup.centralizer ({b} : Set G)) hX B' hB'X hB' hrk L hL
  rcases h3 h2 with hbal | ⟨h5, -⟩ | ⟨-, hext⟩ | ⟨h5, -⟩
  · exact h193 G hS.nonabelian hS.kProper 3 Nat.prime_three B' hB' 2 (by norm_num) D hD b hb hb1 L
      hL hbal
  · omega
  · obtain ⟨e⟩ := quot_oPrimeP_equiv hsimple hON
    exact absurd hext (hty _ ⟨e⟩).1
  · omega

theorem h31_cases (h31 : Lemma31) (hty : InputONTypes) (hsimple : InputONSimple) {m : ℕ}
    (hS : GLStanding G m 3) {B' : Subgroup G} (hBmax : GLAIsBmax 3 B') (hsc : IsSCp 3 ⊤ B')
    {b : G} (hb : b ∈ B') (hb1 : b ≠ 1) {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) (hON : IsHatON (barOf 3 L)) :
    IsStronglyLocallyOneBalanced 3 B' b L ∨ IsInGOne 3 B' L ∨ Lemma31iv 3 B' L := by
  rcases h31 G m 3 hS B' hBmax hsc b hb hb1 L hL with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨-, -, hL34, -⟩ := h
    obtain ⟨e⟩ := quot_oPrimeP_equiv hsimple hON
    exact absurd hL34 (hty _ ⟨e⟩).2
  · exact Or.inr (Or.inr h)
  · exact absurd h.1 (by norm_num)

theorem le_psiStarGroup_of_inGOne {B' : Subgroup G} {b : G} (hb : b ∈ B') (hb1 : b ≠ 1)
    {L : Subgroup G} (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hnb : ¬ IsStronglyLocallyOneBalanced 3 B' b L) (hG : IsInGOne 3 B' L) :
    L ≤ psiStarGroup 3 B' := by
  have h1 : L ≤ psiOf 3 B' b := le_sSup ⟨hL, hnb, hG⟩
  have h2 : psiOf 3 B' b ≤ psiStar 3 B' b := le_sup_left.trans le_sup_left
  exact h1.trans (h2.trans (le_iSup₂_of_le b hb (le_iSup (fun _ : b ≠ 1 => psiStar 3 B' b) hb1)))

theorem not_balanced_of_le_lambdaOf {B' : Subgroup G} {b : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) (hle : L ≤ lambdaOf 3 B' b) :
    ¬ IsStronglyLocallyOneBalanced 3 B' b L := by
  have := comp_mem_of_le_sSup Nat.prime_three
    {L | GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L ∧
      ¬ IsStronglyLocallyOneBalanced 3 B' b L} (fun J hJ => hJ.1) hL hle
  exact this.2

theorem relIndex_ne_27 {B' U L : Subgroup G} (hB'4 : Nat.card B' = 3 ^ 4) (hBL : B' ≤ Subgroup.normalizer (L : Set G))
    {C : Subgroup G} (hU : U ≤ C) (hUB : U ≤ B') (hU9 : Nat.card U = 9) :
    C.relIndex (B' ⊓ Subgroup.normalizer (L : Set G)) ≠ 27 := by
  intro h
  have hBN : B' ⊓ Subgroup.normalizer (L : Set G) = B' := inf_of_le_left hBL
  rw [hBN, Subgroup.relIndex] at h
  have h2 := Subgroup.card_mul_index (C.subgroupOf B')
  have hc : Nat.card ↥(C.subgroupOf B') = Nat.card ↥(B' ⊓ C) := by
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype _ B',
      Subgroup.card_map_of_injective B'.subtype_injective]
  rw [h, hc, hB'4] at h2
  have := Subgroup.card_le_of_le (le_inf hUB hU : U ≤ B' ⊓ C)
  omega

theorem upsilon_eq_bot (h31 : Lemma31) (h54 : Lemma54) (h1910 : Input19_10)
    (h193 : Input19_1_3) (hty : InputONTypes) (hsimple : InputONSimple) {m : ℕ}
    (hS : GLStanding G m 3) (hC : GLCaseFour G 3)
    {Bs : Subgroup G} (hBs1 : IsBOneMax 3 Bs) (hBsel : IsElemAbelian 3 Bs)
    (hBs4 : Nat.card Bs = 3 ^ 4) {b : G} (hb : b ∈ Bs) (hb1 : b ≠ 1) {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) (hON : IsHatON (barOf 3 L))
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {U B0 : Subgroup G} (hU : U ≤ Bs) (hU9 : Nat.card U = 9)
    (hUCQ : U ≤ centralizerQuot L (GLAPPrimeCoreOf 3 L))
    (hB0 : B0 ≤ Bs ⊓ L) (hB0e : IsElemAbelian 3 B0) (hB0c : Nat.card B0 = 3 ^ 3) :
    upsilonOf Bs b = ⊥ := by
  have hsc : IsSCp 3 ⊤ Bs := lemma23_proved G m 3 hS Bs hBs1
  have hrk : CFSG.Open.pRank 3 Bs = 4 := pRank_eq_of_card Nat.prime_three hBsel hBs4
  have hrank : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 Bs := by rw [hrk, hC.2.1]
  have hB0rk : CFSG.Open.pRank 3 B0 = 3 := pRank_eq_of_card Nat.prime_three hB0e hB0c
  refine sSup_eq_bot.2 fun J hJ => ?_
  exfalso
  by_cases hJL : J = L
  · subst hJL
    rcases hJ.2 with ⟨hle, hnpsi⟩ | ⟨D, hD, hnc⟩
    · have hnb := not_balanced_of_le_lambdaOf hJ.1 hle
      rcases h31_cases h31 hty hsimple hS hBs1.1 hsc hb hb1 hJ.1 hON with h | h | h
      · exact hnb h
      · exact hnpsi (le_psiStarGroup_of_inGOne hb hb1 hJ.1 hnb h)
      · exact relIndex_ne_27 hBs4 hBsN hUCQ hU hU9 h.2.2.2
    · exact hnc (not_alt_b h1910 h193 hty hsimple hS hBsel hrank hb hb1 hJ.1 hON D hD)
  · have hpr := h54 G m hS hC Bs hBs1 b hb hb1 J hJ B0 (fun x hx => (hB0 hx).1)
      (fun a ha => inducesFieldAut_of_ne hJ.1 hL hJL (hB0 ha).2)
    omega

theorem pumpUp_ne_bot {a b : G} {I : Subgroup G}
    (hI : GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) I) (hb3 : b ^ 3 = 1)
    (hbN : b ∈ Subgroup.normalizer (I : Set G))
    (hc : ∀ ℓ ∈ I, ℓ * b * ℓ⁻¹ * b⁻¹ ∈ GLAPPrimeCoreOf 3 I) : pumpUp I b ≠ ⊥ := by
  intro h
  have hle : GLAPLayer 3 (I ⊓ Subgroup.centralizer ({b} : Set G)) ≤ pumpUp I b :=
    le_iSup₂_of_le (1 : G) (one_mem _) (by rw [gLBConj_one])
  exact Lemma56Ns.cover_ne_bot hI hb3 hbN hc (le_bot_iff.1 (hle.trans h.le))

theorem exists_sylow_ge {C B : Subgroup G} (hBC : B ≤ C) (hB3 : IsPGroup 3 B) :
    ∃ R : Subgroup G, IsPGroup 3 R ∧ R ≤ C ∧ B ≤ R ∧
      Nat.card R = 3 ^ (Nat.card C).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB' : IsPGroup 3 (B.subgroupOf C) := by
    intro x
    obtain ⟨k, hk⟩ := hB3 ⟨((x : ↥C) : G), x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨P, hP⟩ := hB'.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup ↥C) = 3 ^ (Nat.card C).factorization 3 :=
    Sylow.card_eq_multiplicity P
  refine ⟨(P : Subgroup ↥C).map C.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact IsPGroup.of_card (n := (Nat.card C).factorization 3)
      (by rw [Subgroup.card_map_of_injective C.subtype_injective, hPcard])
  · intro x hx
    refine ⟨⟨x, hBC hx⟩, hP ((Subgroup.mem_subgroupOf).2 hx), rfl⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hPcard]

theorem exists_card_of_isElemAbelian' {E : Subgroup G} (hE : IsElemAbelian 3 E) :
    ∃ k : ℕ, Nat.card E = 3 ^ k :=
  (isPGroup_of_exp_three hE.2).exists_card_eq


theorem conj_mem_cq {L : Subgroup G} {a w : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hw : w ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L)) :
    a * w * a⁻¹ ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
  have hwN : w ∈ Subgroup.normalizer (L : Set G) := hw.1
  have hN : a * w * a⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hwN) (Subgroup.inv_mem _ ha)
  have h1 : barAut 3 L ⟨w, hwN⟩ = 1 :=
    (mem_centralizerQuot_iff_barAut_aux 3 (J := L) ⟨w, hwN⟩).1 hw
  have h2 : barAut 3 L ⟨a * w * a⁻¹, hN⟩ = 1 := by
    have : (⟨a * w * a⁻¹, hN⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨a, ha⟩ * ⟨w, hwN⟩ * ⟨a, ha⟩⁻¹ :=
      rfl
    rw [this, map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  exact (mem_centralizerQuot_iff_barAut_aux 3 (J := L) ⟨a * w * a⁻¹, hN⟩).2 h2

theorem mem_cq_of_centralizes {L : Subgroup G} {b : G}
    (hLC : L ≤ Subgroup.centralizer ({b} : Set G)) :
    b ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
  have hLb : ∀ ℓ ∈ L, ℓ * b = b * ℓ := fun ℓ hℓ => Subgroup.mem_centralizer_singleton_iff.1 (hLC hℓ)
  have hN : b ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have : ∀ y ∈ L, b * y * b⁻¹ = y := fun y hy => by rw [← hLb y hy]; group
    constructor
    · intro hy; rw [this y hy]; exact hy
    · intro hy
      have h2 : y = b * y * b⁻¹ := by
        calc y = b⁻¹ * (b * y * b⁻¹) * b := by group
          _ = (b * y * b⁻¹) := by
            rw [show b⁻¹ * (b * y * b⁻¹) * b = b⁻¹ * ((b * y * b⁻¹) * b) by group,
              hLb _ hy]; group
      rw [h2]; exact hy
  refine ⟨hN, normalizer_le_normalizer_oPrime hN, fun x hx => ?_⟩
  have : x * b * x⁻¹ * b⁻¹ = 1 := by rw [hLb x hx]; group
  rw [this]; exact one_mem _

theorem W_eq {L : Subgroup G} :
    L ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L) =
      ((Subgroup.center (barOf 3 L)).comap (phiL L)).map L.subtype := by
  ext z
  constructor
  · rintro ⟨hzL, hzcq⟩
    exact ⟨⟨z, hzL⟩, phiL_central_of_cq hzL hzcq.2.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hyc : phiL L y ∈ Subgroup.center (barOf 3 L) := hy
    refine ⟨y.2, Subgroup.le_normalizer y.2,
      normalizer_le_normalizer_oPrime (Subgroup.le_normalizer y.2), fun x hx => ?_⟩
    have h1 : phiL L ⟨x * (y : G) * x⁻¹ * (y : G)⁻¹, L.mul_mem (L.mul_mem (L.mul_mem hx y.2)
        (L.inv_mem hx)) (L.inv_mem y.2)⟩ = 1 := by
      have e : (⟨x * (y : G) * x⁻¹ * (y : G)⁻¹, L.mul_mem (L.mul_mem (L.mul_mem hx y.2)
          (L.inv_mem hx)) (L.inv_mem y.2)⟩ : ↥L) = ⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹ * y⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
      have := Subgroup.mem_center_iff.1 hyc (phiL L ⟨x, hx⟩)
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact this
    exact (phiL_eq_one_iff _).1 h1

theorem card_W {L : Subgroup G} (hL : IsHatON (barOf 3 L)) :
    (Nat.card ↥(L ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L))).factorization 3 = 1 := by
  rw [W_eq, Subgroup.card_map_of_injective L.subtype_injective]
  have h1 := card_comap_mk (GLAPPrimeCore 3 ↥L) (Subgroup.center (barOf 3 L))
  have h2 : Nat.card ↥((Subgroup.center (barOf 3 L)).comap (phiL L)) =
      3 * Nat.card (GLAPPrimeCore 3 ↥L) := by
    have : (Subgroup.center (barOf 3 L)).comap (phiL L) =
        (Subgroup.center (barOf 3 L)).comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) := rfl
    rw [this, h1, hL.2.1]
  rw [h2]
  have h0 : Nat.card (GLAPPrimeCore 3 ↥L) ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_mul (by norm_num) h0]
  simp only [Finsupp.add_apply]
  have hz : (Nat.card (GLAPPrimeCore 3 ↥L)).factorization 3 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    have hcop := coprime_card_gLAPPrimeCore_aux 3 ↥L
    exact Nat.prime_three.ne_one (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 3) hd)
  rw [hz, Nat.Prime.factorization Nat.prime_three]
  simp

theorem fix_of_card_three {q a : G} (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1) (ha3 : a ^ 3 = 1)
    (hinv : a * q * a⁻¹ ∈ Subgroup.zpowers q) : a * q * a⁻¹ = q := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hinv
  have hconj : ∀ k : ℤ, a * q ^ k * a⁻¹ = (a * q * a⁻¹) ^ k := fun k => (conj_zpow).symm
  have e1 : a * q ^ n * a⁻¹ = q ^ (n * n) := by
    rw [hconj, ← hn, ← zpow_mul]
  have e2 : a * q ^ (n * n) * a⁻¹ = q ^ (n * n * n) := by
    rw [hconj, ← hn, ← zpow_mul, mul_assoc]
  have h3 : a * a * a = 1 := by
    have : a ^ 3 = a * a * a := by rw [pow_succ, pow_two]
    rw [← this]; exact ha3
  have e3 : a * (a * (a * q * a⁻¹) * a⁻¹) * a⁻¹ = q := by
    calc a * (a * (a * q * a⁻¹) * a⁻¹) * a⁻¹ = (a * a * a) * q * (a * a * a)⁻¹ := by group
      _ = q := by rw [h3]; group
  rw [← hn, e1, e2] at e3
  have hord : orderOf q = 3 := orderOf_eq_prime hq3 hq1
  have hdvd : (3 : ℤ) ∣ n * n * n - 1 := by
    have : q ^ (n * n * n - 1) = 1 := by
      rw [zpow_sub, e3, zpow_one, mul_inv_cancel]
    have h := orderOf_dvd_iff_zpow_eq_one.2 this
    rw [hord] at h
    exact_mod_cast h
  have hn1 : n % 3 = 1 := by
    have h0 : (n * n * n - 1) % 3 = 0 := Int.emod_eq_zero_of_dvd hdvd
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h | h
    · exfalso
      have : (n * n * n) % 3 = 0 := by simp [Int.mul_emod, h]
      omega
    · exact h
    · exfalso
      have : (n * n * n) % 3 = 2 := by simp [Int.mul_emod, h]
      omega
  rw [← hn]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, n = 3 * k + 1 := ⟨n / 3, by omega⟩
  rw [hk, zpow_add, zpow_mul, zpow_one]
  have : q ^ (3 : ℤ) = 1 := by exact_mod_cast hq3
  rw [this, one_zpow, one_mul]

theorem b_mem_L {L B : Subgroup G} {b : G} (hL : IsHatON (barOf 3 L))
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hBmax : ∀ E : Subgroup G, IsElemAbelian 3 E → B ≤ E → E = B)
    (hLC : L ≤ Subgroup.centralizer ({b} : Set G))
    (hcard : Nat.card ↥(B ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L)) = 3) : b ∈ L := by
  set CQ := centralizerQuot L (GLAPPrimeCoreOf 3 L) with hCQ
  set W : Subgroup G := L ⊓ CQ with hW
  have hB3 : IsPGroup 3 B := isPGroup_of_exp_three hBel.2
  have hbCQ : b ∈ CQ := mem_cq_of_centralizes hLC
  let ψ : ↥B →* MulAut G := MulAut.conj.comp B.subtype
  have hψ : ∀ (a : ↥B) (x : G), ψ a x = (a : G) * x * (a : G)⁻¹ := fun a x => rfl
  have hWinv : ∀ (a : ↥B), ∀ w ∈ W, ψ a w ∈ W := by
    intro a w hw
    rw [hψ]
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hBN a.2) w).1 hw.1, conj_mem_cq (hBN a.2) hw.2⟩
  obtain ⟨Q, hQW, hQcard, hQinv⟩ := exists_fixed_sylow_of_action Nat.prime_three hB3 ψ hWinv
  have hQ3 : Nat.card Q = 3 := by
    rw [hQcard, card_W hL]; norm_num
  obtain ⟨q, hqQ, hq1⟩ : ∃ q ∈ Q, q ≠ 1 := by
    by_contra hh
    push Not at hh
    have : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).2 hh
    rw [this, Subgroup.card_bot] at hQ3
    omega
  have hq3 : q ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Q) (x := (⟨q, hqQ⟩ : ↥Q))
    rw [hQ3] at this
    simpa using congrArg Subtype.val this
  have hQeq : Subgroup.zpowers q = Q := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hqQ)
    rw [Nat.card_zpowers, orderOf_eq_prime hq3 hq1, hQ3]
  have hqcomm : ∀ a ∈ B, a * q = q * a := by
    intro a ha
    have ha3 : a ^ 3 = 1 := hBel.2 a ha
    have h1 : a * q * a⁻¹ ∈ Subgroup.zpowers q := by
      rw [hQeq]; exact hQinv ⟨a, ha⟩ q hqQ
    have := fix_of_card_three hq3 hq1 ha3 h1
    calc a * q = (a * q * a⁻¹) * a := by group
      _ = q * a := by rw [this]
  have hEB : B ⊔ Subgroup.zpowers q = B :=
    hBmax _ (isElemAbelian_sup_zpowers hBel hq3 hqcomm) le_sup_left
  have hqB : q ∈ B := by
    rw [← hEB]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers q)
  have hqW : q ∈ W := hQW hqQ
  have hBCQ : B ⊓ CQ = Subgroup.zpowers b := by
    have hbord : orderOf b = 3 := orderOf_eq_prime (hBel.2 b hbB) hb1
    exact (Subgroup.eq_of_le_of_card_ge (le_inf ((Subgroup.zpowers_le).2 hbB)
      ((Subgroup.zpowers_le).2 hbCQ)) (by rw [hcard, Nat.card_zpowers, hbord])).symm
  have hqb : q ∈ Subgroup.zpowers b := hBCQ ▸ (⟨hqB, hqW.2⟩ : q ∈ B ⊓ CQ)
  have hbq : b ∈ Subgroup.zpowers q := by
    have hq1' : q ≠ 1 := hq1
    have hle : Subgroup.zpowers q ≤ Subgroup.zpowers b := (Subgroup.zpowers_le).2 hqb
    have hbord : orderOf b = 3 := orderOf_eq_prime (hBel.2 b hbB) hb1
    have heq : Subgroup.zpowers q = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hbord, orderOf_eq_prime hq3 hq1])
    rw [heq]; exact Subgroup.mem_zpowers b
  rw [hQeq] at hbq
  exact (hQW hbq).1

theorem card_inf_cq_of_relIndex {B L : Subgroup G} (hBcard : Nat.card B = 3 ^ 4)
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h27 : (centralizerQuot L (GLAPPrimeCoreOf 3 L)).relIndex
      (B ⊓ Subgroup.normalizer (L : Set G)) = 27) :
    Nat.card ↥(B ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L)) = 3 := by
  have hBN' : B ⊓ Subgroup.normalizer (L : Set G) = B := inf_of_le_left hBN
  rw [hBN', Subgroup.relIndex] at h27
  have h2 := Subgroup.card_mul_index ((centralizerQuot L (GLAPPrimeCoreOf 3 L)).subgroupOf B)
  rw [h27, hBcard] at h2
  have hc : Nat.card ↥((centralizerQuot L (GLAPPrimeCoreOf 3 L)).subgroupOf B) =
      Nat.card ↥(B ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L)) := by
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype _ B,
      Subgroup.card_map_of_injective B.subtype_injective]
  rw [hc] at h2
  omega

@[expose] def Gap_Final : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B' : Subgroup G, IsBOneMax 3 B' → ∀ b ∈ B', b ≠ 1 → ∀ L : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L → IsHatON (barOf 3 L) → b ∈ L →
      B' ≤ Subgroup.normalizer (L : Set G) → ∀ a ∈ B', a ≠ 1 → ∀ I : Subgroup G,
        IsUpsilonComponent B' a I → b ∈ centralizerQuot I (GLAPPrimeCoreOf 3 I)

theorem core (h52one : Lemma52One) (h53 : Lemma53) (h54 : Lemma54) (h58 : Lemma58)
    (h56 : Lemma56) (h31 : Lemma31) (hSyl : InputONSylow) (hAut : InputONAut)
    (h2029 : Input20_29) (hsimple : InputONSimple) (hty : InputONTypes)
    (h1910 : Input19_10) (h193 : Input19_1_3) (gF : Gap_Final)
    {m : ℕ} (hS : GLStanding G m 3) (hC : GLCaseFour G 3)
    {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G}
    (hL : IsUpsilonComponent B b L) (hON : IsHatON (barOf 3 L)) : False := by
  have hB1 : IsBOneMax 3 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (le_refl 3) hB
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hBcard : Nat.card B = 3 ^ 4 := by
    have := hB.1.2.1
    rwa [hC.2.1] at this
  have hsc : IsSCp 3 ⊤ B := lemma23_proved G m 3 hS B hB1
  have hBmax : ∀ E : Subgroup G, IsElemAbelian 3 E → B ≤ E → E = B :=
    fun E hE hBE => hsc.2.2 E le_top hE hBE
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := (h56 G m hS hC B hB b hbB hb1).2 L hL
  have hLcomp : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L := hL.1
  have hLC : L ≤ Subgroup.centralizer ({b} : Set G) := hLcomp.1
  have hrankB : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 B := by
    rw [pRank_eq_of_card Nat.prime_three hBel hBcard, hC.2.1]
  have hLa : L ≤ lambdaOf 3 B b ∧ ¬ L ≤ psiStarGroup 3 B := by
    rcases hL.2 with h | ⟨D, hD, hnc⟩
    · exact h
    · exact absurd (not_alt_b h1910 h193 hty hsimple hS hBel hrankB hbB hb1 hLcomp hON D hD) hnc
  have hnb := not_balanced_of_le_lambdaOf hLcomp hLa.1
  have hnG : ¬ IsInGOne 3 B L := fun h =>
    hLa.2 (le_psiStarGroup_of_inGOne hbB hb1 hLcomp hnb h)
  have h31iv : Lemma31iv 3 B L := by
    rcases h31_cases h31 hty hsimple hS hB1.1 hsc hbB hb1 hLcomp hON with h | h | h
    · exact absurd h hnb
    · exact absurd h hnG
    · exact h
  have h27 := h31iv.2.2.2
  have hBcq := card_inf_cq_of_relIndex hBcard hBN h27
  have hbL : b ∈ L := b_mem_L hON hBel hBN hbB hb1 hBmax hLC hBcq
  obtain ⟨R, hR3, hRC, hBR, hRcard⟩ :=
    exists_sylow_ge (C := Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.normalizer (L : Set G))
      (B := B)
      (fun g hg => ⟨by
        show g ∈ Subgroup.centralizer ({b} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hBel.1.is_comm.comm ⟨g, hg⟩ ⟨b, hbB⟩), hBN hg⟩)
      (isPGroup_of_exp_three hBel.2)
  have hRN : R ≤ Subgroup.normalizer (L : Set G) := hRC.trans inf_le_right
  have md := transfer hSyl hAut hON hbL hLC (le_inf hLC Subgroup.le_normalizer) hR3 hRC hRcard hRN
    hBR hBel hBcard hbB hb1 hBmax h27
  obtain ⟨U, hUR1, hUe, hU9, hbU, hUc⟩ := mid_exists_U md
  have hrk : MidRank B (R ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L)) := by
    intro E hE hEle
    obtain ⟨hB0card, hdec, hB0comm, hB0exp, hbB0⟩ := mid_B0 md
    have hAR : B ⊔ (R ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L)) ≤ R :=
      sup_le hBR inf_le_left
    obtain ⟨T, hT0, hT2, hAT⟩ := lift_two h2029
      (A := B ⊔ (R ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L)))
      (B0 := (R ⊓ L) ⊓ (B ⊔ (R ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L)))) (b := b) hON
      (hR3.to_le hAR) (hAR.trans hRN) (inf_le_left.trans inf_le_right) hB0card hB0exp hB0comm
      hbB0 hb1 (fun ℓ hℓ => (Subgroup.mem_centralizer_singleton_iff.1 (hLC hℓ)))
      (fun a ha => by
        obtain ⟨x, hx, hxa⟩ := hdec a ha
        exact ⟨x, hx, hxa.2⟩)
    have hrk := pRank_le_glaTwoLocalRank_of_normalizes Nat.prime_three hT0 hT2 (hEle.trans hAT)
    obtain ⟨k, hk⟩ := exists_card_of_isElemAbelian' hE
    rw [pRank_eq_of_card Nat.prime_three hE hk, hC.2.1] at hrk
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hrk
  obtain ⟨Bs, B0s, hBse, hBs81, hBsle, hBBs, hUBs, hB0s, hB0se, hB0s27⟩ :=
    mid_star md hrk hUR1 hUe hU9 hbU hUc
  have hBsrk : CFSG.Open.pRank 3 Bs = 4 := pRank_eq_of_card Nat.prime_three hBse hBs81
  have hBBsrk : CFSG.Open.pRank 3 (B ⊓ Bs) = 3 := by
    refine pRank_eq_of_card Nat.prime_three (isElemAbelian_mono hBel inf_le_left) hBBs
  have hBs1 : IsBOneMax 3 Bs :=
    (h58 G m hS hC B hB Bs hBse (by rw [hBsrk]) (by rw [hBBsrk])).1
  have hBsR : Bs ≤ R := hBsle.trans (sup_le hBR inf_le_left)
  have hbBs : b ∈ Bs := hUBs hbU
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) := hBsR.trans hRN
  have hup := upsilon_eq_bot h31 h54 h1910 h193 hty hsimple hS hC hBs1 hBse hBs81 hbBs hb1 hLcomp
    hON hBsN hUBs hU9 (hUR1.trans inf_le_right)
    (hB0s.trans (inf_le_inf_left Bs inf_le_right))
    hB0se hB0s27
  obtain ⟨a, haBs, ha1, haup⟩ := h52one G m hS hC Bs hBs1
  obtain ⟨I, hI⟩ : ∃ I, IsUpsilonComponent Bs a I := by
    by_contra hno
    push Not at hno
    exact haup (le_bot_iff.1 (sSup_le fun K hK => absurd hK (hno K)))
  have hbI := gF G m hS hC Bs hBs1 b hbBs hb1 L hLcomp hON hbL hBsN a haBs ha1 I hI
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have h53' := h53 G m hS hC Bs hBs1 a haBs ha1 I hI b hbBs hb1 (inducesFieldAut_of_mem_cq hbI)
  have hpu : pumpUp I b = ⊥ := le_bot_iff.1 (h53'.trans hup.le)
  exact pumpUp_ne_bot hI.1 hb3 hbI.1 hbI.2.2 hpu

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma59Ns

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open Lemma59Ns in
theorem lemma59_of_inputs (h52one : Lemma52One) (h53 : Lemma53) (h54 : Lemma54) (h58 : Lemma58)
    (h56 : Lemma56) (h31 : Lemma31) (hSyl : InputONSylow) (hAut : InputONAut)
    (h2029 : Input20_29) (hsimple : InputONSimple) (hty : InputONTypes)
    (h1910 : Input19_10) (h193 : Input19_1_3) (gF : Gap_Final) : Lemma59 := by
  intro G _ _ m hS hC B hB b hb hb1 L hL hON
  exact core h52one h53 h54 h58 h56 h31 hSyl hAut h2029 hsimple hty h1910 h193 gF hS hC hB hb hb1
    hL hON

end CFSG.HardMathSupport.Solomon.LocalBalance
