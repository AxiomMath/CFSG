module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Parity
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Cover
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Frame

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

section Coprime

variable {G : Type*} [Group G]

theorem rightConjugate_commutator_zpowers (V : Subgroup G) (j c : G) :
    rightConjugate ⁅V, zpowers j⁆ c = ⁅rightConjugate V c, zpowers (c⁻¹ * j * c)⁆ := by
  rw [rightConjugate, Subgroup.map_commutator, MonoidHom.map_zpowers]
  congr 2
  simp

theorem commutator_zpowers_le_of_complement {V P Q : Subgroup G} {j : G}
    (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hPV : P ≤ V) (hQV : Q ≤ V)
    (hjP : ∀ p ∈ P, j * p = p * j) (hjQ : j ∈ normalizer (Q : Set G))
    (hVPQ : ∀ v ∈ V, ∃ p ∈ P, ∃ q ∈ Q, v = p * q) : ⁅V, zpowers j⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro v hv y hy
  obtain ⟨p, hp, q, hq, rfl⟩ := hVPQ v hv
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have hyp : Commute (j ^ k) p := (show Commute j p from hjP p hp).zpow_left k
  have hyQ : j ^ k ∈ normalizer (Q : Set G) := zpow_mem hjQ k
  have h1 : j ^ k * q⁻¹ * (j ^ k)⁻¹ ∈ Q := (mem_normalizer_iff.mp hyQ q⁻¹).mp (inv_mem hq)
  have h2 : q * (j ^ k * q⁻¹ * (j ^ k)⁻¹) ∈ Q := mul_mem hq h1
  have hcomm : p * (q * (j ^ k * q⁻¹ * (j ^ k)⁻¹)) = (q * (j ^ k * q⁻¹ * (j ^ k)⁻¹)) * p :=
    hV _ (hPV hp) _ (hQV h2)
  have e : ⁅p * q, j ^ k⁆ = q * (j ^ k * q⁻¹ * (j ^ k)⁻¹) := by
    rw [commutatorElement_def]
    calc p * q * j ^ k * (p * q)⁻¹ * (j ^ k)⁻¹
        = p * (q * (j ^ k * q⁻¹ * (j ^ k)⁻¹)) * (j ^ k * p⁻¹ * (j ^ k)⁻¹) := by group
      _ = (q * (j ^ k * q⁻¹ * (j ^ k)⁻¹)) * p * (j ^ k * p⁻¹ * (j ^ k)⁻¹) := by rw [hcomm]
      _ = q * (j ^ k * q⁻¹ * (j ^ k)⁻¹) := by
          rw [show j ^ k * p⁻¹ * (j ^ k)⁻¹ = p⁻¹ by rw [hyp.inv_right.eq, mul_inv_cancel_right],
            mul_inv_cancel_right]
  rw [e]
  exact h2

theorem le_commutator_zpowers_of_fixedPointFree {V Q : Subgroup G} [Finite Q] {j : G}
    (hQV : Q ≤ V) (hjQ : j ∈ normalizer (Q : Set G))
    (hfree : ∀ q ∈ Q, j * q = q * j → q = 1) : Q ≤ ⁅V, zpowers j⁆ := by
  let δ : Q → Q := fun q => ⟨⁅(q : G), j⁆, by
    rw [commutatorElement_def]
    have h1 : j * (q : G)⁻¹ * j⁻¹ ∈ Q := (mem_normalizer_iff.mp hjQ _).mp (inv_mem q.2)
    have := mul_mem q.2 h1
    rwa [show (q : G) * (j * (q : G)⁻¹ * j⁻¹) = (q : G) * j * (q : G)⁻¹ * j⁻¹ by group]
      at this⟩
  have hδ : Function.Injective δ := by
    intro a b hab
    have h := congrArg Subtype.val hab
    simp only [δ] at h
    rw [commutatorElement_def, commutatorElement_def] at h
    have hu : j * ((b : G)⁻¹ * a) = ((b : G)⁻¹ * a) * j := by
      have h' : (b : G)⁻¹ * a * j * (a : G)⁻¹ = j * (b : G)⁻¹ := by
        calc (b : G)⁻¹ * a * j * (a : G)⁻¹
            = (b : G)⁻¹ * ((a : G) * j * (a : G)⁻¹ * j⁻¹) * j := by group
          _ = (b : G)⁻¹ * ((b : G) * j * (b : G)⁻¹ * j⁻¹) * j := by rw [h]
          _ = j * (b : G)⁻¹ := by group
      calc j * ((b : G)⁻¹ * a) = ((b : G)⁻¹ * a * j * (a : G)⁻¹) * a := by rw [h']; group
        _ = ((b : G)⁻¹ * a) * j := by group
    have h1 := hfree _ (mul_mem (inv_mem b.2) a.2) hu
    rw [inv_mul_eq_one] at h1
    exact Subtype.ext h1.symm
  have hsurj : Function.Surjective δ := Finite.injective_iff_surjective.mp hδ
  intro q hq
  obtain ⟨a, ha⟩ := hsurj ⟨q, hq⟩
  have h := congrArg Subtype.val ha
  simp only [δ] at h
  rw [← h]
  exact commutator_mem_commutator (hQV a.2) (mem_zpowers j)

theorem le_of_commutator_zpowers_le {V P : Subgroup G} {j : G} {n : ℕ} (hj : j ^ 3 ^ n = 1)
    (hV2 : ∀ v ∈ V, v * v = 1) (hPV : P ≤ V) (hjP : ∀ p ∈ P, j * p = p * j)
    (hCP : ∀ v ∈ V, j * v = v * j → v ∈ P) (hle : ⁅V, zpowers j⁆ ≤ P) : V ≤ P := by
  intro v hv
  apply hCP v hv
  have hvi : v⁻¹ ∈ V := inv_mem hv
  have hc : ⁅v⁻¹, j⁆ ∈ P := hle (commutator_mem_commutator hvi (mem_zpowers j))
  set p := ⁅v⁻¹, j⁆ with hp
  have hjv : j * v * j⁻¹ = v * p := by
    rw [hp, commutatorElement_def]
    group
  have hjp : j * p * j⁻¹ = p := by rw [hjP p hc, mul_inv_cancel_right]
  have hpp : p * p = 1 := hV2 p (hPV hc)
  have hj2 : j ^ 2 * v * (j ^ 2)⁻¹ = v := by
    calc j ^ 2 * v * (j ^ 2)⁻¹ = j * (j * v * j⁻¹) * j⁻¹ := by rw [sq, mul_inv_rev]; group
      _ = j * (v * p) * j⁻¹ := by rw [hjv]
      _ = (j * v * j⁻¹) * (j * p * j⁻¹) := by group
      _ = v * p * p := by rw [hjv, hjp]
      _ = v := by rw [mul_assoc, hpp, mul_one]
  have hcomm : Commute (j ^ 2) v := by
    show j ^ 2 * v = v * j ^ 2
    calc j ^ 2 * v = (j ^ 2 * v * (j ^ 2)⁻¹) * j ^ 2 := by group
      _ = v * j ^ 2 := by rw [hj2]
  have hpow : (j ^ 2) ^ ((3 ^ n + 1) / 2) = j := by
    have hodd : Odd (3 ^ n) := Odd.pow (by decide)
    obtain ⟨m, hm⟩ := hodd
    have h1 : (3 ^ n + 1) / 2 = m + 1 := by omega
    rw [h1, ← pow_mul]
    have h2 : 2 * (m + 1) = 3 ^ n + 1 := by omega
    rw [h2, pow_succ, hj, one_mul]
  have := (hcomm.pow_left ((3 ^ n + 1) / 2)).eq
  rwa [hpow] at this

theorem commutator_zpowers_le_of_act [Finite G] {V : Subgroup G} {y z : G}
    (hzV : z ∈ normalizer (V : Set G))
    (hact : ∀ v ∈ V, y⁻¹ * v * y = z⁻¹ * v * z) : ⁅V, zpowers y⁆ ≤ ⁅V, zpowers z⁆ := by
  have hact' : ∀ v ∈ V, y * v * y⁻¹ = z * v * z⁻¹ := by
    intro v hv
    have hw : z * v * z⁻¹ ∈ V := (mem_normalizer_iff.mp hzV v).mp hv
    have h1 := hact _ hw
    have h2 : z⁻¹ * (z * v * z⁻¹) * z = v := by group
    rw [h2] at h1
    calc y * v * y⁻¹ = y * (y⁻¹ * (z * v * z⁻¹) * y) * y⁻¹ := by rw [h1]
      _ = z * v * z⁻¹ := by group
  have hpow : ∀ m : ℕ, ∀ v ∈ V, y ^ m * v * (y ^ m)⁻¹ = z ^ m * v * (z ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro v _; simp
    | succ m ih =>
      intro v hv
      have hw : z * v * z⁻¹ ∈ V := (mem_normalizer_iff.mp hzV v).mp hv
      calc y ^ (m + 1) * v * (y ^ (m + 1))⁻¹ = y ^ m * (y * v * y⁻¹) * (y ^ m)⁻¹ := by
            rw [pow_succ, mul_inv_rev]; group
        _ = y ^ m * (z * v * z⁻¹) * (y ^ m)⁻¹ := by rw [hact' v hv]
        _ = z ^ m * (z * v * z⁻¹) * (z ^ m)⁻¹ := ih _ hw
        _ = z ^ (m + 1) * v * (z ^ (m + 1))⁻¹ := by rw [pow_succ, mul_inv_rev]; group
  rw [Subgroup.commutator_le]
  intro v hv w hw
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hw
  obtain ⟨m, rfl⟩ := hw
  have e : ⁅v, y ^ m⁆ = ⁅v, z ^ m⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    have h := hpow m _ (inv_mem hv)
    calc v * y ^ m * v⁻¹ * (y ^ m)⁻¹ = v * (y ^ m * v⁻¹ * (y ^ m)⁻¹) := by group
      _ = v * (z ^ m * v⁻¹ * (z ^ m)⁻¹) := by rw [h]
      _ = v * z ^ m * v⁻¹ * (z ^ m)⁻¹ := by group
  rw [e]
  exact commutator_mem_commutator hv (pow_mem (mem_zpowers z) m)

end Coprime

section Count

variable {G : Type} [Group G] [Finite G]

theorem card_mul_le_of_pairwise_inf_eq_bot {V : Subgroup G} {Pts : Set (Subgroup G)} {m : ℕ}
    (hle : ∀ Q ∈ Pts, Q ≤ V) (hcard : ∀ Q ∈ Pts, Nat.card Q = m)
    (hdisj : ∀ Q₁ ∈ Pts, ∀ Q₂ ∈ Pts, Q₁ ≠ Q₂ → Q₁ ⊓ Q₂ = ⊥) :
    Nat.card Pts * (m - 1) ≤ Nat.card V - 1 := by
  classical
  have := Fintype.ofFinite G
  let S : Finset (Subgroup G) := (Set.toFinite Pts).toFinset
  let t : Subgroup G → Finset G := fun Q => ((Q : Set G).toFinset).erase 1
  have ht : ∀ Q ∈ S, (t Q).card = m - 1 := by
    intro Q hQ
    have hQ' : Q ∈ Pts := (Set.Finite.mem_toFinset _).mp hQ
    rw [Finset.card_erase_of_mem (by simp), Set.toFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
    rw [← hcard Q hQ']
    rfl
  have hpair : (S : Set (Subgroup G)).PairwiseDisjoint t := by
    intro Q₁ hQ₁ Q₂ hQ₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [t, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hx₁ hx₂
    have h := hdisj Q₁ ((Set.Finite.mem_toFinset _).mp hQ₁) Q₂ ((Set.Finite.mem_toFinset _).mp hQ₂)
      hne
    have hx : x ∈ Q₁ ⊓ Q₂ := ⟨hx₁.2, hx₂.2⟩
    rw [h, mem_bot] at hx
    exact hx₁.1 hx
  have hsub : S.biUnion t ⊆ ((V : Set G).toFinset).erase 1 := by
    intro x hx
    simp only [Finset.mem_biUnion, t, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hx ⊢
    obtain ⟨Q, hQ, hx1, hxQ⟩ := hx
    exact ⟨hx1, hle Q ((Set.Finite.mem_toFinset _).mp hQ) hxQ⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion hpair, Finset.sum_congr rfl ht, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (by simp), Set.toFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at h1
  have hS : S.card = Nat.card Pts := by
    rw [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card]
  have hV : Nat.card V = (V : Set G).ncard := Nat.card_coe_set_eq (V : Set G)
  rw [← hS, hV]
  exact h1

end Count

section Line

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem mem_normalizer_centerIn {H : Subgroup G} {c : G} (hc : c ∈ normalizer (H : Set G)) :
    c ∈ normalizer (centerIn H : Set G) := by
  apply mem_normalizer_fintype
  intro n hn
  have hn' : n ∈ centerIn H := hn
  refine ⟨(mem_normalizer_iff.mp hc n).mp (mem_inf.mp hn').1, ?_⟩
  show c * n * c⁻¹ ∈ centralizer (H : Set G)
  rw [mem_centralizer_iff]
  intro h hh
  have hh' : c⁻¹ * h * c ∈ H := (mem_normalizer_iff''.mp hc h).mp hh
  have hcomm := mem_centralizer_iff.mp (mem_inf.mp hn').2 _ hh'
  calc h * (c * n * c⁻¹) = c * ((c⁻¹ * h * c) * n) * c⁻¹ := by group
    _ = c * (n * (c⁻¹ * h * c)) * c⁻¹ := by rw [hcomm]
    _ = c * n * c⁻¹ * h := by group

theorem exists_point_data {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) {P : Subgroup G}
    (hP : P ∈ pointsIn R (E ⊓ F)) :
    ∃ A' : Subgroup G, ∃ j : G, j ∈ A' ∧ P ≤ centralizer (A' : Set G) ∧
      normalizer (P : Set G) ≤ normalizer (A' : Set G) ∧ (∃ n : ℕ, j ^ 3 ^ n = 1) ∧
      j ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) ∧ (∀ v ∈ E ⊓ F, j * v = v * j → v ∈ P) ∧
      ∀ y ∈ A', y ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) → ∃ k : ℕ, ∀ v ∈ E ⊓ F,
        y⁻¹ * v * y = (j ^ k)⁻¹ * v * j ^ k := by
  obtain ⟨hPV, x, rfl⟩ := hP
  have key : ∀ (A₀ Q : Subgroup G) (g₀ : G), Frame G A₀ A₀ Q g₀ E F → TypeL34 (rankTwoQuot A₀) →
      ∃ A' : Subgroup G, ∃ j : G, j ∈ A' ∧ Q ≤ centralizer (A' : Set G) ∧
        normalizer (Q : Set G) ≤ normalizer (A' : Set G) ∧ (∃ n : ℕ, j ^ 3 ^ n = 1) ∧
        j ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) ∧
        (∀ v ∈ E ⊓ F, j * v = v * j → v ∈ Q) ∧
        ∀ y ∈ A', y ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) → ∃ k : ℕ, ∀ v ∈ E ⊓ F,
          y⁻¹ * v * y = (j ^ k)⁻¹ * v * j ^ k := by
    intro A₀ Q g₀ hF₀ hL₀
    obtain ⟨j, hjA, hj3, hjN, hjC, hjB⟩ := exists_torus_frame h11 hF₀ hL₀
    have hstd₀ := hF₀.base.hyp.standard
    have hQ1 : Q ≠ ⊥ := by
      intro h
      have := hF₀.cardR
      rw [h, Subgroup.card_bot] at this
      omega
    have hN : normalizer (Q : Set G) ≤ normalizer (A₀ : Set G) := by
      rw [← AS76b.normalizer_centralizer_eq hstd₀]
      exact normalizer_two_subgroup_le _ _ (AS76b.tightlyEmbedded_centralizer hstd₀)
        hF₀.sylowR.isPGroup hF₀.sylowR.le hQ1
    exact ⟨A₀, j, hjA, hF₀.sylowR.le, hN, hj3, hjN, hjC, hjB⟩
  by_cases hx : rightConjugate R x = R
  · rw [hx]
    exact key A R g hF hL
  · exact key _ _ _ (frame_at_point hE16 hF hL hPV hx) (typeL34_rightConjugate x hL)

theorem card_pointsIn_inf {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) :
    Nat.card (pointsIn R (E ⊓ F)) = 2 ∨ Nat.card (pointsIn R (E ⊓ F)) = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := E ⊓ F with hVdef
  set Pts := pointsIn R V with hPtsdef
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hcommE a ha.1 b hb.1
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := hF.elemE.2 v hv.1
    rwa [sq] at this
  have hVcard : Nat.card V = 16 := card_inf_of_frame hF
  have hVEF : V = centerIn (E ⊔ F) := hF.inf_eq_center
  have hPtsV : ∀ Q ∈ Pts, Q ≤ V := fun Q hQ => hQ.1
  have hPtscard : ∀ Q ∈ Pts, Nat.card Q = 4 := by
    rintro Q ⟨-, x, rfl⟩
    rw [rightConjugate_card, hF.cardR]
  have hPtsdisj : ∀ Q₁ ∈ Pts, ∀ Q₂ ∈ Pts, Q₁ ≠ Q₂ → Q₁ ⊓ Q₂ = ⊥ := fun Q₁ h₁ Q₂ h₂ hne =>
    inf_eq_bot_of_mem_pointsIn hKte hF.sylowR hVab h₁ h₂ hne
  have hdata : ∀ P ∈ Pts, ∃ A' : Subgroup G, ∃ j : G, j ∈ A' ∧ P ≤ centralizer (A' : Set G) ∧
      normalizer (P : Set G) ≤ normalizer (A' : Set G) ∧ (∃ n : ℕ, j ^ 3 ^ n = 1) ∧
      j ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) ∧ (∀ v ∈ V, j * v = v * j → v ∈ P) ∧
      ∀ y ∈ A', y ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) → ∃ k : ℕ, ∀ v ∈ V,
        y⁻¹ * v * y = (j ^ k)⁻¹ * v * j ^ k :=
    fun P hP => exists_point_data hE16 h11 hF hL hP
  choose! A' j hjA hPC hNA hj3 hjEF hCV hact using hdata
  have hNV : ∀ c ∈ normalizer ((E ⊔ F : Subgroup G) : Set G), c ∈ normalizer (V : Set G) :=
    fun c hc => hVEF ▸ mem_normalizer_centerIn hc
  have hjV : ∀ P ∈ Pts, j P ∈ normalizer (V : Set G) := fun P hP => hNV _ (hjEF P hP)
  have hjP : ∀ P ∈ Pts, ∀ p ∈ P, j P * p = p * j P := fun P hP p hp =>
    mem_centralizer_iff.mp (hPC P hP hp) _ (hjA P hP)
  set ζ : Subgroup G → Subgroup G := fun P => ⁅V, zpowers (j P)⁆ with hζ
  have hperm : ∀ P ∈ Pts, ∀ Q ∈ Pts, rightConjugate Q (j P) ∈ Pts := by
    rintro P hP Q ⟨hQV, y, rfl⟩
    refine ⟨?_, y * j P, rightConjugate_mul R y (j P)⟩
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hQV (j P)
    rwa [(rightConjugate_eq_self_iff V (j P)).mpr (hjV P hP)] at h1
  have hjζ : ∀ P ∈ Pts, j P ∈ normalizer (ζ P : Set G) := by
    intro P hP
    rw [← rightConjugate_eq_self_iff, hζ]
    dsimp only
    rw [rightConjugate_commutator_zpowers, (rightConjugate_eq_self_iff V (j P)).mpr (hjV P hP),
      show (j P)⁻¹ * j P * j P = j P by group]
  have hne : ∀ P ∈ Pts, ζ P ≠ P := by
    intro P hP h
    obtain ⟨n, hn⟩ := hj3 P hP
    have hle := le_of_commutator_zpowers_le hn hV2 (hPtsV P hP) (hjP P hP) (hCV P hP)
      (le_of_eq h)
    have := Subgroup.card_le_of_le hle
    rw [hVcard, hPtscard P hP] at this
    omega
  have hdecomp : ∀ P ∈ Pts, ∀ Q ∈ Pts, P ≠ Q → ∀ v ∈ V, ∃ p ∈ P, ∃ q ∈ Q, v = p * q := by
    intro P hP Q hQ hPQ v hv
    have hN : P ≤ normalizer (Q : Set G) := fun p hp =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun q hq =>
        hVab q (hPtsV Q hQ hq) p (hPtsV P hP hp))
    have hcard := card_sup_mul_card_inf hN
    rw [hPtsdisj Q hQ P hP (Ne.symm hPQ), Subgroup.card_bot, mul_one,
      hPtscard P hP, hPtscard Q hQ] at hcard
    have hsup : P ⊔ Q = V := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le (hPtsV P hP) (hPtsV Q hQ)) ?_
      rw [sup_comm, hcard, hVcard]
    have hv' : v ∈ ((P ⊔ Q : Subgroup G) : Set G) := by rw [hsup]; exact hv
    rw [coe_mul_of_left_le_normalizer_right P Q hN] at hv'
    obtain ⟨p, hp, q, hq, rfl⟩ := hv'
    exact ⟨p, hp, q, hq, rfl⟩
  have hfix : ∀ P ∈ Pts, ∀ Q ∈ Pts, j P ∈ normalizer (Q : Set G) → Q = P ∨ Q = ζ P := by
    intro P hP Q hQ hjQ
    by_cases hQP : Q = P
    · exact Or.inl hQP
    · right
      have hinf : P ⊓ Q = ⊥ := hPtsdisj P hP Q hQ (Ne.symm hQP)
      refine le_antisymm ?_ (commutator_zpowers_le_of_complement hVab (hPtsV P hP) (hPtsV Q hQ)
        (hjP P hP) hjQ (hdecomp P hP Q hQ (Ne.symm hQP)))
      refine le_commutator_zpowers_of_fixedPointFree (hPtsV Q hQ) hjQ fun q hq hjq => ?_
      have hqP := hCV P hP q (hPtsV Q hQ hq) hjq
      have hq' : q ∈ P ⊓ Q := ⟨hqP, hq⟩
      rwa [hinf, mem_bot] at hq'
  have hcomp : ∀ P ∈ Pts, ∀ Q ∈ Pts, j P ∈ normalizer (Q : Set G) →
      j P ∈ normalizer (ζ Q : Set G) := by
    intro P hP Q hQ hjQ
    set c := j P
    have hcA : c ∈ normalizer (A' Q : Set G) := hNA Q hQ hjQ
    have hj'A : c⁻¹ * j Q * c ∈ A' Q := (mem_normalizer_iff''.mp hcA (j Q)).mp (hjA Q hQ)
    have hj'EF : c⁻¹ * j Q * c ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) :=
      mul_mem (mul_mem (inv_mem (hjEF P hP)) (hjEF Q hQ)) (hjEF P hP)
    obtain ⟨k, hk⟩ := hact Q hQ _ hj'A hj'EF
    have hle : ⁅V, zpowers (c⁻¹ * j Q * c)⁆ ≤ ζ Q :=
      (commutator_zpowers_le_of_act (pow_mem (hjV Q hQ) k) hk).trans
        (Subgroup.commutator_mono le_rfl (zpowers_le.mpr (pow_mem (mem_zpowers _) k)))
    have hconj : rightConjugate (ζ Q) c = ⁅V, zpowers (c⁻¹ * j Q * c)⁆ := by
      rw [hζ]
      dsimp only
      rw [rightConjugate_commutator_zpowers, (rightConjugate_eq_self_iff V c).mpr (hjV P hP)]
    rw [← rightConjugate_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge (hconj ▸ hle) ?_
    rw [rightConjugate_card]
  have hR : R ∈ Pts := self_mem_pointsIn (le_inf hF.R_le_E hF.R_le_F)
  have hRg : rightConjugate R g ∈ Pts :=
    ⟨by rw [hVdef, hF.inf_eq]; exact le_sup_right, g, rfl⟩
  have hRne : R ≠ rightConjugate R g := by
    intro h
    have h1 : V = R := by rw [hVdef, hF.inf_eq, ← h, sup_idem]
    have := hVcard
    rw [h1, hF.cardR] at this
    omega
  have hcard2 : 2 ≤ Nat.card Pts := by
    have hsub : ({R, rightConjugate R g} : Set (Subgroup G)) ⊆ Pts := by
      rintro Q (rfl | rfl)
      · exact hR
      · exact hRg
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite Pts)
    rw [Set.ncard_pair hRne] at h1
    rwa [← Nat.card_coe_set_eq] at h1
  have hcard5 : Nat.card Pts ≤ 5 := by
    have h := card_mul_le_of_pairwise_inf_eq_bot hPtsV hPtscard hPtsdisj
    rw [hVcard] at h
    omega
  obtain ⟨n, hn⟩ := hj3 R hR
  have hmod := card_modEq_card_normalized hn (hperm R hR)
  have hjRR : j R ∈ normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr => (hjP R hR r hr).symm)
  set S := {Q : Pts // j R ∈ normalizer ((Q : Subgroup G) : Set G)}
  have hS1 : 1 ≤ Nat.card S := by
    have : Nonempty S := ⟨⟨⟨R, hR⟩, hjRR⟩⟩
    exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hS2 : Nat.card S ≤ 2 := by
    let f : S → Fin 2 := fun Q => if (Q : Pts).1 = R then 0 else 1
    have hf : Function.Injective f := by
      intro Q₁ Q₂ h
      have key : ∀ Q : S, (Q : Pts).1 = R ∨ (Q : Pts).1 = ζ R := fun Q =>
        hfix R hR Q.1.1 Q.1.2 Q.2
      apply Subtype.ext
      apply Subtype.ext
      rcases key Q₁ with h₁ | h₁ <;> rcases key Q₂ with h₂ | h₂
      · rw [h₁, h₂]
      · have : (Q₂ : Pts).1 ≠ R := by rw [h₂]; exact hne R hR
        simp [f, h₁, this] at h
      · have : (Q₁ : Pts).1 ≠ R := by rw [h₁]; exact hne R hR
        simp [f, h₂, this] at h
      · rw [h₁, h₂]
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hmod' : Nat.card Pts % 3 = Nat.card S % 3 := hmod
  rcases (show Nat.card S = 1 ∨ Nat.card S = 2 by omega) with hS | hS
  · right
    rw [hS] at hmod'
    omega
  · left
    rw [hS] at hmod'
    have heven := even_card_of_parity j ζ hj3 hperm hjζ hne hfix hcomp (by omega)
    obtain ⟨m, hm⟩ := heven
    omega

end Line

end CFSG.ComponentClassification.AS81
