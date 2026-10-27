module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open
open scoped commutatorElement

variable {Q : Type*} [Group Q] [Finite Q]

namespace QGroup

open CFSG.LieType.BorelTits

theorem pCoreOf_eq_bot_of_normal
    (hO : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) {N : Subgroup Q} (hN : N.Normal) :
    pCoreOf 2 N = ⊥ := by
  have h1 : Subgroup.normalizer (N : Set Q) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hN
  have h2 := normalizer_le_normalizer_pCoreOf 2 N
  rw [h1, top_le_iff] at h2
  exact hO _ (Subgroup.normalizer_eq_top_iff.mp h2) (pCoreOf_isPGroup 2 N)

theorem eq_bot_of_le_of_le_normalizer
    (hO : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) {A N : Subgroup Q}
    (hN : N.Normal) (hAN : A ≤ N) (hnorm : N ≤ Subgroup.normalizer (A : Set Q))
    (hA : IsPGroup 2 A) : A = ⊥ := by
  have h := le_pCoreOf_of_le_normalizer 2 hAN hnorm hA
  rw [pCoreOf_eq_bot_of_normal hO hN] at h
  exact le_bot_iff.mp h

theorem pCoreOf_eq_bot_of_le_normalizer
    (hO : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) {K W : Subgroup Q}
    (hW : W.Normal) (hKW : K ≤ W) (hWK : W ≤ Subgroup.normalizer (K : Set Q)) :
    pCoreOf 2 K = ⊥ :=
  eq_bot_of_le_of_le_normalizer hO hW ((pCoreOf_le 2 K).trans hKW)
    (hWK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)

theorem odd_card_of_pCore_eq_bot {G : Type*} [Group G] [Finite G] (hG : Group.IsNilpotent G)
    (h : CFSG.pCore 2 G = ⊥) : Odd (Nat.card G) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro hdvd
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 G))
  haveI := hG
  have hP : (P : Subgroup G) ≤ CFSG.pCore 2 G := le_pCore 2 inferInstance P.isPGroup'
  rw [h] at hP
  exact P.ne_bot_of_dvd_card hdvd (le_bot_iff.mp hP)

theorem odd_card_of_isNilpotent
    (hO : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) {K W : Subgroup Q}
    (hW : W.Normal) (hKW : K ≤ W) (hWK : W ≤ Subgroup.normalizer (K : Set Q))
    (hnil : Group.IsNilpotent ↥K) : Odd (Nat.card K) := by
  have h := pCoreOf_eq_bot_of_le_normalizer hO hW hKW hWK
  refine odd_card_of_pCore_eq_bot hnil ?_
  unfold pCoreOf at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp h

theorem eq_bot_of_isPGroup_of_odd {A : Subgroup Q} (hA : IsPGroup 2 A)
    (hodd : Odd (Nat.card A)) : A = ⊥ := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
  rcases n with _ | n
  · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hn)
  · rw [hn, pow_succ] at hodd
    exact absurd (even_two.mul_left _) (Nat.not_even_iff_odd.mpr hodd)

theorem mem_of_pow_two_pow_mem {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G))
    (S : Subgroup G) {g : G} {k : ℕ} (h : g ^ (2 ^ k) ∈ S) : g ∈ S := by
  have hc : (Nat.card G).Coprime (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_left.mpr hodd).symm
  have key := (powCoprime hc).symm_apply_apply g
  rw [powCoprime_apply, powCoprime_symm_apply] at key
  rw [← key]
  exact S.zpow_mem h _

theorem card_sup_mul_card_inf_of_normal {X : Type*} [Group X] (A B : Subgroup X) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer {X : Type*} [Group X] {A B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set X)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N :=
    (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  exact h

theorem isSolvable_sup_of_le_normalizer {A B : Subgroup Q} (hA : Group.IsSolvable ↥A)
    (hB : Group.IsSolvable ↥B) (hBA : B ≤ Subgroup.normalizer (A : Set Q)) :
    Group.IsSolvable ↥(A ⊔ B) := by
  have hAK : A ≤ A ⊔ B := le_sup_left
  have hn : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).2 (sup_le Subgroup.le_normalizer hBA)
  set f : ↥B →* ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_right) with hf
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hk' : k ∈ ((B ⊔ A : Subgroup Q) : Set Q) := by rwa [sup_comm]
    rw [Subgroup.coe_mul_of_left_le_normalizer_right B A hBA] at hk'
    obtain ⟨b, hb, a, ha, rfl⟩ := hk'
    refine ⟨⟨b, hb⟩, ?_⟩
    change (QuotientGroup.mk' _ (Subgroup.inclusion le_sup_right ⟨b, hb⟩) :
      ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) = QuotientGroup.mk ⟨b * a, hk⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using ha
  have : Group.IsSolvable (↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_surjective hfs
  have : Group.IsSolvable ↥(A.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hAK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAK).injective
  exact Group.isSolvable_of_ker_le_range (A.subgroupOf (A ⊔ B)).subtype
    (QuotientGroup.mk' (A.subgroupOf (A ⊔ B)))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isNilpotent_of_commutator_central {K : Subgroup Q}
    (h : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, c * ⁅a, b⁆ = ⁅a, b⁆ * c) : Group.IsNilpotent ↥K := by
  refine Subgroup.isNilpotent_of_ker_le_center (Abelianization.of : ↥K →* Abelianization ↥K) ?_
  rw [Abelianization.ker_of]
  show ⁅(⊤ : Subgroup ↥K), ⊤⁆ ≤ _
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_center_iff]
  intro c
  exact Subtype.ext (h a a.2 b b.2 c c.2)

theorem le_centralizer_of_forall_commute {T X : Subgroup Q}
    (hTX : ∀ t ∈ T, ∀ x ∈ X, t * x = x * t) : T ≤ Subgroup.centralizer (X : Set Q) :=
  fun t ht => Subgroup.mem_centralizer_iff.mpr fun x hx => (hTX t ht x hx).symm

theorem commutator_eq_bot_of_commutator_le
    (hO : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥)
    {T X W : Subgroup Q} (hT : IsPGroup 2 T) (hW : W.Normal) (hX : X.Normal) (hXW : X ≤ W)
    (hTX : ∀ t ∈ T, ∀ x ∈ X, t * x = x * t) (hTW : ⁅T, W⁆ ≤ X) : ⁅T, W⁆ = ⊥ := by
  haveI := hW
  haveI := hX
  have hXT : ⁅T, X⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_of_forall_commute hTX)
  have hYT : T ⊔ X ≤ Subgroup.normalizer (T : Set Q) := by
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.le_normalizer_iff_commutator_le_left, hXT]
    exact bot_le
  have hWY : W ≤ Subgroup.normalizer ((T ⊔ X : Subgroup Q) : Set Q) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left, Subgroup.commutator_sup_right]
    exact sup_le (hTW.trans le_sup_right)
      ((Subgroup.commutator_le_left X W).trans le_sup_right)
  have hTK : T ≤ pCoreOf 2 (T ⊔ X) := le_pCoreOf_of_le_normalizer 2 le_sup_left hYT hT
  have hWK : W ≤ Subgroup.normalizer (pCoreOf 2 (T ⊔ X) : Set Q) :=
    hWY.trans (normalizer_le_normalizer_pCoreOf 2 (T ⊔ X))
  have hKcomm : ⁅pCoreOf 2 (T ⊔ X), W⁆ ≤ pCoreOf 2 (T ⊔ X) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hWK
  have hle : ⁅T, W⁆ ≤ pCoreOf 2 (T ⊔ X) ⊓ W :=
    le_inf ((Subgroup.commutator_mono_left hTK).trans hKcomm) (Subgroup.commutator_le_right T W)
  have hbot : pCoreOf 2 (T ⊔ X) ⊓ W = ⊥ := by
    refine eq_bot_of_le_of_le_normalizer hO hW inf_le_right ?_
      ((pCoreOf_isPGroup 2 (T ⊔ X)).to_le inf_le_left)
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact le_inf ((Subgroup.commutator_mono_left inf_le_left).trans hKcomm)
      (Subgroup.commutator_le_right _ W)
  rw [hbot] at hle
  exact le_bot_iff.mp hle

theorem commutator_eq_bot_of_pGroup_quotient
    (hO : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥)
    {T X W : Subgroup Q} (hT : IsPGroup 2 T) (hW : W.Normal) (hX : X.Normal) (hXW : X ≤ W)
    (hTX : ∀ t ∈ T, ∀ x ∈ X, t * x = x * t) (hB : ∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) ∈ X) :
    ⁅T, W⁆ = ⊥ := by
  haveI := hW
  haveI := hX
  refine commutator_eq_bot_of_commutator_le hO hT hW hX hXW hTX ?_
  have hTc := le_centralizer_of_forall_commute hTX
  have hYN : (W ⊓ Subgroup.centralizer (X : Set Q)).Normal := inferInstance
  refine ((le_inf (Subgroup.commutator_le_right T W)
    ((Subgroup.commutator_mono_left hTc).trans
      (Subgroup.commutator_le_left (Subgroup.centralizer (X : Set Q)) W))) :
      ⁅T, W⁆ ≤ W ⊓ Subgroup.centralizer (X : Set Q)).trans ?_
  set Y : Subgroup Q := W ⊓ Subgroup.centralizer (X : Set Q) with hY
  have hYW : Y ≤ W := inf_le_left
  have hYC : Y ≤ Subgroup.centralizer (X : Set Q) := inf_le_right
  have hZc : X.subgroupOf Y ≤ Subgroup.center ↥Y := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hYC g.2) (z : Q) (Subgroup.mem_subgroupOf.mp hz)).symm
  haveI : (X.subgroupOf Y).Normal := Subgroup.normal_of_le_center hZc
  have hq : IsPGroup 2 (↥Y ⧸ X.subgroupOf Y) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨k, hk⟩ := hB y (hYW y.2)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  haveI : Group.IsNilpotent (↥Y ⧸ X.subgroupOf Y) := hq.isNilpotent
  have hnil : Group.IsNilpotent ↥Y :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (X.subgroupOf Y))
      (by rw [QuotientGroup.ker_mk']; exact hZc)
  have hodd : Odd (Nat.card Y) := odd_card_of_isNilpotent hO hYN le_rfl Subgroup.le_normalizer hnil
  intro y hy
  obtain ⟨k, hk⟩ := hB y (hYW hy)
  have hk' : (⟨y, hy⟩ : ↥Y) ^ (2 ^ k) ∈ X.subgroupOf Y := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hk
  exact Subgroup.mem_subgroupOf.mp (mem_of_pow_two_pow_mem hodd (X.subgroupOf Y) hk')

theorem commutator_isNilpotent_odd
    (hO : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥)
    {T X W : Subgroup Q} (hT : IsPGroup 2 T) (hW : W.Normal) (hX : X.Normal) (hXW : X ≤ W)
    (hTX : ∀ t ∈ T, ∀ x ∈ X, t * x = x * t) (hab : ⁅W, W⁆ ≤ X) :
    Group.IsNilpotent ↥⁅T, W⁆ ∧ Odd (Nat.card ↥⁅T, W⁆) := by
  haveI := hW
  haveI := hX
  have hKW : ⁅T, W⁆ ≤ W := Subgroup.commutator_le_right T W
  have hWK : W ≤ Subgroup.normalizer ((⁅T, W⁆ : Subgroup Q) : Set Q) :=
    Subgroup.normalizer_commutator_ge_right T W
  have hXT : ⁅X, T⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_of_forall_commute hTX)
  have hKX : ⁅⁅T, W⁆, X⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := T) (H₂ := W) (H₃ := X) ?_ ?_
    · refine eq_bot_iff.mpr ?_
      rw [← hXT]
      exact Subgroup.commutator_mono_left (Subgroup.commutator_le_right W X)
    · rw [hXT]
      exact Subgroup.commutator_bot_left W
  have hKc : ⁅T, W⁆ ≤ Subgroup.centralizer (X : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKX
  have hnil : Group.IsNilpotent ↥⁅T, W⁆ := by
    refine isNilpotent_of_commutator_central fun a ha b hb c hc => ?_
    have hab' : ⁅a, b⁆ ∈ X :=
      hab ((Subgroup.commutator_mono hKW hKW) (Subgroup.commutator_mem_commutator ha hb))
    exact (Subgroup.mem_centralizer_iff.mp (hKc hc) _ hab').symm
  exact ⟨hnil, odd_card_of_isNilpotent hO hW hKW hWK hnil⟩

theorem isSylowTwoOf_sup_commutator
    (hO : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥)
    {T X W : Subgroup Q} (hT : IsPGroup 2 T) (hW : W.Normal) (hX : X.Normal) (hXW : X ≤ W)
    (hTX : ∀ t ∈ T, ∀ x ∈ X, t * x = x * t) (hab : ⁅W, W⁆ ≤ X) :
    CFSG.QuasithinUnique.IsSylowTwoOf T (T ⊔ ⁅T, W⁆) := by
  obtain ⟨-, hodd⟩ := commutator_isNilpotent_odd hO hT hW hX hXW hTX hab
  have hTK : T ≤ Subgroup.normalizer ((⁅T, W⁆ : Subgroup Q) : Set Q) :=
    Subgroup.normalizer_commutator_ge_left T W
  have hinf : ⁅T, W⁆ ⊓ T = ⊥ :=
    eq_bot_of_isPGroup_of_odd (hT.to_le inf_le_right)
      (hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  refine ⟨le_sup_left, hT, ?_⟩
  have h1 := card_sup_mul_card_inf_of_le_normalizer hTK
  rw [hinf, Subgroup.card_bot, mul_one, sup_comm] at h1
  have h2 := Subgroup.card_mul_index (T.subgroupOf (T ⊔ ⁅T, W⁆))
  have h3 : Nat.card ↥(T.subgroupOf (T ⊔ ⁅T, W⁆)) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  rw [h3, h1] at h2
  have h4 : (T.subgroupOf (T ⊔ ⁅T, W⁆)).index = Nat.card ↥⁅T, W⁆ :=
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := T)) (h2.trans (mul_comm _ _))
  rw [h4]
  exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem isSolvable_sup_commutator
    (hO : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥)
    {T X W : Subgroup Q} (hT : IsPGroup 2 T) (hW : W.Normal) (hX : X.Normal) (hXW : X ≤ W)
    (hTX : ∀ t ∈ T, ∀ x ∈ X, t * x = x * t) (hab : ⁅W, W⁆ ≤ X) :
    Group.IsSolvable ↥(T ⊔ ⁅T, W⁆) := by
  obtain ⟨hnil, -⟩ := commutator_isNilpotent_odd hO hT hW hX hXW hTX hab
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  rw [sup_comm]
  exact isSolvable_sup_of_le_normalizer inferInstance inferInstance
    (Subgroup.normalizer_commutator_ge_left T W)

theorem not_dvd_card_sup_commutator {T W : Subgroup Q} (hW : W.Normal) {p : ℕ} (hp : p.Prime)
    (hpT : ¬ p ∣ Nat.card T) (hpW : ¬ p ∣ Nat.card W) : ¬ p ∣ Nat.card ↥(T ⊔ ⁅T, W⁆) := by
  haveI := hW
  have hKW : ⁅T, W⁆ ≤ W := Subgroup.commutator_le_right T W
  have hTK : T ≤ Subgroup.normalizer ((⁅T, W⁆ : Subgroup Q) : Set Q) :=
    Subgroup.normalizer_commutator_ge_left T W
  have h := card_sup_mul_card_inf_of_le_normalizer hTK
  have hdvd : Nat.card ↥(T ⊔ ⁅T, W⁆) ∣ Nat.card ↥⁅T, W⁆ * Nat.card T := by
    rw [sup_comm]
    exact Dvd.intro _ h
  intro hp'
  rcases (Nat.Prime.dvd_mul hp).mp (hp'.trans hdvd) with h1 | h1
  · exact hpW (h1.trans (Subgroup.card_dvd_of_le hKW))
  · exact hpT h1

theorem inf_eq_bot_of_forall_commute
    (hO : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥)
    {T N : Subgroup Q} (hT : IsPGroup 2 T) (hN : N.Normal)
    (hTN : ∀ t ∈ T, ∀ n ∈ N, t * n = n * t) : T ⊓ N = ⊥ := by
  refine eq_bot_of_le_of_le_normalizer hO hN inf_le_right ?_ (hT.to_le inf_le_left)
  rw [Subgroup.le_normalizer_iff_commutator_le_left]
  have h : T ⊓ N ≤ Subgroup.centralizer (N : Set Q) :=
    fun t ht => Subgroup.mem_centralizer_iff.mpr fun n hn => (hTN t ht.1 n hn).symm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h]
  exact bot_le

end QGroup

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
