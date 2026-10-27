module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Transport
public import CFSG.CGT.PushingUpLit.LIT.Foote.L53C

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem normalizer_le_M : Subgroup.normalizer (J : Set G) ≤ M := fun x hx =>
  c.mem_of_conj_le (by rw [(rightConjugate_eq_self_iff J x).2 hx]; exact c.le)

theorem mem_normalizer_of_centralizes {m a k : G} (hm : m ∈ M) (haJ : a ∈ J) (hkJ : k ∈ J)
    (hak : a * k ≠ k * a) (ham : m * a = a * m) : m ∈ Subgroup.normalizer (J : Set G) := by
  by_contra hmn
  have hne : rightConjugate J m ≠ J := fun h => hmn ((rightConjugate_eq_self_iff J m).1 h)
  have hcomm := c.commutator_conj_eq_bot hm hne
  have haJm : a ∈ rightConjugate J m := by
    rw [mem_rightConjugate_iff]
    have : m * a * m⁻¹ = a := by rw [ham]; group
    rw [this]
    exact haJ
  have hJC : J ≤ Subgroup.centralizer ((rightConjugate J m : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  exact hak (Subgroup.mem_centralizer_iff.1 (hJC hkJ) a haJm)

theorem mem_of_centralizer_le {g t : G} (ht : t ∈ rightConjugate J g)
    (hC : Subgroup.centralizer ({t} : Set G) ≤ M) : g ∈ M := by
  obtain ⟨m', hm', hne⟩ := (c.transport g).exists_conj_ne
  have hcomm := (c.transport g).commutator_conj_eq_bot hm' hne
  have hJC : rightConjugate J g ≤
      Subgroup.centralizer ((rightConjugate (rightConjugate J g) m' : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hJ2 : rightConjugate J (g * m') ≤ M := by
    rw [← rightConjugate_mul]
    intro y hy
    apply hC
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 (hJC ht) y hy
  have h1 : g * m' ∈ M := c.mem_of_conj_le hJ2
  have h2 : g * m' * g⁻¹ ∈ M := (mem_rightConjugate_iff M g m').1 hm'
  have e : (g * m' * g⁻¹)⁻¹ * (g * m') = g := by group
  have := M.mul_mem (M.inv_mem h2) h1
  rwa [e] at this

theorem eq_one_of_mem_inf {g t : G} (hg : g ∉ M) (htJ : t ∈ J) (htg : t ∈ rightConjugate J g)
    (h2 : ∃ n : ℕ, t ^ 2 ^ n = 1) : t = 1 := by
  by_contra h1
  exact hg (c.mem_of_centralizer_le htg (c.centralizer_le_of_mem htJ h2 h1))

theorem eq_one_of_centralizes {g t m : G} (hg : g ∉ M) (htg : t ∈ rightConjugate J g)
    (h2 : ∃ n : ℕ, t ^ 2 ^ n = 1) (hm : m ∈ M)
    (htm : ∀ y ∈ rightConjugate J m, t * y = y * t) : t = 1 := by
  by_contra h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsPGroup 2 (Subgroup.zpowers t) := by
    obtain ⟨n, hn⟩ := h2
    have : orderOf t ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hA1 : Subgroup.zpowers t ≠ ⊥ := fun h => h1 (Subgroup.zpowers_eq_bot.1 h)
  have hN : rightConjugate J m ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_zpowers (htm y hy).symm
  have hC : Subgroup.centralizer ({t} : Set G) ≤ M := fun k hk => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hk
    exact c.normalizer_le hA hA1 hm hN (mem_normalizer_zpowers hk)
  exact hg (c.mem_of_centralizer_le htg hC)

theorem inf_eq_bot_of_le {g : G} (hg : g ∉ M) {T : Subgroup G} (hT : T ≤ rightConjugate J g)
    (hT2 : IsPGroup 2 T) : T ⊓ J = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  obtain ⟨htT, htJ⟩ := Subgroup.mem_inf.1 ht
  have h2 : ∃ n : ℕ, t ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hT2 ⟨t, htT⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  exact c.eq_one_of_mem_inf hg htJ (hT htT) h2

theorem eq_bot_of_centralizes {g m : G} (hg : g ∉ M) (hm : m ∈ M) {T : Subgroup G}
    (hT : T ≤ rightConjugate J g) (hT2 : IsPGroup 2 T)
    (hc : ∀ t ∈ T, ∀ y ∈ rightConjugate J m, t * y = y * t) : T = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  have h2 : ∃ n : ℕ, t ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  exact c.eq_one_of_centralizes hg (hT ht) h2 hm (hc t ht)

end CE

theorem le_of_normal_sylow {E T R : Subgroup G} (hT : ABGLocalTools.IsSylowOf 2 T E)
    (hnorm : E ≤ Subgroup.normalizer (T : Set G)) (hR : R ≤ E) (hR2 : IsPGroup 2 R) : R ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (T ⊔ R : Subgroup G) :=
    hT.isPGroup.to_sup_of_normal_left' hR2 (hR.trans hnorm)
  have h2 := hT.eq_of_le le_sup_left (sup_le hT.le hR) h1
  exact le_sup_right.trans h2.le

@[expose] def eSub (J : Subgroup G) (h : G) : Subgroup G :=
  rightConjugate J h ⊓ Subgroup.normalizer (J : Set G)

@[expose] def Good56 (M J : Subgroup G) (h : G) : Prop :=
  h ∉ M ∧ ∃ W : Subgroup G, W ≤ eSub J h ∧ CFSG.Open.IsElemAbelian 2 W ∧ Nat.card W = 4

omit [Finite G] in
theorem FourGroupMeet.exists_good {M J : Subgroup G} (h : FourGroupMeet M J) :
    ∃ g, Good56 M J g := by
  obtain ⟨g, hg, W, hW, hW2, hW4⟩ := h
  exact ⟨g, hg, W, hW, hW2, hW4⟩

theorem exists_max56 {M J : Subgroup G} (hf : ∃ g, Good56 M J g) :
    ∃ g, Good56 M J g ∧ ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2 := by
  obtain ⟨g, hg, hmax⟩ := Set.exists_max_image {h : G | Good56 M J h}
    (fun h => (Nat.card ↥(eSub J h)).factorization 2) (Set.toFinite _) hf
  exact ⟨g, hg, fun h hh => hmax h hh⟩

theorem card_le_of_max {M J : Subgroup G} {g : G} {T : Subgroup G}
    (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hmax : ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2)
    {h : G} (hh : Good56 M J h) {R : Subgroup G} (hR : R ≤ eSub J h) (hR2 : IsPGroup 2 R) :
    Nat.card R ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Th, hTh⟩ := exists_isSylowOf 2 (eSub J h)
  have h1 := card_le_of_isSylowOf hTh hR hR2
  rw [hT.card_eq]
  calc Nat.card R ≤ Nat.card Th := h1
    _ = 2 ^ (Nat.card ↥(eSub J h)).factorization 2 := hTh.card_eq
    _ ≤ 2 ^ (Nat.card ↥(eSub J g)).factorization 2 :=
        Nat.pow_le_pow_right (by norm_num) (hmax h hh)

end CFSG.CGT.PushingUpLit.LIT.Foote
