module

public import CFSG.Open.FusionDefs

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Open Subgroup

section TwoElements

variable {X : Type*} [Group X]

theorem mem_of_two_pow_of_odd_index (N : Subgroup X) [N.Normal] (hN : Odd N.index)
    {x : X} (hx : ∃ n : ℕ, x ^ 2 ^ n = 1) : x ∈ N := by
  obtain ⟨n, hn⟩ := hx
  have h1 : orderOf (QuotientGroup.mk x : X ⧸ N) ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hn, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk x : X ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) N.index := Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hN)
  have h3 : orderOf (QuotientGroup.mk x : X ⧸ N) = 1 :=
    (hcop.coprime_dvd_left h1).eq_one_of_dvd h2
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h3)

theorem mem_sylow_of_mem_normalizer [Finite X] (S : Sylow 2 X) {x : X}
    (hx : x ∈ normalizer ((S : Subgroup X) : Set X)) (h2 : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    x ∈ (S : Subgroup X) := by
  have hle : (S : Subgroup X) ≤ normalizer ((S : Subgroup X) : Set X) := le_normalizer
  have hrel : Odd ((S : Subgroup X).relIndex (normalizer ((S : Subgroup X) : Set X))) := by
    have hdvd := Subgroup.relIndex_dvd_index_of_le hle
    have hnd := S.not_dvd_index
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h => hnd (h.trans hdvd)
  have hmem := mem_of_two_pow_of_odd_index
    ((S : Subgroup X).subgroupOf (normalizer ((S : Subgroup X) : Set X))) hrel
    (x := ⟨x, hx⟩) (by
      obtain ⟨k, hk⟩ := h2
      exact ⟨k, Subtype.ext (by simpa using hk)⟩)
  exact (Subgroup.mem_subgroupOf.mp hmem)

theorem mem_normalizer_of_map_conj_eq {H : Subgroup X} {g : X}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : g * y * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      simpa [MulAut.conj_apply] using hzy
    exact this ▸ hz

end TwoElements

section StronglyEmbedded

variable {X : Type*} [Group X] [Finite X]

theorem fusionStronglyEmbedded_normalizer_of_ti (S : Sylow 2 X)
    (hTI : fusionIsTI (S : Subgroup X)) (hS1 : (S : Subgroup X) ≠ ⊥)
    (hnn : ¬ (S : Subgroup X).Normal) :
    fusionStronglyEmbedded (normalizer ((S : Subgroup X) : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun htop => hnn (normalizer_eq_top_iff.mp htop), ?_, ?_⟩
  · have hdvd : Nat.card (S : Subgroup X) ∣ Nat.card (normalizer ((S : Subgroup X) : Set X)) :=
      Subgroup.card_dvd_of_le le_normalizer
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hS1 (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [even_iff_two_dvd]
    refine dvd_trans ?_ hdvd
    rw [hn]
    exact dvd_pow_self 2 hn0
  · intro g hg
    by_contra hodd
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(normalizer ((S : Subgroup X) : Set X) ⊓
      (normalizer ((S : Subgroup X) : Set X)).map (MulAut.conj g⁻¹).toMonoidHom)) 2 hodd
    have ht2 : (t : X) ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rw [ht] at this
      exact congrArg Subtype.val this
    have ht1 : (t : X) ≠ 1 := by
      intro h1
      have : t = 1 := Subtype.ext h1
      rw [this, orderOf_one] at ht
      omega
    have h2 : ∃ k : ℕ, (t : X) ^ 2 ^ k = 1 := ⟨1, by simpa using ht2⟩
    have htM := t.2.1
    have htS : (t : X) ∈ (S : Subgroup X) := mem_sylow_of_mem_normalizer S htM h2
    obtain ⟨u, huM, hu⟩ := t.2.2
    have hu' : g⁻¹ * u * g = (t : X) := by simpa [MulAut.conj_apply] using hu
    have hug : u = g * (t : X) * g⁻¹ := by rw [← hu']; group
    have hu2 : ∃ k : ℕ, u ^ 2 ^ k = 1 := ⟨1, by
      rw [hug]
      have : (g * (t : X) * g⁻¹) ^ 2 = g * (t : X) ^ 2 * g⁻¹ := by
        rw [pow_two, pow_two]; group
      rw [pow_one, this, ht2]; group⟩
    have huS : u ∈ (S : Subgroup X) := mem_sylow_of_mem_normalizer S huM hu2
    have htSg : (t : X) ∈ (S : Subgroup X).map (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨u, huS, hu⟩
    by_cases hconj : (S : Subgroup X).map (MulAut.conj g⁻¹).toMonoidHom = (S : Subgroup X)
    · exact hg (by
        have := mem_normalizer_of_map_conj_eq hconj
        simpa using inv_mem this)
    · have hbot := hTI g⁻¹ hconj
      have : (t : X) ∈ (S : Subgroup X) ⊓ (S : Subgroup X).map (MulAut.conj g⁻¹).toMonoidHom :=
        ⟨htS, htSg⟩
      rw [hbot] at this
      exact ht1 (Subgroup.mem_bot.mp this)

theorem exists_sylow_eq_of_forall_mem_normalizer {Z : Subgroup X} (hZ : IsPGroup 2 Z)
    (h : ∀ x ∈ normalizer (Z : Set X), (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ Z) :
    ∃ S : Sylow 2 X, (S : Subgroup X) = Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hZP⟩ := hZ.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hZP⟩
  by_contra hPZ
  have hlt : Z.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hPZ ?_
    intro x hx
    have := (Subgroup.subgroupOf_eq_top.mp htop)
    exact this hx
  have : Group.IsNilpotent (P : Subgroup X) := P.isPGroup'.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := (P : Subgroup X))
  have hlt2 := hnc _ hlt
  obtain ⟨y, hyN, hyZ⟩ := IsConcreteLE.exists_of_lt hlt2
  refine hyZ ?_
  have hy2 : ∃ k : ℕ, (y : X) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' y
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hyn : (y : X) ∈ normalizer (Z : Set X) := by
    rw [Subgroup.mem_normalizer_iff] at hyN ⊢
    intro x
    constructor
    · intro hx
      have hxP : x ∈ (P : Subgroup X) := hZP hx
      have := (hyN ⟨x, hxP⟩).mp (by simpa [Subgroup.mem_subgroupOf] using hx)
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hx
      have hxP : x ∈ (P : Subgroup X) := by
        have h1 : (y : X) * x * (y : X)⁻¹ ∈ (P : Subgroup X) := hZP hx
        have := (P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem
          ((P : Subgroup X).inv_mem y.2) h1) y.2
        simpa [mul_assoc] using this
      have := (hyN ⟨x, hxP⟩).mpr (by simpa [Subgroup.mem_subgroupOf] using hx)
      simpa [Subgroup.mem_subgroupOf] using this
  exact Subgroup.mem_subgroupOf.mpr (h _ hyn hy2)

end StronglyEmbedded

end CFSG.CGT.PushingUpLit.A78
