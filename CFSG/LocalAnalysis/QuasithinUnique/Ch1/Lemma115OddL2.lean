module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Odd
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CharTwoTools

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Torus

variable {X : Type} [Group X] [Finite X]

theorem not_charTwo_centralizer_of_torus {T₀ : Subgroup X} (hT : IsCyclic T₀)
    (hconj : ∀ y : X, y * y = 1 → y ≠ 1 → ∃ x ∈ T₀, IsConj y x)
    (hcent : ∀ x ∈ T₀, x ≠ 1 → x * x = 1 →
      Nat.card (Subgroup.centralizer ({x} : Set X)) = 2 * Nat.card T₀)
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) (hdvd : m ∣ Nat.card T₀) :
    ∀ t : X, t ≠ 1 → t * t = 1 → ¬ CharTwo (Subgroup.centralizer ({t} : Set X)) := by
  intro t ht1 ht2 hC
  have hcomm : IsMulCommutative T₀ := by
    have := hT
    infer_instance
  have hT₀comm : ∀ y ∈ T₀, ∀ z ∈ T₀, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  obtain ⟨x, hxT, hx⟩ := hconj t ht2 ht1
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  have hx2 : x * x = 1 := by
    rw [← hc]
    calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply ht1
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = c⁻¹ * 1 * c := by rw [hc]
      _ = 1 := by group
  have hCx : CharTwo (Subgroup.centralizer ({x} : Set X)) := by
    have h1 := charTwo_map_mulEquiv (MulAut.conj c) hC
    rw [map_centralizer_singleton] at h1
    have e1 : (MulAut.conj c : MulAut X) t = x := by
      rw [MulAut.conj_apply]
      exact hc
    rwa [e1] at h1
  set C : Subgroup X := Subgroup.centralizer ({x} : Set X) with hCdef
  have hT₀C : T₀ ≤ C := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hT₀comm y hy x hxT)
  have hC2 : Nat.card C = 2 * Nat.card T₀ := hcent x hxT hx1 hx2
  have hindex : (T₀.subgroupOf C).index = 2 := by
    have h1 := Subgroup.card_mul_index (T₀.subgroupOf C)
    have h2 : Nat.card (T₀.subgroupOf C) = Nat.card T₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₀C).toEquiv
    have hpos : 0 < Nat.card T₀ := Nat.card_pos
    rw [h2, hC2] at h1
    have : Nat.card T₀ * (T₀.subgroupOf C).index = Nat.card T₀ * 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hnorm : (T₀.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hindex
  have hCconj : ∀ k ∈ C, ∀ y ∈ T₀, k * y * k⁻¹ ∈ T₀ := by
    intro k hk y hy
    exact hnorm.conj_mem ⟨y, hT₀C hy⟩ hy ⟨k, hk⟩
  let T₁ : Subgroup X :=
    { carrier := {z | z ∈ T₀ ∧ z ^ m = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨T₀.mul_mem ha hb, ?_⟩
        rw [(show Commute a b from hT₀comm a ha b hb).mul_pow, ha', hb', one_mul]
      one_mem' := ⟨T₀.one_mem, one_pow m⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨T₀.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩ }
  have hT₁le : T₁ ≤ T₀ := fun z hz => hz.1
  have hT₁C : T₁ ≤ C := hT₁le.trans hT₀C
  have hT₁conj : ∀ k ∈ C, ∀ y ∈ T₁, k * y * k⁻¹ ∈ T₁ := by
    intro k hk y hy
    refine ⟨hCconj k hk y hy.1, ?_⟩
    rw [conj_pow, hy.2]
    group
  have hT₁norm : (T₁.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hT₁C]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hT₁conj k hk y hy, fun hy => ?_⟩
    have := hT₁conj k⁻¹ (C.inv_mem hk) _ hy
    simpa [mul_assoc] using this
  have hT₁odd : Odd (Nat.card T₁) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    have h2 : 2 ∣ Nat.card T₁ := even_iff_two_dvd.mp hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hg2 : orderOf (g : X) = 2 := by rw [Subgroup.orderOf_coe, hg]
    have : orderOf (g : X) ∣ m := orderOf_dvd_of_pow_eq_one g.2.2
    rw [hg2] at this
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr this)
  have hT₁ne : T₁ ≠ ⊥ := by
    obtain ⟨g, hg⟩ := hT.exists_generator
    have hord : orderOf g = Nat.card T₀ := orderOf_eq_card_of_forall_mem_zpowers hg
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · have : 0 < Nat.card T₀ := Nat.card_pos
        rw [hk, h0] at this
        simp at this
      · exact h0
    have hgm : ((g : X) ^ k) ^ m = 1 := by
      rw [← pow_mul, mul_comm, ← hk]
      have := pow_card_eq_one' (G := T₀) (x := g)
      exact congrArg Subtype.val this
    intro hbot
    have hmem : (g : X) ^ k ∈ T₁ := ⟨T₀.pow_mem g.2 k, hgm⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : orderOf (g : X) ∣ k := orderOf_dvd_of_pow_eq_one hmem
    rw [Subgroup.orderOf_coe, hord, hk] at h1
    have h2 := Nat.le_of_dvd hk0 h1
    nlinarith
  exact not_charTwo_of_normal_odd hT₁C hT₁norm hT₁odd hT₁ne hCx

end Torus

theorem fermat_mersenne_of_torus {p f n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : f = 1 ∨ f = 2)
    (hq : 5 ≤ p ^ f) (hn : n * 2 = if p ^ f % 4 = 1 then p ^ f - 1 else p ^ f + 1)
    (hpow : ∃ a, n = 2 ^ a) :
    (f = 1 ∧ IsFermatOrMersennePrime p) ∨ (f = 2 ∧ p = 3) := by
  obtain ⟨a, rfl⟩ := hpow
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have h2a : 2 ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
  rcases hf with rfl | rfl
  · left
    refine ⟨rfl, hp, ?_⟩
    rw [pow_one] at hq hn
    split_ifs at hn with h4
    · left
      have hp' : p = 2 ^ (a + 1) + 1 := by omega
      have hprime : (2 ^ (a + 1) + 1).Prime := hp' ▸ hp
      obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (n := a + 1) (by norm_num) (by omega) hprime
      exact ⟨m, by rw [hp', hm]⟩
    · right
      have hp' : p = 2 ^ (a + 1) - 1 := by omega
      refine ⟨a + 1, ?_, hp'⟩
      by_contra hlt
      have ha : a = 0 := by omega
      subst ha
      simp at hn
      omega
  · right
    refine ⟨rfl, ?_⟩
    by_contra hp3
    have hp4 : p ^ 2 % 4 = 1 := by
      have : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases this with h | h <;> simp [Nat.pow_mod, h]
    split_ifs at hn
    have h3 : 3 ∣ p ^ 2 - 1 := by
      have hp3' : p % 3 = 1 ∨ p % 3 = 2 := by
        have : ¬ 3 ∣ p := fun h =>
          hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
        omega
      have : p ^ 2 % 3 = 1 := by rcases hp3' with h | h <;> simp [Nat.pow_mod, h]
      omega
    have h3' : 3 ∣ 2 ^ (a + 1) := by
      have : p ^ 2 - 1 = 2 ^ (a + 1) := by omega
      rwa [this] at h3
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3')
    omega

theorem oddInvolutionCentralizers_psl2 {K : Type} [Group K] [Finite K] {p f : ℕ} (hp2 : p ≠ 2)
    (hf : f = 1 ∨ f = 2) (hmodel : StatedClassicalModel K .PSL 2 p f)
    (hno : ¬ Nonempty (K ≃* alternatingGroup (Fin 6))) {t : K} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hC : CharTwo (Subgroup.centralizer ({t} : Set K))) :
    ∃ p' : ℕ, IsFermatOrMersennePrime p' ∧ StatedClassicalModel K .PSL 2 p' 1 := by
  classical
  have hp : p.Prime := hmodel.1.1
  obtain ⟨F, _, _, _, e, hq, hF, hq5⟩ := psl2_model_data hp2 hmodel
  obtain ⟨T₀, w, hcyc, hw, hw2, hinv, hconj, hcent, hcard⟩ := psl2_torus_data hF hq5
  have ht1' : e t ≠ 1 := fun h => ht1 (e.injective (by rw [h, map_one]))
  have ht2' : e t * e t = 1 := by rw [← map_mul, ht2, map_one]
  have hCX : CharTwo (Subgroup.centralizer ({e t} : Set PSL(2, F))) := by
    have := charTwo_map_mulEquiv e hC
    rwa [map_centralizer_singleton] at this
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := T₀)).ne'
  have hm1 : m = 1 := by
    by_contra hne
    have hm3 : 3 ≤ m := by
      obtain ⟨r, hr⟩ := hm
      omega
    exact not_charTwo_centralizer_of_torus hcyc hconj hcent hm hm3
      ⟨2 ^ a, by rw [hnm]; ring⟩ (e t) ht1' ht2' hCX
  have hpow : ∃ a, Nat.card T₀ = 2 ^ a := ⟨a, by rw [hnm, hm1, mul_one]⟩
  have hqpf : Fintype.card F = p ^ f := hq
  have hq5' : 5 ≤ p ^ f := hqpf ▸ hq5
  have hcard' : Nat.card T₀ * 2 = if p ^ f % 4 = 1 then p ^ f - 1 else p ^ f + 1 := by
    rw [hcard, hqpf]
  rcases fermat_mersenne_of_torus hp hp2 hf hq5' hcard' hpow with ⟨rfl, hfm⟩ | ⟨rfl, rfl⟩
  · exact ⟨p, hfm, hmodel⟩
  · exfalso
    apply hno
    have hK9 : Fintype.card F = 9 := by rw [hqpf]; norm_num
    obtain ⟨e9⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
        F hK9
    exact ⟨e.trans e9⟩

@[expose] def OddDegreeThreeCentralizers : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p →
    (StatedClassicalModel K .PSL 3 p 1 ∨ StatedClassicalModel K .PSU 3 p 1) →
    ∀ t : K, t ≠ 1 → t * t = 1 → ¬ CharTwo (Subgroup.centralizer ({t} : Set K))

theorem oddInvolutionCentralizers_of (h3 : OddDegreeThreeCentralizers) :
    OddInvolutionCentralizers := by
  intro K _ _ hK h6 t ht1 ht2 hC
  obtain ⟨p, hp, hp2, hcases⟩ := hK
  have hp3 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  rcases hcases with ⟨f, hf, hm⟩ | hm | hm
  · obtain ⟨p', hp', hm'⟩ := oddInvolutionCentralizers_psl2 hp2 hf hm h6 ht1 ht2 hC
    exact Or.inr (Or.inr ⟨p', hp', hm'⟩)
  · rcases hp3 with rfl | h5
    · exact Or.inl hm
    · exact absurd hC (h3 K p hp h5 (Or.inl hm) t ht1 ht2)
  · rcases hp3 with rfl | h5
    · exact Or.inr (Or.inl hm)
    · exact absurd hC (h3 K p hp h5 (Or.inr hm) t ht1 ht2)

end CFSG.QuasithinUnique.Ch1
