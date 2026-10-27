module

public import CFSG.CGT.PushingUpLit.T2KSW.StrongEmb
import CFSG.StronglyEmbedded.BenderNormalSeries
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG.ABGLocalTools CFSG.Open
open scoped MatrixGroups commutatorElement

section Helpers

variable {Y : Type*} [Group Y]

private theorem mem_normalizer_of_forall_conj_mem [Finite Y] {B : Subgroup Y} {m : Y}
    (h : ∀ y ∈ B, m * y * m⁻¹ ∈ B) : m ∈ Subgroup.normalizer (B : Set Y) := by
  have hle : B.map (MulAut.conj m).toMonoidHom ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    simpa using h y hy
  have heq : B.map (MulAut.conj m).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj m).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  have hy' : (MulAut.conj m).toMonoidHom y ∈ B.map (MulAut.conj m).toMonoidHom := by
    rw [heq]
    simpa using hy
  exact (Subgroup.mem_map_iff_mem (MulAut.conj m).injective).1 hy'

private theorem card_dvd_two_of_isCyclic {P : Subgroup Y} (hexp : ∀ a ∈ P, a * a = 1)
    (hP : IsCyclic P) : Nat.card P ∣ 2 := by
  have h := Monoid.exponent_dvd_of_forall_pow_eq_one (G := P) (n := 2) fun a =>
    Subtype.ext (by simpa [pow_two] using hexp a a.2)
  rwa [IsCyclic.exponent_eq_card] at h

private theorem false_of_quaternion_of_mul_self {P : Subgroup Y} (hexp : ∀ a ∈ P, a * a = 1)
    {n : ℕ} [NeZero n] (e : P ≃* QuaternionGroup n) : False := by
  have h4 := QuaternionGroup.orderOf_xa (n := n) 0
  rw [← e.symm.orderOf_eq] at h4
  have h2 : orderOf (e.symm (QuaternionGroup.xa 0)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      simpa [pow_two] using hexp _ (e.symm (QuaternionGroup.xa 0)).2))
  rw [h4] at h2
  norm_num at h2

private theorem false_of_fusionBenderBorel_of_abelian {K : Type*} [Group K] {q k : ℕ}
    (hB : fusionBenderBorel K q k) (hq : 2 ≤ q) (hk : 2 ≤ k) (Q : Sylow 2 K)
    (hQ : ∀ a ∈ (Q : Subgroup K), ∀ b ∈ (Q : Subgroup K), a * b = b * a) : False := by
  obtain ⟨-, -, -, hZ, hcard⟩ := hB Q
  have hcenter : Subgroup.center (Q : Subgroup K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hQ _ y.2 _ x.2)
  rw [hcenter, Subgroup.card_top, hcard] at hZ
  have hlt : q < q ^ k :=
    calc q = q ^ 1 := (pow_one q).symm
      _ < q ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

end Helpers

theorem irreducible_of_bender_section {Z : Type} [Group Z] [Finite Z] {M B : Subgroup Z}
    [M.Normal] (hM : Odd (Nat.card M)) (hK : fusionIsBenderGroup (Z ⧸ M))
    (hB : IsSylowOf 2 B ⊤) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    ∀ P : Subgroup Z, P ≤ B →
      Subgroup.normalizer (B : Set Z) ≤ Subgroup.normalizer (P : Set Z) → P = ⊥ ∨ P = B := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hB.isPGroup
  have hdisj : Disjoint B M := Subgroup.disjoint_of_coprime_natCard (by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hM))
  have hBM : ∀ b ∈ B, b ∈ M → b = 1 := fun b hb hbM =>
    Subgroup.mem_bot.1 (Subgroup.disjoint_def.1 hdisj hb hbM)
  set π : Z →* Z ⧸ M := QuotientGroup.mk' M
  have hπinj : ∀ a ∈ B, ∀ b ∈ B, π a = π b → a = b := by
    intro a ha b hb h
    have h1 : a⁻¹ * b ∈ M := QuotientGroup.eq.1 h
    exact inv_mul_eq_one.1 (hBM _ (B.mul_mem (B.inv_mem ha) hb) h1)
  have hSp : IsPGroup 2 (B.map π) := hB.isPGroup.map π
  have hSi : ¬ 2 ∣ (B.map π).index := by
    intro h
    have h1 := h.trans (Subgroup.index_map_dvd B (QuotientGroup.mk'_surjective M))
    have hB' := (isSylowOf_iff.1 hB).2.2
    rw [Subgroup.relIndex_top_right] at hB'
    exact hB' h1
  let Q : Sylow 2 (Z ⧸ M) := hSp.toSylow hSi
  have hSab : ∀ a ∈ B.map π, ∀ b ∈ B.map π, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hBab x hx y hy]
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  ·
    have hL2 : CFSG.CGT.Timmesfeld75.IsL2Pair (Z ⧸ M) (B.map π) (2 ^ f) :=
      CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow (by omega : f ≠ 0) ⟨e⟩ Q
    intro P hPB hNP
    by_cases hP1 : P = ⊥
    · exact Or.inl hP1
    right
    obtain ⟨p, hpP, hp1⟩ : ∃ p ∈ P, p ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hP1 ((Subgroup.eq_bot_iff_forall P).2 hcon)
    refine le_antisymm hPB fun b hb => ?_
    by_cases hb1 : b = 1
    · rw [hb1]
      exact P.one_mem
    have hpB : p ∈ B := hPB hpP
    have hπne : ∀ c ∈ B, c ≠ 1 → π c ≠ 1 := fun c hc hc1 h =>
      hc1 (hBM c hc ((QuotientGroup.eq_one_iff c).1 h))
    obtain ⟨g, hg, hgxy⟩ := hL2.transitive (Subgroup.mem_map_of_mem π hpB) (hπne p hpB hp1)
      (Subgroup.mem_map_of_mem π hb) (hπne b hb hb1)
    obtain ⟨m₀, rfl⟩ := QuotientGroup.mk'_surjective M g
    have hconj : ∀ y ∈ B, m₀ * y * m₀⁻¹ ∈ B ⊔ M := by
      intro y hy
      have h1 : π (m₀ * y * m₀⁻¹) ∈ B.map π := by
        have := (Subgroup.mem_normalizer_iff.1 hg (π y)).1 (Subgroup.mem_map_of_mem π hy)
        rw [map_mul, map_mul, map_inv]
        exact this
      obtain ⟨b', hb', hb'eq⟩ := h1
      have h2 : b'⁻¹ * (m₀ * y * m₀⁻¹) ∈ M := QuotientGroup.eq.1 hb'eq
      have h3 := Subgroup.mul_mem_sup hb' h2
      simpa using h3
    have hB₁ : B.map (MulAut.conj m₀).toMonoidHom ≤ B ⊔ M := by
      rintro _ ⟨y, hy, rfl⟩
      simpa using hconj y hy
    obtain ⟨h, hh, hhB⟩ := exists_mem_conj_mem_of_isSylowOf (hB.of_le le_sup_left le_top)
      hB₁ (hB.isPGroup.map _)
    have hm : h⁻¹ * m₀ ∈ Subgroup.normalizer (B : Set Z) :=
      mem_normalizer_of_forall_conj_mem fun y hy => by
        have := hhB (m₀ * y * m₀⁻¹) ⟨y, hy, by simp⟩
        simpa [mul_assoc] using this
    obtain ⟨m, hmdef⟩ : ∃ m, m = h⁻¹ * m₀ := ⟨_, rfl⟩
    rw [← hmdef] at hm
    have hm₀ : m₀ = h * m := by rw [hmdef]; group
    have hp₁ : m * p * m⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hNP hm) p).1 hpP
    obtain ⟨b₁, hb₁, μ, hμ, hhμ⟩ := Subgroup.mem_sup_of_normal_right.1 hh
    have hπμ : π μ = 1 := (QuotientGroup.eq_one_iff μ).2 hμ
    have hπm₀ : π m₀ = π b₁ * π m := by
      rw [hm₀, ← hhμ, map_mul, map_mul, hπμ, mul_one]
    have hS1 : π b₁ * π (m * p * m⁻¹) = π (m * p * m⁻¹) * π b₁ :=
      hSab _ (Subgroup.mem_map_of_mem π hb₁) _ (Subgroup.mem_map_of_mem π (hPB hp₁))
    have key : π (m * p * m⁻¹) = π b := by
      rw [← hgxy, hπm₀]
      calc π (m * p * m⁻¹) = (π (m * p * m⁻¹) * π b₁) * (π b₁)⁻¹ := by group
        _ = (π b₁ * π (m * p * m⁻¹)) * (π b₁)⁻¹ := by rw [hS1]
        _ = π b₁ * π m * π p * (π b₁ * π m)⁻¹ := by
          simp only [map_mul, map_inv]
          group
    have hbeq : b = m * p * m⁻¹ := hπinj b hb _ (hPB hp₁) key.symm
    rw [hbeq]
    exact hp₁
  · exfalso
    have : Finite (PSU3 2 f) := Finite.of_surjective e e.surjective
    refine false_of_fusionBenderBorel_of_abelian
      ((bender_psu3_borel_full f hf).map_mulEquiv e.symm) ?_ (by norm_num) Q hSab
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  · exfalso
    have : Finite (Sz a) := Finite.of_surjective e e.surjective
    refine false_of_fusionBenderBorel_of_abelian
      ((bender_suzuki_borel_full a ha).map_mulEquiv e.symm) ?_ le_rfl Q hSab
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_eq_two_or_irreducible {X : Type} [Group X] [Finite X]
    {H B : Subgroup X} (hH : fusionStronglyEmbedded H) (hB : IsSylowOf 2 B ⊤)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBexp : ∀ a ∈ B, a * a = 1) (hB1 : B ≠ ⊥) :
    Nat.card B = 2 ∨ ∀ P : Subgroup X, P ≤ B →
      Subgroup.normalizer (B : Set X) ≤ Subgroup.normalizer (P : Set X) → P = ⊥ ∨ P = B := by
  obtain ⟨-, hBp, hBi⟩ := isSylowOf_iff.1 hB
  rw [Subgroup.relIndex_top_right] at hBi
  rcases CFSG.Open.bender_strongly_embedded_normal_series X H hH with hcq |
    ⟨M, N, hMn, hNn, hMNn, hMN, hModd, hNodd, hK⟩
  · left
    let S : Sylow 2 X := hBp.toSylow hBi
    rcases hcq S with hcyc | ⟨r, -, ⟨e⟩⟩
    · have hd : Nat.card B ∣ 2 := card_dvd_two_of_isCyclic hBexp hcyc
      have hne : Nat.card B ≠ 1 := fun h => hB1 ((Subgroup.eq_bot_iff_card B).2 h)
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
      · exact absurd h hne
      · exact h
    · exfalso
      have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
      exact false_of_quaternion_of_mul_self hBexp e
  · right
    have hBN : B ≤ N := by
      intro b hb
      obtain ⟨j, hj⟩ := hNodd
      have hpow : b ^ N.index ∈ N := Subgroup.pow_index_mem N b
      rwa [hj, pow_succ, pow_mul, pow_two, hBexp b hb, one_pow, one_mul] at hpow
    have hM₁ : Odd (Nat.card (M.subgroupOf N)) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv]
    have hB₁ : IsSylowOf 2 (B.subgroupOf N) ⊤ := by
      rw [isSylowOf_iff]
      refine ⟨le_top, hBp.comap_subtype, ?_⟩
      rw [Subgroup.relIndex_top_right]
      intro h
      exact hBi (h.trans (Subgroup.relIndex_dvd_index_of_le hBN))
    have hB₁ab : ∀ a ∈ B.subgroupOf N, ∀ b ∈ B.subgroupOf N, a * b = b * a :=
      fun a ha b hb => Subtype.ext (hBab a ha b hb)
    have key := irreducible_of_bender_section hM₁ hK hB₁ hB₁ab
    intro P hPB hNP
    have hPN : P ≤ N := hPB.trans hBN
    have h1 := key (P.subgroupOf N) (fun x hx => hPB hx) (by
      intro z hz
      have hz' : (z : X) ∈ Subgroup.normalizer (B : Set X) := by
        apply mem_normalizer_of_forall_conj_mem
        intro y hy
        exact (Subgroup.mem_normalizer_iff.1 hz ⟨y, hBN hy⟩).1 hy
      have hz'' := hNP hz'
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact Subgroup.mem_normalizer_iff.1 hz'' (y : X))
    rcases h1 with h1 | h1
    · left
      refine (Subgroup.eq_bot_iff_forall P).2 fun x hx => ?_
      have hx' : (⟨x, hPN hx⟩ : N) ∈ P.subgroupOf N := hx
      rw [h1] at hx'
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hx')
    · right
      refine le_antisymm hPB fun x hx => ?_
      have hx' : (⟨x, hBN hx⟩ : N) ∈ B.subgroupOf N := hx
      rw [← h1] at hx'
      exact hx'

private theorem card_eq_card_map_mul_card_inf_ker' {R G : Type*} [Group R] [Group G] (φ : R →* G)
    (H : Subgroup R) : Nat.card H = Nat.card (H.map φ) * Nat.card (H ⊓ φ.ker : Subgroup R) := by
  let ψ : H →* G := φ.comp H.subtype
  have hrange : ψ.range = H.map φ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ψ.ker = Nat.card (H ⊓ φ.ker : Subgroup R) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : H) : R), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker]

private theorem tr_of_normal_good_Q {Z : Type} [Group Z] [Finite Z]
    {T Q Y : Subgroup Z} [Q.Normal] (hT : IsSylowOf 2 T ⊤) (hQT : Q ≤ T) (hlt : Q < T)
    (hTQ : ∀ x ∈ T, ∀ y ∈ T, x ^ 2 ∈ Q ∧ ⁅x, y⁆ ∈ Q) (hY : Y ≠ ⊤) (hQY : Q ≤ Y)
    (hmax : ∀ Q' : Subgroup Z, Q < Q' → Q' ≤ T → Subgroup.normalizer (Q' : Set Z) ≤ Y) :
    Nat.card T = 2 * Nat.card Q ∨ ∀ P : Subgroup Z, P ≤ T →
      Subgroup.normalizer (T : Set Z) ≤ Subgroup.normalizer (P : Set Z) → P ≤ Q ∨ P ⊔ Q = T := by
  set π : Z →* Z ⧸ Q := QuotientGroup.mk' Q
  have hker : π.ker = Q := QuotientGroup.ker_mk' Q
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hB : IsSylowOf 2 (T.map π) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, hT.isPGroup.map π, ?_⟩
    rw [Subgroup.relIndex_top_right]
    intro h
    have h1 := h.trans (Subgroup.index_map_dvd T hπsurj)
    have hT' := (isSylowOf_iff.1 hT).2.2
    rw [Subgroup.relIndex_top_right] at hT'
    exact hT' h1
  have hBab : ∀ a ∈ T.map π, ∀ b ∈ T.map π, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    have h := (hTQ y⁻¹ (T.inv_mem hy) x⁻¹ (T.inv_mem hx)).2
    rw [commutatorElement_def] at h
    exact QuotientGroup.eq.2 (by simpa [mul_assoc] using h)
  have hBexp : ∀ a ∈ T.map π, a * a = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff (x * x)).2 (by simpa [pow_two] using (hTQ x hx x hx).1)
  have hB1 : T.map π ≠ ⊥ := by
    intro h
    obtain ⟨t, htT, htQ⟩ := IsConcreteLE.exists_of_lt hlt
    have h1 : π t = 1 := by
      have := Subgroup.mem_map_of_mem π htT
      rw [h, Subgroup.mem_bot] at this
      exact this
    exact htQ ((QuotientGroup.eq_one_iff t).1 h1)
  have hH : Y.map π ≠ ⊤ := by
    intro h
    apply hY
    have h1 : Subgroup.comap π (Y.map π) = ⊤ := by
      rw [h]
      exact Subgroup.comap_top π
    rw [Subgroup.comap_map_eq, hker, sup_eq_left.2 hQY] at h1
    exact h1
  have hN : ∀ P : Subgroup (Z ⧸ Q), P ≤ T.map π → P ≠ ⊥ →
      Subgroup.normalizer (P : Set (Z ⧸ Q)) ≤ Y.map π := by
    intro P hPB hP1 x hx
    obtain ⟨m, rfl⟩ := hπsurj x
    have hQP : Q ≤ P.comap π := by
      intro q hq
      show π q ∈ P
      have h1 : π q = 1 := (QuotientGroup.eq_one_iff q).2 hq
      rw [h1]
      exact P.one_mem
    have hPT : P.comap π ≤ T := by
      intro z hz
      obtain ⟨t, ht, htz⟩ := hPB hz
      have h1 : t⁻¹ * z ∈ Q := QuotientGroup.eq.1 htz
      have h2 := T.mul_mem ht (hQT h1)
      simpa using h2
    have hlt' : Q < P.comap π := by
      refine lt_of_le_of_ne hQP fun h => hP1 ?_
      refine (Subgroup.eq_bot_iff_forall P).2 fun p hp => ?_
      obtain ⟨z, rfl⟩ := hπsurj p
      have hz : z ∈ P.comap π := hp
      rw [← h] at hz
      exact (QuotientGroup.eq_one_iff z).2 hz
    have hmN : m ∈ Subgroup.normalizer ((P.comap π : Subgroup Z) : Set Z) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      show π y ∈ P ↔ π (m * y * m⁻¹) ∈ P
      rw [map_mul, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.1 hx (π y)
    exact ⟨m, hmax _ hlt' hPT hmN, rfl⟩
  have hSE : fusionStronglyEmbedded (Y.map π) :=
    fusionStronglyEmbedded_of_normalizer_le hB hB1 hH hN
  rcases card_eq_two_or_irreducible hSE hB hBab hBexp hB1 with h2 | hirr
  · left
    have hcard := card_eq_card_map_mul_card_inf_ker' π T
    rw [hker, inf_eq_right.2 hQT, h2] at hcard
    exact hcard
  · right
    intro P hPT hNP
    have hPB : P.map π ≤ T.map π := Subgroup.map_mono hPT
    have hcomapT : (T.map π).comap π = T := by
      rw [Subgroup.comap_map_eq, hker, sup_eq_left.2 hQT]
    have hTmem : ∀ y, y ∈ T ↔ π y ∈ T.map π := fun y => by
      rw [← Subgroup.mem_comap, hcomapT]
    rcases hirr (P.map π) hPB (by
        intro x hx
        obtain ⟨m, rfl⟩ := hπsurj x
        have hmT : m ∈ Subgroup.normalizer (T : Set Z) := by
          rw [Subgroup.mem_normalizer_iff]
          intro y
          rw [hTmem y, hTmem (m * y * m⁻¹), map_mul, map_mul, map_inv]
          exact Subgroup.mem_normalizer_iff.1 hx (π y)
        have hmP := hNP hmT
        apply mem_normalizer_of_forall_conj_mem
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨m * p * m⁻¹, (Subgroup.mem_normalizer_iff.1 hmP p).1 hp, by simp⟩) with h | h
    · left
      have := (Subgroup.map_eq_bot_iff P).1 h
      rwa [hker] at this
    · right
      calc P ⊔ Q = (P.map π).comap π := by rw [Subgroup.comap_map_eq, hker]
        _ = (T.map π).comap π := by rw [h]
        _ = T := hcomapT

theorem tr_of_good_Q_strong {G : Type} [Group G] [Finite G]
    {T E Q : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hQT : Q ≤ T)
    (hTQ : ∀ x ∈ T, ∀ y ∈ T, x ^ 2 ∈ Q ∧ ⁅x, y⁆ ∈ Q)
    (hmove : ∃ n ∈ Subgroup.normalizer (Q : Set G), n ∉ Subgroup.normalizer (E : Set G))
    (hmax : ∀ Q' : Subgroup G, Q < Q' → Q' ≤ T →
      Subgroup.normalizer (Q' : Set G) ≤ Subgroup.normalizer (E : Set G))
    (hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (E : Set G)) :
    Q < T ∧ (Nat.card T = 2 * Nat.card Q ∨ ∀ P : Subgroup G, P ≤ T →
      Subgroup.normalizer (Q : Set G) ⊓ Subgroup.normalizer (T : Set G) ≤
        Subgroup.normalizer (P : Set G) → P ≤ Q ∨ P ⊔ Q = T) := by
  have hTN : T ≤ Subgroup.normalizer (Q : Set G) := fun x hx => by
    apply mem_normalizer_of_forall_conj_mem
    intro y hy
    have h := (hTQ x hx y (hQT hy)).2
    have h' := Q.mul_mem h hy
    rwa [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ * y = x * y * x⁻¹ by group] at h'
  have hQE : Q ≤ Subgroup.normalizer (E : Set G) :=
    hQT.trans (Subgroup.le_normalizer.trans hNT)
  have hlt : Q < T := by
    refine lt_of_le_of_ne hQT fun h => ?_
    obtain ⟨n, hn, hnE⟩ := hmove
    exact hnE (hNT (by rw [← h]; exact hn))
  refine ⟨hlt, ?_⟩
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  have hQN : Q ≤ N := Subgroup.le_normalizer
  have hQ₁n : (Q.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).2 le_rfl
  have hT₁ : IsSylowOf 2 (T.subgroupOf N) ⊤ := by
    rw [isSylowOf_iff]
    obtain ⟨-, hTp, hTi⟩ := isSylowOf_iff.1 hT
    rw [Subgroup.relIndex_top_right] at hTi
    refine ⟨le_top, hTp.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    intro h
    exact hTi (h.trans (Subgroup.relIndex_dvd_index_of_le hTN))
  have hlt₁ : Q.subgroupOf N < T.subgroupOf N := by
    refine lt_of_le_of_ne (fun x hx => hQT hx) fun h => ?_
    obtain ⟨t, htT, htQ⟩ := IsConcreteLE.exists_of_lt hlt
    have ht : (⟨t, hTN htT⟩ : N) ∈ T.subgroupOf N := htT
    rw [← h] at ht
    exact htQ ht
  have hY₁ : (Subgroup.normalizer (E : Set G)).subgroupOf N ≠ ⊤ := by
    intro h
    obtain ⟨n, hn, hnE⟩ := hmove
    have hn' : (⟨n, hn⟩ : N) ∈ (Subgroup.normalizer (E : Set G)).subgroupOf N := by
      rw [h]
      exact Subgroup.mem_top _
    exact hnE hn'
  have hmax₁ : ∀ Q₁' : Subgroup N, Q.subgroupOf N < Q₁' → Q₁' ≤ T.subgroupOf N →
      Subgroup.normalizer (Q₁' : Set N) ≤ (Subgroup.normalizer (E : Set G)).subgroupOf N := by
    intro Q₁' hlt' hle z hz
    have hQ'lt : Q < Q₁'.map N.subtype := by
      refine lt_of_le_of_ne ?_ ?_
      · intro q hq
        exact ⟨⟨q, hQN hq⟩, hlt'.le hq, rfl⟩
      · intro h
        obtain ⟨w, hwQ', hwQ⟩ := IsConcreteLE.exists_of_lt hlt'
        apply hwQ
        have hwG : (w : G) ∈ Q := by
          rw [h]
          exact ⟨w, hwQ', rfl⟩
        exact hwG
    have hQ'T : Q₁'.map N.subtype ≤ T := by
      rintro _ ⟨w, hw, rfl⟩
      exact hle hw
    have hzN : (z : G) ∈ Subgroup.normalizer ((Q₁'.map N.subtype : Subgroup G) : Set G) := by
      apply mem_normalizer_of_forall_conj_mem
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨z * w * z⁻¹, (Subgroup.mem_normalizer_iff.1 hz w).1 hw, rfl⟩
    exact hmax _ hQ'lt hQ'T hzN
  have key := tr_of_normal_good_Q (Z := N) (T := T.subgroupOf N) (Q := Q.subgroupOf N)
    (Y := (Subgroup.normalizer (E : Set G)).subgroupOf N) hT₁ (fun x hx => hQT hx) hlt₁
    (fun x hx y hy => hTQ x hx y hy) hY₁ (fun x hx => hQE hx) hmax₁
  rcases key with h2 | hTR
  · left
    have h1 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
    have h1' := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
    rw [h1, h1'] at h2
    exact h2
  · right
    intro P hPT hNP
    have hPN : P ≤ N := hPT.trans hTN
    have h1 := hTR (P.subgroupOf N) (fun x hx => hPT hx) (by
      intro z hz
      have hz' : (z : G) ∈ Subgroup.normalizer (T : Set G) := by
        apply mem_normalizer_of_forall_conj_mem
        intro y hy
        exact (Subgroup.mem_normalizer_iff.1 hz ⟨y, hTN hy⟩).1 hy
      have hz'' := hNP ⟨z.2, hz'⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact Subgroup.mem_normalizer_iff.1 hz'' (y : G))
    rcases h1 with h1 | h1
    · left
      intro x hx
      have hx' : (⟨x, hPN hx⟩ : N) ∈ P.subgroupOf N := hx
      exact h1 hx'
    · right
      refine le_antisymm (sup_le hPT hQT) fun t ht => ?_
      have ht' : (⟨t, hTN ht⟩ : N) ∈ T.subgroupOf N := ht
      rw [← h1] at ht'
      obtain ⟨p, hp, q, hq, hpq⟩ := Subgroup.mem_sup_of_normal_right.1 ht'
      have htpq : t = (p : G) * (q : G) := congrArg Subtype.val hpq.symm
      rw [htpq]
      exact Subgroup.mul_mem_sup hp hq

theorem tr_of_good_Q_uniform {G : Type} [Group G] [Finite G]
    {T E Q : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hQT : Q ≤ T)
    (hTQ : ∀ x ∈ T, ∀ y ∈ T, x ^ 2 ∈ Q ∧ ⁅x, y⁆ ∈ Q)
    (hmove : ∃ n ∈ Subgroup.normalizer (Q : Set G), n ∉ Subgroup.normalizer (E : Set G))
    (hmax : ∀ Q' : Subgroup G, Q < Q' → Q' ≤ T →
      Subgroup.normalizer (Q' : Set G) ≤ Subgroup.normalizer (E : Set G))
    (hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (E : Set G)) :
    Q < T ∧ ∀ P : Subgroup G, P ≤ T →
      Subgroup.normalizer (Q : Set G) ⊓ Subgroup.normalizer (T : Set G) ≤
        Subgroup.normalizer (P : Set G) → P ≤ Q ∨ P ⊔ Q = T := by
  obtain ⟨hlt, h⟩ := tr_of_good_Q_strong hT hQT hTQ hmove hmax hNT
  refine ⟨hlt, ?_⟩
  rcases h with h2 | h
  · intro P hPT _
    by_cases hPQ : P ≤ Q
    · exact Or.inl hPQ
    right
    have hle : P ⊔ Q ≤ T := sup_le hPT hQT
    have h1 : Q < P ⊔ Q := by
      refine lt_of_le_of_ne le_sup_right fun h => hPQ ?_
      rw [h]
      exact le_sup_left
    obtain ⟨c, hc⟩ : Nat.card Q ∣ Nat.card (P ⊔ Q : Subgroup G) :=
      Subgroup.card_dvd_of_le le_sup_right
    have hd : Nat.card (P ⊔ Q : Subgroup G) ∣ Nat.card T := Subgroup.card_dvd_of_le hle
    have hq : 0 < Nat.card Q := Nat.card_pos
    have hc2 : c ∣ 2 := by
      refine Nat.dvd_of_mul_dvd_mul_left hq ?_
      rw [← hc]
      rw [h2, mul_comm 2] at hd
      exact hd
    have hlt' := Subgroup.card_lt_of_lt h1
    rcases (Nat.dvd_prime Nat.prime_two).1 hc2 with rfl | rfl
    · omega
    · exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  · exact fun P hPT hNP => h P hPT hNP

end CFSG.CGT.PushingUpLit.T2KSW
