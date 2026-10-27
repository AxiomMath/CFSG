module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.Glauberman281.Main
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem card_sup_eq_mul {Y Q : Subgroup G} (hcop : Nat.Coprime (Nat.card Y) (Nat.card Q))
    (hperm : ∀ w ∈ Y ⊔ Q, ∃ y ∈ Y, ∃ q ∈ Q, w = y * q) :
    Nat.card ↥(Y ⊔ Q) = Nat.card Y * Nat.card Q := by
  have hbot : Y ⊓ Q = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  let f : Y × Q → ↥(Y ⊔ Q) := fun x =>
    ⟨(x.1 : G) * (x.2 : G), mul_mem (mem_sup_left x.1.2) (mem_sup_right x.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨y, q⟩ ⟨y', q'⟩ h
      have h1 : (y : G) * q = y' * q' := congrArg Subtype.val h
      have h2 : (y' : G)⁻¹ * y = q' * (q : G)⁻¹ := by
        calc (y' : G)⁻¹ * y = (y' : G)⁻¹ * (y * q) * (q : G)⁻¹ := by group
          _ = (y' : G)⁻¹ * (y' * q') * (q : G)⁻¹ := by rw [h1]
          _ = q' * (q : G)⁻¹ := by group
      have hmemY : (y' : G)⁻¹ * y ∈ Y := mul_mem (inv_mem y'.2) y.2
      have hmemQ : (y' : G)⁻¹ * y ∈ Q := h2 ▸ mul_mem q'.2 (inv_mem q.2)
      have h3 : (y' : G)⁻¹ * y = 1 := by
        have : (y' : G)⁻¹ * y ∈ Y ⊓ Q := ⟨hmemY, hmemQ⟩
        rwa [hbot, Subgroup.mem_bot] at this
      have hyy : (y : G) = y' := by
        have := congrArg (fun z => (y' : G) * z) h3
        simpa using this
      have hqq : (q : G) = q' := by
        rw [h3] at h2
        have : (q' : G) * (q : G)⁻¹ = 1 := h2.symm
        exact (mul_inv_eq_one.1 this).symm
      exact Prod.ext (Subtype.ext hyy) (Subtype.ext hqq)
    · rintro ⟨w, hw⟩
      obtain ⟨y, hy, q, hq, rfl⟩ := hperm w hw
      exact ⟨(⟨y, hy⟩, ⟨q, hq⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem glauberman_product (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) {Y Q : Subgroup G}
    (hY : IsPGroup 2 Y) (hQ : IsPGroup p Q)
    (hperm : ∀ w ∈ Y ⊔ Q, ∃ y ∈ Y, ∃ q ∈ Q, w = y * q) (hF : CharTwo (Y ⊔ Q)) :
    ∀ w ∈ Y ⊔ Q, ∃ a ∈ (Y ⊔ Q) ⊓ normalizer (thompsonJ Y : Set G),
      ∃ b ∈ (Y ⊔ Q) ⊓ normalizer (quasithinOmegaOneCenter Y : Set G), w = a * b := by
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hY.exists_card_eq
  obtain ⟨b, hb⟩ := hQ.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card Q) := by
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hcard := card_sup_eq_mul hcop hperm
  have hSyl : IsSylowTwoOf Y (Y ⊔ Q) := by
    refine ⟨le_sup_left, hY, ?_⟩
    have h1 := Subgroup.card_mul_index ((Y).subgroupOf (Y ⊔ Q))
    have h2 : Nat.card ((Y).subgroupOf (Y ⊔ Q)) = Nat.card Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    rw [h2, hcard] at h1
    have h3 : ((Y).subgroupOf (Y ⊔ Q)).index = Nat.card Q := by
      have hpos : 0 < Nat.card Y := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos h1
    rw [h3, hb]
    intro hd
    have := (Nat.prime_two.dvd_of_dvd_pow hd)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
  have hdiv : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(Y ⊔ Q) → r = 2 ∨ r = p := by
    intro r hr hrd
    rw [hcard, ha, hb] at hrd
    rcases (Nat.Prime.dvd_mul hr).1 hrd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h))
  exact glaubermanTwoP_holds G p hp h5 (Y ⊔ Q) Y hdiv hF hSyl


theorem exists_mul_of_factorization {Y Q N₁ N₂ : Subgroup G}
    (hperm : ∀ w ∈ Y ⊔ Q, ∃ y ∈ Y, ∃ q ∈ Q, w = y * q)
    (hY₁ : Y ≤ N₁) (hY₂ : Y ≤ N₂) (hN₁ : N₁ ≤ Y ⊔ Q)
    (hfac : ∀ w ∈ Y ⊔ Q, ∃ a ∈ N₁, ∃ b ∈ N₂, w = a * b) :
    ∀ q ∈ Q, ∃ a ∈ Q ⊓ N₁, ∃ b ∈ Q ⊓ N₂, q = a * b := by
  intro q hq
  obtain ⟨a₁, ha₁, b₁, hb₁, hq1⟩ := hfac q (mem_sup_right hq)
  obtain ⟨y, hy, q', hq', hya⟩ := hperm a₁⁻¹ (hN₁ (inv_mem ha₁))
  have hq'N : q' ∈ N₁ := by
    have : q' = y⁻¹ * a₁⁻¹ := by rw [hya]; group
    rw [this]
    exact mul_mem (inv_mem (hY₁ hy)) (inv_mem ha₁)
  have hcN : b₁⁻¹ * y ∈ N₂ := mul_mem (inv_mem hb₁) (hY₂ hy)
  have h1 : q⁻¹ = (b₁⁻¹ * y) * q' := by
    calc q⁻¹ = b₁⁻¹ * a₁⁻¹ := by rw [hq1, mul_inv_rev]
      _ = b₁⁻¹ * (y * q') := by rw [hya]
      _ = (b₁⁻¹ * y) * q' := by group
  have hcQ : b₁⁻¹ * y ∈ Q := by
    have : b₁⁻¹ * y = q⁻¹ * q'⁻¹ := by rw [h1]; group
    rw [this]
    exact mul_mem (inv_mem hq) (inv_mem hq')
  refine ⟨q'⁻¹, Subgroup.mem_inf.2 ⟨inv_mem hq', inv_mem hq'N⟩, (b₁⁻¹ * y)⁻¹,
    Subgroup.mem_inf.2 ⟨inv_mem hcQ, inv_mem hcN⟩, ?_⟩
  calc q = (q⁻¹)⁻¹ := (inv_inv q).symm
    _ = ((b₁⁻¹ * y) * q')⁻¹ := by rw [h1]
    _ = q'⁻¹ * (b₁⁻¹ * y)⁻¹ := mul_inv_rev _ _

theorem le_normalizer_omegaOneCenter_self (Y : Subgroup G) :
    Y ≤ normalizer (quasithinOmegaOneCenter Y : Set G) := by
  have hZ : quasithinOmegaOneCenter Y ≤ centralizer (Y : Set G) := by
    refine (Subgroup.closure_le _).2 fun z hz => ?_
    exact hz.1.2
  have hY : Y ≤ centralizer (quasithinOmegaOneCenter Y : Set G) :=
    Subgroup.le_centralizer_iff.2 hZ
  exact hY.trans (Subgroup.centralizer_le_normalizer _)

theorem glauberman_Q_product (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) {Y Q : Subgroup G}
    (hY : IsPGroup 2 Y) (hQ : IsPGroup p Q)
    (hperm : ∀ w ∈ Y ⊔ Q, ∃ y ∈ Y, ∃ q ∈ Q, w = y * q) (hF : CharTwo (Y ⊔ Q)) :
    ∀ q ∈ Q, ∃ a ∈ Q ⊓ normalizer (thompsonJ Y : Set G),
      ∃ b ∈ Q ⊓ normalizer (quasithinOmegaOneCenter Y : Set G), q = a * b := by
  have hprod := glauberman_product p hp h5 hY hQ hperm hF
  have hY₁ : Y ≤ (Y ⊔ Q) ⊓ normalizer (thompsonJ Y : Set G) :=
    le_inf le_sup_left (B2F.R_le_normalizer_thompsonJ Y)
  have hY₂ : Y ≤ (Y ⊔ Q) ⊓ normalizer (quasithinOmegaOneCenter Y : Set G) :=
    le_inf le_sup_left (le_normalizer_omegaOneCenter_self Y)
  intro q hq
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_factorization hperm hY₁ hY₂ inf_le_left hprod q hq
  exact ⟨a, ⟨ha.1, ha.2.2⟩, b, ⟨hb.1, hb.2.2⟩, hab⟩

theorem card_le_of_pRank_le_one {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hAe : ∀ a ∈ A, a ^ p = 1) (hr : CFSG.Open.pRank p A ≤ 1) : Nat.card A ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hApg : IsPGroup p A := fun a => by
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hAe a a.2
  obtain ⟨n, hn⟩ := hApg.exists_card_eq
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · rw [hn]
    calc p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  · exfalso
    obtain ⟨K, hK, -, hKA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := G) (p := p)
      (n := 2) (H := ⊥) hp (by simp) (hn ▸ pow_dvd_pow p hn2) bot_le
    haveI : IsMulCommutative ↥K := IsPGroup.isMulCommutative_of_card_eq_prime_sq hK
    have hE : IsElemAbelian p K := ⟨inferInstance, fun x hx => hAe x (hKA hx)⟩
    have := CFSG.SectionRank.le_pRank hp.one_lt hKA hE hK
    omega

theorem two_le_pRank_of_mul {p : ℕ} (hp : p.Prime) {Q A B : Subgroup G}
    (hQe : ∀ q ∈ Q, q ^ p = 1) (hQc : ¬ IsCyclic Q) (hA : A ≤ Q) (hB : B ≤ Q)
    (hAB : ∀ q ∈ Q, ∃ a ∈ A, ∃ b ∈ B, q = a * b) (hint : A ⊓ B ≠ ⊥) :
    2 ≤ CFSG.Open.pRank p A ∨ 2 ≤ CFSG.Open.pRank p B := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  have hAc := card_le_of_pRank_le_one hp (fun a ha => hQe a (hA ha)) (by omega : _ ≤ 1)
  have hBc := card_le_of_pRank_le_one hp (fun b hb => hQe b (hB hb)) (by omega : _ ≤ 1)
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hint)
  have hxA : x ∈ A := (Subgroup.mem_inf.1 hx).1
  have hxB : x ∈ B := (Subgroup.mem_inf.1 hx).2
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxp : x ^ p = 1 := hQe x (hA hxA)
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1'
  have hcz : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hord]
  have hAz : A = Subgroup.zpowers x :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxA) (by rw [hcz]; exact hAc)).symm
  have hBz : B = Subgroup.zpowers x :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxB) (by rw [hcz]; exact hBc)).symm
  have hQz : Q = Subgroup.zpowers x := by
    apply le_antisymm
    · intro q hq
      obtain ⟨a, ha, b, hb, rfl⟩ := hAB q hq
      rw [hAz] at ha
      rw [hBz] at hb
      exact mul_mem ha hb
    · exact Subgroup.zpowers_le.2 (hA hxA)
  apply hQc
  have hcQ : Nat.card Q = p := by rw [hQz, hcz]
  exact isCyclic_of_prime_card hcQ

end CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281
