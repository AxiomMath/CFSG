module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveFrameKer
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoAssembly

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwFive

open scoped MatrixGroups
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.Open

theorem fiveZpowers_pow_eq_one {G : Type*} [Group G] {c : G} (hc : c ^ 5 = 1) {g : G}
    (hg : g ∈ Subgroup.zpowers c) : g ^ 5 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]

theorem fiveZpowers_commute {G : Type*} [Group G] {c : G} {g h : G}
    (hg : g ∈ Subgroup.zpowers c) (hh : h ∈ Subgroup.zpowers c) : g * h = h * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  rw [← zpow_add, ← zpow_add, add_comm]

theorem card_pi_fiveZpowers {G : Type*} [Group G] {c : G} (hc : orderOf c = 5) (n : ℕ) :
    Nat.card ↥(Subgroup.pi Set.univ fun _ : Fin n => Subgroup.zpowers c) = 5 ^ n := by
  let e : ↥(Subgroup.pi Set.univ fun _ : Fin n => Subgroup.zpowers c) ≃
      (∀ i : Fin n, ↥(Subgroup.zpowers c)) :=
    { toFun := fun x i => ⟨x.1 i, (Subgroup.mem_pi _).1 x.2 i (Set.mem_univ i)⟩
      invFun := fun y => ⟨fun i => (y i).1, (Subgroup.mem_pi _).2 fun i _ => (y i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_pi]
  simp [Nat.card_zpowers, hc]

theorem nat_sq_sub_one_eq_mul (q : ℕ) (hq : 1 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have h : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
  rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]


theorem exists_elemAbelian_six {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h5 : 5 ∣ ℓ ^ f + 1) :
    ∃ E : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 6 ∧ E ≤ frameTorusGroup σ.toRingHom := by
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hkcard : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = ℓ ^ f :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hℓ hf hK hσ'
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hSL : 5 ∣ Nat.card SL(2, RingHom.eqLocusField σ.toRingHom (RingHom.id K)) := by
    rw [card_specialLinear_fin_two, hkcard, nat_sq_sub_one_eq_mul (ℓ ^ f) (by omega)]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h5 (ℓ ^ f - 1)) (ℓ ^ f)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 5 hSL
  have hN : 5 ∣ Nat.card (normOne σ.toRingHom) := h5.trans (dvd_card_normOne hq2 hK hσ')
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 5 hN
  have hc5 : c ^ 5 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hu5 : u ^ 5 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup ((Fin 4 → SL(2, RingHom.eqLocusField σ.toRingHom
      (RingHom.id K))) × (↥(normOne σ.toRingHom) × ↥(normOne σ.toRingHom))),
      Q = (Subgroup.pi Set.univ fun _ : Fin 4 => Subgroup.zpowers c).prod
        ((Subgroup.zpowers u).prod (Subgroup.zpowers u)) := ⟨_, rfl⟩
  have hPpow : ∀ f ∈ Subgroup.pi Set.univ fun _ : Fin 4 => Subgroup.zpowers c, f ^ 5 = 1 := by
    intro f hf
    funext i
    exact fiveZpowers_pow_eq_one hc5 ((Subgroup.mem_pi _).1 hf i (Set.mem_univ i))
  have hRpow : ∀ s ∈ Subgroup.zpowers u, s ^ 5 = 1 := fun s hs =>
    fiveZpowers_pow_eq_one hu5 hs
  have hPcomm : ∀ f ∈ Subgroup.pi Set.univ fun _ : Fin 4 => Subgroup.zpowers c,
      ∀ g ∈ Subgroup.pi Set.univ fun _ : Fin 4 => Subgroup.zpowers c, f * g = g * f := by
    intro f hf g hg
    funext i
    exact fiveZpowers_commute ((Subgroup.mem_pi _).1 hf i (Set.mem_univ i))
      ((Subgroup.mem_pi _).1 hg i (Set.mem_univ i))
  have hQpow : ∀ x ∈ Q, x ^ 5 = 1 := by
    rintro ⟨f, s, t⟩ hx
    rw [hQ] at hx
    obtain ⟨hf, hst⟩ := Subgroup.mem_prod.1 hx
    obtain ⟨hs, ht⟩ := Subgroup.mem_prod.1 hst
    exact Prod.ext (hPpow f hf) (Prod.ext (hRpow s hs) (hRpow t ht))
  have hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    rintro ⟨f, s, t⟩ hx ⟨g, s', t'⟩ hy
    rw [hQ] at hx hy
    obtain ⟨hf, hst⟩ := Subgroup.mem_prod.1 hx
    obtain ⟨hg, hst'⟩ := Subgroup.mem_prod.1 hy
    obtain ⟨hs, ht⟩ := Subgroup.mem_prod.1 hst
    obtain ⟨hs', ht'⟩ := Subgroup.mem_prod.1 hst'
    exact Prod.ext (hPcomm f hf g hg)
      (Prod.ext (fiveZpowers_commute hs hs') (fiveZpowers_commute ht ht'))
  have hQel : IsElemAbelian 5 Q :=
    ⟨⟨⟨fun a b => Subtype.ext (hQcomm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hQpow x hx⟩
  have hQcard : Nat.card ↥Q = 5 ^ 6 := by
    rw [hQ, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      card_pi_fiveZpowers hc 4, Nat.card_zpowers, hu]
    norm_num
  have hdisj : Disjoint Q (frameTorusMap σ.toRingHom).ker := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxk
    exact frameTorusMap_eq_one_of_pow σ.toRingHom Nat.prime_five (le_refl 5) x (m := 1)
      (by rw [pow_one]; exact hQpow x hxQ) (MonoidHom.mem_ker.1 hxk)
  have hcard : Nat.card ↥(Q.map (frameTorusMap σ.toRingHom)) = 5 ^ 6 := by
    rw [card_map_eq_of_disjoint_ker (frameTorusMap σ.toRingHom) hdisj, hQcard]
  have hel : IsElemAbelian 5 (Q.map (frameTorusMap σ.toRingHom)) :=
    CFSG.Open.IsElemAbelian.map hQel (frameTorusMap σ.toRingHom)
  have hle : Q.map (frameTorusMap σ.toRingHom) ≤ frameTorusGroup σ.toRingHom := by
    rintro _ ⟨⟨f, s, t⟩, -, rfl⟩
    rw [frameTorusMap_apply]
    have hmem : frameMap σ.toRingHom f ∈ Subgroup.map
        (MonoidHom.noncommPiCoprod (frameHom σ.toRingHom) (frameHom_pairwise_commute σ.toRingHom))
        ⊤ := ⟨f, Subgroup.mem_top _, rfl⟩
    have h1 : frameMap σ.toRingHom f ∈ ⨆ i, (frameHom σ.toRingHom i).range :=
      map_noncommPiCoprod_le (frameHom σ.toRingHom) (frameHom_pairwise_commute σ.toRingHom) ⊤ hmem
    have h2 : torusG σ.toRingHom (s, t) ∈ (torusG σ.toRingHom).range :=
      MonoidHom.mem_range.2 ⟨(s, t), rfl⟩
    unfold frameTorusGroup
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  exact ⟨Q.map (frameTorusMap σ.toRingHom), hel, hcard, hle⟩

end CFSG.LieType.SeitzGeneration.ExcHigh.TwFive
