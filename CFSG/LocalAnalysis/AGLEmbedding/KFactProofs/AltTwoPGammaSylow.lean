module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltBasic

public section

namespace CFSG.AGLEmbedding

namespace AltTwoPGammaSylow

open CFSG.Open CFSG.Quasithin Equiv

theorem one_le_pRank_zpowers {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) {y : X}
    (hy : orderOf y = p) : 1 ≤ Open.pRank p (Subgroup.zpowers y) := by
  apply le_csSup
  · refine ⟨Nat.card X, fun k hk => ?_⟩
    obtain ⟨E, -, -, hE⟩ := hk
    have h1 : p ^ k ≤ Nat.card X := hE ▸ Subgroup.card_le_card_group E
    have h2 : k < p ^ k := Nat.lt_pow_self hp.one_lt
    omega
  · have hel : IsElemAbelian p (Subgroup.zpowers y) := by
      refine ⟨inferInstance, fun x hx => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hy, pow_orderOf_eq_one,
        one_zpow]
    have hc : Nat.card (Subgroup.zpowers y) = p ^ 1 := by rw [Nat.card_zpowers, hy, pow_one]
    exact ⟨Subgroup.zpowers y, le_rfl, hel, hc⟩

theorem not_cube_dvd_factorial_two_mul {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 3 ∣ (2 * p).factorial := by
  intro h
  have h1 := (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp h
  have h2 := Nat.factorization_factorial_le_div_pred hp (2 * p)
  have h3 : 2 * p / (p - 1) < 3 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  omega

variable {p : ℕ}

def half (p : ℕ) : Finset (Fin (2 * p)) := Finset.univ.filter fun i => (i : ℕ) < p

theorem card_half : (half p).card = p := by
  rw [half, Fin.card_filter_val_lt]
  omega

theorem card_half_compl : (half p)ᶜ.card = p := by
  rw [Finset.card_compl, card_half, Fintype.card_fin]
  omega

abbrev altOn (s : Finset (Fin (2 * p))) : Subgroup (alternatingGroup (Fin (2 * p))) :=
  (alternatingGroup.ofSubtype s).range

theorem altOn_perfect {s : Finset (Fin (2 * p))} (hs : 5 ≤ s.card) :
    ⁅altOn s, altOn s⁆ = altOn s := by
  have h5 : 5 ≤ Nat.card s := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hs
  have htop : ⁅(⊤ : Subgroup ↥(alternatingGroup s)), (⊤ : Subgroup ↥(alternatingGroup s))⁆ =
      ⊤ := by
    apply Subgroup.map_injective (alternatingGroup s).subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      commutator_alternatingGroup_eq_self h5]
  show ⁅(alternatingGroup.ofSubtype s).range, (alternatingGroup.ofSubtype s).range⁆ =
    (alternatingGroup.ofSubtype s).range
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]

theorem dvd_card_altOn {s : Finset (Fin (2 * p))} (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : s.card = p) : p ∣ Nat.card (altOn s) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).toEquiv]
  have hc : Nat.card s = p := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hs]
  have : Nontrivial s := by
    rw [← Finite.one_lt_card_iff_nontrivial, hc]
    exact hp.one_lt
  have h := two_mul_nat_card_alternatingGroup (α := s)
  rw [Nat.card_perm, hc] at h
  have h1 : p ∣ 2 * Nat.card (alternatingGroup s) := h ▸ Nat.dvd_factorial hp.pos le_rfl
  exact (Nat.Coprime.dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)).mp h1

theorem commute_altOn {s : Finset (Fin (2 * p))} {x y : alternatingGroup (Fin (2 * p))}
    (hx : x ∈ altOn s) (hy : y ∈ altOn sᶜ) : x * y = y * x := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  apply Subtype.ext
  change Perm.ofSubtype u.1 * Perm.ofSubtype v.1 = Perm.ofSubtype v.1 * Perm.ofSubtype u.1
  refine Perm.Disjoint.commute fun i => ?_
  by_cases hi : i ∈ s
  · exact Or.inr (Perm.ofSubtype_apply_of_not_mem _ (by simpa using hi))
  · exact Or.inl (Perm.ofSubtype_apply_of_not_mem _ hi)

theorem altOn_inf_compl (s : Finset (Fin (2 * p))) : altOn s ⊓ altOn sᶜ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hx
  apply Subtype.ext
  refine Perm.ext fun i => ?_
  change (x : Perm (Fin (2 * p))) i = i
  by_cases hi : i ∈ s
  · rw [← hv]
    exact Perm.ofSubtype_apply_of_not_mem _ (by simpa using hi)
  · rw [← hu]
    exact Perm.ofSubtype_apply_of_not_mem _ hi

end AltTwoPGammaSylow

open CFSG.Open CFSG.Quasithin AltTwoPGammaSylow

theorem kFactAltTwoPGammaSylow : KFactAltTwoPGammaSylow := by
  intro K _ _ p hp hp5 hA T
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e⟩ := hA
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p (dvd_card_altOn hp hp2 (card_half (p := p)))
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' p
    (dvd_card_altOn hp hp2 (card_half_compl (p := p)))
  set a' : alternatingGroup (Fin (2 * p)) := a.1
  set b' : alternatingGroup (Fin (2 * p)) := b.1
  have ha' : orderOf a' = p := (Subgroup.orderOf_coe a).trans ha
  have hb' : orderOf b' = p := (Subgroup.orderOf_coe b).trans hb
  have hab : a' * b' = b' * a' := commute_altOn a.2 b.2
  have hzp : ∀ {x : alternatingGroup (Fin (2 * p))}, orderOf x = p →
      IsPGroup p (Subgroup.zpowers x) := fun hx =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  set T₀ := Subgroup.zpowers a' ⊔ Subgroup.zpowers b'
  have hnorm : Subgroup.zpowers b' ≤ Subgroup.normalizer (Subgroup.zpowers a' : Set _) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun n hn => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : b' * a' ^ k * b'⁻¹ = a' ^ k := by
      rw [((Commute.zpow_left (show Commute a' b' from hab) k).symm).eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem_zpowers a' k
  have hT₀p : IsPGroup p T₀ := (hzp ha').to_sup_of_normal_left' (hzp hb') hnorm
  have hinf : Subgroup.zpowers a' ⊓ Subgroup.zpowers b' = ⊥ := by
    rw [eq_bot_iff, ← altOn_inf_compl (half p)]
    exact inf_le_inf (Subgroup.zpowers_le.mpr a.2) (Subgroup.zpowers_le.mpr b.2)
  have hT₀c : p * p ≤ Nat.card T₀ := by
    have := mul_card_le_of_inf_eq_bot (le_sup_left : Subgroup.zpowers a' ≤ T₀) le_sup_right hinf
    rwa [Nat.card_zpowers, Nat.card_zpowers, ha', hb'] at this
  set φ₀ : alternatingGroup (Fin (2 * p)) →* K := e.symm.toMonoidHom
  have hφ₀ : Function.Injective φ₀ := e.symm.injective
  have hT₀Kp : IsPGroup p (T₀.map φ₀) := hT₀p.map φ₀
  obtain ⟨T', hT'⟩ := hT₀Kp.exists_le_sylow
  have hT'c : Nat.card (T' : Subgroup K) ≤ p * p := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T'.isPGroup'
    have hdvd : p ^ k ∣ Nat.card K := hk ▸ Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_congr e.toEquiv] at hdvd
    have h2 := two_mul_card_alternatingGroup_fin (n := 2 * p) (by omega)
    have hk2 : k ≤ 2 := by
      by_contra h3
      exact not_cube_dvd_factorial_two_mul hp hp5
        (h2 ▸ ((pow_dvd_pow p (by omega : 3 ≤ k)).trans hdvd).trans (dvd_mul_left _ _))
    rw [hk, ← pow_two]
    exact Nat.pow_le_pow_right hp.pos hk2
  have hT'eq : T₀.map φ₀ = T' := Subgroup.eq_of_le_of_card_ge hT' (by
    rw [Subgroup.card_map_of_injective hφ₀]
    omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T' T
  set φ : alternatingGroup (Fin (2 * p)) →* K := (MulAut.conj g).toMonoidHom.comp φ₀
  have hφ : Function.Injective φ := (MulAut.conj g).injective.comp hφ₀
  have hTφ : (T : Subgroup K) = T₀.map φ := by
    ext k
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv, ← hT'eq]
    constructor
    · rintro ⟨t, ht, htk⟩
      refine ⟨t, ht, ?_⟩
      change g * φ₀ t * g⁻¹ = k
      rw [htk]
      group
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, ht, ?_⟩
      change φ₀ t = g⁻¹ * (g * φ₀ t * g⁻¹) * g
      group
  set x := φ a'
  set y := φ b'
  have hx : orderOf x = p := by rw [orderOf_injective φ hφ, ha']
  have hy : orderOf y = p := by rw [orderOf_injective φ hφ, hb']
  have hxT : x ∈ (T : Subgroup K) :=
    hTφ ▸ ⟨a', (le_sup_left : Subgroup.zpowers a' ≤ T₀) (Subgroup.mem_zpowers a'), rfl⟩
  have hyT : y ∈ (T : Subgroup K) :=
    hTφ ▸ ⟨b', (le_sup_right : Subgroup.zpowers b' ≤ T₀) (Subgroup.mem_zpowers b'), rfl⟩
  have hcore : ∀ {w : K}, w ∈ (T : Subgroup K) → orderOf w = p →
      ∀ B : Subgroup K, ⁅B, B⁆ = B → (∀ u ∈ B, u * w = w * u) →
        B ≤ perfectCore (GLBCore p 1 (T : Subgroup K)) := by
    intro w hwT hw B hBp hBw
    refine le_perfectCore_of_perfect (fun u hu => ?_) hBp
    have hN : u ∈ Subgroup.normalizer (Subgroup.zpowers w : Set K) := by
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have : u * w ^ k * u⁻¹ = w ^ k := by
        rw [(Commute.zpow_right (show Commute u w from hBw u hu) k).eq, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.zpow_mem_zpowers w k
    have hmem : Subgroup.normalizer (Subgroup.zpowers w : Set K) ≤
        GLBCore p 1 (T : Subgroup K) := by
      unfold GLBCore
      exact le_sSup ⟨Subgroup.zpowers w, Subgroup.zpowers_le.mpr hwT,
        one_le_pRank_zpowers hp hw, rfl⟩
    exact hmem hN
  have hB₁ := hcore hyT hy ((altOn (half p)).map φ)
    (by rw [← Subgroup.map_commutator, altOn_perfect (by rw [card_half]; exact hp5)])
    (by
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_mul, ← map_mul, commute_altOn hu b.2])
  have hB₂ := hcore hxT hx ((altOn (half p)ᶜ).map φ)
    (by rw [← Subgroup.map_commutator, altOn_perfect (by rw [card_half_compl]; exact hp5)])
    (by
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_mul, ← map_mul, ← commute_altOn a.2 hu])
  intro t ht
  rw [hTφ, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at ht
  exact (sup_le (Subgroup.zpowers_le.mpr (hB₁ ⟨a', a.2, rfl⟩))
    (Subgroup.zpowers_le.mpr (hB₂ ⟨b', b.2, rfl⟩))) ht

end CFSG.AGLEmbedding
