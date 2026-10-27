module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Burnside
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltPerm
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

section Transport

variable {G X : Type} [Group G] [Group X] {f : G →* X}

theorem thr_isElemAbelian_comap {p : ℕ} (hf : Function.Injective f) {E : Subgroup X}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.comap f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · have h1 := hE.1.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · rw [map_pow, map_one]
    exact hE.2 _ hx

theorem thr_isElemAbelian_map {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map hE _

theorem thr_map_invariantTwoJoinIn (hf : Function.Injective f) (D K : Subgroup G) :
    (invariantTwoJoinIn D K).map f = invariantTwoJoinIn (D.map f) (K.map f) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine invariantTwoJoinIn_le_of_forall fun Y hYK hY hDY => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_invariantTwoJoinIn (Subgroup.map_mono hYK) (hY.map f)
      ((Subgroup.map_mono hDY).trans (Subgroup.le_normalizer_map f))
  · refine invariantTwoJoinIn_le_of_forall fun Y hYK hY hDY => ?_
    have hYr : Y ≤ f.range := hYK.trans (Subgroup.map_le_range f K)
    rw [← Subgroup.map_comap_eq_self hYr]
    refine Subgroup.map_mono (le_invariantTwoJoinIn ?_ (hY.comap_of_injective f hf) ?_)
    · rw [← Subgroup.comap_map_eq_self_of_injective hf K]
      exact Subgroup.comap_mono hYK
    · intro d hd
      exact Subgroup.le_normalizer_comap f (hDY (Subgroup.mem_map_of_mem f hd))

theorem thr_isPSignalizer_comap {p : ℕ} (hf : Function.Injective f) {D : Subgroup G} {d : G}
    {O : Subgroup X} (hO : IsPSignalizer p (D.map f) (f d) O) :
    IsPSignalizer p D d (O.comap f) where
  le_centralizer := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hO.le_centralizer hx)
    apply hf
    rw [map_mul, map_mul, this]
  normal := by
    intro c hc
    apply Subgroup.le_normalizer_comap f
    apply hO.normal
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← map_mul, ← map_mul, hc]
  coprime := Nat.Coprime.coprime_dvd_right (Subgroup.card_comap_dvd_of_injective O f hf) hO.coprime
  le := by
    intro W hWc hWp hDW
    rw [← Subgroup.map_le_iff_le_comap]
    apply hO.le
    · rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hWc hw)
      rw [← map_mul, ← map_mul, this]
    · rwa [Subgroup.card_map_of_injective hf]
    · exact (Subgroup.map_mono hDW).trans (Subgroup.le_normalizer_map f)

end Transport

section Join

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem thr_exists_mem_centralizer_coset {p : ℕ} (hp : p.Prime) {A U L : Subgroup X}
    (hA : IsPGroup p A) (hAL : A ≤ L) (hLn : L.Normal) (hAU : A ≤ normalizer (U : Set X))
    (hUL : ¬ p ∣ Nat.card (U ⊓ L : Subgroup X)) {u : X} (hu : u ∈ U) :
    ∃ c ∈ U ⊓ centralizer (A : Set X), c⁻¹ * u ∈ L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let F := {x : U // ((x : U) : X)⁻¹ * u ∈ L}
  let act : MulAction A F :=
    { smul := fun a x => ⟨⟨(a : X) * x.1 * (a : X)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hAU a.2) _).mp x.1.2⟩, by
          have haL : (a : X) ∈ L := hAL a.2
          have e : ((a : X) * ((x.1 : U) : X) * (a : X)⁻¹)⁻¹ * u =
              (a : X) * (((x.1 : U) : X)⁻¹ * (a : X)⁻¹ * ((x.1 : U) : X)⁻¹⁻¹) *
                (((x.1 : U) : X)⁻¹ * u) := by group
          rw [e]
          exact L.mul_mem (L.mul_mem haL (hLn.conj_mem _ (L.inv_mem haL) _)) x.2⟩
      one_smul := fun x => by
        apply Subtype.ext; apply Subtype.ext
        change (1 : X) * _ * (1 : X)⁻¹ = _
        group
      mul_smul := fun a b x => by
        apply Subtype.ext; apply Subtype.ext
        change ((a : X) * b) * _ * ((a : X) * b)⁻¹ =
          (a : X) * ((b : X) * _ * (b : X)⁻¹) * (a : X)⁻¹
        group }
  have hF : Nat.card F = Nat.card (U ⊓ L : Subgroup X) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨u⁻¹ * ((x.1 : U) : X), U.mul_mem (U.inv_mem hu) x.1.2, by
          have := L.inv_mem x.2
          simpa using this⟩
        invFun := fun y => ⟨⟨u * y, U.mul_mem hu y.2.1⟩, by
          have := L.inv_mem y.2.2
          simpa [mul_assoc] using this⟩
        left_inv := fun x => by
          apply Subtype.ext; apply Subtype.ext
          change u * (u⁻¹ * _) = _
          group
        right_inv := fun y => by
          apply Subtype.ext
          change u⁻¹ * (u * _) = _
          group }
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card F (hF ▸ hUL)
  refine ⟨x.1, ⟨x.1.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩, x.2⟩
  have h := congrArg (fun y : F => ((y.1 : U) : X)) (MulAction.mem_fixedPoints.mp hx ⟨a, ha⟩)
  change a * ((x.1 : U) : X) * a⁻¹ = x.1 at h
  calc a * ((x.1 : U) : X) = a * ((x.1 : U) : X) * a⁻¹ * a := by group
    _ = (x.1 : X) * a := by rw [h]

theorem thr_le_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D L Q U : Subgroup X}
    (hD : IsPGroup p D) (hDL : D ≤ L) (hLn : L.Normal)
    (hQ : ∀ g ∈ centralizer (D : Set X), p.Coprime (orderOf g) → g ∈ Q)
    (hU : IsPGroup 2 U) (hDU : D ≤ normalizer (U : Set X)) :
    U ≤ Q ⊔ invariantTwoJoinIn D L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2' : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  intro u hu
  have hUL2 : IsPGroup 2 (U ⊓ L : Subgroup X) := hU.to_inf_left
  have hUL : ¬ p ∣ Nat.card (U ⊓ L : Subgroup X) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUL2
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.pow_right k hp2')
  obtain ⟨c, ⟨hcU, hcC⟩, hcL⟩ := thr_exists_mem_centralizer_coset hp hD hDL hLn hDU hUL hu
  have hcQ : c ∈ Q := by
    refine hQ c hcC ?_
    obtain ⟨k, hk⟩ := hU ⟨c, hcU⟩
    have h1 : orderOf c ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_mk c hcU]
      exact orderOf_dvd_of_pow_eq_one hk
    exact Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right k hp2')
  have hDUL : D ≤ normalizer ((U ⊓ L : Subgroup X) : Set X) := by
    refine (le_inf hDU ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hN : U ⊓ L ≤ invariantTwoJoinIn D L := le_invariantTwoJoinIn inf_le_right hUL2 hDUL
  have hcu : c⁻¹ * u ∈ U ⊓ L := ⟨U.mul_mem (U.inv_mem hcU) hu, hcL⟩
  have e : u = c * (c⁻¹ * u) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hcQ (hN hcu)

theorem thr_normalizer_le_normalizer {D L : Subgroup X} (hLn : L.Normal) :
    normalizer (D : Set X) ≤ normalizer (invariantTwoJoinIn D L : Set X) := by
  intro g hg
  have hL : L.map (MulAut.conj g).toMonoidHom = L := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have h1 := invariantTwoJoinIn_map_le (K := L) hg
  rw [hL] at h1
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge h1 ?_).symm
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [Finite X] in
theorem thr_dvd_card_of_dvd_card_sup {p : ℕ} (hp : p.Prime) {Q J : Subgroup X}
    (hQJ : Q ≤ normalizer (J : Set X)) (hQ : p.Coprime (Nat.card Q))
    (h : p ∣ Nat.card (Q ⊔ J : Subgroup X)) : p ∣ Nat.card J := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hQJ
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hQJ
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient Q J hQJ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (J.subgroupOf (Q ⊔ J)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : J ≤ Q ⊔ J)).toEquiv] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · exact absurd (h1.trans (Subgroup.card_quotient_dvd_card _))
      ((Nat.Prime.coprime_iff_not_dvd hp).mp hQ)
  · exact h1

theorem thr_dvd_card_invariantTwoJoinIn {p : ℕ} {D L : Subgroup X} (hF : ThompsonFrame p D)
    (hLn : L.Normal) (hDL : D ≤ L) : p ∣ Nat.card (invariantTwoJoinIn D L) := by
  obtain ⟨Q, hQC, hQp, -, hQmem⟩ :=
    exists_normal_pComplement_centralizer hF.prime hF.elem.1 hF.sylow
  have hDp : IsPGroup p D := IsPGroup.of_card hF.card
  have hJ : invariantTwoJoinIn D ⊤ ≤ Q ⊔ invariantTwoJoinIn D L :=
    invariantTwoJoinIn_le_of_forall fun U _ hU hDU =>
      thr_le_sup hF.prime hF.odd hDp hDL hLn hQmem hU hDU
  have hQN : Q ≤ normalizer (invariantTwoJoinIn D L : Set X) :=
    hQC.trans ((Subgroup.centralizer_le_normalizer _).trans (thr_normalizer_le_normalizer hLn))
  exact thr_dvd_card_of_dvd_card_sup hF.prime hQN hQp (hF.join.trans (Subgroup.card_dvd_of_le hJ))

end Join

theorem ThompsonFrame.alt_data {p : ℕ} {X : Type} [Group X] [Finite X] {D : Subgroup X}
    (hF : ThompsonFrame p D) {L : Subgroup X} (hLn : L.Normal) (hDL : D ≤ L) {n : ℕ}
    (φ : L ≃* alternatingGroup (Fin n)) :
    n < 3 * p ∧ ∃ D' : Subgroup (alternatingGroup (Fin n)), IsElemAbelian p D' ∧
      Nat.card D' = p ^ 2 ∧
      (∀ d ∈ D', d ≠ 1 → ∃ O : Subgroup (alternatingGroup (Fin n)), IsPSignalizer p D' d O) ∧
      p ∣ Nat.card (invariantTwoJoinIn D' (⊤ : Subgroup (alternatingGroup (Fin n)))) := by
  obtain ⟨ψ, hψi, hψr⟩ : ∃ ψ : alternatingGroup (Fin n) →* X, Function.Injective ψ ∧
      ψ.range = L := by
    refine ⟨L.subtype.comp φ.symm.toMonoidHom, L.subtype_injective.comp φ.symm.injective, ?_⟩
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr φ.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hDD : (D.comap ψ).map ψ = D := Subgroup.map_comap_eq_self (hψr ▸ hDL)
  refine ⟨?_, D.comap ψ, thr_isElemAbelian_comap hψi hF.elem, ?_, ?_, ?_⟩
  · by_contra hge
    have h3 := CFSG.AGLEmbeddingD2.three_le_pRank_alternatingGroup hF.prime hF.odd
      (not_lt.mp hge)
    have h2 : CFSG.Open.pRank p (⊤ : Subgroup (alternatingGroup (Fin n))) ≤ 2 := by
      refine csSup_le' ?_
      rintro k ⟨E, -, hE, hcard⟩
      have := hF.rank_le (E.map ψ) (thr_isElemAbelian_map hE)
      rw [Subgroup.card_map_of_injective hψi, hcard] at this
      exact (Nat.pow_le_pow_iff_right hF.prime.one_lt).mp this
    omega
  · rw [← Subgroup.card_map_of_injective hψi, hDD, hF.card]
  · intro d hd hd1
    have hψd1 : ψ d ≠ 1 := fun h => hd1 (hψi (h.trans (map_one ψ).symm))
    obtain ⟨O, hO⟩ := hF.signalizer (ψ d) (Subgroup.mem_comap.mp hd) hψd1
    rw [← hDD] at hO
    exact ⟨O.comap ψ, thr_isPSignalizer_comap hψi hO⟩
  · rw [← Subgroup.card_map_of_injective hψi, thr_map_invariantTwoJoinIn hψi, hDD,
      ← MonoidHom.range_eq_map, hψr]
    exact thr_dvd_card_invariantTwoJoinIn hF hLn hDL

end CFSG.LocalAnalysis.RankThreeTheoremC
