module

public import CFSG.CGT.T75P.Chain

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n : ℕ}

theorem isTransvection_of_mem_normIn (h63 : Sec63) (hc : Sec6Ctx T T₁ n 1)
    [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (e : ↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)) ≃*
      SL(n, GaloisField 2 1))
    (φ : ↥T ≃* Multiplicative (Fin n → GaloisField 2 1))
    (hcompat : ∀ (h : ↥(hSub T (normIn T₁ T))) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
      φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ =
        Multiplicative.ofAdd (((e (QuotientGroup.mk h) : SL(n, GaloisField 2 1)) :
          Matrix (Fin n) (Fin n) (GaloisField 2 1)).mulVec (Multiplicative.toAdd (φ t))))
    {ℓ : G} (hℓ : ℓ ∈ normIn T₁ T) (hℓ1 : ℓ ≠ 1) (hℓH : ℓ ∈ hSub T (normIn T₁ T)) :
    IsTransvection (e (QuotientGroup.mk (⟨ℓ, hℓH⟩ : ↥(hSub T (normIn T₁ T))))) := by
  classical
  have : Finite G := hc.finite
  have hTab := hc.hy.pair.wc.1
  obtain ⟨s, hs⟩ := hc.hy.pair.conj
  have hℓT₁ : ℓ ∈ T₁ := (mem_normIn.1 hℓ).1
  have hℓN : ℓ ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hℓ).2
  have hℓD : ℓ ∈ classD T := mem_classD_of_mem_conjSubgroup (k := s) (hs ▸ hℓT₁) hℓ1
  have hℓT : ℓ ∉ T := fun hlT => by
    have : ℓ ∈ T ⊓ T₁ := Subgroup.mem_inf.2 ⟨hlT, hℓT₁⟩
    rw [hc.sec3.cfg.inf, Subgroup.mem_bot] at this
    exact hℓ1 this
  have hℓ2 : ℓ * ℓ = 1 := mul_self_eq_one_of_mem_classD hTab hℓD
  have hu2 : e (QuotientGroup.mk (⟨ℓ, hℓH⟩ : ↥(hSub T (normIn T₁ T)))) *
      e (QuotientGroup.mk (⟨ℓ, hℓH⟩ : ↥(hSub T (normIn T₁ T)))) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul]
    have : (⟨ℓ, hℓH⟩ * ⟨ℓ, hℓH⟩ : ↥(hSub T (normIn T₁ T))) = 1 := Subtype.ext hℓ2
    rw [this, QuotientGroup.mk_one, map_one]
  have hu1 : e (QuotientGroup.mk (⟨ℓ, hℓH⟩ : ↥(hSub T (normIn T₁ T)))) ≠ 1 := by
    intro h
    have h' : (QuotientGroup.mk (⟨ℓ, hℓH⟩ : ↥(hSub T (normIn T₁ T))) :
        ↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) = 1 :=
      e.injective (by rw [map_one]; exact h)
    exact hℓT (Subgroup.mem_subgroupOf.1
      ((QuotientGroup.eq_one_iff (N := T.subgroupOf (hSub T (normIn T₁ T)))
        (⟨ℓ, hℓH⟩ : ↥(hSub T (normIn T₁ T)))).1 h'))
  have hcentcard : Nat.card ↥(T ⊓ Subgroup.centralizer ({ℓ} : Set G)) =
      Nat.card ↥(normIn T T₁) := by
    rcases h63 G T T₁ n 1 hc ℓ ⟨hℓD, hℓN⟩ hℓT with h | ⟨-, hL8, h4⟩
    · exact h
    · exfalso
      have hle : normIn T T₁ ≤ T ⊓ Subgroup.centralizer ({ℓ} : Set G) := by
        intro l hl
        refine Subgroup.mem_inf.2 ⟨normIn_le T T₁ hl, ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.2 (hc.sec3.cfg.comm_L_L₁ hl hℓ)
      have := Subgroup.card_le_of_le hle
      omega
  refine isTransvection_of_card_fixed hu2 hu1 ?_
  rw [card_fixed_eq_card_centralizer e φ hcompat hℓH hℓN, hcentcard, hc.card_normIn,
    GaloisField.card 2 1 one_ne_zero]

theorem odd_index_centralizer_of_chain {H : Subgroup G} [(T.subgroupOf H).Normal]
    (e : ↥H ⧸ T.subgroupOf H ≃* SL(n, GaloisField 2 1)) {k : ℕ} (ch : TransvChain n k)
    (x : Fin k → G) (hxH : ∀ i, x i ∈ H)
    (hxE : ∀ i, e (QuotientGroup.mk (⟨x i, hxH i⟩ : ↥H)) = ch.E i) {z : G}
    (hzT : ∀ t ∈ T, t * z = z * t) (hzx : ∀ i, x i * z = z * x i) :
    Odd (((Subgroup.centralizer ({z} : Set G)).subgroupOf H).index) := by
  classical
  let π : ↥H →* SL(n, GaloisField 2 1) := e.toMonoidHom.comp (QuotientGroup.mk' (T.subgroupOf H))
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨h, rfl⟩
  let S : Subgroup ↥H := (Subgroup.centralizer ({z} : Set G)).subgroupOf H
  let K : Subgroup ↥H := Subgroup.closure (Set.range fun i => (⟨x i, hxH i⟩ : ↥H))
  have hπK : K.map π = Subgroup.closure (Set.range ch.E) := by
    have hcomp : (⇑π ∘ fun i => (⟨x i, hxH i⟩ : ↥H)) = ch.E := funext fun i => hxE i
    rw [MonoidHom.map_closure, ← Set.range_comp, hcomp]
  have hker : π.ker = T.subgroupOf H := by
    ext y
    show e (QuotientGroup.mk y) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff (N := T.subgroupOf H)]
  have hle : (Subgroup.closure (Set.range ch.E)).comap π ≤ S := by
    rw [← hπK, Subgroup.comap_map_eq]
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hzx i)
    · rw [hker]
      intro y hy
      have hyT : (y : G) ∈ T := Subgroup.mem_subgroupOf.1 hy
      exact Subgroup.mem_centralizer_singleton_iff.2 (hzT _ hyT)
  have hdvd : S.index ∣ ((Subgroup.closure (Set.range ch.E)).comap π).index :=
    Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_comap_of_surjective _ hπ] at hdvd
  exact ch.odd_index.of_dvd_nat hdvd

end CFSG.CGT.T75P
