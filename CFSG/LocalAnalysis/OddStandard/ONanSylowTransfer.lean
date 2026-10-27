module

public import CFSG.LocalAnalysis.OddStandard.ONanSylowFacts

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup CFSG.CosetTable F2 F2.AlpE Model

structure AlpEmb (G : Type*) [Group G] (v1 v2 v3 s t : G) where
  φ : AlpE →* G
  inj : Function.Injective φ
  gen_eq : ∀ i : Fin 5, φ (AlpE.gen i) = ![v1, v2, v3, s, t] i

noncomputable def AlpFrame.emb {G : Type*} [Group G] {v1 v2 v3 s t : G}
    (hfr : AlpFrame v1 v2 v3 s t) (hz : v1 ^ 2 * v3 ^ 2 ≠ 1)
    (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) : AlpEmb G v1 v2 v3 s t :=
  ⟨hfr.toG h, hfr.toG_injective h hz, hfr.toG_gen h⟩

noncomputable def AlpFrame.emb' {G : Type*} [Group G] {v1 v2 v3 s t : G}
    (hfr : AlpFrame v1 v2 v3 s t) (hz : orderOf (v1 ^ 2 * v3 ^ 2) = 2)
    (h : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512) : AlpEmb G v1 v2 v3 s t :=
  hfr.emb (fun h1 => by rw [h1, orderOf_one] at hz; exact absurd hz (by norm_num)) h

namespace AlpEmb

variable {G : Type*} [Group G] {v1 v2 v3 s t : G} (E : AlpEmb G v1 v2 v3 s t)

include E

theorem φ_v1 : E.φ (AlpE.gen 0) = v1 := E.gen_eq 0
theorem φ_v2 : E.φ (AlpE.gen 1) = v2 := E.gen_eq 1
theorem φ_v3 : E.φ (AlpE.gen 2) = v3 := E.gen_eq 2
theorem φ_s : E.φ (AlpE.gen 3) = s := E.gen_eq 3
theorem φ_t : E.φ (AlpE.gen 4) = t := E.gen_eq 4

theorem range_eq : E.φ.range = alpP v1 v2 v3 s t := by
  rw [MonoidHom.range_eq_map, ← closure_range_gen, MonoidHom.map_closure, ← Set.range_comp]
  unfold alpP
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, E.gen_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]

theorem card_alpP : Nat.card (alpP v1 v2 v3 s t) = 512 := by
  rw [← E.range_eq, Nat.card_congr (MonoidHom.ofInjective E.inj).toEquiv.symm, AlpE.card]

theorem mem_alpP_iff {x : G} : x ∈ alpP v1 v2 v3 s t ↔ ∃ y : AlpE, E.φ y = x := by
  rw [← E.range_eq]
  exact Iff.rfl

theorem φ_mem (y : AlpE) : E.φ y ∈ alpP v1 v2 v3 s t := E.mem_alpP_iff.2 ⟨y, rfl⟩

theorem φ_eq_iff {x y : AlpE} : E.φ x = E.φ y ↔ x = y := E.inj.eq_iff

theorem map_le (K : Subgroup AlpE) : K.map E.φ ≤ alpP v1 v2 v3 s t := by
  rw [← E.range_eq, MonoidHom.range_eq_map]
  exact Subgroup.map_mono le_top

theorem card_map (K : Subgroup AlpE) : Nat.card (K.map E.φ) = Nat.card K :=
  Subgroup.card_map_of_injective E.inj

theorem closure_map (L : List AlpE) :
    closure {g : G | g ∈ L.map E.φ} = (closure {g : AlpE | g ∈ L}).map E.φ := by
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  simp [List.mem_map]

theorem exists_map {H : Subgroup G} (hH : H ≤ alpP v1 v2 v3 s t) :
    ∃ K : Subgroup AlpE, K.map E.φ = H :=
  ⟨H.comap E.φ, Subgroup.map_comap_eq_self (by rw [E.range_eq]; exact hH)⟩

end AlpEmb

section Words

variable {M N : Type*} [Group M] [Group N] (φ : M →* N) (v1 v2 v3 s t : M)

theorem map_invRep (i : Fin 7) :
    φ (invRep v1 v2 v3 s t i) = invRep (φ v1) (φ v2) (φ v3) (φ s) (φ t) i := by
  fin_cases i <;> simp [invRep, map_mul, map_pow, map_inv]

theorem map_genV0 : (genV0 v1 v2 v3).map φ = genV0 (φ v1) (φ v2) (φ v3) := by
  simp [genV0, map_mul, map_pow]

theorem map_genMax (i : Fin 7) :
    (genMax v1 v2 v3 s t i).map φ = genMax (φ v1) (φ v2) (φ v3) (φ s) (φ t) i := by
  fin_cases i <;> simp [genMax, map_genV0, map_mul, map_pow]

theorem map_genQ : (genQ v1 v2 s t).map φ = genQ (φ v1) (φ v2) (φ s) (φ t) := by
  simp [genQ, map_mul]

theorem map_genCent (i : Fin 3) :
    (genCent v1 v2 v3 s t i).map φ = genCent (φ v1) (φ v2) (φ v3) (φ s) (φ t) i := by
  fin_cases i <;> simp [genCent, map_mul, map_pow, map_inv]

theorem map_xel : φ (xel v1 v2 v3) = xel (φ v1) (φ v2) (φ v3) := by
  simp [xel, map_mul, map_pow, map_inv]

end Words

namespace AlpEmb

variable {G : Type*} [Group G] {v1 v2 v3 s t : G} (E : AlpEmb G v1 v2 v3 s t)

include E

theorem φ_invE (i : Fin 7) : E.φ (invE i) = invRep v1 v2 v3 s t i := by
  rw [invE, map_invRep, E.φ_v1, E.φ_v2, E.φ_v3, E.φ_s, E.φ_t]

theorem φ_xE : E.φ xE = xel v1 v2 v3 := by
  rw [xE, map_xel, E.φ_v1, E.φ_v2, E.φ_v3]

theorem φ_zc : E.φ zc = v1 ^ 2 * v3 ^ 2 := by
  rw [zc, map_mul, map_pow, map_pow, E.φ_v1, E.φ_v3]

theorem closure_genMax (i : Fin 7) :
    closure {g : G | g ∈ genMax v1 v2 v3 s t i} = (subE (genMaxE i)).map E.φ := by
  rw [← E.closure_map, genMaxE, map_genMax, E.φ_v1, E.φ_v2, E.φ_v3, E.φ_s, E.φ_t]

theorem centre_alpP (hF : f2Check = true) {x : G} (hx : x ∈ alpP v1 v2 v3 s t) :
    (∀ g ∈ alpP v1 v2 v3 s t, g * x = x * g) ↔ x = 1 ∨ x = v1 ^ 2 * v3 ^ 2 := by
  obtain ⟨y, rfl⟩ := E.mem_alpP_iff.1 hx
  constructor
  · intro hc
    have hy : y ∈ Subgroup.center AlpE := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply E.inj
      rw [map_mul, map_mul]
      exact hc _ (E.φ_mem g)
    rcases (mem_center_iff_E hF y).1 hy with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr E.φ_zc
  · intro h g hg
    obtain ⟨z, rfl⟩ := E.mem_alpP_iff.1 hg
    have hy : y ∈ Subgroup.center AlpE := by
      rw [mem_center_iff_E hF]
      rcases h with h | h
      · exact Or.inl (E.inj (by rw [h, map_one]))
      · exact Or.inr (E.inj (by rw [h, E.φ_zc]))
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hy z)]

theorem alpV_eq_map : alpV v1 v2 v3 = Vsub.map E.φ := by
  rw [← closure_genVE, ← E.closure_map]
  unfold alpV
  congr 1
  ext g
  simp [genVE, E.φ_v1, E.φ_v2, E.φ_v3]

theorem alpV_le : alpV v1 v2 v3 ≤ alpP v1 v2 v3 s t := by
  rw [alpV_eq_map E]
  exact E.map_le _

theorem card_alpV : Nat.card (alpV v1 v2 v3) = 64 := by
  rw [alpV_eq_map E, E.card_map, card_Vsub]

theorem alpV_normal {g x : G} (hg : g ∈ alpP v1 v2 v3 s t) (hx : x ∈ alpV v1 v2 v3) :
    g * x * g⁻¹ ∈ alpV v1 v2 v3 := by
  rw [alpV_eq_map E] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨z, rfl⟩ := E.mem_alpP_iff.1 hg
  exact Subgroup.mem_map.2 ⟨z * y * z⁻¹, (inferInstance : Vsub.Normal).conj_mem y hy z, by simp⟩

theorem le_alpV_of_abelian (hF : f2Check = true) {H : Subgroup G}
    (hH : H ≤ alpP v1 v2 v3 s t) (hab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hcard : 32 < Nat.card H) : H ≤ alpV v1 v2 v3 := by
  obtain ⟨K, rfl⟩ := E.exists_map hH
  rw [alpV_eq_map E]
  refine Subgroup.map_mono (abelian_le_Vsub hF (fun x hx y hy => E.inj ?_) ?_)
  · rw [map_mul, map_mul]
    exact hab _ (Subgroup.mem_map_of_mem _ hx) _ (Subgroup.mem_map_of_mem _ hy)
  · rwa [← E.card_map]

theorem eq_alpV_of_abelian (hF : f2Check = true) {H : Subgroup G}
    (hH : H ≤ alpP v1 v2 v3 s t) (hab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hcard : Nat.card H = 64) : H = alpV v1 v2 v3 := by
  have : Finite (alpV v1 v2 v3) := Nat.finite_of_card_ne_zero (by rw [card_alpV E]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge (le_alpV_of_abelian E hF hH hab (by omega))
    (by rw [hcard, card_alpV E])

theorem eq_alpV_of_equiv (hF : f2Check = true) {H : Subgroup G}
    (hH : H ≤ alpP v1 v2 v3 s t) (e : H ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) :
    H = alpV v1 v2 v3 := by
  have hcard : Nat.card H = 64 := by
    rw [Nat.card_congr e.toEquiv]
    simp [ZMod.card]
  refine eq_alpV_of_abelian E hF hH (fun x hx y hy => ?_) hcard
  have := e.injective (a₁ := ⟨x, hx⟩ * ⟨y, hy⟩) (a₂ := ⟨y, hy⟩ * ⟨x, hx⟩)
    (by rw [map_mul, map_mul, mul_comm])
  exact congrArg Subtype.val this

theorem nonempty_equiv_alpV :
    Nonempty (alpV v1 v2 v3 ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) :=
  ⟨((MulEquiv.subgroupCongr (alpV_eq_map E)).trans
    (Subgroup.equivMapOfInjective Vsub E.φ E.inj).symm).trans equivVsub⟩

theorem invRep_sq (hF : f2Check = true) (i : Fin 7) :
    invRep v1 v2 v3 s t i * invRep v1 v2 v3 s t i = 1 ∧ invRep v1 v2 v3 s t i ≠ 1 := by
  obtain ⟨h1, h2⟩ := invE_sq hF i
  rw [← E.φ_invE]
  refine ⟨by rw [← map_mul, h1, map_one], fun h => h2 (E.inj (by rw [h, map_one]))⟩

theorem invRep_mem (i : Fin 7) : invRep v1 v2 v3 s t i ∈ alpP v1 v2 v3 s t := by
  rw [← E.φ_invE]
  exact E.φ_mem _

theorem exists_conj_invRep (hF : f2Check = true) {u : G} (hu : u ∈ alpP v1 v2 v3 s t)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ i : Fin 7, ∃ c ∈ alpP v1 v2 v3 s t, c⁻¹ * invRep v1 v2 v3 s t i * c = u := by
  obtain ⟨y, rfl⟩ := E.mem_alpP_iff.1 hu
  have hy2 : y * y = 1 := E.inj (by rw [map_mul, hu2, map_one])
  have hy1 : y ≠ 1 := fun h => hu1 (by rw [h, map_one])
  obtain ⟨i, c, hc⟩ := exists_conj_invE hF hy2 hy1
  refine ⟨i, E.φ c, E.φ_mem c, ?_⟩
  rw [← E.φ_invE, ← map_inv, ← map_mul, ← map_mul, hc]

theorem conj_invRep_eq (hF : f2Check = true) {i j : Fin 7} {c : G}
    (hc : c ∈ alpP v1 v2 v3 s t) (h : c⁻¹ * invRep v1 v2 v3 s t i * c = invRep v1 v2 v3 s t j) :
    i = j := by
  obtain ⟨c', rfl⟩ := E.mem_alpP_iff.1 hc
  refine conj_invE_eq hF (c := c') (E.inj ?_)
  rw [map_mul, map_mul, map_inv, E.φ_invE, E.φ_invE]
  exact h

theorem card_centralizer_invRep (hF : f2Check = true) (i : Fin 7) :
    Nat.card ↥(alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t i} : Set G)) =
      ![512, 256, 128, 32, 16, 32, 32] i := by
  have hmap : alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t i} : Set G) =
      (centralizer ({invE i} : Set AlpE)).map E.φ := by
    ext g
    constructor
    · rintro hg
      obtain ⟨hgP, hgc⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨y, rfl⟩ := E.mem_alpP_iff.1 hgP
      refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hgc ⊢
      apply E.inj
      rw [map_mul, map_mul, E.φ_invE]
      exact hgc
    · intro hg
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
      refine Subgroup.mem_inf.2 ⟨E.φ_mem y, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      rw [← E.φ_invE, ← map_mul, ← map_mul, hy]
  rw [hmap, E.card_map, card_centralizer_invE hF]

theorem inf_centralizer_eq_map (r : AlpE) :
    alpP v1 v2 v3 s t ⊓ centralizer ({E.φ r} : Set G) = (centralizer ({r} : Set AlpE)).map E.φ := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgP, hgc⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨y, rfl⟩ := E.mem_alpP_iff.1 hgP
    refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc ⊢
    apply E.inj
    rw [map_mul, map_mul]
    exact hgc
  · intro hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    refine Subgroup.mem_inf.2 ⟨E.φ_mem y, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← map_mul, ← map_mul, hy]

theorem card_genMax (hF : f2Check = true) (i : Fin 7) :
    Nat.card (closure {g : G | g ∈ genMax v1 v2 v3 s t i}) = 256 := by
  rw [E.closure_genMax, E.card_map, card_subE_max hF]

theorem genMax_le (i : Fin 7) :
    closure {g : G | g ∈ genMax v1 v2 v3 s t i} ≤ alpP v1 v2 v3 s t := by
  rw [E.closure_genMax]
  exact E.map_le _

theorem max_table_alpP (hF : f2Check = true) (i j : Fin 7) :
    (∃ u ∈ closure {g : G | g ∈ genMax v1 v2 v3 s t i},
        ∃ c ∈ alpP v1 v2 v3 s t, c⁻¹ * invRep v1 v2 v3 s t j * c = u) ↔
      maxTable i j = true := by
  rw [← max_table hF i j, E.closure_genMax]
  constructor
  · rintro ⟨u, hu, c, hc, rfl⟩
    obtain ⟨u', hu', hu'e⟩ := Subgroup.mem_map.1 hu
    obtain ⟨c', rfl⟩ := E.mem_alpP_iff.1 hc
    exact ⟨u', hu', c', E.inj (by rw [map_mul, map_mul, map_inv, E.φ_invE, hu'e])⟩
  · rintro ⟨u, hu, c, rfl⟩
    exact ⟨E.φ (c⁻¹ * invE j * c), Subgroup.mem_map_of_mem _ hu, E.φ c, E.φ_mem c, by
      rw [map_mul, map_mul, map_inv, E.φ_invE]⟩

theorem closure_genQ : closure {g : G | g ∈ genQ v1 v2 s t} =
    (subE genQE).map E.φ := by
  rw [← E.closure_map, genQE, map_genQ, E.φ_v1, E.φ_v2, E.φ_s, E.φ_t]

theorem closure_genR : zpowers s = (subE genRE).map E.φ := by
  rw [Subgroup.zpowers_eq_closure, ← E.closure_map]
  congr 1
  ext g
  simp [genRE, E.φ_s]

theorem card_Q (hF : f2Check = true) :
    Nat.card (closure {g : G | g ∈ genQ v1 v2 s t}) = 32 := by
  rw [closure_genQ E, E.card_map, card_subE_Q hF]

theorem card_R (hF : f2Check = true) : Nat.card (zpowers s) = 16 := by
  rw [closure_genR E, E.card_map, card_subE_R hF]

theorem involutions_Q_alpP (hF : f2Check = true) {u : G}
    (hu : u ∈ closure {g : G | g ∈ genQ v1 v2 s t}) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ j : Fin 7, (j = 1 ∨ j = 2 ∨ j = 4) ∧
      ∃ c ∈ alpP v1 v2 v3 s t, c⁻¹ * invRep v1 v2 v3 s t j * c = u := by
  rw [closure_genQ E] at hu
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
  have hu2' : u' * u' = 1 := E.inj (by rw [map_mul, hu2, map_one])
  have hu1' : u' ≠ 1 := fun h => hu1 (by rw [h, map_one])
  have mk : ∀ j : Fin 7, (∃ c : AlpE, c⁻¹ * invE j * c = u') →
      ∃ c ∈ alpP v1 v2 v3 s t, c⁻¹ * invRep v1 v2 v3 s t j * c = E.φ u' := by
    rintro j ⟨c, hc⟩
    exact ⟨E.φ c, E.φ_mem c, by rw [← E.φ_invE, ← map_inv, ← map_mul, ← map_mul, hc]⟩
  rcases involutions_Q hF hu' hu2' hu1' with h | h | h
  · exact ⟨1, Or.inl rfl, mk 1 h⟩
  · exact ⟨2, Or.inr (Or.inl rfl), mk 2 h⟩
  · exact ⟨4, Or.inr (Or.inr rfl), mk 4 h⟩

theorem involution_zpowers_s (hF : f2Check = true) {x : G} (hx : x ∈ zpowers s)
    (hx2 : x * x = 1) : x = 1 ∨ x = v1 ^ 2 * v3 ^ 2 := by
  rw [closure_genR E] at hx
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
  have hx2' : x' * x' = 1 := E.inj (by rw [map_mul, hx2, map_one])
  rcases involution_R hF hx' hx2' with h | h
  · exact Or.inl (by rw [h, map_one])
  · exact Or.inr (by rw [h, E.φ_zc])

theorem closure_genCent (i : Fin 3) :
    closure {g : G | g ∈ genCent v1 v2 v3 s t i} = (subE (genCentE i)).map E.φ := by
  rw [← E.closure_map, genCentE, map_genCent, E.φ_v1, E.φ_v2, E.φ_v3, E.φ_s, E.φ_t]

theorem centralizer_genCent (hF : f2Check = true) (i : Fin 3) :
    alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t (![3, 5, 6] i)} : Set G) =
      closure {g : G | g ∈ genCent v1 v2 v3 s t i} := by
  rw [← E.φ_invE, E.inf_centralizer_eq_map, centralizer_invE_eq hF, closure_genCent E]

theorem card_involutions_genCent (hF : f2Check = true) (i : Fin 3) (j : Fin 7) :
    Nat.card {u : G // u ∈ closure {g : G | g ∈ genCent v1 v2 v3 s t i} ∧ u * u = 1 ∧ u ≠ 1 ∧
      ∃ c ∈ alpP v1 v2 v3 s t, c⁻¹ * invRep v1 v2 v3 s t j * c = u} = centCount i j := by
  rw [← card_involutions_cent hF i j]
  have hset : {u : G | u ∈ closure {g : G | g ∈ genCent v1 v2 v3 s t i} ∧ u * u = 1 ∧ u ≠ 1 ∧
      ∃ c ∈ alpP v1 v2 v3 s t, c⁻¹ * invRep v1 v2 v3 s t j * c = u} =
      E.φ '' {u : AlpE | u ∈ subE (genCentE i) ∧ u * u = 1 ∧ u ≠ 1 ∧
        ∃ c : AlpE, c⁻¹ * invE j * c = u} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    rw [closure_genCent E]
    constructor
    · rintro ⟨hu, hu2, hu1, c, hc, rfl⟩
      obtain ⟨u', hu', hu'e⟩ := Subgroup.mem_map.1 hu
      obtain ⟨c', rfl⟩ := E.mem_alpP_iff.1 hc
      have hcc : c'⁻¹ * invE j * c' = u' := E.inj (by
        rw [map_mul, map_mul, map_inv, E.φ_invE, hu'e])
      refine ⟨u', ⟨hu', ?_, ?_, c', hcc⟩, hu'e⟩
      · exact E.inj (by rw [map_mul, hu'e, hu2, map_one])
      · exact fun h => hu1 (by rw [← hu'e, h, map_one])
    · rintro ⟨u', ⟨hu', hu2, hu1, c, hc⟩, rfl⟩
      refine ⟨Subgroup.mem_map_of_mem _ hu', by rw [← map_mul, hu2, map_one],
        fun h => hu1 (E.inj (by rw [h, map_one])), E.φ c, E.φ_mem c, ?_⟩
      rw [← hc, map_mul, map_mul, map_inv, E.φ_invE]
  change Nat.card ↥{u : G | u ∈ closure {g : G | g ∈ genCent v1 v2 v3 s t i} ∧ u * u = 1 ∧
    u ≠ 1 ∧ ∃ c ∈ alpP v1 v2 v3 s t, c⁻¹ * invRep v1 v2 v3 s t j * c = u} = _
  rw [hset, Nat.card_image_of_injective E.inj]
  rfl

theorem closure_genVt : closure {g : G | g ∈ [v1, v2, v3, t]} = (subE genVtE).map E.φ := by
  rw [← E.closure_map]
  congr 1
  ext g
  simp [genVtE, E.φ_v1, E.φ_v2, E.φ_v3, E.φ_t]

theorem centralizer_special_alpP (hF : f2Check = true) :
    alpP v1 v2 v3 s t ⊓ centralizer ({v2 ^ 2} : Set G) = closure {g : G | g ∈ [v1, v2, v3, t]} ∧
    alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G) =
      closure {g : G | g ∈ genMax v1 v2 v3 s t 0} ∧
    alpP v1 v2 v3 s t ⊓ centralizer ({xel v1 v2 v3} : Set G) =
      closure {g : G | g ∈ genMax v1 v2 v3 s t 1} := by
  obtain ⟨h1, h2, h3⟩ := centralizer_special hF
  refine ⟨?_, ?_, ?_⟩
  · have : v2 ^ 2 = E.φ (gen 1 ^ 2) := by rw [map_pow, E.φ_v2]
    rw [this, E.inf_centralizer_eq_map, h1, closure_genVt E]
  · have : v1 * v3 = E.φ (gen 0 * gen 2) := by rw [map_mul, E.φ_v1, E.φ_v3]
    rw [this, E.inf_centralizer_eq_map, h2, E.closure_genMax]
  · rw [← E.φ_xE, E.inf_centralizer_eq_map, h3, E.closure_genMax]

theorem alpW_eq_map : alpW v1 v2 v3 = (subE genWE).map E.φ := by
  rw [← E.closure_map]
  unfold alpW
  congr 1
  ext g
  simp [genWE, map_pow, E.φ_v1, E.φ_v2, E.φ_v3]

omit E in
theorem subE_W_le_Vsub : subE genWE ≤ Vsub := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [genWE, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · show (gen 0 ^ 2).d = 0
    decide
  · show (gen 1 ^ 2).d = 0
    decide
  · show (gen 2 ^ 2).d = 0
    decide

theorem alpW_le_alpV : alpW v1 v2 v3 ≤ alpV v1 v2 v3 := by
  rw [alpW_eq_map E, alpV_eq_map E]
  exact Subgroup.map_mono subE_W_le_Vsub

theorem card_alpW (hF : f2Check = true) : Nat.card (alpW v1 v2 v3) = 8 := by
  rw [alpW_eq_map E, E.card_map, card_subE_W hF]

theorem sq_eq_one_iff_mem_alpW (hF : f2Check = true) {v : G} (hv : v ∈ alpV v1 v2 v3) :
    v * v = 1 ↔ v ∈ alpW v1 v2 v3 := by
  rw [alpV_eq_map E] at hv
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hv
  rw [alpW_eq_map E, ← map_mul, ← map_one E.φ, E.inj.eq_iff, Subgroup.mem_map_iff_mem E.inj]
  exact (W_facts hF).1 y hy

theorem alpW_normal (hF : f2Check = true) {g w : G} (hg : g ∈ alpP v1 v2 v3 s t)
    (hw : w ∈ alpW v1 v2 v3) : g * w * g⁻¹ ∈ alpW v1 v2 v3 := by
  rw [alpW_eq_map E] at hw ⊢
  obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hw
  obtain ⟨g', rfl⟩ := E.mem_alpP_iff.1 hg
  exact Subgroup.mem_map.2 ⟨g' * w' * g'⁻¹, (W_facts hF).2.2.2 g' w' hw', by simp⟩

theorem centralizer_alpW (hF : f2Check = true) :
    alpP v1 v2 v3 s t ⊓ centralizer (alpW v1 v2 v3 : Set G) = alpV v1 v2 v3 := by
  obtain ⟨-, hW, -, -⟩ := W_facts hF
  ext g
  constructor
  · intro hg
    obtain ⟨hgP, hgc⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨y, rfl⟩ := E.mem_alpP_iff.1 hgP
    rw [alpV_eq_map E]
    refine Subgroup.mem_map.2 ⟨y, (hW y).1 (fun w hw => E.inj ?_), rfl⟩
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.1 hgc (E.φ w) (by
      rw [alpW_eq_map E]
      exact Subgroup.mem_map_of_mem _ hw)).symm
  · intro hg
    have hgP : g ∈ alpP v1 v2 v3 s t := alpV_le E hg
    refine Subgroup.mem_inf.2 ⟨hgP, ?_⟩
    rw [alpV_eq_map E] at hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [SetLike.mem_coe, alpW_eq_map E] at hw
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hw
    rw [← map_mul, ← map_mul, ((hW y).2 hy w' hw').symm]

theorem centralizer_alpV (hF : f2Check = true) :
    alpP v1 v2 v3 s t ⊓ centralizer (alpV v1 v2 v3 : Set G) = alpV v1 v2 v3 := by
  obtain ⟨-, -, hV, -⟩ := W_facts hF
  ext g
  constructor
  · intro hg
    obtain ⟨hgP, hgc⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨y, rfl⟩ := E.mem_alpP_iff.1 hgP
    rw [alpV_eq_map E]
    refine Subgroup.mem_map.2 ⟨y, (hV y).1 (fun w hw => E.inj ?_), rfl⟩
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.1 hgc (E.φ w) (by
      rw [alpV_eq_map E]
      exact Subgroup.mem_map_of_mem _ hw)).symm
  · intro hg
    have hgP : g ∈ alpP v1 v2 v3 s t := alpV_le E hg
    refine Subgroup.mem_inf.2 ⟨hgP, ?_⟩
    rw [alpV_eq_map E] at hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [SetLike.mem_coe, alpV_eq_map E] at hw
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hw
    rw [← map_mul, ← map_mul, ((hV y).2 hy w' hw').symm]

end AlpEmb

end CFSG.OddStandard.ONanRec
