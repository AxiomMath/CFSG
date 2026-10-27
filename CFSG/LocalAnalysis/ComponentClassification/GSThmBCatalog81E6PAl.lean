module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PT
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Perm
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PS

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10

namespace P211

variable {X : Type} [Group X]

theorem exists_perm_embedding_n {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) (G : Subgroup X) [G.Normal]
    (hC : centralizer (G : Set X) = ⊥) (e : G ≃* alternatingGroup (Fin n)) :
    ∃ φ : X →* Perm (Fin n), Function.Injective φ ∧ ∀ s : G, φ s = (e s : Perm (Fin n)) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  set ψ := MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
    Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) hbij
  refine ⟨ψ.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal),
    ψ.symm.injective.comp ((MulAut.congr e).injective.comp (conjNormal_injective' G hC)),
    fun s => ?_⟩
  apply ψ.injective
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  have h1 : (MulAut.conjNormal (s : X) (e.symm a) : G) = s * e.symm a * s⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  change ((e (MulAut.conjNormal (s : X) (e.symm a)) : alternatingGroup (Fin n)) :
    Perm (Fin n)) = _
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  simp [ψ, MulAut.conjNormal_apply]

theorem alternating_le_range_n {n : ℕ} (G : Subgroup X) (e : G ≃* alternatingGroup (Fin n))
    (φ : X →* Perm (Fin n)) (hφ : ∀ s : G, φ s = (e s : Perm (Fin n))) :
    alternatingGroup (Fin n) ≤ φ.range := by
  intro a ha
  refine ⟨(e.symm ⟨a, ha⟩ : X), ?_⟩
  rw [hφ, MulEquiv.apply_symm_apply]

theorem le_of_perfect_n {n : ℕ} (G : Subgroup X) (e : G ≃* alternatingGroup (Fin n))
    (φ : X →* Perm (Fin n)) (hinj : Function.Injective φ)
    (hφ : ∀ s : G, φ s = (e s : Perm (Fin n))) {K : Subgroup X} (hK : ⁅K, K⁆ = K) : K ≤ G := by
  have hperf : ⁅K.map φ, K.map φ⁆ = K.map φ := by rw [← Subgroup.map_commutator, hK]
  intro k hk
  have hA : φ k ∈ alternatingGroup (Fin n) := perfect_le_alternating _ hperf ⟨k, hk, rfl⟩
  have h1 : φ (e.symm ⟨φ k, hA⟩ : X) = φ k := by rw [hφ, MulEquiv.apply_symm_apply]
  rw [← hinj h1]
  exact (e.symm _).2

theorem card_centralizer_inv {n : ℕ} {σ : Perm (Fin n)} (h : orderOf σ = 2) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin n)))) =
      (n - 2 * (σ.support.card / 2)).factorial * 2 ^ (σ.support.card / 2) *
        (σ.support.card / 2).factorial := by
  obtain ⟨hct, -, hm⟩ := cycleType_of_orderOf_two h
  have hne : σ.support.card / 2 ≠ 0 := by omega
  rw [nat_card_centralizer, hct, Multiset.sum_replicate, Multiset.prod_replicate, smul_eq_mul,
    Fintype.card_fin, Multiset.toFinset_replicate]
  simp only [hne, ↓reduceIte, Finset.prod_singleton, Multiset.count_replicate_self,
    mul_comm (σ.support.card / 2) 2]

theorem ne_bot_of_isPComp' {Y : Type*} [Group Y] {L : Subgroup Y} (hL : IsPComponent 2 L) :
    L ≠ ⊥ := by
  obtain ⟨K, hK, -, hLK, -⟩ := hL
  intro h
  rw [h, Subgroup.map_bot] at hLK
  subst hLK
  obtain ⟨a, b, hab⟩ := hK.1.2.2
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have : a = b := Subsingleton.elim _ _
  rw [this]

theorem map_eq_altOn_n [Finite X] {n : ℕ} (φ : X →* Perm (Fin n)) (hinj : Function.Injective φ)
    (hA : alternatingGroup (Fin n) ≤ φ.range) (ι : X) (J : Subgroup X)
    (hJC : J ≤ centralizer ({ι} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({ι} : Set X))))
    (hS : (φ ι).support.card ≤ 4) (hT : 5 ≤ ((φ ι).support)ᶜ.card) :
    J.map φ = altOn (φ ι).supportᶜ := by
  classical
  set C := centralizer ({ι} : Set X)
  set T := (φ ι).supportᶜ
  have hJperf : ⁅J, J⁆ = J := commutator_eq_of_isPComp hJC hJ
  have hmapperf : ⁅J.map φ, J.map φ⁆ = J.map φ := by rw [← Subgroup.map_commutator, hJperf]
  have hpres : ∀ g ∈ J.map φ, ∀ x, g x ∈ (φ ι).support ↔ x ∈ (φ ι).support := by
    rintro _ ⟨j, hj, rfl⟩ x
    apply Catalog82A10.mem_support_iff_of_commute
    have hjc : ι * j = j * ι := mem_centralizer_iff.mp (hJC hj) ι rfl
    rw [← map_mul, ← map_mul, hjc]
  have hfix := perfect_fix_small (J.map φ) hmapperf (φ ι).support hS hpres
  have halt := perfect_le_alternating (J.map φ) hmapperf
  have hle : J.map φ ≤ altOn T := by
    intro g hg
    refine mem_altOn.mpr ⟨halt hg, fun x hx => ?_⟩
    rw [Finset.mem_compl]
    intro hxσ
    exact (Equiv.Perm.mem_support.mp hx) (hfix g hg x hxσ)
  set N := (altOn T).comap φ
  have hJN : J ≤ N := Subgroup.map_le_iff_le_comap.mp hle
  have hNC : N ≤ C := by
    intro m hm
    rw [mem_centralizer_iff]
    rintro _ rfl
    apply hinj
    rw [map_mul, map_mul]
    exact (commute_of_support_subset_compl (mem_altOn.mp hm).2).symm
  have hNmap : N.map φ = altOn T := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr (fun g hg => hA (mem_altOn.mp hg).1)
  have hNsimple : IsSimpleGroup N := by
    have := isSimpleGroup_altOn T hT
    exact ((N.equivMapOfInjective φ hinj).trans (MulEquiv.subgroupCongr hNmap)).isSimpleGroup
  have hsub : (J.subgroupOf C).IsSubnormal := hJ.choose_spec.2.1
  have hsubN : (J.subgroupOf N).IsSubnormal := by
    have h1 := hsub.comap (Subgroup.inclusion hNC)
    have h2 : (J.subgroupOf C).comap (Subgroup.inclusion hNC) = J.subgroupOf N := by
      ext x
      simp [mem_subgroupOf]
    rwa [h2] at h1
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hNsimple hsubN with h | h
  · exfalso
    apply ne_bot_of_isPComp' hJ
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x.val, hJN (mem_subgroupOf.mp hx)⟩ : N) ∈ J.subgroupOf N :=
      mem_subgroupOf.mpr (mem_subgroupOf.mp hx)
    rw [h, mem_bot] at h1
    rw [mem_bot]
    have h2 : (x : X) = 1 := congrArg (fun y : N => (y : X)) h1
    exact Subtype.ext h2
  · have hNJ : N ≤ J := by
      intro m hm
      have : (⟨m, hm⟩ : N) ∈ J.subgroupOf N := h ▸ mem_top _
      exact this
    rw [← hNmap, le_antisymm hJN hNJ]

theorem ordBC_ne {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) : Open.ordBC 2 q ≠ 181440 := by
  intro h
  have h2 := ordBC_two_mul hq
  rw [h] at h2
  rcases (show q = 3 ∨ 5 ≤ q by obtain ⟨k, rfl⟩ := hq; omega) with rfl | h5
  · norm_num at h2
  · have h4 : 625 ≤ q ^ 4 := by
      calc 625 = 5 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left h5 4
    have hsq : 25 ≤ q ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left h5 2
    have h24 : 24 ≤ q ^ 2 - 1 := by omega
    have h624 : 624 ≤ q ^ 4 - 1 := by omega
    have : 625 * (24 * 624) ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
      Nat.mul_le_mul h4 (Nat.mul_le_mul h24 h624)
    omega

theorem card_quot_of_simple [Finite X] {K : Subgroup X} (hs : IsSimpleGroup K)
    (heven : Even (Nat.card K)) : Nat.card (K ⧸ pPrimeCore 2 K) = Nat.card K := by
  have hO : pPrimeCore 2 K = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (pPrimeCore 2 K) with h | h
    · exact h
    · exfalso
      have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 K)) := pPrimeCore_coprime_card
      rw [h, Subgroup.card_top] at hcop
      exact Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp hcop) heven
  rw [hO]
  exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv

end P211

open P211

theorem cf81E6P211Alt : CF81E6P211Alt := by
  intro X _ _ _ hC ⟨n, hn8, hn11, ⟨e⟩⟩ p f hp hp2 hf a J D _ _ _ _ _ _ _ _ _ b K hb hb1 hKC hK
    hKt
  by_cases hn10 : n = 10
  · subst hn10
    exact Or.inl ⟨e⟩
  exfalso
  classical
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have : (generalizedFitting X).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := X)).2
  obtain ⟨φ, hinj, hφe⟩ := exists_perm_embedding_n (by omega) (by omega) _ hC e
  have hA := alternating_le_range_n _ e φ hφe
  have hKF := le_of_perfect_n _ e φ hinj hφe (commutator_eq_of_isPComp hKC hK)
  have hK20 := le_card_of_socle hp hp2 hf hKt
  have hcardF : Nat.card (generalizedFitting X) = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  have hb2 : orderOf (φ b) = 2 := by
    rw [orderOf_injective φ hinj]
    exact orderOf_eq_prime (by rw [pow_two]; exact hb) hb1
  obtain ⟨-, hsupp, hm1⟩ := cycleType_of_orderOf_two hb2
  have hKcard : Nat.card K ≤ Nat.card (centralizer ({φ b} : Set (Perm (Fin n)))) := by
    rw [← Subgroup.card_map_of_injective hinj]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ rfl
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (hKC hk) b rfl]
  rw [card_centralizer_inv hb2] at hKcard
  have hsupple := (φ b).support.card_le_univ
  rw [Fintype.card_fin] at hsupple
  have hT : ((φ b).support)ᶜ.card = n - 2 * ((φ b).support.card / 2) := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  generalize hk : (φ b).support.card / 2 = k at hKcard hsupp hm1 hT
  obtain rfl | rfl | rfl : n = 8 ∨ n = 9 ∨ n = 11 := by omega
  · exact hb1 (eq_one_of_card_le hC hKF hKC (by rw [hcardF]; exact le_trans (by decide) hK20))
  · have hk4 : k ≤ 4 := by omega
    interval_cases k <;> norm_num [Nat.factorial] at hKcard <;> omega
  · have hk5 : k ≤ 5 := by omega
    rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | hk3
    · have hKmap := map_eq_altOn_n φ hinj hA b K hKC hK (by omega) (by omega)
      have : IsSimpleGroup (altOn ((φ b).support)ᶜ) := isSimpleGroup_altOn _ (by omega)
      have hKsimple : IsSimpleGroup K :=
        ((K.equivMapOfInjective φ hinj).trans (MulEquiv.subgroupCongr hKmap)).isSimpleGroup
      have hKcard' : Nat.card K = 181440 := by
        rw [← Subgroup.card_map_of_injective hinj, hKmap, card_altOn _ (by omega), hT]
        norm_num [Nat.factorial]
      have hquot := card_quot_of_simple hKsimple (by rw [hKcard']; decide)
      rw [hKcard'] at hquot
      rcases card_socle_cases hp2 hKt with h | h
      · exact ordBC_ne (hp.odd_of_ne_two hp2).pow
          (le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)) (h ▸ hquot)
      · rw [hquot] at h
        exact absurd h (by decide)
    · have hKmap := map_eq_altOn_n φ hinj hA b K hKC hK (by omega) (by omega)
      have hKcard' : Nat.card K = 2520 := by
        rw [← Subgroup.card_map_of_injective hinj, hKmap, card_altOn _ (by omega), hT]
        norm_num [Nat.factorial]
      omega
    · interval_cases k <;> norm_num [Nat.factorial] at hKcard <;> omega

end CFSG.ComponentClassification.GSThmB
