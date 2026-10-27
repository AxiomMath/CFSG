module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open scoped Pointwise

section Elementary

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem zpowers_inf_eq_bot_of_notMem (hp : p.Prime) {E : Subgroup X} {t : X}
    (ht : orderOf t = p) (htE : t ∉ E) : zpowers t ⊓ E = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (zpowers t) = p := by rw [Nat.card_zpowers, ht]
  have : Fact (Nat.card (zpowers t)).Prime := ⟨by rw [hcard]; exact hp⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (E.subgroupOf (zpowers t)) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : zpowers t) ∈ E.subgroupOf (zpowers t) := hx.2
    rw [h, mem_bot] at this
    exact mem_bot.2 (congrArg Subtype.val this)
  · exfalso
    apply htE
    have : (⟨t, mem_zpowers t⟩ : zpowers t) ∈ E.subgroupOf (zpowers t) := by
      rw [h]; exact mem_top _
    exact this

theorem card_sup_zpowers_of_mem_centralizer (hp : p.Prime) {E : Subgroup X} {t : X}
    (ht : orderOf t = p) (hC : t ∈ centralizer (E : Set X)) (htE : t ∉ E) :
    Nat.card (E ⊔ zpowers t : Subgroup X) = Nat.card E * p := by
  have hcomm : ∀ (e : E) (s : zpowers t), Commute (E.subtype e) ((zpowers t).subtype s) := by
    intro e s
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 s.2
    show (e : X) * (s : X) = (s : X) * (e : X)
    rw [← hk]
    have h1 : Commute (e : X) t := ((mem_centralizer_iff.1 hC) (e : X) e.2).symm.symm
    exact (h1.zpow_right k).eq
  let φ : E × zpowers t →* X := E.subtype.noncommCoprod (zpowers t).subtype hcomm
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨e, s⟩ h
    have h' : (e : X) * (s : X) = 1 := h
    have hs : (s : X) = (e : X)⁻¹ := eq_inv_of_mul_eq_one_right h'
    have hmem : (s : X) ∈ zpowers t ⊓ E := ⟨s.2, by rw [hs]; exact E.inv_mem e.2⟩
    rw [zpowers_inf_eq_bot_of_notMem hp ht htE, mem_bot] at hmem
    have he : (e : X) = 1 := by rw [hs] at hmem; simpa using hmem
    exact Prod.ext (Subtype.ext he) (Subtype.ext hmem)
  have hrange : φ.range = E ⊔ zpowers t := by
    rw [MonoidHom.noncommCoprod_range]
    simp [Subgroup.range_subtype]
  have hcard : Nat.card φ.range = Nat.card (E × zpowers t) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [← hrange, hcard, Nat.card_prod, Nat.card_zpowers, ht]

theorem isElemAbelian_sup_zpowers (hp : p.Prime) {E : Subgroup X} (hE : IsElemAbelian p E)
    {k : ℕ} (hk : Nat.card E = p ^ k) {t : X} (ht : orderOf t = p)
    (hC : t ∈ centralizer (E : Set X)) (htE : t ∉ E) :
    IsElemAbelian p (E ⊔ zpowers t) ∧ Nat.card (E ⊔ zpowers t : Subgroup X) = p ^ (k + 1) := by
  have htp : t ^ p = 1 := ht ▸ pow_orderOf_eq_one t
  have hEt : E ≤ centralizer ((zpowers t : Subgroup X) : Set X) :=
    le_centralizer_iff.mp (zpowers_le.mpr hC)
  refine ⟨CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p hE
    (isElemAbelian_zpowers htp) hEt, ?_⟩
  rw [card_sup_zpowers_of_mem_centralizer hp ht hC htE, hk, pow_succ]

end Elementary

section Conj

variable {X : Type*} [Group X]

theorem mem_conj_smul_iff (g : X) (K : Subgroup X) (x : X) :
    x ∈ MulAut.conj g • K ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def]
  rw [← map_inv, MulAut.conj_apply]
  simp [mul_assoc]

theorem conj_smul_eq_self_iff (g : X) (K : Subgroup X) :
    MulAut.conj g • K = K ↔ g ∈ normalizer (K : Set X) := by
  rw [mem_normalizer_iff]
  constructor
  · intro h x
    have h1 : g * x * g⁻¹ ∈ MulAut.conj g • K ↔ g * x * g⁻¹ ∈ K := by rw [h]
    rw [mem_conj_smul_iff] at h1
    simpa [mul_assoc] using h1
  · intro h
    ext x
    rw [mem_conj_smul_iff, h (g⁻¹ * x * g)]
    simp [mul_assoc]

theorem isComponentOf_conj_smul {K : Subgroup X} (hK : IsComponentOf K ⊤) (g : X) :
    IsComponentOf (MulAut.conj g • K) ⊤ :=
  (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).2 hK

end Conj

section Components

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem exists_isElemAbelian_of_components (hp : p.Prime) (hodd : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (S : Finset (Subgroup X))
    (hS : ∀ K ∈ S, IsComponentOf K ⊤) {A : Subgroup X} (hA : IsElemAbelian p A) {a : ℕ}
    (hAcard : Nat.card A = p ^ a) (hAC : ∀ K ∈ S, A ≤ centralizer (K : Set X)) :
    ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ (S.card + a) ∧
      E ≤ A ⊔ ⨆ K ∈ S, K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R⟩ : Nonempty (Sylow p X) := inferInstance
  revert hS hAC
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    exact ⟨A, hA, by simpa using hAcard, le_sup_left⟩
  | insert K₀ S' hK₀ ih =>
    intro hS hAC
    obtain ⟨E', hE', hE'card, hE'le⟩ :=
      ih (fun K hK => hS K (Finset.mem_insert_of_mem hK))
        (fun K hK => hAC K (Finset.mem_insert_of_mem hK))
    have hK₀c : IsComponentOf K₀ ⊤ := hS K₀ (Finset.mem_insert_self _ _)
    obtain ⟨t, htRK, ht, htZ⟩ := exists_mem_sylow_inf_component hp hodd hcore R hK₀c
    have htK₀ : t ∈ K₀ := htRK.2
    have hE'C : E' ≤ centralizer (K₀ : Set X) := by
      refine hE'le.trans (sup_le (hAC K₀ (Finset.mem_insert_self _ _)) ?_)
      refine iSup₂_le fun K hK => ?_
      have hne : K ≠ K₀ := fun h => hK₀ (h ▸ hK)
      exact commutator_eq_bot_iff_le_centralizer.mp
        (ComponentClassification.LocalComponents.commute_of_ne K K₀
          (hS K (Finset.mem_insert_of_mem hK)) hK₀c hne)
    have htC : t ∈ centralizer (E' : Set X) := by
      rw [mem_centralizer_iff]
      intro e he
      exact (mem_centralizer_iff.1 (hE'C he) t htK₀).symm
    have htE' : t ∉ E' := fun h => htZ (hE'C h)
    obtain ⟨hEel, hEcard⟩ := isElemAbelian_sup_zpowers hp hE' hE'card ht htC htE'
    refine ⟨E' ⊔ zpowers t, hEel, ?_, sup_le ?_ ?_⟩
    · rw [hEcard, Finset.card_insert_of_notMem hK₀]
      congr 1
      omega
    · refine hE'le.trans (sup_le_sup_left ?_ A)
      exact iSup₂_le fun K hK => le_iSup₂_of_le K (Finset.mem_insert_of_mem hK) le_rfl
    · exact (zpowers_le.mpr htK₀).trans
        (le_sup_of_le_right (le_iSup₂_of_le K₀ (Finset.mem_insert_self _ _) le_rfl))

theorem card_add_le_pRank_of_components (hp : p.Prime) (hodd : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (S : Finset (Subgroup X))
    (hS : ∀ K ∈ S, IsComponentOf K ⊤) {A : Subgroup X} (hA : IsElemAbelian p A) {a : ℕ}
    (hAcard : Nat.card A = p ^ a) (hAC : ∀ K ∈ S, A ≤ centralizer (K : Set X)) :
    S.card + a ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨E, hE, hcard, -⟩ := exists_isElemAbelian_of_components hp hodd hcore S hS hA hAcard hAC
  exact le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp ⊤)
    ⟨E, le_top, hE, hcard⟩

end Components

section Normalize

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem mem_normalizer_of_pow_mem (hp : p.Prime) {u : X} (hu : IsPGroup p (zpowers u)) {d : ℕ}
    (hd0 : 0 < d) (hdp : d < p) {K : Subgroup X} (h : u ^ d ∈ normalizer (K : Set X)) :
    u ∈ normalizer (K : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hu) (⟨u, mem_zpowers u⟩ : zpowers u)
  have hord : orderOf u = p ^ j := by
    have h := Subgroup.orderOf_coe (⟨u, mem_zpowers u⟩ : zpowers u)
    rw [← hj, ← h]
  have hcop : (orderOf u).Coprime d := by
    rw [hord]
    refine Nat.Coprime.pow_left _ ?_
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (fun hdvd => by
      have := Nat.le_of_dvd hd0 hdvd
      omega)
  have hord' : orderOf (u ^ d) = orderOf u := Nat.Coprime.orderOf_pow hcop
  have hle : zpowers (u ^ d) ≤ zpowers u := zpowers_le.mpr (pow_mem (mem_zpowers u) d)
  have hcard : Nat.card (zpowers u) ≤ Nat.card (zpowers (u ^ d)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord']
  have heq : zpowers (u ^ d) = zpowers u := (eq_of_le_of_card_ge hle hcard)
  have hu' : u ∈ zpowers (u ^ d) := by rw [heq]; exact mem_zpowers u
  exact (zpowers_le.mpr h) hu'

theorem le_normalizer_of_card_components_le (hp : p.Prime) {m : ℕ} (hmp : m < p)
    (hcard : ∀ S : Finset (Subgroup X), (∀ K ∈ S, IsComponentOf K ⊤) → S.card ≤ m)
    {R : Subgroup X} (hR : IsPGroup p R) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    R ≤ normalizer (K : Set X) := by
  classical
  intro u hu
  let f : Fin (m + 1) → Subgroup X := fun i => MulAut.conj (u ^ (i : ℕ)) • K
  have hfc : ∀ i, IsComponentOf (f i) ⊤ := fun i => isComponentOf_conj_smul hK _
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    have h1 := hcard (Finset.univ.image f) (by
      intro L hL
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hL
      exact hfc i)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at h1
    omega
  have key : ∀ a b : ℕ, a < b → b ≤ m → MulAut.conj (u ^ a) • K = MulAut.conj (u ^ b) • K →
      u ∈ normalizer (K : Set X) := by
    intro a b hab hbm h
    have hb : u ^ b = u ^ a * u ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [hb, map_mul, mul_smul] at h
    have h2 : K = MulAut.conj (u ^ (b - a)) • K := MulAction.injective (MulAut.conj (u ^ a)) h
    have h3 : u ^ (b - a) ∈ normalizer (K : Set X) :=
      (conj_smul_eq_self_iff _ _).1 h2.symm
    have hu' : IsPGroup p (zpowers u) :=
      hR.to_le (zpowers_le.mpr hu)
    exact mem_normalizer_of_pow_mem hp hu' (d := b - a) (by omega) (by omega) h3
  obtain ⟨i, j, hfij, hij⟩ := Function.not_injective_iff.mp hnotinj
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key i j hlt (by omega) hfij
  · exact key j i hlt (by omega) hfij.symm

end Normalize

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
