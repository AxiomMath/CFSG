module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestExcl
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreSix
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagSp
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def L154OutdiagCfg (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .twA ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 4 ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .E6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1)

theorem exists_pow_eq_of_pow_eq_pow {G : Type*} [CommGroup G] {p d : ℕ} (hpd : Nat.Coprime p d)
    {c x : G} (h : x ^ p = c ^ d) : ∃ μ : G, μ ^ d = x := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hpd
  refine ⟨c ^ a * x ^ b, ?_⟩
  have hc : c ^ (a * (d : ℤ)) = x ^ (a * (p : ℤ)) := by
    rw [mul_comm a (d : ℤ), mul_comm a (p : ℤ), zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, h]
  have e : x = x ^ (a * (p : ℤ) + b * (d : ℤ)) := by rw [hab, zpow_one]
  calc (c ^ a * x ^ b) ^ d = (c ^ a * x ^ b) ^ (d : ℤ) := (zpow_natCast _ _).symm
    _ = c ^ (a * (d : ℤ)) * x ^ (b * (d : ℤ)) := by rw [mul_zpow, ← zpow_mul, ← zpow_mul]
    _ = x ^ (a * (p : ℤ)) * x ^ (b * (d : ℤ)) := by rw [hc]
    _ = x := by rw [← zpow_add, ← e]

theorem mem_of_sq_mem_of_pow_eq_one_of_odd {G : Type*} [Group G] {N : Subgroup G} {φ : G}
    {p : ℕ} (hp : Odd p) (h2 : φ ^ 2 ∈ N) (hφ : φ ^ p = 1) : φ ∈ N := by
  obtain ⟨m, rfl⟩ := hp
  have h : (φ ^ 2) ^ m * φ = 1 := by
    rw [← pow_mul, ← pow_succ]
    exact hφ
  rw [eq_inv_of_mul_eq_one_right h]
  exact N.inv_mem (N.pow_mem h2 m)

theorem ggOutdiagPrime_linear_of_not_dvd {d p : ℕ} {K : Type} [Field K] [CharP K 2]
    (hp : p.Prime) (hpd : ¬ p ∣ d) (hd : 1 ≤ d) :
    GGOutdiagPrime p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  intro φ hφ hφp
  obtain ⟨A, hA⟩ := TypeA.congr_recipeEquiv_mem hφ
  have h1 : conjAut d K (A ^ p) = 1 := by
    rw [map_pow, hA, ← map_pow, hφp, map_one]
  have h2 := AutPSL.mem_center_of_conjAut_eq_one hd h1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
  obtain ⟨c, hc⟩ := h2
  have hdet : Matrix.GeneralLinearGroup.det A ^ p = c ^ d := by
    have := congrArg Matrix.GeneralLinearGroup.det hc
    rw [Matrix.GeneralLinearGroup.det_scalar, map_pow, Fintype.card_fin] at this
    exact this.symm
  obtain ⟨μ, hμ⟩ := exists_pow_eq_of_pow_eq_pow ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd) hdet
  set A' : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) μ⁻¹ * A with hA'
  have hdet' : (A' : Matrix (Fin d) (Fin d) K).det = 1 := by
    have h : Matrix.GeneralLinearGroup.det A' = 1 := by
      rw [hA', map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hμ, inv_pow,
        inv_mul_cancel]
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one]
  set X : Matrix.SpecialLinearGroup (Fin d) K := ⟨A', hdet'⟩ with hX
  have hXA : conjAut d K (Matrix.SpecialLinearGroup.toGL X) = conjAut d K A := by
    have e : Matrix.SpecialLinearGroup.toGL X = A' := Units.ext rfl
    rw [e, hA', map_mul, conjAut_scalar, one_mul]
  rw [← ggCongr_mem_range_conj_iff (TypeA.recipeEquiv d K), ← hA, ← hXA,
    CFSG.LieType.SeitzGeneration.conjAut_toGL]
  exact ⟨_, rfl⟩

theorem l154_outdiagPrime_linear {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .A) (hd : ¬ p ∣ lab.rank + 1) :
    CFSG.StandardType.LargeEvenLabelAll lab fun R _ I _ => GGOutdiagPrime p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hd
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨K, _, _, hK, hq'⟩ := hQ
  have : CharP K 2 := NbrInnerMore.charP_two_of_card_pow hn hK
  exact ⟨K, inferInstance, inferInstance, hK, hq',
    ggOutdiagPrime_linear_of_not_dvd hp hd (by omega)⟩

theorem l154_outdiagPrime_A {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .A)
    (hcfg : ¬ (p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n - 1)) :
    CFSG.StandardType.LargeEvenLabelAll lab fun R _ I _ => GGOutdiagPrime p R I := by
  by_cases hd : p ∣ lab.rank + 1
  · exact NbrInnerMore.largeEvenLabelAll_outdiagPrime_linear hp hlab ht fun hq => hcfg ⟨hd, hq⟩
  · exact l154_outdiagPrime_linear hp hlab ht hd

theorem l154_outdiagPrime_unitary {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twA) (hpq : p ∣ 2 ^ lab.n + 1)
    (hd : ¬ p ∣ lab.rank + 1) :
    CFSG.StandardType.LargeEvenLabelAll lab fun R _ I _ => GGOutdiagPrime p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hpq hd
  subst ht
  obtain ⟨hn, hl, hl2⟩ := hlab
  dsimp only at hl hl2
  have hq' : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have h4 : 4 ≤ 2 ^ n := by
      have := hl2 (by omega)
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this
    omega
  intro Q hQ
  obtain ⟨K, _, _, hK, hq''⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hq'',
    InndiagSU.ggOutdiagPrime_unitary hK hn (show 3 ≤ l + 1 by omega) hq' hp hpq hd⟩

theorem l154_outdiagPrime_twA {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twA)
    (hcfg : ¬ (p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1)) :
    CFSG.StandardType.LargeEvenLabelAll lab fun R _ I _ => GGOutdiagPrime p R I := by
  by_cases hq : p ∣ 2 ^ lab.n + 1
  · exact l154_outdiagPrime_unitary hp hlab ht hq fun hd => hcfg ⟨hd, hq⟩
  · exact NbrInnerMore.largeEvenLabelAll_outdiagPrime_unitary hp hlab ht hq

theorem l154_subset_inn_twD_three {n : ℕ} (hn : 1 ≤ n) :
    CFSG.StandardType.LargeEvenLabelAll ⟨.twD, 3, n⟩
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
  intro Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  simp only [show (3 : ℕ) ≠ 2 by decide, ↓reduceIte] at hQ ⊢
  exact recipeUnitary_subsetInn (coprime_two_pow_add_one_four hn) hQ

theorem ggOutdiagPrime_b2der {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {p : ℕ}
    (hp : Odd p) :
    GGOutdiagPrime p (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
      (LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenGSpSet K 2)) := by
  intro φ hφ hφp
  have hS : LargeEvenGSpSet K 2 ⊆ Subgroup.normalizer
      ((⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ : Subgroup (GL (Fin 2 ⊕ Fin 2) K)) :
        Set (GL (Fin 2 ⊕ Fin 2) K)) := fun A hA =>
    TableB.mem_normalizer_commutator (TableB.mem_largeEvenSpGroup_of_gsp hK hA)
  obtain ⟨A, hA, rfl⟩ := TableB.exists_eq_projConj hS hφ
  have hA2 : A ^ 2 ∈ (⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ :
      Subgroup (GL (Fin 2 ⊕ Fin 2) K)) := by
    have h := Subgroup.pow_index_mem (commutator (LargeEvenSpGroup K 2))
      (⟨A, TableB.mem_largeEvenSpGroup_of_gsp hK hA⟩ : LargeEvenSpGroup K 2)
    rw [TableB.index_commutator_largeEvenSpGroup hK] at h
    exact (TableB.mem_commutator_iff_coe _).mp h
  refine mem_of_sq_mem_of_pow_eq_one_of_odd hp ?_ hφp
  rw [← map_pow]
  exact ⟨_, (TableB.projConj_of_mem _ _ hA2).symm.trans rfl⟩

theorem l154_outdiagPrime_b2der {p : ℕ} (hp : Odd p) {lab : LargeEvenLabel}
    (ht : lab.tag = .B2der) :
    CFSG.StandardType.LargeEvenLabelAll lab fun R _ I _ => GGOutdiagPrime p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  obtain ⟨K, _, _, hK, hq⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hq, ggOutdiagPrime_b2der hK hp⟩

theorem l154_outdiagPrime_E6 {p : ℕ}
    (hp : p.Prime) {lab : LargeEvenLabel} (ht : lab.tag = .E6)
    (hcfg : ¬ (p = 3 ∧ 3 ∣ 2 ^ lab.n - 1)) :
    CFSG.StandardType.LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hcfg
  subst ht
  have hp3 : p ≠ 3 ∨ ¬ 3 ∣ 2 ^ n - 1 := by
    by_cases h3 : p = 3
    · exact Or.inr fun h => hcfg ⟨h3, h⟩
    · exact Or.inl h3
  intro Q hQ
  obtain ⟨K, _, _, hK, hq'⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hq', fun _ _ φ hφ hφp =>
    mem_inn_of_mem_recipeID_E6 hK hp hp3 hφ hφp⟩

section TwE6Diag

@[expose] def DiagInnOn {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r)) (n : ℕ)
    (K : Type) [Field K] (S : (Fin r → ℤ) → Prop) : Prop :=
  ∀ a : Fin r → Kˣ,
    (∀ h ∈ MarkChev.twistedH A S K ρ n, ∃ h' ∈ MarkChev.twistedH A S K ρ n,
      (h' : Module.End K (MarkChev.Space S K)) * TableB.markDiag S K a =
        TableB.markDiag S K a * h) →
    ∃ g ∈ MarkChev.twistedH A S K ρ n,
      (g : Module.End K (MarkChev.Space S K)) = TableB.markDiag S K a

theorem DiagInnOn.of_eq {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {ρ : Equiv.Perm (Fin r)} {n : ℕ}
    {K : Type} [Field K] {S S' : (Fin r → ℤ) → Prop} (hS : S = S') (h : DiagInnOn A ρ n K S) :
    DiagInnOn A ρ n K S' :=
  hS ▸ h

theorem diagHom_mem_of_diagInnOn {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {ρ : Equiv.Perm (Fin r)} {n : ℕ} {K : Type} [Field K]
    (h : DiagInnOn A ρ n K (LargeEvenIsRoot A)) {a : Fin r → Kˣ}
    (ha : ∀ x ∈ LargeEvenTwistedH A K ρ n,
      TableB.diagHom A K a * x * (TableB.diagHom A K a)⁻¹ ∈ LargeEvenTwistedH A K ρ n) :
    TableB.diagHom A K a ∈ LargeEvenTwistedH A K ρ n := by
  rw [largeEvenTwistedH_eq] at ha ⊢
  obtain ⟨g, hg, hgd⟩ := h a fun x hx => ⟨_, ha x hx, by
    rw [← TableB.largeEvenDiagMap_eq_markDiag]
    exact (TableB.diag_rel_iff a x _).2 rfl⟩
  have hge : g = TableB.diagHom A K a := Units.ext (by
    rw [hgd, TableB.coe_diagHom, TableB.largeEvenDiagMap_eq_markDiag])
  rw [← hge]
  exact hg

end TwE6Diag

section TwE6Cert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableB.TwE6


theorem diagInnOn_isRoot {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : ¬ 3 ∣ 2 ^ n + 1) :
    DiagInnOn TwistTag.E6.tag.cartan TwistTag.E6.perm n K (IsRoot TwistTag.E6.tag) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobenius K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := iterateFrobenius_def 2 n
  have hq : 2 ≤ 2 ^ n := TwE6Toral.two_le_two_pow hn
  have hC : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K TwistTag.E6.perm
      n = graphFixedRootGroup TwistTag.E6 K σ := by
    rw [twistedH_eq_commutator K .E6 n σ hσ]
    exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ hσ).2.2.1
  intro a ha
  rw [hC] at ha ⊢
  have hconj : ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ, rootDiagUnit TwistTag.E6.tag a * g *
      (rootDiagUnit TwistTag.E6.tag a)⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    intro g hg
    obtain ⟨h', hh', e⟩ := ha g hg
    rw [TableB.TwE6.markDiag_isRoot] at e
    rw [← TableB.TwE6.eq_conj_of_mul_rootDiag e]
    exact hh'
  have hT : ∀ c ∈ torus₀ σ,
      rootDiagUnit TwistTag.E6.tag c ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    rintro _ ⟨s, hs, rfl⟩
    exact rootDiagUnit_cartanChar_mem (t := TwistTag.E6) hs
  exact ⟨_, hT _ (TwE6Toral.mem_torus₀_of_not_dvd hq hK hσ h3
    fun i => compat_of_forall_conj_mem hconj i), (TableB.TwE6.markDiag_isRoot _).symm⟩

theorem diagHom_mem_twE6_of_not_three_dvd {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : ¬ 3 ∣ 2 ^ n + 1) {a : Fin 6 → Kˣ}
    (ha : ∀ x ∈ LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n,
      TableB.diagHom (LargeEvenCartanE 6) K a * x * (TableB.diagHom (LargeEvenCartanE 6) K a)⁻¹ ∈
        LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) :
    TableB.diagHom (LargeEvenCartanE 6) K a ∈
      LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n :=
  diagHom_mem_of_diagInnOn
    ((diagInnOn_isRoot hn hK h3).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm) ha

theorem l154_subset_inn_twE6 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twE6) (h3 : ¬ 3 ∣ 2 ^ lab.n + 1) :
    CFSG.StandardType.LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h3
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨K, _, _, hK, hq⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hq, fun _ _ =>
    chevIDImage_subset_inn fun a ha => diagHom_mem_twE6_of_not_three_dvd hn hK h3 ha⟩

theorem l154_outdiagPrime_twE6 {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twE6)
    (hcfg : ¬ (p = 3 ∧ 3 ∣ 2 ^ lab.n + 1)) :
    CFSG.StandardType.LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) := by
  by_cases h3 : p = 3
  · subst h3
    exact (l154_subset_inn_twE6 hlab ht fun h => hcfg ⟨rfl, h⟩).mono
      fun _ _ _ _ hI hs hna _ hφ _ => hI hs hna hφ
  · exact NbrInnerMore.largeEvenLabelAll_outdiagPrime_twE6 hp h3 hlab ht

end TwE6Cert

section Labels


theorem l154_outdiagPrime_of_innSubset {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGInnSubsetLabel lab) :
    CFSG.StandardType.LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) :=
  (largeEvenLabelAll_subset_inn_ext hlab h).mono fun _ _ _ _ hI hs hna _ hφ _ => hI hs hna hφ

theorem l154_outdiagPrime_legacy {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hcfg : ¬ L154OutdiagCfg p lab) :
    CFSG.StandardType.LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) := by
  obtain ⟨t, l, n⟩ := lab
  have hS := fun (h : GGInnSubsetLabel ⟨t, l, n⟩) => l154_outdiagPrime_of_innSubset (p := p) hlab h
  cases t
  case A =>
    exact (l154_outdiagPrime_A hp hlab rfl fun h => hcfg (Or.inl ⟨rfl, h.1, h.2⟩)).mono
      fun _ _ _ _ h _ _ => h
  case twA =>
    exact (l154_outdiagPrime_twA hp hlab rfl fun h => hcfg (Or.inr (Or.inl ⟨rfl, h.1, h.2⟩))).mono
      fun _ _ _ _ h _ _ => h
  case B => exact hS (by simp [GGInnSubsetLabel, GGInnerDiagInnLabel, GGInndiagInnLabel])
  case C => exact hS (by simp [GGInnSubsetLabel, GGInnerDiagInnLabel, GGInndiagInnLabel])
  case D =>
    by_cases h3 : l = 3 <;>
      exact hS (by simp [GGInnSubsetLabel, GGInnerDiagInnLabel, GGInndiagInnLabel,
        GGLinearInnLabel, h3])
  case twD =>
    by_cases h3 : l = 3
    · subst h3
      exact (l154_subset_inn_twD_three hlab.1).mono fun _ _ _ _ hI hs hna _ hφ _ => hI hs hna hφ
    · by_cases h2 : l = 2 <;>
        exact hS (by simp [GGInnSubsetLabel, GGInnerDiagInnLabel, GGInndiagInnLabel,
          GGLinearInnLabel, h2, h3])
  case E6 =>
    exact l154_outdiagPrime_E6 hp rfl fun h => hcfg (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))))
  case E7 => exact hS (by simp [GGInnSubsetLabel, GGInnerDiagInnLabel])
  case E8 => exact hS (by simp [GGInnSubsetLabel, GGInnerDiagInnLabel])
  case F4 => exact hS (by simp [GGInnSubsetLabel, GGInnerDiagInnLabel])
  case twE6 =>
    exact l154_outdiagPrime_twE6 hp hlab rfl fun h => hcfg (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, h⟩))))
  case triD4 => exact hS (by simp [GGInnSubsetLabel])
  case G2 => exact hS (by simp [GGInnSubsetLabel, GGInnerDiagInnLabel])
  case twB2 => exact hS (by simp [GGInnSubsetLabel, GGInnerDiagInnLabel, GGInndiagInnLabel])
  case twF4 => exact hS (by simp [GGInnSubsetLabel])
  case B2der =>
    exact (l154_outdiagPrime_b2der (hp.odd_of_ne_two hp2) rfl).mono fun _ _ _ _ h _ _ => h
  case G2der => exact hS (by simp [GGInnSubsetLabel, GGInnerDiagInnLabel])
  case twF4der => exact hS (by simp [GGInnSubsetLabel, GGInnerDiagInnLabel])

end Labels

section Canon


theorem l154_outdiagPrime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hcfg : ¬ L154OutdiagCfg p lab) :
    CFSG.StandardType.Canonical.LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  by_cases hd : MI.DerivedLab lab
  · obtain ⟨t, l, n⟩ := lab
    rcases hd with hd | hd <;> dsimp only at hd <;> subst hd
    · intro Q hQ
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeG2Derived] at hQ ⊢
      obtain ⟨K, _, _, hK, hQK⟩ := hQ
      exact ⟨K, inferInstance, inferInstance, hK,
        ⟨hQK, fun _ hna φ _ hφp => RawAutSmall.mem_inner_g2der hK hna hodd hφp⟩⟩
    · intro Q hQ
      obtain ⟨-, rfl⟩ := hlab.2
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at hQ ⊢
      obtain ⟨K, _, _, hK, hQK⟩ := hQ
      have h2 := RawAutSmall.isPGroup_outer_twF4der (a := (1 - 1) / 2) (by norm_num) hK
      exact ⟨K, inferInstance, inferInstance, hK,
        ⟨hQK, fun _ _ φ _ hφp => RawAut.mem_inner_of_isPGroup_outer h2 hodd hφp⟩⟩
  · exact (MI.canonAll_iff_legacyAll hlab hd _).2 (l154_outdiagPrime_legacy hp hp2 hlab hcfg)

end Canon

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
