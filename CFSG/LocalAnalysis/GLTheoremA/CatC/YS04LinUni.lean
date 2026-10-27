module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04Torus
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04Cover
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Decode
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LieType.Steinberg.CentralExt.UnitaryPerfect
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS04G

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.Blueprint.Multiplier
open Matrix

theorem transfer_torus {H : Type} [Group H] {n : ℕ} {F : Type} [Field F] (f : H →* GL (Fin n) F)
    (hf : Function.Injective f) {p k : ℕ} (E : Subgroup (GL (Fin n) F)) (hE : E ≤ f.range)
    (t : GL (Fin n) F) (htr : t ∈ f.range) (hk : Nat.card E = p ^ k)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hpow : ∀ a ∈ E, a ^ p = 1)
    (hEt : ∀ a ∈ E, a * t = t * a) (ht2 : t ^ 2 = 1) :
    ∃ (E' : Subgroup H) (t' : H), f t' = t ∧ Nat.card E' = p ^ k ∧ IsElemAbelian p E' ∧
      (∀ x ∈ E', x * t' = t' * x) ∧ t' ^ 2 = 1 := by
  obtain ⟨t', rfl⟩ := htr
  refine ⟨E.comap f, t', rfl, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, fun x hx => ?_, ?_⟩
  · have h1 : (E.comap f).map f = E := by
      rw [Subgroup.map_comap_eq, inf_eq_right.2 hE]
    calc Nat.card ↥(E.comap f) = Nat.card ↥((E.comap f).map f) :=
          (Subgroup.card_map_of_injective hf).symm
      _ = Nat.card E := by rw [h1]
      _ = p ^ k := hk
  · apply Subtype.ext
    apply hf
    simp only [Subgroup.coe_mul, map_mul]
    exact hcomm _ a.2 _ b.2
  · apply hf
    rw [map_pow, map_one]
    exact hpow _ hx
  · apply hf
    rw [map_mul, map_mul]
    exact hEt _ hx
  · apply hf
    rw [map_pow, map_one]
    exact ht2

theorem kd26g_linear (hG : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : IsPGroup p (Subgroup.center K)) {m : ℕ} {F : Type} [Field F] [Finite F]
    (e : K ⧸ Subgroup.center K ≃* ProjectiveSpecialLinearGroup (Fin (m + 1)) F)
    (hpn : p ∣ m + 1) (hpq : p ∣ Nat.card F - 1) :
    m + 1 - 3 ≤ GLATwoLocalRank p K ∧
      (Nat.card (Subgroup.center K) = p ^ (Nat.gcd (m + 1) (Nat.card F - 1)).factorization p →
        m + 1 - 2 ≤ GLATwoLocalRank p K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hn3 : 3 ≤ m + 1 := hp3.trans (Nat.le_of_dvd (by omega) hpn)
  have hdvd : p ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact hpq
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨E, t, k, hk, hk2, hcomm, hpow, hEt, ht2, htc, hdetE, hdett, -⟩ :=
    exists_torus (F := F) hn3 hp hω
  set H := SpecialLinearGroup (Fin (m + 1)) F with hH
  have hmemker : ∀ a : GL (Fin (m + 1)) F, (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1 →
      a ∈ (SpecialLinearGroup.toGL : H →* GL (Fin (m + 1)) F).range := by
    intro a ha
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, ha, Units.val_one])
  obtain ⟨E', t', ht'f, hk', hE', hEt', ht2'⟩ := transfer_torus SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective E (fun a ha => hmemker a (hdetE a ha)) t
    (hmemker t hdett) hk hcomm hpow hEt ht2
  have ht'N : t' ∉ Subgroup.center H := fun hc =>
    htc (ht'f ▸ (SpecialLinearGroup.toGL_mem_center_iff t').2 hc)
  set N : Subgroup H := Subgroup.center H with hN
  let ρ : K →* H ⧸ N := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨p', f, hp', hf, hFq⟩ : ∃ p' f : ℕ, p'.Prime ∧ 0 < f ∧ Nat.card F = p' ^ f := by
    haveI := Fintype.ofFinite F
    obtain ⟨n, hp', hn⟩ := FiniteField.card F (ringChar F)
    exact ⟨ringChar F, n, hp', n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hadm : StatedLieAdmissible .PSL (m + 1) p' f := by
    refine ⟨hp', hf, by omega, ?_, ?_⟩ <;>
    · intro h
      have := congrArg Prod.fst h
      simp only at this
      omega
  have hmodel : CFSG.Models.LieModel (ProjectiveSpecialLinearGroup (Fin (m + 1)) F) .PSL (m + 1)
      p' f :=
    ⟨hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, hFq,
      ⟨projectiveSpecialLinearGroupEquivStatedProj (m + 1) F⟩⟩⟩
  haveI : Finite (hopfMultiplier (ProjectiveSpecialLinearGroup (Fin (m + 1)) F)) :=
    finite_hopf_of_model hG hmodel
  have hcenter : Nat.card N = Nat.gcd (m + 1) (Nat.card F - 1) :=
    CFSG.OrderReductions.LinearOrders.card_specialLinear_center F (m + 1) (by omega)
  have hg : genericOrders .PSL (m + 1) p' f = (Nat.gcd (m + 1) (Nat.card F - 1), 1) := by
    rw [hFq]
    rfl
  have hg0 : Nat.gcd (m + 1) (Nat.card F - 1) ≠ 0 := by
    rw [← hcenter]
    exact Nat.card_pos.ne'
  have hM := hopf_factorization_le hG hmodel (Or.inl rfl) hp hp2 hpn hn3 hg hg0
  have hM' : (Nat.card (hopfMultiplier (H ⧸ N))).factorization p ≤
      (Nat.card N).factorization p := by rw [hcenter]; exact hM
  have hKperf : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
  have hHperf : Group.IsPerfect H :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hn3
  obtain ⟨h1, h2⟩ := rank_of_cover hp N le_rfl
    (CFSG.LieType.Steinberg.isCyclic_center_specialLinearGroup (m + 1) F) hHperf hKperf ρ hρ hρk
    hZ hM' hE' hk' ht2' ht'N hEt'
  refine ⟨?_, fun hcard => ?_⟩
  · exact le_trans (by omega) h1
  · exact le_trans (by omega) (h2 (by rw [hcenter]; exact hcard))

theorem kd26g_unitary (hG : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : IsPGroup p (Subgroup.center K)) {m ℓ f : ℕ} {F : Type} [Field F]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f F)
    (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU (m + 1) (ℓ ^ f) F))
    (hq3 : m = 2 → 3 ≤ ℓ ^ f) (hpn : p ∣ m + 1) (hpq : p ∣ ℓ ^ f + 1) :
    m + 1 - 3 ≤ GLATwoLocalRank p K ∧
      (Nat.card (Subgroup.center K) = p ^ (Nat.gcd (m + 1) (ℓ ^ f + 1)).factorization p →
        m + 1 - 2 ≤ GLATwoLocalRank p K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : Finite F := h.finite
  haveI : CharP F ℓ := h.charP
  have hF : Nat.card F = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hn3 : 3 ≤ m + 1 := hp3.trans (Nat.le_of_dvd (by omega) hpn)
  have hq : (m + 1, ℓ ^ f) ≠ (3, 2) := by
    intro h32
    have h1 := congrArg Prod.fst h32
    have h2 := congrArg Prod.snd h32
    simp only at h1 h2
    have := hq3 (by omega)
    omega
  have hdvd : p ∣ Nat.card Fˣ := by
    have h1 := Nat.sq_sub_sq (ℓ ^ f) 1
    rw [one_pow] at h1
    rw [Nat.card_units, hF, h1]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hωq : ω ^ (ℓ ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hω ▸ hpq)
  have hneg : (-1 : F) ^ (ℓ ^ f) = -1 := neg_one_pow_char_pow F (p := ℓ) (n := f)
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ h.prime.ne_zero
  obtain ⟨E, t, k, hk, hk2, hcomm, hpow, hEt, ht2, htc, hdetE, hdett, hunit⟩ :=
    exists_torus (F := F) hn3 hp hω
  obtain ⟨hunitE, hunitt⟩ := hunit (ℓ ^ f) hq0 hωq hneg
  set H₀ := StatedSU (m + 1) (ℓ ^ f) F with hH₀
  have hset := (CFSG.LinearGroups.unitary_scalar_kernel h.prime hF (n := m + 1) (by omega)).1
  have hmem : ∀ a : GL (Fin (m + 1)) F, (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1 →
      ((a : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (· ^ ℓ ^ f))ᵀ *
        (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 → a ∈ H₀ := by
    intro a h1 h2
    rw [← SetLike.mem_coe, hset]
    exact ⟨h1, h2⟩
  have hrange : H₀.subtype.range = H₀ := Subgroup.range_subtype H₀
  have hEle : E ≤ H₀.subtype.range := by
    rw [hrange]
    intro a ha
    exact hmem a (hdetE a ha) (hunitE a ha)
  have htr : t ∈ H₀.subtype.range := by
    rw [hrange]
    exact hmem t hdett hunitt
  obtain ⟨E', t', ht'f, hk', hE', hEt', ht2'⟩ := transfer_torus H₀.subtype
    H₀.subtype_injective E hEle t htr hk hcomm hpow hEt ht2
  set N : Subgroup H₀ := (StatedScalars (Fin (m + 1)) F).subgroupOf H₀ with hN
  have hNc : N ≤ Subgroup.center H₀ := fun z hz => by
    have hz' : (z : GL (Fin (m + 1)) F) ∈ Subgroup.center (GL (Fin (m + 1)) F) := by
      have h1 := Subgroup.mem_subgroupOf.1 hz
      rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 hz' g)
  have ht'N : t' ∉ N := fun hc => by
    have h1 := Subgroup.mem_subgroupOf.1 hc
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    exact htc (by rw [← ht'f]; exact h1)
  obtain ⟨hZcyc, -⟩ := CFSG.LieType.Steinberg.isCyclic_scalars_statedSU hF (n := m + 1) (by omega)
  have hcenter : Nat.card N = Nat.gcd (m + 1) (ℓ ^ f + 1) :=
    (CFSG.LinearGroups.unitary_scalar_kernel h.prime hF (n := m + 1) (by omega)).2.2
  let ρ : K →* H₀ ⧸ N := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hadm : StatedLieAdmissible .PSU (m + 1) ℓ f := by
    refine ⟨h.prime, h.one_le, hn3, hq⟩
  have hmodel : CFSG.Models.LieModel (StatedProj H₀) .PSU (m + 1) ℓ f :=
    ⟨hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩⟩
  haveI : Finite (hopfMultiplier (StatedProj H₀)) := finite_hopf_of_model hG hmodel
  have hg : genericOrders .PSU (m + 1) ℓ f = (Nat.gcd (m + 1) (ℓ ^ f + 1), 1) := rfl
  have hg0 : Nat.gcd (m + 1) (ℓ ^ f + 1) ≠ 0 := by
    rw [← hcenter]
    exact Nat.card_pos.ne'
  have hM := hopf_factorization_le hG hmodel (Or.inr rfl) hp hp2 hpn hn3 hg hg0
  have hM' : (Nat.card (hopfMultiplier (H₀ ⧸ N))).factorization p ≤
      (Nat.card N).factorization p := by rw [hcenter]; exact hM
  have hKperf : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
  have hHperf : Group.IsPerfect H₀ :=
    CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd hF hn3 hq
  obtain ⟨h1, h2⟩ := rank_of_cover hp N hNc hZcyc hHperf hKperf ρ hρ hρk hZ hM' hE' hk' ht2'
    ht'N hEt'
  refine ⟨?_, fun hcard => ?_⟩
  · exact le_trans (by omega) h1
  · exact le_trans (by omega) (h2 (by rw [hcenter]; exact hcard))

end CFSG.LocalAnalysis.GLTheoremA.YS04G
