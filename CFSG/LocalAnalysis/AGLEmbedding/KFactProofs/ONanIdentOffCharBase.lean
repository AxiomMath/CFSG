module

public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.LocalAnalysis.AGLEmbedding.AltBeta
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.AGLEmbeddingD2

section Generic

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

omit [Finite K] in
theorem mem_normalizer_zpowers_of_commute {x k : K} (hk : k * x = x * k) :
    k ∈ Subgroup.normalizer (Subgroup.zpowers x : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hc : ∀ n : ℤ, k * x ^ n * k⁻¹ = x ^ n := by
    intro n
    rw [mul_inv_eq_iff_eq_mul]
    exact (Commute.zpow_right (show Commute k x from hk) n).eq
  constructor
  · intro hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [hc n]
    exact hh
  · intro hh
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hcomm : Commute k (x ^ n) := Commute.zpow_right (show Commute k x from hk) n
    have hh' : h = x ^ n := by
      calc h = k⁻¹ * (k * h * k⁻¹) * k := by group
        _ = k⁻¹ * x ^ n * k := by rw [← hn]
        _ = x ^ n := by rw [hcomm.inv_left.eq, inv_mul_cancel_right]
    rw [hh']
    exact Subgroup.zpow_mem_zpowers x n

theorem mem_glbCore_of_commute (hp : p.Prime) {E : Subgroup K} (hE : IsElemAbelian p E) {x k : K}
    (hx : x ∈ E) (hx1 : x ≠ 1) (hk : k * x = x * k) : k ∈ GLBCore p 1 E := by
  have : Fact p.Prime := ⟨hp⟩
  have hoc : orderOf x = p := orderOf_eq_prime (hE.2 x hx) hx1
  exact normalizer_zpowers_le_glbCore hp hx hoc (mem_normalizer_zpowers_of_commute hk)

omit [Finite K] in
theorem isPGroup_of_isElemAbelian {E : Subgroup K} (hE : IsElemAbelian p E) : IsPGroup p E :=
  CFSG.Open.IsElemAbelian.isPGroup hE

omit [Finite K] in
theorem isElemAbelian_closure {S : Set K} (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hpow : ∀ x ∈ S, x ^ p = 1) : IsElemAbelian p (Subgroup.closure S) := by
  have hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    have hS : S ⊆ Subgroup.centralizer S := fun x hx y hy => hcomm y hy x hx
    have h1 : Subgroup.closure S ≤ Subgroup.centralizer S :=
      (Subgroup.closure_le_centralizer_centralizer S).trans (Subgroup.centralizer_le hS)
    intro x hx y hy
    have h2 : x ∈ Subgroup.centralizer (Subgroup.closure S : Set K) := by
      rw [Subgroup.centralizer_closure]
      exact h1 hx
    exact (Subgroup.mem_centralizer_iff.mp h2 y hy).symm
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hc a a.2 b b.2), fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hpow x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [(show Commute x y from hc x hx y hy).mul_pow, ihx, ihy, one_mul]
  | inv _ _ ih => rw [inv_pow, ih, inv_one]

theorem glbCore_eq_top_of_mulEquiv {L : Type*} [Group L] [Finite L] (hp : p.Prime) (e : K ≃* L)
    {E : Subgroup L} (hE : IsPGroup p E) (hcore : GLBCore p 1 E = ⊤) (T : Sylow p K) :
    GLBCore p 1 (T : Subgroup K) = ⊤ := by
  have h := map_glbCore_le hp 1 e.symm E
  rw [hcore, Subgroup.map_top_of_surjective _ e.symm.surjective, top_le_iff] at h
  exact glbCore_eq_top_of_pGroup hp 1 (hE.map e.symm.toMonoidHom) h T

end Generic

section ConjFamily

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

inductive Derivable {ι : Type*} (τ : ι → ι → ι) (I : Set ι) : ι → Prop
  | base {i : ι} : i ∈ I → Derivable τ I i
  | step {a b : ι} : Derivable τ I a → Derivable τ I b → Derivable τ I (τ a b)

theorem glbCore_eq_top_of_conj_family (hp : p.Prime) {ι : Type*} (s : ι → K) (τ : ι → ι → ι)
    (hconj : ∀ a b, s a * s b * (s a)⁻¹ = s (τ a b)) (hgen : Subgroup.closure (Set.range s) = ⊤)
    {E : Subgroup K} (hE : IsElemAbelian p E) (I : Set ι)
    (hI : ∀ i ∈ I, ∃ x ∈ E, x ≠ 1 ∧ s i * x = x * s i) (hder : ∀ j, Derivable τ I j) :
    GLBCore p 1 E = ⊤ := by
  have hmem : ∀ j, s j ∈ GLBCore p 1 E := by
    intro j
    have h := hder j
    induction h with
    | base hi =>
      obtain ⟨x, hx, hx1, hc⟩ := hI _ hi
      exact mem_glbCore_of_commute hp hE hx hx1 hc
    | step _ _ iha ihb =>
      rw [← hconj]
      exact mul_mem (mul_mem iha ihb) (inv_mem iha)
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact hmem j

end ConjFamily

theorem conj_injective_of_simple {K : Type*} [Group K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) : Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (MonoidHom.ker (MulAut.conj : K →* MulAut K)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ MonoidHom.ker (MulAut.conj : K →* MulAut K) := h ▸ Subgroup.mem_top a
    have := congrArg (fun f : MulAut K => f b) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact hab (by simpa [mul_inv_eq_iff_eq_mul] using this)

theorem glbCore_eq_top_of_seitz (hS : KFactSeitzRankTwo) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* CatGroup d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException p d.1) (T : Sylow p K) (hT : ¬ IsCyclic (T : Subgroup K)) :
    GLBCore p 1 (T : Subgroup K) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p (T : Subgroup K)) := ⟨T.isPGroup'⟩
  obtain ⟨E, -, hEcard, hEel⟩ := CFSG.lemma_4_5_a hp2 hT
  set E₀ : Subgroup K := E.map (T : Subgroup K).subtype with hE₀
  have hEel' : IsElemAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mp hEel
  have hE₀el : IsElemAbelian p E₀ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEel' _
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hEcard]
  have hinj := conj_injective_of_simple hs hnab
  let ψ : K →* MulAut (CatGroup d) := (MulAut.congr e).toMonoidHom.comp MulAut.conj
  have hψ : Function.Injective ψ := (MulAut.congr e).injective.comp hinj
  have hψel : IsElemAbelian p (E₀.map ψ) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀el ψ
  have hclos := hS d p hp hp2 hpd hex (E₀.map ψ) hψel
    (by rw [Subgroup.card_map_of_injective hψ, hE₀card])
  have hle : (⊤ : Subgroup (CatGroup d)) ≤ (GLBCore p 1 E₀).map e.toMonoidHom := by
    rw [← hclos, Subgroup.closure_le]
    rintro c ⟨ε, hε, hε1, hεc⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hε
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hε1 (map_one ψ)
    refine ⟨e.symm c, mem_glbCore_of_commute hp hE₀el hx hx1 ?_, by simp⟩
    have h1 : ψ x c = e (x * e.symm c * x⁻¹) := by
      simp [ψ, MulAut.congr_apply]
    rw [h1] at hεc
    have h2 : x * e.symm c * x⁻¹ = e.symm c := by
      apply e.injective
      rw [hεc]
      simp
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  have hcore : GLBCore p 1 E₀ = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨k', hk', hk'e⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_top (e k)))
    exact e.injective hk'e ▸ hk'
  exact glbCore_eq_top_of_mulEquiv hp (MulEquiv.refl K) (isPGroup_of_isElemAbelian hE₀el) hcore T

end CFSG.AGLEmbedding
