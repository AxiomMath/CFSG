module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusGLB
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharBase

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

section Plane

variable {G : Type*} [Group G] [Finite G]

theorem exists_elemAbelian_card_sq {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (h : 2 ≤ CFSG.Open.pRank p H) :
    ∃ A : Subgroup G, A ≤ H ∧ CFSG.Open.IsElemAbelian p A ∧ Nat.card A = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEH, hEa, hEc⟩ := exists_elem_of_pRank hp.one_lt H
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := 2)
    (by rw [hEc]; exact pow_dvd_pow p h)
  refine ⟨A₀.map E.subtype, (Subgroup.map_subtype_le A₀).trans hEH, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, ⟨x, -, rfl⟩⟩ ⟨_, ⟨y, -, rfl⟩⟩
    apply Subtype.ext
    change (x : G) * y = y * x
    exact congrArg Subtype.val (hEa.1.is_comm.comm x y)
  · rintro _ ⟨x, -, rfl⟩
    exact hEa.2 x x.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hA₀]

omit [Finite G] in
theorem not_isCyclic_of_elemAbelian_card_sq {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hc : Nat.card A = 3 ^ 2) : ¬ IsCyclic A := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h1 : orderOf g = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : g ^ 3 = 1 := Subtype.ext (by simpa using hA.2 g g.2)
  have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h2
  rw [h1, hc] at h3
  omega

end Plane

section Gamma

variable {X : Type} [Group X] [Finite X]

theorem one_le_pRank_of_mem {H : Subgroup X} {x : X} (hx : x ∈ H) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : 1 ≤ CFSG.Open.pRank 3 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hel : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, ha⟩ ⟨_, hb⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact Subtype.ext (Commute.zpow_zpow_self x i j).eq
    · intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hx3]
  exact le_pRank_of_elem (by norm_num) ((Subgroup.zpowers_le).2 hx) hel
    (by rw [Nat.card_zpowers, hord]; norm_num)

theorem mem_gammaCore_of_commute (P : Subgroup X) {x k : X} (hx : x ∈ P) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hk : x * k * x⁻¹ = k) : k ∈ gammaCore 3 1 ⊤ P := by
  have hzP : Subgroup.zpowers x ≤ P := (Subgroup.zpowers_le).2 hx
  have hrk : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers x) :=
    one_le_pRank_of_mem (Subgroup.mem_zpowers x) hx3 hx1
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _, Subgroup.zpowers x, hzP, hrk, ?_⟩
  exact CFSG.AGLEmbedding.mem_normalizer_zpowers_of_commute (by
    have := congrArg (· * x) hk
    simpa [mul_assoc] using this.symm)

theorem le_gammaCore_of_plane {K : Subgroup X} [K.Normal] {L : Type*} [Group L] (e : ↥K ≃* L)
    (P E₀ : Subgroup X) (hE₀P : E₀ ≤ P) (hE₀3 : ∀ x ∈ E₀, x ^ 3 = 1)
    (hplane : Subgroup.closure {c : L | ∃ ε ∈ E₀.map
      (((MulAut.congr e).toMonoidHom).comp (MulAut.conjNormal : X →* MulAut ↥K)),
        ε ≠ 1 ∧ ε c = c} = ⊤) :
    K ≤ gammaCore 3 1 ⊤ P := by
  set H : Subgroup L := ((gammaCore 3 1 ⊤ P).comap K.subtype).map e.toMonoidHom with hH
  have hsub : {c : L | ∃ ε ∈ E₀.map
      (((MulAut.congr e).toMonoidHom).comp (MulAut.conjNormal : X →* MulAut ↥K)),
        ε ≠ 1 ∧ ε c = c} ⊆ H := by
    rintro c ⟨_, ⟨x, hx, rfl⟩, hε1, hεc⟩
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hε1 (map_one _)
    have hfix : MulAut.conjNormal x (e.symm c) = e.symm c := by
      apply e.injective
      have : (MulAut.congr e) (MulAut.conjNormal x) c = c := hεc
      simpa [MulAut.congr_apply] using this
    have hk : x * ((e.symm c : ↥K) : X) * x⁻¹ = ((e.symm c : ↥K) : X) := by
      have := congrArg (fun y : ↥K => (y : X)) hfix
      simpa [MulAut.conjNormal_apply] using this
    exact ⟨e.symm c, mem_gammaCore_of_commute P (hE₀P hx) (hE₀3 x hx) hx1 hk, by simp⟩
  have htop : H = ⊤ := top_le_iff.mp (by rw [← hplane]; exact (Subgroup.closure_le H).2 hsub)
  intro k hk
  have hmem : e ⟨k, hk⟩ ∈ H := htop ▸ Subgroup.mem_top _
  obtain ⟨k', hk', hkk⟩ := hmem
  have : k' = ⟨k, hk⟩ := e.injective hkk
  subst this
  exact hk'

theorem gammaCore_eq_top_of_le {K : Subgroup X} [K.Normal] (P : Sylow 3 X)
    (hKH : K ≤ gammaCore 3 1 ⊤ (P : Subgroup X))
    (hrk : 1 ≤ CFSG.Open.pRank 3 ((P : Subgroup X) ⊓ K)) :
    gammaCore 3 1 ⊤ (P : Subgroup X) = ⊤ := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 3) P (N := K)
  set H : Subgroup X := gammaCore 3 1 ⊤ (P : Subgroup X) with hH
  have hNH : Subgroup.normalizer ((((P : Subgroup X) ⊓ K : Subgroup X)) : Set X) ≤ H :=
    fun x hx => Subgroup.subset_closure ⟨Subgroup.mem_top _, _, inf_le_left, hrk, hx⟩
  have hfr := Sylow.normalizer_sup_eq_top (N := K) T
  have hmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr inf_le_right
  rw [eq_top_iff, ← hfr]
  refine sup_le ?_ hKH
  rw [hmap]
  exact hNH

open Pointwise in
theorem isCyclic_sylow_of {K : Type} [Group K] [Finite K] (T T' : Sylow 3 K)
    (h : IsCyclic (T : Subgroup K)) : IsCyclic (T' : Subgroup K) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T' T
  have hmem : ∀ x : (T' : Subgroup K), g * x * g⁻¹ ∈ (T : Subgroup K) := by
    intro x
    have hc : ((g • T' : Sylow 3 K) : Subgroup K) = MulAut.conj g • (T' : Subgroup K) := rfl
    rw [← hg, hc]
    simpa [MulAut.conj_apply] using
      (Subgroup.smul_mem_pointwise_smul (x : K) (MulAut.conj g) (T' : Subgroup K) x.2)
  let φ : (T' : Subgroup K) →* (T : Subgroup K) :=
    ((MulAut.conj g).toMonoidHom.comp (T' : Subgroup K).subtype).codRestrict _ (fun x => by
      simpa [MulAut.conj_apply] using hmem x)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    simp [φ, MulAut.conj_apply] at this
    exact this
  exact isCyclic_of_injective φ hφ

end Gamma

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
