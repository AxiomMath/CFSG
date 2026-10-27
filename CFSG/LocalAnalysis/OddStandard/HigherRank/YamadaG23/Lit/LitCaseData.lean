module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitQuot1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

@[expose] def litImg (φ : ↥(normalizer (A : Set G)) →* Equiv.Perm (Fin 6)) (M : Subgroup G) :
    Subgroup (Equiv.Perm (Fin 6)) :=
  (M.subgroupOf (normalizer (A : Set G))).map φ

theorem lit_quotIso_M {φ : ↥(normalizer (A : Set G)) →* Equiv.Perm (Fin 6)} (h : LitBar A φ)
    (M : Subgroup G) : IsQuotIso (normIn M A) (centIn M A) ↥(litImg φ M) := by
  have hle : normIn M A ≤ normalizer (A : Set G) := by rw [normIn]; exact inf_le_right
  let ψ : ↥(normIn M A) →* Equiv.Perm (Fin 6) := φ.comp (Subgroup.inclusion hle)
  have hrange : ψ.range = litImg φ M := by
    ext σ
    constructor
    · intro hσ
      rw [MonoidHom.mem_range] at hσ
      obtain ⟨n, rfl⟩ := hσ
      rw [litImg]
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hle n,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp n.2).1, rfl⟩
    · intro hσ
      rw [litImg] at hσ
      rw [MonoidHom.mem_range]
      obtain ⟨y, hy, hyσ⟩ := Subgroup.mem_map.mp hσ
      let ny : ↥(normIn M A) :=
        ⟨(y : G), Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hy, y.2⟩⟩
      refine ⟨ny, ?_⟩
      · change φ (Subgroup.inclusion hle ny) = σ
        have hy_eq : Subgroup.inclusion hle ny = y := Subtype.ext rfl
        rw [hy_eq, hyσ]
  let φ' : ↥(normIn M A) →* ↥(litImg φ M) :=
    ψ.codRestrict (litImg φ M) (fun n => by rw [← hrange]; exact ⟨n, rfl⟩)
  refine ⟨?_, φ', ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ M ∧ x ∈ centralizer (A : Set G) := hx
    exact ⟨hx'.1, Subgroup.centralizer_le_normalizer (A : Set G) hx'.2⟩
  · intro σ
    have hmem : (σ : Equiv.Perm (Fin 6)) ∈ ψ.range := by rw [hrange]; exact σ.2
    rw [MonoidHom.mem_range] at hmem
    obtain ⟨n, hn⟩ := hmem
    exact ⟨n, Subtype.ext hn⟩
  · ext n
    rw [MonoidHom.mem_ker]
    constructor
    · intro hn
      rw [Subgroup.mem_subgroupOf]
      rw [centIn, Subgroup.mem_inf]
      refine ⟨(Subgroup.mem_inf.mp n.2).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 : φ (Subgroup.inclusion hle n) = 1 := by
        have := congrArg Subtype.val hn
        simpa [φ', ψ] using this
      rw [h.ker (Subgroup.inclusion hle n)] at h1
      exact (h1 a ha).symm
    · intro hn
      rw [Subgroup.mem_subgroupOf] at hn
      show φ' n = 1
      apply Subtype.ext
      show φ (Subgroup.inclusion hle n) = 1
      rw [h.ker (Subgroup.inclusion hle n)]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2 a ha).symm

theorem lit_sylow_M {φ : ↥(normalizer (A : Set G)) →* Equiv.Perm (Fin 6)} (h : LitBar A φ)
    {M : Subgroup G} (hAM : A ≤ M) : IsSylowIn 2 (centIn M A) A := by
  have hcent : A ≤ centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr
      (IsMulCommutative.of_setLike_mul_comm h.comm)
  have hAC : A ≤ centIn M A := by
    rw [centIn]
    exact le_inf hAM hcent
  have hA : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [h.card]; norm_num)
  refine ⟨hAC, hA, ?_⟩
  intro h2
  let A' : Subgroup ↥(centIn M A) := A.subgroupOf (centIn M A)
  haveI hA'norm : A'.Normal := by
    change (A.subgroupOf (centIn M A)).Normal
    rw [Subgroup.normal_subgroupOf_iff hAC]
    intro x y hx hy
    have hycent : y ∈ centralizer (A : Set G) := (Subgroup.mem_inf.mp hy).2
    have hcomm : x * y = y * x := Subgroup.mem_centralizer_iff.mp hycent x hx
    have hyx : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [hcomm]
        _ = x := by group
    rwa [hyx]
  have hdvd : 2 ∣ Nat.card (↥(centIn M A) ⧸ A') := by
    rw [← Subgroup.index_eq_card (H := A')]
    exact h2
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centIn M A) ⧸ A') 2 hdvd
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective A' x
  have horder : orderOf (QuotientGroup.mk' A' c) = 2 := by rw [hc, hx]
  have hc_notA : (c : G) ∉ A := by
    intro hcA
    have hcA' : c ∈ A' := Subgroup.mem_subgroupOf.mpr hcA
    have hone : QuotientGroup.mk' A' c = 1 := (QuotientGroup.eq_one_iff c).mpr hcA'
    rw [hone, orderOf_one] at horder
    omega
  have hc_sq_A : (c : G) ^ 2 ∈ A := by
    have h2q : (QuotientGroup.mk' A' c) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (QuotientGroup.mk' A' c)
      rwa [horder] at this
    have hsq : c ^ 2 ∈ A' := by
      have hsq_mk : QuotientGroup.mk' A' (c ^ 2) = 1 := by
        rw [map_pow]
        exact h2q
      exact (QuotientGroup.eq_one_iff (c ^ 2)).mp hsq_mk
    have := Subgroup.mem_subgroupOf.mp hsq
    simpa using this
  have hpow : ∃ k, (c : G) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hA ⟨(c : G) ^ 2, hc_sq_A⟩
    have hk' : ((c : G) ^ 2) ^ 2 ^ k = 1 := by simpa using hk
    refine ⟨k + 1, ?_⟩
    calc (c : G) ^ 2 ^ (k + 1)
        = (c : G) ^ (2 * 2 ^ k) := by
          rw [show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ, Nat.mul_comm (2 ^ k) 2]]
      _ = ((c : G) ^ 2) ^ 2 ^ k := by rw [pow_mul]
      _ = 1 := hk'
  exact hc_notA (h.two_mem (c : G) (Subgroup.mem_inf.mp c.2).2 hpow)

theorem lit_image_cases {φ : ↥(normalizer (A : Set G)) →* Equiv.Perm (Fin 6)} {M : Subgroup G}
    (hA6 : ∀ σ ∈ alternatingGroup (Fin 6),
      ∃ g : ↥(normalizer (A : Set G)), (g : G) ∈ M ∧ φ g = σ) :
    litImg φ M = alternatingGroup (Fin 6) ∨ litImg φ M = ⊤ := by
  by_cases hK : litImg φ M = alternatingGroup (Fin 6)
  · exact Or.inl hK
  · right
    have hle : alternatingGroup (Fin 6) ≤ litImg φ M := by
      intro σ hσ
      obtain ⟨g, hgM, hgφ⟩ := hA6 σ hσ
      rw [← hgφ]
      rw [litImg]
      exact Subgroup.mem_map.mpr ⟨g, Subgroup.mem_subgroupOf.mpr hgM, rfl⟩
    have hdvd : (litImg φ M).index ∣ (alternatingGroup (Fin 6)).index :=
      Subgroup.index_dvd_of_le hle
    rw [alternatingGroup.index_eq_two] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      apply hK
      have hmul := Subgroup.relIndex_mul_index hle
      rw [h2, alternatingGroup.index_eq_two] at hmul
      have hrel : (alternatingGroup (Fin 6)).relIndex (litImg φ M) = 1 := by omega
      exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel) hle

theorem lit_isE_bar {X : Type} [Group X] [Finite X] {Z B : Subgroup X} [Z.Normal]
    (h : LitCtx Z B) {π : X →* G} (hk : π.ker = litP Z) : IsE 4 ↥(B.map π) := by
  change CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup ↥(B.map π)) ∧
    Nat.card ↥(B.map π) = 2 ^ 4
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isMulCommutative_iff_of_setLike]
    intro a _ b _
    exact Subtype.ext (lit_map_comm h hk (a : G) a.2 (b : G) b.2)
  · intro x _
    exact Subtype.ext (lit_map_sq h hk (x : G) x.2)
  · change Nat.card (B.map π) = 2 ^ 4
    rw [lit_map_card h hk]
    norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
