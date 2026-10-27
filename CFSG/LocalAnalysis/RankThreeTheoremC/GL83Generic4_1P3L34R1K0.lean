module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34c
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Basics

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_transitive (hK7 : KFactL34SylowTransitive) {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    ∀ a ∈ (P : Subgroup G) ⊓ J, ∀ b ∈ (P : Subgroup G) ⊓ J, a ≠ 1 → b ≠ 1 →
      ∃ n ∈ centralizer ({x} : Set G),
        n ∈ normalizer (((P : Subgroup G) ⊓ J : Subgroup G) : Set G) ∧ n * a * n⁻¹ = b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJC := hJ.le_centralizer
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hOcop : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  set A : Subgroup G := (P : Subgroup G) ⊓ J with hA
  have hAC : A ≤ C := inf_le_right.trans hJC
  set K' : Subgroup C := A.subgroupOf C with hK'
  have hK'p : IsPGroup 3 K' := (P.isPGroup'.to_le inf_le_left).comap_subtype
  have hSylJ : IsSylowOf 3 A J := by
    have h := hgen.2.2.1.inf_of_le_normalizer hJC hJ.centralizer_le
    have hPJ : ((P : Subgroup G) ⊓ C) ⊓ J = (P : Subgroup G) ⊓ J := by
      rw [inf_assoc, inf_eq_right.mpr hJC]
    rwa [hPJ] at h
  obtain ⟨TJ, hTJ⟩ := hSylJ
  set φ : ↥J →* ↥(r1sBar x J) := r1sHom x hJC with hφ
  set S : Sylow 3 ↥(r1sBar x J) := TJ.mapSurjective (r1sHom_surjective x hJC) with hS
  have hSmap : (S : Subgroup ↥(r1sBar x J)).map (r1sBar x J).subtype = K'.map π := by
    rw [hS, Sylow.coe_mapSurjective, Subgroup.map_map]
    rw [hK', ← hTJ]
    have h1 : ((TJ : Subgroup ↥J).map J.subtype).subgroupOf C =
        (TJ : Subgroup ↥J).map (Subgroup.inclusion hJC) := by
      ext c
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨j, hj, hjc⟩
        exact ⟨j, hj, Subtype.ext hjc⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
    rw [h1, Subgroup.map_map]
    rfl
  have hAS : ∀ c : ↥C, (c : G) ∈ A → π c ∈ ((S : Subgroup ↥(r1sBar x J)).map
      (r1sBar x J).subtype) := fun c hc => by
    rw [hSmap]
    exact ⟨c, mem_subgroupOf.mpr hc, rfl⟩
  intro a ha b hb ha1 hb1
  have haC : a ∈ C := hAC ha
  have hbC : b ∈ C := hAC hb
  have hmem : ∀ z : G, z ∈ A → ∀ hz : z ∈ C, ∃ s ∈ (S : Subgroup ↥(r1sBar x J)),
      ((s : ↥(r1sBar x J)) : C ⧸ O) = π ⟨z, hz⟩ := by
    intro z hz hzC
    obtain ⟨s, hs, hs'⟩ := hAS ⟨z, hzC⟩ hz
    exact ⟨s, hs, hs'⟩
  obtain ⟨a', ha', ha'π⟩ := hmem a ha haC
  obtain ⟨b', hb', hb'π⟩ := hmem b hb hbC
  have hπinj : ∀ {u v : C}, (u : G) ∈ A → (v : G) ∈ A → π u = π v → u = v := fun {u v} hu hv h =>
    p34_mk_inj hOcop hK'p (mem_subgroupOf.mpr hu) (mem_subgroupOf.mpr hv) h
  have ha'1 : a' ≠ 1 := by
    intro h
    rw [h] at ha'π
    have : π ⟨a, haC⟩ = π 1 := by rw [map_one]; exact ha'π.symm
    have := hπinj ha (by simp) this
    exact ha1 (congrArg Subtype.val this)
  have hb'1 : b' ≠ 1 := by
    intro h
    rw [h] at hb'π
    have : π ⟨b, hbC⟩ = π 1 := by rw [map_one]; exact hb'π.symm
    have := hπinj hb (by simp) this
    exact hb1 (congrArg Subtype.val this)
  obtain ⟨n', hn'N, hn'ab⟩ := hK7 _ (r1sBar_isL34 hJ) S a' b' ha' hb' ha'1 hb'1
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective O (n' : C ⧸ O)
  have hnN : n ∈ (normalizer ((K'.map π : Subgroup (C ⧸ O)) : Set (C ⧸ O))).comap π := by
    rw [Subgroup.mem_comap, ← hSmap]
    have := Subgroup.le_normalizer_map (r1sBar x J).subtype ⟨n', hn'N, rfl⟩
    rw [hπ, hn]
    exact this
  have hfr := CFSG.AGLEmbedding.comap_normalizer_map_le_sup Nat.prime_three O hOcop hK'p hnN
  have hfr' : n ∈ ((O ⊔ normalizer (K' : Set C) : Subgroup C) : Set C) := hfr
  rw [Subgroup.normal_mul] at hfr'
  obtain ⟨o, ho, n₁, hn₁, hon⟩ := hfr'
  have hon' : o * n₁ = n := hon
  have ho' : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  have hπn : π n = π n₁ := by rw [← hon', map_mul, ho', one_mul]
  have hmemK : n₁ * ⟨a, haC⟩ * n₁⁻¹ ∈ K' := (mem_normalizer_iff.mp hn₁ _).mp (mem_subgroupOf.mpr ha)
  have heq : n₁ * ⟨a, haC⟩ * n₁⁻¹ = ⟨b, hbC⟩ := by
    refine p34_mk_inj hOcop hK'p hmemK (mem_subgroupOf.mpr hb) ?_
    rw [map_mul, map_mul, map_inv, ← hπn, hπ, hn]
    have h2 := congrArg (fun z : ↥(r1sBar x J) => (z : C ⧸ O)) hn'ab
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h2
    rw [← ha'π, ← hb'π]
    exact h2
  refine ⟨(n₁ : G), n₁.2, ?_, congrArg Subtype.val heq⟩
  have hKA : K'.map C.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAC
  have := Subgroup.le_normalizer_map C.subtype ⟨n₁, hn₁, rfl⟩
  rwa [hKA] at this

end CFSG.LocalAnalysis.RankThreeTheoremC
