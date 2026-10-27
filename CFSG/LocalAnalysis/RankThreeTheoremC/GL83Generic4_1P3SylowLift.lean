module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowActionKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Basics
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Basics
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34c

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_of_mk_mem_normalizer {C : Type*} [Group C] [Finite C]
    (O : Subgroup C) [O.Normal] (hO : Nat.Coprime 3 (Nat.card O)) {K' : Subgroup C}
    (hK' : IsPGroup 3 K') {n : C}
    (hn : QuotientGroup.mk' O n ∈
      normalizer ((K'.map (QuotientGroup.mk' O) : Subgroup (C ⧸ O)) : Set (C ⧸ O))) :
    ∃ n₁ ∈ normalizer (K' : Set C), QuotientGroup.mk' O n₁ = QuotientGroup.mk' O n := by
  have hfr := CFSG.AGLEmbedding.comap_normalizer_map_le_sup Nat.prime_three O hO hK'
    (Subgroup.mem_comap.mpr hn)
  have hfr' : n ∈ ((O ⊔ normalizer (K' : Set C) : Subgroup C) : Set C) := hfr
  rw [Subgroup.normal_mul] at hfr'
  obtain ⟨o, ho, n₁, hn₁, hon⟩ := hfr'
  refine ⟨n₁, hn₁, ?_⟩
  have hon' : o * n₁ = n := hon
  have ho' : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  rw [← hon', map_mul, ho', one_mul]

theorem r1s_normalizer_data {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJC : J ≤ centralizer ({x} : Set G))
    (hCJ : centralizer ({x} : Set G) ≤ normalizer (J : Set G)) :
    ∃ (S : Sylow 3 ↥(r1sBar x J)) (φ : ↥((P : Subgroup G) ⊓ J) →* ↥(r1sBar x J)),
      Function.Injective φ ∧ (∀ a, φ a ∈ (S : Subgroup ↥(r1sBar x J))) ∧
      (∀ s ∈ (S : Subgroup ↥(r1sBar x J)), ∃ a, φ a = s) ∧
      ∀ n' ∈ normalizer ((S : Subgroup ↥(r1sBar x J)) : Set ↥(r1sBar x J)),
        ∃ n ∈ centralizer ({x} : Set G),
          n ∈ normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ∧
          ∀ a b : ↥((P : Subgroup G) ⊓ J), (b : G) = n * a * n⁻¹ → φ b = n' * φ a * n'⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hOcop : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  set A : Subgroup G := (P : Subgroup G) ⊓ J with hA
  have hAJ : A ≤ J := inf_le_right
  have hAC : A ≤ C := hAJ.trans hJC
  set K' : Subgroup C := A.subgroupOf C with hK'
  have hK'p : IsPGroup 3 K' := (P.isPGroup'.to_le inf_le_left).comap_subtype
  have hSylJ : IsSylowOf 3 A J := by
    have h := hgen.2.2.1.inf_of_le_normalizer hJC hCJ
    have hPJ : ((P : Subgroup G) ⊓ C) ⊓ J = (P : Subgroup G) ⊓ J := by
      rw [inf_assoc, inf_eq_right.mpr hJC]
    rwa [hPJ] at h
  obtain ⟨TJ, hTJ⟩ := hSylJ
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
  have hπinj : ∀ {u v : C}, (u : G) ∈ A → (v : G) ∈ A → π u = π v → u = v := fun {u v} hu hv h =>
    p34_mk_inj hOcop hK'p (mem_subgroupOf.mpr hu) (mem_subgroupOf.mpr hv) h
  set φ : ↥A →* ↥(r1sBar x J) := (r1sHom x hJC).comp (Subgroup.inclusion hAJ) with hφ
  have hφval : ∀ a : ↥A, ((φ a : ↥(r1sBar x J)) : C ⧸ O) = π ⟨(a : G), hAC a.2⟩ := fun a => rfl
  refine ⟨S, φ, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 := congrArg (fun z : ↥(r1sBar x J) => (z : C ⧸ O)) hab
    simp only [hφval] at h1
    have h2 : (⟨(a : G), hAC a.2⟩ : C) = ⟨(b : G), hAC b.2⟩ := hπinj a.2 b.2 h1
    exact Subtype.ext (congrArg (fun c : ↥C => (c : G)) h2)
  · intro a
    have hmem : π ⟨(a : G), hAC a.2⟩ ∈ (S : Subgroup ↥(r1sBar x J)).map (r1sBar x J).subtype := by
      rw [hSmap]
      exact ⟨⟨(a : G), hAC a.2⟩, mem_subgroupOf.mpr a.2, rfl⟩
    obtain ⟨s, hs, hsπ⟩ := hmem
    have : φ a = s := Subtype.ext ((hφval a).trans hsπ.symm)
    rw [this]
    exact hs
  · intro s hs
    have hmem : (s : C ⧸ O) ∈ K'.map π := by
      rw [← hSmap]
      exact ⟨s, hs, rfl⟩
    obtain ⟨c, hc, hcπ⟩ := hmem
    exact ⟨⟨(c : G), mem_subgroupOf.mp hc⟩, Subtype.ext (by rw [hφval]; exact hcπ)⟩
  · intro n' hn'N
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective O (n' : C ⧸ O)
    have hnN : π n ∈ normalizer ((K'.map π : Subgroup (C ⧸ O)) : Set (C ⧸ O)) := by
      rw [hn, ← hSmap]
      exact Subgroup.le_normalizer_map (r1sBar x J).subtype ⟨n', hn'N, rfl⟩
    obtain ⟨n₁, hn₁, hn₁π⟩ := exists_mem_normalizer_of_mk_mem_normalizer O hOcop hK'p hnN
    refine ⟨(n₁ : G), n₁.2, ?_, fun a b hab => ?_⟩
    · have hKA : K'.map C.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAC
      have := Subgroup.le_normalizer_map C.subtype ⟨n₁, hn₁, rfl⟩
      rwa [hKA] at this
    · refine Subtype.ext ?_
      have hbC : (⟨(b : G), hAC b.2⟩ : C) = n₁ * ⟨(a : G), hAC a.2⟩ * n₁⁻¹ :=
        Subtype.ext (by simpa using hab)
      have h2 : π ⟨(b : G), hAC b.2⟩ = π n₁ * π ⟨(a : G), hAC a.2⟩ * (π n₁)⁻¹ := by
        rw [hbC, map_mul, map_mul, map_inv]
      have h3 : π n₁ = (n' : C ⧸ O) := by rw [hn₁π, hn]
      change ((φ b : ↥(r1sBar x J)) : C ⧸ O) = ((n' * φ a * n'⁻¹ : ↥(r1sBar x J)) : C ⧸ O)
      rw [hφval, h2, h3]
      rfl

theorem r1s_inf_isElemAbelian {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJC : J ≤ centralizer ({x} : Set G))
    (hCJ : centralizer ({x} : Set G) ≤ normalizer (J : Set G))
    (hel : ∀ S : Sylow 3 ↥(r1sBar x J), IsElemAbelian 3 (S : Subgroup ↥(r1sBar x J))) :
    IsElemAbelian 3 ((P : Subgroup G) ⊓ J) := by
  obtain ⟨S, φ, hinj, hφS, -, -⟩ := r1s_normalizer_data hgen hJC hCJ
  obtain ⟨hcomm, hexp⟩ := hel S
  refine ⟨⟨⟨fun a b => hinj ?_⟩⟩, fun a ha => ?_⟩
  · have h := congrArg Subtype.val
      (hcomm.is_comm.comm (⟨φ a, hφS a⟩ : ↥(S : Subgroup ↥(r1sBar x J))) ⟨φ b, hφS b⟩)
    rw [map_mul, map_mul]
    exact h
  · have h := hexp (φ ⟨a, ha⟩) (hφS _)
    have h1 : φ (⟨a, ha⟩ ^ 3) = φ 1 := by rw [map_pow, h, map_one]
    exact congrArg Subtype.val (hinj h1)

theorem a6_exists_inverting (hK : KFactA6SylowAction) {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J) :
    ∃ n ∈ centralizer ({x} : Set G),
      n ∈ normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ∧
      ∀ a ∈ (P : Subgroup G) ⊓ J, n * a * n⁻¹ = a⁻¹ := by
  obtain ⟨S, φ, hinj, hφS, -, hlift⟩ :=
    r1s_normalizer_data hgen hJ.le_centralizer hJ.centralizer_le
  obtain ⟨⟨n', hn'N, hn'inv⟩, -⟩ := hK _ (r1sBar_isA6 hJ) S
  obtain ⟨n, hnC, hnN, hnact⟩ := hlift n' hn'N
  refine ⟨n, hnC, hnN, fun a ha => ?_⟩
  have hna : n * a * n⁻¹ ∈ (P : Subgroup G) ⊓ J := (mem_normalizer_iff.mp hnN a).mp ha
  have h1 := hnact ⟨a, ha⟩ ⟨_, hna⟩ rfl
  have h2 : φ ⟨_, hna⟩ = φ ⟨a⁻¹, inv_mem ha⟩ := by
    rw [h1, hn'inv _ (hφS _)]
    exact (map_inv φ ⟨a, ha⟩).symm
  exact congrArg Subtype.val (hinj h2)

theorem a6_exists_moving (hK : KFactA6SylowAction) {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J)
    {a : G} (ha : a ∈ (P : Subgroup G) ⊓ J) (ha1 : a ≠ 1) :
    ∃ n ∈ centralizer ({x} : Set G),
      n ∈ normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ∧
      n * a * n⁻¹ ∉ zpowers a := by
  obtain ⟨S, φ, hinj, hφS, -, hlift⟩ :=
    r1s_normalizer_data hgen hJ.le_centralizer hJ.centralizer_le
  have hφa1 : φ ⟨a, ha⟩ ≠ 1 := fun h => ha1 (congrArg Subtype.val (hinj (h.trans (map_one φ).symm)))
  obtain ⟨n', hn'N, hn'mv⟩ := (hK _ (r1sBar_isA6 hJ) S).2 _ (hφS ⟨a, ha⟩) hφa1
  obtain ⟨n, hnC, hnN, hnact⟩ := hlift n' hn'N
  refine ⟨n, hnC, hnN, fun hmem => hn'mv ?_⟩
  have hna : n * a * n⁻¹ ∈ (P : Subgroup G) ⊓ J := (mem_normalizer_iff.mp hnN a).mp ha
  have h1 := hnact ⟨a, ha⟩ ⟨_, hna⟩ rfl
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
  have h2 : (⟨_, hna⟩ : ↥((P : Subgroup G) ⊓ J)) = ⟨a, ha⟩ ^ j :=
    Subtype.ext (by simpa using hj.symm)
  rw [← h1, h2, map_zpow]
  exact zpow_mem_zpowers _ _

theorem a6_inf_isElemAbelian (hK : A6SylowData) {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J) :
    IsElemAbelian 3 ((P : Subgroup G) ⊓ J) :=
  r1s_inf_isElemAbelian hgen hJ.le_centralizer hJ.centralizer_le fun S =>
    (hK _ (r1sBar_isA6 hJ) S).1

theorem u3_exists_inverting (hK : KFactU3SylowInversion) {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsU3Normal M x J) :
    ∃ n ∈ centralizer ({x} : Set G),
      n ∈ normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ∧
      ∀ z ∈ (center ↥((P : Subgroup G) ⊓ J)).map ((P : Subgroup G) ⊓ J).subtype,
        n * z * n⁻¹ = z⁻¹ := by
  obtain ⟨S, φ, hinj, hφS, hSφ, hlift⟩ :=
    r1s_normalizer_data hgen hJ.le_centralizer hJ.centralizer_le
  obtain ⟨n', hn'N, hn'inv⟩ := hK _ (r1sBar_isU3 hJ) S
  obtain ⟨n, hnC, hnN, hnact⟩ := hlift n' hn'N
  refine ⟨n, hnC, hnN, fun z hz => ?_⟩
  obtain ⟨z', hz'c, rfl⟩ := hz
  have hz'A : (z' : G) ∈ (P : Subgroup G) ⊓ J := z'.2
  have hna : n * (z' : G) * n⁻¹ ∈ (P : Subgroup G) ⊓ J := (mem_normalizer_iff.mp hnN _).mp hz'A
  have h1 := hnact z' ⟨_, hna⟩ rfl
  have hcent : (⟨φ z', hφS z'⟩ : ↥(S : Subgroup ↥(r1sBar x J))) ∈
      center ↥(S : Subgroup ↥(r1sBar x J)) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨s, hs⟩
    obtain ⟨b, rfl⟩ := hSφ s hs
    refine Subtype.ext ?_
    show φ b * φ z' = φ z' * φ b
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz'c b]
  have hmem : φ z' ∈ (center ↥(S : Subgroup ↥(r1sBar x J))).map
      (S : Subgroup ↥(r1sBar x J)).subtype := ⟨⟨φ z', hφS z'⟩, hcent, rfl⟩
  have h2 : φ ⟨_, hna⟩ = φ z'⁻¹ := by
    rw [h1, hn'inv _ hmem, map_inv]
  exact congrArg Subtype.val (hinj h2)

end CFSG.LocalAnalysis.RankThreeTheoremC
