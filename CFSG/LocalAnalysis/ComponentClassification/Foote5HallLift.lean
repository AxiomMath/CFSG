module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallWeak

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

omit [Finite G] in
theorem exists_orderOf_eq_of_isPGroup {T : Subgroup G} (hT : IsPGroup 2 T) {s : G} (hs : s ∈ T)
    (hs2 : s * s ≠ 1) : ∃ j : ℕ, orderOf s = 2 ^ (j + 2) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨s, hs⟩
  rw [Subgroup.orderOf_mk] at hn
  rcases n with _ | _ | j
  · exfalso
    rw [pow_zero, orderOf_eq_one_iff] at hn
    exact hs2 (by rw [hn, mul_one])
  · exfalso
    apply hs2
    have h2 : orderOf s = 2 := by simpa using hn
    rw [← sq, ← h2]
    exact pow_orderOf_eq_one s
  · exact ⟨j, hn⟩

theorem card_le_of_isSylowOf_top {X : Type} [Group X] [Finite X] {P Q : Subgroup X}
    (hP : IsSylowOf 2 P ⊤) (hQ : IsPGroup 2 Q) : Nat.card Q ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := FooteLit.exists_conj_le_of_isSylowOf hP le_top hQ
  have hle : Q.map (MulAut.conj k⁻¹).toMonoidHom ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hk x hx
  have := card_le_of_le hle
  rwa [card_map_of_injective (MulAut.conj k⁻¹).injective] at this

omit [Finite G] in
theorem mem_normalizer_of_subgroupOf {H : Subgroup G} (hDH : D ≤ H) {x : H}
    (hx : x ∈ normalizer ((D.subgroupOf H : Subgroup H) : Set H)) :
    (x : G) ∈ normalizer (D : Set G) := by
  rw [mem_normalizer_iff] at hx ⊢
  intro y
  constructor
  · intro hy
    have h := (hx ⟨y, hDH hy⟩).mp (mem_subgroupOf.mpr hy)
    rw [mem_subgroupOf] at h
    simpa using h
  · intro hy
    have hyH : y ∈ H := by
      have h : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x := by group
      rw [h]
      exact mul_mem (mul_mem (inv_mem x.2) (hDH hy)) x.2
    have h := (hx ⟨y, hyH⟩).mpr (mem_subgroupOf.mpr (by simpa using hy))
    exact mem_subgroupOf.mp h

variable (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹))

omit [Finite G] in
include hD in
theorem data_subgroupOf {H : Subgroup G} (hDH : D ≤ H) (hcD : c ∈ D) :
    ∀ x ∈ D.subgroupOf H, x ∈ zpowers (⟨c, hDH hcD⟩ : H) ∨
      (x * x = 1 ∧ x * ⟨c, hDH hcD⟩ * x⁻¹ = (⟨c, hDH hcD⟩ : H)⁻¹) := by
  intro x hx
  rcases hD x (mem_subgroupOf.mp hx) with h | ⟨h1, h2⟩
  · left
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h
    exact mem_zpowers_iff.mpr ⟨i, Subtype.ext (by simpa using hi)⟩
  · right
    exact ⟨Subtype.ext (by simpa using h1), Subtype.ext (by simpa using h2)⟩

variable (hk : 4 ∣ orderOf c) (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
    ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)

omit [Finite G] in
include hcl in
theorem sic_subgroupOf {H : Subgroup G} (hDH : D ≤ H) :
    ∀ x ∈ normalizer ((D.subgroupOf H : Subgroup H) : Set H), x ∉ D.subgroupOf H →
      orderOf x = 2 → ∀ d ∈ D.subgroupOf H, orderOf d = 2 → ∀ g : H, g⁻¹ * x * g ≠ d := by
  intro x hx hxD hx2 d hd hd2 g hg
  refine hcl (x : G) (mem_normalizer_of_subgroupOf hDH hx) (fun h => hxD (mem_subgroupOf.mpr h))
    (by rwa [Subgroup.orderOf_coe]) (d : G) (mem_subgroupOf.mp hd) (by rwa [Subgroup.orderOf_coe])
    g ?_
  rw [← hg]
  simp

include hD hk hcl

theorem stronglyClosed_of_centralizer (hcard : Nat.card D = 2 * orderOf c) (hcD : c ∈ D)
    {T S₀ : Subgroup G} (hT2 : IsPGroup 2 T) (hDS : D ≤ S₀) (hST : S₀ ≤ T)
    (hinv : ∀ x ∈ S₀, x * x = 1 → x ∈ D)
    (hsc : ∀ s ∈ S₀, ∀ g ∈ centralizer ({cz c} : Set G), g⁻¹ * s * g ∈ T → g⁻¹ * s * g ∈ S₀) :
    Open.fusionStronglyClosed (S₀ : Set G) T := by
  have hTN := le_normalizer_of_sic hD hcl hcard hT2 (hDS.trans hST)
  intro s hs g hg
  by_cases hs2 : s * s = 1
  · exact hDS (HallD8.conj_mem_of_sic hcl (hinv s hs hs2) hs2 (hTN hg))
  · obtain ⟨j, hj⟩ := exists_orderOf_eq_of_isPGroup hT2 (hST hs) hs2
    set w := s ^ (2 ^ j) with hw
    have hw2 : s ^ (2 ^ (j + 1)) = w * w := by rw [hw, ← pow_add, ← two_mul, ← pow_succ']
    have hinvol : (w * w) * (w * w) = 1 := by
      rw [← hw2, ← pow_add, ← two_mul, ← pow_succ', ← hj, pow_orderOf_eq_one]
    have hwwD : w * w ∈ D := hinv _ (by rw [← hw2]; exact pow_mem hs _) hinvol
    have hwN : w ∈ normalizer (D : Set G) := hTN (hST (pow_mem hs _))
    have hwwC := sq_mem_zpowers hD hk hwN hcD hwwD
    have hpz : s ^ (2 ^ (j + 1)) = cz c := by
      rcases eq_one_or_eq_cz hk hwwC hinvol with h | h
      · exfalso
        rw [← hw2] at h
        exact pow_ne_one_of_lt_orderOf (by positivity)
          (by rw [hj]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)) h
      · rw [hw2, h]
    exact hsc s hs g (mem_centralizer_of_pow hD hk hcl hcD hTN hpz hg) hg

theorem weak_of_subgroup (hcard : Nat.card D = 2 * orderOf c) (hcD : c ∈ D)
    (hD2 : IsPGroup 2 D) {H : Subgroup G} (hzH : centralizer ({cz c} : Set G) ≤ H)
    (hW : HallWeakConclusion (D.subgroupOf H)) : HallWeakConclusion D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDH : D ≤ H := fun d hd =>
    hzH (mem_centralizer_singleton_iff.mpr (comm_cz hD hk hd))
  obtain ⟨S, T', hT', hDS, hST, hsc, hinv, hcardS⟩ := hW
  obtain ⟨T, hT, hDT⟩ := FooteLit.exists_isSylowOf_ge_of_le (le_top : D ≤ ⊤) hD2
  have hTN := le_normalizer_of_sic hD hcl hcard hT.isPGroup hDT
  have hTH : T ≤ H := fun t ht => hzH (by
    rw [mem_centralizer_singleton_iff]
    have h := conj_cz hD hk (hTN ht) hcD
    calc t * cz c = t * cz c * t⁻¹ * t := by group
      _ = cz c * t := by rw [h])
  set S₀ := S.map H.subtype with hS₀
  set T₀ := T'.map H.subtype with hT₀
  have hT₀2 : IsPGroup 2 T₀ := hT'.isPGroup.map _
  have hDS₀ : D ≤ S₀ := fun d hd => ⟨⟨d, hDH hd⟩, hDS (mem_subgroupOf.mpr hd), rfl⟩
  have hS₀T₀ : S₀ ≤ T₀ := map_mono hST
  have hinv₀ : ∀ x ∈ S₀, x * x = 1 → x ∈ D := by
    rintro _ ⟨x, hx, rfl⟩ hx2
    exact mem_subgroupOf.mp (hinv x hx (Subtype.ext (by simpa using hx2)))
  refine ⟨S₀, T₀, ?_, hDS₀, hS₀T₀, ?_, hinv₀, ?_⟩
  · have h1 : Nat.card T₀ = Nat.card T' := card_map_of_injective H.subtype_injective
    have h2 : Nat.card T ≤ Nat.card T' := by
      have h := card_le_of_isSylowOf_top hT' (Q := T.subgroupOf H) hT.isPGroup.comap_subtype
      rwa [Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv] at h
    have h3 : Nat.card T₀ ≤ Nat.card T := card_le_of_isSylowOf_top hT hT₀2
    apply isSylowOf_of_card le_top
    rw [← hT.card_eq]
    omega
  · refine stronglyClosed_of_centralizer hD hk hcl hcard hcD hT₀2 hDS₀ hS₀T₀ hinv₀ ?_
    rintro _ ⟨s, hs, rfl⟩ g hg hgT
    have hgH := hzH hg
    have hmem : (⟨g, hgH⟩ : H)⁻¹ * s * ⟨g, hgH⟩ ∈ T' := by
      obtain ⟨t, ht, hts⟩ := hgT
      have h : t = (⟨g, hgH⟩ : H)⁻¹ * s * ⟨g, hgH⟩ := Subtype.ext (by simpa using hts)
      rw [← h]
      exact ht
    exact ⟨_, hsc s hs _ hmem, by simp⟩
  · rw [card_map_of_injective H.subtype_injective,
      ← Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv]
    exact hcardS

end CFSG.ComponentClassification.Foote5.HallGen
