module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternPartner
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Pair
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Shared
public import CFSG.ClassicalInvolution.RouteD.AllA1
public import CFSG.ClassicalInvolution.Asc77.TwinLookup
public import CFSG.ClassicalInvolution.SmallCases.TwinChainDefs

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Centralizer

theorem mem_centralizer_mul {z w k : G} (hz : k ∈ Subgroup.centralizer ({z} : Set G))
    (hw : k ∈ Subgroup.centralizer ({w} : Set G)) :
    k ∈ Subgroup.centralizer ({z * w} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hz hw ⊢
  calc k * (z * w) = (k * z) * w := by rw [mul_assoc]
    _ = (z * k) * w := by rw [hz]
    _ = z * (k * w) := by rw [mul_assoc]
    _ = z * (w * k) := by rw [hw]
    _ = z * w * k := by rw [mul_assoc]

theorem mem_centralizer_left_of_mul {z w k : G}
    (hzw : k ∈ Subgroup.centralizer ({z * w} : Set G))
    (hw : k ∈ Subgroup.centralizer ({w} : Set G)) :
    k ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hzw hw ⊢
  apply mul_right_cancel (b := w)
  calc k * z * w = k * (z * w) := by rw [mul_assoc]
    _ = z * w * k := hzw
    _ = z * (w * k) := by rw [mul_assoc]
    _ = z * (k * w) := by rw [hw]
    _ = z * k * w := by rw [mul_assoc]

theorem mem_centralizer_right_of_mul {z w k : G}
    (hzw : k ∈ Subgroup.centralizer ({z * w} : Set G))
    (hz : k ∈ Subgroup.centralizer ({z} : Set G)) :
    k ∈ Subgroup.centralizer ({w} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hzw hz ⊢
  apply mul_left_cancel (a := z)
  calc z * (k * w) = (z * k) * w := by rw [mul_assoc]
    _ = (k * z) * w := by rw [hz]
    _ = k * (z * w) := by rw [mul_assoc]
    _ = z * w * k := hzw
    _ = z * (w * k) := by rw [mul_assoc]

end Centralizer

section Lookup

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem tag_rank_of_twinFamily_at (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {j : Fin D.card}
    (hDj : D.tag j ≠ .G2 ∧ D.tag j ≠ .trialityD4) (hnA1 : ¬ (D.tag j = .PSL ∧ D.rank j = 2))
    {a : ℕ} (ha : 3 ≤ a) (T : Fin a → Subgroup G)
    (hTx : ∀ k, T k ∈ centralizingMembers Ω {x}) (hTj : ∀ k, locImg Ω x (T k) ≤ (D.hom j).range)
    (hinj : Function.Injective T) (hcomm : ∀ k l, k ≠ l → Commutes (T k) (T l))
    (htwin : ∀ N ∈ centralizingMembers Ω {x}, ∀ k l,
      (N = T k ∨ Commutes N (T k)) ↔ (N = T l ∨ Commutes N (T l))) :
    D.tag j = .POmegaPlus ∧ D.rank j = 4 := by
  have hq4 : 4 ≤ p ^ f := by omega
  have hexp : D.exp j = f := by
    rcases D.exp_eq j with h | ⟨h, -⟩
    · exact h
    · exact absurd h hDj.2
  have hsc := fundamentalSingleClass_of_ne D j hDj.1 hDj.2
  have hperf := fundPerfect_modelUniv hp2 (D.isFundTag j) (D.admissible j)
    (by rw [hexp]; exact hq4)
  obtain ⟨F, hF, hFinj, hFcomm, hFtwin⟩ :=
    Asc77.modelTwinClass_of_layer_family hΩ hex hP1 D (j := j) hsc hperf T hTx hTj hinj
      hcomm htwin
  have hmtc : ModelTwinClass p (D.tag j) (D.rank j) (D.exp j) a :=
    ⟨F, hF, hFinj, hFcomm, fun k l S hS => hFtwin k l S hS⟩
  have hmtc' := modelTwinClass_congr (p := p) rfl rfl hexp hmtc
  have hadm : StatedLieAdmissible (D.tag j) (D.rank j) p f := by
    have := D.admissible j
    rwa [hexp] at this
  rcases mfTwin (p := p) (f := f) hp2 hq (D.tag j) (D.rank j) a (D.isFundTag j) hDj.1 hDj.2
      hadm hnA1 (by omega) hmtc' with h | h
  · exact absurd (Asc77.ShapeTable.le_two h) (by omega)
  · exact ⟨h.1, h.2.1⟩

end Lookup

section Chain

variable [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem isClassicalMember_mul_self {N : Subgroup G} {y : G} (h : IsClassicalMember p f N y) :
    y * y = 1 := by
  have h2 : y ^ 2 = 1 := by rw [← h.orderOf_eq_two]; exact pow_orderOf_eq_one y
  simpa [pow_two] using h2

theorem exists_d4_component_of_twin_product (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hcen : Subgroup.center G = ⊥) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hIH : LocalLieSystems p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) {T₁ : Subgroup G} (hT₁ : T₁ ∈ centralizingMembers Ω {z})
    (hT₁K : T₁ ≠ K) (hT₁comm : ∀ N ∈ centralizingMembers Ω {z}, N ≠ T₁ → Commutes T₁ N)
    {K₂ : Subgroup G} (hK₂ : K₂ ∈ centralizingMembers Ω {z}) (hK₂K : K₂ ≠ K) (hK₂T : K₂ ≠ T₁)
    {w : G} (hw : IsClassicalMember p f K₂ w) (hzw : z ≠ w) (hP1x : LocalOddCentral Ω {z * w})
    (hlink : LinkedAtProduct Ω K z w) :
    ∃ (D : LieSystemData p f (locQuot Ω (z * w)) (locFamily Ω (z * w))) (c : Fin D.card),
      D.tag c = .POmegaPlus ∧ D.rank c = 4 ∧ D.exp c = f ∧ Commutes K K₂ ∧
      K ∈ compMembers Ω (z * w) D c ∧ K₂ ∈ compMembers Ω (z * w) D c ∧
      T₁ ∈ compMembers Ω (z * w) D c ∧
      ∀ N ∈ centralizingMembers Ω {z * w}, N ≠ K → ¬ Commutes K N →
        N ∈ compMembers Ω (z * w) D c := by
  classical
  have hf : 0 < f := pos_of_five_le hq
  have hq4 : 4 ≤ p ^ f := by omega
  have hMFZ := Gaps.fundNoncentral p
  have hzc : ¬ ({z} : Set G) ⊆ Subgroup.center G := by
    intro h
    have h1 : z ∈ Subgroup.center G := h rfl
    rw [hcen, Subgroup.mem_bot] at h1
    have := hz.orderOf_eq_two
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨Dz⟩ := exists_lieSystemData hIH hzc
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hK₂w : K₂ ∈ centralizingMembers Ω {w} := ⟨hK₂.1, le_centralizer_of_isClassicalMember hw⟩
  have cpz : ∀ {L : Subgroup G}, L ∈ centralizingMembers Ω {z} → Commutes K L ∨ L = K :=
    fun hL => commutes_or_eq_at_member_involution hMFZ hΩ hex hp2 hsingle hz hP1 Dz hK hz hKz hL
  have cpw : ∀ {L : Subgroup G}, L ∈ centralizingMembers Ω {w} → Commutes K₂ L ∨ L = K₂ :=
    fun hL => commutes_or_eq_at_member_involution hMFZ hΩ hex hp2 hsingle hz hP1 Dz hK₂.1 hw
      hK₂w hL
  have hKK₂ : Commutes K K₂ := (cpz hK₂).resolve_right hK₂K
  obtain ⟨t₁, ht₁⟩ := hΩ.classical T₁ hT₁.1
  have hΩt : centralizingMembers Ω {t₁} = centralizingMembers Ω {z} :=
    centralizingMembers_eq_of_twin hp2 hf hΩ hz ht₁ (hsingle T₁ hT₁.1) hT₁ hT₁comm
  have hx_nc : ¬ ({z * w} : Set G) ⊆ Subgroup.center G := by
    intro h
    have h1 : z * w ∈ Subgroup.center G := h rfl
    rw [hcen, Subgroup.mem_bot] at h1
    apply hzw
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_eq_of_mul_eq_one_right (isClassicalMember_mul_self hw)
  obtain ⟨D⟩ := exists_lieSystemData hIH hx_nc
  have hcent_x : ∀ {N : Subgroup G}, N ∈ Ω → N ≤ Subgroup.centralizer ({z} : Set G) →
      N ≤ Subgroup.centralizer ({w} : Set G) → N ∈ centralizingMembers Ω {z * w} :=
    fun hN h1 h2 => ⟨hN, fun n hn => mem_centralizer_mul (h1 hn) (h2 hn)⟩
  have hKx : K ∈ centralizingMembers Ω {z * w} :=
    hcent_x hK (le_centralizer_of_isClassicalMember hz) (le_centralizer_of_commutes hKK₂ hw.mem)
  have hK₂x : K₂ ∈ centralizingMembers Ω {z * w} :=
    hcent_x hK₂.1 hK₂.2 (le_centralizer_of_isClassicalMember hw)
  have hT₁x : T₁ ∈ centralizingMembers Ω {z * w} :=
    hcent_x hT₁.1 hT₁.2 (le_centralizer_of_commutes (hT₁comm K₂ hK₂ hK₂T) hw.mem)
  have hCzw : ∀ {N : Subgroup G}, N ∈ centralizingMembers Ω {z * w} →
      (N ≤ Subgroup.centralizer ({z} : Set G) ↔ N ≤ Subgroup.centralizer ({w} : Set G)) := by
    intro N hN
    exact ⟨fun h n hn => mem_centralizer_right_of_mul (hN.2 hn) (h hn),
      fun h n hn => mem_centralizer_left_of_mul (hN.2 hn) (h hn)⟩
  have hPK : ∀ {N : Subgroup G}, N ∈ centralizingMembers Ω {z * w} →
      ((N = K ∨ Commutes N K) ↔ N ≤ Subgroup.centralizer ({z} : Set G)) := by
    intro N hN
    constructor
    · rintro (rfl | h)
      · exact le_centralizer_of_isClassicalMember hz
      · exact le_centralizer_of_commutes h hz.mem
    · intro h
      rcases cpz ⟨hN.1, h⟩ with h' | h'
      · exact Or.inr (Commutes.symm h')
      · exact Or.inl h'
  have hPK₂ : ∀ {N : Subgroup G}, N ∈ centralizingMembers Ω {z * w} →
      ((N = K₂ ∨ Commutes N K₂) ↔ N ≤ Subgroup.centralizer ({w} : Set G)) := by
    intro N hN
    constructor
    · rintro (rfl | h)
      · exact le_centralizer_of_isClassicalMember hw
      · exact le_centralizer_of_commutes h hw.mem
    · intro h
      rcases cpw ⟨hN.1, h⟩ with h' | h'
      · exact Or.inr (Commutes.symm h')
      · exact Or.inl h'
  have hPT : ∀ {N : Subgroup G}, N ∈ centralizingMembers Ω {z * w} →
      ((N = T₁ ∨ Commutes N T₁) ↔ N ≤ Subgroup.centralizer ({z} : Set G)) := by
    intro N hN
    constructor
    · rintro (rfl | h)
      · exact hT₁.2
      · have hmem : N ∈ centralizingMembers Ω {t₁} :=
          ⟨hN.1, le_centralizer_of_commutes h ht₁.mem⟩
        rw [hΩt] at hmem
        exact hmem.2
    · intro h
      by_cases hNT : N = T₁
      · exact Or.inl hNT
      · exact Or.inr (Commutes.symm (hT₁comm N ⟨hN.1, h⟩ hNT))
  obtain ⟨N₀, hN₀x, hN₀K, hN₀nc⟩ := hlink
  have hN₀z : ¬ N₀ ≤ Subgroup.centralizer ({z} : Set G) := by
    intro h
    rcases (hPK hN₀x).mpr h with h' | h'
    · exact hN₀K h'
    · exact hN₀nc (Commutes.symm h')
  obtain ⟨i₀, hKi⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨K, hKx, rfl⟩)
  obtain ⟨j₀, hN₀j⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N₀, hN₀x, rfl⟩)
  have hij : i₀ = j₀ :=
    eq_of_not_commutes hΩ hP1x D (A := K) (B := N₀) ⟨hKx, hKi⟩ ⟨hN₀x, hN₀j⟩ hN₀nc
  subst hij
  obtain ⟨b, hKb⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨K₂, hK₂x, rfl⟩)
  have hb : b = i₀ := by
    by_contra hb
    have hc : Commutes N₀ K₂ :=
      commutes_of_ne_comp hΩ hP1x D (Ne.symm hb) ⟨hN₀x, hN₀j⟩ ⟨hK₂x, hKb⟩
    exact hN₀z ((hCzw hN₀x).mpr (le_centralizer_of_commutes hc hw.mem))
  subst hb
  obtain ⟨c, hTc⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨T₁, hT₁x, rfl⟩)
  have hc : c = b := by
    by_contra hc
    have hcm : Commutes N₀ T₁ :=
      commutes_of_ne_comp hΩ hP1x D (Ne.symm hc) ⟨hN₀x, hN₀j⟩ ⟨hT₁x, hTc⟩
    exact hN₀z ((hPT hN₀x).mp (Or.inr hcm))
  subst hc
  have hKc : K ∈ compMembers Ω (z * w) D c := ⟨hKx, hKi⟩
  have hK₂c : K₂ ∈ compMembers Ω (z * w) D c := ⟨hK₂x, hKb⟩
  have hnA1 : ¬ (D.tag c = .PSL ∧ D.rank c = 2) := by
    rintro ⟨ht, hr⟩
    have e1 : locImg Ω (z * w) K = (D.hom c).range :=
      Subgroup.eq_of_le_of_card_ge hKi (by
        rw [card_locImg hΩ hex hKx]
        exact card_range_le_of_psl_two D c ht hr)
    have e2 : locImg Ω (z * w) N₀ = (D.hom c).range :=
      Subgroup.eq_of_le_of_card_ge hN₀j (by
        rw [card_locImg hΩ hex hN₀x]
        exact card_range_le_of_psl_two D c ht hr)
    exact hN₀K (locImg_injOn hΩ hP1x hN₀x hKx (e2.trans e1.symm))
  have hexc : D.tag c ≠ .G2 ∧ D.tag c ≠ .trialityD4 := by
    constructor
    · intro ht
      exact hzw (G2D4.eq_involution_of_commuting_pair (G2D4.g2d4SharedInvolution p) hp2 hΩ hP1x
        D (Or.inl ht) hKc hK₂c hz hw hKK₂)
    · intro ht
      exact hzw (G2D4.eq_involution_of_commuting_pair (G2D4.g2d4SharedInvolution p) hp2 hΩ hP1x
        D (Or.inr ht) hKc hK₂c hz hw hKK₂)
  have hTk : ∀ N ∈ centralizingMembers Ω {z * w}, ∀ k : Fin 3,
      (N = ![K, K₂, T₁] k ∨ Commutes N (![K, K₂, T₁] k)) ↔
        N ≤ Subgroup.centralizer ({z} : Set G) := by
    intro N hN k
    fin_cases k
    · exact hPK hN
    · exact (hPK₂ hN).trans (hCzw hN).symm
    · exact hPT hN
  have hTx : ∀ k : Fin 3, ![K, K₂, T₁] k ∈ centralizingMembers Ω {z * w} := by
    intro k
    fin_cases k
    · exact hKx
    · exact hK₂x
    · exact hT₁x
  have hTj : ∀ k : Fin 3, locImg Ω (z * w) (![K, K₂, T₁] k) ≤ (D.hom c).range := by
    intro k
    fin_cases k
    · exact hKi
    · exact hKb
    · exact hTc
  have hinj : Function.Injective ![K, K₂, T₁] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; simp_all)
  have hcomm : ∀ k l : Fin 3, k ≠ l → Commutes (![K, K₂, T₁] k) (![K, K₂, T₁] l) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    all_goals first
      | exact absurd rfl hkl
      | exact hKK₂
      | exact Commutes.symm hKK₂
      | exact Commutes.symm (hT₁comm K hKz hT₁K.symm)
      | exact hT₁comm K hKz hT₁K.symm
      | exact Commutes.symm (hT₁comm K₂ hK₂ hK₂T)
      | exact hT₁comm K₂ hK₂ hK₂T
  have hTW : D.tag c = .POmegaPlus ∧ D.rank c = 4 :=
    tag_rank_of_twinFamily_at hp2 hq hΩ hex hP1x D hexc hnA1 (a := 3) le_rfl ![K, K₂, T₁] hTx hTj
      hinj hcomm fun N hN k l => (hTk N hN k).trans (hTk N hN l).symm
  have hexp : D.exp c = f := by
    rcases D.exp_eq c with h | ⟨h, -⟩
    · exact h
    · exact absurd h hexc.2
  refine ⟨D, c, hTW.1, hTW.2, hexp, hKK₂, hKc, hK₂c, ⟨hT₁x, hTc⟩, ?_⟩
  intro N hN hNK hnc
  obtain ⟨j', hj'⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  have hcj : c = j' :=
    eq_of_not_commutes hΩ hP1x D (A := K) (B := N) ⟨hKx, hKi⟩ ⟨hN, hj'⟩ hnc
  subst hcj
  exact ⟨hN, hj'⟩

theorem exists_chain_of_twin_product (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hcen : Subgroup.center G = ⊥) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hIH : LocalLieSystems p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) {T₁ : Subgroup G} (hT₁ : T₁ ∈ centralizingMembers Ω {z})
    (hT₁K : T₁ ≠ K) (hT₁comm : ∀ N ∈ centralizingMembers Ω {z}, N ≠ T₁ → Commutes T₁ N)
    {K₂ : Subgroup G} (hK₂ : K₂ ∈ centralizingMembers Ω {z}) (hK₂K : K₂ ≠ K) (hK₂T : K₂ ≠ T₁)
    {w : G} (hw : IsClassicalMember p f K₂ w) (hzw : z ≠ w) (hP1x : LocalOddCentral Ω {z * w})
    (hlink : LinkedAtProduct Ω K z w) (hTwin : TwinPartnerFactTwin p f .POmegaPlus 4 f) :
    ∃ N ∈ centralizingMembers Ω {z * w},
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K N) ∧
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W N K₂ := by
  obtain ⟨D, c, htag, hrank, hexp, hKK₂, hKc, hK₂c, -, -⟩ :=
    exists_d4_component_of_twin_product hp2 hq hcen hΩ hex hIH hK hsingle hz hP1 hT₁ hT₁K
      hT₁comm hK₂ hK₂K hK₂T hw hzw hP1x hlink
  have h1 : D.tag c ≠ .G2 := by rw [htag]; decide
  have h2 : D.tag c ≠ .trialityD4 := by rw [htag]; decide
  have hsc := fundamentalSingleClass_of_ne D c h1 h2
  have hperf := fundPerfect_modelUniv hp2 (D.isFundTag c) (D.admissible c)
    (by rw [hexp]; omega)
  have hTwin' : TwinPartnerFactTwin p f (D.tag c) (D.rank c) (D.exp c) := by
    rw [htag, hrank, hexp]
    exact hTwin
  obtain ⟨N, hN, pKN, pNM⟩ := exists_twin_partner_of_twin hq hΩ hex hP1x D hsc hperf hTwin' hKc
    hK₂c hK₂K.symm hKK₂ hz.mem hw.mem hz.orderOf_eq_two hw.orderOf_eq_two rfl
  exact ⟨N, hN.1, pKN, pNM⟩

end Chain

end CFSG.ClassicalInvolution.RouteD
