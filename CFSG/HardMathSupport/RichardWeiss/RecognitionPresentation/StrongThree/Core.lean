module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Coprime
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Normal

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open Subgroup

variable {X : Type*} [Group X] [Finite X]

structure CoreFree (M E : Subgroup X) : Prop where
  strong : GLBStronglyEmbedded 3 M
  core : M.normalCore = ⊥
  le : E ≤ M
  elem : IsElemAbelian 3 E
  card : 9 ≤ Nat.card E

namespace CoreFree

variable {M E : Subgroup X}

omit [Finite X] in
theorem not_le_of_normal (D : CoreFree M E) {K : Subgroup X} [K.Normal] (hK0 : K ≠ ⊥) :
    ¬ K ≤ M := fun h =>
  hK0 (le_bot_iff.mp (D.core ▸ Subgroup.normal_le_normalCore.mpr h))

theorem three_dvd_of_normal (D : CoreFree M E) {K : Subgroup X} [K.Normal] (hK0 : K ≠ ⊥) :
    3 ∣ Nat.card K := by
  by_contra h
  exact hK0 (normal_eq_bot_of_not_dvd D.strong D.core D.le D.elem D.card h)

theorem isSimpleGroup_of_minimal (D : CoreFree M E) {K : Subgroup X} [hKn : K.Normal]
    (hK0 : K ≠ ⊥) (hKmin : ∀ L : Subgroup X, L.Normal → L ≤ K → L = ⊥ ∨ L = K)
    {P : Sylow 3 X} (hPM : (P : Subgroup X) ≤ M) : IsSimpleGroup ↥K := by
  have h3K : 3 ∣ Nat.card K := D.three_dvd_of_normal hK0
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK0
  obtain ⟨S, hSn, hS0, hSmin⟩ := exists_minimal_normal (G := ↥K)
  let σ : X →* MulAut ↥K := MulAut.conjNormal
  let T : X → Subgroup ↥K := fun x => S.map (σ x).toMonoidHom
  have hTn : ∀ x, (T x).Normal := fun x => hSn.map (σ x).toMonoidHom (σ x).surjective
  have hT0 : ∀ x, T x ≠ ⊥ := fun x h =>
    hS0 ((Subgroup.map_eq_bot_iff_of_injective S (σ x).injective).mp h)
  have hTcard : ∀ x, Nat.card (T x) = Nat.card S := fun x =>
    Subgroup.card_map_of_injective (σ x).injective
  have hT1 : T 1 = S := by
    ext k; simp [T, σ, Subgroup.mem_map]
  have hTmul : ∀ g x, T (g * x) = (T x).map (σ g).toMonoidHom := by
    intro g x
    ext k
    simp only [T, Subgroup.mem_map, map_mul]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(σ x) s, ⟨s, hs, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, hs, rfl⟩
  have hTmin : ∀ x, ∀ L : Subgroup ↥K, L.Normal → L ≤ T x → L = ⊥ ∨ L = T x := by
    intro x L hL hLT
    have hc : (L.comap (σ x).toMonoidHom).Normal := hL.comap _
    have hcS : L.comap (σ x).toMonoidHom ≤ S := by
      intro y hy
      obtain ⟨s, hs, hsy⟩ := hLT hy
      have : s = y := (σ x).injective hsy
      exact this ▸ hs
    rcases hSmin _ hc hcS with h | h
    · left
      refine eq_bot_iff.mpr fun l hl => ?_
      obtain ⟨y, rfl⟩ := (σ x).surjective l
      have : y ∈ L.comap (σ x).toMonoidHom := hl
      rw [h] at this
      have hy : y = 1 := this
      simp [hy]
    · right
      refine le_antisymm hLT fun l hl => ?_
      obtain ⟨s, hs, rfl⟩ := hl
      have : s ∈ L.comap (σ x).toMonoidHom := h ▸ hs
      exact this
  have hcomm : ∀ x z, T x ≠ T z → ∀ u ∈ T x, ∀ v ∈ T z, u * v = v * u := by
    intro x z hxz u hu v hv
    have := hTn x
    have := hTn z
    have hdisj : Disjoint (T x) (T z) := by
      rw [disjoint_iff]
      rcases hTmin x (T x ⊓ T z) inferInstance inf_le_left with h | h
      · exact h
      · exfalso
        have hle : T x ≤ T z := h ▸ inf_le_right
        rcases hTmin z (T x) (hTn x) hle with h' | h'
        · exact hT0 x h'
        · exact hxz h'
    exact Subgroup.commute_of_normal_of_disjoint (T x) (T z) (hTn x) (hTn z) hdisj u v hu hv
  set U : Subgroup ↥K := ⨆ x, T x with hU
  have hUinv : ∀ g, U.map (σ g).toMonoidHom ≤ U := by
    intro g
    rw [hU, Subgroup.map_iSup]
    exact iSup_le fun x => by rw [← hTmul]; exact le_iSup T (g * x)
  have hUtop : U = ⊤ := by
    have hnorm : (U.map K.subtype).Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨u, hu, rfl⟩ := hn
      exact ⟨σ g u, hUinv g ⟨u, hu, rfl⟩, by simp [σ, MulAut.conjNormal_apply]⟩
    have hne : U.map K.subtype ≠ ⊥ := by
      intro h
      have : U = ⊥ := (Subgroup.map_eq_bot_iff_of_injective U K.subtype_injective).mp h
      exact hT0 1 (le_bot_iff.mp (this ▸ le_iSup T 1))
    rcases hKmin _ hnorm (Subgroup.map_subtype_le U) with h | h
    · exact absurd h hne
    · refine eq_top_iff.mpr fun k _ => ?_
      have : (k : X) ∈ U.map K.subtype := by rw [h]; exact k.2
      obtain ⟨u, hu, hu'⟩ := this
      exact (Subtype.ext hu' : u = k) ▸ hu
  have h3S : 3 ∣ Nat.card S := by
    by_contra h3
    have hT3 : ∀ x, ¬ 3 ∣ Nat.card (T x) := fun x => by rw [hTcard x]; exact h3
    have : ∀ x, (T x).Normal := hTn
    have h' := not_dvd_card_iSup_of_normal T hT3
    rw [← hU, hUtop, Subgroup.card_top] at h'
    exact h' h3K
  set S' : Subgroup X := S.map K.subtype with hS'
  have h3S' : 3 ∣ Nat.card S' := by
    rw [hS', Subgroup.card_map_of_injective K.subtype_injective]; exact h3S
  obtain ⟨y, a, haP, haS, ha3⟩ := exists_conj_orderThree_mem h3S' P
  have haM : a ∈ M := hPM haP
  have hay : ∃ a' ∈ T y, (a' : X) = a := by
    obtain ⟨b, ⟨s, hs, rfl⟩, rfl⟩ := haS
    exact ⟨σ y s, ⟨s, hs, rfl⟩, by simp [σ, MulAut.conjNormal_apply]⟩
  by_cases hall : ∀ x, T x = T y
  ·
    have hSeq : ∀ g, T g = S := fun g => (hall g).trans ((hall 1).symm.trans hT1)
    have hnorm : S'.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨s, hs, rfl⟩ := hn
      have : σ g s ∈ S := by rw [← hSeq g]; exact ⟨s, hs, rfl⟩
      exact ⟨σ g s, this, by simp [σ, MulAut.conjNormal_apply]⟩
    have hS'0 : S' ≠ ⊥ := fun h =>
      hS0 ((Subgroup.map_eq_bot_iff_of_injective S K.subtype_injective).mp h)
    have hStop : S = ⊤ := by
      rcases hKmin S' hnorm (Subgroup.map_subtype_le S) with h | h
      · exact absurd h hS'0
      · refine eq_top_iff.mpr fun k _ => ?_
        have : (k : X) ∈ S' := by rw [h]; exact k.2
        obtain ⟨s, hs, hsk⟩ := this
        exact (Subtype.ext hsk : s = k) ▸ hs
    exact @IsSimpleGroup.mk _ _ inferInstance fun L hL => by
      rcases hSmin L hL (hStop ▸ le_top) with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans hStop)
  ·
    exfalso
    push Not at hall
    obtain ⟨x, hx⟩ := hall
    have hcentM : ∀ z, T z ≠ T y → (T z).map K.subtype ≤ M := by
      intro z hz w hw
      obtain ⟨w', hw', rfl⟩ := hw
      obtain ⟨a', ha', haeq⟩ := hay
      refine centralizer_le_of_orderThree D.strong haM ha3 ?_
      rw [Subgroup.mem_centralizer_singleton_iff, ← haeq]
      exact congrArg Subtype.val (hcomm z y hz w' hw' a' ha')
    obtain ⟨b, hbT, hb3⟩ : ∃ b ∈ (T x).map K.subtype, orderOf b = 3 := by
      have h3Tx : 3 ∣ Nat.card (T x) := by rw [hTcard x]; exact h3S
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T x) 3 h3Tx
      refine ⟨((t : ↥K) : X), ⟨t, t.2, rfl⟩, ?_⟩
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
    have hbM : b ∈ M := hcentM x hx hbT
    have hTyM : (T y).map K.subtype ≤ M := by
      intro w hw
      obtain ⟨w', hw', rfl⟩ := hw
      obtain ⟨t, ht, rfl⟩ := hbT
      refine centralizer_le_of_orderThree D.strong hbM hb3 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hcomm y x (Ne.symm hx) w' hw' t ht)
    have hallM : ∀ z, (T z).map K.subtype ≤ M := fun z => by
      by_cases hz : T z = T y
      · rw [hz]; exact hTyM
      · exact hcentM z hz
    have hKM : K ≤ M := by
      intro k hk
      have hk' : (⟨k, hk⟩ : ↥K) ∈ U := hUtop ▸ Subgroup.mem_top _
      have hUle : U ≤ M.comap K.subtype :=
        iSup_le fun z => (Subgroup.map_le_iff_le_comap).mp (hallM z)
      exact hUle hk'
    exact D.not_le_of_normal hK0 hKM

theorem nonabelian_of_simple (D : CoreFree M E) {K : Subgroup X} [K.Normal] (hK0 : K ≠ ⊥)
    (hsimple : IsSimpleGroup ↥K) : ∃ a b : ↥K, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have h3K := D.three_dvd_of_normal hK0
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3K
  have hnorm : (Subgroup.zpowers s).Normal :=
    ⟨fun n hn g => by rwa [mul_inv_eq_iff_eq_mul.mpr (hcomm g n)]⟩
  have := hnorm
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers s) with h | h
  · have : s = 1 := by
      have : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
      rw [h] at this
      exact this
    rw [this, orderOf_one] at hs
    omega
  · have hcard : Nat.card K = 3 := by
      rw [← hs, ← Nat.card_zpowers, h, Subgroup.card_top]
    have hp : IsPGroup 3 ↥K := IsPGroup.of_card (n := 1) (by simpa using hcard)
    exact hK0 (normal_eq_bot_of_isPGroup D.strong D.core hp)

theorem centralizer_eq_bot (D : CoreFree M E) {K : Subgroup X} [hKn : K.Normal] (hK0 : K ≠ ⊥)
    {P : Sylow 3 X} (hPM : (P : Subgroup X) ≤ M) : Subgroup.centralizer (K : Set X) = ⊥ := by
  obtain ⟨y, a, haP, haK, ha3⟩ := exists_conj_orderThree_mem (D.three_dvd_of_normal hK0) P
  have haK' : a ∈ K := by
    obtain ⟨k, hk, rfl⟩ := haK
    exact hKn.conj_mem k hk y
  have hC : Subgroup.centralizer (K : Set X) ≤ M := fun c hc =>
    centralizer_le_of_orderThree D.strong (hPM haP) ha3
      (by rw [Subgroup.mem_centralizer_singleton_iff]; exact (Subgroup.mem_centralizer_iff.mp hc a haK').symm)
  exact le_bot_iff.mp (D.core ▸ Subgroup.normal_le_normalCore.mpr hC)

theorem exists_simple_normal (D : CoreFree M E) :
    ∃ K : Subgroup X, K.Normal ∧ IsSimpleGroup ↥K ∧ (∃ a b : ↥K, a * b ≠ b * a) ∧
      Subgroup.centralizer (K : Set X) = ⊥ := by
  obtain ⟨g, hg⟩ : ∃ g : X, g ∉ M := by
    by_contra hall
    exact D.strong.1 (eq_top_iff.mpr fun x _ => by_contra fun hx => hall ⟨x, hx⟩)
  have : Nontrivial X := ⟨⟨g, 1, fun h => hg (h ▸ M.one_mem)⟩⟩
  obtain ⟨K, hKn, hK0, hKmin⟩ := exists_minimal_normal (G := X)
  obtain ⟨P, hPM⟩ := exists_sylow_le D.strong
  have hsimple := D.isSimpleGroup_of_minimal hK0 hKmin hPM
  exact ⟨K, hKn, hsimple, D.nonabelian_of_simple hK0 hsimple, D.centralizer_eq_bot hK0 hPM⟩

end CoreFree

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
