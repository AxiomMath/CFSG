module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Lemmas

variable {X : Type*} [Group X] [Finite X]

theorem exists_commute_mem_inf_centralizer {p : ℕ} [Fact p.Prime] {R L : Subgroup X}
    (hR : IsPGroup p R) (hRL : R ≤ Subgroup.normalizer (L : Set X))
    (hne : R ⊓ Subgroup.centralizer (L : Set X) ≠ ⊥) :
    ∃ z ∈ R ⊓ Subgroup.centralizer (L : Set X), orderOf z = p ∧ ∀ v ∈ R, Commute v z := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have : ((Subgroup.centralizer (L : Set X)).subgroupOf R).Normal := by
    refine ⟨fun c hc v => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : (v : X)⁻¹ * x * (v : X) ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hRL v.2)) x).mp hx
    have hcx := hc _ hx'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc x * ((v : X) * c * (v : X)⁻¹) = v * ((v : X)⁻¹ * x * v * c) * (v : X)⁻¹ := by group
      _ = v * (c * ((v : X)⁻¹ * x * v)) * (v : X)⁻¹ := by rw [hcx]
      _ = (v : X) * c * (v : X)⁻¹ * x := by group
  have hCne : (Subgroup.centralizer (L : Set X)).subgroupOf R ≠ ⊥ := by
    intro hbot
    apply hne
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype, hbot, Subgroup.map_bot]
  obtain ⟨c, hcT, hc, -⟩ := exists_mem_centralizer_orderOf_eq
    (hR.to_subgroup _) (Group.IsNilpotent.inf_center_ne_bot_of_normal hCne)
  exact ⟨c, ⟨c.2, Subgroup.mem_subgroupOf.mp hcT.1⟩, by rw [Subgroup.orderOf_coe, hc],
    fun v hv => congrArg Subtype.val (Subgroup.mem_center_iff.mp hcT.2 ⟨v, hv⟩)⟩

theorem card_map_eq_of_pRank_le {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (f : X →* H) {A : Subgroup X} (hA : IsElemAbelian p A) {a b : ℕ}
    (hAcard : Nat.card A = p ^ (a + b)) (ha : Open.pRank p (A ⊓ f.ker) ≤ a)
    (hb : Open.pRank p (⊤ : Subgroup H) ≤ b) : Nat.card (A.map f) = p ^ b := by
  have : Fact p.Prime := ⟨hp⟩
  have hK : IsElemAbelian p (f.ker ⊓ A) := isElemAbelian_of_le_of_isElemAbelian hA inf_le_right
  have hM : IsElemAbelian p (A.map f) := elementary_abelian_map p hA f
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp
    (fun y => ⟨1, Subtype.ext (by simpa using hK.2 y y.2)⟩ : IsPGroup p ↥(f.ker ⊓ A))
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp
    (fun y => ⟨1, Subtype.ext (by simpa using hM.2 y y.2)⟩ : IsPGroup p ↥(A.map f))
  have hprod := Subgroup.relIndex_mul_card f.ker A
  rw [Subgroup.relIndex_ker, hi, hj, hAcard, ← pow_add] at hprod
  have hsum := Nat.pow_right_injective hp.two_le hprod
  have hi' : i ≤ Open.pRank p (A ⊓ f.ker) :=
    le_csSup (pRank_bddAbove p hp _) ⟨_, (inf_comm _ _).le, hK, hi⟩
  have hj' : j ≤ Open.pRank p (⊤ : Subgroup H) :=
    le_csSup (pRank_bddAbove p hp _) ⟨_, le_top, hM, hj⟩
  rw [hj]
  congr 1
  omega

theorem not_le_range_conj_of_isCyclic {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hZ : Subgroup.center K = ⊥) (T : Sylow p K) (hT : IsCyclic (T : Subgroup K))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    ¬ E ≤ (MulAut.conj : K →* MulAut K).range := by
  intro hle
  have hinj := mulAut_conj_injective hZ
  have hJ : IsElemAbelian p (E.comap (MulAut.conj : K →* MulAut K)) := by
    refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hinj ?_), fun x hx => hinj ?_⟩
    · have : IsMulCommutative E := hE.1
      simpa only [Subgroup.coe_mul, map_mul] using
        setLike_mul_comm (show MulAut.conj (a : K) ∈ E from a.2)
          (show MulAut.conj (b : K) ∈ E from b.2)
    · rw [map_pow, map_one]
      exact hE.2 _ hx
  have hcard : Nat.card (E.comap (MulAut.conj : K →* MulAut K)) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hle, hEcard]
  have hle' := card_le_of_isElemAbelian_of_isCyclic_sylow T hT hJ
  rw [hcard, sq] at hle'
  have := (Fact.out : p.Prime).two_le
  nlinarith

end Lemmas

section Reduced

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.inf_normalizer_zpowers_le_of_aut
    (h : ReducedNongeneration p Y Rb Y₀)
    (hA : CycAutRankLeTwo p Y Rb)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (h3 : Open.pRank p (Rb : Subgroup Y) = 3) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    {t : Y} (ht : t ∈ (Rb : Subgroup Y) ⊓ L) (htp : orderOf t = p) :
    L ⊓ Subgroup.normalizer (Subgroup.zpowers t : Set Y) ≤ Y₀ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hRL := h.sylow_le_normalizer_component hL
  have h2 := pRank_le_pRank_inf_centralizer_add_pRank_mulAut hp hRL
  have h4 := hA L hL (hcyc L hL)
  obtain ⟨z, ⟨hzR, hzC⟩, hz, hzZ⟩ := exists_commute_mem_inf_centralizer Rb.isPGroup' hRL
    fun hbot => by
      rw [hbot, pRank_bot_eq_zero hp] at h2
      omega
  have hZ := h.center_eq_bot_of_isCyclic hL (hcyc L hL)
  have hzt : z ∉ Subgroup.zpowers t := by
    intro hzt
    have hmem : (⟨z, Subgroup.zpowers_le.mpr ht.2 hzt⟩ : L) ∈ Subgroup.center L :=
      Subgroup.mem_center_iff.mpr fun k =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC k k.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    have hz1 : z = 1 := congrArg Subtype.val hmem
    rw [hz1, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hQR : Subgroup.zpowers t ⊔ Subgroup.zpowers z ≤ Rb :=
    sup_le (Subgroup.zpowers_le.mpr ht.1) (Subgroup.zpowers_le.mpr hzR)
  have hQ2 : 2 ≤ Open.pRank p (Subgroup.zpowers t ⊔ Subgroup.zpowers z) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp htp (hz ▸ pow_orderOf_eq_one z) hzt
      (Subgroup.mem_centralizer_iff.mp hzC t ht.2)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hC := h.three_le_pRank_inf_centralizer_sup_zpowers htp hz
    (fun v hv => h.conj_mem_zpowers_of_component hL (hcyc L hL) ht hv)
    fun v hv => by
      rw [(hzZ v hv).eq, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers z
  have hN := (normalizer_le_weakCore p hQR hQ2 (hC.trans (pRank_mono p hp le_sup_right))).trans
    h.weakCore_le
  rintro g ⟨hgL, hgN⟩
  refine hN (mem_normalizer_sup_zpowers ?_ ?_)
  · exact Subgroup.mem_sup_left
      ((Subgroup.mem_normalizer_iff.mp hgN t).mp (Subgroup.mem_zpowers t))
  · rw [Subgroup.mem_centralizer_iff.mp hzC g hgL, mul_inv_cancel_right]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem ReducedNongeneration.inf_normalizer_zpowers_le (h : ReducedNongeneration p Y Rb Y₀)
    (hX : CatalogSimpleSections Y) (hβ : KFactBeta)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (h3 : Open.pRank p (Rb : Subgroup Y) = 3) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    {t : Y} (ht : t ∈ (Rb : Subgroup Y) ⊓ L) (htp : orderOf t = p) :
    L ⊓ Subgroup.normalizer (Subgroup.zpowers t : Set Y) ≤ Y₀ :=
  h.inf_normalizer_zpowers_le_of_aut (h.cycAutRankLeTwo_of_kFactBeta hX hβ) hcyc h3 hL ht htp


theorem ReducedNongeneration.mem_of_commute (h : ReducedNongeneration p Y Rb Y₀)
    {L A : Subgroup Y} {z : Y} (hzR : z ∈ (Rb : Subgroup Y)) (hz : orderOf z = p)
    (hzC : z ∈ Subgroup.centralizer (L : Set Y))
    (hzZ : ∀ v ∈ (Rb : Subgroup Y), Commute v z) (hAR : A ≤ Rb) (hA : IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 3) {a : Y} (haA : a ∈ A)
    (haC : a ∉ Subgroup.centralizer (L : Set Y)) {k : Y} (hkL : k ∈ L) (hka : Commute k a) :
    k ∈ Y₀ := by
  have hp := h.prime
  have haz : a ∉ Subgroup.zpowers z := fun ha => haC (Subgroup.zpowers_le.mpr hzC ha)
  have hQR : Subgroup.zpowers z ⊔ Subgroup.zpowers a ≤ Rb :=
    sup_le (Subgroup.zpowers_le.mpr hzR) (Subgroup.zpowers_le.mpr (hAR haA))
  have hQ2 : 2 ≤ Open.pRank p (Subgroup.zpowers z ⊔ Subgroup.zpowers a) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp hz (hA.2 a haA) haz (hzZ a (hAR haA)).symm
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  have hAC : A ≤ (Rb : Subgroup Y) ⊓ Subgroup.centralizer
      ((Subgroup.zpowers z ⊔ Subgroup.zpowers a : Subgroup Y) : Set Y) := by
    have : IsMulCommutative A := hA.1
    exact le_inf hAR (le_centralizer_sup_zpowers (fun v hv => hzZ v (hAR hv))
      fun v hv => setLike_mul_comm hv haA)
  have h3 : 3 ≤ Open.pRank p (Subgroup.zpowers z ⊔ Subgroup.zpowers a ⊔
      ((Rb : Subgroup Y) ⊓ Subgroup.centralizer
        ((Subgroup.zpowers z ⊔ Subgroup.zpowers a : Subgroup Y) : Set Y))) :=
    (le_csSup (pRank_bddAbove p hp _) ⟨A, le_rfl, hA, hAcard⟩).trans
      (pRank_mono p hp (hAC.trans le_sup_right))
  have hkz : Commute k z := Subgroup.mem_centralizer_iff.mp hzC k hkL
  refine (normalizer_le_weakCore p hQR hQ2 h3).trans h.weakCore_le
    (Subgroup.centralizer_le_normalizer _ ?_)
  exact le_centralizer_sup_zpowers (A := Subgroup.zpowers k)
    (fun v hv => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact hkz.zpow_left n)
    (fun v hv => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact hka.zpow_left n)
    (Subgroup.mem_zpowers k)

theorem ReducedNongeneration.closure_fixed_le (h : ReducedNongeneration p Y Rb Y₀)
    {L A : Subgroup Y} {z : Y} (hzR : z ∈ (Rb : Subgroup Y)) (hz : orderOf z = p)
    (hzC : z ∈ Subgroup.centralizer (L : Set Y))
    (hzZ : ∀ v ∈ (Rb : Subgroup Y), Commute v z) (hAR : A ≤ Rb) (hA : IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 3) :
    Subgroup.closure {k : L | ∃ e ∈ (A.subgroupOf (Subgroup.normalizer (L : Set Y))).map
      L.normalizerMonoidHom, e ≠ 1 ∧ e k = k} ≤ Y₀.subgroupOf L := by
  rw [Subgroup.closure_le]
  rintro k ⟨_, ⟨a, haA, rfl⟩, he1, hek⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  have haC : (a : Y) ∉ Subgroup.centralizer (L : Set Y) := fun haC =>
    he1 (MonoidHom.mem_ker.mp (by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact Subgroup.mem_subgroupOf.mpr haC))
  have hka : Commute (k : Y) a := by
    have h1 := Subgroup.normalizerMonoidHom_apply_apply_coe L a k
    rw [hek] at h1
    calc (k : Y) * a = a * k * (a : Y)⁻¹ * a := by rw [← h1]
      _ = a * k := by group
  exact h.mem_of_commute hzR hz hzC hzZ hAR hA hAcard (Subgroup.mem_subgroupOf.mp haA) haC k.2
    hka

theorem ReducedNongeneration.isCaseTwoGroup_of_not_le_of_aut
    (h : ReducedNongeneration p Y Rb Y₀)
    (hX : CatalogSimpleSections Y) (hA : CycAutRankLeTwo p Y Rb) (hS : KFactSeitzCyc)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (h3 : Open.pRank p (Rb : Subgroup Y) = 3) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hLY₀ : ¬ L ≤ Y₀) : IsCaseTwoGroup p L := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hRL := h.sylow_le_normalizer_component hL
  have h1 := h.pRank_inf_centralizer_le_one_of_not_le hL hLY₀
  have h2 := pRank_le_pRank_inf_centralizer_add_pRank_mulAut hp hRL
  have h4 := hA L hL (hcyc L hL)
  obtain ⟨z, ⟨hzR, hzC⟩, hz, hzZ⟩ := exists_commute_mem_inf_centralizer Rb.isPGroup' hRL
    fun hbot => by
      rw [hbot, pRank_bot_eq_zero hp] at h2
      omega
  obtain ⟨hsimple, hnonab, hcat, T, hTne, hTcyc⟩ := h.isSimpleGroup_of_isCyclic hX hL (hcyc L hL)
  obtain ⟨A, hAR, hA, hAcard⟩ := pRank_attained p hp (Rb : Subgroup Y)
  rw [h3] at hAcard
  have hA' := isElemAbelian_subgroupOf hA (Subgroup.normalizer (L : Set Y))
  have hA'card : Nat.card (A.subgroupOf (Subgroup.normalizer (L : Set Y))) = p ^ (1 + 2) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAR.trans hRL)).toEquiv, hAcard]
  have hker : Open.pRank p (A.subgroupOf (Subgroup.normalizer (L : Set Y)) ⊓
      L.normalizerMonoidHom.ker) ≤ 1 := by
    rw [← pRank_map_of_injective p hp _ (Subgroup.normalizer (L : Set Y)).subtype_injective]
    refine (pRank_mono p hp ?_).trans h1
    rintro _ ⟨x, ⟨hxA, hxK⟩, rfl⟩
    have hxK' : x ∈ L.normalizerMonoidHom.ker := hxK
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hxK'
    exact ⟨hAR (Subgroup.mem_subgroupOf.mp hxA), hxK'⟩
  have hE := elementary_abelian_map p hA' L.normalizerMonoidHom
  have hEcard := card_map_eq_of_pRank_le hp L.normalizerMonoidHom hA' hA'card hker h4
  have hfix := h.closure_fixed_le hzR hz hzC hzZ hAR hA hAcard
  refine hS L hsimple hnonab hcat p hp h.ne_two T hTne hTcyc _ hE hEcard
    (not_le_range_conj_of_isCyclic (h.center_eq_bot_of_isCyclic hL (hcyc L hL)) T hTcyc hE
      hEcard) fun htop => hLY₀ ?_
  rw [htop, top_le_iff, Subgroup.subgroupOf_eq_top] at hfix
  exact hfix

theorem ReducedNongeneration.isCaseTwoGroup_of_not_le (h : ReducedNongeneration p Y Rb Y₀)
    (hX : CatalogSimpleSections Y) (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (h3 : Open.pRank p (Rb : Subgroup Y) = 3) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hLY₀ : ¬ L ≤ Y₀) : IsCaseTwoGroup p L :=
  h.isCaseTwoGroup_of_not_le_of_aut hX (h.cycAutRankLeTwo_of_kFactBeta hX hβ) hS hcyc h3 hL hLY₀


end Reduced

end CFSG.AGLEmbedding
