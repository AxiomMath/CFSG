module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_zpowers_sup_centralizer {P E : Subgroup G} (hEP : E ≤ P)
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEc : ∀ x ∈ P, x ^ 3 = 1 → ∀ e ∈ E, x * e = e * x) (hrank : 3 ≤ CFSG.Open.pRank 3 P)
    {x : G} (hxP : x ∈ P) (hx : orderOf x = 3) :
    3 ≤ CFSG.Open.pRank 3
      (Subgroup.zpowers x ⊔ (P ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G))) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  set C : Subgroup G := P ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G) with hC
  have hcentr : ∀ y : G, x * y = y * x →
      y ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    intro y hxy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute x y from hxy) k).eq
  by_cases hxE : x ∈ E
  · obtain ⟨F, hFP, hFe, hFcard⟩ := pRank_attained 3 hp P
    have hFC : F ≤ C := by
      refine le_inf hFP ?_
      intro f hf
      apply hcentr
      exact (hEc f (hFP hf) (hFe.2 f hf) x hxE).symm
    have h3 : 3 ≤ CFSG.Open.pRank 3 F :=
      hrank.trans (CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian hp hFe hFcard)
    exact h3.trans ((pRank_mono 3 hp hFC).trans (pRank_mono 3 hp le_sup_right))
  · set P' : Subgroup G := Subgroup.zpowers x with hP'
    have hExc : ∀ r ∈ E, x * r = r * x := fun r hr => hEc x hxP hx3 r hr
    have hEC : E ≤ C := fun r hr => ⟨hEP hr, hcentr r (hExc r hr)⟩
    have hP'card : Nat.card P' = 3 := by rw [hP', Nat.card_zpowers, hx]
    have hP'cent : ∀ p ∈ P', ∀ r ∈ E, p * r = r * p := by
      intro p hp' r hr
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp'
      exact (Commute.zpow_left (show Commute x r from hExc r hr) m).eq
    have hP'cube : ∀ p ∈ P', p ^ 3 = 1 := by
      intro p hp'
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp'
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    have hinf : P' ⊓ E = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      by_contra hy1
      have hyo : orderOf y = 3 := orderOf_eq_prime (hP'cube y hy.1) hy1
      have hzp : Subgroup.zpowers y = P' := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy.1) ?_
        rw [hP'card, Nat.card_zpowers, hyo]
      have hxy : x ∈ Subgroup.zpowers y := by rw [hzp]; exact Subgroup.mem_zpowers x
      exact hxE (Subgroup.zpowers_le.mpr hy.2 hxy)
    have hnormE : P' ≤ Subgroup.normalizer (E : Set G) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have : x * h * x⁻¹ = h := by
          calc x * h * x⁻¹ = h * x * x⁻¹ := by rw [hExc h hh]
            _ = h := by group
        rw [this]; exact hh
      · intro hh
        have h1 := hExc _ hh
        have h2 : h = x * h * x⁻¹ := by
          calc h = x⁻¹ * ((x * h * x⁻¹) * x) := by group
            _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [← h1]
            _ = x * h * x⁻¹ := by group
        rw [h2]; exact hh
    have hfac : ∀ z ∈ P' ⊔ E, ∃ p ∈ P', ∃ r ∈ E, z = p * r := by
      intro z hz
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P' E hnormE,
        Set.mem_mul] at hz
      obtain ⟨p, hp', r, hr, rfl⟩ := hz
      exact ⟨p, hp', r, hr, rfl⟩
    have hrel := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.relIndex_sup_eq_three_of_mul
      hP'card hinf hfac
    set F : Subgroup G := P' ⊔ E with hF
    have hEF : E ≤ F := le_sup_right
    have hFcard : Nat.card F = 3 ^ 3 := by
      have h1 := Subgroup.card_mul_index (E.subgroupOf F)
      have h2 : Nat.card (E.subgroupOf F) = Nat.card E :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEF).toEquiv
      have h3 : (E.subgroupOf F).index = 3 := hrel
      rw [h2, h3, hE9] at h1
      rw [← h1]; norm_num
    have hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
      intro a ha b hb
      obtain ⟨p, hp', r, hr, rfl⟩ := hfac a ha
      obtain ⟨q, hq', s, hs, rfl⟩ := hfac b hb
      have hpq : Commute p q := by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp'
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq'
        exact (Commute.refl x).zpow_zpow m n
      have hps : Commute p s := hP'cent p hp' s hs
      have hrq : Commute r q := (hP'cent q hq' r hr).symm
      have hrs : Commute r s :=
        congrArg Subtype.val (isMulCommutative_iff.mp hE.1 ⟨r, hr⟩ ⟨s, hs⟩)
      exact (Commute.mul_left (Commute.mul_right hpq hps) (Commute.mul_right hrq hrs)).eq
    have hFe : IsElemAbelian 3 F := by
      refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hFcomm a a.2 b b.2), ?_⟩
      intro a ha
      obtain ⟨p, hp', r, hr, rfl⟩ := hfac a ha
      have hpr : Commute p r := hP'cent p hp' r hr
      rw [hpr.mul_pow, hP'cube p hp', hE.2 r hr, one_mul]
    have hFle : F ≤ P' ⊔ C := sup_le_sup_left hEC P'
    exact (CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian hp hFe hFcard).trans
      (pRank_mono 3 hp hFle)

omit [Finite G] in
theorem mem_zpowers_conj_iff (m x h : G) :
    h ∈ Subgroup.zpowers (m * x * m⁻¹) ↔ m⁻¹ * h * m ∈ Subgroup.zpowers x := by
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [conj_zpow]
    have : m⁻¹ * (m * x ^ k * m⁻¹) * m = x ^ k := by group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [conj_zpow, hk]
    group

omit [Finite G] in
theorem normalizer_zpowers_le_of_conj {M : Subgroup G} {m : G} (hm : m ∈ M) {x : G}
    (h : Subgroup.normalizer ((Subgroup.zpowers (m * x * m⁻¹) : Subgroup G) : Set G) ≤ M) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M := by
  intro g hg
  have hgm : m * g * m⁻¹ ∈ Subgroup.normalizer
      ((Subgroup.zpowers (m * x * m⁻¹) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_zpowers_conj_iff, mem_zpowers_conj_iff]
    have e : m⁻¹ * (m * g * m⁻¹ * y * (m * g * m⁻¹)⁻¹) * m = g * (m⁻¹ * y * m) * g⁻¹ := by
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hg) (m⁻¹ * y * m)
  have hM := h hgm
  have : g = m⁻¹ * (m * g * m⁻¹) * m := by group
  rw [this]
  exact M.mul_mem (M.mul_mem (M.inv_mem hm) hM) hm

theorem D2L34SideCtx3.stronglyEmbedded_of_center {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K) {E : Subgroup G} (hEP : E ≤ (P : Subgroup G))
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEc : ∀ x ∈ (P : Subgroup G), x ^ 3 = 1 → ∀ e ∈ E, x * e = e * x) :
    GLBStronglyEmbedded 3 M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.setting.simple
  have hMtop : M ≠ ⊤ := twoLocal_ne_top h.setting.nonab h.maxLocal.1
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal h.setting h.sigma h.core
  have hrank : 3 ≤ CFSG.Open.pRank 3 (P : Subgroup G) := hP3.ge
  refine D2Escape.stronglyEmbedded_of_order_p h.conf.esc hMtop ?_
  intro x hxM hx
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hzp : IsPGroup 3 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx]
    simp
  obtain ⟨m, hm⟩ := exists_conjugate_le_sylow_of_le 3 P hPM
    (Subgroup.zpowers_le.mpr hxM) hzp
  set x' : G := (m : G) * x * (m : G)⁻¹ with hx'
  have hx'P : x' ∈ (P : Subgroup G) := by
    refine hm ⟨x, Subgroup.mem_zpowers x, ?_⟩
    simp [hx', MulAut.conj_apply]
  have hx'o : orderOf x' = 3 := by
    have h1 := orderOf_injective (MulAut.conj (m : G)).toMonoidHom
      (MulAut.conj (m : G)).injective x
    have h2 : (MulAut.conj (m : G)).toMonoidHom x = x' := by simp [hx', MulAut.conj_apply]
    rw [h2, hx] at h1
    exact h1
  have hQP : Subgroup.zpowers x' ≤ (P : Subgroup G) := Subgroup.zpowers_le.mpr hx'P
  have hQ1 : Subgroup.zpowers x' ≠ ⊥ := by
    intro hbot
    have : x' = 1 := by
      have := Subgroup.mem_zpowers x'
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [this, orderOf_one] at hx'o
    omega
  have hpure := three_le_pRank_zpowers_sup_centralizer hEP hE hE9 hEc hrank hx'P hx'o
  have hcl := ((h.threeClause h.sigma P h.core).1 (Subgroup.zpowers x') hQP hQ1
    (by simpa [Subgroup.centralizer, Set.centralizer] using hpure))
  exact normalizer_zpowers_le_of_conj m.2 hcl

theorem d2L34BetaMSide3_stronglyEmbedded_of_center (hSC : D2L34BetaMSolvableCenter3 G)
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K) (hs : Group.IsSolvable M) :
    GLBStronglyEmbedded 3 M := by
  obtain ⟨E, hEP, hE, hE9, hEc⟩ := hSC d P M A H R Rbar K h hs
  exact h.stronglyEmbedded_of_center hEP hE hE9 hEc

end CFSG.LocalAnalysis.RankThreeTheoremC
