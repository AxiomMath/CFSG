module

public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideWreathAux
import CFSG.LocalAnalysis.AGLEmbedding.EscapeRankBar

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Diagonal

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem exists_orderOf_eq_three_commute {K : Subgroup Y}
    (hK : Nat.Coprime 3 (Nat.card (K ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y)))
    {a c : Y} (ha : a ∈ K) (hc : c ∈ Subgroup.centralizer (K : Set Y)) (h3 : (c * a) ^ 3 = 1)
    (hne : c * a ∉ Subgroup.centralizer (K : Set Y)) :
    ∃ ℓ ∈ K, orderOf ℓ = 3 ∧ ∀ x ∈ K, Commute x ℓ → Commute x (c * a) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hca : Commute c a := (Subgroup.mem_centralizer_iff.mp hc a ha).symm
  have ha3C : a ^ 3 ∈ Subgroup.centralizer (K : Set Y) := by
    have h1 : c ^ 3 * a ^ 3 = 1 := by rw [← hca.mul_pow]; exact h3
    rw [eq_inv_of_mul_eq_one_right h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc 3)
  have hn : Nat.Coprime 3 (orderOf (a ^ 3)) := Nat.Coprime.coprime_dvd_right
    (Subgroup.orderOf_dvd_natCard _
      (Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ ha 3, ha3C⟩)) hK
  obtain ⟨m, k, hmk⟩ : ∃ m k : ℕ, orderOf (a ^ 3) * m = 3 * k + 1 := by
    have h3n : ¬ 3 ∣ orderOf (a ^ 3) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hn
    rcases (by omega : orderOf (a ^ 3) % 3 = 1 ∨ orderOf (a ^ 3) % 3 = 2) with h1 | h1
    · exact ⟨1, orderOf (a ^ 3) / 3, by omega⟩
    · exact ⟨2, 2 * orderOf (a ^ 3) / 3, by omega⟩
  have hrepr : a = ((a ^ 3) ^ k)⁻¹ * (a ^ orderOf (a ^ 3)) ^ m := by
    rw [← pow_mul a (orderOf (a ^ 3)) m, hmk, pow_succ a (3 * k), pow_mul a 3 k,
      inv_mul_cancel_left]
  have hl3 : (a ^ orderOf (a ^ 3)) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]
  have hl1 : a ^ orderOf (a ^ 3) ≠ 1 := by
    intro hl1
    apply hne
    have haC : a ∈ Subgroup.centralizer (K : Set Y) := by
      rw [hrepr, hl1, one_pow, mul_one]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ ha3C k)
    exact Subgroup.mul_mem _ hc haC
  refine ⟨a ^ orderOf (a ^ 3), Subgroup.pow_mem _ ha _, orderOf_eq_prime hl3 hl1,
    fun x hx hxl => ?_⟩
  have hx3 : Commute x (a ^ 3) := Subgroup.mem_centralizer_iff.mp ha3C x hx
  have hxa : Commute x a := by
    rw [hrepr]
    exact ((hx3.pow_right k).inv_right).mul_right (hxl.pow_right m)
  have hxc : Commute x c := Subgroup.mem_centralizer_iff.mp hc x hx
  exact hxc.mul_right hxa

theorem succ_le_pRank_centralizer_of_diagonal {K F : Subgroup Y} {s t : Y}
    (hK : Nat.Coprime 3 (Nat.card (K ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y)))
    (hs3 : s ^ 3 = 1) (hsK : s ∉ Subgroup.normalizer (K : Set Y)) (hst : Commute s t)
    (h01 : ∀ x ∈ K, ∀ y ∈ K, Commute x (MulAut.conj s y))
    (h02 : ∀ x ∈ K, ∀ y ∈ K, Commute x (MulAut.conj s (MulAut.conj s y)))
    (hFK : F ≤ K) (hF : IsElemAbelian 3 F) (hFt : F ≤ Subgroup.centralizer ({t} : Set Y))
    {k : ℕ} (hFc : Nat.card F = 3 ^ k) :
    k + 1 ≤ Open.pRank 3
      (Subgroup.centralizer ({s} : Set Y) ⊓ Subgroup.centralizer ({t} : Set Y)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c := MulAut.conj s with hc
  have h12 : ∀ x ∈ K, ∀ y ∈ K, Commute (c x) (c (c y)) := fun x hx y hy =>
    (h01 x hx y hy).map c
  have hcC : ∀ x ∈ K, c x ∈ Subgroup.centralizer (K : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (h01 y hy x hx).eq
  have hccC : ∀ x ∈ K, c (c x) ∈ Subgroup.centralizer (K : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (h02 y hy x hx).eq
  have hc3 : ∀ x, c (c (c x)) = x := fun x => by
    rw [hc, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    calc s * (s * (s * x * s⁻¹) * s⁻¹) * s⁻¹ = (s * s * s) * x * (s * s * s)⁻¹ := by group
      _ = x := by rw [← pow_three', hs3, one_mul, inv_one, mul_one]
  have hct : c t = t := by rw [hc, MulAut.conj_apply, hst.eq, mul_inv_cancel_right]
  have key : ∀ a ∈ K, ∀ b ∈ K,
      a * b * c (a * b) * c (c (a * b)) = a * c a * c (c a) * (b * c b * c (c b)) := by
    intro a ha b hb
    simp only [map_mul]
    calc a * b * (c a * c b) * (c (c a) * c (c b))
        = a * b * c a * (c b * c (c a)) * c (c b) := by simp only [mul_assoc]
      _ = a * b * c a * (c (c a) * c b) * c (c b) := by rw [(h12 b hb a ha).eq]
      _ = a * (b * c a) * c (c a) * (c b * c (c b)) := by simp only [mul_assoc]
      _ = a * (c a * b) * c (c a) * (c b * c (c b)) := by rw [(h01 b hb a ha).eq]
      _ = a * c a * (b * c (c a)) * (c b * c (c b)) := by simp only [mul_assoc]
      _ = a * c a * (c (c a) * b) * (c b * c (c b)) := by rw [(h02 b hb a ha).eq]
      _ = a * c a * c (c a) * (b * c b * c (c b)) := by simp only [mul_assoc]
  let φ : ↥F →* Y := MonoidHom.mk' (fun x => (x : Y) * c x * c (c x)) fun x y =>
    key _ (hFK x.2) _ (hFK y.2)
  have hφ : ∀ x : ↥F, φ x = (x : Y) * c x * c (c x) := fun x => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hφ, mul_assoc] at hx
    have hxK := hFK x.2
    have hxC : (x : Y) ∈ Subgroup.centralizer (K : Set Y) := by
      rw [eq_inv_of_mul_eq_one_left hx]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (hcC _ hxK) (hccC _ hxK))
    have h1 : orderOf (x : Y) = 1 := Nat.eq_one_of_dvd_coprimes hK
      (orderOf_dvd_of_pow_eq_one (hF.2 _ x.2)) (Subgroup.orderOf_dvd_natCard _ ⟨hxK, hxC⟩)
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  have hφs : ∀ x : ↥F, s * φ x = φ x * s := by
    intro x
    have hxK := hFK x.2
    have hcomm : Commute (x : Y) (c x * c (c x)) := (h01 _ hxK _ hxK).mul_right (h02 _ hxK _ hxK)
    have hfix : c (φ x) = φ x := by
      rw [hφ, map_mul, map_mul, hc3, mul_assoc (x : Y), hcomm.eq]
    rw [hc, MulAut.conj_apply] at hfix
    calc s * φ x = s * φ x * s⁻¹ * s := by group
      _ = φ x * s := by rw [hfix]
  have hφt : ∀ x : ↥F, t * φ x = φ x * t := by
    intro x
    have hxt : Commute (x : Y) t := (Subgroup.mem_centralizer_iff.mp (hFt x.2) t rfl).symm
    have h1 : Commute (c x) t := by
      have h2 := hxt.map c
      rwa [hct] at h2
    have h2 : Commute (c (c x)) t := by
      have h3 := h1.map c
      rwa [hct] at h3
    exact ((hxt.mul_left h1).mul_left h2).eq.symm
  have hsφ : s ∉ φ.range := by
    rintro ⟨x, hx⟩
    apply hsK
    rw [← hx, hφ]
    have hxK := hFK x.2
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer hxK)
      (Subgroup.centralizer_le_normalizer _ (hcC _ hxK)))
      (Subgroup.centralizer_le_normalizer _ (hccC _ hxK))
  have hR : IsElemAbelian 3 φ.range := by
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
      refine Subtype.ext ?_
      change φ x * φ y = φ y * φ x
      rw [← map_mul, ← map_mul, (isMulCommutative_iff.mp hF.1) x y]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow, show x ^ 3 = 1 from Subtype.ext (hF.2 _ x.2), map_one]
  have hRc : Nat.card φ.range = 3 ^ k := by
    rw [← hFc]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  refine succ_le_pRank_of_isElemAbelian_of_mem_centralizer Nat.prime_three hR hRc hs3 hsφ ?_ ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    exact (hφs x).symm
  · rintro _ ⟨x, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun g hg => ?_,
      Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    · rw [Set.mem_singleton_iff.mp hg]
      exact hφs x
    · rw [Set.mem_singleton_iff.mp hg]
      exact hφt x
  · refine ⟨Subgroup.mem_centralizer_iff.mpr fun g hg => ?_,
      Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    · rw [Set.mem_singleton_iff.mp hg]
    · rw [Set.mem_singleton_iff.mp hg]
      exact hst.eq.symm

end Diagonal

section A9MSide

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X : Subgroup G} {σ z : G}

theorem IsTwoPrimeComponent.commute_of_mem_barM {A B : Subgroup G}
    (hA : IsTwoPrimeComponent M A) (hB : IsTwoPrimeComponent M B) (hne : A ≠ B)
    {a b : ↥M ⧸ CFSG.pCore 2 ↥M} (ha : a ∈ barM M A) (hb : b ∈ barM M B) : Commute a b := by
  have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA.component
    hB.component fun he => hne (hA.eq_of_barM_eq hB he)
  exact (Subgroup.mem_centralizer_iff.mp
    ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc ha) b hb).symm

theorem D1A9DataCore.exists_mem_barM_orderOf_eq_three (h : D1A9DataCore P M H R X σ z)
    (hB3 : StmtBlockThree) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hzL : z ∉ blockCentralizer M L) (t : M)
    (ht : (t : G) = z) :
    ∃ ℓ ∈ barM M L, orderOf ℓ = 3 ∧ ∀ x ∈ barM M L, Commute x ℓ →
      Commute x (QuotientGroup.mk' (CFSG.pCore 2 ↥M) t) := by
  have hLM : L ≤ M := hL.le
  have hbarC : barM M (blockCentralizer M L) ≤
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨c, hcM⟩, hc, rfl⟩
    exact (mem_blockCentralizer_iff ⟨c, hcM⟩).mp (Subgroup.mem_subgroupOf.mp hc)
  have hCL : blockCentralizer M L ≤ Subgroup.normalizer (L : Set G) :=
    hL.toIsTwoPrimeComponent.le_normalizer (hbarC.trans (Subgroup.centralizer_le_normalizer _))
      (blockCentralizer_le M L)
  have hzLC : z ∈ ((blockCentralizer M L ⊔ L : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact h.le_sup_blockCentralizer hB3 hL h.z_mem
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ L hCL] at hzLC
  obtain ⟨c, hc, l, hl, hcl⟩ := hzLC
  have hcM := blockCentralizer_le M L hc
  have hzt : QuotientGroup.mk' (CFSG.pCore 2 ↥M) t =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨c, hcM⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM hl⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext (ht.trans hcl.symm)
  have ht3 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) t ^ 3 = 1 := by
    rw [← map_pow, show t ^ 3 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, ht]
      exact h.elem.2 z h.z_mem), map_one]
  have hne : QuotientGroup.mk' (CFSG.pCore 2 ↥M) t ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun hC =>
    hzL (ht ▸ (mem_blockCentralizer_iff t).mpr hC)
  rw [hzt] at ht3 hne ⊢
  exact exists_orderOf_eq_three_commute (coprime_three_card_inf_centralizer hO hL.component.2.1)
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl))
    ((mem_blockCentralizer_iff ⟨c, hcM⟩).mp hc) ht3 hne

theorem D1A9DataCore.false_of_lt_card_le_barM (h : D1A9DataCore P M H R X σ z)
    (hB3 : StmtBlockThree) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hσL : σ ∉ Subgroup.normalizer (L : Set G))
    (hzL : z ∉ blockCentralizer M L) {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hEL : E ≤ barM M L) (hE : IsElemAbelian 3 E) (hEc : 3 < Nat.card E) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := h.surv.ph3
  have hσM : σ ∈ M := h3.le_M h.σ_mem
  have hzM : z ∈ M := h3.le_M (h.surv.le_R h.z_mem)
  have h2 : 2 ≤ Open.pRank 3 (barM M L) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (show IsPGroup 3 E from fun x =>
      ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩)
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have h1 : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hk] at h1
      omega
    exact hk2.trans (le_csSup (pRank_bddAbove 3 Nat.prime_three _) ⟨E, hEL, hE, hk⟩)
  obtain ⟨ℓ, hℓL, hℓ3, hℓz⟩ := h.exists_mem_barM_orderOf_eq_three hB3 hO hL hzL ⟨z, hzM⟩ rfl
  have hF2 := two_le_pRank_inf_centralizer_of_two_le Nat.prime_three (by decide) h2 hℓL hℓ3
  obtain ⟨F, hFle, hFe, hFc⟩ := pRank_attained 3 Nat.prime_three
    (barM M L ⊓ Subgroup.centralizer ({ℓ} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
  have hσK : σ ∈ H ⊓ M := h3.le_inf h.σ_mem
  have hσS : σ ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (h3.inf_eq_inf_normalizer_twoCore ▸ hσK).2
  have hL₁ := hL.map_conj hσK.2 hσS
  have hL₂ := hL₁.map_conj hσK.2 hσS
  have h01 : L ≠ L.map (MulAut.conj σ).toMonoidHom := fun he =>
    hσL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have h02 : L ≠ (L.map (MulAut.conj σ).toMonoidHom).map (MulAut.conj σ).toMonoidHom := by
    intro he
    rw [← map_conj_mul_eq] at he
    have hσ2 : σ * σ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm
    have hσ4 : σ = (σ * σ) * (σ * σ) := by
      calc σ = σ ^ 3 * σ := by rw [h.σ_pow, one_mul]
        _ = (σ * σ) * (σ * σ) := by rw [pow_three']; simp only [mul_assoc]
    exact hσL (by rw [hσ4]; exact Subgroup.mul_mem _ hσ2 hσ2)
  have hb₁ := barM_map_conj hσM L
  have hb₂ := barM_map_conj hσM (L.map (MulAut.conj σ).toMonoidHom)
  have hc₁ : ∀ y ∈ barM M L, MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨σ, hσM⟩) y ∈
      barM M (L.map (MulAut.conj σ).toMonoidHom) := fun y hy => by
    rw [hb₁]
    exact Subgroup.mem_map_of_mem _ hy
  have hc₂ : ∀ y ∈ barM M L, MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨σ, hσM⟩)
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨σ, hσM⟩) y) ∈
        barM M ((L.map (MulAut.conj σ).toMonoidHom).map (MulAut.conj σ).toMonoidHom) :=
    fun y hy => by
      rw [hb₂]
      exact Subgroup.mem_map_of_mem _ (hc₁ y hy)
  have hsN : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨σ, hσM⟩ ∉
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun hs => by
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hs
    exact h01 (hL.toIsTwoPrimeComponent.eq_of_barM_eq hL₁.toIsTwoPrimeComponent
      (by rw [hb₁]; exact h1.symm))
  have hs3 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨σ, hσM⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨σ, hσM⟩ : M) ^ 3 = 1 from Subtype.ext h.σ_pow, map_one]
  have hst : Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨σ, hσM⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩) := by
    have h1 : Commute (⟨σ, hσM⟩ : M) ⟨z, hzM⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp h.z_center σ h.σ_mem)
    exact h1.map _
  have hk := succ_le_pRank_centralizer_of_diagonal
    (coprime_three_card_inf_centralizer hO hL.component.2.1) hs3 hsN hst
    (fun x hx y hy => hL.toIsTwoPrimeComponent.commute_of_mem_barM hL₁.toIsTwoPrimeComponent
      h01 hx (hc₁ y hy))
    (fun x hx y hy => hL.toIsTwoPrimeComponent.commute_of_mem_barM hL₂.toIsTwoPrimeComponent
      h02 hx (hc₂ y hy))
    (hFle.trans inf_le_left) hFe (fun x hx => Subgroup.mem_centralizer_iff.mpr fun g hg => by
      rw [Set.mem_singleton_iff.mp hg]
      exact (hℓz x (hFle hx).1
        (Subgroup.mem_centralizer_iff.mp (hFle hx).2 ℓ rfl).symm).eq.symm) hFc
  have hE2 := h.pRank_inf_centralizer_le_two ⟨σ, hσM⟩ ⟨z, hzM⟩ rfl rfl
  omega

theorem D1A9DataCore.eq_sylow_of_not_mem_normalizer (h : D1A9DataCore P M H R X σ z)
    (hB3 : StmtBlockThree) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (ha : KFactBlockCyclicThree) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hσL : σ ∉ Subgroup.normalizer (L : Set G)) : R = (P : Subgroup G) :=
  h.eq_sylow_of_forall_card_le_three hB3 h84 h85 hD2 ha hO hL hσL fun _ hL' _ hEL hE =>
    not_lt.mp fun hEc => h.false_of_lt_card_le_barM hB3 hO hL'
      (h.not_mem_normalizer_of_isWeakSBlock hB3 hL hL' hσL)
      (h.not_mem_blockCentralizer h84 hD2 hB3 hO hL hL' hσL) hEL hE hEc

end A9MSide

end CFSG.AGLEmbedding
