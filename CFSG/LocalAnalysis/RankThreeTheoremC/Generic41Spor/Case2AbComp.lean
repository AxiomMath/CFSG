module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Case2AbDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2AS
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2KFact
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

theorem case2ab_pow_pow_eq_one_of_mem_sylow (S : Sylow p Y) {a : Y} (ha : a ∈ (S : Subgroup Y)) :
    ∃ k : ℕ, a ^ (p ^ k) = 1 := by
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨a, ha⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem case2ab_mem_normalizer_of_pow_coprime {H : Subgroup Y} {y : Y} {n : ℕ}
    (hy : y ^ n = 1) {m : ℕ} (hm : Nat.Coprime m n) (hym : y ^ m ∈ normalizer (H : Set Y)) :
    y ∈ normalizer (H : Set Y) := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm hn
    have h1 : y = (y ^ m) ^ k := by
      rw [← pow_mul, pow_eq_pow_mod (m * k) hy, hk, pow_one]
    rw [h1]
    exact pow_mem hym k
  · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · have hm1 : m = 1 := by simpa using hm
      subst hm1
      simpa using hym
    · have hy1 : y = 1 := by simpa using hy
      subst hy1
      exact one_mem _

theorem case2ab_mem_normalizer_of_pElement (h : Case2DataAb p P T D F x) {y : Y}
    (hy : ∃ k : ℕ, y ^ (p ^ k) = 1) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    y ∈ normalizer (L : Set Y) := by
  classical
  obtain ⟨k, hk⟩ := hy
  have hp5 : 5 ≤ p := h.five
  by_contra hyL
  set f : ℕ → Subgroup Y := fun i => L.map (MulAut.conj (y ^ i)).toMonoidHom with hf
  have hfK : ∀ i, IsComponentOf (f i) ⊤ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (y ^ i)) L).mpr hL
  have hinj : Set.InjOn f (Finset.range 4 : Set ℕ) := by
    have key : ∀ i j : ℕ, i < j → j < 4 → f i ≠ f j := by
      intro i j hij hj hfij
      apply hyL
      refine case2ab_mem_normalizer_of_pow_coprime hk (m := j - i) ?_ ?_
      · have hcop : Nat.Coprime (j - i) p :=
          (Nat.coprime_of_lt_prime (by omega) (by omega) h.prime).symm
        exact Nat.Coprime.pow_right k hcop
      · rw [mem_normalizer_iff_map_conj_eq]
        have h1 : f j = (f (j - i)).map (MulAut.conj (y ^ i)).toMonoidHom := by
          simp only [hf]
          rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, ← pow_add,
            Nat.add_sub_cancel' hij.le]
        rw [h1] at hfij
        exact (map_injective (MulAut.conj (y ^ i)).injective hfij).symm
    intro i hi j hj hfij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hlt | heq | hlt
    · exact absurd hfij (key i j hlt hj)
    · exact heq
    · exact absurd hfij.symm (key j i hlt hi)
  have hcard := CFSG.LocalAnalysis.RankThreeTheoremC.card_le_pRank_of_isComponentOf h.prime
    (by omega) h.core ((Finset.range 4).image f) (fun K' hK' => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK'
      exact hfK i)
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  have hrank := h.rank
  omega

theorem case2ab_P_normalizes_component (h : Case2DataAb p P T D F x) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) : P ≤ normalizer (L : Set Y) := by
  intro a ha
  obtain ⟨S, hS⟩ := h.sylow
  rw [← hS] at ha
  exact case2ab_mem_normalizer_of_pElement h (case2ab_pow_pow_eq_one_of_mem_sylow S ha) hL

theorem case2ab_pow_mul_mem_of_conj_mem {Y : Type*} [Group Y] {N : Subgroup Y} {a : Y}
    (ha : ∀ n ∈ N, a⁻¹ * n * a ∈ N) (n : Y) (hn : n ∈ N) (m : ℕ) :
    ∃ n' ∈ N, (a * n) ^ m = a ^ m * n' := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨n', hn', h⟩ := ih
    refine ⟨a⁻¹ * n' * a * n, N.mul_mem (ha n' hn') hn, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem case2ab_pow_mul_mem_of_pow_eq_one {Y : Type*} [Group Y] {N : Subgroup Y} {a : Y}
    (ha : ∀ n ∈ N, a⁻¹ * n * a ∈ N) {m : ℕ} (hm : a ^ m = 1) (n : Y) (hn : n ∈ N) :
    (a * n) ^ m ∈ N := by
  obtain ⟨n', hn', h⟩ := case2ab_pow_mul_mem_of_conj_mem ha n hn m
  rw [h, hm, one_mul]
  exact hn'

theorem case2ab_not_isPGroup_quotient_center {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hc : commutator G = ⊤)
    [hs : IsSimpleGroup (G ⧸ Subgroup.center G)] :
    ¬ IsPGroup p (G ⧸ Subgroup.center G) := by
  intro hpg
  have hbot : (⊥ : Subgroup (G ⧸ Subgroup.center G)) < Subgroup.center (G ⧸ Subgroup.center G) :=
    hpg.bot_lt_center
  have htop : Subgroup.center (G ⧸ Subgroup.center G) = ⊤ :=
    (hs.eq_bot_or_eq_top_of_normal (Subgroup.center (G ⧸ Subgroup.center G))).resolve_left hbot.ne'
  have hcomm_bot : commutator (G ⧸ Subgroup.center G) = ⊥ :=
    (commutator_eq_bot_iff_center_eq_top _).mpr htop
  have hsurj : Function.Surjective
      (QuotientGroup.mk' (Subgroup.center G) : G →* G ⧸ Subgroup.center G) :=
    QuotientGroup.mk'_surjective _
  have key : (commutator G).map (QuotientGroup.mk' (Subgroup.center G)) =
      commutator (G ⧸ Subgroup.center G) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hsurj, _root_.commutator_def]
  have hcomm_top : commutator (G ⧸ Subgroup.center G) = ⊤ := by
    rw [← key, hc]
    exact Subgroup.map_top_of_surjective _ hsurj
  have h1 : (⊤ : Subgroup (G ⧸ Subgroup.center G)) = ⊥ := hcomm_top.symm.trans hcomm_bot
  obtain ⟨z, hz⟩ := exists_ne (1 : G ⧸ Subgroup.center G)
  have hz' : z ∈ (⊥ : Subgroup (G ⧸ Subgroup.center G)) := by
    rw [← h1]
    exact Subgroup.mem_top z
  exact hz (Subgroup.mem_bot.mp hz')

theorem case2ab_not_le_centralizer_x (h : Case2DataAb p P T D F x) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    ¬ L ≤ centralizer ({x} : Set Y) := by
  intro hLW
  obtain ⟨N, hser⟩ := h.series
  haveI : Fact p.Prime := ⟨h.prime⟩
  have h5 : 5 ≤ p := h.five
  obtain ⟨S, hS⟩ := h.sylow
  obtain ⟨t, htmem, hto, htc⟩ :=
    exists_mem_sylow_inf_component h.prime (by omega) h.core S hL
  rw [hS] at htmem
  obtain ⟨htP, htL⟩ := Subgroup.mem_inf.mp htmem
  have ht_pow : t ^ p = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hto] at this
  have hPp : ∀ a ∈ P, ∃ k : ℕ, a ^ p ^ k = 1 := by
    intro a ha
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨a, by rw [hS]; exact ha⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hPW : P ≤ centralizer ({x} : Set Y) := hser.P_le
  have hPN : P ≤ Subgroup.normalizer N := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hser.N_norm g (hPW hg) n hn
    · intro hn
      have := hser.N_norm g⁻¹ ((centralizer ({x} : Set Y)).inv_mem (hPW hg)) _ hn
      rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at this
  have hdecomp : ∀ q ∈ P ⊔ N, ∃ a ∈ P, ∃ n ∈ N, q = a * n := by
    intro q hq
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P N hPN, Set.mem_mul] at hq
    obtain ⟨a, ha, n, hn, hq'⟩ := hq
    exact ⟨a, ha, n, hn, hq'.symm⟩
  have hconj : ∀ a ∈ P, ∀ n ∈ N, a⁻¹ * n * a ∈ N := by
    intro a ha n hn
    have := hser.N_norm a⁻¹ ((centralizer ({x} : Set Y)).inv_mem (hPW ha)) n hn
    rwa [inv_inv] at this
  have hPNpow : ∀ q ∈ P ⊔ N, ∃ k : ℕ, q ^ p ^ k ∈ N := by
    intro q hq
    obtain ⟨a, ha, n, hn, rfl⟩ := hdecomp q hq
    obtain ⟨k, hk⟩ := hPp a ha
    exact ⟨k, case2ab_pow_mul_mem_of_pow_eq_one (hconj a ha) hk n hn⟩
  obtain ⟨hcomm, hsimp⟩ := hL.2.2
  haveI := hsimp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : L →* L ⧸ Subgroup.center L, ρ = QuotientGroup.mk' (Subgroup.center L) :=
    ⟨_, rfl⟩
  have hρsurj : Function.Surjective ρ := by
    rw [hρ]
    exact QuotientGroup.mk'_surjective _
  have hker : ∀ a : L, ρ a = 1 ↔ a ∈ Subgroup.center L := by
    intro a
    rw [hρ]
    exact QuotientGroup.eq_one_iff a
  have hK₁ : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hser.N_norm (g : Y) (hLW g.2) (n : Y) hn
    simpa using this
  have hK₂ : ((P ⊔ N).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hser.PN_norm (g : Y) (hLW g.2) (n : Y) hn
    simpa using this
  obtain ⟨t', ht'⟩ : ∃ t' : L, (t' : Y) = t := ⟨⟨t, htL⟩, rfl⟩
  have ht'_pow : t' ^ p = 1 := by
    apply Subtype.ext
    simp [ht', ht_pow]
  have hρt_pow : ρ t' ^ p = 1 := by
    rw [← map_pow, ht'_pow, map_one]
  have hρt : ρ t' ≠ 1 := by
    intro h1
    apply htc
    have hcen := Subgroup.mem_center_iff.mp ((hker t').mp h1)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := congrArg Subtype.val (hcen ⟨l, hl⟩)
    rw [← ht']
    simpa using this
  have htPN : t ∈ P ⊔ N := (le_sup_left : P ≤ P ⊔ N) htP
  haveI hK₁map : ((N.subgroupOf L).map ρ).Normal := hK₁.map ρ hρsurj
  rcases hsimp.eq_bot_or_eq_top_of_normal ((N.subgroupOf L).map ρ) with hA₁ | hA₁
  ·
    haveI hK₂map : (((P ⊔ N).subgroupOf L).map ρ).Normal := hK₂.map ρ hρsurj
    have hB : ((P ⊔ N).subgroupOf L).map ρ = ⊤ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (((P ⊔ N).subgroupOf L).map ρ) with hB | hB
      · exfalso
        have hmem : ρ t' ∈ ((P ⊔ N).subgroupOf L).map ρ :=
          Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr (by rw [ht']; exact htPN))
        rw [hB, Subgroup.mem_bot] at hmem
        exact hρt hmem
      · exact hB
    have hPG : IsPGroup p (L ⧸ Subgroup.center L) := by
      intro q
      have hq : q ∈ ((P ⊔ N).subgroupOf L).map ρ := by
        rw [hB]
        exact Subgroup.mem_top q
      obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.mp hq
      obtain ⟨k, hk⟩ := hPNpow (ℓ : Y) (Subgroup.mem_subgroupOf.mp hℓ)
      refine ⟨k, ?_⟩
      have hmem : ℓ ^ p ^ k ∈ N.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
        exact hk
      have h1 : ρ (ℓ ^ p ^ k) ∈ (N.subgroupOf L).map ρ := Subgroup.mem_map_of_mem ρ hmem
      rw [hA₁, Subgroup.mem_bot] at h1
      rw [← map_pow]
      exact h1
    exact case2ab_not_isPGroup_quotient_center hcomm hPG
  ·
    have hmem : ρ t' ∈ (N.subgroupOf L).map ρ := by
      rw [hA₁]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hρn⟩ := Subgroup.mem_map.mp hmem
    have hnN : (n : Y) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have hkn : n ^ orderOf (n : Y) = 1 := by
      apply Subtype.ext
      simp [pow_orderOf_eq_one]
    have hρk : ρ t' ^ orderOf (n : Y) = 1 := by
      rw [← hρn, ← map_pow, hkn, map_one]
    have hgcd : orderOf (ρ t') ∣ Nat.gcd p (orderOf (n : Y)) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hρt_pow) (orderOf_dvd_of_pow_eq_one hρk)
    have hcop : Nat.gcd p (orderOf (n : Y)) = 1 := hser.N_cop (n : Y) hnN
    rw [hcop] at hgcd
    exact hρt (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd))

theorem case2ab_x_mem_P (h : Case2DataAb p P T D F x) : x ∈ P := h.pdata.D_le h.pdata.x_mem

theorem case2ab_x_pow_p (h : Case2DataAb p P T D F x) : x ^ p = 1 := by
  rw [← h.pdata.x_ord]
  exact pow_orderOf_eq_one x

theorem case2ab_P_comm (h : Case2DataAb p P T D F x) : IsMulCommutative P := by
  have hT : T ≤ centralizer (T : Set Y) :=
    le_centralizer_iff_isMulCommutative.mpr h.pdata.T_comm
  have hD : D ≤ centralizer (D : Set Y) := by
    haveI := h.pdata.D_cyc
    exact le_centralizer_iff_isMulCommutative.mpr IsCyclic.isMulCommutative
  have hTD : T ≤ centralizer (D : Set Y) := fun t ht =>
    mem_centralizer_iff.mpr fun d hd => (h.pdata.comm t ht d hd).symm
  have hDT : D ≤ centralizer (T : Set Y) := le_centralizer_iff.mp hTD
  have hPT : P ≤ centralizer (T : Set Y) := h.pdata.sup_eq ▸ sup_le hT hDT
  have hPD : P ≤ centralizer (D : Set Y) := h.pdata.sup_eq ▸ sup_le hTD hD
  have hPP : P ≤ centralizer (P : Set Y) := by
    conv_lhs => rw [← h.pdata.sup_eq]
    exact sup_le (le_centralizer_iff.mp hPT) (le_centralizer_iff.mp hPD)
  exact le_centralizer_iff_isMulCommutative.mp hPP

theorem case2ab_card_inf_cases {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {T C : Subgroup G} (hT : Nat.card T = p ^ 2) :
    Nat.card ↥(T ⊓ C) = p ∨ T ≤ C ∨ T ⊓ C = ⊥ := by
  have hdvd : Nat.card ↥(T ⊓ C) ∣ p ^ 2 := hT ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  interval_cases m
  · right; right
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using hmeq)
  · left
    simpa using hmeq
  · right; left
    have h1 : T ⊓ C = T :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hT, hmeq])
    rw [← h1]
    exact inf_le_right

open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (exists_almostSimple kFactWeakClosureRank2_of)

theorem case2ab_exists_psi (h : Case2DataAb p P T D F x) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (K : Subgroup X) (Q : Sylow p X) (ψ : ↥P →* X),
      K.Normal ∧ IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ IsCatalogGroup K ∧
      centralizer (K : Set X) = ⊥ ∧ p ∣ Nat.card K ∧ K ⊔ (Q : Subgroup X) = ⊤ ∧
      (∀ a : ↥P, ψ a = 1 ↔ (a : Y) ∈ centralizer (L : Set Y)) ∧
      ψ.range = (Q : Subgroup X) ∧
      ∀ g : X, (zpowers (ψ ⟨x, case2ab_x_mem_P h⟩)).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) →
        (zpowers (ψ ⟨x, case2ab_x_mem_P h⟩)).map (MulAut.conj g).toMonoidHom =
          zpowers (ψ ⟨x, case2ab_x_mem_P h⟩) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨X, hG, hF, π, K, Q, hπ⟩ :=
    exists_almostSimple h.core h.catalog hL h.sylow (case2ab_P_normalizes_component h hL)
  have hPL : P ≤ L ⊔ P := le_sup_right
  have hzp : ((zpowers x).subgroupOf (L ⊔ P)).map π
      = zpowers ((π.comp (Subgroup.inclusion hPL)) ⟨x, case2ab_x_mem_P h⟩) := by
    ext q
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, ⟨k, hk⟩, rfl⟩
      refine ⟨k, ?_⟩
      have : (Subgroup.inclusion hPL ⟨x, case2ab_x_mem_P h⟩) ^ k = n := by
        apply Subtype.ext
        simpa using hk
      simp only [MonoidHom.comp_apply]
      rw [← map_zpow, this]
    · rintro ⟨k, rfl⟩
      refine ⟨(Subgroup.inclusion hPL ⟨x, case2ab_x_mem_P h⟩) ^ k, ⟨k, by simp⟩, ?_⟩
      simp
  refine ⟨X, hG, hF, K, Q, π.comp (Subgroup.inclusion hPL), hπ.normal, hπ.simple, hπ.nonab, hπ.catalog,
    hπ.cent, hπ.dvd, hπ.sup, ?_, ?_, ?_⟩
  · intro a
    exact hπ.ker_iff (Subgroup.inclusion hPL a)
  · ext q
    rw [hπ.Q_eq]
    simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Subgroup.inclusion hPL a, a.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  · intro g
    have := hπ.weakClosed_transfer (A := zpowers x) (by simpa using case2ab_x_mem_P h) h.wc g
    rw [hzp] at this
    exact this

theorem case2ab_inf_centralizer_ne_bot (h : Case2DataAb p P T D F x) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    T ⊓ centralizer (L : Set Y) ≠ ⊥ := by
  intro hbot
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨X, _, _, K, Q, ψ, hKn, hKs, hKnab, hKcat, hKc, hKdvd, hKsup, hker, hrange, hwc⟩ :=
    case2ab_exists_psi h hL
  set x' : ↥P := ⟨x, case2ab_x_mem_P h⟩ with hx'
  have hψx : ψ x' ≠ 1 := by
    intro h1
    have hxc : x ∈ centralizer (L : Set Y) := (hker x').1 h1
    apply case2ab_not_le_centralizer_x h hL
    intro l hl
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (mem_centralizer_iff.mp hxc l hl).symm
  have hψxp : (ψ x') ^ p = 1 := by
    rw [← map_pow]
    have : x' ^ p = 1 := Subtype.ext (by simpa using case2ab_x_pow_p h)
    rw [this, map_one]
  have hAord : orderOf (ψ x') = p := orderOf_eq_prime hψxp hψx
  haveI hPcomm : IsMulCommutative P := case2ab_P_comm h
  have hQab : IsMulCommutative (Q : Subgroup X) := by
    rw [← hrange]
    refine isMulCommutative_iff.2 fun u v => ?_
    obtain ⟨a, ha⟩ := u.2
    obtain ⟨b, hb⟩ := v.2
    apply Subtype.ext
    show (u : X) * v = v * u
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg ψ (mul_comm' a b)
  have hrank : 2 ≤ CFSG.Open.pRank p (Q : Subgroup X) := by
    set ψT : ↥T →* X := ψ.comp (Subgroup.inclusion h.pdata.T_le) with hψT
    have hinj : Function.Injective ψT := by
      rw [injective_iff_map_eq_one]
      intro t ht
      have h1 : ψ (Subgroup.inclusion h.pdata.T_le t) = 1 := ht
      have h2 : ((Subgroup.inclusion h.pdata.T_le t : ↥P) : Y) ∈ centralizer (L : Set Y) :=
        (hker _).1 h1
      have h3 : (t : Y) ∈ T ⊓ centralizer (L : Set Y) := ⟨t.2, h2⟩
      rw [hbot, Subgroup.mem_bot] at h3
      exact Subtype.ext h3
    haveI hTcomm : IsMulCommutative T := h.pdata.T_comm
    refine le_pRank_of_elemAbelian_card (p := p) (P := (Q : Subgroup X)) (E := ψT.range) (k := 2) ?_ ?_ ?_
    · rw [← hrange]
      rintro _ ⟨t, rfl⟩
      exact ⟨Subgroup.inclusion h.pdata.T_le t, rfl⟩
    · refine ⟨?_, ?_⟩
      · refine isMulCommutative_iff.2 fun u v => ?_
        obtain ⟨a, ha⟩ := u.2
        obtain ⟨b, hb⟩ := v.2
        apply Subtype.ext
        show (u : X) * v = v * u
        rw [← ha, ← hb, ← map_mul, ← map_mul]
        exact congrArg ψT (mul_comm' a b)
      · rintro _ ⟨t, rfl⟩
        rw [← map_pow]
        have : t ^ p = 1 := Subtype.ext (by simpa using h.pdata.T_exp t t.2)
        rw [this, map_one]
    · rw [← h.pdata.T_card]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hAQ : zpowers (ψ x') ≤ (Q : Subgroup X) :=
    Subgroup.zpowers_le.2 (by rw [← hrange]; exact ⟨x', rfl⟩)
  have hAcard : Nat.card (zpowers (ψ x')) = p := by rw [Nat.card_zpowers]; exact hAord
  obtain ⟨g, hg1, hg2⟩ := kFactWeakClosureRank2_of hInn hWC p h.prime (by have := h.five; omega)
    X K hKn hKs hKnab hKcat hKc hKdvd Q hKsup hQab hrank (zpowers (ψ x')) hAQ hAcard
  exact hg2 (hwc g hg1)

theorem case2ab_centralizer_cases (h : Case2DataAb p P T D F x) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    Nat.card ↥(T ⊓ centralizer (L : Set Y)) = p ∨ T ≤ centralizer (L : Set Y) := by
  rcases case2ab_card_inf_cases h.prime h.pdata.T_card (C := centralizer (L : Set Y)) with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd h1 (case2ab_inf_centralizer_ne_bot h hInn hWC hL)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
