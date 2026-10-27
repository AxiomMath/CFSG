module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltDataOfAlt
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltLargePrime
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCentralExtOne
import CFSG.LocalAnalysis.AGLEmbeddingD2.Closure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCase
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

namespace AltSevenPrime

theorem pRank_le_pRank_comap {V W : Type*} [Group V] [Finite V] [Group W] [Finite W] {p : ℕ}
    [Fact p.Prime] (f : V →* W) (hf : Function.Surjective f) (hker : ¬ p ∣ Nat.card f.ker)
    (Z : Subgroup W) : Open.pRank p Z ≤ Open.pRank p (Z.comap f) := by
  let g : Z.comap f →* Z := (f.comp (Z.comap f).subtype).codRestrict Z fun x => x.2
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨v, hv⟩ := hf z
    exact ⟨⟨v, by simp [hv]⟩, Subtype.ext hv⟩
  have hgker : ¬ p ∣ Nat.card g.ker := by
    refine fun hdvd => hker (hdvd.trans (Subgroup.card_dvd_of_injective
      (((Z.comap f).subtype.comp g.ker.subtype).codRestrict f.ker fun x => ?_) ?_))
    · have := x.2
      rw [MonoidHom.mem_ker] at this ⊢
      exact congrArg Subtype.val this
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
  rw [SectionRank.pRank_eq_pRank_top_subgroup Z,
    SectionRank.pRank_eq_pRank_top_subgroup (Z.comap f),
    ← SectionRank.pRank_quotient_eq g.ker hgker]
  exact (SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt
    (QuotientGroup.quotientKerEquivOfSurjective g hg)).ge

end AltSevenPrime

theorem four_le_pRank_comap_of_central_sylow_alt {J : Type*} [Group J] [Finite J] {n : ℕ}
    (ψ : J →* alternatingGroup (Fin n)) (hψ : Function.Surjective ψ) (U : Sylow 3 ψ.ker)
    (hU : ∀ u : ψ.ker, u ∈ U → (u : J) ∈ Subgroup.center J)
    (c : Fin 4 → alternatingGroup (Fin n)) (hc : ∀ i, (c i : Equiv.Perm (Fin n)).IsThreeCycle)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (c i : Equiv.Perm (Fin n)).support (c j : Equiv.Perm (Fin n)).support) :
    4 ≤ Open.pRank 3 ((Subgroup.closure (Set.range c)).comap ψ) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : Subgroup.normalizer (U : Subgroup ψ.ker) ≤ Subgroup.centralizer (U : Set ψ.ker) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hU u hu) g.1).symm
  let φ : ψ.ker →* U := MonoidHom.transferSylow U hP
  have hcompl := MonoidHom.ker_transferSylow_isComplement' U hP
  have hO3 : ¬ 3 ∣ Nat.card φ.ker := MonoidHom.not_dvd_card_ker_transferSylow U hP
  let O : Subgroup J := φ.ker.map ψ.ker.subtype
  have hmem : ∀ y : ψ.ker, y ∈ φ.ker ↔ Nat.Coprime (orderOf y) 3 := by
    intro y
    constructor
    · intro hy
      have h1 := Subgroup.orderOf_dvd_natCard φ.ker hy
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 => hO3 (h3.trans h1)).symm
    · intro hy
      obtain ⟨k, hk⟩ := U.isPGroup' (φ y)
      have h1 : orderOf (φ y) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
      have h2 : orderOf (φ y) ∣ orderOf y :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hy.symm) h1 h2)
  have hOmem : ∀ x : J, x ∈ O ↔ x ∈ ψ.ker ∧ Nat.Coprime (orderOf x) 3 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by
        change (orderOf (y : J)).Coprime 3
        rw [Subgroup.orderOf_coe]
        exact (hmem y).1 hy⟩
    · rintro ⟨hx, hcop⟩
      refine ⟨⟨x, hx⟩, (hmem ⟨x, hx⟩).2 ?_, rfl⟩
      rw [← Subgroup.orderOf_coe]
      exact hcop
  have hOn : O.Normal := ⟨fun x hx g => by
    rw [hOmem] at hx ⊢
    refine ⟨Subgroup.Normal.conj_mem (MonoidHom.normal_ker ψ) x hx.1 g, ?_⟩
    have := (MulAut.conj g).orderOf_eq x
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hx.2⟩
  have hOker : O ≤ ψ.ker := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  let ψ' : J ⧸ O →* alternatingGroup (Fin n) := QuotientGroup.lift O ψ hOker
  have hψ' : Function.Surjective ψ' := by
    intro y
    obtain ⟨g, rfl⟩ := hψ y
    exact ⟨g, QuotientGroup.lift_mk O hOker g⟩
  have hform : ∀ q ∈ ψ'.ker, ∃ u : ψ.ker, u ∈ U ∧ q = (QuotientGroup.mk (u : J) : J ⧸ O) := by
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.lift_mk O hOker g).symm.trans hq
    obtain ⟨⟨⟨o, ho⟩, ⟨u, hu⟩⟩, hou, -⟩ :=
      (Subgroup.isComplement_iff_existsUnique.1 (Subgroup.isComplement'_def.1 hcompl)) ⟨g, hg⟩
    refine ⟨u, hu, ?_⟩
    have hgou : g = (o : J) * (u : J) := (congrArg Subtype.val hou).symm
    have hoO : QuotientGroup.mk (o : J) = (1 : J ⧸ O) :=
      (QuotientGroup.eq_one_iff _).2 ⟨o, ho, rfl⟩
    rw [hgou, QuotientGroup.mk_mul, hoO, one_mul]
  have hcenter : ψ'.ker ≤ Subgroup.center (J ⧸ O) := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := hform q hq
    rw [Subgroup.mem_center_iff]
    intro q'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 (hU u hu) g]
  have hp : IsPGroup 3 ψ'.ker := by
    intro q
    obtain ⟨u, hu, hq⟩ := hform q q.2
    obtain ⟨k, hk⟩ := U.isPGroup' ⟨u, hu⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (u : J) ^ 3 ^ k = 1 := congrArg (fun z : U => ((z : ψ.ker) : J)) hk
    change (q : J ⧸ O) ^ 3 ^ k = 1
    rw [hq, ← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
  have h4 := four_le_pRank_comap_of_central_three ψ' hψ' hcenter hp c hc hdisj
  have hOcard : ¬ 3 ∣ Nat.card (QuotientGroup.mk' O).ker := by
    rwa [QuotientGroup.ker_mk', Subgroup.card_map_of_injective ψ.ker.subtype_injective]
  have hcomp : ((Subgroup.closure (Set.range c)).comap ψ').comap (QuotientGroup.mk' O) =
      (Subgroup.closure (Set.range c)).comap ψ := by
    ext x
    simp only [Subgroup.mem_comap, QuotientGroup.mk'_apply]
    rw [show ψ' (QuotientGroup.mk x) = ψ x from QuotientGroup.lift_mk O hOker x]
  rw [← hcomp]
  exact h4.trans (AltSevenPrime.pRank_le_pRank_comap (QuotientGroup.mk' O)
    (QuotientGroup.mk'_surjective O) hOcard _)

theorem four_le_pRank_map_comap_of_central_sylow_alt {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} {n : ℕ} (ψ : J →* alternatingGroup (Fin n)) (hψ : Function.Surjective ψ)
    (U : Sylow 3 ψ.ker) (hU : ∀ u : ψ.ker, u ∈ U → (u : J) ∈ Subgroup.center J)
    (c : Fin 4 → alternatingGroup (Fin n)) (hc : ∀ i, (c i : Equiv.Perm (Fin n)).IsThreeCycle)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (c i : Equiv.Perm (Fin n)).support (c j : Equiv.Perm (Fin n)).support) :
    4 ≤ Open.pRank 3 (((Subgroup.closure (Set.range c)).comap ψ).map J.subtype) :=
  (four_le_pRank_comap_of_central_sylow_alt ψ hψ U hU c hc hdisj).trans
    (SectionRank.pRank_le_map (by norm_num) J.subtype J.subtype_injective _)

namespace AltSevenPrime

theorem le_map_closure_sevenElements {W X : Type*} [Group W] [Finite W] [Group X]
    (π : W →* X) (J : Subgroup W) (hJ : J.map π = ⊤) (K : Subgroup X) [IsSimpleGroup K] {σ : X}
    (hσK : σ ∈ K) (hσ7 : σ ^ 7 = 1) (hσ1 : σ ≠ 1) :
    K ≤ (Subgroup.closure {x : W | x ∈ J ∧ ∃ a : ℕ, x ^ 7 ^ a = 1}).map π := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set S : Set W := {x | x ∈ J ∧ ∃ a : ℕ, x ^ 7 ^ a = 1} with hS
  set J₁ : Subgroup W := Subgroup.closure S with hJ₁
  set Q : Subgroup X := J₁.map π with hQ
  have hJe : ∀ y : X, ∃ j ∈ J, π j = y := fun y => by
    have : y ∈ J.map π := hJ ▸ Subgroup.mem_top y
    exact this
  have hconj : ∀ j ∈ J, ∀ x ∈ J₁, j * x * j⁻¹ ∈ J₁ := by
    intro j hj x hx
    refine Subgroup.closure_induction (p := fun x _ => j * x * j⁻¹ ∈ J₁) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨hxJ, a, hxa⟩
      refine Subgroup.subset_closure ⟨J.mul_mem (J.mul_mem hj hxJ) (J.inv_mem hj), a, ?_⟩
      rw [conj_pow, hxa, mul_one, mul_inv_cancel]
    · simp
    · intro x y _ _ hx hy
      have := J₁.mul_mem hx hy
      rwa [show j * x * j⁻¹ * (j * y * j⁻¹) = j * (x * y) * j⁻¹ by group] at this
    · intro x _ hx
      have := J₁.inv_mem hx
      rwa [show (j * x * j⁻¹)⁻¹ = j * x⁻¹ * j⁻¹ by group] at this
  have hQn : Q.Normal := ⟨by
    rintro _ ⟨x, hx, rfl⟩ g
    obtain ⟨j, hjJ, rfl⟩ := hJe g
    exact ⟨j * x * j⁻¹, hconj j hjJ x hx, by simp⟩⟩
  obtain ⟨j, hjJ, hjσ⟩ := hJe σ
  obtain ⟨e, m, hm, hom⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos j).ne' 7 (by norm_num)
  have hjm : σ ^ m ∈ Q := by
    refine ⟨j ^ m, Subgroup.subset_closure ⟨J.pow_mem hjJ m, e, ?_⟩, by rw [map_pow, hjσ]⟩
    rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
  have hσm : σ ^ m ≠ 1 := fun h =>
    hm ((orderOf_eq_prime hσ7 hσ1).symm ▸ orderOf_dvd_of_pow_eq_one h)
  have : (Q.subgroupOf K).Normal := hQn.subgroupOf K
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q.subgroupOf K) with h | h
  · have hmem : (⟨σ ^ m, K.pow_mem hσK m⟩ : K) ∈ Q.subgroupOf K := hjm
    rw [h, Subgroup.mem_bot] at hmem
    exact absurd (congrArg Subtype.val hmem) hσm
  · intro k hk
    have : (⟨k, hk⟩ : K) ∈ Q.subgroupOf K := h ▸ Subgroup.mem_top _
    exact this

theorem exists_central_sylow_cover_centralizer {W : Type*} [Group W] [Finite W] {N : Subgroup W}
    [N.Normal]
    {n : ℕ} (hn : 8 ≤ n) (K : Subgroup (W ⧸ N)) (e : K ≃* alternatingGroup (Fin n))
    (T : Sylow 3 N) (hT : Open.pRank 3 ((T : Subgroup N).map N.subtype) ≤ 3) :
    ∃ (L : Subgroup W) (ψ : L →* alternatingGroup (Fin n)), Function.Surjective ψ ∧
      (∀ x : L, ∃ k : K, (k : W ⧸ N) = QuotientGroup.mk (x : W) ∧ e k = ψ x) ∧
      L ≤ Subgroup.centralizer (((T : Subgroup N).map N.subtype : Subgroup W) : Set W) ∧
      ∃ U : Sylow 3 ψ.ker, ∀ u : ψ.ker, u ∈ U → (u : L) ∈ Subgroup.center L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T' : Subgroup W := (T : Subgroup N).map N.subtype with hT'
  have hT3 : IsPGroup 3 T' := T.isPGroup'.map N.subtype
  set J : Subgroup W := Subgroup.normalizer (T' : Set W) with hJ
  have hJmap : J.map (QuotientGroup.mk' N) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    have hw : w ∈ J ⊔ N := Sylow.normalizer_sup_eq_top T ▸ Subgroup.mem_top w
    obtain ⟨j, hj, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hw
    exact ⟨j, hj, by rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff k).2 hk, mul_one]⟩
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using (by omega : 5 ≤ n))
  have : IsSimpleGroup K := e.isSimpleGroup
  obtain ⟨σ, hσ7, hσ1⟩ := AltLargePrime.exists_pow_seven_eq_one hn
  set J₇ : Subgroup W := Subgroup.closure {x : W | x ∈ J ∧ ∃ a : ℕ, x ^ 7 ^ a = 1} with hJ₇
  have hKJ : K ≤ J₇.map (QuotientGroup.mk' N) :=
    le_map_closure_sevenElements (QuotientGroup.mk' N) J hJmap K (σ := ((e.symm σ : K) : W ⧸ N))
      (e.symm σ).2 (by rw [← SubgroupClass.coe_pow, ← map_pow, hσ7, map_one, OneMemClass.coe_one])
      (fun h => hσ1 (by simpa using (OneMemClass.coe_eq_one.1 h : e.symm σ = 1)))
  have hJ₇C : J₇ ≤ Subgroup.centralizer (T' : Set W) :=
    (Subgroup.closure_le _).2 fun x ⟨hxJ, a, hxa⟩ =>
      mem_centralizer_of_pow_seven_pow hT3 hT hxa hxJ
  set L : Subgroup W := J₇ ⊓ K.comap (QuotientGroup.mk' N) with hL
  have hLK : ∀ x : L, QuotientGroup.mk' N (x : W) ∈ K := fun x => (Subgroup.mem_inf.1 x.2).2
  let ψ : L →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (((QuotientGroup.mk' N).comp L.subtype).codRestrict K hLK)
  have hψdef : ∀ x : L, ψ x = e ⟨QuotientGroup.mk' N (x : W), hLK x⟩ := fun x => rfl
  have hψ : Function.Surjective ψ := by
    intro a
    obtain ⟨x, hx, hxa⟩ := hKJ (e.symm a).2
    have hxL : x ∈ L := Subgroup.mem_inf.2 ⟨hx, by
      rw [Subgroup.mem_comap, hxa]
      exact (e.symm a).2⟩
    refine ⟨⟨x, hxL⟩, ?_⟩
    rw [hψdef]
    have : (⟨QuotientGroup.mk' N x, hLK ⟨x, hxL⟩⟩ : K) = e.symm a := Subtype.ext hxa
    change e ⟨QuotientGroup.mk' N x, _⟩ = a
    rw [this, MulEquiv.apply_symm_apply]
  have hker : ∀ u : ψ.ker, (u : W) ∈ N := by
    intro u
    have h1 : ψ u = 1 := u.2
    rw [hψdef, map_eq_one_iff _ e.injective] at h1
    exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val h1)
  obtain ⟨U⟩ : Nonempty (Sylow 3 ψ.ker) := Sylow.nonempty
  refine ⟨L, ψ, hψ, fun x => ⟨⟨QuotientGroup.mk' N (x : W), hLK x⟩, rfl, rfl⟩,
    inf_le_left.trans hJ₇C, U, ?_⟩
  let ε : ψ.ker →* N := (L.subtype.comp ψ.ker.subtype).codRestrict N hker
  have hU3 : IsPGroup 3 ((U : Subgroup ψ.ker).map ε) := U.isPGroup'.map ε
  have hnorm : (U : Subgroup ψ.ker).map ε ≤ Subgroup.normalizer (T : Set N) := by
    rintro _ ⟨v, hv, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1
      (hJ₇C (Subgroup.mem_inf.1 v.1.2).1) q.1 ⟨q, hq, rfl⟩)
  have hUT : (U : Subgroup ψ.ker).map ε ≤ T := fun z hz =>
    ((hU3.inf_normalizer_sylow T ▸ Subgroup.mem_inf.2 ⟨hz, hnorm hz⟩ :
      z ∈ (U : Subgroup ψ.ker).map ε ⊓ (T : Subgroup N))).2
  intro u hu
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hJ₇C (Subgroup.mem_inf.1 y.2).1) _
    ⟨ε u, hUT ⟨u, hu, rfl⟩, rfl⟩).symm

theorem exists_central_sylow_cover {W : Type*} [Group W] [Finite W] {N : Subgroup W} [N.Normal]
    {n : ℕ} (hn : 8 ≤ n) (K : Subgroup (W ⧸ N)) (e : K ≃* alternatingGroup (Fin n))
    (T : Sylow 3 N) (hT : Open.pRank 3 ((T : Subgroup N).map N.subtype) ≤ 3) :
    ∃ (L : Subgroup W) (ψ : L →* alternatingGroup (Fin n)), Function.Surjective ψ ∧
      (∀ x : L, ∃ k : K, (k : W ⧸ N) = QuotientGroup.mk (x : W) ∧ e k = ψ x) ∧
      ∃ U : Sylow 3 ψ.ker, ∀ u : ψ.ker, u ∈ U → (u : L) ∈ Subgroup.center L := by
  obtain ⟨L, ψ, hψ, hπ, -, hU⟩ := exists_central_sylow_cover_centralizer hn K e T hT
  exact ⟨L, ψ, hψ, hπ, hU⟩

open Equiv in
theorem exists_two_threeCycles {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α)
    (hS : 6 ≤ S.card) :
    ∃ x y : Perm α, x.IsThreeCycle ∧ y.IsThreeCycle ∧ x.support ⊆ S ∧ y.support ⊆ S ∧
      Disjoint x.support y.support := by
  obtain ⟨t, htS, htc⟩ := Finset.exists_subset_card_eq hS
  obtain ⟨t₁, ht₁, ht₁c⟩ := Finset.exists_subset_card_eq (s := t) (n := 3) (by omega)
  have ht₂c : (t \ t₁).card = 3 := by
    rw [Finset.card_sdiff_of_subset ht₁]
    omega
  have hcyc : ∀ u : Finset α, u.card = 3 → ∃ x : Perm α, x.IsThreeCycle ∧ x.support = u := by
    intro u hu
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hu
    have hsupp : (swap a b * swap b c).support = {a, b, c} :=
      Perm.support_swap_mul_swap (by simp [hab, hac, hbc])
    exact ⟨swap a b * swap b c, card_support_eq_three_iff.1 (hsupp ▸ hu), hsupp⟩
  obtain ⟨x, hx, hxs⟩ := hcyc t₁ ht₁c
  obtain ⟨y, hy, hys⟩ := hcyc (t \ t₁) ht₂c
  refine ⟨x, y, hx, hy, ?_, ?_, ?_⟩
  · rw [hxs]
    exact ht₁.trans htS
  · rw [hys]
    exact Finset.sdiff_subset.trans htS
  · rw [hxs, hys]
    exact Finset.disjoint_sdiff

end AltSevenPrime

namespace D2AltModel

open AltSurvivor Equiv

variable {X : Type} [Group X] {p : ℕ} {A X₀ K : Subgroup X}
  {e : K ≃* alternatingGroup (Fin (2 * p))}

theorem exists_four_cycles (Mo : D2AltModel p A X₀ K e) (hp : 6 ≤ p) :
    ∃ c : Fin 4 → alternatingGroup (Fin (2 * p)),
      (∀ i, (c i : Perm (Fin (2 * p))).IsThreeCycle) ∧
      (∀ i j, i ≠ j →
        Disjoint (c i : Perm (Fin (2 * p))).support (c j : Perm (Fin (2 * p))).support) ∧
      ∀ i, (c i : Perm (Fin (2 * p))) ∈ X₀.map Mo.ι := by
  obtain ⟨x₁, y₁, hx₁, hy₁, hx₁O, hy₁O, hd₁⟩ :=
    AltSevenPrime.exists_two_threeCycles Mo.O₁ (by rw [Mo.card₁]; exact hp)
  obtain ⟨x₂, y₂, hx₂, hy₂, hx₂O, hy₂O, hd₂⟩ :=
    AltSevenPrime.exists_two_threeCycles Mo.O₂ (by rw [Mo.card₂]; exact hp)
  let P : Fin 4 → Perm (Fin (2 * p)) := ![x₁, y₁, x₂, y₂]
  have hP : ∀ i, (P i).IsThreeCycle := by
    intro i
    fin_cases i
    exacts [hx₁, hy₁, hx₂, hy₂]
  have hcross : ∀ {u v : Perm (Fin (2 * p))}, u.support ⊆ Mo.O₁ → v.support ⊆ Mo.O₂ →
      Disjoint u.support v.support := fun hu hv => Mo.disjoint.mono hu hv
  have hPd : ∀ i j, i ≠ j → Disjoint (P i).support (P j).support := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact hd₁ | exact hd₁.symm | exact hd₂ | exact hd₂.symm
      | exact hcross hx₁O hx₂O | exact hcross hx₁O hy₂O
      | exact hcross hy₁O hx₂O | exact hcross hy₁O hy₂O
      | exact (hcross hx₁O hx₂O).symm | exact (hcross hx₁O hy₂O).symm
      | exact (hcross hy₁O hx₂O).symm | exact (hcross hy₁O hy₂O).symm
  have hPX : ∀ i, P i ∈ X₀.map Mo.ι := by
    intro i
    fin_cases i
    · exact Mo.altOn₁ (mem_altOn.2 ⟨(hx₁).sign, fun z hz =>
        Perm.notMem_support.1 fun h => hz (hx₁O h)⟩)
    · exact Mo.altOn₁ (mem_altOn.2 ⟨(hy₁).sign, fun z hz =>
        Perm.notMem_support.1 fun h => hz (hy₁O h)⟩)
    · exact Mo.altOn₂ (mem_altOn.2 ⟨(hx₂).sign, fun z hz =>
        Perm.notMem_support.1 fun h => hz (hx₂O h)⟩)
    · exact Mo.altOn₂ (mem_altOn.2 ⟨(hy₂).sign, fun z hz =>
        Perm.notMem_support.1 fun h => hz (hy₂O h)⟩)
  exact ⟨fun i => ⟨P i, Perm.mem_alternatingGroup.2 (hP i).sign⟩, hP, hPd, hPX⟩

end D2AltModel

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem pRank_three_le_three_of_map_le (hD1 : D1For G) (h : AGLPair p M H R) {Y : Subgroup H}
    (hY : Y.map H.subtype ≤ M) : Open.pRank 3 Y ≤ 3 := by
  by_contra hlt
  refine h.false_of_four_le_pRank hD1 Nat.prime_three (by norm_num) ?_
  exact (by omega : 4 ≤ Open.pRank 3 Y).trans
    ((SectionRank.pRank_le_map (by norm_num) H.subtype H.subtype_injective Y).trans
      (SectionRank.pRank_mono (by norm_num) (le_inf (Subgroup.map_subtype_le Y) hY)))

end AGLPair

section Seven

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.false_of_alt_seven_le [Fact p.Prime] (h : D2Escape p P M A H A)
    (hglob : AGLGlobal G) (hD1 : D1For G)
    (hRbar : (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* alternatingGroup (Fin (2 * p))) (hp7 : 7 ≤ p) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp5 : 5 ≤ p := by omega
  have hpair : AGLPair p M H A := (h.altData_of_alt hglob hRbar hK e hp5).pair
  set N : Subgroup H := primeComplementCore (G := H) p with hN
  have hNM : N.map H.subtype ≤ M :=
    (le_of_eq (CFSG.AGLEmbedding.glbPrimeCore_eq_primeComplementCoreOf p H).symm).trans
      h.primeCore_le
  have hNX : N ≤ (H ⊓ M).subgroupOf H := fun o ho =>
    Subgroup.mem_subgroupOf.mpr ⟨o.2, hNM ⟨o, ho, rfl⟩⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 N) := Sylow.nonempty
  have hT : Open.pRank 3 ((T : Subgroup N).map N.subtype) ≤ 3 :=
    hpair.pRank_three_le_three_of_map_le hD1
      ((Subgroup.map_mono (Subgroup.map_subtype_le _)).trans hNM)
  obtain ⟨L, ψ, hψ, hπ, U, hU⟩ :=
    AltSevenPrime.exists_central_sylow_cover (N := N) (by omega) K e T hT
  obtain ⟨Mo⟩ := hK.nonempty_altModel hp5 e
  obtain ⟨c, hc, hdisj, hcX⟩ := Mo.exists_four_cycles (by omega)
  have h4 := four_le_pRank_map_comap_of_central_sylow_alt ψ hψ U hU c hc hdisj
  have hclosure : Subgroup.closure (Set.range c) ≤
      ((((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' N)).map Mo.ι).comap
        (alternatingGroup (Fin (2 * p))).subtype :=
    (Subgroup.closure_le _).2 (Set.range_subset_iff.2 hcX)
  have hY : (((Subgroup.closure (Set.range c)).comap ψ).map L.subtype).map H.subtype ≤ M := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨k, hk1, hk2⟩ := hπ x
    have hkX : Mo.ι (k : H ⧸ N) ∈ (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' N)).map Mo.ι := by
      rw [Mo.ι_val k]
      exact hclosure (hk2 ▸ hx)
    obtain ⟨z, hz, hzk⟩ := hkX
    have hz' : z = (k : H ⧸ N) := Mo.injective hzk
    have hxX : QuotientGroup.mk' N (x : H) ∈ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' N) := by
      rw [QuotientGroup.mk'_apply, ← hk1, ← hz']
      exact hz
    have hxX' : (x : H) ∈ (H ⊓ M).subgroupOf H := by
      have := Subgroup.mem_comap.2 hxX
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hNX] at this
    exact (Subgroup.mem_subgroupOf.1 hxX').2
  have := hpair.pRank_three_le_three_of_map_le hD1 hY
  omega

end Seven

@[expose] def D2AltFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) [Fact p.Prime], p = 5 → ∀ (P : Sylow p G) (M A H : Subgroup G),
      D2Escape p P M A H A → D2EscapeMax p P M A → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* alternatingGroup (Fin (2 * p))) → False

theorem d2AltNoConfig_of_five (h5 : D2AltFive) : D2AltNoConfig := by
  intro G _ _ hglob hD1 p _ hp5 P M A H hesc hmax hβ Rbar K hRbar hK ⟨e⟩
  by_cases hp : p = 5
  · exact h5 G hglob hD1 p hp P M A H hesc hmax hβ Rbar K hRbar hK ⟨e⟩
  · have hp6 : p ≠ 6 := by
      rintro rfl
      exact absurd (Fact.out : Nat.Prime 6) (by norm_num)
    exact hesc.false_of_alt_seven_le hglob.toAGLGlobal hD1 hRbar hK e (by omega)

end CFSG.AGLEmbeddingD2
