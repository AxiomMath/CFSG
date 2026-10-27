module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
import CFSG.GroupTheory.LocalCores.MinimalNormal
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding Subgroup

section Irreducible

variable {X : Type} [Group X]

private abbrev IsMinNormal (K : Subgroup X) : Prop :=
  K.Normal ∧ K ≠ ⊥ ∧ ∀ M : Subgroup X, M.Normal → M ≤ K → M = ⊥ ∨ M = K

private theorem map_mul_aut (K : Subgroup X) (e₁ e₂ : MulAut X) :
    K.map (e₁ * e₂).toMonoidHom = (K.map e₂.toMonoidHom).map e₁.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem map_one_aut (K : Subgroup X) : K.map (1 : MulAut X).toMonoidHom = K := by
  ext y
  simp

private theorem IsMinNormal.map_aut {K : Subgroup X} (hK : IsMinNormal K) (e : MulAut X) :
    IsMinNormal (K.map e.toMonoidHom) := by
  obtain ⟨hn, hne, hmin⟩ := hK
  refine ⟨hn.map _ e.surjective,
    fun h => hne ((map_eq_bot_iff_of_injective _ e.injective).mp h), fun M hM hle => ?_⟩
  have h1 : M.comap e.toMonoidHom ≤ K := by
    rw [← comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective K]
    exact comap_mono hle
  have h2 : (M.comap e.toMonoidHom).map e.toMonoidHom = M :=
    map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective M
  rcases hmin _ (hM.comap _) h1 with h | h
  · left
    rw [← h2, h, Subgroup.map_bot]
  · right
    rw [← h2, h]

private theorem IsMinNormal.commute {K₁ K₂ : Subgroup X} (h₁ : IsMinNormal K₁)
    (h₂ : IsMinNormal K₂) (hne : K₁ ≠ K₂) {a b : X} (ha : a ∈ K₁) (hb : b ∈ K₂) :
    Commute a b := by
  have := h₁.1
  have := h₂.1
  exact CFSG.LocalCores.commute_of_normal_of_inf_eq_bot
    (CFSG.LocalCores.inf_eq_bot_of_minimal_normal h₁ h₂ hne) ha hb

private theorem isSolvable_of_irreducible (hEv : KFactCoprimeAutEvenCentralizer) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) [Finite X] (φ : MulAut X) (hφp : φ ^ p = 1)
    (hpX : ¬ p ∣ Nat.card X) (hfix : ∀ t : X, orderOf t = 2 → φ t ≠ t)
    (hcat : CatalogSimpleSections X)
    (hirr : ∀ N : Subgroup X, N.Normal → N.map φ.toMonoidHom ≤ N → N = ⊥ ∨ N = ⊤) :
    Group.IsSolvable X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hns
  have hXnt : Nontrivial X := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hns (Group.isSolvable_of_comm fun _ _ => Subsingleton.elim _ _)
  obtain ⟨K, ⟨hKn, hK1⟩, hKmin⟩ :=
    (Set.toFinite {M : Subgroup X | M.Normal ∧ M ≠ ⊥}).exists_minimal
      ⟨⊤, inferInstance, top_ne_bot⟩
  have hK : IsMinNormal K := ⟨hKn, hK1, fun M hM hle =>
    (em (M = ⊥)).imp id fun hM1 => le_antisymm hle (hKmin ⟨hM, hM1⟩ hle)⟩
  have hKi : ∀ i : ℕ, IsMinNormal (K.map (φ ^ i).toMonoidHom) := fun i => hK.map_aut _
  have hK0 : K.map (φ ^ 0).toMonoidHom = K := by rw [pow_zero, map_one_aut]
  have hKsucc : ∀ i : ℕ, K.map (φ ^ (i + 1)).toMonoidHom =
      (K.map (φ ^ i).toMonoidHom).map φ.toMonoidHom := fun i => by
    rw [pow_succ', map_mul_aut]
  have hnab : ¬ ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro hab
    have hcomm : ∀ i j : ℕ, ∀ a ∈ K.map (φ ^ i).toMonoidHom, ∀ b ∈ K.map (φ ^ j).toMonoidHom,
        a * b = b * a := by
      intro i j a ha b hb
      by_cases hij : K.map (φ ^ i).toMonoidHom = K.map (φ ^ j).toMonoidHom
      · rw [← hij] at hb
        obtain ⟨a', ha', rfl⟩ := ha
        obtain ⟨b', hb', rfl⟩ := hb
        rw [← map_mul, ← map_mul, hab a' ha' b' hb']
      · exact hKi i |>.commute (hKi j) hij ha hb
    have : ∀ i : ℕ, (K.map (φ ^ i).toMonoidHom).Normal := fun i => (hKi i).1
    set J : Subgroup X := ⨆ i : ℕ, K.map (φ ^ i).toMonoidHom with hJ
    have hJn : J.Normal := iSup_normal _
    have hJφ : J.map φ.toMonoidHom ≤ J := by
      rw [hJ, Subgroup.map_iSup]
      exact iSup_le fun i => (hKsucc i).symm ▸ le_iSup (fun i => K.map (φ ^ i).toMonoidHom) (i + 1)
    have hKJ : K ≤ J := hK0 ▸ le_iSup (fun i => K.map (φ ^ i).toMonoidHom) 0
    have hJtop : J = ⊤ := (hirr J hJn hJφ).resolve_left fun h => hK1 (le_bot_iff.mp (h ▸ hKJ))
    have hJc : J ≤ centralizer (J : Set X) := by
      refine iSup_le fun i => le_centralizer_iff.mpr (iSup_le fun j => fun b hb =>
        mem_centralizer_iff.mpr fun a ha => hcomm i j a ha b hb)
    exact hns (Group.isSolvable_of_comm fun a b =>
      (mem_centralizer_iff.mp (hJc (hJtop ▸ mem_top b)) a (hJtop ▸ mem_top a)))
  have hKc : ¬ K ≤ centralizer (K : Set X) := fun h =>
    hnab fun a ha b hb => (mem_centralizer_iff.mp (h hb) a ha)
  have hZ : K ⊓ centralizer (K : Set X) = ⊥ :=
    (hK.2.2 _ inferInstance inf_le_left).resolve_right fun h => hKc (h.symm.le.trans inf_le_right)
  have hperf : ⁅K, K⁆ = K := (hK.2.2 _ inferInstance (commutator_le_left K K)).resolve_left
    fun h => hKc (commutator_eq_bot_iff_le_centralizer.mp h)
  have hK2 : 2 ∣ Nat.card K := by
    by_contra h
    have : Group.IsPerfect K := isPerfect_iff.mpr hperf
    have : Nontrivial K := (nontrivial_iff_ne_bot K).mpr hK1
    exact Group.IsPerfect.not_isSolvable K
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)))
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' 2 hK2
  set t : X := (t₀ : X) with ht
  have htK : t ∈ K := t₀.2
  have ht2 : orderOf t = 2 := by rw [ht, Subgroup.orderOf_coe, ht₀]
  have hts : t ^ 2 = 1 := ht2 ▸ pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; exact absurd ht2 (by norm_num)
  by_cases hinv : K.map φ.toMonoidHom ≤ K
  ·
    have hKtop : K = ⊤ := (hirr K hKn hinv).resolve_left hK1
    have hsimple : IsSimpleGroup X := ⟨fun H _ => (em (H = ⊥)).imp id fun hH1 =>
      ((hK.2.2 H inferInstance (hKtop ▸ le_top)).resolve_left hH1).trans hKtop⟩
    have hnab' : ∃ a b : X, a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact hnab fun a _ b _ => h a b
    have hcatX : IsCatalogGroup X :=
      hcat.surjective_image ⊤ (⊤ : Subgroup X).subtype (fun y => ⟨⟨y, mem_top y⟩, rfl⟩) hnab'
    have hφ1 : φ ≠ 1 := fun h => hfix t ht2 (by rw [h]; rfl)
    obtain ⟨s, hs2, hsφ⟩ := hEv p hp.out hp2 X hsimple hnab' hcatX hpX φ hφp hφ1
    exact hfix s hs2 hsφ
  ·
    have hdist : ∀ d : ℕ, 0 < d → d < p → K.map (φ ^ d).toMonoidHom ≠ K := by
      intro d hd0 hdp hd
      have hcop : d.Coprime (orderOf φ) := by
        rcases (Nat.dvd_prime hp.out).mp (orderOf_dvd_of_pow_eq_one hφp) with h | h
        · rw [h]
          exact Nat.coprime_one_right d
        · rw [h]
          exact (Nat.coprime_of_lt_prime hd0.ne' hdp hp.out).symm
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      have hpow : ∀ k : ℕ, K.map ((φ ^ d) ^ k).toMonoidHom = K := by
        intro k
        induction k with
        | zero => rw [pow_zero, map_one_aut]
        | succ k ihk => rw [pow_succ, map_mul_aut, hd, ihk]
      exact hinv (by rw [← hm, hpow m])
    have hdist2 : ∀ i j : ℕ, i < j → j < p →
        K.map (φ ^ i).toMonoidHom ≠ K.map (φ ^ j).toMonoidHom := by
      intro i j hij hjp h
      have hj : φ ^ j = φ ^ i * φ ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij.le]
      rw [hj, map_mul_aut] at h
      exact hdist (j - i) (Nat.sub_pos_of_lt hij) (by omega)
        ((map_injective (f := (φ ^ i).toMonoidHom) (φ ^ i).injective) h).symm
    set c : ℕ → X := fun i => (φ ^ i) t with hc
    have hcmem : ∀ i, c i ∈ K.map (φ ^ i).toMonoidHom := fun i => mem_map_of_mem _ htK
    have hcsq : ∀ i, c i ^ 2 = 1 := fun i => by
      simp only [hc]
      rw [← map_pow, hts, map_one]
    have hccomm : ∀ i j : ℕ, i < p → j < p → i ≠ j → Commute (c i) (c j) := by
      intro i j hip hjp hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact (hKi i).commute (hKi j) (hdist2 i j h hjp) (hcmem i) (hcmem j)
      · exact (hKi i).commute (hKi j) (hdist2 j i h hip).symm (hcmem i) (hcmem j)
    have hcK : ∀ i, 0 < i → i < p → c i ∈ centralizer (K : Set X) := by
      intro i hi0 hip
      refine mem_centralizer_iff.mpr fun k hk => ?_
      have h := (hKi i).commute (hKi 0) (hK0.symm ▸ hdist i hi0 hip) (hcmem i)
        (hK0.symm ▸ hk)
      exact h.eq.symm
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
    set w : X := ((List.range q).map fun i => c (i + 1)).prod with hw
    have hwK : w ∈ centralizer (K : Set X) := by
      refine Subgroup.list_prod_mem _ fun y hy => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      exact hcK (i + 1) (Nat.succ_pos i) (by rw [List.mem_range] at hi; omega)
    set s : X := ((List.range p).map c).prod with hs
    have hc0 : c 0 = t := by simp [hc]
    have hcp : c p = t := by simp [hc, hφp]
    have hst : s = t * w := by
      rw [hs, hq, List.prod_range_succ', hc0]
    have hφc : ∀ i, φ (c i) = c (i + 1) := fun i => by
      simp only [hc]
      rw [pow_succ', MulAut.mul_apply]
    have hφs : φ s = w * t := by
      rw [hs, map_list_prod, List.map_map]
      have hfun : (⇑φ ∘ c) = fun i => c (i + 1) := funext hφc
      rw [hfun, hq, List.prod_range_succ, ← hq, hcp]
    have htw : t * w = w * t := mem_centralizer_iff.mp hwK t htK
    have hsfix : φ s = s := by rw [hφs, hst, htw]
    have hs1 : s ≠ 1 := by
      intro h
      rw [hst] at h
      have htw' : t = w⁻¹ := eq_inv_of_mul_eq_one_left h
      have hwi : w⁻¹ ∈ centralizer (K : Set X) := inv_mem hwK
      rw [← htw'] at hwi
      have hmem : t ∈ K ⊓ centralizer (K : Set X) := ⟨htK, hwi⟩
      rw [hZ, mem_bot] at hmem
      exact ht1 hmem
    have key : ∀ n, n ≤ p → ((List.range n).map c).prod ^ 2 = 1 ∧
        ∀ j, n ≤ j → j < p → Commute ((List.range n).map c).prod (c j) := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ihn =>
        intro hn
        obtain ⟨ih1, ih2⟩ := ihn (by omega)
        rw [List.prod_range_succ]
        have hcn : Commute ((List.range n).map c).prod (c n) := ih2 n le_rfl (by omega)
        refine ⟨by rw [hcn.mul_pow, ih1, hcsq, one_mul], fun j hj hjp => ?_⟩
        exact (ih2 j (by omega) hjp).mul_left (hccomm n j (by omega) hjp (by omega))
    have hs2 : s ^ 2 = 1 := (key p le_rfl).1
    exact hfix s (orderOf_eq_prime hs2 hs1) hsfix

end Irreducible

section Reducible

private theorem exists_commute_mk_eq {B : Type} [Group B] [Finite B] {p : ℕ} (hp : p.Prime)
    (O : Subgroup B) [O.Normal] (hO : ¬ p ∣ Nat.card O) {b y : B} (hb : b ^ p = 1)
    (hy : Commute (QuotientGroup.mk' O y) (QuotientGroup.mk' O b)) :
    ∃ c : B, QuotientGroup.mk' O c = QuotientGroup.mk' O y ∧ Commute c b := by
  have hZ : IsPGroup p (zpowers b) := by
    rintro ⟨g, hg⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    rw [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
  obtain ⟨c, hc, hcfix⟩ := @CFSG.RankThreeCoreUniqueness.Helpers.coprime_pGroup_fixed_lift
    (zpowers b) B (B ⧸ O) _ _ _ _
    (CFSG.RankThreeCoreUniqueness.Helpers.multiplicativeActionOfMulAutHom
      (MulAut.conj.comp (zpowers b).subtype))
    (CFSG.RankThreeCoreUniqueness.Helpers.multiplicativeActionOfMulAutHom
      (MulAut.conj.comp ((QuotientGroup.mk' O).comp (zpowers b).subtype)))
    p hp hZ (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
    (fun a z => by
      change QuotientGroup.mk' O ((a : B) * z * (a : B)⁻¹) =
        QuotientGroup.mk' O a * QuotientGroup.mk' O z * (QuotientGroup.mk' O a)⁻¹
      rw [map_mul, map_mul, map_inv])
    (by rwa [QuotientGroup.ker_mk', Nat.Prime.coprime_iff_not_dvd hp])
    (QuotientGroup.mk' O y)
    (fun a => by
      change QuotientGroup.mk' O a * QuotientGroup.mk' O y * (QuotientGroup.mk' O a)⁻¹ =
        QuotientGroup.mk' O y
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp a.2
      have h : Commute (QuotientGroup.mk' O a) (QuotientGroup.mk' O y) := by
        rw [← hk, map_zpow]
        exact hy.symm.zpow_left k
      rw [h.eq, mul_inv_cancel_right])
  refine ⟨c, hc, ?_⟩
  have h := hcfix ⟨b, mem_zpowers b⟩
  change b * c * b⁻¹ = c at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

private theorem isSolvable_of_reducible {p : ℕ} [hp : Fact p.Prime] {A : Type} [Group A]
    [Finite A] {X : Subgroup A} {x : A} (hxX : x ∈ normalizer (X : Set A)) (hxp : x ^ p = 1)
    (hpX : ¬ p ∣ Nat.card X)
    (hodd : ¬ 2 ∣ Nat.card (X ⊓ centralizer ({x} : Set A) : Subgroup A))
    (hcat : CatalogSimpleSections X)
    (ih : ∀ {A' : Type} [Group A'] [Finite A'] {X' : Subgroup A'} {x' : A'},
      Nat.card X' < Nat.card X → x' ∈ normalizer (X' : Set A') → x' ^ p = 1 →
      ¬ p ∣ Nat.card X' → ¬ 2 ∣ Nat.card (X' ⊓ centralizer ({x'} : Set A') : Subgroup A') →
      CatalogSimpleSections X' → Group.IsSolvable X')
    {N : Subgroup X} (hNn : N.Normal)
    (hNφ : N.map (X.normalizerMonoidHom ⟨x, hxX⟩).toMonoidHom ≤ N) (hN1 : N ≠ ⊥)
    (hNtop : N ≠ ⊤) : Group.IsSolvable X := by
  set φ : MulAut X := X.normalizerMonoidHom ⟨x, hxX⟩
  set N' : Subgroup A := N.map X.subtype with hN'
  have hN'X : N' ≤ X := map_subtype_le N
  have hcardN' : Nat.card N' = Nat.card N := card_map_of_injective X.subtype_injective
  have hmemN' : ∀ y : X, (y : A) ∈ N' ↔ y ∈ N := fun y =>
    ⟨fun ⟨z, hz, hzy⟩ => (X.subtype_injective hzy) ▸ hz, fun h => mem_map_of_mem _ h⟩
  have hXN' : X ≤ normalizer (N' : Set A) := by
    rw [← normal_subgroupOf_iff_le_normalizer hN'X]
    have h : N'.subgroupOf X = N := by
      ext y
      rw [mem_subgroupOf]
      exact hmemN' y
    rw [h]
    exact hNn
  have hφN : N.map φ.toMonoidHom = N :=
    eq_of_le_of_card_ge hNφ (card_map_of_injective φ.injective).ge
  have hxN' : x ∈ normalizer (N' : Set A) := by
    rw [mem_normalizer_iff_map_conj_eq]
    calc N'.map (MulAut.conj x : A →* A) = (N.map φ.toMonoidHom).map X.subtype := by
          rw [hN', map_map, map_map]
          congr 1
      _ = N' := by rw [hφN]
  have hNlt : Nat.card N' < Nat.card X := by
    rw [hcardN', ← card_top (G := X)]
    exact card_lt_of_lt (lt_top_iff_ne_top.mpr hNtop)
  have hN'sol : Group.IsSolvable N' := by
    refine ih hNlt hxN' hxp (fun h => hpX (h.trans (card_dvd_of_le hN'X)))
      (fun h => hodd (h.trans (card_dvd_of_le (inf_le_inf_right _ hN'X)))) ?_
    exact (hcat.subgroup N).of_surjective
      (N.equivMapOfInjective X.subtype X.subtype_injective).toMonoidHom (MulEquiv.surjective _)
  have hNsol : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (f := (N.equivMapOfInjective X.subtype X.subtype_injective).toMonoidHom) (MulEquiv.injective _)
  set B : Subgroup A := normalizer (N' : Set A)
  have hxB : x ∈ B := hxN'
  set O : Subgroup B := N'.subgroupOf B with hO
  have hOn : O.Normal := normal_in_normalizer
  set π : B →* B ⧸ O := QuotientGroup.mk' O with hπ
  set X' : Subgroup (B ⧸ O) := (X.subgroupOf B).map π
  set x' : B ⧸ O := π ⟨x, hxB⟩ with hx'
  have hcardO : Nat.card O = Nat.card N' :=
    Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv
  have hcardXB : Nat.card (X.subgroupOf B) = Nat.card X :=
    Nat.card_congr (subgroupOfEquivOfLe hXN').toEquiv
  let g : X →* X' := (π.subgroupMap (X.subgroupOf B)).comp
    (subgroupOfEquivOfLe hXN').symm.toMonoidHom
  have hg : Function.Surjective g := (π.subgroupMap_surjective _).comp (MulEquiv.surjective _)
  have hgker : ∀ y : X, g y = 1 → y ∈ N := by
    intro y hy
    have h1 : π ⟨y, hXN' y.2⟩ = 1 := congrArg Subtype.val hy
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO, mem_subgroupOf] at h1
    exact (hmemN' y).mp h1
  have hNker : N ≤ g.ker := fun y hy => by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change π ⟨y, hXN' y.2⟩ = 1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO, mem_subgroupOf]
    exact (hmemN' y).mpr hy
  have hlt : Nat.card X' < Nat.card X := by
    have h1 := card_mul_index g.ker
    rw [index_ker, MonoidHom.range_eq_top.mpr hg, card_top] at h1
    have h2 := (one_lt_card_iff_ne_bot g.ker).mpr fun h => hN1 (le_bot_iff.mp (h ▸ hNker))
    have h3 : 0 < Nat.card X' := Nat.card_pos
    nlinarith
  have hxXB : (⟨x, hxB⟩ : B) ∈ normalizer ((X.subgroupOf B : Subgroup B) : Set B) := by
    rw [mem_normalizer_iff]
    intro h
    rw [mem_subgroupOf, mem_subgroupOf]
    exact hxX h
  have hx'X' : x' ∈ normalizer (X' : Set (B ⧸ O)) := le_normalizer_map π (mem_map_of_mem π hxXB)
  have hxBp : (⟨x, hxB⟩ : B) ^ p = 1 := Subtype.ext (by simp [hxp])
  have hx'p : x' ^ p = 1 := by rw [hx', ← map_pow, hxBp, map_one]
  have hpX' : ¬ p ∣ Nat.card X' := fun h =>
    hpX (hcardXB ▸ h.trans (card_map_dvd (X.subgroupOf B) π))
  have hcent : X' ⊓ centralizer ({x'} : Set (B ⧸ O)) ≤
      ((X ⊓ centralizer ({x} : Set A)).subgroupOf B).map π := by
    rintro _ ⟨⟨b, hbX, rfl⟩, hbc⟩
    have hcomm : Commute (π b) x' := mem_centralizer_singleton_iff.mp hbc
    obtain ⟨c, hc, hcx⟩ := exists_commute_mk_eq hp.out O
      (by rw [hcardO]; exact fun h => hpX (h.trans (card_dvd_of_le hN'X))) hxBp hcomm
    refine ⟨c, mem_subgroupOf.mpr ⟨?_, ?_⟩, hc⟩
    · have h1 : c⁻¹ * b ∈ O := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hc
        exact QuotientGroup.eq.mp hc
      have h2 : ((c⁻¹ * b : B) : A) ∈ X := hN'X (mem_subgroupOf.mp h1)
      have h3 : (b : A) ∈ X := hbX
      have h4 : (c : A) = b * ((c⁻¹ * b : B) : A)⁻¹ := by simp
      rw [h4]
      exact X.mul_mem h3 (X.inv_mem h2)
    · exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcx.eq)
  have hodd' : ¬ 2 ∣ Nat.card (X' ⊓ centralizer ({x'} : Set (B ⧸ O)) : Subgroup (B ⧸ O)) := by
    intro h
    apply hodd
    have h1 := h.trans ((card_dvd_of_le hcent).trans (card_map_dvd _ π))
    rwa [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hXN')).toEquiv] at h1
  have hX'sol : Group.IsSolvable X' := ih hlt hx'X' hx'p hpX' hodd' (hcat.of_surjective g hg)
  exact Group.isSolvable_of_ker_le_range N.subtype g fun y hy => ⟨⟨y, hgker y hy⟩, rfl⟩

end Reducible

private theorem isSolvable_of_card_eq (hEv : KFactCoprimeAutEvenCentralizer) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ) :
    ∀ {A : Type} [Group A] [Finite A] {X : Subgroup A} {x : A}, Nat.card X = n →
      x ∈ normalizer (X : Set A) → x ^ p = 1 → ¬ p ∣ Nat.card X →
      ¬ 2 ∣ Nat.card (X ⊓ centralizer ({x} : Set A) : Subgroup A) →
      CatalogSimpleSections X → Group.IsSolvable X := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ X x hn hxX hxp hpX hodd hcat
  set φ : MulAut X := X.normalizerMonoidHom ⟨x, hxX⟩ with hφ
  have hφx : ∀ y : X, ((φ y : X) : A) = x * y * x⁻¹ := fun y =>
    normalizerMonoidHom_apply_apply_coe _ _ _
  by_cases hred : ∃ N : Subgroup X, N.Normal ∧ N.map φ.toMonoidHom ≤ N ∧ N ≠ ⊥ ∧ N ≠ ⊤
  · obtain ⟨N, hNn, hNφ, hN1, hNtop⟩ := hred
    exact isSolvable_of_reducible hxX hxp hpX hodd hcat
      (fun hlt => ih _ (hn ▸ hlt) rfl) hNn hNφ hN1 hNtop
  · push Not at hred
    have hφp : φ ^ p = 1 := by
      have h : (⟨x, hxX⟩ : normalizer (X : Set A)) ^ p = 1 := Subtype.ext (by simp [hxp])
      rw [hφ, ← map_pow, h, map_one]
    refine isSolvable_of_irreducible hEv hp2 φ hφp hpX (fun t ht2 hft => hodd ?_) hcat
      fun N hN hNφ => (em (N = ⊥)).imp id (hred N hN hNφ)
    have hmem : (t : A) ∈ X ⊓ centralizer ({x} : Set A) := by
      refine ⟨t.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have h := congrArg Subtype.val hft
      rw [hφx] at h
      calc (t : A) * x = x * t * x⁻¹ * x := by rw [h]
        _ = x * t := by group
    have h := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [Subgroup.orderOf_coe, ht2] at h

theorem oddCentralizerSolvable_holds :
    KFactCoprimeAutEvenCentralizer →
    ∀ {A : Type} [Group A] [Finite A] {p : ℕ} [Fact p.Prime], p ≠ 2 →
      ∀ {X : Subgroup A} {x : A}, x ∈ normalizer (X : Set A) → x ^ p = 1 →
        ¬ p ∣ Nat.card X → Odd (Nat.card (X ⊓ centralizer ({x} : Set A) : Subgroup A)) →
        CatalogSimpleSections X → Group.IsSolvable X := by
  intro hEv A _ _ p _ hp2 X x hxX hxp hpX hodd hcat
  exact isSolvable_of_card_eq hEv hp2 _ rfl hxX hxp hpX
    (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)) hcat

end CFSG.LocalAnalysis.RankThreeTheoremC
