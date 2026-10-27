module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Setting
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs
public import CFSG.CGT.PushingUpLit.LIT.Foote.L52Pair

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.AS76b (oUpperTwoPrime)
open CFSG.ComponentClassification.AschbacherTheorem3 (Theorem3Statement)
open CFSG.Open (IsElemAbelian fusionStronglyEmbedded standardComponentOddCore)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace QBlock

variable {K : Subgroup G}

theorem ne_bot (h : QBlock K) : K ≠ ⊥ := fun hK =>
  blockU_ne_bot_of_short h.short (le_bot_iff.1 (hK ▸ blockU_le K))

theorem even_card (h : QBlock K) : Even (Nat.card K) := by
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 h.ne_bot
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 h.perfect
  exact even_iff_two_dvd.2 ((by norm_num : 2 ∣ 4).trans four_dvd_card_of_perfect)

theorem isElemAbelian_blockU (h : QBlock K) : IsElemAbelian 2 (blockU K) :=
  ⟨⟨⟨fun a b => Subtype.ext (h.blockU_comm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => by
    rw [pow_two]
    exact h.blockU_sq_eq_one x hx⟩

theorem sylow_not_comm (h : QBlock K) {R : Subgroup G} (hR : IsSylowOf 2 R K) :
    ¬ ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
  intro hcomm
  have hVR : blockU K ≤ R :=
    QBlock.le_of_isPGroup_normal' hR (blockU_le K) (le_normalizer_blockU K) h.isPGroup_blockU
  have hKV : K ≤ Subgroup.normalizer (blockU K : Set G) := le_normalizer_blockU K
  have hRC : R ≤ K ⊓ Subgroup.centralizer (blockU K : Set G) :=
    le_inf hR.le fun x hx => Subgroup.mem_centralizer_iff.2 fun v hv => hcomm v (hVR hv) x hx
  have heq := eq_of_isSylowOf_le h.perfect (inf_le_left : K ⊓ Subgroup.centralizer
    (blockU K : Set G) ≤ K) (conj_mem_inf_centralizer hKV) hR hRC
  have hKC : K ≤ Subgroup.centralizer (blockU K : Set G) := by
    intro x hx
    rw [← heq] at hx
    exact (Subgroup.mem_inf.1 hx).2
  have hcom : ⁅K, blockU K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hKC
  rw [Subgroup.commutator_comm, h.blockU_stable] at hcom
  exact blockU_ne_bot_of_short h.short hcom

end QBlock

theorem le_pRank_of_isElemAbelian {R E : Subgroup G} {k : ℕ} (hER : E ≤ R)
    (hE : IsElemAbelian 2 E) (hk : Nat.card E = 2 ^ k) : k ≤ CFSG.Open.pRank 2 R :=
  CFSG.SectionRank.le_pRank (by norm_num) hER hE hk

omit [Finite G] in
theorem mem_normalizer_zpowers {t k : G} (hk : k * t = t * k) :
    k ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  have hc : Commute t k := hk.symm
  exact (hc.zpow_left i).eq

section
variable {M J : Subgroup G}

theorem conj_le_normalizer (h3 : Theorem3Statement) (hJ : QBlock J) (hJt : TightlyEmbedded J)
    {g : G} (heven : Even (Nat.card ↥(rightConjugate J g ⊓ Subgroup.normalizer (J : Set G)))) :
    rightConjugate J g ≤ Subgroup.normalizer (J : Set G) := by
  by_cases hg : g ∈ Subgroup.normalizer (J : Set G)
  · rw [(rightConjugate_eq_self_iff J g).2 hg]
    exact Subgroup.le_normalizer
  · have hcomm := commutator_conj_eq_bot h3 hJ hJt hg heven
    rw [Subgroup.commutator_comm] at hcomm
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm).trans
      (Subgroup.centralizer_le_normalizer _)

namespace CE

variable (c : CE G M J)
include c

theorem tightlyEmbedded_of
    (hno : ∀ m ∈ M, rightConjugate J m ≠ J → Odd (Nat.card ↥(J ⊓ rightConjugate J m))) :
    TightlyEmbedded J := by
  refine ⟨c.block.even_card, fun g hg => ?_⟩
  by_contra hodd
  have heven : Even (Nat.card ↥(J ⊓ rightConjugate J g)) := Nat.not_odd_iff_even.1 hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(J ⊓ rightConjugate J g)) 2
    (even_iff_two_dvd.1 heven)
  have htJ : (x : G) ∈ J := (Subgroup.mem_inf.1 x.2).1
  have htJg : (x : G) ∈ rightConjugate J g := (Subgroup.mem_inf.1 x.2).2
  have ht2 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  set t : G := (x : G) with ht
  obtain ⟨m, hm, hne⟩ := c.exists_conj_ne
  have hcomm := c.commutator_conj_eq_bot hm hne
  have hJC : J ≤ Subgroup.centralizer ((rightConjugate J m : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hcen : ∀ j ∈ J, ∀ k ∈ rightConjugate J m, k * j = j * k := fun j hj k hk =>
    Subgroup.mem_centralizer_iff.1 (hJC hj) k hk
  have hA : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; simp)
  have hA1 : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at ht2
    omega
  have hK : rightConjugate J m ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
    fun k hk => mem_normalizer_zpowers (hcen t htJ k hk)
  have hM1 := c.normalizer_le hA hA1 hm hK
  have hKg : rightConjugate J (m * g) ≤ Subgroup.normalizer
      ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    have hgt : g * t * g⁻¹ ∈ J := by
      rw [mem_rightConjugate_iff] at htJg
      exact htJg
    have hy' : g * y * g⁻¹ ∈ rightConjugate J m := by
      rw [mem_rightConjugate_iff]
      have e : m * (g * y * g⁻¹) * m⁻¹ = (m * g) * y * (m * g)⁻¹ := by group
      rw [e]
      exact hy
    have h1 := hcen _ hgt _ hy'
    refine mem_normalizer_zpowers ?_
    have h2 : g * (y * t) * g⁻¹ = g * (t * y) * g⁻¹ := by
      calc g * (y * t) * g⁻¹ = (g * y * g⁻¹) * (g * t * g⁻¹) := by group
        _ = (g * t * g⁻¹) * (g * y * g⁻¹) := h1
        _ = g * (t * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hmg : m * g ∈ M := c.mem_of_conj_le ((hKg.trans hM1))
  have hgM : g ∈ M := by
    have := M.mul_mem (M.inv_mem hm) hmg
    simpa using this
  have hne' : rightConjugate J g ≠ J := fun h => hg ((rightConjugate_eq_self_iff J g).1 h)
  exact (Nat.not_even_iff_odd.2 (hno g hgM hne')) heven

theorem lemma_5_2 (h3 : Theorem3Statement) (h1 : Asc76Theorem1) :
    ∃ m ∈ M, rightConjugate J m ≠ J ∧ Even (Nat.card ↥(J ⊓ rightConjugate J m)) := by
  by_contra hno
  push Not at hno
  have hno' : ∀ m ∈ M, rightConjugate J m ≠ J →
      Odd (Nat.card ↥(J ⊓ rightConjugate J m)) := fun m hm hne =>
    Nat.not_even_iff_odd.1 (hno m hm hne)
  have hJt := c.tightlyEmbedded_of hno'
  have := c.simple
  have hJ := c.block
  have hnc : Subgroup.normalClosure (J : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (J : Set G)) with h | h
    · exfalso
      apply hJ.ne_bot
      rw [eq_bot_iff]
      intro x hx
      have := Subgroup.subset_normalClosure hx
      rw [h] at this
      exact this
    · exact h
  have hup : oUpperTwoPrime J = J := by
    have hS : ∀ g ∈ J, ∀ n ∈ oUpperTwoPrime J, g * n * g⁻¹ ∈ oUpperTwoPrime J := by
      intro g hg n hn
      induction hn using Subgroup.closure_induction with
      | mem x hx =>
        apply Subgroup.subset_closure
        obtain ⟨hxJ, k, hk⟩ := hx
        refine ⟨J.mul_mem (J.mul_mem hg hxJ) (J.inv_mem hg), k, ?_⟩
        rw [conj_pow, hk]
        group
      | one => simp
      | mul x y _ _ hx hy =>
        have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hx hy
      | inv x _ hx =>
        have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ hx
    exact eq_of_forall_isTwoElement_mem hJ.perfect
      (Subgroup.closure_le _ |>.2 fun x hx => hx.1) hS
      fun g hg h2 => Subgroup.subset_closure ⟨hg, h2⟩
  have hodd : standardComponentOddCore G = ⊥ := by
    refine sSup_eq_bot.2 fun N hN => ?_
    obtain ⟨hNn, hNodd⟩ := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hNodd
      have hJG : Even (Nat.card G) := by
        have h2 : 2 ∣ Nat.card J := even_iff_two_dvd.1 hJ.even_card
        exact even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le (le_top : J ≤ ⊤) |>.trans
          (by rw [Subgroup.card_top])))
      exact (Nat.not_even_iff_odd.2 hNodd) hJG
  have hstar : ∀ g : G, Even (Nat.card ↥(rightConjugate J g ⊓ Subgroup.normalizer (J : Set G))) →
      SylowNormalizes (rightConjugate J g) J := fun g hg => by
    obtain ⟨S, hS⟩ := exists_isSylowOf 2 (rightConjugate J g)
    exact ⟨S, hS, hS.le.trans (conj_le_normalizer h3 hJ hJt hg)⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 J
  have hrank : 1 < CFSG.Open.pRank 2 R := by
    have hVR : blockU J ≤ R :=
      QBlock.le_of_isPGroup_normal' hR (blockU_le J) (le_normalizer_blockU J) hJ.isPGroup_blockU
    obtain ⟨k, hk⟩ := hJ.isPGroup_blockU.exists_card_eq
    have h8 := hJ.eight_le_card_blockU
    have hk3 : 3 ≤ k := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have := le_pRank_of_isElemAbelian hVR hJ.isElemAbelian_blockU hk
    omega
  rcases h1 G J hJt hnc hup hodd hstar R hR hrank with htop | habel | ⟨-, hse⟩
  · exact c.ne_top (top_le_iff.1 (htop ▸ c.le))
  · have := habel.1
    exact hJ.sylow_not_comm hR fun x hx y hy => setLike_mul_comm hx hy
  · obtain ⟨m, hm, hne⟩ := c.exists_conj_ne
    have hcomm := c.commutator_conj_eq_bot hm hne
    have hJC : J ≤ Subgroup.centralizer ((rightConjugate J m : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hmN : m ∉ Subgroup.normalizer (J : Set G) := fun h =>
      hne ((rightConjugate_eq_self_iff J m).2 h)
    have hodd2 := hse.2.2 m hmN
    have hJle : J ≤ Subgroup.normalizer (J : Set G) ⊓
        (Subgroup.normalizer (J : Set G)).map (MulAut.conj m⁻¹).toMonoidHom := by
      refine le_inf Subgroup.le_normalizer fun x hx => ?_
      show x ∈ rightConjugate (Subgroup.normalizer (J : Set G)) m
      rw [mem_rightConjugate_iff]
      exact mem_normalizer_rightConjugate.1
        (Subgroup.centralizer_le_normalizer _ (hJC hx))
    have h2 : 2 ∣ Nat.card ↥(Subgroup.normalizer (J : Set G) ⊓
        (Subgroup.normalizer (J : Set G)).map (MulAut.conj m⁻¹).toMonoidHom) :=
      (even_iff_two_dvd.1 hJ.even_card).trans (Subgroup.card_dvd_of_le hJle)
    exact (Nat.not_even_iff_odd.2 hodd2) (even_iff_two_dvd.2 h2)

theorem exists_involution_center (h3 : Theorem3Statement) (h1 : Asc76Theorem1) :
    ∃ z ∈ J, orderOf z = 2 ∧ ∀ j ∈ J, z * j = j * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hne, heven⟩ := c.lemma_5_2 h3 h1
  have hcomm := c.commutator_conj_eq_bot hm hne
  rw [Subgroup.commutator_comm] at hcomm
  have hJC : rightConjugate J m ≤ Subgroup.centralizer (J : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(J ⊓ rightConjugate J m)) 2
    (even_iff_two_dvd.1 heven)
  refine ⟨(x : G), (Subgroup.mem_inf.1 x.2).1, by rw [Subgroup.orderOf_coe]; exact hx,
    fun j hj => ?_⟩
  exact (Subgroup.mem_centralizer_iff.1 (hJC (Subgroup.mem_inf.1 x.2).2) j hj).symm

end CE

end

end CFSG.CGT.PushingUpLit.LIT.Foote
