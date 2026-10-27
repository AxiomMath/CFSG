module

public import CFSG.CGT.PushingUpLit.SolKNA.SzU3
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22Weak
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
import CFSG.RankThree.GF2n.Tim78Normal

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (exists_isSylowOf_le IsDihedralTwoGroup
  rightConjugate_le_rightConjugate exists_rightConjugate_eq_of_isSylowOf)
open CFSG.ComponentClassification.AS76b (oUpperTwoPrime oddCoreIn oddCoreIn_le odd_card_oddCoreIn
  normalizer_le_normalizer_oddCoreIn tightlyEmbedded_rightConjugate)
open CFSG.ComponentClassification.Asc76 (Asc76Lemma22 Asc76Theorem3Large IsSzOrU3)
open CFSG.ComponentClassification.Asc76.Lemma22 (weakClosure)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open CFSG.Assembly (pCoreOf)
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup IsTI)
open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome STSetting sylowImg IsCommSubgroup)

section TI

variable {G : Type} [Group G] [Finite G]

open CFSG.LieType.BorelTits in
theorem isTI_of_normal_le_pCoreOf {K B : Subgroup G} (hK : TightlyEmbedded K)
    (hB : B ≤ pCoreOf 2 K)
    (hBM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (B : Set G)) : IsTI B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 B := (pCoreOf_isPGroup 2 K).to_le hB
  have hBK : B ≤ K := hB.trans (pCoreOf_le 2 K)
  intro g
  by_cases hg : g ∈ Subgroup.normalizer (K : Set G)
  · right
    rw [conjSubgroup_eq_self_iff.mpr (hBM hg), inf_idem]
  · left
    rw [eq_bot_iff]
    rintro x ⟨hxB, hxg⟩
    have hxg' : g⁻¹ * x * g ∈ B := mem_conjSubgroup.mp hxg
    have hg' : g⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h' => hg (by simpa using inv_mem h')
    have hodd := hK.2 g⁻¹ hg'
    have hmem : x ∈ K ⊓ rightConjugate K g⁻¹ :=
      ⟨hBK hxB, (mem_rightConjugate_iff K g⁻¹ x).mpr (by simpa using hBK hxg')⟩
    have hox : Odd (orderOf x) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hmem)
    exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_isPGroup hB2 hxB hox)

end TI

section Conj

variable {G : Type} [Group G]

omit [Group G] in
theorem isCommSubgroup_of_rightConjugate {G : Type} [Group G] {P : Subgroup G} (c : G)
    (h : IsCommSubgroup (rightConjugate P c)) : IsCommSubgroup P := by
  intro a ha b hb
  have hmem : ∀ y ∈ P, c⁻¹ * y * c ∈ rightConjugate P c := fun y hy =>
    (mem_rightConjugate_iff P c _).mpr (by simpa [mul_assoc] using hy)
  have h1 := h _ (hmem a ha) _ (hmem b hb)
  calc a * b = c * (c⁻¹ * a * c * (c⁻¹ * b * c)) * c⁻¹ := by group
    _ = c * (c⁻¹ * b * c * (c⁻¹ * a * c)) * c⁻¹ := by rw [h1]
    _ = b * a := by group

variable [Finite G]

theorem one_lt_pRank_rightConjugate {K : Subgroup G} (hm : 1 < CFSG.Open.pRank 2 K) (g : G) :
    1 < CFSG.Open.pRank 2 (rightConjugate K g) := by
  obtain ⟨E, hEK, hE, hE4⟩ := CFSG.ComponentClassification.Asc76X.exists_fourGroup_le hm
  exact CFSG.ComponentClassification.Asc76X.one_lt_pRank_of_fourGroup
    (rightConjugate_le_rightConjugate hEK g)
    (CFSG.ComponentClassification.Asc76X.isElemAbelian_rightConjugate hE g)
    (by rw [rightConjugate_card, hE4])

end Conj

structure NAConfig (G : Type) [Group G] [Finite G] (K R T : Subgroup G) (g : G) : Prop where
  stSetting : STSetting G K
  perfect : oUpperTwoPrime K = K
  sylowR : IsSylowOf 2 R K
  noncomm : ¬ IsCommSubgroup R
  rank : 2 ≤ CFSG.Open.pRank 2 R
  g_not : g ∉ Subgroup.normalizer (K : Set G)
  sylowT : IsSylowOf 2 T (rightConjugate K g ⊓ Subgroup.normalizer (K : Set G))
  T_ne : T ≠ ⊥
  T_lt : Nat.card T < Nat.card R
  T_norm : T ≤ Subgroup.normalizer (R : Set G)
  T_le : T ≤ rightConjugate R g

namespace NAConfig

variable {G : Type} [Group G] [Finite G] {K R T : Subgroup G} {g : G}

theorem tight (h : NAConfig G K R T g) : TightlyEmbedded K := h.stSetting.tight

theorem R_le_K (h : NAConfig G K R T g) : R ≤ K := h.sylowR.le

theorem T_le_J (h : NAConfig G K R T g) : T ≤ rightConjugate K g :=
  h.sylowT.le.trans inf_le_left

theorem T_le_normalizer (h : NAConfig G K R T g) : T ≤ Subgroup.normalizer (K : Set G) :=
  h.sylowT.le.trans inf_le_right

theorem T_isPGroup (h : NAConfig G K R T g) : IsPGroup 2 T := h.sylowT.isPGroup

theorem one_lt_pRank_K (h : NAConfig G K R T g) : 1 < CFSG.Open.pRank 2 K := by
  obtain ⟨E, hER, hE, hE4⟩ := CFSG.ComponentClassification.Asc76X.exists_fourGroup_le
    (show 1 < CFSG.Open.pRank 2 R by have := h.rank; omega)
  exact CFSG.ComponentClassification.Asc76X.one_lt_pRank_of_fourGroup (hER.trans h.R_le_K) hE hE4

theorem inf_K (h : NAConfig G K R T g) : T ⊓ K = ⊥ :=
  two_subgroup_inf_conjugate_eq_bot K T h.tight h.T_isPGroup g h.g_not h.T_le_J

theorem inf_R (h : NAConfig G K R T g) : R ⊓ T = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxR, hxT⟩
  have hx : x ∈ T ⊓ K := ⟨hxT, h.R_le_K hxR⟩
  rwa [h.inf_K] at hx

theorem inf_normalizer_eq (h : NAConfig G K R T g) :
    R ⊓ Subgroup.normalizer (T : Set G) = R ⊓ Subgroup.centralizer (T : Set G) :=
  CFSG.ComponentClassification.Asc76.Sec5.inf_normalizer_eq_inf_centralizer h.T_norm h.inf_R

theorem oddCoreIn_eq_bot (h : NAConfig G K R T g) : oddCoreIn K = ⊥ :=
  h.stSetting.eq_bot_of_normal_of_odd_card ((oddCoreIn_le K).trans Subgroup.le_normalizer)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer
      ((oddCoreIn_le K).trans Subgroup.le_normalizer)).mpr (normalizer_le_normalizer_oddCoreIn K))
    (odd_card_oddCoreIn K)

theorem rightConjugate_eq_of_mem_R (h : NAConfig G K R T g) {r : G} (hr : r ∈ R)
    (hne : T ⊓ rightConjugate T r ≠ ⊥) : rightConjugate T r = T := by
  have hJ : TightlyEmbedded (rightConjugate K g) := tightlyEmbedded_rightConjugate h.tight g
  have hrJ : r ∈ Subgroup.normalizer ((rightConjugate K g : Subgroup G) : Set G) := by
    by_contra hrJ
    refine hne (two_subgroup_of_odd_eq_bot (T ⊓ rightConjugate T r)
      (rightConjugate K g ⊓ rightConjugate (rightConjugate K g) r) h.T_isPGroup.to_inf_left
      (hJ.2 r hrJ) (inf_le_inf h.T_le_J (rightConjugate_le_rightConjugate h.T_le_J r)))
  have hbot : rightConjugate K g ⊓ R = ⊥ :=
    two_subgroup_of_odd_eq_bot (rightConjugate K g ⊓ R) (K ⊓ rightConjugate K g)
      h.sylowR.isPGroup.to_inf_right (h.tight.2 g h.g_not)
      (le_inf (inf_le_right.trans h.R_le_K) inf_le_left)
  have hcent : r ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hu : r * t * r⁻¹ * t⁻¹ ∈ rightConjugate K g ⊓ R := by
      refine ⟨Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (h.T_le_J ht)), ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hrJ t).mp (h.T_le_J ht)
      · have h1 : t * r⁻¹ * t⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (h.T_norm ht) r⁻¹).mp (R.inv_mem hr)
        have := R.mul_mem hr h1
        simpa [mul_assoc] using this
    rw [hbot, Subgroup.mem_bot] at hu
    have h2 : r * t * r⁻¹ = t := mul_inv_eq_one.mp hu
    exact ((mul_inv_eq_iff_eq_mul.mp h2).symm)
  exact (rightConjugate_eq_self_iff T r).mpr
    ((Subgroup.centralizer_le_normalizer (T : Set G)) hcent)

theorem isTI_T (h : NAConfig G K R T g) :
    ∀ x ∈ R ⊔ T, T ⊓ rightConjugate T x ≠ ⊥ → rightConjugate T x = T := by
  intro x hx hne
  obtain ⟨r, hr, t, ht, rfl⟩ := exists_mul_of_mem_sup h.T_norm hx
  have htT : rightConjugate T t = T :=
    (rightConjugate_eq_self_iff T t).mpr (Subgroup.le_normalizer ht)
  have e : rightConjugate T (r * t) = rightConjugate (rightConjugate T r) t :=
    (rightConjugate_mul T r t).symm
  have hne' : T ⊓ rightConjugate T r ≠ ⊥ := by
    intro hbot
    apply hne
    have hinf := Subgroup.map_inf_eq T (rightConjugate T r) (MulAut.conj t⁻¹).toMonoidHom
      (MulAut.conj t⁻¹).injective
    have h1 : T.map (MulAut.conj t⁻¹).toMonoidHom = T := htT
    rw [e]
    calc T ⊓ rightConjugate (rightConjugate T r) t
        = T.map (MulAut.conj t⁻¹).toMonoidHom ⊓
            (rightConjugate T r).map (MulAut.conj t⁻¹).toMonoidHom := by rw [h1]; rfl
      _ = (T ⊓ rightConjugate T r).map (MulAut.conj t⁻¹).toMonoidHom := hinf.symm
      _ = ⊥ := by rw [hbot, Subgroup.map_bot]
  rw [e, h.rightConjugate_eq_of_mem_R hr hne', htT]

theorem not_isDihedral_of (h3L : Asc76Theorem3Large) (h : NAConfig G K R T g) :
    ¬ IsDihedralTwoGroup R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hD
  have hS := h.stSetting
  have := hS.simple
  obtain ⟨m, hm, ⟨e⟩⟩ := id hD
  have hc : Nat.card R = 2 ^ m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, ← pow_succ']
    congr 1
    omega
  have hm3 : 3 ≤ m := by
    by_contra hlt
    have hm2 : m = 2 := by omega
    apply h.noncomm
    have hc' : Nat.card ↥R = 2 ^ 2 := by rw [hc, hm2]
    have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hc'
    intro a ha b hb
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h4 : 4 < Nat.card R := by
    rw [hc]
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  have hconc := h3L G K hS.tight (normalClosure_eq_top hS) (standardComponentOddCore_eq_bot hS)
    R h.sylowR hD h4
  rcases hconc with hKn | ⟨-, hR4, -⟩ | ⟨U, hUR, -, hUi, hUab⟩
  · exact CFSG.CGT.PushingUp.ne_top_of_isPLocal hS.nonab hS.max.1
      (Subgroup.normalizer_eq_top_iff.mpr hKn)
  · omega
  · have hcard := Subgroup.relIndex_mul_card (H := U) (K := R)
    rw [inf_of_le_left hUR, hUi] at hcard
    have hUne : U ≠ ⊥ := by
      intro hU
      rw [hU, Subgroup.card_bot] at hcard
      omega
    have hNC : Subgroup.normalClosure (U : Set G) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (U : Set G)) with
        hbot | htop
      · exact absurd (le_bot_iff.mp (hbot ▸ fun x hx => Subgroup.subset_normalClosure hx)) hUne
      · exact htop
    rw [hNC] at hUab
    obtain ⟨a, b, hab⟩ := hS.nonab
    exact hab (congrArg Subtype.val (hUab.is_comm.comm ⟨a, Subgroup.mem_top a⟩
      ⟨b, Subgroup.mem_top b⟩))

theorem ne_weakClosure (h22 : Asc76Lemma22) (h : NAConfig G K R T g) :
    T ≠ weakClosure K T (R ⊔ T) := by
  obtain ⟨⟨h1, -⟩, -⟩ := h22 G K (rightConjugate K g) T R h.tight
    (tightlyEmbedded_rightConjugate h.tight g) (h.tight.2 g h.g_not)
    (by rw [rightConjugate_card]) h.sylowT h.T_ne h.sylowR h.T_norm h.one_lt_pRank_K
    (one_lt_pRank_rightConjugate h.one_lt_pRank_K g)
  intro hTW
  have hRN : R ≤ Subgroup.normalizer (T : Set G) := by
    intro r hr
    rw [← rightConjugate_eq_self_iff]
    have hle : rightConjugate T r ≤ R ⊔ T := by
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      have hy : r * x * r⁻¹ ∈ T := hx
      have h1' : r * x * r⁻¹ * r * (r * x * r⁻¹)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (h.T_norm hy) r).mp hr
      have hxe : x = (r⁻¹ * (r * x * r⁻¹ * r * (r * x * r⁻¹)⁻¹)) * (r * x * r⁻¹) := by group
      rw [hxe]
      exact Subgroup.mul_mem_sup (R.mul_mem (R.inv_mem hr) h1') hy
    have hle2 : rightConjugate T r ≤ T :=
      le_trans (le_iSup₂_of_le r (h.R_le_K hr)
        (le_iSup (fun _ : rightConjugate T r ≤ R ⊔ T => rightConjugate T r) hle)) hTW.symm.le
    exact Subgroup.eq_of_le_of_card_ge hle2 (by rw [rightConjugate_card])
  rw [inf_eq_left.mpr hRN] at h1
  have := h.T_lt
  omega

theorem not_isCyclic_of (h22 : Asc76Lemma22) (h3L : Asc76Theorem3Large) (h : NAConfig G K R T g) :
    ¬ IsCyclic T := by
  obtain ⟨-, h2, -⟩ := h22 G K (rightConjugate K g) T R h.tight
    (tightlyEmbedded_rightConjugate h.tight g) (h.tight.2 g h.g_not)
    (by rw [rightConjugate_card]) h.sylowT h.T_ne h.sylowR h.T_norm h.one_lt_pRank_K
    (one_lt_pRank_rightConjugate h.one_lt_pRank_K g)
  exact fun hc => h.not_isDihedral_of h3L (h2 (h.ne_weakClosure h22) hc).1

theorem basic_of (h22 : Asc76Lemma22) (h3L : Asc76Theorem3Large) (h : NAConfig G K R T g) :
    T ⊓ K = ⊥ ∧
    (∀ x ∈ R ⊔ T, T ⊓ rightConjugate T x ≠ ⊥ → rightConjugate T x = T) ∧
    Nat.card (R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) = Nat.card T ∧
    R ⊓ Subgroup.normalizer (T : Set G) = R ⊓ Subgroup.centralizer (T : Set G) ∧
    ((R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G).subgroupOf R).Normal ∧
    IsCommSubgroup T ∧ ¬ IsCyclic T ∧ T ≠ weakClosure K T (R ⊔ T) ∧
    K ⊔ T ≤ Subgroup.normalizer (weakClosure K T (R ⊔ T) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨h1, -⟩, -, h3, -, h5, -, h7⟩ := h22 G K (rightConjugate K g) T R h.tight
    (tightlyEmbedded_rightConjugate h.tight g) (h.tight.2 g h.g_not)
    (by rw [rightConjugate_card]) h.sylowT h.T_ne h.sylowR h.T_norm h.one_lt_pRank_K
    (one_lt_pRank_rightConjugate h.one_lt_pRank_K g)
  have hTW := h.ne_weakClosure h22
  have hnotcyc : ¬ IsCyclic ↥T := h.not_isCyclic_of h22 h3L
  have hnotSyl : ¬ IsSylowOf 2 T (rightConjugate K g) := by
    intro hS
    have h1' := hS.card_eq
    have h2' := h.sylowR.card_eq
    rw [rightConjugate_card] at h1'
    have hlt := h.T_lt
    rw [h1', ← h2'] at hlt
    exact lt_irrefl _ hlt
  have hcomm : IsCommSubgroup T := fun a ha b hb =>
    congrArg Subtype.val ((h5 hnotSyl).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨h.inf_K, h.isTI_T, h1, h.inf_normalizer_eq, h7, hcomm, hnotcyc, hTW, ?_⟩
  rcases h3 with hN | ⟨n, -, φ, -, hker⟩ | hcyc
  · have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hN.1).mp hN.2
    rw [h.oddCoreIn_eq_bot, sup_bot_eq] at hle
    exact hle
  · exfalso
    have hsq := CFSG.ComponentClassification.Asc76.Sec5.sq_eq_one_of_caseL2 h.sylowR φ hker
    apply h.noncomm
    intro a ha b hb
    have ha2 : a * a = 1 := by simpa [sq] using hsq a ha
    have hb2 : b * b = 1 := by simpa [sq] using hsq b hb
    have hab2 : a * b * (a * b) = 1 := by simpa [sq] using hsq (a * b) (R.mul_mem ha hb)
    have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have e3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab2
    rw [mul_inv_rev, e1, e2] at e3
    exact e3.symm
  · exact absurd hcyc hnotcyc

end NAConfig

section Construction

variable {G : Type} [Group G] [Finite G] {K R T : Subgroup G} {g : G}

theorem exists_config_or_szU3 (S : STSetting G K) (hK : oUpperTwoPrime K = K) {R₀ : Subgroup G}
    (hR₀ : IsSylowOf 2 R₀ K) (hnc : ¬ IsCommSubgroup R₀) (hrk : 2 ≤ CFSG.Open.pRank 2 R₀) :
    IsSzOrU3 G ∨ ∃ (R T : Subgroup G) (g : G), NAConfig G K R T g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases exists_J_or_szU3 S hK hR₀ hnc hrk with hSz | ⟨g, T, hg, hT, hT1, hTR₀⟩
  · exact Or.inl hSz
  right
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := hT.le.trans inf_le_right
  have hTJ : T ≤ rightConjugate K g := hT.le.trans inf_le_left
  obtain ⟨S₁, hS₁, hTS₁⟩ := exists_isSylowOf_le hT.isPGroup (le_sup_right : T ≤ K ⊔ T)
  have hKT : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTN
  have hR : IsSylowOf 2 (S₁ ⊓ K) K := hS₁.inf_of_le_normalizer le_sup_left hKT
  have hTR : T ≤ Subgroup.normalizer ((S₁ ⊓ K : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf (Subgroup.le_normalizer (hTS₁ ht)) (hTN ht)
  obtain ⟨c, -, hcR⟩ := exists_rightConjugate_eq_of_isSylowOf hR hR₀
  have hncR : ¬ IsCommSubgroup (S₁ ⊓ K) := fun hc =>
    hnc (isCommSubgroup_of_rightConjugate c (hcR ▸ hc))
  have hrkR : 2 ≤ CFSG.Open.pRank 2 (S₁ ⊓ K) := by
    have := one_lt_pRank_rightConjugate (K := R₀) (by omega) c
    rw [hcR] at this
    omega
  obtain ⟨S₂, hS₂, hTS₂⟩ := exists_isSylowOf_le hT.isPGroup hTJ
  have hRg : IsSylowOf 2 (rightConjugate (S₁ ⊓ K) g) (rightConjugate K g) :=
    isSylowOf_of_card (rightConjugate_le_rightConjugate hR.le g)
      (by rw [rightConjugate_card, rightConjugate_card, hR.card_eq])
  obtain ⟨x, hx, hxS⟩ := exists_rightConjugate_eq_of_isSylowOf hS₂ hRg
  have hKg' : rightConjugate K (g * x) = rightConjugate K g := by
    rw [← rightConjugate_mul, (rightConjugate_eq_self_iff _ x).mpr (Subgroup.le_normalizer hx)]
  have hRg' : rightConjugate (S₁ ⊓ K) (g * x) = S₂ := by
    rw [← rightConjugate_mul]
    exact hxS
  have hgx : g * x ∉ Subgroup.normalizer (K : Set G) := by
    intro hgx
    apply hg
    have hk : g * x * g⁻¹ ∈ K := (mem_rightConjugate_iff K g x).mp hx
    have hge : g = (g * x * g⁻¹)⁻¹ * (g * x) := by group
    rw [hge]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hk)) hgx
  refine ⟨S₁ ⊓ K, T, g * x, ⟨S, hK, hR, hncR, hrkR, hgx, ?_, hT1, ?_, hTR, ?_⟩⟩
  · rw [hKg']
    exact hT
  · rw [hR.card_eq, ← hR₀.card_eq]
    exact hTR₀
  · rw [hRg']
    exact hTS₂

theorem mtOutcome_or_exists_config (S : STSetting G K) (R : Sylow 2 K)
    (hnc : ¬ IsCommSubgroup (sylowImg R)) (hrk : 2 ≤ CFSG.Open.pRank 2 (sylowImg R)) :
    MTOutcome G K R ∨ ∃ (R₁ T : Subgroup G) (g : G), NAConfig G (oUpperTwoPrime K) R₁ T g := by
  rcases exists_config_or_szU3 (stSetting_oUpperTwoPrime S) (oUpperTwoPrime_oUpperTwoPrime K)
    (isSylowOf_oUpperTwoPrime R) hnc hrk with hSz | h
  · exact Or.inl (szU3_mtOutcome S hSz R)
  · exact Or.inr h

theorem NAConfig.not_isCyclic (h : NAConfig G K R T g) : ¬ IsCyclic T :=
  h.not_isCyclic_of (CFSG.ComponentClassification.Asc76.asc76Lemma22
    CFSG.ComponentClassification.AschbacherTheorem3.theorem_3_holds)
    CFSG.ComponentClassification.RankTwoFoundation.asc76Theorem3Large

theorem NAConfig.basic (h : NAConfig G K R T g) :
    T ⊓ K = ⊥ ∧
    (∀ x ∈ R ⊔ T, T ⊓ rightConjugate T x ≠ ⊥ → rightConjugate T x = T) ∧
    Nat.card (R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) = Nat.card T ∧
    R ⊓ Subgroup.normalizer (T : Set G) = R ⊓ Subgroup.centralizer (T : Set G) ∧
    ((R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G).subgroupOf R).Normal ∧
    IsCommSubgroup T ∧ ¬ IsCyclic T ∧ T ≠ weakClosure K T (R ⊔ T) ∧
    K ⊔ T ≤ Subgroup.normalizer (weakClosure K T (R ⊔ T) : Set G) :=
  h.basic_of (CFSG.ComponentClassification.Asc76.asc76Lemma22
    CFSG.ComponentClassification.AschbacherTheorem3.theorem_3_holds)
    CFSG.ComponentClassification.RankTwoFoundation.asc76Theorem3Large

end Construction

end CFSG.CGT.PushingUpLit.SolKNA
