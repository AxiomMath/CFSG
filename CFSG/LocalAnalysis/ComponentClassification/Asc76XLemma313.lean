module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem1
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Defs

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def adj (Ω : Set (Subgroup G)) (K J : Subgroup G) : Prop :=
  J ∈ Ω ∧ J ≠ K ∧ J ≤ normalizer (K : Set G)

abbrev reach (Ω : Set (Subgroup G)) : Subgroup G → Subgroup G → Prop :=
  Relation.ReflTransGen (adj Ω)

theorem adj_conj {Ω : Set (Subgroup G)} (hΩinv : ∀ K ∈ Ω, ∀ g : G, rightConjugate K g ∈ Ω)
    {K J : Subgroup G} (h : adj Ω K J) (g : G) :
    adj Ω (rightConjugate K g) (rightConjugate J g) := by
  obtain ⟨hJ, hne, hle⟩ := h
  refine ⟨hΩinv J hJ g, fun h' => hne ?_, fun x hx => ?_⟩
  · have := congrArg (rightConjugate · g⁻¹) h'
    simpa only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] using this
  · rw [mem_rightConjugate_iff] at hx
    exact mem_normalizer_rightConjugate_iff.mpr (hle hx)

theorem reach_conj {Ω : Set (Subgroup G)} (hΩinv : ∀ K ∈ Ω, ∀ g : G, rightConjugate K g ∈ Ω)
    {K J : Subgroup G} (h : reach Ω K J) (g : G) :
    reach Ω (rightConjugate K g) (rightConjugate J g) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact ih.tail (adj_conj hΩinv hab g)

theorem reach_mem {Ω : Set (Subgroup G)} {K J : Subgroup G} (hK : K ∈ Ω) (h : reach Ω K J) :
    J ∈ Ω := by
  induction h with
  | refl => exact hK
  | tail _ hab _ => exact hab.1

end CFSG.ComponentClassification.Asc76X

namespace CFSG.ComponentClassification.Asc76.Sec3Setting

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76X
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem adj_of_even (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hne : J ≠ K) (h : Even (Nat.card (J ⊓ normalizer (K : Set G) : Subgroup G))) :
    adj Ω K J :=
  ⟨hJ, hne, (hΩ.lemma35 h22 hK hJ hne h).1⟩

theorem adj_symm (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K J : Subgroup G} (hK : K ∈ Ω)
    (h : adj Ω K J) : adj Ω J K := by
  obtain ⟨hJ, hne, hle⟩ := h
  have heven : Even (Nat.card (J ⊓ normalizer (K : Set G) : Subgroup G)) := by
    rw [inf_of_le_left hle]
    exact (hΩ.tightlyEmbedded hJ).1
  exact hΩ.adj_of_even h22 hJ hK (Ne.symm hne) (hΩ.even_inf_normalizer_symm hK hJ hne heven)

theorem reach_symm (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K J : Subgroup G} (hK : K ∈ Ω)
    (h : reach Ω K J) : reach Ω J K := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hb hbc ih =>
    exact Relation.ReflTransGen.head (hΩ.adj_symm h22 (reach_mem hK hb) hbc) ih

theorem reach_trans' (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K J L : Subgroup G}
    (hK : K ∈ Ω) (h₁ : reach Ω K J) (h₂ : reach Ω K L) : reach Ω J L :=
  (hΩ.reach_symm h22 hK h₁).trans h₂

@[expose] def compStab (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K : Subgroup G} (hK : K ∈ Ω) :
    Subgroup G where
  carrier := {g | reach Ω K (rightConjugate K g)}
  one_mem' := by
    show reach Ω K (rightConjugate K 1)
    rw [rightConjugate_one]
  mul_mem' := by
    intro a b ha hb
    show reach Ω K (rightConjugate K (a * b))
    rw [← rightConjugate_mul]
    exact (hb : reach Ω K (rightConjugate K b)).trans (reach_conj hΩ.conj_mem ha b)
  inv_mem' := by
    intro a ha
    show reach Ω K (rightConjugate K a⁻¹)
    have h := reach_conj hΩ.conj_mem (ha : reach Ω K (rightConjugate K a)) a⁻¹
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h
    exact hΩ.reach_symm h22 (hΩ.conj_mem K hK _) h

theorem mem_compStab_iff (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K : Subgroup G}
    (hK : K ∈ Ω) {g : G} : g ∈ hΩ.compStab h22 hK ↔ reach Ω K (rightConjugate K g) :=
  Iff.rfl

theorem reach_of_mem_compStab (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : reach Ω K J) {g : G} (hg : g ∈ hΩ.compStab h22 hK) :
    reach Ω K (rightConjugate J g) :=
  ((mem_compStab_iff hΩ h22 hK).mp hg).trans (reach_conj hΩ.conj_mem hJ g)

theorem mem_compStab_of_reach (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : reach Ω K J) {g : G} (hJg : reach Ω K (rightConjugate J g)) :
    g ∈ hΩ.compStab h22 hK := by
  rw [mem_compStab_iff]
  exact hJg.trans (hΩ.reach_symm h22 (hΩ.conj_mem K hK g) (reach_conj hΩ.conj_mem hJ g))

theorem le_compStab (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : reach Ω K J) : J ≤ hΩ.compStab h22 hK := by
  intro j hj
  refine hΩ.mem_compStab_of_reach h22 hK hJ ?_
  rw [(rightConjugate_eq_self_iff J j).mpr (le_normalizer hj)]
  exact hJ

theorem compStab_le_normalizer (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {J₁ : Subgroup G}
    (hJ₁ : J₁ ∈ Ω) : hΩ.compStab h22 hJ₁ ≤
      normalizer ((sSup {J | reach Ω J₁ J} : Subgroup G) : Set G) := by
  intro g hg
  have hle : rightConjugate (sSup {J | reach Ω J₁ J}) g ≤ sSup {J | reach Ω J₁ J} := by
    rw [rightConjugate, map_le_iff_le_comap]
    refine sSup_le fun J hJ x hx => ?_
    have h1 : (MulAut.conj g⁻¹) x ∈ rightConjugate J g := ⟨x, hx, rfl⟩
    exact le_sSup (hΩ.reach_of_mem_compStab h22 hJ₁ hJ hg) h1
  exact (rightConjugate_eq_self_iff _ g).mp
    (eq_of_le_of_card_ge hle (by rw [rightConjugate_card]))

theorem reach_of_fourGroup (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K J₁ E : Subgroup G}
    (hK : K ∈ Ω) (hJ₁ : J₁ ∈ Ω) (hEK : E ≤ K) (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4)
    (hstab : E ≤ hΩ.compStab h22 hJ₁) : reach Ω K J₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := hΩ.compStab h22 hJ₁ with hMdef
  set Y := sSup {J | reach Ω J₁ J} with hYdef
  have hYM : Y ≤ M := sSup_le fun J hJ => hΩ.le_compStab h22 hJ₁ hJ
  have hMY := hΩ.compStab_le_normalizer h22 hJ₁
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by rw [hE4]; norm_num)
  obtain ⟨P, hP, hEP⟩ := exists_isSylowOf_le hstab hE2
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (isSylowOf_iff_card.mp hP).2
  have hPY : IsSylowOf 2 (P ⊓ Y) Y := isSylowOf_inf hYM hMY hP
  obtain ⟨T₀, hT₀⟩ := Sec3Setting.exists_sylow J₁
  have hT₀' := isSylowOf_iff_card.mp hT₀
  have hT₀Y : T₀ ≤ Y := hT₀'.1.trans (le_sSup (Relation.ReflTransGen.refl : reach Ω J₁ J₁))
  obtain ⟨S₀, hS₀, hT₀S₀⟩ := exists_isSylowOf_le hT₀Y (IsPGroup.of_card hT₀'.2)
  obtain ⟨y, hyY, hS₀y⟩ := exists_conj_of_isSylowOf hPY hS₀
  set T₁ := rightConjugate T₀ y⁻¹ with hT₁def
  have hT₁P : T₁ ≤ P := by
    intro x hx
    rw [hT₁def, mem_rightConjugate_iff, inv_inv] at hx
    have h1 : y⁻¹ * x * y ∈ rightConjugate (P ⊓ Y) y := hS₀y ▸ hT₀S₀ (by simpa using hx)
    rw [mem_rightConjugate_iff] at h1
    have : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
    rw [this]
    exact (mem_inf.mp h1).1
  set J₁' := rightConjugate J₁ y⁻¹ with hJ₁'def
  have hJ₁'Ω : J₁' ∈ Ω := hΩ.conj_mem J₁ hJ₁ y⁻¹
  have hreach : reach Ω J₁ J₁' :=
    hΩ.reach_of_mem_compStab h22 hJ₁ Relation.ReflTransGen.refl (hYM (inv_mem hyY))
  have hT₁ : IsSylowOf 2 T₁ J₁' := isSylowOf_rightConjugate hT₀ y⁻¹
  have hT₁2 : IsPGroup 2 T₁ := IsPGroup.of_card (isSylowOf_iff_card.mp hT₁).2
  have hcomm : ∀ g ∈ P, rightConjugate T₁ g ≠ T₁ → ⁅T₁, rightConjugate T₁ g⁆ = ⊥ := by
    intro g hg hne
    refine hΩ.commute_of_sylow hP2 hJ₁'Ω (hΩ.conj_mem _ hJ₁'Ω g) hT₁
      (isSylowOf_rightConjugate hT₁ g) hT₁P (fun x hx => ?_) (Ne.symm hne)
    rw [mem_rightConjugate_iff] at hx
    have h1 := hT₁P hx
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hg) h1) hg
  obtain ⟨-, h24⟩ := lemma24In hT₁P hEP hT₁2 hE hE4 hcomm (hΩ.frattini_sylow_ne_bot hJ₁'Ω hT₁)
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h24
  obtain ⟨hzΓ, hzT⟩ := mem_inf.mp hz
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hΓK : gammaOneOn E P ≤ normalizer (K : Set G) := by
    refine iSup_le fun E₀ => iSup_le fun hE₀ => iSup_le fun hE₀1 => ?_
    exact inf_le_right.trans (hΩ.normalizer_le_normalizer hK (hE2.to_le hE₀) hE₀1
      (hE₀.trans hEK))
  obtain ⟨k, hk⟩ := hT₁2 ⟨z, (mem_inf.mp hzT).1⟩
  have hk' : z ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have heven : Even (Nat.card (J₁' ⊓ normalizer (K : Set G) : Subgroup G)) :=
    even_card_of_two_element (mem_inf.mpr ⟨(isSylowOf_iff_card.mp hT₁).1 (mem_inf.mp hzT).1,
      hΓK hzΓ⟩) hz1' hk'
  have hback : reach Ω J₁' J₁ := hΩ.reach_symm h22 hJ₁ hreach
  by_cases hJK : J₁' = K
  · rw [← hJK]
    exact hback
  · exact (Relation.ReflTransGen.single (hΩ.adj_of_even h22 hK hJ₁'Ω hJK heven)).trans hback

end CFSG.ComponentClassification.Asc76.Sec3Setting

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.LiteratureLocal.TightCommuting
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def sylowSet (Ω : Set (Subgroup G)) : Set (Subgroup G) :=
  {T | ∃ J ∈ Ω, IsSylowOf 2 T J}

end CFSG.ComponentClassification.Asc76X

namespace CFSG.ComponentClassification.Asc76X.MinCounter

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.LiteratureLocal.TightCommuting
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem reach_of_sylow_le (hM : MinCounter Ω) (h22 : Lemma22Four) {K R S J T : Subgroup G}
    (hK : K ∈ Ω) (hR : IsSylowOf 2 R K) (hS2 : IsPGroup 2 S) (hRS : R ≤ S) (hJ : J ∈ Ω)
    (hT : IsSylowOf 2 T J) (hTS : T ≤ S) : reach Ω K J := by
  have hΩ := hM.setting
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (isSylowOf_iff_card.mp hR).2
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (isSylowOf_iff_card.mp hT).2
  by_cases hJK : J = K
  · rw [hJK]
  have hRT : R ≠ T := fun h => hJK (hΩ.eq_of_pGroup_le hJ hK hT2 (hΩ.sylow_ne_bot hJ hT)
    (isSylowOf_iff_card.mp hT).1 (h ▸ (isSylowOf_iff_card.mp hR).1))
  have hc := hΩ.commute_of_sylow hS2 hK hJ hR hT hRS hTS hRT
  have hTN : T ≤ normalizer (K : Set G) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (centralizer_le_normalizer _)).trans (hΩ.normalizer_le_normalizer hK hR2
        (hΩ.sylow_ne_bot hK hR) (isSylowOf_iff_card.mp hR).1)
  have heven : Even (Nat.card (J ⊓ normalizer (K : Set G) : Subgroup G)) := by
    obtain ⟨x, hx, hx2⟩ := exists_involution hT2 (hΩ.sylow_ne_bot hJ hT)
    rw [even_iff_two_dvd, ← hx2]
    exact orderOf_dvd_natCard _ (mem_inf.mpr ⟨(isSylowOf_iff_card.mp hT).1 hx, hTN hx⟩)
  exact Relation.ReflTransGen.single (hΩ.adj_of_even h22 hK hJ hJK heven)

omit [Finite G] in
theorem orderOf_conj' (g x : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  have hsc : SemiconjBy g (g⁻¹ * x * g) x := by
    simp only [SemiconjBy]
    group
  exact SemiconjBy.orderOf_eq g hsc

theorem strongClosed_gammaSet (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    {K R S : Subgroup G} (hK : K ∈ Ω) (hR : IsSylowOf 2 R K) (hS : IsSylowOf 2 S ⊤)
    (hRS : R ≤ S) (hSgood : IsSylowOf 2 (S ⊓ sSup (perp Ω K)) (sSup (perp Ω K)))
    (hdisc : ∃ J ∈ Ω, ¬ reach Ω K J) :
    fusionStronglyClosed (L26.gammaSet S (sylowSet Ω)) S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (isSylowOf_iff_card.mp hS).2
  have hR' := isSylowOf_iff_card.mp hR
  have hR2 : IsPGroup 2 R := IsPGroup.of_card hR'.2
  set H := hΩ.compStab h22 hK with hHdef
  have hSH : S ≤ H := by
    intro s hs
    show reach Ω K (rightConjugate K s)
    refine hM.reach_of_sylow_le h22 hK hR hS2 hRS (hΩ.conj_mem K hK s)
      (isSylowOf_rightConjugate hR s) (fun x hx => ?_)
    rw [mem_rightConjugate_iff] at hx
    have h1 := hRS hx
    have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hs) h1) hs
  set α₀ : Set (Subgroup G) := {J | reach Ω K J} with hα₀
  have hα₀Ω : α₀ ⊆ Ω := fun J hJ => reach_mem hK hJ
  have hX₀H : sSup α₀ ≤ H := sSup_le fun J hJ => hΩ.le_compStab h22 hK hJ
  have hCα₀ : Conc4 (bar (sSup α₀) '' α₀) := by
    refine hM.conc4_bar hα₀Ω
      (fun J hJ x hx => hΩ.reach_of_mem_compStab h22 hK hJ (hX₀H hx)) (Or.inl ?_)
    obtain ⟨J, hJ, hKJ⟩ := hdisc
    refine Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hα₀Ω, fun h => hKJ ?_⟩)
      (Set.toFinite Ω)
    rw [← h] at hJ
    exact hJ
  have hSX₀ : IsSylowOf 2 (S ⊓ sSup α₀) (sSup α₀) :=
    isSylowOf_inf hX₀H (hΩ.compStab_le_normalizer h22 hK) (isSylowOf_of_le hSH le_top hS)
  intro y hy g hgS
  by_contra hng
  obtain ⟨hy1, T₁, ⟨J₁, hJ₁, hT₁⟩, hT₁S, hyT₁⟩ := hy
  have hT₁' := isSylowOf_iff_card.mp hT₁
  have hT₁2 : IsPGroup 2 T₁ := IsPGroup.of_card hT₁'.2
  obtain ⟨k, hk⟩ := hT₁2 ⟨y, hyT₁⟩
  have hk' : y ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hy1 (orderOf_eq_one_iff.mp (by rw [hm, pow_zero]))
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  set t := g⁻¹ * y ^ (2 ^ n) * g with htdef
  have hto : orderOf t = 2 := by
    rw [htdef, orderOf_conj', orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (hm ▸ pow_dvd_pow 2 (Nat.le_succ n)), hm, pow_succ, Nat.mul_div_cancel_left _
      (pow_pos two_pos n)]
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at hto; exact absurd hto (by decide)
  have htsq : t ^ (2 ^ 1) = 1 := by rw [pow_one, ← hto]; exact pow_orderOf_eq_one t
  have htS : t ∈ S := by
    have : t = (g⁻¹ * y * g) ^ (2 ^ n) := by
      have h := conj_pow (a := g⁻¹) (b := y) (i := 2 ^ n)
      rw [inv_inv] at h
      rw [htdef, h]
    rw [this]
    exact pow_mem hgS _
  set J := rightConjugate J₁ g with hJdef
  have hJΩ : J ∈ Ω := hΩ.conj_mem J₁ hJ₁ g
  have hyJ : g⁻¹ * y * g ∈ J := by
    rw [hJdef, mem_rightConjugate_iff]
    simpa [mul_assoc] using hT₁'.1 hyT₁
  have htJ : t ∈ J := by
    rw [hJdef, mem_rightConjugate_iff]
    simpa [htdef, mul_assoc] using pow_mem (hT₁'.1 hyT₁) (2 ^ n)
  have htΓ : t ∉ L26.gammaSet S (sylowSet Ω) := by
    rintro ⟨-, T₂, ⟨J₂, hJ₂, hT₂⟩, hT₂S, htT₂⟩
    have hT₂' := isSylowOf_iff_card.mp hT₂
    have hJ₂J : J₂ = J := hΩ.eq_of_mem_of_mem hJ₂ hJΩ (hT₂'.1 htT₂) htJ hto
    apply hng
    refine ⟨fun h => hy1 ?_, T₂, ⟨J₂, hJ₂, hT₂⟩, hT₂S, ?_⟩
    · have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      rw [this, h]
      group
    · have h1 : S ⊓ J₂ = T₂ := eq_of_isSylowOf_le hT₂ (hS2.to_le inf_le_left) inf_le_right
        (le_inf hT₂S hT₂'.1)
      rw [← h1]
      exact mem_inf.mpr ⟨hgS, hJ₂J ▸ hyJ⟩
  have key : ¬ IsSylowOf 2 (S ⊓ J) J := fun h =>
    htΓ ⟨ht1, S ⊓ J, ⟨J, hJΩ, h⟩, inf_le_left, mem_inf.mpr ⟨htS, htJ⟩⟩
  have hSJ1 : S ⊓ J ≠ ⊥ := fun h => ht1 (by
    have : t ∈ S ⊓ J := mem_inf.mpr ⟨htS, htJ⟩
    rwa [h, mem_bot] at this)
  have hJ₁reach : reach Ω K J₁ := hM.reach_of_sylow_le h22 hK hR hS2 hRS hJ₁ hT₁ hT₁S
  have hgH : g ∉ H := by
    intro hg
    exact key (isSylowOf_inf_of_conc4 hΩ hB hα₀Ω hCα₀ hSX₀
      (hΩ.reach_of_mem_compStab h22 hK hJ₁reach hg) hSJ1)
  have hCRt : ∀ r ∈ R, r * t = t * r → r = 1 := by
    intro r hr hrt
    by_contra hr1
    obtain ⟨i, hi⟩ := hR2 ⟨r, hr⟩
    have hi' : r ^ (2 ^ i) = 1 := by simpa using congrArg Subtype.val hi
    have htK : t ∈ normalizer (K : Set G) :=
      hΩ.normalizer_le_normalizer hK (isPGroup_zpowers_of_two_element hi')
        (zpowers_ne_bot_of_ne_one' hr1) ((zpowers_le).mpr (hR'.1 hr))
        (mem_normalizer_zpowers_of_commute hrt.symm)
    have hJperp : J ∈ perp Ω K :=
      ⟨hJΩ, even_card_of_two_element (mem_inf.mpr ⟨htJ, htK⟩) ht1 htsq⟩
    exact key (hM.isSylowOf_inf_of_mem_perp h22 hB hK hSgood hJperp hSJ1)
  have htt : t * t = 1 := by rw [← sq]; simpa using htsq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  set Rt := rightConjugate R t with hRtdef
  have hRRt : R ⊓ Rt = ⊥ := by
    by_contra hD
    have htD : t ∈ normalizer ((R ⊓ Rt : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      simp only [mem_inf, hRtdef, mem_rightConjugate_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        have e : t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        rw [e, htt, one_mul, inv_one, mul_one]
        exact h1
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h1⟩
        have e : t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        rw [e, htt, one_mul, inv_one, mul_one] at h2
        exact h2
    have hP2 : IsPGroup 2 ↥(zpowers t ⊔ (R ⊓ Rt)) :=
      (isPGroup_zpowers_of_two_element htsq).to_sup_of_normal_right' (hR2.to_le inf_le_left)
        ((zpowers_le).mpr htD)
    have hc := inf_center_ne_bot' hP2 le_sup_right
      (sup_le ((zpowers_le).mpr htD) le_normalizer) hD
    obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc
    obtain ⟨hdD, hdP⟩ := mem_inf.mp hd
    have hdt := mem_centralizer_iff.mp (mem_inf.mp hdP).2 t (mem_sup_left (mem_zpowers t))
    exact hd1 (Subtype.ext (hCRt d (mem_inf.mp hdD).1 hdt.symm))
  have hRtS : Rt ≤ S := fun x hx => by
    rw [hRtdef, mem_rightConjugate_iff] at hx
    have h1 := hRS hx
    have : x = t⁻¹ * (t * x * t⁻¹) * t := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem htS) h1) htS
  have hRne : R ≠ Rt := fun h => hΩ.sylow_ne_bot hK hR (by
    have : R ⊓ Rt = R := by rw [← h, inf_idem]
    rw [← this, hRRt])
  have hcomm := hΩ.commute_of_sylow hS2 hK (hΩ.conj_mem K hK t) hR
    (isSylowOf_rightConjugate hR t) hRS hRtS hRne
  have hreachJ : reach Ω (rightConjugate K g) J := reach_conj hΩ.conj_mem hJ₁reach g
  have hinvH : ∀ r ∈ R, r ^ 2 = 1 → g * r * g⁻¹ ∈ H := by
    intro r hr hr2
    have hrr : r * r = 1 := by rw [← sq]; exact hr2
    have htrt : t * r * t ∈ Rt := by
      rw [hRtdef, mem_rightConjugate_iff]
      have e : t * (t * r * t) * t⁻¹ = (t * t) * r := by group
      rw [e, htt, one_mul]
      exact hr
    have hc1 : r * (t * r * t) = (t * r * t) * r :=
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm hr) _ htrt).symm
    have hc2 : (r * t * r) * t = t * (r * t * r) := by
      calc (r * t * r) * t = r * (t * r * t) := by group
        _ = (t * r * t) * r := hc1
        _ = t * (r * t * r) := by group
    have htrN : r * t * r ∈ normalizer (J : Set G) :=
      hΩ.centralizer_le_normalizer hJΩ htJ hto (mem_centralizer_singleton_iff.mpr hc2)
    have htrJ : r * t * r ∈ rightConjugate J r := by
      rw [mem_rightConjugate_iff]
      have e : r * (r * t * r) * r⁻¹ = (r * r) * t := by group
      rw [e, hrr, one_mul]
      exact htJ
    have htr1 : r * t * r ≠ 1 := fun h => ht1 (by
      have e : r * (r * t * r) * r = (r * r) * t * (r * r) := by group
      rw [h, mul_one, hrr] at e
      simpa using e.symm)
    have htrsq : (r * t * r) ^ (2 ^ 1) = 1 := by
      rw [pow_one, sq]
      have e : r * t * r * (r * t * r) = r * (t * (r * r) * t) * r := by group
      rw [e, hrr, mul_one, htt, mul_one, hrr]
    have hJJr : reach Ω J (rightConjugate J r) := by
      by_cases h : rightConjugate J r = J
      · rw [h]
      · exact Relation.ReflTransGen.single (hΩ.adj_of_even h22 hJΩ (hΩ.conj_mem J hJΩ r) h
          (even_card_of_two_element (mem_inf.mpr ⟨htrJ, htrN⟩) htr1 htrsq))
    have h1 : reach Ω (rightConjugate K g) (rightConjugate (rightConjugate K g) r) :=
      hreachJ.trans (hJJr.trans (hΩ.reach_symm h22 (hΩ.conj_mem _ (hΩ.conj_mem K hK g) r)
        (reach_conj hΩ.conj_mem hreachJ r)))
    have h2 := reach_conj hΩ.conj_mem h1 g⁻¹
    rw [rightConjugate_mul, rightConjugate_mul, rightConjugate_mul, mul_inv_cancel,
      rightConjugate_one] at h2
    show reach Ω K (rightConjugate K (g * r * g⁻¹))
    convert h2 using 2
    group
  obtain ⟨E, hER, hE, hE4⟩ := exists_fourGroup_le (hΩ.rank K hK R hR).1
  have hEstab : E ≤ hΩ.compStab h22 (hΩ.conj_mem K hK g) := by
    intro e he
    show reach Ω (rightConjugate K g) (rightConjugate (rightConjugate K g) e)
    have h1 := hinvH e (hER he) (hE.2 e he)
    have h2 := reach_conj hΩ.conj_mem (h1 : reach Ω K (rightConjugate K (g * e * g⁻¹))) g
    rw [rightConjugate_mul, show g * e * g⁻¹ * g = g * e by group] at h2
    rwa [rightConjugate_mul]
  exact hgH (hΩ.reach_of_fourGroup h22 hK (hΩ.conj_mem K hK g) (hER.trans hR'.1) hE hE4 hEstab)

theorem fusionGen_le_compStab (hM : MinCounter Ω) (h22 : Lemma22Four) {K R S : Subgroup G}
    (hK : K ∈ Ω) (hR : IsSylowOf 2 R K) (hS2 : IsPGroup 2 S) (hRS : R ≤ S) :
    L26.fusionGen (L26.gammaSet S (sylowSet Ω)) ≤ hM.setting.compStab h22 hK := by
  have hΩ := hM.setting
  rw [L26.fusionGen, closure_le]
  rintro g ⟨x, ⟨hx1, T₁, ⟨J₁, hJ₁, hT₁⟩, hT₁S, hxT₁⟩, ⟨-, T₂, ⟨J₂, hJ₂, hT₂⟩, hT₂S, hxT₂⟩⟩
  have hT₁' := isSylowOf_iff_card.mp hT₁
  have hT₂' := isSylowOf_iff_card.mp hT₂
  obtain ⟨k, hk⟩ := IsPGroup.of_card hT₁'.2 ⟨x, hxT₁⟩
  have hk' : (g⁻¹ * x * g) ^ (2 ^ k) = 1 := by
    have h := conj_pow (a := g⁻¹) (b := x) (i := 2 ^ k)
    rw [inv_inv] at h
    rw [h, show x ^ (2 ^ k) = 1 by simpa using congrArg Subtype.val hk, mul_one,
      inv_mul_cancel]
  have hy1 : g⁻¹ * x * g ≠ 1 := fun h => hx1 (by
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]
    group)
  have hJ₂J₁ : J₂ = rightConjugate J₁ g :=
    hΩ.eq_of_pGroup_le hJ₂ (hΩ.conj_mem J₁ hJ₁ g) (isPGroup_zpowers_of_two_element hk')
      (zpowers_ne_bot_of_ne_one' hy1) ((zpowers_le).mpr (hT₂'.1 hxT₂)) ((zpowers_le).mpr (by
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using hT₁'.1 hxT₁))
  have h₁ := hM.reach_of_sylow_le h22 hK hR hS2 hRS hJ₁ hT₁ hT₁S
  have h₂ := hM.reach_of_sylow_le h22 hK hR hS2 hRS hJ₂ hT₂ hT₂S
  rw [hJ₂J₁] at h₂
  exact hΩ.mem_compStab_of_reach h22 hK h₁ h₂

theorem conc4_of_isSzOrU3 (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylowOf 2 R K)
    (hRsyl : IsSylowOf 2 R (normalClosure (R : Set G)))
    (hsz : IsSzOrU3 (↥(normalClosure (R : Set G)) ⧸
      CFSG.Assembly.oddCore ↥(normalClosure (R : Set G)))) : Conc4 Ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  have hΩK := hM.lemma312 h22 hB hK
  have hR' := isSylowOf_iff_card.mp hR
  have hKN : K ≤ normalClosure (R : Set G) := by
    rw [← hΩ.perfect K hK]
    refine (closure_le _).mpr fun x hx => ?_
    obtain ⟨hxK, i, hxi⟩ := hx
    obtain ⟨S', hS', hxS'⟩ := exists_isSylowOf_le ((zpowers_le).mpr hxK)
      (isPGroup_zpowers_of_two_element hxi)
    obtain ⟨k, -, hk⟩ := exists_conj_of_isSylowOf hR hS'
    have hx' : x ∈ rightConjugate R k := hk ▸ hxS' (mem_zpowers x)
    rw [mem_rightConjugate_iff] at hx'
    have h1 := normalClosure_normal.conj_mem _ (subset_normalClosure hx') k⁻¹
    simpa [mul_assoc] using h1
  have hN : normalClosure (R : Set G) = ⊤ := by
    rw [eq_top_iff, ← hΩ.generates]
    refine sSup_le fun J hJ => ?_
    rw [hΩK] at hJ
    obtain ⟨a, rfl⟩ := hJ
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have h1 := normalClosure_normal.conj_mem _ (hKN hx) a⁻¹
    simpa [mul_assoc] using h1
  rw [hN] at hsz hRsyl
  have hO : CFSG.Assembly.oddCore ↥(⊤ : Subgroup G) = ⊥ := by
    have h1 := oddCore_map_mulEquiv' (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    have h2 : CFSG.oddCore G = ⊥ := hΩ.oddCore
    rw [h2, map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective] at h1
    exact h1
  have hszG : IsSzOrU3 G :=
    isSzOrU3_of_mulEquiv (Subgroup.topEquiv.symm.trans ((QuotientGroup.quotientMulEquivOfEq
      hO).trans QuotientGroup.quotientBot).symm) hsz
  intro J hJ
  have hJ' := hJ
  rw [hΩK] at hJ'
  obtain ⟨a, rfl⟩ := hJ'
  refine ⟨fun J' hJ' hne => ?_, Or.inr ⟨?_, fun R' hR'' => ?_⟩⟩
  · exfalso
    rw [hΩK] at hJ'
    obtain ⟨b, rfl⟩ := hJ'
    apply hne (a⁻¹ * b)
    rw [rightConjugate_mul, mul_inv_cancel_left]
  · have hJN : normalClosure ((rightConjugate K a : Subgroup G) : Set G) = ⊤ := by
      rw [eq_top_iff, ← hN]
      refine normalClosure_le_normal fun x hx => ?_
      have hxK : x ∈ K := hR'.1 hx
      have h1 : a⁻¹ * x * a ∈ rightConjugate K a := by
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using hxK
      have h2 := normalClosure_normal.conj_mem _ (subset_normalClosure h1) a
      simpa [mul_assoc] using h2
    rw [hJN]
    exact isSzOrU3_of_mulEquiv Subgroup.topEquiv hszG
  · have hJN : normalClosure ((rightConjugate K a : Subgroup G) : Set G) = ⊤ := by
      rw [eq_top_iff, ← hN]
      refine normalClosure_le_normal fun x hx => ?_
      have hxK : x ∈ K := hR'.1 hx
      have h1 : a⁻¹ * x * a ∈ rightConjugate K a := by
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using hxK
      have h2 := normalClosure_normal.conj_mem _ (subset_normalClosure h1) a
      simpa [mul_assoc] using h2
    rw [hJN]
    rw [isSylowOf_iff_card] at hR'' hRsyl ⊢
    refine ⟨le_top, ?_⟩
    rw [hR''.2, rightConjugate_card, ← hR'.2, hRsyl.2]

theorem lemma313 (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    (h26 : L26.Asc76Lemma26) : ∀ K ∈ Ω, ∀ J ∈ Ω, reach Ω K J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  by_contra hcon
  push Not at hcon
  obtain ⟨K, hK, J, hJ, hKJ⟩ := hcon
  obtain ⟨R, hR⟩ := Sec3Setting.exists_sylow K
  obtain ⟨S, hS, hRS, hSgood⟩ := hM.exists_sylow_good hK hR
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (isSylowOf_iff_card.mp hS).2
  have hclosed := hM.strongClosed_gammaSet h22 hB hK hR hS hRS hSgood ⟨J, hJ, hKJ⟩
  have hH := hM.fusionGen_le_compStab h22 hK hR hS2 hRS
  have hHne : hΩ.compStab h22 hK ≠ ⊤ := by
    intro htop
    have hJ' : J ∈ Set.range (rightConjugate K) := hM.lemma312 h22 hB hK ▸ hJ
    obtain ⟨g, rfl⟩ := hJ'
    have hg : g ∈ hΩ.compStab h22 hK := htop ▸ mem_top g
    exact hKJ hg
  have hΔ2 : ∀ T ∈ sylowSet Ω, IsPGroup 2 T := by
    rintro T ⟨L, -, hT⟩
    exact IsPGroup.of_card (isSylowOf_iff_card.mp hT).2
  have hΔinv : ∀ T ∈ sylowSet Ω, ∀ g : G, rightConjugate T g ∈ sylowSet Ω := by
    rintro T ⟨L, hL, hT⟩ g
    exact ⟨rightConjugate L g, hΩ.conj_mem L hL g, isSylowOf_rightConjugate hT g⟩
  have hΔcomm : ∀ T₁ ∈ sylowSet Ω, ∀ T₂ ∈ sylowSet Ω, T₁ ≤ S → T₂ ≤ S → T₁ ≠ T₂ →
      ⁅T₁, T₂⁆ = ⊥ := by
    rintro T₁ ⟨L₁, hL₁, hT₁⟩ T₂ ⟨L₂, hL₂, hT₂⟩ h₁ h₂ hne
    exact hΩ.commute_of_sylow hS2 hL₁ hL₂ hT₁ hT₂ h₁ h₂ hne
  obtain ⟨hm, hΦ⟩ := hΩ.rank K hK R hR
  rcases h26 G S (sylowSet Ω) hS hΔ2 hΔinv hclosed hΔcomm R ⟨K, hK, hR⟩ hRS hm hΦ with
    h | ⟨-, hRsyl, hsz⟩
  · exact hHne (top_le_iff.mp (h ▸ hH))
  · exact hM.not_conc (hM.conc4_of_isSzOrU3 h22 hB hK hR hRsyl hsz)

end CFSG.ComponentClassification.Asc76X.MinCounter
