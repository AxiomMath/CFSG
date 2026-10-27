module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D8

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem not_isCyclic_of_card_four {E : Subgroup G} (hE2 : ∀ e ∈ E, e * e = 1)
    (hE4 : Nat.card E = 4) : ¬ IsCyclic E := by
  intro hc
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top E).mp hc
  have hgE : g ∈ E := hg ▸ mem_zpowers g
  have hord : orderOf g = 4 := by rw [← hE4, ← hg, Nat.card_zpowers]
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hE2 g hgE)
  rw [hord] at hdvd
  omega

omit [Finite G] in
theorem mem_normalizer_of_forall_mul_comm {H : Subgroup G} {g : G}
    (h : ∀ y ∈ H, g * y = y * g) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := h _ hy
    have e : y = g * y * g⁻¹ := by
      calc y = g⁻¹ * ((g * y * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * y * g⁻¹)) := by rw [← h1]
        _ = g * y * g⁻¹ := by group
    rw [e]
    exact hy

@[expose] def IsZInv (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∃ M ∈ Ω, ∃ T V : Subgroup G, IsSylowOf 2 T M ∧ IsDihedralRot V T ∧ x ∈ V ∧ x ≠ 1 ∧ x * x = 1

theorem IsZInv.conj (hΩ : Assumption41 Ω) {x : G} (hx : IsZInv Ω x) (g : G) :
    IsZInv Ω (g⁻¹ * x * g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hM, T, V, hT, hV, hxV, hx1, hxx⟩ := hx
  refine ⟨_, hΩ.conj_mem M hM g, _, _, isSylowOf_rightConjugate hT g, hV.rightConjugate g,
    conj_mem_rightConjugate hxV g, ?_, ?_⟩
  · intro h
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hxx]; group

theorem not_isZInv_mul_of_commute (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω)
    {K K' R R' U : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hKK' : K ≠ K')
    (hR : IsSylowOf 2 R K) (hU : IsDihedralRot U R) (hR' : IsSylowOf 2 R' K')
    (hc : ∀ a ∈ R, ∀ b ∈ R', a * b = b * a) {r r' : G} (hrR : r ∈ R) (hrU : r ∉ U)
    (hr'R : r' ∈ R') (hr'1 : r' ≠ 1) : ¬ IsZInv Ω (r' * r) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨M, hM, T, V, hT, hV, hxV, hx1, hxx⟩
  obtain ⟨z, hzU, hz1, hzz, -, hzR⟩ := hU.exists_involution
  have hrr : r * r = 1 := hU.mul_self r hrR hrU
  have hMK : M ≠ K := by
    intro hMK
    have hr'M : r' ∈ M := by
      have : r' = r' * r * r⁻¹ := by group
      rw [this]
      exact mul_mem (hT.le (hV.le hxV)) (inv_mem (hMK ▸ hR.le hrR))
    have hr'2 : IsPGroup 2 (zpowers r') := hR'.isPGroup.to_le ((zpowers_le).mpr hr'R)
    have h2 := Assumption41.inf_eq_bot hΩ hK hK' hKK' hr'2 ((zpowers_le).mpr (hMK ▸ hr'M))
      ((zpowers_le).mpr (hR'.le hr'R))
    rw [inf_idem] at h2
    exact hr'1 (mem_bot.mp (h2 ▸ mem_zpowers r'))
  have hcr : r * (r' * r) = (r' * r) * r := by rw [← mul_assoc, ← hc _ hrR _ hr'R, mul_assoc]
  have hcz : z * (r' * r) = (r' * r) * z := by
    have h1 := hzR r hrR
    calc z * (r' * r) = (z * r') * r := by group
      _ = (r' * z) * r := by rw [hc _ (hU.le hzU) _ hr'R]
      _ = r' * (z * r) := by group
      _ = r' * (r * z) := by rw [h1]
      _ = r' * r * z := by group
  have hxM : r' * r ∈ M := hT.le (hV.le hxV)
  have hCN := Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hM) hxM hx1 hxx
  set E : Subgroup G := Sec4.fourGroup r z hrr hzz (hzR r hrR) with hEdef
  have hrz : r ≠ z := fun h => hrU (h ▸ hzU)
  have hr1 : r ≠ 1 := fun h => hrU (h ▸ U.one_mem)
  have hE4 : Nat.card E = 4 := card_fourGroup hrr hzz (hzR r hrR) hr1 hz1 hrz
  have hEK : E ≤ K := by
    intro y hy
    obtain h | h | h | h := (mem_fourGroup).mp hy
    · rw [h]; exact one_mem _
    · rw [h]; exact hR.le hrR
    · rw [h]; exact hR.le (hU.le hzU)
    · rw [h]; exact mul_mem (hR.le hrR) (hR.le (hU.le hzU))
  have hEM : E ≤ normalizer (M : Set G) := by
    intro y hy
    apply hCN
    rw [mem_centralizer_singleton_iff]
    obtain h | h | h | h := (mem_fourGroup).mp hy
    · rw [h]; simp
    · rw [h]; exact hcr
    · rw [h]; exact hcz
    · rw [h]
      calc r * z * (r' * r) = r * (z * (r' * r)) := by group
        _ = r * ((r' * r) * z) := by rw [hcz]
        _ = (r * (r' * r)) * z := by group
        _ = (r' * r * r) * z := by rw [hcr]
        _ = r' * r * (r * z) := by group
  have hEsq : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have := (isElemAbelian_fourGroup hrr hzz (hzR r hrR)).2 e he
    rwa [pow_two] at this
  have hE2 : IsPGroup 2 E := fun e => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, pow_two, OneMemClass.coe_one]; exact hEsq e e.2)⟩
  obtain ⟨Vs, hVs, hEVs⟩ := exists_isSylowOf_le hE2 (le_inf hEK hEM)
  obtain ⟨RM, hRM, hVsRM⟩ := exists_isSylowOf_normalized hVs.isPGroup (hVs.le.trans inf_le_right)
  obtain ⟨UM, hUM⟩ := Assumption41.exists_rot hΩ hM hRM
  have hVs1 : Vs ≠ ⊥ := by
    intro h
    have : Nat.card E ≤ Nat.card Vs := card_le_of_le hEVs
    rw [h, card_bot, hE4] at this
    omega
  have hKM : K ≤ normalizer (M : Set G) ∧ M ≤ normalizer (K : Set G) := by
    rcases lemma415 h22 hΩ hM hK hRM hUM hVs hVs1 hVsRM with ⟨-, h1, h2⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨h2, -⟩
    · exact ⟨h1, h2⟩
    · exfalso
      have hcyc : IsCyclic Vs := by
        have := hUM.isCyclic
        exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
      have hEc : IsCyclic E := Subgroup.isCyclic_of_le hEVs
      exact not_isCyclic_of_card_four hEsq hE4 hEc
    · exfalso
      have : Nat.card E ≤ Nat.card Vs := card_le_of_le hEVs
      omega
  have hRR' : R ≤ normalizer (R' : Set G) := fun a ha =>
    mem_normalizer_of_forall_mul_comm fun b hb => hc a ha b hb
  have hP2 : IsPGroup 2 (R ⊔ R' : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hR.isPGroup hR'.isPGroup hRR'
  have hodd := hΩ.inter K hK M hM hMK.symm
  have hxR : ∀ y ∈ R, (r' * r) * y = y * (r' * r) := by
    intro y hy
    set c := (r' * r) * y * (r' * r)⁻¹ * y⁻¹ with hcdef
    have hcK : c ∈ K := by
      have h1 : (r' * r) * y * (r' * r)⁻¹ ∈ K :=
        (mem_normalizer_iff.mp (hKM.2 hxM) y).mp (hR.le hy)
      exact mul_mem h1 (inv_mem (hR.le hy))
    have hcM : c ∈ M := by
      have h1 : y * (r' * r)⁻¹ * y⁻¹ ∈ M :=
        (mem_normalizer_iff.mp (hKM.1 (hR.le hy)) _).mp (inv_mem hxM)
      have : c = (r' * r) * (y * (r' * r)⁻¹ * y⁻¹) := by rw [hcdef]; group
      rw [this]
      exact mul_mem hxM h1
    have hcP : c ∈ R ⊔ R' := by
      have hx : r' * r ∈ R ⊔ R' := mul_mem (mem_sup_right hr'R) (mem_sup_left hrR)
      exact mul_mem (mul_mem (mul_mem hx (mem_sup_left hy)) (inv_mem hx))
        (inv_mem (mem_sup_left hy))
    have hbot : (K ⊓ M) ⊓ (R ⊔ R') = ⊥ :=
      eq_bot_of_isPGroup_of_odd (hP2.to_le inf_le_right)
        (hodd.of_dvd_nat (card_dvd_of_le inf_le_left))
    have hc1 : c = 1 := by
      have : c ∈ (K ⊓ M) ⊓ (R ⊔ R') := mem_inf.mpr ⟨mem_inf.mpr ⟨hcK, hcM⟩, hcP⟩
      rw [hbot, mem_bot] at this
      exact this
    have := mul_inv_eq_one.mp hc1
    calc r' * r * y = (r' * r) * y * (r' * r)⁻¹ * (r' * r) := by group
      _ = y * (r' * r) := by rw [this]
  apply hrU
  refine hU.mem_of_commute hrR fun u hu => ?_
  have h1 := hxR u (hU.le hu)
  have h2 := hc u (hU.le hu) r' hr'R
  have : r' * (r * u) = r' * (u * r) := by
    calc r' * (r * u) = r' * r * u := by group
      _ = u * (r' * r) := h1
      _ = (u * r') * r := by group
      _ = (r' * u) * r := by rw [h2]
      _ = r' * (u * r) := by group
  exact mul_left_cancel this

theorem dStarAdj_of_le_isPGroup (hΩ : Assumption41 Ω) {P K J R T : Subgroup G}
    (hP : IsPGroup 2 P) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hR : IsSylowOf 2 R K) (hT : IsSylowOf 2 T J)
    (hRP : R ≤ P) (hTP : T ≤ P) : DStarAdj Ω K J := by
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  obtain ⟨V, hV⟩ := Assumption41.exists_rot hΩ hJ hT
  have hUW : U ≤ sec4W Ω P := le_sec4W (hU.le.trans hRP) (isRot_of hK hR hU)
  have hVW : V ≤ sec4W Ω P := le_sec4W (hV.le.trans hTP) (isRot_of hJ hT hV)
  have hc := isMulCommutative_sec4W hΩ hP
  exact dStarAdj_of_commute hΩ hK hJ hR hU hT hV fun u hu v hv =>
    congrArg Subtype.val (hc.is_comm.comm ⟨u, hUW hu⟩ ⟨v, hVW hv⟩)

omit [Finite G] in
theorem IsDihedralRot.le_of_forall_not_mem {U R H : Subgroup G} (hU : IsDihedralRot U R)
    (h : ∀ x ∈ R, x ∉ U → x ∈ H) : R ≤ H := by
  obtain ⟨x, hxR, hxU⟩ := hU.exists_not_mem
  intro y hy
  by_cases hyU : y ∈ U
  · have h1 : y * x ∈ R := R.mul_mem hy hxR
    have h2 : y * x ∉ U := fun h' => hxU (by
      have : x = y⁻¹ * (y * x) := by group
      rw [this]
      exact U.mul_mem (inv_mem hyU) h')
    have : y = (y * x) * x⁻¹ := by group
    rw [this]
    exact H.mul_mem (h _ h1 h2) (inv_mem (h x hxR hxU))
  · exact h y hy hyU

theorem mem_setStab_dStarComp (hΩ : Assumption41 Ω) {J : Subgroup G} {r : G}
    (hr : AschbacherTightEmbedding.rightConjugate J r ∈ dStarComp Ω J) :
    r ∈ setStab (dStarComp Ω J) := by
  have hr' : AschbacherTightEmbedding.rightConjugate J r⁻¹ ∈ dStarComp Ω J := by
    have h1 := reflTransGen_dStarAdj_rightConjugate hΩ hr r⁻¹
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
    exact reflTransGen_dStarAdj_symm h1
  intro L
  constructor
  · intro hL
    exact Relation.ReflTransGen.trans hr (reflTransGen_dStarAdj_rightConjugate hΩ hL r)
  · intro hL
    have h1 := reflTransGen_dStarAdj_rightConjugate hΩ hL r⁻¹
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
    exact Relation.ReflTransGen.trans hr' h1

omit [Finite G] in
theorem setStab_le_normalizer_sSup (Λ : Set (Subgroup G)) :
    setStab Λ ≤ normalizer ((sSup Λ : Subgroup G) : Set G) :=
  le_normalizer_sSup fun J hJ _ hy => (hy J).mp hJ

theorem exists_isSylowOf_commute_rightConjugate (hΩ : Assumption41 Ω) {K R W : Subgroup G}
    (hK : K ∈ Ω) (hR : IsSylowOf 2 R K) (hRW : R ≤ normalizer (W : Set G)) {t : G}
    (htt : t * t = 1) (htW : t ∈ normalizer (W : Set G))
    (hKt : AschbacherTightEmbedding.rightConjugate K t ≠ K)
    (h2 : K ≤ normalizer (AschbacherTightEmbedding.rightConjugate K t : Set G)) :
    ∃ R₁, IsSylowOf 2 R₁ K ∧ R₁ ≤ normalizer (W : Set G) ∧
      ∀ a ∈ R₁, ∀ b ∈ AschbacherTightEmbedding.rightConjugate R₁ t, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' := AschbacherTightEmbedding.rightConjugate K t with hK'def
  have hconjt : ∀ y : G, t * (t * y * t⁻¹) * t⁻¹ = y := by
    intro y
    calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
      _ = y := by rw [htt]; group
  have hnK' : ∀ x, x ∈ normalizer (K' : Set G) ↔ t * x * t⁻¹ ∈ normalizer (K : Set G) := by
    intro x
    rw [hK'def, normalizer_rightConjugate, mem_rightConjugate_iff]
  have hnK : ∀ x, x ∈ normalizer (K : Set G) ↔ t * x * t⁻¹ ∈ normalizer (K' : Set G) := by
    intro x
    rw [hnK', hconjt]
  have hnW : ∀ x, x ∈ normalizer (W : Set G) ↔ t * x * t⁻¹ ∈ normalizer (W : Set G) := by
    intro x
    constructor
    · intro hx
      exact mul_mem (mul_mem htW hx) (inv_mem htW)
    · intro hx
      have := mul_mem (mul_mem (inv_mem htW) hx) htW
      have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
      rwa [e] at this
  set B : Subgroup G := normalizer (W : Set G) ⊓ normalizer (K : Set G) ⊓
    normalizer (K' : Set G) with hBdef
  have htB : t ∈ normalizer (B : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    simp only [hBdef, mem_inf]
    rw [hnW x, hnK x, hnK' x]
    tauto
  have htP : IsPGroup 2 (zpowers t) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact htt)
  obtain ⟨Q, hQ, htQ⟩ := exists_isSylowOf_normalized htP ((zpowers_le).mpr htB)
  have htQ' : t ∈ normalizer (Q : Set G) := htQ (mem_zpowers t)
  set N : Subgroup G := K ⊓ normalizer (W : Set G) with hNdef
  have hNB : N ≤ B := by
    intro x hx
    obtain ⟨hxK, hxW⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hxW, le_normalizer hxK⟩, h2 hxK⟩
  have hBN : B ≤ normalizer (N : Set G) := by
    intro x hx
    obtain ⟨hx1, -⟩ := mem_inf.mp hx
    obtain ⟨hxW, hxK⟩ := mem_inf.mp hx1
    exact inf_le_normalizer_inf (mem_inf.mpr ⟨hxK, le_normalizer hxW⟩)
  have hQN : IsSylowOf 2 (Q ⊓ N) N := hQ.inf_of_le_normalizer hNB hBN
  have hR₁ : IsSylowOf 2 (Q ⊓ N) K :=
    isSylowOf_of_isSylowOf_le hR (le_inf hR.le hRW) inf_le_left hQN
  refine ⟨Q ⊓ N, hR₁, inf_le_right.trans inf_le_right, ?_⟩
  intro a ha b hb
  rw [mem_rightConjugate_iff] at hb
  obtain ⟨haQ, haN⟩ := mem_inf.mp ha
  obtain ⟨hbQ', hbN'⟩ := mem_inf.mp hb
  have haK : a ∈ K := (mem_inf.mp haN).1
  have hbQ : b ∈ Q := by
    have := (mem_normalizer_iff.mp (inv_mem htQ') _).mp hbQ'
    have e : t⁻¹ * (t * b * t⁻¹) * t⁻¹⁻¹ = b := by group
    rwa [e] at this
  have hbK' : b ∈ K' := by
    rw [hK'def, mem_rightConjugate_iff]
    exact (mem_inf.mp hbN').1
  have haB : a ∈ B := hQ.le haQ
  have hbB : b ∈ B := hQ.le hbQ
  set c := a * b * a⁻¹ * b⁻¹ with hcdef
  have hcQ : c ∈ Q := mul_mem (mul_mem (mul_mem haQ hbQ) (inv_mem haQ)) (inv_mem hbQ)
  have hcK : c ∈ K := by
    have hbNK : b ∈ normalizer (K : Set G) := (mem_inf.mp (mem_inf.mp hbB).1).2
    have h3 : b * a⁻¹ * b⁻¹ ∈ K := (mem_normalizer_iff.mp hbNK _).mp (inv_mem haK)
    have e : c = a * (b * a⁻¹ * b⁻¹) := by rw [hcdef]; group
    rw [e]
    exact mul_mem haK h3
  have hcK' : c ∈ K' := by
    have haNK' : a ∈ normalizer (K' : Set G) := (mem_inf.mp haB).2
    have h3 : a * b * a⁻¹ ∈ K' := (mem_normalizer_iff.mp haNK' _).mp hbK'
    exact mul_mem h3 (inv_mem hbK')
  have hodd := hΩ.inter K hK K' (hΩ.conj_mem K hK t) (fun h => hKt h.symm)
  have hbot : (K ⊓ K') ⊓ Q = ⊥ :=
    eq_bot_of_isPGroup_of_odd (hQ.isPGroup.to_le inf_le_right)
      (hodd.of_dvd_nat (card_dvd_of_le inf_le_left))
  have hc1 : c ∈ (K ⊓ K') ⊓ Q := mem_inf.mpr ⟨mem_inf.mpr ⟨hcK, hcK'⟩, hcQ⟩
  rw [hbot, mem_bot] at hc1
  calc a * b = c * (b * a) := by rw [hcdef]; group
    _ = b * a := by rw [hc1, one_mul]

theorem dStarAdj_or_isZInv (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω) {J T₀ V₀ : Subgroup G}
    (hJ : J ∈ Ω) (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀) {t : G} (htV : t ∈ V₀)
    (ht1 : t ≠ 1) (htt : t * t = 1) (r : G) (hc : t * (r⁻¹ * t * r) = (r⁻¹ * t * r) * t) :
    DStarAdj Ω J (AschbacherTightEmbedding.rightConjugate J r) ∨
      IsZInv Ω (t * (r⁻¹ * t * r)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hadj, hz⟩ := hcon
  set t' := r⁻¹ * t * r with ht'def
  set L := AschbacherTightEmbedding.rightConjugate J r with hLdef
  have htJ : t ∈ J := hT₀.le (hV₀.le htV)
  have hL : L ∈ Ω := hΩ.conj_mem J hJ r
  have ht'L : t' ∈ L := conj_mem_rightConjugate htJ r
  have ht'1 : t' ≠ 1 := by
    intro h
    apply ht1
    calc t = r * t' * r⁻¹ := by rw [ht'def]; group
      _ = 1 := by rw [h]; group
  have ht't' : t' * t' = 1 := by
    calc t' * t' = r⁻¹ * (t * t) * r := by rw [ht'def]; group
      _ = 1 := by rw [htt]; group
  have ht'C : t' ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr hc.symm
  have ht'N : t' ∈ normalizer (J : Set G) :=
    Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ) htJ ht1 htt ht'C
  obtain ⟨z₀, -, -, -, hz₀uniq, hz₀T⟩ := hV₀.exists_involution
  have htz₀ : t = z₀ := (hz₀uniq t htV htt).resolve_left ht1
  have hT₀C : T₀ ≤ J ⊓ centralizer ({t} : Set G) := by
    refine le_inf hT₀.le fun y hy => ?_
    rw [mem_centralizer_singleton_iff, htz₀]
    exact hz₀T y hy
  have ht'P : IsPGroup 2 (zpowers t') :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact ht't')
  have ht'H : zpowers t' ≤
      normalizer ((J ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
    (zpowers_le).mpr (inf_le_normalizer_inf (mem_inf.mpr ⟨ht'N, le_normalizer ht'C⟩))
  obtain ⟨T, hT, ht'T⟩ := exists_isSylowOf_normalized ht'P ht'H
  have ht'T' : t' ∈ normalizer (T : Set G) := ht'T (mem_zpowers t')
  have hTJ : IsSylowOf 2 T J := isSylowOf_of_isSylowOf_le hT₀ hT₀C inf_le_left hT
  obtain ⟨V, hV⟩ := Assumption41.exists_rot hΩ hJ hTJ
  have htP : IsPGroup 2 (zpowers t) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact htt)
  have hTt : ∀ y ∈ T, t * y = y * t := fun y hy =>
    (mem_centralizer_singleton_iff.mp (mem_inf.mp (hT.le hy)).2).symm
  have htT : t ∈ T := by
    have hP : IsPGroup 2 (zpowers t ⊔ T : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' htP hT.isPGroup
        ((zpowers_le).mpr (mem_normalizer_of_forall_mul_comm hTt))
    have hle : zpowers t ⊔ T ≤ J ⊓ centralizer ({t} : Set G) :=
      sup_le ((zpowers_le).mpr (mem_inf.mpr ⟨htJ, mem_centralizer_singleton_iff.mpr rfl⟩))
        hT.le
    have heq := hT.eq_of_le le_sup_right hle hP
    rw [← heq]
    exact mem_sup_left (mem_zpowers t)
  obtain ⟨z₁, hz₁V, -, -, hz₁uniq, -⟩ := hV.exists_involution
  have htV' : t ∈ V := by
    rcases hV.eq_of_central hz₁uniq htT hTt with h | h
    · exact absurd h ht1
    · rw [h]
      exact hz₁V
  have hinv := conj_eq_inv_of_not_dStarAdj h22 hΩ hL hJ hadj ht'L ht'1 ht't' ht'N hTJ hV ht'T'
  have hpow : t ^ (Nat.card V / 2) = 1 := by
    obtain ⟨k, hk⟩ := (hV.isPGroup.to_le hV.le).exists_card_eq
    have h4 := hV.four_le
    rw [hk] at h4
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · simp at h4
      · simp at h4
      · omega
    have h4dvd : 4 ∣ Nat.card V := by
      rw [hk]
      have := Nat.pow_dvd_pow 2 hk2
      simpa using this
    obtain ⟨m, hm⟩ := h4dvd
    have e : Nat.card V / 2 = 2 * m := by omega
    rw [e, pow_mul, pow_two, htt, one_pow]
  obtain ⟨v, hvV, hvt⟩ := hV.exists_sq_of_pow_half_eq_one htV' hpow
  have hv := hinv v hvV
  have key : t * t' = v⁻¹ * t' * v := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have h1 : t' * v = v⁻¹ * t' := by
      calc t' * v = (t' * v * t'⁻¹) * t' := by group
        _ = v⁻¹ * t' := by rw [hv]
    calc t * t' = (v * v)⁻¹ * t' := by rw [← hvt, htinv]
      _ = v⁻¹ * (v⁻¹ * t') := by group
      _ = v⁻¹ * (t' * v) := by rw [h1]
      _ = v⁻¹ * t' * v := by group
  apply hz
  rw [key]
  have ht'Z : IsZInv Ω t' := IsZInv.conj hΩ ⟨J, hJ, T₀, V₀, hT₀, hV₀, htV, ht1, htt⟩ r
  exact ht'Z.conj hΩ v

theorem MinCounter.rightConjugate_eq_of_mem_omegaD (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) {K₀ : Subgroup G} (hK₀ : K₀ ∈ omegaD Ω (sec4W Ω S))
    (hX : sSup (dStarComp Ω K₀) ≠ ⊤) {J T₀ V₀ : Subgroup G} (hJ : J ∈ Ω)
    (hJC : J ∉ dStarComp Ω K₀) (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀) {t : G}
    (htV : t ∈ V₀) (ht1 : t ≠ 1) (htt : t * t = 1)
    (htW : t ∈ normalizer (sec4W Ω S : Set G)) {K : Subgroup G}
    (hK : K ∈ omegaD Ω (sec4W Ω S)) : AschbacherTightEmbedding.rightConjugate K t = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  by_contra hKt
  obtain ⟨hKΩ, R, hR, hRW⟩ := hK
  have hKD : K ∈ omegaD Ω (sec4W Ω S) := ⟨hKΩ, R, hR, hRW⟩
  have hRt := (hM.rightConjugate_eq_or_le_normalizer h22 hK₀ hX hJ hJC hT₀ hV₀ htV ht1 htt htW
    hKΩ hR hRW).resolve_left hKt
  set K' := AschbacherTightEmbedding.rightConjugate K t with hK'def
  have hK' : K' ∈ Ω := hΩ.conj_mem K hKΩ t
  have hKK' : K ≠ K' := fun h => hKt h.symm
  obtain ⟨-, h2⟩ :=
    le_normalizer_of_sylow h22 hΩ hKΩ hK' hKK' (isSylowOf_rightConjugate hR t) hRt
  obtain ⟨R₁, hR₁, -, hc⟩ :=
    exists_isSylowOf_commute_rightConjugate hΩ hKΩ hR hRW htt htW hKt h2
  obtain ⟨U₁, hU₁⟩ := Assumption41.exists_rot hΩ hKΩ hR₁
  have hR₁' : IsSylowOf 2 (AschbacherTightEmbedding.rightConjugate R₁ t) K' :=
    isSylowOf_rightConjugate hR₁ t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hR₁J : R₁ ≤ setStab (dStarComp Ω J) := by
    refine hU₁.le_of_forall_not_mem fun r hrR hrU => ?_
    apply mem_setStab_dStarComp hΩ
    have hrr : r * r = 1 := hU₁.mul_self r hrR hrU
    have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
    set r' := t⁻¹ * r * t with hr'def
    have hr'R : r' ∈ AschbacherTightEmbedding.rightConjugate R₁ t :=
      conj_mem_rightConjugate hrR t
    have hr'1 : r' ≠ 1 := by
      intro h
      have hr1 : r ≠ 1 := fun h' => hrU (h' ▸ U₁.one_mem)
      apply hr1
      calc r = t * r' * t⁻¹ := by rw [hr'def]; group
        _ = 1 := by rw [h]; group
    have hrr' := hc r hrR r' hr'R
    have e : t * (r⁻¹ * t * r) = r' * r := by
      rw [hrinv, hr'def, htinv]
      group
    have e' : (r⁻¹ * t * r) * t = r * r' := by
      rw [hrinv, hr'def, htinv]
      group
    have hcomm : t * (r⁻¹ * t * r) = (r⁻¹ * t * r) * t := by
      rw [e, e', hrr']
    have hnz := not_isZInv_mul_of_commute h22 hΩ hKΩ hK' hKK' hR₁ hU₁ hR₁' hc hrR hrU hr'R hr'1
    rcases dStarAdj_or_isZInv h22 hΩ hJ hT₀ hV₀ htV ht1 htt r hcomm with h | h
    · exact Relation.ReflTransGen.single h
    · rw [e] at h
      exact absurd h hnz
  have hR₁Y : R₁ ≤ normalizer ((sSup (dStarComp Ω J) : Subgroup G) : Set G) :=
    hR₁J.trans (setStab_le_normalizer_sSup _)
  obtain ⟨P, hP, hR₁P⟩ := exists_isSylowOf_normalized hR₁.isPGroup hR₁Y
  have hJY : J ≤ sSup (dStarComp Ω J) := le_sSup Relation.ReflTransGen.refl
  obtain ⟨P₀, hP₀, hT₀P₀⟩ := exists_isSylowOf_le hT₀.isPGroup (hT₀.le.trans hJY)
  obtain ⟨k, hkY, hk⟩ := L26.IsSylowOf.exists_conj_mem hP hP₀
  have hJ₁ : AschbacherTightEmbedding.rightConjugate J k ∈ Ω := hΩ.conj_mem J hJ k
  have hJ₁C : AschbacherTightEmbedding.rightConjugate J k ∈ dStarComp Ω J := by
    have hkS : k ∈ setStab (dStarComp Ω J) :=
      (sSup_le fun L hL => le_setStab_dStarComp hΩ hL) hkY
    exact (hkS J).mp Relation.ReflTransGen.refl
  have hT₁ : IsSylowOf 2 (AschbacherTightEmbedding.rightConjugate T₀ k)
      (AschbacherTightEmbedding.rightConjugate J k) := isSylowOf_rightConjugate hT₀ k
  have hT₁P : AschbacherTightEmbedding.rightConjugate T₀ k ≤ P := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have := (hk (k * x * k⁻¹)).mp (hT₀P₀ hx)
    have e : k⁻¹ * (k * x * k⁻¹) * k = x := by group
    rwa [e] at this
  have hP2 : IsPGroup 2 (R₁ ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hR₁.isPGroup hP.isPGroup hR₁P
  have hadj := dStarAdj_of_le_isPGroup hΩ hP2 hKΩ hJ₁ hR₁ hT₁ le_sup_left
    (hT₁P.trans le_sup_right)
  apply hJC
  have hKC : K ∈ dStarComp Ω K₀ := (hM.dStarComp_eq_omegaD hK₀ hX) ▸ hKD
  exact (Relation.ReflTransGen.tail hKC hadj).trans (reflTransGen_dStarAdj_symm hJ₁C)

end CFSG.ComponentClassification.Asc76.Sec4
