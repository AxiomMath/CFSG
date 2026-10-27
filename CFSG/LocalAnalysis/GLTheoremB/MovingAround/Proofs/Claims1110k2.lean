module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110k
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Certified
import CFSG.HardMathSupport.Solomon.Coordinator.I22_7Rk
import CFSG.HardMathSupport.Solomon.Coordinator.I22_7Cop
import CFSG.HardMathSupport.Solomon.Coordinator.I22_7MainQ
import CFSG.HardMathSupport.Solomon.Coordinator.I22_7UMain
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110j
import CFSG.HardMathSupport.Solomon.Coordinator.I22_7CmpB

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110k

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

section GLBCore

variable {K : Type} [Group K] [Finite K]

theorem normalizer_le_glbCore_three {P Q : Subgroup K} (hQP : Q ≤ P)
    (hr : 3 ≤ CFSG.Open.pRank 3 Q) : Subgroup.normalizer (Q : Set K) ≤ GLBCore 3 3 P :=
  le_sSup ⟨Q, hQP, hr, rfl⟩

theorem top_le_glbCore_three_conj {P : Subgroup K} (h : (⊤ : Subgroup K) ≤ GLBCore 3 3 P) (g : K) :
    (⊤ : Subgroup K) ≤ GLBCore 3 3 (GLBConj g P) := by
  have h2 := gLBConj_mono g h
  have htop : GLBConj g (⊤ : Subgroup K) = ⊤ := by
    ext z
    simp [mem_gLBConj]
  rw [htop] at h2
  exact h2.trans (Lemma118T.glbCore_gLBConj_le' (by norm_num) P g)

theorem top_le_glbCore_three_of_sylow {P0 P : Subgroup K}
    (hP0 : Nat.card P0 = 3 ^ (Nat.card K).factorization 3)
    (hP : Nat.card P = 3 ^ (Nat.card K).factorization 3) (h : (⊤ : Subgroup K) ≤ GLBCore 3 3 P0) :
    (⊤ : Subgroup K) ≤ GLBCore 3 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S0 : Sylow 3 K := Sylow.ofCard P0 hP0
  let S1 : Sylow 3 K := Sylow.ofCard P hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S0 S1
  have hS1 : (S1 : Subgroup K) = GLBConj g⁻¹ P0 := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    simp [GLBConj]
    rfl
  have hPeq : P = GLBConj g⁻¹ P0 := hS1
  rw [hPeq]
  exact top_le_glbCore_three_conj h g⁻¹

theorem normal_le_glbCore_three_of_coprime (N : Subgroup K) [N.Normal] (hN : Nat.Coprime 3 (Nat.card N))
    (P : Subgroup K) (hrk : 4 ≤ CFSG.Open.pRank 3 P) : N ≤ GLBCore 3 3 P := by
  classical
  have h3 : 1 < 3 := by norm_num
  obtain ⟨E, hEP, hE, hcard⟩ := CFSG.SectionRank.exists_pRank h3 P
  set r := CFSG.Open.pRank 3 P with hr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEA : CFSG.IsElementaryAbelian 3 E :=
    { hE.1 with
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hE.2 (a : K) a.2) }
  have hnt : Nontrivial E := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hcard]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have hN3 : ¬ 3 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hN
  let : MulDistribMulAction E N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp E.subtype)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 3) (A := E) (H := N) hN3
  have hle : ∀ B : Subgroup E, B.index = 3 →
      (CFSG.fixedPointSubgroup B N).map N.subtype ≤ GLBCore 3 3 P := by
    intro B hB
    set Q : Subgroup K := B.map E.subtype with hQ
    have hQE : Q ≤ E := Subgroup.map_subtype_le B
    have hQP : Q ≤ P := hQE.trans hEP
    have hcardQ : Nat.card Q = 3 ^ (r - 1) := by
      have h1 : Nat.card B * 3 = 3 ^ r := by
        rw [← hcard, ← hB]
        exact Subgroup.card_mul_index B
      have h2 : 3 ^ r = 3 ^ (r - 1) * 3 := by
        rw [← pow_succ]
        congr 1
        omega
      have h3' : Nat.card B = 3 ^ (r - 1) := by
        rw [h2] at h1
        exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
      rw [hQ, Subgroup.card_map_of_injective E.subtype_injective]
      exact h3'
    have hQab : CFSG.Open.IsElemAbelian 3 Q := CFSG.Open.IsElemAbelian.mono hE hQE
    have hrQ : 3 ≤ CFSG.Open.pRank 3 Q := by
      have := CFSG.SectionRank.le_pRank h3 le_rfl hQab hcardQ
      omega
    rintro _ ⟨n, hn, rfl⟩
    refine normalizer_le_glbCore_three hQP hrQ ?_
    have hc : N.subtype n ∈ Subgroup.centralizer (Q : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have h : (b : K) * n * (b : K)⁻¹ = n := congrArg Subtype.val (hn ⟨b, hb⟩)
      change (b : K) * n = n * (b : K)
      calc (b : K) * n = (b : K) * n * (b : K)⁻¹ * b := by group
        _ = n * b := by rw [h]
    exact Subgroup.centralizer_le_normalizer (Q : Set K) hc
  have hmap : (⊤ : Subgroup N).map N.subtype ≤ GLBCore 3 3 P := by
    have h : (⨆ (B : Subgroup E) (_ : B.index = 3), CFSG.fixedPointSubgroup B N).map N.subtype
        ≤ GLBCore 3 3 P := by
      simp only [Subgroup.map_iSup]
      exact iSup₂_le fun B hB => hle B hB
    rwa [hgen] at h
  intro x hx
  exact hmap ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

theorem top_le_glbCore_three_of_quotient (N : Subgroup K) [N.Normal] (hN : Nat.Coprime 3 (Nat.card N))
    (P : Subgroup K) (hP : IsPGroup 3 P) (hrk : 4 ≤ CFSG.Open.pRank 3 P)
    (hquot : (⊤ : Subgroup (K ⧸ N)) ≤ GLBCore 3 3 (P.map (QuotientGroup.mk' N))) :
    (⊤ : Subgroup K) ≤ GLBCore 3 3 P := by
  have h3 : 1 < 3 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : K →* K ⧸ N := QuotientGroup.mk' N with hπ
  have hPN : P ⊓ N = ⊥ := CFSG.HardMathSupport.Solomon.Coordinator.i227cop_inf_eq_bot hP hN
  have hinjP : ∀ {T : Subgroup K}, T ≤ P → ∀ x ∈ T, π x = 1 → x = 1 := by
    intro T hT x hx h1
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 h1
    have : x ∈ P ⊓ N := ⟨hT hx, hxN⟩
    rwa [hPN, Subgroup.mem_bot] at this
  have hNH : N ≤ GLBCore 3 3 P := normal_le_glbCore_three_of_coprime N hN P hrk
  have hH : GLBCore 3 3 (P.map π) ≤ (GLBCore 3 3 P).map π := by
    refine sSup_le ?_
    rintro _ ⟨Qb, hQP, hr, rfl⟩
    set Q : Subgroup K := P ⊓ Qb.comap π with hQ
    have hQP' : Q ≤ P := inf_le_left
    have hQmap : Q.map π = Qb := by
      ext y
      constructor
      · rintro ⟨x, ⟨_, hx2⟩, rfl⟩
        exact hx2
      · intro hy
        obtain ⟨x, hxP, rfl⟩ := hQP hy
        exact ⟨x, ⟨hxP, hy⟩, rfl⟩
    have hr' : 3 ≤ CFSG.Open.pRank 3 Q := by
      have := CFSG.HardMathSupport.Solomon.Coordinator.i227cop_pRank_map_le π (hinjP hQP') h3
      rw [hQmap] at this
      omega
    intro xb hxb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    have hxn : ∀ h : K ⧸ N, h ∈ Qb ↔ (x : K ⧸ N) * h * (x : K ⧸ N)⁻¹ ∈ Qb :=
      Subgroup.mem_normalizer_iff.1 hxb
    have hx' : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q ⊔ N := by
      intro q hq
      have hqb : π q ∈ Qb := hQmap ▸ Subgroup.mem_map_of_mem π hq
      have h1 : π (x * q * x⁻¹) ∈ Qb := by
        have := (hxn (π q)).1 hqb
        simpa [hπ] using this
      rw [← hQmap] at h1
      obtain ⟨q', hq', hqq⟩ := h1
      have h2 : q'⁻¹ * (x * q * x⁻¹) ∈ N := by
        refine (QuotientGroup.eq_one_iff _).1 ?_
        change π (q'⁻¹ * (x * q * x⁻¹)) = 1
        rw [map_mul, map_inv, hqq, inv_mul_cancel]
      have h3 : x * q * x⁻¹ = q' * (q'⁻¹ * (x * q * x⁻¹)) := by group
      rw [h3]
      exact Subgroup.mul_mem_sup hq' h2
    obtain ⟨y, hy, n, hn, rfl⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.i227cop_exists_normalizer_mul hN (hP.to_le hQP') x hx'
    refine ⟨y, normalizer_le_glbCore_three hQP' hr' hy, ?_⟩
    have hn1 : π n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    show π y = π (y * n)
    rw [map_mul, hn1, mul_one]
  intro k _
  have h1 : π k ∈ GLBCore 3 3 (P.map π) := hquot (Subgroup.mem_top _)
  obtain ⟨h, hh, hhk⟩ := hH h1
  have h2 : h⁻¹ * k ∈ N := QuotientGroup.eq.1 hhk
  have h4 : k = h * (h⁻¹ * k) := by group
  rw [h4]
  exact mul_mem hh (hNH h2)

end GLBCore

theorem map_glbCore_three_subtype_le {G : Type} [Group G] [Finite G] (J : Subgroup G) (P : Subgroup ↥J) :
    (GLBCore 3 3 P).map J.subtype ≤ GLBCore 3 3 (P.map J.subtype) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le ?_
  rintro _ ⟨Q, hQP, hr, rfl⟩
  rw [← Subgroup.map_le_iff_le_comap]
  have hr' : 3 ≤ CFSG.Open.pRank 3 (Q.map J.subtype) :=
    hr.trans (CFSG.SectionRank.pRank_le_map (by norm_num) J.subtype J.subtype_injective Q)
  exact (Subgroup.le_normalizer_map J.subtype).trans
    (le_sSup ⟨Q.map J.subtype, Subgroup.map_mono hQP, hr', rfl⟩)

section Components

variable {K : Type} [Group K] [Finite K]

open CFSG.HardMathSupport.Solomon.Coordinator (i227cmp_elem_family i227cmp_zpowers_inter i227cmp_isPGroup_of_elem)
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs (exists_sylow_ge le_sup_normalizer_of_sylow)

theorem top_le_glbCore_three_of_components (O : Set (Subgroup K))
    (hconj : ∀ k : K, ∀ L ∈ O, GLBConj k L ∈ O) (hcard : 4 ≤ Nat.card O)
    (hx : ∀ L ∈ O, ∃ x ∈ L, orderOf x = 3 ∧ ∃ y ∈ L, x * y ≠ y * x)
    (hcomm : ∀ L ∈ O, ∀ L' ∈ O, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (P : Subgroup K) (hPc : Nat.card P = 3 ^ (Nat.card K).factorization 3) :
    (⊤ : Subgroup K) ≤ GLBCore 3 3 P := by
  classical
  let _ : Fintype O := Fintype.ofFinite O
  choose x hxL hxo hxn using fun L : O => hx L.1 L.2
  have hcx : ∀ i j : O, i ≠ j → Commute (x i) (x j) := fun i j hij =>
    hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) _ (hxL i) _ (hxL j)
  have hind : iSupIndep fun i : O => Subgroup.zpowers (x i) := by
    intro i
    rw [Subgroup.disjoint_def]
    intro y hy1 hy2
    have hle : (⨆ (j : O) (_ : j ≠ i), Subgroup.zpowers (x j)) ≤
        Subgroup.centralizer (i.1 : Set K) := by
      refine iSup₂_le fun j hj => ?_
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm i.1 i.2 j.1 j.2 (fun h => hj (Subtype.ext h).symm) a ha _ (hxL j)
    exact i227cmp_zpowers_inter (hxo i) (hxn i) hy1 (Subgroup.mem_centralizer_iff.1 (hle hy2))
  set Es : Finset O → Subgroup K := fun S => ⨆ i : S, Subgroup.zpowers (x i) with hEs
  have hE : ∀ S : Finset O, IsElemAbelian 3 (Es S) ∧ Nat.card (Es S) = 3 ^ S.card := by
    intro S
    have := i227cmp_elem_family (fun i : S => x i) (fun i => hxo i)
      (fun i j hij => hcx i j (fun h => hij (Subtype.ext h)))
      (hind.comp (f := fun i : S => (i : O)) Subtype.val_injective)
    simpa [Fintype.card_coe] using this
  have hle : ∀ (S : Finset O) (H : Subgroup K), (∀ i ∈ S, x i ∈ H) → Es S ≤ H :=
    fun S H h => iSup_le fun i => Subgroup.zpowers_le.2 (h i i.2)
  have hmem : ∀ (S : Finset O), ∀ i ∈ S, x i ∈ Es S := fun S i hi =>
    (le_iSup (fun j : S => Subgroup.zpowers (x j)) ⟨i, hi⟩) (Subgroup.mem_zpowers _)
  have hmono : ∀ S T : Finset O, S ⊆ T → Es S ≤ Es T := fun S T hST =>
    hle S _ fun i hi => hmem T i (hST hi)
  set M : Subgroup K := ⨆ (L : Subgroup K) (_ : L ∈ O), L with hM
  have hLM : ∀ L ∈ O, L ≤ M := fun L hL =>
    le_iSup₂ (f := fun (L : Subgroup K) (_ : L ∈ O) => L) L hL
  have hMn : M.Normal := by
    have h1 : ∀ g : K, M ≤ M.comap (MulAut.conj g).toMonoidHom := by
      intro g
      refine iSup₂_le fun L hL a ha => ?_
      have hL' : GLBConj g⁻¹ L ∈ O := hconj g⁻¹ L hL
      have : g * a * g⁻¹ ∈ GLBConj g⁻¹ L := by
        rw [mem_gLBConj]
        convert ha using 1
        group
      exact hLM _ hL' this
    exact ⟨fun n hn g => by simpa using h1 g hn⟩
  have hEM : Es Finset.univ ≤ M := hle _ _ fun i _ => hLM i.1 i.2 (hxL i)
  have hcardO : 4 ≤ (Finset.univ : Finset O).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨hEel, hEc⟩ := hE Finset.univ
  obtain ⟨Q0, hEQ0, hQ0M, hQ0p, hQ0c⟩ :=
    exists_sylow_ge Nat.prime_three hEM (i227cmp_isPGroup_of_elem hEel)
  have hfr : (⊤ : Subgroup K) ≤ M ⊔ Subgroup.normalizer (Q0 : Set K) :=
    le_sup_normalizer_of_sylow Nat.prime_three le_top (hMn.subgroupOf ⊤) hQ0M hQ0p hQ0c
  obtain ⟨P0, hQ0P0, -, hP0p, hP0c⟩ := exists_sylow_ge Nat.prime_three
    (K := (⊤ : Subgroup K)) le_top hQ0p
  have hP0c' : Nat.card P0 = 3 ^ (Nat.card K).factorization 3 := by rw [hP0c, Subgroup.card_top]
  refine top_le_glbCore_three_of_sylow hP0c' hPc ?_
  have hr0 : 3 ≤ CFSG.Open.pRank 3 Q0 :=
    ((by omega : 3 ≤ (Finset.univ : Finset O).card).trans
      (CFSG.SectionRank.le_pRank (by norm_num) hEQ0 hEel hEc))
  have hN0 : Subgroup.normalizer (Q0 : Set K) ≤ GLBCore 3 3 P0 :=
    normalizer_le_glbCore_three hQ0P0 hr0
  have hMH : M ≤ GLBCore 3 3 P0 := by
    refine iSup₂_le fun L hL => ?_
    set i : O := ⟨L, hL⟩ with hi
    have hcard' : 3 ≤ (Finset.univ.erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      omega
    obtain ⟨S, hS, hS3⟩ := Finset.exists_subset_card_eq hcard'
    have hiS : i ∉ S := fun h => (Finset.mem_erase.1 (hS h)).1 rfl
    obtain ⟨hSel, hSc⟩ := hE S
    have hQP : Es S ≤ P0 := (hmono S Finset.univ (Finset.subset_univ S)).trans (hEQ0.trans hQ0P0)
    have hr : 3 ≤ CFSG.Open.pRank 3 (Es S) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_rfl hSel (by rw [hSc, hS3])
    have hcent : Es S ≤ Subgroup.centralizer (L : Set K) := by
      refine hle S _ fun j hj => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hji : j ≠ i := fun h => hiS (h ▸ hj)
      exact hcomm L hL j.1 j.2 (fun h => hji (Subtype.ext h.symm)) a ha _ (hxL j)
    refine le_trans ?_ (normalizer_le_glbCore_three hQP hr)
    intro a ha
    apply Subgroup.centralizer_le_normalizer (Es S : Set K)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((Subgroup.mem_centralizer_iff.1 (hcent hh)) a ha).symm
  exact hfr.trans (sup_le hMH hN0)

theorem three_dvd_card_of_component (hcore : GLAPPrimeCore 3 K = ⊥) {L : Subgroup K}
    (hL : IsComponentOf L ⊤) : 3 ∣ Nat.card L := by
  by_contra hnd
  have hcop : Nat.Coprime 3 (Nat.card L) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd
  have h1 : L ≤ GLAPPrimeCoreOf 3 (⊤ : Subgroup K) := by
    rw [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.glaPPrimeCoreOf_eq_self_of_coprime hcop]
    exact glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hL.2.1
  rw [CFSG.HardMathSupport.Timmesfeld.ComponentBalance.glaPPrimeCoreOf_top_eq_bot_of_eq_bot hcore,
    le_bot_iff] at h1
  have hnt : Nontrivial L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt h1

end Components

section Abstract

variable {K : Type} [Group K] [Finite K]

open CFSG.HardMathSupport.Solomon.Coordinator

theorem top_le_glbCore_three_of_family_core
    (hOut : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsKGroup Q → ∀ {J : Subgroup Q},
      IsComponentOf J ⊤ → Group.IsSolvable (Outer ↥J))
    (hK : CFSG.Open.IsKGroup K) (hperf : commutator K = ⊤)
    (h5 : ∀ C : Subgroup K, C.Normal → Nat.Coprime 5 C.index → C = ⊤)
    {ι : Type} (L : ι → Subgroup K) (hLn : ∀ i, (L i).Normal) (hLp : ∀ i, ⁅L i, L i⁆ = L i)
    (hLr : ∀ i, 4 ≤ CFSG.Open.pRank 3 (L i)) (hgen : (⊤ : Subgroup K) ≤ ⨆ i, L i)
    (hLc : ∀ i j, i ≠ j → ⁅L i, L j⁆ ≤ GLAPPrimeCore 5 K) (hι : ∀ i : ι, ∃ j : ι, j ≠ i)
    (hY : GLAPPrimeCore 3 K = ⊥) (P : Subgroup K) (hP3 : IsPGroup 3 P)
    (hPc : Nat.card P = 3 ^ (Nat.card K).factorization 3) :
    (⊤ : Subgroup K) ≤ GLBCore 3 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R : Subgroup K := GLAPPrimeCore 5 K with hR
  set W : Subgroup K := ⁅R, (⊤ : Subgroup K)⁆ with hWdef
  have hRc : Nat.Coprime 5 (Nat.card R) := CFSG.pPrimeCore_coprime_card
  by_cases hcomp : ∃ J : Subgroup K, J ≤ W ∧ IsSubnormal J ⊤ ∧ CFSG.Open.IsQuasisimple ↥J
  ·
    obtain ⟨J, hJW, hJsn, hJq⟩ := hcomp
    have hJc : IsComponentOf J ⊤ := ⟨le_top, hJsn, hJq⟩
    have hJR : J ≤ R := hJW.trans (Subgroup.commutator_le_left _ _)
    have hcov : ∀ C : Subgroup K, C.Normal → C ⊔ R = ⊤ → C = ⊤ := by
      intro C hC hCR
      refine h5 C hC ?_
      have h1 : C.relIndex R ∣ Nat.card R := Subgroup.relIndex_dvd_card C R
      have h2 : C.index = C.relIndex R := by
        rw [← Subgroup.relIndex_top_right, ← hCR, sup_comm, Subgroup.relIndex_sup_right]
      rw [h2]
      exact Nat.Coprime.coprime_dvd_right h1 hRc
    set O : Set (Subgroup K) := Set.range fun k : K => GLBConj k J with hO
    have hOc : ∀ L ∈ O, IsComponentOf L ⊤ := by
      rintro _ ⟨k, rfl⟩
      exact isComponentOf_gLBConj hJc k
    rcases i227cmp_orbit_dichotomy hperf J with h5' | hnorm
    · change 5 ≤ Nat.card O at h5'
      refine top_le_glbCore_three_of_components O ?_ (by omega) ?_ ?_ P hPc
      · rintro k _ ⟨k', rfl⟩
        exact ⟨k' * k, by simp only [gLBConj_gLBConj]⟩
      · intro L hL
        obtain ⟨x, hx, hxc⟩ :=
          CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
            (hOc L hL).2.2 Nat.prime_three (by norm_num) (three_dvd_card_of_component hY (hOc L hL))
        refine ⟨x, x.2, ?_, ?_⟩
        · rw [← hx]
          exact Subgroup.orderOf_coe x
        · by_contra hno
          push Not at hno
          refine hxc (Subgroup.mem_center_iff.2 fun g => ?_)
          exact Subtype.ext (hno g g.2).symm
      · intro L hL L' hL' hne a ha b hb
        have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' (hOc L hL)
          (hOc L' hL') hne
        have hmem : a * b * a⁻¹ * b⁻¹ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator ha hb
        rw [h, Subgroup.mem_bot] at hmem
        calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
          _ = b * a := by rw [hmem, one_mul]
    · have hN : J.Normal := ⟨fun n hn g => by
        have : n ∈ GLBConj g J := by rw [hnorm g]; exact hn
        exact mem_gLBConj.1 this⟩
      exact (i227cmp_not_normal hperf hJR hJq (hOut K hK hJc) hcov).elim
  · have hNo : NoCompIn W := fun J hJW hJ hq => hcomp ⟨J, hJW, hJ, hq⟩
    by_cases h3 : 3 ≤ CFSG.Open.pRank 3 (oThreeIn W)
    ·
      haveI := i227um_oThreeIn_normal W
      have hle : oThreeIn W ≤ P := i227um_le_of_normal (i227um_oThreeIn_isPGroup W) hPc
      have htop : Subgroup.normalizer ((oThreeIn W : Subgroup K) : Set K) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.2 inferInstance
      rw [← htop]
      exact normalizer_le_glbCore_three hle h3
    ·
      have hle : CFSG.Open.pRank 3 (oThreeIn W) ≤ 2 := by omega
      have hW : W = ⊥ := i227_rank_holds K hperf hY R W hWdef hNo hle
      have hRL : ∀ j, ⁅R, L j⁆ = ⊥ := fun j =>
        le_bot_iff.1 (hW ▸ Subgroup.commutator_mono le_rfl le_top)
      have hP' : IsSylowIn 3 ⊤ P :=
        Claims1110.isSylowIn_of_card le_top hP3 (by rw [Subgroup.card_top]; exact hPc)
      refine hgen.trans (iSup_le fun i => ?_)
      obtain ⟨j, hji⟩ := hι i
      have hcij : ⁅L j, L i⁆ = ⊥ := by
        have h1 : ⁅⁅L j, L i⁆, L j⁆ = ⊥ := le_bot_iff.1 ((hRL j) ▸ Subgroup.commutator_mono
          (hLc j i hji) le_rfl)
        have h2 : ⁅⁅L i, L j⁆, L j⁆ = ⊥ := le_bot_iff.1 ((hRL j) ▸ Subgroup.commutator_mono
          (hLc i j (Ne.symm hji)) le_rfl)
        have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
        rwa [hLp j] at h3
      have hS : IsSylowIn 3 (L j) (P ⊓ L j) := Claims1110d.isSylowIn_inf' hP' le_top
        (by rw [Subgroup.normalizer_eq_top_iff.2 (hLn j)])
      have hQr : 3 ≤ CFSG.Open.pRank 3 (P ⊓ L j) :=
        le_trans (by omega) ((hLr j).trans (Claims1110i.pRank_le_of_isSylowIn hS))
      intro a ha
      refine normalizer_le_glbCore_three inf_le_left hQr ?_
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun q hq => ?_)
      have hmem : q * a * q⁻¹ * a⁻¹ ∈ ⁅L j, L i⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_inf.1 hq).2 ha
      rw [hcij, Subgroup.mem_bot] at hmem
      calc q * a = q * a * q⁻¹ * a⁻¹ * (a * q) := by group
        _ = a * q := by rw [hmem, one_mul]

theorem pRank_le_pRank_map_of_coprime {K' : Type} [Group K'] [Finite K'] (π : K →* K')
    (hker : Nat.Coprime 3 (Nat.card π.ker)) (L : Subgroup K) :
    CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 (L.map π) := by
  obtain ⟨E, hEL, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) L
  have hbot : E ⊓ π.ker = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i227cop_inf_eq_bot (CFSG.Open.IsElemAbelian.isPGroup hE) hker
  have hinj : Function.Injective (π.comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : (x : K) ∈ E ⊓ π.ker := ⟨x.2, hx⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hrange : (π.comp E.subtype).range = E.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.map_mono hEL)
    (CFSG.SectionRank.isElemAbelian_map hE π) ?_
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hEc]

theorem top_le_glbCore_three_of_family
    (hOut : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsKGroup Q → ∀ {J : Subgroup Q},
      IsComponentOf J ⊤ → Group.IsSolvable (Outer ↥J))
    (hK : CFSG.Open.IsKGroup K) (hperf : commutator K = ⊤)
    (h5 : ∀ C : Subgroup K, C.Normal → Nat.Coprime 5 C.index → C = ⊤)
    {ι : Type} (L : ι → Subgroup K) (hLn : ∀ i, (L i).Normal) (hLp : ∀ i, ⁅L i, L i⁆ = L i)
    (hLr : ∀ i, 4 ≤ CFSG.Open.pRank 3 (L i)) (hgen : (⊤ : Subgroup K) ≤ ⨆ i, L i)
    (hLc : ∀ i j, i ≠ j → ⁅L i, L j⁆ ≤ GLAPPrimeCore 5 K) (hι : ∀ i : ι, ∃ j : ι, j ≠ i)
    (P : Subgroup K) (hP3 : IsPGroup 3 P) (hPc : Nat.card P = 3 ^ (Nat.card K).factorization 3)
    (hP4 : 4 ≤ CFSG.Open.pRank 3 P) :
    (⊤ : Subgroup K) ≤ GLBCore 3 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y : Subgroup K := GLAPPrimeCore 3 K with hYdef
  set π : K →* K ⧸ Y := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  have hYc : Nat.Coprime 3 (Nat.card Y) := CFSG.pPrimeCore_coprime_card
  have hker : π.ker = Y := QuotientGroup.ker_mk' Y
  refine top_le_glbCore_three_of_quotient Y hYc P hP3 hP4 ?_
  obtain ⟨hPb3, hPbc⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i227m_sylow_map hP3 hPc Y
  have hperf' : commutator (K ⧸ Y) = ⊤ := by
    have : Group.IsPerfect K := Group.isPerfect_def.2 hperf
    exact (Group.IsPerfect.ofSurjective hπs).commutator_eq_top
  have h5' : ∀ C : Subgroup (K ⧸ Y), C.Normal → Nat.Coprime 5 C.index → C = ⊤ := by
    intro C hC hCi
    have hC' : (C.comap π).Normal := hC.comap π
    have htop := h5 (C.comap π) hC' (by rwa [Subgroup.index_comap_of_surjective C hπs])
    rw [← Subgroup.map_comap_eq_self_of_surjective hπs C, htop, Subgroup.map_top_of_surjective π hπs]
  have hRle : (GLAPPrimeCore 5 K).map π ≤ GLAPPrimeCore 5 (K ⧸ Y) := by
    refine le_sSup ⟨(inferInstance : (GLAPPrimeCore 5 K).Normal).map π hπs, ?_⟩
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ π) CFSG.pPrimeCore_coprime_card
  refine top_le_glbCore_three_of_family_core hOut (hK.of_surjective π hπs) hperf' h5'
    (fun i => (L i).map π) (fun i => (hLn i).map π hπs) (fun i => ?_) (fun i => ?_) ?_
    (fun i j hij => ?_) hι
    (CFSG.HardMathSupport.Solomon.Coordinator.i227m_primeCore_three_quotient K) _ hPb3 hPbc
  · rw [← Subgroup.map_commutator, hLp i]
  · exact (hLr i).trans (pRank_le_pRank_map_of_coprime π (by rw [hker]; exact hYc) (L i))
  · rw [← Subgroup.map_iSup, ← Subgroup.map_top_of_surjective π hπs]
    exact Subgroup.map_mono hgen
  · rw [← Subgroup.map_commutator]
    exact (Subgroup.map_mono (hLc i j hij)).trans hRle

end Abstract

section Family

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (mem_gLAPPrimeCoreOf_iff inf_gLAPPrimeCoreOf_eq)

theorem pRank_le_pRank_subgroupOf {p : ℕ} (hp : 1 < p) {H J : Subgroup G} (hHJ : H ≤ J) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (H.subgroupOf J) := by
  obtain ⟨E, hEH, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp H
  refine CFSG.SectionRank.le_pRank hp
    (fun x hx => Subgroup.mem_subgroupOf.2 (hEH (Subgroup.mem_subgroupOf.1 hx)))
    (CFSG.Open.IsElemAbelian.subgroupOf hE J) ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEH.trans hHJ)).toEquiv, hEc]

theorem iSup_le_normalizer_of_mem {Y : Subgroup G} {𝒞 : Set (Subgroup G)}
    (h𝒞 : ∀ L ∈ 𝒞, GLAPComponent 5 Y L) {L : Subgroup G} (hL : L ∈ 𝒞) :
    (⨆ L' ∈ 𝒞, L') ≤ Subgroup.normalizer (L : Set G) := by
  refine iSup₂_le fun L' hL' => ?_
  by_cases h : L' = L
  · subst h
    exact Subgroup.le_normalizer
  · exact le_normalizer_of_ne_pComponent (h𝒞 L hL) (h𝒞 L' hL') (Ne.symm h)

theorem eq_top_of_normal_of_coprime_index {Y : Subgroup G} {𝒞 : Set (Subgroup G)}
    (h𝒞 : ∀ L ∈ 𝒞, Claims1110i.IsD4Comp Y L) {J : Subgroup G} (hJdef : J = ⨆ L ∈ 𝒞, L) (C : Subgroup ↥J)
    (hC : C.Normal) (hCi : Nat.Coprime 5 C.index) : C = ⊤ := by
  have hp5 : Nat.Prime 5 := by norm_num
  haveI := hC
  set C' : Subgroup G := C.map J.subtype with hC'def
  have hLJ : ∀ L ∈ 𝒞, L ≤ J := fun L hL => hJdef ▸ le_iSup₂_of_le L hL le_rfl
  have key : ∀ L ∈ 𝒞, L ≤ C' := by
    intro L hL
    have hLc : GLAPComponent 5 Y L := (h𝒞 L hL).1
    set φ : ↥L →* ↥J ⧸ C := (QuotientGroup.mk' C).comp (Subgroup.inclusion (hLJ L hL)) with hφdef
    have hkerφ : ∀ l : ↥L, l ∈ φ.ker ↔ (l : G) ∈ C' := by
      intro l
      rw [MonoidHom.mem_ker, hφdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      constructor
      · intro h
        exact ⟨_, h, rfl⟩
      · rintro ⟨c, hc, hcl⟩
        have : c = Subgroup.inclusion (hLJ L hL) l := Subtype.ext hcl
        rwa [← this]
    have hidx : Nat.Coprime 5 φ.ker.index := by
      rw [Subgroup.index_ker]
      refine Nat.Coprime.coprime_dvd_right ?_ hCi
      exact Subgroup.card_subgroup_dvd_card φ.range
    set ψ : ↥L →* barOf 5 L := QuotientGroup.mk' (GLAPPrimeCore 5 ↥L) with hψdef
    have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective _
    have hMn : (φ.ker.map ψ).Normal := (MonoidHom.normal_ker φ).map ψ hψs
    have hq : CFSG.Open.IsQuasisimple (barOf 5 L) := Lemma1313.isQuasisimple_barOf_of_pComp hLc
    have hidx' : Nat.Coprime 5 (φ.ker.map ψ).index :=
      Nat.Coprime.coprime_dvd_right (Subgroup.index_map_dvd _ hψs) hidx
    have htop : φ.ker.map ψ = ⊤ := by
      rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq (φ.ker.map ψ) with
        hle | htop
      · exfalso
        have hcl : StatedClassicalModel (barOf 5 L ⧸ Subgroup.center (barOf 5 L)) .POmegaPlus 4 2 1 := by
          rcases (h𝒞 L hL).2.2 with h | ⟨h4, -⟩
          · exact h
          · norm_num at h4
        obtain ⟨e⟩ := CFSG.EvenSmallLie.OmegaEight.nonempty_mulEquiv_omegaT (Or.inl ⟨by decide, hcl⟩)
        have hc : (Subgroup.center (barOf 5 L)).index = 174182400 := by
          rw [Subgroup.index, Nat.card_congr e.toEquiv, CFSG.EvenSmallLie.OmegaEight.card_omegaT]
        have h1 : (Subgroup.center (barOf 5 L)).index ∣ (φ.ker.map ψ).index := Subgroup.index_dvd_of_le hle
        rw [hc] at h1
        have h2 : 5 ∣ (φ.ker.map ψ).index := (by norm_num : 5 ∣ 174182400).trans h1
        exact (Nat.Prime.coprime_iff_not_dvd hp5).1 hidx' h2
      · exact htop
    set M : Subgroup G := L ⊓ C' with hMdef
    have hML : M ≤ L := inf_le_left
    have hMnL : (M.subgroupOf L).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnL, c, hc, hcn⟩ := hn
      refine ⟨L.mul_mem (L.mul_mem g.2 hnL) (L.inv_mem g.2), ?_⟩
      have hgJ : (g : G) ∈ J := hLJ L hL g.2
      refine ⟨⟨g, hgJ⟩ * c * ⟨g, hgJ⟩⁻¹, hC.conj_mem c hc _, ?_⟩
      have hcn' : (c : G) = (n : G) := hcn
      show (g : G) * (c : G) * (g : G)⁻¹ = (g : G) * (n : G) * (g : G)⁻¹
      rw [hcn']
    have hMsn : IsSubnormal M Y := IsSubnormal.step hML hMnL hLc.2.1
    have hbar : (M.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥Y)) =
        (L.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥Y)) := by
      apply le_antisymm
      · exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2 (hML (Subgroup.mem_subgroupOf.1 hx))
      · rintro _ ⟨y, hy, rfl⟩
        have hyL : (y : G) ∈ L := Subgroup.mem_subgroupOf.1 hy
        have hmem : ψ ⟨y, hyL⟩ ∈ φ.ker.map ψ := by rw [htop]; exact Subgroup.mem_top _
        obtain ⟨m, hm, hmy⟩ := hmem
        have hmC : (m : G) ∈ C' := (hkerφ m).1 hm
        have hcore : (m : ↥L)⁻¹ * ⟨y, hyL⟩ ∈ GLAPPrimeCore 5 ↥L := QuotientGroup.eq.1 hmy
        have hcoreG : (m : G)⁻¹ * (y : G) ∈ GLAPPrimeCoreOf 5 L := ⟨_, hcore, by simp⟩
        have hcoreY : (m : G)⁻¹ * (y : G) ∈ GLAPPrimeCoreOf 5 Y :=
          CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 5 hLc.2.1 hcoreG
        obtain ⟨hmemY, hcY⟩ := (mem_gLAPPrimeCoreOf_iff 5 Y _).1 hcoreY
        have hmY : (m : G) ∈ Y := hLc.1 m.2
        refine ⟨⟨m, hmY⟩, Subgroup.mem_subgroupOf.2 ⟨m.2, hmC⟩, ?_⟩
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        convert hcY using 1
    have hMeq : M = L := by
      by_contra hne
      exact hLc.2.2.2 M (lt_of_le_of_ne hML hne) hMsn hbar
    rw [← hMeq]
    exact inf_le_right
  have hJC : J ≤ C' := hJdef.le.trans (iSup₂_le key)
  rw [eq_top_iff]
  intro x _
  obtain ⟨c, hc, hcx⟩ := hJC x.2
  have : c = x := Subtype.ext hcx
  rwa [← this]

theorem inputD4LayerGen_of_schreier
    (hOut : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsKGroup Q → ∀ {J : Subgroup Q},
      IsComponentOf J ⊤ → Group.IsSolvable (Outer ↥J)) : Claims1110i.InputD4LayerGen := by
  intro G _ _ Y hY 𝒞 h𝒞 h2 S hS
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J : Subgroup G := ⨆ L ∈ 𝒞, L with hJdef
  have hLJ : ∀ L ∈ 𝒞, L ≤ J := fun L hL => le_iSup₂_of_le L hL le_rfl
  have hJY : J ≤ Y := iSup₂_le fun L hL => (h𝒞 L hL).1.1
  let Lf : ↥𝒞 → Subgroup ↥J := fun L => (L : Subgroup G).subgroupOf J
  have hLn : ∀ i, (Lf i).Normal := fun L =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hLJ L L.2)).2
      (iSup_le_normalizer_of_mem (fun L hL => (h𝒞 L hL).1) L.2)
  have hLp : ∀ i, ⁅Lf i, Lf i⁆ = Lf i := by
    intro L
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hLJ L L.2)]
    exact glaPComponent_perfect (h𝒞 L L.2).1
  have hLr : ∀ i, 4 ≤ CFSG.Open.pRank 3 (Lf i) := by
    intro L
    have h1 := inputD4ThreeRank_holds G Y hY {(L : Subgroup G)} fun L' hL' => by
      rw [Set.mem_singleton_iff] at hL'
      subst hL'
      exact h𝒞 L L.2
    simp only [Set.ncard_singleton, mul_one, Set.mem_singleton_iff, iSup_iSup_eq_left] at h1
    exact h1.trans (pRank_le_pRank_subgroupOf (by norm_num) (hLJ L L.2))
  have hgen : (⊤ : Subgroup ↥J) ≤ ⨆ i, Lf i := by
    intro x _
    have hJeq : (⨆ i, Lf i).map J.subtype = J := by
      rw [Subgroup.map_iSup]
      have h1 : ∀ i : ↥𝒞, (Lf i).map J.subtype = (i : Subgroup G) := fun i =>
        Subgroup.map_subgroupOf_eq_of_le (hLJ i i.2)
      simp only [h1]
      exact iSup_subtype'' 𝒞 fun L => L
    have hx : (x : G) ∈ (⨆ i, Lf i).map J.subtype := by
      rw [hJeq]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rwa [← this]
  have hLc : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ ≤ GLAPPrimeCore 5 ↥J := by
    intro i j hij
    set T : Subgroup ↥J := (GLAPPrimeCoreOf 5 Y).subgroupOf J with hTdef
    have hTn : T.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [hTdef, Subgroup.mem_subgroupOf] at hn ⊢
      have h1 := (Subgroup.mem_normalizer_iff.1
        (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPPrimeCoreOf 5 Y
          (hJY g.2)) (n : G)).1 hn
      simpa using h1
    have hTc : Nat.Coprime 5 (Nat.card T) := by
      refine Nat.Coprime.coprime_dvd_right ?_
        (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 5 Y)
      rw [← Subgroup.card_map_of_injective J.subtype_injective]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hy
    have hTle : T ≤ GLAPPrimeCore 5 ↥J := le_sSup ⟨hTn, hTc⟩
    refine le_trans ?_ hTle
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [hTdef, Subgroup.mem_subgroupOf]
    have hne : (i : Subgroup G) ≠ j := fun h => hij (Subtype.ext h)
    have h1 := Claims1110i.comm_mem_core_of_ne_pComponent (h𝒞 i i.2).1 (h𝒞 j j.2).1 hne
      (Subgroup.mem_subgroupOf.1 ha) (Subgroup.mem_subgroupOf.1 hb)
    simpa [commutatorElement_def] using h1
  have hι : ∀ i : ↥𝒞, ∃ j : ↥𝒞, j ≠ i := by
    obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite 𝒞)).1 (by omega)
    intro i
    by_cases hi : (i : Subgroup G) = a
    · exact ⟨⟨b, hb⟩, fun h => hab (hi ▸ (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨a, ha⟩, fun h => hi (congrArg Subtype.val h).symm⟩
  have hK : CFSG.Open.IsKGroup ↥J := hY.of_le hJY
  have hperf : commutator ↥J = ⊤ := by
    have hJp : ⁅J, J⁆ = J := by
      refine le_antisymm (Subgroup.commutator_le_self J) ?_
      refine hJdef.le.trans (iSup₂_le fun L hL => ?_)
      rw [← glaPComponent_perfect (h𝒞 L hL).1]
      exact Subgroup.commutator_mono (hLJ L hL) (hLJ L hL)
    exact (Subgroup.isPerfect_iff.2 hJp).commutator_eq_top
  have h5 : ∀ C : Subgroup ↥J, C.Normal → Nat.Coprime 5 C.index → C = ⊤ :=
    fun C hC hCi => eq_top_of_normal_of_coprime_index h𝒞 hJdef C hC hCi
  have hSJ : S ≤ J := hS.1
  set P : Subgroup ↥J := S.subgroupOf J with hPdef
  have hPc : Nat.card P = 3 ^ (Nat.card ↥J).factorization 3 := by
    rw [hPdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSJ).toEquiv]
    exact Claims1110.card_of_isSylowIn hS
  have hP3 : IsPGroup 3 P := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSJ).symm
  obtain ⟨i₀⟩ : Nonempty ↥𝒞 := by
    obtain ⟨a, b, ha, -, -⟩ := (Set.one_lt_ncard_iff (Set.toFinite 𝒞)).1 (by omega)
    exact ⟨⟨a, ha⟩⟩
  have hP4 : 4 ≤ CFSG.Open.pRank 3 P := by
    have hP' : IsSylowIn 3 ⊤ P :=
      Claims1110.isSylowIn_of_card le_top hP3 (by rw [Subgroup.card_top]; exact hPc)
    have hSy : IsSylowIn 3 (Lf i₀) (P ⊓ Lf i₀) := Claims1110d.isSylowIn_inf' hP' le_top
      (by rw [Subgroup.normalizer_eq_top_iff.2 (hLn i₀)])
    exact (hLr i₀).trans ((Claims1110i.pRank_le_of_isSylowIn hSy).trans
      (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left))
  have hcore := top_le_glbCore_three_of_family hOut hK hperf h5 Lf hLn hLp hLr hgen hLc hι P hP3 hPc hP4
  have hmap := map_glbCore_three_subtype_le J P
  rw [hPdef, Subgroup.map_subgroupOf_eq_of_le hSJ] at hmap
  intro x hx
  exact hmap ⟨⟨x, hx⟩, hcore (Subgroup.mem_top _), rfl⟩

end Family

section UpRank

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)

@[expose] def InputD4UpRankBar : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore 5 K = ⊥ →
    ∀ (D : Type) [Group D], CFSG.Models.LieModel D .POmegaPlus 4 2 1 →
    ∀ x : MulAut K, Lemma1314.PumpupVia 5 D K x →
    ∀ R : Subgroup (MulAut K), IsPGroup 5 R → x ∈ R → 4 ≤ CFSG.Open.pRank 5 R →
      ∃ T : Subgroup K, T ≤ Lemma1314.fixSub x ∧ IsElemAbelian 5 T ∧ 5 ^ 4 ≤ Nat.card T

theorem centMod_of_barAut_eq_one {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (h1 : barAut 5 L ⟨g, hg⟩ = 1) : CFSG.Yardstones.Md0ec50421ce4.CentMod 5 L g := by
  refine ⟨hg, ?_⟩
  rw [Subgroup.commutator_le]
  intro l hl z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hzN : g ^ k ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ hg k
  have hz1 : barAut 5 L ⟨g ^ k, hzN⟩ = 1 := by
    have e : (⟨g ^ k, hzN⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨g, hg⟩ ^ k := rfl
    rw [e, map_zpow, h1, one_zpow]
  have h2 := Subgroup.inv_mem _ (Claims1110d.comm_mem_core_of_barAut_eq_one hzN hz1 l hl)
  have e2 : (g ^ k * l * (g ^ k)⁻¹ * l⁻¹)⁻¹ = ⁅l, g ^ k⁆ := by
    rw [commutatorElement_def]
    group
  rwa [e2] at h2

theorem pRank_le_pRank_map_of_injOn {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K'] {p : ℕ}
    (hp : 1 < p) (f : K →* K') {T : Subgroup K} (hinj : ∀ t ∈ T, f t = 1 → t = 1) :
    CFSG.Open.pRank p T ≤ CFSG.Open.pRank p (T.map f) := by
  obtain ⟨E, hET, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp T
  have hinjE : Function.Injective (f.comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (Subtype.ext (hinj x (hET x.2) hx))
  have hrange : (f.comp E.subtype).range = E.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine CFSG.SectionRank.le_pRank hp (Subgroup.map_mono hET) (CFSG.SectionRank.isElemAbelian_map hE f) ?_
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinjE).toEquiv, hEc]

theorem inputD4UpRank_of_bar (hres : InputD4UpRankBar) : Claims1110i.InputD4UpRank := by
  intro G _ _ Y hY L hL x hxY hxN hx5 hnc K₁ hK₁ hs hlie R hRY hRN hRp hxR hfaith hrank
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple (barOf 5 L) := Lemma1313.isQuasisimple_barOf_of_pComp hL
  have hKG : CFSG.Open.IsKGroup (barOf 5 L) := (hY.of_le hL.1).quotient _
  have hKH : CFSG.LocalAnalysis.GLTheoremA.IsKHat (barOf 5 L) :=
    ⟨hq, CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' hKG hq⟩
  have hcore : GLAPPrimeCore 5 (barOf 5 L) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  set xb : MulAut (barOf 5 L) := barAut 5 L ⟨x, hxN⟩ with hxbdef
  have hxb1 : xb ≠ 1 := fun h1 => hnc (centMod_of_barAut_eq_one hxN h1)
  have hxb5 : xb ^ 5 = 1 := by
    rw [hxbdef, ← map_pow]
    have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 5 = 1 := Subtype.ext (by simpa using hx5)
    rw [this, map_one]
  have hK₁L : K₁ ≤ L := hK₁.1.trans inf_le_left
  have hfix := AltFacts3.fixedSub_barAut_eq_p hp hx5 hxN
  have e1 : Lemma1314.fixSub xb = barX 5 L (L ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [← hfix]
    rfl
  have hpump : Lemma1314.PumpupVia 5 (barOf 5 K₁) (barOf 5 L) xb := by
    refine ⟨orderOf_eq_prime hxb5 hxb1, barX 5 L K₁, ?_, ⟨(Prop115.barOfIso hK₁L).symm⟩⟩
    rw [e1]
    exact Prop115b.barX_glaPComponent_of_le hp inf_le_left hK₁
  set R' : Subgroup ↥(Subgroup.normalizer (L : Set G)) := R.subgroupOf (Subgroup.normalizer (L : Set G))
    with hR'def
  have hinjR : ∀ r ∈ R', barAut 5 L r = 1 → r = 1 := by
    intro r hr h1
    have h2 := hfaith r (Subgroup.mem_subgroupOf.1 hr) (centMod_of_barAut_eq_one r.2 h1)
    exact Subtype.ext h2
  have hRb3 : IsPGroup 5 (R'.map (barAut 5 L)) :=
    (hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm).map _
  have hxRb : xb ∈ R'.map (barAut 5 L) := ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.2 hxR, rfl⟩
  have hRb4 : 4 ≤ CFSG.Open.pRank 5 (R'.map (barAut 5 L)) :=
    hrank.trans ((pRank_le_pRank_subgroupOf (by norm_num) hRN).trans
      (pRank_le_pRank_map_of_injOn (by norm_num) _ hinjR))
  obtain ⟨T, hTfix, hTel, hT4⟩ := hres (barOf 5 L) hKH hcore (barOf 5 K₁) hlie xb hpump _ hRb3 hxRb hRb4
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hTel)
  set π : ↥L →* barOf 5 L := QuotientGroup.mk' (GLAPPrimeCore 5 ↥L) with hπdef
  set A : Subgroup ↥L := (L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf L with hAdef
  have hA : ¬ 5 ∣ Nat.card ↥(A ⊓ π.ker) := by
    intro h5
    have h1 : Nat.card ↥(A ⊓ π.ker) ∣ Nat.card ↥(GLAPPrimeCore 5 ↥L) := by
      refine Subgroup.card_dvd_of_le (inf_le_right.trans ?_)
      rw [hπdef, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥L) (h5.trans h1)
  have hTA : T ≤ A.map π := hTfix.trans_eq e1
  obtain ⟨E, hEA, hEel, hEc⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1020_coprime_lift π A hA hTA hTel hk
  set F : Subgroup G := E.map L.subtype ⊔ Subgroup.zpowers x with hFdef
  have hEx : ∀ e ∈ E.map L.subtype, e * x = x * e := by
    rintro _ ⟨e, he, rfl⟩
    have h1 : (e : G) ∈ L ⊓ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_subgroupOf.1 (hEA he)
    exact (Subgroup.mem_centralizer_singleton_iff.1 h1.2)
  refine ⟨F, sup_le (Subgroup.map_subtype_le E |>.trans hL.1) (Subgroup.zpowers_le.2 hxY), ?_,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x), ?_⟩
  · refine CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.SectionRank.isElemAbelian_map hEel _)
      (CFSG.Open.isElemAbelian_zpowers hx5) fun a ha b hb => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hEx a ha) m).eq
  · have h1 : Nat.card ↥(E.map L.subtype) = 5 ^ k := by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hEc]
    have h2 : Nat.card ↥(E.map L.subtype) ≤ Nat.card ↥F := Subgroup.card_le_of_le le_sup_left
    rw [hk] at hT4
    omega

end UpRank

section Certified


theorem inputD4LayerGen_holds :
    Claims1110i.InputD4LayerGen :=
  inputD4LayerGen_of_schreier fun _ _ _ hQ _ hJ =>
    CFSG.LocalAnalysis.GLTheoremB.outer_solvable_of_component_certified hQ hJ

theorem step6D4Inputs_of_upRankBar
    (hres : InputD4UpRankBar) : Claims1110j.Step6D4Inputs :=
  ⟨inputD4UpRank_of_bar hres, inputD4ThreeRank_holds, inputD4LayerGen_holds⟩

end Certified

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110k
