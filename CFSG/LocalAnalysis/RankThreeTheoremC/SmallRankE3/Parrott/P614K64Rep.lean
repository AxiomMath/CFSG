module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64McL
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K64

open CFSG.Open Subgroup CFSG.Quasithin CFSG.HardMathSupport.Solomon
open scoped MatrixGroups


section Component

variable {A : Type} [Group A] [Finite A] {K O : Subgroup A}

theorem normal_inf_subgroupOf_self (hKO : K ≤ normalizer (O : Set A)) :
    ((K ⊓ O).subgroupOf K).Normal :=
  normal_inf_subgroupOf hKO

theorem pPrimeCore_eq (hKO : K ≤ normalizer (O : Set A)) (hO2 : IsPGroup 2 O)
    (hmax : ∀ N : Subgroup A, N ≤ K → (N.subgroupOf K).Normal → K ⊓ O ≤ N →
      N = K ⊓ O ∨ N = K)
    (hne : Nat.card (Kbar K) ≠ 1) :
    CFSG.pPrimeCore 3 ↥K = (K ⊓ O).subgroupOf K := by
  have hle : (K ⊓ O).subgroupOf K ≤ CFSG.pPrimeCore 3 ↥K := by
    refine le_sSup ⟨normal_inf_subgroupOf_self hKO, ?_⟩
    have h2 : IsPGroup 2 ↥((K ⊓ O).subgroupOf K) := by
      have h := hO2.to_le (inf_le_right : K ⊓ O ≤ O)
      exact IsPGroup.of_equiv h (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  set N₃ : Subgroup A := (CFSG.pPrimeCore 3 ↥K).map K.subtype with hN₃
  have hN₃K : N₃ ≤ K := map_subtype_le _
  have hN₃s : N₃.subgroupOf K = CFSG.pPrimeCore 3 ↥K :=
    comap_map_eq_self_of_injective K.subtype_injective _
  have hN₃n : (N₃.subgroupOf K).Normal := by
    rw [hN₃s]
    exact CFSG.pPrimeCore_normal
  have hKON : K ⊓ O ≤ N₃ := by
    have h := map_mono (f := K.subtype) hle
    rwa [map_subgroupOf_eq_of_le inf_le_left] at h
  rcases hmax N₃ hN₃K hN₃n hKON with h | h
  · rw [← hN₃s, h]
  · exfalso
    apply hne
    have htop : CFSG.pPrimeCore 3 ↥K = ⊤ := by
      rw [← hN₃s, h, subgroupOf_self]
    have : Subsingleton (Kbar K) := by
      unfold Kbar
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact Nat.card_unique

theorem isSimpleGroup_of_ker (hKO : K ≤ normalizer (O : Set A)) (hlt : K ⊓ O < K)
    (hmax : ∀ N : Subgroup A, N ≤ K → (N.subgroupOf K).Normal → K ⊓ O ≤ N →
      N = K ⊓ O ∨ N = K)
    {H : Type} [Group H] (ψ : ↥K →* H) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (K ⊓ O).subgroupOf K) : IsSimpleGroup H := by
  have hnt : Nontrivial H := by
    obtain ⟨k, hkK, hkO⟩ := SetLike.exists_of_lt hlt
    refine ⟨⟨ψ ⟨k, hkK⟩, 1, fun h1 => hkO ?_⟩⟩
    have h2 : (⟨k, hkK⟩ : ↥K) ∈ ψ.ker := h1
    rw [hker, mem_subgroupOf] at h2
    exact h2
  refine ⟨fun M hM => ?_⟩
  set P : Subgroup A := (M.comap ψ).map K.subtype with hP
  have hPK : P ≤ K := map_subtype_le _
  have hPs : P.subgroupOf K = M.comap ψ := comap_map_eq_self_of_injective K.subtype_injective _
  have hPn : (P.subgroupOf K).Normal := by
    rw [hPs]
    exact hM.comap ψ
  have hKOP : K ⊓ O ≤ P := by
    have h1 : (K ⊓ O).subgroupOf K ≤ M.comap ψ := by
      rw [← hker]
      exact MonoidHom.ker_le_comap ψ M
    have h := map_mono (f := K.subtype) h1
    rwa [map_subgroupOf_eq_of_le inf_le_left] at h
  rcases hmax P hPK hPn hKOP with h | h
  · left
    have h1 : M.comap ψ = ψ.ker := by rw [← hPs, h, hker]
    rw [← map_comap_eq_self_of_surjective hψ M, h1]
    exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
  · right
    have h1 : M.comap ψ = ⊤ := by rw [← hPs, h, subgroupOf_self]
    rw [← map_comap_eq_self_of_surjective hψ M, h1, map_top_of_surjective ψ hψ]

theorem inf_centralizer_eq {W : Subgroup A} (hKW : K ≤ normalizer (W : Set A))
    (hOW : O ≤ centralizer (W : Set A)) (hKC : ¬ K ≤ centralizer (W : Set A))
    (hmax : ∀ N : Subgroup A, N ≤ K → (N.subgroupOf K).Normal → K ⊓ O ≤ N →
      N = K ⊓ O ∨ N = K) :
    K ⊓ centralizer (W : Set A) = K ⊓ O := by
  have hn : ((K ⊓ centralizer (W : Set A)).subgroupOf K).Normal :=
    normal_inf_subgroupOf (B2F.le_normalizer_centralizer hKW)
  rcases hmax _ inf_le_left hn (inf_le_inf_left K hOW) with h | h
  · exact h
  · exact absurd (h.ge.trans inf_le_right) hKC

theorem convI_mul_self {W : Subgroup A} (hW : IsElemAbelian 2 W) {a : A}
    (haW : a ∈ normalizer (W : Set A)) (ha2 : a * a ∈ centralizer (W : Set A)) :
    convI hW ⟨a, haW⟩ * convI hW ⟨a, haW⟩ = 1 := by
  rw [← map_mul]
  exact (convI_eq_one_iff hW _).mpr ha2

theorem convI_conj_mem {W : Subgroup A} (hW : IsElemAbelian 2 W) {a : A}
    (haW : a ∈ normalizer (W : Set A)) (haK : a ∈ normalizer (K : Set A)) :
    ∀ n ∈ autI hW K, convI hW ⟨a, haW⟩ * n * (convI hW ⟨a, haW⟩)⁻¹ ∈ autI hW K := by
  intro n hn
  obtain ⟨g, hgK, rfl⟩ := (mem_autI hW).mp hn
  rw [← map_inv, ← map_mul, ← map_mul]
  refine (mem_autI hW).mpr ⟨_, ?_, rfl⟩
  exact (mem_normalizer_iff.mp haK g).mp hgK

end Component

section Model


theorem nonempty_psl_equiv_S :
    Nonempty (PSL(3, GaloisField 2 2) ≃* ↥CFSG.ComponentClassification.PSL3Four.S) :=
  CFSG.ComponentClassification.PSL3Four.nonempty_equiv_of_stated _
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, GaloisField 2 2,
      inferInstance, inferInstance, GaloisField.card 2 2 (by norm_num),
      ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3
        (GaloisField 2 2)⟩⟩

variable {A : Type} [Group A] [Finite A] {K O : Subgroup A}

theorem card_kbar (e : Kbar K ≃* PSL(3, GaloisField 2 2)) : Nat.card (Kbar K) = 20160 := by
  obtain ⟨θ⟩ := nonempty_psl_equiv_S
  exact (CFSG.ComponentClassification.PSL3Four.facts_of_equiv_S.{0, 0} (e.trans θ)).1

theorem nonempty_equiv_S_of_ker (hKO : K ≤ normalizer (O : Set A)) (hO2 : IsPGroup 2 O)
    (hmax : ∀ N : Subgroup A, N ≤ K → (N.subgroupOf K).Normal → K ⊓ O ≤ N →
      N = K ⊓ O ∨ N = K)
    (e : Kbar K ≃* PSL(3, GaloisField 2 2)) {H : Type} [Group H] (ψ : ↥K →* H)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (K ⊓ O).subgroupOf K) :
    Nonempty (H ≃* ↥CFSG.ComponentClassification.PSL3Four.S) := by
  obtain ⟨θ⟩ := nonempty_psl_equiv_S
  have hc : Nat.card (Kbar K) ≠ 1 := by rw [card_kbar e]; norm_num
  have hk : ψ.ker = CFSG.pPrimeCore 3 ↥K := by rw [hker, pPrimeCore_eq hKO hO2 hmax hc]
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hk)).trans (e.trans θ)⟩

theorem autI_facts {W : Subgroup A} (hO2 : IsPGroup 2 O) (hKO : K ≤ normalizer (O : Set A))
    (hlt : K ⊓ O < K)
    (hmax : ∀ N : Subgroup A, N ≤ K → (N.subgroupOf K).Normal → K ⊓ O ≤ N →
      N = K ⊓ O ∨ N = K)
    (e : Kbar K ≃* PSL(3, GaloisField 2 2))
    (hW : IsElemAbelian 2 W) (hKW : K ≤ normalizer (W : Set A))
    (hOW : O ≤ centralizer (W : Set A)) (hKC : ¬ K ≤ centralizer (W : Set A)) :
    IsSimpleGroup ↥(autI hW K) ∧ Nat.card ↥(autI hW K) = 20160 ∧
      ∀ t : ↥(autI hW K), orderOf t = 2 → Nat.card (centralizer ({t} : Set ↥(autI hW K))) = 64 := by
  have hKC' := inf_centralizer_eq hKW hOW hKC hmax
  have hmemR : ∀ k : ↥K, convHom hW K hKW k ∈ autI hW K := by
    intro k
    rw [← range_convHom hW K hKW]
    exact ⟨k, rfl⟩
  let ψ : ↥K →* ↥(autI hW K) := (convHom hW K hKW).codRestrict (autI hW K) hmemR
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← range_convHom hW K hKW] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨k, rfl⟩
  have hker : ψ.ker = (K ⊓ O).subgroupOf K := by
    rw [MonoidHom.ker_codRestrict, ker_convHom, hKC']
  obtain ⟨θ⟩ := nonempty_equiv_S_of_ker hKO hO2 hmax e ψ hψ hker
  obtain ⟨hc, hi, -⟩ := CFSG.ComponentClassification.PSL3Four.facts_of_equiv_S.{0, 0} θ
  exact ⟨isSimpleGroup_of_ker hKO hlt hmax ψ hψ hker, hc, hi⟩

theorem false_of_module {W : Subgroup A} (hO2 : IsPGroup 2 O) (hKO : K ≤ normalizer (O : Set A))
    (hlt : K ⊓ O < K)
    (hmax : ∀ N : Subgroup A, N ≤ K → (N.subgroupOf K).Normal → K ⊓ O ≤ N →
      N = K ⊓ O ∨ N = K)
    (e : Kbar K ≃* PSL(3, GaloisField 2 2))
    (hW : IsElemAbelian 2 W) (hKW : K ≤ normalizer (W : Set A))
    (hOW : O ≤ centralizer (W : Set A)) (hKC : ¬ K ≤ centralizer (W : Set A))
    {a : A} (haW : a ∈ normalizer (W : Set A)) (haK : a ∈ normalizer (K : Set A))
    (ha2 : a * a ∈ centralizer (W : Set A))
    (hτ : UniquenessMaximal.IsTransvection (convI hW ⟨a, haW⟩))
    (hτc : ∃ n ∈ autI hW K, convI hW ⟨a, haW⟩ * n ≠ n * convI hW ⟨a, haW⟩)
    (hout : ∀ n ∈ autI hW K, (∀ m ∈ autI hW K,
      n * convI hW ⟨a, haW⟩ * m = m * (n * convI hW ⟨a, haW⟩)) → n * convI hW ⟨a, haW⟩ = 1) :
    False := by
  obtain ⟨hs, hc, hi⟩ := autI_facts hO2 hKO hlt hmax e hW hKW hOW hKC
  haveI := hs
  exact false_of_transvection (fun v => by rw [← pow_two]; exact IntMod.sq_eq_one v)
    (autI hW K) hc hi _ hτ (convI_mul_self hW haW ha2) (convI_conj_mem hW haW haK) hτc hout

theorem false_of_module_of_mem {W : Subgroup A} (hO2 : IsPGroup 2 O)
    (hKO : K ≤ normalizer (O : Set A)) (hlt : K ⊓ O < K)
    (hmax : ∀ N : Subgroup A, N ≤ K → (N.subgroupOf K).Normal → K ⊓ O ≤ N →
      N = K ⊓ O ∨ N = K)
    (e : Kbar K ≃* PSL(3, GaloisField 2 2))
    (hW : IsElemAbelian 2 W) (hKW : K ≤ normalizer (W : Set A))
    (hOW : O ≤ centralizer (W : Set A)) (hKC : ¬ K ≤ centralizer (W : Set A))
    {a : A} (haW : a ∈ normalizer (W : Set A)) (haK : a ∈ normalizer (K : Set A))
    (ha2 : a * a ∈ centralizer (W : Set A))
    (hτ : UniquenessMaximal.IsTransvection (convI hW ⟨a, haW⟩))
    (hτK : convI hW ⟨a, haW⟩ ∈ autI hW K) : False := by
  obtain ⟨hs, hc, hi⟩ := autI_facts hO2 hKO hlt hmax e hW hKW hOW hKC
  haveI := hs
  refine false_of_module hO2 hKO hlt hmax e hW hKW hOW hKC haW haK ha2 hτ ?_
    (hout_of_mem hc hi hτK)
  by_contra hall
  push Not at hall
  have hz := center_eq_bot_of_l34 hc hi
  have hmem : (⟨convI hW ⟨a, haW⟩, hτK⟩ : ↥(autI hW K)) ∈ center ↥(autI hW K) := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hall g g.2).symm
  rw [hz, mem_bot] at hmem
  exact hτ.1 (congrArg Subtype.val hmem)

end Model

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K64
