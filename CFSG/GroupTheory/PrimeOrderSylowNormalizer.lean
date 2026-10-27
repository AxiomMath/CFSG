module

public import CFSG.GroupTheory.DihedralQuotientNormalizer
public import CFSG.GroupTheory.WielandtProductLocal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InPStarCriteria
public import CFSG.Quasithin.EmptyFaithful.S153QPC1

public section

open Subgroup
open scoped Pointwise

namespace CFSG.GroupTheory

theorem exists_orderOf_eq_prime_mem_normalizer_sup_of_dihedral
    {G : Type} [Group G] [Finite G]
    {M X C T : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hXM : X ≤ M) (hCM : C ≤ M)
    (hMX : M ≤ Subgroup.normalizer (X : Set G))
    (φ : ↥M →* DihedralGroup p) (hφ : Function.Surjective φ)
    (hker : φ.ker = (X ⊔ C).subgroupOf M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hrank : CFSG.Open.pRank p C ≤ 1)
    (hpK : ¬ p ∣ Nat.card ↥(X ⊓ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G)))
    {b : G} (hbM : b ∈ M) (hbN : b ∉ X ⊔ C) (hbord : orderOf b = p)
    (hbTN : b ∈ Subgroup.normalizer ((T ⊓ (X ⊔ C) : Subgroup G) : Set G)) :
    ∃ y ∈ M, y ∉ X ⊔ C ∧ orderOf y = p ∧
      y ∈ Subgroup.normalizer ((T ⊓ (X ⊔ C) : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer
        ((Subgroup.zpowers y ⊔ (T ⊓ (X ⊔ C)) : Subgroup G) : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let N : Subgroup G := X ⊔ C
  have hXN : X ≤ N := le_sup_left
  have hCN : C ≤ N := le_sup_right
  have hNM : N ≤ M := sup_le hXM hCM
  have hNnormal : (N.subgroupOf M).Normal := by
    rw [show N.subgroupOf M = φ.ker from hker.symm]
    exact MonoidHom.normal_ker φ
  have hMN : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNnormal
  have hTM : T ≤ M := hT.le
  have hTN : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ N) N :=
    hT.inf_of_le_normalizer hNM hMN
  have hT2 : IsPGroup 2 ↥T := hT.isPGroup
  have hTN2 : IsPGroup 2 ↥(T ⊓ N) := hTN.isPGroup
  have hTnormTN : T ≤ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) := by
    intro t ht
    have htN : t ∈ Subgroup.normalizer (N : Set G) := hMN (hTM ht)
    rw [Subgroup.mem_normalizer_iff] at htN ⊢
    intro x
    constructor
    · rintro ⟨hxT, hxN⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), (htN x).mp hxN⟩
    · rintro ⟨hxT, hxN⟩
      have hxT' : x ∈ T := by
        have h := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
        rwa [show t⁻¹ * (t * x * t⁻¹) * t = x from by group] at h
      exact ⟨hxT', (htN x).mpr hxN⟩
  let rot : Subgroup (DihedralGroup p) := TauCeti.dihedralRotations p
  let M₁ : Subgroup G := (Subgroup.comap φ rot).map M.subtype
  have hM₁M : M₁ ≤ M := Subgroup.map_subtype_le _
  have hM₁sub : M₁.subgroupOf M = Subgroup.comap φ rot := by
    change Subgroup.comap M.subtype (Subgroup.map M.subtype (Subgroup.comap φ rot)) =
      Subgroup.comap φ rot
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hM₁normalSub : (M₁.subgroupOf M).Normal := by
    rw [hM₁sub]
    exact (TauCeti.dihedralRotations_normal p).comap φ
  have hMM₁ : M ≤ Subgroup.normalizer (M₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hM₁M).mp hM₁normalSub
  have hTM₁ : T ≤ Subgroup.normalizer (M₁ : Set G) := hTM.trans hMM₁
  have hmem_rot : ∀ {m : G} (hm : m ∈ M₁), φ ⟨m, hM₁M hm⟩ ∈ rot := by
    intro m hm
    obtain ⟨mm, hmm, rfl⟩ := Subgroup.mem_map.mp hm
    simpa using hmm
  have hNM₁ : N ≤ M₁ := by
    intro n hn
    have hnM : n ∈ M := hNM hn
    refine Subgroup.mem_map.mpr ⟨⟨n, hnM⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hnker : φ ⟨n, hnM⟩ = 1 := by
      have hmem : ⟨n, hnM⟩ ∈ φ.ker := by
        rw [hker]
        exact hn
      exact MonoidHom.mem_ker.mp hmem
    rw [hnker]
    exact rot.one_mem
  have hidxNM : N.relIndex M = 2 * p := by
    have h1 : N.relIndex M = (N.subgroupOf M).index := rfl
    rw [h1, show N.subgroupOf M = φ.ker from hker.symm, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top, DihedralGroup.nat_card]
  have hidxM₁M : M₁.relIndex M = 2 := by
    have h1 : M₁.relIndex M = (Subgroup.comap φ rot).index := by
      rw [Subgroup.relIndex, hM₁sub]
    rw [h1, Subgroup.index_comap_of_surjective rot hφ, TauCeti.index_dihedralRotations]
  have hidxNM₁ : N.relIndex M₁ = p := by
    have h := Subgroup.relIndex_mul_relIndex N M₁ M hNM₁ hM₁M
    rw [hidxM₁M, hidxNM] at h
    omega
  have hbker : φ ⟨b, hbM⟩ ≠ 1 := by
    intro h1
    apply hbN
    have hmem : ⟨b, hbM⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hker] at hmem
    exact hmem
  have hbordM : orderOf (⟨b, hbM⟩ : ↥M) = p := by
    have h := orderOf_injective (Subgroup.subtype M) Subtype.val_injective ⟨b, hbM⟩
    exact h.symm.trans hbord
  have hdvd : orderOf (φ ⟨b, hbM⟩) ∣ p := by
    have h := orderOf_map_dvd φ ⟨b, hbM⟩
    rwa [hbordM] at h
  have hord : orderOf (φ ⟨b, hbM⟩) = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hbker
    · exact h1
  have hb_rot : φ ⟨b, hbM⟩ ∈ rot := by
    rw [TauCeti.mem_dihedralRotations_iff]
    by_contra h
    push Not at h
    rcases hd : (φ ⟨b, hbM⟩) with i | i
    · exact h i hd
    · have h2 : orderOf (DihedralGroup.sr i) = p := by rw [← hd]; exact hord
      rw [DihedralGroup.orderOf_sr] at h2
      exact hp2 h2.symm
  have hbM₁ : b ∈ M₁ := by
    refine Subgroup.mem_map.mpr ⟨⟨b, hbM⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact hb_rot
  let K : Subgroup G := M₁ ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G)
  have hKM₁ : K ≤ M₁ := inf_le_left
  have hKR : K ≤ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) := inf_le_right
  have hTNK : T ⊓ N ≤ K :=
    le_inf (inf_le_right.trans hNM₁) Subgroup.le_normalizer
  have hTNK' : T ⊓ N ≤ K ⊓ N := le_inf hTNK inf_le_right
  have hbK : b ∈ K := ⟨hbM₁, hbTN⟩
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := by
    have hTNN : T ≤ Subgroup.normalizer
        (Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) : Subgroup G) :=
      hTnormTN.trans Subgroup.le_normalizer
    exact (le_inf hTM₁ hTNN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hNnormalM₁ : (N.subgroupOf M₁).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hM₁M.trans hMN)
  have hodd : Odd ((T ⊓ N).relIndex K) := by
    have := hNnormalM₁
    have hR_of_le : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ N)
        (N ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G)) :=
      hTN.of_le (le_inf inf_le_right Subgroup.le_normalizer) inf_le_left
    have hodd_a : Odd ((T ⊓ N).relIndex
        (N ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G))) := by
      have hnot : ¬ 2 ∣ (T ⊓ N).relIndex
          (N ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G)) :=
        (CFSG.ABGLocalTools.isSylowOf_iff.mp hR_of_le).2.2
      exact Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hnot)
    have hodd_b : Odd ((K ⊓ N).relIndex K) := by
      have hsupK : N ⊔ K ≤ M₁ := sup_le hNM₁ hKM₁
      have hNK : N.relIndex K = N.relIndex (N ⊔ K) := by
        have h := Subgroup.relIndex_sup_left (K.subgroupOf M₁) (N.subgroupOf M₁)
        rw [← Subgroup.subgroupOf_sup hNM₁ hKM₁,
          Subgroup.relIndex_subgroupOf hsupK,
          Subgroup.relIndex_subgroupOf hKM₁] at h
        exact h.symm
      have h2 : (K ⊓ N).relIndex K = N.relIndex K := by
        rw [inf_comm]
        exact Subgroup.inf_relIndex_right N K
      have hdiv : N.relIndex (N ⊔ K) ∣ p := by
        have hmul := Subgroup.relIndex_mul_relIndex N (N ⊔ K) M₁ le_sup_left hsupK
        rw [hidxNM₁] at hmul
        exact ⟨_, hmul.symm⟩
      have hnot1 : N.relIndex (N ⊔ K) ≠ 1 := by
        intro h1
        have hKN : K ≤ N := by
          have : N.relIndex K = 1 := by rw [hNK, h1]
          exact Subgroup.relIndex_eq_one.mp this
        exact hbN (hKN hbK)
      rw [h2, hNK]
      rcases (Nat.dvd_prime hp).mp hdiv with h1 | h1
      · exact absurd h1 hnot1
      · rw [h1]
        exact hp.odd_of_ne_two hp2
    have hodd_R1 : Odd ((T ⊓ N).relIndex (K ⊓ N)) := by
      have hle : K ⊓ N ≤ N ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) :=
        le_inf inf_le_right (inf_le_left.trans hKR)
      have hmul := Subgroup.relIndex_mul_relIndex (T ⊓ N) (K ⊓ N)
        (N ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G)) hTNK' hle
      exact Odd.of_dvd_nat hodd_a ⟨_, hmul.symm⟩
    have hmul := Subgroup.relIndex_mul_relIndex (T ⊓ N) (K ⊓ N) K hTNK' inf_le_left
    rw [← hmul]
    exact hodd_R1.mul hodd_b
  obtain ⟨S, hS, hTS⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_isSylowOf_le_normalizer_sup_of_odd
      hp hp2 hT2 hTN2 hTNK hKR hTK hTnormTN hodd
  have hSX_bot : S ⊓ X = ⊥ := by
    have hSXp : IsPGroup p ↥(S ⊓ X) := hS.isPGroup.to_le inf_le_left
    have hle : S ⊓ X ≤ X ⊓ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G) := by
      intro y hy
      have hyS : y ∈ S := hy.1
      have hyX : y ∈ X := hy.2
      have hyN : y ∈ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) :=
        hKR (hS.le hyS)
      refine ⟨hyX, ?_⟩
      change y ∈ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G)
      rw [Subgroup.mem_normalizer_iff] at hyN ⊢
      intro z
      constructor
      · rintro ⟨hzT, hzX⟩
        have hzTN : z ∈ T ⊓ N := ⟨hzT, hXN hzX⟩
        have h1 : y * z * y⁻¹ ∈ T ⊓ N := (hyN z).mp hzTN
        exact ⟨h1.1, X.mul_mem (X.mul_mem hyX hzX) (X.inv_mem hyX)⟩
      · rintro ⟨hzT, hzX⟩
        have hmem : y * z * y⁻¹ ∈ T ⊓ N := ⟨hzT, hXN hzX⟩
        have hzT' : z ∈ T := ((hyN z).mpr hmem).1
        have hzX' : z ∈ X := by
          have h := X.mul_mem (X.mul_mem (X.inv_mem hyX) hzX) hyX
          rwa [show y⁻¹ * (y * z * y⁻¹) * y = z from by group] at h
        exact ⟨hzT', hzX'⟩
    have hnotdvd : ¬ p ∣ Nat.card ↥(S ⊓ X) := by
      have hdvd : Nat.card ↥(S ⊓ X) ∣
          Nat.card ↥(X ⊓ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G)) :=
        Subgroup.card_dvd_of_le hle
      exact fun h => hpK (h.trans hdvd)
    have hcard1 : Nat.card ↥(S ⊓ X) = 1 := by
      rcases hSXp.card_eq_or_dvd with h1 | h1
      · exact h1
      · exact absurd h1 hnotdvd
    exact Subgroup.card_eq_one.mp hcard1
  have hbzp : IsPGroup p ↥(Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbord, pow_one])
  obtain ⟨k, hkK, hkS⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_conj_le_of_isSylowOf hS
      (Subgroup.zpowers_le.mpr hbK) hbzp
  let s : G := k⁻¹ * b * k
  have hsS : s ∈ S := hkS b (Subgroup.mem_zpowers b)
  have hkM : k ∈ M := hM₁M (hKM₁ hkK)
  have hsN : s ∉ N := by
    intro hs
    apply hbN
    have hb_eq : b = k * s * k⁻¹ := by dsimp only [s]; group
    rw [hb_eq]
    exact (Subgroup.mem_normalizer_iff.mp (hMN hkM) s).mp hs
  have hsord : orderOf s = p := by
    have h1 : orderOf s = orderOf ((MulAut.conj k⁻¹) b) := by
      dsimp only [s]
      rw [MulAut.conj_apply, inv_inv]
    rw [h1, MulEquiv.orderOf_eq, hbord]
  have hsM : s ∈ M := hM₁M (hKM₁ (hS.le hsS))
  have hCX : C ≤ Subgroup.normalizer (X : Set G) := hCM.trans hMX
  have hXNnormal : (X.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hNM.trans hMX)
  have := hXNnormal
  let ψ : ↥C →* (↥N ⧸ (X.subgroupOf N)) :=
    (QuotientGroup.mk' (X.subgroupOf N)).comp (Subgroup.inclusion hCN)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (X.subgroupOf N) q
    have hn : (n : G) ∈ (↑(C ⊔ X) : Set G) := by
      rw [show C ⊔ X = X ⊔ C from sup_comm C X]
      exact n.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right C X hCX] at hn
    obtain ⟨c, hc, x, hx, hcx⟩ := hn
    refine ⟨⟨c, hc⟩, ?_⟩
    change (QuotientGroup.mk' (X.subgroupOf N)) (Subgroup.inclusion hCN ⟨c, hc⟩) =
      (QuotientGroup.mk' (X.subgroupOf N)) n
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hval : ((Subgroup.inclusion hCN ⟨c, hc⟩)⁻¹ * n : ↥N) = ⟨x, hXN hx⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hcx]
      group
    rw [Subgroup.mem_subgroupOf, hval]
    exact hx
  have hcycC : ∀ P : Subgroup ↥C, IsPGroup p P → IsCyclic P := by
    intro P hP
    have hrk : CFSG.Open.pRank p P ≤ 1 := by
      calc CFSG.Open.pRank p P
          ≤ CFSG.Open.pRank p (P.map C.subtype) :=
            CFSG.SectionRank.pRank_le_map hp.one_lt C.subtype C.subtype_injective P
        _ ≤ CFSG.Open.pRank p C :=
            CFSG.SectionRank.pRank_mono hp.one_lt (Subgroup.map_subtype_le P)
        _ ≤ 1 := hrank
    exact
      CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H.isCyclic_of_pRank_le_one
        hp hp2 hP hrk
  have hcycNX : ∀ E : Subgroup (↥N ⧸ (X.subgroupOf N)), IsPGroup p E → IsCyclic E :=
    CFSG.Quasithin.QP.forall_isCyclic_of_surjective ψ hψ hcycC
  let D : Subgroup G := S ⊓ N
  have hD_le_S : D ≤ S := inf_le_left
  have hD_le_N : D ≤ N := inf_le_right
  have hDp : IsPGroup p ↥D := hS.isPGroup.to_le inf_le_left
  have hDX : D ⊓ X = ⊥ := by
    have h : D ⊓ X = S ⊓ X := by
      dsimp only [D]
      rw [inf_assoc, inf_eq_right.mpr hXN]
    rw [h, hSX_bot]
  have hDcyc : IsCyclic ↥D := by
    let π : ↥D →* (↥N ⧸ (X.subgroupOf N)) :=
      (QuotientGroup.mk' (X.subgroupOf N)).comp (Subgroup.inclusion hD_le_N)
    have hπinj : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro d hd
      rw [MonoidHom.mem_ker] at hd
      have hdX : (d : G) ∈ X := by
        have := (QuotientGroup.eq_one_iff (Subgroup.inclusion hD_le_N d)).mp hd
        exact Subgroup.mem_subgroupOf.mp this
      have hdD : (d : G) ∈ D := d.2
      have hdinf : (d : G) ∈ D ⊓ X := ⟨hdD, hdX⟩
      rw [hDX, Subgroup.mem_bot] at hdinf
      exact Subgroup.mem_bot.mpr (Subtype.ext hdinf)
    let P : Subgroup (↥N ⧸ (X.subgroupOf N)) := (⊤ : Subgroup ↥D).map π
    have hPp : IsPGroup p P := by
      have htop : IsPGroup p ↥(⊤ : Subgroup ↥D) :=
        hDp.of_equiv Subgroup.topEquiv.symm
      exact htop.map π
    have hPcyc : IsCyclic ↥P := hcycNX P hPp
    let π' : ↥D →* ↥P :=
      π.codRestrict P (fun d => Subgroup.mem_map_of_mem π (Subgroup.mem_top d))
    have hπ'inj : Function.Injective π' := by
      intro a b hab
      apply hπinj
      exact congrArg Subtype.val hab
    exact isCyclic_of_injective π' hπ'inj
  have hS_M₁ : S ≤ M₁ := hS.le.trans hKM₁
  have hNS_eq : N.relIndex S = N.relIndex (N ⊔ S) := by
    have := hNnormalM₁
    have hsupS : N ⊔ S ≤ M₁ := sup_le hNM₁ hS_M₁
    have h := Subgroup.relIndex_sup_left (S.subgroupOf M₁) (N.subgroupOf M₁)
    rw [← Subgroup.subgroupOf_sup hNM₁ hS_M₁,
        Subgroup.relIndex_subgroupOf hsupS,
        Subgroup.relIndex_subgroupOf hS_M₁] at h
    exact h.symm
  have hD_idx : D.relIndex S = p := by
    have hD_eq : D.relIndex S = N.relIndex S := by
      dsimp only [D]
      rw [inf_comm]
      exact Subgroup.inf_relIndex_right N S
    have hdiv : N.relIndex (N ⊔ S) ∣ p := by
      have hmul := Subgroup.relIndex_mul_relIndex N (N ⊔ S) M₁ le_sup_left
        (sup_le hNM₁ hS_M₁)
      rw [hidxNM₁] at hmul
      exact ⟨_, hmul.symm⟩
    have hnot1 : N.relIndex (N ⊔ S) ≠ 1 := by
      intro h1
      have hSN : S ≤ N := by
        have : N.relIndex S = 1 := by rw [hNS_eq, h1]
        exact Subgroup.relIndex_eq_one.mp this
      exact hsN (hSN hsS)
    rw [hD_eq, hNS_eq]
    rcases (Nat.dvd_prime hp).mp hdiv with h1 | h1
    · exact absurd h1 hnot1
    · exact h1
  have hfac2p : (2 * p).factorization 2 = 1 := by
    rw [Nat.factorization_mul (by norm_num) hp.ne_zero, Nat.Prime.factorization Nat.prime_two,
      Nat.Prime.factorization hp]
    simp [hp2]
  have hcardM : Nat.card ↥M = 2 * p * Nat.card ↥N := by
    have h := Subgroup.relIndex_mul_card N M
    rw [inf_eq_left.mpr hNM, hidxNM] at h
    exact h.symm
  have hfacM : (Nat.card ↥M).factorization 2 = (Nat.card ↥N).factorization 2 + 1 := by
    rw [hcardM, Nat.factorization_mul (mul_ne_zero (by norm_num) hp.ne_zero)
      (Nat.card_pos.ne'), Nat.factorization_mul (by norm_num) hp.ne_zero,
      Nat.Prime.factorization Nat.prime_two, Nat.Prime.factorization hp]
    simp [hp2, add_comm]
  have hcardT : Nat.card ↥T = 2 * Nat.card ↥(T ⊓ N) := by
    rw [hT.card_eq, hTN.card_eq, hfacM, pow_succ]
    ring
  have hidxTTN : (T ⊓ N).relIndex T = 2 := by
    have h := Subgroup.relIndex_mul_card (T ⊓ N) T
    rw [inf_eq_left.mpr inf_le_left, hcardT] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have ht_exists : ∃ t ∈ T, t ∉ T ⊓ N := by
    by_contra h
    push Not at h
    have hle : T ≤ T ⊓ N := fun t ht => h t ht
    have heq : T = T ⊓ N := le_antisymm hle inf_le_left
    have hc : Nat.card ↥(T ⊓ N) = 2 * Nat.card ↥(T ⊓ N) := by
      have h := hcardT
      rw [heq] at h
      simpa only [inf_assoc, inf_idem] using h
    have hpos : 0 < Nat.card ↥(T ⊓ N) := Nat.card_pos
    omega
  obtain ⟨t, htT, htTN⟩ := ht_exists
  have htN : t ∉ N := fun h => htTN ⟨htT, h⟩
  have htM : t ∈ M := hTM htT
  have ht_pow2 : ∃ kk : ℕ, orderOf (⟨t, htM⟩ : ↥M) = 2 ^ kk := by
    have hzp : Subgroup.zpowers t ≤ T := Subgroup.zpowers_le.mpr htT
    have h2 : IsPGroup 2 ↥(Subgroup.zpowers t) := hT2.to_le hzp
    obtain ⟨kk, hkk⟩ := IsPGroup.iff_card.mp h2
    refine ⟨kk, ?_⟩
    rw [Nat.card_zpowers] at hkk
    rw [Subgroup.orderOf_mk t htM]
    exact hkk
  obtain ⟨kk, hkk⟩ := ht_pow2
  have htker : φ ⟨t, htM⟩ ≠ 1 := by
    intro h1
    apply htN
    have hmem : ⟨t, htM⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hker] at hmem
    exact hmem
  have htord2 : orderOf (φ ⟨t, htM⟩) = 2 := by
    rcases hd : (φ ⟨t, htM⟩) with i | i
    · exfalso
      have hdp : orderOf (DihedralGroup.r i) ∣ p := by
        apply orderOf_dvd_of_pow_eq_one
        rw [DihedralGroup.r_pow]
        have : i * (p : ZMod p) = 0 := by simp
        rw [this, DihedralGroup.r_zero]
      have hd2 : orderOf (DihedralGroup.r i) ∣ 2 ^ kk := by
        have h := orderOf_map_dvd φ ⟨t, htM⟩
        rw [hkk, hd] at h
        exact h
      have hcop : Nat.Coprime p (2 ^ kk) :=
        Nat.Coprime.pow_right kk ((Nat.Prime.coprime_iff_not_dvd hp).mpr (by
          intro h
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)))
      have hone : orderOf (DihedralGroup.r i) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hdp hd2
      apply htker
      rw [hd]
      exact orderOf_eq_one_iff.mp hone
    · exact DihedralGroup.orderOf_sr i
  have ht2N : t ^ 2 ∈ N := by
    have hphi : φ ⟨t ^ 2, M.pow_mem htM 2⟩ = 1 := by
      rw [show (⟨t ^ 2, M.pow_mem htM 2⟩ : ↥M) = ⟨t, htM⟩ ^ 2 from Subtype.ext (by simp),
        map_pow]
      have h2 : φ ⟨t, htM⟩ ^ 2 = 1 := by
        rw [← htord2]
        exact pow_orderOf_eq_one _
      rw [h2]
    have hmem : ⟨t ^ 2, M.pow_mem htM 2⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr hphi
    rw [hker] at hmem
    exact hmem
  have ht2R : t ^ 2 ∈ T ⊓ N := ⟨T.pow_mem htT 2, ht2N⟩
  let st : G := t * s * t⁻¹
  have hst_mem : st ∈ S ⊔ (T ⊓ N : Subgroup G) := by
    have htN' : t ∈ Subgroup.normalizer ((S ⊔ (T ⊓ N) : Subgroup G) : Set G) := hTS htT
    have hsH : s ∈ (S ⊔ (T ⊓ N) : Subgroup G) := Subgroup.mem_sup_left hsS
    dsimp only [st]
    exact (Subgroup.mem_normalizer_iff.mp htN' s).mp hsH
  obtain ⟨σ, hσS, u, huTN, hst_eq⟩ : ∃ σ ∈ S, ∃ u ∈ T ⊓ N, σ * u = st := by
    have hSRnorm : S ≤ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) := hS.le.trans hKR
    have hset : (↑(S ⊔ (T ⊓ N)) : Set G) =
        (S : Set G) * ((T ⊓ N : Subgroup G) : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right S (T ⊓ N) hSRnorm
    have hst' : st ∈ (↑(S ⊔ (T ⊓ N)) : Set G) := hst_mem
    rw [hset] at hst'
    exact Set.mem_mul.mp hst'
  have hσM : σ ∈ M := hM₁M (hKM₁ (hS.le hσS))
  have huM : u ∈ M := hNM huTN.2
  have hu_ker : φ ⟨u, huM⟩ = 1 := by
    have hmem : ⟨u, huM⟩ ∈ φ.ker := by
      rw [hker]
      exact huTN.2
    exact MonoidHom.mem_ker.mp hmem
  have hσp : σ ^ p = 1 := by
    have hmain : ∀ n : ℕ, ∃ v ∈ T ⊓ N, (σ * u) ^ n = σ ^ n * v := by
      intro n
      induction n with
      | zero => exact ⟨1, (T ⊓ N).one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨v, hv, hvn⟩ := ih
        have hconj : σ⁻¹ * v * σ ∈ T ⊓ N := by
          have := (Subgroup.mem_normalizer_iff.mp (hKR (hS.le (S.inv_mem hσS))) v).mp hv
          simpa only [inv_inv] using this
        refine ⟨(σ⁻¹ * v * σ) * u, (T ⊓ N).mul_mem hconj huTN, ?_⟩
        rw [pow_succ, hvn]
        group
    obtain ⟨v, hv, hvp⟩ := hmain p
    have hsp : s ^ p = 1 := by rw [← hsord]; exact pow_orderOf_eq_one s
    have hst_pow : st ^ p = 1 := by
      dsimp only [st]
      rw [conj_pow, hsp, mul_one, mul_inv_cancel]
    have h1 : σ ^ p * v = 1 := by
      rw [← hvp, hst_eq, hst_pow]
    have hσR : σ ^ p ∈ T ⊓ N := by
      have hval : σ ^ p = v⁻¹ := by
        calc σ ^ p = (σ ^ p * v) * v⁻¹ := by group
          _ = 1 * v⁻¹ := by rw [h1]
          _ = v⁻¹ := one_mul _
      rw [hval]
      exact (T ⊓ N).inv_mem hv
    have hmem : σ ^ p ∈ S ⊓ (T ⊓ N) := ⟨S.pow_mem hσS p, hσR⟩
    have hSR_bot : S ⊓ (T ⊓ N) = ⊥ := by
      have hdisj : Disjoint S (T ⊓ N) :=
        IsPGroup.disjoint_of_ne p 2 hp2 S (T ⊓ N) hS.isPGroup hTN2
      exact hdisj.eq_bot
    rw [hSR_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hσne : σ ≠ 1 := by
    intro h1
    apply hsN
    have hstN : st ∈ N := by rw [← hst_eq, h1, one_mul]; exact huTN.2
    have hconj : t⁻¹ * st * t ∈ N := by
      have h := (Subgroup.mem_normalizer_iff.mp (hMN (M.inv_mem htM)) st).mp hstN
      simpa only [inv_inv] using h
    have hs_eq : s = t⁻¹ * st * t := by dsimp only [st]; group
    rwa [hs_eq]
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσne
  have hσM₁ : σ ∈ M₁ := hKM₁ (hS.le hσS)
  let Ω : Subgroup G := (CFSG.omega₁ (G := ↥S) (p := p)).map S.subtype
  have hΩel : CFSG.Open.IsElemAbelian p Ω := by
    by_cases hcycS : IsCyclic ↥S
    · have : IsMulCommutative ↥S := hcycS.isMulCommutative
      have hE : CFSG.IsElementaryAbelian p (CFSG.omega₁ (G := ↥S) (p := p)) :=
        CFSG.IsElementaryAbelian.omega₁_of_isMulCommutative (p := p) ↥S
      have hE' : CFSG.Open.IsElemAbelian p (CFSG.omega₁ (G := ↥S) (p := p)) :=
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hE
      exact CFSG.SectionRank.isElemAbelian_map hE' S.subtype
    · have : Fact (IsPGroup p ↥S) := ⟨hS.isPGroup⟩
      have hindex : ∃ S₀ : Subgroup ↥S, IsCyclic S₀ ∧ Nat.card (↥S ⧸ S₀) = p := by
        refine ⟨(S ⊓ N).subgroupOf S, ?_, ?_⟩
        · have hcycD : IsCyclic ↥(S ⊓ N) := by simpa only [D] using hDcyc
          exact (Subgroup.subgroupOfEquivOfLe inf_le_left).isCyclic.mpr hcycD
        · rw [← Subgroup.index_eq_card]
          show ((S ⊓ N).subgroupOf S).index = p
          simpa only [Subgroup.relIndex, D] using hD_idx
      have hΩ := CFSG.lemma_4_5_b (R := ↥S) hp2 hcycS hindex
      have hE' : CFSG.Open.IsElemAbelian p (CFSG.omega₁ (G := ↥S) (p := p)) :=
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hΩ.2
      exact CFSG.SectionRank.isElemAbelian_map hE' S.subtype
  have hsΩ : s ∈ Ω := by
    have hsp : (⟨s, hsS⟩ : ↥S) ^ p = 1 := by
      apply Subtype.ext
      exact (show s ^ p = 1 from by rw [← hsord]; exact pow_orderOf_eq_one s)
    have hmem : (⟨s, hsS⟩ : ↥S) ∈ Subgroup.closure {x : ↥S | x ^ (p ^ 1) = 1} :=
      Subgroup.subset_closure (by simpa using hsp)
    change s ∈ (CFSG.omega₁ (G := ↥S) (p := p)).map S.subtype
    exact Subgroup.mem_map_of_mem S.subtype hmem
  have hσΩ : σ ∈ Ω := by
    have hσp' : (⟨σ, hσS⟩ : ↥S) ^ p = 1 := by
      apply Subtype.ext
      exact hσp
    have hmem : (⟨σ, hσS⟩ : ↥S) ∈ Subgroup.closure {x : ↥S | x ^ (p ^ 1) = 1} :=
      Subgroup.subset_closure (by simpa using hσp')
    change σ ∈ (CFSG.omega₁ (G := ↥S) (p := p)).map S.subtype
    exact Subgroup.mem_map_of_mem S.subtype hmem
  let y : G := s * σ⁻¹
  have hyΩ : y ∈ Ω := Ω.mul_mem hsΩ (Ω.inv_mem hσΩ)
  have hyp : y ^ p = 1 := hΩel.2 y hyΩ
  have hyS : y ∈ S := S.mul_mem hsS (S.inv_mem hσS)
  have hyM : y ∈ M := hM₁M (hKM₁ (hS.le hyS))
  have hyR : y ∈ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) :=
    hKR (hS.le hyS)
  have hs_rot : φ ⟨s, hsM⟩ ∈ rot := hmem_rot (hKM₁ (hS.le hsS))
  have hσ_rot : φ ⟨σ, hσM⟩ ∈ rot := hmem_rot hσM₁
  have hs_ne1 : φ ⟨s, hsM⟩ ≠ 1 := by
    intro h1
    apply hsN
    have hmem : ⟨s, hsM⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hker] at hmem
    exact hmem
  have hs_pow_phi : φ ⟨s, hsM⟩ ^ p = 1 := by
    have hsp : (⟨s, hsM⟩ : ↥M) ^ p = 1 := by
      apply Subtype.ext
      exact (show s ^ p = 1 from by rw [← hsord]; exact pow_orderOf_eq_one s)
    rw [← map_pow, hsp, map_one]
  have hs_order : orderOf (φ ⟨s, hsM⟩) = p := orderOf_eq_prime hs_pow_phi hs_ne1
  have ht_reflect : φ ⟨t, htM⟩ ∉ rot := by
    intro hmem
    have hdvd : orderOf (φ ⟨t, htM⟩) ∣ p := by
      have h := Subgroup.orderOf_dvd_natCard rot hmem
      rwa [TauCeti.card_dihedralRotations] at h
    rw [htord2] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd).symm
  have hσ_eq : φ ⟨σ, hσM⟩ = (φ ⟨s, hsM⟩)⁻¹ := by
    have hφeq : φ ⟨σ * u, M.mul_mem hσM huM⟩ =
        φ ⟨st, M.mul_mem (M.mul_mem htM hsM) (M.inv_mem htM)⟩ := by
      congr 1
      exact Subtype.ext hst_eq
    rw [show (⟨σ * u, M.mul_mem hσM huM⟩ : ↥M) = ⟨σ, hσM⟩ * ⟨u, huM⟩ from
        Subtype.ext rfl, map_mul, hu_ker, mul_one] at hφeq
    have hst_phi : φ ⟨st, M.mul_mem (M.mul_mem htM hsM) (M.inv_mem htM)⟩ =
        φ ⟨t, htM⟩ * φ ⟨s, hsM⟩ * (φ ⟨t, htM⟩)⁻¹ := by
      dsimp only [st]
      rw [show (⟨t * s * t⁻¹, M.mul_mem (M.mul_mem htM hsM) (M.inv_mem htM)⟩ : ↥M) =
        ⟨t, htM⟩ * ⟨s, hsM⟩ * ⟨t, htM⟩⁻¹ from Subtype.ext rfl,
        map_mul, map_mul, map_inv]
    rw [hst_phi, TauCeti.conj_eq_inv_of_notMem_dihedralRotations ht_reflect hs_rot] at hφeq
    exact hφeq
  have hyN : y ∉ N := by
    intro hy
    have hyker : φ ⟨y, hNM hy⟩ = 1 := by
      have hmem : ⟨y, hNM hy⟩ ∈ φ.ker := by
        rw [hker]
        exact hy
      exact MonoidHom.mem_ker.mp hmem
    have hy_eq : (⟨y, hNM hy⟩ : ↥M) = ⟨s, hsM⟩ * ⟨σ, hσM⟩⁻¹ :=
      Subtype.ext (by dsimp only [y]; rfl)
    rw [hy_eq, map_mul, map_inv, hσ_eq] at hyker
    have hsq : φ ⟨s, hsM⟩ ^ 2 = 1 := by
      simpa [pow_two] using hyker
    have hdvd : orderOf (φ ⟨s, hsM⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rw [hs_order] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have hy_ne1 : y ≠ 1 := by
    intro h1
    apply hyN
    rw [h1]
    exact N.one_mem
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy_ne1
  let c : G := t ^ 2 * s * (t ^ 2)⁻¹ * s⁻¹
  have hcR : c ∈ T ⊓ N := by
    have h1 : t ^ 2 ∈ T ⊓ N := ht2R
    have h2 : s * (t ^ 2)⁻¹ * s⁻¹ ∈ T ⊓ N := by
      have hsNR : s ∈ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) := hKR (hS.le hsS)
      exact (Subgroup.mem_normalizer_iff.mp hsNR (t ^ 2)⁻¹).mp ((T ⊓ N).inv_mem ht2R)
    have heq : t ^ 2 * (s * (t ^ 2)⁻¹ * s⁻¹) = c := by dsimp only [c]; group
    rw [← heq]
    exact (T ⊓ N).mul_mem h1 h2
  let r0 : G := s⁻¹ * c * s
  have hr0R : r0 ∈ T ⊓ N := by
    have h := (Subgroup.mem_normalizer_iff.mp (hKR (hS.le (S.inv_mem hsS))) c).mp hcR
    simpa only [r0, inv_inv] using h
  have hconj_s : t * (t * s * t⁻¹) * t⁻¹ = s * r0 := by
    dsimp only [c, r0]
    simp only [pow_two]
    group
  have hu_t_R : t * u⁻¹ * t⁻¹ ∈ T ⊓ N :=
    (Subgroup.mem_normalizer_iff.mp (hTnormTN htT) (u⁻¹)).mp ((T ⊓ N).inv_mem huTN)
  let r1 : G := r0 * (t * u⁻¹ * t⁻¹)
  have hr1R : r1 ∈ T ⊓ N := (T ⊓ N).mul_mem hr0R hu_t_R
  have hσt : t * σ * t⁻¹ = s * r1 := by
    have hσ_eq' : σ = (t * s * t⁻¹) * u⁻¹ := by
      have h := hst_eq
      dsimp only [st] at h
      calc σ = (σ * u) * u⁻¹ := by group
        _ = (t * s * t⁻¹) * u⁻¹ := by rw [h]
    rw [hσ_eq']
    calc t * ((t * s * t⁻¹) * u⁻¹) * t⁻¹
        = (t * (t * s * t⁻¹) * t⁻¹) * (t * u⁻¹ * t⁻¹) := by group
      _ = (s * r0) * (t * u⁻¹ * t⁻¹) := by rw [hconj_s]
      _ = s * r1 := by dsimp only [r1]; group
  let r2 : G := s * (u * r1⁻¹) * s⁻¹
  have hr2R : r2 ∈ T ⊓ N := by
    have hmem : u * r1⁻¹ ∈ T ⊓ N := (T ⊓ N).mul_mem huTN ((T ⊓ N).inv_mem hr1R)
    have h := (Subgroup.mem_normalizer_iff.mp (hKR (hS.le hsS)) (u * r1⁻¹)).mp hmem
    simpa only [r2] using h
  have hyt : t * y * t⁻¹ = y⁻¹ * r2 := by
    have h1 : t * (s * σ⁻¹) * t⁻¹ = (t * s * t⁻¹) * (t * σ * t⁻¹)⁻¹ := by group
    have hy_inv : y⁻¹ = σ * s⁻¹ := by dsimp only [y]; group
    calc t * y * t⁻¹ = t * (s * σ⁻¹) * t⁻¹ := by dsimp only [y]
      _ = (t * s * t⁻¹) * (t * σ * t⁻¹)⁻¹ := h1
      _ = (σ * u) * (s * r1)⁻¹ := by rw [hst_eq, hσt]
      _ = σ * s⁻¹ * r2 := by dsimp only [r2]; group
      _ = y⁻¹ * r2 := by rw [hy_inv]
  have ht_y_mem : t * y * t⁻¹ ∈ Subgroup.zpowers y ⊔ (T ⊓ N) := by
    rw [hyt]
    exact Subgroup.mul_mem_sup (Subgroup.inv_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y))
      hr2R
  have ht_map_le : (Subgroup.zpowers y ⊔ (T ⊓ N)).map (MulAut.conj t).toMonoidHom ≤
      Subgroup.zpowers y ⊔ (T ⊓ N) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [MonoidHom.map_zpowers]
      simpa [MulAut.conj_apply] using Subgroup.zpowers_le.mpr ht_y_mem
    · have hRmap : (T ⊓ N).map (MulEquiv.toMonoidHom (MulAut.conj t)) = T ⊓ N := by
        simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnormTN htT))
      rw [hRmap]
      exact le_sup_right
  have ht_map_eq : (Subgroup.zpowers y ⊔ (T ⊓ N)).map (MulAut.conj t).toMonoidHom =
      Subgroup.zpowers y ⊔ (T ⊓ N) := by
    refine Subgroup.eq_of_le_of_card_ge ht_map_le ?_
    rw [Subgroup.card_map_of_injective (K := Subgroup.zpowers y ⊔ (T ⊓ N))
      (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective]
  have ht_norm : t ∈ Subgroup.normalizer
      ((Subgroup.zpowers y ⊔ (T ⊓ N) : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr ht_map_eq
  have hT_le : T ≤ Subgroup.zpowers t ⊔ (T ⊓ N) := by
    have hle : Subgroup.zpowers t ⊔ (T ⊓ N) ≤ T :=
      sup_le (Subgroup.zpowers_le.mpr htT) inf_le_left
    have hRT : (T ⊓ N).relIndex (Subgroup.zpowers t ⊔ (T ⊓ N)) = 2 := by
      have hmul := Subgroup.relIndex_mul_relIndex (T ⊓ N)
        (Subgroup.zpowers t ⊔ (T ⊓ N)) T le_sup_right hle
      rw [hidxTTN] at hmul
      have hnot1 : (T ⊓ N).relIndex (Subgroup.zpowers t ⊔ (T ⊓ N)) ≠ 1 := by
        intro h1
        have hleR : Subgroup.zpowers t ⊔ (T ⊓ N) ≤ T ⊓ N :=
          Subgroup.relIndex_eq_one.mp h1
        exact htTN (hleR (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)))
      have hdvd : (T ⊓ N).relIndex (Subgroup.zpowers t ⊔ (T ⊓ N)) ∣ 2 := ⟨_, hmul.symm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact absurd h1 hnot1
      · exact h1
    have hcard_sup : Nat.card ↥(Subgroup.zpowers t ⊔ (T ⊓ N)) =
        2 * Nat.card ↥(T ⊓ N) := by
      have h := Subgroup.relIndex_mul_card (T ⊓ N) (Subgroup.zpowers t ⊔ (T ⊓ N))
      have hinf : (T ⊓ N) ⊓ (Subgroup.zpowers t ⊔ (T ⊓ N)) = T ⊓ N :=
        inf_eq_left.mpr le_sup_right
      rw [hinf, hRT] at h
      exact h.symm
    have hcard_le : Nat.card ↥T ≤ Nat.card ↥(Subgroup.zpowers t ⊔ (T ⊓ N)) := by
      rw [hcardT, hcard_sup]
    have heq : Subgroup.zpowers t ⊔ (T ⊓ N) = T :=
      Subgroup.eq_of_le_of_card_ge hle hcard_le
    rw [heq]
  have hT_in : T ≤ Subgroup.normalizer
      ((Subgroup.zpowers y ⊔ (T ⊓ N) : Subgroup G) : Set G) := by
    have hR_in : T ⊓ N ≤ Subgroup.normalizer
        ((Subgroup.zpowers y ⊔ (T ⊓ N) : Subgroup G) : Set G) :=
      le_sup_right.trans Subgroup.le_normalizer
    have hzt_in : Subgroup.zpowers t ≤ Subgroup.normalizer
        ((Subgroup.zpowers y ⊔ (T ⊓ N) : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr ht_norm
    exact hT_le.trans (sup_le hzt_in hR_in)
  refine ⟨y, hyM, ?_, hyord, ?_, ?_⟩
  · simpa only [N] using hyN
  · simpa only [N] using hyR
  · simpa only [N] using hT_in

theorem exists_orderOf_eq_prime_mem_normalizer_inf_of_dihedral
    {G : Type} [Group G] [Finite G] {M X C T : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hXM : X ≤ M) (hCM : C ≤ M) (hMX : M ≤ Subgroup.normalizer (X : Set G))
    (φ : ↥M →* DihedralGroup p) (hφ : Function.Surjective φ)
    (hker : φ.ker = (X ⊔ C).subgroupOf M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hrank : CFSG.Open.pRank p C ≤ 1)
    (hpK : ¬ p ∣ Nat.card ↥(X ⊓ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G)))
    (hy : ∃ y ∈ M, y ∉ X ⊔ C ∧ orderOf y = p) (hK : CFSG.Open.IsKGroup ↥M)
    (hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction) :
    ∃ b ∈ M, b ∉ X ⊔ C ∧ orderOf b = p ∧
      b ∈ Subgroup.normalizer ((T ⊓ (X ⊔ C) : Subgroup G) : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := X ⊔ C
  have hNM : N ≤ M := sup_le hXM hCM
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp ?_
    rw [← hker]
    exact MonoidHom.normal_ker φ
  have hTN : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ N) N :=
    hT.inf_of_le_normalizer hNM hMN
  let Xm : Subgroup ↥M := X.subgroupOf M
  have hXmNormal : Xm.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr hMX
  let q : ↥M →* (↥M ⧸ Xm) := QuotientGroup.mk' Xm
  have hXker : Xm ≤ φ.ker := by
    intro x hx
    rw [hker]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
  let π : (↥M ⧸ Xm) →* DihedralGroup p := QuotientGroup.lift Xm φ hXker
  have hπ : Function.Surjective π :=
    QuotientGroup.lift_surjective_of_surjective Xm φ hφ hXker
  have hkerπ : π.ker = ((X ⊔ C).subgroupOf M).map q := by
    rw [QuotientGroup.ker_lift, hker]
  have hCcyc : ∀ P : Subgroup ↥M, P ≤ C.subgroupOf M → IsPGroup p P → IsCyclic P := by
    intro P hP hPp
    have hPleC : P.map M.subtype ≤ C := by
      rintro z ⟨x, hx, rfl⟩
      exact hP hx
    have hcyc' : IsCyclic (P.map M.subtype) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H.isCyclic_of_pRank_le_one
        hp hp2 (hPp.map M.subtype)
        ((CFSG.SectionRank.pRank_mono hp.one_lt hPleC).trans hrank)
    exact (Subgroup.equivMapOfInjective (f := M.subtype) P M.subtype_injective).isCyclic.mpr hcyc'
  have hcyc : ∀ P : Subgroup (↥M ⧸ Xm), P ≤ π.ker → IsPGroup p P → IsCyclic P := by
    intro P hP hPp
    have hXmap_bot : (X.subgroupOf M).map q = ⊥ :=
      (Subgroup.map_eq_bot_iff (X.subgroupOf M)).mpr (by rw [QuotientGroup.ker_mk'])
    have hNmap : ((X ⊔ C).subgroupOf M).map q = (C.subgroupOf M).map q := by
      rw [Subgroup.subgroupOf_sup hXM hCM, Subgroup.map_sup, hXmap_bot, bot_sup_eq]
    have hPle : P ≤ (C.subgroupOf M).map q := by
      rw [hkerπ, hNmap] at hP
      exact hP
    exact CFSG.AGLEmbedding.isCyclic_of_le_map q hCcyc hPle hPp
  obtain ⟨y, hyM, hyN, hyord⟩ := hy
  let ybar : ↥M ⧸ Xm := q ⟨y, hyM⟩
  have hybar_out : ybar ∉ π.ker := by
    intro h
    apply hyN
    rw [hkerπ] at h
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp h
    have hxN : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp hx
    have h1 : q (x * (⟨y, hyM⟩ : ↥M)⁻¹) = 1 := by
      rw [map_mul, map_inv, hxq, mul_inv_cancel]
    have h2 : ((x * (⟨y, hyM⟩ : ↥M)⁻¹ : ↥M) : G) ∈ X :=
      (QuotientGroup.eq_one_iff (N := Xm) _).mp h1
    have h3 : (((⟨y, hyM⟩ : ↥M) * x⁻¹ : ↥M) : G) =
        ((x * (⟨y, hyM⟩ : ↥M)⁻¹ : ↥M) : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hyX : (((⟨y, hyM⟩ : ↥M) * x⁻¹ : ↥M) : G) ∈ X := by
      rw [h3]
      exact X.inv_mem h2
    have hy_eq : y = (((⟨y, hyM⟩ : ↥M) * x⁻¹ : ↥M) : G) * (x : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hy_eq]
    exact N.mul_mem (Subgroup.mem_sup_left hyX) hxN
  have hyp : (⟨y, hyM⟩ : ↥M) ^ p = 1 := by
    have h := pow_orderOf_eq_one (⟨y, hyM⟩ : ↥M)
    rwa [Subgroup.orderOf_mk, hyord] at h
  have hybar_ord : orderOf ybar = p := by
    have hdvd : orderOf ybar ∣ p := by
      rw [orderOf_dvd_iff_pow_eq_one]
      show (q ⟨y, hyM⟩) ^ p = 1
      rw [← map_pow, hyp, map_one]
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exfalso
      apply hybar_out
      rw [orderOf_eq_one_iff.mp h]
      exact π.ker.one_mem
    · exact h
  have hybarπ : π ybar ≠ 1 := fun h => hybar_out (MonoidHom.mem_ker.mpr h)
  let Nm : Subgroup ↥M := N.subgroupOf M
  let Q0 : Subgroup ↥M := (T ⊓ N).subgroupOf M
  have hTNm : CFSG.ABGLocalTools.IsSylowOf 2 Q0 Nm := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) M).mp ?_
    show CFSG.ABGLocalTools.IsSylowOf 2 (((T ⊓ N).subgroupOf M).map M.subtype)
      ((N.subgroupOf M).map M.subtype)
    rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hT.le),
      Subgroup.map_subgroupOf_eq_of_le hNM]
    exact hTN
  let Wbar : Subgroup (↥M ⧸ Xm) := Q0.map q
  have hQbar : CFSG.ABGLocalTools.IsSylowOf 2 Wbar π.ker := by
    obtain ⟨QH, hQH⟩ := hTNm.exists_sylow_eq_subgroupOf
    have hQ0leNm : Q0 ≤ Nm := Subgroup.subgroupOf_mono M inf_le_right
    let qN : ↥Nm →* Nm.map q :=
      (q.comp Nm.subtype).codRestrict (Nm.map q) fun x => Subgroup.mem_map_of_mem q x.2
    have hqN : Function.Surjective qN := by
      intro z
      obtain ⟨h, hh, hhz⟩ := Subgroup.mem_map.mp z.2
      exact ⟨⟨h, hh⟩, Subtype.ext hhz⟩
    let QbarN : Sylow 2 (Nm.map q) := QH.mapSurjective hqN
    have hmap_cod : (QH : Subgroup ↥Nm).map qN =
        ((QH : Subgroup ↥Nm).map (q.comp Nm.subtype)).subgroupOf (Nm.map q) := by
      ext x
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h, hh, rfl⟩
      · rintro ⟨h, hh, hx⟩
        exact ⟨h, hh, Subtype.ext hx⟩
    have hQbarN : (QbarN : Subgroup (Nm.map q)) = (Q0.map q).subgroupOf (Nm.map q) := by
      rw [Sylow.coe_mapSurjective hqN QH, hmap_cod]
      rw [← Subgroup.map_map (K := (QH : Subgroup ↥Nm)) q Nm.subtype, hQH,
        Subgroup.map_subgroupOf_eq_of_le hQ0leNm]
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (Q0.map q) (Nm.map q) := by
      refine ⟨QbarN, ?_⟩
      rw [hQbarN]
      exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_mono hQ0leNm)
    rwa [← hkerπ] at hSyl
  obtain ⟨ebar, hebarπ, hebarord, hebarN⟩ :=
    exists_orderOf_eq_prime_mem_normalizer_of_dihedral hp hp2 π hπ hcyc
      ⟨ybar, hybarπ, hybar_ord⟩ (hK.quotient Xm) hKF hQbar
  let Zbar : Subgroup (↥M ⧸ Xm) := Subgroup.zpowers ebar ⊔ Wbar
  let Zm : Subgroup ↥M := Zbar.comap q
  let Wm : Subgroup ↥M := Wbar.comap q
  have hWm_eq : Wm = Q0 ⊔ Xm := by
    change (Q0.map q).comap q = Q0 ⊔ Xm
    rw [QuotientGroup.comap_map_mk', sup_comm]
  have hUWm : Xm ≤ Wm := by
    rw [hWm_eq]
    exact le_sup_right
  have hWmZ : Wm ≤ Zm := Subgroup.comap_mono le_sup_right
  have hWm_le_Nm : Wm ≤ Nm := by
    rw [hWm_eq]
    exact sup_le (Subgroup.subgroupOf_mono M inf_le_right)
      (Subgroup.subgroupOf_mono M (le_sup_left : X ≤ X ⊔ C))
  have hWbar_normal : Zbar ≤ Subgroup.normalizer (Wbar : Set (↥M ⧸ Xm)) := by
    change Subgroup.zpowers ebar ⊔ Wbar ≤ _
    exact sup_le (Subgroup.zpowers_le.mpr hebarN) Subgroup.le_normalizer
  have hWnorm : (Wm.subgroupOf Zm).Normal := by
    have : (Wbar.subgroupOf Zbar).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : Wbar ≤ Zbar)).mpr
        hWbar_normal
    let ψ : Zm →* Zbar := (q.comp Zm.subtype).codRestrict Zbar fun z => z.2
    have hEq : (Wbar.subgroupOf Zbar).comap ψ = Wm.subgroupOf Zm := by
      ext x
      change q (x : ↥M) ∈ Wbar ↔ q (x : ↥M) ∈ Wbar
      exact Iff.rfl
    rw [← hEq]
    exact Subgroup.Normal.comap inferInstance ψ
  have hUnorm : (Xm.subgroupOf Zm).Normal := Subgroup.normal_subgroupOf
  have hZbar_card : Nat.card Zbar = p * Nat.card Wbar := by
    have hHnorm : Subgroup.zpowers ebar ≤
        Subgroup.normalizer (Wbar : Set (↥M ⧸ Xm)) := Subgroup.zpowers_le.mpr hebarN
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Subgroup.zpowers ebar) (K := Wbar) hHnorm
    have hinf : Subgroup.zpowers ebar ⊓ Wbar = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      by_contra hx1
      have hxbar : ebar ∈ Wbar := by
        have hcyc : Subgroup.zpowers x = Subgroup.zpowers ebar :=
          TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp
            (by simpa [hebarord] using pow_orderOf_eq_one ebar) hx1 hx.1
        exact (Subgroup.zpowers_le.mpr hx.2) (by rw [hcyc]; exact Subgroup.mem_zpowers ebar)
      exact hebarπ (by
        have := hQbar.le hxbar
        exact MonoidHom.mem_ker.mp this)
    rw [show Subgroup.zpowers ebar ⊔ Wbar = Zbar from rfl, hinf, Subgroup.card_bot, mul_one,
      Nat.card_zpowers, hebarord] at h
    exact h
  have hZm_card : Nat.card Zm = Nat.card Xm * Nat.card Zbar :=
    QuotientGroup.card_preimage_mk Xm (Zbar : Set (↥M ⧸ Xm))
  have hWm_card : Nat.card Wm = Nat.card Xm * Nat.card Wbar :=
    QuotientGroup.card_preimage_mk Xm (Wbar : Set (↥M ⧸ Xm))
  have hidx : Wm.relIndex Zm = p := by
    have h := Subgroup.relIndex_mul_card Wm Zm
    rw [inf_eq_left.mpr hWmZ] at h
    rw [hZm_card, hWm_card, hZbar_card] at h
    have hpos : 0 < Nat.card Xm * Nat.card Wbar := Nat.mul_pos Nat.card_pos Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h]
    ring
  have h2 : ∀ w ∈ Wm, ∃ k : ℕ, w ^ (2 ^ k) ∈ Xm := by
    intro w hw
    have hWbarP : IsPGroup 2 Wbar := hTNm.isPGroup.map q
    obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hWbarP ⟨q w, hw⟩
    refine ⟨k, ?_⟩
    have hq1 : q (w ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    exact (QuotientGroup.eq_one_iff (N := Xm) _).mp hq1
  have hTX : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ X) X :=
    hT.inf_of_le_normalizer hXM hMX
  have hR0 : CFSG.ABGLocalTools.IsSylowOf 2 ((T ⊓ X).subgroupOf M) Xm := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨?_, ?_, ?_⟩
    · intro x hx
      exact (Subgroup.mem_subgroupOf.mp hx).2
    · exact hTX.isPGroup.comap_subtype
    · rw [Subgroup.relIndex_subgroupOf (H := T ⊓ X) (K := X) (L := M) hXM]
      exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hTX).2.2
  have hNUm : ¬ p ∣ Nat.card ↥(Xm ⊓ Subgroup.normalizer
      (((T ⊓ X).subgroupOf M) : Set ↥M)) := by
    have hEq : Xm ⊓ Subgroup.normalizer (((T ⊓ X).subgroupOf M) : Set ↥M)
        = (X ⊓ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G)).subgroupOf M := by
      rw [CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer
        M (T ⊓ X) (inf_le_left.trans hT.le)]
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨hxX, -, hxN⟩
        exact ⟨hxX, hxN⟩
      · rintro ⟨hxX, hxN⟩
        exact ⟨hxX, hXM hxX, hxN⟩
    rw [hEq]
    have hcard : Nat.card ↥((X ⊓ Subgroup.normalizer
          ((T ⊓ X : Subgroup G) : Set G)).subgroupOf M)
        = Nat.card ↥(X ⊓ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans inf_le_left hXM)).toEquiv
    rw [hcard]
    exact hpK
  obtain ⟨R, hR, b, hbZ, hbW, hbord, hbR⟩ :=
    CFSG.GroupTheory.exists_orderOf_eq_prime_mem_normalizer_sylow_of_relIndex
      (G := ↥M) hp hp2 hUWm hWmZ hWnorm hUnorm hidx h2 hR0 hNUm
  have hQ0W : CFSG.ABGLocalTools.IsSylowOf 2 Q0 Wm := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) M).mp ?_
    have hmapQ : Q0.map M.subtype = T ⊓ N :=
      Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hT.le)
    have hmapW : Wm.map M.subtype = (T ⊓ N) ⊔ X := by
      rw [hWm_eq, Subgroup.map_sup, hmapQ, Subgroup.map_subgroupOf_eq_of_le hXM]
    rw [hmapQ, hmapW]
    exact CFSG.ABGLocalTools.IsSylowOf.of_le hTN le_sup_left
      (sup_le inf_le_right (le_sup_left : X ≤ X ⊔ C))
  obtain ⟨k, hkW, hconj⟩ := hR.exists_mem_conj hQ0W
  have hy_norm : (k * b * k⁻¹) ∈
      Subgroup.normalizer ((Q0 : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxR : k⁻¹ * x * k ∈ R := (hconj x).mp hx
      have hb : b * (k⁻¹ * x * k) * b⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp hbR (k⁻¹ * x * k)).mp hxR
      have hz : k⁻¹ * ((k * b * k⁻¹) * x * (k * b * k⁻¹)⁻¹) * k =
          b * (k⁻¹ * x * k) * b⁻¹ := by group
      rw [show (k * b * k⁻¹) * x * (k * b * k⁻¹)⁻¹ ∈ Q0 ↔
        k⁻¹ * ((k * b * k⁻¹) * x * (k * b * k⁻¹)⁻¹) * k ∈ R from hconj _]
      rw [hz]
      exact hb
    · intro hx
      have hxR : b * (k⁻¹ * x * k) * b⁻¹ ∈ R := by
        have hz : k⁻¹ * ((k * b * k⁻¹) * x * (k * b * k⁻¹)⁻¹) * k =
            b * (k⁻¹ * x * k) * b⁻¹ := by group
        rw [← hz]
        exact (hconj _).mp hx
      have hxR' : k⁻¹ * x * k ∈ R :=
        (Subgroup.mem_normalizer_iff.mp hbR (k⁻¹ * x * k)).mpr hxR
      exact (hconj x).mpr hxR'
  have hWbar_le_ker : Wbar ≤ π.ker := hQbar.le
  have hZbar_inf : Zbar ⊓ π.ker = Wbar := by
    have hWle : Wbar ≤ Zbar ⊓ π.ker := le_inf le_sup_right hWbar_le_ker
    have hle : Zbar ⊓ π.ker ≤ Zbar := inf_le_left
    have hrel := Subgroup.relIndex_mul_relIndex Wbar (Zbar ⊓ π.ker) Zbar hWle hle
    have hrelp : Wbar.relIndex Zbar = p := by
      have h := Subgroup.relIndex_mul_card Wbar Zbar
      rw [inf_eq_left.mpr (le_sup_right : Wbar ≤ Zbar)] at h
      have hpos : 0 < Nat.card Wbar := Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [← hZbar_card]
      exact h
    have hne1 : (Zbar ⊓ π.ker).relIndex Zbar ≠ 1 := by
      intro h1
      have htop : Zbar ≤ Zbar ⊓ π.ker := Subgroup.relIndex_eq_one.mp h1
      have hebarZ : ebar ∈ Zbar := Subgroup.mem_sup_left (Subgroup.mem_zpowers ebar)
      exact hebarπ (MonoidHom.mem_ker.mp (htop hebarZ).2)
    have hdvd : (Zbar ⊓ π.ker).relIndex Zbar ∣ Wbar.relIndex Zbar := by
      rw [← hrel]
      exact dvd_mul_left _ _
    have hval : (Zbar ⊓ π.ker).relIndex Zbar = p := by
      rw [hrelp] at hdvd
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hone : Wbar.relIndex (Zbar ⊓ π.ker) = 1 := by
      have h2 : Wbar.relIndex (Zbar ⊓ π.ker) * (Zbar ⊓ π.ker).relIndex Zbar =
          Wbar.relIndex Zbar := hrel
      rw [hrelp, hval] at h2
      refine Nat.eq_of_mul_eq_mul_right hp.pos ?_
      calc Wbar.relIndex (Zbar ⊓ π.ker) * p = p := h2
        _ = 1 * p := by rw [one_mul]
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hWle
  have hb_notNm : b ∉ Nm := by
    intro hbN
    have hqb_ker : q b ∈ π.ker := by
      rw [hkerπ]
      exact Subgroup.mem_map_of_mem q hbN
    have hqb_W : q b ∈ Wbar := by
      have : q b ∈ Zbar ⊓ π.ker := ⟨hbZ, hqb_ker⟩
      rwa [hZbar_inf] at this
    exact hbW hqb_W
  have hy_notNm : k * b * k⁻¹ ∉ Nm := by
    intro hy
    apply hb_notNm
    have hkNm : k ∈ Nm := hWm_le_Nm hkW
    have hbeq : b = k⁻¹ * (k * b * k⁻¹) * k := by group
    rw [hbeq]
    exact Nm.mul_mem (Nm.mul_mem (Nm.inv_mem hkNm) hy) hkNm
  have hyord : orderOf (k * b * k⁻¹ : ↥M) = p := by
    have h := MulEquiv.orderOf_eq (MulAut.conj k) b
    simpa [MulAut.conj_apply] using h.trans hbord
  have hyTN_G : ((k * b * k⁻¹ : ↥M) : G) ∈
      Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) := by
    have h := CFSG.GroupTheory.WielandtProduct.mem_normalizer_map_subtype hy_norm
    simpa [Q0, Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hT.le)] using h
  refine ⟨((k * b * k⁻¹ : ↥M) : G), (k * b * k⁻¹).2, ?_, ?_, ?_⟩
  · intro hN
    exact hy_notNm (Subgroup.mem_subgroupOf.mpr hN)
  · exact (orderOf_injective M.subtype M.subtype_injective (k * b * k⁻¹)).trans hyord
  · simpa [N] using hyTN_G

end CFSG.GroupTheory
