module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3CompBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_eq_of_mem_cComp {S K B H : Subgroup G}
    (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (hSH : S ≤ H) (hK : K ∈ cComp H)
    (hB : B ∈ cComp H) (hBK : B ≤ conjJoin S K) :
    ∃ t ∈ S, B = K.map (MulAut.conj t).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  have hBH : B ≤ H := le_of_mem_cComp hB
  have hKt : ∀ t : S, K.map (MulAut.conj (t : G)).toMonoidHom ∈ cComp H := fun t =>
    map_conj_mem_cComp hK (hSH t.2)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hcomm : ∀ t : S,
      ⁅modO2Image H B, modO2Image H (K.map (MulAut.conj (t : G)).toMonoidHom)⁆ = ⊥ :=
    fun t => h37 _ (modO2Image_mem_cComp hB) _ (modO2Image_mem_cComp (hKt t))
      (fun heq => hne t t.2 ((modO2Image_injOn H) hB (hKt t) heq))
  set P : Subgroup ↥H :=
    (Subgroup.centralizer ((modO2Image H B : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap π with hP
  have hKtP : ∀ t : S, K.map (MulAut.conj (t : G)).toMonoidHom ≤ P.map H.subtype := by
    intro t y hy
    have hyH : y ∈ H := le_of_mem_cComp (hKt t) hy
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    show (⟨y, hyH⟩ : ↥H) ∈ P
    rw [hP, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro b hb
    have hk : π ⟨y, hyH⟩ ∈ modO2Image H (K.map (MulAut.conj (t : G)).toMonoidHom) :=
      ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have h1 : ⁅b, π ⟨y, hyH⟩⁆ ∈ ⁅modO2Image H B,
        modO2Image H (K.map (MulAut.conj (t : G)).toMonoidHom)⁆ :=
      Subgroup.commutator_mem_commutator hb hk
    rw [hcomm t, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hK₀P : conjJoin S K ≤ P.map H.subtype := iSup_le fun t => hKtP t
  have hBP : B ≤ P.map H.subtype := hBK.trans hK₀P
  have hcommBB : ∀ (b : G) (hb : b ∈ B) (b' : G) (hb' : b' ∈ B),
      ⁅(⟨b, hBH hb⟩ : ↥H), (⟨b', hBH hb'⟩ : ↥H)⁆ ∈ CFSG.pCore 2 ↥H := by
    intro b hb b' hb'
    obtain ⟨x, hxP, hxb⟩ := hBP hb
    have hx : x = ⟨b, hBH hb⟩ := Subtype.ext hxb
    have hxP' : x ∈ P := hxP
    rw [hP, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hxP'
    have hb'bar : π ⟨b', hBH hb'⟩ ∈ modO2Image H B :=
      ⟨⟨b', hBH hb'⟩, Subgroup.mem_subgroupOf.mpr hb', rfl⟩
    have h1 := hxP' _ hb'bar
    rw [hx] at h1
    have h2 : π ⁅(⟨b, hBH hb⟩ : ↥H), (⟨b', hBH hb'⟩ : ↥H)⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h1.symm
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hBle : B ≤ pCoreOf 2 H := by
    calc B = ⁅B, B⁆ := (perfect_of_mem_cComp hB).symm
      _ ≤ pCoreOf 2 H := by
        refine Subgroup.commutator_le.mpr fun b hb b' hb' => ?_
        have h1 := (mem_pCore_iff_mem_pCoreOf
          (⁅(⟨b, hBH hb⟩ : ↥H), (⟨b', hBH hb'⟩ : ↥H)⁆)).mp (hcommBB b hb b' hb')
        simpa [commutatorElement_def] using h1
  have hBp : IsPGroup 2 B := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le hBle
  have hnil : Group.IsNilpotent ↥B := hBp.isNilpotent
  exact not_isSolvable_of_mem_cComp hB inferInstance

theorem compChi0Block_of (h238 : Lemma2_3_8_4) (h37 : Vol2Native.A37ForSQTKCat) :
    CompChi0Block := by
  intro G _ _ T M H₁ K h hH hc hK hKM
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf (H₁ ⊓ M)
  obtain ⟨hSH, -, -⟩ := IsGamma.sylow_properties h hH.isGamma hS
  have hS2 : IsPGroup 2 S := hSH.2.1
  have hSH₁ : S ≤ H₁ := hSH.1
  have hKH : K ≤ H₁ := le_of_mem_cComp hK
  have hK₀H : conjJoin S K ≤ H₁ := conjJoin_le_of_le hSH₁ hKH
  have hSN : S ≤ Subgroup.normalizer (conjJoin S K : Set G) := le_normalizer_conjJoin' S K
  have hKK₀ : K ≤ conjJoin S K := le_conjJoin S K
  have hK₀perf : ⁅conjJoin S K, conjJoin S K⁆ = conjJoin S K :=
    perfect_conjJoin (perfect_of_mem_cComp hK)
  have hK₀sub : IsSubnormal (conjJoin S K) H₁ := isSubnormal_conjJoin hSH₁ hK
  have hXH : conjJoin S K ⊔ S ≤ H₁ := sup_le hK₀H hSH₁
  have hXc : CharTwo (conjJoin S K ⊔ S) := C1GN.charTwo_of_le hc hSH le_sup_right hXH
  have hXM : ¬ conjJoin S K ⊔ S ≤ M := fun hle => hKM ((hKK₀.trans le_sup_left).trans hle)
  obtain ⟨hX0, -, hSXM⟩ :=
    Vol2Native.L239.IsGamma0.exists_of_charTwo_not_le h hH hS le_sup_right hXc hXM
  have hXSQ : CFSG.SectionRank.IsSQTKCat ↥(conjJoin S K ⊔ S) := h.qtke.1 _ hX0.isGamma.1
  have hQ : Vol2Native.SQTKHypCat (↥(conjJoin S K ⊔ S) ⧸ CFSG.pCore 2 ↥(conjJoin S K ⊔ S)) :=
    Vol2Native.SQTKHypCat.quotient_pCore _ hXSQ
  have h37X := h37 _ hQ
  have hX3 := L238.rank_le_of_isSQTKCat hXSQ Nat.prime_three (by norm_num)
  have hrk := L238.rank_quotient_le_of_isSQTKCat hXSQ 3 Nat.prime_three (by norm_num)
  obtain ⟨-, s, L, hs1, -, hL, hjoin⟩ := h238 G T M (conjJoin S K ⊔ S) S h hX0 hXc hSXM
  have hLK : ∀ i, IsChi0Block (conjJoin S K) (L i) := fun i =>
    Vol2Native.L239.isChi0Block_of_isChi0Block_sup hS2 hSN (hL i).1
  by_cases hnon : ∃ i, ¬ IsAltType (L i) 3
  ·
    obtain ⟨i, hi3⟩ := hnon
    have hBK : IsChi0Block (conjJoin S K) (L i) := hLK i
    have hty : (∃ n : ℕ, 1 < n ∧ IsLin2Type (L i) n) ∨ IsAltType (L i) 5 := by
      rcases hBK.2 with h1 | h3 | h5
      · exact Or.inl h1
      · exact absurd h3 hi3
      · exact Or.inr h5
    have hBc : L i ∈ cComp (conjJoin S K) := L238.mem_cComp_of_isChi0Block_nonsolvable hBK.1 hty
    have hBH : L i ∈ cComp H₁ := cComp_mem_of_subnormal hK₀sub hBc
    have hQH : Vol2Native.SQTKHypCat (↥H₁ ⧸ CFSG.pCore 2 ↥H₁) :=
      Vol2Native.SQTKHypCat.quotient_pCore _ (h.qtke.1 H₁ hH.isGamma.1)
    obtain ⟨t, htS, hBt⟩ := exists_conj_eq_of_mem_cComp (h37 _ hQH) hSH₁ hK hBH hBK.1.2.1
    have hBblock : IsChi0Block H₁ (L i) := by
      refine ⟨⟨hBK.1.1, le_of_mem_cComp hBH, ?_⟩, hBK.2⟩
      exact (isSubnormal_iff_subgroupOf (le_of_mem_cComp hBH)).mp (subnormal_of_mem_cComp hBH)
    have hconj := isChi0Block_conj hBblock (H₁.inv_mem (hSH₁ htS))
    have hKeq : (L i).map (MulAut.conj t⁻¹).toMonoidHom = K := by
      rw [hBt, map_conj_map_conj, inv_mul_cancel, map_conj_one]
    rw [hKeq] at hconj
    exact hconj
  ·
    exfalso
    push Not at hnon
    have hZ : (⨆ i, L i) ≤ conjJoin S K ⊓ Subgroup.centralizer (conjJoin S K : Set G) := by
      refine iSup_le fun i => ?_
      have hchi : IsChiBlock (conjJoin S K ⊔ S) (L i) :=
        C1GN.isChiBlock_of_isChi0Block (hL i).1.1 (hL i).1
      exact le_center_of_isAltType_three hXc hX3 hrk h37X hchi (hnon i) (hLK i).1.2.1 le_sup_left
        hK₀perf
    have hXle : conjJoin S K ⊔ S ≤ (conjJoin S K ⊔ S) ⊓ M ⊔
        (conjJoin S K ⊓ Subgroup.centralizer (conjJoin S K : Set G)) := by
      calc conjJoin S K ⊔ S = (conjJoin S K ⊔ S) ⊓ M ⊔ ⨆ i, L i := hjoin
        _ ≤ _ := sup_le_sup_left hZ _
    have hDN : (conjJoin S K ⊔ S) ⊓ M ≤ Subgroup.normalizer
        ((conjJoin S K ⊓ Subgroup.centralizer (conjJoin S K : Set G) : Subgroup G) : Set G) :=
      le_normalizer_center (inf_le_left.trans (sup_le Subgroup.le_normalizer hSN))
    have hle := le_of_le_sup_center hK₀perf hDN (le_sup_left.trans hXle)
    exact hKM ((hKK₀.trans hle).trans inf_le_right)

end CFSG.QuasithinUnique.A5.G3
