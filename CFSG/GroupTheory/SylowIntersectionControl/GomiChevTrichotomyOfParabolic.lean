module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicOfBorelTits
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTrichotomyLocal
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomNormalizer
import CFSG.GroupTheory.SylowIntersectionControl.RadicalHull
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools Subgroup

private def GomiChevSecond_ctp {G : Type} [Group G] (L X H : Subgroup G) : Prop :=
  ∃ I : Subgroup G, I ≠ ⊥ ∧ I ≤ L ∧ IsPGroup 2 I ∧
    pCoreOf 2 (L ⊓ normalizer (I : Set G)) = I ∧
    (∃ K : Subgroup G, H ≤ K ∧ K ≤ normalizer (H : Set G) ⊓ X ∧
      (K.subgroupOf (normalizer (H : Set G) ⊓ X)).IsSubnormal ∧ 2 ∣ H.relIndex K ∧
      K ≤ normalizer (I : Set G)) ∧
    Odd (normalizer (I : Set G)).index

private def GomiChevThird_ctp {G : Type} [Group G] (L H : Subgroup G) : Prop :=
  (IsGomiL3 (↥L ⧸ center ↥L) ∨ IsGomiSp4 (↥L ⧸ center ↥L)) ∧
    (∃ U : Subgroup G, IsSylowOf 2 U L ∧
      L ⊓ normalizer (U : Set G) < L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) ∧
    L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) < L ∧
    pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L ∧
    ∃ g : G, IsPGroup 2 (zpowers g) ∧ ∃ U : Subgroup G, IsSylowOf 2 U L ∧
      g ∈ normalizer (U : Set G) ∧ ∃ P : Subgroup G, L ⊓ normalizer (U : Set G) < P ∧ P < L ∧
        g ∉ normalizer (P : Set G)

private theorem odd_index_normalizer_of_sylow_le_ctp {G : Type} [Group G] [Finite G]
    {N : Subgroup G} (T : Sylow 2 G) (hTN : (T : Subgroup G) ≤ normalizer (N : Set G)) :
    Odd (normalizer (N : Set G)).index :=
  Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
    T.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hTN)))

private theorem normalizer_le_normalizer_inf_of_normal_ctp {G : Type} [Group G]
    {H L : Subgroup G} (hLn : L.Normal) :
    normalizer (H : Set G) ≤ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
  intro g hg
  exact Subgroup.inf_normalizer_le_normalizer_inf
    (Subgroup.mem_inf.mpr ⟨hg, by
      rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
      exact Subgroup.mem_top g⟩)

private theorem le_normalizer_inf_of_normal_ctp {G : Type} [Group G] {H L : Subgroup G}
    (hLn : L.Normal) : H ≤ normalizer ((H ⊓ L : Subgroup G) : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_inf_of_normal_ctp hLn)

private theorem exists_sylow_data_ctp {G : Type} [Group G] [Finite G] {L H I : Subgroup G}
    (hLn : L.Normal) (hL : IsGomiChevTwo ↥L) (hHp : IsPGroup 2 H)
    (hI : pCoreOf 2 (L ⊓ normalizer (I : Set G)) = I) (hIL : I ≤ L)
    (hIp : IsPGroup 2 I) (hHNI : H ≤ normalizer (I : Set G)) (hPar : GomiChevParabolic) :
    ∃ U : Subgroup G, IsSylowOf 2 U L ∧
      L ⊓ normalizer (U : Set G) ≤ L ⊓ normalizer (I : Set G) ∧
      H ≤ normalizer (U : Set G) ∧
      ∃ T : Sylow 2 G, U ⊔ H ≤ (T : Subgroup G) ∧ (T : Subgroup G) ⊓ L = U := by
  obtain ⟨U₀, hU₀, hU₀P⟩ := hPar G L I hL hIL hIp hI
  have hHL : H ≤ normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact le_top
  have hHNA : H ≤ normalizer (L ⊓ normalizer (I : Set G) : Set G) :=
    (le_inf hHL (hHNI.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨U, hU, hUP, hHU, hUP'⟩ :=
    exists_isSylowOf_le_normalizer (p := 2) (L := L) (P := L ⊓ normalizer (I : Set G))
      (U₀ := U₀) (H := H) inf_le_left hU₀ hU₀P hHp hHNA
  obtain ⟨T, hUT, hTL⟩ :=
    exists_sylow_sup_le_inf_eq (p := 2) (L := L) (U := U) (W := H) hLn hU hHp hHU
  exact ⟨U, hU, hUP', hHU, T, hUT, hTL⟩

private theorem not_le_of_isSylow_ctp {G : Type} [Group G] [Finite G] {H L U : Subgroup G}
    (hU : IsSylowOf 2 U L) (hIp : IsPGroup 2 ↥(H ⊓ L)) (T : Sylow 2 G)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hTnot : ¬ (T : Subgroup G) ≤ normalizer ((H ⊓ L : Subgroup G) : Set G)) : ¬ U ≤ H := by
  intro hUH
  have hUI : U ≤ H ⊓ L := le_inf hUH hU.le
  have hIU : H ⊓ L = U := IsSylowOf.eq_of_le hU hUI inf_le_right hIp
  exact hTnot (by rw [hIU]; exact hTU)

private theorem normalizer_lt_ctp {G : Type} [Group G] [Finite G] {L H I U : Subgroup G}
    (hL : IsGomiChevTwo ↥L)
    (hI : pCoreOf 2 (L ⊓ normalizer (I : Set G)) = I)
    (hU : IsSylowOf 2 U L)
    (hUP : L ⊓ normalizer (U : Set G) ≤ L ⊓ normalizer (I : Set G))
    (hUH : ¬ U ≤ H) (hIbot : I ≠ ⊥) (hIH : I ≤ H) (hIL : I ≤ L) (hIp : IsPGroup 2 I) :
    L ⊓ normalizer (U : Set G) < L ⊓ normalizer (I : Set G) ∧
      L ⊓ normalizer (I : Set G) < L := by
  constructor
  · refine lt_of_le_of_ne hUP ?_
    intro heq
    have hUle : U ≤ pCoreOf 2 (L ⊓ normalizer (U : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (le_inf hU.le Subgroup.le_normalizer) inf_le_right hU.isPGroup
    rw [heq, hI] at hUle
    exact hUH (hUle.trans hIH)
  · refine lt_of_le_of_ne inf_le_left ?_
    intro hAeq
    have hLle : L ≤ normalizer (I : Set G) := by
      intro x hx
      have hx' : x ∈ L ⊓ normalizer (I : Set G) := hAeq.symm ▸ hx
      exact hx'.2
    have hIn : (I.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hIL).mpr hLle
    have hIpsub : IsPGroup 2 (I.subgroupOf L) := hIp.comap_subtype
    have hle := CFSG.LieType.BorelTits.le_pCore 2 hIn hIpsub
    rw [hL.2.1] at hle
    have hbot : I.subgroupOf L = ⊥ := le_bot_iff.mp hle
    have hIbot' : I = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hIL, hbot, Subgroup.map_bot]
    exact hIbot hIbot'

private theorem second_disjunct_ctp {G : Type} [Group G] [Finite G] {L X H : Subgroup G}
    (hLn : L.Normal) (hHp : IsPGroup 2 H) (hHX : H ≤ X)
    (hIso : IsPIsolatedOver 2 (normalizer (H : Set G) ⊓ X) H)
    (hI : pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L)
    (hIbot : H ⊓ L ≠ ⊥) (hIp : IsPGroup 2 ↥(H ⊓ L))
    (T : Sylow 2 G) (hTNI : (T : Subgroup G) ≤ normalizer ((H ⊓ L : Subgroup G) : Set G)) :
    GomiChevSecond_ctp L X H := by
  have hKle : normalizer (H : Set G) ⊓ X ≤ normalizer ((H ⊓ L : Subgroup G) : Set G) :=
    inf_le_left.trans (normalizer_le_normalizer_inf_of_normal_ctp hLn)
  have hHK : H ≤ normalizer (H : Set G) ⊓ X := le_inf Subgroup.le_normalizer hHX
  refine ⟨H ⊓ L, hIbot, inf_le_right, hIp, hI, ⟨normalizer (H : Set G) ⊓ X, hHK, le_rfl, ?_, ?_,
    hKle⟩, odd_index_normalizer_of_sylow_le_ctp T hTNI⟩
  · rw [Subgroup.subgroupOf_self]
    exact Subgroup.IsSubnormal.top
  · exact IsPIsolatedOver.dvd_relIndex hIso hHp hHK inf_le_left

private theorem third_disjunct_ctp {G : Type} [Group G] [Finite G] {L H U : Subgroup G}
    {t : G} (hSwap : GomiChevSwap) (hL : IsGomiChevTwo ↥L) (hU : IsSylowOf 2 U L)
    (hAtom : IsGomiAtom L U (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)))
    (htL : t ∈ normalizer (L : Set G)) (htU : t ∈ normalizer (U : Set G))
    (hAt : (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)).map (MulAut.conj t).toMonoidHom ≠
      L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G))
    (hNL : (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) ⊔
      (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)).map (MulAut.conj t).toMonoidHom = L)
    (hzp : IsPGroup 2 (Subgroup.zpowers t))
    (hNUI : L ⊓ normalizer (U : Set G) < L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G))
    (hAL : L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) < L)
    (hcore : pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L)
    (hnotA : t ∉ normalizer (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) : Set G)) :
    GomiChevThird_ctp L H :=
  ⟨hSwap G L U _ hL hU hAtom t (Subgroup.mem_inf.mpr ⟨htL, htU⟩) hAt hNL,
    ⟨U, hU, hNUI⟩, hAL, hcore, t, hzp, U, hU, htU, _, hNUI, hAL, hnotA⟩

private theorem radical_disjunct_ctp {G : Type} [Group G] [Finite G] {L X H U N : Subgroup G}
    (hRad : GomiChevRadical) (hLn : L.Normal) (hL : IsGomiChevTwo ↥L) (hLX : L ≤ X)
    (hHX : H ≤ X) (hU : IsSylowOf 2 U L)
    (hev : 2 ∣ H.relIndex (L ⊓ normalizer (H : Set G)))
    (T : Sylow 2 G) (hHT : H ≤ (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTN : (T : Subgroup G) ≤ normalizer (N : Set G))
    (hNL : N ≤ L) (hNne : N ≠ L) (hUPN : L ⊓ normalizer (U : Set G) ≤ N)
    (hAN : L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) ≤ N) :
    GomiChevSecond_ctp L X H := by
  have hpCore_ne : pCoreOf 2 N ≠ ⊥ :=
    (hRad G L U N hL hU hUPN (lt_of_le_of_ne hNL hNne)).1
  obtain ⟨J, hXJ, hJL, hJcore, hTJ, hNXJ⟩ :=
    exists_pCoreOf_inf_normalizer_eq (p := 2) (L := L) (A := (T : Subgroup G))
      (X := pCoreOf 2 N) hTL ((CFSG.LieType.BorelTits.pCoreOf_le 2 N).trans hNL)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
      (hTN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N))
  have hJne : J ≠ ⊥ := fun hJ => hpCore_ne (le_bot_iff.mp (hJ ▸ hXJ))
  have hJp : IsPGroup 2 J := hJcore ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hNLH_le_A : L ⊓ normalizer (H : Set G) ≤
      L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) :=
    le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_inf_of_normal_ctp hLn))
  have hNLH_le_inf : L ⊓ normalizer (H : Set G) ≤ L ⊓ normalizer (pCoreOf 2 N : Set G) :=
    le_inf inf_le_left (hNLH_le_A.trans (hAN.trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)))
  have hNLH_le_NJ : L ⊓ normalizer (H : Set G) ≤ normalizer (J : Set G) :=
    hNLH_le_inf.trans hNXJ
  obtain ⟨K, hHK, hKle, hKsn, hKdvd, hKNJ⟩ :=
    exists_le_of_inf_normalizer_le (p := 2) hLn hLX hHX hev hNLH_le_NJ (hHT.trans hTJ)
  exact ⟨J, hJne, hJL, hJp, hJcore, ⟨K, hHK, hKle, hKsn, hKdvd, hKNJ⟩,
    odd_index_normalizer_of_sylow_le_ctp T hTJ⟩

private theorem step_five_atom_ctp {G : Type} [Group G] [Finite G] {L X H U : Subgroup G}
    (hOrb : GomiChevAtomOrbit) (hRad : GomiChevRadical) (hSwap : GomiChevSwap)
    (hLn : L.Normal) (hL : IsGomiChevTwo ↥L) (hLX : L ≤ X) (hHX : H ≤ X)
    (hI : pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L)
    (hev : 2 ∣ H.relIndex (L ⊓ normalizer (H : Set G)))
    (hU : IsSylowOf 2 U L)
    (hUP : L ⊓ normalizer (U : Set G) ≤
      L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G))
    (hNUI : L ⊓ normalizer (U : Set G) <
      L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G))
    (hAL : L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) < L)
    (T : Sylow 2 G) (hHT : H ≤ (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hTnot : ¬ (T : Subgroup G) ≤ normalizer ((H ⊓ L : Subgroup G) : Set G))
    (hAtom : IsGomiAtom L U (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G))) :
    GomiChevSecond_ctp L X H ∨ GomiChevThird_ctp L H := by
  let A : Subgroup G := L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)
  have hT2 : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  have hNA_le : normalizer (A : Set G) ≤ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    change normalizer (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) : Set G) ≤
      normalizer ((H ⊓ L : Subgroup G) : Set G)
    exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _).trans
      (le_of_eq (congrArg (fun J : Subgroup G => Subgroup.normalizer (J : Set G)) hI))
  have hTNA : ¬ (T : Subgroup G) ≤ normalizer (A : Set G) :=
    fun hle => hTnot (hle.trans hNA_le)
  obtain ⟨t, ht, hAt⟩ : ∃ t ∈ (T : Subgroup G),
      A.map (MulAut.conj t).toMonoidHom ≠ A := by
    by_contra hcon
    push Not at hcon
    exact hTNA fun x hx => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hcon x hx)
  have hNsubL : A ⊔ A.map (MulAut.conj t).toMonoidHom ≤ L := by
    refine sup_le inf_le_left ?_
    calc A.map (MulAut.conj t).toMonoidHom ≤ L.map (MulAut.conj t).toMonoidHom :=
          Subgroup.map_mono inf_le_left
      _ = L := Subgroup.Normal.map_conj_eq L t
  have hNsubN : (T : Subgroup G) ≤
      normalizer (A ⊔ A.map (MulAut.conj t).toMonoidHom : Subgroup G) :=
    le_normalizer_sup_map_conj hOrb hL hU hT2 hTL hTU hAtom ht hAt
  have hAN : A ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom := le_sup_left
  by_cases hNL : A ⊔ A.map (MulAut.conj t).toMonoidHom = L
  · refine Or.inr (third_disjunct_ctp (U := U) (t := t) hSwap hL hU hAtom (hTL ht) (hTU ht)
      hAt hNL (hT2.to_le (Subgroup.zpowers_le.mpr ht)) hNUI hAL hI ?_)
    intro hmem
    exact hAt (Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem)
  · refine Or.inl (radical_disjunct_ctp (U := U) (N := A ⊔ A.map (MulAut.conj t).toMonoidHom)
      hRad hLn hL hLX hHX hU hev T hHT hTL hNsubN hNsubL hNL (hUP.trans le_sup_left) hAN)

private theorem step_five_move_ctp {G : Type} [Group G] [Finite G] {L X H U : Subgroup G}
    (hGen : GomiChevAtomGeneration) (hOrb : GomiChevAtomOrbit)
    (hLn : L.Normal) (hL : IsGomiChevTwo ↥L)
    (hI : pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L)
    (hU : IsSylowOf 2 U L)
    (hUP : L ⊓ normalizer (U : Set G) ≤
      L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G))
    (hHL : H ≤ normalizer (L : Set G))
    (T : Sylow 2 G) (hHT : H ≤ (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hTnot : ¬ (T : Subgroup G) ≤ normalizer ((H ⊓ L : Subgroup G) : Set G))
    (hmove : ∀ A : Subgroup G, IsGomiAtom L U A →
      A ≤ L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) →
        ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≠ A) :
    GomiChevSecond_ctp L X H ∨ GomiChevThird_ctp L H := by
  let A : Subgroup G := L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)
  have hT2 : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  have hHP : H ≤ normalizer (A : Set G) := by
    change H ≤ normalizer (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) : Set G)
    exact (le_inf hHL ((le_normalizer_inf_of_normal_ctp hLn).trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTNA : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    le_normalizer_of_forall_isGomiAtom (P := A) hGen hOrb hL hU hT2 hTL hTU hHT hHP
      (by simpa [A] using hUP) inf_le_left hmove
  have hNA_le : normalizer (A : Set G) ≤ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    change normalizer (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) : Set G) ≤
      normalizer ((H ⊓ L : Subgroup G) : Set G)
    exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _).trans
      (le_of_eq (congrArg (fun J : Subgroup G => Subgroup.normalizer (J : Set G)) hI))
  exact (hTnot (hTNA.trans hNA_le)).elim

private theorem step_five_ctp {G : Type} [Group G] [Finite G] {L X H U : Subgroup G}
    (hGen : GomiChevAtomGeneration) (hOrb : GomiChevAtomOrbit)
    (hRad : GomiChevRadical) (hSwap : GomiChevSwap) (hLevi : GomiChevLevi)
    (hLn : L.Normal) (hL : IsGomiChevTwo ↥L) (hLX : L ≤ X)
    (hHp : IsPGroup 2 H) (hHX : H ≤ X)
    (hIso : IsPIsolatedOver 2 (normalizer (H : Set G) ⊓ X) H)
    (hI : pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L)
    (hIbot : H ⊓ L ≠ ⊥) (hIp : IsPGroup 2 ↥(H ⊓ L))
    (hU : IsSylowOf 2 U L)
    (hUP : L ⊓ normalizer (U : Set G) ≤
      L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G))
    (hHU : H ≤ normalizer (U : Set G))
    (T : Sylow 2 G) (hHT : H ≤ (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hTnot : ¬ (T : Subgroup G) ≤ normalizer ((H ⊓ L : Subgroup G) : Set G)) :
    GomiChevSecond_ctp L X H ∨ GomiChevThird_ctp L H := by
  let A : Subgroup G := L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)
  have hHU' : ¬ U ≤ H := not_le_of_isSylow_ctp hU hIp T hTU hTnot
  have hev : 2 ∣ H.relIndex (L ⊓ normalizer (H : Set G)) :=
    dvd_relIndex_inf_normalizer hHp hU.isPGroup hU.le hHU hHU'
  have hIsoH : IsPIsolatedOver 2 (L ⊓ normalizer (H : Set G)) (H ⊓ L) :=
    isPIsolatedOver_inf_normalizer hLn hLX hHp hHX hIso hev
  obtain ⟨hNUI, hAL⟩ :=
    normalizer_lt_ctp hL (by simpa [A] using hI) hU (by simpa [A] using hUP) hHU'
      hIbot (inf_le_left : H ⊓ L ≤ H) inf_le_right hIp
  have hHL : H ≤ normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact le_top
  rcases hLevi G L U H hL hU hHp hHL hHU (by simpa [A]) (by simpa [A] using hAL)
    (by simpa [A] using hI) hIsoH with hAtom | hmove
  · exact step_five_atom_ctp hOrb hRad hSwap hLn hL hLX hHX hI hev hU hUP hNUI hAL T hHT hTL
      hTU hTnot hAtom
  · exact step_five_move_ctp hGen hOrb hLn hL hI hU hUP hHL T hHT hTL hTU hTnot hmove

theorem gomiChevTrichotomy_of_parabolic (hBT : GomiChevBorelTits)
    (hGen : GomiChevAtomGeneration) (hOrb : GomiChevAtomOrbit) (hRad : GomiChevRadical)
    (hSwap : GomiChevSwap) (hLevi : GomiChevLevi) : GomiChevTrichotomy := by
  intro G _ _ L X H hLn hL hLX hH1 hHp hHX hIso
  let I : Subgroup G := H ⊓ L
  have hI : pCoreOf 2 (L ⊓ normalizer (I : Set G)) = I :=
    pCoreOf_inf_normalizer_inf_eq hLn hLX hHp hHX hIso
  have hIp : IsPGroup 2 I := hHp.to_le inf_le_left
  by_cases hIbot : I = ⊥
  · have hpL : 2 ∣ Nat.card L := by
      refine even_iff_two_dvd.mp (by_contra fun hodd => ?_)
      have hs : Group.IsSolvable ↥L :=
        CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
      have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
      have : Nontrivial ↥L := (QuotientGroup.mk_surjective (s := Subgroup.center ↥L)).nontrivial
      have : Group.IsPerfect ↥L := hL.1.1
      exact Group.IsPerfect.not_isSolvable ↥L hs
    exact Or.inl (isPIsolatedOver_inf_centralizer hLn hpL hLX hHp hHX hIso hIbot)
  · have hHNI : H ≤ normalizer (I : Set G) := le_normalizer_inf_of_normal_ctp hLn
    obtain ⟨U, hU, hUP, hHU, T, hUT, hTLU⟩ :=
      exists_sylow_data_ctp (I := I) hLn hL hHp hI inf_le_right hIp hHNI
        (gomiChevParabolic_of_borelTits hBT)
    have hHT : H ≤ (T : Subgroup G) := (le_sup_right : H ≤ U ⊔ H).trans hUT
    have hTL : (T : Subgroup G) ≤ normalizer (L : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
      exact le_top
    have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by
      have h : (T : Subgroup G) ≤ normalizer ((T : Subgroup G) ⊓ L : Subgroup G) :=
        (le_inf Subgroup.le_normalizer hTL).trans Subgroup.inf_normalizer_le_normalizer_inf
      rwa [hTLU] at h
    by_cases hTNI : (T : Subgroup G) ≤ normalizer (I : Set G)
    · exact Or.inr (Or.inl
        (second_disjunct_ctp hLn hHp hHX hIso hI hIbot hIp T hTNI))
    · exact Or.inr (step_five_ctp hGen hOrb hRad hSwap hLevi hLn hL hLX hHp hHX hIso hI hIbot
        hIp hU hUP hHU T hHT hTL hTU hTNI)

end CFSG.GroupTheory
