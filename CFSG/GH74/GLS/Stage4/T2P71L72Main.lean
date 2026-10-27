module

public import CFSG.GH74.GLS.Stage4.T2P71L72Glue
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Red
public import CFSG.GH74.GLS.Stage4.T2P71L72Def47g
public import CFSG.GH74.GLS.Stage4.T2P71L72Cyc
public import CFSG.GH74.GLS.Stage4.T2P71L72Local

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L72

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

section Main


theorem p71L72Env_of_leaves (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hIVK : IVK_4_1_R_L3) (h94 : IVK_9_4_g4_G2three) (h47e : IVK_4_7e) (h47g : IVK_4_7g) :
    P71L72Env := by
  intro G _ _ Gs _ n N u h P hPC
  by_contra hnK
  obtain ⟨f, hf, hfo, hn3⟩ := exists_order_three h (P : Subgroup G) hPC P.isPGroup' hnK
  have hlt : Lt3 G n := lt3_of_sylow h P hPC
  have hcyc : IsCyclic ↥N.F := F_isCyclic hL hL3 hIVK h hlt hn3
  have hAbP : AbCyc ↥(P : Subgroup G) := abCyc_of_cent h hcyc (P : Subgroup G) hPC P.isPGroup'
  obtain ⟨m, hzC, hnm, hHyp⟩ := local_three hL hL3 hIVK h hlt hn3 hf hfo
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hStd : Std G := h.std
  have hfne : centralizer ({f} : Set G) ≠ ⊤ := by
    intro htop
    have hfc : f ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ centralizer ({f} : Set G) := by rw [htop]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    have hsimple : IsSimpleGroup G := hStd.kps.1
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
    · rw [h0] at hfc
      have h1 : f = 1 := Subgroup.mem_bot.1 hfc
      rw [h1, orderOf_one] at hfo
      omega
    · obtain ⟨b, c, hbc⟩ := hStd.kps.2.1
      apply hbc
      have := Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top c : c ∈ Subgroup.center G) b
      exact this
  have hKX : IsKGroupNative ↥(centralizer ({f} : Set G)) :=
    hStd.kps.isKGroupNative_of_ne_top hfne
  have hKH : IsKGroupNative
      (↥(centralizer ({f} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f} : Set G))) :=
    CFSG.SectionRank.IsKGroupCat.quotient hKX _
  have hO : pPrimeCore 2
      (↥(centralizer ({f} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f} : Set G))) = ⊥ :=
    pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥(centralizer ({f} : Set G))) (p := 2)
  have hGen4H : Gen4
      (↥(centralizer ({f} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f} : Set G))) :=
    Gen4.quotient _ (Gen4.subgroup _ hStd.gen4)
  have hrkH : CFSG.pRank 2
      (↥(centralizer ({f} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f} : Set G))) ≤ 3 :=
    pRank_two_centralizerBar_le f h.rank.le
  have hLie := h94 _ Gs _ m (Nat.one_le_iff_ne_zero.2 hm0) hGen4H hrkH ⟨hKH, hO, hHyp⟩
  set Hb := ↥(centralizer ({f} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f} : Set G)) with hHb
  have hY : ∀ T : Subgroup ↥(centralizer ({f} : Set G)), IsPGroup 3 ↥T → AbCyc ↥T := by
    intro T hT
    have hT' : IsPGroup 3 ↥(T.map (centralizer ({f} : Set G)).subtype) := hT.map _
    have h1 : AbCyc ↥(T.map (centralizer ({f} : Set G)).subtype) :=
      AbCyc.of_pSubgroup P hAbP _ hT'
    exact AbCyc.of_injective
      (Subgroup.equivMapOfInjective T _ (centralizer ({f} : Set G)).subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective T _ (centralizer ({f} : Set G)).subtype_injective).injective h1
  have hπ : Function.Surjective (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({f} : Set G)))) :=
    QuotientGroup.mk'_surjective _
  obtain ⟨P'⟩ : Nonempty (Sylow 3 ↥(layer Hb)) := inferInstance
  let V : Subgroup Hb := (P' : Subgroup ↥(layer Hb)).map (layer Hb).subtype
  have hVp : IsPGroup 3 ↥V := P'.isPGroup'.map _
  have hAbV : AbCyc ↥V := AbCyc.of_section _ hπ hY V hVp
  have hAbP' : AbCyc ↥(P' : Subgroup ↥(layer Hb)) :=
    AbCyc.of_injective
      (Subgroup.equivMapOfInjective (P' : Subgroup ↥(layer Hb)) (layer Hb).subtype
        (layer Hb).subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective (P' : Subgroup ↥(layer Hb)) (layer Hb).subtype
        (layer Hb).subtype_injective).injective hAbV
  obtain ⟨hΩ, -⟩ := h47e ↥(layer Hb) 3 m Nat.prime_three (by norm_num) (Or.inl hLie) P'
  obtain ⟨B, hBP, hBab, hBcard⟩ := exists_abelian_index_le_three (P' : Subgroup ↥(layer Hb)) hΩ hAbP'
  exact h47g ↥(layer Hb) m (Nat.one_le_iff_ne_zero.2 hm0) hLie P' B hBP hBab hBcard

theorem p71L72_of_leaves
    (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hIVK : IVK_4_1_R_L3) (h94 : IVK_9_4_g4_G2three) (h47e : IVK_4_7e) (h47g : IVK_4_7g) : P71L72 :=
  p71L72_of_env (p71L72Env_of_leaves hL hL3 hIVK h94 h47e h47g)

end Main

end CFSG.GH74.GLS.Stage4.Rest.L72
