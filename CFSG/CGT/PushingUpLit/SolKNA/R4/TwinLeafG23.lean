module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafGLR
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocal2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafG23Shape
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Cent

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3 CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4

theorem card_comap_of_le_range {G Y : Type*} [Group G] [Group Y] (ι : G →* Y)
    (hι : Function.Injective ι) {H : Subgroup Y} (h : H ≤ ι.range) :
    Nat.card (H.comap ι) = Nat.card H := by
  rw [← Subgroup.card_map_of_injective hι (K := H.comap ι), Subgroup.map_comap_eq_self h]


theorem localG23_holds : LocalNoQ16Q16' fun F _ => LieModel F .G2 0 3 1 := by
  intro F _ hF Y _ _ N _ ⟨e⟩ hC t ht K K' hK hK' h2 h2' x hx y hy x' hx' y' hy' hxt hq
  have hm : LieModel ↥N .G2 0 3 1 := LieModel.of_mulEquiv e.symm hF
  have hO : Nobq.OutTwoCyclic ↥N :=
    outTwoCyclic_G2 (by decide)
      (Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide) (by decide))
  obtain ⟨D, Ō, M, hDC, hŌD, hMD, htM, hDn, -, hŌodd, hDŌ, hM2, hM64⟩ :=
    Q16Q16.local_reduction N hC hO hK hK' h2 h2' hx hy hx' hy' hq hxt
  have htN : t ∈ N := (Subgroup.mem_inf.1 (hDC (hMD htM))).1
  have htN' : orderOf (⟨t, htN⟩ : ↥N) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  obtain ⟨F', _, _, Sh, hc, hz⟩ :=
    GH74.GLS.IVK.GHInv.exists_shape_G2 Nat.prime_three (by decide) hm _ htN'
  have hF' : Nat.card F' = 3 := by rw [hc, pow_one]
  set ι := Q3Sh.ι htN with hι_def
  have hι : Function.Injective ι := Q3Sh.ι_injective htN
  have hrange : ∀ c ∈ N ⊓ Subgroup.centralizer ({t} : Set Y), c ∈ ι.range := fun c hc =>
    Q3Sh.exists_ι htN hc
  have hDr : D ≤ ι.range := fun d hd => hrange d (hDC hd)
  have hŌr : Ō ≤ ι.range := hŌD.trans hDr
  have hMr : M ≤ ι.range := hMD.trans hDr
  refine Shape.false_of_normal_odd_two Sh hF' hF' (D := D.comap ι) (O := Ō.comap ι)
    (M := M.comap ι) ?_ ?_ ?_ (Subgroup.comap_mono hMD) ?_ ?_
  · intro c d hd
    rw [Subgroup.mem_comap] at hd ⊢
    rw [map_mul, map_mul, map_inv]
    exact hDn _ (Q3Sh.ι_mem htN c) _ hd
  · rw [card_comap_of_le_range ι hι hŌr]
    exact hŌodd
  · intro g hg
    obtain ⟨k, hk⟩ := hDŌ (ι g) (Subgroup.mem_comap.1 hg)
    exact ⟨k, Subgroup.mem_comap.2 (by rw [map_pow]; exact hk)⟩
  · obtain ⟨m, hm⟩ := hM2.exists_card_eq
    exact IsPGroup.of_card (n := m) (by rw [card_comap_of_le_range ι hι hMr, hm])
  · rw [card_comap_of_le_range ι hι hMr]
    exact hM64

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
