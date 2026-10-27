module

public import CFSG.ClassicalGroups.Symplectic.OddCentralizerSylow
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.QuasithinUnique
open CFSG.ClassicalGroups.Symplectic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem odd_centralizer_centralizes_of_component_sp_card_four
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 3 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2) (hQ4 : Q.card = 4)
    (hv : (TauCeti.LieTypeIndex.B m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {U : Subgroup L} (hU2 : IsPGroup 2 U) (hUmax : IsSylowTwoOf U ⊤)
    {x : L} (hxodd : Odd (orderOf x)) (hxc : x ∈ Subgroup.centralizer (U : Set L)) :
    ∀ l : L, x * l = l * x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 2
  have hFcard : Nat.card F = Q.card := by
    change Nat.card (GaloisField 2 2) = Q.card
    rw [GaloisField.card (p := 2) (n := 2) (by norm_num), hQ4]
    norm_num
  obtain ⟨eB⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj
    (r := m) (q := Q) hv hQ hm (k := F) hFcard
  let φ : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp m F) := e.trans eB.symm
  have hUindex : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hUmax.2.2
  let S : Sylow 2 L := hU2.toSylow hUindex
  have hScoe : (S : Subgroup L) = U := IsPGroup.toSylow_coe hU2 hUindex
  let q : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  let W : Sylow 2 (L ⧸ Subgroup.center L) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L)) S
  have hWcoe : (W : Subgroup (L ⧸ Subgroup.center L)) = U.map q := by
    rw [Sylow.coe_mapSurjective, hScoe]
  have hxq_central : q x ∈ Subgroup.centralizer
      ((W : Subgroup (L ⧸ Subgroup.center L)) : Set (L ⧸ Subgroup.center L)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hWcoe] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rw [← map_mul, ← map_mul]
    exact congrArg q ((Subgroup.mem_centralizer_iff.mp hxc) u hu)
  let V : Sylow 2 (StatedProj (StatedSp m F)) :=
    Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective W
  have hVcoe : (V : Subgroup (StatedProj (StatedSp m F))) = W.map φ := rfl
  let y : StatedProj (StatedSp m F) := φ (q x)
  have hy_central : y ∈ Subgroup.centralizer
      ((V : Subgroup (StatedProj (StatedSp m F))) :
        Set (StatedProj (StatedSp m F))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hVcoe] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hWcoe] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    calc φ (q u) * y = φ (q u * q x) := (map_mul φ _ _).symm
      _ = φ (q (u * x)) := by
        rw [show q u * q x = q (u * x) from map_mul q u x]
      _ = φ (q (x * u)) := by
        rw [(Subgroup.mem_centralizer_iff.mp hxc) u hu]
      _ = φ (q x * q u) := by
        rw [show q x * q u = q (x * u) from map_mul q x u]
      _ = y * φ (q u) := map_mul φ _ _
  have hyodd : Odd (orderOf y) := by
    rw [MulEquiv.orderOf_eq]
    exact Odd.of_dvd_nat hxodd (orderOf_map_dvd q x)
  haveI : NeZero m := ⟨by omega⟩
  have hproj_bij : Function.Bijective
      (proj m F) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := m) (K := F)
  let xhat : StatedSp m F :=
    (MulEquiv.ofBijective
      (proj m F) hproj_bij).symm y
  have hxhat : proj m F xhat = y :=
    (MulEquiv.ofBijective
      (proj m F) hproj_bij).apply_symm_apply y
  let Vhat : Sylow 2 (StatedSp m F) :=
    V.comapOfInjective (proj m F) hproj_bij.1
      (by rw [MonoidHom.range_eq_top_of_surjective (proj m F) hproj_bij.2]; exact le_top)
  have hxhat_odd : Odd (orderOf xhat) := by
    rw [← orderOf_injective
      (proj m F) hproj_bij.1 xhat, hxhat]
    exact hyodd
  have hxhat_central : xhat ∈ Subgroup.centralizer
      ((Vhat : Subgroup (StatedSp m F)) : Set (StatedSp m F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzV : proj m F z ∈ V := by
      simpa [Vhat] using hz
    have hcomm : proj m F z * y =
        y * proj m F z :=
      (Subgroup.mem_centralizer_iff.mp hy_central) _ hzV
    apply hproj_bij.1
    calc proj m F (z * xhat)
        = proj m F z *
            proj m F xhat := map_mul _ _ _
      _ = proj m F z * y := by rw [hxhat]
      _ = y * proj m F z := hcomm
      _ = proj m F xhat *
            proj m F z := by rw [hxhat]
      _ = proj m F (xhat * z) :=
        (map_mul _ _ _).symm
  have hxhat_center : xhat ∈ Subgroup.center (StatedSp m F) :=
    odd_centralizer_sylow_le_center_sp (F := F) hm Vhat hxhat_odd hxhat_central
  have hcenter : Subgroup.center (StatedSp m F) = ⊥ :=
    center_statedSp_eq_bot_of_charP_two (m := m) (F := F) (by omega)
  rw [hcenter] at hxhat_center
  have hxhat_one : xhat = 1 := Subgroup.mem_bot.mp hxhat_center
  have hy_one : y = 1 := by
    rw [← hxhat, hxhat_one, map_one]
  have hqx_one : q x = 1 := by
    apply φ.injective
    rw [map_one]
    exact hy_one
  have hxZ : x ∈ Subgroup.center L := (QuotientGroup.eq_one_iff x).mp hqx_one
  intro l
  exact (Subgroup.mem_center_iff.mp hxZ l).symm

end CFSG.LocalAnalysis.RankThreeUC.S15

end
