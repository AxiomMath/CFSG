module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBaumMod
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
import CFSG.Adapters.GeneralizedFittingTop

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open CFSG.RankThree.PartTwo CFSG.AGLEmbeddingD2.GN
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open scoped commutatorElement

section Helpers

private theorem isComponentOf_conjSub_top {Y : Type*} [Group Y] {L : Subgroup Y}
    (hL : Open.IsComponentOf L ⊤) (t : Y) : Open.IsComponentOf (B6.conjSub t L) ⊤ :=
  (CFSG.Adapters.isComponentOf_top_iff _).2
    (CFSG.GorensteinWalter.fstar_isComponentOf_conjugateSubgroup_of_mem
      ((CFSG.Adapters.isComponentOf_top_iff L).1 hL) t (Subgroup.mem_top t))

private theorem conjSub_le_centralizer_of_not_mem_normalizer {Y : Type*} [Group Y] [Finite Y]
    {L : Subgroup Y} (hL : Open.IsComponentOf L ⊤) {t : Y}
    (ht : t ∉ Subgroup.normalizer (L : Set Y)) :
    B6.conjSub t L ≤ Subgroup.centralizer (L : Set Y) := by
  have hne : B6.conjSub t L ≠ L := fun h =>
    ht (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.GorensteinWalter.component_commute_of_ne
      ((CFSG.Adapters.isComponentOf_top_iff _).1 (isComponentOf_conjSub_top hL t))
      ((CFSG.Adapters.isComponentOf_top_iff L).1 hL) hne)

end Helpers

section Main

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem baum_le_normalizer_of_natural (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : Open.IsComponentOf L ⊤) {V K : Subgroup X} (hV : V = gnV T)
    (hK : K = L.comap (QuotientGroup.mk' (gnC T))) {n : ℕ} (hn : 9 ≤ n) (hodd : Odd n)
    {Φ : ↥K →* alternatingGroup (Fin n)} (hΦs : Function.Surjective Φ)
    (hΦk : ∀ k : ↥K, Φ k = 1 → (k : X) ∈ gnC T)
    {π : ↥⁅V, K⁆ →* Multiplicative (evenWeight n)} (hπ : AltBaumSection V K Φ π) :
    gnImg T (baum T) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := by
  classical
  have hVel : IsElemAbelian 2 V := hV ▸ isElemAbelian_gnV T hX
  have hVT : V ≤ T := hV ▸ gnV_le T hX
  have hVnorm : V.Normal := hV ▸ inferInstance
  have hVC : ∀ c ∈ gnC T, ∀ v ∈ V, c * v * c⁻¹ = v := fun c hc v hv => by
    have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.1 hc v (hV ▸ hv)
    rw [← h1, mul_inv_cancel_right]
  have hS : AltBaumSetup V K Φ :=
    { comm := fun v hv w hw => congrArg Subtype.val (hVel.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
      sq := fun v hv => by have := hVel.2 v hv; simpa [pow_two] using this
      norm := fun k _ v hv => hVnorm.conj_mem v hv k
      surj := hΦs
      ker := fun k hk v hv => hVC _ (hΦk k hk) v hv }
  have hinj := hπ.injective hS hodd hn
  have hUV : ⁅V, K⁆ ≤ V := commutator_le_of_invariant V K hS.norm
  have hJK : ∀ j ∈ thompsonJ T, j ∈ Subgroup.normalizer (K : Set X) := by
    intro j hj
    have hq : QuotientGroup.mk' (gnC T) j ∈ Subgroup.normalizer (L : Set (X ⧸ gnC T)) :=
      thompsonJ_le_normalizer_of_isComponentOf hX hL
        (Subgroup.mem_map_of_mem (QuotientGroup.mk' (gnC T)) hj)
    rw [Subgroup.mem_normalizer_iff] at hq ⊢
    intro k
    rw [hK, Subgroup.mem_comap, Subgroup.mem_comap]
    have := hq (QuotientGroup.mk' (gnC T) k)
    simpa [map_mul, map_inv] using this
  have hU_norm : ∀ g ∈ Subgroup.normalizer (K : Set X),
      g ∈ Subgroup.normalizer ((⁅V, K⁆ : Subgroup X) : Set X) := by
    intro g hg
    have hgV : g ∈ Subgroup.normalizer (V : Set X) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hVnorm]; exact Subgroup.mem_top g
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg hgV ⊢
    rw [Subgroup.map_commutator, hg, hgV]
  have hJU : thompsonJ T ≤ Subgroup.normalizer ((⁅V, K⁆ : Subgroup X) : Set X) :=
    fun j hj => hU_norm j (hJK j hj)
  have hJp : IsPGroup 2 ↥(thompsonJ T) := hX.sylow.2.1.to_le (B6.thompsonJ_le T)
  have hUp : IsPGroup 2 ↥⁅V, K⁆ := fun u => ⟨1, by
    rw [pow_one, pow_two]; exact Subtype.ext (hS.sq u (hUV u.2))⟩
  have hn0 : 0 < n := by omega
  have hUnt : ∃ u : ↥⁅V, K⁆, u ≠ 1 := by
    obtain ⟨u, hu⟩ := hπ.surj (Multiplicative.ofAdd (altBaumY hodd ⟨0, hn0⟩))
    refine ⟨u, fun h => ?_⟩
    rw [h, map_one] at hu
    have h0 := congrArg Multiplicative.toAdd hu
    exact altBaumY_ne_zero hodd (by omega) ⟨0, hn0⟩ (by simpa using h0.symm)
  let _ : MulDistribMulAction ↥(thompsonJ T) ↥⁅V, K⁆ :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer _ _ hJU
  obtain ⟨m, hmfix, hm1⟩ : ∃ m : ↥⁅V, K⁆, (∀ j : ↥(thompsonJ T), j • m = m) ∧ m ≠ 1 := by
    have hmod := hJp.card_modEq_card_fixedPoints ↥⁅V, K⁆
    have h2 : 2 ∣ Nat.card ↥⁅V, K⁆ := by
      rcases hUp.card_eq_or_dvd with h1 | h2
      · exfalso
        obtain ⟨u, hu⟩ := hUnt
        have : Subsingleton ↥⁅V, K⁆ := (Nat.card_eq_one_iff_unique.1 h1).1
        exact hu (Subsingleton.elim _ _)
      · exact h2
    have h0 : Nat.card ↥(MulAction.fixedPoints ↥(thompsonJ T) ↥⁅V, K⁆) ≡ 0 [MOD 2] :=
      hmod.symm.trans ((Nat.modEq_zero_iff_dvd).2 h2)
    by_contra hall
    push Not at hall
    have h1 : Subsingleton ↥(MulAction.fixedPoints ↥(thompsonJ T) ↥⁅V, K⁆) :=
      ⟨fun a b => Subtype.ext ((hall a.1 a.2).trans (hall b.1 b.2).symm)⟩
    have h3 : Nat.card ↥(MulAction.fixedPoints ↥(thompsonJ T) ↥⁅V, K⁆) = 1 := by
      have hne : Nonempty ↥(MulAction.fixedPoints ↥(thompsonJ T) ↥⁅V, K⁆) :=
        ⟨⟨1, fun j => smul_one j⟩⟩
      exact Nat.card_of_subsingleton hne.some
    rw [h3] at h0
    exact absurd h0 (by decide)
  have hm_conj : ∀ j ∈ thompsonJ T, (j : X) * (m : X) * (j : X)⁻¹ = m := fun j hj => by
    have h1 := congrArg Subtype.val (hmfix ⟨j, hj⟩)
    exact (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit _ _ hJU ⟨j, hj⟩ m).symm.trans h1
  have hmV : (m : X) ∈ V := hUV m.2
  have hmT : (m : X) ∈ T := hVT hmV
  have hmC : (m : X) ∈ Subgroup.centralizer ((thompsonJ T : Subgroup X) : Set X) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      have := hm_conj h hh
      calc h * (m : X) = (h * (m : X) * h⁻¹) * h := by group
        _ = (m : X) * h := by rw [this]
  have hm2 : (m : X) ^ 2 = 1 := by rw [pow_two]; exact hS.sq _ hmV
  have hmE : (m : X) ∈ omegaOneCenterOf (thompsonJ T) := by
    rw [← (omegaOne_centralizer_thompsonJ T).1]
    exact Subgroup.subset_closure ⟨⟨hmT, hmC⟩, hm2⟩
  intro q hq
  obtain ⟨t, htb, rfl⟩ := Subgroup.mem_map.1 hq
  by_contra hnot
  have htm : (t : X) * (m : X) * (t : X)⁻¹ = m := by
    have h1 : (m : X) * t = t * m := Subgroup.mem_centralizer_iff.1 htb.2 m hmE
    rw [mul_inv_eq_iff_eq_mul]; exact h1.symm
  have hnot' : (QuotientGroup.mk' (gnC T) t)⁻¹ ∉ Subgroup.normalizer (L : Set (X ⧸ gnC T)) :=
    fun h => hnot (by simpa using (Subgroup.normalizer (L : Set (X ⧸ gnC T))).inv_mem h)
  have hc := conjSub_le_centralizer_of_not_mem_normalizer hL hnot'
  have hkm : ∀ k ∈ K, (k : X) * (m : X) * (k : X)⁻¹ = m := by
    intro k hk
    obtain ⟨x, hx⟩ : ∃ x : X, x = (t : X)⁻¹ * k * t := ⟨_, rfl⟩
    have hkL : QuotientGroup.mk' (gnC T) k ∈ L := by rw [hK] at hk; exact hk
    have hxL : QuotientGroup.mk' (gnC T) x ∈ B6.conjSub (QuotientGroup.mk' (gnC T) t)⁻¹ L := by
      rw [B6.mem_conjSub]
      have e : ((QuotientGroup.mk' (gnC T) t)⁻¹)⁻¹ * QuotientGroup.mk' (gnC T) x *
          (QuotientGroup.mk' (gnC T) t)⁻¹ = QuotientGroup.mk' (gnC T) k := by
        rw [hx]; simp only [map_mul, map_inv]; group
      rw [e]; exact hkL
    have hxc := hc hxL
    have hcomm : ∀ k' ∈ K, ∀ v ∈ V, x * (k' * v * k'⁻¹) * x⁻¹ = k' * (x * v * x⁻¹) * k'⁻¹ := by
      intro k' hk' v hv
      have hk'L : QuotientGroup.mk' (gnC T) k' ∈ L := by rw [hK] at hk'; exact hk'
      have h1 := Subgroup.mem_centralizer_iff.1 hxc _ hk'L
      have h2 : x * k' * x⁻¹ * k'⁻¹ ∈ gnC T := by
        refine (QuotientGroup.eq_one_iff _).1 ?_
        show QuotientGroup.mk' (gnC T) (x * k' * x⁻¹ * k'⁻¹) = 1
        simp only [map_mul, map_inv]
        calc QuotientGroup.mk' (gnC T) x * QuotientGroup.mk' (gnC T) k' *
              (QuotientGroup.mk' (gnC T) x)⁻¹ * (QuotientGroup.mk' (gnC T) k')⁻¹
            = (QuotientGroup.mk' (gnC T) k' * QuotientGroup.mk' (gnC T) x) *
              (QuotientGroup.mk' (gnC T) x)⁻¹ * (QuotientGroup.mk' (gnC T) k')⁻¹ := by rw [h1]
          _ = 1 := by group
      have e : x * (k' * v * k'⁻¹) * x⁻¹ =
          (x * k' * x⁻¹ * k'⁻¹) * (k' * (x * v * x⁻¹) * k'⁻¹) * (x * k' * x⁻¹ * k'⁻¹)⁻¹ := by
        group
      rw [e]
      exact hVC _ h2 _ (hS.norm k' hk' _ (hVnorm.conj_mem v hv x))
    have hxm := hπ.centralizes_of_commute hS hodd hn (x := x)
      (fun v hv => hVnorm.conj_mem v hv x) hcomm m m.2
    calc (k : X) * (m : X) * (k : X)⁻¹ = k * (t * m * (t : X)⁻¹) * k⁻¹ := by rw [htm]
      _ = t * (x * m * x⁻¹) * (t : X)⁻¹ := by rw [hx]; group
      _ = t * m * (t : X)⁻¹ := by rw [hxm]
      _ = m := htm
  have hm_one : π m = 1 := (hπ.ker_iff m).2 hkm
  exact hm1 (hinj (hm_one.trans (map_one π).symm))

theorem baum_le_normalizer_alt (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : Open.IsComponentOf L ⊤) {n : ℕ} (hn : 9 ≤ n) (hodd : Odd n)
    (e : ↥L ≃* alternatingGroup (Fin n))
    (π : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (altHeart n))
    (hπs : Function.Surjective π)
    (hπk : ∀ u, π u = 1 ↔
      ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), (k : X) * u * (k : X)⁻¹ = u)
    (hπi : ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L)
      (u u' : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
        Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
          (e ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin n)) x) : altHeart n)) :
    gnImg T (baum T) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := by
  classical
  let ε : evenWeight n ≃+ altHeart n :=
    AddEquiv.ofBijective (QuotientAddGroup.mk' (evenWeightOnes n))
      ⟨altHeart_mk_injective hodd, QuotientAddGroup.mk_surjective⟩
  let ε' : Multiplicative (altHeart n) ≃* Multiplicative (evenWeight n) :=
    AddEquiv.toMultiplicative ε.symm
  let π' : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (evenWeight n) :=
    ε'.toMonoidHom.comp π
  let f : ↥(L.comap (QuotientGroup.mk' (gnC T))) →* ↥L :=
    ((QuotientGroup.mk' (gnC T)).comp (L.comap (QuotientGroup.mk' (gnC T))).subtype).codRestrict L
      (fun k => k.2)
  have hf : Function.Surjective f := fun l => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (l : X ⧸ gnC T)
    exact ⟨⟨x, by
      show QuotientGroup.mk' (gnC T) x ∈ L
      rw [show QuotientGroup.mk' (gnC T) x = (l : X ⧸ gnC T) from hx]; exact l.2⟩,
      Subtype.ext hx⟩
  let Φ : ↥(L.comap (QuotientGroup.mk' (gnC T))) →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp f
  refine baum_le_normalizer_of_natural hX hL (V := gnV T)
    (K := L.comap (QuotientGroup.mk' (gnC T))) rfl rfl hn hodd (Φ := Φ)
    (e.surjective.comp hf) (fun k hk => ?_) (π := π') ?_
  · have h1 : f k = 1 := e.injective (hk.trans (map_one e).symm)
    have h2 : QuotientGroup.mk' (gnC T) (k : X) = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).1 h2
  · refine ⟨ε'.surjective.comp hπs, fun u => ?_, fun l u u' h => ?_⟩
    · rw [show π' u = ε' (π u) from rfl, MulEquiv.map_eq_one_iff]
      exact hπk u
    · have hx : Multiplicative.toAdd (π u) =
          (QuotientAddGroup.mk (Multiplicative.toAdd (π' u)) : altHeart n) := by
        show _ = ε (ε.symm (Multiplicative.toAdd (π u)))
        rw [ε.apply_symm_apply]
      have h1 := hπi (l : X) l.2 u u' h _ hx
      show ε.symm (Multiplicative.toAdd (π u')) = _
      rw [h1]
      exact ε.symm_apply_apply _

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
