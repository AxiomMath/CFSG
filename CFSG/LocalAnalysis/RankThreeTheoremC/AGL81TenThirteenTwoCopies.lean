module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenReduce
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenGeneric
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven
import CFSG.HardMathSupport.Cooperstein.Proving.A6Z3Kernel
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

open scoped commutatorElement

theorem card_sq_dvd_of_commute {A B V T : Type*} [Group A] [Group B] [Group V] [Group T]
    [Finite A] [Finite B] (hT : center T = ⊥) (α : A →* V) (β : B →* V) (W : Subgroup V)
    (hαW : α.range ≤ W) (hβW : β.range ≤ W) (hcomm : ∀ a b, Commute (α a) (β b))
    (fA : A →* T) (fB : B →* T) (hfA : Function.Surjective fA) (hfB : Function.Surjective fB)
    (hkA : α.ker ≤ fA.ker) (hkB : β.ker ≤ fB.ker) : Nat.card T ^ 2 ∣ Nat.card W := by
  classical
  let Φ : A × B →* V := MonoidHom.noncommCoprod α β hcomm
  have hΦ : ∀ a b, Φ (a, b) = α a * β b := fun _ _ => rfl
  have hrange : Φ.range ≤ W := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [hΦ]
    exact W.mul_mem (hαW (MonoidHom.mem_range.mpr ⟨a, rfl⟩))
      (hβW (MonoidHom.mem_range.mpr ⟨b, rfl⟩))
  have hker : Φ.ker ≤ (fA.prodMap fB).ker := by
    rintro ⟨a, b⟩ hab
    have hab' : α a * β b = 1 := by rw [← hΦ]; exact hab
    have hfa : fA a = 1 := by
      have hcenter : fA a ∈ Subgroup.center T := by
        rw [Subgroup.mem_center_iff]
        intro t
        obtain ⟨a', rfl⟩ := hfA t
        have hc : Commute (α a) (α a') := by
          rw [mul_eq_one_iff_eq_inv] at hab'
          rw [hab']
          exact ((hcomm a' b).symm).inv_left
        have hmem : ⁅a', a⁆ ∈ fA.ker :=
          hkA (by rw [MonoidHom.mem_ker, map_commutatorElement]; exact hc.symm.commutator_eq)
        have h2 : ⁅fA a', fA a⁆ = 1 := by
          simpa [map_commutatorElement] using hmem
        exact (commutatorElement_eq_one_iff_commute.mp h2)
      rw [hT] at hcenter
      simpa using hcenter
    have hfb : fB b = 1 := by
      have hcenter : fB b ∈ Subgroup.center T := by
        rw [Subgroup.mem_center_iff]
        intro t
        obtain ⟨b', rfl⟩ := hfB t
        have hb : β b = (α a)⁻¹ := by
          rw [mul_eq_one_iff_eq_inv] at hab'
          rw [hab']
          simp
        have hc : Commute (β b) (β b') := by
          rw [hb]
          exact (hcomm a b').inv_left
        have hmem : ⁅b', b⁆ ∈ fB.ker :=
          hkB (by rw [MonoidHom.mem_ker, map_commutatorElement]; exact hc.symm.commutator_eq)
        have h2 : ⁅fB b', fB b⁆ = 1 := by
          simpa [map_commutatorElement] using hmem
        exact (commutatorElement_eq_one_iff_commute.mp h2)
      rw [hT] at hcenter
      simpa using hcenter
    rw [MonoidHom.mem_ker]
    show (fA.prodMap fB) (a, b) = 1
    rw [show (fA.prodMap fB) (a, b) = (fA a, fB b) from rfl, hfa, hfb]
    rfl
  have htop : (fA.prodMap fB).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    rintro ⟨t₁, t₂⟩
    obtain ⟨a, rfl⟩ := hfA t₁
    obtain ⟨b, rfl⟩ := hfB t₂
    exact ⟨(a, b), rfl⟩
  have hcard : (fA.prodMap fB).ker.index = Nat.card T ^ 2 := by
    rw [Subgroup.index_ker, htop, Subgroup.card_top, Nat.card_prod, pow_two]
  calc Nat.card T ^ 2 = (fA.prodMap fB).ker.index := hcard.symm
    _ ∣ Φ.ker.index := Subgroup.index_dvd_of_le hker
    _ = Nat.card Φ.range := Subgroup.index_ker Φ
    _ ∣ Nat.card W := Subgroup.card_dvd_of_le hrange

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_two_inf_le_d1PlusCore {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    pCoreOf 2 (H ⊓ L) ≤ d1PlusCore p H K :=
  (CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2
    (isSubnormal_inf_inf hL.subnormal)).trans
    (hd.b3 (pCoreOf 2 (H ⊓ M)) (pCoreOf_isPGroup 2 (H ⊓ M))
      ((pCoreOf_le 2 (H ⊓ M)).trans inf_le_left)
      ((le_inf hd.le_H hd.base.1).trans (localGroup_le_normalizer_pCoreOf 2 (H ⊓ M))))

theorem comap_centralizer_eq_d1PlusCore_self {p : ℕ} {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} :
    (Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))).comap
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (d1PlusCore p H K).subgroupOf H := by
  have h := comap_centralizer_eq_subgroupOf (I := H) (K := K) le_rfl
  rw [show Subgroup.inclusion (le_refl H) = MonoidHom.id H from by ext x; rfl,
    MonoidHom.comp_id] at h
  exact h

theorem normal_subgroupOf_d1PlusCore {p : ℕ} {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} [K.Normal] :
    ((d1PlusCore p H K).subgroupOf H).Normal := by
  rw [← comap_centralizer_eq_d1PlusCore_self]
  exact Subgroup.normal_comap _

theorem le_normalizer_of_not_card_sq_dvd (h31 : KFactThreeOne) (hSch : KFactCatalogSchreier)
    (hS : Setting G) {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {I₀ : Subgroup G}
    (hI₀ : I₀ ∈ cZero (H ⊓ L)) (hI : IsTwoPrimeComponent I₀ I₀) {T : Type*} [Group T]
    (hT : center T = ⊥) (f : I₀ →* T) (hf : Function.Surjective f)
    (hfX : (d1PlusCore p H K).subgroupOf I₀ ≤ f.ker) (hn : ¬ Nat.card T ^ 2 ∣ Nat.card K) :
    H ⊓ L ≤ normalizer (I₀ : Set G) := by
  classical
  by_contra hcon
  obtain ⟨y, hy, hyN⟩ := Set.not_subset.mp hcon
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  haveI hsimp : IsSimpleGroup G := hS.simple
  have hHtop : H ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hd.maxH.1
  have hKne : d1KBar p M H ≠ ⊥ :=
    fun h => hd.not_le_X0 (by rw [hd.kbar, h]; exact bot_le)
  have hKn : K.Normal := by
    rw [hd.kbar]
    exact d1KBar_normal_of_escape he hd.base hd.le_H hKne
  haveI : K.Normal := hKn
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set C : Subgroup (H ⧸ primeComplementCore (G := H) p) :=
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) with hC
  haveI hCn : C.Normal := by rw [hC]; exact Subgroup.normal_centralizer
  set mkC := QuotientGroup.mk' C with hmkC
  set I₁ : Subgroup G := I₀.map (MulAut.conj y).toMonoidHom with hI₁
  have hI₀' : IsTwoPrimeComponent (H ⊓ L) I₀ :=
    isTwoPrimeComponent_of_self hI hI₀.le hI₀.subnormal
  have hI₁' : IsTwoPrimeComponent (H ⊓ L) I₁ := by
    rw [hI₁]
    exact hI₀'.map_conj hy
  have hne' : I₀ ≠ I₁ := by
    rw [hI₁]
    intro h
    exact hyN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hcommut : ⁅I₀, I₁⁆ ≤ d1PlusCore p H K :=
    (IsTwoPrimeComponent.commutator_le hI₀' hI₁' hne').trans (pCoreOf_two_inf_le_d1PlusCore hd hL)
  have hI₀H : I₀ ≤ H := hI₀.le.trans inf_le_left
  have hI₁H : I₁ ≤ H := by
    rw [hI₁]
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    exact H.mul_mem (H.mul_mem hy.1 (hI₀H ha)) (H.inv_mem hy.1)
  haveI hperfI : Group.IsPerfect ↥I₀ := Subgroup.isPerfect_iff.mpr hI.perfect
  haveI hperfH : Group.IsPerfect ↥(I₀.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hI₀H).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hI₁sub : I₁.subgroupOf H =
      (I₀.subgroupOf H).map (MulAut.conj (⟨y, hy.1⟩ : H)).toMonoidHom := by
    rw [hI₁]
    exact subgroupOf_map_conj hy.1 I₀
  haveI hperfH₁ : Group.IsPerfect ↥(I₁.subgroupOf H) := by
    rw [hI₁sub]
    exact Group.IsPerfect.map (f := (MulAut.conj (⟨y, hy.1⟩ : H)).toMonoidHom)
      (H := I₀.subgroupOf H)
  have hZle₀ : (I₀.subgroupOf H).map π ≤ K ⊔ C := by
    have h := le_sup_centralizer_d1KBar_of_isPerfect h31 hSch hS.kProper he hd.base hd.le_H
      hHtop hKne (Z := (I₀.subgroupOf H).map π)
      (Group.IsPerfect.map (f := π) (H := I₀.subgroupOf H))
    rwa [← hd.kbar] at h
  have hZle₁ : (I₁.subgroupOf H).map π ≤ K ⊔ C := by
    have h := le_sup_centralizer_d1KBar_of_isPerfect h31 hSch hS.kProper he hd.base hd.le_H
      hHtop hKne (Z := (I₁.subgroupOf H).map π)
      (Group.IsPerfect.map (f := π) (H := I₁.subgroupOf H))
    rwa [← hd.kbar] at h
  let V := (H ⧸ primeComplementCore (G := H) p) ⧸ C
  let α : I₀ →* V := mkC.comp (π.comp (Subgroup.inclusion hI₀H))
  let β : I₁ →* V := mkC.comp (π.comp (Subgroup.inclusion hI₁H))
  have hCbot : C.map mkC = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hsup : (K ⊔ C).map mkC = K.map mkC := by
    rw [Subgroup.map_sup, hCbot, sup_bot_eq]
  have hαW : α.range ≤ K.map mkC := by
    rw [show α.range = ((I₀.subgroupOf H).map π).map mkC from by
      rw [show α = mkC.comp (π.comp (Subgroup.inclusion hI₀H)) from rfl, MonoidHom.range_comp,
        MonoidHom.range_comp, Subgroup.inclusion_range], ← hsup]
    exact Subgroup.map_mono hZle₀
  have hβW : β.range ≤ K.map mkC := by
    rw [show β.range = ((I₁.subgroupOf H).map π).map mkC from by
      rw [show β = mkC.comp (π.comp (Subgroup.inclusion hI₁H)) from rfl, MonoidHom.range_comp,
        MonoidHom.range_comp, Subgroup.inclusion_range], ← hsup]
    exact Subgroup.map_mono hZle₁
  have hαker : α.ker = (d1PlusCore p H K).subgroupOf I₀ := by
    ext a
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' C (π (Subgroup.inclusion hI₀H a)) = 1 ↔
      a ∈ (d1PlusCore p H K).subgroupOf I₀
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← comap_centralizer_eq_subgroupOf (K := K) hI₀H, Subgroup.mem_comap]
    rfl
  have hβker : β.ker = (d1PlusCore p H K).subgroupOf I₁ := by
    ext a
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' C (π (Subgroup.inclusion hI₁H a)) = 1 ↔
      a ∈ (d1PlusCore p H K).subgroupOf I₁
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← comap_centralizer_eq_subgroupOf (K := K) hI₁H, Subgroup.mem_comap]
    rfl
  let e : I₀ ≃* I₁ :=
    Subgroup.equivMapOfInjective I₀ (MulAut.conj y).toMonoidHom (MulAut.conj y).injective
  let fB : I₁ →* T := f.comp e.symm.toMonoidHom
  have hfB : Function.Surjective fB := hf.comp (MulEquiv.surjective e.symm)
  have hkA : α.ker ≤ f.ker := by
    rw [hαker]
    exact hfX
  have hkX : ((d1PlusCore p H K).subgroupOf H).Normal := normal_subgroupOf_d1PlusCore
  have hkB : β.ker ≤ fB.ker := by
    intro b hb
    have hbC : π (Subgroup.inclusion hI₁H b) ∈ C := by
      change QuotientGroup.mk' C (π (Subgroup.inclusion hI₁H b)) = 1 at hb
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb
      exact hb
    have hbX : (b : G) ∈ d1PlusCore p H K := by
      have h : Subgroup.inclusion hI₁H b ∈ (d1PlusCore p H K).subgroupOf H := by
        rwa [← comap_centralizer_eq_d1PlusCore_self, Subgroup.mem_comap]
      exact Subgroup.mem_subgroupOf.mp h
    have hbdecomp : (b : G) = y * ((e.symm b : I₀) : G) * y⁻¹ := by
      conv_lhs => rw [← MulEquiv.apply_symm_apply e b]
      rfl
    have hzX : ((e.symm b : I₀) : G) ∈ d1PlusCore p H K := by
      have hzH : (Subgroup.inclusion hI₀H (e.symm b) : H) =
          (⟨y, hy.1⟩ : H)⁻¹ * (Subgroup.inclusion hI₁H b : H) * ⟨y, hy.1⟩ := by
        ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
        rw [hbdecomp]
        group
      have hbH : (Subgroup.inclusion hI₁H b : H) ∈ (d1PlusCore p H K).subgroupOf H :=
        Subgroup.mem_subgroupOf.mpr hbX
      have h := hkX.conj_mem (Subgroup.inclusion hI₁H b) hbH (⟨y, hy.1⟩ : H)⁻¹
      have hz' : (Subgroup.inclusion hI₀H (e.symm b) : H) ∈
          (d1PlusCore p H K).subgroupOf H := by
        rw [hzH]
        simpa using h
      exact Subgroup.mem_subgroupOf.mp hz'
    exact hfX (Subgroup.mem_subgroupOf.mpr hzX)
  have hcomm : ∀ a b, Commute (α a) (β b) := by
    intro a b
    have hX : (⁅Subgroup.inclusion hI₀H a, Subgroup.inclusion hI₁H b⁆ : H) ∈
        (d1PlusCore p H K).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      change H.subtype ⁅Subgroup.inclusion hI₀H a, Subgroup.inclusion hI₁H b⁆ ∈
        d1PlusCore p H K
      rw [map_commutatorElement]
      simpa [Subgroup.coe_inclusion] using
        hcommut (Subgroup.commutator_mem_commutator a.2 b.2)
    have hX' : π (⁅Subgroup.inclusion hI₀H a, Subgroup.inclusion hI₁H b⁆ : H) ∈ C := by
      rw [← Subgroup.mem_comap, comap_centralizer_eq_d1PlusCore_self]
      exact hX
    have h1 : (mkC.comp π) ⁅Subgroup.inclusion hI₀H a, Subgroup.inclusion hI₁H b⁆ = 1 := by
      change QuotientGroup.mk' C (π ⁅Subgroup.inclusion hI₀H a, Subgroup.inclusion hI₁H b⁆) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hX'
    rw [← commutatorElement_eq_one_iff_commute]
    show ⁅α a, β b⁆ = 1
    rw [show α a = (mkC.comp π) (Subgroup.inclusion hI₀H a) from rfl,
      show β b = (mkC.comp π) (Subgroup.inclusion hI₁H b) from rfl,
      ← map_commutatorElement, h1]
  exact hn ((card_sq_dvd_of_commute hT α β (K.map mkC) hαW hβW hcomm f fB hf hfB hkA hkB).trans
    (Subgroup.card_map_dvd K mkC))

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
