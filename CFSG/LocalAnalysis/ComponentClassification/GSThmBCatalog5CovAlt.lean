module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovOdd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovAltLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovAltComp
public import CFSG.GH74.Generic.GKFAlt
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovSpor

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.OutInv
open CFSG.ComponentClassification.GSThmB.Fus23 CFSG.LocalAnalysis.ComponentInitial

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

theorem isComponentOf_comap_conj {Y : Type*} [Group Y] (hZ : center Y = ⊥)
    {G : Subgroup (MulAut Y)} (hInn : (MulAut.conj : Y →* MulAut Y).range ≤ G) (φ : G)
    {Jh : Subgroup G} (hJle : Jh ≤ (MulAut.conj : Y →* MulAut Y).range.subgroupOf G)
    (hJc : Jh ≤ centralizer ({φ} : Set G))
    (hJ : CFSG.IsComponent (Jh.subgroupOf (centralizer ({φ} : Set G)))) :
    CFSG.Assembly.IsComponentOf ((Jh.map G.subtype).comap (MulAut.conj : Y →* MulAut Y))
      (fixSub (φ : MulAut Y)) := by
  set ι := (MulAut.conj : Y →* MulAut Y) with hιdef
  have hι : Function.Injective ι := conj_injective_of_center hZ
  have hG : Function.Injective G.subtype := Subtype.val_injective
  have h1 : CFSG.Assembly.IsComponentOf Jh (centralizer ({φ} : Set G)) :=
    (isComponentOf_iff_isComponent_subgroupOf hJc).2 hJ
  have h2 := (isComponentOf_map_iff hG).2 h1
  rw [CFSG.Sporadic.SmallOddCore.map_centralizer_eq_inf hG, range_subtype,
    Set.image_singleton] at h2
  have hJι : Jh.map G.subtype ≤ ι.range := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact mem_subgroupOf.mp (hJle hσ)
  have hR : ι.range ⊓ centralizer ({(φ : MulAut Y)} : Set (MulAut Y)) ≤
      G ⊓ centralizer ({(φ : MulAut Y)} : Set (MulAut Y)) :=
    inf_le_inf_right _ hInn
  have h3 := isComponentOf_of_le h2 (le_inf hJι (h2.1.trans inf_le_right)) hR
  rw [← map_conj_fixSub hZ] at h3
  rw [← isComponentOf_map_iff hι, map_comap_eq_self hJι]
  exact h3

include hKa in
theorem comap_conj_Jhat_eq :
    ((Jhat hKa).map (GAut hKa).subtype).comap (MulAut.conj : LK h →* MulAut (LK h)) =
      (imJB h).map (QuotientGroup.mk' (center (OddBar h.K))) := by
  ext ℓ
  constructor
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, hℓ⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hy
    have hyK : (y : H) ∈ h.K := fixedLayer_le_K h hKa hy
    have h1 : MulAut.conj ℓ =
        MulAut.conj ((((⟨(y : H), hyK⟩ : h.K) : OddBar h.K)) : LK h) := by
      rw [← hℓ]
      show rhoBar hKa (wbarMk h.B y) = _
      rw [rhoBar_mk, ← rhoL_of_mem_K hKa ⟨(y : H), hyK⟩]
    rw [OutInv.conj_injective (h := h) h1]
    exact ⟨((⟨(y : H), hyK⟩ : h.K) : OddBar h.K),
      ⟨⟨(y : H), hyK⟩, mem_subgroupOf.mpr hy, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    rw [mem_comap]
    refine ⟨phi hKa (wbarMk h.B ⟨k, K_le_W h k.2⟩),
      ⟨wbarMk h.B ⟨k, K_le_W h k.2⟩, ⟨⟨k, K_le_W h k.2⟩,
        mem_subgroupOf.mpr (mem_subgroupOf.mp hk), rfl⟩, rfl⟩, ?_⟩
    show rhoBar hKa (wbarMk h.B ⟨k, K_le_W h k.2⟩) = _
    rw [rhoBar_mk, rhoL_of_mem_K hKa k]
    rfl

include hKa in
theorem eq_one_of_mem_imJB_center (hZJ : center (OddBar h.J) = ⊥) {w : OddBar h.K}
    (hw : w ∈ imJB h) (hwc : w ∈ center (OddBar h.K)) : w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_two_center_oddBar h.K)) ⟨w, hwc⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exfalso
    have hw1 : w ^ 2 ^ k ≠ 1 :=
      pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero)
        (by rw [hk]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hw2 : w ^ 2 ^ k * w ^ 2 ^ k = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', ← hk, pow_orderOf_eq_one]
    exact hw1 (eq_one_of_central_sq h hKa hZJ (pow_mem hw _)
      (fun y _ => (mem_center_iff.mp (pow_mem hwc _) y).symm) hw2)

include hKa in
theorem false_of_alt (hZK : center (OddBar h.K) ≠ ⊥)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f)
    {n : ℕ} (hn : 7 ≤ n) (e : ZStarBar h.K ≃* alternatingGroup (Fin n)) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hZJ := center_eq_bot_of_small hJ
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hZ2 := isPGroup_two_center_oddBar h.K
  have hcard : Nat.card (center (OddBar h.K)) = 2 := card_center_eq_two hZK
    (GH74.Generic.alt_cover_of_central_kernel (by omega) h.isQuasisimple_K hZ2 (eZ.trans e))
  have hM₀ : CFSG.Assembly.IsComponentOf ((imJB h).map (QuotientGroup.mk' (center (OddBar h.K))))
      (fixSub ((phi hKa (abar h) : ↥(GAut hKa)) : MulAut (LK h))) := by
    have h0 := isComponentOf_comap_conj center_LK (inn_le_GAut hKa) (phi hKa (abar h))
      (Jhat_le_NL hKa) (Jhat_component hKa).1 (Jhat_component hKa).2
    rwa [comap_conj_Jhat_eq hKa] at h0
  obtain ⟨eA, -⟩ : ∃ f : LK h ≃* alternatingGroup (Fin (m + 2)), f = eZ.trans e := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ g : MulAut (LK h),
      g = ((phi hKa (abar h) : ↥(GAut hKa)) : MulAut (LK h)) := ⟨_, rfl⟩
  rw [← hφ] at hM₀
  have hφ2 : φ * φ = 1 := by
    have h0 := pow_orderOf_eq_one (phi hKa (abar h))
    rw [orderOf_phi_abar' hKa, sq] at h0
    rw [hφ, ← Subgroup.coe_mul, h0, Subgroup.coe_one]
  have hφ1 : φ ≠ 1 := by
    intro h1
    have h0 := orderOf_phi_abar' hKa
    have h2 : phi hKa (abar h) = 1 := Subtype.ext (by rw [← hφ, h1, Subgroup.coe_one])
    rw [h2, orderOf_one] at h0
    exact absurd h0 (by norm_num)
  set β : MulAut (alternatingGroup (Fin (m + 2))) := (eA.symm.trans φ).trans eA with hβ
  have hβ2 : β * β = 1 := by
    refine MulEquiv.ext fun s => ?_
    have h1 := congrArg (fun g : MulAut (LK h) => g (eA.symm s)) hφ2
    simp only [MulAut.mul_apply, MulAut.one_apply] at h1
    simp only [hβ, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h1,
      MulEquiv.apply_symm_apply, MulAut.one_apply]
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hφ1
    refine MulEquiv.ext fun y => ?_
    have h2 := congrArg (fun g : MulAut (alternatingGroup (Fin (m + 2))) => g (eA y)) h1
    simp only [hβ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
    rw [MulAut.one_apply]
    exact eA.injective h2
  obtain ⟨a, b, c, d, hnd, hmem, hmemP⟩ :=
    exists_dt_mem_of_component hn hβ2 hβ1 (isComponentOf_fixSub_map eA φ hM₀)
  obtain ⟨_, ⟨x, hx, rfl⟩, hxe⟩ := hmemP
  have : Group.IsPerfect (OddBar h.K) := h.isQuasisimple_K.1
  set η : OddBar h.K →* alternatingGroup (Fin (m + 2)) :=
    eA.toMonoidHom.comp (QuotientGroup.mk' (center (OddBar h.K))) with hη
  have hηs : Function.Surjective η := by
    rw [hη, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center (OddBar h.K) := by
    ext v
    rw [hη, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hxd : η x = ⟨Equiv.swap a b * Equiv.swap c d, hmem⟩ := hxe
  have hdd : (⟨Equiv.swap a b * Equiv.swap c d, hmem⟩ : alternatingGroup (Fin (m + 2))) ^ 2 =
      1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, sq]
    have hcomm := (Equiv.Perm.disjoint_swap_swap hnd).commute
    calc Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b * Equiv.swap c d) =
        Equiv.swap a b * (Equiv.swap c d * Equiv.swap a b) * Equiv.swap c d := by group
      _ = Equiv.swap a b * (Equiv.swap a b * Equiv.swap c d) * Equiv.swap c d := by
          rw [hcomm.eq]
      _ = 1 := by rw [← mul_assoc, Equiv.swap_mul_self, one_mul, Equiv.swap_mul_self]
  have hx2 : x ^ 2 = 1 := by
    apply eq_one_of_mem_imJB_center hKa hZJ (pow_mem hx 2)
    rw [← hker, MonoidHom.mem_ker, map_pow, hxd, hdd]
  exact sq_ne_one_of_map_eq_dt (by omega) η hηs (hker ▸ le_refl _) (by rw [hker]; exact hcard)
    hnd hmem hxd hx2

end CFSG.ComponentClassification.GSThmB.Cov
