module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndGLocal
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4KGModel

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.ComponentClassification.AschbacherKnownGroup (HasDihedralSylowTwo HasCyclicSylowTwo)
open CFSG.GorensteinWalter

section Odd

variable {X : Type*} [Group X]

theorem exists_zpow_conj_eq_mul_of_odd {s o : X} (hs : s ^ 2 = 1) (hso : (s * o) ^ 2 = 1)
    (ho : Odd (orderOf o)) : ∃ m : ℤ, o ^ (-m) * s * o ^ m = s * o := by
  obtain ⟨j, hj⟩ := ho
  have hss : s * s = 1 := by rw [← pow_two]; exact hs
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hinv : s * o * s = o⁻¹ := by
    have h1 : s * o * (s * o) = 1 := by rw [← pow_two]; exact hso
    calc s * o * s = s * o * (s * o) * o⁻¹ := by group
      _ = o⁻¹ := by rw [h1, one_mul]
  have hpow : ∀ n : ℤ, s * o ^ n * s = o ^ (-n) := by
    intro n
    have h := conj_zpow (a := s) (b := o) (i := n)
    rw [hsinv] at h
    rw [← h, hinv, inv_zpow, zpow_neg]
  refine ⟨(j : ℤ) + 1, ?_⟩
  have ho1 : o ^ ((2 * j + 1 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hj, pow_orderOf_eq_one]
  calc o ^ (-((j : ℤ) + 1)) * s * o ^ ((j : ℤ) + 1)
      = s * (s * o ^ (-((j : ℤ) + 1)) * s) * o ^ ((j : ℤ) + 1) := by
        rw [show s * (s * o ^ (-((j : ℤ) + 1)) * s) = (s * s) * o ^ (-((j : ℤ) + 1)) * s by group,
          hss, one_mul]
    _ = s * o ^ ((j : ℤ) + 1) * o ^ ((j : ℤ) + 1) := by rw [hpow, neg_neg]
    _ = s * (o ^ ((2 * j + 1 : ℕ) : ℤ) * o) := by
        rw [mul_assoc, ← zpow_add, ← zpow_add_one]
        congr 2
        push_cast
        ring
    _ = s * o := by rw [ho1, one_mul]

end Odd

variable {G : Type} [Group G] [Finite G]

structure PSLModel (Q : Subgroup G) where
  F : Type
  [field : Field F]
  [finite : Finite F]
  hF : IsOddPrimePower (Nat.card F)
  h3 : 3 < Nat.card F
  e : bar Q (twoPrimeLayerIn Q) ≃* PSL2 F

attribute [instance] PSLModel.field PSLModel.finite

namespace PSLModel

variable {Q : Subgroup G} (M : PSLModel Q)

noncomputable def psi : Bar Q →* PGammaL2 M.F :=
  normalPSL2ToPGammaL2 (bar Q (twoPrimeLayerIn Q)) M.F M.hF M.h3 M.e
    (Asc75T4KG.pGammaL2ToMulAutPSL2_surjective' M.hF M.h3)

theorem psi_eq_one_iff (x : Bar Q) :
    M.psi x = 1 ↔ x ∈ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) :=
  Asc75T4KG.psl2Action_eq_one_iff _ M.hF M.h3 M.e _ x

theorem mem_sup_centralizer_iff (x : Bar Q) :
    x ∈ bar Q (twoPrimeLayerIn Q) ⊔ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) ↔
      M.psi x ∈ pGammaL2PSLRange M.F :=
  Asc75T4KG.mem_sup_centralizer_iff _ M.hF M.h3 M.e _ x

theorem psi_apply_of_mem (n : bar Q (twoPrimeLayerIn Q)) :
    M.psi n = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (M.e n)) :=
  AschbacherKnownGroup.FactsL2.psl2Action_apply _ M.hF M.h3 M.e _ n

omit [Finite G] in
theorem pslRange_le_pglRange : pGammaL2PSLRange M.F ≤ pGammaL2PGLRange M.F := by
  rintro _ ⟨y, rfl⟩
  exact ⟨_, rfl⟩

end PSLModel

namespace EndSetting

variable {Q : Subgroup G} (hE : EndSetting Q)
include hE

theorem nonempty_pslModel :
    Nonempty (PSLModel Q) := by
  have := hE.isSimpleGroup_bar
  obtain ⟨u, hu⟩ := hE.exists_isOverlapInv
  rcases AschbacherKnownGroup.FactsL2.simple_dihedral_cases
      (AschbacherKnownGroup.FactsL2.exists_ne_comm_of_simple_dihedral hE.hasDihedralSylowTwo_bar)
      hE.hasDihedralSylowTwo_bar with ⟨⟨eA⟩⟩ | ⟨F, _, _, p, f, -, -, hF, h3, ⟨e⟩⟩
  · exfalso
    obtain ⟨v, w, hv, hw, hv1, hw1, hvw, hc, hav, haw⟩ :=
      AschbacherKnownGroup.FactsL2.a7_involution_commuting_pair (bar Q (twoPrimeLayerIn Q)) eA
        (toBar Q ⟨u, hu.mem_normalizer⟩) hu.bar_sq
    have hmem : ∀ x : bar Q (twoPrimeLayerIn Q),
        toBar Q ⟨u, hu.mem_normalizer⟩ * x = x * toBar Q ⟨u, hu.mem_normalizer⟩ →
        (x : Bar Q) ∈ bar Q (twoPrimeLayerIn Q) ⊓
          centralizer ({toBar Q ⟨u, hu.mem_normalizer⟩} : Set (Bar Q)) := fun x hx =>
      mem_inf.mpr ⟨x.2, mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact hx⟩
    exact AschbacherKnownGroup.FactsL2.not_hasCyclicSylowTwo_of_commuting_involutions _
      (hmem v hav) (hmem w haw) (congrArg Subtype.val hv) (congrArg Subtype.val hw)
      (fun h => hv1 (Subtype.ext h)) (fun h => hw1 (Subtype.ext h))
      (fun h => hvw (Subtype.ext h)) (congrArg Subtype.val hc)
      (hE.hasCyclicSylowTwo_of_isOverlapInv hu)
  · exact ⟨⟨F, hF, h3, e⟩⟩

end EndSetting

namespace PSLModel

variable {Q : Subgroup G} (M : PSLModel Q) (hE : EndSetting Q)
include M hE

theorem outerDiagonal {u : G} (hu : IsOverlapInv Q u) :
    M.psi (toBar Q ⟨u, hu.mem_normalizer⟩) ∈ pGammaL2PGLRange M.F ∧
      M.psi (toBar Q ⟨u, hu.mem_normalizer⟩) ∉ pGammaL2PSLRange M.F := by
  refine Asc75T4KG.outerDiagonal_of_involution _ M.hF M.h3 M.e _ hu.bar_sq
    (hE.not_mem_layer_sup_centralizer hu) fun v w hv hw hv1 hw1 hvw hc hav haw => ?_
  have hmem : ∀ x : bar Q (twoPrimeLayerIn Q),
      toBar Q ⟨u, hu.mem_normalizer⟩ * x = x * toBar Q ⟨u, hu.mem_normalizer⟩ →
      (x : Bar Q) ∈ bar Q (twoPrimeLayerIn Q) ⊓
        centralizer ({toBar Q ⟨u, hu.mem_normalizer⟩} : Set (Bar Q)) := fun x hx =>
    mem_inf.mpr ⟨x.2, mem_centralizer_iff.mpr fun z hz => by
      rw [Set.mem_singleton_iff.mp hz]
      exact hx⟩
  exact AschbacherKnownGroup.FactsL2.not_hasCyclicSylowTwo_of_commuting_involutions _
    (hmem v hav) (hmem w haw) (congrArg Subtype.val hv) (congrArg Subtype.val hw)
    (fun h => hv1 (Subtype.ext h)) (fun h => hw1 (Subtype.ext h))
    (fun h => hvw (Subtype.ext h)) (congrArg Subtype.val hc)
    (hE.hasCyclicSylowTwo_of_isOverlapInv hu)

theorem sq_eq_one_of_isPGroup {g x : G} (hg : g ∉ normalizer (Q : Set G))
    (hxQg : x ∈ rightConjugate Q g) (hxN : x ∈ normalizer (Q : Set G))
    (hx : IsPGroup 2 (zpowers x)) : x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hx2
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hx ⟨x, mem_zpowers x⟩
  have hk' : orderOf x = 2 ^ k := (Subgroup.orderOf_coe (⟨x, mem_zpowers x⟩ : zpowers x)).trans hk
  have hk2 : 2 ≤ k := by
    by_contra hlt
    apply hx2
    rw [← orderOf_dvd_iff_pow_eq_one, hk']
    exact (Nat.pow_dvd_pow 2 (show k ≤ 1 by omega)).trans (by norm_num)
  set y := x ^ 2 ^ (k - 2) with hy
  have hy4 : orderOf y = 4 := by
    rw [hy, orderOf_pow_of_dvd (by positivity) (by rw [hk']; exact Nat.pow_dvd_pow 2 (by omega)),
      hk', Nat.pow_div (by omega) (by norm_num), show k - (k - 2) = 2 by omega]
  set u := y ^ 2 with hu
  have hu2 : orderOf u = 2 := by
    rw [hu, orderOf_pow_of_dvd (by norm_num) (by rw [hy4]; norm_num), hy4]
  have huN : u ∈ normalizer (Q : Set G) := pow_mem (pow_mem hxN _) _
  have hov : IsOverlapInv Q u := ⟨by rw [← hu2]; exact pow_orderOf_eq_one u,
    fun h => by rw [h, orderOf_one] at hu2; norm_num at hu2, huN, g, hg,
    pow_mem (pow_mem hxQg _) _⟩
  have hyN : y ∈ normalizer (Q : Set G) := pow_mem hxN _
  obtain ⟨h1, h2⟩ := M.outerDiagonal hE hov
  apply Asc75T4KG.sq_mul_inv_not_mem _ M.hF M.h3 M.e _ h1 h2 (toBar Q ⟨y, hyN⟩)
  have : toBar Q ⟨y, hyN⟩ ^ 2 = toBar Q ⟨u, hov.mem_normalizer⟩ := by
    rw [← map_pow]
    rfl
  rw [this, mul_inv_cancel]
  exact one_mem _

theorem exists_conj_eq_mul {t r : G} (ht : IsOverlapInv Q t) (hrQ : r ∈ Q)
    (hrL : toBar Q ⟨r, le_normalizer hrQ⟩ ∈ bar Q (twoPrimeLayerIn Q)) (hsq : (t * r) ^ 2 = 1) :
    ∃ q ∈ Q, q * t * q⁻¹ = t * r := by
  set tb := toBar Q ⟨t, ht.mem_normalizer⟩ with htb
  set rb := toBar Q ⟨r, le_normalizer hrQ⟩ with hrb
  set ψ := M.psi with hψ
  obtain ⟨hpgl, hpsl⟩ := M.outerDiagonal hE ht
  have hrpsl : ψ rb ∈ pGammaL2PSLRange M.F :=
    (M.mem_sup_centralizer_iff rb).mp (mem_sup_left hrL)
  have hprod_pgl : ψ (tb * rb) ∈ pGammaL2PGLRange M.F := by
    rw [map_mul]
    exact mul_mem hpgl (M.pslRange_le_pglRange hrpsl)
  have hprod_psl : ψ (tb * rb) ∉ pGammaL2PSLRange M.F := by
    intro h
    apply hpsl
    have h1 := mul_mem h (inv_mem hrpsl)
    rwa [map_mul, mul_inv_cancel_right] at h1
  obtain ⟨a, ha⟩ := hpgl
  obtain ⟨b, hb⟩ := hprod_pgl
  have hJ : commutator (PGL2 M.F) = AschbacherKnownGroup.FactsL2.pslRange M.F :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three M.F M.hF M.h3
  have hnotJ : ∀ c : PGL2 M.F, SemidirectProduct.inl c ∉ pGammaL2PSLRange M.F →
      c ∉ commutator (PGL2 M.F) := by
    intro c hc hcJ
    rw [hJ] at hcJ
    obtain ⟨y, rfl⟩ := hcJ
    exact hc ⟨y, rfl⟩
  have hinv : ∀ c : PGL2 M.F, ∀ z : Bar Q, SemidirectProduct.inl c = ψ z → z ^ 2 = 1 →
      SemidirectProduct.inl c ∉ pGammaL2PSLRange M.F →
      BenderSuzuki.PFAppendixIII.IsInvolution c := by
    intro c z hcz hz hc
    refine ⟨fun h1 => hc ?_, ?_⟩
    · rw [h1, map_one]
      exact one_mem _
    · have h2 : (SemidirectProduct.inl (c ^ 2) : PGammaL2 M.F) = SemidirectProduct.inl 1 := by
        rw [map_pow, hcz, ← map_pow, hz, map_one, map_one]
      exact SemidirectProduct.inl_injective h2
  have hsqb : (tb * rb) ^ 2 = 1 := by
    rw [htb, hrb, ← map_mul, ← map_pow]
    have : ((⟨t, ht.mem_normalizer⟩ : normalizer (Q : Set G)) * ⟨r, le_normalizer hrQ⟩) ^ 2 = 1 :=
      Subtype.ext (by simpa using hsq)
    rw [this, map_one]
  have hai := hinv a tb ha ht.bar_sq (ha ▸ hpsl)
  have hbi := hinv b (tb * rb) hb hsqb (hb ▸ hprod_psl)
  obtain ⟨c, hc⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate M.F M.hF M.h3 hai hbi
    (hnotJ a (ha ▸ hpsl)) (hnotJ b (hb ▸ hprod_psl)))
  obtain ⟨c', hc'J, hc'⟩ : ∃ c' : PGL2 M.F, c' ∈ AschbacherKnownGroup.FactsL2.pslRange M.F ∧
      c' * a * c'⁻¹ = b := by
    by_cases hcJ : c ∈ AschbacherKnownGroup.FactsL2.pslRange M.F
    · exact ⟨c, hcJ, hc⟩
    · refine ⟨c * a, ?_, ?_⟩
      · have haJ : a ∉ AschbacherKnownGroup.FactsL2.pslRange M.F := by
          rw [← hJ]
          exact hnotJ a (ha ▸ hpsl)
        exact (Subgroup.mul_mem_iff_of_index_two
          (AschbacherKnownGroup.FactsL2.pslRange_index_eq_two M.hF)).mpr
          ⟨fun h => absurd h hcJ, fun h => absurd h haJ⟩
      · have ha2 : a * a = 1 := by rw [← pow_two]; exact hai.2
        calc c * a * a * (c * a)⁻¹ = c * (a * a) * a⁻¹ * c⁻¹ := by group
          _ = c * a⁻¹ * c⁻¹ := by rw [ha2, mul_one]
          _ = c * a * c⁻¹ := by rw [inv_eq_of_mul_eq_one_right ha2]
          _ = b := hc
  obtain ⟨p, rfl⟩ := hc'J
  set l : bar Q (twoPrimeLayerIn Q) := M.e.symm p with hl
  have hψl : ψ (l : Bar Q) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL p) := by
    rw [hψ, M.psi_apply_of_mem, hl, MulEquiv.apply_symm_apply]
  have hconj : (l : Bar Q) * tb * (l : Bar Q)⁻¹ = tb * rb := by
    set w := ((l : Bar Q) * tb * (l : Bar Q)⁻¹)⁻¹ * (tb * rb) with hw
    have hwC : w ∈ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) := by
      rw [← M.psi_eq_one_iff, hw, map_mul, map_inv, map_mul, map_mul, map_inv, hψl, ← ha, ← hb,
        ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, hc', inv_mul_cancel, map_one]
    have hwL : w ∈ bar Q (twoPrimeLayerIn Q) := by
      have hLn := bar_twoPrimeLayerIn_normal Q
      have h1 : tb⁻¹ * (l : Bar Q)⁻¹ * tb ∈ bar Q (twoPrimeLayerIn Q) := by
        have := hLn.conj_mem _ (inv_mem l.2) tb⁻¹
        rwa [inv_inv] at this
      have : w = (l : Bar Q) * (tb⁻¹ * (l : Bar Q)⁻¹ * tb) * rb := by
        rw [hw]
        group
      rw [this]
      exact mul_mem (mul_mem l.2 h1) hrL
    have hw1 : w ∈ (⊥ : Subgroup (Bar Q)) := by
      rw [← hE.inf_centralizer_bar_eq_bot]
      exact mem_inf.mpr ⟨bar_mono Q (twoPrimeLayerIn_le Q) hwL, hwC⟩
    rw [mem_bot, hw, inv_mul_eq_one] at hw1
    exact hw1
  obtain ⟨k, hkK, hkl⟩ := (mem_bar_iff Q _ _).mp l.2
  have hkQ : (k : G) ∈ Q := twoPrimeLayerIn_le Q hkK
  set s : G := (k : G) * t * (k : G)⁻¹ with hs
  set o : G := s⁻¹ * (t * r) with ho
  have hoO : o ∈ oddCoreIn Q := by
    have h1 : toBar Q ((k * ⟨t, ht.mem_normalizer⟩ * k⁻¹)⁻¹ *
        (⟨t, ht.mem_normalizer⟩ * ⟨r, le_normalizer hrQ⟩)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, map_mul, hkl, ← htb, ← hrb, hconj,
        inv_mul_cancel]
    rw [toBar_eq_one_iff] at h1
    exact h1
  have hss : s ^ 2 = 1 := by
    rw [hs, conj_pow, ht.1]
    group
  have hso : (s * o) ^ 2 = 1 := by
    rw [ho, mul_inv_cancel_left]
    exact hsq
  have hoodd : Odd (orderOf o) := by
    have h := orderOf_dvd_natCard (⟨o, hoO⟩ : oddCoreIn Q)
    rw [Subgroup.orderOf_mk] at h
    exact (odd_card_oddCoreIn Q).of_dvd_nat h
  obtain ⟨m, hm⟩ := exists_zpow_conj_eq_mul_of_odd hss hso hoodd
  refine ⟨o ^ (-m) * k, mul_mem (zpow_mem (oddCoreIn_le Q hoO) _) hkQ, ?_⟩
  calc o ^ (-m) * k * t * (o ^ (-m) * k)⁻¹ = o ^ (-m) * s * o ^ m := by
        rw [hs, mul_inv_rev, zpow_neg, inv_inv]
        group
    _ = s * o := hm
    _ = t * r := by rw [ho, mul_inv_cancel_left]

end PSLModel

end CFSG.ComponentClassification.Asc75T4
