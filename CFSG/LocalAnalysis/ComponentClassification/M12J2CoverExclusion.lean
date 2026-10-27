module

public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionAssemblyDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBPrimeLifts
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStar
import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
import CFSG.Sporadic.J2
import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.ComponentClassification.StandardRecognition

open Subgroup CFSG.Assembly

@[expose] def IsM12OrJ2Quotient {X : Type} [Group X] (L : Subgroup X) : Prop :=
  Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) .M12 ∨
    Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) .J2

@[expose] def M12J2LocalKernel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → ∀ L : Subgroup G, Assembly.ComponentType.IsStandardSubgroup L →
    (∀ x : G, orderOf x = 2 → Assembly.oddCore (centralizer ({x} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G))) →
    ∀ t : G, orderOf t = 2 → (center L).map L.subtype = zpowers t → IsM12OrJ2Quotient L →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t

@[expose] def M12J2LocalInvolutionData : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H) (t : H), L.Normal →
    Assembly.IsQuasisimple L → orderOf t = 2 → (center L).map L.subtype = zpowers t →
    IsM12OrJ2Quotient L → centralizer (L : Set H) = zpowers t →
    L.index ≤ 2 ∧
    (∃ T : Sylow 2 H,
      (∀ φ : MulAut (T : Subgroup H), ∀ x : (T : Subgroup H), (x : H) = t → φ x = x) ∧
      ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L, ∃ z ∈ center (T : Subgroup H),
        (z : H) = k⁻¹ * u * k) ∧
    (∀ x y : H, x ∉ L → orderOf x = 2 → y ∉ L → orderOf y = 2 → ∃ h : H, h⁻¹ * x * h = y) ∧
    ∀ p : H, p ∉ L → orderOf p = 2 → ∃ A : Subgroup H, A ≤ L ∧
      zpowers t ⊔ A = L ⊓ centralizer ({p} : Set H) ∧ zpowers t ⊓ A = ⊥ ∧
      (∀ a ∈ A, a * t = t * a) ∧ _root_.commutator A = ⊤ ∧ Even (Nat.card A) ∧
      ¬ 3 ∣ Nat.card (OuterAutomorphisms.Outer A)

section Transport

variable {G : Type} [Group G] {C L : Subgroup G}

private theorem isQuasisimple_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : Assembly.IsQuasisimple A) : Assembly.IsQuasisimple B :=
  h.of_mulEquiv e.symm

private theorem isSporadic_quotient_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {s : TauCeti.SporadicName}
    (h : Blueprint.NativeSporadic.IsSporadic (A ⧸ center A) s) :
    Blueprint.NativeSporadic.IsSporadic (B ⧸ center B) s := by
  obtain ⟨f⟩ := h
  exact ⟨(QuotientGroup.congr (center A) (center B) e (map_center_eq e)).symm.trans f⟩

private theorem map_subtype_centralizer_singleton (p : C) :
    (centralizer ({p} : Set C)).map C.subtype = centralizer ({(p : G)} : Set G) ⊓ C := by
  ext x
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨congrArg Subtype.val hy, y.2⟩
  · rintro ⟨hx, hxC⟩
    exact ⟨⟨x, hxC⟩, Subtype.ext hx, rfl⟩

private theorem mem_zpowers_coe_iff (t x : C) : x ∈ zpowers t ↔ (x : G) ∈ zpowers (t : G) := by
  rw [← (Subgroup.mem_map_iff_mem (subtype_injective C)), MonoidHom.map_zpowers]
  rfl

private theorem commutator_eq_top_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : _root_.commutator A = ⊤) : _root_.commutator B = ⊤ := by
  have hP : Group.IsPerfect A := (Group.isPerfect_def).2 h
  exact (Group.isPerfect_def).1 (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

end Transport

theorem m12J2DoubleCoverExclusion_of_local (hK : M12J2LocalKernel)
    (hD : M12J2LocalInvolutionData) : M12J2DoubleCoverExclusion := by
  intro G _ _ _ hnonab hKP L hL hcore S hS hZ2 hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (center L) := isCyclic_of_prime_card hZ2
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := center L)
  have hgtop : zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
  have hg2 : orderOf g = 2 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hZ2]
  set t : G := ((g : L) : G) with ht_def
  have ht2 : orderOf t = 2 := by
    rw [ht_def, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg2]
  have hZt : (center L).map L.subtype = zpowers t := by
    have hc : center L = (zpowers g).map (center L).subtype := by
      rw [hgtop, ← MonoidHom.range_eq_map, range_subtype]
    rw [hc, map_map, MonoidHom.map_zpowers]
    rfl
  have htL : t ∈ L := (g : L).2
  have htCL : t ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (mem_center_iff.mp g.2 ⟨l, hl⟩)
  obtain ⟨-, hLC, hLn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL htCL ht2
  have hker := hK G hnonab hKP L hL hcore S hS t ht2 hZt hQ
  set C : Subgroup G := centralizer ({t} : Set G) with hC
  have htC : t ∈ C := mem_centralizer_singleton_iff.mpr rfl
  set t' : C := ⟨t, htC⟩
  set L' : Subgroup C := L.subgroupOf C
  let e : L' ≃* L := subgroupOfEquivOfLe hLC
  have hLq' : Assembly.IsQuasisimple L' := isQuasisimple_of_mulEquiv e.symm hL.1
  have ht2' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk, ht2]
  have hmemL' : ∀ x : C, x ∈ L' ↔ (x : G) ∈ L := fun x => mem_subgroupOf
  have hZt' : (center L').map L'.subtype = zpowers t' := by
    ext x
    have hxz : x ∈ zpowers t' ↔ (x : G) ∈ zpowers t := mem_zpowers_coe_iff t' x
    rw [hxz, ← hZt]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨e y, ?_, rfl⟩
      rw [← map_center_eq e]
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨e.symm y, ?_, Subtype.ext ?_⟩
      · rw [← map_center_eq e.symm]
        exact ⟨y, hy, rfl⟩
      · exact hyx
  have hQ' : IsM12OrJ2Quotient L' :=
    hQ.imp (isSporadic_quotient_of_mulEquiv e.symm) (isSporadic_quotient_of_mulEquiv e.symm)
  have hCL' : centralizer (L' : Set C) = zpowers t' := by
    ext x
    have hxz : x ∈ zpowers t' ↔ (x : G) ∈ zpowers t := mem_zpowers_coe_iff t' x
    rw [hxz, ← hker, mem_inf, mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨fun l hl => ?_, x.2⟩
      exact congrArg Subtype.val (h ⟨l, hLC hl⟩ ((hmemL' _).mpr hl))
    · rintro ⟨h, -⟩ l hl
      exact Subtype.ext (h l ((hmemL' l).mp hl))
  obtain ⟨hidx, ⟨T, hfix, hcent⟩, hext, hA⟩ :=
    hD C L' t' hLn hLq' ht2' hZt' hQ' hCL'
  obtain ⟨-, -, hfact, -⟩ :=
    rigid_index_two_centralizer_perfect_data_give_zStar ht2 hLC htL hidx T
      (fun φ x hx => hfix φ x (Subtype.ext hx))
      (fun u hu hu2 => by
        obtain ⟨k, hk, z, hz, hzk⟩ :=
          hcent ⟨u, hLC hu⟩ ((hmemL' _).mpr hu) (by rw [Subgroup.orderOf_mk, hu2])
        exact ⟨k, (hmemL' k).mp hk, z, hz, congrArg Subtype.val hzk⟩)
      (fun x y hx hxL hx2 hy hyL hy2 => by
        obtain ⟨h, hh⟩ := hext ⟨x, hx⟩ ⟨y, hy⟩ (fun h => hxL ((hmemL' _).mp h))
          (by rw [Subgroup.orderOf_mk, hx2]) (fun h => hyL ((hmemL' _).mp h))
          (by rw [Subgroup.orderOf_mk, hy2])
        exact ⟨h, h.2, congrArg Subtype.val hh⟩)
      (fun p hp hpL hp2 => by
        obtain ⟨A, -, hAsup, -, -, hAperf, hAeven, -⟩ :=
          hA ⟨p, hp⟩ (fun h => hpL ((hmemL' _).mp h)) (by rw [Subgroup.orderOf_mk, hp2])
        refine ⟨A.map C.subtype, ?_, ?_, ?_⟩
        · have h1 := congrArg (Subgroup.map C.subtype) hAsup
          rw [Subgroup.map_sup, MonoidHom.map_zpowers,
            Subgroup.map_inf_eq _ _ _ (subtype_injective C), map_subtype_centralizer_singleton,
            subgroupOf_map_subtype] at h1
          refine h1.trans ?_
          rw [inf_of_le_left hLC, ← inf_assoc, inf_right_comm, inf_of_le_left hLC]
        · exact commutator_eq_top_of_mulEquiv
            (A.equivMapOfInjective C.subtype (subtype_injective C)) hAperf
        · rwa [Nat.card_congr (A.equivMapOfInjective C.subtype
            (subtype_injective C)).toEquiv.symm])
  have hodd : CFSG.oddCore G = ⊥ := by
    refine sSup_eq_bot.mpr fun N ⟨hN, hNodd⟩ => ?_
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      have h2 : 2 ∣ Nat.card N := by
        rw [h, card_top, ← ht2]
        exact orderOf_dvd_natCard t
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)
  have htZ : t ∈ center G := by
    rw [mem_center_iff]
    intro x
    obtain ⟨c, hc, k, hk, rfl⟩ := hfact x
    rw [hodd, mem_bot] at hk
    subst hk
    rw [mul_one]
    exact (mem_centralizer_singleton_iff.mp hc)
  have hZbot : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab ((mem_center_iff.mp (h ▸ mem_top a : a ∈ center G) b).symm)
  rw [hZbot, mem_bot] at htZ
  rw [htZ, orderOf_one] at ht2
  exact absurd ht2 (by norm_num)

@[expose] def M12J2PairDisplacement : Prop :=
  ∀ s : TauCeti.SporadicName, (s = .M12 ∨ s = .J2) →
    ∃ x y : Blueprint.NativeSporadic.Carrier s, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y ∧
      x * y = y * x ∧
      ∀ (E : Type) [Group E] [Finite E], Assembly.IsQuasisimple E → ∀ t : E, orderOf t = 2 →
        center E = zpowers t → ∀ ρ : E →* Blueprint.NativeSporadic.Carrier s,
          Function.Surjective ρ → ρ.ker = zpowers t →
          ∀ X Y : E, ρ X = x → ρ Y = y → X⁻¹ * Y⁻¹ * X * Y = t

private theorem center_eq_bot_of_not_prime {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : ¬ (Nat.card Q).Prime) : center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative Q :=
      ⟨⟨fun a b => (mem_center_iff.mp (h ▸ mem_top b : b ∈ center Q) a)⟩⟩
    exact hQ (Group.is_simple_iff_prime_card.mp inferInstance)

private theorem carrier_center_eq_bot {s : TauCeti.SporadicName} (hs : s = .M12 ∨ s = .J2) :
    IsSimpleGroup (Blueprint.NativeSporadic.Carrier s) ∧
      center (Blueprint.NativeSporadic.Carrier s) = ⊥ := by
  rcases hs with rfl | rfl
  · obtain ⟨hfin, -, hsimp⟩ := CFSG.Sporadic.Mathieu.fam_m12_simplicity
    refine ⟨hsimp, @center_eq_bot_of_not_prime _ _ hfin hsimp ?_⟩
    change ¬ (Nat.card Blueprint.NativeSporadic.M12).Prime
    rw [CFSG.Sporadic.Mathieu.card_M12]
    norm_num
  · obtain ⟨hfin, -, hsimp⟩ := CFSG.Sporadic.J2.fam_j2_simplicity
    refine ⟨hsimp, @center_eq_bot_of_not_prime _ _ hfin hsimp ?_⟩
    change ¬ (Nat.card Blueprint.NativeSporadic.J2).Prime
    rw [CFSG.Sporadic.J2.card_J2]
    norm_num

theorem m12J2CentralTwoGroupOrderBound_of_displacement (hD : M12J2PairDisplacement) :
    M12J2CentralTwoGroupOrderBound := by
  intro L _ _ hLq h2 hQ
  have key : ∀ s : TauCeti.SporadicName, (s = .M12 ∨ s = .J2) →
      Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) s → Nat.card (center L) ≤ 2 := by
    rintro s hs ⟨e⟩
    obtain ⟨hsimp, hZ⟩ := carrier_center_eq_bot hs
    obtain ⟨x, y, hx2, -, -, hxy, hdisp⟩ := hD s hs
    let π : L →* Blueprint.NativeSporadic.Carrier s :=
      e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    have hπ : Function.Surjective π :=
      e.surjective.comp (QuotientGroup.mk'_surjective (center L))
    have hker : π.ker = center L := by
      ext l
      simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have : Group.IsPerfect L := (Group.isPerfect_def).2 hLq.1
    obtain ⟨U, hU⟩ := hπ x
    obtain ⟨V, hV⟩ := hπ y
    have huniv : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
        (ρ : E →* Blueprint.NativeSporadic.Carrier s), Function.Surjective ρ →
        ρ.ker ≤ center E → Nat.card ρ.ker = 2 →
        ∀ X Y : E, ρ X = x → ρ Y = y → X⁻¹ * Y⁻¹ * X * Y ≠ 1 := by
      intro E _ _ hEp ρ hρ hρZ hρ2 X Y hX hY
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : IsCyclic ρ.ker := isCyclic_of_prime_card hρ2
      obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := ρ.ker)
      have hktop : zpowers k = ⊤ := eq_top_iff.mpr fun x _ => hk x
      have hkt : ρ.ker = zpowers (k : E) := by
        have hc : (zpowers k).map ρ.ker.subtype = ρ.ker := by
          rw [hktop, ← MonoidHom.range_eq_map, range_subtype]
        rw [MonoidHom.map_zpowers] at hc
        exact hc.symm
      have hk2 : orderOf (k : E) = 2 := by
        rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hk, hρ2]
      have hZE : center E = zpowers (k : E) := by
        refine le_antisymm ?_ (hkt ▸ hρZ)
        intro z hz
        rw [← hkt, MonoidHom.mem_ker]
        have hzQ : ρ z ∈ center (Blueprint.NativeSporadic.Carrier s) := by
          rw [mem_center_iff]
          intro q
          obtain ⟨w, rfl⟩ := hρ q
          rw [← map_mul, ← map_mul, mem_center_iff.mp hz w]
        rwa [hZ, mem_bot] at hzQ
      have hEq : Assembly.IsQuasisimple E := by
        refine ⟨(Group.isPerfect_def).1 hEp, ?_⟩
        have he : E ⧸ center E ≃* Blueprint.NativeSporadic.Carrier s :=
          (QuotientGroup.quotientMulEquivOfEq (hZE.trans hkt.symm)).trans
            (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
        exact he.isSimpleGroup
      rw [hdisp E hEq (k : E) hk2 hZE ρ hρ hkt X Y hX hY]
      intro h
      rw [h, orderOf_one] at hk2
      exact absurd hk2 (by norm_num)
    have h2' : IsPGroup 2 π.ker := by rw [hker]; exact h2
    obtain ⟨-, hcard⟩ :=
      CentralCover.universal_noncommuting_prime_lifts_bound_central_p_kernels
        Nat.prime_two hx2 hxy huniv π hπ hker.le h2' hU hV
    rwa [hker] at hcard
  rcases hQ with h | h
  · exact key .M12 (.inl rfl) h
  · exact key .J2 (.inr rfl) h

end CFSG.ComponentClassification.StandardRecognition
