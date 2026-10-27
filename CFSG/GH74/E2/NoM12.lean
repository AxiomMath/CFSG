module

public import CFSG.GH74.E2.NoM12Local
public import CFSG.GH74.AS16.E2.Pump2
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverRigid
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternal
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernel
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverRigid
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternal
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.E2.NoM12

open Subgroup CFSG.Assembly CFSG.ComponentClassification.StandardRecognition CFSG.ComponentClassification

@[expose] def LocalKernelNoK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ L : Subgroup G, CFSG.Assembly.ComponentType.IsStandardSubgroup L →
    (∀ x : G, orderOf x = 2 → CFSG.Assembly.oddCore (centralizer ({x} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G))) →
    ∀ t : G, orderOf t = 2 → (center L).map L.subtype = zpowers t →
    CFSG.Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) .M12 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t

section Transport

variable {G : Type} [Group G] {C L : Subgroup G}

private theorem isQuasisimple_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Assembly.IsQuasisimple A) : CFSG.Assembly.IsQuasisimple B :=
  h.of_mulEquiv e.symm

private theorem isSporadic_quotient_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {s : TauCeti.SporadicName}
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (A ⧸ center A) s) :
    CFSG.Blueprint.NativeSporadic.IsSporadic (B ⧸ center B) s := by
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

theorem localKernelNoK :
    LocalKernelNoK := by
  intro G _ _ _ hnonab L hL hcore S hS t ht hZ hQ
  classical
  have htL : t ∈ L := by
    have h : t ∈ (center L).map L.subtype := by rw [hZ]; exact mem_zpowers t
    obtain ⟨z, -, rfl⟩ := h
    exact z.2
  have htC : t ∈ centralizer (L : Set G) := by
    have h : t ∈ (center L).map L.subtype := by rw [hZ]; exact mem_zpowers t
    obtain ⟨z, hz, hzt⟩ := h
    rw [mem_centralizer_iff]
    intro l hl
    rw [← hzt]
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)
  have ht₁ : orderOf (⟨t, htC⟩ : centralizer (L : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk, ht]
  have ht₁S : (⟨t, htC⟩ : centralizer (L : Set G)) ∈ S :=
    mem_sylow_of_mem_center_of_orderOf_eq_two
      (mem_center_iff.mpr fun x => Subtype.ext (mem_centralizer_iff.mp x.2 t htL).symm) ht₁ S
  obtain ⟨-, -, -, -, -, -, hCH, -, -⟩ :=
    standard_cyclic_local_centralizer_kernel hL S hS ht₁S ht₁ (hcore t ht)
  have hCH' : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) =
      (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype := hCH
  by_cases hS4 : 4 ≤ Nat.card S
  · exact (M12Cover.ctss_m12_original_large_cyclic_kernel_false hnonab hL hcore S hS ht hZ hQ hS4).elim
  · rw [hCH']
    have htT : t ∈ (S : Subgroup (centralizer (L : Set G))).map
        (centralizer (L : Set G)).subtype := ⟨_, ht₁S, rfl⟩
    have hcard : Nat.card ((S : Subgroup (centralizer (L : Set G))).map
        (centralizer (L : Set G)).subtype) = Nat.card S :=
      card_map_of_injective (subtype_injective _)
    have h2 : 2 ∣ Nat.card ((S : Subgroup (centralizer (L : Set G))).map
        (centralizer (L : Set G)).subtype) := by
      have h := orderOf_dvd_natCard _ htT
      rwa [ht] at h
    have hpos : 0 < Nat.card S := Nat.card_pos
    refine (eq_of_le_of_card_ge (zpowers_le.mpr htT) ?_).symm
    rw [Nat.card_zpowers, ht]
    omega


theorem exclusion_of_local (hK : LocalKernelNoK) (hD : M12J2LocalInvolutionData)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (L : Subgroup G) (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hcore : ∀ x : G, orderOf x = 2 → CFSG.Assembly.oddCore (centralizer ({x} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (hZ2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) .M12) : False := by
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
  have hker := hK G hnonab L hL hcore S hS t ht2 hZt hQ
  set C : Subgroup G := centralizer ({t} : Set G) with hC
  have htC : t ∈ C := mem_centralizer_singleton_iff.mpr rfl
  set t' : C := ⟨t, htC⟩
  set L' : Subgroup C := L.subgroupOf C
  let e : L' ≃* L := subgroupOfEquivOfLe hLC
  have hLq' : CFSG.Assembly.IsQuasisimple L' := isQuasisimple_of_mulEquiv e.symm hL.1
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
  have hQ' : IsM12OrJ2Quotient L' := Or.inl (isSporadic_quotient_of_mulEquiv e.symm hQ)
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


theorem oddCore_eq_pPrimeCore_two (H : Type*) [Group H] :
    CFSG.Assembly.oddCore H = CFSG.pPrimeCore 2 H := by
  unfold CFSG.Assembly.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem exclusion_noKProper
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (L : Subgroup G)
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hcore : ∀ x : G, orderOf x = 2 → CFSG.Assembly.oddCore (centralizer ({x} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (hZ2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) .M12) : False :=
  exclusion_of_local localKernelNoK
    (m12J2LocalInvolutionData_of_data M12Cover.internalSylowData_M12 J2Cover.internalSylowData_J2
      M12Cover.ctss_m12_central_double_cover_external_data_from_fusion_and_section
      J2Cover.ctss_j2_central_double_cover_external_involution_data_frontier)
    G hnonab L hL hcore S hS hZ2 hQ

open CFSG.GH74.E2 hiding Hyp in
theorem noComponent2M12_of
    (hComp : ComponentList) : CFSG.GH74.AS16.E2.NoComponent2M12 := by
  intro G _ _ hH w hw K hK hsh
  have huniq : ∀ K₁ K₂ : Subgroup G, IsCompCen w K₁ → IsCompCen w K₂ → K₁ = K₂ :=
    fun K₁ K₂ h1 h2 => ((hComp G hH w hw K₁ h1).2 K₂ h2).symm
  have := hH.simple
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥(centralizer (K : Set G))))
  have := isCyclic_centralizer hH hw huniq hK hsh
  exact exclusion_noKProper G hH.nonabelian K (isStandardSubgroup hH hw huniq hK hsh)
    (fun x hx => by rw [oddCore_eq_pPrimeCore_two]; exact hH.pPrimeCore_cen_bot hx) S
    inferInstance hsh.2.1 hsh.2.2

end CFSG.GH74.E2.NoM12
