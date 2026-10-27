module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitHypothesisI
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralDerivedInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionTwoGroup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

open SectionSix AschbacherToolkit

theorem pRank_top_le_one_of_atMostOne {P : Type} [Group P] [Finite P]
    (hP : AtMostOneInvolution P) : CFSG.Open.pRank 2 (⊤ : Subgroup P) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 2) (H := (⊤ : Subgroup P)) (k := 2) (by omega)
  have hsub : ¬ (E : Set P) ⊆ {1, (1 : P)} := by
    intro h
    have := card_le_two_of_subset h
    rw [hcard] at this
    norm_num at this
  obtain ⟨x, hx, hxne⟩ := Set.not_subset.mp hsub
  have hx1 : x ≠ 1 := fun h => hxne (Or.inl h)
  have hsub2 : ¬ (E : Set P) ⊆ {1, x} := by
    intro h
    have := card_le_two_of_subset h
    rw [hcard] at this
    norm_num at this
  obtain ⟨y, hy, hyne⟩ := Set.not_subset.mp hsub2
  have hy1 : y ≠ 1 := fun h => hyne (Or.inl h)
  have hyx : y ≠ x := fun h => hyne (Or.inr h)
  exact hyx (hP y x (orderOf_eq_prime (hE.2 y hy) hy1) (orderOf_eq_prime (hE.2 x hx) hx1))

theorem false_of_fixed_central {X : Type} [Group X] [Finite X] (hX : Group.IsPerfect X)
    (α : MulAut X) (hα : α ^ 2 = 1) (P : Sylow 2 X)
    (hPα : (P : Subgroup X).map (α : X →* X) = P) (Z : Subgroup X)
    (hZc : Z ≤ Subgroup.center X) (hZP : Z ≤ (P : Subgroup X))
    (hZα : Z.map (α : X →* X) = Z) (hZcyc : IsCyclic Z) (hZne : Z ≠ ⊥)
    (hfix : ∀ p ∈ (P : Subgroup X), α p = p → p ∈ Z) {s u : X}
    (hsP : s ∈ (P : Subgroup X)) (huP : u ∈ (P : Subgroup X)) (hs : orderOf s = 2)
    (hu : orderOf u = 2) (hsu : s ≠ u) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Z.Normal := Subgroup.normal_of_le_center hZc
  set π := QuotientGroup.mk' Z with hπ
  set Pb : Subgroup (X ⧸ Z) := (P : Subgroup X).map π with hPb
  have hPbα := map_mk_congr_eq α Z hZα P hPα
  have hβ₁2 := restrictAut_sq (QuotientGroup.congr Z Z α hZα) (quotient_congr_sq α hα Z hZα)
    Pb hPbα
  have hβ₁fix := card_fixedSubgroup_quotient_le_two α hα Z P hZc hZP hZα hZcyc hfix hPbα
  have hPb2 : IsPGroup 2 Pb := P.isPGroup'.map π
  let f : (P : Subgroup X) →* Pb := π.subgroupMap (P : Subgroup X)
  have hf : Function.Surjective f := π.subgroupMap_surjective _
  have hfker : f.ker = Z.subgroupOf (P : Subgroup X) := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : π p = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff (p : X)).mp h'
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (p : X)).mpr h
  have hfkerc : f.ker ≤ Subgroup.center (P : Subgroup X) := by
    rw [hfker]
    intro p hp
    rw [Subgroup.mem_subgroupOf] at hp
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZc hp) q)
  have h8 := central_sylow_commutator P hZc (P.isPGroup'.to_le hZP)
  rw [show commutator X = ⊤ from hX.commutator_eq_top, inf_top_eq] at h8
  have hZD : f.ker ≤ commutator (P : Subgroup X) := by
    rw [hfker]
    intro p hp
    rw [Subgroup.mem_subgroupOf] at hp
    have hpZ : (p : X) ∈ Z ⊓ (commutator (P : Subgroup X)).map (P : Subgroup X).subtype :=
      h8 ▸ hp
    obtain ⟨-, q, hq, hqp⟩ := hpZ
    rwa [← Subtype.ext hqp]
  have hkerne : f.ker ≠ ⊥ := by
    rw [hfker]
    intro hbot
    apply hZne
    rw [eq_bot_iff]
    intro z hz
    have : (⟨z, hZP hz⟩ : (P : Subgroup X)) ∈ Z.subgroupOf (P : Subgroup X) := hz
    rw [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  rcases involutory_automorphism_shape hPb2 _ hβ₁2 hβ₁fix with hA | hB
  ·
    have hr := pRank_top_le_one_of_atMostOne hA
    rcases cyclic_or_quaternion_of_pRank_le_one (X := Pb) (P := ⊤) (hPb2.to_subgroup ⊤) hr
      with hcyc | ⟨n, hn, ⟨e⟩⟩
    · have : IsCyclic Pb := isCyclic_of_surjective Subgroup.topEquiv.toMonoidHom
        Subgroup.topEquiv.surjective
      have hcomm := cyclic_central_extension f hfkerc
      apply hkerne
      rw [eq_bot_iff, ← hcomm]
      exact hZD
    · set m := 2 ^ (n - 2)
      have : NeZero m := ⟨by positivity⟩
      let g := (e.toMonoidHom.comp Subgroup.topEquiv.symm.toMonoidHom).comp f
      have hg : Function.Surjective g :=
        (e.surjective.comp Subgroup.topEquiv.symm.surjective).comp hf
      have hgker : g.ker = f.ker := by
        ext p
        rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
        change e (Subgroup.topEquiv.symm (f p)) = 1 ↔ f p = 1
        rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
      have hgc : g.ker ≤ Subgroup.center (P : Subgroup X) := hgker ▸ hfkerc
      have hq := quaternion_central_extension_of_surjective g hg hgc
      apply hkerne
      rw [← hgker, eq_bot_iff, ← hq]
      exact le_inf le_rfl (hgker ▸ hZD)
  ·
    have hext := dihedral_central_extension_card_le f hf hfkerc hB
    have hZcard : Nat.card Z ≤ 2 := by
      rw [inf_of_le_left hZD, hfker] at hext
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv] at hext
    have hβ₂2 := restrictAut_sq α hα _ hPα
    have hβ₂fix : Nat.card (fixedSubgroup (restrictAut α (P : Subgroup X) hPα)) ≤ 2 := by
      have hle : (fixedSubgroup (restrictAut α (P : Subgroup X) hPα)).map
          (P : Subgroup X).subtype ≤ Z := by
        rintro _ ⟨p, hp, rfl⟩
        exact hfix p p.2 (congrArg Subtype.val ((mem_fixedSubgroup).mp hp))
      calc Nat.card (fixedSubgroup (restrictAut α (P : Subgroup X) hPα))
          = Nat.card ((fixedSubgroup (restrictAut α (P : Subgroup X) hPα)).map
              (P : Subgroup X).subtype) :=
            (Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective).symm
        _ ≤ Nat.card Z := Subgroup.card_le_of_le hle
        _ ≤ 2 := hZcard
    rcases involutory_automorphism_shape P.isPGroup' _ hβ₂2 hβ₂fix with hPA | hPB
    · apply hsu
      have := hPA ⟨s, hsP⟩ ⟨u, huP⟩ (by rw [Subgroup.orderOf_mk]; exact hs)
        (by rw [Subgroup.orderOf_mk]; exact hu)
      exact congrArg Subtype.val this
    ·
      obtain ⟨x, y, hgen, hy2, hyx, hy⟩ := hPB
      obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem x y hgen.symm hy2 hyx hy
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') x
      have hk1 : 1 ≤ k := by
        by_contra hk0
        have hk0' : k = 0 := by omega
        rw [hk0', pow_zero, orderOf_eq_one_iff] at hk
        apply hsu
        have hPy : ∀ p : (P : Subgroup X), p ∈ Subgroup.zpowers y := by
          intro p
          have hp : p ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := hgen ▸ Subgroup.mem_top p
          rwa [hk, Subgroup.zpowers_one_eq_bot, bot_sup_eq] at hp
        have hy1 : y ≠ 1 := fun h1 => hy (h1 ▸ Subgroup.one_mem _)
        have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
        have hinv : ∀ p : (P : Subgroup X), orderOf p = 2 → p = y := by
          intro p hp
          rcases CFSG.RankTwoShapes.eq_one_or_eq_of_mem_zpowers hyo (hPy p) with h1 | h1
          · rw [h1, orderOf_one] at hp
            omega
          · exact h1
        have h1 := hinv ⟨s, hsP⟩ (by rw [Subgroup.orderOf_mk]; exact hs)
        have h2 := hinv ⟨u, huP⟩ (by rw [Subgroup.orderOf_mk]; exact hu)
        exact congrArg Subtype.val (h1.trans h2.symm)
      have hn : 2 ≤ k + 1 := by omega
      have e' : (P : Subgroup X) ≃* DihedralGroup (2 ^ (k + 1 - 1)) := by
        rw [Nat.add_sub_cancel, ← hk]
        exact e
      obtain ⟨-, -, -, -, hconj⟩ :=
        CFSG.Semidihedral.Principal.dihedral_derived_involutions_conjugate P hn ⟨e'.symm⟩
      have hall := hconj hX.commutator_eq_top
      obtain ⟨z, hzZ, hz2⟩ := exists_orderOf_eq_two_of_isPGroup (P.isPGroup'.to_le hZP) hZne
      have hcentral : ∀ w : X, orderOf w = 2 → w = z := by
        intro w hw
        obtain ⟨c, hc⟩ := isConj_iff.mp (hall w z hw hz2)
        have hzc : c⁻¹ * z = z * c⁻¹ := (Subgroup.mem_center_iff.mp (hZc hzZ) c⁻¹)
        calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
          _ = c⁻¹ * z * c := by rw [hc]
          _ = z := by rw [hzc]; group
      exact hsu ((hcentral s hs).trans (hcentral u hu).symm)

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem pRank_preimage_le (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    CFSG.Open.pRank 2 (aschbacherThm5Preimage D Ā) ≤ CFSG.Open.pRank 2 Ā := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEA, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two
    (aschbacherThm5Preimage D Ā)
  have hED : E ≤ D := hEA.trans (preimage_le D Ā)
  set E' := E.subgroupOf D
  have hE'2 : IsPGroup 2 E' := (IsPGroup.of_card hcard).comap_subtype
  set f := QuotientGroup.mk' (aschbacherThm5OddCore D)
  have hcardE' : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv
  have hdisj : aschbacherThm5OddCore D ⊓ E' = ⊥ := by
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    rw [hcardE', hcard]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_left.mpr (oddCore_odd D)).symm
  have hmap : Nat.card (E'.map f) = Nat.card E' := by
    have h1 := Subgroup.relIndex_mul_card (aschbacherThm5OddCore D) E'
    have h2 := Subgroup.relIndex_ker E' f
    rw [QuotientGroup.ker_mk'] at h2
    rw [h2, hdisj, Subgroup.card_bot, mul_one] at h1
    exact h1
  refine CFSG.SectionRank.le_pRank one_lt_two (E := E'.map f) ?_
    (CFSG.SectionRank.isElemAbelian_map ?_ f) ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact (mem_preimage_iff D Ā d).mp (hEA (Subgroup.mem_subgroupOf.mp hd))
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have hc := hE.1
      have := congrArg Subtype.val (mul_comm' (⟨(a : D), a.2⟩ : E) ⟨(b : D), b.2⟩)
      exact Subtype.ext this
    · have := hE.2 _ hx
      rw [Subgroup.coe_pow]
      exact this
  · rw [hmap, hcardE', hcard]

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5
