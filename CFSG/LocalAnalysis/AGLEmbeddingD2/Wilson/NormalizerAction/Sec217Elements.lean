module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217KSym
public import CFSG.RankThree.PartOne.S12.Sec12TwoAssembly

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.SectionRank.Native
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

theorem pgl_pow_four_not_mem_centralizer {X : Type*} [Group X] {H I : Subgroup X}
    (hP : IsPGL29 H I) {u : X} (huH : u ∈ H) (hu8 : orderOf u = 8) :
    u ^ 4 ∉ Subgroup.centralizer (I : Set X) := by
  obtain ⟨hIH, ⟨e⟩, hnorm, hidx, -, -⟩ := hP
  intro hc
  have h2 : (⟨u, huH⟩ : ↥H) ^ 2 ∈ I.subgroupOf H := Subgroup.sq_mem_of_index_two hidx _
  have h2' : u ^ 2 ∈ I := Subgroup.mem_subgroupOf.1 h2
  have h4 : u ^ 4 ∈ I := by
    have := I.pow_mem h2' 2
    rwa [← pow_mul] at this
  have hcen : (⟨u ^ 4, h4⟩ : ↥I) ∈ Subgroup.center ↥I := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_centralizer_iff.1 hc (y : X) y.2
    exact Subtype.ext this
  rw [center_eq_bot_of_equiv_alt6 I e, Subgroup.mem_bot] at hcen
  have h1 : u ^ 4 = 1 := congrArg Subtype.val hcen
  have := orderOf_dvd_of_pow_eq_one h1
  rw [hu8] at this
  omega

theorem mem_normalizer_of_normal_subgroupOf {X : Type*} [Group X] {H I : Subgroup X}
    (hIH : I ≤ H) (hnorm : (I.subgroupOf H).Normal) {u : X} (huH : u ∈ H) :
    u ∈ Subgroup.normalizer (I : Set X) := by
  have key : ∀ w ∈ H, ∀ x ∈ I, w * x * w⁻¹ ∈ I := by
    intro w hw x hx
    have := hnorm.conj_mem ⟨x, hIH hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨w, hw⟩
    exact Subgroup.mem_subgroupOf.1 this
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key u huH x
  · intro hx
    have := key u⁻¹ (H.inv_mem huH) _ hx
    simpa [mul_assoc] using this

theorem eq_of_perfect_le_inf_thetaComponentsAt {G : Type} [Group G] [Finite G] {c : G}
    {K K' I : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c) (hK' : K' ∈ thetaComponentsAt 3 c)
    (hI : I ≤ K ⊓ K') (hIp : ⁅I, I⁆ = I) (hIs : ¬ Group.IsSolvable ↥I) : K = K' := by
  by_contra hne
  have hcomm := Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK hK' hne
  have hIθ : I ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
    calc I = ⁅I, I⁆ := hIp.symm
      _ ≤ ⁅K, K'⁆ := Subgroup.commutator_mono (hI.trans inf_le_left) (hI.trans inf_le_right)
      _ ≤ _ := hcomm
  obtain ⟨hθs, -, -⟩ := solvable_prime_complement_core_characterization
    (H := ↥(Subgroup.centralizer ({c} : Set G))) Nat.prime_three
  have hsolM : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({c} : Set G))) := by
    unfold inSubgroup
    have e := (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({c} : Set G))).equivMapOfInjective
      (Subgroup.centralizer ({c} : Set G)).subtype (Subgroup.centralizer ({c} : Set G)).subtype_injective
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact hIs (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hIθ)
    (Subgroup.inclusion_injective hIθ))

variable {G : Type} [Group G] [Finite G]

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Cover217.exists_u {A E U : Subgroup G} {c : G} {L : Subgroup G} (h : Cover217 A E U c L)
    (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G} (ha : Valid217 A c L a) :
    ∃ u : G, u ∈ L ∧ u ∈ Subgroup.normalizer (A : Set G) ∧
      u ∈ Subgroup.normalizer (dGroup a c : Set G) ∧ u ∉ Subgroup.centralizer ({a} : Set G) ∧
      orderOf u = 8 ∧ c * u = u * c ∧ u ∈ Subgroup.normalizer (iCore L a : Set G) ∧
      u ^ 4 ∉ Subgroup.centralizer (iCore L a : Set G) := by
  obtain ⟨hq, hZ3⟩ := h.quasi_card_center hθ
  obtain ⟨e⟩ := h.quot
  obtain ⟨a', I', ha'G, ha'c, ha3, hI'C, ⟨φ⟩, hI, hD9, hDI, hDcomm, hCeq, hNC⟩ :=
    h.local_frame hθ hAL ha
  subst ha'G
  have hab := h.isElemAbelian_A
  have hab' := isElemAbelian_iff.1 hab
  set F : Subgroup ↥L := A.subgroupOf L with hF
  have hFmem : ∀ x : ↥L, x ∈ F ↔ (x : G) ∈ A := fun x => Subgroup.mem_subgroupOf
  have hFel : CFSG.IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (center ↥L))) := by
    rw [CFSG.RankThree.Asc83Table.isElementaryAbelian_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hab'.1 _ ((hFmem x).1 hx) _ ((hFmem y).1 hy))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (hab'.2 _ ((hFmem x).1 hx))
      rw [this, map_one]
  have hZF : center ↥L ≤ F := by
    rw [h.center_eq hθ, Subgroup.zpowers_le]
    exact (hFmem _).2 h.c_mem_A
  have hF81 : Nat.card F = 81 := by
    rw [hF, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, h.card]; norm_num
  have ha'F : a' ∈ F := (hFmem a').2 ha.mem
  have hq3 : (a' : ↥L ⧸ center ↥L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 (by
      rw [show a' ^ 3 = 1 from ha3]; exact Subgroup.one_mem _)
  have hq1 : (a' : ↥L ⧸ center ↥L) ≠ 1 := fun h1 => ha'c ((QuotientGroup.eq_one_iff _).1 h1)
  have h5 : 5 ∣ Nat.card (centralizer ({e (a' : ↥L ⧸ center ↥L)} : Set NativeSporadic.J3)) :=
    five_dvd_centralizer_of_nonCentral e hq3 hq1 hNC
  obtain ⟨u, I₂, huN, hu8, huD, huC, hI₂C, hI₂p, ⟨φ₂⟩, hI₂max, hPGL⟩ :=
    exists_pgl29_u_of_class hq hZ3 e hFel hZF hF81 ha'F ha'c h5
  have hC : Subgroup.centralizer ({(a' : G)} : Set G) ⊓ L =
      (Subgroup.centralizer ({a'} : Set ↥L)).map L.subtype := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨hx, hxL⟩
      exact ⟨⟨x, hxL⟩, Subtype.ext hx, rfl⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨congrArg Subtype.val hx', x'.2⟩
  have hI₂ : iCore L (a' : G) = I₂.map L.subtype := by
    unfold iCore
    rw [hC]
    exact CFSG.AGLEmbeddingD2.Wilson.Proving.perfCore_map_of_greatest L.subtype
      L.subtype_injective _ I₂ hI₂C hI₂p hI₂max
  have hDmap : dGroup (a' : G) c = (zpowers a' ⊔ center ↥L).map L.subtype := by
    rw [dGroup, Subgroup.map_sup, MonoidHom.map_zpowers, h.center_eq hθ, MonoidHom.map_zpowers]
    rfl
  have huH : u ∈ I₂ ⊔ zpowers u := (le_sup_right : zpowers u ≤ _) (Subgroup.mem_zpowers u)
  have huI₂ : u ∈ Subgroup.normalizer (I₂ : Set ↥L) :=
    mem_normalizer_of_normal_subgroupOf (hPGL.1) (hPGL.2.2.1) huH
  refine ⟨(u : G), u.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mem_normalizer_subgroupOf_iff hAL u).1 huN
  · have hDL : dGroup (a' : G) c ≤ L := by
      rw [hDmap]; exact Subgroup.map_subtype_le _
    rw [← mem_normalizer_subgroupOf_iff hDL u, hDmap]
    rw [show ((zpowers a' ⊔ center ↥L).map L.subtype).subgroupOf L = zpowers a' ⊔ center ↥L from
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    exact huD
  · intro hc
    apply huC
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    exact Subtype.ext (by simpa using hc)
  · rw [Subgroup.orderOf_coe]; exact hu8
  · exact h.c_comm u u.2
  · rw [hI₂]
    exact Subgroup.le_normalizer_map L.subtype ⟨u, huI₂, rfl⟩
  · intro hc
    apply pgl_pow_four_not_mem_centralizer hPGL huH hu8
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    rw [hI₂] at hc
    have := Subgroup.mem_centralizer_iff.1 hc (i : G) ⟨i, hi, rfl⟩
    exact Subtype.ext this

theorem Cover217.iCore_K_eq {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (hvL : Valid217 A c L a) {U₀ K : Subgroup G} (hK : Cover217 A E U₀ a K)
    (hθK : aschbacherSolvableCore 3 K = ⊥) (hAK : A ≤ K) (hvK : Valid217 A a K c)
    (hIK : iCore L a ≤ K) : iCore K c = iCore L a := by
  obtain ⟨eI⟩ := h.iCore_equiv hθ hAL hvL
  have hperf : ⁅iCore L a, iCore L a⁆ = iCore L a := perfect_of_equiv_alt6 _ eI
  have hle : iCore L a ≤ iCore K c := by
    refine le_sSup ⟨fun x hx => ⟨?_, hIK hx⟩, hperf⟩
    show x ∈ Subgroup.centralizer ({c} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h.c_comm x (iCore_le L a hx).2).symm
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hK.card_iCore hθK hAK hvK, h.card_iCore hθ hAL hvL]

theorem Cover217.card_inf_iCore {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (hv : Valid217 A c L a) : Nat.card ↥(A ⊓ iCore L a) = 9 := by
  obtain ⟨hB27, -⟩ := h.invariant_B hθ hAL hv
  obtain ⟨eI⟩ := h.iCore_equiv hθ hAL hv
  have hZI := center_eq_bot_of_equiv_alt6 (iCore L a) eI
  have hcI : ∀ x ∈ iCore L a, c * x = x * c := fun x hx => h.c_comm x (iCore_le L a hx).2
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ iCore L a : Subgroup G) : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer' _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcI x hx.2).symm
  have hdisj : Disjoint (A ⊓ iCore L a) (Subgroup.zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro x hxI hxc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxc
    have : (⟨c ^ n, hxI.2⟩ : ↥(iCore L a)) ∈ Subgroup.center ↥(iCore L a) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : c * y = y * c := hcI y y.2
      exact Subtype.ext (Commute.zpow_left (show Commute c (y : G) from h1) n).eq.symm
    rw [hZI, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj
  rw [hB27, Nat.card_zpowers, h.orderOf_c] at this
  omega

theorem Cover217.normalizes_L {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (hv : Valid217 A c L a) {g : G} (hgI : g ∈ Subgroup.centralizer (iCore L a : Set G))
    (hgc : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  have hpairs := mem_lThreeStarPairs_iff.mp h.pair.mem_pair
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  obtain ⟨eI⟩ := h.iCore_equiv hθ hAL hv
  have hperf : ⁅iCore L a, iCore L a⁆ = iCore L a := perfect_of_equiv_alt6 _ eI
  have hns : ¬ Group.IsSolvable ↥(iCore L a) := by
    intro hs
    have hA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have : Group.IsSolvable (alternatingGroup (Fin 6)) :=
      Group.isSolvable_of_surjective (f := eI.toMonoidHom) eI.surjective
    have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide
    exact not_isSolvable_of_simple (Q := alternatingGroup (Fin 6)) (by
      rw [h360]; norm_num) this
  have hL' := CFSG.RankThree.PartOne.Sec12TwoAssembly.conj_mem_thetaComponentsAt Nat.prime_three hgc hLc
  have hgfix : ∀ i ∈ iCore L a, g * i * g⁻¹ = i := by
    intro i hi
    have := Subgroup.mem_centralizer_iff.1 hgI i hi
    calc g * i * g⁻¹ = i * g * g⁻¹ := by rw [← this]
      _ = i := by group
  have hIle : iCore L a ≤ L ⊓ L.map (MulAut.conj g).toMonoidHom := by
    intro i hi
    exact ⟨(iCore_le L a hi).2, ⟨i, (iCore_le L a hi).2, by simpa using hgfix i hi⟩⟩
  have heq := eq_of_perfect_le_inf_thetaComponentsAt hLc hL' hIle hperf hns
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [heq]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h2 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h2
    exact this ▸ hy

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
