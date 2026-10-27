module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217Frame
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217InvariantB
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217U0
public import CFSG.RankThree.PartTwo.Sec21.Item215

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem nonempty_quot_center_of_lBar {L : Subgroup G} (hq : IsQuasisimple L) {S : Type*}
    [Group S] (e : lBar L ⧸ Subgroup.center (lBar L) ≃* S) :
    Nonempty (L ⧸ Subgroup.center L ≃* S) := by
  obtain ⟨hTs, hTch, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hT
  have : T.Normal := Subgroup.normal_of_characteristic T
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  have hperf : Group.IsPerfect L := hq.1
  have hK₀s : Group.IsSolvable (Item21EarlyProof.centerPre T) :=
    Item21EarlyProof.isSolvable_centerPre T hTs
  have hle : Item21EarlyProof.centerPre T ≤ Subgroup.center L :=
    Sec4.Census.le_of_isSolvable_of_normal inferInstance hK₀s
  have hge : Subgroup.center L ≤ Item21EarlyProof.centerPre T := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective T q
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz l)]
  have heq : Item21EarlyProof.centerPre T = Subgroup.center L := le_antisymm hle hge
  exact ⟨((QuotientGroup.quotientMulEquivOfEq heq.symm).trans
    (Item21EarlyProof.centerPreEquiv T)).trans e⟩

section Main

set_option linter.unusedSectionVars false

theorem nonCentral_of_card_dvd {Q : Type*} [Group Q] [Finite Q] (e : Q ≃* NativeSporadic.J3)
    {q : Q} (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1) {I : Subgroup Q} (hI : Nat.card I = 360)
    (hIC : I ≤ centralizer ({q} : Set Q)) : NonCentral 3 q := by
  have hQ : Nat.card Q = 50232960 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J3.card_J3]
  have hdvd : 360 ∣ Nat.card (centralizer ({q} : Set Q)) := hI ▸ Subgroup.card_dvd_of_le hIC
  rcases card_centralizer_of_equiv_J3_dichotomy e hq3 hq1 with h | h
  · exact nonCentral_of_card_centralizer hQ h
  · rw [h] at hdvd
    norm_num at hdvd

theorem center_eq_bot_of_equiv_J3 {Y : Type*} [Group Y] (e : Y ≃* NativeSporadic.J3) :
    Subgroup.center Y = ⊥ := by
  have hs : IsSimpleGroup Y := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J3.isSimpleGroup_J3 e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h0 | h0
  · exact h0
  · exfalso
    have hcomm : ∀ x y : Y, x * y = y * x := fun x y =>
      (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top y)) x
    have hs' : Group.IsSolvable Y := Group.isSolvable_of_comm hcomm
    have hfin : Finite Y := Finite.of_equiv _ e.symm.toEquiv
    exact not_isSolvable_of_simple (Q := Y) (by
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J3.card_J3]; norm_num) hs'

theorem Cover217.sec21Pair_K {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) {a : G} {U₀ K : Subgroup G} (hU₀ : U₀ ∈ fourGroupsMinus E)
    (hpair : (a, K) ∈ lThreeStarPairs A E U₀) : Sec21Pair G A E U₀ a K :=
  { h.pair.toSec21Std with
    mem_E := h.pair.mem_E
    mem_U := fourGroupsMinus_subset E hU₀
    mem_pair := hpair }

theorem Cover217.iCore_equiv {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (ha : Valid217 A c L a) : Nonempty (↥(iCore L a) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨a', I', -, -, -, -, ⟨φ⟩, hI, -⟩ := h.local_frame hθ hAL ha
  exact ⟨(MulEquiv.subgroupCongr hI).trans
    (((I'.equivMapOfInjective L.subtype L.subtype_injective).symm).trans φ)⟩

theorem Cover217.card_iCore {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (ha : Valid217 A c L a) : Nat.card ↥(iCore L a) = 360 := by
  obtain ⟨e⟩ := h.iCore_equiv hθ hAL ha
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem iCore_le (L : Subgroup G) (a : G) :
    iCore L a ≤ Subgroup.centralizer ({a} : Set G) ⊓ L :=
  sSup_le fun _ hK => hK.1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Cover217.frame_K {A E U : Subgroup G} {c : G} {L : Subgroup G} (h : Cover217 A E U c L)
    (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G} (hfr : Frame217 E c L a)
    {U₀ K : Subgroup G} (hK : Cover217 A E U₀ a K) (hθK : aschbacherSolvableCore 3 K = ⊥)
    (hAK : A ≤ K) (hIK : iCore L a ≤ K) : Frame217 E a K c := by
  have hpairs := mem_lThreeStarPairs_iff.mp h.pair.mem_pair
  have hcE : c ∈ E := hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have ha3 : a ^ 3 = 1 := h.isElemAbelian_A.2 a (h.pair.mem_E.2 hfr.mem)
  have hcK : c ∈ K := hAK h.c_mem_A
  have hnot : c ∉ Subgroup.zpowers a := by
    intro hc
    exact hfr.not_mem (mem_zpowers_of_mem_zpowers ha3 hc1 hc)
  refine ⟨hcE, hnot, ⟨⟨c, hcK⟩, ⟨1, Subgroup.one_mem _, by simp⟩, ?_⟩⟩
  obtain ⟨e⟩ := hK.quot
  have hc3 : c ^ 3 = 1 := h.isElemAbelian_A.2 c h.c_mem_A
  have hcZ : (⟨c, hcK⟩ : ↥K) ∉ Subgroup.center ↥K := by
    intro hz
    rw [hK.center_eq hθK] at hz
    apply hnot
    have := Subgroup.mem_zpowers_iff.1 hz
    obtain ⟨n, hn⟩ := this
    exact ⟨n, congrArg Subtype.val hn⟩
  have hq3 : (QuotientGroup.mk (⟨c, hcK⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨c, hcK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this]; rfl
  have hq1 : (QuotientGroup.mk (⟨c, hcK⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K) ≠ 1 := fun h1 =>
    hcZ ((QuotientGroup.eq_one_iff _).1 h1)
  have hI : Valid217 A c L a := hfr.valid h.pair.mem_E.2
  obtain ⟨eI⟩ := h.iCore_equiv hθ hAL hI
  have hI360 := h.card_iCore hθ hAL hI
  set IK : Subgroup ↥K := (iCore L a).subgroupOf K with hIKdef
  have hIKmem : ∀ x : ↥K, x ∈ IK ↔ (x : G) ∈ iCore L a := fun x => Subgroup.mem_subgroupOf
  have hIKcard : Nat.card IK = 360 := by
    rw [hIKdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIK).toEquiv, hI360]
  have hinj : Function.Injective ((QuotientGroup.mk' (Subgroup.center ↥K)).comp IK.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : (x : ↥K) ∈ Subgroup.center ↥K := (QuotientGroup.eq_one_iff _).1 hx
    have hxI : (x : G) ∈ iCore L a := (hIKmem x).1 x.2
    have hc : (⟨(x : G), hxI⟩ : ↥(iCore L a)) ∈ Subgroup.center ↥(iCore L a) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyK : (y : G) ∈ K := hIK y.2
      have := Subgroup.mem_center_iff.1 hxZ ⟨(y : G), hyK⟩
      exact Subtype.ext (congrArg (fun z : ↥K => (z : G)) this)
    rw [center_eq_bot_of_equiv_alt6 (iCore L a) eI, Subgroup.mem_bot] at hc
    have h1 : ((x : ↥K) : G) = 1 := by simpa using congrArg Subtype.val hc
    exact Subtype.ext (Subtype.ext (by simpa using h1))
  set IQ : Subgroup (↥K ⧸ Subgroup.center ↥K) := IK.map (QuotientGroup.mk' (Subgroup.center ↥K))
    with hIQ
  have hIQcard : Nat.card IQ = 360 := by
    rw [← hIKcard]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun x : IK => (⟨QuotientGroup.mk' (Subgroup.center ↥K) (x : ↥K), ⟨x, x.2, rfl⟩⟩ : IQ))
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ?_⟩)).symm
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hIQC : IQ ≤ Subgroup.centralizer
      ({(QuotientGroup.mk (⟨c, hcK⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K)} :
        Set (↥K ⧸ Subgroup.center ↥K)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show QuotientGroup.mk x * QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have hxI : (x : G) ∈ iCore L a := (hIKmem x).1 hx
    exact (h.c_comm x ((iCore_le L a hxI).2)).symm
  exact nonCentral_of_card_dvd e hq3 hq1 hIQcard hIQC

theorem Cover217.c_not_mem_BK {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) {a : G} {U₀ K : Subgroup G} (hK : Cover217 A E U₀ a K)
    (hθK : aschbacherSolvableCore 3 K = ⊥) (hAK : A ≤ K) (hcK : Valid217 A a K c)
    (hKC : K ≤ Subgroup.centralizer ({a} : Set G)) :
    c ∉ (A ⊓ iCore K c) ⊔ Subgroup.zpowers a := by
  obtain ⟨eI⟩ := hK.iCore_equiv hθK hAK hcK
  have hab := h.isElemAbelian_A
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have haA : a ∈ A := hK.c_mem_A
  have haC : a ∈ Subgroup.centralizer (((A ⊓ iCore K c : Subgroup G)) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcomm x hx.1 a haA)
  have hN : Subgroup.zpowers a ≤ Subgroup.normalizer ((A ⊓ iCore K c : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.2 haC).trans (centralizer_le_normalizer' _)
  intro hmem
  have hmemP : ∀ g, g ∈ prodSubgroup (A ⊓ iCore K c) (Subgroup.zpowers a) hN ↔
      ∃ m ∈ (A ⊓ iCore K c), ∃ k ∈ Subgroup.zpowers a, g = m * k := fun g => Iff.rfl
  have hle : (A ⊓ iCore K c) ⊔ Subgroup.zpowers a ≤
      prodSubgroup (A ⊓ iCore K c) (Subgroup.zpowers a) hN :=
    sup_le (fun m hm => (hmemP m).2 ⟨m, hm, 1, Subgroup.one_mem _, by simp⟩)
      (fun k hk => (hmemP k).2 ⟨1, Subgroup.one_mem _, k, hk, by simp⟩)
  obtain ⟨y, hy, k, hk, hyk⟩ := (hmemP c).1 (hle hmem)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hy' : y = c * (a ^ n)⁻¹ := by rw [hyk]; group
  have hyI : y ∈ iCore K c := hy.2
  have hcen : (⟨y, hyI⟩ : ↥(iCore K c)) ∈ Subgroup.center ↥(iCore K c) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hxC := iCore_le K c x.2
    have hxc : c * (x : G) = (x : G) * c :=
      (Subgroup.mem_centralizer_singleton_iff.1 hxC.1).symm
    have hxa : (x : G) * a = a * (x : G) := Subgroup.mem_centralizer_singleton_iff.1
      (hKC hxC.2)
    have hxan : (x : G) * (a ^ n)⁻¹ = (a ^ n)⁻¹ * (x : G) := by
      have := Commute.zpow_right (show Commute (x : G) a from hxa) (-n)
      simpa [zpow_neg] using this.eq
    apply Subtype.ext
    show (x : G) * y = y * (x : G)
    rw [hy']
    calc (x : G) * (c * (a ^ n)⁻¹) = (x * c) * (a ^ n)⁻¹ := by group
      _ = (c * x) * (a ^ n)⁻¹ := by rw [← hxc]
      _ = c * (x * (a ^ n)⁻¹) := by group
      _ = c * ((a ^ n)⁻¹ * x) := by rw [hxan]
      _ = (c * (a ^ n)⁻¹) * x := by group
  rw [center_eq_bot_of_equiv_alt6 (iCore K c) eI, Subgroup.mem_bot] at hcen
  have hy1 : y = 1 := congrArg Subtype.val hcen
  apply hcK.not_mem
  rw [hy1, one_mul] at hyk
  exact hyk ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Cover217.irreducible_of_K {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (hfr : Frame217 E c L a) {U₀ K : Subgroup G} (hK : Cover217 A E U₀ a K)
    (hθK : aschbacherSolvableCore 3 K = ⊥) (hAK : A ≤ K) (hIK : iCore L a ≤ K)
    (hKC : K ≤ Subgroup.centralizer ({a} : Set G)) (S : Subgroup G) (hSA : S ≤ A)
    (hS : ∀ x ∈ Subgroup.normalizer (A : Set G), S.map (MulAut.conj x).toMonoidHom = S) :
    S = ⊥ ∨ S = A := by
  have hEA : E ≤ A := h.pair.mem_E.2
  have hfrK := h.frame_K hθ hAL hfr hK hθK hAK hIK
  have hvL := hfr.valid hEA
  have hvK := hfrK.valid hEA
  obtain ⟨hBL, hclsL⟩ := h.invariant_B hθ hAL hvL
  obtain ⟨hBK, hclsK⟩ := hK.invariant_B hθK hAK hvK
  have hcard_c : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, h.orderOf_c]
  have hcard_a : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hK.orderOf_c]
  have hcardA : Nat.card A = 81 := by rw [h.card]; norm_num
  have hSL : ∀ x ∈ L ⊓ Subgroup.normalizer (A : Set G), S.map (MulAut.conj x).toMonoidHom = S :=
    fun x hx => hS x hx.2
  have hSK : ∀ x ∈ K ⊓ Subgroup.normalizer (A : Set G), S.map (MulAut.conj x).toMonoidHom = S :=
    fun x hx => hS x hx.2
  have hc_notB := h.c_not_mem_BK hK hθK hAK hvK hKC
  rcases hclsL S hSA hSL with h0 | hA | hc | hB
  · exact Or.inl h0
  · exact Or.inr hA
  · exfalso
    have hS3 : Nat.card S = 3 := by rw [hc]; exact hcard_c
    rcases hclsK S hSA hSK with k0 | kA | ka | kB
    · rw [k0, Subgroup.card_bot] at hS3; norm_num at hS3
    · rw [kA, hcardA] at hS3; norm_num at hS3
    · have hcS : c ∈ S := hc ▸ Subgroup.mem_zpowers c
      rw [ka] at hcS
      exact hfrK.not_mem hcS
    · rw [kB, hBK] at hS3; norm_num at hS3
  · exfalso
    have hS27 : Nat.card S = 27 := by rw [hB]; exact hBL
    rcases hclsK S hSA hSK with k0 | kA | ka | kB
    · rw [k0, Subgroup.card_bot] at hS27; norm_num at hS27
    · rw [kA, hcardA] at hS27; norm_num at hS27
    · rw [ka, hcard_a] at hS27; norm_num at hS27
    · have hcS : c ∈ S := hB ▸ (show c ∈ (A ⊓ iCore L a) ⊔ Subgroup.zpowers c from (le_sup_right : Subgroup.zpowers c ≤ _) (Subgroup.mem_zpowers c))
      rw [kB] at hcS
      exact hc_notB hcS

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
