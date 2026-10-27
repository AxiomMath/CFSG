module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.RankThree.PartOne.AUTSL.L4Out
import CFSG.RankThree.PartOne.KLC.D4OutCentral
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Psl2
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrModel
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
import CFSG.LargeExtraspecial.DW2AOutInput

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open scoped commutatorElement

@[expose] def InnAut (Y : Type) [Group Y] : Subgroup (MulAut Y) :=
  (MulAut.conj : Y →* MulAut Y).range

@[expose] def OutTwoRank (Y : Type) [Group Y] : Prop :=
  ∀ P : Subgroup (MulAut Y), IsPGroup 2 P →
    (∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ InnAut Y) ∧
    ∀ E : Subgroup (MulAut Y), E ≤ P → (∀ a ∈ E, a ^ 2 ∈ InnAut Y) → (E ⊓ InnAut Y).relIndex E ≤ 4

@[expose] def TwoRankAt {R : Type*} [Group R] (I H : Subgroup R) : Prop :=
  ∀ P : Subgroup R, P ≤ H → IsPGroup 2 P →
    (∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ I) ∧
    ∀ E : Subgroup R, E ≤ P → (∀ a ∈ E, a ^ 2 ∈ I) → (E ⊓ I).relIndex E ≤ 4

instance InnAut.normal (Y : Type) [Group Y] : (InnAut Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨y, rfl⟩ := hn
  refine ⟨g y, ?_⟩
  ext z
  simp [MulAut.conj_apply]

theorem InnAut.map_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    (InnAut X).map (MulAut.congr e).toMonoidHom = InnAut Y := by
  ext z
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨e a, ?_⟩
    ext w
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · rintro ⟨b, rfl⟩
    refine ⟨MulAut.conj (e.symm b), ⟨e.symm b, rfl⟩, ?_⟩
    ext w
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem outTwoRank_iff {Y : Type} [Group Y] : OutTwoRank Y ↔ TwoRankAt (InnAut Y) ⊤ :=
  ⟨fun h P _ hP => h P hP, fun h P hP => h P le_top hP⟩

theorem TwoRankAt.map {R R' : Type*} [Group R] [Group R'] {I H : Subgroup R} (φ : R ≃* R')
    (h : TwoRankAt I H) : TwoRankAt (I.map φ.toMonoidHom) (H.map φ.toMonoidHom) := by
  intro P' hP'H hP'
  set P : Subgroup R := P'.map φ.symm.toMonoidHom with hPdef
  have hPH : P ≤ H := by
    rintro _ ⟨x', hx', rfl⟩
    obtain ⟨h0, hh0, hh0e⟩ := hP'H hx'
    have : φ.symm x' = h0 := by rw [← hh0e]; simp
    simpa [this] using hh0
  have hP : IsPGroup 2 P := hP'.map _
  obtain ⟨hcomm, hrank⟩ := h P hPH hP
  have hmem : ∀ a' ∈ P', φ.symm a' ∈ P := fun a' ha' => ⟨a', ha', rfl⟩
  refine ⟨fun a' ha' b' hb' => ?_, fun E' hE'P hE'2 => ?_⟩
  · have := hcomm _ (hmem a' ha') _ (hmem b' hb')
    refine ⟨_, this, ?_⟩
    simp [map_commutatorElement]
  · set E : Subgroup R := E'.map φ.symm.toMonoidHom with hEdef
    have hEP : E ≤ P := Subgroup.map_mono hE'P
    have hE2 : ∀ a ∈ E, a ^ 2 ∈ I := by
      rintro _ ⟨x', hx', rfl⟩
      have := hE'2 x' hx'
      obtain ⟨y, hy, hye⟩ := this
      have h3 : φ.symm x' ^ 2 = y := by rw [← map_pow, ← hye]; simp
      show φ.symm x' ^ 2 ∈ I
      rw [h3]; exact hy
    have h1 := hrank E hEP hE2
    have h2 := Subgroup.relIndex_map_map_of_injective (f := φ.toMonoidHom) (E ⊓ I) E φ.injective
    rw [Subgroup.map_inf _ _ _ φ.injective] at h2
    have hE' : E.map φ.toMonoidHom = E' := by
      rw [hEdef, Subgroup.map_map]
      ext x; simp
    rw [hE'] at h2
    rw [← h2] at h1
    exact h1



theorem OutTwoRank.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : OutTwoRank X) : OutTwoRank Y := by
  have h1 := (outTwoRank_iff.mp h).map (MulAut.congr e)
  rw [InnAut.map_congr, Subgroup.map_top_of_surjective _ (MulAut.congr e).surjective] at h1
  exact outTwoRank_iff.mpr h1

theorem TwoRankAt.of_hom {R C : Type*} [Group R] [Group C] {I H : Subgroup R} (Θ : R →* C)
    (c1 : ∀ a ∈ H, ∀ b ∈ H, Θ a * Θ b = Θ b * Θ a)
    (c2 : ∀ x ∈ I, Θ x = 1)
    (c3 : ∀ x ∈ H, Θ x = 1 → (∃ k : ℕ, x ^ (2 ^ k) ∈ I) → x ∈ I)
    (c4 : ∀ S : Subgroup C, S ≤ H.map Θ → (∀ y ∈ S, y ^ 2 = 1) → Nat.card S ≤ 4) :
    TwoRankAt I H := by
  intro P hPH hP
  have key : ∀ x ∈ P, Θ x = 1 → x ∈ I := by
    intro x hx hΘ
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    refine c3 x (hPH hx) hΘ ⟨k, ?_⟩
    have : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    rw [this]; exact I.one_mem
  refine ⟨fun a ha b hb => ?_, fun E hEP hE2 => ?_⟩
  · refine key _ ?_ ?_
    · rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    · rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact c1 a (hPH ha) b (hPH hb)
  · let φ : E →* C := Θ.comp E.subtype
    have hker : φ.ker = (E ⊓ I).subgroupOf E := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro h
        exact ⟨x.2, key x (hEP x.2) h⟩
      · intro h
        exact c2 _ h.2
    have hS : φ.range ≤ H.map Θ := by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, hPH (hEP x.2), rfl⟩
    have hS2 : ∀ y ∈ φ.range, y ^ 2 = 1 := by
      rintro _ ⟨x, rfl⟩
      show Θ (x : R) ^ 2 = 1
      rw [← map_pow]
      exact c2 _ (hE2 x x.2)
    have := c4 φ.range hS hS2
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    exact this

theorem index_le_two_of_two_cosets {G : Type*} [Group G] (H : Subgroup G) (a : G)
    (h : ∀ b : G, b ∈ H ∨ a⁻¹ * b ∈ H) : H.index ≤ 2 := by
  rw [Subgroup.index_eq_card]
  have hs : Function.Surjective (fun t : Bool => if t then (QuotientGroup.mk 1 : G ⧸ H) else
      QuotientGroup.mk a) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H b =>
      rcases h b with hb | hb
      · refine ⟨true, ?_⟩
        simp only [ite_true]
        rw [QuotientGroup.eq]
        simpa using H.inv_mem hb
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        rw [QuotientGroup.eq]
        exact hb
  have := Nat.card_le_card_of_surjective _ hs
  simpa using this



theorem TwoRankAt.of_pNice {R : Type*} [Group R] (I : Subgroup R) [I.Normal] (D E : Subgroup R)
    (hD2 : ∀ δ ∈ D, ∀ k : ℕ, δ ^ (2 ^ k) ∈ I → δ ∈ I)
    (hpE : ∀ α : R, (∃ k : ℕ, α ^ (2 ^ k) ∈ D) → α ∈ E)
    (hD3 : ∀ γ α : R, α ∈ E → ⁅γ, α⁆ ∈ D)
    (hcmp : ∀ α ∈ E, ∀ β ∈ E, (∃ k : ℕ, α ^ (2 ^ k) ∈ D) → (∃ k : ℕ, β ^ (2 ^ k) ∈ D) →
      (∃ m : ℤ, α * β ^ m ∈ D) ∨ ∃ m : ℤ, β * α ^ m ∈ D) :
    TwoRankAt I ⊤ := by
  intro P _ hP
  have hPE : ∀ x ∈ P, x ∈ E := by
    intro x hx
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    refine hpE x ⟨k, ?_⟩
    have : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    rw [this]; exact D.one_mem
  have key : ∀ x ∈ P, x ∈ D → x ∈ I := by
    intro x hx hxD
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    refine hD2 x hxD k ?_
    have : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    rw [this]; exact I.one_mem
  have hPk : ∀ x ∈ P, ∃ k : ℕ, x ^ (2 ^ k) ∈ D := by
    intro x hx
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    refine ⟨k, ?_⟩
    have : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    rw [this]; exact D.one_mem
  refine ⟨fun a ha b hb => ?_, fun E' hE'P hE'2 => ?_⟩
  · refine key _ ?_ (hD3 a b (hPE b hb))
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
  · by_cases hall : ∀ x ∈ E', x ∈ I
    · have : E' ⊓ I = E' := inf_eq_left.mpr hall
      rw [this, Subgroup.relIndex_self]; norm_num
    · push Not at hall
      obtain ⟨g, hgE', hgI⟩ := hall
      have hg2 : g ^ 2 ∈ I := hE'2 g hgE'
      have claim : ∀ x ∈ E', x ∈ I ∨ g⁻¹ * x ∈ I := by
        intro x hx
        have hxP : x ∈ P := hE'P hx
        have hgP : g ∈ P := hE'P hgE'
        have hx2 : x ^ 2 ∈ I := hE'2 x hx
        set π := QuotientGroup.mk' I with hπ
        have hz2 : ∀ {z : R ⧸ I}, z ^ 2 = 1 → ∀ m : ℤ, z ^ m = 1 ∨ z ^ m = z := by
          intro z hz m
          obtain ⟨q, hq | hq⟩ := Int.even_or_odd' m
          · left; rw [hq, zpow_mul]; simp [hz]
          · right; rw [hq, zpow_add, zpow_mul]; simp [hz]
        have hg'2 : π g ^ 2 = 1 := by
          rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).mpr hg2
        have hx'2 : π x ^ 2 = 1 := by
          rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).mpr hx2
        have hg'1 : π g ≠ 1 := fun h => hgI ((QuotientGroup.eq_one_iff _).mp h)
        have hinv : (π g)⁻¹ = π g := by
          rw [inv_eq_iff_mul_eq_one, ← sq]; exact hg'2
        have hfin : π x = 1 ∨ π x = π g := by
          rcases hcmp x (hPE x hxP) g (hPE g hgP) (hPk x hxP) (hPk g hgP) with ⟨m, hm⟩ | ⟨m, hm⟩
          · have hxm : x * g ^ m ∈ I :=
              key _ (P.mul_mem hxP (P.zpow_mem hgP m)) hm
            have h1 : π x * π g ^ m = 1 := by
              rw [← map_zpow, ← map_mul]; exact (QuotientGroup.eq_one_iff _).mpr hxm
            rcases hz2 hg'2 m with h | h
            · left; rw [h, mul_one] at h1; exact h1
            · right; rw [h] at h1; exact eq_inv_of_mul_eq_one_left h1 |>.trans hinv
          · have hxm : g * x ^ m ∈ I :=
              key _ (P.mul_mem hgP (P.zpow_mem hxP m)) hm
            have h1 : π g * π x ^ m = 1 := by
              rw [← map_zpow, ← map_mul]; exact (QuotientGroup.eq_one_iff _).mpr hxm
            rcases hz2 hx'2 m with h | h
            · rw [h, mul_one] at h1; exact absurd h1 hg'1
            · right; rw [h] at h1; exact eq_inv_of_mul_eq_one_right h1 |>.trans hinv
        rcases hfin with h | h
        · left; exact (QuotientGroup.eq_one_iff _).mp h
        · right
          refine (QuotientGroup.eq_one_iff _).mp ?_
          show π (g⁻¹ * x) = 1
          rw [map_mul, map_inv, h, inv_mul_cancel]
      have h2 := index_le_two_of_two_cosets ((E' ⊓ I).subgroupOf E') ⟨g, hgE'⟩ (fun b => by
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_mul, Subgroup.coe_inv]
        rcases claim b b.2 with h | h
        · exact Or.inl ⟨b.2, h⟩
        · exact Or.inr ⟨E'.mul_mem (E'.inv_mem hgE') b.2, h⟩)
      exact h2.trans (by norm_num)



theorem mul_comm_of_card_le_four {C : Type*} [Group C] [Finite C] (h : Nat.card C ≤ 4) :
    ∀ x y : C, x * y = y * x := by
  have hpos : 0 < Nat.card C := Nat.card_pos
  have : IsMulCommutative C := by
    interval_cases hc : Nat.card C
    · have : Subsingleton C := (Nat.card_eq_one_iff_unique.mp hc).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : IsCyclic C := isCyclic_of_prime_card hc
      infer_instance
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have : IsCyclic C := isCyclic_of_prime_card hc
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hc)
  exact fun x y => this.is_comm.comm x y

theorem TwoRankAt.of_index_le_four {R : Type*} [Group R] [Finite R] (I : Subgroup R) [I.Normal]
    (h : I.index ≤ 4) : TwoRankAt I ⊤ := by
  have hc : Nat.card (R ⧸ I) ≤ 4 := by rw [← Subgroup.index_eq_card]; exact h
  have hcomm := mul_comm_of_card_le_four hc
  refine TwoRankAt.of_hom (QuotientGroup.mk' I) (fun a _ b _ => hcomm _ _) ?_ ?_ ?_
  · intro x hx; exact (QuotientGroup.eq_one_iff _).mpr hx
  · intro x _ hx _; exact (QuotientGroup.eq_one_iff _).mp hx
  · intro S _ _
    exact (Nat.card_le_card_of_injective (fun s : S => (s : R ⧸ I)) Subtype.val_injective).trans hc



theorem map_conj_eq {R : Type*} [Group R] (I : Subgroup R) [I.Normal] (x : R) :
    I.map (MulAut.conj x).toMonoidHom = I := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using Subgroup.Normal.conj_mem inferInstance z hz x
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, ?_⟩
    · simpa using Subgroup.Normal.conj_mem inferInstance y hy x⁻¹
    · simp [MulAut.conj_apply, mul_assoc]

theorem TwoRankAt.of_odd_index {R : Type*} [Group R] [Finite R] {I H : Subgroup R} [I.Normal]
    (h : TwoRankAt I H) (hodd : Odd H.index) : TwoRankAt I ⊤ := by
  intro P _ hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints (R ⧸ H)
  have hcard : Nat.card (R ⧸ H) = H.index := (Subgroup.index_eq_card H).symm
  have hfix : (MulAction.fixedPoints P (R ⧸ H)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : Nat.card (MulAction.fixedPoints P (R ⧸ H)) = 0 := by simp [hne]
    rw [h0, hcard] at hmod
    have := (Nat.modEq_zero_iff_dvd.mp hmod)
    obtain ⟨m, hm⟩ := hodd
    omega
  obtain ⟨q, hq⟩ := hfix
  induction q using QuotientGroup.induction_on with
  | H x =>
    have hPx : P ≤ H.map (MulAut.conj x).toMonoidHom := by
      intro p hp
      have h1 : (⟨p, hp⟩ : P) • (QuotientGroup.mk x : R ⧸ H) = QuotientGroup.mk x := hq ⟨p, hp⟩
      have h2 : (QuotientGroup.mk (p * x) : R ⧸ H) = QuotientGroup.mk x := h1
      rw [QuotientGroup.eq] at h2
      refine ⟨x⁻¹ * p * x, ?_, ?_⟩
      · have : (p * x)⁻¹ * x = x⁻¹ * p⁻¹ * x := by group
        have h3 := H.inv_mem (by rw [this] at h2; exact h2)
        simpa [mul_assoc] using h3
      · simp [MulAut.conj_apply, mul_assoc]
    have h' := h.map (MulAut.conj x)
    rw [map_conj_eq] at h'
    exact h' P hPx hP



theorem card_map_mk'_eq_relIndex' {G : Type*} [Group G] (N K : Subgroup G) [N.Normal] :
    Nat.card (K.map (QuotientGroup.mk' N)) = N.relIndex K := by
  have h1 : ((QuotientGroup.mk' N).comp K.subtype).range = K.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h2 : ((QuotientGroup.mk' N).comp K.subtype).ker = N.subgroupOf K := by
    ext x
    simp [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rw [← h1, ← Subgroup.index_ker, h2]
  rfl

theorem exists_two_cosets {R : Type*} [Group R] [Finite R] (I D : Subgroup R)
    (h : I.relIndex D ≤ 2) : ∃ c ∈ D, ∀ d ∈ D, d ∈ I ∨ d * c ∈ I := by
  have h0 : (I.subgroupOf D).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (I.subgroupOf D).index ≤ 2 := h
  by_cases hi : (I.subgroupOf D).index = 1
  · refine ⟨1, D.one_mem, fun d hd => Or.inl ?_⟩
    have := Subgroup.index_eq_one.mp hi
    have hmem : (⟨d, hd⟩ : D) ∈ I.subgroupOf D := by rw [this]; exact Subgroup.mem_top _
    exact hmem
  · have h2 : (I.subgroupOf D).index = 2 := by omega
    obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp h2
    refine ⟨a, a.2, fun d hd => ?_⟩
    rcases (ha ⟨d, hd⟩).or with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem TwoRankAt.of_tower_central {R : Type*} [Group R] [Finite R] (I D H : Subgroup R)
    [I.Normal] (hDH : D ≤ H) (hDn : ∀ x ∈ H, ∀ d ∈ D, x * d * x⁻¹ ∈ D) (g : R) (hgH : g ∈ H)
    (hg : ∀ x ∈ H, ∃ k : ℤ, g ^ k * x ∈ D) (hrel : I.relIndex D ≤ 2) : TwoRankAt I H := by
  obtain ⟨c, hcD, hc⟩ := exists_two_cosets I D hrel
  set π := QuotientGroup.mk' I with hπ
  have hker : ∀ x, π x = 1 ↔ x ∈ I := fun x => QuotientGroup.eq_one_iff x
  have cent : ∀ h ∈ H, ∀ d ∈ D, Commute (π h) (π d) := by
    intro h hh d hd
    have hu := hDn h hh d hd
    have hπu : π (h * d * h⁻¹) = π d := by
      by_cases hdI : d ∈ I
      · have : h * d * h⁻¹ ∈ I := Subgroup.Normal.conj_mem inferInstance d hdI h
        rw [(hker _).mpr this, (hker _).mpr hdI]
      · have hdc : d * c ∈ I := (hc d hd).resolve_left hdI
        have huI : h * d * h⁻¹ ∉ I := by
          intro hI
          apply hdI
          have := Subgroup.Normal.conj_mem inferInstance _ hI h⁻¹
          simpa [mul_assoc] using this
        have huc : h * d * h⁻¹ * c ∈ I := (hc _ hu).resolve_left huI
        have e1 : π (h * d * h⁻¹) * π c = 1 := by
          rw [← map_mul]; exact (hker _).mpr huc
        have e2 : π d * π c = 1 := by
          rw [← map_mul]; exact (hker _).mpr hdc
        exact (mul_right_cancel (e1.trans e2.symm))
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at hπu
    exact hπu
  have decomp : ∀ x ∈ H, ∃ k : ℤ, ∃ d ∈ D, π x = (π g ^ k)⁻¹ * π d := by
    intro x hx
    obtain ⟨k, hk⟩ := hg x hx
    refine ⟨k, _, hk, ?_⟩
    rw [map_mul, map_zpow]
    group
  have c1 : ∀ a ∈ H, ∀ b ∈ H, π a * π b = π b * π a := by
    intro a ha b hb
    obtain ⟨k, d₁, hd₁, h1⟩ := decomp a ha
    obtain ⟨l, d₂, hd₂, h2⟩ := decomp b hb
    have hGd₁ : Commute (π g) (π d₁) := cent g hgH d₁ hd₁
    have hGd₂ : Commute (π g) (π d₂) := cent g hgH d₂ hd₂
    have hd₁d₂ : Commute (π d₁) (π d₂) := (cent d₂ (hDH hd₂) d₁ hd₁).symm
    rw [h1, h2]
    have hA : Commute ((π g ^ k)⁻¹) ((π g ^ l)⁻¹) :=
      ((Commute.refl (π g)).zpow_zpow k l).inv_inv
    have hB : Commute ((π g ^ k)⁻¹) (π d₂) := (hGd₂.zpow_left k).inv_left
    have hC : Commute (π d₁) ((π g ^ l)⁻¹) := (hGd₁.symm.zpow_right l).inv_right
    exact ((hA.mul_right hB).mul_left ((hC.mul_right hd₁d₂))) 
  refine TwoRankAt.of_hom π c1 (fun x hx => (hker x).mpr hx) (fun x _ hx _ => (hker x).mp hx) ?_
  intro S hSH hS2
  set Z : Subgroup (R ⧸ I) := D.map π with hZ
  have hZcard : Nat.card Z ≤ 2 := by
    rw [hZ]
    exact (card_map_mk'_eq_relIndex' I D).le.trans hrel
  have hz2 : ∀ z ∈ Z, z ^ 2 = 1 := by
    intro z hz
    have h1 : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    have h2 : z ^ Nat.card Z = 1 := congrArg Subtype.val h1
    have hpos : 0 < Nat.card Z := Nat.card_pos
    interval_cases hZc : Nat.card Z
    · rw [pow_one] at h2; rw [h2]; simp
    · exact h2
  set G := π g with hG
  let T := {t : Subgroup.zpowers G // t ^ 2 = 1}
  have hTcard : Nat.card T ≤ 2 := by
    classical
    have : Fintype (Subgroup.zpowers G) := Fintype.ofFinite _
    have := IsCyclic.card_pow_eq_one_le (α := Subgroup.zpowers G) (n := 2) two_pos
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact this
  have hex : ∀ y : S, ∃ p : T × Z, ((p.1 : Subgroup.zpowers G) : R ⧸ I) * (p.2 : R ⧸ I) = y := by
    intro y
    obtain ⟨h, hh, hhy⟩ := hSH y.2
    obtain ⟨k, d, hd, hπh⟩ := decomp h hh
    have hy : (y : R ⧸ I) = (G ^ k)⁻¹ * π d := by rw [← hhy]; exact hπh
    have hyy : (y : R ⧸ I) ^ 2 = 1 := hS2 y y.2
    have hzd : π d ∈ Z := ⟨d, hd, rfl⟩
    have hcom : Commute ((G ^ k)⁻¹) (π d) := ((cent g hgH d hd).zpow_left k).inv_left
    have ht : ((G ^ k)⁻¹) ^ 2 = 1 := by
      rw [hy, hcom.mul_pow, hz2 _ hzd, mul_one] at hyy
      exact hyy
    refine ⟨(⟨⟨(G ^ k)⁻¹, Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers G k)⟩, ?_⟩, ⟨π d, hzd⟩), hy.symm⟩
    exact Subtype.ext ht
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro y y' h
    apply Subtype.ext
    rw [← hf y, ← hf y', h]
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod] at this
  calc Nat.card S ≤ Nat.card T * Nat.card Z := this
    _ ≤ 2 * 2 := Nat.mul_le_mul hTcard hZcard



theorem TwoRankAt.of_tower_index_two {R : Type*} [Group R] [Finite R] (I D E : Subgroup R)
    (hID : I ≤ D) (hDn : D.Normal) (hEn : E.Normal)
    (hcomm : ∀ a b : R, ⁅a, b⁆ ∈ D) (hD2 : ∀ δ ∈ D, ∀ k : ℕ, δ ^ (2 ^ k) ∈ I → δ ∈ I)
    (hcyc : ∃ g ∈ E, ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D) (hE : E.index ≤ 2) : TwoRankAt I ⊤ := by
  set π := QuotientGroup.mk' D with hπ
  have hker : ∀ x, π x = 1 ↔ x ∈ D := fun x => QuotientGroup.eq_one_iff x
  refine TwoRankAt.of_hom π (fun a _ b _ => ?_) (fun x hx => (hker x).mpr (hID hx))
    (fun x _ hx hk => ?_) ?_
  · have h1 : π ⁅a, b⁆ = 1 := (hker _).mpr (hcomm a b)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h1
    exact h1
  · obtain ⟨k, hk⟩ := hk
    exact hD2 x ((hker x).mp hx) k hk
  · intro S _ hS2
    have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective D
    have hEn' : (E.map π).Normal := hEn.map π hsurj
    obtain ⟨g, hgE, hg⟩ := hcyc
    have h1 := CFSG.RankThree.PartOne.AUTSL.relIndex_inf_le_four (R := R ⧸ D) (I := ⊥) (D := ⊥)
      (E := E.map π) le_rfl bot_le (fun δ hδ _ => hδ) inferInstance hEn'
      ⟨π g, ⟨g, hgE, rfl⟩, by
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨k, hk⟩ := hg x hx
        exact ⟨k, by rw [← map_zpow, ← map_mul]; exact (hker _).mpr hk⟩⟩
      ((Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_map_dvd E hsurj)).trans hE) (F := S) hS2
    rw [inf_bot_eq, Subgroup.relIndex_bot_left] at h1
    exact h1



section Linear

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.OutStructure

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem not_two_dvd_gcd_of_charTwo [CharP K 2] (n : ℕ) : ¬ 2 ∣ Nat.gcd n (Nat.card K - 1) := by
  intro h
  have h2 : 2 ∣ Nat.card K - 1 := h.trans (Nat.gcd_dvd_right _ _)
  have := Fintype.ofFinite K
  obtain ⟨f, hp, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [← Nat.card_eq_fintype_card] at hf; exact hf
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have h2K : 2 ∣ Nat.card K := by rw [hK]; exact dvd_pow_self 2 (by omega)
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  omega


theorem outTwoRank_projectiveSL [CharP K 2] (hn : 3 ≤ n) : OutTwoRank (projectiveSL n K) := by
  obtain ⟨hgenTop, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, hDn, hEn, -, hcyc, -, hidx, -, -⟩ :=
    standard_outer_quotients (n := n) (K := K)
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL n
  have hnorm : ∀ N : Subgroup (MulAut (projectiveSL n K)),
      (N.subgroupOf (standardAutGroup n K)).Normal → N.Normal := by
    intro N hN
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hN.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  have hDnorm : (linearAutGroup n K).Normal := hnorm _ hDn
  have hEnorm : (semilinearAutGroup n K).Normal := hnorm _ hEn
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  have hcomm : ∀ a b : MulAut (projectiveSL n K), ⁅a, b⁆ ∈ linearAutGroup n K := by
    intro a b
    obtain ⟨A, σ, ε, hε, rfl⟩ := hgen a
    obtain ⟨B, τ, ε', hε', rfl⟩ := hgen b
    set π := QuotientGroup.mk' (linearAutGroup n K) with hπ
    have hπc : ∀ C : GL (Fin n) K, π (conjAut n K C) = 1 := fun C =>
      (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup C)
    have hfσ : Commute (π (fieldAut n K σ)) (π (fieldAut n K τ)) := by
      have h1 : fieldAut n K σ * fieldAut n K τ = fieldAut n K τ * fieldAut n K σ := by
        rw [htrans.2.1, htrans.2.1, ringAut_comm K σ τ]
      have h3 := congrArg π h1
      rw [map_mul π, map_mul π] at h3
      exact h3
    have hδf : ∀ τ : K ≃+* K, Commute (π (dualAut n K)) (π (fieldAut n K τ)) := by
      intro τ
      have h1 : dualAut n K * fieldAut n K τ = fieldAut n K τ * dualAut n K := by
        have h2 := htrans.2.2.2.2.2.1 τ
        calc dualAut n K * fieldAut n K τ
            = (dualAut n K * fieldAut n K τ * dualAut n K) * dualAut n K := by
              rw [mul_assoc (dualAut n K * fieldAut n K τ), htrans.2.2.2.1, mul_one]
          _ = fieldAut n K τ * dualAut n K := by rw [h2]
      have h3 := congrArg π h1
      rw [map_mul π, map_mul π] at h3
      exact h3
    have hc : Commute (π (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε))
        (π (conjAut n K B * fieldAut n K τ * dualAut n K ^ ε')) := by
      rw [map_mul, map_mul, map_mul, map_mul, hπc, hπc, one_mul, one_mul, map_pow, map_pow]
      exact (hfσ.mul_left ((hδf τ).pow_left ε)).mul_right
        (((hδf σ).symm.pow_right ε').mul_left ((Commute.refl (π (dualAut n K))).pow_pow ε ε'))
    have h1 : π ⁅conjAut n K A * fieldAut n K σ * dualAut n K ^ ε,
        conjAut n K B * fieldAut n K τ * dualAut n K ^ ε'⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr hc
    exact (QuotientGroup.eq_one_iff _).mp h1
  refine outTwoRank_iff.mpr (TwoRankAt.of_tower_index_two _ (linearAutGroup n K)
    (semilinearAutGroup n K) hID hDnorm hEnorm hcomm ?_ hcyc hidx')
  intro δ hδ k hk
  exact linear_D2 Nat.prime_two hn (not_two_dvd_gcd_of_charTwo n) δ hδ k hk

end Linear



section Models

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.OutStructure

private theorem outTwoRank_of_outPNice {Y : Type} [Group Y] (h : OutPNice 2 Y) : OutTwoRank Y := by
  obtain ⟨D, E, -, hD2, hpE, hD3, hcmp⟩ := h
  exact outTwoRank_iff.mpr (TwoRankAt.of_pNice (InnAut Y) D E hD2 hpE hD3 hcmp)

theorem outTwoRank_PSL_two {X : Type} [Group X] {m : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 m) : OutTwoRank X :=
  outTwoRank_of_outPNice (outPNice_PSL_two Nat.prime_two h)

theorem outTwoRank_PSp_two {X : Type} [Group X] {m : ℕ}
    (h : StatedClassicalModel X .PSp 2 2 m) : OutTwoRank X :=
  outTwoRank_of_outPNice (outPNice_PSp_two Nat.prime_two h)

theorem outTwoRank_PSp_ge_three {X : Type} [Group X] {r m : ℕ} (hr : 3 ≤ r)
    (h : StatedClassicalModel X .PSp r 2 m) : OutTwoRank X :=
  outTwoRank_of_outPNice (outPNice_PSp_ge_three Nat.prime_two hr h)

theorem outTwoRank_PSU {X : Type} [Group X] {n m : ℕ}
    (h : StatedClassicalModel X .PSU n 2 m) : OutTwoRank X := by
  have hm : 1 ≤ m := h.1.2.1
  refine outTwoRank_of_outPNice (outPNice_PSU Nat.prime_two h ?_)
  intro hd
  have h1 : 2 ∣ 2 ^ m + 1 := hd.trans (Nat.gcd_dvd_right _ _)
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  omega

theorem outTwoRank_PSL_ge_three {X : Type} [Group X] {n m : ℕ} (hn : 3 ≤ n)
    (h : StatedClassicalModel X .PSL n 2 m) : OutTwoRank X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have e' : X ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  exact OutTwoRank.of_mulEquiv e'.symm (outTwoRank_projectiveSL hn)

end Models



theorem ncard_orbit_odd {A X : Type*} [Group A] [MulAction A X] {F y z : X}
    (hsub : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z) {κ : A} (hκF : κ • F = F)
    (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z) :
    Odd (MulAction.orbit A F).ncard := by
  have hFy : F ≠ y := by
    intro h
    apply hyz
    rw [← hκy, ← h, hκF, h]
  have hFz : F ≠ z := by
    intro h
    apply hyz
    rw [← hκz, ← h, hκF, h]
  by_cases hy : ∃ a : A, a • F = y
  · obtain ⟨a, ha⟩ := hy
    have hz : (κ * a) • F = z := by rw [mul_smul, ha, hκy]
    have : MulAction.orbit A F = {F, y, z} := by
      ext x
      constructor
      · rintro ⟨b, rfl⟩
        rcases hsub b with h | h | h <;> simp [h]
      · intro hx
        rcases hx with rfl | rfl | rfl
        · exact MulAction.mem_orbit_self _
        · exact ⟨a, ha⟩
        · exact ⟨κ * a, hz⟩
    rw [this, Set.ncard_eq_three.mpr ⟨F, y, z, hFy, hFz, hyz, rfl⟩]
    exact ⟨1, rfl⟩
  · push Not at hy
    have hz : ∀ a : A, a • F ≠ z := by
      intro a ha
      apply hy (κ * a)
      rw [mul_smul, ha, hκz]
    have : MulAction.orbit A F = {F} := by
      ext x
      constructor
      · rintro ⟨b, rfl⟩
        rcases hsub b with h | h | h
        · simp [h]
        · exact absurd h (hy b)
        · exact absurd h (hz b)
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact MulAction.mem_orbit_self _
    rw [this, Set.ncard_singleton]
    exact ⟨0, rfl⟩

section Orthogonal

open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.RankThree.PartOne.OutStructure (orthD inner_le_orthD exists_gen mem_orthD_iff)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

private theorem twoRankAt_matrixProjectiveImage (hQ : ∃ v, Q v ≠ 0)
    (hA : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2) :
    TwoRankAt (InnAut (matrixProjectiveDerived Q)) (matrixProjectiveImage Q) := by
  have : Finite (matrixProjectiveDerived Q) := inferInstance
  have : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  obtain ⟨g₀, hg₀⟩ := exists_gen Q
  have hDE : orthD Q ≤ matrixProjectiveImage Q := by
    intro δ hδ
    obtain ⟨g, rfl⟩ := (mem_orthD_iff Q δ).1 hδ
    exact ⟨g.val, rfl⟩
  refine TwoRankAt.of_tower_central _ (orthD Q) (matrixProjectiveImage Q) hDE ?_
    (matrixProjectiveConjugationHom Q g₀) ⟨g₀, rfl⟩ ?_
    (CFSG.RankThree.PartOne.KLC.relIndex_inner_orthD_le_two Q hQ hA)
  · intro e he d hd
    obtain ⟨g, rfl⟩ := (mem_matrixProjectiveImage_iff Q e).1 he
    obtain ⟨ℓ, rfl⟩ := (mem_orthD_iff Q d).1 hd
    refine (mem_orthD_iff Q _).2 ⟨⟨g * ℓ.val * g⁻¹,
      (linearPairsNormal Q).conj_mem ℓ.val ℓ.property g⟩, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  · intro e he
    obtain ⟨h, rfl⟩ := (mem_matrixProjectiveImage_iff Q e).1 he
    obtain ⟨k, hk⟩ := hg₀ h
    refine ⟨k, (mem_orthD_iff Q _).2 ⟨⟨g₀ ^ k * h, hk⟩, ?_⟩⟩
    rw [map_mul, map_zpow]
    rfl


section OrthogonalModels

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.LargeExtraspecial.DW
open scoped Pointwise

theorem outTwoRank_POmegaPlus_ge_five {X : Type} [Group X] {n m : ℕ} (hn : 5 ≤ n)
    (h : StatedClassicalModel X .POmegaPlus n 2 m) : OutTwoRank X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) n 2 m h K hK (quadPlus n K) (coe_quadPlus n K) e
  have hab' : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus n K))) ≤ 2 := by
    rw [show coordinateQuadPlus n K = reindexQuadraticForm (plusIndexEquiv n) (quadPlus n K)
      from rfl, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  have h1 := twoRankAt_matrixProjectiveImage (coordinateQuadPlus n K) hQ hab'
  rw [htop] at h1
  exact OutTwoRank.of_mulEquiv (coordinatePlusWitnessEquiv K e).symm (outTwoRank_iff.mpr h1)

theorem outTwoRank_POmegaMinus {X : Type} [Group X] {n m : ℕ}
    (h : StatedClassicalModel X .POmegaMinus n 2 m) : OutTwoRank X := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hQ : ∃ v, coordinateQuadMinus n K hn1 b c v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaMinus
    (.inr (.inr rfl)) n 2 m h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hab' :
      Nat.card (Abelianization (matrixIsometries (coordinateQuadMinus n K hn1 b c))) ≤ 2 := by
    rw [show coordinateQuadMinus n K hn1 b c =
      reindexQuadraticForm (minusIndexEquiv n hn1) (quadMinus n K b c) from rfl,
      card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c
    hirr
  have h1 := twoRankAt_matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) hQ hab'
  rw [htop] at h1
  exact OutTwoRank.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e).symm (outTwoRank_iff.mpr h1)


theorem outTwoRank_POmegaPlus_four {X : Type} [Group X] {m : ℕ}
    (h : StatedClassicalModel X .POmegaPlus 4 2 m) : OutTwoRank X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) 4 2 m h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hab' : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := CFSG.RankThree.PartOne.KLC.swap_data_coordinate K
  have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
      (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
    MulAction.index_stabilizer _ _
  have hodd : Odd (matrixProjectiveImage (coordinateQuadPlus 4 K)).index := by
    rw [← hEA, hst]
    refine ncard_orbit_odd (y := plusCX 4 K) (z := plusCXstar 4 K (by omega)) ?_ hκF hκy hκz hyz
    intro a
    have := hsub (MulAction.mem_orbit _ a)
    simpa using this
  have h1 := twoRankAt_matrixProjectiveImage (coordinateQuadPlus 4 K) hQ hab'
  have h2 := TwoRankAt.of_odd_index h1 hodd
  exact OutTwoRank.of_mulEquiv (coordinatePlusWitnessEquiv K e).symm (outTwoRank_iff.mpr h2)

end OrthogonalModels

end Orthogonal



section Small

open CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem outTwoRank_alternatingGroup {n : ℕ} (hn : 5 ≤ n) :
    OutTwoRank (alternatingGroup (Fin n)) := by
  refine outTwoRank_iff.mpr (TwoRankAt.of_index_le_four _ ?_)
  have h := CFSG.RankThree.PartOne.card_outer_alternating_le_four hn
  rw [Subgroup.index_eq_card]
  exact h

private theorem outTwoRank_PSL_two_prime {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime]
    (hK : Nat.card K = r) (hodd : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    OutTwoRank (PSL2 K) := by
  have hbij := CFSG.Quasithin.A312U3.pgl2InnerAutPSL2_bijective hK hodd hcard
  let φ : PGL2 K ≃* MulAut (PSL2 K) :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 K hodd hcard) hbij
  have hInn : InnAut (PSL2 K) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map
        φ.toMonoidHom := by
    ext δ
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL y, ⟨y, rfl⟩, ?_⟩
      exact pgl2InnerAutPSL2_toPGL K hodd hcard y
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, (pgl2InnerAutPSL2_toPGL K hodd hcard y).symm⟩
  have : Finite (PSL2 K) := inferInstance
  refine outTwoRank_iff.mpr (TwoRankAt.of_index_le_four _ ?_)
  have h2 : (Subgroup.map φ.toMonoidHom
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range).index =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.index :=
    Subgroup.index_map_equiv _ φ
  rw [hInn, h2, pgl2_psl2Range_index_eq_two K hodd]
  norm_num

theorem outTwoRank_PSL_two_seven {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 2 7 1) : OutTwoRank X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hK7 : Nat.card K = 7 := by rw [hK]; norm_num
  have hodd : IsOddPrimePower (Nat.card K) := ⟨7, 1, by norm_num, by decide, le_rfl, by rw [hK7]; norm_num⟩
  have hcard : 3 < Nat.card K := by rw [hK7]; norm_num
  have e' : X ≃* PSL2 K := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  exact OutTwoRank.of_mulEquiv e'.symm (outTwoRank_PSL_two_prime hK7 hodd hcard)

end Small

section SmallUnitary

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.OutStructure

theorem outTwoRank_PSU_three_three {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU 3 3 1) : OutTwoRank X := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 3 1 K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(3 = 3 ∧ 3 ^ 1 = 2) := by decide
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := 3)) hn3 hq
  have e' : X ≃* primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact outTwoRank_of_outPNice (OutPNice.of_mulEquiv e'
    (outPNice_primeFormP hU hn3 hq Nat.prime_two (by norm_num)))

end SmallUnitary

section Exceptional

open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.RankThree.PartOne.OutStructure

theorem outTwoRank_G2
    (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p = 2) {Y : Type} [Group Y]
    (e : Y ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : OutTwoRank Y := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨e0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp2
    (GaloisField q.p q.exponent) hK
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2
      q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩, GaloisField q.p q.exponent, inferInstance,
      inferInstance, ?_, ⟨e0.symm⟩⟩
    · rw [← PrimePower.card_def]
      exact hq3
    · rw [hK, PrimePower.card_def]
  rw [hp2] at hce
  exact OutTwoRank.of_mulEquiv e.symm
    (outTwoRank_of_outPNice (outPNice_G2 Nat.prime_two hce))

end Exceptional


section Main

open CFSG.Assembly.LowTwoRank TauCeti CFSG.AGLEmbedding

private theorem outTwoRank_of_small {Y : Type} [Group Y] (d : ValidLieTypeIndex)
    (hd : (∃ q : PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
      (∃ q : PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q))
    (e : Y ≃* (CFSGIndex.lie d).Group) : OutTwoRank Y := by
  obtain ⟨d1, hv⟩ := d
  rcases hd with ⟨q, hq, hd1⟩ | ⟨q, hq, hd1⟩
  · simp only at hd1
    subst hd1
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    have hq' : q.p ^ q.exponent = 7 := by rw [← PrimePower.card_def]; exact hq
    obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
    rw [hp7, he1] at h
    exact outTwoRank_PSL_two_seven h
  · simp only at hd1
    subst hd1
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    have hq' : q.p ^ q.exponent = 3 := by rw [← PrimePower.card_def]; exact hq
    obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hq'
    rw [hp3, he1] at h
    exact outTwoRank_PSU_three_three h

theorem outTwoRank_of_isClassicalTwoOrG2_of_G2 {Y : Type} [Group Y]
    (hG2 : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 →
      (Y ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) → OutTwoRank Y)
    (h : IsClassicalTwoOrG2 Y) : OutTwoRank Y := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · rcases CFSG.AGLEmbedding.ParabAutIrr.classical_model_or_g2 d hd e with
      ⟨t, n, f, ht, hm⟩ | ⟨q, hq, hq2, hdq⟩
    · have hadm := hm.1
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · obtain ⟨-, -, hn2, -⟩ := hadm
        rcases Nat.lt_or_ge n 3 with h3 | h3
        · have : n = 2 := by omega
          subst this
          exact outTwoRank_PSL_two hm
        · exact outTwoRank_PSL_ge_three h3 hm
      · exact outTwoRank_PSU hm
      · obtain ⟨-, -, hn2, -⟩ := hadm
        rcases Nat.lt_or_ge n 3 with h3 | h3
        · have : n = 2 := by omega
          subst this
          exact outTwoRank_PSp_two hm
        · exact outTwoRank_PSp_ge_three h3 hm
      · obtain ⟨-, -, hn4⟩ := hadm
        rcases Nat.lt_or_ge n 5 with h5 | h5
        · have : n = 4 := by omega
          subst this
          exact outTwoRank_POmegaPlus_four hm
        · exact outTwoRank_POmegaPlus_ge_five h5 hm
      · exact outTwoRank_POmegaMinus hm
    · subst hdq
      exact hG2 q hq hq2 e
  · exact OutTwoRank.of_mulEquiv e.symm (outTwoRank_alternatingGroup (by omega))
  · exact outTwoRank_of_small d hd e

theorem outTwoRank_of_isClassicalTwoOrG2
    {Y : Type} [Group Y] [Finite Y] (h : IsClassicalTwoOrG2 Y) : OutTwoRank Y :=
  outTwoRank_of_isClassicalTwoOrG2_of_G2 (fun q hv hp2 e => outTwoRank_G2 q hv hp2 e) h

end Main

end CFSG.HardMathSupport.Cooperstein.StructureLie
