module

public import CFSG.ClassicalInvolution.RouteD.LocalMembers
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSU
public import CFSG.ClassicalInvolution.Models.Transfer.Unitary
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Frame

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime]

theorem psu_model_equiv (hp2 : p ≠ 2) {n : ℕ}
    (hadm : StatedLieAdmissible .PSU n p f) :
    ∃ e : (modelUniv .PSU n p f Fact.out).K ≃* Su (GaloisField p (2 * f)) p f n,
      ∀ R : Subgroup (modelUniv .PSU n p f Fact.out).K,
        R ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p f Fact.out).D ↔
          R.map e.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
            (by have := hadm.2.2.1; omega : 2 ≤ n) := by
  have hf : 1 ≤ f := hadm.2.1
  have : NeZero (2 * f) := ⟨by omega⟩
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul p f hf
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hn2 : 2 ≤ n := by omega
  obtain ⟨P, hP⟩ := Unitary.exists_wittMatrix hF n
  obtain ⟨k, γ, hγlong, hγ, hγ'⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_longest_root_psu
    Fact.out hadm
  obtain ⟨i₀, hR₀⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_isLongRootSU2_map_rankOne hF hp2
    hn2 hγ hγ' P hP
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .PSU n p f Fact.out
    trivial hadm (by decide) (by decide)
  have hM : Generic.modelUniv .PSU n p f Fact.out =
      ⟨↥(Unitary.SU (unitaryInvolution (GaloisField p (2 * f)) p f) n),
        Unitary.rootDatum (card_galoisField_two_mul p f hf) n⟩ :=
    (rfl : Generic.modelUniv .PSU n p f Fact.out =
      CFSG.ClassicalInvolution.ModelFacts.modelUniv .PSU n p f Fact.out).trans
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv_PSU hf)
  suffices key : ∀ M : LieUniversal, M =
      ⟨↥(Unitary.SU (unitaryInvolution (GaloisField p (2 * f)) p f) n),
        Unitary.rootDatum (card_galoisField_two_mul p f hf) n⟩ →
      FundamentalSingleClass .PSU M.D →
      ∃ e : M.K ≃* Su (GaloisField p (2 * f)) p f n, ∀ R : Subgroup M.K,
        R ∈ fundamentalSubgroups .PSU M.D ↔ R.map e.toMonoidHom ∈
          longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hn2 from
    key _ hM hsingle
  intro M hM' hs
  subst hM'
  refine ⟨Unitary.conjEquiv P hP, fun R => ?_⟩
  obtain ⟨R0, hR0f, hR0L⟩ : ∃ R0 : Subgroup (Unitary.SU (unitaryInvolution
      (GaloisField p (2 * f)) p f) n), R0 ∈ fundamentalSubgroups .PSU
        (Unitary.rootDatum (card_galoisField_two_mul p f hf) n) ∧
      R0.map (Unitary.conjEquiv P hP).toMonoidHom ∈
        longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hn2 :=
    ⟨_, ⟨1, γ, Or.inl hγlong, (conjSub_one _).symm⟩, ⟨i₀, hR₀⟩⟩
  constructor
  · intro hR
    obtain ⟨g, rfl⟩ := hs R0 hR0f R hR
    show (R0.map (MulAut.conj g).toMonoidHom).map (Unitary.conjEquiv P hP).toMonoidHom ∈ _
    rw [map_map_conj]
    exact longRootSetU_conjInvariant hn2 _ _ hR0L
  · intro hL
    obtain ⟨i, hi⟩ := hL
    obtain ⟨i', hi'⟩ := hR0L
    obtain ⟨c, hc⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_conj_of_isLongRootSU2 hi hi'
    have hRR : R = conjSub ((Unitary.conjEquiv P hP).symm c) R0 := by
      apply Subgroup.map_injective (f := (Unitary.conjEquiv P hP).toMonoidHom)
        (Unitary.conjEquiv P hP).injective
      rw [hc]
      show _ = (R0.map (MulAut.conj ((Unitary.conjEquiv P hP).symm c)).toMonoidHom).map _
      rw [map_map_conj]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [hRR]
    obtain ⟨g, γ', hγ', rfl⟩ := hR0f
    exact ⟨(Unitary.conjEquiv P hP).symm c * g, γ', hγ', (conjSub_mul _ _ _).symm⟩

theorem exists_psu_hom (hp2 : p ≠ 2) {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) (ht : D.tag i = .PSU) {n : ℕ}
    (hr : D.rank i = n) (hn : 2 ≤ n) :
    ∃ ψ : Su (GaloisField p (2 * f)) p f n →* X,
      ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f n) ∧ ψ.range = (D.hom i).range ∧
      ∀ K : Subgroup X, (∃ R ∈ fundamentalSubgroups (D.tag i)
          (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, K = R.map (D.hom i)) ↔
        ∃ L ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hn, K = L.map ψ := by
  have key : ∀ (t : StatedLieTag) (n' e : ℕ) (hT : t = .PSU) (hN : n' = n) (hE : e = f)
      (φ : (modelUniv t n' p e Fact.out).K →* X) (hφ : φ.ker ≤ Subgroup.center _),
      StatedLieAdmissible t n' p e →
      ∃ ψ : Su (GaloisField p (2 * f)) p f n →* X,
        ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f n) ∧ ψ.range = φ.range ∧
        ∀ K : Subgroup X, (∃ R ∈ fundamentalSubgroups t (modelUniv t n' p e Fact.out).D,
            K = R.map φ) ↔
          ∃ L ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hn, K = L.map ψ := by
    intro t n' e hT hN hE φ hφ hA
    have hE' : f = e := hE.symm
    subst hT hN hE'
    obtain ⟨e, he⟩ := psu_model_equiv hp2 hA
    refine ⟨φ.comp e.symm.toMonoidHom, ?_, ?_, fun K => ?_⟩
    · intro x hx
      have h1 : e.symm x ∈ Subgroup.center (modelUniv .PSU _ p f Fact.out).K :=
        hφ (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
      rw [Subgroup.mem_center_iff] at h1 ⊢
      intro y
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact h1 (e.symm y)
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
        ← MonoidHom.range_eq_map]
    · constructor
      · rintro ⟨R, hR, rfl⟩
        refine ⟨R.map e.toMonoidHom, (he R).mp hR, ?_⟩
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp
      · rintro ⟨L, hL, rfl⟩
        refine ⟨L.map e.symm.toMonoidHom, (he _).mpr ?_, ?_⟩
        · rw [Subgroup.map_map]
          have : (e.toMonoidHom.comp e.symm.toMonoidHom) = MonoidHom.id _ := by
            ext x; simp
          rw [this, Subgroup.map_id]
          exact hL
        · rw [Subgroup.map_map]
  have he : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h; exact absurd h (by decide)
  exact key _ _ _ ht hr he (D.hom i) (D.ker_le_center i) (D.admissible i)

section Dict

variable {G : Type} [Group G]

@[expose] def LocalShapeU (p f m : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∃ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x), D.card = 2 ∧
    ∃ i₀ i₁ : Fin D.card, i₀ ≠ i₁ ∧ D.tag i₀ = .PSL ∧ D.rank i₀ = 2 ∧ D.tag i₁ = .PSU ∧
      D.rank i₁ = m + 1

structure ShapeUDict (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (z : G) where
  ψ : Su (GaloisField p (2 * f)) p f (m + 1) →* locQuot Ω z
  ker_le : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f (m + 1))
  Q₀ : Subgroup (locQuot Ω z)
  commutes : Commutes Q₀ ψ.range
  mem_fam : ∀ (hk : 2 ≤ m + 1), ∀ L ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p)
    (f := f) hk, L.map ψ ∈ locFamily Ω z
  fam_cases : ∀ (hk : 2 ≤ m + 1), ∀ K ∈ locFamily Ω z, K ≤ Q₀ ∨
    ∃ L ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hk, K = L.map ψ
  card_le : Nat.card Q₀ ≤ Nat.card SL(2, GaloisField p f)

theorem LocalShapeU.nonempty_dict [Finite G] (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (h : LocalShapeU p f m Ω z) :
    Nonempty (ShapeUDict p f m Ω z) := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  have hk : 2 ≤ m + 1 := by omega
  obtain ⟨ψ₁, hker₁, hrange₁, hfund₁⟩ := exists_psu_hom hp2 D i₁ ht₁ hr₁ hk
  obtain ⟨ψ₀, hker₀, hrange₀, hfund₀⟩ := exists_psl_hom D i₀ ht₀ (k := 1) hr₀
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hΦ : ConjInvariant (locFamily Ω z) :=
    conjInvariant_oddQuotientFamily (inClass_local hΩ {z} ⟨K, hKz⟩).conjInvariant
  have hsingle : FundamentalSingleClass (D.tag i₁)
      (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ p _ _ (D.isFundTag i₁)
      (D.admissible i₁) (by rw [ht₁]; decide) (by rw [ht₁]; decide)
  refine ⟨{
    ψ := ψ₁
    ker_le := hker₁
    Q₀ := (D.hom i₀).range
    commutes := ?_
    mem_fam := ?_
    fam_cases := ?_
    card_le := ?_ }⟩
  · rw [hrange₁]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₀ i₁ hne a b
  · intro hk' L hL
    obtain ⟨R', hR', hRR'⟩ := (hfund₁ (L.map ψ₁)).mpr ⟨L, hL, rfl⟩
    rw [hRR']
    exact D.map_mem_of_single_class hΦ i₁ hsingle hR'
  · intro hk' K' hK'
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K' hK'
    have hi := i.isLt
    have hi₀ := i₀.isLt
    have hi₁ := i₁.isLt
    have hne' : i₀.val ≠ i₁.val := fun e => hne (Fin.ext e)
    have : i = i₀ ∨ i = i₁ := by
      rcases Nat.lt_or_ge i.val 1 with h1 | h1
      · by_cases h0 : i₀.val = 0
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
      · by_cases h0 : i₀.val = 1
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
    rcases this with rfl | rfl
    · exact Or.inl (Subgroup.map_le_range _ _)
    · obtain ⟨L, hL, hLL⟩ := (hfund₁ _).mp ⟨R, hR, rfl⟩
      exact Or.inr ⟨L, hL, hLL⟩
  · show Nat.card (D.hom i₀).range ≤ _
    rw [← hrange₀]
    exact Nat.card_le_card_of_surjective (ψ₀.rangeRestrict) ψ₀.rangeRestrict_surjective

end Dict

section Members

variable {G : Type} [Group G]

theorem typeU_card_field (hq : 5 ≤ p ^ f) : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
  card_galoisField_two_mul p f (by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h)

theorem isPerfect_su (hq : 5 ≤ p ^ f) {n : ℕ} (hn3 : 3 ≤ n) :
    Group.IsPerfect (Su (GaloisField p (2 * f)) p f n) := by
  have hK := typeU_card_field (p := p) (f := f) hq
  have h := (Unitary.isQuasisimple_statedSU_of_card (n := n) hK hn3
    (Transfer.pair_ne_three_two_of_five_le hq)).1
  have h2 := Unitary.isQuasisimple_of_mulEquiv
    (MulEquiv.subgroupCongr (Unitary.SUid_eq_statedSU hK n)).symm h
  exact h2.1

variable [Finite G]

theorem typeU_locImg_self_le_Q₀ (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 2 ≤ m)
    {Ω : Set (Subgroup G)} {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (d : ShapeUDict p f m Ω z) : locImg Ω z K ≤ d.Q₀ := by
  have hk : 2 ≤ m + 1 := by omega
  have hn3 : 3 ≤ m + 1 := by omega
  have hF := typeU_card_field (p := p) (f := f) hq
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, hKz, rfl⟩
  rcases d.fam_cases hk _ hmem with h | ⟨L, hL, hLK⟩
  · exact h
  · exfalso
    let zY : ↥(locLayer Ω z) := ⟨z, le_centralizingLayer hKz hz.mem⟩
    have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY ∈
        locImg Ω z K := ⟨zY, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
    rw [hLK] at hzK
    obtain ⟨r, hrR, hr⟩ := hzK
    have hcentral : ∀ w : locQuot Ω z,
        w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY * w := by
      intro w
      obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (centralizingLayer_le_centralizer Ω {z} w'.2)
    have hrc : r ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f (m + 1)) := by
      have := isPerfect_su (p := p) (f := f) hq hn3
      refine mem_center_of_comm_mem_center fun s => d.ker_le ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, hr]
      rw [commutatorElement_def, ← hcentral (d.ψ s), mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨i, hi⟩ := hL
    have hr1 : r = 1 := by
      have hker : (QuotientGroup.mk' (Subgroup.center
          (Su (GaloisField p (2 * f)) p f (m + 1)))).ker ≤
          Subgroup.center (Su (GaloisField p (2 * f)) p f (m + 1)) := by
        rw [QuotientGroup.ker_mk']
      exact Transfer.eq_one_of_mem_ker_of_isLongRootSU2 hF hp2 hq hn3 hi hker r hrR
        (by rw [QuotientGroup.ker_mk']; exact hrc)
    rw [hr1, map_one] at hr
    have hO : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω z) :=
      (QuotientGroup.eq_one_iff _).mp hr.symm
    have h2 : orderOf zY = 2 := by
      rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two
    have h3 := orderOf_dvd_natCard (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z))
    have h4 : orderOf (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h2
    rw [h4] at h3
    have := (CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω z)))
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h3)

theorem typeU_eq_of_locImg_le_Q₀ (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 2 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (d : ShapeUDict p f m Ω z) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLQ : locImg Ω z L ≤ d.Q₀) : L = K := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hKQ := typeU_locImg_self_le_Q₀ hp2 hq hm hK hz d
  have hcL := card_locImg hΩ hex hL
  have hcK := card_locImg hΩ hex hKz
  have e1 : locImg Ω z L = d.Q₀ := Subgroup.eq_of_le_of_card_ge hLQ (by rw [hcL]; exact d.card_le)
  have e2 : locImg Ω z K = d.Q₀ := Subgroup.eq_of_le_of_card_ge hKQ (by rw [hcK]; exact d.card_le)
  exact locImg_injOn hΩ hP1 hL hKz (e1.trans e2.symm)

theorem typeU_exists_root_of_ne (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 2 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (d : ShapeUDict p f m Ω z) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLK : L ≠ K) :
    ∃ R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by omega : 2 ≤ m + 1),
      locImg Ω z L = R.map d.ψ := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  rcases d.fam_cases (by omega) _ hmem with h | h
  · exact absurd (typeU_eq_of_locImg_le_Q₀ hp2 hq hm hΩ hex hK hz hP1 d hL h) hLK
  · obtain ⟨R, hR, hLR⟩ := h
    exact ⟨R, hR, hLR⟩

theorem typeU_exists_member_of_root (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 2 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z}) (d : ShapeUDict p f m Ω z)
    {R : Subgroup (Su (GaloisField p (2 * f)) p f (m + 1))}
    (hR : R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by omega : 2 ≤ m + 1)) :
    ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = R.map d.ψ := by
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp (d.mem_fam (by omega) R hR)
  refine ⟨L, hL, fun hLK => ?_, hLR⟩
  subst hLK
  have h1 : Commutes (locImg Ω z L) (locImg Ω z L) := by
    intro a ha b hb
    have hb' : b ∈ d.ψ.range := by
      rw [hLR] at hb
      obtain ⟨c, _, rfl⟩ := hb
      exact ⟨c, rfl⟩
    exact d.commutes a (typeU_locImg_self_le_Q₀ hp2 hq hm hK hz d ha) b hb'
  exact not_commutes_self_of_isClassicalMember hz
    ((commutes_iff_locImg hΩ hP1 hL hL).mpr h1)

theorem typeU_commutes_K_of_ne (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 2 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (d : ShapeUDict p f m Ω z) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLK : L ≠ K) : Commutes K L := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  obtain ⟨R, hR, hLR⟩ := typeU_exists_root_of_ne hp2 hq hm hΩ hex hK hz hP1 d hL hLK
  refine commutes_of_commutes_locImg hΩ hP1 hKz hL ?_
  have := d.commutes
  intro a ha b hb
  rw [hLR] at hb
  exact this a (typeU_locImg_self_le_Q₀ hp2 hq hm hK hz d ha) b
    (by obtain ⟨c, _, rfl⟩ := hb; exact ⟨c, rfl⟩)

end Members

end CFSG.ClassicalInvolution.RouteD
