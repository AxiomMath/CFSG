module

public import CFSG.ClassicalInvolution.RouteD.LocalTwin
public import CFSG.ClassicalInvolution.RouteD.LocalRoot
public import CFSG.ClassicalInvolution.ModelFacts.StandardPair

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime]

structure ShapeDictT (p f : ℕ) [Fact p.Prime] (tY : StatedLieTag) (nY : ℕ) {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (z : G) where
  ψ : (modelUniv tY nY p f Fact.out).K →* locQuot Ω z
  ker_le : ψ.ker ≤ Subgroup.center _
  Q₀ : Subgroup (locQuot Ω z)
  commutes : Commutes Q₀ ψ.range
  mem_fam : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
    R.map ψ ∈ locFamily Ω z
  fam_cases : ∀ K ∈ locFamily Ω z, K ≤ Q₀ ∨
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D, K = R.map ψ
  card_le : Nat.card Q₀ ≤ Nat.card SL(2, GaloisField p f)

section Dict

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem exists_hom_of_comp (D : LieSystemData p f X Φ) (i : Fin D.card) {tY : StatedLieTag}
    {nY : ℕ} (ht : D.tag i = tY) (hr : D.rank i = nY) (hY : tY ≠ .trialityD4) :
    ∃ ψ : (modelUniv tY nY p f Fact.out).K →* X, ψ.ker ≤ Subgroup.center _ ∧
      ψ.range = (D.hom i).range ∧
      ∀ K : Subgroup X, (∃ R ∈ fundamentalSubgroups (D.tag i)
          (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, K = R.map (D.hom i)) ↔
        ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D, K = R.map ψ := by
  have key : ∀ (t : StatedLieTag) (n e : ℕ) (hT : t = tY) (hN : n = nY) (hE : e = f)
      (φ : (modelUniv t n p e Fact.out).K →* X) (hφ : φ.ker ≤ Subgroup.center _),
      ∃ ψ : (modelUniv tY nY p f Fact.out).K →* X, ψ.ker ≤ Subgroup.center _ ∧
        ψ.range = φ.range ∧
        ∀ K : Subgroup X, (∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
            K = R.map φ) ↔
          ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D, K = R.map ψ := by
    intro t n e hT hN hE φ hφ
    subst hT hN hE
    exact ⟨φ, hφ, rfl, fun K => Iff.rfl⟩
  have he : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h; exact absurd h hY
  exact key _ _ _ ht hr he (D.hom i) (D.ker_le_center i)

theorem singleClass_of_comp (D : LieSystemData p f X Φ) (i : Fin D.card) {tY : StatedLieTag}
    {nY : ℕ} (ht : D.tag i = tY) (hr : D.rank i = nY) (hY : tY ≠ .trialityD4)
    (hsc : FundamentalSingleClass tY (modelUniv tY nY p f Fact.out).D) :
    FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D := by
  have key : ∀ (t : StatedLieTag) (n e : ℕ) (hT : t = tY) (hN : n = nY) (hE : e = f),
      FundamentalSingleClass t (modelUniv t n p e Fact.out).D := by
    intro t n e hT hN hE
    subst hT hN hE
    exact hsc
  have he : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h; exact absurd h hY
  exact key _ _ _ ht hr he

end Dict

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}

theorem LocalShapeT.nonempty_dictT [Finite G] {tY : StatedLieTag} {nY : ℕ}
    (hY : tY ≠ .trialityD4) (hsc : FundamentalSingleClass tY (modelUniv tY nY p f Fact.out).D)
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    (h : LocalShapeT p f 1 tY nY Ω z) : Nonempty (ShapeDictT p f tY nY Ω z) := by
  obtain ⟨D, hcard, i₁, ht, hr, hrest⟩ := h
  have hc2 : D.card = 2 := hcard
  let i₀ : Fin D.card := ⟨if i₁.val = 0 then 1 else 0, by
    have := i₁.isLt
    split_ifs <;> omega⟩
  have hne : i₀ ≠ i₁ := by
    intro e
    have := congrArg Fin.val e
    simp only [i₀] at this
    split_ifs at this <;> omega
  have hall : ∀ i : Fin D.card, i = i₀ ∨ i = i₁ := by
    intro i
    have h1 := i.isLt
    have h2 := i₁.isLt
    by_cases h3 : i₁.val = 0
    · by_cases h4 : i.val = 0
      · right; exact Fin.ext (by omega)
      · left; exact Fin.ext (by simp only [i₀, h3]; simp; omega)
    · by_cases h4 : i.val = 0
      · left; exact Fin.ext (by simp only [i₀, h3]; simp; omega)
      · right; exact Fin.ext (by omega)
  obtain ⟨ht₀, hr₀⟩ := hrest i₀ hne
  obtain ⟨ψ, hker, hrange, hfund⟩ := exists_hom_of_comp D i₁ ht hr hY
  obtain ⟨ψ₀, -, hrange₀, -⟩ := exists_psl_hom D i₀ ht₀ (k := 1) hr₀
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hΦ : ConjInvariant (locFamily Ω z) :=
    conjInvariant_oddQuotientFamily (inClass_local hΩ {z} ⟨K, hKz⟩).conjInvariant
  have hsingle := singleClass_of_comp D i₁ ht hr hY hsc
  refine ⟨{
    ψ := ψ
    ker_le := hker
    Q₀ := (D.hom i₀).range
    commutes := ?_
    mem_fam := ?_
    fam_cases := ?_
    card_le := ?_ }⟩
  · rw [hrange]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₀ i₁ hne a b
  · intro R hR
    obtain ⟨R', hR', hRR'⟩ := (hfund (R.map ψ)).mpr ⟨R, hR, rfl⟩
    rw [hRR']
    exact D.map_mem_of_single_class hΦ i₁ hsingle hR'
  · intro K' hK'
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K' hK'
    rcases hall i with rfl | rfl
    · exact Or.inl (Subgroup.map_le_range _ _)
    · obtain ⟨R', hR', hRR'⟩ := (hfund _).mp ⟨R, hR, rfl⟩
      exact Or.inr ⟨R', hR', hRR'⟩
  · show Nat.card (D.hom i₀).range ≤ _
    rw [← hrange₀]
    exact Nat.card_le_card_of_surjective ψ₀.rangeRestrict ψ₀.rangeRestrict_surjective


theorem perfect_of_le_commutator {X : Type} [Group X] {H : Subgroup X} (h : H ≤ ⁅H, H⁆) :
    Group.IsPerfect ↥H := by
  refine Subgroup.isPerfect_iff.mpr (le_antisymm ?_ h)
  exact Subgroup.commutator_le.mpr fun a ha b hb =>
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

structure YData (p f : ℕ) [Fact p.Prime] (tY : StatedLieTag) (nY : ℕ) : Prop where
  ne_d4 : tY ≠ .trialityD4
  sc : FundamentalSingleClass tY (modelUniv tY nY p f Fact.out).D
  perfK : Group.IsPerfect (modelUniv tY nY p f Fact.out).K
  perfR : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D, R ≤ ⁅R, R⁆
  central : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
    ∀ r ∈ R, r ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K → r = 1
  std : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
    ∃ R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      ∃ W : Subgroup (modelUniv tY nY p f Fact.out).K,
        LinearBlockStandardPair (GaloisField p f) W R R'

structure ETCtx (p f : ℕ) [Fact p.Prime] (tY : StatedLieTag) (nY : ℕ) {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) where
  hp2 : p ≠ 2
  hq : 5 ≤ p ^ f
  hΩ : InClass p f Ω
  hex : ExactMembers Ω
  hK : K ∈ Ω
  hz : IsClassicalMember p f K z
  hP1 : LocalOddCentral Ω {z}
  d : ShapeDictT p f tY nY Ω z
  hF : OddCoverSL3 (GaloisField p f)
  hY : YData p f tY nY

namespace ETCtx

variable {tY : StatedLieTag} {nY : ℕ} {K : Subgroup G} (c : ETCtx p f tY nY Ω K z)

include c

theorem hf : f ≠ 0 := by
  rintro rfl
  have := c.hq
  simp at this

theorem card_eq : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f c.hf

theorem hodd : Odd (Nat.card (GaloisField p f)) := by
  rw [c.card_eq]
  exact (Nat.Prime.odd_of_ne_two Fact.out c.hp2).pow

theorem h4 : 4 ≤ Nat.card (GaloisField p f) := by
  have := c.hq
  rw [c.card_eq]
  omega

theorem hKz : K ∈ centralizingMembers Ω {z} :=
  ⟨c.hK, le_centralizer_of_isClassicalMember c.hz⟩

variable [Finite G]

theorem locImg_self_le_Q₀ : locImg Ω z K ≤ c.d.Q₀ := by
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, c.hKz, rfl⟩
  rcases c.d.fam_cases _ hmem with h | ⟨R, hR, hRK⟩
  · exact h
  · exfalso
    let zY : ↥(locLayer Ω z) := ⟨z, le_centralizingLayer c.hKz c.hz.mem⟩
    have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY ∈
        locImg Ω z K := ⟨zY, Subgroup.mem_subgroupOf.mpr c.hz.mem, rfl⟩
    rw [hRK] at hzK
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
    have hrc : r ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K := by
      have := c.hY.perfK
      refine mem_center_of_comm_mem_center fun s => c.d.ker_le ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, hr]
      rw [commutatorElement_def, ← hcentral (c.d.ψ s), mul_inv_cancel_right, mul_inv_cancel]
    have hr1 : r = 1 := c.hY.central R hR r hrR hrc
    rw [hr1, map_one] at hr
    have hO : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω z) :=
      (QuotientGroup.eq_one_iff _).mp hr.symm
    have h2 : orderOf zY = 2 := by
      rw [Subgroup.orderOf_mk]; exact c.hz.orderOf_eq_two
    have h3 := orderOf_dvd_natCard (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z))
    have h4 : orderOf (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h2
    rw [h4] at h3
    have := CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω z))
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h3)

theorem eq_of_locImg_le_Q₀ {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLQ : locImg Ω z L ≤ c.d.Q₀) : L = K := by
  have hKQ := c.locImg_self_le_Q₀
  have hcL := card_locImg c.hΩ c.hex hL
  have hcK := card_locImg c.hΩ c.hex c.hKz
  have e1 : locImg Ω z L = c.d.Q₀ :=
    Subgroup.eq_of_le_of_card_ge hLQ (by rw [hcL]; exact c.d.card_le)
  have e2 : locImg Ω z K = c.d.Q₀ :=
    Subgroup.eq_of_le_of_card_ge hKQ (by rw [hcK]; exact c.d.card_le)
  exact locImg_injOn c.hΩ c.hP1 hL c.hKz (e1.trans e2.symm)

theorem exists_fund_of_ne {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      locImg Ω z L = R.map c.d.ψ := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  rcases c.d.fam_cases _ hmem with h | h
  · exact absurd (c.eq_of_locImg_le_Q₀ hL h) hLK
  · exact h

theorem exists_member_of_fund {R : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) :
    ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = R.map c.d.ψ := by
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp (c.d.mem_fam R hR)
  refine ⟨L, hL, fun hLK => ?_, hLR⟩
  subst hLK
  have h1 : Commutes (locImg Ω z L) (locImg Ω z L) := by
    intro a ha b hb
    have hb' : b ∈ c.d.ψ.range := by
      rw [hLR] at hb
      obtain ⟨x, _, rfl⟩ := hb
      exact ⟨x, rfl⟩
    exact c.d.commutes a (c.locImg_self_le_Q₀ ha) b hb'
  exact not_commutes_self_of_isClassicalMember c.hz
    ((commutes_iff_locImg c.hΩ c.hP1 hL hL).mpr h1)

theorem commutes_K_of_ne {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    Commutes K L := by
  obtain ⟨R, hR, hLR⟩ := c.exists_fund_of_ne hL hLK
  refine commutes_of_commutes_locImg c.hΩ c.hP1 c.hKz hL ?_
  intro a ha b hb
  rw [hLR] at hb
  exact c.d.commutes a (c.locImg_self_le_Q₀ ha) b (by obtain ⟨x, _, rfl⟩ := hb; exact ⟨x, rfl⟩)

theorem eq_of_locImg_eq {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (h : locImg Ω z L = locImg Ω z L') : L = L' :=
  locImg_injOn c.hΩ c.hP1 hL hL' h

theorem commutes_iff_fund {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) :
    Commutes L L' ↔ Commutes R R' := by
  constructor
  · intro h
    have h1 := commutes_locImg_of_commutes (x := z) (Ω := Ω) h
    rw [hLR, hLR'] at h1
    exact commutes_of_commutes_map c.d.ψ c.d.ker_le
      (perfect_of_le_commutator (c.hY.perfR R hR)) h1
  · intro h
    refine commutes_of_commutes_locImg c.hΩ c.hP1 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map _ h

end ETCtx


section StdPair

variable {F : Type} [Field F] {X Y : Type} [Group X] [Group Y]

theorem mem_center_of_map_mem_center (θ : SL(3, F) →* X)
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) {x : SL(3, F)} (hx : θ x ∈ Subgroup.center X) :
    x ∈ Subgroup.center SL(3, F) := by
  have : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  refine mem_center_of_comm_mem_center fun s => hker ?_
  rw [MonoidHom.mem_ker, map_commutatorElement]
  have h := Subgroup.mem_center_iff.mp hx (θ s)
  rw [commutatorElement_def, ← h]
  group

theorem linearBlockStandardPair_map_central {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) (φ : X →* Y) (hφ : φ.ker ≤ Subgroup.center X) :
    LinearBlockStandardPair F (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, hcases⟩ := h
  refine ⟨φ.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · intro x hx
    exact mem_center_of_map_mem_center θ hker (hφ (MonoidHom.mem_ker.mpr hx))
  · rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

theorem eq_one_of_mem_center_of_stdPair {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) :
    (∀ r ∈ U, r ∈ Subgroup.center X → r = 1) ∧ (∀ r ∈ V, r ∈ Subgroup.center X → r = 1) := by
  obtain ⟨θ, c, -, hker, hcases⟩ := h
  have key : ∀ B : Subgroup SL(3, F), (∀ b ∈ B, b ∈ Subgroup.center SL(3, F) → b = 1) →
      ∀ r ∈ (B.map (MulAut.conj c⁻¹).toMonoidHom).map θ, r ∈ Subgroup.center X → r = 1 := by
    intro B hB r hr hrc
    obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := hr
    set x : SL(3, F) := (MulAut.conj c⁻¹).toMonoidHom b with hxdef
    have hx : x ∈ Subgroup.center SL(3, F) := mem_center_of_map_mem_center θ hker hrc
    have hxb : x = c⁻¹ * b * c := by simp [hxdef]
    have hcomm : c * x = x * c := Subgroup.mem_center_iff.mp hx c
    have hb_eq : b = x := by
      calc b = c * (c⁻¹ * b * c) * c⁻¹ := by group
        _ = c * x * c⁻¹ := by rw [hxb]
        _ = x * c * c⁻¹ := by rw [hcomm]
        _ = x := by group
    have hb1 : b = 1 := hB b hb (hb_eq ▸ hx)
    have hx1 : x = 1 := hb_eq ▸ hb1
    show θ x = 1
    rw [hx1, map_one]
  have h12 : ∀ b ∈ CFSG.ClassicalInvolution.WeakCT.B12 F, b ∈ Subgroup.center SL(3, F) → b = 1 := fun b hb hz =>
    CFSG.ClassicalInvolution.WeakCT.B12_center b hb hz
  have h23 : ∀ b ∈ CFSG.ClassicalInvolution.WeakCT.B23 F, b ∈ Subgroup.center SL(3, F) → b = 1 := fun b hb hz =>
    CFSG.ClassicalInvolution.WeakCT.B23_center b hb hz
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ key _ h12, h2 ▸ key _ h23⟩
  · exact ⟨h2 ▸ key _ h23, h1 ▸ key _ h12⟩

end StdPair


namespace ETCtx

variable {tY : StatedLieTag} {nY : ℕ} {K : Subgroup G} [Finite G]

theorem stdPair_of_fund (c : ETCtx p f tY nY Ω K z) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    {W : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hW : LinearBlockStandardPair (GaloisField p f) W R R')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) :
    ∃ W' : Subgroup G, LinearBlockStandardPair (GaloisField p f) W' L L' := by
  have := linearBlockStandardPair_map_central hW c.d.ψ c.d.ker_le
  rw [← hLR, ← hLR'] at this
  exact linearBlockStandardPair_of_locImg (by have := c.hq; omega) c.hF c.hΩ c.hP1 hL hL' this

theorem exists_nodes (c : ETCtx p f tY nY Ω K z) {r : ℕ}
    (R : Fin r → Subgroup (modelUniv tY nY p f Fact.out).K)
    (hR : ∀ a, R a ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (adj : Fin r → Fin r → Prop)
    (hcomm : ∀ a b, a ≠ b → ¬ adj a b → ¬ adj b a → Commutes (R a) (R b))
    (hstd : ∀ a b, adj a b → ∃ W : Subgroup (modelUniv tY nY p f Fact.out).K,
      LinearBlockStandardPair (GaloisField p f) W (R a) (R b)) :
    ∃ j : Fin r → Subgroup G, (∀ a, j a ∈ centralizingMembers Ω {z} ∧ j a ≠ K ∧
        locImg Ω z (j a) = (R a).map c.d.ψ) ∧
      (∀ a b, a ≠ b → ¬ adj a b → ¬ adj b a → Commutes (j a) (j b)) ∧
      (∀ a b, adj a b → ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
      (∀ a, Commutes K (j a)) := by
  choose j hj using fun a => c.exists_member_of_fund (hR a)
  refine ⟨j, fun a => ⟨(hj a).1, (hj a).2.1, (hj a).2.2⟩, ?_, ?_, ?_⟩
  · intro a b hab h1 h2
    exact (c.commutes_iff_fund (hj a).1 (hj b).1 (hR a) (hj a).2.2 (hj b).2.2).mpr
      (hcomm a b hab h1 h2)
  · intro a b hadj
    obtain ⟨W, hW⟩ := hstd a b hadj
    exact c.stdPair_of_fund (hj a).1 (hj b).1 hW (hj a).2.2 (hj b).2.2
  · intro a
    exact c.commutes_K_of_ne (hj a).1 (hj a).2.1

theorem exists_partner_transport (c : ETCtx p f tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {M : Subgroup G} (hM : M ∈ Ω) (hMK : M ≠ K)
    (hKM : Commutes K M) :
    ∃ β ∈ Ω, (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) ∧
      Commutes β M := by
  obtain ⟨g, hg⟩ := hsingle M hM
  have hw : g * z * g⁻¹ ∈ M := hg ▸ conj_mem_conjSub c.hz.mem
  have hK'm : conjSub g⁻¹ K ∈ centralizingMembers Ω {z} :=
    conjSub_inv_mem_centralizingMembers c.hΩ.conjInvariant c.hK hw hKM
  have hK'ne : conjSub g⁻¹ K ≠ K := by
    intro h
    apply hMK
    calc M = conjSub g K := hg
      _ = conjSub g (conjSub g⁻¹ K) := by rw [h]
      _ = K := conjSub_conjSub_inv g K
  obtain ⟨R₀, hR₀, hKR₀⟩ := c.exists_fund_of_ne hK'm hK'ne
  obtain ⟨R', hR', W, hW⟩ := c.hY.std R₀ hR₀
  obtain ⟨β', hβ'm, hβ'K, hβ'img⟩ := c.exists_member_of_fund hR'
  obtain ⟨W', hW'⟩ := c.stdPair_of_fund hK'm hβ'm hW hKR₀ hβ'img
  refine ⟨conjSub g β', c.hΩ.conjInvariant g β' hβ'm.1, ⟨conjSub g W', ?_⟩, ?_⟩
  · have h : LinearBlockStandardPair (GaloisField p f) (conjSub g W') (conjSub g (conjSub g⁻¹ K))
        (conjSub g β') := ModelFacts.linearBlockStandardPair_map_conj hW' g
    rwa [conjSub_conjSub_inv] at h
  · rw [hg]
    exact (commutes_conjSub_iff g).mpr (c.commutes_K_of_ne hβ'm hβ'K).symm

end ETCtx

end CFSG.ClassicalInvolution.RouteD
