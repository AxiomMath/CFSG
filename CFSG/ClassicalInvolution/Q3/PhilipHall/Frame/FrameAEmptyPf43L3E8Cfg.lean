module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Shape2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43Cfg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement

section Cfg

structure L3E8Std {T : Type} [Group T] (K : Subgroup T) (z : T) (J : Subgroup T) (zJ : T)
    (H : Subgroup T) : Prop extends FrameStd K z J zJ where
  hH : omegaGen (aStar (CoreAssembly.conjClass K) K) = H
  row : Thm3RowL3E8 (⊤ : Subgroup ↥H)

structure L3E8Cfg {T : Type} [Group T] [Finite T] (K : Subgroup T) (z : T) (J : Subgroup T)
    (zJ : T) (H Q E S : Subgroup T) : Prop extends FrameQCfg K z J zJ Q E S where
  hH : omegaGen (aStar (CoreAssembly.conjClass K) K) = H
  row : Thm3RowL3E8 (⊤ : Subgroup ↥H)
  faithful : IsFaithfulL3E8 (SecQuot (firstFactor K))

end Cfg

section SecAux

private theorem le_oddCore_of_odd {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (h : Odd (Nat.card N)) : N ≤ classicalInvolutionOddCore X :=
  le_sSup ⟨‹N.Normal›, h⟩

private theorem odd_card_oddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (classicalInvolutionOddCore X)) :=
  CFSG.ComponentClassification.OddCore.odd_card X

private theorem secQuot_equiv_of_sup {A X : Type} [Group A] [Group X] [Finite X]
    (ι : A →* X) (hι : Function.Injective ι) (N : Subgroup X) [N.Normal]
    (hN : Odd (Nat.card N)) (hsup : ι.range ⊔ N = ⊤) :
    Nonempty ((A ⧸ classicalInvolutionOddCore A) ≃* (X ⧸ classicalInvolutionOddCore X)) := by
  haveI : Finite A := Finite.of_injective ι hι
  have hNO : N ≤ classicalInvolutionOddCore X := le_oddCore_of_odd hN
  let ψ : A →* X ⧸ classicalInvolutionOddCore X :=
    (QuotientGroup.mk' (classicalInvolutionOddCore X)).comp ι
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ ι.range ⊔ N := by
      rw [hsup]
      exact Subgroup.mem_top x
    obtain ⟨g, hg, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨a, rfl⟩ := hg
    refine ⟨a, ?_⟩
    show (QuotientGroup.mk' (classicalInvolutionOddCore X)) (ι a) =
      (QuotientGroup.mk' (classicalInvolutionOddCore X)) (ι a * n)
    have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore X)) n = 1 :=
      (QuotientGroup.eq_one_iff n).mpr (hNO hn)
    rw [map_mul, h1, mul_one]
  have hker : ψ.ker = classicalInvolutionOddCore A := by
    ext a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      have h1 : ι a ∈ classicalInvolutionOddCore X := (QuotientGroup.eq_one_iff _).mp ha
      have hPodd : Odd (Nat.card ((classicalInvolutionOddCore X).comap ι)) := by
        have e1 : Nat.card (((classicalInvolutionOddCore X).comap ι).map ι) =
            Nat.card ((classicalInvolutionOddCore X).comap ι) :=
          Subgroup.card_map_of_injective hι
        have e2 : Nat.card (((classicalInvolutionOddCore X).comap ι).map ι) ∣
            Nat.card (classicalInvolutionOddCore X) :=
          Subgroup.card_dvd_of_le (Subgroup.map_comap_le ι _)
        rw [← e1]
        exact (odd_card_oddCore X).of_dvd_nat e2
      exact le_oddCore_of_odd hPodd h1
    · intro ha
      set B : Subgroup X := (classicalInvolutionOddCore A).map ι with hB
      have hBodd : Odd (Nat.card B) := by
        rw [hB, Subgroup.card_map_of_injective hι]
        exact odd_card_oddCore A
      have hDodd : Odd (Nat.card (N ⊔ B : Subgroup X)) :=
        CFSG.ComponentClassification.OddCore.odd_card_sup N B hN hBodd
      have hconj : ∀ g ∈ ι.range, ∀ d ∈ N ⊔ B, g * d * g⁻¹ ∈ N ⊔ B := by
        intro g hg d hd
        obtain ⟨n', hn', b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hd
        obtain ⟨a₀, rfl⟩ := hg
        obtain ⟨b', hb', rfl⟩ := hb
        have e : ι a₀ * (n' * ι b') * (ι a₀)⁻¹ =
            (ι a₀ * n' * (ι a₀)⁻¹) * ι (a₀ * b' * a₀⁻¹) := by
          rw [map_mul, map_mul, map_inv]
          group
        rw [e]
        exact (N ⊔ B).mul_mem (Subgroup.mem_sup_left (‹N.Normal›.conj_mem n' hn' _))
          (Subgroup.mem_sup_right ⟨a₀ * b' * a₀⁻¹,
            (inferInstance : (classicalInvolutionOddCore A).Normal).conj_mem b' hb' a₀, rfl⟩)
      have hDnormal : (N ⊔ B).Normal := by
        refine ⟨fun d hd x => ?_⟩
        have hx : x ∈ ι.range ⊔ N := by
          rw [hsup]
          exact Subgroup.mem_top x
        obtain ⟨g, hg, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
        have h1 : n * d * n⁻¹ ∈ N ⊔ B :=
          (N ⊔ B).mul_mem ((N ⊔ B).mul_mem (Subgroup.mem_sup_left hn) hd)
            ((N ⊔ B).inv_mem (Subgroup.mem_sup_left hn))
        have h2 := hconj g hg _ h1
        have e : g * n * d * (g * n)⁻¹ = g * (n * d * n⁻¹) * g⁻¹ := by group
        rw [e]
        exact h2
      have hDle : N ⊔ B ≤ classicalInvolutionOddCore X := le_oddCore_of_odd hDodd
      exact (QuotientGroup.eq_one_iff _).mpr (hDle (Subgroup.mem_sup_right ⟨a, ha, rfl⟩))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)⟩

private theorem isL3E8_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsL3E8 X) :
    IsL3E8 Y := by
  obtain ⟨E, hEn, hEab, hcard, ⟨q⟩⟩ := h
  haveI : (E.map e.toMonoidHom).Normal := hEn.map _ e.surjective
  have hEab' : IsElemAbelian 2 (E.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · rcases a with ⟨_, x₁, hx₁, rfl⟩
      rcases b with ⟨_, x₂, hx₂, rfl⟩
      apply Subtype.ext
      show e.toMonoidHom x₁ * e.toMonoidHom x₂ = e.toMonoidHom x₂ * e.toMonoidHom x₁
      rw [← map_mul, ← map_mul]
      congr 1
      have := hEab.1.1.comm ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
      simpa using congrArg Subtype.val this
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [← map_pow, hEab.2 x hx, map_one]
  refine ⟨E.map e.toMonoidHom, inferInstance, hEab', ?_, ⟨?_⟩⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hcard
  · exact (QuotientGroup.congr E (E.map e.toMonoidHom) e rfl).symm.trans q

end SecAux

section SecAux2

variable {T : Type} [Group T] [Finite T]

private theorem eq_one_of_mem_oddCore {X : Type} [Group X] [Finite X] {x : X}
    (hx : x ∈ classicalInvolutionOddCore X) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have hodd : Odd (orderOf x) :=
    (odd_card_oddCore X).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  exact orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow hodd (orderOf_dvd_of_pow_eq_one hk))

private theorem secMk_injective_of_isPGroup {Ht R : Subgroup T} (hRHt : R ≤ Ht)
    (hR : IsPGroup 2 R) :
    Function.Injective ((QuotientGroup.mk' (classicalInvolutionOddCore ↥Ht)).comp
      (Subgroup.inclusion hRHt)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨k, hk⟩ := hR a
  have h1 : Subgroup.inclusion hRHt a ∈ classicalInvolutionOddCore ↥Ht :=
    (QuotientGroup.eq_one_iff _).mp ha
  have hk' : (Subgroup.inclusion hRHt a) ^ 2 ^ k = 1 := by
    rw [← map_pow, hk, map_one]
  have h3 : Subgroup.inclusion hRHt a = 1 := eq_one_of_mem_oddCore h1 hk'
  exact (Subgroup.inclusion_injective hRHt) (by rw [h3, map_one])

private theorem q8_image {Ht R : Subgroup T} (hRHt : R ≤ Ht) (hR : IsPGroup 2 R)
    (hq : Nonempty (↥R ≃* QuaternionGroup 2)) {u : T} (hu : IsUniqueInvolution R u) :
    ∃ P : Subgroup (SecQuot Ht), Nonempty (↥P ≃* QuaternionGroup 2) ∧
      IsUniqueInvolution P
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥Ht) ⟨u, hRHt hu.mem⟩) := by
  set φ : ↥R →* SecQuot Ht := (QuotientGroup.mk' (classicalInvolutionOddCore ↥Ht)).comp
    (Subgroup.inclusion hRHt) with hφ
  have hinj : Function.Injective φ := secMk_injective_of_isPGroup hRHt hR
  refine ⟨φ.range, ?_, ⟨⟨⟨u, hu.mem⟩, rfl⟩, ?_, ?_, ?_⟩⟩
  · obtain ⟨e⟩ := hq
    exact ⟨(MonoidHom.ofInjective hinj).symm.trans e⟩
  · intro h
    apply hu.ne_one
    have : (⟨u, hu.mem⟩ : ↥R) = 1 := hinj (h.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  · have h1 : (⟨u, hRHt hu.mem⟩ : ↥Ht) * ⟨u, hRHt hu.mem⟩ = 1 := Subtype.ext hu.sq
    rw [← map_mul, h1, map_one]
  · rintro y ⟨r, rfl⟩ hy2
    have hr2 : r * r = 1 := hinj (by rw [map_mul, hy2, map_one])
    rcases hu.unique (r : T) r.2 (congrArg Subtype.val hr2) with h | h
    · left
      have : r = 1 := Subtype.ext h
      rw [this, map_one]
    · right
      have : r = ⟨u, hu.mem⟩ := Subtype.ext h
      rw [this]
      rfl

private theorem K_le_firstFactor (K : Subgroup T) : K ≤ firstFactor K := fun x hx =>
  (le_sup_left : omegaGen (aStar (CoreAssembly.conjClass K) K) ≤ firstFactor K)
    (le_omegaGen (Relation.ReflTransGen.refl :
      K ∈ aStar (CoreAssembly.conjClass K) K) hx)

variable {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}

private theorem J_le_firstFactor (hs : FrameStd K z J zJ) : J ≤ firstFactor K := fun x hx =>
  (le_sup_left : omegaGen (aStar (CoreAssembly.conjClass K) K) ≤ firstFactor K)
    (le_omegaGen (Relation.ReflTransGen.single ⟨hs.viol.mem, Or.inl ⟨z, zJ, hs.viol⟩⟩ :
      J ∈ aStar (CoreAssembly.conjClass K) K) hx)

private theorem exists_q8_K (hs : FrameStd K z J zJ) :
    ∃ R : Subgroup T, R ≤ K ∧ IsPGroup 2 R ∧ Nonempty (↥R ≃* QuaternionGroup 2) ∧
      IsUniqueInvolution R z := by
  have hz := hs.datum.unique
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup T))
    (bot_le : (⊥ : Subgroup T) ≤ K)
  obtain ⟨e⟩ := hs.datum.quat R hR
  have hu2 : e.symm (QuaternionGroup.a 2) * e.symm (QuaternionGroup.a 2) = 1 := by
    apply e.injective
    rw [map_mul, map_one, MulEquiv.apply_symm_apply]
    decide
  have hu1 : e.symm (QuaternionGroup.a 2) ≠ 1 := by
    intro h
    have := congrArg e h
    rw [MulEquiv.apply_symm_apply, map_one] at this
    revert this
    decide
  have huz : ((e.symm (QuaternionGroup.a 2) : ↥R) : T) = z := by
    rcases hz.unique _ (hR.1 (e.symm (QuaternionGroup.a 2)).2) (congrArg Subtype.val hu2) with h | h
    · exact absurd (Subtype.ext h) hu1
    · exact h
  have hzR : z ∈ R := huz ▸ (e.symm (QuaternionGroup.a 2)).2
  exact ⟨R, hR.1, hR.2.1, ⟨e⟩, hzR, hz.ne_one, hz.sq,
    fun y hy hy2 => hz.unique y (hR.1 hy) hy2⟩

private theorem exists_q8_J (hs : FrameStd K z J zJ) :
    ∃ R : Subgroup T, R ≤ J ∧ IsPGroup 2 R ∧ Nonempty (↥R ≃* QuaternionGroup 2) ∧
      IsUniqueInvolution R zJ := by
  obtain ⟨R, hRK, hR2, ⟨e⟩, hzR⟩ := exists_q8_K hs
  obtain ⟨g, hg⟩ := hs.viol.mem
  have hg' : conjSub g K = J := hg
  refine ⟨conjSub g R, ?_, ?_, ⟨?_⟩, ?_⟩
  · rw [← hg']
    exact conjSub_mono hRK
  · exact hR2.map (MulAut.conj g).toMonoidHom
  · exact (Subgroup.equivMapOfInjective R (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans e
  · have hzJ : zJ = g * z * g⁻¹ := by
      have h1 := hs.datum.unique.conj g
      rw [hg'] at h1
      exact hs.viol.hzJ.eq h1
    rw [hzJ]
    exact hzR.conj g

private theorem viol_comm {Λ : Set (Subgroup T)} (hΩ : HypOmegaGen Λ) {K J : Subgroup T}
    {zK zJ : T} (h : AViol Λ K J zK zJ) : zK * zJ = zJ * zK := by
  obtain ⟨-, -, U, hU, hUJ, hUN⟩ := h.star
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hU2 := Sec6Gen.isPGroup_of_mem_USet hΩ hU
  have hj : zJ ∈ Subgroup.normalizer (K : Set T) :=
    hUN (mem_of_isPGroup h.hzJ hUJ hU2 (by omega))
  have h1 := h.hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp hj)
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

private theorem viol_ne {Λ : Set (Subgroup T)} (hΩ : HypOmegaGen Λ) {K J : Subgroup T}
    {zK zJ : T} (hK : K ∈ Λ) (h : AViol Λ K J zK zJ) : zJ ≠ zK := by
  intro he
  subst he
  refine h.not_nbr ?_
  obtain ⟨R, hR, hRJ, -⟩ := exists_mem_RSet_ge h.mem (isPGroup_two_bot' (G := T)) bot_le
  exact ⟨h.mem, h.ne, R, hR, hRJ.1,
    hRJ.1.trans (Sec6Gen.le_normalizer_of_twin hΩ h.mem hK h.ne h.hzJ h.hzK)⟩

end SecAux2

section SecAux3

private theorem isPGroup_zpowers_of_pow {X : Type} [Group X] {u : X} {k : ℕ} (h : u ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers u) := by
  intro g
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, h, one_zpow]

private theorem F_comm {X : Type} [Group X] {F : Subgroup X} (hF : IsElemAbelian 2 F) {a b : X}
    (ha : a ∈ F) (hb : b ∈ F) : a * b = b * a := by
  have := hF.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

private theorem pCore_eq_of_faithful {X : Type} [Group X] {F : Subgroup X}
    (h : FaithfulL3E8 X F) : CFSG.pCore 2 X = F := by
  haveI := h.normal
  obtain ⟨e⟩ := h.quotient
  haveI : IsSimpleGroup L3Two := isSimpleGroup_l3Two
  let f : X →* L3Two := e.toMonoidHom.comp (QuotientGroup.mk' F)
  have hfs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective F)
  have hfker : ∀ x : X, f x = 1 ↔ x ∈ F := fun x => by
    show e (QuotientGroup.mk' F x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  apply le_antisymm
  · have hP2 : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
    haveI hPn : ((CFSG.pCore 2 X).map f).Normal :=
      (CFSG.pCore_normal (p := 2) (G := X)).map f hfs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 X).map f) with h0 | h0
    · intro x hx
      have : f x ∈ (CFSG.pCore 2 X).map f := ⟨x, hx, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact (hfker x).mp this
    · exfalso
      have hP2' : IsPGroup 2 ↥((CFSG.pCore 2 X).map f) := hP2.map f
      rw [h0] at hP2'
      obtain ⟨n, hn⟩ := hP2'.exists_card_eq
      rw [Subgroup.card_top] at hn
      have hcard : Nat.card L3Two = 168 := by
        rw [Nat.card_eq_fintype_card]
        decide +kernel
      have h3 : 3 ∣ 2 ^ n := by
        rw [← hn, hcard]
        norm_num
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  · exact le_sSup ⟨h.normal, fun g => ⟨1, by simpa using Subtype.ext (h.elemAbelian.2 g g.2)⟩⟩

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

private theorem mem_oddTwoCoreIn_iff {Ht : Subgroup T} {F : Subgroup (SecQuot Ht)}
    (hF : FaithfulL3E8 (SecQuot Ht) F) (x : ↥Ht) :
    (x : T) ∈ oddTwoCoreIn Ht ↔
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Ht) x ∈ F := by
  unfold oddTwoCoreIn
  show Ht.subtype x ∈ _ ↔ _
  rw [Subgroup.mem_map_iff_mem Ht.subtype_injective, Subgroup.mem_comap,
    pCore_eq_of_faithful hF]

private theorem cfg_mem_Q_iff (cfg : L3E8Cfg K z J zJ H Q E S) {F : Subgroup (SecQuot (firstFactor K))}
    (hF : FaithfulL3E8 (SecQuot (firstFactor K)) F) (x : ↥(firstFactor K)) :
    (x : T) ∈ Q ↔ QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) x ∈ F := by
  rw [cfg.hQ]
  exact mem_oddTwoCoreIn_iff hF x

private def phiE (cfg : L3E8Cfg K z J zJ H Q E S) : ↥E →* SecQuot (firstFactor K) :=
  (QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))).comp
    (Subgroup.inclusion (cfg.E_le_Q.trans cfg.Q_le_ht))

private theorem phiE_injective (cfg : L3E8Cfg K z J zJ H Q E S) : Function.Injective (phiE cfg) :=
  secMk_injective_of_isPGroup (cfg.E_le_Q.trans cfg.Q_le_ht) cfg.E_sylow.2.1

private theorem phiE_mem (cfg : L3E8Cfg K z J zJ H Q E S)
    {F : Subgroup (SecQuot (firstFactor K))} (hF : FaithfulL3E8 (SecQuot (firstFactor K)) F)
    (a : ↥E) : phiE cfg a ∈ F :=
  (cfg_mem_Q_iff cfg hF _).mp (cfg.E_le_Q a.2)

private theorem phiE_surjective (cfg : L3E8Cfg K z J zJ H Q E S)
    {F : Subgroup (SecQuot (firstFactor K))} (hF : FaithfulL3E8 (SecQuot (firstFactor K)) F)
    {f : SecQuot (firstFactor K)} (hf : f ∈ F) : ∃ a : ↥E, phiE cfg a = f := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective f
  have hπx : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) x = f := hx
  have hf2 : f ^ 2 = 1 := hF.elemAbelian.2 f hf
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  set u : ↥(firstFactor K) := x ^ m with hu
  have hu2 : u ^ 2 ^ k = 1 := by
    rw [hu, ← pow_mul, mul_comm, ← hord]
    exact pow_orderOf_eq_one x
  have hπu : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) u = f := by
    rw [hu, map_pow, hπx]
    obtain ⟨j, hj⟩ := hm
    rw [hj, pow_succ, pow_mul, hf2, one_pow, one_mul]
  have huQ : (u : T) ∈ Q := (cfg_mem_Q_iff cfg hF u).mpr (hπu ▸ hf)
  have hu2T : (u : T) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hu2
    simpa using this
  obtain ⟨c, hcQ, hc⟩ :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7.exists_conj_le_of_isSylow2In cfg.E_sylow
      (isPGroup_zpowers_of_pow hu2T) (Subgroup.zpowers_le.mpr huQ)
  have hcE : c⁻¹ * (u : T) * c ∈ E :=
    mem_conjSub_iff.mp (hc (Subgroup.mem_zpowers (u : T)))
  refine ⟨⟨c⁻¹ * (u : T) * c, hcE⟩, ?_⟩
  set c' : ↥(firstFactor K) := ⟨c, cfg.Q_le_ht hcQ⟩ with hc'
  have hπc : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) c' ∈ F :=
    (cfg_mem_Q_iff cfg hF c').mp hcQ
  have e1 : (Subgroup.inclusion (cfg.E_le_Q.trans cfg.Q_le_ht) ⟨c⁻¹ * (u : T) * c, hcE⟩ :
      ↥(firstFactor K)) = c'⁻¹ * u * c' := rfl
  show QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))
    (Subgroup.inclusion (cfg.E_le_Q.trans cfg.Q_le_ht) ⟨c⁻¹ * (u : T) * c, hcE⟩) = f
  rw [e1, map_mul, map_mul, map_inv, hπu]
  have hcomm := F_comm hF.elemAbelian hf hπc
  rw [mul_assoc, hcomm, inv_mul_cancel_left]

private theorem cfg_z_img (cfg : L3E8Cfg K z J zJ H Q E S)
    {F : Subgroup (SecQuot (firstFactor K))} (hF : FaithfulL3E8 (SecQuot (firstFactor K)) F) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))
      ⟨z, K_le_firstFactor K cfg.datum.unique.mem⟩ ∈ F := by
  obtain ⟨R, hRK, hR2, hq, hu⟩ := exists_q8_K cfg.toFrameStd
  obtain ⟨P, hP, hw⟩ := q8_image (hRK.trans (K_le_firstFactor K)) hR2 hq hu
  exact FaithfulL3E8.mem_E_of_q8 hF hP hw

end SecAux3

section Setup

variable {T : Type} [Group T] [Finite T]
  {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T} {H : Subgroup T}

theorem l3e8_isL3E8_ht (hs : L3E8Std K z J zJ H) :
    IsL3E8 (SecQuot (firstFactor K)) := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := hs.datum.hyp
  have hHle : H ≤ firstFactor K := by
    rw [← hs.hH]
    exact le_sup_left
  have hNle : oddCoreOf (sigmaGen K) ≤ firstFactor K := le_sup_right
  have hHtsup : H ⊔ oddCoreOf (sigmaGen K) = firstFactor K := by
    rw [← hs.hH]
    rfl
  have hHs : firstFactor K ≤ sigmaGen K := firstFactor_le_sigmaGen hΩ
  have hnorm : firstFactor K ≤ Subgroup.normalizer (oddCoreOf (sigmaGen K) : Set T) := fun x hx =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (hHs hx))
  haveI : ((oddCoreOf (sigmaGen K)).subgroupOf (firstFactor K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hnorm
  have hodd : Odd (Nat.card ((oddCoreOf (sigmaGen K)).subgroupOf (firstFactor K))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv]
    exact oddCoreOf_odd_natCard _
  let ι : ↥(⊤ : Subgroup ↥H) →* ↥(firstFactor K) :=
    (Subgroup.inclusion hHle).comp (⊤ : Subgroup ↥H).subtype
  have hι : Function.Injective ι :=
    (Subgroup.inclusion_injective hHle).comp (⊤ : Subgroup ↥H).subtype_injective
  have hrange : ι.range = H.subgroupOf (firstFactor K) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_top, Subgroup.inclusion_range]
  have hsup : ι.range ⊔ (oddCoreOf (sigmaGen K)).subgroupOf (firstFactor K) = ⊤ := by
    rw [hrange, ← Subgroup.subgroupOf_sup hHle hNle, hHtsup, Subgroup.subgroupOf_self]
  obtain ⟨e⟩ := secQuot_equiv_of_sup ι hι _ hodd hsup
  exact isL3E8_of_mulEquiv e hs.row

theorem l3e8_two_q8_ht (hs : FrameStd K z J zJ) :
    ∃ (P P' : Subgroup (SecQuot (firstFactor K))) (w w' : SecQuot (firstFactor K)),
      Nonempty (↥P ≃* QuaternionGroup 2) ∧ IsUniqueInvolution P w ∧
      Nonempty (↥P' ≃* QuaternionGroup 2) ∧ IsUniqueInvolution P' w' ∧ w ≠ w' := by
  obtain ⟨R, hRK, hR2, hq, hu⟩ := exists_q8_K hs
  obtain ⟨R', hRJ, hR'2, hq', hu'⟩ := exists_q8_J hs
  obtain ⟨P, hP, hw⟩ := q8_image (hRK.trans (K_le_firstFactor K)) hR2 hq hu
  obtain ⟨P', hP', hw'⟩ := q8_image (hRJ.trans (J_le_firstFactor hs)) hR'2 hq' hu'
  refine ⟨P, P', _, _, hP, hw, hP', hw', fun heq => ?_⟩
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := hs.datum.hyp
  have hne := viol_ne hΩ (CoreAssembly.mem_conjClass_self K) hs.viol
  have hcomm := viol_comm hΩ hs.viol
  have hz2 := hs.datum.unique.sq
  have hzJ2 := hs.viol.hzJ.sq
  have h1 := QuotientGroup.eq.mp heq
  set z' : ↥(firstFactor K) := ⟨z, hRK.trans (K_le_firstFactor K) hu.mem⟩ with hz'
  set zJ' : ↥(firstFactor K) := ⟨zJ, (hRJ.trans (J_le_firstFactor hs)) hu'.mem⟩ with hzJ'
  have hz'2 : z' * z' = 1 := Subtype.ext hz2
  have hzJ'2 : zJ' * zJ' = 1 := Subtype.ext hzJ2
  have hcomm' : z' * zJ' = zJ' * z' := Subtype.ext hcomm
  have hm2 : (z'⁻¹ * zJ') ^ 2 ^ 1 = 1 := by
    have hzi : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
    rw [hzi, pow_one, pow_two]
    calc z' * zJ' * (z' * zJ') = z' * (zJ' * z') * zJ' := by group
      _ = z' * (z' * zJ') * zJ' := by rw [hcomm']
      _ = (z' * z') * (zJ' * zJ') := by group
      _ = 1 := by rw [hz'2, hzJ'2, one_mul]
  have hm := eq_one_of_mem_oddCore h1 hm2
  exact hne (congrArg Subtype.val (inv_mul_eq_one.mp hm)).symm

theorem l3e8_faithful (hs : L3E8Std K z J zJ H) :
    IsFaithfulL3E8 (SecQuot (firstFactor K)) := by
  obtain ⟨P, P', w, w', hP, hw, hP', hw', hne⟩ := l3e8_two_q8_ht hs.toFrameStd
  exact isFaithfulL3E8_of_two_q8 (l3e8_isL3E8_ht hs) hP hw hP' hw' hne

end Setup

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem E8 (cfg : L3E8Cfg K z J zJ H Q E S) : IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  obtain ⟨F, hF⟩ := cfg.faithful
  have hinj := phiE_injective cfg
  have hrange : (phiE cfg).range = F := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact phiE_mem cfg hF a
    · intro f hf
      obtain ⟨a, ha⟩ := phiE_surjective cfg hF hf
      exact ⟨a, ha⟩
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply hinj
    rw [map_mul, map_mul]
    exact F_comm hF.elemAbelian (phiE_mem cfg hF a) (phiE_mem cfg hF b)
  · have h1 : (phiE cfg ⟨x, hx⟩) ^ 2 = 1 := hF.elemAbelian.2 _ (phiE_mem cfg hF ⟨x, hx⟩)
    have h2 : (⟨x, hx⟩ : ↥E) ^ 2 = 1 := hinj (by rw [map_pow, h1, map_one])
    simpa using congrArg Subtype.val h2
  · rw [← hF.card]
    exact Nat.card_congr ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).toEquiv

theorem E_conj (cfg : L3E8Cfg K z J zJ H Q E S) {e : T} (he : e ∈ E) (he1 : e ≠ 1) :
    ∃ l ∈ firstFactor K, l⁻¹ * z * l = e := by
  obtain ⟨F, hF⟩ := cfg.faithful
  have hEQ : E ≤ Q := cfg.E_le_Q
  have hQHt : Q ≤ firstFactor K := cfg.Q_le_ht
  have hz := cfg.datum.unique
  set z' : ↥(firstFactor K) := ⟨z, K_le_firstFactor K hz.mem⟩ with hz'
  set e' : ↥(firstFactor K) := ⟨e, hQHt (hEQ he)⟩ with he'
  have hπz : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) z' ∈ F :=
    cfg_z_img cfg hF
  have hπe : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) e' ∈ F :=
    (cfg_mem_Q_iff cfg hF e').mp (hEQ he)
  have hz'2 : z' * z' = 1 := Subtype.ext hz.sq
  have hπz1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) z' ≠ 1 := by
    intro h
    have h1 : z' = 1 :=
      eq_one_of_mem_oddCore (k := 1) ((QuotientGroup.eq_one_iff _).mp h) (by rw [pow_one, pow_two, hz'2])
    exact hz.ne_one (congrArg Subtype.val h1)
  have hπe1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) e' ≠ 1 := by
    intro h
    apply he1
    have : (⟨e, he⟩ : ↥E) = 1 := phiE_injective cfg (by rw [map_one]; exact h)
    exact congrArg Subtype.val this
  obtain ⟨xb, hxb⟩ := FaithfulL3E8.exists_conj hF hπz hπe hπz1 hπe1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  set y' : ↥(firstFactor K) := x * z' * x⁻¹ with hy'
  have hy'π : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) y' =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) e' := by
    rw [hy', map_mul, map_mul, map_inv]
    exact hxb
  have hy'2 : y' * y' = 1 := by
    calc y' * y' = x * (z' * z') * x⁻¹ := by rw [hy']; group
      _ = 1 := by rw [hz'2]; group
  have hy'1 : y' ≠ 1 := by
    intro h
    apply hz.ne_one
    have : z' = 1 := by
      calc z' = x⁻¹ * y' * x := by rw [hy']; group
        _ = 1 := by rw [h]; group
    exact congrArg Subtype.val this
  have hyQ : (y' : T) ∈ Q := (cfg_mem_Q_iff cfg hF y').mpr (hy'π ▸ hπe)
  have hord : orderOf (y' : T) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      exact congrArg Subtype.val hy'2
    · intro h
      exact hy'1 (Subtype.ext h)
  obtain ⟨c, hcQ, hcE⟩ :=
    CFSG.StronglyEmbedded.UniqueCoset.exists_conj_mem_of_isSylow2In cfg.E_sylow hyQ hord
  set c' : ↥(firstFactor K) := ⟨c, hQHt hcQ⟩ with hc'
  have hπc : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) c' ∈ F :=
    (cfg_mem_Q_iff cfg hF c').mp hcQ
  have hde : c⁻¹ * (y' : T) * c = e := by
    refine congrArg Subtype.val (phiE_injective cfg (a₁ := ⟨c⁻¹ * (y' : T) * c, hcE⟩)
      (a₂ := ⟨e, he⟩) ?_)
    show QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) (c'⁻¹ * y' * c') =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)) e'
    rw [map_mul, map_mul, map_inv, hy'π]
    have hcomm := F_comm hF.elemAbelian hπe hπc
    rw [mul_assoc, hcomm, inv_mul_cancel_left]
  refine ⟨(x : T)⁻¹ * c, (firstFactor K).mul_mem ((firstFactor K).inv_mem x.2) (hQHt hcQ), ?_⟩
  calc ((x : T)⁻¹ * c)⁻¹ * z * ((x : T)⁻¹ * c) = c⁻¹ * ((x * z' * x⁻¹ : ↥(firstFactor K)) : T) * c := by
        simp only [hz', Subgroup.coe_mul, Subgroup.coe_inv]
        group
    _ = e := hde

theorem z_mem_E (cfg : L3E8Cfg K z J zJ H Q E S) : z ∈ E := by
  obtain ⟨F, hF⟩ := cfg.faithful
  have hzQ : z ∈ Q :=
    (cfg_mem_Q_iff cfg hF ⟨z, K_le_firstFactor K cfg.datum.unique.mem⟩).mpr (cfg_z_img cfg hF)
  rw [cfg.hE]
  exact ⟨hzQ, cfg.hzS⟩

theorem efacts (cfg : L3E8Cfg K z J zJ H Q E S) : EFacts K z E :=
  ⟨cfg.z_mem_E, fun _ he _ he1 => cfg.E_conj he he1⟩

theorem tight (cfg : L3E8Cfg K z J zJ H Q E S) : TightlyEmbedded Q :=
  cfg.toFrameQCfg.tight cfg.efacts

end L3E8Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
