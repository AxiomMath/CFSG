module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1115b
public import CFSG.HardMathSupport.Solomon.Coordinator.InnDiagThreeLink
public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankCore
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeOrthTwo
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.D44

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn IsCatalogLieIso IsL364Index Is3D44Index
  IsD44Index)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open scoped commutatorElement

section Statement

variable {G : Type} [Group G]

@[expose] def IsLThreeFourCubeLayer [Finite G] (X : Subgroup G) : Prop :=
  ∃ K₁ K₂ K₃ : Subgroup G, GLAPComponent 3 X K₁ ∧ GLAPComponent 3 X K₂ ∧ GLAPComponent 3 X K₃ ∧
    K₁ ≠ K₂ ∧ K₁ ≠ K₃ ∧ K₂ ≠ K₃ ∧ GLAPLayer 3 X = K₁ ⊔ K₂ ⊔ K₃ ∧
    IsLThreeFour ↥(barX 3 X K₁) ∧ IsLThreeFour ↥(barX 3 X K₂) ∧ IsLThreeFour ↥(barX 3 X K₃)

end Statement

section CharSub

variable {G : Type} [Group G] [Finite G]

theorem thompsonJ_le (T : Subgroup G) : thompsonJ 2 T ≤ T :=
  iSup₂_le fun _ hE => hE.1

theorem isCharIn_thompsonJ (T : Subgroup G) : IsCharIn (thompsonJ 2 T) T := by
  refine ⟨thompsonJ_le T, fun ψ x hx => ?_⟩
  have key : ∀ E : Subgroup G, IsEkIn 2 (CFSG.Open.pRank 2 T) T E →
      ∀ y : ↥T, (y : G) ∈ E → ((ψ y : ↥T) : G) ∈ thompsonJ 2 T := by
    intro E hE y hy
    set E' : Subgroup G := ((E.subgroupOf T).map ψ.toMonoidHom).map T.subtype with hE'
    have hE'ek : IsEkIn 2 (CFSG.Open.pRank 2 T) T E' := by
      refine ⟨Subgroup.map_subtype_le _, ((hE.2.1.subgroupOf T).map _).map _, ?_⟩
      rw [hE', Subgroup.card_map_of_injective T.subtype_injective,
        Subgroup.card_map_of_injective ψ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE.1).toEquiv, hE.2.2]
    exact le_iSup₂ (f := fun (E : Subgroup G) (_ : IsEkIn 2 (CFSG.Open.pRank 2 T) T E) => E) E'
      hE'ek ⟨ψ y, ⟨y, Subgroup.mem_subgroupOf.2 hy, rfl⟩, rfl⟩
  have hle : thompsonJ 2 T ≤ (((thompsonJ 2 T).subgroupOf T).comap ψ.toMonoidHom).map T.subtype := by
    refine iSup₂_le fun E hE e he => ?_
    refine ⟨⟨e, hE.1 he⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (key E hE ⟨e, hE.1 he⟩ he)
  obtain ⟨w, hw, hwx⟩ := hle hx
  obtain rfl : w = x := Subtype.ext hwx
  exact hw

theorem thompsonJ_ne_bot {T : Subgroup G} (hT2 : IsPGroup 2 ↥T) (hT : T ≠ ⊥) :
    thompsonJ 2 T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card T :=
    (hT2.card_eq_or_dvd).resolve_left fun h => hT (Subgroup.card_eq_one.1 h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 hdvd
  have hx2 : (x : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (x : G)
    rwa [Subgroup.orderOf_coe, hx] at this
  have h1 : 1 ≤ CFSG.Open.pRank 2 T := by
    refine CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.zpowers_le.2 x.2)
      (CFSG.Open.isElemAbelian_zpowers hx2) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]
  obtain ⟨E, hET, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) T
  intro hJ
  have hEJ : E ≤ thompsonJ 2 T :=
    le_iSup₂ (f := fun (E : Subgroup G) (_ : IsEkIn 2 (CFSG.Open.pRank 2 T) T E) => E) E
      ⟨hET, hEel, hEcard⟩
  rw [hJ, le_bot_iff] at hEJ
  rw [hEJ, Subgroup.card_bot] at hEcard
  have : 2 ^ 1 ≤ 2 ^ CFSG.Open.pRank 2 T := Nat.pow_le_pow_right (by norm_num) h1
  omega

theorem omegaOne_center_le (T : Subgroup G) : omegaOne 2 (centerOf T) ≤ T := by
  refine (Subgroup.closure_le _).2 fun z hz => ?_
  obtain ⟨⟨w, -, rfl⟩, -⟩ := hz
  exact w.2

theorem isCharIn_omegaOne_center (T : Subgroup G) : IsCharIn (omegaOne 2 (centerOf T)) T := by
  refine ⟨omegaOne_center_le T, fun ψ x hx => ?_⟩
  have hgen : ∀ z : ↥T, (z : G) ∈ centerOf T → (z : G) ^ 2 = 1 →
      ((ψ z : ↥T) : G) ∈ omegaOne 2 (centerOf T) := by
    intro z hz hz2
    refine Subgroup.subset_closure ⟨⟨ψ z, ?_, rfl⟩, ?_⟩
    · obtain ⟨w, hw, hwz⟩ := hz
      obtain rfl : w = z := Subtype.ext hwz
      rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hw ⊢
      intro g
      obtain ⟨g', rfl⟩ := ψ.surjective g
      rw [← map_mul, ← map_mul, hw g']
    · have h1 : z ^ 2 = 1 := Subtype.ext (by simpa using hz2)
      have h2 : (ψ z) ^ 2 = 1 := by rw [← map_pow, h1, map_one]
      simpa using congrArg Subtype.val h2
  have hle : omegaOne 2 (centerOf T) ≤
      (((omegaOne 2 (centerOf T)).subgroupOf T).comap ψ.toMonoidHom).map T.subtype := by
    refine (Subgroup.closure_le _).2 fun z hz => ?_
    obtain ⟨hzc, hz2⟩ := hz
    have hzT : z ∈ T := by
      obtain ⟨w, -, rfl⟩ := hzc
      exact w.2
    exact ⟨⟨z, hzT⟩, Subgroup.mem_subgroupOf.2 (hgen ⟨z, hzT⟩ hzc hz2), rfl⟩
  obtain ⟨w, hw, hwx⟩ := hle hx
  obtain rfl : w = x := Subtype.ext hwx
  exact hw

theorem omegaOne_center_ne_bot {T : Subgroup G} (hT2 : IsPGroup 2 ↥T) (hT : T ≠ ⊥) :
    omegaOne 2 (centerOf T) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hT
  have hZ : Nontrivial (Subgroup.center ↥T) := hT2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center ↥T) := hT2.to_subgroup _
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.2 hZ).ne' hk
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥T)) 2
    (hk ▸ dvd_pow_self 2 hk0)
  intro hbot
  have hzmem : (((z : ↥T) : G)) ∈ omegaOne 2 (centerOf T) := by
    refine Subgroup.subset_closure ⟨⟨z, z.2, rfl⟩, ?_⟩
    have := pow_orderOf_eq_one z
    rw [hz] at this
    have := congrArg (fun w : ↥(Subgroup.center ↥T) => ((w : ↥T) : G)) this
    simpa using this
  rw [hbot, Subgroup.mem_bot] at hzmem
  have h1 : z = 1 := Subtype.ext (Subtype.ext hzmem)
  rw [h1, orderOf_one] at hz
  norm_num at hz

end CharSub

section Generic

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mk_centralizes {H L : Subgroup G} (hL : GLAPComponent 3 H L) {x : G}
    (hxH : x ∈ H)
    (hx : QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) ⟨x, hxH⟩ ∈
      Subgroup.centralizer (barX 3 H L : Set (↥H ⧸ GLAPPrimeCore 3 ↥H))) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  have hc : GLAPComponent 3 H (GLBConj x L) := Inputs1115.glaPComponent_conj_of_mem hL hxH
  refine glaPComponent_unique hc hL ?_
  rw [barX_gLBConj_eq 3 hxH]
  exact gLBConj_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hx)

theorem core_le_normalizer {H L : Subgroup G} (hL : GLAPComponent 3 H L) :
    GLAPPrimeCoreOf 3 H ≤ Subgroup.normalizer (L : Set G) := by
  intro o ho
  have hoH : o ∈ H := Subgroup.map_subtype_le _ ho
  rw [mem_normalizer_iff_gLBConj_eq]
  exact glaPComponent_unique (Inputs1115.glaPComponent_conj_of_mem hL hoH) hL
    (barX_gLBConj_of_mem 3 ho L)

theorem le_normalizer_of_ne {H L L' : Subgroup G} (hL : GLAPComponent 3 H L)
    (hL' : GLAPComponent 3 H L') (hne : L ≠ L') : L' ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  refine mem_normalizer_of_mk_centralizes hL (hL'.1 hx) ?_
  exact Claims1115b.barX_le_centralizer_of_ne' hL hL' hne (Inputs1115.mk_mem_barX (hL'.1 hx) hx)

theorem commutator_sup_le {Y A : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : ⁅Y ⊔ A, Y ⊔ A⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro u hu v hv
  have hu' : u ∈ ((Y ⊔ A : Subgroup G) : Set G) := hu
  have hv' : v ∈ ((Y ⊔ A : Subgroup G) : Set G) := hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y A hAY] at hu' hv'
  obtain ⟨y₁, hy₁, x₁, hx₁, rfl⟩ := hu'
  obtain ⟨y₂, hy₂, x₂, hx₂, rfl⟩ := hv'
  have hN : ∀ x ∈ A, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 (hAY hx) y).1 hy
  have hN' : ∀ x ∈ A, ∀ y ∈ Y, x⁻¹ * y * x ∈ Y := fun x hx y hy => by
    have := hN x⁻¹ (A.inv_mem hx) y hy
    simpa using this
  have hc : x₁ * x₂ = x₂ * x₁ := hA x₁ hx₁ x₂ hx₂
  have e : ⁅y₁ * x₁, y₂ * x₂⁆ = (y₁ * (x₁ * y₂ * x₁⁻¹)) * (y₂ * (x₂ * y₁ * x₂⁻¹))⁻¹ := by
    rw [commutatorElement_def]
    calc y₁ * x₁ * (y₂ * x₂) * (y₁ * x₁)⁻¹ * (y₂ * x₂)⁻¹
        = (y₁ * (x₁ * y₂ * x₁⁻¹)) * (x₁ * x₂) * (x₂ * x₁)⁻¹ * (y₂ * (x₂ * y₁ * x₂⁻¹))⁻¹ := by
          group
      _ = (y₁ * (x₁ * y₂ * x₁⁻¹)) * (y₂ * (x₂ * y₁ * x₂⁻¹))⁻¹ := by rw [hc]; group
  rw [e]
  exact Y.mul_mem (Y.mul_mem hy₁ (hN x₁ hx₁ y₂ hy₂))
    (Y.inv_mem (Y.mul_mem hy₂ (hN x₂ hx₂ y₁ hy₁)))

theorem le_of_le_sup_two {Y J N T : Subgroup G} (hJ : GLAPComponent 3 Y J)
    (hT : IsPGroup 2 ↥T) (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hJNT : J ≤ N ⊔ T) :
    J ≤ N := by
  have hNA : N ≤ N ⊔ T := le_sup_left
  have hTA : T ≤ N ⊔ T := le_sup_right
  have hAN : N ⊔ T ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hTN
  haveI : (N.subgroupOf (N ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).2 hAN
  refine CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_coprime_index Nat.prime_three hJ
    hJNT ?_
  have htop : T.subgroupOf (N ⊔ T) ⊔ N.subgroupOf (N ⊔ T) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTA hNA, sup_comm, Subgroup.subgroupOf_self]
  have h1 := Subgroup.relIndex_sup_right (T.subgroupOf (N ⊔ T)) (N.subgroupOf (N ⊔ T))
  rw [htop, Subgroup.relIndex_top_right] at h1
  rw [h1]
  refine Nat.Coprime.coprime_dvd_right (Subgroup.relIndex_dvd_card _ _) ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

end Generic

section Join

variable {G : Type} [Group G] [Finite G]

structure IsJoin (H J : Subgroup G) (𝒞 : Set (Subgroup G)) : Prop where
  comp : ∀ L ∈ 𝒞, GLAPComponent 3 H L
  eq : J = ⨆ L ∈ 𝒞, L

variable {H J : Subgroup G} {𝒞 : Set (Subgroup G)}

theorem IsJoin.mem_le (hJ : IsJoin H J 𝒞) {L : Subgroup G} (hL : L ∈ 𝒞) : L ≤ J := by
  rw [hJ.eq]
  exact le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ 𝒞) => L) L hL

theorem IsJoin.le (hJ : IsJoin H J 𝒞) : J ≤ H := by
  rw [hJ.eq]
  exact iSup₂_le fun L hL => (hJ.comp L hL).1

theorem IsJoin.le_of_forall (hJ : IsJoin H J 𝒞) {N : Subgroup G} (h : ∀ L ∈ 𝒞, L ≤ N) : J ≤ N := by
  rw [hJ.eq]
  exact iSup₂_le h

theorem IsJoin.mem_normalizer (hJ : IsJoin H J 𝒞) {x : G}
    (h : ∀ L ∈ 𝒞, x ∈ Subgroup.normalizer (L : Set G)) :
    x ∈ Subgroup.normalizer (J : Set G) := by
  have key : ∀ y : G, (∀ L ∈ 𝒞, y ∈ Subgroup.normalizer (L : Set G)) → GLBConj y J ≤ J := by
    intro y hy
    rw [hJ.eq]
    refine Inputs1115.gLBConj_sSup_le ?_
    rintro _ ⟨L, rfl⟩
    refine Inputs1115.gLBConj_sSup_le ?_
    rintro _ ⟨hL, rfl⟩
    rw [gLBConj_eq_of_mem_normalizer (hy L hL)]
    exact le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ 𝒞) => L) L hL
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key x h) ?_
  have := gLBConj_mono x (key x⁻¹ fun L hL => Subgroup.inv_mem _ (h L hL))
  rwa [gLBConj_gLBConj_inv] at this

theorem IsJoin.core_le_normalizer (hJ : IsJoin H J 𝒞) :
    GLAPPrimeCoreOf 3 H ≤ Subgroup.normalizer (J : Set G) := fun _ ho =>
  hJ.mem_normalizer fun L hL =>
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115c.core_le_normalizer (hJ.comp L hL) ho

theorem IsJoin.le_layer (hJ : IsJoin H J 𝒞) {X : Subgroup G} (hJX : J ≤ X) (hXH : X ≤ H) :
    J ≤ GLAPLayer 3 X :=
  hJ.le_of_forall fun L hL =>
    le_sSup (glaPComponent_of_le Nat.prime_three (hJ.comp L hL) ((hJ.mem_le hL).trans hJX) hXH)

theorem IsJoin.le_of_pElements (hJ : IsJoin H J 𝒞) {N : Subgroup G}
    (h : ∀ L ∈ 𝒞, ∀ x ∈ L, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ N) : J ≤ N :=
  hJ.le_of_forall fun L hL => Inputs1115.le_of_pElements Nat.prime_three (hJ.comp L hL) (h L hL)

theorem IsJoin.barX_le_centralizer (hJ : IsJoin H J 𝒞)
    {U : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H)} (hU : Nat.Coprime 3 (Nat.card U))
    (hJU : barX 3 H J ≤ Subgroup.normalizer (U : Set (↥H ⧸ GLAPPrimeCore 3 ↥H))) :
    barX 3 H J ≤ Subgroup.centralizer (U : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := by
  rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff hJ.le]
  refine hJ.le_of_forall fun L hL => ?_
  have hLH : L ≤ H := (hJ.comp L hL).1
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff hLH]
  have hc := Inputs1115.commutator_eq_bot_of_normalizes_coprime (hJ.comp L hL).2.2.1
    (glaPPrimeCore_quotient_eq_bot Nat.prime_three) hU
    ((Inputs1115.barX_le_barX (hJ.mem_le hL)).trans hJU)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc

theorem _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115b.Sit.exists_isJoin
    {M E A K : Subgroup G} {a : G} {K' : Subgroup G} (S : Claims1115b.Sit M E A K H a K') :
    ∃ 𝒞 : Set (Subgroup G), IsJoin H (Lemma1115.jLayer a H) 𝒞 := by
  rcases S.cases with ⟨L, hL, -, hJ⟩ | ⟨L, c, hJ⟩
  · refine ⟨{L}, fun L' hL' => (Set.mem_singleton_iff.1 hL') ▸ hL, ?_⟩
    rw [hJ]
    simp
  · have hL₂ : GLAPComponent 3 H (GLBConj a L) := Inputs1115.glaPComponent_conj_of_mem c.hM S.haH
    have hL₃ : GLAPComponent 3 H (GLBConj a (GLBConj a L)) :=
      Inputs1115.glaPComponent_conj_of_mem hL₂ S.haH
    refine ⟨{L, GLBConj a L, GLBConj a (GLBConj a L)}, ?_, ?_⟩
    · intro L' hL'
      rcases hL' with rfl | rfl | rfl
      · exact c.hM
      · exact hL₂
      · exact hL₃
    · rw [hJ]
      refine le_antisymm (sup_le (sup_le ?_ ?_) ?_) (iSup₂_le fun L' hL' => ?_)
      · exact le_iSup₂ (f := fun (L' : Subgroup G) (_ : L' ∈ ({L, GLBConj a L,
          GLBConj a (GLBConj a L)} : Set (Subgroup G))) => L') L (by simp)
      · exact le_iSup₂ (f := fun (L' : Subgroup G) (_ : L' ∈ ({L, GLBConj a L,
          GLBConj a (GLBConj a L)} : Set (Subgroup G))) => L') (GLBConj a L) (by simp)
      · exact le_iSup₂ (f := fun (L' : Subgroup G) (_ : L' ∈ ({L, GLBConj a L,
          GLBConj a (GLBConj a L)} : Set (Subgroup G))) => L') (GLBConj a (GLBConj a L)) (by simp)
      · rcases hL' with rfl | rfl | rfl
        · exact le_sup_left.trans le_sup_left
        · exact le_sup_right.trans le_sup_left
        · exact le_sup_right

theorem A_le_normalizer_jLayer {A : Subgroup G} {a : G} (hAH : A ≤ H)
    (hAC : A ≤ Cg a) : A ≤ Subgroup.normalizer (Lemma1115.jLayer a H : Set G) := by
  set K0 := GLAPLayer 3 (H ⊓ Cg a) with hK0
  set L := GLAPLayer 3 H with hL
  have hK0N : ∀ x ∈ A, GLBConj x K0 = K0 := fun x hx =>
    gLBConj_eq_of_mem_normalizer
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPLayer 3
        (fun y hy => Subgroup.le_normalizer hy) ⟨hAH hx, hAC hx⟩)
  have hLN : ∀ x ∈ H, x ∈ Subgroup.normalizer (L : Set G) := fun x hx =>
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPLayer 3
      (fun y hy => Subgroup.le_normalizer hy) hx
  have key : ∀ x ∈ A, GLBConj x (Lemma1115.jLayer a H) ≤ Lemma1115.jLayer a H := by
    intro x hx
    refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun g hg => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    show GLBConj x (GLBConj g K0) ≤ Lemma1115.jLayer a H
    have e : GLBConj x (GLBConj g K0) = GLBConj (x⁻¹ * g * x) (GLBConj x K0) := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj]
      congr 1
      group
    rw [e, hK0N x hx]
    have hg' : x⁻¹ * g * x ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (hLN x⁻¹ (H.inv_mem (hAH hx))) g).1 hg
      simpa using this
    exact le_iSup₂ (f := fun (g : G) (_ : g ∈ L) => GLBConj g K0) _ hg'
  intro x hx
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key x hx) ?_
  have := gLBConj_mono x (key x⁻¹ (A.inv_mem hx))
  rwa [gLBConj_gLBConj_inv] at this

end Join

section XFacts

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_sup {P Q : Subgroup G} {x : G} (hP : x ∈ Subgroup.normalizer (P : Set G))
    (hQ : x ∈ Subgroup.normalizer (Q : Set G)) : x ∈ Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hP hQ ⊢
  unfold GLBConj at hP hQ ⊢
  rw [Subgroup.map_sup, hP, hQ]

theorem layer_eq_of_join {H J : Subgroup G} {𝒞 : Set (Subgroup G)} (hJ : IsJoin H J 𝒞)
    {T A : Subgroup G} (hT : IsPGroup 2 ↥T) (hTH : T ≤ H) (hAH : A ≤ H)
    (hTN : T ≤ Subgroup.normalizer (J : Set G)) (hAN : A ≤ Subgroup.normalizer (J : Set G))
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    GLAPLayer 3 (GLAPPrimeCoreOf 3 H ⊔ J ⊔ T ⊔ A) = J := by
  set O := GLAPPrimeCoreOf 3 H with hO
  set X := O ⊔ J ⊔ T ⊔ A with hX
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 H
  have hXH : X ≤ H := sup_le (sup_le (sup_le hOH hJ.le) hTH) hAH
  refine le_antisymm (sSup_le fun L' hL' => ?_)
    (hJ.le_layer (le_sup_right.trans (le_sup_left.trans le_sup_left)) hXH)
  set Y := O ⊔ J ⊔ T with hY
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := fun x hx =>
    mem_normalizer_sup (mem_normalizer_sup (hHO (hAH hx)) (hAN hx)) (hAT hx)
  have hcomm : ⁅X, X⁆ ≤ Y := commutator_sup_le hAY hAab
  have hL'X : L' ≤ X := hL'.1
  have hL'Y : L' ≤ Y := by
    rw [← glaPComponent_perfect hL']
    exact (Subgroup.commutator_mono hL'X hL'X).trans hcomm
  have hTN' : T ≤ Subgroup.normalizer ((J ⊔ O : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_sup (hTN hx) (hHO (hTH hx))
  have hYle : Y ≤ (J ⊔ O) ⊔ T := sup_le (sup_le (le_sup_right.trans le_sup_left)
    (le_sup_left.trans le_sup_left)) le_sup_right
  have h1 : L' ≤ J ⊔ O := le_of_le_sup_two hL' hT hTN' (hL'Y.trans hYle)
  exact CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_le_sup Nat.prime_three hL'
    (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 H)
    hJ.core_le_normalizer h1

theorem centralizer_pCore_le {H X : Subgroup G} (hH : IsTwoLocal H) (hchar : IsCharTwoType G)
    (hXH : X ≤ H) (hOX : GLAPPrimeCoreOf 3 H ≤ X) :
    X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) ≤ pCoreOf 2 X := by
  set P := pCoreOf 2 H with hP
  have hPH : P ≤ H := Subgroup.map_subtype_le _
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := Inputs1114.le_normalizer_pCoreOf_two le_rfl
  have hP2 : IsPGroup 2 ↥P := Lemma1114.isPGroup_pCoreOf_two H
  have hPO : P ≤ GLAPPrimeCoreOf 3 H := by
    refine Inputs1115.le_glaPPrimeCoreOf_of_le_normalizer hPH hHP ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hPX : P ≤ X := hPO.trans hOX
  have hPX2 : P ≤ pCoreOf 2 X := Lemma1114.le_pCoreOf_two_of_normal hPX hP2 fun y hy w hw =>
    (Subgroup.mem_normalizer_iff.1 (hHP (hXH hy)) w).1 hw
  intro x hx
  refine hPX2 (hchar H hH ⟨hXH hx.1, ?_⟩)
  exact Subgroup.centralizer_le hPX2 hx.2

end XFacts

section Centre

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)

theorem mem_normalizer_center {Γ : Type} [Group Γ] [Finite Γ] {P : Subgroup Γ} {x : Γ}
    (hx : x ∈ Subgroup.normalizer (P : Set Γ)) :
    x ∈ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (P : Set Γ) : Subgroup Γ) : Set Γ) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hx ⊢
  have e : GLBConj x (P ⊓ Subgroup.centralizer (P : Set Γ)) =
      GLBConj x P ⊓ GLBConj x (Subgroup.centralizer (P : Set Γ)) :=
    Subgroup.map_inf_eq _ _ _ (MulAut.conj x⁻¹).injective
  rw [e, ← Inputs1114.centralizer_gLBConj, hx]

theorem barX_center_facts {H L : Subgroup G} (hL : GLAPComponent 3 H L) :
    IsPGroup 3 ↥(barX 3 H L ⊓ Subgroup.centralizer (barX 3 H L : Set (↥H ⧸ GLAPPrimeCore 3 ↥H))) ∧
      (barX 3 H L ⊓ Subgroup.centralizer (barX 3 H L : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) = ⊥ ↔
        Subgroup.center (barOf 3 L) = ⊥) := by
  set Lt := barX 3 H L with hLt
  set e : barOf 3 L ≃* ↥Lt := quotEquivBarX Nat.prime_three hL.1 hL.2.1 with he
  have hmap : (Subgroup.center ↥Lt).map Lt.subtype =
      Lt ⊓ Subgroup.centralizer (Lt : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      have := Subgroup.mem_center_iff.1 hw ⟨y, hy⟩
      exact congrArg Subtype.val this
    · rintro ⟨hz, hzc⟩
      refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.1 hzc y y.2
  have hcen : (Subgroup.center (barOf 3 L)).map e.toMonoidHom = Subgroup.center ↥Lt :=
    Subgroup.map_center_eq e
  have hcore : GLAPPrimeCore 3 (barOf 3 L) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hp : IsPGroup 3 ↥(Subgroup.center (barOf 3 L)) := isPGroup_center Nat.prime_three hcore
  refine ⟨?_, ?_⟩
  · rw [← hmap, ← hcen]
    exact (hp.map _).map _
  · rw [← hmap, ← hcen]
    constructor
    · intro h
      have h1 := (Subgroup.map_eq_bot_iff_of_injective _ Lt.subtype_injective).1 h
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1
    · intro h
      rw [h, Subgroup.map_bot, Subgroup.map_bot]

variable {M E A K H : Subgroup G} {a : G} {K' : Subgroup G}

theorem _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115b.Sit.mem_sup_of_center
    (S : Claims1115b.Sit M E A K H a K') {Zt : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H)}
    (hZp : IsPGroup 3 ↥Zt) (hZ0 : Zt ≠ ⊥)
    (haZ : QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) ⟨a, S.haH⟩ ∈
      Subgroup.normalizer (Zt : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)))
    (hZK : Zt ≤ Subgroup.centralizer (barX 3 H K' : Set (↥H ⧸ GLAPPrimeCore 3 ↥H))) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) ⟨a, S.haH⟩ ∈ barX 3 H (E ⊓ A) ⊔ Zt := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) with hπ
  set at' := π ⟨a, S.haH⟩ with hat'
  have hA0H : E ⊓ A ≤ H := inf_le_right.trans S.hAH
  have hAp : IsPGroup 3 ↥A := CFSG.Open.IsElemAbelian.isPGroup S.cfg.hAel
  have hap : IsPGroup 3 ↥(Subgroup.zpowers at') := by
    have h1 : at' ^ 3 = 1 := by
      rw [hat', ← map_pow]
      have : (⟨a, S.haH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using S.ha3)
      rw [this, map_one]
    exact (CFSG.Open.isElemAbelian_zpowers h1).isPGroup
  have hS₀p : IsPGroup 3 ↥(Zt ⊔ Subgroup.zpowers at') :=
    IsPGroup.to_sup_of_normal_left' hZp hap (Subgroup.zpowers_le.2 haZ)
  have hS₀N : Zt ⊔ Subgroup.zpowers at' ≤ Subgroup.normalizer (Zt : Set _) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 haZ)
  obtain ⟨z, hzZ, hz3, hzc⟩ := Claims1115b.exists_central_of_normal hS₀p le_sup_left hS₀N hZ0
  have hzat : at' * z = z * at' := hzc at' (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hAeq : (E ⊓ A) ⊔ Subgroup.zpowers a = A :=
    (Lemma1114.coord_setup S.cfg.hAel S.cfg.hA27 inf_le_right S.cfg.hA0card S.cfg.ha S.cfg.ha1
      S.cfg.haA0).2
  have hAbar : barX 3 H A = barX 3 H (E ⊓ A) ⊔ Subgroup.zpowers at' := by
    have e0 : barX 3 H A = barX 3 H ((E ⊓ A) ⊔ Subgroup.zpowers a) := by rw [hAeq]
    rw [e0, CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup hA0H
      (Subgroup.zpowers_le.2 S.haH)]
    congr 1
    unfold barX
    have e1 : (Subgroup.zpowers a).subgroupOf H = Subgroup.zpowers ⟨a, S.haH⟩ := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, by simp⟩
    rw [e1, MonoidHom.map_zpowers]
  have hA0K' : barX 3 H (E ⊓ A) ≤ barX 3 H K' := Inputs1115.barX_le_barX S.A0_le
  have hzA : z ∈ barX 3 H A := by
    refine S.mem_barX_A (by have := pow_orderOf_eq_one z; rwa [hz3] at this) ?_
    rw [hAbar]
    have hle : barX 3 H (E ⊓ A) ⊔ Subgroup.zpowers at' ≤
        Subgroup.centralizer ({z} : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := by
      refine sup_le (fun u hu => ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 (hZK hzZ) u (hA0K' hu)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hzat
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hu)
  have hzA0 : z ∉ barX 3 H (E ⊓ A) := by
    rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ E ⊓ A := Subgroup.mem_subgroupOf.1 hx
    have hx1 : (x : G) = 1 := by
      refine S.eq_one_of_A0 hx' fun k hk => ?_
      have hkH : k ∈ H := (S.hK'.1.trans inf_le_left) hk
      have hcomm := Subgroup.mem_centralizer_iff.1 (hZK hzZ) _ (Inputs1115.mk_mem_barX hkH hk)
      have e1 : (⟨(x : G), x.2⟩ : ↥H) = x := rfl
      refine Claims1115b.commutator_mem_core_of_commute x.2 hkH ?_
      rw [e1]
      exact hcomm.symm
    have : x = 1 := Subtype.ext hx1
    rw [this, map_one, orderOf_one] at hz3
    norm_num at hz3
  have hAbel : IsElemAbelian 3 (barX 3 H A) := (S.cfg.hAel.subgroupOf H).map _
  have hA0bA : barX 3 H (E ⊓ A) ≤ barX 3 H A := Inputs1115.barX_le_barX inf_le_right
  have hAz : barX 3 H (E ⊓ A) ⊔ Subgroup.zpowers z = barX 3 H A := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hA0bA (Subgroup.zpowers_le.2 hzA)) ?_
    rw [GL83.CompFam.card_sup_zpowers hAbel hA0bA hzA hzA0,
      Claims1115b.card_barX_of_isPGroup hA0H (hAp.to_le inf_le_right), S.cfg.hA0card,
      Claims1115b.card_barX_of_isPGroup S.hAH hAp, S.cfg.hA27]
  have hat'A : at' ∈ barX 3 H A := Inputs1115.mk_mem_barX S.haH S.cfg.ha
  rw [← hAz] at hat'A
  exact (sup_le_sup_left (Subgroup.zpowers_le.2 hzZ) _) hat'A

theorem isInnDiagThree_conj {Y : Type} [Group Y]
    (hT : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)))
    (w : Y) : CFSG.HardMathSupport.Solomon.LocalBalance.IsInnDiagThree (MulAut.conj w) := by
  refine Or.inl ((CFSG.HardMathSupport.Solomon.Coordinator.isInnDiagPSL3_iff_mem_innAutDerived
    _).2 ⟨hT, ?_⟩)
  rw [CFSG.HardMathSupport.Solomon.Coordinator.centerDescend_conj]
  exact CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ ⟨_, rfl⟩

theorem barAut_core_eq_one {H L : Subgroup G} (hL : GLAPComponent 3 H L) {o : G}
    (ho : o ∈ GLAPPrimeCoreOf 3 H) (hoN : o ∈ Subgroup.normalizer (L : Set G)) :
    barAut 3 L ⟨o, hoN⟩ = 1 := by
  have hoH : o ∈ H := Subgroup.map_subtype_le _ ho
  refine (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns.mem_centralizerQuot_iff_barAut' 3
    ⟨o, hoN⟩).1 ?_
  refine ⟨hoN, CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_normalizer_gLAPPrimeCoreOf
    3 hoN, fun y hy => ?_⟩
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hL.2.1]
  refine ⟨?_, ?_⟩
  · have h1 : o * y⁻¹ * o⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hoN y⁻¹).1 (L.inv_mem hy)
    have := L.mul_mem hy h1
    simpa [mul_assoc] using this
  · have h1 : y * o * y⁻¹ ∈ GLAPPrimeCoreOf 3 H :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 H (hL.1 hy)) o).1 ho
    exact (GLAPPrimeCoreOf 3 H).mul_mem h1 ((GLAPPrimeCoreOf 3 H).inv_mem ho)

theorem _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115b.Sit.center_eq_bot_single
    (S : Claims1115b.Sit M E A K H a K') {L : Subgroup G} (hL : GLAPComponent 3 H L)
    (hJ : Lemma1115.jLayer a H = L) (haN : a ∈ Subgroup.normalizer (L : Set G))
    (hT : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty ((barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F)))
    (hnd : ¬ CFSG.HardMathSupport.Solomon.LocalBalance.IsInnDiagThree (barAut 3 L ⟨a, haN⟩)) :
    Subgroup.center (barOf 3 L) = ⊥ := by
  obtain ⟨hZp, hZiff⟩ := barX_center_facts hL
  by_contra hZ
  set Lt := barX 3 H L with hLt
  set Zt := Lt ⊓ Subgroup.centralizer (Lt : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) with hZt
  have hZ0 : Zt ≠ ⊥ := fun h => hZ (hZiff.1 h)
  have hK'L : K' ≤ L := hJ ▸ S.K'_le_jLayer
  have haLt : QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) ⟨a, S.haH⟩ ∈
      Subgroup.normalizer (Lt : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) :=
    barX_le_normalizer (Subgroup.zpowers_le.2 haN)
      (Inputs1115.mk_mem_barX S.haH (Subgroup.mem_zpowers a))
  have haZ : QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) ⟨a, S.haH⟩ ∈
      Subgroup.normalizer (Zt : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := mem_normalizer_center haLt
  have hZK : Zt ≤ Subgroup.centralizer (barX 3 H K' : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) :=
    inf_le_right.trans (Subgroup.centralizer_le (Inputs1115.barX_le_barX hK'L))
  have hmem := S.mem_sup_of_center hZp hZ0 haZ hZK
  have hA0L : barX 3 H (E ⊓ A) ≤ Lt := Inputs1115.barX_le_barX (S.A0_le.trans hK'L)
  have haLt' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) ⟨a, S.haH⟩ ∈ Lt :=
    (sup_le hA0L inf_le_left) hmem
  have haLO := CFSG.HardMathSupport.Solomon.Coordinator.i183_mem_sup_of_mk_mem haLt'
  have hON : GLAPPrimeCoreOf 3 H ≤ Subgroup.normalizer (L : Set G) := core_le_normalizer hL
  have haLO' : a ∈ ((L ⊔ GLAPPrimeCoreOf 3 H : Subgroup G) : Set G) := haLO
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L _ hON] at haLO'
  obtain ⟨l, hl, o, ho, hlo⟩ := haLO'
  apply hnd
  have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
  have hoN : o ∈ Subgroup.normalizer (L : Set G) := hON ho
  have e : (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨l, hlN⟩ * ⟨o, hoN⟩ :=
    Subtype.ext hlo.symm
  rw [e, map_mul, barAut_core_eq_one hL ho hoN, mul_one, Inputs1114.barAut_of_mem hl]
  exact isInnDiagThree_conj hT _

theorem le_centralizer_sup {Γ : Type*} [Group Γ] {P Q R : Subgroup Γ}
    (hP : R ≤ Subgroup.centralizer (P : Set Γ)) (hQ : R ≤ Subgroup.centralizer (Q : Set Γ)) :
    R ≤ Subgroup.centralizer ((P ⊔ Q : Subgroup Γ) : Set Γ) := by
  intro r hr
  have hle : P ⊔ Q ≤ Subgroup.centralizer ({r} : Set Γ) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (hP hr) x hx
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (hQ hr) x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem gLBConj_center {Γ : Type} [Group Γ] [Finite Γ] (g : Γ) (P : Subgroup Γ) :
    GLBConj g (P ⊓ Subgroup.centralizer (P : Set Γ)) =
      GLBConj g P ⊓ Subgroup.centralizer ((GLBConj g P : Subgroup Γ) : Set Γ) := by
  rw [Inputs1114.centralizer_gLBConj]
  exact Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective

theorem _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115b.Sit.center_eq_bot_triple
    (S : Claims1115b.Sit M E A K H a K') {L : Subgroup G}
    (c : CFSG.HardMathSupport.Solomon.Coordinator.I183vCyc H a L)
    (hJ : Lemma1115.jLayer a H = L ⊔ GLBConj a L ⊔ GLBConj a (GLBConj a L)) :
    Subgroup.center (barOf 3 L) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : GLAPComponent 3 H L := c.hM
  have hL₂ : GLAPComponent 3 H (GLBConj a L) := Inputs1115.glaPComponent_conj_of_mem hL S.haH
  have hL₃ : GLAPComponent 3 H (GLBConj a (GLBConj a L)) :=
    Inputs1115.glaPComponent_conj_of_mem hL₂ S.haH
  have h12 : L ≠ GLBConj a L := fun h => c.h1 h.symm
  have h13 : L ≠ GLBConj a (GLBConj a L) := fun h => c.h2 h.symm
  have ha3' : a * (a * a) = 1 := by rw [← pow_three]; exact S.ha3
  have h31 : GLBConj a (GLBConj a (GLBConj a L)) = L := by
    rw [gLBConj_gLBConj, gLBConj_gLBConj, ha3', gLBConj_one]
  obtain ⟨hZ₁p, hZ₁iff⟩ := barX_center_facts hL
  obtain ⟨hZ₂p, -⟩ := barX_center_facts hL₂
  obtain ⟨hZ₃p, -⟩ := barX_center_facts hL₃
  by_contra hZ
  let Zc : Subgroup G → Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H) := fun L₀ =>
    barX 3 H L₀ ⊓ Subgroup.centralizer (barX 3 H L₀ : Set (↥H ⧸ GLAPPrimeCore 3 ↥H))
  have hZc : ∀ L₀ : Subgroup G, GLBConj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) ⟨a, S.haH⟩) (Zc L₀) =
      Zc (GLBConj a L₀) := by
    intro L₀
    show GLBConj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) ⟨a, S.haH⟩)
        (barX 3 H L₀ ⊓ Subgroup.centralizer (barX 3 H L₀ : Set (↥H ⧸ GLAPPrimeCore 3 ↥H))) =
      barX 3 H (GLBConj a L₀) ⊓
        Subgroup.centralizer (barX 3 H (GLBConj a L₀) : Set (↥H ⧸ GLAPPrimeCore 3 ↥H))
    rw [gLBConj_center, barX_gLBConj_eq 3 S.haH]
  have hcomm : ∀ {L₀ L₀' : Subgroup G}, GLAPComponent 3 H L₀ → GLAPComponent 3 H L₀' →
      Zc L₀ ≤ Subgroup.centralizer (barX 3 H L₀' : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := by
    intro L₀ L₀' h₀ h₀'
    by_cases he : L₀ = L₀'
    · subst he
      exact inf_le_right
    · exact inf_le_left.trans (Claims1115b.barX_le_centralizer_of_ne' h₀' h₀ (Ne.symm he))
  have hcommZ : ∀ {L₀ L₀' : Subgroup G}, GLAPComponent 3 H L₀ → GLAPComponent 3 H L₀' →
      Zc L₀ ≤ Subgroup.centralizer (Zc L₀' : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) :=
    fun h₀ h₀' => (hcomm h₀ h₀').trans (Subgroup.centralizer_le inf_le_left)
  set Zt := Zc L ⊔ Zc (GLBConj a L) ⊔ Zc (GLBConj a (GLBConj a L)) with hZt
  have hZ0 : Zt ≠ ⊥ := by
    intro h
    apply hZ
    refine hZ₁iff.1 (le_bot_iff.1 ?_)
    rw [← h]
    exact le_sup_left.trans le_sup_left
  have hJbar : barX 3 H (Lemma1115.jLayer a H) =
      barX 3 H L ⊔ barX 3 H (GLBConj a L) ⊔ barX 3 H (GLBConj a (GLBConj a L)) := by
    rw [hJ, CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup (sup_le hL.1 hL₂.1) hL₃.1,
      CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup hL.1 hL₂.1]
  have hZiJ : ∀ {L₀ : Subgroup G}, GLAPComponent 3 H L₀ →
      Zc L₀ ≤ Subgroup.centralizer (barX 3 H (Lemma1115.jLayer a H) :
        Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := by
    intro L₀ h₀
    rw [hJbar]
    exact le_centralizer_sup (le_centralizer_sup (hcomm h₀ hL) (hcomm h₀ hL₂)) (hcomm h₀ hL₃)
  have hZtJ : Zt ≤ Subgroup.centralizer (barX 3 H (Lemma1115.jLayer a H) :
      Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := sup_le (sup_le (hZiJ hL) (hZiJ hL₂)) (hZiJ hL₃)
  have hZ12p : IsPGroup 3 ↥(Zc L ⊔ Zc (GLBConj a L)) :=
    IsPGroup.to_sup_of_normal_left' hZ₁p hZ₂p
      ((hcommZ hL₂ hL).trans (Subgroup.centralizer_le_normalizer _))
  have hZtp : IsPGroup 3 ↥Zt :=
    IsPGroup.to_sup_of_normal_left' hZ12p hZ₃p
      ((le_centralizer_sup (hcommZ hL₃ hL) (hcommZ hL₃ hL₂)).trans
        (Subgroup.centralizer_le_normalizer _))
  have haZ : QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) ⟨a, S.haH⟩ ∈
      Subgroup.normalizer (Zt : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    have e : ∀ (P Q : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H)) (g : ↥H ⧸ GLAPPrimeCore 3 ↥H),
        GLBConj g (P ⊔ Q) = GLBConj g P ⊔ GLBConj g Q := by
      intro P Q g
      unfold GLBConj
      exact Subgroup.map_sup _ _ _
    rw [hZt, e, e, hZc, hZc, hZc, h31]
    exact (sup_comm _ _).trans (sup_assoc _ _ _).symm
  have hZK : Zt ≤ Subgroup.centralizer (barX 3 H K' : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) :=
    hZtJ.trans (Subgroup.centralizer_le (Inputs1115.barX_le_barX S.K'_le_jLayer))
  have hmem := S.mem_sup_of_center hZtp hZ0 haZ hZK
  have hZtJ' : Zt ≤ barX 3 H (Lemma1115.jLayer a H) := by
    rw [hJbar]
    exact sup_le_sup (sup_le_sup inf_le_left inf_le_left) inf_le_left
  have hA0J : barX 3 H (E ⊓ A) ≤ barX 3 H (Lemma1115.jLayer a H) :=
    Inputs1115.barX_le_barX (S.A0_le.trans S.K'_le_jLayer)
  have haJ : QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) ⟨a, S.haH⟩ ∈
      barX 3 H (Lemma1115.jLayer a H) := (sup_le hA0J hZtJ') hmem
  have haJO := CFSG.HardMathSupport.Solomon.Coordinator.i183_mem_sup_of_mk_mem haJ
  have hJN : Lemma1115.jLayer a H ⊔ GLAPPrimeCoreOf 3 H ≤ Subgroup.normalizer (L : Set G) := by
    refine sup_le ?_ (core_le_normalizer hL)
    rw [hJ]
    exact sup_le (sup_le Subgroup.le_normalizer (le_normalizer_of_ne hL hL₂ h12))
      (le_normalizer_of_ne hL hL₃ h13)
  exact c.h1 (gLBConj_eq_of_mem_normalizer (hJN haJO))

end Centre

section CoverTransfer

variable {G : Type} [Group G] [Finite G]

theorem covers_of_covers_sub {H X J N : Subgroup G} {𝒞 : Set (Subgroup G)} (hJ : IsJoin H J 𝒞)
    (hJX : J ≤ X) (hXH : X ≤ H) (hcov : Covers 3 X N J) : Covers 3 H (N ⊓ H) J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOXX : GLAPPrimeCoreOf 3 X ≤ X := Subgroup.map_subtype_le _
  have hOXH : GLAPPrimeCoreOf 3 X ≤ H := hOXX.trans hXH
  have hOH : GLAPPrimeCoreOf 3 H ≤ H := Subgroup.map_subtype_le _
  have hUc : Nat.Coprime 3 (Nat.card (barX 3 H (GLAPPrimeCoreOf 3 X))) :=
    Claims1115b.coprime_card_barX hOXH
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 X)
  have hJU : barX 3 H J ≤ Subgroup.normalizer (barX 3 H (GLAPPrimeCoreOf 3 X) :
      Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) :=
    barX_le_normalizer (hJX.trans (le_normalizer_glaPPrimeCoreOf 3 X))
  have hJc := hJ.barX_le_centralizer hUc hJU
  have hkey : ∀ L ∈ 𝒞, ∀ s ∈ L, (∃ j : ℕ, s ^ 3 ^ j = 1) →
      s ∈ (N ⊓ H) ⊔ GLAPPrimeCoreOf 3 H := by
    rintro L hL s hsL ⟨j, hj⟩
    have hsJ : s ∈ J := hJ.mem_le hL hsL
    have hsX : s ∈ X := hJX hsJ
    have hsH : s ∈ H := hXH hsX
    obtain ⟨y, hyN, hys⟩ := exists_of_barX_le hcov hsJ hsX
    have hyX : y ∈ X := by
      have h1 := X.mul_mem hsX (X.inv_mem (hOXX hys))
      have e : s * (y⁻¹ * s)⁻¹ = y := by group
      rwa [e] at h1
    have hyH : y ∈ H := hXH hyX
    have huH : y⁻¹ * s ∈ H := hOXH hys
    set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) with hπ
    have hs : π ⟨s, hsH⟩ = π ⟨y, hyH⟩ * π ⟨y⁻¹ * s, huH⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext (by simp)
    have hsu : Commute (π ⟨s, hsH⟩) (π ⟨y⁻¹ * s, huH⟩) :=
      (Subgroup.mem_centralizer_iff.1 (hJc (Inputs1115.mk_mem_barX hsH hsJ)) _
        (Inputs1115.mk_mem_barX huH hys)).symm
    set ub := π ⟨y⁻¹ * s, huH⟩ with hub
    set sb := π ⟨s, hsH⟩ with hsb
    set wb := π ⟨y, hyH⟩ with hwb
    have hwe : wb ^ orderOf ub = sb ^ orderOf ub := by
      have hw' : wb = sb * ub⁻¹ := by rw [hs]; group
      rw [hw', (hsu.inv_right).mul_pow, inv_pow, pow_orderOf_eq_one, inv_one, mul_one]
    have hs3 : sb ^ 3 ^ j = 1 := by
      rw [hsb, ← map_pow]
      have e : (⟨s, hsH⟩ : ↥H) ^ 3 ^ j = 1 := Subtype.ext (by simpa using hj)
      rw [e, map_one]
    have hcop : (orderOf ub).gcd (orderOf sb) = 1 := by
      have h1 : orderOf sb ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hs3
      have h2 : orderOf ub ∣ Nat.card (barX 3 H (GLAPPrimeCoreOf 3 X)) :=
        Subgroup.orderOf_dvd_natCard _ (Inputs1115.mk_mem_barX huH hys)
      have h3 : Nat.Coprime (orderOf ub) (3 ^ j) :=
        Nat.Coprime.pow_right j (Nat.Coprime.coprime_dvd_left h2 hUc.symm)
      exact Nat.Coprime.coprime_dvd_right h1 h3
    have hmem : sb ∈ Subgroup.zpowers (sb ^ orderOf ub) := mem_zpowers_pow_iff.2 hcop
    have hsW : sb ∈ barX 3 H (N ⊓ H) := by
      have hwbar : wb ^ orderOf ub ∈ barX 3 H (N ⊓ H) :=
        Subgroup.pow_mem _ (Inputs1115.mk_mem_barX hyH (Subgroup.mem_inf.2 ⟨hyN, hyH⟩)) _
      rw [hwe] at hwbar
      exact (Subgroup.zpowers_le.2 hwbar) hmem
    exact CFSG.HardMathSupport.Solomon.Coordinator.i183_mem_sup_of_mk_mem hsW
  have hJW : J ≤ (N ⊓ H) ⊔ GLAPPrimeCoreOf 3 H := hJ.le_of_pElements hkey
  show barX 3 H J ≤ barX 3 H (N ⊓ H)
  calc barX 3 H J ≤ barX 3 H ((N ⊓ H) ⊔ GLAPPrimeCoreOf 3 H) := Inputs1115.barX_le_barX hJW
    _ = barX 3 H (N ⊓ H) := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup inf_le_right hOH,
        (CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_eq_bot_iff hOH).2 le_rfl, sup_bot_eq]

theorem ne_bot_of_isMaxInvTwoSub {H A T : Subgroup G} (hH : IsTwoLocal H) (hAH : A ≤ H)
    (hT : IsMaxInvTwoSub H A T) : T ≠ ⊥ := by
  intro hbot
  obtain ⟨Q, hQ1, hQ2, hHQ⟩ := hH
  have hPH : pCoreOf 2 H ≤ H := Subgroup.map_subtype_le _
  have hHP : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := Inputs1114.le_normalizer_pCoreOf_two le_rfl
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 H) := Lemma1114.isPGroup_pCoreOf_two H
  have hQH : Q ≤ H := by
    rw [hHQ]
    exact Subgroup.le_normalizer
  have hQP : Q ≤ pCoreOf 2 H := Lemma1114.le_pCoreOf_two_of_normal hQH hQ2 fun y hy w hw => by
    rw [hHQ] at hy
    exact (Subgroup.mem_normalizer_iff.1 hy w).1 hw
  have hTP : T ≤ pCoreOf 2 H := by
    rw [hbot]
    exact bot_le
  have hPT : pCoreOf 2 H = T := hT.2.2.2 _ hPH hP2 (hAH.trans hHP) hTP
  apply hQ1
  rw [eq_bot_iff, ← hbot, ← hPT]
  exact hQP

end CoverTransfer

section PushUpX

variable {G : Type} [Group G] [Finite G] {M E A K H : Subgroup G} {a : G} {K' : Subgroup G}

@[expose] def Centre3D44 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q → GLAPPrimeCore 3 Q = ⊥ →
    IsCatalogLieIso (Q ⧸ Subgroup.center Q) Is3D44Index → Subgroup.center Q = ⊥

theorem _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115b.Sit.not_mem_K'
    (S : Claims1115b.Sit M E A K H a K') : a ∉ K' := by
  intro haK
  have hK'C : K' ≤ Cg a := S.hK'.1.trans inf_le_right
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K') with hπ
  have hcen : π ⟨a, haK⟩ ∈ Subgroup.center (barOf 3 K') := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K') z
    have hk : (k : G) * a = a * k := Subgroup.mem_centralizer_singleton_iff.1 (hK'C k.2)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hk
  rw [Claims1115b.center_eq_bot_of_isLThreeFour (Claims1115b.isLThreeFour_barOf_K' S.cfg S.hK' S.hbar),
    Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  have hdvd : orderOf (⟨a, haK⟩ : ↥K') ∣ Nat.card (GLAPPrimeCore 3 ↥K') :=
    Subgroup.orderOf_dvd_natCard _ hcen
  rw [Subgroup.orderOf_mk] at hdvd
  have hcop := CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥K'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf a = 3 := orderOf_eq_prime S.ha3 S.cfg.ha1
  rw [hord] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop hdvd

theorem _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115b.Sit.zpowers_inf
    (S : Claims1115b.Sit M E A K H a K') : Subgroup.zpowers a ⊓ (A ⊓ K') = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf a = 3 := orderOf_eq_prime S.ha3 S.cfg.ha1
  rw [inf_comm]
  exact GL83.CompFam.inf_zpowers_eq_bot hord fun h => S.not_mem_K' h.2

theorem _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115b.Sit.zpowers_sup
    (S : Claims1115b.Sit M E A K H a K') : Subgroup.zpowers a ⊔ (A ⊓ K') = A := by
  have hAeq : (E ⊓ A) ⊔ Subgroup.zpowers a = A :=
    (Lemma1114.coord_setup S.cfg.hAel S.cfg.hA27 inf_le_right S.cfg.hA0card S.cfg.ha S.cfg.ha1
      S.cfg.haA0).2
  refine le_antisymm (sup_le (Subgroup.zpowers_le.2 S.cfg.ha) inf_le_left) ?_
  calc A = (E ⊓ A) ⊔ Subgroup.zpowers a := hAeq.symm
    _ ≤ Subgroup.zpowers a ⊔ (A ⊓ K') :=
      sup_le (le_sup_of_le_right (le_inf inf_le_right S.A0_le)) le_sup_left

theorem _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115b.Sit.types_X {m : ℕ} {B : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) (h1111 : Lemma1111Statement) (h104v : Lemma104_vStatement)
    (h111 : Prop111Statement) (hup34 : CFSG.HardMathSupport.Dickson.Sec6.Up34Statement)
    (hD44 : Claims1115b.Seitz2310D44Inner) (h102 : Claims1115b.Input10_2D44) (hZ3D4 : Centre3D44)
    (S : Claims1115b.Sit M E A K H a K') {X : Subgroup G}
    (hJX : Lemma1115.jLayer a H ≤ X) (hXH : X ≤ H) (hlayer : GLAPLayer 3 X = Lemma1115.jLayer a H) :
    IsLThreeFour ↥(barX 3 X (GLAPLayer 3 X)) ∨
      IsCatalogLieIso ↥(barX 3 X (GLAPLayer 3 X)) IsL364Index ∨
      IsCatalogLieIso ↥(barX 3 X (GLAPLayer 3 X)) Is3D44Index ∨
      IsLThreeFourCubeLayer X := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hbar : ∀ {L₀ : Subgroup G}, GLAPComponent 3 X L₀ → IsLThreeFour (barOf 3 L₀) →
      IsLThreeFour ↥(barX 3 X L₀) := by
    intro L₀ hL₀ h34
    obtain ⟨F, hF, hFf, hcF, ⟨f⟩⟩ := h34
    exact ⟨F, hF, hFf, hcF, ⟨(quotEquivBarX hp hL₀.1 hL₀.2.1).symm.trans f⟩⟩
  rcases S.cases with ⟨L, hL, haL, hJ⟩ | ⟨L, c, hJ⟩
  · rw [hlayer, hJ]
    rw [hJ] at hJX
    have hLX : GLAPComponent 3 X L := glaPComponent_of_le hp hL hJX hXH
    have e : barOf 3 L ≃* ↥(barX 3 X L) := quotEquivBarX hp hLX.1 hLX.2.1
    rcases S.single_types hup34 hL haL hJ with ⟨-, h34⟩ | ⟨-, haN, htype⟩
    · exact Or.inl (hbar hLX h34)
    · rcases htype with ⟨hcat, hnd⟩ | hcat | ⟨hD4, hZD⟩
      · refine Or.inr (Or.inl ?_)
        obtain ⟨K₀, hK₀, hK₀f, -, ⟨e₀⟩⟩ :=
          CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.exists_model_of_catalogL364 hcat
        have hZ := S.center_eq_bot_single hL hJ haN ⟨K₀, hK₀, hK₀f, ⟨e₀⟩⟩ hnd
        have eZ : (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ≃* barOf 3 L :=
          (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
        obtain ⟨d, hd, ⟨f⟩⟩ := hcat
        exact ⟨d, hd, ⟨e.symm.trans (eZ.symm.trans f)⟩⟩
      · refine Or.inr (Or.inr (Or.inl ?_))
        obtain ⟨hq, hcore⟩ := Claims1115b.barOf_facts hL
        have hZ := hZ3D4 (barOf 3 L) hq hcore hcat
        have eZ : (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ≃* barOf 3 L :=
          (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
        obtain ⟨d, hd, ⟨f⟩⟩ := hcat
        exact ⟨d, hd, ⟨e.symm.trans (eZ.symm.trans f)⟩⟩
      · exact (S.false_of_D44 h h1111 h104v h111 hD44 h102 hL hJ hD4 hZD).elim
  · refine Or.inr (Or.inr (Or.inr ?_))
    have hL : GLAPComponent 3 H L := c.hM
    have hL₂ : GLAPComponent 3 H (GLBConj a L) := Inputs1115.glaPComponent_conj_of_mem hL S.haH
    have hL₃ : GLAPComponent 3 H (GLBConj a (GLBConj a L)) :=
      Inputs1115.glaPComponent_conj_of_mem hL₂ S.haH
    have hJX' : L ⊔ GLBConj a L ⊔ GLBConj a (GLBConj a L) ≤ X := hJ ▸ hJX
    have hK₁ := glaPComponent_of_le hp hL ((le_sup_left.trans le_sup_left).trans hJX') hXH
    have hK₂ := glaPComponent_of_le hp hL₂ ((le_sup_right.trans le_sup_left).trans hJX') hXH
    have hK₃ := glaPComponent_of_le hp hL₃ (le_sup_right.trans hJX') hXH
    have h34 : IsLThreeFour (barOf 3 L) := by
      have hZ := S.center_eq_bot_triple c hJ
      have eZ : (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ≃* barOf 3 L :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      obtain ⟨F, hF, hFf, hcF, ⟨f⟩⟩ := S.triple_type c hJ
      exact ⟨F, hF, hFf, hcF, ⟨eZ.symm.trans f⟩⟩
    have hconj : ∀ (g : G) (L₀ : Subgroup G), IsLThreeFour (barOf 3 L₀) →
        IsLThreeFour (barOf 3 (GLBConj g L₀)) := by
      intro g L₀ h34'
      obtain ⟨F, hF, hFf, hcF, ⟨f⟩⟩ := h34'
      exact ⟨F, hF, hFf, hcF, ⟨(conjQuotEquiv 3 g L₀).symm.trans f⟩⟩
    have h23 : GLBConj a L ≠ GLBConj a (GLBConj a L) := by
      intro h'
      apply c.h1
      have := congrArg (GLBConj a⁻¹) h'
      rw [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at this
      exact this.symm
    refine ⟨L, GLBConj a L, GLBConj a (GLBConj a L), hK₁, hK₂, hK₃, fun h' => c.h1 h'.symm,
      fun h' => c.h2 h'.symm, h23, ?_, hbar hK₁ h34, hbar hK₂ (hconj a L h34),
      hbar hK₃ (hconj a _ (hconj a L h34))⟩
    rw [hlayer, hJ]

end PushUpX

section PushUpMain

theorem centre3D44_holds :
    Centre3D44 := by
  intro Q _ _ hq hcore hiso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨x, hv⟩, hd, ⟨e⟩⟩ := hiso
  obtain ⟨q, rfl, hqp, -⟩ : ∃ q : TauCeti.PrimePower,
      x = TauCeti.LieTypeIndex.trialityD4 q ∧ q.p = 2 ∧ q.exponent = 2 := by
    cases x <;> first | exact ⟨_, rfl, hd⟩ | exact hd.elim
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩).Group .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hqp (by decide) (MulEquiv.refl _)⟩
  rw [hqp] at hm
  have hmod := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hm
  have : Group.IsPerfect Q := ⟨hq.1⟩
  have hZ3 : IsPGroup 3 (Subgroup.center Q) := isPGroup_center Nat.prime_three hcore
  have hZodd : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center Q)).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ3
    rw [hn]
    exact Odd.pow (by decide)
  have hker := CFSG.SectionRank.triality_even_perfect_odd_cover_trivial hmod
    (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hZodd
  rwa [QuotientGroup.ker_mk'] at hker

theorem seitz2310D44Inner_holds :
    Claims1115b.Seitz2310D44Inner := by
  intro Y _ _ hs hD A hA hcard hinn
  obtain ⟨⟨x, hv⟩, hd, ⟨e⟩⟩ := hD
  obtain ⟨q, rfl, hq2, hqe⟩ : ∃ q : TauCeti.PrimePower,
      x = TauCeti.LieTypeIndex.D 4 q ∧ q.p = 2 ∧ q.exponent = 2 := by
    cases x <;> first | exact ⟨_, by rw [hd.1], hd.2.1, hd.2.2⟩ | exact hd.elim
  have hL : CFSG.LieType.SeitzGeneration.SeitzHyperLie fun d _ _ => IsD44Index d.1 := by
    intro d' p hp hp2 hpd hlist E₀ hE₀ hc hD'
    by_cases hred : CFSG.LieType.SeitzGeneration.OReducible d' p E₀
    · exact CFSG.LieType.SeitzGeneration.seitzHyperLie_orthReducible d' p hp hp2 hpd hlist E₀ hE₀ hc
        hred
    · refine CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.seitzGoodInnerOrth_holds d' p hp hp2 hpd
        hlist E₀ hE₀ hc ⟨?_, hred, Or.inr ?_⟩
      · obtain ⟨x', hv'⟩ := d'
        cases x' <;> first | exact Or.inr (Or.inl ⟨_, _, rfl⟩) | exact hD'.elim
      · exact Or.inr (Or.inl
          ((CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isD44Index_iff _).2 hD'))
  have hCP : CFSG.LieType.SeitzGeneration.SeitzHyperInnerCP fun d => IsD44Index d.1 := by
    intro p hp hp2 Y' _ _ K₀ E₀ hKn hKq d' hd' he' hpd hlist hEa hEc hker hin hz
    exfalso
    obtain ⟨e'⟩ := he'
    have hZ : Subgroup.center ↥K₀ = ⊥ :=
      CFSG.HardMathSupport.Dickson.Sec6.up34D44Centre_holds K₀ hKq ⟨d', hd', ⟨e'⟩⟩
    rw [hZ, Subgroup.card_bot] at hz
    exact hp.one_lt.ne' (Nat.dvd_one.1 hz)
  have hF := CFSG.LieType.SeitzGeneration.seitzHyperInnerFor_of_lie_cp hL hCP
  have hnab : ∃ y z : Y, y * z ≠ z * y := by
    by_contra hab
    push Not at hab
    have hbot : (MulAut.conj : Y →* MulAut Y).range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨y, rfl⟩
      rw [Subgroup.mem_bot]
      ext z
      simp [MulAut.conj_apply, hab y z]
    have h1 := Subgroup.card_le_of_le (hinn.trans hbot.le)
    rw [Subgroup.card_bot, hcard] at h1
    norm_num at h1
  have hpd : (3 : ℕ) ≠ (TauCeti.LieTypeIndex.D 4 q).characteristic := by
    rw [TauCeti.LieTypeIndex.characteristic_D, hq2]
    norm_num
  have hP : ¬ CFSG.AGLEmbedding.P1ThreeLieList 3 ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩ := by
    intro hlist
    simp [CFSG.AGLEmbedding.P1ThreeLieList, CFSG.AGLEmbedding.IsLinTwoIndex,
      CFSG.AGLEmbedding.IsUnitaryIndex, CFSG.AGLEmbedding.IsReeGTwoIndex,
      CFSG.AGLEmbedding.IsSpFourIndex, CFSG.AGLEmbedding.IsP1ChevTwoIndex, hqe] at hlist
  exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.seitzHyperGamma_eq_top_of_inner hF
    Nat.prime_three (by norm_num) hs hnab ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩ hd e hpd hP hA hcard hinn

end PushUpMain

section PairE81

open QuadraticMap Module
open CFSG.HardMathSupport.Solomon.Coordinator.LBID4

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def frameSw (F : EFrame Q) : EFrame Q where
  b := F.b
  b' := -F.b - F.b'
  c := F.c
  c_ne := F.c_ne
  q_b := F.q_b
  q_b' := by
    rw [show -F.b - F.b' = -(F.b + F.b') by abel, QuadraticMap.map_neg, q_add, F.q_b, F.q_b',
      F.polar_bb']
    ring
  polar_bb' := by
    rw [polar_sub_right, polar_neg_right, F.polar_bb, F.polar_bb']
    ring

theorem frameSw_b (F : EFrame Q) : (frameSw F).b = F.b := rfl

theorem frameSw_b' (F : EFrame Q) : (frameSw F).b' = -F.b - F.b' := rfl

theorem frameSw_orth {F : EFrame Q} {v : V} : (frameSw F).Orth v ↔ F.Orth v := by
  simp only [EFrame.Orth, frameSw_b, frameSw_b', polar_sub_right, polar_neg_right]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h1] at h2
    linear_combination -h2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h1, h2]; ring⟩

theorem frameSw_orthSub (F : EFrame Q) : (frameSw F).orthSub = F.orthSub := by
  ext v
  rw [EFrame.mem_orthSub, EFrame.mem_orthSub, frameSw_orth]

theorem frameSw_perp_left {F G : EFrame Q} (h : F.Perp G) : (frameSw F).Perp G :=
  ⟨frameSw_orth.2 h.1, frameSw_orth.2 h.2⟩

theorem frameSw_perp_right {F G : EFrame Q} (h : F.Perp G) : F.Perp (frameSw G) := by
  refine ⟨h.1, ?_⟩
  rw [frameSw_b']
  exact ⟨by rw [polar_sub_left, polar_neg_left, h.1.1, h.2.1]; ring,
    by rw [polar_sub_left, polar_neg_left, h.1.2, h.2.2]; ring⟩

theorem frameSw_rot (h3 : (3 : K) ≠ 0) (F : EFrame Q) : (frameSw F).rot = F.rot ^ 2 := by
  have hext : (frameSw F).rotL = F.rotL ∘ₗ F.rotL := by
    refine F.linearMap_ext h3 ?_ ?_ ?_
    · rw [LinearMap.comp_apply, EFrame.rotL_b, EFrame.rotL_b']
      exact (frameSw F).rotL_b
    · have e : F.b' = -(frameSw F).b - (frameSw F).b' := by
        rw [frameSw_b, frameSw_b']
        abel
      have hL : (frameSw F).rotL F.b' = F.b := by
        rw [e, map_sub, map_neg, EFrame.rotL_b, EFrame.rotL_b', frameSw_b, frameSw_b']
        abel
      have hR : F.rotL (F.rotL F.b') = F.b := by
        rw [EFrame.rotL_b', map_sub, map_neg, EFrame.rotL_b, EFrame.rotL_b']
        abel
      rw [LinearMap.comp_apply, hL, hR]
    · intro v hv
      rw [LinearMap.comp_apply, F.rotL_of_orth hv, F.rotL_of_orth hv,
        (frameSw F).rotL_of_orth (frameSw_orth.2 hv)]
  ext v
  rw [pow_two, LinearEquiv.mul_apply, EFrame.rot_apply, EFrame.rot_apply, EFrame.rot_apply]
  exact LinearMap.congr_fun hext v

@[expose] def PAdapted (g : V ≃ₗ[K] V) (F : EFrame Q) : Prop := Adapted g F ∨ Adapted g (frameSw F)

theorem padapted_inf_orthSub_invariant {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {F : EFrame Q} (hF : PAdapted g F)
    {M : Submodule K V} (hM : ∀ v ∈ M, g v ∈ M) : ∀ v ∈ M ⊓ F.orthSub, g v ∈ M ⊓ F.orthSub := by
  rcases hF with hF | hF
  · exact F.inf_orthSub_invariant hg hF hM
  · rw [← frameSw_orthSub F]
    exact (frameSw F).inf_orthSub_invariant hg hF hM

theorem nDeg_inf_fixSp (h3 : (3 : K) ≠ 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : ∀ v, g (g (g v)) = v)
    {M : Submodule K V} (hM : NDeg Q M) (hMg : ∀ v ∈ M, g v ∈ M) : NDeg Q (M ⊓ fixSp g) := by
  intro v hv hvw
  refine hM v hv.1 fun m hm => ?_
  set p := (3 : K)⁻¹ • (m + g m + g (g m)) with hp
  have hpM : p ∈ M := M.smul_mem _ (M.add_mem (M.add_mem hm (hMg m hm)) (hMg _ (hMg m hm)))
  have e : m = p + (m - p) := by abel
  rw [e, polar_add_right, hvw p ⟨hpM, fix3_mem hg3 m⟩, zero_add]
  exact polar_fixSp_movSp h3 hg hv.2 (sub_fix3_mem h3 hg3 m)

variable {g h : V ≃ₗ[K] V}

theorem exists_moved_frame (h3 : (3 : K) ≠ 0) (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : ∀ v, g (g (g v)) = v)
    (hh3 : ∀ v, h (h (h v)) = v) (hgh : ∀ v, h (g v) = g (h v))
    {M : Submodule K V} (hM : NDeg Q M) (hMg : ∀ v ∈ M, g v ∈ M) (hMh : ∀ v ∈ M, h v ∈ M)
    (hmov : M ⊓ movSp g ≠ ⊥ ∨ M ⊓ movSp h ≠ ⊥) :
    ∃ F : EFrame Q, F.b ∈ M ∧ F.b' ∈ M ∧ PAdapted g F ∧ PAdapted h F := by
  by_cases hgm : M ⊓ movSp g = ⊥
  ·
    have hfix := le_fixSp_of_inf_movSp h3 hg3 hMg hgm
    have hhm : M ⊓ movSp h ≠ ⊥ := hmov.resolve_left fun h' => h' hgm
    obtain ⟨v, hv, hQv⟩ := (nDeg_inf_movSp h3 hh3 hh hM hMh).exists_ne_zero hhm
    obtain ⟨F, hFb, hFb', hFa⟩ := exists_rotFrame hh hv.2 hQv
    refine ⟨F, hFb ▸ hv.1, hFb' ▸ hMh v hv.1, Or.inl (adapted_of_mem_fixSp ?_ ?_), Or.inl hFa⟩
    · rw [hFb]; exact hfix hv.1
    · rw [hFb']; exact hfix (hMh v hv.1)
  ·
    set M' := M ⊓ movSp g with hM'def
    have hM' : NDeg Q M' := nDeg_inf_movSp h3 hg3 hg hM hMg
    have hmovh : ∀ v ∈ movSp g, h v ∈ movSp g := by
      intro v hv
      rw [mem_movSp] at hv ⊢
      have := congrArg h hv
      simp only [map_add, map_zero, hgh] at this
      exact this
    have hM'g : ∀ v ∈ M', g v ∈ M' := fun v hv => ⟨hMg v hv.1, movSp_apply_mem hg3 hv.2⟩
    have hM'h : ∀ v ∈ M', h v ∈ M' := fun v hv => ⟨hMh v hv.1, hmovh v hv.2⟩
    have hmulO : ∀ x y : V ≃ₗ[K] V, x ∈ TauCeti.QuadraticMap.orthogonalGroup Q →
        y ∈ TauCeti.QuadraticMap.orthogonalGroup Q →
        x * y ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun x y hx hy =>
      Subgroup.mul_mem _ hx hy
    have hcube : ∀ (a b : ℕ) (v : V), ((g ^ a * h ^ b) ^ 3) v = v := by
      intro a b v
      have hc : Commute (g ^ a) (h ^ b) := by
        refine Commute.pow_pow ?_ a b
        ext w
        exact (hgh w).symm
      rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm a 3, mul_comm b 3, pow_mul, pow_mul]
      have hg3' : g ^ 3 = 1 := by
        ext w
        rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        exact hg3 w
      have hh3' : h ^ 3 = 1 := by
        ext w
        rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        exact hh3 w
      rw [hg3', hh3', one_pow, one_pow, mul_one]
      rfl
    have hinv : ∀ (a b : ℕ), ∀ v ∈ M', (g ^ a * h ^ b) v ∈ M' := by
      intro a b v hv
      rw [LinearEquiv.mul_apply]
      have hb : ∀ k : ℕ, ∀ w ∈ M', (h ^ k) w ∈ M' := by
        intro k
        induction k with
        | zero => intro w hw; simpa using hw
        | succ k ih =>
          intro w hw
          rw [pow_succ', LinearEquiv.mul_apply]
          exact hM'h _ (ih w hw)
      have ha : ∀ k : ℕ, ∀ w ∈ M', (g ^ k) w ∈ M' := by
        intro k
        induction k with
        | zero => intro w hw; simpa using hw
        | succ k ih =>
          intro w hw
          rw [pow_succ', LinearEquiv.mul_apply]
          exact hM'g _ (ih w hw)
      exact ha a _ (hb b v hv)
    have hnO : ∀ a b : ℕ, g ^ a * h ^ b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      fun a b => hmulO _ _ (Subgroup.pow_mem _ hg a) (Subgroup.pow_mem _ hh b)
    have hn3 : ∀ (a b : ℕ) (v : V), (g ^ a * h ^ b) ((g ^ a * h ^ b) ((g ^ a * h ^ b) v)) = v := by
      intro a b v
      have := hcube a b v
      rwa [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
    obtain ⟨w, hwM', hw0⟩ := (Submodule.ne_bot_iff M').mp hgm
    have hw : w + g w + g (g w) = 0 := mem_movSp.mp hwM'.2
    have r1 : h w + g (h w) + g (g (h w)) = 0 := by
      have := congrArg h hw
      simp only [map_add, map_zero, hgh] at this
      exact this
    have r2 : h (h w) + g (h (h w)) + g (g (h (h w))) = 0 := by
      have := congrArg h r1
      simp only [map_add, map_zero, hgh] at this
      exact this
    have key : (3 : K) • w = (w + h w + h (h w)) + (w + g (h w) + g (g (h (h w)))) +
        (w + g (h (h w)) + g (g (h w))) := by
      have e : (w + h w + h (h w)) + (w + g (h w) + g (g (h (h w)))) +
          (w + g (h (h w)) + g (g (h w))) =
          (3 : K) • w + (h w + g (h w) + g (g (h w))) + (h (h w) + g (h (h w)) + g (g (h (h w)))) := by
        module
      rw [e, r1, r2, add_zero, add_zero]
    have hP : ∀ (a b : ℕ), (g ^ a * h ^ b) ((3 : K)⁻¹ • (w + (g ^ a * h ^ b) w +
        (g ^ a * h ^ b) ((g ^ a * h ^ b) w))) =
        (3 : K)⁻¹ • (w + (g ^ a * h ^ b) w + (g ^ a * h ^ b) ((g ^ a * h ^ b) w)) := by
      intro a b
      rw [map_smul, map_add, map_add, hn3]
      congr 1
      abel
    have hPM : ∀ (a b : ℕ), (3 : K)⁻¹ • (w + (g ^ a * h ^ b) w +
        (g ^ a * h ^ b) ((g ^ a * h ^ b) w)) ∈ M' := fun a b =>
      M'.smul_mem _ (M'.add_mem (M'.add_mem hwM' (hinv a b w hwM')) (hinv a b _ (hinv a b w hwM')))
    obtain ⟨a, b, hab, hne⟩ : ∃ a b : ℕ, ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) ∧
        (3 : K)⁻¹ • (w + (g ^ a * h ^ b) w + (g ^ a * h ^ b) ((g ^ a * h ^ b) w)) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have e0 := hcon 0 1 (Or.inl ⟨rfl, rfl⟩)
      have e1 := hcon 1 1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have e2 := hcon 1 2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      simp only [pow_zero, pow_one, one_mul, LinearEquiv.mul_apply, pow_two, hgh, hh3] at e0 e1 e2
      rw [smul_eq_zero, or_iff_right (inv_ne_zero h3)] at e0 e1 e2
      rw [e0, e1, e2, add_zero, add_zero, smul_eq_zero] at key
      exact hw0 (key.resolve_left h3)
    set n := g ^ a * h ^ b with hn
    have hM'' : NDeg Q (M' ⊓ fixSp n) := nDeg_inf_fixSp h3 (hnO a b) (hn3 a b) hM' (hinv a b)
    have hne' : M' ⊓ fixSp n ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨_, ⟨hPM a b, (mem_fixSp).mpr (hP a b)⟩, hne⟩
    obtain ⟨v, hv, hQv⟩ := hM''.exists_ne_zero hne'
    have hvM : v ∈ M := hv.1.1
    have hvg : v ∈ movSp g := hv.1.2
    have hvn : n v = v := mem_fixSp.mp hv.2
    obtain ⟨F, hFb, hFb', hFa⟩ := exists_rotFrame hg hvg hQv
    refine ⟨F, hFb ▸ hvM, hFb' ▸ hMg v hvM, Or.inl hFa, ?_⟩
    have hgg : g (g v) = -v - g v := by
      have := mem_movSp.mp hvg
      rw [← sub_eq_zero, ← this]
      abel
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    ·
      have hhv : h v = v := by simpa [hn] using hvn
      have hA : Adapted h F := Or.inl ⟨by rw [hFb, hhv], by rw [hFb', hgh, hhv]⟩
      exact Or.inl hA
    ·
      have hhv : g (h v) = v := by simpa [hn] using hvn
      have hhv' : h v = -v - g v := by
        have e : g (g (g (h v))) = g (g v) := by rw [hhv]
        rw [hg3] at e
        rw [e, hgg]
      have hA : Adapted h (frameSw F) := Or.inr ⟨by rw [frameSw_b, frameSw_b', hFb, hFb', hhv'],
        by rw [frameSw_b, frameSw_b', hFb, hFb', map_sub, map_neg, hhv', hgh, hhv]; abel⟩
      exact Or.inr hA
    ·
      have hhv : g (h (h v)) = v := by simpa [hn, pow_two] using hvn
      have hh2 : h (h v) = g (g v) := by
        have e : g (g (g (h (h v)))) = g (g v) := by rw [hhv]
        rw [hg3] at e
        exact e
      have hhv' : h v = g v := by
        calc h v = h (h (h (h v))) := by rw [hh3]
          _ = h (h (g (g v))) := by rw [hh2]
          _ = g (g (h (h v))) := by simp only [hgh]
          _ = g (g (g (g v))) := by rw [hh2]
          _ = g v := by rw [hg3]
      have hA : Adapted h F := Or.inr ⟨by rw [hFb, hFb', hhv'], by rw [hFb', hFb, hgh, hhv', hgg]⟩
      exact Or.inl hA

theorem exists_padapted_frame [Finite K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg3 : ∀ v, g (g (g v)) = v) (hh3 : ∀ v, h (h (h v)) = v) (hgh : ∀ v, h (g v) = g (h v))
    {M : Submodule K V} (hM : NDeg Q M) (hMg : ∀ v ∈ M, g v ∈ M) (hMh : ∀ v ∈ M, h v ∈ M)
    (h4 : 4 ≤ finrank K M) :
    ∃ F : EFrame Q, F.b ∈ M ∧ F.b' ∈ M ∧ PAdapted g F ∧ PAdapted h F := by
  by_cases hmov : M ⊓ movSp g ≠ ⊥ ∨ M ⊓ movSp h ≠ ⊥
  · exact exists_moved_frame h3 hg hh hg3 hh3 hgh hM hMg hMh hmov
  · push Not at hmov
    have hfg := le_fixSp_of_inf_movSp h3 hg3 hMg hmov.1
    have hfh := le_fixSp_of_inf_movSp h3 hh3 hMh hmov.2
    obtain ⟨F, hb, hb'⟩ := exists_frame_of_nDeg hM h4
    exact ⟨F, hb, hb', Or.inl (adapted_of_mem_fixSp (hfg hb) (hfg hb')),
      Or.inl (adapted_of_mem_fixSp (hfh hb) (hfh hb'))⟩

theorem exists_padapted_frame_last [Finite K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg3 : ∀ v, g (g (g v)) = v) (hh3 : ∀ v, h (h (h v)) = v) (hgh : ∀ v, h (g v) = g (h v))
    (hB : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8) {W : Submodule K V}
    (hW : ∀ w ∈ W, Q w = 0) (hWdim : finrank K W = 4) (F0 F1 F2 : EFrame Q) (h01 : F0.Perp F1)
    (h02 : F0.Perp F2) (h12 : F1.Perp F2) (hR : NDeg Q (lastPlane F0 F1 F2))
    (hRg : ∀ v ∈ lastPlane F0 F1 F2, g v ∈ lastPlane F0 F1 F2)
    (hRh : ∀ v ∈ lastPlane F0 F1 F2, h v ∈ lastPlane F0 F1 F2)
    (hM'dim : finrank K ↥(F0.orthSub ⊓ F1.orthSub) = 4)
    (hRdim : finrank K ↥(lastPlane F0 F1 F2) = 2) :
    ∃ F : EFrame Q, F.b ∈ lastPlane F0 F1 F2 ∧ F.b' ∈ lastPlane F0 F1 F2 ∧ PAdapted g F ∧
      PAdapted h F := by
  by_cases hmov : lastPlane F0 F1 F2 ⊓ movSp g ≠ ⊥ ∨ lastPlane F0 F1 F2 ⊓ movSp h ≠ ⊥
  · exact exists_moved_frame h3 hg hh hg3 hh3 hgh hR hRg hRh hmov
  · push Not at hmov
    have hfg := le_fixSp_of_inf_movSp h3 hg3 hRg hmov.1
    have hfh := le_fixSp_of_inf_movSp h3 hh3 hRh hmov.2
    obtain ⟨F, hb, hb'⟩ :=
      exists_frame_last h3 hB hdim hW hWdim F0 F1 F2 h01 h02 h12 hR hM'dim hRdim
    exact ⟨F, hb, hb', Or.inl (adapted_of_mem_fixSp (hfg hb) (hfg hb')),
      Or.inl (adapted_of_mem_fixSp (hfh hb) (hfh hb'))⟩

theorem exists_E81_of_frames_pair (F : Fin 4 → EFrame Q) (hperp : ∀ i j, i ≠ j → (F i).Perp (F j))
    (h3 : (3 : K) ≠ 0) [FiniteDimensional K V] (hdim : finrank K V = 8) :
    ∃ E : Subgroup (V ≃ₗ[K] V),
      E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ ∀ x : V ≃ₗ[K] V, (∀ i, PAdapted x (F i)) → x ∈ E := by
  classical
  let ψ : ∀ i : Fin 4, Multiplicative (ZMod 3) →* (V ≃ₗ[K] V) := fun i =>
    powHom (F i).rot (F i).rot_pow_three
  have hcomm : Pairwise fun i j => ∀ x y, Commute (ψ i x) (ψ j y) := by
    intro i j hij x y
    exact Commute.pow_pow ((F i).rot_comm (hperp i j hij)) _ _
  let φ := MonoidHom.noncommPiCoprod ψ hcomm
  have hrot : ∀ (i : Fin 4) (k : ℕ), ((F i).rot ^ k) (F i).b = (F i).b → k % 3 = 0 := by
    intro i k hk
    have hk' : ((F i).rot ^ (k % 3)) (F i).b = (F i).b := by
      rwa [← pow_eq_pow_mod_three (F i).rot_pow_three]
    exact (F i).eq_zero_of_rot_pow_b h3 (Nat.mod_lt _ (by norm_num)) hk'
  have hψinj : ∀ i, Function.Injective (ψ i) := by
    intro i
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    have h : (((F i).rot) ^ (Multiplicative.toAdd n).val) (F i).b = (F i).b := by
      have := congrArg (fun f : V ≃ₗ[K] V => f (F i).b) hn
      simpa [ψ, powHom_apply] using this
    have hk := hrot i _ h
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _)] at hk
    rw [Subgroup.mem_bot, ← toAdd_eq_zero]
    exact (ZMod.val_eq_zero _).mp hk
  have hind : iSupIndep fun i => (ψ i).range := by
    intro i
    rw [Subgroup.disjoint_def]
    intro x hx hxK
    obtain ⟨n, rfl⟩ := hx
    have hstab : (⨆ (j) (_ : j ≠ i), (ψ j).range) ≤
        MulAction.stabilizer (V ≃ₗ[K] V) (F i).b := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨m, rfl⟩
      rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
      exact (F j).rot_pow_of_orth (orth_b_of_ne hperp hj) _
    have h := hstab hxK
    rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def] at h
    have hk := hrot i _ h
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _)] at hk
    change (F i).rot ^ (Multiplicative.toAdd n).val = 1
    rw [hk, pow_zero]
  have hφ : Function.Injective φ :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep ψ hind hψinj
  have hmem : ∀ i, (F i).rot ∈ φ.range := by
    intro i
    refine ⟨Pi.mulSingle i (Multiplicative.ofAdd 1), ?_⟩
    rw [MonoidHom.noncommPiCoprod_mulSingle]
    change (F i).rot ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3))).val = _
    rw [toAdd_ofAdd]
    exact pow_one _
  refine ⟨φ.range, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨n, rfl⟩
    exact rot_pow_mem_commutator h3 i _
  · obtain ⟨a', ha'⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨b', hb'⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : V ≃ₗ[K] V) * b = b * a
    rw [← ha', ← hb', ← map_mul, ← map_mul, mul_comm a' b']
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := by
      funext i
      change (a i) ^ 3 = 1
      generalize a i = m
      revert m
      decide
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_fun]
    simp
  · intro x hx
    set F' : Fin 4 → EFrame Q := fun i => if Adapted x (F i) then F i else frameSw (F i) with hF'
    have hF'perp : ∀ i j, i ≠ j → (F' i).Perp (F' j) := by
      intro i j hij
      have h0 := hperp i j hij
      simp only [hF']
      split_ifs
      · exact h0
      · exact frameSw_perp_right h0
      · exact frameSw_perp_left h0
      · exact frameSw_perp_left (frameSw_perp_right h0)
    have hxF' : ∀ i, Adapted x (F' i) := by
      intro i
      simp only [hF']
      split_ifs with hi
      · exact hi
      · exact (hx i).resolve_left hi
    have hrotF' : ∀ i, (F' i).rot ∈ φ.range := by
      intro i
      simp only [hF']
      split_ifs
      · exact hmem i
      · rw [frameSw_rot h3]
        exact φ.range.pow_mem (hmem i) 2
    obtain ⟨e, he⟩ := exists_eq_rotProd hF'perp h3 hdim x hxF'
    rw [he]
    simp only [rotProd]
    exact φ.range.mul_mem (φ.range.mul_mem (φ.range.mul_mem
      (φ.range.pow_mem (hrotF' 0) _) (φ.range.pow_mem (hrotF' 1) _)) (φ.range.pow_mem (hrotF' 2) _))
      (φ.range.pow_mem (hrotF' 3) _)

theorem exists_E81_of_pair [Finite K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg3 : ∀ v, g (g (g v)) = v) (hh3 : ∀ v, h (h (h v)) = v) (hgh : ∀ v, h (g v) = g (h v))
    (hB : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8) {W : Submodule K V}
    (hW : ∀ w ∈ W, Q w = 0) (hWdim : finrank K W = 4) :
    ∃ E : Subgroup (V ≃ₗ[K] V),
      E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ g ∈ E ∧ h ∈ E := by
  have hTop : NDeg Q (⊤ : Submodule K V) := fun v _ hv =>
    hB.1 v fun w => by rw [polarBilin_apply_apply]; exact hv w trivial
  have hTopg : ∀ v ∈ (⊤ : Submodule K V), g v ∈ (⊤ : Submodule K V) := fun _ _ => trivial
  have hToph : ∀ v ∈ (⊤ : Submodule K V), h v ∈ (⊤ : Submodule K V) := fun _ _ => trivial
  have hTopdim : finrank K (⊤ : Submodule K V) = 8 := by rw [finrank_top, hdim]
  obtain ⟨F0, -, -, hF0g, hF0h⟩ :=
    exists_padapted_frame h3 hg hh hg3 hh3 hgh hTop hTopg hToph (by omega)
  obtain ⟨hM1, hM1dim⟩ := F0.split h3 (Submodule.mem_top) (Submodule.mem_top) hTop
  have hM1g := padapted_inf_orthSub_invariant hg hF0g hTopg
  have hM1h := padapted_inf_orthSub_invariant hh hF0h hToph
  rw [top_inf_eq] at hM1 hM1dim hM1g hM1h
  obtain ⟨F1, h1b, h1b', hF1g, hF1h⟩ :=
    exists_padapted_frame h3 hg hh hg3 hh3 hgh hM1 hM1g hM1h (by omega)
  obtain ⟨hM2, hM2dim⟩ := F1.split h3 h1b h1b' hM1
  have hM2g := padapted_inf_orthSub_invariant hg hF1g hM1g
  have hM2h := padapted_inf_orthSub_invariant hh hF1h hM1h
  obtain ⟨F2, h2b, h2b', hF2g, hF2h⟩ :=
    exists_padapted_frame h3 hg hh hg3 hh3 hgh hM2 hM2g hM2h (by omega)
  obtain ⟨hM3, hM3dim⟩ := F2.split h3 h2b h2b' hM2
  have hM3g := padapted_inf_orthSub_invariant hg hF2g hM2g
  have hM3h := padapted_inf_orthSub_invariant hh hF2h hM2h
  have h01 : F0.Perp F1 := ⟨(F0.mem_orthSub).mp h1b, (F0.mem_orthSub).mp h1b'⟩
  have h02 : F0.Perp F2 :=
    ⟨(F0.mem_orthSub).mp (Submodule.mem_inf.mp h2b).1,
      (F0.mem_orthSub).mp (Submodule.mem_inf.mp h2b').1⟩
  have h12 : F1.Perp F2 :=
    ⟨(F1.mem_orthSub).mp (Submodule.mem_inf.mp h2b).2,
      (F1.mem_orthSub).mp (Submodule.mem_inf.mp h2b').2⟩
  have hlast : F0.orthSub ⊓ F1.orthSub ⊓ F2.orthSub = lastPlane F0 F1 F2 := rfl
  rw [hlast] at hM3 hM3dim hM3g hM3h
  obtain ⟨F3, h3b, h3b', hF3g, hF3h⟩ := exists_padapted_frame_last h3 hg hh hg3 hh3 hgh hB hdim
    hW hWdim F0 F1 F2 h01 h02 h12 hM3 hM3g hM3h (by omega) (by omega)
  obtain ⟨ho0, ho1, ho2⟩ := (mem_lastPlane F0 F1 F2).mp h3b
  obtain ⟨ho0', ho1', ho2'⟩ := (mem_lastPlane F0 F1 F2).mp h3b'
  have h03 : F0.Perp F3 := ⟨ho0, ho0'⟩
  have h13 : F1.Perp F3 := ⟨ho1, ho1'⟩
  have h23 : F2.Perp F3 := ⟨ho2, ho2'⟩
  let F : Fin 4 → EFrame Q := ![F0, F1, F2, F3]
  have hperp : ∀ i j, i ≠ j → (F i).Perp (F j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact h01 | exact h02 | exact h03 | exact h12 | exact h13 | exact h23
      | exact h01.symm | exact h02.symm | exact h03.symm | exact h12.symm | exact h13.symm
      | exact h23.symm
  have hadg : ∀ i, PAdapted g (F i) := by
    intro i
    fin_cases i
    · exact hF0g
    · exact hF1g
    · exact hF2g
    · exact hF3g
  have hadh : ∀ i, PAdapted h (F i) := by
    intro i
    fin_cases i
    · exact hF0h
    · exact hF1h
    · exact hF2h
    · exact hF3h
  obtain ⟨E, hEO, hE, hcard, hmemE⟩ := exists_E81_of_frames_pair F hperp h3 hdim
  exact ⟨E, hEO, hE, hcard, hmemE g hadg, hmemE h hadh⟩

end PairE81

section D44Model

open Module Matrix CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv statedOmega_eq_comap)
open CFSG.HardMathSupport.Solomon.Coordinator (lbid4_totallySingular lbid4_lift lbid4_scalar_sq
  lbid4_three_ne_zero)

theorem exists_E81_of_pair_statedOmega (K : Type) [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    {g h : GL (Fin 4 ⊕ Fin 4) K} (hg : g ∈ StatedOmega (StatedQuadPlus 4 K))
    (hh : h ∈ StatedOmega (StatedQuadPlus 4 K)) (hg3 : g ^ 3 = 1) (hh3 : h ^ 3 = 1)
    (hgh : g * h = h * g) :
    ∃ E : Subgroup (GL (Fin 4 ⊕ Fin 4) K), E ≤ StatedOmega (StatedQuadPlus 4 K) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ g ∈ E ∧ h ∈ E := by
  have hQ : ⇑(quadPlus 4 K) = StatedQuadPlus 4 K := by
    funext v
    rw [quadPlus_apply]
    rfl
  have hΩ : StatedOmega (StatedQuadPlus 4 K) =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆.comap
          (toLinEquiv (Fin 4 ⊕ Fin 4) K).toMonoidHom :=
    statedOmega_eq_comap hQ
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hmemO : ∀ x : GL (Fin 4 ⊕ Fin 4) K, x ∈ StatedOmega (StatedQuadPlus 4 K) →
      toLinEquiv (Fin 4 ⊕ Fin 4) K x ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := by
    intro x hx
    rw [hΩ] at hx
    exact hle hx
  have hcube : ∀ x : GL (Fin 4 ⊕ Fin 4) K, x ^ 3 = 1 → ∀ v, toLinEquiv (Fin 4 ⊕ Fin 4) K x
      (toLinEquiv (Fin 4 ⊕ Fin 4) K x (toLinEquiv (Fin 4 ⊕ Fin 4) K x v)) = v := by
    intro x hx v
    have h := congrArg (fun f : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) => f v)
      (show toLinEquiv (Fin 4 ⊕ Fin 4) K x ^ 3 = 1 by rw [← map_pow, hx, map_one])
    simpa [pow_three] using h
  have hcomm : ∀ v, toLinEquiv (Fin 4 ⊕ Fin 4) K h (toLinEquiv (Fin 4 ⊕ Fin 4) K g v) =
      toLinEquiv (Fin 4 ⊕ Fin 4) K g (toLinEquiv (Fin 4 ⊕ Fin 4) K h v) := by
    intro v
    have e := congrArg (fun f : GL (Fin 4 ⊕ Fin 4) K => toLinEquiv (Fin 4 ⊕ Fin 4) K f v) hgh
    simp only [map_mul, LinearEquiv.mul_apply] at e
    exact e.symm
  have hdim : finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    rfl
  obtain ⟨hW, hWdim⟩ := lbid4_totallySingular K
  obtain ⟨E, hEO, hE, hcard, hgE, hhE⟩ := exists_E81_of_pair h3 (hmemO g hg) (hmemO h hh)
    (hcube g hg3) (hcube h hh3) hcomm (nondegenerate_polarBilin_quadPlus 4 K) hdim hW hWdim
  refine ⟨E.map (toLinEquiv (Fin 4 ⊕ Fin 4) K).symm.toMonoidHom, ?_, ?_, ?_, ⟨_, hgE, by simp⟩,
    ⟨_, hhE, by simp⟩⟩
  · rw [hΩ]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_comap]
    simpa using hEO hx
  · refine ⟨?_, ?_⟩
    · have := hE.1
      infer_instance
    · rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hE.2 y hy, map_one]
  · rw [Subgroup.card_map_of_injective (toLinEquiv (Fin 4 ⊕ Fin 4) K).symm.injective, hcard]

theorem exists_E81_of_E9_statedProj (K : Type) [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) :
    ∃ F : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K))), E ≤ F ∧ IsElemAbelian 3 F ∧
      Nat.card F = 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.comm_of_isElemAbelian hE
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
    rw [hbot, Subgroup.card_bot] at hEc
    norm_num at hEc
  have hx3 : x ^ 3 = 1 := hE.2 x hxE
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨y, hyE, hyx⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers x from hcon)
    rw [Nat.card_zpowers, hxo, hEc] at hle
    norm_num at hle
  have hy3 : y ^ 3 = 1 := hE.2 y hyE
  have hy1 : y ≠ 1 := fun h1 => hyx (h1 ▸ Subgroup.one_mem _)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  obtain ⟨g, hg3, hgx⟩ := lbid4_lift x hx3
  obtain ⟨h, hh3, hhy⟩ := lbid4_lift y hy3
  have hG3 : (g : GL (Fin 4 ⊕ Fin 4) K) ^ 3 = 1 := by
    rw [← SubgroupClass.coe_pow, hg3, OneMemClass.coe_one]
  have hH3 : (h : GL (Fin 4 ⊕ Fin 4) K) ^ 3 = 1 := by
    rw [← SubgroupClass.coe_pow, hh3, OneMemClass.coe_one]
  have hcommGL : (g : GL (Fin 4 ⊕ Fin 4) K) * h = h * g := by
    set z : ↥(StatedOmega (StatedQuadPlus 4 K)) := g * h * g⁻¹ * h⁻¹ with hzdef
    have hzZ : z ∈ (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedOmega (StatedQuadPlus 4 K)) := by
      rw [← QuotientGroup.eq_one_iff, hzdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hgx, hhy,
        hEcomm x hxE y hyE]
      group
    have hzs : (z : GL (Fin 4 ⊕ Fin 4) K) ∈ StatedScalars (Fin 4 ⊕ Fin 4) K :=
      Subgroup.mem_subgroupOf.1 hzZ
    have hz2 : (z : GL (Fin 4 ⊕ Fin 4) K) ^ 2 = 1 := lbid4_scalar_sq z.2 hzs
    have hzc : (z : GL (Fin 4 ⊕ Fin 4) K) ∈ Subgroup.center (GL (Fin 4 ⊕ Fin 4) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hzs
    have hZ' : (z : GL (Fin 4 ⊕ Fin 4) K) =
        (g : GL (Fin 4 ⊕ Fin 4) K) * h * (g : GL (Fin 4 ⊕ Fin 4) K)⁻¹ * (h : GL (Fin 4 ⊕ Fin 4) K)⁻¹ := by
      rw [hzdef]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have e1 : (g : GL (Fin 4 ⊕ Fin 4) K) * h * (g : GL (Fin 4 ⊕ Fin 4) K)⁻¹ =
        (z : GL (Fin 4 ⊕ Fin 4) K) * h := by
      rw [hZ']
      group
    have hgz : Commute (g : GL (Fin 4 ⊕ Fin 4) K) (z : GL (Fin 4 ⊕ Fin 4) K) :=
      (Subgroup.mem_center_iff.1 hzc (g : GL (Fin 4 ⊕ Fin 4) K))
    have e2 : ∀ n : ℕ, (g : GL (Fin 4 ⊕ Fin 4) K) ^ n * h * ((g : GL (Fin 4 ⊕ Fin 4) K) ^ n)⁻¹ =
        (z : GL (Fin 4 ⊕ Fin 4) K) ^ n * h := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (g : GL (Fin 4 ⊕ Fin 4) K) ^ (n + 1) * h * ((g : GL (Fin 4 ⊕ Fin 4) K) ^ (n + 1))⁻¹
            = (g : GL (Fin 4 ⊕ Fin 4) K) * ((g : GL (Fin 4 ⊕ Fin 4) K) ^ n * h *
              ((g : GL (Fin 4 ⊕ Fin 4) K) ^ n)⁻¹) * (g : GL (Fin 4 ⊕ Fin 4) K)⁻¹ := by group
          _ = (g : GL (Fin 4 ⊕ Fin 4) K) * ((z : GL (Fin 4 ⊕ Fin 4) K) ^ n * h) *
              (g : GL (Fin 4 ⊕ Fin 4) K)⁻¹ := by rw [ih]
          _ = (z : GL (Fin 4 ⊕ Fin 4) K) ^ n * ((g : GL (Fin 4 ⊕ Fin 4) K) * h *
              (g : GL (Fin 4 ⊕ Fin 4) K)⁻¹) := by
            rw [← mul_assoc, (hgz.pow_right n).eq]
            group
          _ = (z : GL (Fin 4 ⊕ Fin 4) K) ^ (n + 1) * h := by
            rw [e1]
            group
    have hz3 : (z : GL (Fin 4 ⊕ Fin 4) K) ^ 3 = 1 := by
      have e3 := e2 3
      rw [hG3, one_mul, inv_one, mul_one] at e3
      have e4 := congrArg (· * (h : GL (Fin 4 ⊕ Fin 4) K)⁻¹) e3
      simp only [mul_inv_cancel, mul_assoc, mul_one] at e4
      exact e4.symm
    have hz1 : (z : GL (Fin 4 ⊕ Fin 4) K) = 1 := by
      calc (z : GL (Fin 4 ⊕ Fin 4) K) = (z : GL (Fin 4 ⊕ Fin 4) K) ^ 3 *
          ((z : GL (Fin 4 ⊕ Fin 4) K) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hz3, hz2, inv_one, mul_one]
    rw [hZ'] at hz1
    calc (g : GL (Fin 4 ⊕ Fin 4) K) * h = ((g : GL (Fin 4 ⊕ Fin 4) K) * h *
        (g : GL (Fin 4 ⊕ Fin 4) K)⁻¹ * (h : GL (Fin 4 ⊕ Fin 4) K)⁻¹) * (h * g) := by group
      _ = h * g := by rw [hz1, one_mul]
  obtain ⟨E81, hE81Ω, hE81el, hE81c, hgE, hhE⟩ :=
    exists_E81_of_pair_statedOmega K h3 g.2 h.2 hG3 hH3 hcommGL
  have hZ3 : ¬ 3 ∣ Nat.card ((StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf
      (StatedOmega (StatedQuadPlus 4 K))) := by
    intro hdvd
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    have hw2 : (((w : ↥(StatedOmega (StatedQuadPlus 4 K))) : GL (Fin 4 ⊕ Fin 4) K)) ^ 2 = 1 :=
      lbid4_scalar_sq (w : ↥(StatedOmega (StatedQuadPlus 4 K))).2 (Subgroup.mem_subgroupOf.1 w.2)
    have hw2' : w ^ 2 = 1 := Subtype.ext (Subtype.ext (by simpa using hw2))
    have hdvd2 := orderOf_dvd_of_pow_eq_one hw2'
    rw [hw] at hdvd2
    norm_num at hdvd2
  set A := (E81.subgroupOf (StatedOmega (StatedQuadPlus 4 K))).map (QuotientGroup.mk'
    ((StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedOmega (StatedQuadPlus 4 K)))) with hA
  have hAel : IsElemAbelian 3 A := (hE81el.subgroupOf _).map _
  have hAc : Nat.card A = 3 ^ 4 := by
    rw [hA, Inputs1114.card_map_mk_of_isPGroup hZ3 (hE81el.subgroupOf _).isPGroup,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE81Ω).toEquiv, hE81c]
  have hxA : x ∈ A := ⟨g, Subgroup.mem_subgroupOf.2 hgE, hgx⟩
  have hyA : y ∈ A := ⟨h, Subgroup.mem_subgroupOf.2 hhE, hhy⟩
  have hxy : Subgroup.zpowers x ⊔ Subgroup.zpowers y = E := by
    have hc : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := fun a ha b hb =>
      hEcomm a (Subgroup.zpowers_le.2 hxE ha) b (Subgroup.zpowers_le.2 hyE hb)
    refine Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.2 hxE) (Subgroup.zpowers_le.2 hyE)) ?_
    rw [GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hc (GL83.CompFam.inf_zpowers_eq_bot hyo hyx),
      Nat.card_zpowers, Nat.card_zpowers, hxo, hyo, hEc]
    norm_num
  refine ⟨A, ?_, hAel, hAc⟩
  rw [← hxy]
  exact sup_le (Subgroup.zpowers_le.2 hxA) (Subgroup.zpowers_le.2 hyA)

theorem input10_2D44_holds : Claims1115b.Input10_2D44 := by
  intro Y _ _ hD E hE hEc
  obtain ⟨⟨x₀, hv⟩, hd, ⟨e⟩⟩ := hD
  obtain ⟨q, rfl, hq2, hqe⟩ : ∃ q : TauCeti.PrimePower,
      x₀ = TauCeti.LieTypeIndex.D 4 q ∧ q.p = 2 ∧ q.exponent = 2 := by
    cases x₀ <;> first | exact ⟨_, by rw [hd.1], hd.2.1, hd.2.2⟩ | exact hd.elim
  have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hKc : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩) =
      2 ^ 2 := by
    rw [CFSG.LieType.SeitzGeneration.card_fixedField_eq]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent, hq2,
      hqe]
  have h3 := lbid4_three_ne_zero Nat.prime_two (by norm_num) hKc
  let θ := e.trans
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv)
  obtain ⟨F, hEF, hFel, hFc⟩ := exists_E81_of_E9_statedProj _ h3 (E.map θ.toMonoidHom) (hE.map _)
    (by rw [Subgroup.card_map_of_injective θ.injective, hEc])
  refine ⟨F.map θ.symm.toMonoidHom, ?_, hFel.map _, ?_⟩
  · intro z hz
    exact ⟨θ z, hEF ⟨z, hz, rfl⟩, by simp⟩
  · rw [Subgroup.card_map_of_injective θ.symm.injective, hFc]

end D44Model

section Discharged

theorem input1115Gamma_of_leaves
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h1111 : Lemma1111Statement) (h119 : Lemma119Statement) (h1112 : Lemma1112Statement)
    (h104v : Lemma104_vStatement) (h111 : Prop111Statement)
    (hup34 : CFSG.HardMathSupport.Dickson.Sec6.Up34Statement) : Lemma1115.Input1115Gamma :=
  Claims1115b.input1115Gamma_of_inputs hS h1111 h119 h1112 h104v h111 hup34
    CFSG.HardMathSupport.Dickson.Sec6.gen3D4_holds seitz2310D44Inner_holds input10_2D44_holds

end Discharged

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115c

end
