module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm12
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Cor15
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_eq_bot_of_fStar (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) : pPrimeCore 2 G = ⊥ := by
  set F := GeneralizedFitting.subgroup G with hF
  have hFn : F.Normal := GeneralizedFitting.normal G
  set O := pPrimeCore 2 G with hO
  have hFO : F ⊓ O = ⊥ := by
    have hn : (O.subgroupOf F).Normal := Subgroup.normal_subgroupOf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.subgroupOf F) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.1⟩ : F) ∈ O.subgroupOf F := mem_subgroupOf.mpr hx.2
      rw [h, mem_bot] at hx'
      exact mem_bot.mpr (congrArg Subtype.val hx')
    · exfalso
      have hFO' : F ≤ O := fun x hx => by
        have : (⟨x, hx⟩ : F) ∈ O.subgroupOf F := by rw [h]; trivial
        exact mem_subgroupOf.mp this
      have hOodd : Odd (Nat.card O) :=
        Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))
      have hodd : Odd (Nat.card F) := hOodd.of_dvd_nat (Subgroup.card_dvd_of_le hFO')
      have hsol : Group.IsSolvable F := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      obtain ⟨a, b, hab⟩ := hnF
      exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsol a b)
  have hOC : O ≤ centralizer (F : Set G) := by
    intro o ho
    rw [mem_centralizer_iff]
    intro f hf
    have hOn : O.Normal := inferInstance
    have h1 : f * o * f⁻¹ * o⁻¹ ∈ F ⊓ O := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [show f * o * f⁻¹ * o⁻¹ = f * (o * f⁻¹ * o⁻¹) by group]
        exact mul_mem hf (hFn.conj_mem _ (inv_mem hf) o)
      · exact mul_mem (hOn.conj_mem _ ho f) (inv_mem ho)
    rw [hFO, mem_bot] at h1
    calc f * o = f * o * f⁻¹ * o⁻¹ * (o * f) := by group
      _ = o * f := by rw [h1, one_mul]
  have hOF : O ≤ F :=
    hOC.trans ((GeneralizedFitting.centralizer_le_fitting G).trans le_sup_left)
  exact le_bot_iff.mp (hFO ▸ le_inf hOF le_rfl)

omit [Finite G] in
theorem center_eq_bot_of_simple_nonab {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (h : ∃ a b : Q, a * b ≠ b * a) : center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with hc | hc
  · exact hc
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hb : b ∈ center Q := by rw [hc]; exact mem_top b
    exact hab (mem_center_iff.mp hb a)

omit [Finite G] in
theorem open_isSubnormal_top {H : Subgroup G} (h : H.IsSubnormal) :
    CFSG.Open.IsSubnormal H ⊤ :=
  CFSG.Open.IsSubnormal.of_mathlib h

theorem solomonKStarOf_top_eq_bot_of_fStar (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) :
    solomonKStarOf (⊤ : Subgroup G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GeneralizedFitting.subgroup G with hF
  have hO := pPrimeCore_eq_bot_of_fStar hsF hnF
  have hZF : center F = ⊥ := center_eq_bot_of_simple_nonab hnF
  apply le_antisymm _ bot_le
  refine iSup₂_le fun K hK => ?_
  exfalso
  obtain ⟨hK2, ⟨⟨-, T, hT, -, hTC, -⟩, -⟩, -⟩ := hK
  have hKp : IsPComponent 2 K := isPComponent_subgroupOf_top_iff'.mp hK2.2
  obtain ⟨hsub, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 K).mp hKp
  have hOK : pPrimeCore 2 ↥K = ⊥ := by
    have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hsub
    rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h1
    exact h1
  have hKq : IsQuasisimple ↥K := LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hOK).trans QuotientGroup.quotientBot) hq
  have hKcomp : CFSG.Open.IsComponentOf K ⊤ :=
    ⟨le_top, open_isSubnormal_top hsub, Group.isPerfect_def.mp hKq.1, hKq.2.1⟩
  have hKF : K ≤ F := (Layer.component_le hKcomp).trans le_sup_right
  have hFq : IsQuasisimple ↥F := (LocalCores.isQuasisimple_of_isSimpleGroup hnF).1
  have hKne : K ≠ ⊥ := Sol78.ne_bot_of_isPComponent' hKp
  have hKeq : K = F := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hFq
        (hsub.subgroupOf (K := F)) with h | h
    · refine le_antisymm hKF fun x hx => ?_
      have : (⟨x, hx⟩ : F) ∈ K.subgroupOf F := by rw [h]; trivial
      exact mem_subgroupOf.mp this
    · exfalso
      rw [hZF, le_bot_iff] at h
      apply hKne
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hKF hx⟩ : F) ∈ K.subgroupOf F := mem_subgroupOf.mpr hx
      rw [h, mem_bot] at this
      exact mem_bot.mpr (congrArg Subtype.val this)
  apply hT
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨-, hxK⟩ := hTC hx
  have hxc : x ∈ centralizer (F : Set G) := by
    rw [mem_centralizer_iff]
    intro f hf
    have h1 := hxK f (hKeq ▸ hf)
    rw [hOK, Subgroup.map_bot, mem_bot] at h1
    calc f * x = x * (f * (f⁻¹ * x⁻¹ * f * x)) := by group
      _ = x * f := by rw [h1, mul_one]
  have hxF : x ∈ F :=
    ((GeneralizedFitting.centralizer_le_fitting G).trans le_sup_left) hxc
  have hxZ : (⟨x, hxF⟩ : F) ∈ center F := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.mp hxc) g g.2)
  rw [hZF, mem_bot] at hxZ
  exact mem_bot.mpr (congrArg Subtype.val hxZ)

omit [Finite G] in
theorem eq_top_of_sup_center_eq_top' {Q : Type*} [Group Q] (hQ : commutator Q = ⊤)
    {H : Subgroup Q} (h : H ⊔ center Q = ⊤) : H = ⊤ := by
  rw [eq_top_iff, ← hQ, commutator_eq_closure, closure_le]
  rintro _ ⟨a, b, rfl⟩
  have ha : a ∈ H ⊔ center Q := by rw [h]; trivial
  have hb : b ∈ H ⊔ center Q := by rw [h]; trivial
  obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
  obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
  have hc₁ := mem_center_iff.mp hz₁
  have hc₂ := mem_center_iff.mp hz₂
  have e : ⁅h₁ * z₁, h₂ * z₂⁆ = ⁅h₁, h₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc h₁ * z₁ * (h₂ * z₂) * (h₁ * z₁)⁻¹ * (h₂ * z₂)⁻¹
        = h₁ * (z₁ * h₂) * z₂ * z₁⁻¹ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by group
      _ = h₁ * (h₂ * z₁) * z₂ * z₁⁻¹ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by rw [hc₁ h₂]
      _ = h₁ * h₂ * (z₁ * z₂ * z₁⁻¹) * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by group
      _ = h₁ * h₂ * z₂ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by
          rw [show z₁ * z₂ * z₁⁻¹ = z₂ by rw [hc₂ z₁]; group]
      _ = h₁ * h₂ * (z₂ * h₁⁻¹) * z₂⁻¹ * h₂⁻¹ := by group
      _ = h₁ * h₂ * (h₁⁻¹ * z₂) * z₂⁻¹ * h₂⁻¹ := by rw [hc₂ h₁⁻¹]
      _ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ := by group
  rw [SetLike.mem_coe, e, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hh₁ hh₂) (inv_mem hh₁)) (inv_mem hh₂)

theorem sup_oddCoreIn_eq_of_fusionZStar {J M CJ CM : Subgroup G} (hJ : IsTwoComponentIn J CJ)
    (hM : IsTwoComponentIn M CM) (hJM : J ≤ M) (hJinv : ∃ b ∈ J, orderOf b = 2)
    (e : ↥M ⧸ Open.fusionZStar ↥M ≃* ↥J ⧸ Open.fusionZStar ↥J) : J ⊔ oddCoreIn M = M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hJres, hJq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J CJ hJ.1).mp hJ.2
  have hJperf : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJ.1 hJ.2
  have hMperf : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hM.1 hM.2
  set Z := Open.fusionZStar ↥M with hZ
  set ι : ↥J →* ↥M := Subgroup.inclusion hJM with hι
  set π₀ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ₀
  have hZcomap : Z = (center (↥M ⧸ pPrimeCore 2 ↥M)).comap π₀ := Sol78.fusionZStar_eq_comap _
  set N₀ : Subgroup ↥J := Z.comap ι with hN₀
  have hN₀n : N₀.Normal := Subgroup.Normal.comap inferInstance ι
  set π₁ := QuotientGroup.mk' (pPrimeCore 2 ↥J) with hπ₁
  have hN₀' : (N₀.map π₁).Normal := hN₀n.map π₁ (QuotientGroup.mk'_surjective _)
  have hN₀Z : N₀ ≤ Open.fusionZStar ↥J := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hJq hN₀'.isSubnormal with
      htop | hcen
    · exfalso
      have hmem : ∀ x : ↥J, (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ N₀ := by
        rintro x ⟨k, hk⟩
        have hx : π₁ x ∈ N₀.map π₁ := by rw [htop]; trivial
        obtain ⟨d, hd, hdx⟩ := hx
        have h1 : d⁻¹ * x ∈ pPrimeCore 2 ↥J := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          change (π₁ d)⁻¹ * π₁ x = 1
          rw [hdx, inv_mul_cancel]
        have hsup : x ∈ pPrimeCore 2 ↥J ⊔ N₀ := by
          rw [show x = d * (d⁻¹ * x) by group]
          exact mul_mem (mem_sup_right hd) (mem_sup_left h1)
        exact mem_of_sup_odd (H := N₀) (pPrimeCore_coprime_card (p := 2) (G := ↥J)) hsup
          (k := k) (by rw [← hk, pow_orderOf_eq_one])
      have hN₀top : N₀ = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hxT : x ∈ CatalogueBPrimeJoin.primeResidual 2 J := by rw [hJres]; trivial
        rw [CatalogueBPrimeJoin.primeResidual_eq_closure] at hxT
        exact (closure_le _).mpr (fun y hy => hmem y hy) hxT
      have hJO : J ≤ oddCoreIn M := by
        rw [← hJperf]
        refine commutator_le.mpr fun a ha b hb => ?_
        have hza : π₀ (ι ⟨a, ha⟩) ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
          have : ι ⟨a, ha⟩ ∈ Z := (show (⟨a, ha⟩ : ↥J) ∈ N₀ by rw [hN₀top]; trivial)
          rw [hZcomap] at this
          exact this
        have hc : π₀ ⁅ι ⟨a, ha⟩, ι ⟨b, hb⟩⁆ = 1 := by
          rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          exact ((mem_center_iff.mp hza) (π₀ (ι ⟨b, hb⟩))).symm
        rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
        exact ⟨_, hc, rfl⟩
      obtain ⟨b, hbJ, hb2⟩ := hJinv
      have h1 := orderOf_dvd_natCard (⟨b, hJO hbJ⟩ : oddCoreIn M)
      rw [Subgroup.orderOf_mk, hb2] at h1
      exact absurd (Nat.Coprime.eq_one_of_dvd (coprime_card_oddCoreIn M) h1) (by norm_num)
    · rw [Sol78.fusionZStar_eq_comap]
      intro x hx
      exact hcen (mem_map_of_mem π₁ hx)
  set ψ : ↥J →* ↥M ⧸ Z := (QuotientGroup.mk' Z).comp ι with hψ
  have hker : ψ.ker = N₀ := by
    ext x
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hN₀, mem_comap]
  have h1 := Subgroup.card_ker_mul_card_range ψ
  rw [hker] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.fusionZStar ↥J)
  have h3 : Nat.card N₀ ≤ Nat.card (Open.fusionZStar ↥J) := Subgroup.card_le_of_le hN₀Z
  have h4 : Nat.card (↥M ⧸ Z) = Nat.card (↥J ⧸ Open.fusionZStar ↥J) := Nat.card_congr e.toEquiv
  have hpos : 0 < Nat.card (Open.fusionZStar ↥J) := Nat.card_pos
  have h5 : Nat.card (↥M ⧸ Z) ≤ Nat.card ψ.range := by
    have h6 : Nat.card (↥M ⧸ Z) * Nat.card (Open.fusionZStar ↥J) ≤
        Nat.card ψ.range * Nat.card (Open.fusionZStar ↥J) := by
      calc Nat.card (↥M ⧸ Z) * Nat.card (Open.fusionZStar ↥J) = Nat.card ↥J := by
            rw [h4, ← h2]
        _ = Nat.card N₀ * Nat.card ψ.range := h1.symm
        _ ≤ Nat.card (Open.fusionZStar ↥J) * Nat.card ψ.range := Nat.mul_le_mul_right _ h3
        _ = Nat.card ψ.range * Nat.card (Open.fusionZStar ↥J) := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right h6 hpos
  have hrange : ψ.range = ⊤ := Subgroup.eq_top_of_le_card _ h5
  set H : Subgroup (↥M ⧸ pPrimeCore 2 ↥M) := ι.range.map π₀ with hH
  have hHZ : H ⊔ center (↥M ⧸ pPrimeCore 2 ↥M) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) y
    have hm : (QuotientGroup.mk' Z m) ∈ ψ.range := by rw [hrange]; trivial
    obtain ⟨j, hj⟩ := hm
    have hz : (ι j)⁻¹ * m ∈ Z := by
      rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at hj
      exact hj
    rw [hZcomap, mem_comap] at hz
    rw [show m = ι j * ((ι j)⁻¹ * m) by group, map_mul]
    exact mul_mem (mem_sup_left ⟨ι j, ⟨j, rfl⟩, rfl⟩) (mem_sup_right hz)
  have hMp : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr hMperf
  have hHtop : H = ⊤ := eq_top_of_sup_center_eq_top'
    (Group.isPerfect_def.mp inferInstance) hHZ
  refine le_antisymm (sup_le hJM (map_subtype_le _)) fun m hm => ?_
  have hm' : π₀ ⟨m, hm⟩ ∈ H := by rw [hHtop]; trivial
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hm'
  have ho : (ι j)⁻¹ * ⟨m, hm⟩ ∈ pPrimeCore 2 ↥M := by
    rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hj
    exact hj
  have hmeq : m = (j : G) * (((ι j)⁻¹ * ⟨m, hm⟩ : ↥M) : G) := by
    simp [hι]
  rw [hmeq]
  exact mul_mem (mem_sup_left j.2) (mem_sup_right ⟨_, ho, rfl⟩)

theorem eq_of_isQuasisimple_solomonLStarOf {N K₁ K₂ : Subgroup G}
    (hq : IsQuasisimple (solomonLStarOf N ⧸ pPrimeCore 2 (solomonLStarOf N)))
    (h₁ : IsTwoComponentIn K₁ N ∧ IsSolomonMaximal K₁)
    (h₂ : IsTwoComponentIn K₂ N ∧ IsSolomonMaximal K₂) : K₁ = K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := solomonLStarOf N with hD
  have hDN : D ≤ N := iSup₂_le fun K hK => hK.1.1
  have hK₁D : K₁ ≤ D := le_iSup₂_of_le K₁ h₁ le_rfl
  have hK₂D : K₂ ≤ D := le_iSup₂_of_le K₂ h₂ le_rfl
  have hc₁ := isTwoComponentIn_of_le h₁.1 hK₁D hDN
  have hc₂ := isTwoComponentIn_of_le h₂.1 hK₂D hDN
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥D) with hπ
  have himage : ∀ {K : Subgroup G}, IsTwoComponentIn K D → (K.subgroupOf D).map π = ⊤ := by
    intro K hK
    have hsub : ((K.subgroupOf D).map π).IsSubnormal := by
      obtain ⟨h, -, -⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K D hK.1).mp hK.2
      exact h.map (QuotientGroup.mk'_surjective _)
    have hKq := isQuasisimple_image hK (pPrimeCore 2 ↥D) rfl
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq hsub with h | h
    · exact h
    · exfalso
      have hcen : ∀ y : ↥((K.subgroupOf D).map π), y ∈ center ↥((K.subgroupOf D).map π) :=
        fun y => mem_center_iff.mpr fun x => Subtype.ext ((mem_center_iff.mp (h y.2)) x)
      obtain ⟨a, b, hab⟩ := hKq.2.1.exists_pair_ne
      apply hab
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact QuotientGroup.eq.mpr (hcen _)
  have heq : K₁.subgroupOf D = K₂.subgroupOf D :=
    UnbalancedLayer.pComponent_eq_of_map_eq hc₁.2 hc₂.2 (by rw [himage hc₁, himage hc₂])
  have h := Subgroup.subgroupOf_inj.mp heq
  rwa [inf_eq_left.mpr hK₁D, inf_eq_left.mpr hK₂D] at h

omit [Finite G] in
theorem isSolomonMaximal_of_solomonEquiv {L K : Subgroup G} (hL : IsSolomonMaximal L)
    (h : SolomonEquiv L K) : IsSolomonMaximal K := by
  have hK := isSolomonMember_of_reflTransGen h.1 h.2
  have hKL := reflTransGen_solomonLink_symm h.2
  exact ⟨hK, fun K' K₁ hK' hlt => ⟨hK, hKL.trans (hL.2 K' K₁ ⟨hL.1, h.2.trans hK'.2⟩ hlt).2⟩⟩

theorem mem_solomonKStar_of_aschbacher (hA : AschbacherRankOneInput)
    (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hoF : ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G)) {J : Subgroup G}
    (hJ : IsSolomonMaximal J) : J ∈ solomonKStar G := by
  refine ⟨hJ, hJ.1, fun K hK => ?_⟩
  by_contra h
  rw [not_le] at h
  exact hoF (hA G hsF hnF K (isSolomonMaximal_of_solomonEquiv hJ hK) (by omega))

theorem solomonEquiv_of_not_le_coreActionKernel {t : G} (ht : orderOf t = 2)
    {J CJ M : Subgroup G} (hJ : IsTwoComponentIn J CJ) (hJmax : IsSolomonMaximal J)
    (hJt : J ≤ centralizer ({t} : Set G)) (hJL : J ≤ twoLayerIn (centralizer ({t} : Set G)))
    (hM : IsTwoComponentIn M (centralizer ({t} : Set G))) (hJM : ¬ J ≤ coreActionKernel M) :
    SolomonEquiv J M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set G) with hC
  set T := zpowers t with hT
  have hCT : centralizer ((T : Subgroup G) : Set G) = C := by
    rw [hT, zpowers_eq_closure, centralizer_closure]
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hTJ : T ≤ coreActionKernel J := by
    rw [hT, zpowers_le]
    exact Sol78.mem_coreActionKernel_of_commute fun j hj =>
      mem_centralizer_singleton_iff.mp (hJt hj)
  have hKP := isTwoComponentIn_conjClosure_of_not_le hM hJL hJM
  have hlt : SolomonLt J M := by
    refine ⟨hJmax.1, isSolomonMember_of_isTwoComponentIn_centralizer ht hM, T, hT2, hTJ, ?_⟩
    rwa [hCT, inf_eq_left.mpr hJt, twoLayerIn_eq_self_of_isTwoComponentIn hJ]
  exact hJmax.2 J M ⟨hJmax.1, Relation.ReflTransGen.refl⟩ hlt

omit [Finite G] in
theorem mk_mul_comm_iff {N : Subgroup G} (x y : ↥N) :
    QuotientGroup.mk' (pPrimeCore 2 ↥N) x * QuotientGroup.mk' (pPrimeCore 2 ↥N) y =
        QuotientGroup.mk' (pPrimeCore 2 ↥N) y * QuotientGroup.mk' (pPrimeCore 2 ↥N) x ↔
      (x : G)⁻¹ * (y : G)⁻¹ * x * y ∈ oddCoreIn N := by
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm,
    QuotientGroup.eq]
  have e : (y * x)⁻¹ * (x * y) = x⁻¹ * y⁻¹ * x * y := by group
  rw [e]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨z, hz, hze⟩
    have : z = x⁻¹ * y⁻¹ * x * y := Subtype.ext (by simpa using hze)
    rwa [← this]

theorem exists_not_le_coreActionKernel {N J CJ : Subgroup G} (hJ : IsTwoComponentIn J CJ)
    (hJN : J ≤ solomonKStarOf N) (hJinv : ∃ b ∈ J, orderOf b = 2) :
    ∃ M : Subgroup G, (IsTwoComponentIn M N ∧ M ∈ solomonKStar G) ∧
      ¬ J ≤ coreActionKernel M := by
  by_contra hcon
  push Not at hcon
  have hperf : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJ.1 hJ.2
  have hKN : solomonKStarOf N ≤ N := iSup₂_le fun K hK => hK.1.1
  have hJN' : J ≤ N := hJN.trans hKN
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥N) with hπ
  set Jbar := (J.subgroupOf N).map π with hJbar
  set Cen : Subgroup G := ((centralizer (Jbar : Set (↥N ⧸ pPrimeCore 2 ↥N))).comap π).map
    N.subtype with hCen
  have hMC : ∀ M : Subgroup G, IsTwoComponentIn M N ∧ M ∈ solomonKStar G → M ≤ Cen := by
    intro M hM m hm
    refine ⟨⟨m, hM.1.1 hm⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap, mem_centralizer_iff]
    rintro _ ⟨⟨j, hjN⟩, hj, rfl⟩
    have h1 := (hcon M hM (mem_subgroupOf.mp hj)).2 m hm
    have h2 : m⁻¹ * j⁻¹ * m * j ∈ oddCoreIn N := oddCoreIn_le_of_isTwoComponentIn hM.1 h1
    exact ((mk_mul_comm_iff (N := N) ⟨m, hM.1.1 hm⟩ ⟨j, hjN⟩).mpr h2).symm
  have hJC : J ≤ Cen := hJN.trans (iSup₂_le fun M hM => hMC M hM)
  have hJO : J ≤ oddCoreIn N := by
    rw [← hperf]
    refine commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨y, hy, hye⟩ := hJC (inv_mem hb)
    have hyb : y = ⟨b⁻¹, hJN' (inv_mem hb)⟩ := Subtype.ext hye
    rw [hyb, SetLike.mem_coe, mem_comap, mem_centralizer_iff] at hy
    have hab := hy (π ⟨a⁻¹, hJN' (inv_mem ha)⟩)
      ⟨⟨a⁻¹, hJN' (inv_mem ha)⟩, mem_subgroupOf.mpr (inv_mem ha), rfl⟩
    have h1 := (mk_mul_comm_iff (N := N) ⟨a⁻¹, hJN' (inv_mem ha)⟩
      ⟨b⁻¹, hJN' (inv_mem hb)⟩).mp hab
    simp only [inv_inv] at h1
    rw [commutatorElement_def]
    exact h1
  obtain ⟨b, hbJ, hb2⟩ := hJinv
  have h1 := orderOf_dvd_natCard (⟨b, hJO hbJ⟩ : oddCoreIn N)
  rw [Subgroup.orderOf_mk, hb2] at h1
  exact absurd (Nat.Coprime.eq_one_of_dvd (coprime_card_oddCoreIn N) h1) (by norm_num)

omit [Finite G] in
theorem nonempty_fusionZStar_equiv_statedProj {K : Type*} [Group K] {F : Type} [Field F]
    (e : K ⧸ pPrimeCore 2 K ≃* Assembly.LowTwoRank.StatedSp 2 F) :
    Nonempty (K ⧸ Open.fusionZStar K ≃*
      Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 F)) :=
  ⟨((Sol78.coreQuotientCenterEquiv K).symm.trans (Sol78.centerQuotCongr e)).trans
    (QuotientGroup.quotientMulEquivOfEq (CFSG.LieType.Universal.Symplectic.center_eq 2 F))⟩

omit [Finite G] in
theorem not_le_coreActionKernel_of_le [Finite G] {J M : Subgroup G} (hJM : J ≤ M)
    (hperf : ⁅J, J⁆ = J) (hJinv : ∃ b ∈ J, orderOf b = 2) : ¬ J ≤ coreActionKernel M := by
  intro h
  have hJO : J ≤ oddCoreIn M := by
    rw [← hperf]
    refine commutator_le.mpr fun a ha b hb => ?_
    have h1 := (h (inv_mem hb)).2 a⁻¹ (hJM (inv_mem ha))
    rwa [inv_inv, inv_inv, ← commutatorElement_def] at h1
  obtain ⟨b, hbJ, hb2⟩ := hJinv
  have h1 := orderOf_dvd_natCard (⟨b, hJO hbJ⟩ : oddCoreIn M)
  rw [Subgroup.orderOf_mk, hb2] at h1
  exact absurd (Nat.Coprime.eq_one_of_dvd (coprime_card_oddCoreIn M) h1) (by norm_num)

@[expose] def SolomonThm13FStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G →
    ∀ N : Subgroup G, IsKBalanced N → solomonKStarOf N ≤ solomonKStarOf (⊤ : Subgroup G)

theorem solomonThm13FStar_of_thm13 (h : SolomonThm13Input) : SolomonThm13FStar :=
  fun G _ _ _ _ _ N hN => h G N hN

theorem maximalTwoComponent_of_thm12 (h12 : Thm12Input) (hA : AschbacherRankOneInput)
    (hGS : GSLStarSolomonStep) (h212 : Lemma212Input) (h13 : SolomonThm13FStar) :
    GrSLit.MaximalTwoComponentInput := by
  intro G _ _ _ hsF hnF hoF hK J hJgs h2 hpsp _ t ht hJt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJmax : IsSolomonMaximal J := hGS G hsF hnF hoF hK J hJgs h2 hpsp
  have hJs : J ∈ solomonKStar G := mem_solomonKStar_of_aschbacher hA hsF hnF hoF hJmax
  obtain ⟨⟨a, -, hJa, hJap⟩, -⟩ := hJgs
  have hJtc : IsTwoComponentIn J (centralizer ({a} : Set G)) := ⟨hJa, hJap⟩
  have hperf : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hJap
  have hJinv : ∃ b ∈ J, orderOf b = 2 := by
    have h2' := h2
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h2'
    exact exists_orderOf_eq_two_of_pRank (by omega)
  have hJne : J ≠ ⊥ := by
    obtain ⟨b, hbJ, hb2⟩ := hJinv
    intro h
    rw [h, mem_bot] at hbJ
    rw [hbJ, orderOf_one] at hb2
    norm_num at hb2
  refine ⟨?_, fun h3 g hc => ?_⟩
  ·
    set C := centralizer ({t} : Set G) with hC
    set T := zpowers t with hT
    have hCT : centralizer ((T : Subgroup G) : Set G) = C := by
      rw [hT, zpowers_eq_closure, centralizer_closure]
    have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hTne : T ≠ ⊥ := by
      intro h
      rw [hT, zpowers_eq_bot] at h
      rw [h, orderOf_one] at ht
      norm_num at ht
    have hCloc : IsPLocal 2 C := Sol78.isPLocal_centralizer_of_orderOf_eq_two ht
    have hconj : ∀ g : G, conjugate J g ≤ C →
        IsTwoComponentIn (conjugate J g) (conjugate (centralizer ({a} : Set G)) g) ∧
          IsSolomonMaximal (conjugate J g) ∧ (∃ b ∈ conjugate J g, orderOf b = 2) ∧
          conjugate J g ≤ solomonKStarOf C := by
      intro g hg
      have hJgs : conjugate J g ∈ solomonKStar G := conjugate_mem_solomonKStar hJs g
      have hJgtc : IsTwoComponentIn (conjugate J g) (conjugate (centralizer ({a} : Set G)) g) :=
        isTwoComponentIn_map (MulAut.conj g⁻¹) hJtc
      refine ⟨hJgtc, hJgs.1, ?_, ?_⟩
      · obtain ⟨b, hbJ, hb2⟩ := hJinv
        refine ⟨(MulAut.conj g⁻¹) b, ⟨b, hbJ, rfl⟩, ?_⟩
        rw [MulEquiv.orderOf_eq, hb2]
      · have hTJg : T ≤ coreActionKernel (conjugate J g) := by
          rw [hT, zpowers_le]
          exact Sol78.mem_coreActionKernel_of_commute fun j hj =>
            mem_centralizer_singleton_iff.mp (hg hj)
        have h := h212 G (conjugate J g) T hJgs hTne hT2 hTJg
        rwa [hCT, inf_eq_left.mpr hg, twoLayerIn_eq_self_of_isTwoComponentIn hJgtc] at h
    have hJ1 : conjugate J 1 = J := by
      ext x
      rw [SolAltLit.mem_conjugate_iff_conj, one_mul, inv_one, mul_one]
    have hJK : J ≤ solomonKStarOf C := by
      have h := (hconj 1 (by rw [hJ1]; exact hJt)).2.2.2
      rwa [hJ1] at h
    have hKL : solomonKStarOf C ≤ solomonLStarOf C :=
      iSup₂_le fun K hK => le_iSup₂_of_le K ⟨hK.1, hK.2.1⟩ le_rfl
    have hKTL : solomonKStarOf C ≤ twoLayerIn C :=
      iSup₂_le fun K hK => le_twoLayerIn_of_isTwoComponentIn hK.1
    have hLne : solomonLStarOf C ≠ ⊥ := fun h => hJne (le_bot_iff.mp (h ▸ hJK.trans hKL))
    rcases h12 G hsF hnF C hCloc hLne with hq | hLie | ⟨-, hSp⟩
    ·
      obtain ⟨M, hMS⟩ : ∃ M : Subgroup G, IsTwoComponentIn M C ∧ IsSolomonMaximal M := by
        by_contra hnone
        push Not at hnone
        apply hLne
        exact le_bot_iff.mp (iSup₂_le fun K hK => absurd hK.2 (hnone K hK.1))
      have hLM : solomonLStarOf C = M :=
        le_antisymm (iSup₂_le fun K hK => (eq_of_isQuasisimple_solomonLStarOf hq hK hMS).le)
          (le_iSup₂_of_le M hMS le_rfl)
      have hMJ : ∀ {L CL : Subgroup G}, IsTwoComponentIn L CL → IsSolomonMaximal L →
          (∃ b ∈ L, orderOf b = 2) → L ≤ C → L ≤ solomonKStarOf C → L ⊔ oddCoreIn M = M := by
        intro L CL hL hLmax hLinv hLC hLK
        have hLperf : ⁅L, L⁆ = L := UnbalancedCorr.commutator_eq_of_isPComponent hL.1 hL.2
        have hLM' : L ≤ M := hLM ▸ hLK.trans hKL
        have hequiv := solomonEquiv_of_not_le_coreActionKernel ht hL hLmax hLC (hLK.trans hKTL)
          hMS.1 (not_le_coreActionKernel_of_le hLM' hLperf hLinv)
        obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_reflTransGen hequiv.2
        exact sup_oddCoreIn_eq_of_fusionZStar hL hMS.1 hLM' hLinv e.symm
      have hJM := hMJ hJtc hJmax hJinv hJt hJK
      refine iSup₂_le fun g hg => ?_
      obtain ⟨hJgtc, hJgmax, hJginv, hJgK⟩ := hconj g hg
      have hJgM := hMJ hJgtc hJgmax hJginv hg hJgK
      calc conjugate J g ≤ M := hJgM ▸ le_sup_left
        _ = J ⊔ oddCoreIn M := hJM.symm
        _ ≤ oddCoreIn C ⊔ J :=
          sup_le le_sup_right ((oddCoreIn_le_of_isTwoComponentIn hMS.1).trans le_sup_left)
    · exact absurd hLie hoF
    ·
      exfalso
      obtain ⟨M, ⟨hMC, -⟩, hJM⟩ := exists_not_le_coreActionKernel hJtc hJK hJinv
      have hequiv := solomonEquiv_of_not_le_coreActionKernel ht hJtc hJmax hJt (hJK.trans hKTL)
        hMC hJM
      obtain ⟨F, _, _, hF, ⟨eM⟩⟩ := hSp M hMC
      obtain ⟨eM'⟩ := nonempty_fusionZStar_equiv_statedProj eM
      obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_reflTransGen hequiv.2
      exact hpsp ⟨F, inferInstance, inferInstance, hF, ⟨e.trans eM'⟩⟩
  ·
    have hle := sup_conjugate_le_solomonKStarOf_top (h13 G hsF hnF hK) hJtc hJs h3 g hc
    rw [solomonKStarOf_top_eq_bot_of_fStar hsF hnF] at hle
    exact hJne (le_bot_iff.mp (le_sup_left.trans hle))

theorem solomon76TwoLocal_of_thm12 (h12 : Thm12Input) :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
      (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
      ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) →
      ∀ N : Subgroup G, IsPLocal 2 N →
        (∀ K : Subgroup G, GH74.GLS.IsPCompIn 2 N K → ¬ ∃ (F : Type) (_ : Field F) (_ : Finite F),
          Odd (Nat.card F) ∧ Nonempty (K ⧸ pPrimeCore 2 K ≃* Assembly.LowTwoRank.StatedSp 2 F)) →
        sSup {K | GH74.GLS.IsPCompIn 2 N K ∧ IsSolomonMaximal K} ≠ ⊥ →
        IsQuasisimple (↥(sSup {K | GH74.GLS.IsPCompIn 2 N K ∧ IsSolomonMaximal K}) ⧸
          pPrimeCore 2 ↥(sSup {K | GH74.GLS.IsPCompIn 2 N K ∧ IsSolomonMaximal K})) := by
  intro G _ _ hsF hnF hoF N hN hSp hne
  have heq : sSup {K | GH74.GLS.IsPCompIn 2 N K ∧ IsSolomonMaximal K} = solomonLStarOf N := by
    rw [sSup_eq_iSup]
    rfl
  rw [heq] at hne ⊢
  rcases h12 G hsF hnF N hN hne with h | h | ⟨-, h⟩
  · exact h
  · exact absurd h hoF
  · exfalso
    obtain ⟨K, hK⟩ : ∃ K : Subgroup G, IsTwoComponentIn K N ∧ IsSolomonMaximal K := by
      by_contra hnone
      push Not at hnone
      exact hne (le_bot_iff.mp (iSup₂_le fun K hK => absurd hK.2 (hnone K hK.1)))
    exact hSp K hK.1 (h K hK.1)

end CFSG.ComponentClassification.Sol76
