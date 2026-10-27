module

public import CFSG.Goldschmidt.Steps.G3aGlue
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.Goldschmidt.Steps.GoldTypeBender

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace G3a

section Frame

variable {G : Type} [Group G] [Finite G]

@[expose] def phiK (H A : Subgroup G) : normalClosureIn H A →* H ⧸ goldschmidtOddCore H :=
  (QuotientGroup.mk' (goldschmidtOddCore H)).comp (Subgroup.inclusion (normalClosureIn_le H A))

omit [Finite G] in
theorem phiK_apply (H A : Subgroup G) (k : normalClosureIn H A) :
    phiK H A k = QuotientGroup.mk' (goldschmidtOddCore H) ⟨k, normalClosureIn_le H A k.2⟩ := rfl

theorem ker_phiK (H A : Subgroup G) :
    goldschmidtOddCore (normalClosureIn H A) = (phiK H A).ker := by
  have := normalClosureIn_normal H A
  ext k
  rw [MonoidHom.mem_ker, phiK_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact CFSG.ComponentClassification.OddCore.normal_step_mem_iff (normalClosureIn_le H A) k

omit [Finite G] in
theorem range_phiK (H A : Subgroup G) :
    (phiK H A).range = barOf H (normalClosureIn H A) := by
  rw [phiK, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

@[expose] noncomputable def phiQ (H A : Subgroup G) :
    normalClosureIn H A ⧸ goldschmidtOddCore (normalClosureIn H A) →* H ⧸ goldschmidtOddCore H :=
  QuotientGroup.lift _ (phiK H A) (le_of_eq (ker_phiK H A))

theorem phiQ_mk (H A : Subgroup G) (k : normalClosureIn H A) :
    phiQ H A (QuotientGroup.mk' _ k) = phiK H A k := rfl

theorem frame {H A : Subgroup G} (hS : IsSStarIn H A) {L : Subgroup (H ⧸ goldschmidtOddCore H)}
    (hL : IsComponentOf L (barOf H (normalClosureIn H A))) :
    ∃ T : Subgroup G, fusionIsSylowIn 2 T H ∧ A ≤ T ∧ IsStronglyClosedIn A T H ∧
    ∃ P : Sylow 2 (normalClosureIn H A ⧸ goldschmidtOddCore (normalClosureIn H A)),
      (P : Subgroup _) = barOf (normalClosureIn H A) T ∧
      SConf P (barOf (normalClosureIn H A) A) ∧
    ∃ L' : Subgroup (normalClosureIn H A ⧸ goldschmidtOddCore (normalClosureIn H A)),
      IsComponentOf L' ⊤ ∧ ∀ k : normalClosureIn H A,
        QuotientGroup.mk' (goldschmidtOddCore (normalClosureIn H A)) k ∈ L' ↔ phiK H A k ∈ L := by
  obtain ⟨T, hT, hAT, hcl, P, hP, hc⟩ := sconf_of_isSStarIn hS
  refine ⟨T, hT, hAT, hcl, P, hP, hc, ?_⟩
  set ψ := quotientEquivRange (phiK H A) _ (ker_phiK H A) with hψ
  have hL' : IsComponentOf L (phiK H A).range := by rw [range_phiK]; exact hL
  refine ⟨(L.subgroupOf (phiK H A).range).map ψ.symm.toMonoidHom,
    (CFSG.ComponentClassification.LocalComponents.equiv_iff ψ.symm _).mpr
      (isComponentOf_subgroupOf hL'), fun k => ?_⟩
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf, hψ,
    quotientEquivRange_mk]

omit [Finite G] in
theorem mem_preOf {H : Subgroup G} {L : Subgroup (H ⧸ goldschmidtOddCore H)} {x : G}
    (hxH : x ∈ H) (hx : QuotientGroup.mk' (goldschmidtOddCore H) ⟨x, hxH⟩ ∈ L) :
    x ∈ preOf H L := ⟨⟨x, hxH⟩, hx, rfl⟩

omit [Finite G] in
theorem mem_preOf_iff {H : Subgroup G} {L : Subgroup (H ⧸ goldschmidtOddCore H)} {x : H} :
    (x : G) ∈ preOf H L ↔ QuotientGroup.mk' (goldschmidtOddCore H) x ∈ L := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [show y = x from Subtype.ext hyx] at hy
  · exact fun hx => ⟨x, hx, rfl⟩

theorem part_c
    {H A : Subgroup G} (hS : IsSStarIn H A) {L : Subgroup (H ⧸ goldschmidtOddCore H)}
    (hL : IsComponentOf L (barOf H (normalClosureIn H A))) :
    A = A ⊓ preOf H L ⊔
      A ⊓ preOf H (Subgroup.centralizer (L : Set (H ⧸ goldschmidtOddCore H))) := by
  obtain ⟨T, hT, hAT, hcl, P, hP, hc, L', hL', hmem⟩ := frame hS hL
  obtain ⟨-, -, hF3⟩ := hc.analysis hL'
  have hAH : A ≤ H := hS.1
  have hAK : A ≤ normalClosureIn H A := le_normalClosureIn hAH
  refine le_antisymm (fun a ha => ?_) (sup_le inf_le_left inf_le_left)
  set k : normalClosureIn H A := ⟨a, hAK ha⟩ with hk
  have hkB : QuotientGroup.mk' _ k ∈ barOf (normalClosureIn H A) A := ⟨k, ha, rfl⟩
  obtain ⟨x, ⟨hxB, hxL⟩, hact⟩ := hF3 _ hkB
  obtain ⟨x', hx'A, rfl⟩ := hxB
  have hx'L : phiK H A x' ∈ L := (hmem x').mp hxL
  have hyC : phiK H A (k * x'⁻¹) ∈
      Subgroup.centralizer (L : Set (H ⧸ goldschmidtOddCore H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro ℓ hℓ
    have hℓR : ℓ ∈ (phiK H A).range := by rw [range_phiK]; exact hL.1 hℓ
    obtain ⟨k₁, rfl⟩ := hℓR
    have hk₁ : QuotientGroup.mk' _ k₁ ∈ L' := (hmem k₁).mpr hℓ
    have h1 := congrArg (phiQ H A) (hact _ hk₁)
    simp only [map_mul, map_inv, phiQ_mk] at h1
    rw [map_mul, map_inv]
    calc phiK H A k₁ * (phiK H A k * (phiK H A x')⁻¹)
        = phiK H A k * ((phiK H A k)⁻¹ * phiK H A k₁ * phiK H A k) * (phiK H A x')⁻¹ := by
          group
      _ = phiK H A k * ((phiK H A x')⁻¹ * phiK H A k₁ * phiK H A x') * (phiK H A x')⁻¹ := by
          rw [h1]
      _ = phiK H A k * (phiK H A x')⁻¹ * phiK H A k₁ := by group
  have hxpre : (x' : G) ∈ A ⊓ preOf H L := ⟨hx'A, mem_preOf _ hx'L⟩
  have hypre : a * (x' : G)⁻¹ ∈
      A ⊓ preOf H (Subgroup.centralizer (L : Set (H ⧸ goldschmidtOddCore H))) :=
    ⟨A.mul_mem ha (A.inv_mem hx'A), mem_preOf _ hyC⟩
  have e : a = (a * (x' : G)⁻¹) * x' := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hypre) (Subgroup.mem_sup_left hxpre)

omit [Finite G] in
theorem normalClosureIn_le_of {H A K : Subgroup G} (hKH : K ≤ H) :
    normalClosureIn K (A ⊓ K) ≤ normalClosureIn H A := by
  unfold normalClosureIn
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp hax
  have haA : (a : G) ∈ A := ha.1
  refine ⟨⟨(c : G) * a * (c : G)⁻¹, H.mul_mem (H.mul_mem (hKH c.2) (hKH a.2))
    (H.inv_mem (hKH c.2))⟩, ?_, rfl⟩
  have h1 : (⟨(a : G), hKH a.2⟩ : H) ∈ Subgroup.normalClosure
      ((A.subgroupOf H : Subgroup H) : Set H) := Subgroup.subset_normalClosure haA
  exact Subgroup.Normal.conj_mem inferInstance _ h1 ⟨(c : G), hKH c.2⟩

theorem oddCoreOf_le_of {H K : Subgroup G} (hKH : K ≤ H) (hOK : oddCoreOf H ≤ K) :
    oddCoreOf H ≤ oddCoreOf K := by
  have hle : (oddCoreOf H).subgroupOf K ≤ goldschmidtOddCore K := by
    refine le_sSup ⟨⟨fun n hn g => ?_⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨o, ho, hon⟩ := hn
      refine ⟨⟨(g : G), hKH g.2⟩ * o * ⟨(g : G), hKH g.2⟩⁻¹,
        (goldschmidtOddCore_normal H).conj_mem o ho _, ?_⟩
      have hon' : (o : G) = n := hon
      simp only [Subgroup.coe_subtype, MulMemClass.coe_mul, InvMemClass.coe_inv, hon']
    · have e : Nat.card ((oddCoreOf H).subgroupOf K) = Nat.card (oddCoreOf H) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOK).toEquiv
      rw [e, oddCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
      exact CFSG.ComponentClassification.OddCore.odd_card H
  intro x hx
  exact ⟨⟨x, hOK hx⟩, hle hx, rfl⟩

theorem quasisimple_facts {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsQuasisimple X)
    (hZ : IsPGroup 2 (Subgroup.center X)) :
    goldschmidtLayer X = ⊤ ∧ CFSG.Open.pCore 2 X = Subgroup.center X ∧
      ∀ L : Subgroup X, IsComponentOf L ⊤ → L = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hntriv := CFSG.ComponentClassification.Quasisimple.nontrivial hX
  refine ⟨?_, ?_, fun L hL => ?_⟩
  · rw [eq_top_iff]
    refine le_sSup (show IsComponentOf ⊤ ⊤ from ⟨le_rfl, CFSG.Open.IsSubnormal.refl _,
      CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv hX⟩)
  · have hn := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal (G := X) 2
    apply le_antisymm
    · rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hX
        (CFSG.Open.pCore 2 X) with h | h
      · exact h
      · exfalso
        have hp : IsPGroup 2 X := by
          have := CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup (G := X) 2
          rw [h] at this
          exact this.of_equiv Subgroup.topEquiv
        have := hp.isNilpotent
        have : Group.IsPerfect X := ⟨hX.1⟩
        exact Group.IsPerfect.not_isSolvable X inferInstance
    · exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore 2 _ inferInstance hZ
  · have : Group.IsPerfect L := ⟨hL.2.2.1⟩
    rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hX L
      hL.2.1 with h | h
    · exfalso
      have hnt := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
      rw [h] at hnt
      exact not_nontrivial _ hnt
    · exact h

theorem part_ab
    {H A : Subgroup G} (hS : IsSStarIn H A) {L : Subgroup (H ⧸ goldschmidtOddCore H)}
    (hL : IsComponentOf L (barOf H (normalClosureIn H A))) :
    IsSStarIn (preOf H L) (A ⊓ preOf H L) ∧
      preOf H L = normalClosureIn (preOf H L) (A ⊓ preOf H L) ⊔ oddCoreOf (preOf H L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hAT, hcl, P, hP, hc, L', hL', hmem⟩ := frame hS hL
  obtain ⟨hF1, hF2, hF3⟩ := hc.analysis hL'
  have hAH : A ≤ H := hS.1
  set K := preOf H L with hKdef
  set K' := normalClosureIn K (A ⊓ K) with hK'def
  have hAK₀ : A ≤ normalClosureIn H A := le_normalClosureIn hAH
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hK'K : K' ≤ K := normalClosureIn_le K (A ⊓ K)
  have hK'K₀ : K' ≤ normalClosureIn H A := normalClosureIn_le_of hKH
  have hAKK' : A ⊓ K ≤ K' := le_normalClosureIn inf_le_right
  have hmemK : ∀ k : normalClosureIn H A, phiK H A k ∈ L ↔ (k : G) ∈ K := by
    intro k
    rw [phiK_apply]
    exact (mem_preOf_iff (x := ⟨(k : G), normalClosureIn_le H A k.2⟩)).symm
  set μ : K' →* normalClosureIn H A ⧸ goldschmidtOddCore (normalClosureIn H A) :=
    (QuotientGroup.mk' (goldschmidtOddCore (normalClosureIn H A))).comp
      (Subgroup.inclusion hK'K₀) with hμdef
  have hμ : ∀ x : K', μ x = QuotientGroup.mk' _ ⟨x, hK'K₀ x.2⟩ := fun x => rfl
  have hrange_le : μ.range ≤ L' := by
    rintro _ ⟨x, rfl⟩
    rw [hμ, hmem, hmemK]
    exact hK'K x.2
  have hBle : barOf (normalClosureIn H A) A ⊓ L' ≤ μ.range := by
    rintro _ ⟨⟨x, hxA, rfl⟩, hxL⟩
    have hxK : (x : G) ∈ K := (hmemK x).mp ((hmem x).mp hxL)
    exact ⟨⟨x, hAKK' ⟨hxA, hxK⟩⟩, rfl⟩
  have hK'n := normalClosureIn_normal K (A ⊓ K)
  have hrange_n : (μ.range.subgroupOf L').Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k', hk'⟩ := hn
    obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore (normalClosureIn H A))
      (g : normalClosureIn H A ⧸ goldschmidtOddCore (normalClosureIn H A))
    have hk₀K : (k₀ : G) ∈ K := by
      rw [← hmemK, ← hmem, hk₀]
      exact g.2
    have hconj := hK'n.conj_mem ⟨(k' : G), hK'K k'.2⟩ (k'.2 : (k' : G) ∈ K') ⟨(k₀ : G), hk₀K⟩
    refine ⟨⟨_, hconj⟩, ?_⟩
    rw [hμ]
    simp only [MulMemClass.coe_mul, InvMemClass.coe_inv]
    rw [← hk₀, ← hk', hμ]
    rfl
  have hq : CFSG.Open.IsQuasisimple L' := hL'.2.2
  have hrange : μ.range = L' := by
    refine le_antisymm hrange_le ?_
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (μ.range.subgroupOf L') with hcen | htop
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := hF1
      have hxc := hcen (show (⟨x, hx.2⟩ : L') ∈ μ.range.subgroupOf L' from hBle hx)
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨y, hy⟩)
      exact hxy this.symm
    · intro x hx
      have : (⟨x, hx⟩ : L') ∈ μ.range.subgroupOf L' := by rw [htop]; exact Subgroup.mem_top _
      exact this
  have hmemker : ∀ x : K', x ∈ μ.ker ↔
      (⟨x, hK'K₀ x.2⟩ : normalClosureIn H A) ∈ goldschmidtOddCore (normalClosureIn H A) := by
    intro x
    rw [MonoidHom.mem_ker, hμ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker1 : μ.ker ≤ goldschmidtOddCore K' := by
    apply CFSG.ComponentClassification.OddCore.maximal K' μ.ker (MonoidHom.normal_ker μ)
    have hle : (μ.ker).map (Subgroup.inclusion hK'K₀) ≤ goldschmidtOddCore (normalClosureIn H A) :=
      by
        rintro _ ⟨x, hx, rfl⟩
        exact (hmemker x).mp hx
    have hcard : Nat.card μ.ker ∣ Nat.card (goldschmidtOddCore (normalClosureIn H A)) := by
      rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hK'K₀)]
      exact Subgroup.card_dvd_of_le hle
    exact (CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat hcard
  have hZ2 : IsPGroup 2 (Subgroup.center L') := (N8d _ hc.odd).1 L' hL'
  have hker2 : goldschmidtOddCore K' ≤ μ.ker := by
    set N := (goldschmidtOddCore K').map μ with hN
    have hNL : N ≤ L' := (Subgroup.map_le_range μ _).trans hrange_le
    have hNodd : Odd (Nat.card N) :=
      (CFSG.ComponentClassification.OddCore.odd_card K').of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hNn : (N.subgroupOf L').Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨o, ho, hon⟩ := hn
      have hg : (g : normalClosureIn H A ⧸ goldschmidtOddCore (normalClosureIn H A)) ∈ μ.range :=
        by rw [hrange]; exact g.2
      obtain ⟨y, hy⟩ := hg
      refine ⟨y * o * y⁻¹, (goldschmidtOddCore_normal K').conj_mem o ho y, ?_⟩
      simp only [map_mul, map_inv, MulMemClass.coe_mul, InvMemClass.coe_inv]
      rw [hy, hon]
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (N.subgroupOf L') with hcen | htop
    ·
      have hNbot : N = ⊥ := by
        have hNZ : N ≤ (Subgroup.center L').map L'.subtype := by
          intro x hx
          exact ⟨⟨x, hNL hx⟩, hcen (show (⟨x, hNL hx⟩ : L') ∈ N.subgroupOf L' from hx), rfl⟩
        have hp : IsPGroup 2 N := (hZ2.map L'.subtype).to_le hNZ
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
        rw [hk] at hNodd
        have hk0 : k = 0 := by
          by_contra hk0
          exact (Nat.not_even_iff_odd.mpr hNodd) ((Nat.even_pow' hk0).mpr even_two)
        rw [hk0, pow_zero] at hk
        exact Subgroup.card_eq_one.mp hk
      rw [← Subgroup.map_eq_bot_iff]
      exact hNbot
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := hF1
      have hxN : x ∈ N := by
        have : (⟨x, hx.2⟩ : L') ∈ N.subgroupOf L' := by rw [htop]; exact Subgroup.mem_top _
        exact this
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hxy (by rw [one_mul, mul_one])
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨x, hc.le hx.1⟩
      have hj' : orderOf x = 2 ^ j := by rw [← hj, Subgroup.orderOf_mk]
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hj'
        exact hx1 hj'
      have h2 : 2 ∣ Nat.card N := by
        have h1 := Subgroup.orderOf_dvd_natCard N hxN
        rw [hj'] at h1
        exact (dvd_pow_self 2 hj0).trans h1
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)
  have hker : goldschmidtOddCore K' = μ.ker := le_antisymm hker2 hker1
  set χ : K' ⧸ goldschmidtOddCore K' ≃* L' :=
    (quotientEquivRange μ _ hker).trans (MulEquiv.subgroupCongr hrange) with hχdef
  have hχ : ∀ x : K', ((χ (QuotientGroup.mk' _ x) : L') :
      normalClosureIn H A ⧸ goldschmidtOddCore (normalClosureIn H A)) = μ x := fun x => rfl
  have hOK : oddCoreOf H ≤ K := by
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨o, ?_, rfl⟩
    show QuotientGroup.mk' (goldschmidtOddCore H) o ∈ L
    rw [show QuotientGroup.mk' (goldschmidtOddCore H) o = 1 from
      (QuotientGroup.eq_one_iff _).mpr ho]
    exact L.one_mem
  have hOOK := oddCoreOf_le_of hKH hOK
  have hb : K = K' ⊔ oddCoreOf K := by
    refine le_antisymm (fun x hx => ?_) (sup_le hK'K (Subgroup.map_subtype_le _))
    have hxH : x ∈ H := hKH hx
    have hxL : QuotientGroup.mk' (goldschmidtOddCore H) ⟨x, hxH⟩ ∈ L :=
      mem_preOf_iff.mp hx
    have hxR : QuotientGroup.mk' (goldschmidtOddCore H) ⟨x, hxH⟩ ∈ (phiK H A).range := by
      rw [range_phiK]
      exact hL.1 hxL
    obtain ⟨k₀, hk₀⟩ := hxR
    have hk₀L' : QuotientGroup.mk' _ k₀ ∈ L' := (hmem k₀).mpr (by rw [hk₀]; exact hxL)
    rw [← hrange] at hk₀L'
    obtain ⟨k', hk'⟩ := hk₀L'
    rw [hμ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk'
    have ho₁ : (k' : G)⁻¹ * k₀ ∈ oddCoreOf H := by
      have := normalClosureIn_normal H A
      have := (CFSG.ComponentClassification.OddCore.normal_step_mem_iff (G := G)
        (normalClosureIn_le H A) _).mp hk'
      exact ⟨_, this, rfl⟩
    have ho₂ : (k₀ : G)⁻¹ * x ∈ oddCoreOf H := by
      rw [phiK_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk₀
      exact ⟨_, hk₀, rfl⟩
    have e : x = (k' : G) * (((k' : G)⁻¹ * k₀) * ((k₀ : G)⁻¹ * x)) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left k'.2)
      (Subgroup.mem_sup_right (hOOK ((oddCoreOf H).mul_mem ho₁ ho₂)))
  refine ⟨?_, hb⟩
  have hLn : (L.subgroupOf (barOf H (normalClosureIn H A))).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgR : (g : H ⧸ goldschmidtOddCore H) ∈ (phiK H A).range := by
      rw [range_phiK]; exact g.2
    obtain ⟨k, hk⟩ := hgR
    have hnR : (n : H ⧸ goldschmidtOddCore H) ∈ (phiK H A).range := by
      rw [range_phiK]; exact n.2
    obtain ⟨k₁, hk₁⟩ := hnR
    have h1 : QuotientGroup.mk' _ k₁ ∈ L' := (hmem k₁).mpr (by rw [hk₁]; exact hn)
    have h2 := (hc.normal hL').conj_mem _ h1 (QuotientGroup.mk' _ k)
    rw [← map_mul, ← map_inv, ← map_mul, hmem] at h2
    simp only [MulMemClass.coe_mul, InvMemClass.coe_inv]
    rw [← hk, ← hk₁, ← map_mul, ← map_inv, ← map_mul]
    exact h2
  have hRn : (barOf H (normalClosureIn H A)).Normal :=
    (normalClosureIn_normal H A).map _ (QuotientGroup.mk'_surjective _)
  have hLsub : L.IsSubnormal := Subgroup.IsSubnormal.step L _ hL.1 hRn.isSubnormal hLn
  have hKsub : (K.subgroupOf H).IsSubnormal := by
    have e : K.subgroupOf H = L.comap (QuotientGroup.mk' (goldschmidtOddCore H)) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [e]
    exact hLsub.comap _
  have hTK : fusionIsSylowIn 2 (T ⊓ K) K := fusionIsSylowIn_inf hT hKH hKsub
  have hAc := hS.2.1
  refine ⟨inf_le_right, ⟨⟨fun a b => Subtype.ext ?_⟩⟩, T ⊓ K, hTK, inf_le_inf_right K hAT,
    fun a ha k hk h => ⟨hcl a ha.1 k (hKH hk) h.1, h.2⟩, ?_⟩
  · have := congrArg Subtype.val (hAc.is_comm.comm ⟨(a : G), a.2.1⟩ ⟨(b : G), b.2.1⟩)
    exact this
  have hqK : CFSG.Open.IsQuasisimple (K' ⧸ goldschmidtOddCore K') :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv χ hq
  have hm3 : (Subgroup.center (K' ⧸ goldschmidtOddCore K')).map χ.toMonoidHom =
      Subgroup.center L' := Subgroup.map_center_eq χ
  have hZK : IsPGroup 2 (Subgroup.center (K' ⧸ goldschmidtOddCore K')) :=
    hZ2.of_equiv ((Subgroup.equivMapOfInjective _ χ.toMonoidHom χ.injective).trans
      (MulEquiv.subgroupCongr hm3)).symm
  obtain ⟨hlayer, hpcore, hcomps⟩ := quasisimple_facts hqK hZK
  refine ⟨by rw [hlayer, sup_top_eq], by rw [hpcore], ?_, fun L₀ hL₀ => ?_⟩
  · rw [hlayer, inf_top_eq, hpcore]
    have hm1 : (barOf K' (A ⊓ K)).map χ.toMonoidHom =
        (barOf (normalClosureIn H A) A).subgroupOf L' := by
      ext b
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        show ((χ (QuotientGroup.mk' _ x) : L') :
          normalClosureIn H A ⧸ goldschmidtOddCore (normalClosureIn H A)) ∈
          barOf (normalClosureIn H A) A
        rw [hχ, hμ]
        exact ⟨_, hx.1, rfl⟩
      · intro hb
        rw [Subgroup.mem_subgroupOf] at hb
        obtain ⟨x₀, hx₀A, hx₀⟩ := hb
        have hx₀L : QuotientGroup.mk' _ x₀ ∈ L' := by rw [hx₀]; exact b.2
        have hx₀K : (x₀ : G) ∈ K := (hmemK x₀).mp ((hmem x₀).mp hx₀L)
        refine ⟨QuotientGroup.mk' _ ⟨(x₀ : G), hAKK' ⟨hx₀A, hx₀K⟩⟩,
          ⟨⟨(x₀ : G), hAKK' ⟨hx₀A, hx₀K⟩⟩, ⟨hx₀A, hx₀K⟩, rfl⟩, ?_⟩
        apply Subtype.ext
        change ((χ (QuotientGroup.mk' _ ⟨(x₀ : G), hAKK' ⟨hx₀A, hx₀K⟩⟩) : L') :
          normalClosureIn H A ⧸ goldschmidtOddCore (normalClosureIn H A)) = b
        rw [hχ, hμ, ← hx₀]
    have hTK' : fusionIsSylowIn 2 ((T ⊓ K) ⊓ K') K' :=
      fusionIsSylowIn_inf hTK hK'K hK'n.isSubnormal
    obtain ⟨PK', hPK'⟩ := exists_sylow_of_fusionIsSylowIn hTK'
    set S : Sylow 2 L' := (PK'.mapSurjective (QuotientGroup.mk'_surjective
      (goldschmidtOddCore K'))).mapSurjective (f := χ.toMonoidHom) χ.surjective with hSdef
    have hS : (S : Subgroup L') = (barOf K' (T ⊓ K)).map χ.toMonoidHom := by
      have e : ((T ⊓ K) ⊓ K').subgroupOf K' = (T ⊓ K).subgroupOf K' := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      show (((PK' : Subgroup K').map (QuotientGroup.mk' _)).map χ.toMonoidHom) = _
      rw [hPK', e]
      rfl
    have hle : (barOf K' (T ⊓ K)).map χ.toMonoidHom ≤ (P : Subgroup _).subgroupOf L' := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      show ((χ (QuotientGroup.mk' _ x) : L') :
        normalClosureIn H A ⧸ goldschmidtOddCore (normalClosureIn H A)) ∈ (P : Subgroup _)
      rw [hχ, hμ, hP]
      exact ⟨_, hx.1, rfl⟩
    have hm2 : (barOf K' (T ⊓ K)).map χ.toMonoidHom = (P : Subgroup _).subgroupOf L' :=
      ((S.is_maximal' P.isPGroup'.comap_subtype (by rw [hS]; exact hle)).trans hS).symm
    have hQ : barOf (normalClosureIn H A) A ⊓ L' =
        (Subgroup.center L').map L'.subtype ⊔ Omega1 ((P : Subgroup _) ⊓ L') :=
      le_antisymm hF2 (sup_le (le_inf (hc.center_le hL') (Subgroup.map_subtype_le _))
        (le_inf (hc.omega1_le hL') ((GoldType.omega1_le _).trans inf_le_right)))
    have hm5 : (barOf (normalClosureIn H A) A).subgroupOf L' =
        Subgroup.center L' ⊔ Omega1 ((P : Subgroup _).subgroupOf L') := by
      have e1 : (barOf (normalClosureIn H A) A).subgroupOf L' =
          (barOf (normalClosureIn H A) A ⊓ L').subgroupOf L' := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      rw [e1, hQ, Subgroup.subgroupOf_sup (Subgroup.map_subtype_le _)
        ((GoldType.omega1_le _).trans inf_le_right)]
      congr 1
      · exact Subgroup.comap_map_eq_self_of_injective L'.subtype_injective _
      · have e2 : (P : Subgroup _) ⊓ L' = ((P : Subgroup _).subgroupOf L').map L'.subtype :=
          (Subgroup.subgroupOf_map_subtype _ _).symm
        rw [e2, ← omega1_map _ L'.subtype_injective]
        exact Subgroup.comap_map_eq_self_of_injective L'.subtype_injective _
    apply Subgroup.map_injective (f := χ.toMonoidHom) χ.injective
    rw [hm1, Subgroup.map_sup, hm3, omega1_map _ χ.injective, hm2, hm5]
  · have hL₀ := hcomps L₀ hL₀
    subst hL₀
    have e : (⊤ : Subgroup (K' ⧸ goldschmidtOddCore K')) ≃* L' := Subgroup.topEquiv.trans χ
    rcases hc.types L' hL' with hI | hII
    · exact Or.inl (isGoldTypeI_of_mulEquiv e.symm hI)
    · exact Or.inr (isGoldTypeII_of_mulEquiv e.symm hII)

end Frame

end G3a

end CFSG.Goldschmidt
