module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46c1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitQuoted46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped commutatorElement

theorem hasDihedralSylowTwo_of_isSylowOf {G : Type*} [Group G] [Finite G] {C R : Subgroup G}
    (hR : IsSylowOf 2 R C) {m : ℕ} (hm : 1 ≤ m) (e : ↥R ≃* DihedralGroup (2 ^ m)) :
    GorensteinWalter.HasDihedralSylowTwo ↥C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hR
  intro S
  exact ⟨m, hm, ⟨(Sylow.equiv S Q).trans (((Q : Subgroup ↥C).equivMapOfInjective C.subtype
    C.subtype_injective).trans e)⟩⟩

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem betaBar_ne_one (hσ : Setup42 h hS w z) (i j : ℕ) :
    betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≠ 1 := by
  intro h1
  rw [betaBar, QuotientGroup.eq_one_iff] at h1
  have hdvd := Subgroup.orderOf_dvd_natCard _ h1
  rw [Subgroup.orderOf_mk] at hdvd
  have hβ1 : w ^ (orderOf w / 2) * t ^ i * z ^ j ≠ 1 := fun h2 =>
    hσ.rho_beta_ne_one i j (by
      rw [show (⟨_, hσ.beta_mem_H i j⟩ : ↥(centralizer ({t} : Set X))) = 1 from Subtype.ext h2,
        map_one])
  have hord : orderOf (w ^ (orderOf w / 2) * t ^ i * z ^ j) = 2 :=
    orderOf_eq_prime (hσ.sq_eq_one_of_mem_X (beta_mem_X i j)) hβ1
  rw [hord] at hdvd
  exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)

theorem isLemma46c_of [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (h219 : Harris82Lemma219Input) (hσ : Setup42 h hS w z) (i j : ℕ)
    (hSD : (∀ R : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
        IsSylowOf 2 R (centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) →
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥R ≃* CFSG.Open.SemidihedralGroup n)) →
      ∀ J : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), IsComponent J →
        J ≤ centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →
        ⁅J, zpowers (hσ.tBar i j)⁆ ≠ J) :
    IsLemma46c L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set E := layer (MBar β) with hE
  set Kb := KBar L β with hKb
  set tb := hσ.tBar i j with htb
  have hO : pPrimeCore 2 (MBar β) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hEn : E.Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  have hKE : Kb ≤ E := hσ.KBar_le_layer hnonab hK hSch hFC hKC i j
  have h46b := hσ.lemma46b hFC hKC i j
  have h46f := hσ.lemma46f hnonab hK hSch hFC hKC i j
  obtain ⟨hab, hc⟩ := h219 (MBar β) tb (hσ.orderOf_tBar i j)
  obtain ⟨K₀, hK₀, hcases, -, hc2, hc3⟩ := hc Kb (hσ.isTwoComponentIn_KBar hFC hKC i j)
  rw [twoLayer_eq_layer hO] at hc2 hc3
  set B := K₀ ⊔ K₀.map (MulAut.conj tb).toMonoidHom with hB
  have hKB : Kb ≤ B := by
    rcases hcases with ⟨-, hJ⟩ | ⟨-, hJ⟩
    · exact hJ.1.trans (inf_le_left.trans le_sup_left)
    · rw [hJ]
      exact fun x hx => (centralizerResidual_le hx).1
  have htb2 : tb ^ 2 = 1 := by
    have := pow_orderOf_eq_one tb
    rwa [hσ.orderOf_tBar i j] at this
  have htbinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right (by rw [← sq, htb2])
  have hBt : B.map (MulAut.conj tb).toMonoidHom = B := by
    rw [hB, Subgroup.map_sup, Subgroup.map_map]
    have h1 : ((MulAut.conj tb).toMonoidHom.comp (MulAut.conj tb).toMonoidHom) =
        MonoidHom.id _ := MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      rw [show tb * (tb * x * tb⁻¹) * tb⁻¹ = (tb * tb) * x * (tb * tb)⁻¹ by group, ← sq, htb2]
      group
    rw [h1, Subgroup.map_id, sup_comm]
  have hK₀c : IsComponent K₀ := (isTwoComponent_iff_isComponent hO K₀).mp hK₀
  have hK₀tc : IsComponent (K₀.map (MulAut.conj tb).toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv _ hK₀c
  have hcentB : ∀ J' : Subgroup (MBar β), IsComponent J' → ¬ J' ≤ B →
      J' ≤ centralizer (B : Set (MBar β)) := by
    intro J' hJ' hJ'B
    rcases LocalCores.component_subnormal_subgroup hJ' hK₀c.2 with h1 | h1
    · exact absurd (h1.trans le_sup_left) hJ'B
    rcases LocalCores.component_subnormal_subgroup hJ' hK₀tc.2 with h2 | h2
    · exact absurd (h2.trans le_sup_right) hJ'B
    rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h1))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h2))
  have htC : tb ∈ centralizer (Kb : Set (MBar β)) := hσ.tBar_mem_centralizer_K i j
  have hbC : betaBar β ∈ centralizer (Kb : Set (MBar β)) := betaBar_mem_centralizer_K β
  have htbb : tb * betaBar β = betaBar β * tb := mem_center_iff.mp (betaBar_mem_center β) tb
  have hb2 : betaBar β ^ 2 = 1 := by
    rw [betaBar, ← QuotientGroup.mk_pow]
    rw [show (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({β} : Set X))) ^ 2 =
      1 from Subtype.ext (by rw [Subgroup.coe_pow, hσ.sq_eq_one_of_mem_X (beta_mem_X i j),
        Subgroup.coe_one]), QuotientGroup.mk_one]
  have hEK : E ≤ centralizer ({tb} : Set (MBar β)) → E ≤ Kb := fun hEt =>
    sSup_le fun J hJ => hσ.le_KBar_of_isComponent hFC hKC i j hJ
      ((le_sSup (s := {K : Subgroup (MBar β) | IsComponent K}) hJ : J ≤ E).trans hEt)
  have hBE : B = E := by
    refine le_antisymm (by rw [← hc2]; exact commutator_le_right Kb E) ?_
    refine sSup_le fun J hJ => ?_
    by_contra hJB
    have hJC : J ≤ centralizer (B : Set (MBar β)) := hcentB J hJ hJB
    have hJK : J ≤ centralizer (Kb : Set (MBar β)) := hJC.trans (centralizer_le hKB)
    have hJt : ⁅J, zpowers tb⁆ = J := by
      by_cases hinv : J.map (MulAut.conj tb).toMonoidHom = J
      · have hT : zpowers tb ≤ normalizer (J : Set (MBar β)) := by
          rw [zpowers_le, mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            rw [← hinv]
            exact ⟨x, hx, rfl⟩
          · intro hx
            rw [← hinv] at hx
            obtain ⟨y, hy, hyx⟩ := hx
            have : y = x := (MulAut.conj tb).injective hyx
            rwa [← this]
        rcases commutator_eq_self_or_eq_bot_of_le_normalizer hT hJ.1 with h1 | h1
        · exact h1
        · exfalso
          have hJt : J ≤ centralizer ({tb} : Set (MBar β)) := fun x hx =>
            mem_centralizer_singleton_iff.mpr
              ((mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h1 hx) tb
                (mem_zpowers tb)).symm)
          exact hJB ((hσ.le_KBar_of_isComponent hFC hKC i j hJ hJt).trans hKB)
      · exfalso
        have hJ2 : IsTwoComponent J := (isTwoComponent_iff_isComponent hO J).mpr hJ
        obtain ⟨hE', -, -⟩ := (hab J hJ2).2 hinv
        set E' := centralizerResidual (J ⊔ J.map (MulAut.conj tb).toMonoidHom) tb with hE'def
        have hE'K : E' ≤ Kb := by
          show E' ≤ KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)
          rw [← hσ.layerIn_centralizer_tBar hFC hKC i j]
          intro x hx
          exact ⟨⟨x, hE'.1 hx⟩, (le_sSup (s := {L' : Subgroup ↥(centralizer ({tb} :
            Set (MBar β))) | IsPComponent 2 L'}) ((isTwoComponentIn_iff hE'.1).mp hE') :
            _ ≤ pLayer _ 2) hx, rfl⟩
        have hJtc : IsComponent (J.map (MulAut.conj tb).toMonoidHom) :=
          LocalCores.isComponent_map_mulEquiv _ hJ
        have hJtB : ¬ J.map (MulAut.conj tb).toMonoidHom ≤ B := by
          intro h1
          apply hJB
          have h2 := map_mono (f := (MulAut.conj tb).toMonoidHom) h1
          rw [hBt, Subgroup.map_map] at h2
          have h3 : ((MulAut.conj tb).toMonoidHom.comp (MulAut.conj tb).toMonoidHom) =
              MonoidHom.id _ := MonoidHom.ext fun x => by
            simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
              MonoidHom.id_apply]
            rw [show tb * (tb * x * tb⁻¹) * tb⁻¹ = (tb * tb) * x * (tb * tb)⁻¹ by group, ← sq,
              htb2]
            group
          rwa [h3, Subgroup.map_id] at h2
        have hE'C : E' ≤ centralizer (B : Set (MBar β)) := fun x hx =>
          sup_le hJC (hcentB _ hJtc hJtB) (centralizerResidual_le hx).1
        have hperf : Group.IsPerfect ↥E' := hE'.2.2.1
        have hcomm : ⁅E', E'⁆ = ⊥ := by
          rw [commutator_eq_bot_iff_le_centralizer]
          intro x hx
          rw [mem_centralizer_iff]
          intro y hy
          exact (mem_centralizer_iff.mp (hE'C hx) y (hKB (hE'K hy)))
        rw [commutator_eq_self] at hcomm
        obtain ⟨-, -, a, b, hab'⟩ := hE'.2.2.2
        have : Subsingleton ↥E' := by
          rw [hcomm]
          infer_instance
        apply hab'
        exact Subsingleton.elim _ _
    have hU2 : IsPGroup 2 (closure {tb, betaBar β}) := by
      intro x
      refine ⟨1, ?_⟩
      rw [pow_one]
      apply Subtype.ext
      rcases mem_closure_pair htb2 hb2 htbb x.2 with hx | hx | hx | hx <;>
        simp only [Subgroup.coe_pow, hx, Subgroup.coe_one, one_pow, htb2, hb2]
      rw [(show Commute tb (betaBar β) from htbb).mul_pow, htb2, hb2, one_mul]
    have hUK : closure {tb, betaBar β} ≤ centralizer (Kb : Set (MBar β)) := by
      rw [closure_le]
      rintro _ (rfl | rfl)
      · exact htC
      · exact hbC
    obtain ⟨R₀, hR₀, hUR⟩ := exists_isSylowOf_ge hU2 hUK
    have htne : tb ≠ betaBar β := by
      intro h1
      apply hJB
      refine (hσ.le_KBar_of_isComponent hFC hKC i j hJ fun x _ => ?_).trans hKB
      rw [mem_centralizer_singleton_iff]
      show x * tb = tb * x
      rw [h1]
      exact (mem_center_iff.mp (betaBar_mem_center β) x)
    have hdih : GorensteinWalter.HasDihedralSylowTwo ↥(centralizer (Kb : Set (MBar β))) := by
      rcases h46b.2 R₀ hR₀ with h4 | ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
      ·
        have hlt : zpowers tb < closure {tb, betaBar β} := by
          refine IsConcreteLE.lt_iff_le_and_exists.mpr ⟨zpowers_le.mpr
            (subset_closure (Set.mem_insert _ _)), betaBar β,
            subset_closure (Set.mem_insert_of_mem _ rfl), fun hb => ?_⟩
          rcases eq_one_or_eq_of_mem_zpowers (hσ.orderOf_tBar i j) hb with h1 | h1
          · exact hσ.betaBar_ne_one i j h1
          · exact htne h1.symm
        have hcard := two_mul_card_le_of_lt hlt
        rw [Nat.card_zpowers, hσ.orderOf_tBar i j] at hcard
        have hR₀eq : closure {tb, betaBar β} = R₀ :=
          eq_of_le_of_card_ge hUR (by rw [h4]; exact hcard)
        have hsq : ∀ x : ↥R₀, x ^ 2 = 1 := by
          intro x
          have hx : (x : MBar β) ∈ closure {tb, betaBar β} := by rw [hR₀eq]; exact x.2
          apply Subtype.ext
          rcases mem_closure_pair htb2 hb2 htbb hx with hx | hx | hx | hx <;>
            simp only [Subgroup.coe_pow, hx, Subgroup.coe_one, one_pow, htb2, hb2]
          rw [(show Commute tb (betaBar β) from htbb).mul_pow, htb2, hb2, one_mul]
        have : IsKleinFour ↥R₀ := ⟨h4, by
          rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq)
            with h | h
          · have : Subsingleton ↥R₀ := Monoid.exp_eq_one_iff.mp h
            have h1 : Nat.card ↥R₀ = 1 := Nat.card_of_subsingleton (1 : ↥R₀)
            exact absurd (h4.symm.trans h1) (by norm_num)
          · exact h⟩
        obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := ↥R₀) (G₂ := DihedralGroup 2)
        exact hasDihedralSylowTwo_of_isSylowOf hR₀ (le_refl 1) (e.trans (MulEquiv.refl _))
      · exact hasDihedralSylowTwo_of_isSylowOf hR₀ (by omega) e
      · exfalso
        apply hSD (fun R hR => ⟨n, hn, ⟨(nonempty_mulEquiv_of_isSylowOf hR₀ hR).some.trans e⟩⟩)
          J hJ hJK
        exact hJt
    have hbc : (⟨betaBar β, hbC⟩ : ↥(centralizer (Kb : Set (MBar β)))) ∈ center _ := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_center_iff.mp (betaBar_mem_center β) y)
    have hbo : orderOf (⟨betaBar β, hbC⟩ : ↥(centralizer (Kb : Set (MBar β)))) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hb2 (hσ.betaBar_ne_one i j)
    have hq := isPGroup_quotient_of_hasDihedralSylowTwo hdih hbc hbo
    have hJperf : Group.IsPerfect ↥(J.subgroupOf (centralizer (Kb : Set (MBar β)))) :=
      have : Group.IsPerfect ↥J := hJ.1.1
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJK).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have hJbot := eq_bot_of_isPerfect_of_isPGroup_quotient hq hJperf
    obtain ⟨-, -, a, b, hab'⟩ := hJ.1
    apply hab'
    have : Subsingleton ↥J := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hJK, hJbot, Subgroup.map_bot]
      infer_instance
    exact Subsingleton.elim _ _
  refine ⟨(hc3.trans hBE).symm, (hc2.trans hBE).symm, fun hZ => ?_⟩
  set Z := (center ↥E).map E.subtype with hZdef
  have hZE : Z ≤ E := map_subtype_le _
  have hZc : ∀ x ∈ Z, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x', hx', rfl⟩ y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hx' ⟨y, hy⟩).symm)
  have hZn : Z.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxE := hZE hx
    refine ⟨⟨g * x * g⁻¹, hEn.conj_mem x hxE g⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro y
    apply Subtype.ext
    have hy' : g⁻¹ * y * g ∈ E := by simpa using hEn.conj_mem _ y.2 g⁻¹
    have hc' := hZc x hx _ hy'
    show (y : MBar β) * (g * x * g⁻¹) = g * x * g⁻¹ * y
    calc (y : MBar β) * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc']
      _ = g * x * g⁻¹ * y := by group
  have : IsMulCommutative ↥Z := ⟨⟨fun a b => Subtype.ext (hZc _ a.2 _ (hZE b.2))⟩⟩
  have hZ2 : IsPGroup 2 ↥Z := isPGroup_of_nilpotent_normal Z hZn CommGroup.isNilpotent hO
  have hZO : Z ≤ pCore 2 (MBar β) := le_sSup ⟨hZn, hZ2⟩
  have hZne : Z ≠ ⊥ := fun h0 => hZ ((map_eq_bot_iff_of_injective _ E.subtype_injective).mp h0)
  have hT2 : IsPGroup 2 (zpowers tb) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ.orderOf_tBar i j, pow_one])
  have hP2 : IsPGroup 2 ↥(Z ⊔ zpowers tb) := hZ2.to_sup_of_normal_left hT2
  have : Group.IsNilpotent ↥(Z ⊔ zpowers tb) := hP2.isNilpotent
  have : (Z.subgroupOf (Z ⊔ zpowers tb)).Normal := hZn.subgroupOf _
  have hne : Z.subgroupOf (Z ⊔ zpowers tb) ≠ ⊥ := by
    intro h0
    apply hZne
    rw [← Subgroup.map_subgroupOf_eq_of_le (le_sup_left : Z ≤ Z ⊔ zpowers tb), h0,
      Subgroup.map_bot]
  obtain ⟨⟨a, haZ, hac⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hx1 : (a : MBar β) ≠ 1 := fun h1 => ha1 (Subtype.ext (Subtype.ext h1))
  have hxZ : (a : MBar β) ∈ Z := haZ
  have hxt : (a : MBar β) ∈ centralizer ({tb} : Set (MBar β)) := by
    rw [mem_centralizer_singleton_iff]
    have := mem_center_iff.mp hac ⟨tb, mem_sup_right (mem_zpowers tb)⟩
    exact (congrArg Subtype.val this).symm
  have hxcl := h46f.2.2.2 ⟨hZO hxZ, hxt⟩
  rcases mem_closure_pair htb2 hb2 htbb hxcl with hx | hx | hx | hx
  · exact absurd hx hx1
  · exfalso
    rw [hx] at hxZ
    have hEt : E ≤ centralizer ({tb} : Set (MBar β)) := fun y hy =>
      mem_centralizer_singleton_iff.mpr ((hZc tb hxZ y hy).symm)
    exact hσ.tBar_not_mem_KBar i j (hEK hEt (hZE hxZ))
  · rw [← hx]
    exact hxZ
  · exfalso
    rw [hx] at hxZ
    have hEt : E ≤ centralizer ({tb} : Set (MBar β)) := fun y hy => by
      rw [mem_centralizer_singleton_iff]
      have h1 := hZc _ hxZ y hy
      have h2 : betaBar β * y = y * betaBar β := (mem_center_iff.mp (betaBar_mem_center β) y).symm
      calc y * tb = y * (tb * betaBar β) * (betaBar β)⁻¹ := by group
        _ = tb * betaBar β * y * (betaBar β)⁻¹ := by rw [h1]
        _ = tb * (betaBar β * y) * (betaBar β)⁻¹ := by group
        _ = tb * (y * betaBar β) * (betaBar β)⁻¹ := by rw [h2]
        _ = tb * y := by group
    exact hσ.tBar_mul_betaBar_not_mem_KBar i j (hEK hEt (hZE hxZ))

end Standing.Setup42

theorem harris46c_of (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h219 : Harris82Lemma219Input) (hSD : Harris46SemidihedralInput) : Harris46cInput := by
  intro X _ _ _ hnonab hK hcat t L p f S w z V i j hs i' j'
  exact hs.setup.isLemma46c_of hnonab hK hSch hFC hKC h219 i' j'
    (hSD X hnonab hK hcat t L p f S w z V i j hs i' j')

end CFSG.ComponentClassification.HarrisLit
