module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46dTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46c
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1NoSLTwo
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSwap

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

theorem nonempty_KBar_quotient_equiv (L : Subgroup X) (β : X) :
    Nonempty (↥(KBar L β) ⧸ pPrimeCore 2 ↥(KBar L β) ≃* Bar (centralizerResidual L β)) := by
  have hKM : centralizerResidual L β ≤ centralizer ({β} : Set X) :=
    centralizerResidual_le.trans inf_le_right
  obtain ⟨e₂⟩ := GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X))))
    GSThmB.OddQuot.not_two_dvd_card_ker
    ((centralizerResidual L β).subgroupOf (centralizer ({β} : Set X)))
  let e := subgroupOfEquivOfLe hKM
  exact ⟨e₂.symm.trans (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e))⟩

theorem exists_intrinsic_isMTypeSchur (hGA : TBLit.GriessMultipliersOdd) {β : X}
    (hβ2 : orderOf β = 2) {K₀ : Subgroup (MBar β)} (hK₀ : IsComponent K₀)
    (hβK₀ : betaBar β ∈ K₀) (hZ : Nat.card ↥(center ↥K₀) = 2) {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : Blueprint.LieModel (↥K₀ ⧸ center ↥K₀) .PSL 2 p k) :
    ∃ J : Subgroup X, IsTwoComponentIn J (centralizer {β}) ∧ β ∈ J ∧ IsMTypeSchur p ↥J ∧
      Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* ↥K₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (MBar β) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hK₀p : IsPComponent 2 K₀ :=
    (isTwoComponent_iff_isPComponent K₀).mp ((isTwoComponent_iff_isComponent hO K₀).mpr hK₀)
  obtain ⟨-, hlift, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X))))
    (QuotientGroup.mk'_surjective _)
    (GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥(centralizer ({β} : Set X))))
  obtain ⟨hJ₀, hJ₀map⟩ := hlift K₀ hK₀p
  set J₀ := closure {x : ↥(centralizer ({β} : Set X)) |
    x ∈ K₀.comap (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X)))) ∧
      ∃ k : ℕ, orderOf x = 2 ^ k} with hJ₀def
  have hβJ₀ : (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({β} : Set X))) ∈ J₀ :=
    subset_closure ⟨hβK₀, 1, by rw [pow_one, Subgroup.orderOf_mk]; exact hβ2⟩
  have hJM : J₀.map (centralizer ({β} : Set X)).subtype ≤ centralizer ({β} : Set X) :=
    map_subtype_le J₀
  have hsub : (J₀.map (centralizer ({β} : Set X)).subtype).subgroupOf
      (centralizer ({β} : Set X)) = J₀ :=
    comap_map_eq_self_of_injective (centralizer ({β} : Set X)).subtype_injective J₀
  have hJ : IsTwoComponentIn (J₀.map (centralizer ({β} : Set X)).subtype) (centralizer {β}) :=
    (isTwoComponentIn_iff hJM).mpr (by rw [hsub]; exact hJ₀)
  refine ⟨J₀.map (centralizer ({β} : Set X)).subtype, hJ, ⟨_, hβJ₀, rfl⟩, ?_⟩
  set ρ := (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X)))).comp
    (Subgroup.inclusion hJM) with hρ
  have hrange : ρ.range = K₀ := by
    rw [hρ, MonoidHom.range_comp, Subgroup.inclusion_range, hsub, hJ₀map]
  set g := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ρ.rangeRestrict with hg
  have hgs : Function.Surjective g := by
    rw [hg, MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp ρ.rangeRestrict_surjective
  have hgk : g.ker = ρ.ker := by
    rw [hg, MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _),
      MonoidHom.ker_rangeRestrict]
  have hker : ¬ 2 ∣ Nat.card g.ker := by
    rw [hgk, hρ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    intro h2
    have hdvd := Subgroup.card_comap_dvd_of_injective
      (pPrimeCore 2 ↥(centralizer ({β} : Set X))) (Subgroup.inclusion hJM)
      (Subgroup.inclusion_injective hJM)
    exact (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) (h2.trans hdvd)
  have hO₀ : pPrimeCore 2 ↥K₀ = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hK₀.2
  obtain ⟨eJ⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective g hgs hker
  exact ⟨isMTypeSchur_of_surjective hGA hp hp2 g hgs hker hJ.2.2.1 hK₀.1 hO₀ hZ hm,
    ⟨eJ.trans ((QuotientGroup.quotientMulEquivOfEq hO₀).trans QuotientGroup.quotientBot)⟩⟩

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem orderOf_beta (hσ : Setup42 h hS w z) (i j : ℕ) :
    orderOf (w ^ (orderOf w / 2) * t ^ i * z ^ j) = 2 := by
  have hβ1 : w ^ (orderOf w / 2) * t ^ i * z ^ j ≠ 1 := fun h2 =>
    hσ.rho_beta_ne_one i j (by
      rw [show (⟨_, hσ.beta_mem_H i j⟩ : ↥(centralizer ({t} : Set X))) = 1 from Subtype.ext h2,
        map_one])
  exact orderOf_eq_prime (hσ.sq_eq_one_of_mem_X (beta_mem_X i j)) hβ1

theorem isLemma46d_of_ne
    [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hGA : TBLit.GriessMultipliersOdd) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hCI : GSLit.ClassicalInvolutionInput) (hσ : Setup42 h hS w z) (i j : ℕ) :
    ∀ K₀ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), IsComponent K₀ →
      K₀.map (MulAut.conj (hσ.tBar i j)).toMonoidHom ≠ K₀ →
      KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
        centralizerResidual (K₀ ⊔ K₀.map (MulAut.conj (hσ.tBar i j)).toMonoidHom)
          (hσ.tBar i j) →
      K₀ ⊔ K₀.map (MulAut.conj (hσ.tBar i j)).toMonoidHom =
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) →
      IsLemma46d p f L (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hσ.tBar i j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβ2 := hσ.orderOf_beta i j
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set tb := hσ.tBar i j with htb
  intro K₀ hK₀ hne hKb hE
  have hO : pPrimeCore 2 (MBar β) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have htb2 : tb ^ 2 = 1 := by
    have := pow_orderOf_eq_one tb
    rwa [hσ.orderOf_tBar i j] at this
  have htbinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right (by rw [← sq, htb2])
  have hc : K₀ ≤ centralizer
      ((K₀.map (MulAut.conj tb).toMonoidHom : Subgroup (MBar β)) : Set (MBar β)) :=
    le_centralizer_map_conj_of_isComponent hK₀ hne
  have hK₀perf : Group.IsPerfect ↥K₀ := hK₀.1.1
  have hKbφ : KBar L β = (swapDiag K₀ tb hc).range :=
    hKb.trans (centralizerResidual_sup_eq_range K₀ htb2 hc hK₀perf)
  have hO₀ : pPrimeCore 2 ↥K₀ = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hK₀.2
  have hZ₀ : IsPGroup 2 ↥(center ↥K₀) := isPGroup_center_of_pPrimeCore_eq_bot hO₀
  have hOR : pPrimeCore 2 ↥(swapDiag K₀ tb hc).range = ⊥ :=
    pPrimeCore_eq_bot_of_surjective_of_isQuasisimple hK₀.1 hZ₀ _
      (swapDiag K₀ tb hc).rangeRestrict_surjective
  obtain ⟨eK⟩ := nonempty_KBar_quotient_equiv L β
  have eR : ↥(swapDiag K₀ tb hc).range ≃* Bar (centralizerResidual L β) :=
    ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hOR.symm)).trans
      (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hKbφ.symm)
        (pPrimeCore_map_iso 2 _))).trans eK
  have hmR : Blueprint.LieModel ↥(swapDiag K₀ tb hc).range .PSL 2 p (f / 2) :=
    GSThmB.OddQuot.lieModel_of_equiv eR.symm (hσ.lieModel_bar_K hFC hKC i j)
  have : IsSimpleGroup ↥(swapDiag K₀ tb hc).range := isSimpleGroup_of_lieModel_psl2 hmR
  have hZR : center ↥(swapDiag K₀ tb hc).range = ⊥ :=
    (LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_of_lieModel_psl2 hmR)).2
  have hAcen := inf_le_centralizer_sup K₀ hc
  have hAt : ∀ a ∈ K₀ ⊓ K₀.map (MulAut.conj tb).toMonoidHom,
      MulAut.conj tb a ∈ K₀ ⊓ K₀.map (MulAut.conj tb).toMonoidHom := by
    rintro a ⟨ha₀, ⟨b, hb, rfl⟩⟩
    refine ⟨?_, ⟨_, ha₀, rfl⟩⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [conj_conj_of_sq_eq_one htb2]
    exact hb
  have hφE : ∀ k : ↥K₀, swapDiag K₀ tb hc k ∈ K₀ ⊔ K₀.map (MulAut.conj tb).toMonoidHom :=
    fun k => mul_mem (mem_sup_left k.2) (mem_sup_right ⟨k, k.2, rfl⟩)
  have hAinv : ∀ a ∈ K₀ ⊓ K₀.map (MulAut.conj tb).toMonoidHom, MulAut.conj tb a = a⁻¹ := by
    intro a ha
    have hφa : (⟨swapDiag K₀ tb hc ⟨a, ha.1⟩, ⟨_, rfl⟩⟩ : ↥(swapDiag K₀ tb hc).range) ∈
        center _ := by
      rw [mem_center_iff]
      rintro ⟨_, k, rfl⟩
      apply Subtype.ext
      show swapDiag K₀ tb hc k * swapDiag K₀ tb hc ⟨a, ha.1⟩ =
        swapDiag K₀ tb hc ⟨a, ha.1⟩ * swapDiag K₀ tb hc k
      have h1 := mem_centralizer_iff.mp (hAcen ha) _ (hφE k)
      have h2 := mem_centralizer_iff.mp (hAcen (hAt a ha)) _ (hφE k)
      rw [swapDiag_apply K₀ tb hc ⟨a, ha.1⟩]
      calc swapDiag K₀ tb hc k * (a * MulAut.conj tb a) =
            swapDiag K₀ tb hc k * a * MulAut.conj tb a := (mul_assoc _ _ _).symm
        _ = a * swapDiag K₀ tb hc k * MulAut.conj tb a := by rw [h1]
        _ = a * (swapDiag K₀ tb hc k * MulAut.conj tb a) := mul_assoc _ _ _
        _ = a * (MulAut.conj tb a * swapDiag K₀ tb hc k) := by rw [h2]
        _ = a * MulAut.conj tb a * swapDiag K₀ tb hc k := (mul_assoc _ _ _).symm
    rw [hZR, mem_bot] at hφa
    exact eq_inv_of_mul_eq_one_right (congrArg Subtype.val hφa)
  have hkerA : ∀ k ∈ (swapDiag K₀ tb hc).ker,
      (k : MBar β) ∈ K₀ ⊓ K₀.map (MulAut.conj tb).toMonoidHom := by
    intro k hk
    rw [MonoidHom.mem_ker, swapDiag_apply] at hk
    have hk' : MulAut.conj tb (k : MBar β) = (k : MBar β)⁻¹ := eq_inv_of_mul_eq_one_right hk
    have hkinv : (k : MBar β)⁻¹ ∈ K₀.map (MulAut.conj tb).toMonoidHom := hk' ▸ ⟨k, k.2, rfl⟩
    exact ⟨k.2, by simpa using inv_mem hkinv⟩
  have hkerφ : (swapDiag K₀ tb hc).ker = center ↥K₀ := by
    apply le_antisymm
    · intro k hk
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp (hc y.2) _ (hkerA k hk).2).symm
    · intro c hc'
      have hφc : (⟨swapDiag K₀ tb hc c, ⟨_, rfl⟩⟩ : ↥(swapDiag K₀ tb hc).range) ∈ center _ := by
        rw [mem_center_iff]
        rintro ⟨_, k, rfl⟩
        apply Subtype.ext
        show swapDiag K₀ tb hc k * swapDiag K₀ tb hc c =
          swapDiag K₀ tb hc c * swapDiag K₀ tb hc k
        rw [← map_mul, ← map_mul, mem_center_iff.mp hc' k]
      rw [hZR, mem_bot] at hφc
      exact congrArg Subtype.val hφc
  have eZ : ↥K₀ ⧸ center ↥K₀ ≃* ↥(swapDiag K₀ tb hc).range :=
    (QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans (QuotientGroup.quotientKerEquivRange _)
  have hmK₀ : Blueprint.LieModel (↥K₀ ⧸ center ↥K₀) .PSL 2 p (f / 2) :=
    GSThmB.OddQuot.lieModel_of_equiv eZ.symm hmR
  have hA : K₀ ⊓ K₀.map (MulAut.conj tb).toMonoidHom = ⊥ := by
    by_contra hA
    have hA2 : IsPGroup 2 ↥(K₀ ⊓ K₀.map (MulAut.conj tb).toMonoidHom) := by
      intro x
      have hxc : (⟨x, x.2.1⟩ : ↥K₀) ∈ center ↥K₀ := by
        rw [mem_center_iff]
        intro y
        exact Subtype.ext (mem_centralizer_iff.mp (hAcen x.2) _ (mem_sup_left y.2))
      obtain ⟨k, hk⟩ := hZ₀ ⟨_, hxc⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun y : ↥(center ↥K₀) => ((y : ↥K₀) : MBar β)) hk
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      simpa using this
    have hcard : 2 ∣ Nat.card ↥(K₀ ⊓ K₀.map (MulAut.conj tb).toMonoidHom) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA2
      rcases n with _ | n
      · exact absurd (Subgroup.card_eq_one.mp (by rw [hn, pow_zero])) hA
      · rw [hn, pow_succ]
        exact dvd_mul_left 2 _
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 hcard
    have ha2 : (a : MBar β) ^ 2 = 1 := by
      have h1 := pow_orderOf_eq_one a
      rw [ha] at h1
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2
    have ha1 : (a : MBar β) ≠ 1 := by
      intro h1
      have h0 : a = 1 := Subtype.ext h1
      rw [h0, orderOf_one] at ha
      exact absurd ha (by norm_num)
    have hat : MulAut.conj tb (a : MBar β) = a := by
      rw [hAinv _ a.2]
      exact inv_eq_of_mul_eq_one_right (by rw [← sq, ha2])
    have haC : (a : MBar β) ∈ centralizer ({tb} : Set (MBar β)) := by
      rw [mem_centralizer_singleton_iff]
      rw [MulAut.conj_apply] at hat
      calc (a : MBar β) * tb = tb * a * tb⁻¹ * tb := by rw [hat]
        _ = tb * a := by group
    have hEc : ∀ y ∈ layer (MBar β), y * (a : MBar β) = a * y := fun y hy =>
      mem_centralizer_iff.mp (hAcen a.2) y (by rw [hE]; exact hy)
    have haE : (a : MBar β) ∈ layer (MBar β) := by
      rw [← hE]
      exact mem_sup_left a.2.1
    have haZ : (a : MBar β) ∈ (center ↥(layer (MBar β))).map (layer (MBar β)).subtype := by
      refine ⟨⟨a, haE⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      intro y
      exact Subtype.ext (hEc y y.2)
    have haO := map_center_layer_le_pCore hO haZ
    have h46f := hσ.lemma46f hnonab hK hSch hFC hKC i j
    have hacl := h46f.2.2.2 ⟨haO, haC⟩
    have hb2 : betaBar β ^ 2 = 1 := by
      rw [betaBar, ← QuotientGroup.mk_pow]
      rw [show (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({β} : Set X))) ^ 2 =
        1 from Subtype.ext (by rw [Subgroup.coe_pow, hσ.sq_eq_one_of_mem_X (beta_mem_X i j),
          Subgroup.coe_one]), QuotientGroup.mk_one]
    have htbb : tb * betaBar β = betaBar β * tb := mem_center_iff.mp (betaBar_mem_center β) tb
    have hEK : layer (MBar β) ≤ centralizer ({tb} : Set (MBar β)) → layer (MBar β) ≤ KBar L β :=
      fun hEt => sSup_le fun J hJ => hσ.le_KBar_of_isComponent hFC hKC i j hJ
        ((le_sSup (s := {K : Subgroup (MBar β) | IsComponent K}) hJ : J ≤ layer (MBar β)).trans
          hEt)
    have haβ : (a : MBar β) = betaBar β := by
      rcases mem_closure_pair htb2 hb2 htbb hacl with hx | hx | hx | hx
      · exact absurd hx ha1
      · exfalso
        have hEt : layer (MBar β) ≤ centralizer ({tb} : Set (MBar β)) := fun y hy =>
          mem_centralizer_singleton_iff.mpr (by rw [← hx]; exact hEc y hy)
        exact hσ.tBar_not_mem_KBar i j
          (hEK hEt (show tb ∈ layer (MBar β) by rw [← hx]; exact haE))
      · exact hx
      · exfalso
        have hEt : layer (MBar β) ≤ centralizer ({tb} : Set (MBar β)) := fun y hy => by
          rw [mem_centralizer_singleton_iff]
          have h1 := hEc y hy
          rw [hx] at h1
          have h2 : betaBar β * y = y * betaBar β :=
            (mem_center_iff.mp (betaBar_mem_center β) y).symm
          calc y * tb = y * (tb * betaBar β) * (betaBar β)⁻¹ := by group
            _ = tb * betaBar β * y * (betaBar β)⁻¹ := by rw [h1]
            _ = tb * (betaBar β * y) * (betaBar β)⁻¹ := by group
            _ = tb * (y * betaBar β) * (betaBar β)⁻¹ := by rw [h2]
            _ = tb * y := by group
        exact hσ.tBar_mul_betaBar_not_mem_KBar i j
          (hEK hEt (show tb * betaBar β ∈ layer (MBar β) by rw [← hx]; exact haE))
    have hβK₀ : betaBar β ∈ K₀ := haβ ▸ a.2.1
    have hZne : center ↥K₀ ≠ ⊥ := by
      intro h0
      have hβc : (⟨betaBar β, hβK₀⟩ : ↥K₀) ∈ center ↥K₀ := by
        rw [mem_center_iff]
        intro y
        exact Subtype.ext (mem_center_iff.mp (betaBar_mem_center β) y)
      rw [h0, mem_bot] at hβc
      exact hσ.betaBar_ne_one i j (congrArg Subtype.val hβc)
    have hZ2 := card_center_eq_two_of_psl_two hGA hGC hK₀.1 hZ₀ hZne h.config.prime
      h.config.ne_two hmK₀
    obtain ⟨J, hJ, hβJ, -, ⟨eJ⟩⟩ := exists_intrinsic_isMTypeSchur hGA hβ2 hK₀ hβK₀ hZ2
      h.config.prime h.config.ne_two hmK₀
    obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := T1.isSLTwoOver_of_psl2Cover hGA h.config.prime
      h.config.ne_two hK₀.1 hZ₀ hZne hmK₀
    exact T1.false_of_intrinsic_slTwo hCI hnonab hcat hβ2 hJ hβJ h.config.prime h.config.ne_two
      ⟨F, inferInstance, inferInstance, hF, ⟨eJ.trans eF⟩⟩
  have hinj : Function.Injective (swapDiag K₀ tb hc) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have h1 := hkerA k hk
    rw [hA, mem_bot] at h1
    exact Subtype.ext h1
  have eK₀ : ↥K₀ ≃* ↥(KBar L β) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hKbφ.symm)
  have hset : ((swapDiag K₀ tb hc).range : Set (MBar β)) =
      (fun k => k * (tb⁻¹ * k * tb)) '' (K₀ : Set (MBar β)) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, by rw [swapDiag_apply, MulAut.conj_apply, htbinv]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, by rw [swapDiag_apply, MulAut.conj_apply, htbinv]⟩
  refine .inr ⟨K₀, K₀.map (MulAut.conj tb⁻¹).toMonoidHom, by rw [htbinv]; exact hE,
    by rw [htbinv]; exact hA, by rw [htbinv]; exact hc, rfl, ⟨eK₀⟩,
    ⟨(K₀.equivMapOfInjective _ (MulAut.conj tb⁻¹).injective).symm.trans eK₀⟩,
    GSThmB.OddQuot.lieModel_of_equiv (MulEquiv.subgroupCongr hKbφ.symm) hmR, ?_, ?_⟩
  · apply le_antisymm
    · refine le_inf (hσ.KBar_le_layer hnonab hK hSch hFC hKC i j) ?_
      rw [hKb]
      exact fun x hx => (centralizerResidual_le hx).2
    · rintro x ⟨hxE, hxC⟩
      obtain ⟨a, c, hcA, rfl⟩ := exists_eq_swapDiag_mul K₀ htb2 hc
        ⟨by rw [hE]; exact hxE, hxC⟩
      rw [hA, mem_bot] at hcA
      rw [hcA, mul_one, hKbφ]
      exact ⟨a, rfl⟩
  · rw [hKbφ, ← hset, closure_eq]

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
