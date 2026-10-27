module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdSchur
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row40
public import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma119
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HF4Model
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HTE6Model
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import CFSG.GroupTheory.PerfectLeSupCenter
public import CFSG.GroupTheory.PerfectCoverProduct
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TStdCovDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HStdExcl

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.CatB

theorem exclQuot_of_noSmall {S : Type} [Group S] (h : NoSmall S) : ExclQuot S := by
  intro α hα hα1 I hI hsmall
  exact (h α hα hα1 I hI hsmall).elim

private theorem card_of_catalogIs_isA6 {S : Type} [Group S] [Finite S]
    (h : catalogIs S S10.isA6) : Nat.card S = 360 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | alternating n hn =>
    simp only [S10.isA6] at hi
    subst hi
    rw [CFSG.LocalAnalysis.GLTheoremA.CatDistinct.card_alternating_of_iso
      (n := 6) (by norm_num : 5 ≤ 6) e]
    norm_num [Nat.factorial]
  | cyclic _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie _ => exact hi.elim

private theorem three_dvd_card_of_smallType {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (h : SmallType 3 K) : 3 ∣ Nat.card ↥K := by
  have hPS : Nat.card (PSimple 3 K) ∣ Nat.card ↥K :=
    (Subgroup.card_quotient_dvd_card (Subgroup.center (PQuot 3 K))).trans
      (Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥K))
  rcases h with hU | hA
  · rw [U48.card_of_isU4two hU] at hPS
    exact (by norm_num : (3 : ℕ) ∣ 25920).trans hPS
  · rw [card_of_catalogIs_isA6 hA] at hPS
    exact (by norm_num : (3 : ℕ) ∣ 360).trans hPS

private theorem exists_mul_ne_of_isQuasisimple {G : Type*} [Group G]
    (h : CFSG.Open.IsQuasisimple G) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hcomm : IsMulCommutative G := isMulCommutative_iff.mpr hcon
  have hbot : commutator G = ⊥ := (commutator_eq_bot_iff G).2 hcomm
  rw [h.1] at hbot
  have h1 : ∀ x : G, x = 1 := fun x => by
    have hx : x ∈ (⊤ : Subgroup G) := Subgroup.mem_top x
    rw [hbot] at hx
    exact Subgroup.mem_bot.1 hx
  haveI : Subsingleton G := ⟨fun a b => by rw [h1 a, h1 b]⟩
  haveI : Nontrivial (G ⧸ Subgroup.center G) := h.2.toNontrivial
  haveI : Subsingleton (G ⧸ Subgroup.center G) :=
    (QuotientGroup.mk'_surjective (Subgroup.center G)).subsingleton
  exact not_subsingleton _ ‹Subsingleton (G ⧸ Subgroup.center G)›

theorem center_eq_bot_of_exclQuot {X : Type} [Group X] [Finite X] {L K : Subgroup X} {d : X}
    (hL : CFSG.Open.IsQuasisimple ↥L) {S : Type} [Group S] (e : ↥L ⧸ Subgroup.center ↥L ≃* S)
    (hS : ExclQuot S) (hdN : d ∈ Subgroup.normalizer (L : Set X)) (hd3 : d ^ 3 = 1)
    (hdL : d ∉ Subgroup.centralizer (L : Set X))
    (hK : CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({d} : Set X)))
    (hKs : SmallType 3 K) : Subgroup.center ↥K = ⊥ := by
  classical
  let Q := ↥L
  let Z : Subgroup Q := Subgroup.center Q
  let π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  let γ : MulAut Q :=
    normalizerConjAutOfMem L (Subgroup.normalizer (L : Set X)) le_rfl ⟨d, hdN⟩
  let γbar : MulAut (Q ⧸ Z) :=
    normalizerToCenterQuotientAut L (Subgroup.normalizer (L : Set X)) le_rfl ⟨d, hdN⟩
  let α : MulAut S := MulAut.congr e γbar
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker ≤ Subgroup.center Q := by
    rw [show π.ker = Subgroup.center Q from QuotientGroup.ker_mk' _]
  have hcomp : ∀ k : Q, π (γ k) = γbar (π k) := fun k =>
    normalizerConjAutOfMem_comp_mk L (Subgroup.normalizer (L : Set X)) le_rfl ⟨d, hdN⟩ k
  have hperf : Group.IsPerfect Q := ⟨hL.1⟩
  have hdNpow : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (L : Set X))) ^ 3 = 1 := by
    ext
    simp [hd3]
  have hγ3 : γ ^ 3 = 1 := by
    change ((Subgroup.normalizerMonoidHom (H := L)) ⟨d, hdN⟩) ^ 3 = 1
    rw [← map_pow, hdNpow, map_one]
  have hγbar3 : γbar ^ 3 = 1 := by
    change ((normalizerToCenterQuotientAut L (Subgroup.normalizer (L : Set X)) le_rfl)
      ⟨d, hdN⟩) ^ 3 = 1
    rw [← map_pow, hdNpow, map_one]
  have hα3 : α ^ 3 = 1 := by
    change (MulAut.congr e γbar) ^ 3 = 1
    rw [← map_pow (MulAut.congr e) γbar 3, hγbar3, map_one]
  have hα1 : α ≠ 1 := by
    intro hα
    have hγbar1 : γbar = 1 := by
      ext q
      have h : e (γbar q) = e q := by
        have h' := congrArg (fun f : MulAut S => f (e q)) hα
        simpa [α, MulAut.congr_apply, MulAut.one_apply] using h'
      exact e.injective h
    have hdC := (normalizerToCenterQuotientAut_eq_one_iff hperf le_rfl ⟨d, hdN⟩).1 hγbar1
    exact hdL hdC.2
  let K' : Subgroup Q := K.subgroupOf L
  have hKL : K ≤ L := hK.1.trans inf_le_left
  have hK'qs : CFSG.Open.IsQuasisimple ↥K' :=
    hK.2.2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL)
  have hmemK' : ∀ k : ↥K', (k : Q) ∈ fixSubgroup γ := by
    intro k
    rw [mem_fixSubgroup]
    apply Subtype.ext
    have hkK : ((k : Q) : X) ∈ K := k.2
    have hkC : ((k : Q) : X) ∈ Subgroup.centralizer ({d} : Set X) :=
      (Subgroup.mem_inf.1 (hK.1 hkK)).2
    have hcomm : ((k : Q) : X) * d = d * ((k : Q) : X) :=
      Subgroup.mem_centralizer_singleton_iff.1 hkC
    have hval : (((normalizerConjAutOfMem L (Subgroup.normalizer (L : Set X)) le_rfl
        ⟨d, hdN⟩) k : Q) : X) = d * ((k : Q) : X) * d⁻¹ := by
      simp [normalizerConjAutOfMem]
    rw [hval, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hK'le : K' ≤ fixSubgroup γ := fun k hk => hmemK' ⟨k, hk⟩
  have hγeq : γ = (Subgroup.normalizerMonoidHom (H := L)) ⟨d, hdN⟩ := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    simp [γ, normalizerConjAutOfMem, Subgroup.inclusion]
  have hK'sub : IsSubnormal K' (fixSubgroup γ) := by
    have hfixmap : (fixSubgroup γ).map L.subtype =
        L ⊓ Subgroup.centralizer ({d} : Set X) := by
      rw [hγeq]
      exact CFSG.map_eqLocus_normalizerMonoidHom L hdN
    have hcomap : (L ⊓ Subgroup.centralizer ({d} : Set X)).comap L.subtype = fixSubgroup γ := by
      rw [← hfixmap]
      exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective (fixSubgroup γ)
    have h := hK.2.1.comap L.subtype
    rw [show K.comap L.subtype = K' from rfl, hcomap] at h
    exact h
  let J : Subgroup (Q ⧸ Z) := K'.map π
  let I : Subgroup S := J.map e.toMonoidHom
  have hK'notZ : ¬ K' ≤ π.ker := by
    intro hle
    have hZQ : K' ≤ Subgroup.center Q := by
      rwa [show π.ker = Subgroup.center Q from QuotientGroup.ker_mk' _] at hle
    have hcenter_top : Subgroup.center ↥K' = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 (hZQ x.2) (y : Q)
    haveI : Subsingleton (↥K' ⧸ Subgroup.center ↥K') := by
      rw [hcenter_top]
      exact QuotientGroup.subsingleton_quotient_top
    haveI : Nontrivial (↥K' ⧸ Subgroup.center ↥K') := hK'qs.2.toNontrivial
    exact not_subsingleton _ ‹Subsingleton (↥K' ⧸ Subgroup.center ↥K')›
  have hJqs : CFSG.Open.IsQuasisimple ↥J := by
    have hrange : (π.comp K'.subtype).range = J := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hkerne : (π.comp K'.subtype).ker ≠ ⊤ := by
      intro htop
      apply hK'notZ
      intro k hk
      have hk' : (⟨k, hk⟩ : ↥K') ∈ (π.comp K'.subtype).ker := by rw [htop]; trivial
      exact hk'
    rw [← hrange]
    exact CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top
      hK'qs (π.comp K'.subtype) hkerne
  have hJle : J ≤ fixSubgroup γbar :=
    (Subgroup.map_mono hK'le).trans (map_fixSubgroup_le π hker γ γbar hcomp)
  have hJsub : IsSubnormal J (fixSubgroup γbar) := by
    have h1 : IsSubnormal J ((fixSubgroup γ).map π) := hK'sub.map π
    have hnormal : (((fixSubgroup γ).map π).subgroupOf (fixSubgroup γbar)).Normal :=
      normal_map_fixSubgroup π hker γ γbar hcomp hπsurj
    have h2 : IsSubnormal ((fixSubgroup γ).map π) (fixSubgroup γbar) :=
      CFSG.Open.IsSubnormal.step (H := (fixSubgroup γ).map π) (M := fixSubgroup γbar)
        (K := fixSubgroup γbar) (map_fixSubgroup_le π hker γ γbar hcomp) hnormal
        (CFSG.Open.IsSubnormal.refl _)
    exact h1.trans h2
  have hIsub : IsSubnormal I (fixSubgroup α) := by
    have h := hJsub.map e.toMonoidHom
    have hfix : fixSubgroup α = (fixSubgroup γbar).map e.toMonoidHom := by
      change fixSubgroup (MulAut.congr e γbar) = _
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e γbar
    rw [hfix]
    exact h
  have hIqs : CFSG.Open.IsQuasisimple ↥I := by
    let eJI : ↥J ≃* ↥I := Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
    exact hJqs.of_mulEquiv eJI.symm
  have hIcomp : CFSG.Open.IsComponentOf I (fixSubgroup α) := ⟨hIsub.le, hIsub, hIqs⟩
  have hKcard : 1 < Nat.card (PSimple 3 K) := by
    rcases hKs with hU | hA
    · rw [U48.card_of_isU4two hU]
      norm_num
    · rw [card_of_catalogIs_isA6 hA]
      norm_num
  have hne : GLAPPrimeCore 3 ↥K ≠ ⊤ := hstd_ne_top_of_one_lt hKcard
  obtain ⟨eKps⟩ := hstd_pSimple_equiv_center hK.2.2 hne
  have hψkerZ : (π.subgroupMap K').ker ≤ Subgroup.center ↥K' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxZ : (x : Q) ∈ Subgroup.center Q := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center Q)]
      exact congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hxZ (y : Q)
  obtain ⟨eJq⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hK'qs.1 (π.subgroupMap K') (π.subgroupMap_surjective K') hψkerZ
  let eKK' : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKL
  let eKK'q : ↥K' ⧸ Subgroup.center ↥K' ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.congr (Subgroup.center ↥K') (Subgroup.center ↥K) eKK'
      (Subgroup.map_center_eq eKK')
  let eJI : ↥J ≃* ↥I := Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
  let eJqI : ↥J ⧸ Subgroup.center ↥J ≃* ↥I ⧸ Subgroup.center ↥I :=
    QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥I) eJI
      (Subgroup.map_center_eq eJI)
  let eIps : ↥I ⧸ Subgroup.center ↥I ≃* PSimple 3 K :=
    eJqI.symm.trans (eJq.symm.trans (eKK'q.trans eKps.symm))
  have hcardI : Nat.card (↥I ⧸ Subgroup.center ↥I) = Nat.card (PSimple 3 K) :=
    Nat.card_congr eIps.toEquiv
  have hSmallOrd : SmallOrd I := by
    rcases hKs with hU | hA
    · left
      rw [hcardI, U48.card_of_isU4two hU]
    · right
      rw [hcardI, card_of_catalogIs_isA6 hA]
  obtain ⟨hZI, H, hIH, hHsimple, hHtriv⟩ := hS α hα3 hα1 I hIcomp hSmallOrd
  haveI : IsSimpleGroup ↥H := hHsimple
  let Lbar : Subgroup (Q ⧸ Z) := H.map e.symm.toMonoidHom
  let P : Subgroup Q := Lbar.comap π
  let M : Subgroup Q := ⁅P, P⁆
  have hHnc : ∃ a b : ↥H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_mul_ne_of_isQuasisimple hIqs
    refine ⟨⟨a, hIH a.2⟩, ⟨b, hIH b.2⟩, ?_⟩
    intro h
    apply hab
    apply Subtype.ext
    exact congrArg (fun x : ↥H => (x : S)) h
  have hHperf : Group.IsPerfect ↥H := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hHnc).1.1
  have hHcomm : ⁅H, H⁆ = H := Subgroup.isPerfect_iff.mp hHperf
  have hHZ : Subgroup.center ↥H = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hHnc).2
  have hLcomm : ⁅Lbar, Lbar⁆ = Lbar := by
    change ⁅H.map e.symm.toMonoidHom, H.map e.symm.toMonoidHom⁆ = H.map e.symm.toMonoidHom
    rw [← Subgroup.map_commutator, hHcomm]
  have hMmap : M.map π = Lbar :=
    CFSG.GroupTheory.PerfectCover.map_commutator_comap π hπsurj hLcomm
  have hMperf : Group.IsPerfect ↥M :=
    CFSG.GroupTheory.PerfectCover.isPerfect_commutator_comap π hπsurj hker hLcomm
  have hZP : Z ≤ P := by
    intro z hz
    rw [Subgroup.mem_comap]
    have hz1 : π z = 1 := by
      have hz' : z ∈ π.ker := by rwa [show π.ker = Z from QuotientGroup.ker_mk' _]
      exact hz'
    rw [hz1]
    exact Subgroup.one_mem _
  have hMP : M ≤ P := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hP_eq : P = M ⊔ Z := by
    apply le_antisymm
    · intro p hp
      obtain ⟨q, hq, z, hz, hpq⟩ :=
        CFSG.GroupTheory.PerfectCover.exists_mul_of_mem_comap π hπsurj hLcomm hp
      have hzZ : z ∈ Z := by
        rw [show π.ker = Z from QuotientGroup.ker_mk' _] at hz
        exact hz
      rw [hpq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hzZ)
    · exact sup_le hMP hZP
  let ψ : ↥M →* ↥Lbar :=
    (π.comp M.subtype).codRestrict Lbar (fun m => by
      have hm : π (m : Q) ∈ M.map π := Subgroup.mem_map_of_mem π m.2
      rwa [hMmap] at hm)
  have hψsurj : Function.Surjective ψ := by
    intro l
    have hl : (l : Q ⧸ Z) ∈ M.map π := by rw [hMmap]; exact l.2
    obtain ⟨m, hm, hml⟩ := hl
    refine ⟨⟨m, hm⟩, ?_⟩
    apply Subtype.ext
    exact hml
  have hψker : ψ.ker ≤ Subgroup.center ↥M := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    have hmZ : (m : Q) ∈ Z := by
      have h1 : π (m : Q) = 1 := congrArg Subtype.val hm
      rw [← QuotientGroup.ker_mk' Z]
      exact h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hmZ (y : Q)
  obtain ⟨eM⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hMperf.commutator_eq_top ψ hψsurj hψker
  let eLH : ↥Lbar ≃* ↥H :=
    (Subgroup.equivMapOfInjective H e.symm.toMonoidHom e.symm.injective).symm
  let eLHq : ↥Lbar ⧸ Subgroup.center ↥Lbar ≃* ↥H ⧸ Subgroup.center ↥H :=
    QuotientGroup.congr (Subgroup.center ↥Lbar) (Subgroup.center ↥H) eLH
      (Subgroup.map_center_eq eLH)
  let eH : ↥H ⧸ Subgroup.center ↥H ≃* ↥H :=
    (QuotientGroup.quotientMulEquivOfEq hHZ).trans QuotientGroup.quotientBot
  let eMH : ↥M ⧸ Subgroup.center ↥M ≃* ↥H := eM.trans (eLHq.trans eH)
  have hMqs : CFSG.IsQuasisimple ↥M := by
    refine ⟨hMperf, eMH.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hHnc
    exact ⟨eMH.symm a, eMH.symm b, fun h => hab (by
      have := congrArg eMH h
      simpa using this)⟩
  have hMtriv : Subgroup.center ↥M = ⊥ := hHtriv M hMqs ⟨eMH⟩
  have hMZ : M ⊓ Z = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxM : x ∈ M := hx.1
    have hxZ : x ∈ Z := hx.2
    have hxc : (⟨x, hxM⟩ : ↥M) ∈ Subgroup.center ↥M := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 hxZ (y : Q)
    rw [hMtriv] at hxc
    have hx1 : (⟨x, hxM⟩ : ↥M) = 1 := Subgroup.mem_bot.1 hxc
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hx1)
  have hK'P : K' ≤ P := by
    rw [← Subgroup.map_le_iff_le_comap]
    have hJI : J = I.map e.symm.toMonoidHom := by
      ext x
      constructor
      · intro hx
        have h1 : e x ∈ I := Subgroup.mem_map_of_mem e.toMonoidHom hx
        have h2 : e.symm (e x) ∈ I.map e.symm.toMonoidHom :=
          Subgroup.mem_map_of_mem e.symm.toMonoidHom h1
        simpa using h2
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨j, hj, rfl⟩ := hy
        simpa using hj
    have hJL : J ≤ Lbar := by
      rw [hJI]
      exact Subgroup.map_mono hIH
    exact hJL
  have hK'perf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.mp ⟨hK'qs.1⟩
  have hMperfSub : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.mp hMperf
  have hK'M : K' ≤ M :=
    CFSG.le_of_perfect_of_le_sup_center hMperfSub hK'perf (hK'P.trans (le_of_eq hP_eq))
  have hK'Z : K' ⊓ Z = ⊥ := by
    have hle : K' ⊓ Z ≤ M ⊓ Z := inf_le_inf_right Z hK'M
    rw [hMZ] at hle
    exact le_bot_iff.mp hle
  have hψkerK : (π.subgroupMap K').ker = ⊥ := by
    ext x
    rw [Subgroup.mem_bot, MonoidHom.mem_ker]
    constructor
    · intro hx
      have hxZ : (x : Q) ∈ Z := by
        rw [← QuotientGroup.ker_mk' Z]
        exact congrArg Subtype.val hx
      have hxinf : (x : Q) ∈ K' ⊓ Z := ⟨x.2, hxZ⟩
      rw [hK'Z] at hxinf
      exact Subtype.ext (Subgroup.mem_bot.1 hxinf)
    · intro hx
      rw [hx]
      simp
  have hψinj : Function.Injective (π.subgroupMap K') := (MonoidHom.ker_eq_bot_iff _).1 hψkerK
  let eK'J : ↥K' ≃* ↥J :=
    MulEquiv.ofBijective (π.subgroupMap K') ⟨hψinj, π.subgroupMap_surjective K'⟩
  let eK'I : ↥K' ≃* ↥I := eK'J.trans eJI
  have hcenterK' : Subgroup.center ↥K' = ⊥ := by
    have hcard : Nat.card ↥(Subgroup.center ↥K') = Nat.card ↥(Subgroup.center ↥I) :=
      Nat.card_congr (Subgroup.centerCongr eK'I).toEquiv
    rw [hZI] at hcard
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using hcard)
  have hcenterK : Subgroup.center ↥K = ⊥ := by
    have hcard : Nat.card ↥(Subgroup.center ↥K) = Nat.card ↥(Subgroup.center ↥K') :=
      Nat.card_congr (Subgroup.centerCongr eKK'.symm).toEquiv
    rw [hcenterK'] at hcard
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using hcard)
  exact hcenterK

theorem stdCovDiagExclAt_of_quot
    (hF : ExclF4) (hU : ExclU6) (hT : ExclTE6) : StdCovDiagExclAt := by
  intro X _ _ L K B d hL hcat hB hBcard hidm hCB hdB hdL hKcomp hsmall
  obtain ⟨i, hi, ⟨ePS⟩⟩ := hcat
  have hKL : K ≤ L := hKcomp.1.trans inf_le_left
  have h3L : 3 ∣ Nat.card ↥L :=
    dvd_trans (three_dvd_card_of_smallType hsmall) (Subgroup.card_dvd_of_le hKL)
  have hneL : GLAPPrimeCore 3 ↥L ≠ ⊤ := by
    intro htop
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcop : Nat.Coprime 3 (Nat.card ↥L) := by
      have h := pPrimeCore_coprime_card (p := 3) (G := ↥L)
      have htop' : CFSG.pPrimeCore 3 ↥L = ⊤ := htop
      rw [htop'] at h
      simpa using h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop h3L
  obtain ⟨eL0⟩ := hstd_pSimple_equiv_center hL hneL
  have hdN : d ∈ Subgroup.normalizer (L : Set X) := S11.le_normalizer_of_innerDiag hidm hdB
  have hd3 : d ^ 3 = 1 := hB.2 d hdB
  rcases hi with hF4 | hU6 | hTE6
  · obtain ⟨Kf, hfield, hfinite, hKfcard, ⟨eF⟩⟩ :=
      I2610.exists_adjointGroup_of_catalogIs_isF4two ⟨i, hF4, ⟨ePS⟩⟩
    letI : Field Kf := hfield
    letI : Finite Kf := hfinite
    have hS : ExclQuot ↥(adjointGroup Tag.F4 Kf) :=
      exclQuot_of_noSmall (hF Kf hKfcard)
    exact center_eq_bot_of_exclQuot hL (eL0.symm.trans eF) hS hdN hd3 hdL hKcomp hsmall
  · obtain ⟨e6⟩ := HSubT.nonempty_S6_of_isU6two ⟨i, hU6, ⟨ePS⟩⟩
    exact center_eq_bot_of_exclQuot hL (eL0.symm.trans e6) hU hdN hd3 hdL hKcomp hsmall
  · obtain ⟨Kf, hfield, hfinite, σ, hKfcard, hσ, ⟨eT⟩⟩ :=
      I2610.exists_twistedE6RootGroup_of_catalogIs_isTE6two ⟨i, hTE6, ⟨ePS⟩⟩
    letI : Field Kf := hfield
    letI : Finite Kf := hfinite
    have hS : ExclQuot ↥(twistedE6RootGroup Kf σ) :=
      exclQuot_of_noSmall (hT Kf σ hKfcard hσ)
    exact center_eq_bot_of_exclQuot hL (eL0.symm.trans eT) hS hdN hd3 hdL hKcomp hsmall

end CFSG.LocalAnalysis.GLTheoremA.HStdExcl

end
