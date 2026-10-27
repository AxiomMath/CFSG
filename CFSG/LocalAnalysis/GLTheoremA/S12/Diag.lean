module

public import CFSG.LocalAnalysis.GLTheoremA.S6.I183Diag
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9_1
public import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.Lemma44
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S12

variable {G : Type} [Group G] [Finite G] {p : ℕ} {x : G}

@[expose] def conjFam (x : G) (M : Subgroup G) : Set (Subgroup G) := (fun e => GLBConj e M) '' (Subgroup.zpowers x : Set G)

theorem closureIn_zpowers_eq_iSup (x : G) (M : Subgroup G) :
    closureIn M (Subgroup.zpowers x) = ⨆ M' ∈ conjFam x M, M' := by
  rw [closureIn_eq_iSup_gLBConj]
  simp only [conjFam, iSup_image, SetLike.mem_coe]

theorem conjFam_comp {p : ℕ} {Y M : Subgroup G} {x : G} (hM : GLAPComponent p Y M) (hxY : x ∈ Y) :
    ∀ M' ∈ conjFam x M, GLAPComponent p Y M' := by
  rintro _ ⟨e, he, rfl⟩
  have h1 := glaPComponent_gLBConj hM e
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer ((Subgroup.zpowers_le.2 hxY) he))] at h1

theorem le_normalizer_closureIn_self (I H : Subgroup G) : H ≤ Subgroup.normalizer (closureIn I H : Set G) := by
  have hle : ∀ g ∈ H, GLBConj g (closureIn I H) ≤ closureIn I H := by
    intro g hg
    refine (Subgroup.map_le_iff_le_comap).2 ?_
    rw [closureIn_eq_iSup_gLBConj]
    refine iSup₂_le fun a ha => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    show GLBConj g (GLBConj a I) ≤ _
    rw [gLBConj_gLBConj]
    exact le_biSup (fun h => GLBConj h I) (H.mul_mem ha hg)
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (hle g hg) ?_
  have h := gLBConj_mono (g := g) (hle g⁻¹ (Subgroup.inv_mem _ hg))
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h

theorem conjFam_inv (M : Subgroup G) {C : Subgroup G} (hC : C ∈ conjFam x M) {e : G}
    (he : e ∈ Subgroup.zpowers x) : GLBConj e C ∈ conjFam x M := by
  obtain ⟨a, ha, rfl⟩ := hC
  exact ⟨a * e, Subgroup.mul_mem _ ha he, (gLBConj_gLBConj e a M).symm⟩

theorem conjFam_trans (M : Subgroup G) {C C' : Subgroup G} (hC : C ∈ conjFam x M) (hC' : C' ∈ conjFam x M) :
    ∃ e ∈ Subgroup.zpowers x, GLBConj e C = C' := by
  obtain ⟨a, ha, rfl⟩ := hC
  obtain ⟨b, hb, rfl⟩ := hC'
  refine ⟨a⁻¹ * b, Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hb, ?_⟩
  rw [gLBConj_gLBConj, mul_inv_cancel_left]

theorem conjFam_ne {M : Subgroup G} (hxM : x ∉ Subgroup.normalizer (M : Set G)) {C : Subgroup G}
    (hC : C ∈ conjFam x M) : ∃ C₂ ∈ conjFam x M, C₂ ≠ C := by
  obtain ⟨a, ha, rfl⟩ := hC
  refine ⟨GLBConj (a * x) M, ⟨a * x, Subgroup.mul_mem _ ha (Subgroup.mem_zpowers x), rfl⟩, fun h => hxM ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hax : x ^ k * x = x * x ^ k := ((Commute.refl x).zpow_left k).eq
  rw [hax, ← gLBConj_gLBConj] at h
  have h2 := congrArg (GLBConj (x ^ k)⁻¹) h
  rw [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at h2
  exact mem_normalizer_iff_gLBConj_eq.2 h2

section Lift

variable {Y H : Subgroup G}

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns in
theorem exists_hom_barX_to_pquot (hHY : H ≤ Y) :
    ∃ ψ : ↥(barX p Y H) →* ↥H ⧸ GLAPPrimeCore p ↥H, Function.Surjective ψ ∧
      ∀ h : ↥H, ψ (barXHom p hHY h) = QuotientGroup.mk' (GLAPPrimeCore p ↥H) h := by
  set f := barXHom p hHY with hf
  have hfs : Function.Surjective f := barXHom_surjective p hHY
  have hker : f.ker ≤ (QuotientGroup.mk' (GLAPPrimeCore p ↥H)).ker := by
    rw [QuotientGroup.ker_mk']
    exact barXHom_ker_le_core p hHY
  have key : ∀ h : ↥H, ((QuotientGroup.lift f.ker (QuotientGroup.mk' (GLAPPrimeCore p ↥H)) hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm.toMonoidHom) (f h) =
        QuotientGroup.mk' (GLAPPrimeCore p ↥H) h := by
    intro h
    show (QuotientGroup.lift f.ker (QuotientGroup.mk' (GLAPPrimeCore p ↥H)) hker)
      ((QuotientGroup.quotientKerEquivOfSurjective f hfs).symm (f h)) = _
    have : (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm (f h) =
        (QuotientGroup.mk h : ↥H ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    rw [this, QuotientGroup.lift_mk]
  refine ⟨_, ?_, key⟩
  intro q
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨f h, key h⟩

theorem isComponentOf_map_of_not_le_ker {X Q : Type*} [Group X] [Group Q] (f : X →* Q) {K T : Subgroup X}
    (hK : IsComponentOf K T) (hKf : ¬ K ≤ f.ker) : IsComponentOf (K.map f) (T.map f) :=
  ⟨Subgroup.map_mono hK.1, hK.2.1.map f,
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp (CFSG.LocalCores.isQuasisimple_map
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hK.2.2) f hKf)⟩

theorem isComponentOf_top_subgroupOf {Q : Type*} [Group Q] {L R : Subgroup Q} (h : IsComponentOf L R) :
    IsComponentOf (L.subgroupOf R) ⊤ := by
  refine ⟨le_top, ?_, CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.subgroupOfEquivOfLe h.1) h.2.2⟩
  have h1 := h.2.1.comap R.subtype
  rwa [show R.comap R.subtype = ⊤ from Subgroup.subgroupOf_self R] at h1

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns in
theorem pcomp_of_barred_component (hp : p.Prime) (hHY : H ≤ Y)
    {Dl : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y)} (hDl : IsComponentOf Dl (barX p Y H))
    (hdvd : p ∣ Nat.card Dl) : ∃ P : Subgroup G, GLAPComponent p H P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ψ, hψs, hψ⟩ := exists_hom_barX_to_pquot (p := p) hHY
  have hDl' : IsComponentOf (Dl.subgroupOf (barX p Y H)) ⊤ := isComponentOf_top_subgroupOf hDl
  have hker : ψ.ker ≤ (GLAPPrimeCore p ↥H).map (barXHom p hHY) := by
    intro b hb
    obtain ⟨h, rfl⟩ := barXHom_surjective p hHY b
    refine ⟨h, ?_, rfl⟩
    have h1 := (MonoidHom.mem_ker).1 hb
    rw [hψ] at h1
    exact (QuotientGroup.eq_one_iff h).1 h1
  have hnot : ¬ Dl.subgroupOf (barX p Y H) ≤ ψ.ker := by
    intro hle
    have h1 : Nat.card (Dl.subgroupOf (barX p Y H)) ∣ Nat.card ((GLAPPrimeCore p ↥H).map (barXHom p hHY)) :=
      Subgroup.card_dvd_of_le (hle.trans hker)
    have h2 : Nat.card ((GLAPPrimeCore p ↥H).map (barXHom p hHY)) ∣ Nat.card (GLAPPrimeCore p ↥H) :=
      Subgroup.card_map_dvd _ _
    have h3 : Nat.card (Dl.subgroupOf (barX p Y H)) = Nat.card Dl :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDl.1).toEquiv
    have h4 : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥H)) := CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h4 (hdvd.trans (h3 ▸ h1.trans h2))
  have hcomp := isComponentOf_map_of_not_le_ker ψ hDl' hnot
  rw [Subgroup.map_top_of_surjective ψ hψs] at hcomp
  obtain ⟨L, hL, -⟩ := exists_glaPComponent_barX_eq (p := p) H hcomp
  exact ⟨L, hL⟩

end Lift

section Barred

variable {Y M : Subgroup G}

theorem closureIn_zpowers_le (hM : GLAPComponent p Y M) (hxY : x ∈ Y) : closureIn M (Subgroup.zpowers x) ≤ Y := by
  rw [closureIn_zpowers_eq_iSup]
  exact iSup₂_le fun M' hM' => (conjFam_comp hM hxY M' hM').1

open CFSG.HardMathSupport.Solomon.Coordinator in
theorem layer_isSubnormal {Q : Type*} [Group Q] (H : Subgroup Q) : IsSubnormal (GLALayer H) H := by
  have hle : GLALayer H ≤ H := i25_layer_le H
  have hconj : ∀ g ∈ H, GLBConj g (GLALayer H) ≤ GLALayer H := by
    intro g hg
    show (GLALayer H).map (MulAut.conj g⁻¹).toMonoidHom ≤ GLALayer H
    refine Subgroup.map_le_iff_le_comap.2 (sSup_le fun K hK => ?_)
    refine Subgroup.map_le_iff_le_comap.1 ?_
    exact le_sSup (i25_isComponentOf_gLBConj hK (Subgroup.le_normalizer hg))
  have hN : H ≤ Subgroup.normalizer (GLALayer H : Set Q) := by
    intro g hg
    rw [mem_normalizer_iff_gLBConj_eq]
    refine le_antisymm (hconj g hg) ?_
    have h1 := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g (hconj g⁻¹ (H.inv_mem hg))
    rwa [gLBConj_gLBConj_inv] at h1
  exact IsSubnormal.step hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hN) (IsSubnormal.refl H)

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns in
theorem barX_closure_eq (hM : GLAPComponent p Y M) (hxY : x ∈ Y) :
    barX p Y (closureIn M (Subgroup.zpowers x)) = ⨆ C' : conjFam x M, barX p Y (C' : Subgroup G) := by
  have hcomp := conjFam_comp hM hxY
  have hJsup : closureIn M (Subgroup.zpowers x) ≤ ⨆ C : conjFam x M, (C : Subgroup G) := by
    rw [closureIn_zpowers_eq_iSup]
    exact (iSup_subtype' (p := fun C : Subgroup G => C ∈ conjFam x M) (f := fun C _ => C)).le
  refine le_antisymm (idiag_barX_le_kb hcomp hJsup) (iSup_le fun C' => ?_)
  refine barX_mono p ?_
  rw [closureIn_zpowers_eq_iSup]
  exact le_biSup (fun M' => M') C'.2

theorem centralizer_barX_zpowers (hxY : x ∈ Y) :
    Subgroup.centralizer (barX p Y (Subgroup.zpowers x) : Set (↥Y ⧸ GLAPPrimeCore p ↥Y)) =
      Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥Y) ⟨x, hxY⟩} :
        Set (↥Y ⧸ GLAPPrimeCore p ↥Y)) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    exact h _ ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers x), rfl⟩
  · intro h e he
    obtain ⟨k, rfl⟩ := idiag_E_pow hxY he
    exact (Commute.zpow_left (show Commute (QuotientGroup.mk' (GLAPPrimeCore p ↥Y) ⟨x, hxY⟩) g from h) k).eq

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance in
theorem dvd_card_barX_of_component (hp : p.Prime) (hM : GLAPComponent p Y M) : p ∣ Nat.card (barX p Y M) := by
  by_contra hndvd
  have hcop : Nat.Coprime p (Nat.card (barX p Y M)) := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have hLc : IsComponentOf (barX p Y M) ⊤ := hM.2.2.1
  have hcore : GLAPPrimeCore p (↥Y ⧸ GLAPPrimeCore p ↥Y) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have h1 : barX p Y M ≤ GLAPPrimeCoreOf p (⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y)) := by
    rw [← glaPPrimeCoreOf_eq_self_of_coprime hcop]
    exact glaPPrimeCoreOf_le_of_isSubnormal hp hLc.2.1
  rw [glaPPrimeCoreOf_top_eq_bot_of_eq_bot hcore, le_bot_iff] at h1
  have hnt : Nontrivial (barX p Y M) := CFSG.ComponentClassification.Quasisimple.nontrivial hLc.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt h1

open CFSG.HardMathSupport.Solomon.Coordinator in
theorem diag_barred (hp : p.Prime) (hM : GLAPComponent p Y M) (hxY : x ∈ Y) (hxp : x ^ p = 1)
    (hxM : x ∉ Subgroup.normalizer (M : Set G)) :
    ∃ Dl : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y),
      IsComponentOf Dl (barX p Y (closureIn M (Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G))) ∧
        p ∣ Nat.card Dl := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := fun h => hxM (h ▸ Subgroup.one_mem _)
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hcomp := conjFam_comp hM hxY
  have hM𝒞 : M ∈ conjFam x M := ⟨1, Subgroup.one_mem _, gLBConj_one M⟩
  have hD : IsElemAbelian p (Subgroup.zpowers x) := idiag_elemAbelian_zpowers hxp
  have hidx : (⊥ : Subgroup G).relIndex (Subgroup.zpowers x) = p := by
    rw [Subgroup.relIndex_bot_left, Nat.card_zpowers, hord]
  have hdA : x ∉ (⊥ : Subgroup G) := fun h => hx1 (Subgroup.mem_bot.1 h)
  have hAX : ∀ a ∈ (⊥ : Subgroup G), ∀ y ∈ Y, a * y = y * a := fun a ha y _ => by
    rw [Subgroup.mem_bot.1 ha, one_mul, mul_one]
  have hinv : ∀ C ∈ conjFam x M, ∀ e ∈ Subgroup.zpowers x, GLBConj e C ∈ conjFam x M :=
    fun C hC e he => conjFam_inv M hC he
  have htrans : ∀ C ∈ conjFam x M, ∀ C' ∈ conjFam x M, ∃ e ∈ Subgroup.zpowers x, GLBConj e C = C' :=
    fun C hC C' hC' => conjFam_trans M hC hC'
  have hne : ∀ C ∈ conjFam x M, ∃ C₂ ∈ conjFam x M, C₂ ≠ C := fun C hC => conjFam_ne hxM hC
  set Kb : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y) := ⨆ C' : conjFam x M, barX p Y (C' : Subgroup G) with hKb
  set E : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y) := barX p Y (Subgroup.zpowers x) with hE
  have hlay : GLALayer Kb = Kb := by
    refine le_antisymm (i25_layer_le Kb) ?_
    exact iSup_le fun C' => i25_le_layer (idiag_barX_isComponent hcomp C'.2)
  have hEnorm : E ≤ Subgroup.normalizer (Kb : Set (↥Y ⧸ GLAPPrimeCore p ↥Y)) :=
    idiag_E_le_normalizer hinv (Subgroup.mem_zpowers x) hxY
  have hEab : IsElemAbelian p E := isElemAbelian_barX hD
  have htr : ∀ L L' : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y), IsComponentOf L Kb → IsComponentOf L' Kb →
      ∃ e ∈ E, GLBConj e L = L' := fun L L' hL hL' =>
    idiag_trans hp hD bot_le hidx (Subgroup.mem_zpowers x) hdA hxY hAX hcomp htrans hL hL'
  have hfree : ∀ e ∈ E, e ≠ 1 → ∀ L : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y), IsComponentOf L Kb →
      GLBConj e L ≠ L := fun e he he1 L hL =>
    idiag_free hp hD bot_le hidx (Subgroup.mem_zpowers x) hdA hxY hAX hcomp hne htrans he he1 hL
  obtain ⟨hI25a, -⟩ := input2_5_proved _ p hp Kb E hlay hEnorm hEab htr hfree
  set S : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y) := Kb ⊓ Subgroup.centralizer (E : Set (↥Y ⧸ GLAPPrimeCore p ↥Y))
    with hS
  have hX₁ := idiag_barX_isComponent hcomp hM𝒞
  obtain ⟨Z, hZn, hZc, ⟨φ⟩⟩ := hI25a _ hX₁
  have hDq : CFSG.Open.IsQuasisimple ↥(GLALayer S) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv φ
      (CFSG.ComponentClassification.Quasisimple.central_quotient hX₁.2.2 Z hZc)
  have hLY : closureIn M (Subgroup.zpowers x) ≤ Y := closureIn_zpowers_le hM hxY
  have hbar : barX p Y (closureIn M (Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G)) = S := by
    rw [barX_inf_centralizer hp hxY hLY (le_normalizer_closureIn_self M _ (Subgroup.mem_zpowers x))
      (isPGroup_of_isElemAbelian' hD), barX_closure_eq hM hxY, hS, hE, centralizer_barX_zpowers hxY]
  refine ⟨GLALayer S, ?_, ?_⟩
  · rw [hbar]
    exact ⟨i25_layer_le S, layer_isSubnormal S, hDq⟩
  · have h1 : p ∣ Nat.card (barX p Y M) := dvd_card_barX_of_component hp hM
    haveI : Group.IsPerfect ↥(barX p Y M) := Group.isPerfect_def.mpr hX₁.2.2.1
    have h2 : p ∣ Nat.card (↥(barX p Y M) ⧸ Subgroup.center ↥(barX p Y M)) := by
      by_contra hn
      exact CFSG.RankThree.PerfectCover.perfect_central_quotient_prime_support hp hn h1
    have h3 : Nat.card (↥(barX p Y M) ⧸ Subgroup.center ↥(barX p Y M)) ∣ Nat.card (↥(barX p Y M) ⧸ Z) :=
      Subgroup.index_dvd_of_le hZc
    rw [Nat.card_congr φ.toEquiv]
    exact h2.trans h3

theorem diag_pcomp_exists (hp : p.Prime) (hM : GLAPComponent p Y M) (hxY : x ∈ Y) (hxp : x ^ p = 1)
    (hxM : x ∉ Subgroup.normalizer (M : Set G)) :
    ∃ P : Subgroup G, GLAPComponent p (closureIn M (Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G)) P := by
  obtain ⟨Dl, hDl, hdvd⟩ := diag_barred hp hM hxY hxp hxM
  exact pcomp_of_barred_component hp (inf_le_left.trans (closureIn_zpowers_le hM hxY)) hDl hdvd

end Barred

end S12

end CFSG.LocalAnalysis.GLTheoremA
