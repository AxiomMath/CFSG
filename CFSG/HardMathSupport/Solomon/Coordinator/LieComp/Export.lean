module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Interface
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md42047359a2a

theorem mem_center_of_commutator_mem_center {H : Type*} [Group H]
    (hH : commutator H = ⊤) {x : H}
    (hx : ∀ y : H, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center H) : x ∈ Subgroup.center H := by
  let φ : H →* Subgroup.center H :=
    { toFun := fun y => ⟨x * y * x⁻¹ * y⁻¹, hx y⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun y z => by
        apply Subtype.ext
        have hb := (Subgroup.mem_center_iff.1 (hx z)) y⁻¹
        change x * (y * z) * x⁻¹ * (y * z)⁻¹ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹)
        calc x * (y * z) * x⁻¹ * (y * z)⁻¹
            = x * y * x⁻¹ * ((x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
          _ = x * y * x⁻¹ * (y⁻¹ * (x * z * x⁻¹ * z⁻¹)) := by rw [← hb]
          _ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by group }
  have hle : commutator H ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hH] at hle
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : φ y = 1 := hle (Subgroup.mem_top y)
  have h2 := congrArg Subtype.val h1
  change x * y * x⁻¹ * y⁻¹ = 1 at h2
  calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
    _ = x * y := by rw [h2]; simp

theorem comap_center_of_surjective {H H' : Type*} [Group H] [Group H']
    (hH : commutator H = ⊤) (ψ : H →* H') (hψ : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center H) :
    (Subgroup.center H').comap ψ = Subgroup.center H := by
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · intro hx
    refine mem_center_of_commutator_mem_center hH fun y => hk ?_
    have hc : ψ y * ψ x = ψ x * ψ y := (Subgroup.mem_center_iff.1 hx) (ψ y)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hψ z
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx) y]

theorem map_center_of_surjective {H H' : Type*} [Group H] [Group H']
    (hH : commutator H = ⊤) (ψ : H →* H') (hψ : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center H) :
    (Subgroup.center H).map ψ = Subgroup.center H' := by
  rw [← comap_center_of_surjective hH ψ hψ hk, Subgroup.map_comap_eq_self_of_surjective hψ]

theorem nonempty_centralQuotient_mulEquiv {H H' : Type*} [Group H] [Group H']
    (hH : commutator H = ⊤) (ψ : H →* H') (hψ : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center H) :
    Nonempty ((H ⧸ Subgroup.center H) ≃* (H' ⧸ Subgroup.center H')) := by
  let χ : H →* H' ⧸ Subgroup.center H' := (QuotientGroup.mk' (Subgroup.center H')).comp ψ
  have hχ : Function.Surjective χ := (QuotientGroup.mk'_surjective _).comp hψ
  have hker : χ.ker = Subgroup.center H := by
    rw [← comap_center_of_surjective hH ψ hψ hk]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff (ψ x)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective χ hχ)⟩

theorem card_center_dvd_of_surjective {H H' : Type*} [Group H] [Group H'] [Finite H]
    (hH : commutator H = ⊤) (ψ : H →* H') (hψ : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center H) :
    Nat.card (Subgroup.center H') ∣ Nat.card (Subgroup.center H) := by
  rw [← map_center_of_surjective hH ψ hψ hk]
  exact Subgroup.card_map_dvd _ _

theorem isChevSimple_congr {q : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q A) :
    CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q B := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.symm.trans f⟩⟩

structure LieFactorData (q : ℕ) (X : Type) [Group X] : Prop where
  perfect : commutator X = ⊤
  chev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q (X ⧸ Subgroup.center X)
  centre : Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6)) →
    ¬ 3 ∣ Nat.card (Subgroup.center X)

theorem LieFactorData.lieCompData {q : ℕ} {X H : Type} [Group X] [Finite X] [Group H]
    (hX : LieFactorData q X) (f : X →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center X) : LieCompData q H := by
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hX.perfect f hf hk
  refine ⟨isChevSimple_congr e hX.chev, fun ⟨a⟩ h3 => hX.centre ⟨e.trans a⟩ ?_⟩
  exact h3.trans (card_center_dvd_of_surjective hX.perfect f hf hk)

structure LieCompExport (q : ℕ) {S : Type} [Group S] (β : MulAut S) : Prop where
  layer : PerfectInLayer β
  comps : ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) →
    ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
      ∃ f : X →* ↥K, Function.Surjective f ∧ f.ker ≤ Subgroup.center X
  a6 : (∃ K : Subgroup S, IsComponentOf K (fixSubgroup β) ∧
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6))) → NoThreeCover S

@[expose] def NoThreeComponents {S : Type} [Group S] (β : MulAut S) : Prop :=
  ∀ J : Subgroup S, ¬ GLAPComponent 3 (Lemma510Ns.fixSub β) J

private theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [hp] at hcomm
    exact eq_top_iff.mpr hcomm

private theorem glaPPrimeCore_le_center {S : Type} [Group S] {K : Subgroup S}
    (hK : CFSG.Open.IsQuasisimple ↥K) (hbar : CFSG.Open.IsQuasisimple (barOf 3 K)) :
    GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K := by
  rcases normal_eq_top_or_le_center hK (inferInstance : (GLAPPrimeCore 3 ↥K).Normal) with h | h
  · exfalso
    have hsub : Subsingleton (barOf 3 K) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      exact QuotientGroup.eq.2 (h ▸ Subgroup.mem_top _)
    have := hbar.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (barOf 3 K ⧸ Subgroup.center (barOf 3 K))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (congrArg _ (Subsingleton.elim a b))
  · exact h

theorem LieCompExport.lieCompData {q : ℕ} {S : Type} [Group S] [Finite S] {β : MulAut S}
    (h : LieCompExport q β) {J : Subgroup S} (hJ : GLAPComponent 3 (Lemma510Ns.fixSub β) J) :
    LieCompData q (barOf 3 J) ∧
      (Nonempty ((barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≃* alternatingGroup (Fin 6)) →
        NoThreeCover S) := by
  have hJ' : GLAPComponent 3 (fixSubgroup β) J := hJ
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ'
  have hle : J ≤ GLALayer (fixSubgroup β) := h.layer J hJ'.1 hperf
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hJ' hle
  have hbar : CFSG.Open.IsQuasisimple (barOf 3 J) :=
    isQuasisimple_quotient_of_glaPComponent hJ'
  have hO : GLAPPrimeCore 3 ↥J ≤ Subgroup.center ↥J := glaPPrimeCore_le_center hcomp.2.2 hbar
  let π : ↥J →* barOf 3 J := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker ≤ Subgroup.center ↥J := by
    rw [QuotientGroup.ker_mk']
    exact hO
  refine ⟨?_, fun ⟨a⟩ => ?_⟩
  · obtain ⟨X, _, _, hX, f, hf, hfk⟩ := h.comps J hcomp
    have hk : (π.comp f).ker ≤ Subgroup.center X := by
      intro x hx
      have h1 : f x ∈ Subgroup.center ↥J := hπk hx
      have h2 : x ∈ (Subgroup.center ↥J).comap f := h1
      rwa [comap_center_of_surjective hX.perfect f hf hfk] at h2
    exact hX.lieCompData (π.comp f) (hπ.comp hf) hk
  · obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hcomp.2.2.1 π hπ hπk
    exact h.a6 ⟨J, hcomp, ⟨e.trans a⟩⟩

theorem NoThreeCover.of_mulEquiv {S G : Type} [Group S] [Group G] (e : S ≃* G)
    (h : NoThreeCover G) : NoThreeCover S :=
  fun Y _ _ hY ⟨f⟩ => h Y hY ⟨f.trans e⟩

theorem LieCompExport.of_congr {q : ℕ} {S G : Type} [Group S] [Group G] (e : S ≃* G)
    {β : MulAut S} (h : LieCompExport q (MulAut.congr e β)) : LieCompExport q β := by
  have hfix : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* G) := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [mem_fixSubgroup]
    show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hmapc : ∀ {K : Subgroup S}, IsComponentOf K (fixSubgroup β) →
      IsComponentOf (K.map (e : S →* G)) (fixSubgroup (MulAut.congr e β)) := fun hK => by
    rw [hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK
  refine ⟨LieSemisimple.perfectInLayer_of_congr e β h.layer, fun K hK => ?_, fun ⟨K, hK, ⟨a⟩⟩ => ?_⟩
  · obtain ⟨X, _, _, hX, f, hf, hfk⟩ := h.comps _ (hmapc hK)
    let g : ↥(K.map (e : S →* G)) ≃* ↥K :=
      (K.equivMapOfInjective (e : S →* G) e.injective).symm
    refine ⟨X, inferInstance, inferInstance, hX, (g : _ →* ↥K).comp f, g.surjective.comp hf, ?_⟩
    intro x hx
    apply hfk
    rw [MonoidHom.mem_ker] at hx ⊢
    apply g.injective
    rw [map_one]
    exact hx
  · let g : ↥K ≃* ↥(K.map (e : S →* G)) := K.equivMapOfInjective (e : S →* G) e.injective
    have hZ : (Subgroup.center ↥K).map (g : ↥K →* _) = Subgroup.center ↥(K.map (e : S →* G)) :=
      Subgroup.map_center_eq g
    let g' : (↥K ⧸ Subgroup.center ↥K) ≃*
        (↥(K.map (e : S →* G)) ⧸ Subgroup.center ↥(K.map (e : S →* G))) :=
      QuotientGroup.congr _ _ g hZ
    exact NoThreeCover.of_mulEquiv e (h.a6 ⟨_, hmapc hK, ⟨g'.symm.trans a⟩⟩)

private theorem eq_bot_or_top_of_isSubnormal {S : Type*} [Group S] [IsSimpleGroup S]
    {L : Subgroup S} (h : IsSubnormal L ⊤) : L = ⊥ ∨ L = ⊤ := by
  suffices ∀ M K : Subgroup S, IsSubnormal M K → K = ⊤ → M = ⊥ ∨ M = ⊤ from this L ⊤ h rfl
  intro M K hMK
  induction hMK with
  | refl => intro hK; exact Or.inr hK
  | @step H M K hle hnormal _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · left
      exact le_bot_iff.1 (hM ▸ hle)
    · subst hM
      have hN : H.Normal := by
        rw [Subgroup.normal_subgroupOf_iff hle] at hnormal
        exact ⟨fun x hx g => hnormal x g hx (Subgroup.mem_top g)⟩
      haveI := hN
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

theorem lieCompExport_one {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (hS6 : IsEmpty (S ≃* alternatingGroup (Fin 6))) :
    LieCompExport (lieIndexChar idx.1) (1 : MulAut S) := by
  obtain ⟨e⟩ := he
  have hfix : fixSubgroup (1 : MulAut S) = ⊤ := by
    ext x
    simp [mem_fixSubgroup]
  have hZ : Subgroup.center S = ⊥ := b3Lie_center_eq_bot hna
  have hq := b3Lie_isQuasisimple_of_simple hna
  let eZ : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hK : ∀ K : Subgroup S, IsComponentOf K (fixSubgroup (1 : MulAut S)) → K = ⊤ := by
    intro K hK
    rw [hfix] at hK
    rcases eq_bot_or_top_of_isSubnormal hK.2.1 with h | h
    · exfalso
      subst h
      have := hK.2.2.2.toNontrivial
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(⊥ : Subgroup S) ⧸ Subgroup.center ↥(⊥ : Subgroup S))
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (congrArg _ (Subsingleton.elim a b))
    · exact h
  refine ⟨?_, fun K hKc => ?_, fun ⟨K, hKc, ⟨a⟩⟩ => ?_⟩
  · intro P _ hP
    rw [hfix]
    refine le_trans le_top (le_sSup ?_)
    exact ⟨le_rfl, IsSubnormal.refl _,
      LieSemisimple.open_isQuasisimple
        (LieSemisimple.isQuasisimple_of_isSimpleGroup
          ((Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).isSimpleGroup_congr.2 inferInstance)
          (by
            obtain ⟨a, b, hab⟩ := hna
            exact ⟨⟨a, Subgroup.mem_top a⟩, ⟨b, Subgroup.mem_top b⟩,
              fun h => hab (congrArg Subtype.val h)⟩))⟩
  · obtain rfl := hK K hKc
    refine ⟨S, inferInstance, inferInstance, ⟨hq.1, ?_, ?_⟩,
      (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).symm.toMonoidHom,
      (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).symm.surjective, ?_⟩
    · refine Or.inl ⟨TauCeti.CFSGIndex.lie idx, ?_, ⟨eZ.trans e⟩⟩
      show idx.1.characteristic = lieIndexChar idx.1
      cases idx.1 <;> simp [lieIndexChar]
    · intro _
      rw [hZ, Subgroup.card_bot]
      norm_num
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      have : x = 1 := (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).symm.injective (by
        rw [map_one]
        exact hx)
      rw [this]
      exact one_mem _
  · exfalso
    obtain rfl := hK K hKc
    let g : ↥(⊤ : Subgroup S) ⧸ Subgroup.center ↥(⊤ : Subgroup S) ≃* S ⧸ Subgroup.center S :=
      QuotientGroup.congr _ _ (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S)
        (Subgroup.map_center_eq _)
    exact hS6.false ((eZ.symm.trans g.symm).trans a)

theorem lieCompOn_of_exports {F : LieFamily}
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = F →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) → ∀ β : MulAut S, β ^ 3 = 1 →
        LieCompExport (lieIndexChar idx.1) β ∨ NoThreeComponents β) :
    LieCompOn F := by
  intro S _ _ hs hna idx hF he β hβ J hJ
  rcases h S hs hna idx hF he β hβ with hE | hN
  · exact hE.lieCompData hJ
  · exact (hN J hJ).elim

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
