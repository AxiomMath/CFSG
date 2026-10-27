module

public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Quotient
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LocalAnalysis.ComponentClassification.TBLitSLLift

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open CFSG Subgroup CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement MatrixGroups

theorem exists_sl_lift_of_split {Q B : Type} [Group Q] [Group B] [Finite Q] (σ : Q →* B)
    (hker : σ.ker ≤ center Q) (hker2 : IsPGroup 2 σ.ker) {S : Subgroup B} (hSr : S ≤ σ.range)
    {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) (h4 : 4 ≤ Nat.card F)
    (eS : S ≃* SL(2, F)) :
    ⁅S.comap σ, S.comap σ⁆.map σ = S ∧ ∀ x ∈ ⁅S.comap σ, S.comap σ⁆, σ x = 1 → x = 1 := by
  have hSLp : Group.IsPerfect SL(2, F) := CatalogueBGeneralLinear.specialLinear_perfect 2 F
    le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  have hS : ⁅S, S⁆ = S := by
    have : Group.IsPerfect S := Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom)
      eS.symm.surjective
    exact Subgroup.isPerfect_iff.mp this
  set T₁ := S.comap σ with hT₁
  set T := ⁅T₁, T₁⁆ with hT
  have hT₁S : T₁.map σ = S := map_comap_eq_self hSr
  have hTS : T.map σ = S := by rw [hT, map_commutator, hT₁S, hS]
  refine ⟨hTS, ?_⟩
  have hdec : ∀ x ∈ T₁, ∃ t ∈ T, ∃ z ∈ center Q, x = t * z := by
    intro x hx
    have hx' : σ x ∈ T.map σ := by
      rw [hTS]
      exact hx
    obtain ⟨t, ht, htx⟩ := hx'
    refine ⟨t, ht, t⁻¹ * x, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, htx, inv_mul_cancel]
  have hTT : ⁅T, T⁆ = T := by
    refine le_antisymm (commutator_self_le T) ?_
    change ⁅T₁, T₁⁆ ≤ ⁅T, T⁆
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨t, ht, z, hz, rfl⟩ := hdec x hx
    obtain ⟨t', ht', z', hz', rfl⟩ := hdec y hy
    rw [commutatorElement_mul_center hz hz']
    exact commutator_mem_commutator ht ht'
  have hTp : Group.IsPerfect T := Subgroup.isPerfect_iff.mpr hTT
  have hφmem : ∀ x : T, σ x ∈ S := fun x => by
    rw [← hTS]
    exact mem_map_of_mem σ x.2
  let π : T →* SL(2, F) := eS.toMonoidHom.comp ((σ.comp T.subtype).codRestrict S hφmem)
  have hπone : ∀ x : T, π x = 1 ↔ σ x = 1 := by
    intro x
    change eS ⟨σ x, hφmem x⟩ = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨⟨s, hs⟩, rfl⟩ := eS.surjective g
    rw [← hTS] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    exact ⟨⟨x, hx⟩, rfl⟩
  have hπker : π.ker ≤ center T := by
    intro x hx
    have h2 : (x : Q) ∈ center Q := hker (MonoidHom.mem_ker.mpr ((hπone x).mp hx))
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp h2 g)
  have hπ2 : IsPGroup 2 π.ker := by
    intro x
    obtain ⟨k, hk⟩ := hker2 ⟨(x : T), MonoidHom.mem_ker.mpr ((hπone x).mp x.2)⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : σ.ker => ((y : Q))) hk
    simpa using this
  obtain ⟨τ, hτ, -, e, he⟩ := CFSG.LieType.Steinberg.sl_central_two_extension_splitting 1 hF hπ
    hπker hπ2
  have hkerbot : ∀ a : π.ker, a = 1 := by
    have hcomm : ∀ a b : π.ker, a * b = b * a := fun a b =>
      Subtype.ext (mem_center_iff.mp (hπker a.2) b).symm
    let f : T →* π.ker := (MonoidHom.fst π.ker τ.range).comp e.symm.toMonoidHom
    have hk : ⁅(⊤ : Subgroup T), ⊤⁆ ≤ f.ker := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    have htop : ⁅(⊤ : Subgroup T), ⊤⁆ = ⊤ := hTp.commutator_eq_top
    intro a
    have h1 : e.symm (a : T) = (a, 1) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply, he]
      simp
    have h2 : f (a : T) = 1 := MonoidHom.mem_ker.mp (hk (by rw [htop]; exact mem_top _))
    change (e.symm (a : T)).1 = 1 at h2
    rw [h1] at h2
    exact h2
  intro x hx h1
  have h2 : (⟨x, hx⟩ : T) ∈ π.ker := MonoidHom.mem_ker.mpr ((hπone ⟨x, hx⟩).mpr h1)
  have h3 := hkerbot ⟨_, h2⟩
  exact congrArg (fun y : π.ker => ((y : T) : Q)) h3

section Setting

variable {J : Type} [Group J] (K : Subgroup J) [K.Normal]

@[expose] def zStarEquiv :
    K ⧸ centralPreimage (pPrimeCore 2 K) ≃*
      (K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K) :=
  (QuotientGroup.quotientQuotientEquivQuotient (pPrimeCore 2 K)
    (centralPreimage (pPrimeCore 2 K)) (le_centralPreimage _)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _))

omit [K.Normal] in
theorem center_zStar_eq_bot (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K)) :
    center (K ⧸ centralPreimage (pPrimeCore 2 K)) = ⊥ := by
  have h := QuasithinUnique.Ch1.center_quotient_eq_bot hq
  rw [eq_bot_iff] at h ⊢
  intro x hx
  have hx' : zStarEquiv K x ∈ center ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := (zStarEquiv K).surjective y
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx y']
  have := h hx'
  rw [mem_bot, MulEquiv.map_eq_one_iff] at this
  rw [this]
  exact one_mem _

abbrev rhoZ : J →* MulAut (K ⧸ centralPreimage (pPrimeCore 2 K)) :=
  conjQuotAction K (centralPreimage (pPrimeCore 2 K))

abbrev phiO : J →* MulAut (K ⧸ pPrimeCore 2 K) :=
  conjQuotAction K (pPrimeCore 2 K)

theorem pPrimeCore_le_ker : pPrimeCore 2 K ≤ ((rhoZ K).rangeRestrict.comp K.subtype).ker := by
  intro r hr
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  change rhoZ K (r : J) = 1
  rw [conjQuotAction_coe]
  have h1 : (r : K ⧸ centralPreimage (pPrimeCore 2 K)) = 1 :=
    (QuotientGroup.eq_one_iff r).2 (le_centralPreimage _ hr)
  rw [h1, map_one]

@[expose] def liftHom : K ⧸ pPrimeCore 2 K →* (rhoZ K).range :=
  QuotientGroup.lift _ ((rhoZ K).rangeRestrict.comp K.subtype) (pPrimeCore_le_ker K)

theorem liftHom_mk (k : K) :
    liftHom K (k : K ⧸ pPrimeCore 2 K) = (rhoZ K).rangeRestrict (k : J) := rfl

theorem liftHom_surjective_inner {g : (rhoZ K).range}
    (hg : ∃ k : K, (rhoZ K).rangeRestrict (k : J) = g) : g ∈ (liftHom K).range := by
  obtain ⟨k, rfl⟩ := hg
  exact ⟨_, liftHom_mk K k⟩

theorem liftHom_conj (g : J) (x : K ⧸ pPrimeCore 2 K) :
    liftHom K (phiO K g x) =
      (rhoZ K).rangeRestrict g * liftHom K x * ((rhoZ K).rangeRestrict g)⁻¹ := by
  induction x using QuotientGroup.induction_on with
  | H k =>
    have hl : g * (k : J) * g⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem _ k.2 g
    rw [conjQuotAction_mk' g k hl, liftHom_mk, liftHom_mk]
    change (rhoZ K).rangeRestrict (g * k * g⁻¹) = _
    rw [map_mul, map_mul, map_inv]

theorem ker_liftHom (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K)) :
    (liftHom K).ker = center (K ⧸ pPrimeCore 2 K) := by
  have hZ := center_zStar_eq_bot K hq
  ext x
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [MonoidHom.mem_ker, liftHom_mk]
    constructor
    · intro h
      have h2 : rhoZ K (k : J) = 1 := congrArg Subtype.val h
      exact (conjQuotAction_coe_eq_one_iff hZ k).mp h2
    · intro h
      apply Subtype.ext
      exact (conjQuotAction_coe_eq_one_iff hZ k).mpr h

omit [K.Normal] in
theorem isPGroup_center [Finite K] : IsPGroup 2 (center (K ⧸ pPrimeCore 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact center_isPGroup_two_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)

theorem phiO_eq_one_of_rhoZ_eq_one (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K)) {a : J}
    (ha : rhoZ K a = 1) : phiO K a = 1 := by
  have : Group.IsPerfect (K ⧸ pPrimeCore 2 K) := hq.1
  rw [conjQuotAction_eq_one_iff] at ha
  apply CentralCover.eq_one_of_forall_inv_mul_mem_center
  intro x
  induction x using QuotientGroup.induction_on with
  | H k =>
    obtain ⟨z, hz, hzk⟩ := ha (k⁻¹ : K) (inv_mem k.2)
    have hl : a * (k : J) * a⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem _ k.2 a
    rw [conjQuotAction_mk' a k hl]
    have hval : ((k : K)⁻¹ * ⟨a * (k : J) * a⁻¹, hl⟩ : K) = z := by
      apply Subtype.ext
      have hzk' : (z : J) = ⁅((k⁻¹ : K) : J), a⁆ := hzk
      rw [hzk']
      change ((k : J))⁻¹ * (a * (k : J) * a⁻¹) = ⁅((k : J))⁻¹, a⁆
      rw [commutatorElement_def]
      group
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, hval]
    exact hz

theorem conjQuotAction_eq_of_rangeRestrict_eq (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
    {g y : J} (h : (rhoZ K).rangeRestrict g = (rhoZ K).rangeRestrict y) :
    phiO K g = phiO K y := by
  have h1 : rhoZ K (y⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact (congrArg Subtype.val h).symm
  have h2 := phiO_eq_one_of_rhoZ_eq_one K hq h1
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

theorem rangeRestrict_mem_closure {t : J} {Y : Subgroup J} {g : J}
    (hg : g ∈ closure (insert t (Y : Set J))) :
    (rhoZ K).rangeRestrict g ∈
      closure (insert ((rhoZ K).rangeRestrict t) ((Y.map (rhoZ K).rangeRestrict : Subgroup _) :
        Set (rhoZ K).range)) := by
  have h1 : (closure (insert t (Y : Set J))).map (rhoZ K).rangeRestrict =
      closure ((rhoZ K).rangeRestrict '' insert t (Y : Set J)) := MonoidHom.map_closure _ _
  have h2 : (rhoZ K).rangeRestrict '' insert t (Y : Set J) =
      insert ((rhoZ K).rangeRestrict t) ((Y.map (rhoZ K).rangeRestrict : Subgroup _) :
        Set (rhoZ K).range) := by
    rw [Set.image_insert_eq, coe_map]
  rw [← h2, ← h1]
  exact mem_map_of_mem _ hg

theorem actsProperlyVia_lift (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K)) {t : J}
    {Y : Subgroup J} {S : Subgroup (rhoZ K).range}
    (hTS : ⁅S.comap (liftHom K), S.comap (liftHom K)⁆.map (liftHom K) = S)
    (hprop : ActsProperly ((rhoZ K).rangeRestrict t) (Y.map (rhoZ K).rangeRestrict) S ⊥) :
    ActsProperlyVia (phiO K) t Y ⁅S.comap (liftHom K), S.comap (liftHom K)⁆ ⊥ := by
  set σ := liftHom K with hσ
  set T := ⁅S.comap σ, S.comap σ⁆ with hT
  have hle : ∀ g : J, (rhoZ K).rangeRestrict g ∈ normalizer (S : Set (rhoZ K).range) →
      T.map (phiO K g).toMonoidHom ≤ T := by
    intro g hg
    have h1 : (S.comap σ).map (phiO K g).toMonoidHom ≤ S.comap σ := by
      rintro _ ⟨y, hy, rfl⟩
      change σ (phiO K g y) ∈ S
      rw [liftHom_conj]
      exact (mem_normalizer_iff.mp hg _).mp hy
    rw [hT, map_commutator]
    exact commutator_mono h1 h1
  refine ⟨fun g hg => ⟨?_, by rw [Subgroup.map_bot]⟩, fun g hg hfix => ?_, ?_⟩
  · have hgN := hprop.1 (rangeRestrict_mem_closure K hg)
    have hgiN := hprop.1 (rangeRestrict_mem_closure K (inv_mem hg))
    refine le_antisymm (hle g (mem_inf.mp hgN).1) ?_
    intro x hx
    have h1 : phiO K g⁻¹ x ∈ T := hle g⁻¹ (mem_inf.mp hgiN).1 (mem_map_of_mem _ hx)
    refine ⟨phiO K g⁻¹ x, h1, ?_⟩
    change phiO K g (phiO K g⁻¹ x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  ·
    have hcent : ∀ s ∈ S, ⁅s, (rhoZ K).rangeRestrict g⁆ ∈ (⊥ : Subgroup (rhoZ K).range) := by
      intro s hs
      rw [← hTS] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      have h1 := liftHom_conj K g x
      have hx1 : phiO K g x = x := by
        have := hfix x hx
        rwa [mem_bot, mul_inv_eq_one] at this
      rw [hx1] at h1
      rw [mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      calc σ x * (rhoZ K).rangeRestrict g
          = ((rhoZ K).rangeRestrict g * σ x * ((rhoZ K).rangeRestrict g)⁻¹) *
              (rhoZ K).rangeRestrict g := by rw [← h1]
        _ = (rhoZ K).rangeRestrict g * σ x := by group
    obtain ⟨y, hy, hyg⟩ := hprop.2.1 _ (rangeRestrict_mem_closure K hg) hcent
    exact ⟨y, hy, conjQuotAction_eq_of_rangeRestrict_eq K hq hyg.symm⟩
  · obtain ⟨_, ⟨y, hy, rfl⟩, s, hs, hse⟩ := hprop.2.2
    refine ⟨y, hy, ?_⟩
    rw [← hTS] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    refine ⟨x, hx, fun h => hse ?_⟩
    rw [mem_bot, mul_inv_eq_one] at h
    have h1 := liftHom_conj K y x
    rw [h] at h1
    rw [mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    calc σ x * (rhoZ K).rangeRestrict y
        = ((rhoZ K).rangeRestrict y * σ x * ((rhoZ K).rangeRestrict y)⁻¹) *
            (rhoZ K).rangeRestrict y := by rw [← h1]
      _ = (rhoZ K).rangeRestrict y * σ x := by group

end Setting

end CFSG.ComponentClassification.Burgoyne.B
