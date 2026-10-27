module

public import CFSG.CGT.PushingUpLit.CGT6X.End4Mod
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

open scoped commutatorElement

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6X.End3
  CFSG.CGT.PushingUpLit.BHS6

variable {V : Type} [CommGroup V] {G T Y : Subgroup (MulAut V)}

@[expose] def layerMk (G Y : Subgroup (MulAut V)) :
    ↥(CGT6.conjClosure Y G) →* LayerQ G Y :=
  QuotientGroup.mk' (Subgroup.center ↥(CGT6.conjClosure Y G))

theorem layerMk_surjective : Function.Surjective (layerMk G Y) :=
  QuotientGroup.mk'_surjective _

theorem layerMk_eq_one_iff (l : ↥(CGT6.conjClosure Y G)) :
    layerMk G Y l = 1 ↔ l ∈ Subgroup.center ↥(CGT6.conjClosure Y G) :=
  QuotientGroup.eq_one_iff l

@[expose] noncomputable def piHom {m : ℕ} (e : LayerQ G Y ≃* alternatingGroup (Fin m)) :
    ↥(CGT6.conjClosure Y G) →* alternatingGroup (Fin m) :=
  (e : LayerQ G Y →* alternatingGroup (Fin m)).comp (layerMk G Y)

theorem piHom_surjective {m : ℕ} (e : LayerQ G Y ≃* alternatingGroup (Fin m)) :
    Function.Surjective (piHom e) :=
  e.surjective.comp layerMk_surjective

theorem piHom_eq_one_iff {m : ℕ} (e : LayerQ G Y ≃* alternatingGroup (Fin m))
    (l : ↥(CGT6.conjClosure Y G)) :
    piHom e l = 1 ↔ l ∈ Subgroup.center ↥(CGT6.conjClosure Y G) := by
  show e (layerMk G Y l) = 1 ↔ _
  rw [map_eq_one_iff e e.injective]
  exact layerMk_eq_one_iff l

theorem ker_piHom {m : ℕ} (e : LayerQ G Y ≃* alternatingGroup (Fin m)) :
    (piHom e).ker = Subgroup.center ↥(CGT6.conjClosure Y G) := by
  ext l
  rw [MonoidHom.mem_ker]
  exact piHom_eq_one_iff e l

theorem exists_sigma {m : ℕ} (hm : 5 ≤ m) (hm6 : m ≠ 6)
    (e : LayerQ G Y ≃* alternatingGroup (Fin m)) {t : MulAut V} (htG : t ∈ G) :
    ∃ σ : Equiv.Perm (Fin m), ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
      ((piHom e ⟨t * l * t⁻¹, conj_mem_conjClosure htG hl⟩ : alternatingGroup (Fin m)) :
        Equiv.Perm (Fin m)) = σ * ((piHom e ⟨l, hl⟩ : alternatingGroup (Fin m)) :
          Equiv.Perm (Fin m)) * σ⁻¹ := by
  have hN := normalizer_conjClosure (Y := Y) (G := G) htG
  let φ : MulAut (LayerQ G Y) :=
    K7a.centerAutHom ↥(CGT6.conjClosure Y G) (conjOn (CGT6.conjClosure Y G) t hN)
  let ψ : MulAut (alternatingGroup (Fin m)) := MulAut.congr e φ
  obtain ⟨σ, hσ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm hm6).2 ψ
  refine ⟨σ, fun l hl => ?_⟩
  have h1 : piHom e ⟨t * l * t⁻¹, conj_mem_conjClosure htG hl⟩ = ψ (piHom e ⟨l, hl⟩) := by
    show e (layerMk G Y ⟨t * l * t⁻¹, conj_mem_conjClosure htG hl⟩) =
      MulAut.congr e φ (e (layerMk G Y ⟨l, hl⟩))
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  rw [h1, ← hσ]
  rfl

section Sigma

variable [Finite V]

theorem sigma_ne_one (cfg : EndCfg4 G T Y) {m : ℕ} (e : LayerQ G Y ≃* alternatingGroup (Fin m))
    {t : MulAut V} (htG : t ∈ G) (ht2 : t * t = 1) (ht1 : t ≠ 1) {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
      ((piHom e ⟨t * l * t⁻¹, conj_mem_conjClosure htG hl⟩ : alternatingGroup (Fin m)) :
        Equiv.Perm (Fin m)) = σ * ((piHom e ⟨l, hl⟩ : alternatingGroup (Fin m)) :
          Equiv.Perm (Fin m)) * σ⁻¹) : σ ≠ 1 := by
  intro hσ1
  have hN := normalizer_conjClosure (Y := Y) (G := G) htG
  have hperf : Group.IsPerfect ↥(CGT6.conjClosure Y G) := ⟨cfg.quasi.1⟩
  have hcentral := centralizes_of_central_conj (L := CGT6.conjClosure Y G) hN (fun l => by
    refine ⟨l⁻¹ * ⟨t * l * t⁻¹, conj_mem_conjClosure htG l.2⟩, ?_, ?_⟩
    · rw [← ker_piHom e, MonoidHom.mem_ker, map_mul, map_inv]
      have := hσ l l.2
      rw [hσ1] at this
      have h2 : piHom e ⟨t * l * t⁻¹, conj_mem_conjClosure htG l.2⟩ = piHom e l := by
        apply Subtype.ext
        simpa using this
      rw [h2]
      exact inv_mul_cancel _
    · simp)
  have htL : t ∈ CGT6.conjClosure Y G := centralizer_le_of_cfg cfg t htG hcentral
  have hcen : (⟨t, htL⟩ : ↥(CGT6.conjClosure Y G)) ∈
      Subgroup.center ↥(CGT6.conjClosure Y G) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcentral g g.2).symm
  have h1 : (⟨⟨t, htL⟩, hcen⟩ : ↥(Subgroup.center ↥(CGT6.conjClosure Y G))) ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp [pow_two, ht2]
  have := eq_one_of_sq_eq_one_odd (K := Subgroup.center ↥(CGT6.conjClosure Y G)) cfg.oddZ h1
  have h3 := congrArg (fun z : ↥(Subgroup.center ↥(CGT6.conjClosure Y G)) =>
    (((z : ↥(CGT6.conjClosure Y G))) : MulAut V)) this
  exact ht1 (by simpa using h3)

omit [Finite V] in
theorem sigma_sq {m : ℕ} (hm : 5 ≤ m) (e : LayerQ G Y ≃* alternatingGroup (Fin m))
    {t : MulAut V} (htG : t ∈ G) (ht2 : t * t = 1) {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
      ((piHom e ⟨t * l * t⁻¹, conj_mem_conjClosure htG hl⟩ : alternatingGroup (Fin m)) :
        Equiv.Perm (Fin m)) = σ * ((piHom e ⟨l, hl⟩ : alternatingGroup (Fin m)) :
          Equiv.Perm (Fin m)) * σ⁻¹) : σ * σ = 1 := by
  have key : ∀ a : alternatingGroup (Fin m),
      σ * σ * (a : Equiv.Perm (Fin m)) * (σ * σ)⁻¹ = (a : Equiv.Perm (Fin m)) := by
    intro a
    obtain ⟨l, rfl⟩ := piHom_surjective e a
    have hl1 := conj_mem_conjClosure (Y := Y) htG l.2
    have h1 := hσ _ l.2
    have h2 := hσ _ hl1
    have e1 : (⟨t * (t * (l : MulAut V) * t⁻¹) * t⁻¹, conj_mem_conjClosure htG hl1⟩ :
        ↥(CGT6.conjClosure Y G)) = l := by
      apply Subtype.ext
      show t * (t * (l : MulAut V) * t⁻¹) * t⁻¹ = l
      calc t * (t * (l : MulAut V) * t⁻¹) * t⁻¹ = (t * t) * (l : MulAut V) * (t * t)⁻¹ := by group
        _ = l := by rw [ht2]; simp
    rw [e1] at h2
    calc σ * σ * ((piHom e l : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) * (σ * σ)⁻¹
        = σ * (σ * ((piHom e l : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) * σ⁻¹) * σ⁻¹ := by
          group
      _ = σ * ((piHom e ⟨t * (l : MulAut V) * t⁻¹, hl1⟩ : alternatingGroup (Fin m)) :
            Equiv.Perm (Fin m)) * σ⁻¹ := by rw [← h1]
      _ = ((piHom e l : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) := h2.symm
  have hinj := GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup m (by omega)
  have hc : ∀ (g : Equiv.Perm (Fin m)) (a : alternatingGroup (Fin m)),
      ((MulAut.conjNormal (H := alternatingGroup (Fin m)) g a : alternatingGroup (Fin m)) :
        Equiv.Perm (Fin m)) = g * a * g⁻¹ := fun g a => rfl
  have : MulAut.conjNormal (H := alternatingGroup (Fin m)) (σ * σ) = MulAut.conjNormal 1 := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [hc, map_one, MulAut.one_apply, key a]
  have h3 := hinj this
  exact h3

theorem sigma_comm (cfg : EndCfg4 G T Y) {m : ℕ} (e : LayerQ G Y ≃* alternatingGroup (Fin m))
    {t : MulAut V} (htT : t ∈ T) {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
      ((piHom e ⟨t * l * t⁻¹, conj_mem_conjClosure (cfg.adm.hTG htT) hl⟩ :
        alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) = σ * ((piHom e ⟨l, hl⟩ :
          alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) * σ⁻¹) :
    ∀ h ∈ (Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e),
      σ * (h : Equiv.Perm (Fin m)) = (h : Equiv.Perm (Fin m)) * σ := by
  rintro _ ⟨y, hy, rfl⟩
  have hyY : (y : MulAut V) ∈ Y := hy
  have hty : t * (y : MulAut V) * t⁻¹ = y := by
    rw [cfg_comm_ty cfg htT hyY]
    group
  have h1 := hσ y y.2
  have e1 : (⟨t * (y : MulAut V) * t⁻¹, conj_mem_conjClosure (cfg.adm.hTG htT) y.2⟩ :
      ↥(CGT6.conjClosure Y G)) = y := Subtype.ext hty
  rw [e1] at h1
  have h2 : ((piHom e y : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) * σ =
      σ * ((piHom e y : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) := by
    calc ((piHom e y : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) * σ
        = (σ * ((piHom e y : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) * σ⁻¹) * σ := by
          rw [← h1]
      _ = σ * ((piHom e y : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) := by group
  exact h2.symm

omit [Finite V] in
theorem piHom_subgroupMap_injective (hY2 : YSL Y 2) {m : ℕ}
    (e : LayerQ G Y ≃* alternatingGroup (Fin m)) :
    Function.Injective ((piHom e).subgroupMap (Y.subgroupOf (CGT6.conjClosure Y G))) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : piHom e (y : ↥(CGT6.conjClosure Y G)) = 1 := congrArg Subtype.val hy
  rw [piHom_eq_one_iff, Subgroup.mem_center_iff] at h1
  have hyY : ((y : ↥(CGT6.conjClosure Y G)) : MulAut V) ∈ Y := y.2
  have hc : (⟨(y : ↥(CGT6.conjClosure Y G)), hyY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg Subtype.val (h1 ⟨g, CGT6.le_conjClosure g.2⟩)
    exact Subtype.ext h2
  rw [YSL.center_eq_bot hY2] at hc
  have h3 := congrArg Subtype.val (Subgroup.mem_bot.mp hc)
  exact Subtype.ext (Subtype.ext (by simpa using h3))

omit [Finite V] in
@[expose] noncomputable def piYEquiv (hY2 : YSL Y 2) {m : ℕ}
    (e : LayerQ G Y ≃* alternatingGroup (Fin m)) :
    ↥((Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e)) ≃* ↥Y :=
  (MulEquiv.ofBijective ((piHom e).subgroupMap (Y.subgroupOf (CGT6.conjClosure Y G)))
    ⟨piHom_subgroupMap_injective hY2 e,
      (piHom e).subgroupMap_surjective _⟩).symm.trans
    (Subgroup.subgroupOfEquivOfLe CGT6.le_conjClosure)

omit [Finite V] in
theorem piYEquiv_symm_coe (hY2 : YSL Y 2) {m : ℕ} (e : LayerQ G Y ≃* alternatingGroup (Fin m))
    (y : ↥Y) :
    (((piYEquiv hY2 e).symm y :
      ↥((Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e))) : alternatingGroup (Fin m)) =
      piHom e ⟨y, CGT6.le_conjClosure y.2⟩ := rfl

omit [Finite V] in
theorem card_piY (hY2 : YSL Y 2) {m : ℕ} (e : LayerQ G Y ≃* alternatingGroup (Fin m)) :
    Nat.card ↥((Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e)) = 60 := by
  rw [Nat.card_congr (piYEquiv hY2 e).toEquiv, YSL.card_eq (by norm_num) hY2]
  norm_num

omit [Finite V] in
theorem isSimpleGroup_piY (hY2 : YSL Y 2) {m : ℕ} (e : LayerQ G Y ≃* alternatingGroup (Fin m)) :
    IsSimpleGroup ↥((Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e)) := by
  obtain ⟨e1⟩ := hY2
  obtain ⟨e2⟩ := CFSG.CGT.PushingUpLit.CGT6.sl2_four_equiv_alt5
  have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact (MulEquiv.isSimpleGroup_congr ((piYEquiv ⟨e1⟩ e).trans (e1.trans e2))).mpr this

end Sigma

end CFSG.CGT.PushingUpLit.CGT6X.End4
