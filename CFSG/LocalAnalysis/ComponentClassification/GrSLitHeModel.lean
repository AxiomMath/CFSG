module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeFacts
public import CFSG.Sporadic.HeldB.AutModel

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

section Model

variable {X : Type} [Group X] (L : Subgroup X)

noncomputable def coreQuotAction :
    ↥(normalizer (L : Set X)) →* MulAut (L ⧸ pPrimeCore 2 ↥L) :=
  Semidihedral.Principal.CoprimeFixedPoint.quotientAction
    (LocalAnalysis.ComponentInitial.normalizerConjHom L) (pPrimeCore 2 ↥L) fun a n hn => by
      have h := Subgroup.characteristic_iff_map_eq.mp
        (inferInstance : (pPrimeCore 2 ↥L).Characteristic)
        (LocalAnalysis.ComponentInitial.normalizerConjHom L a)
      rw [← h]
      exact ⟨n, hn, rfl⟩

variable {L}

noncomputable def heModelL (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He) :
    ↥L →* ↥heP :=
  (e.trans heEquivP).toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L))

noncomputable def heModelN (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He) :
    ↥(normalizer (L : Set X)) →* ↥heAutGroup :=
  (MulEquiv.ofBijective heConjR ctbh_full_automorphism_permutation_model.1).symm.toMonoidHom.comp
    ((MulAut.congr (e.trans heEquivP)).toMonoidHom.comp (coreQuotAction L))

variable (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)

theorem heModelL_surjective : Function.Surjective (heModelL e) := by
  intro y
  obtain ⟨q, hq⟩ := (e.trans heEquivP).surjective y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) q
  exact ⟨l, hq⟩

theorem heModelL_eq_one_iff (l : ↥L) : heModelL e l = 1 ↔ l ∈ pPrimeCore 2 ↥L := by
  rw [heModelL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem heConjR_heModelN (n : ↥(normalizer (L : Set X))) :
    heConjR (heModelN e n) = MulAut.congr (e.trans heEquivP) (coreQuotAction L n) := by
  rw [heModelN, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact MulEquiv.apply_symm_apply (MulEquiv.ofBijective heConjR _) _

theorem heModelL_conj (n : ↥(normalizer (L : Set X))) (l : ↥L) :
    ((heModelL e (LocalAnalysis.ComponentInitial.normalizerConjHom L n l) : heP) :
        Equiv.Perm (Fin 8330)) =
      (heModelN e n : Equiv.Perm (Fin 8330)) * (heModelL e l : Equiv.Perm (Fin 8330)) *
        (heModelN e n : Equiv.Perm (Fin 8330))⁻¹ := by
  have h := congrArg (fun α : MulAut heP => ((α (heModelL e l) : heP) : Equiv.Perm (Fin 8330)))
    (heConjR_heModelN e n)
  simp only [heConjR_apply, InvMemClass.coe_inv] at h
  rw [h, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply]
  have h1 : (e.trans heEquivP).symm (heModelL e l) = ((l : ↥L) : L ⧸ pPrimeCore 2 ↥L) :=
    MulEquiv.symm_apply_apply (e.trans heEquivP) _
  have h2 : heModelL e (LocalAnalysis.ComponentInitial.normalizerConjHom L n l) =
      heEquivP (e ((LocalAnalysis.ComponentInitial.normalizerConjHom L n l : ↥L) :
        L ⧸ pPrimeCore 2 ↥L)) := rfl
  rw [h1, h2]
  rfl

theorem heModelN_of_mem (l : ↥L) :
    (heModelN e ⟨l, le_normalizer l.2⟩ : Equiv.Perm (Fin 8330)) = heModelL e l := by
  have hinj := heConjR_injective
  have key : heConjR (heModelN e ⟨l, le_normalizer l.2⟩) =
      heConjR ⟨(heModelL e l : Equiv.Perm (Fin 8330)), heP_le_heAutGroup (heModelL e l).2⟩ := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    obtain ⟨l', rfl⟩ := heModelL_surjective e g
    rw [heConjR_apply, heConjR_apply]
    simp only [InvMemClass.coe_inv]
    rw [← heModelL_conj]
    have h3 : LocalAnalysis.ComponentInitial.normalizerConjHom L ⟨l, le_normalizer l.2⟩ l' =
        l * l' * l⁻¹ := Subtype.ext rfl
    rw [h3, map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  exact congrArg Subtype.val (hinj key)

theorem heModelN_eq_one_of_forall (n : ↥(normalizer (L : Set X)))
    (h : ∀ l : ↥L, heModelL e (LocalAnalysis.ComponentInitial.normalizerConjHom L n l) =
      heModelL e l) : heModelN e n = 1 := by
  apply heConjR_injective
  rw [map_one]
  refine MulEquiv.ext fun g => Subtype.ext ?_
  obtain ⟨l', rfl⟩ := heModelL_surjective e g
  rw [heConjR_apply, MulAut.one_apply]
  simp only [InvMemClass.coe_inv]
  rw [← heModelL_conj, h l']

theorem heModelN_eq_one_iff (n : ↥(normalizer (L : Set X))) :
    heModelN e n = 1 ↔ (n : X) ∈ coreActionKernel L := by
  rw [mem_coreActionKernel]
  constructor
  · intro h
    refine ⟨n.2, fun j hj => ?_⟩
    have hn' : heModelN e n⁻¹ = 1 := by rw [map_inv, h, inv_one]
    have h1 := heModelL_conj e n⁻¹ ⟨j, hj⟩
    rw [hn', OneMemClass.coe_one, one_mul, inv_one, mul_one] at h1
    have h2 : heModelL e (⟨j, hj⟩⁻¹ *
        LocalAnalysis.ComponentInitial.normalizerConjHom L n⁻¹ ⟨j, hj⟩) = 1 := by
      rw [map_mul, map_inv]
      apply Subtype.ext
      rw [Subgroup.coe_mul, InvMemClass.coe_inv, h1, inv_mul_cancel, OneMemClass.coe_one]
    rw [heModelL_eq_one_iff] at h2
    refine ⟨_, h2, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv,
      LocalAnalysis.ComponentInitial.coe_normalizerConjHom_apply, inv_inv]
    group
  · rintro ⟨-, hK⟩
    refine heModelN_eq_one_of_forall e n fun l => ?_
    set m : ↥L := LocalAnalysis.ComponentInitial.normalizerConjHom L n l with hm
    obtain ⟨o, ho, hoeq⟩ := hK m m.2
    have h1 : heModelL e o = 1 := (heModelL_eq_one_iff e o).mpr ho
    have h2 : (o : X) = (m : X)⁻¹ * l := by
      rw [Subgroup.coe_subtype] at hoeq
      rw [hoeq, hm, LocalAnalysis.ComponentInitial.coe_normalizerConjHom_apply]
      group
    have h3 : o = m⁻¹ * l := Subtype.ext (by rw [h2]; rfl)
    rw [h3, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1

theorem heModelN_mem_heP_iff (n : ↥(normalizer (L : Set X))) :
    (heModelN e n : Equiv.Perm (Fin 8330)) ∈ heP ↔ (n : X) ∈ L ⊔ coreActionKernel L := by
  constructor
  · intro h
    obtain ⟨l, hl⟩ := heModelL_surjective e ⟨_, h⟩
    have hρ : heModelN e (⟨l, le_normalizer l.2⟩⁻¹ * n) = 1 := by
      rw [map_mul, map_inv]
      apply Subtype.ext
      rw [Subgroup.coe_mul, InvMemClass.coe_inv, heModelN_of_mem, hl, inv_mul_cancel,
        OneMemClass.coe_one]
    rw [heModelN_eq_one_iff] at hρ
    have : (n : X) = l * ((⟨l, le_normalizer l.2⟩⁻¹ * n : ↥(normalizer (L : Set X))) : X) := by
      simp
    rw [this]
    exact mul_mem (mem_sup_left l.2) (mem_sup_right hρ)
  · intro h
    set H : Subgroup ↥(normalizer (L : Set X)) :=
      ((heP.subgroupOf heAutGroup).comap (heModelN e)) with hH
    have hLH : L.subgroupOf (normalizer (L : Set X)) ≤ H := by
      intro m hm
      rw [hH, mem_comap, mem_subgroupOf]
      have := heModelN_of_mem e ⟨m, hm⟩
      simp only [Subtype.coe_eta] at this
      rw [this]
      exact (heModelL e _).2
    have hKH : (coreActionKernel L).subgroupOf (normalizer (L : Set X)) ≤ H := by
      intro m hm
      rw [hH, mem_comap, (heModelN_eq_one_iff e m).mpr hm]
      exact one_mem _
    have hsup : (L ⊔ coreActionKernel L).subgroupOf (normalizer (L : Set X)) ≤ H := by
      rw [subgroupOf_sup le_normalizer (fun g hg => (mem_coreActionKernel.mp hg).1)]
      exact sup_le hLH hKH
    exact hsup h

end Model

section Wrappers

variable {X : Type} [Group X] {L : Subgroup X}
variable (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)

open Classical in
noncomputable def heL (x : X) : Equiv.Perm (Fin 8330) :=
  if h : x ∈ L then (heModelL e ⟨x, h⟩ : Equiv.Perm (Fin 8330)) else 1

open Classical in
noncomputable def heN (x : X) : Equiv.Perm (Fin 8330) :=
  if h : x ∈ normalizer (L : Set X) then (heModelN e ⟨x, h⟩ : Equiv.Perm (Fin 8330)) else 1

variable {e}

theorem heL_of_mem {x : X} (h : x ∈ L) : heL e x = heModelL e ⟨x, h⟩ := dite_eq_left h

theorem heN_of_mem {x : X} (h : x ∈ normalizer (L : Set X)) :
    heN e x = heModelN e ⟨x, h⟩ := dite_eq_left h

theorem heN_eq_heL {x : X} (h : x ∈ L) : heN e x = heL e x := by
  rw [heN_of_mem (le_normalizer h), heL_of_mem h]
  exact heModelN_of_mem e ⟨x, h⟩

theorem heL_mul {x y : X} (hx : x ∈ L) (hy : y ∈ L) : heL e (x * y) = heL e x * heL e y := by
  rw [heL_of_mem (mul_mem hx hy), heL_of_mem hx, heL_of_mem hy]
  have : (⟨x * y, mul_mem hx hy⟩ : ↥L) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, Subgroup.coe_mul]

theorem heL_inv {x : X} (hx : x ∈ L) : heL e x⁻¹ = (heL e x)⁻¹ := by
  rw [heL_of_mem (inv_mem hx), heL_of_mem hx]
  have : (⟨x⁻¹, inv_mem hx⟩ : ↥L) = (⟨x, hx⟩ : ↥L)⁻¹ := rfl
  rw [this, map_inv, InvMemClass.coe_inv]

theorem heL_one : heL e (1 : X) = 1 := by
  rw [heL_of_mem (one_mem L)]
  have : (⟨1, one_mem L⟩ : ↥L) = 1 := rfl
  rw [this, map_one, OneMemClass.coe_one]

theorem heN_mul {x y : X} (hx : x ∈ normalizer (L : Set X)) (hy : y ∈ normalizer (L : Set X)) :
    heN e (x * y) = heN e x * heN e y := by
  rw [heN_of_mem (mul_mem hx hy), heN_of_mem hx, heN_of_mem hy]
  have : (⟨x * y, mul_mem hx hy⟩ : ↥(normalizer (L : Set X))) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, Subgroup.coe_mul]

theorem heN_inv {x : X} (hx : x ∈ normalizer (L : Set X)) : heN e x⁻¹ = (heN e x)⁻¹ := by
  rw [heN_of_mem (inv_mem hx), heN_of_mem hx]
  have : (⟨x⁻¹, inv_mem hx⟩ : ↥(normalizer (L : Set X))) = (⟨x, hx⟩ : _)⁻¹ := rfl
  rw [this, map_inv, InvMemClass.coe_inv]

theorem heL_mem_heP {x : X} (hx : x ∈ L) : heL e x ∈ heP := by
  rw [heL_of_mem hx]
  exact (heModelL e _).2

theorem heN_mem {x : X} (hx : x ∈ normalizer (L : Set X)) : heN e x ∈ heAutGroup := by
  rw [heN_of_mem hx]
  exact (heModelN e _).2

theorem exists_heL_eq {y : Equiv.Perm (Fin 8330)} (hy : y ∈ heP) : ∃ x ∈ L, heL e x = y := by
  obtain ⟨l, hl⟩ := heModelL_surjective e ⟨y, hy⟩
  exact ⟨l, l.2, by rw [heL_of_mem l.2, Subtype.coe_eta, hl]⟩

theorem heL_eq_one_iff {x : X} (hx : x ∈ L) :
    heL e x = 1 ↔ x ∈ (pPrimeCore 2 ↥L).map L.subtype := by
  rw [heL_of_mem hx]
  constructor
  · intro h
    exact ⟨⟨x, hx⟩, (heModelL_eq_one_iff e _).mp (Subtype.ext h), rfl⟩
  · rintro ⟨l, hl, rfl⟩
    have : (⟨L.subtype l, hx⟩ : ↥L) = l := rfl
    rw [this, (heModelL_eq_one_iff e _).mpr hl]
    rfl

theorem heN_eq_one_iff {x : X} (hx : x ∈ normalizer (L : Set X)) :
    heN e x = 1 ↔ x ∈ coreActionKernel L := by
  rw [heN_of_mem hx, ← heModelN_eq_one_iff e ⟨x, hx⟩]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    rw [h]
    rfl

theorem heN_mem_heP_iff {x : X} (hx : x ∈ normalizer (L : Set X)) :
    heN e x ∈ heP ↔ x ∈ L ⊔ coreActionKernel L := by
  rw [heN_of_mem hx]
  exact heModelN_mem_heP_iff e ⟨x, hx⟩

theorem heL_conj {n l : X} (hn : n ∈ normalizer (L : Set X)) (hl : l ∈ L) :
    heL e (n * l * n⁻¹) = heN e n * heL e l * (heN e n)⁻¹ := by
  have hm : n * l * n⁻¹ ∈ L := (mem_normalizer_iff.mp hn l).mp hl
  rw [heL_of_mem hm, heN_of_mem hn, heL_of_mem hl, ← heModelL_conj]
  rfl

theorem heL_injOn [Finite X] {T : Subgroup X} (hTL : T ≤ L) (hT : IsPGroup 2 T) {x y : X}
    (hx : x ∈ T) (hy : y ∈ T) (h : heL e x = heL e y) : x = y := by
  have h1 : heL e (x⁻¹ * y) = 1 := by
    rw [heL_mul (inv_mem (hTL hx)) (hTL hy), heL_inv (hTL hx), h, inv_mul_cancel]
  rw [heL_eq_one_iff (mul_mem (inv_mem (hTL hx)) (hTL hy))] at h1
  have hbot := eq_bot_of_le_two_group_of_le_odd hT
    (by rw [card_map_of_injective L.subtype_injective]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    (zpowers_le.mpr (mul_mem (inv_mem hx) hy)) (zpowers_le.mpr h1)
  have : x⁻¹ * y = 1 := by
    rw [← mem_bot, ← hbot]
    exact mem_zpowers _
  exact (inv_mul_eq_one.mp this)

end Wrappers

section Transport

variable {X : Type} [Group X] [Finite X] {L : Subgroup X}
variable {e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He}

variable (e) in
noncomputable def imL (U : Subgroup X) : Subgroup (Equiv.Perm (Fin 8330)) :=
  ((U.subgroupOf L).map (heModelL e)).map heP.subtype

omit [Finite X] in
theorem mem_imL {U : Subgroup X} (hU : U ≤ L) {y : Equiv.Perm (Fin 8330)} :
    y ∈ imL e U ↔ ∃ x ∈ U, heL e x = y := by
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨l, hl, by rw [heL_of_mem l.2]; rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨heModelL e ⟨x, hU hx⟩, ⟨⟨x, hU hx⟩, hx, rfl⟩, by rw [heL_of_mem (hU hx)]; rfl⟩

omit [Finite X] in
theorem imL_le_heP (U : Subgroup X) : imL e U ≤ heP := map_subtype_le _

variable (e) in
noncomputable def pbL (T : Subgroup X) (F : Subgroup (Equiv.Perm (Fin 8330))) : Subgroup X :=
  T ⊓ ((F.subgroupOf heP).comap (heModelL e)).map L.subtype

omit [Finite X] in
theorem mem_pbL {T : Subgroup X} (hTL : T ≤ L) {F : Subgroup (Equiv.Perm (Fin 8330))} {x : X} :
    x ∈ pbL e T F ↔ x ∈ T ∧ heL e x ∈ F := by
  constructor
  · rintro ⟨hxT, ⟨l, hl, rfl⟩⟩
    refine ⟨hxT, ?_⟩
    change heL e (l : X) ∈ F
    rw [heL_of_mem l.2]
    exact hl
  · rintro ⟨hxT, hxF⟩
    refine ⟨hxT, ⟨⟨x, hTL hxT⟩, ?_, rfl⟩⟩
    rw [heL_of_mem (hTL hxT)] at hxF
    exact hxF

omit [Finite X] in
theorem pbL_le (T : Subgroup X) (F : Subgroup (Equiv.Perm (Fin 8330))) : pbL e T F ≤ T :=
  inf_le_left

theorem isElemTwo_pbL {T : Subgroup X} (hTL : T ≤ L) (hT : IsPGroup 2 T)
    {F : Subgroup (Equiv.Perm (Fin 8330))} (hF : IsElemTwo F) : IsElemTwo (pbL e T F) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · rw [mem_pbL hTL] at hx hy
    refine heL_injOn (e := e) hTL hT (mul_mem hx.1 hy.1) (mul_mem hy.1 hx.1) ?_
    rw [heL_mul (hTL hx.1) (hTL hy.1), heL_mul (hTL hy.1) (hTL hx.1), hF.1 _ hx.2 _ hy.2]
  · rw [mem_pbL hTL] at hx
    refine heL_injOn (e := e) hTL hT (mul_mem hx.1 hx.1) (one_mem T) ?_
    rw [heL_mul (hTL hx.1) (hTL hx.1), hF.2 _ hx.2, heL_one]

theorem pbL_sq {T : Subgroup X} (hTL : T ≤ L) (hT : IsPGroup 2 T)
    {F : Subgroup (Equiv.Perm (Fin 8330))} (hF : ∀ x ∈ F, x * x = 1) :
    ∀ x ∈ pbL e T F, x * x = 1 := by
  intro x hx
  rw [mem_pbL hTL] at hx
  refine heL_injOn (e := e) hTL hT (mul_mem hx.1 hx.1) (one_mem T) ?_
  rw [heL_mul (hTL hx.1) (hTL hx.1), hF _ hx.2, heL_one]

theorem card_pbL {T : Subgroup X} (hTL : T ≤ L) (hT : IsPGroup 2 T)
    {F : Subgroup (Equiv.Perm (Fin 8330))} (hFT : F ≤ imL e T) :
    Nat.card (pbL e T F) = Nat.card F := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : pbL e T F => (⟨heL e x, ((mem_pbL hTL).mp x.2).2⟩ : F)) ⟨?_, ?_⟩)
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (heL_injOn hTL hT ((mem_pbL hTL).mp x.2).1 ((mem_pbL hTL).mp y.2).1 h)
  · rintro ⟨f, hf⟩
    obtain ⟨x, hx, rfl⟩ := (mem_imL hTL).mp (hFT hf)
    exact ⟨⟨x, (mem_pbL hTL).mpr ⟨hx, hf⟩⟩, rfl⟩

theorem card_imL {T : Subgroup X} (hTL : T ≤ L) (hT : IsPGroup 2 T) :
    Nat.card (imL e T) = Nat.card T := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : T => (⟨heL e x, (mem_imL hTL).mpr ⟨x, x.2, rfl⟩⟩ : imL e T)) ⟨?_, ?_⟩)).symm
  · intro x y hxy
    exact Subtype.ext (heL_injOn hTL hT x.2 y.2 (congrArg Subtype.val hxy))
  · rintro ⟨f, hf⟩
    obtain ⟨x, hx, rfl⟩ := (mem_imL hTL).mp hf
    exact ⟨⟨x, hx⟩, rfl⟩

noncomputable def imLEquiv {T : Subgroup X} (hTL : T ≤ L) (hT : IsPGroup 2 T) :
    T ≃* imL e T :=
  MulEquiv.ofBijective
    ({ toFun := fun x => ⟨heL e x, (mem_imL hTL).mpr ⟨x, x.2, rfl⟩⟩
       map_one' := Subtype.ext heL_one
       map_mul' := fun x y => Subtype.ext (heL_mul (hTL x.2) (hTL y.2)) } : T →* imL e T)
    ⟨fun x y hxy => Subtype.ext (heL_injOn hTL hT x.2 y.2 (congrArg Subtype.val hxy)),
      fun ⟨f, hf⟩ => by
        obtain ⟨x, hx, rfl⟩ := (mem_imL hTL).mp hf
        exact ⟨⟨x, hx⟩, rfl⟩⟩

variable (e) in
noncomputable def imN (U : Subgroup X) : Subgroup (Equiv.Perm (Fin 8330)) :=
  ((U.subgroupOf (normalizer (L : Set X))).map (heModelN e)).map heAutGroup.subtype

omit [Finite X] in
theorem mem_imN {U : Subgroup X} (hU : U ≤ normalizer (L : Set X))
    {y : Equiv.Perm (Fin 8330)} : y ∈ imN e U ↔ ∃ x ∈ U, heN e x = y := by
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨l, hl, by rw [heN_of_mem l.2]; rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨heModelN e ⟨x, hU hx⟩, ⟨⟨x, hU hx⟩, hx, rfl⟩, by rw [heN_of_mem (hU hx)]; rfl⟩

omit [Finite X] in
theorem isPGroup_imN {U : Subgroup X} (hU : U ≤ normalizer (L : Set X)) (hU2 : IsPGroup 2 U) :
    IsPGroup 2 (imN e U) :=
  ((hU2.of_equiv (subgroupOfEquivOfLe hU).symm).map _).map _

end Transport

section HeldTwoGroups

theorem card_le_of_le_heP {Q : Subgroup (Equiv.Perm (Fin 8330))} (hQP : Q ≤ heP)
    (hQ : IsPGroup 2 Q) : Nat.card Q ≤ 1024 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : 2 ^ k ∣ 4030387200 := by
    rw [← hk, ← card_heP]
    exact card_dvd_of_le hQP
  have hk10 : k ≤ 10 := by
    by_contra h
    push Not at h
    have h11 : 2 ^ 11 ∣ 4030387200 := (pow_dvd_pow 2 h).trans hdvd
    norm_num at h11
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hk10
    _ = 1024 := by norm_num

theorem inv_mul_mem_heP {x y : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup) (hy : y ∈ heAutGroup)
    (hxP : x ∉ heP) (hyP : y ∉ heP) : x⁻¹ * y ∈ heP := by
  have hxu := (mem_heAutGroup_cases hx).resolve_left hxP
  have hyu := (mem_heAutGroup_cases hy).resolve_left hyP
  have h1 : (x * heAutU)⁻¹ * (y * heAutU) ∈ heP := mul_mem (inv_mem hxu) hyu
  have h2 := (mem_normalizer_iff.mp heAutU_mem_normalizer _).mp h1
  have : heAutU * ((x * heAutU)⁻¹ * (y * heAutU)) * heAutU⁻¹ = x⁻¹ * y := by group
  rwa [this] at h2

end HeldTwoGroups

section HeldFacts

variable {X : Type} [Group X] [Finite X] {L : Subgroup X}
variable (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)

theorem isPGroup_imL {T : Subgroup X} (hTL : T ≤ L) (hT : IsPGroup 2 T) :
    IsPGroup 2 (imL e T) :=
  hT.of_equiv (imLEquiv hTL hT)

include e in
theorem exists_elem_sixtyFour (h64 : HeldSylowElementarySixtyFour) {T : Subgroup X}
    (hTL : T ≤ L) (hT : IsPGroup 2 T) (h1024 : Nat.card T = 1024) :
    ∃ E : Subgroup X, E ≤ T ∧ T ≤ normalizer (E : Set X) ∧ IsElemTwo E ∧ Nat.card E = 64 := by
  obtain ⟨F, hFT, hTN, hc, h2, hF64⟩ :=
    h64 (imL e T) (imL_le_heP T) (by rw [card_imL hTL hT, h1024])
  refine ⟨pbL e T F, pbL_le T F, ?_, isElemTwo_pbL hTL hT ⟨hc, h2⟩,
    by rw [card_pbL hTL hT hFT, hF64]⟩
  have key : ∀ t ∈ T, ∀ x ∈ pbL e T F, t * x * t⁻¹ ∈ pbL e T F := by
    intro t ht x hx
    rw [mem_pbL hTL] at hx ⊢
    refine ⟨mul_mem (mul_mem ht hx.1) (inv_mem ht), ?_⟩
    rw [heL_mul (mul_mem (hTL ht) (hTL hx.1)) (inv_mem (hTL ht)), heL_mul (hTL ht) (hTL hx.1),
      heL_inv (hTL ht)]
    have htN := hTN ((mem_imL hTL).mpr ⟨t, ht, rfl⟩)
    exact (mem_normalizer_iff.mp htN _).mp hx.2
  intro t ht
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key t ht x, fun hx => ?_⟩
  have h := key t⁻¹ (inv_mem ht) _ hx
  rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at h

include e in
theorem card_center_eq_two (hZ : HeldSylowCenterTwo) {T : Subgroup X} (hTL : T ≤ L)
    (hT : IsPGroup 2 T) (h1024 : Nat.card T = 1024) : Nat.card (center T) = 2 := by
  rw [← hZ (imL e T) (imL_le_heP T) (by rw [card_imL hTL hT, h1024])]
  exact Nat.card_congr (Subgroup.centerCongr (imLEquiv (e := e) hTL hT)).toEquiv

include e in
theorem exists_outer_eight (hOut : HeldOuterInvolutionRank) {T : Subgroup X} (hTL : T ≤ L)
    (hT : IsPGroup 2 T) (h1024 : Nat.card T = 1024) {a : X}
    (haN : a ∈ normalizer (L : Set X)) (haT : a ∈ normalizer (T : Set X))
    (haLK : a ∉ L ⊔ coreActionKernel L) (ha2 : a * a ∈ coreActionKernel L) {a₁ : X}
    (ha₁ : a₁ ∈ T) (ha₁2 : a₁ * a₁ = 1) (hc : a₁ * a = a * a₁) :
    ∃ F : Subgroup X, F ≤ T ∧ F ≤ centralizer ({a} : Set X) ∧
      F ≤ centralizer ({a₁} : Set X) ∧ IsElemTwo F ∧ Nat.card F = 8 := by
  set x := heN e a with hxdef
  have hxR : x ∈ heAutGroup := heN_mem haN
  have hxP : x ∉ heP := fun h => haLK ((heN_mem_heP_iff haN).mp h)
  have hx2 : x * x = 1 := by
    rw [hxdef, ← heN_mul haN haN]
    exact (heN_eq_one_iff (mul_mem haN haN)).mpr ha2
  have hx1 : x ≠ 1 := fun h => hxP (h ▸ one_mem _)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hconj : ∀ t ∈ T, x * heL e t * x⁻¹ = heL e (a * t * a⁻¹) := fun t ht =>
    (heL_conj haN (hTL ht)).symm
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxN : x ∈ normalizer (imL e T : Set (Equiv.Perm (Fin 8330))) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨t, ht, rfl⟩ := (mem_imL hTL).mp hy
      rw [hconj t ht]
      exact (mem_imL hTL).mpr ⟨_, (mem_normalizer_iff.mp haT t).mp ht, rfl⟩
    · intro hy
      obtain ⟨t, ht, hteq⟩ := (mem_imL hTL).mp hy
      have hy' : y = x * heL e t * x⁻¹ := by
        rw [hteq, hxinv]
        calc y = (x * x) * y * (x * x) := by rw [hx2, one_mul, mul_one]
          _ = x * (x * y * x) * x := by group
      rw [hy', hconj t ht]
      exact (mem_imL hTL).mpr ⟨_, (mem_normalizer_iff.mp haT t).mp ht, rfl⟩
  set T₀ : Subgroup (Equiv.Perm (Fin 8330)) := imL e T ⊔ zpowers x with hT₀
  have hT₀R : T₀ ≤ heAutGroup :=
    sup_le ((imL_le_heP T).trans heP_le_heAutGroup) (zpowers_le.mpr hxR)
  have hcardT : Nat.card (imL e T) = 1024 := by rw [card_imL hTL hT, h1024]
  have hTT₀ : imL e T ≤ T₀ := le_sup_left
  have hxT₀ : x ∈ T₀ := (le_sup_right : zpowers x ≤ imL e T ⊔ zpowers x) (mem_zpowers x)
  have hT₀le : Nat.card T₀ ≤ 2048 := by
    have := card_zpowers_sup_le hx2 hxN
    rw [hT₀, sup_comm]
    omega
  have hT₀ne : Nat.card T₀ ≠ 1024 := fun h => hxP (imL_le_heP T
    ((eq_of_le_of_card_ge hTT₀ (by rw [h, hcardT])) ▸ hxT₀))
  have hT₀card : Nat.card T₀ = 2048 := by
    obtain ⟨m, hm⟩ := hcardT ▸ card_dvd_of_le hTT₀
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact Nat.card_pos.ne' (by rw [hm, mul_zero])
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hT₀ne (by rw [hm, mul_one])
    have hm2 : m ≤ 2 := by omega
    interval_cases m <;> omega
  have hT₀P : T₀ ⊓ heP = imL e T := by
    refine (eq_of_le_of_card_ge (le_inf hTT₀ (imL_le_heP T)) ?_).symm
    rw [hcardT]
    obtain ⟨m, hm⟩ := hcardT ▸ card_dvd_of_le (le_inf hTT₀ (imL_le_heP T))
    obtain ⟨k, hk⟩ := card_dvd_of_le (inf_le_left : T₀ ⊓ heP ≤ T₀)
    rw [hT₀card] at hk
    have hne : Nat.card ↥(T₀ ⊓ heP) ≠ 2048 := fun h => hxP
      ((eq_of_le_of_card_ge (inf_le_left : T₀ ⊓ heP ≤ T₀) (by rw [h, hT₀card])) ▸ hxT₀).2
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact Nat.card_pos.ne' hm
    have hk2 : k ≤ 2 := by
      by_contra h
      push Not at h
      have h1 : 1024 * 3 ≤ Nat.card ↥(T₀ ⊓ heP) * k := by
        rw [hm]
        exact Nat.mul_le_mul (Nat.le_mul_of_pos_right 1024 (Nat.pos_of_ne_zero hm0)) h
      omega
    interval_cases k
    · omega
    · omega
    · omega
  have ha₁P : heL e a₁ ∈ T₀ ⊓ heP :=
    ⟨hTT₀ ((mem_imL hTL).mpr ⟨a₁, ha₁, rfl⟩), heL_mem_heP (hTL ha₁)⟩
  have ha₁sq : heL e a₁ * heL e a₁ = 1 := by
    rw [← heL_mul (hTL ha₁) (hTL ha₁), ha₁2, heL_one]
  have hfix : ∀ t ∈ T, a * t * a⁻¹ = t → heL e t * x = x * heL e t := by
    intro t ht hat
    have h := hconj t ht
    rw [hat] at h
    calc heL e t * x = x * heL e t * x⁻¹ * x := by rw [h]
      _ = x * heL e t := by group
  have ha₁x : heL e a₁ * x = x * heL e a₁ :=
    hfix a₁ ha₁ (by rw [← hc]; group)
  obtain ⟨F, hFle, hFc, hF2, hF8⟩ :=
    hOut T₀ hT₀R hT₀card x hxT₀ hxP hxo (heL e a₁) ha₁P ha₁sq ha₁x
  have hFT : F ≤ imL e T := by
    rw [← hT₀P]
    exact hFle.trans (inf_le_left.trans inf_le_left)
  have hFx : ∀ f ∈ F, f * x = x * f := fun f hf =>
    mem_centralizer_singleton_iff.mp ((hFle.trans (inf_le_left.trans inf_le_right)) hf)
  have hFa₁ : ∀ f ∈ F, f * heL e a₁ = heL e a₁ * f := fun f hf =>
    mem_centralizer_singleton_iff.mp ((hFle.trans inf_le_right) hf)
  refine ⟨pbL e T F, pbL_le T F, ?_, ?_, isElemTwo_pbL hTL hT ⟨hFc, hF2⟩,
    by rw [card_pbL hTL hT hFT, hF8]⟩
  · intro f hf
    rw [mem_pbL hTL] at hf
    rw [mem_centralizer_singleton_iff]
    have h1 : heL e (a * f * a⁻¹) = heL e f := by
      rw [← hconj f hf.1, ← hFx _ hf.2, mul_assoc, mul_inv_cancel, mul_one]
    have h2 := heL_injOn (e := e) hTL hT ((mem_normalizer_iff.mp haT f).mp hf.1) hf.1 h1
    calc f * a = a * f * a⁻¹ * a := by rw [h2]
      _ = a * f := by group
  · intro f hf
    rw [mem_pbL hTL] at hf
    rw [mem_centralizer_singleton_iff]
    refine heL_injOn (e := e) hTL hT (mul_mem hf.1 ha₁) (mul_mem ha₁ hf.1) ?_
    rw [heL_mul (hTL hf.1) (hTL ha₁), heL_mul (hTL ha₁) (hTL hf.1), hFa₁ _ hf.2]

omit [Finite X] in
theorem le_normalizer_oddIn : L ≤ normalizer (((pPrimeCore 2 ↥L).map L.subtype : Subgroup X) :
    Set X) := by
  intro l hl
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨o, ho, rfl⟩
    refine ⟨⟨l, hl⟩ * o * ⟨l, hl⟩⁻¹, (inferInstance : (pPrimeCore 2 ↥L).Normal).conj_mem o ho _,
      rfl⟩
  · rintro ⟨o, ho, hoeq⟩
    refine ⟨⟨l, hl⟩⁻¹ * o * ⟨l, hl⟩, ?_, ?_⟩
    · have := (inferInstance : (pPrimeCore 2 ↥L).Normal).conj_mem o ho ⟨l, hl⟩⁻¹
      rwa [inv_inv] at this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv] at hoeq ⊢
      rw [hoeq]
      group

theorem relIndex_sup_eq_relIndex_inf_of_le_normalizer {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (hK : H ≤ normalizer (K : Set G)) :
    H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K := by
  have hKrel : K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
    let NG : Subgroup G := normalizer (K : Set G)
    have hHleNG : H ≤ NG := hK
    have hKleNG : K ≤ NG := le_normalizer
    have hHKleNG : H ⊔ K ≤ NG := sup_le hHleNG hKleNG
    have : (K.subgroupOf NG).Normal :=
      (normal_subgroupOf_iff_le_normalizer (H := K) (K := NG) hKleNG).2 le_rfl
    calc K.relIndex (H ⊔ K)
        = (K.subgroupOf NG).relIndex ((H ⊔ K).subgroupOf NG) :=
          (relIndex_subgroupOf (H := K) (K := H ⊔ K) (L := NG) hHKleNG).symm
      _ = (K.subgroupOf NG).relIndex ((H.subgroupOf NG) ⊔ (K.subgroupOf NG)) := by
          rw [subgroupOf_sup (A := H) (A' := K) (B := NG) hHleNG hKleNG]
      _ = (K.subgroupOf NG).relIndex (H.subgroupOf NG) :=
          relIndex_sup_right (H := H.subgroupOf NG) (K := K.subgroupOf NG)
      _ = ((H.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex (H.subgroupOf NG) :=
          (inf_relIndex_left (H := H.subgroupOf NG) (K := K.subgroupOf NG)).symm
      _ = ((H ⊓ K).subgroupOf NG).relIndex (H.subgroupOf NG) := by
          rw [show (H.subgroupOf NG) ⊓ (K.subgroupOf NG) = (H ⊓ K).subgroupOf NG by
            ext x
            simp [mem_subgroupOf]]
      _ = (H ⊓ K).relIndex H := relIndex_subgroupOf (H := H ⊓ K) (K := H) (L := NG) hHleNG
  have hmul : (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) =
      (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by
    calc (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) = (H ⊓ K).relIndex (H ⊔ K) :=
          relIndex_mul_relIndex (H := H ⊓ K) (K := H) (L := H ⊔ K) inf_le_left le_sup_left
      _ = (H ⊓ K).relIndex K * K.relIndex (H ⊔ K) :=
          (relIndex_mul_relIndex (H := H ⊓ K) (K := K) (L := H ⊔ K) inf_le_right
            le_sup_right).symm
      _ = (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by rw [hKrel]
  have hpos : 0 < (H ⊓ K).relIndex H := by
    have hne : (H ⊓ K).relIndex H ≠ 0 := by
      dsimp [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite (H := (H ⊓ K).subgroupOf H)
    exact Nat.pos_of_ne_zero hne
  have hmul' : (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) =
      (H ⊓ K).relIndex H * (H ⊓ K).relIndex K := by
    rw [hmul, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos hmul'

theorem isSylowTwoIn_sup_odd {G : Type*} [Group G] [Finite G] {B O : Subgroup G}
    (hB : IsPGroup 2 B) (hO : Odd (Nat.card O)) (hBO : B ≤ normalizer (O : Set G)) :
    IsSylowTwoIn B (B ⊔ O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_sup_left, ?_⟩
  have hp : IsPGroup 2 (B.subgroupOf (B ⊔ O)) :=
    hB.of_equiv (subgroupOfEquivOfLe le_sup_left).symm
  have hidx : ¬ 2 ∣ (B.subgroupOf (B ⊔ O)).index := by
    change ¬ 2 ∣ B.relIndex (B ⊔ O)
    rw [relIndex_sup_eq_relIndex_inf_of_le_normalizer hBO]
    intro h
    have h2 : 2 ∣ Nat.card O := h.trans (relIndex_dvd_card _ _)
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h2)
  exact ⟨hp.toSylow hidx, rfl⟩

include e in
theorem le_of_fourGroup_normalizers (hGen : HeldFourGroupGeneration) {T : Subgroup X}
    (hTL : T ≤ L) (hT : IsPGroup 2 T) (h1024 : Nat.card T = 1024) {N : Subgroup X}
    (hON : (pPrimeCore 2 ↥L).map L.subtype ≤ N)
    (hBN : ∀ B : Subgroup X, B ≤ T → Nat.card B = 4 → (∀ b ∈ B, b * b = 1) →
      L ⊓ normalizer (B : Set X) ≤ N) : L ≤ N := by
  set O : Subgroup X := (pPrimeCore 2 ↥L).map L.subtype with hOdef
  have hOodd : Odd (Nat.card O) := by
    rw [hOdef, card_map_of_injective L.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOL : O ≤ L := map_subtype_le _
  have hLO : L ≤ normalizer (O : Set X) := le_normalizer_oddIn
  have hgen := hGen (imL e T) (imL_le_heP T) (by rw [card_imL hTL hT, h1024])
  have hPQ : heP ≤ imL e (L ⊓ N) := by
    rw [← hgen]
    refine iSup_le fun F => iSup_le fun hFT => iSup_le fun hF4 => iSup_le fun hF2 => ?_
    intro y hy
    obtain ⟨hyP, hyN⟩ := mem_inf.mp hy
    set B := pbL e T F with hBdef
    have hB4 : Nat.card B = 4 := by rw [card_pbL hTL hT hFT, hF4]
    have hB2 : ∀ b ∈ B, b * b = 1 := pbL_sq hTL hT hF2
    have hBT : B ≤ T := pbL_le T F
    have hBp : IsPGroup 2 B := hT.to_le hBT
    obtain ⟨x₀, hx₀L, rfl⟩ := exists_heL_eq (e := e) hyP
    have hSyl := isSylowTwoIn_sup_odd hBp hOodd ((hBT.trans hTL).trans hLO)
    have hconjB : B.map (MulAut.conj x₀).toMonoidHom ≤ B ⊔ O := by
      rintro _ ⟨b, hb, rfl⟩
      have hb' := (mem_pbL hTL).mp hb
      have hmem : heL e (x₀ * b * x₀⁻¹) ∈ F := by
        rw [heL_mul (mul_mem hx₀L (hTL hb'.1)) (inv_mem hx₀L), heL_mul hx₀L (hTL hb'.1),
          heL_inv hx₀L]
        exact (mem_normalizer_iff.mp hyN _).mp hb'.2
      obtain ⟨b', hb'T, hb'eq⟩ := (mem_imL hTL).mp (hFT hmem)
      have hb'B : b' ∈ B := (mem_pbL hTL).mpr ⟨hb'T, hb'eq ▸ hmem⟩
      have hxbL : x₀ * b * x₀⁻¹ ∈ L := mul_mem (mul_mem hx₀L (hTL hb'.1)) (inv_mem hx₀L)
      have h1 : heL e (b'⁻¹ * (x₀ * b * x₀⁻¹)) = 1 := by
        rw [heL_mul (inv_mem (hTL hb'T)) hxbL, heL_inv (hTL hb'T), hb'eq, inv_mul_cancel]
      rw [heL_eq_one_iff (mul_mem (inv_mem (hTL hb'T)) hxbL)] at h1
      have : (MulAut.conj x₀).toMonoidHom b = b' * (b'⁻¹ * (x₀ * b * x₀⁻¹)) := by
        simp [MulAut.conj_apply]
      rw [this]
      exact mul_mem (mem_sup_left hb'B) (mem_sup_right h1)
    obtain ⟨c, hcH, hcB⟩ := hSyl.exists_conj_le hconjB (hBp.map _)
    have hcxN : c * x₀ ∈ normalizer (B : Set X) := by
      rw [mem_normalizer_iff_map_conj_eq]
      refine eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj _).injective])
      rintro _ ⟨b, hb, rfl⟩
      have := hcB (x₀ * b * x₀⁻¹) ⟨b, hb, by simp [MulAut.conj_apply]⟩
      simpa [MulAut.conj_apply, mul_assoc] using this
    have hBN' : B ≤ normalizer (O : Set X) := (hBT.trans hTL).trans hLO
    have hcset : c ∈ ((B : Set X) * (O : Set X)) := by
      rw [← coe_mul_of_left_le_normalizer_right B O hBN']
      exact hcH
    obtain ⟨b₀, hb₀, o₀, ho₀, rfl⟩ := hcset
    have ho₀L : o₀ ∈ L := hOL ho₀
    have hox : o₀ * x₀ ∈ L ⊓ normalizer (B : Set X) := by
      refine mem_inf.mpr ⟨mul_mem ho₀L hx₀L, ?_⟩
      have : o₀ * x₀ = b₀⁻¹ * (b₀ * o₀ * x₀) := by group
      rw [this]
      have hb₀' : b₀ ∈ B := hb₀
      exact mul_mem (inv_mem (le_normalizer hb₀')) hcxN
    have hheL : heL e (o₀ * x₀) = heL e x₀ := by
      rw [heL_mul ho₀L hx₀L, (heL_eq_one_iff ho₀L).mpr ho₀, one_mul]
    exact (mem_imL inf_le_left).mpr
      ⟨o₀ * x₀, mem_inf.mpr ⟨(mem_inf.mp hox).1, hBN B hBT hB4 hB2 hox⟩, hheL⟩
  intro x hx
  obtain ⟨x', hx', hx'eq⟩ := (mem_imL inf_le_left).mp (hPQ (heL_mem_heP (e := e) hx))
  obtain ⟨hx'L, hx'N⟩ := mem_inf.mp hx'
  have h1 : heL e (x'⁻¹ * x) = 1 := by
    rw [heL_mul (inv_mem hx'L) hx, heL_inv hx'L, hx'eq, inv_mul_cancel]
  rw [heL_eq_one_iff (mul_mem (inv_mem hx'L) hx)] at h1
  have : x = x' * (x'⁻¹ * x) := by group
  rw [this]
  exact mul_mem hx'N (hON h1)

include e in
theorem card_inf_eq_1024 {S : Subgroup X} (hS : IsSylowTwoIn S (normalizer (L : Set X))) :
    Nat.card ↥(S ⊓ L) = 1024 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥(S ⊓ L) := hS.isPGroup.to_le inf_le_left
  apply le_antisymm
  · rw [← card_imL (e := e) inf_le_right h2]
    exact card_le_of_le_heP (imL_le_heP _) (isPGroup_imL e inf_le_right h2)
  · have hL : Nat.card L = Nat.card heP * Nat.card (pPrimeCore 2 ↥L) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥L),
        Nat.card_congr (e.trans heEquivP).toEquiv]
    have hdvd : 2 ^ 10 ∣ Nat.card L := by
      rw [hL, card_heP]
      exact Dvd.dvd.mul_right (by norm_num) _
    obtain ⟨T', hT'⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    set T'' : Subgroup X := T'.map L.subtype with hT''
    have hT''L : T'' ≤ L := map_subtype_le _
    have hT''c : Nat.card T'' = 1024 := by
      rw [hT'', card_map_of_injective L.subtype_injective, hT']
      norm_num
    have hT''2 : IsPGroup 2 T'' := IsPGroup.of_card (n := 10) (by rw [hT''c]; norm_num)
    obtain ⟨c, hcN, hcT⟩ := hS.exists_conj_le (hT''L.trans le_normalizer) hT''2
    have hle : T''.map (MulAut.conj c).toMonoidHom ≤ S ⊓ L := by
      rintro _ ⟨t, ht, rfl⟩
      exact mem_inf.mpr ⟨hcT t ht, (mem_normalizer_iff.mp hcN t).mp (hT''L ht)⟩
    calc 1024 = Nat.card ↥(T''.map (MulAut.conj c).toMonoidHom) := by
          rw [card_map_of_injective (MulAut.conj c).injective, hT''c]
      _ ≤ Nat.card ↥(S ⊓ L) := card_le_of_le hle

include e in
theorem inf_sup_coreActionKernel_le {S : Subgroup X}
    (hS : IsSylowTwoIn S (normalizer (L : Set X))) :
    S ⊓ (L ⊔ coreActionKernel L) ≤ S ⊓ L ⊔ S ⊓ coreActionKernel L := by
  intro s hs
  obtain ⟨hsS, hsLK⟩ := mem_inf.mp hs
  have hsN : s ∈ normalizer (L : Set X) := hS.1 hsS
  have hsP : heN e s ∈ heP := (heN_mem_heP_iff hsN).mpr hsLK
  have h2 : IsPGroup 2 ↥(S ⊓ L) := hS.isPGroup.to_le inf_le_left
  have hle : imL e (S ⊓ L) ≤ imN e S ⊓ heP := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := (mem_imL inf_le_right).mp hy
    exact mem_inf.mpr ⟨(mem_imN hS.1).mpr ⟨t, (mem_inf.mp ht).1, heN_eq_heL (mem_inf.mp ht).2⟩,
      heL_mem_heP (mem_inf.mp ht).2⟩
  have heq : imL e (S ⊓ L) = imN e S ⊓ heP := by
    refine eq_of_le_of_card_ge hle ?_
    rw [card_imL inf_le_right h2, card_inf_eq_1024 e hS]
    exact card_le_of_le_heP inf_le_right ((isPGroup_imN hS.1 hS.isPGroup).to_le inf_le_left)
  have hs' : heN e s ∈ imL e (S ⊓ L) := by
    rw [heq]
    exact mem_inf.mpr ⟨(mem_imN hS.1).mpr ⟨s, hsS, rfl⟩, hsP⟩
  obtain ⟨t, ht, hteq⟩ := (mem_imL inf_le_right).mp hs'
  obtain ⟨htS, htL⟩ := mem_inf.mp ht
  have htN : t ∈ normalizer (L : Set X) := le_normalizer htL
  have h1 : heN e (t⁻¹ * s) = 1 := by
    rw [heN_mul (inv_mem htN) hsN, heN_inv htN, heN_eq_heL htL, hteq, inv_mul_cancel]
  rw [heN_eq_one_iff (mul_mem (inv_mem htN) hsN)] at h1
  have : s = t * (t⁻¹ * s) := by group
  rw [this]
  exact mul_mem (mem_sup_left ht) (mem_sup_right (mem_inf.mpr ⟨mul_mem (inv_mem htS) hsS, h1⟩))

omit [Finite X] in
include e in
theorem inv_mul_mem_sup_of_not_mem {a f : X} (ha : a ∈ normalizer (L : Set X))
    (hf : f ∈ normalizer (L : Set X)) (haLK : a ∉ L ⊔ coreActionKernel L)
    (hfLK : f ∉ L ⊔ coreActionKernel L) : a⁻¹ * f ∈ L ⊔ coreActionKernel L := by
  rw [← heN_mem_heP_iff (e := e) (mul_mem (inv_mem ha) hf), heN_mul (inv_mem ha) hf,
    heN_inv ha]
  exact inv_mul_mem_heP (heN_mem ha) (heN_mem hf)
    (fun h => haLK ((heN_mem_heP_iff ha).mp h)) (fun h => hfLK ((heN_mem_heP_iff hf).mp h))

include e in
theorem card_le_two_mul_card_inf {F : Subgroup X} (hF : F ≤ normalizer (L : Set X)) :
    Nat.card F ≤ 2 * Nat.card ↥(F ⊓ (L ⊔ coreActionKernel L)) := by
  classical
  by_cases h : F ≤ L ⊔ coreActionKernel L
  · rw [inf_eq_left.mpr h]
    omega
  · obtain ⟨a, haF, haLK⟩ := IsConcreteLE.not_le_iff_exists.mp h
    let g : F → ↥(F ⊓ (L ⊔ coreActionKernel L)) ⊕ ↥(F ⊓ (L ⊔ coreActionKernel L)) := fun f =>
      if hf : (f : X) ∈ L ⊔ coreActionKernel L then Sum.inl ⟨f, mem_inf.mpr ⟨f.2, hf⟩⟩
      else Sum.inr ⟨a⁻¹ * f, mem_inf.mpr ⟨mul_mem (inv_mem haF) f.2,
        inv_mul_mem_sup_of_not_mem e (hF haF) (hF f.2) haLK hf⟩⟩
    have hg : Function.Injective g := by
      intro f₁ f₂ h12
      by_cases h1 : (f₁ : X) ∈ L ⊔ coreActionKernel L <;>
        by_cases h2 : (f₂ : X) ∈ L ⊔ coreActionKernel L <;>
        simp only [g, h1, h2, dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq] at h12
      · exact Subtype.ext (congrArg (fun w : ↥(F ⊓ (L ⊔ coreActionKernel L)) => (w : X)) h12)
      · exact Subtype.ext (mul_left_cancel
          (congrArg (fun w : ↥(F ⊓ (L ⊔ coreActionKernel L)) => (w : X)) h12))
    have := Nat.card_le_card_of_injective g hg
    rw [Nat.card_sum] at this
    omega

end HeldFacts

end CFSG.ComponentClassification.GrSLit
