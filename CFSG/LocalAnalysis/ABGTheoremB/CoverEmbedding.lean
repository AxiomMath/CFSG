module

public import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.FeitThompson.OddOrderTheorem

public noncomputable section

namespace CFSG.ABGTheoremB.Setting

open CFSG.ABGQGroups CFSG.QuasiDihedralFusion
open scoped Pointwise

universe u

section Transport

variable {A B : Type*} [Group A] [Group B] {ι : A →* B}

theorem normal_iff_range_le_normalizer_map (hι : Function.Injective ι) (Y : Subgroup A) :
    Y.Normal ↔ ι.range ≤ Subgroup.normalizer ((Y.map ι : Subgroup B) : Set B) := by
  constructor
  · intro hY b hb
    obtain ⟨a, rfl⟩ := hb
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨a * y * a⁻¹, hY.conj_mem y hy a, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨y, hy, hyz⟩
      refine ⟨a⁻¹ * y * a, ?_, ?_⟩
      · simpa using hY.conj_mem y hy a⁻¹
      · rw [map_mul, map_mul, map_inv, hyz]
        group
  · intro h
    refine ⟨fun y hy a => ?_⟩
    obtain ⟨y', hy', hyy'⟩ :=
      (Subgroup.mem_normalizer_iff.mp (h ⟨a, rfl⟩) (ι y)).mp ⟨y, hy, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at hyy'
    rwa [← hι hyy']

theorem normal_comap_iff_range_le_normalizer (hι : Function.Injective ι) {Z : Subgroup B}
    (hZ : Z ≤ ι.range) :
    (Z.comap ι).Normal ↔ ι.range ≤ Subgroup.normalizer (Z : Set B) := by
  rw [normal_iff_range_le_normalizer_map hι, Subgroup.map_comap_eq_self hZ]

theorem map_centralizer_eq_range_inf (hι : Function.Injective ι) (X : Subgroup A) :
    (Subgroup.centralizer (X : Set A)).map ι =
      ι.range ⊓ Subgroup.centralizer ((X.map ι : Subgroup B) : Set B) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at ha
    refine Subgroup.mem_inf.mpr ⟨⟨a, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, ha x hx]
  · intro hb
    obtain ⟨⟨a, rfl⟩, hb⟩ := Subgroup.mem_inf.mp hb
    refine ⟨a, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hb
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    apply hι
    rw [map_mul, map_mul]
    exact hb _ ⟨x, hx, rfl⟩

theorem map_centralizer_comap_eq_range_inf (hι : Function.Injective ι) {Z : Subgroup B}
    (hZ : Z ≤ ι.range) :
    (Subgroup.centralizer ((Z.comap ι : Subgroup A) : Set A)).map ι =
      ι.range ⊓ Subgroup.centralizer (Z : Set B) := by
  rw [map_centralizer_eq_range_inf hι, Subgroup.map_comap_eq_self hZ]

private theorem oddCore_map_mulEquiv_aux {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) : (CFSG.oddCore X).map e.toMonoidHom = CFSG.oddCore Y := by
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.oddCore_normal X).map _ e.surjective,
      by rw [Subgroup.card_map_of_injective e.injective]; exact odd_card_oddCore X⟩
  · have hle : (CFSG.oddCore Y).map e.symm.toMonoidHom ≤ CFSG.oddCore X :=
      le_sSup ⟨(CFSG.oddCore_normal Y).map _ e.symm.surjective,
        by rw [Subgroup.card_map_of_injective e.symm.injective]; exact odd_card_oddCore Y⟩
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

private theorem isSolvable_map_of_injective {X Y : Type*} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Injective f) (K : Subgroup X) [Group.IsSolvable K] :
    Group.IsSolvable (K.map f) :=
  Group.isSolvable_of_surjective (f := (K.equivMapOfInjective f hf).toMonoidHom)
    (K.equivMapOfInjective f hf).surjective

private theorem solvableRadical_map_mulEquiv_aux {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (CFSG.solvableRadical X).map e.toMonoidHom = CFSG.solvableRadical Y := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    obtain ⟨hKn, hKs⟩ := hK
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨hKn.map _ e.surjective, isSolvable_map_of_injective e.injective K⟩
  · refine sSup_le fun K hK => ?_
    obtain ⟨hKn, hKs⟩ := hK
    have hle : K.map e.symm.toMonoidHom ≤ CFSG.solvableRadical X :=
      le_sSup ⟨hKn.map _ e.symm.surjective, isSolvable_map_of_injective e.symm.injective K⟩
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

theorem map_oddCore_of_injective [Finite A] (hι : Function.Injective ι) :
    (CFSG.oddCore A).map ι = (CFSG.oddCore ι.range).map ι.range.subtype := by
  have : Finite ι.range := Finite.of_equiv A (MonoidHom.ofInjective hι).toEquiv
  have hcomp : ι = ι.range.subtype.comp (MonoidHom.ofInjective hι).toMonoidHom := by
    ext a
    exact (MonoidHom.ofInjective_apply hι).symm
  rw [← oddCore_map_mulEquiv_aux (MonoidHom.ofInjective hι), Subgroup.map_map, ← hcomp]

theorem map_solvableRadical_of_injective (hι : Function.Injective ι) :
    (CFSG.solvableRadical A).map ι = (CFSG.solvableRadical ι.range).map ι.range.subtype := by
  have hcomp : ι = ι.range.subtype.comp (MonoidHom.ofInjective hι).toMonoidHom := by
    ext a
    exact (MonoidHom.ofInjective_apply hι).symm
  rw [← solvableRadical_map_mulEquiv_aux (MonoidHom.ofInjective hι), Subgroup.map_map, ← hcomp]

private theorem hasNormalSL2_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {q : ℕ} (h : HasNormalSL2 X q) : HasNormalSL2 Y q := by
  obtain ⟨L, F, hF, hFin, hL, hq, ⟨φ⟩⟩ := h
  exact ⟨L.map e.toMonoidHom, F, hF, hFin, hL.map _ e.surjective, hq,
    ⟨(L.equivMapOfInjective e.toMonoidHom e.injective).symm.trans φ⟩⟩

theorem hasNormalSL2_congr (e : A ≃* B) (q : ℕ) : HasNormalSL2 A q ↔ HasNormalSL2 B q :=
  ⟨hasNormalSL2_of_mulEquiv e, hasNormalSL2_of_mulEquiv e.symm⟩

theorem hasNormalSL2_iff_range (hι : Function.Injective ι) (q : ℕ) :
    HasNormalSL2 A q ↔ HasNormalSL2 ι.range q :=
  hasNormalSL2_congr (MonoidHom.ofInjective hι) q

theorem hasNormalSL2_of_le_range (hι : Function.Injective ι) {Z : Subgroup B}
    (hZ : Z ≤ ι.range) (hZn : ι.range ≤ Subgroup.normalizer (Z : Set B)) {F : Type} [Field F]
    [Finite F] (e : Z ≃* Matrix.SpecialLinearGroup (Fin 2) F) : HasNormalSL2 A (Nat.card F) :=
  ⟨Z.comap ι, F, inferInstance, inferInstance,
    (normal_comap_iff_range_le_normalizer hι hZ).mpr hZn, rfl,
    ⟨(((Z.comap ι).equivMapOfInjective ι hι).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hZ))).trans e⟩⟩

end Transport

section Quotient

variable {K : Type*} [Group K]

private theorem card_comap_mk'_aux (M : Subgroup K) [M.Normal] (V : Subgroup (K ⧸ M)) :
    Nat.card (V.comap (QuotientGroup.mk' M)) = Nat.card M * Nat.card V := by
  have hMV : M ≤ V.comap (QuotientGroup.mk' M) := by
    intro x hx
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have h1 := Subgroup.relIndex_mul_card M (V.comap (QuotientGroup.mk' M))
  rw [inf_eq_left.mpr hMV] at h1
  have h2 : M.relIndex (V.comap (QuotientGroup.mk' M)) = Nat.card V := by
    have h := Subgroup.relIndex_comap (⊥ : Subgroup (K ⧸ M)) (QuotientGroup.mk' M)
      (V.comap (QuotientGroup.mk' M))
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk', Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective M), Subgroup.relIndex_bot_left] at h
    exact h
  rw [← h1, h2, mul_comm]

theorem normal_map_mk'_iff (M : Subgroup K) [M.Normal] {Y : Subgroup K} (hMY : M ≤ Y) :
    (Y.map (QuotientGroup.mk' M)).Normal ↔ Y.Normal := by
  constructor
  · intro h
    have h' := h.comap (QuotientGroup.mk' M)
    rwa [Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])] at h'
  · intro h
    exact h.map _ (QuotientGroup.mk'_surjective M)

theorem oddCore_quotient_oddCore [Finite K] : CFSG.oddCore (K ⧸ CFSG.oddCore K) = ⊥ := by
  set P := (CFSG.oddCore (K ⧸ CFSG.oddCore K)).comap (QuotientGroup.mk' (CFSG.oddCore K))
    with hP
  have hPn : P.Normal := (CFSG.oddCore_normal _).comap _
  have hPodd : Odd (Nat.card P) := by
    rw [hP, card_comap_mk'_aux]
    exact (odd_card_oddCore K).mul (odd_card_oddCore _)
  have hPO : P ≤ CFSG.oddCore K := le_sSup ⟨hPn, hPodd⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  exact hPO hx

theorem solvableRadical_quotient_oddCore [Finite K] :
    CFSG.solvableRadical (K ⧸ CFSG.oddCore K) =
      (CFSG.solvableRadical K).map (QuotientGroup.mk' (CFSG.oddCore K)) := by
  apply le_antisymm
  · set P := (CFSG.solvableRadical (K ⧸ CFSG.oddCore K)).comap
      (QuotientGroup.mk' (CFSG.oddCore K)) with hP
    have hPn : P.Normal := (CFSG.ABGLocalTools.solvableRadical_normal).comap _
    have hOP : CFSG.oddCore K ≤ P := by
      intro x hx
      rw [hP, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem _
    have : Group.IsSolvable (CFSG.solvableRadical (K ⧸ CFSG.oddCore K)) :=
      CFSG.ABGLocalTools.solvableRadical_isSolvable
    have : Group.IsSolvable (CFSG.oddCore K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCore K)
    let g : P →* CFSG.solvableRadical (K ⧸ CFSG.oddCore K) :=
      MonoidHom.codRestrict ((QuotientGroup.mk' (CFSG.oddCore K)).comp P.subtype) _
        (fun x => x.2)
    have hPs : Group.IsSolvable P := by
      refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hOP) g ?_
      intro x hx
      have hx1 : QuotientGroup.mk' (CFSG.oddCore K) (x : K) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
      exact ⟨⟨x, hx1⟩, rfl⟩
    have hPS : P ≤ CFSG.solvableRadical K := le_sSup ⟨hPn, hPs⟩
    intro y hy
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore K) y
    exact ⟨k, hPS hy, rfl⟩
  · apply le_sSup
    refine ⟨(CFSG.ABGLocalTools.solvableRadical_normal).map _
      (QuotientGroup.mk'_surjective _), ?_⟩
    have : Group.IsSolvable (CFSG.solvableRadical K) :=
      CFSG.ABGLocalTools.solvableRadical_isSolvable
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' (CFSG.oddCore K)).subgroupMap (CFSG.solvableRadical K))
      ((QuotientGroup.mk' (CFSG.oddCore K)).subgroupMap_surjective _)

theorem oddCore_range_eq_bot_of_injective [Finite K] {B : Type*} [Group B]
    {ι : K ⧸ CFSG.oddCore K →* B} (hι : Function.Injective ι) : CFSG.oddCore ι.range = ⊥ := by
  have h := map_oddCore_of_injective hι
  rw [oddCore_quotient_oddCore, Subgroup.map_bot, eq_comm,
    Subgroup.map_eq_bot_iff_of_injective _ ι.range.subtype_injective] at h
  exact h

end Quotient

variable {G : Type u} [Group G] (σ : Setting G)

instance normal_ON_subgroupOf_N : (σ.ON.subgroupOf σ.N).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer σ.ON_le_N).mpr σ.N_le_normalizer_ON

abbrev L₀Bar : Subgroup (↥σ.N ⧸ σ.ON.subgroupOf σ.N) :=
  (σ.L₀.subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N))

abbrev LBar : Subgroup (↥σ.N ⧸ σ.ON.subgroupOf σ.N) :=
  (σ.L.subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N))

theorem L₀Bar_le_LBar : σ.L₀Bar ≤ σ.LBar :=
  Subgroup.map_mono fun _ hx => (le_sup_left : σ.L₀ ≤ σ.L) hx

theorem L₀Bar_normal [Finite G] (hσ : σ.IsValid) : σ.L₀Bar.Normal :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hσ.L₀_le_N).mpr hσ.N_le_normalizer_L₀).map _
    (QuotientGroup.mk'_surjective _)

theorem exists_L₀Bar_mulEquiv [Finite G] (hσ : σ.IsValid) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
      Nonempty (σ.L₀Bar ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨F, hF, hFin, hq, ψ, hψ, hker⟩ := hσ.L₀_quotient
  let γ : ↥σ.L₀ →* ↥σ.N ⧸ σ.ON.subgroupOf σ.N :=
    (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)).comp (Subgroup.inclusion hσ.L₀_le_N)
  have hγker : γ.ker = ψ.ker := by
    rw [hker]
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk (⟨l, hσ.L₀_le_N l.2⟩ : ↥σ.N) : ↥σ.N ⧸ σ.ON.subgroupOf σ.N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hγrange : γ.range = σ.L₀Bar := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  exact ⟨F, hF, hFin, hq, ⟨((MulEquiv.subgroupCongr hγrange).symm.trans
    (QuotientGroup.quotientKerEquivRange γ).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hγker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))⟩⟩

theorem le_normalizer_iff_range_le_normalizer {H Y : Subgroup G} (hYH : Y ≤ H)
    (hOY : oddCoreIn H ≤ Y) {B : Type*} [Group B] {ι : ↥H ⧸ CFSG.oddCore ↥H →* B}
    (hι : Function.Injective ι) :
    H ≤ Subgroup.normalizer (Y : Set G) ↔ ι.range ≤ Subgroup.normalizer
      ((((Y.subgroupOf H).map (QuotientGroup.mk' (CFSG.oddCore ↥H))).map ι : Subgroup B) :
        Set B) := by
  have hOY' : CFSG.oddCore ↥H ≤ Y.subgroupOf H := fun o ho => hOY ⟨o, ho, rfl⟩
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hYH, ← normal_map_mk'_iff _ hOY',
    normal_iff_range_le_normalizer_map hι]

theorem oddCoreIn_inf_N_eq_ON_inf {H : Subgroup G} (hON₁ : oddCoreIn H ⊓ σ.N ≤ σ.ON)
    (hON₂ : σ.ON ⊓ H ≤ oddCoreIn H) : oddCoreIn H ⊓ σ.N = σ.ON ⊓ H :=
  le_antisymm (le_inf hON₁ (inf_le_left.trans (oddCoreIn_le H)))
    (le_inf hON₂ (inf_le_left.trans σ.ON_le_N))

theorem exists_quotient_embedding_of_factorization {H : Subgroup G}
    (hfac : oddCoreIn H ⊔ (H ⊓ σ.N) = H) (hON₁ : oddCoreIn H ⊓ σ.N ≤ σ.ON)
    (hON₂ : σ.ON ⊓ H ≤ oddCoreIn H) :
    ∃ ι : (↥H ⧸ CFSG.oddCore ↥H) →* (↥σ.N ⧸ σ.ON.subgroupOf σ.N), Function.Injective ι ∧
      (∀ (h : ↥H) (hN : (h : G) ∈ σ.N),
        ι (QuotientGroup.mk h) = QuotientGroup.mk (⟨h, hN⟩ : ↥σ.N)) ∧
      (∀ x : ↥H ⧸ CFSG.oddCore ↥H, ∃ (h : ↥H) (_ : (h : G) ∈ σ.N),
        (QuotientGroup.mk h : ↥H ⧸ CFSG.oddCore ↥H) = x) ∧
      ι.range = ((H ⊓ σ.N).subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)) := by
  let α : ↥(H ⊓ σ.N) →* ↥H ⧸ CFSG.oddCore ↥H :=
    (QuotientGroup.mk' (CFSG.oddCore ↥H)).comp (Subgroup.inclusion inf_le_left)
  let β : ↥(H ⊓ σ.N) →* ↥σ.N ⧸ σ.ON.subgroupOf σ.N :=
    (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)).comp (Subgroup.inclusion inf_le_right)
  have hcoe : ((oddCoreIn H ⊔ (H ⊓ σ.N) : Subgroup G) : Set G) =
      (oddCoreIn H : Set G) * ((H ⊓ σ.N : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (inf_le_left.trans (le_normalizer_oddCoreIn H))
  have hα : Function.Surjective α := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    have hh : (h : G) ∈ ((oddCoreIn H ⊔ (H ⊓ σ.N) : Subgroup G) : Set G) := by
      rw [hfac]
      exact h.2
    rw [hcoe] at hh
    obtain ⟨o, ho, a, ha, hoa⟩ := Set.mem_mul.mp hh
    obtain ⟨o', ho', rfl⟩ := ho
    refine ⟨⟨a, ha⟩, ?_⟩
    change (QuotientGroup.mk (⟨a, ha.1⟩ : ↥H) : ↥H ⧸ CFSG.oddCore ↥H) = QuotientGroup.mk h
    rw [QuotientGroup.eq]
    have e : (⟨a, ha.1⟩ : ↥H)⁻¹ * h =
        (⟨a, ha.1⟩ : ↥H)⁻¹ * o' * (⟨a, ha.1⟩ : ↥H)⁻¹⁻¹ := by
      apply Subtype.ext
      have hoa' : (o' : G) * a = h := hoa
      change a⁻¹ * (h : G) = a⁻¹ * o' * a⁻¹⁻¹
      rw [← hoa']
      group
    rw [e]
    exact (CFSG.oddCore_normal _).conj_mem o' ho' _
  have hker : α.ker ≤ β.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    change (QuotientGroup.mk (⟨a, a.2.1⟩ : ↥H) : ↥H ⧸ CFSG.oddCore ↥H) = 1 at ha
    change (QuotientGroup.mk (⟨a, a.2.2⟩ : ↥σ.N) : ↥σ.N ⧸ σ.ON.subgroupOf σ.N) = 1
    rw [QuotientGroup.eq_one_iff] at ha ⊢
    exact hON₁ ⟨⟨_, ha, rfl⟩, a.2.2⟩
  have hker' : β.ker ≤ α.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    change (QuotientGroup.mk (⟨a, a.2.2⟩ : ↥σ.N) : ↥σ.N ⧸ σ.ON.subgroupOf σ.N) = 1 at ha
    change (QuotientGroup.mk (⟨a, a.2.1⟩ : ↥H) : ↥H ⧸ CFSG.oddCore ↥H) = 1
    rw [QuotientGroup.eq_one_iff] at ha ⊢
    obtain ⟨o, ho, hoa⟩ := hON₂ ⟨ha, a.2.1⟩
    have e : o = ⟨a, a.2.1⟩ := Subtype.ext hoa
    rw [← e]
    exact ho
  let ι := MonoidHom.liftOfRightInverse α (Function.surjInv hα)
    (Function.rightInverse_surjInv hα) ⟨β, hker⟩
  have hια : ∀ a, ι (α a) = β a := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hα)
      (Function.rightInverse_surjInv hα) ⟨β, hker⟩ a
  refine ⟨ι, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨a, rfl⟩ := hα x
    rw [hια] at hx
    exact hker' hx
  · intro h hN
    exact hια ⟨h, h.2, hN⟩
  · intro x
    obtain ⟨a, rfl⟩ := hα x
    exact ⟨⟨a, a.2.1⟩, a.2.2, rfl⟩
  · have hrange : ι.range = β.range := by
      rw [MonoidHom.range_eq_map, ← MonoidHom.range_eq_top.mpr hα, ← MonoidHom.range_comp]
      congr 1
      ext a
      exact hια a
    rw [hrange, MonoidHom.range_comp, Subgroup.inclusion_range]

theorem map_image_of_le_inf_N {H : Subgroup G}
    {ι : (↥H ⧸ CFSG.oddCore ↥H) →* (↥σ.N ⧸ σ.ON.subgroupOf σ.N)}
    (hι : ∀ (h : ↥H) (hN : (h : G) ∈ σ.N),
      ι (QuotientGroup.mk h) = QuotientGroup.mk (⟨h, hN⟩ : ↥σ.N))
    {X : Subgroup G} (hX : X ≤ H ⊓ σ.N) :
    ((X.subgroupOf H).map (QuotientGroup.mk' (CFSG.oddCore ↥H))).map ι =
      (X.subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)) := by
  ext y
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨⟨h, (hX hh).2⟩, hh, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hι h (hX hh).2]
  · rintro ⟨n, hn, rfl⟩
    refine ⟨QuotientGroup.mk' (CFSG.oddCore ↥H) ⟨n, (hX hn).1⟩, ⟨⟨n, (hX hn).1⟩, hn, rfl⟩, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hι ⟨n, (hX hn).1⟩ n.2]

theorem LBar_le_of_subset_mul {H : Subgroup G}
    (hLH : (σ.L : Set G) ⊆ (H : Set G) * (σ.ON : Set G)) :
    σ.LBar ≤ ((H ⊓ σ.N).subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)) := by
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨h, hh, o, ho, hho⟩ := hLH hl
  have hho : h * o = (l : G) := hho
  have hoN : o ∈ σ.N := σ.ON_le_N ho
  have hhN : h ∈ σ.N := by
    have : h = (l : G) * o⁻¹ := by rw [← hho, mul_inv_cancel_right]
    rw [this]
    exact σ.N.mul_mem l.2 (σ.N.inv_mem hoN)
  refine ⟨⟨h, hhN⟩, ⟨hh, hhN⟩, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  change (⟨h, hhN⟩ : ↥σ.N)⁻¹ * l ∈ σ.ON.subgroupOf σ.N
  rw [Subgroup.mem_subgroupOf]
  change h⁻¹ * (l : G) ∈ σ.ON
  rw [← hho, inv_mul_cancel_left]
  exact ho

theorem exists_quotient_embedding_of_mem_familyL [Finite G] (hσ : σ.IsValid)
    (hII : σ.ChapterIIFacts) {r : ℕ} (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON)
    {H : Subgroup G} (hH : H ∈ σ.familyL r) :
    ∃ ι : (↥H ⧸ CFSG.oddCore ↥H) →* (↥σ.N ⧸ σ.ON.subgroupOf σ.N), Function.Injective ι ∧
      (∀ (h : ↥H) (hN : (h : G) ∈ σ.N),
        ι (QuotientGroup.mk h) = QuotientGroup.mk (⟨h, hN⟩ : ↥σ.N)) ∧
      (∀ x : ↥H ⧸ CFSG.oddCore ↥H, ∃ (h : ↥H) (_ : (h : G) ∈ σ.N),
        (QuotientGroup.mk h : ↥H ⧸ CFSG.oddCore ↥H) = x) ∧
      ι.range = ((H ⊓ σ.N).subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)) ∧
      σ.LBar ≤ ι.range := by
  obtain ⟨-, hfac, hLH, -, ⟨hON₁, hON₂⟩, -⟩ := σ.familyL_properties hσ hII hr hdiv hH
  obtain ⟨ι, hinj, hcomp, hsurj, hrange⟩ :=
    σ.exists_quotient_embedding_of_factorization hfac hON₁ hON₂
  exact ⟨ι, hinj, hcomp, hsurj, hrange, hrange ▸ σ.LBar_le_of_subset_mul hLH⟩

theorem D_le_inf_N_of_mem_familyL [Finite G] (hσ : σ.IsValid) {r : ℕ} {H : Subgroup G}
    (hH : H ∈ σ.familyL r) : σ.D ≤ H ⊓ σ.N := by
  obtain ⟨-, -, hDH, -⟩ := hH
  exact le_inf hDH (σ.D_le_N hσ)

theorem inf_L_le_inf_N [Finite G] (hσ : σ.IsValid) (H : Subgroup G) : H ⊓ σ.L ≤ H ⊓ σ.N :=
  inf_le_inf_left _ (sup_le hσ.L₀_le_N (σ.S_le_N hσ))

theorem map_solvableRadical_quotient_of_mem_familyL [Finite G] (hσ : σ.IsValid)
    (hII : σ.ChapterIIFacts) {r : ℕ} (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON)
    {H : Subgroup G} (hH : H ∈ σ.familyL r)
    {ι : (↥H ⧸ CFSG.oddCore ↥H) →* (↥σ.N ⧸ σ.ON.subgroupOf σ.N)}
    (hι : ∀ (h : ↥H) (hN : (h : G) ∈ σ.N),
      ι (QuotientGroup.mk h) = QuotientGroup.mk (⟨h, hN⟩ : ↥σ.N)) :
    (CFSG.solvableRadical (↥H ⧸ CFSG.oddCore ↥H)).map ι =
      ((centerOf σ.D).subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)) := by
  have hDHN := σ.D_le_inf_N_of_mem_familyL hσ hH
  obtain ⟨hloc, hcov, hDH, -⟩ := hH
  have hO : oddCoreIn H ≠ ⊥ :=
    oddCoreIn_ne_bot_of_isPLocal hr (σ.prime_ne_two_of_dvd_ON hr hdiv) hloc
  have hS := hII.qgroup_solvRad H hDH hO hcov
  have hZ : centerOf σ.D ≤ H ⊓ σ.N := inf_le_left.trans hDHN
  rw [solvableRadical_quotient_oddCore, ← σ.map_image_of_le_inf_N hι hZ]
  congr 1
  have hSH : CFSG.solvableRadical ↥H = (oddCoreIn H ⊔ centerOf σ.D).subgroupOf H := by
    rw [← hS, solvRadIn]
    exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm
  rw [hSH]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hcoe : ((oddCoreIn H ⊔ centerOf σ.D : Subgroup G) : Set G) =
        (oddCoreIn H : Set G) * (centerOf σ.D : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _
        ((hZ.trans inf_le_left).trans (le_normalizer_oddCoreIn H))
    have hx' : (x : G) ∈ ((oddCoreIn H ⊔ centerOf σ.D : Subgroup G) : Set G) := hx
    rw [hcoe] at hx'
    obtain ⟨o, ho, z, hz, hoz⟩ := Set.mem_mul.mp hx'
    obtain ⟨o', ho', rfl⟩ := ho
    refine ⟨⟨z, (hZ hz).1⟩, hz, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : (⟨z, (hZ hz).1⟩ : ↥H)⁻¹ * x =
        (⟨z, (hZ hz).1⟩ : ↥H)⁻¹ * o' * (⟨z, (hZ hz).1⟩ : ↥H)⁻¹⁻¹ := by
      apply Subtype.ext
      have hoz' : (o' : G) * z = x := hoz
      change z⁻¹ * (x : G) = z⁻¹ * o' * z⁻¹⁻¹
      rw [← hoz']
      group
    rw [e]
    exact (CFSG.oddCore_normal _).conj_mem o' ho' _
  · exact Subgroup.map_mono fun _ hx => (le_sup_right : centerOf σ.D ≤ _) hx

theorem L₀Bar_comap_properties [Finite G] (hσ : σ.IsValid) {H : Subgroup G}
    {ι : (↥H ⧸ CFSG.oddCore ↥H) →* (↥σ.N ⧸ σ.ON.subgroupOf σ.N)} (hι : Function.Injective ι)
    (hL : σ.L₀Bar ≤ ι.range) :
    (σ.L₀Bar.comap ι).Normal ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
        Nonempty (σ.L₀Bar.comap ι ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      (Subgroup.centralizer ((σ.L₀Bar.comap ι : Subgroup _) : Set (↥H ⧸ CFSG.oddCore ↥H))).map
        ι = ι.range ⊓ Subgroup.centralizer (σ.L₀Bar : Set (↥σ.N ⧸ σ.ON.subgroupOf σ.N)) := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := σ.exists_L₀Bar_mulEquiv hσ
  have := σ.L₀Bar_normal hσ
  refine ⟨(normal_comap_iff_range_le_normalizer hι hL).mpr Subgroup.le_normalizer_of_normal,
    ⟨F, hF, hFin, hq,
      ⟨(((σ.L₀Bar.comap ι).equivMapOfInjective ι hι).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hL))).trans e⟩⟩,
    map_centralizer_comap_eq_range_inf hι hL⟩

theorem hasNormalSL2_of_L₀Bar_le_range [Finite G] (hσ : σ.IsValid) {H : Subgroup G}
    {ι : (↥H ⧸ CFSG.oddCore ↥H) →* (↥σ.N ⧸ σ.ON.subgroupOf σ.N)} (hι : Function.Injective ι)
    (hL : σ.L₀Bar ≤ ι.range) : HasNormalSL2 (↥H ⧸ CFSG.oddCore ↥H) σ.q := by
  obtain ⟨hn, ⟨F, hF, hFin, hq, ⟨e⟩⟩, -⟩ := σ.L₀Bar_comap_properties hσ hι hL
  exact ⟨σ.L₀Bar.comap ι, F, hF, hFin, hn, hq, ⟨e⟩⟩

end CFSG.ABGTheoremB.Setting
