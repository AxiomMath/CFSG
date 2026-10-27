module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndUnitary
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndLift
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint CFSG.ClassicalInvolution.WeakCT
open scoped Pointwise MatrixGroups

section Generic

variable {G : Type} [Group G] {G' : Type} [Group G']

theorem map_conjR (φ : G' →* G) (X : Subgroup G') (g : G') :
    (conjR X g).map φ = conjR (X.map φ) (φ g) := by
  rw [conjR, conjR, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem le_of_perfect_of_map_le {M A₁ A₂ : Subgroup G} (δ : M →* G)
    (hker : ∀ x : M, δ x = 1 → (x : G) ∈ centralizer (M : Set G)) (hA₁ : A₁ ≤ M) (hA₂ : A₂ ≤ M)
    (hperf : ⁅A₁, A₁⁆ = A₁)
    (h : ∀ a (ha : a ∈ A₁), ∃ b, ∃ hb : b ∈ A₂, δ ⟨a, hA₁ ha⟩ = δ ⟨b, hA₂ hb⟩) : A₁ ≤ A₂ := by
  set Z : Subgroup G := δ.ker.map M.subtype with hZ
  have hZC : Z ≤ centralizer (M : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hker x hx
  have hZM : Z ≤ M := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hle : A₁ ≤ A₂ ⊔ Z := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := h a ha
    have hk : (⟨b, hA₂ hb⟩ : M)⁻¹ * ⟨a, hA₁ ha⟩ ∈ δ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have : a = b * (b⁻¹ * a) := by group
    rw [this]
    exact mul_mem (mem_sup_left hb) (mem_sup_right ⟨_, hk, rfl⟩)
  have hAZ : ∀ x ∈ A₂, ∀ z ∈ Z, x * z = z * x := fun x hx z hz =>
    (mem_centralizer_iff.mp (hZC hz) x (hA₂ hx))
  have hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := fun z hz z' hz' =>
    (mem_centralizer_iff.mp (hZC hz') z (hZM hz))
  rw [← hperf]
  exact (commutator_mono hle hle).trans (YamadaSection4.commutator_sup_le hAZ hZZ)

theorem card_center_SL_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card (center SL(3, F)) = 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
  simp only [Fintype.card_fin]
  have hU : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have htop : rootsOfUnity (max 3 1) F = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rw [mem_rootsOfUnity]
    have := pow_card_eq_one' (G := Fˣ) (x := u)
    rw [hU] at this
    simpa using this
  rw [htop, Subgroup.card_top, hU]

theorem IsCentralPair.diag_comm {R M : Subgroup G} {t : G} (ht : t * t = 1)
    (hp : IsCentralPair R M t) :
    ∀ u ∈ M, ∀ v ∈ M, v * (t * u * t⁻¹) = t * u * t⁻¹ * v := by
  have hMC : M ≤ centralizer (conjR M t : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp hp.comm
  exact fun u hu v hv => (mem_centralizer_iff.mp (hMC hv) _ (conj_mem_conjR_of_sq ht hu)).symm

theorem rootPair_diag_le {M U X : Subgroup G} {t w : G}
    (hc : ∀ u ∈ M, ∀ v ∈ M, v * (t * u * t⁻¹) = t * u * t⁻¹ * v) (htw : t * w = w * t)
    (hwM : w ∈ normalizer (M : Set G)) (hX : ∀ y ∈ U ⊓ M, y * (t * y * t⁻¹) ∈ X) :
    ∀ z ∈ rootPair U M w, z * (t * z * t⁻¹) ∈ X ⊔ conjR X w := by
  have key : rootPair U M w ≤ ((X ⊔ conjR X w).comap (diagHom M t hc)).map M.subtype := by
    refine sup_le (fun v hv => ⟨⟨v, hv.2⟩, mem_sup_left (hX v hv), rfl⟩) ?_
    intro x hx
    have hy : w * x * w⁻¹ ∈ U ⊓ M := mem_conjR.mp hx
    have hxM : x ∈ M := rootPair_le hwM (mem_sup_right hx)
    have hxy : x = w⁻¹ * (w * x * w⁻¹) * w := by group
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    change (diagHom M t hc) ⟨x, hxM⟩ ∈ X ⊔ conjR X w
    rw [diagHom_apply]
    refine mem_sup_right (mem_conjR.mpr ?_)
    change w * (x * (t * x * t⁻¹)) * w⁻¹ ∈ X
    rw [hxy, conj_mul_conj_eq htw]
    convert hX _ hy using 1
    group
  intro z hz
  obtain ⟨m, hm, hmz⟩ := key hz
  rw [← hmz]
  exact hm

theorem le_rootPair_diag {M U X : Subgroup G} {t w : G}
    (hc : ∀ u ∈ M, ∀ v ∈ M, v * (t * u * t⁻¹) = t * u * t⁻¹ * v) (htw : t * w = w * t)
    (hwM : w ∈ normalizer (M : Set G)) (hX : ∀ x ∈ X, ∃ y ∈ U ⊓ M, x = y * (t * y * t⁻¹)) :
    ∀ x ∈ X ⊔ conjR X w, ∃ z ∈ rootPair U M w, x = z * (t * z * t⁻¹) := by
  have hZM : rootPair U M w ≤ M := rootPair_le hwM
  let ψ : rootPair U M w →* G := (diagHom M t hc).comp (inclusion hZM)
  have hψ : ∀ z, ψ z = (z : G) * (t * z * t⁻¹) := fun z => rfl
  have hle : X ⊔ conjR X w ≤ ψ.range := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, hy, rfl⟩ := hX x hx
      exact ⟨⟨y, mem_sup_left hy⟩, rfl⟩
    · obtain ⟨y, hy, hyx⟩ := hX _ (mem_conjR.mp hx)
      have hyw : w⁻¹ * y * w ∈ rootPair U M w := mem_sup_right (conj_mem_conjR hy)
      refine ⟨⟨_, hyw⟩, ?_⟩
      rw [hψ]
      change w⁻¹ * y * w * (t * (w⁻¹ * y * w) * t⁻¹) = x
      rw [conj_mul_conj_eq htw, ← hyx]
      group
  intro x hx
  obtain ⟨z, hz⟩ := hle hx
  exact ⟨z, z.2, hz.symm⟩

end Generic

section Pairs

variable {G : Type} [Group G] {F : Type} [Field F]

theorem map_conj_one_inv (H : Subgroup SL(3, F)) :
    H.map (MulAut.conj (1 : SL(3, F))⁻¹).toMonoidHom = H := by
  ext x
  simp

theorem map_codRestrict_eq_subgroupOf {K : Subgroup G} (θ : SL(3, F) →* G) (hθK : ∀ A, θ A ∈ K)
    (H : Subgroup SL(3, F)) : H.map (θ.codRestrict K hθK) = (H.map θ).subgroupOf K := by
  ext x
  rw [mem_subgroupOf]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, rfl⟩
  · rintro ⟨A, hA, hAx⟩
    exact ⟨A, hA, Subtype.ext hAx⟩

theorem linearBlockStandardPair_of_map {K : Subgroup G} (θ : SL(3, F) →* G)
    (hθK : ∀ A, θ A ∈ K) (hker : θ.ker ≤ center SL(3, F)) {U V : Subgroup G}
    (hU : (B12 F).map θ = U) (hV : (B23 F).map θ = V) :
    LinearBlockStandardPair F (θ.codRestrict K hθK).range (U.subgroupOf K) (V.subgroupOf K) := by
  refine ⟨θ.codRestrict K hθK, 1, rfl, ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.ker_codRestrict]
    exact hker
  · rw [map_conj_one_inv, map_codRestrict_eq_subgroupOf, hU]
  · rw [map_conj_one_inv, map_codRestrict_eq_subgroupOf, hV]

theorem linearBlockStandardPair_of_map' {K : Subgroup G} (θ : SL(3, F) →* G)
    (hθK : ∀ A, θ A ∈ K) (hker : θ.ker ≤ center SL(3, F)) {U V : Subgroup G}
    (hU : (B23 F).map θ = U) (hV : (B12 F).map θ = V) :
    LinearBlockStandardPair F (θ.codRestrict K hθK).range (U.subgroupOf K) (V.subgroupOf K) := by
  refine ⟨θ.codRestrict K hθK, 1, rfl, ?_, Or.inr ⟨?_, ?_⟩⟩
  · rw [MonoidHom.ker_codRestrict]
    exact hker
  · rw [map_conj_one_inv, map_codRestrict_eq_subgroupOf, hV]
  · rw [map_conj_one_inv, map_codRestrict_eq_subgroupOf, hU]

theorem mul_comm_of_commutator_eq_bot {A B K : Subgroup G} (h : ⁅A, B⁆ = ⊥) :
    ∀ x ∈ A.subgroupOf K, ∀ y ∈ B.subgroupOf K, x * y = y * x := by
  intro x hx y hy
  have hAC : A ≤ centralizer (B : Set G) := (commutator_eq_bot_iff_le_centralizer).mp h
  exact Subtype.ext (mem_centralizer_iff.mp (hAC hx) y hy).symm

theorem iSup_subgroupOf_eq_top {ι : Type*} {K : Subgroup G} (Y : ι → Subgroup G)
    (h : ⨆ i, Y i = K) : ⨆ i, (Y i).subgroupOf K = ⊤ := by
  apply map_injective K.subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
  simp only [subgroupOf_map_subtype]
  rw [← h]
  exact iSup_congr fun i => inf_of_le_left (le_iSup Y i)

theorem commutator_range_eq {A B : Type} [Group A] [Group B] [Group.IsPerfect A] (f : A →* B) :
    ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

end Pairs

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
  {d : YamadaData G}

namespace YamadaSection4

variable (h : YamadaSection4 F d)
include h

theorem K₂_perfect : ⁅d.K₂, d.K₂⁆ = d.K₂ := by
  obtain ⟨θ, hθ, -, -, -⟩ := h.K₂_pair
  have : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  rw [← hθ, MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem diag_mem_K₂ {M : Subgroup G} (hp : IsCentralPair d.L₂ M d.t) {m : G} (hm : m ∈ M) :
    m * (d.t * m * d.t⁻¹) ∈ d.K₂ := by
  rw [← h.L₂_facts.1]
  exact ⟨mul_mem (hp.le hm) (hp.le' (conj_mem_conjR_of_sq h.t_sq hm)),
    diagHom_mem_centralizer (hp.diag_comm h.t_sq) h.t_sq ⟨m, hm⟩⟩

theorem K₂_le_range {M : Subgroup G} (hp : IsCentralPair d.L₂ M d.t) :
    d.K₂ ≤ (diagHom M d.t (hp.diag_comm h.t_sq)).range :=
  le_range_diagHom hp.comm (fun _ ha => conj_mem_conjR_of_sq h.t_sq ha)
    (fun _ ha => conj_mem_of_mem_conjR ha) _ (hp.sup_eq.symm ▸ h.K₂_le_L₂)
    (h.K₂_le.trans h.L_le_H) h.K₂_perfect

theorem X₁_diag {M : Subgroup G} (hp : IsCentralPair d.L₂ M d.t) :
    ∀ x ∈ d.X₁, ∃ y ∈ d.Ua ⊓ M, x = y * (d.t * y * d.t⁻¹) := by
  intro x hx
  rw [← h.Ua_inf_H] at hx
  obtain ⟨hxU, hxH⟩ := hx
  have hmul : x ∈ ((d.Ua ⊓ M : Subgroup G) : Set G) *
      ((d.Ua ⊓ conjR M d.t : Subgroup G) : Set G) := by
    rw [← coe_sup_eq_mul hp.comm inf_le_right inf_le_right, ← h.Ua_decomp hp]
    exact hxU
  obtain ⟨y, hy, z, hz, rfl⟩ := hmul
  have hc1 : y * z * d.t = d.t * (y * z) := mem_centralizer_singleton_iff.mp hxH
  have hfix : d.t * (y * z) * d.t⁻¹ = y * z := by rw [← hc1, mul_inv_cancel_right]
  have hty : d.t * y * d.t⁻¹ ∈ conjR M d.t := conj_mem_conjR_of_sq h.t_sq hy.2
  have htz : d.t * z * d.t⁻¹ ∈ M := conj_mem_of_mem_conjR hz.2
  have hMC : M ≤ centralizer (conjR M d.t : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp hp.comm
  have heq : y * z = d.t * z * d.t⁻¹ * (d.t * y * d.t⁻¹) := by
    rw [(mem_centralizer_iff.mp (hMC htz) _ hty).symm, ← hfix]
    group
  have hUa2 : IsPGroup 2 d.Ua :=
    h.isPGroup_P.to_le (inf_le_left.trans inf_le_left)
  have h2 : ∀ u ∈ d.Ua, ∃ k : ℕ, u ^ 2 ^ k = 1 := fun u hu => by
    obtain ⟨k, hk⟩ := hUa2 ⟨u, hu⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨k, hk⟩ := h2 y hy.1
  obtain ⟨k', hk'⟩ := h2 _ ((mem_normalizer_iff.mp h.t_Ua z).mp hz.1)
  obtain ⟨-, hz'⟩ := eq_of_mul_eq_mul hp.comm hp.odd hy.2 htz hz.2 hty heq hk hk'
  exact ⟨y, hy, by rw [hz']⟩

theorem Ub_diag {M : Subgroup G} (hp : IsCentralPair d.L₂ M d.t) :
    ∀ y ∈ d.Ub ⊓ M, y * (d.t * y * d.t⁻¹) ∈ d.X₂ := fun y hy => by
  rw [← h.Ub_inf_H]
  exact ⟨mul_mem hy.1 ((mem_normalizer_iff.mp h.t_Ub y).mp hy.1),
    diagHom_mem_centralizer (hp.diag_comm h.t_sq) h.t_sq ⟨y, hy.2⟩⟩

theorem exists_M_linear {Y₂ Y₄ : Subgroup G} (hq : CFSG.Open.IsQuasisimple Y₂)
    (hYb : d.Yb = Y₂ ⊔ Y₄) (hc : ⁅Y₂, Y₄⁆ = ⊥) :
    ∃ M : Subgroup G, IsCentralPair d.L₂ M d.t ∧ ⁅M, M⁆ = M ∧ Y₂ ≤ rootPair d.Ub M d.w₂ := by
  obtain ⟨M, hn, hn', hsup, hc', hodd, θ, hθ, -⟩ := h.L₂_components
  have hp : IsCentralPair d.L₂ M d.t := ⟨hn, hn', hsup, hc', hodd⟩
  have hperf : ⁅M, M⁆ = M := by
    have : Group.IsPerfect SL(3, F) := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le
      (by norm_num)
    have : Group.IsPerfect M := Group.IsPerfect.ofSurjective hθ
    exact YamadaEnd.commutator_eq_self_of_isPerfect this
  have htw : d.t * d.w₂ = d.w₂ * d.t := t_comm_of_mem_H h.w₂_H
  have hYb' : d.Yb = rootPair d.Ub M d.w₂ ⊔ conjR (rootPair d.Ub M d.w₂) d.t :=
    sup_conjR_eq_rootPair h.t_Ub htw (h.Ub_decomp₂ hp)
  have hZM : rootPair d.Ub M d.w₂ ≤ M := rootPair_le (hn (h.K₂_le_L₂ h.w₂_K₂))
  have hZc : ⁅rootPair d.Ub M d.w₂, conjR (rootPair d.Ub M d.w₂) d.t⁆ = ⊥ :=
    le_bot_iff.mp (hc' ▸ commutator_mono hZM (conjR_mono hZM d.t))
  have hN : d.Yb ≤ normalizer (Y₂ : Set G) := by
    rw [hYb]
    have hY₄C : Y₄ ≤ centralizer (Y₂ : Set G) :=
      (commutator_eq_bot_iff_le_centralizer).mp (by rw [commutator_comm]; exact hc)
    exact sup_le le_normalizer (hY₄C.trans (centralizer_le_normalizer _))
  rcases le_or_le_of_quasisimple hq hZc ((le_sup_left.trans hYb.ge).trans hYb'.le)
      (hYb'.ge.trans hN) with hle | hle
  · exact ⟨M, hp, hperf, hle⟩
  · refine ⟨conjR M d.t, hp.swap h.t_sq, by rw [← conjR_commutator, hperf], ?_⟩
    rwa [← conjR_rootPair h.t_Ub htw]

theorem exists_theta
    {M : Subgroup G} (hp : IsCentralPair d.L₂ M d.t) (hperf : ⁅M, M⁆ = M)
    (θK : SL(3, F) →* G) (hθK : θK.range = d.K₂) (hθKker : θK.ker = center SL(3, F)) :
    ∃ θ : SL(3, F) →* G, θ.range = M ∧ ∀ A, θ A * (d.t * θ A * d.t⁻¹) = θK A := by
  have hc := hp.diag_comm h.t_sq
  have hK := h.K₂_le_range hp
  have hδK : ∀ m : M, diagHom M d.t hc m ∈ d.K₂ := fun m => h.diag_mem_K₂ hp m.2
  let δ : M →* d.K₂ := (diagHom M d.t hc).codRestrict d.K₂ hδK
  have hδ : Function.Surjective δ := by
    rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := hK hk
    exact ⟨m, Subtype.ext hm⟩
  have hδker' : ∀ m : M, diagHom M d.t hc m = 1 → (m : G) ∈ M ⊓ conjR M d.t := by
    intro m hm
    have h2 : d.t * m * d.t⁻¹ = (m : G)⁻¹ := eq_inv_of_mul_eq_one_right hm
    refine ⟨m.2, ?_⟩
    have := conj_mem_conjR_of_sq h.t_sq m.2
    rw [h2] at this
    simpa using (conjR M d.t).inv_mem this
  have hMC' : conjR M d.t ≤ centralizer (M : Set G) :=
    le_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer).mp hp.comm)
  have hδker : δ.ker ≤ center M := fun m hm =>
    mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp
      (hMC' (hδker' m (congrArg Subtype.val (MonoidHom.mem_ker.mp hm))).2) y y.2)
  have hodd : Odd (Nat.card δ.ker) := by
    have hle : δ.ker.map M.subtype ≤ M ⊓ conjR M d.t := by
      rintro _ ⟨m, hm, rfl⟩
      exact hδker' m (congrArg Subtype.val (MonoidHom.mem_ker.mp hm))
    have h1 := card_dvd_of_le hle
    rw [card_map_of_injective M.subtype_injective] at h1
    exact Odd.of_dvd_nat hp.odd h1
  have hχK : ∀ A, θK A ∈ d.K₂ := fun A => hθK ▸ ⟨A, rfl⟩
  let χ : SL(3, F) →* d.K₂ := θK.codRestrict d.K₂ hχK
  have hχ : Function.Surjective χ := by
    rintro ⟨k, hk⟩
    rw [← hθK] at hk
    obtain ⟨A, hA⟩ := hk
    exact ⟨A, Subtype.ext hA⟩
  have hχker : χ.ker = center SL(3, F) := by rw [MonoidHom.ker_codRestrict, hθKker]
  have : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  obtain ⟨θ', hθ'⟩ := exists_lift h.K₂_lie χ hχ hχker (card_center_SL_three h.card_field) δ hδ
    hδker hodd
  have hval : ∀ A, (θ' A : G) * (d.t * θ' A * d.t⁻¹) = θK A := fun A =>
    congrArg (fun f : SL(3, F) →* d.K₂ => ((f A : d.K₂) : G)) hθ'
  refine ⟨M.subtype.comp θ', ?_, hval⟩
  have hle : (M.subtype.comp θ').range ≤ M := by
    rintro _ ⟨A, rfl⟩
    exact (θ' A).2
  refine le_antisymm hle (le_of_perfect_of_map_le (diagHom M d.t hc)
    (fun x hx => hMC' (hδker' x hx).2) le_rfl hle hperf fun a ha => ?_)
  obtain ⟨A, hA⟩ := hχ ⟨_, hδK ⟨a, ha⟩⟩
  refine ⟨θ' A, ⟨A, rfl⟩, ?_⟩
  have h1 := congrArg Subtype.val hA
  change θK A = diagHom M d.t hc ⟨a, ha⟩ at h1
  rw [← h1, ← hval A]
  rfl

theorem diag_ker_mem {M : Subgroup G} (hp : IsCentralPair d.L₂ M d.t) (x : M)
    (hx : diagHom M d.t (hp.diag_comm h.t_sq) x = 1) : (x : G) ∈ conjR M d.t := by
  have h2 : d.t * x * d.t⁻¹ = (x : G)⁻¹ := eq_inv_of_mul_eq_one_right hx
  have := conj_mem_conjR_of_sq h.t_sq x.2
  rw [h2] at this
  simpa using (conjR M d.t).inv_mem this

theorem map_B23_eq {M Y₂ : Subgroup G} (hp : IsCentralPair d.L₂ M d.t) {θK θ : SL(3, F) →* G}
    (hB₂ : (B23 F).map θK = d.X₂ ⊔ conjR d.X₂ d.w₂) (hθr : θ.range = M)
    (hθd : ∀ A, θ A * (d.t * θ A * d.t⁻¹) = θK A) (hθker : θ.ker ≤ center SL(3, F))
    (hY₂Z : Y₂ ≤ rootPair d.Ub M d.w₂) (hperf₂ : ⁅Y₂, Y₂⁆ = Y₂)
    (hcard : Nat.card Y₂ = Nat.card SL(2, F)) : (B23 F).map θ = Y₂ := by
  have hc := hp.diag_comm h.t_sq
  have hw₂M : d.w₂ ∈ normalizer (M : Set G) := hp.normal (h.K₂_le_L₂ h.w₂_K₂)
  have hMC' : conjR M d.t ≤ centralizer (M : Set G) :=
    le_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer).mp hp.comm)
  have hVM : (B23 F).map θ ≤ M := hθr ▸ map_le_range θ (B23 F)
  have hle : Y₂ ≤ (B23 F).map θ := by
    refine le_of_perfect_of_map_le (diagHom M d.t hc) (fun x hx => hMC' (h.diag_ker_mem hp x hx))
      (hY₂Z.trans (rootPair_le hw₂M)) hVM hperf₂ fun a ha => ?_
    have h1 := rootPair_diag_le hc (t_comm_of_mem_H h.w₂_H) hw₂M (h.Ub_diag hp) a (hY₂Z ha)
    rw [← hB₂] at h1
    obtain ⟨B, hB, hBa⟩ := h1
    refine ⟨θ B, ⟨B, hB, rfl⟩, ?_⟩
    rw [diagHom_apply, diagHom_apply]
    change a * (d.t * a * d.t⁻¹) = θ B * (d.t * θ B * d.t⁻¹)
    rw [hθd, hBa]
  obtain ⟨-, -, hinj, hrange⟩ := pair_block_inj hθker rfl rfl
  have hcardV : Nat.card ((B23 F).map θ) = Nat.card SL(2, F) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  exact (eq_of_le_of_card_ge hle (by rw [hcardV, hcard])).symm

theorem map_B12_le {M : Subgroup G} (hp : IsCentralPair d.L₂ M d.t) {θK θ : SL(3, F) →* G}
    (hB₁ : (B12 F).map θK = d.X₁ ⊔ conjR d.X₁ d.w₁) (hθr : θ.range = M)
    (hθd : ∀ A, θ A * (d.t * θ A * d.t⁻¹) = θK A) :
    (B12 F).map θ ≤ rootPair d.Ua M d.w₁ := by
  have hc := hp.diag_comm h.t_sq
  have hw₁M : d.w₁ ∈ normalizer (M : Set G) := hp.normal (h.K₂_le_L₂ h.w₁_K₂)
  have hMC' : conjR M d.t ≤ centralizer (M : Set G) :=
    le_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer).mp hp.comm)
  have hVM : (B12 F).map θ ≤ M := hθr ▸ map_le_range θ (B12 F)
  have h4 : 4 ≤ Nat.card F := h.card_field.ge
  have : Group.IsPerfect SL(2, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  have hperf : ⁅(B12 F).map θ, (B12 F).map θ⁆ = (B12 F).map θ := by
    rw [B12, ← MonoidHom.range_comp]
    exact commutator_range_eq _
  refine le_of_perfect_of_map_le (diagHom M d.t hc) (fun x hx => hMC' (h.diag_ker_mem hp x hx))
    hVM (rootPair_le hw₁M) hperf fun a ha => ?_
  obtain ⟨B, hB, rfl⟩ := ha
  have h1 : θK B ∈ d.X₁ ⊔ conjR d.X₁ d.w₁ := hB₁ ▸ ⟨B, hB, rfl⟩
  obtain ⟨z, hz, hzB⟩ := le_rootPair_diag hc (t_comm_of_mem_H h.w₁_H) hw₁M (h.X₁_diag hp) _ h1
  refine ⟨z, hz, ?_⟩
  rw [diagHom_apply, diagHom_apply]
  change θ B * (d.t * θ B * d.t⁻¹) = z * (d.t * z * d.t⁻¹)
  rw [hθd, ← hzB]

theorem linearCase_of_coords
    (φ : SL(4, F) →* G) (hφ : Function.Injective φ)
    (hφL : φ.range = d.L₁)
    (hYb : d.Yb = (blockSL2 F 3 0).range.map φ ⊔ (blockSL2 F 3 2).range.map φ)
    (hYc : d.Yc = (blockSL2 F 3 1).range.map φ)
    (hswap : conjR ((blockSL2 F 3 0).range.map φ) d.t = (blockSL2 F 3 2).range.map φ) :
    LinearCase F d.G₀ := by
  set Y₂ := (blockSL2 F 3 0).range.map φ with hY₂
  set Y₃ := (blockSL2 F 3 1).range.map φ with hY₃
  set Y₄ := (blockSL2 F 3 2).range.map φ with hY₄
  have h4 : 4 ≤ Nat.card F := h.card_field.ge
  have hinj₂ : Function.Injective (φ.comp (blockSL2 F 3 0)) := hφ.comp (blockSL2_injective 3 0)
  have hr₂ : (φ.comp (blockSL2 F 3 0)).range = Y₂ := MonoidHom.range_comp _ _
  let e₂ : SL(2, F) ≃* Y₂ := (MonoidHom.ofInjective hinj₂).trans (MulEquiv.subgroupCongr hr₂)
  have hq₂ : CFSG.Open.IsQuasisimple Y₂ := isQuasisimple_of_mulEquiv e₂
    ⟨(CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4).commutator_eq_top,
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4⟩
  have hcard₂ : Nat.card Y₂ = Nat.card SL(2, F) := (Nat.card_congr e₂.toEquiv).symm
  have hc₂₄ : ⁅Y₂, Y₄⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, blockSL2_comm 3 0 2 (by decide) A B]
  obtain ⟨M, hp, hperf, hY₂Z⟩ := h.exists_M_linear hq₂ hYb hc₂₄
  obtain ⟨θK, hθKr, hθKk, hB₁, hB₂⟩ := h.K₂_pair
  obtain ⟨θ, hθr, hθd⟩ := h.exists_theta hp hperf θK hθKr hθKk
  have hθker : θ.ker ≤ center SL(3, F) := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA
    rw [← hθKk, MonoidHom.mem_ker, ← hθd A, hA]
    simp
  have hY₂eq := h.map_B23_eq hp hB₂ hθr hθd hθker hY₂Z (commutator_eq_self_of_quasisimple hq₂)
    hcard₂
  have hY₁Z := h.map_B12_le hp hB₁ hθr hθd
  set Y₁ := (B12 F).map θ with hY₁
  set Y₅ := conjR Y₁ d.t with hY₅
  have hL₂G : d.L₂ ≤ d.G₀ := h.Ya_Yb_eq.ge.trans (le_sup_left : d.Ya ⊔ d.Yb ≤ d.G₀)
  have hMG : M ≤ d.G₀ := hp.le.trans hL₂G
  have hY₁M : Y₁ ≤ M := hθr ▸ map_le_range θ (B12 F)
  have hY₂M : Y₂ ≤ M := hY₂Z.trans (rootPair_le (hp.normal (h.K₂_le_L₂ h.w₂_K₂)))
  have hY₄Mt : Y₄ ≤ conjR M d.t := hswap ▸ conjR_mono hY₂M d.t
  have hY₅Mt : Y₅ ≤ conjR M d.t := conjR_mono hY₁M d.t
  have hY₁Ya : Y₁ ≤ d.Ya := hY₁Z.trans rootPair_le_sup
  have hY₅Ya : Y₅ ≤ d.Ya := (conjR_mono hY₁Ya d.t).trans (conjR_eq_self h.t_Ya).le
  have hcMMt : ∀ {A B : Subgroup G}, A ≤ M → B ≤ conjR M d.t → ⁅A, B⁆ = ⊥ := fun hA hB =>
    le_bot_iff.mp (hp.comm ▸ commutator_mono hA hB)
  have h13 : ⁅Y₁, Y₃⁆ = ⊥ :=
    le_bot_iff.mp (h.commutator_Ya_Yc ▸ commutator_mono hY₁Ya hYc.ge)
  have h14 : ⁅Y₁, Y₄⁆ = ⊥ := hcMMt hY₁M hY₄Mt
  have h15 : ⁅Y₁, Y₅⁆ = ⊥ := hcMMt hY₁M hY₅Mt
  have h25 : ⁅Y₂, Y₅⁆ = ⊥ := hcMMt hY₂M hY₅Mt
  have h35 : ⁅Y₃, Y₅⁆ = ⊥ := by
    rw [commutator_comm]
    exact le_bot_iff.mp (h.commutator_Ya_Yc ▸ commutator_mono hY₅Ya hYc.ge)
  have hMeq : M = Y₁ ⊔ Y₂ := by
    rw [← hθr, MonoidHom.range_eq_map, ← B12_sup_B23, Subgroup.map_sup, hY₂eq]
  have hMt : conjR M d.t = Y₅ ⊔ Y₄ := by rw [hMeq, conjR_sup, hswap]
  have hYa : d.Ya = rootPair d.Ua M d.w₁ ⊔ conjR (rootPair d.Ua M d.w₁) d.t :=
    sup_conjR_eq_rootPair h.t_Ua (t_comm_of_mem_H h.w₁_H) (h.Ua_decomp hp)
  have hYaM : d.Ya ≤ M ⊔ conjR M d.t := by
    rw [hYa]
    have hZ := rootPair_le (U := d.Ua) (hp.normal (h.K₂_le_L₂ h.w₁_K₂))
    exact sup_le_sup hZ (conjR_mono hZ d.t)
  set Yf : Fin 5 → Subgroup G := ![Y₁, Y₂, Y₃, Y₄, Y₅] with hYf
  have hgen : ⨆ i, Yf i = d.G₀ := by
    refine le_antisymm (iSup_le fun i => ?_) ?_
    · have hYbG : d.Yb ≤ d.G₀ := le_sup_right.trans le_sup_left
      fin_cases i
      · exact hY₁Ya.trans (le_sup_left.trans le_sup_left)
      · exact (le_sup_left.trans hYb.ge).trans hYbG
      · exact hYc.ge.trans le_sup_right
      · exact (le_sup_right.trans hYb.ge).trans hYbG
      · exact hY₅Ya.trans (le_sup_left.trans le_sup_left)
    · have hk : ∀ k, Yf k ≤ ⨆ i, Yf i := le_iSup Yf
      have h1 : Y₁ ≤ ⨆ i, Yf i := hk 0
      have h2 : Y₂ ≤ ⨆ i, Yf i := hk 1
      have h3 : Y₃ ≤ ⨆ i, Yf i := hk 2
      have h4' : Y₄ ≤ ⨆ i, Yf i := hk 3
      have h5 : Y₅ ≤ ⨆ i, Yf i := hk 4
      have hM' : M ⊔ conjR M d.t ≤ ⨆ i, Yf i := by
        rw [hMt, hMeq]
        exact sup_le (sup_le h1 h2) (sup_le h5 h4')
      refine sup_le (sup_le (hYaM.trans hM') ?_) ?_
      · rw [hYb]
        exact sup_le h2 h4'
      · rw [hYc]
        exact h3
  let U : Fin 5 → Subgroup d.G₀ := fun i => (Yf i).subgroupOf d.G₀
  have hcomm : ∀ i j : Fin 5, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact mul_comm_of_commutator_eq_bot h13
    · exact mul_comm_of_commutator_eq_bot h14
    · exact mul_comm_of_commutator_eq_bot h15
    · exact mul_comm_of_commutator_eq_bot hc₂₄
    · exact mul_comm_of_commutator_eq_bot h25
    · exact mul_comm_of_commutator_eq_bot h35
  have hconjt : ∀ X : Subgroup G, X.map (MulAut.conj d.t).toMonoidHom = conjR X d.t := fun X => by
    rw [conjR, h.t_inv]
  have hθG : ∀ A, θ A ∈ d.G₀ := fun A => hMG (hθr ▸ ⟨A, rfl⟩)
  have hφG : ∀ A, φ A ∈ d.G₀ := fun A =>
    ((le_sup_left : d.L₁ ≤ d.L₁ ⊔ d.L₂).trans h.G₀_eq_L₁_sup_L₂.ge) (hφL ▸ ⟨A, rfl⟩)
  have htθG : ∀ A, (MulAut.conj d.t).toMonoidHom.comp θ A ∈ d.G₀ := fun A =>
    (mem_normalizer_iff.mp h.t_G₀ _).mp (hθG A)
  have hker_of_inj : ∀ f : SL(3, F) →* G, Function.Injective f → f.ker ≤ center SL(3, F) :=
    fun f hf => ((MonoidHom.ker_eq_bot_iff f).mpr hf).le.trans bot_le
  have hpair : ∀ i j : Fin 5, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact ⟨_, linearBlockStandardPair_of_map θ hθG hθker rfl hY₂eq⟩
    · refine ⟨_, linearBlockStandardPair_of_map (φ.comp (blockSL3 F 3 0 (by decide)))
        (fun A => hφG _) (hker_of_inj _ (hφ.comp (blockSL3_injective 3 0 _))) ?_ ?_⟩
      · rw [← Subgroup.map_map, map_B12_blockSL3]
        rfl
      · rw [← Subgroup.map_map, map_B23_blockSL3]
        rfl
    · refine ⟨_, linearBlockStandardPair_of_map (φ.comp (blockSL3 F 3 1 (by decide)))
        (fun A => hφG _) (hker_of_inj _ (hφ.comp (blockSL3_injective 3 1 _))) ?_ ?_⟩
      · rw [← Subgroup.map_map, map_B12_blockSL3]
        rfl
      · rw [← Subgroup.map_map, map_B23_blockSL3]
        rfl
    · refine ⟨_, linearBlockStandardPair_of_map' ((MulAut.conj d.t).toMonoidHom.comp θ) htθG
        ?_ ?_ ?_⟩
      · intro A hA
        apply hθker
        rw [MonoidHom.mem_ker] at hA ⊢
        exact (MulAut.conj d.t).injective (by rw [map_one]; exact hA)
      · rw [← Subgroup.map_map, hY₂eq, hconjt, hswap]
        rfl
      · rw [← Subgroup.map_map, hconjt]
        rfl
  obtain ⟨ψ, hψ, hψker, hqs, -⟩ := weakCT_recognition_of_pairs F 2 2 Nat.prime_two
    (by rw [h.card_field]; norm_num) (by norm_num) (by norm_num : 3 ≤ 5) hcomm hpair
    (iSup_subgroupOf_eq_top Yf hgen)
  exact ⟨⟨ψ, hψ, hψker⟩, hqs⟩

end YamadaSection4

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
