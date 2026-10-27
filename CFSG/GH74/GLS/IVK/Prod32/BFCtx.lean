module

public import CFSG.GH74.GLS.IVK.Prod32.BFAbs
public import CFSG.GH74.GLS.IVK.Prod32.LangDefs
public import CFSG.GH74.GLS.IVK.Prod32.CaPart
public import CFSG.GH74.GLS.IVK.Prod32.Compat
public import CFSG.GH74.GLS.IVK.Prod32.Kernel

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank Matrix
open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass squareClassMap)
open CFSG.GH74.GLS.IVK.Lifted (gammaOf slFieldAut slFieldAut_apply)
open scoped commutatorElement

section BFCtx

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H} {T : Subgroup H} {a : H}
  {F : Type} [Field F] [Finite F]

@[expose] noncomputable def E1 (K₁ T : Subgroup H) (ê : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F) :
    ↥(T1 T K₁) →* SquareClass F × (F ≃+* F) :=
  (coordHom K₁ ê hF).comp (Subgroup.inclusion (inf_le_right : T1 T K₁ ≤ normalizer (K₁ : Set H)))

omit [Finite H] in
theorem E1_apply (ê : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F) (x : ↥(T1 T K₁)) :
    E1 K₁ T ê hF x = coordHom K₁ ê hF ⟨(x : H), x.2.2⟩ := rfl

@[expose] noncomputable def E2 (hS : Setting H K₁ K₂ z) (T : Subgroup H)
    (ê : ↥K₂ ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F) :
    ↥(T1 T K₁) →* SquareClass F × (F ≃+* F) :=
  (coordHom K₂ ê hF).comp (Subgroup.inclusion
    (fun _ hx => hS.normalizer₁₂ hx.2 : T1 T K₁ ≤ normalizer (K₂ : Set H)))

theorem E2_apply (hS : Setting H K₁ K₂ z) (ê : ↥K₂ ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F)
    (x : ↥(T1 T K₁)) :
    E2 hS T ê hF x = coordHom K₂ ê hF ⟨(x : H), hS.normalizer₁₂ x.2.2⟩ := rfl

theorem E1_eq_one_iff (h : Hyp H K₁ K₂ z T a)
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (ê : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F) (x : ↥(T1 T K₁)) :
    E1 K₁ T ê hF x = 1 ↔ (x : H) ∈ P T K₁ K₂ := by
  rw [E1_apply, coordHom_eq_one_iff]
  exact h.inner_iff_mem_P hP₂ x.2

theorem E1_eq_iff (h : Hyp H K₁ K₂ z T a)
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (ê : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F) (x y : ↥(T1 T K₁)) :
    E1 K₁ T ê hF x = E1 K₁ T ê hF y ↔ ((x : H)⁻¹ * y) ∈ P T K₁ K₂ := by
  have h1 := E1_eq_one_iff h hP₂ ê hF (x⁻¹ * y)
  have h2 : ((x⁻¹ * y : ↥(T1 T K₁)) : H) = (x : H)⁻¹ * y := rfl
  rw [h2, map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem P_le_T1 (hS : Setting H K₁ K₂ z) : P T K₁ K₂ ≤ T1 T K₁ :=
  fun _ hx => ⟨hx.1, (sup_le Subgroup.le_normalizer hS.le_normalizer₁) hx.2⟩

theorem Setting.index_eq_two (hS : Setting H K₁ K₂ z) {t : H} (htN : t ∉ normalizer (K₁ : Set H)) :
    (normalizer (K₁ : Set H)).index = 2 := by
  have hle : (normalizer (K₁ : Set H)).index ≤ 2 := hS.index_le_two
  have hne : (normalizer (K₁ : Set H)).index ≠ 1 := fun h1 =>
    htN (by rw [Subgroup.index_eq_one.mp h1]; trivial)
  have hpos : (normalizer (K₁ : Set H)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem Setting.normalizer_normal (hS : Setting H K₁ K₂ z) {t : H}
    (htN : t ∉ normalizer (K₁ : Set H)) : (normalizer (K₁ : Set H)).Normal :=
  Subgroup.normal_of_index_eq_two (hS.index_eq_two htN)

theorem T1_conj_mem (hS : Setting H K₁ K₂ z) {t : H} (htT : t ∈ T) (htN : t ∉ normalizer (K₁ : Set H))
    {x : H} (hx : x ∈ T1 T K₁) : t * x * t⁻¹ ∈ T1 T K₁ :=
  ⟨T.mul_mem (T.mul_mem htT hx.1) (T.inv_mem htT), (hS.normalizer_normal htN).conj_mem x hx.2 t⟩

theorem T1_conj_inv_mem (hS : Setting H K₁ K₂ z) {t : H} (htT : t ∈ T)
    (htN : t ∉ normalizer (K₁ : Set H)) {x : H} (hx : x ∈ T1 T K₁) : t⁻¹ * x * t ∈ T1 T K₁ := by
  have hN' : t⁻¹ ∉ normalizer (K₁ : Set H) := fun hh => htN (by simpa using Subgroup.inv_mem _ hh)
  have := T1_conj_mem hS (T.inv_mem htT) hN' hx
  simpa using this

theorem sq_mem_T1 (hS : Setting H K₁ K₂ z) {t : H} (htT : t ∈ T) (htN : t ∉ normalizer (K₁ : Set H)) :
    t * t ∈ T1 T K₁ :=
  ⟨T.mul_mem htT htT, sq_mem_of_index_two (N := normalizer (K₁ : Set H)) (hS.index_eq_two htN) htN⟩

theorem E1_conj_t (hS : Setting H K₁ K₂ z) (ê : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F)
    {t : H} (htT : t ∈ T) (htN : t ∉ normalizer (K₁ : Set H)) {x : H} (hx : x ∈ T1 T K₁) :
    E1 K₁ T ê hF ⟨t * x * t⁻¹, T1_conj_mem hS htT htN hx⟩ =
      E1 K₁ T ê hF ⟨t⁻¹ * x * t, T1_conj_inv_mem hS htT htN hx⟩ := by
  have h2 := sq_mem_T1 hS htT htN
  have e : (⟨t * x * t⁻¹, T1_conj_mem hS htT htN hx⟩ : ↥(T1 T K₁)) =
      ⟨t * t, h2⟩ * ⟨t⁻¹ * x * t, T1_conj_inv_mem hS htT htN hx⟩ * ⟨t * t, h2⟩⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  rw [e, map_mul, map_mul, map_inv, qc_comm (E1 K₁ T ê hF ⟨t * t, h2⟩), mul_assoc, mul_inv_cancel,
    mul_one]


theorem P_conj_mem (hS : Setting H K₁ K₂ z) {t : H} (htT : t ∈ T) {x : H} (hx : x ∈ P T K₁ K₂) :
    t * x * t⁻¹ ∈ P T K₁ K₂ :=
  ⟨T.mul_mem (T.mul_mem htT hx.1) (T.inv_mem htT), hS.normal.conj_mem x hx.2 t⟩

theorem P_conj_inv_mem (hS : Setting H K₁ K₂ z) {t : H} (htT : t ∈ T) {x : H} (hx : x ∈ P T K₁ K₂) :
    t⁻¹ * x * t ∈ P T K₁ K₂ := by
  have := P_conj_mem hS (T.inv_mem htT) hx
  simpa using this

theorem bfAbs_of_ctx (h : Hyp H K₁ K₂ z T a)
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (ê₁ : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F)
    {σ : F ≃+* F} (hact₁ : SLAct K₁ a ê₁ σ) (hσ : σ ≠ 1)
    (ê₂ : ↥K₂ ≃* SpecialLinearGroup (Fin 2) F) (hact₂ : SLAct K₂ a ê₂ σ)
    {t : H} (htT : t ∈ T) (htN : t ∉ normalizer (K₁ : Set H))
    (hcoord : ∀ (x : H) (hx : x ∈ normalizer (K₁ : Set H))
        (hx' : t⁻¹ * x * t ∈ normalizer (K₁ : Set H)),
        coordHom K₂ ê₂ hF ⟨x, h.setting.normalizer₁₂ hx⟩ = coordHom K₁ ê₁ hF ⟨t⁻¹ * x * t, hx'⟩)
    {h' : H} (hh' : h' ∈ T1 T K₁) (hP' : a⁻¹ * (h' * t * h'⁻¹ * t⁻¹) ∈ P T K₁ K₂) :
    BFAbs (E1 K₁ T ê₁ hF) (E2 h.setting T ê₂ hF) ⟨a, h.a_mem⟩ ⟨h', hh'⟩ σ := by
  have hS := h.setting
  have hv : ∀ x : ↥(T1 T K₁), E2 hS T ê₂ hF x =
      E1 K₁ T ê₁ hF ⟨t⁻¹ * x * t, T1_conj_inv_mem hS htT htN x.2⟩ := fun x => by
    rw [E2_apply, E1_apply]
    exact hcoord x x.2.2 (T1_conj_inv_mem hS htT htN x.2).2
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ⟨_, hv x⟩, ?_, ?_, hσ, ?_, ?_, ?_⟩
  · rw [hv]
    have := (E1_eq_one_iff h hP₂ ê₁ hF x).mp hx
    exact (E1_eq_one_iff h hP₂ ê₁ hF _).mpr (P_conj_inv_mem hS htT this)
  · rw [hv] at hx
    have := (E1_eq_one_iff h hP₂ ê₁ hF _).mp hx
    have h2 := P_conj_mem hS htT this
    refine (E1_eq_one_iff h hP₂ ê₁ hF x).mpr ?_
    simpa [mul_assoc] using h2
  · rw [E1_apply]
    exact coordHom_slAct hF hact₁ _
  · rw [E2_apply]
    exact coordHom_slAct hF hact₂ _
  · have h1 : E1 K₁ T ê₁ hF (⟨a, h.a_mem⟩ * ⟨a, h.a_mem⟩) = 1 := by
      have : (⟨a, h.a_mem⟩ * ⟨a, h.a_mem⟩ : ↥(T1 T K₁)) = 1 := Subtype.ext h.a_mul_a
      rw [this, map_one]
    rw [map_mul, show E1 K₁ T ê₁ hF ⟨a, h.a_mem⟩ = (1, σ) from by
      rw [E1_apply]; exact coordHom_slAct hF hact₁ _] at h1
    exact congrArg Prod.snd h1
  · set g : ↥(T1 T K₁) := ⟨t * h'⁻¹ * t⁻¹, T1_conj_mem hS htT htN ((T1 T K₁).inv_mem hh')⟩ with hg
    have h1 : E1 K₁ T ê₁ hF (⟨a, h.a_mem⟩⁻¹ * (⟨h', hh'⟩ * g)) = 1 := by
      refine (E1_eq_one_iff h hP₂ ê₁ hF _).mpr ?_
      have : ((⟨a, h.a_mem⟩⁻¹ * (⟨h', hh'⟩ * g) : ↥(T1 T K₁)) : H) = a⁻¹ * (h' * t * h'⁻¹ * t⁻¹) := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hg]
        group
      rw [this]; exact hP'
    have hgi : g = (⟨t * h' * t⁻¹, T1_conj_mem hS htT htN hh'⟩ : ↥(T1 T K₁))⁻¹ := by
      apply Subtype.ext
      simp only [InvMemClass.coe_inv, hg]
      group
    have h2 := E1_conj_t hS ê₁ hF htT htN hh'
    rw [map_mul, map_mul, map_inv, hgi, map_inv, h2, ← hv ⟨h', hh'⟩] at h1
    exact (inv_mul_eq_one.mp (by simpa [mul_assoc] using h1) : _)
  · intro x hx2 h1
    have hxx : (x : H) * x ∈ K₁ ⊔ K₂ := by
      have : E1 K₁ T ê₁ hF (x * x) = 1 := by rw [map_mul]; exact hx2
      exact ((E1_eq_one_iff h hP₂ ê₁ hF _).mp this).2
    have h1' : (coordHom K₁ ê₁ hF ⟨(x : H), x.2.2⟩).2 = 1 := h1
    exact compat_fieldTriv hS ê₁ ê₂ hF hF x.2.2 hxx h1'


end BFCtx

section PreSub

variable {H : Type} [Group H] {G : Type} [Group G] {Γ₀ : Subgroup H}

@[expose] def preSub (u : ↥Γ₀ →* G) (S : Subgroup G) : Subgroup H := (S.comap u).map Γ₀.subtype

theorem mem_preSub {u : ↥Γ₀ →* G} {S : Subgroup G} {x : H} :
    x ∈ preSub u S ↔ ∃ hx : x ∈ Γ₀, u ⟨x, hx⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem preSub_le (u : ↥Γ₀ →* G) (S : Subgroup G) : preSub u S ≤ Γ₀ :=
  fun _ hx => (mem_preSub.mp hx).1

theorem preSub_mono (u : ↥Γ₀ →* G) {S₁ S₂ : Subgroup G} (h : S₁ ≤ S₂) :
    preSub u S₁ ≤ preSub u S₂ := fun _ hx => by
  obtain ⟨hx, h1⟩ := mem_preSub.mp hx
  exact mem_preSub.mpr ⟨hx, h h1⟩

theorem preSub_inf (u : ↥Γ₀ →* G) (S₁ S₂ : Subgroup G) :
    preSub u (S₁ ⊓ S₂) = preSub u S₁ ⊓ preSub u S₂ := by
  ext x
  rw [Subgroup.mem_inf, mem_preSub, mem_preSub, mem_preSub]
  constructor
  · rintro ⟨hx, h1, h2⟩
    exact ⟨⟨hx, h1⟩, ⟨hx, h2⟩⟩
  · rintro ⟨⟨hx, h1⟩, ⟨_, h2⟩⟩
    exact ⟨hx, h1, h2⟩

theorem preSub_range (u : ↥Γ₀ →* G) : preSub u u.range = Γ₀ := by
  apply le_antisymm (preSub_le u _)
  intro x hx
  exact mem_preSub.mpr ⟨hx, ⟨⟨x, hx⟩, rfl⟩⟩

theorem preSub_sup (u : ↥Γ₀ →* G) (hcomm : ∀ x y : G, x * y = y * x) {S₁ S₂ : Subgroup G}
    (h₁ : S₁ ≤ u.range) (h₂ : S₂ ≤ u.range) :
    preSub u (S₁ ⊔ S₂) = preSub u S₁ ⊔ preSub u S₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxΓ, hux⟩ := mem_preSub.mp hx
    obtain ⟨p, hp, q, hq, hpq⟩ := (mem_sup_of_comm (fun x _ y _ => hcomm x y) (u ⟨x, hxΓ⟩)).mp hux
    obtain ⟨x₁, hx₁⟩ := h₁ hp
    obtain ⟨x₂, hx₂⟩ := h₂ hq
    have hk : u (⟨x, hxΓ⟩⁻¹ * (x₁ * x₂)) = 1 := by
      rw [map_mul, map_inv, map_mul, hx₁, hx₂, ← hpq, inv_mul_cancel]
    have hx2k : x₂ * (⟨x, hxΓ⟩⁻¹ * (x₁ * x₂))⁻¹ ∈ S₂.comap u := by
      rw [Subgroup.mem_comap, map_mul, map_inv, hk, inv_one, mul_one, hx₂]; exact hq
    have hx1 : x₁ ∈ S₁.comap u := by rw [Subgroup.mem_comap, hx₁]; exact hp
    have hxe : (⟨x, hxΓ⟩ : ↥Γ₀) = x₁ * (x₂ * (⟨x, hxΓ⟩⁻¹ * (x₁ * x₂))⁻¹) := by group
    have hmem : (x₁ : H) * (x₂ * (⟨x, hxΓ⟩⁻¹ * (x₁ * x₂))⁻¹ : ↥Γ₀) ∈ preSub u S₁ ⊔ preSub u S₂ :=
      Subgroup.mul_mem_sup ⟨x₁, hx1, rfl⟩ ⟨_, hx2k, rfl⟩
    have this : x = (x₁ : H) * ((x₂ * (⟨x, hxΓ⟩⁻¹ * (x₁ * x₂))⁻¹ : ↥Γ₀) : H) := congrArg Subtype.val hxe
    rw [this]
    exact hmem
  · exact sup_le (preSub_mono u le_sup_left) (preSub_mono u le_sup_right)

theorem relIndex_preSub (u : ↥Γ₀ →* G) {S : Subgroup G} (hS : S ≤ u.range) :
    (preSub u ⊥).relIndex (preSub u S) = Nat.card S := by
  rw [preSub, preSub, Subgroup.relIndex_map_map_of_injective _ _ Γ₀.subtype_injective,
    Subgroup.relIndex_comap, Subgroup.map_comap_eq, inf_eq_right.mpr hS, Subgroup.relIndex_bot_left]

theorem preSub_zpowers (u : ↥Γ₀ →* G) (c' : ↥Γ₀) :
    preSub u (zpowers (u c')) = preSub u ⊥ ⊔ zpowers (c' : H) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxΓ, hux⟩ := mem_preSub.mp hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hux
    have hk' : u (⟨x, hxΓ⟩ * c' ^ (-k)) = 1 := by
      rw [map_mul, map_zpow, ← hk, _root_.zpow_neg, mul_inv_cancel]
    have hΓ : x * (c' : H) ^ (-k) ∈ Γ₀ := Γ₀.mul_mem hxΓ (Γ₀.zpow_mem c'.2 _)
    have hmem : x * (c' : H) ^ (-k) ∈ preSub u ⊥ := by
      refine mem_preSub.mpr ⟨hΓ, ?_⟩
      have : (⟨x * (c' : H) ^ (-k), hΓ⟩ : ↥Γ₀) = ⟨x, hxΓ⟩ * c' ^ (-k) := Subtype.ext (by simp)
      rw [this, hk', Subgroup.mem_bot]
    have hxe : x = (x * (c' : H) ^ (-k)) * (c' : H) ^ k := by group
    rw [hxe]
    exact Subgroup.mul_mem_sup hmem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)
  · refine sup_le (preSub_mono u bot_le) (Subgroup.zpowers_le.mpr ?_)
    exact mem_preSub.mpr ⟨c'.2, Subgroup.mem_zpowers _⟩

theorem preSub_cyclic (u : ↥Γ₀ →* G) {S : Subgroup G} (hS : S ≤ u.range) (hcyc : IsCyclic ↥S) :
    ∃ c' : ↥Γ₀, u c' ∈ S ∧ preSub u S = preSub u ⊥ ⊔ zpowers (c' : H) := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨c', hc'⟩ := hS g.2
  have hSz : S = zpowers (u c') := by
    rw [hc']
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · exact Subgroup.zpowers_le.mpr g.2
  refine ⟨c', hc' ▸ g.2, ?_⟩
  rw [hSz]; exact preSub_zpowers u c'

end PreSub

section BFCtx2

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H}

theorem comm_mem_of_t (hS : Setting H K₁ K₂ z) (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7) {t : H}
    (htN : t ∉ normalizer (K₁ : Set H)) {y : H} (hy : y ∈ normalizer (K₁ : Set H))
    (hty : t * y * t⁻¹ * y⁻¹ ∈ K₁ ⊔ K₂) (g : H) : ⁅g, y⁆ ∈ K₁ ⊔ K₂ := by
  have hidx := hS.index_eq_two htN
  by_cases hg : g ∈ normalizer (K₁ : Set H)
  · exact hS.comm_mem h2A7 hg hy
  · have hn : t⁻¹ * g ∈ normalizer (K₁ : Set H) := by
      rcases mem_or_of_index_two (N := normalizer (K₁ : Set H)) hidx htN g with h | h
      · exact absurd h hg
      · exact h
    have hκ := hS.comm_mem h2A7 hn hy
    have e : ⁅g, y⁆ = (t * ⁅t⁻¹ * g, y⁆ * t⁻¹) * (t * y * t⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (K₁ ⊔ K₂).mul_mem (hS.normal.conj_mem _ hκ t) hty

end BFCtx2

section BFD

variable {H : Type} [Group H] {F : Type} [Field F] [Finite F]

theorem diagOutE_of_coord {K : Subgroup H} (ê : ↥K ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F) {y : H}
    (hy : y ∈ normalizer (K : Set H)) (h2 : (coordHom K ê hF ⟨y, hy⟩).2 = 1)
    (h1 : (coordHom K ê hF ⟨y, hy⟩).1 ≠ 1) :
    DiagOutE K (ê.trans (specialLinearGroupEquivStatedSL 2 F)) y := by
  refine ⟨fun x hx => (Subgroup.mem_normalizer_iff.mp hy x).mp hx, ?_⟩
  set α : MulAut (SpecialLinearGroup (Fin 2) F) :=
    MulAut.congr ê (K.normalizerMonoidHom ⟨y, hy⟩) with hα
  have hcoord : coordHom K ê hF ⟨y, hy⟩ = outHom hF α := rfl
  rw [hcoord] at h2 h1
  obtain ⟨G, hG, hdet⟩ := exists_rep' hF α
  rw [h2] at hG
  refine ⟨G, ?_, fun x hx => ?_⟩
  · intro hsq
    apply h1
    rw [hdet, squareClassMap_eq_one_iff]
    rwa [Matrix.GeneralLinearGroup.val_det_apply]
  · have h3 : ê ⟨y * x * y⁻¹, hx⟩ = α (ê x) := by
      rw [hα, congr_apply_eq, MulEquiv.symm_apply_apply]
      congr 1
    show SpecialLinearGroup.toGL (ê ⟨y * x * y⁻¹, hx⟩) =
      G * SpecialLinearGroup.toGL (ê x) * G⁻¹
    rw [h3, hG, CFSG.GH74.GLS.IVK.glMap_one]

end BFD

section BFL

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H} {a : H}
  {F : Type} [Field F] [Finite F]

theorem langHyp_of_slAct (hS : Setting H K₁ K₂ z) (haa : a * a = 1)
    (ê₁ : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F) (ê₂ : ↥K₂ ≃* SpecialLinearGroup (Fin 2) F)
    (hF : GoodF F) {σ : F ≃+* F} (hσ : orderOf σ = 2) (hact₁ : SLAct K₁ a ê₁ σ)
    (hact₂ : SLAct K₂ a ê₂ σ) :
    LangHyp K₁ K₂ z a (ê₁.trans (specialLinearGroupEquivStatedSL 2 F))
      (ê₂.trans (specialLinearGroupEquivStatedSL 2 F)) σ σ where
  comm := hS.comm
  inter := hS.inter
  z_ord := hS.z_ord
  a_sq := haa
  norm₁ := hact₁.norm
  norm₂ := hact₂.norm
  odd₁ := ⟨hF.odd, hF.gt3⟩
  odd₂ := ⟨hF.odd, hF.gt3⟩
  σ₁_ord := hσ
  σ₂_ord := hσ
  act₁ := fun x hx => by
    show specialLinearGroupEquivStatedSL 2 F (ê₁ ⟨a * x * a⁻¹, hx⟩) =
      stableAut (StatedSL 2 F) (fieldStable_statedSL 2) σ (specialLinearGroupEquivStatedSL 2 F (ê₁ x))
    rw [hact₁.act x hx, stableAut_eq_slFieldAut]
  act₂ := fun x hx => by
    show specialLinearGroupEquivStatedSL 2 F (ê₂ ⟨a * x * a⁻¹, hx⟩) =
      stableAut (StatedSL 2 F) (fieldStable_statedSL 2) σ (specialLinearGroupEquivStatedSL 2 F (ê₂ x))
    rw [hact₂.act x hx, stableAut_eq_slFieldAut]

end BFL


end CFSG.GH74.GLS.IVK.Prod3
