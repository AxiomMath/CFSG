module

public import CFSG.CGT.Foote81L6.DescentTools
public import CFSG.CGT.Foote81L6.Star

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

variable {G H : Type*} [Group G] [Group H]

private noncomputable def mapEquivOfInjOn (f : G →* H) {X : Subgroup G}
    (hf : ∀ x ∈ X, f x = 1 → x = 1) : ↥(X.map f) ≃* ↥X :=
  ((MonoidHom.ofInjective (f := f.domRestrict X) ((injective_iff_map_eq_one _).2 fun x hx =>
      Subtype.ext (hf x x.2 (by simpa using hx)))).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range X f))).symm

theorem nonempty_mulEquiv_map_of_injOn (f : G →* H) {X : Subgroup G} {K : Type*} [Group K]
    (hf : ∀ x ∈ X, f x = 1 → x = 1) (e : Nonempty (↥X ≃* K)) : Nonempty (↥(X.map f) ≃* K) :=
  ⟨(mapEquivOfInjOn f hf).trans e.some⟩

theorem eq_of_map_eq_of_injOn (f : G →* H) {X : Subgroup G}
    (hf : ∀ x ∈ X, f x = 1 → x = 1) {x y : G} (hx : x ∈ X) (hy : y ∈ X) (h : f x = f y) :
    x = y := by
  have := hf (x⁻¹ * y) (mul_mem (inv_mem hx) hy) (by rw [map_mul, map_inv, h, inv_mul_cancel])
  rw [← mul_inv_cancel_left x y, this, mul_one]

theorem orderOf_map_of_injOn (f : G →* H) {X : Subgroup G} (hf : ∀ x ∈ X, f x = 1 → x = 1)
    {x : G} (hx : x ∈ X) : orderOf (f x) = orderOf x := by
  have hinj : Function.Injective (f.domRestrict X) := (injective_iff_map_eq_one _).2 fun y hy =>
    Subtype.ext (hf y y.2 (by simpa using hy))
  have := orderOf_injective (f.domRestrict X) hinj ⟨x, hx⟩
  simpa using this

namespace FooteCore

variable {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n) (f : G →* H)
  (hf : ∀ x ∈ T, f x = 1 → x = 1)

include hf in
theorem map_B_inf_centralizer_of_injOn :
    D.B.map f ⊓ centralizer ({f D.t} : Set H) = (D.B ⊓ centralizer ({D.t} : Set G)).map f := by
  apply le_antisymm
  · rintro _ ⟨⟨y, hy, rfl⟩, hc⟩
    refine ⟨y, mem_inf.2 ⟨hy, mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
    have hc' := mem_centralizer_singleton_iff.1 hc
    rw [← map_mul, ← map_mul] at hc'
    exact eq_of_map_eq_of_injOn f hf (mul_mem (D.B_le_T hy) D.t_mem_T)
      (mul_mem D.t_mem_T (D.B_le_T hy)) hc'
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyB, hyc⟩ := mem_inf.1 hy
    refine mem_inf.2 ⟨⟨y, hyB, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hyc]

theorem map_At (D : FooteCore G T m n) (f : G →* H) :
    (D.A ⊔ zpowers D.t).map f = D.A.map f ⊔ zpowers (f D.t) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]

@[expose] noncomputable def mapOfInjOn : FooteCore H (T.map f) m n where
  A := D.A.map f
  B := D.B.map f
  B₀ := D.B₀.map f
  B₁ := D.B₁.map f
  t := f D.t
  s := f D.s
  a := f D.a
  b₀ := f D.b₀
  b₁ := f D.b₁
  T_eq := (congrArg (Subgroup.map f) D.T_eq).trans (by
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers])
  A_inf_B := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    rw [mem_bot]
    have hyx := eq_of_map_eq_of_injOn f hf (D.B_le_T hy) (D.A_le_T hx) hxy
    have : x ∈ D.A ⊓ D.B := mem_inf.2 ⟨hx, hyx ▸ hy⟩
    rw [D.A_inf_B, mem_bot] at this
    rw [this, map_one]
  A_comm_B := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, D.A_comm_B x hx y hy]
  conj_t_A := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨D.t * x * D.t⁻¹, D.conj_t_A x hx, by simp only [map_mul, map_inv]⟩
  conj_t_B := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨D.t * x * D.t⁻¹, D.conj_t_B x hx, by simp only [map_mul, map_inv]⟩
  t_sq := by rw [← map_pow, D.t_sq, map_one]
  two_le_m := D.two_le_m
  A_iso := nonempty_mulEquiv_map_of_injOn f (fun x hx => hf x (D.A_le_T hx)) D.A_iso
  At_iso := (D.map_At f) ▸ nonempty_mulEquiv_map_of_injOn f (fun x hx => hf x (D.At_le_T hx))
    D.At_iso
  B_eq := by rw [D.B_eq, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers]
  B₀_inf_B₁ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    rw [mem_bot]
    have hyx := eq_of_map_eq_of_injOn f hf (D.B_le_T (D.B₁_le_B hy)) (D.B_le_T (D.B₀_le_B hx)) hxy
    have : x ∈ D.B₀ ⊓ D.B₁ := mem_inf.2 ⟨hx, hyx ▸ hy⟩
    rw [D.B₀_inf_B₁, mem_bot] at this
    rw [this, map_one]
  B₀_comm_B₁ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, D.B₀_comm_B₁ x hx y hy]
  m_lt_n := D.m_lt_n
  B₀_iso := nonempty_mulEquiv_map_of_injOn f (fun x hx => hf x (D.B_le_T (D.B₀_le_B hx)))
    D.B₀_iso
  B₁_iso := nonempty_mulEquiv_map_of_injOn f (fun x hx => hf x (D.B_le_T (D.B₁_le_B hx)))
    D.B₁_iso
  s_sq := by rw [← map_pow, D.s_sq, map_one]
  conj_s_B₀ := by
    rw [← D.conj_s_B₀]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨D.s * x * D.s⁻¹, ⟨x, hx, rfl⟩, by simp [map_mul, map_inv]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, by simp [map_mul, map_inv]⟩
  Bt_conj := by
    rintro _ ⟨x, hx, rfl⟩ hsq
    rw [← map_mul, ← map_pow] at hsq
    have hxt : (x * D.t) ^ 2 ∈ T := pow_mem (mul_mem (D.B_le_T hx) D.t_mem_T) 2
    obtain ⟨y, hy, hyx⟩ := D.Bt_conj x hx (hf _ hxt hsq)
    exact ⟨f y, ⟨y, hy, rfl⟩, by rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, hyx]⟩
  CBt_iso := (D.map_B_inf_centralizer_of_injOn f hf).symm ▸
    nonempty_mulEquiv_map_of_injOn f (fun x hx => hf x (D.B_le_T (mem_inf.1 hx).1)) D.CBt_iso
  a_mem := ⟨D.a, D.a_mem, rfl⟩
  a_order := orderOf_eq_prime (by rw [← map_pow, sq, D.a_mul_a, map_one])
    fun h => D.a_ne_one (hf _ D.a_mem_T h)
  a_comm := by
    intro x hx
    rw [← D.map_At f] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_mul, ← map_mul, D.a_comm y hy]
  b₀_mem := ⟨D.b₀, D.b₀_mem, rfl⟩
  b₀_order := orderOf_eq_prime (by rw [← map_pow, sq, D.b₀_mul_b₀, map_one])
    fun h => D.b₀_ne_one (hf _ (D.B_le_T D.b₀_mem_B) h)
  b₀_comm := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, D.b₀_comm x hx]
  b₁_mem := ⟨D.b₁, D.b₁_mem, rfl⟩
  b₁_order := orderOf_eq_prime (by rw [← map_pow, sq, D.b₁_mul_b₁, map_one])
    fun h => D.b₁_ne_one (hf _ (D.B_le_T D.b₁_mem_B) h)
  b₁_comm := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, D.b₁_comm x hx]

theorem Astar_mapOfInjOn : (D.mapOfInjOn f hf).Astar = D.Astar.map f := by
  have hb : f D.b = (D.mapOfInjOn f hf).b := by
    show f (D.b₀ * D.b₁) = f D.b₀ * f D.b₁
    rw [map_mul]
  rw [FooteCore.Astar, FooteCore.Astar, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hx2, hxa, rfl⟩
    refine ⟨x * D.b, ⟨x, hx, ?_, fun h => hxa (by rw [h]; rfl), rfl⟩, by rw [map_mul, hb]⟩
    rwa [orderOf_map_of_injOn f hf (D.A_le_T hx)] at hx2
  · rintro ⟨_, ⟨x, hx, hx2, hxa, rfl⟩, rfl⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_,
      fun h => hxa (eq_of_map_eq_of_injOn f hf (D.A_le_T hx) D.a_mem_T h), by rw [map_mul, hb]⟩
    rwa [orderOf_map_of_injOn f hf (D.A_le_T hx)]

end FooteCore

theorem stronglyInvolutionClosed_of_map_of_injOn (f : G →* H) {T X : Subgroup G}
    (hf : ∀ x ∈ T, f x = 1 → x = 1) (hXT : X ≤ T)
    (h : StronglyInvolutionClosed (X.map f) (T.map f)) : StronglyInvolutionClosed X T := by
  intro k hk hk2 g hg
  obtain ⟨y, hy, hyk⟩ := h (f k) ⟨k, hk, rfl⟩ (by rw [orderOf_map_of_injOn f hf (hXT hk), hk2])
    (f g) ⟨g * k * g⁻¹, hg, by simp only [map_mul, map_inv]⟩
  rw [← map_inv, ← map_mul, ← map_mul] at hyk
  rw [← eq_of_map_eq_of_injOn f hf (hXT hy) hg hyk]
  exact hy

namespace FooteData

variable {T : Subgroup G} {m n : ℕ} (D : FooteData G T m n) (f : G →* H)
  (hf : ∀ x ∈ T, f x = 1 → x = 1)
  (hlift : ∀ x ∈ T, ∀ y ∈ T, IsConj (f x) (f y) → IsConj x y)

@[expose] noncomputable def mapOfInjOn : FooteData H (T.map f) m n :=
  { D.toFooteCore.mapOfInjOn f hf with
    fusion_i := by
      rintro _ ⟨x, hx, rfl⟩ hx2 hxa _ ⟨r, hr, rfl⟩ hr2 hc
      have hxT := D.A_le_T hx
      have hrT := D.B_le_T (D.B₀_le_B hr)
      rw [orderOf_map_of_injOn f hf hxT] at hx2
      rw [orderOf_map_of_injOn f hf hrT] at hr2
      rw [← map_mul] at hc
      exact D.fusion_i x hx hx2 (fun h => hxa (by rw [h]; rfl)) r hr hr2
        (hlift _ D.a_mem_T _ (mul_mem hxT hrT) hc)
    fusion_ii := by
      rintro _ ⟨r, hr, rfl⟩ hr2 hc
      have hrT := D.B_le_T (D.B₀_le_B hr)
      rw [orderOf_map_of_injOn f hf hrT] at hr2
      change IsConj (f D.a) (f r * f D.b₁) at hc
      rw [← map_mul] at hc
      exact D.fusion_ii r hr hr2 (hlift _ D.a_mem_T _ (mul_mem hrT (D.B_le_T D.b₁_mem_B)) hc)
    fusion_iii := by
      rintro _ ⟨x, hx, rfl⟩ hx2 hxa _ ⟨y, hy, rfl⟩ hy2 hya _ ⟨r, hr, rfl⟩ hr2 hc
      have hxT := D.A_le_T hx
      have hyT := D.A_le_T hy
      have hrT := D.B_le_T (D.B₀_le_B hr)
      rw [orderOf_map_of_injOn f hf hxT] at hx2
      rw [orderOf_map_of_injOn f hf hyT] at hy2
      rw [orderOf_map_of_injOn f hf hrT] at hr2
      rw [← map_mul] at hc
      exact D.fusion_iii x hx hx2 (fun h => hxa (by rw [h]; rfl)) y hy hy2
        (fun h => hya (by rw [h]; rfl)) r hr hr2 (hlift _ (mul_mem hxT hrT) _ hyT hc)
    fusion_iv := by
      rintro _ ⟨x, hx, rfl⟩ hx2 hxa _ ⟨r, hr, rfl⟩ hr2 hc
      have hxT := D.A_le_T hx
      have hrT := D.B_le_T (D.B₀_le_B hr)
      rw [orderOf_map_of_injOn f hf hxT] at hx2
      rw [orderOf_map_of_injOn f hf hrT] at hr2
      change IsConj (f x * f r * f D.b₁) (f x * f D.b₀) at hc
      rw [← map_mul, ← map_mul, ← map_mul] at hc
      exact D.fusion_iv x hx hx2 (fun h => hxa (by rw [h]; rfl)) r hr hr2
        (hlift _ (mul_mem (mul_mem hxT hrT) (D.B_le_T D.b₁_mem_B)) _
          (mul_mem hxT (D.B_le_T D.b₀_mem_B)) hc)
    fusion_v := by
      rintro _ ⟨r, hr, rfl⟩ hr2 hc
      have hrT := D.B_le_T (D.B₀_le_B hr)
      rw [orderOf_map_of_injOn f hf hrT] at hr2
      change IsConj (f D.a) (f r * (f D.t * f r * (f D.t)⁻¹)) at hc
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul] at hc
      exact D.fusion_v r hr hr2 (hlift _ D.a_mem_T _
        (mul_mem hrT (D.B_le_T (D.conj_t_B _ (D.B₀_le_B hr)))) hc) }

variable [Finite G] {O : Subgroup G} [O.Normal] (hO : Odd (Nat.card O))

include D hO in
theorem mk_eq_one_of_odd : ∀ x ∈ T, QuotientGroup.mk' O x = 1 → x = 1 := by
  intro x hx h
  have hcop : Nat.Coprime (Nat.card T) (Nat.card O) := by
    rw [D.card_T]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hO)
  have : x ∈ T ⊓ O := mem_inf.2 ⟨hx, (QuotientGroup.eq_one_iff x).1 h⟩
  rw [Subgroup.inf_eq_bot_of_coprime hcop, mem_bot] at this
  exact this

include D hO in
theorem isConj_of_isConj_mk_of_odd :
    ∀ x ∈ T, ∀ y ∈ T, IsConj (QuotientGroup.mk' O x) (QuotientGroup.mk' O y) → IsConj x y := by
  intro x hx y hy h
  have h2 : ∀ {u : G}, u ∈ T → ∃ k : ℕ, u ^ (2 ^ k) = 1 := by
    intro u hu
    obtain ⟨j, hj⟩ := D.isPGroup_T ⟨u, hu⟩
    exact ⟨j, congrArg Subtype.val hj⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
  have hM : O = O ⊔ zpowers (1 : G) := by rw [zpowers_one_eq_bot, sup_bot_eq]
  rcases isConj_or_isConj_mul_of_isConj_mk_sup (M := O) hO (mul_one 1) (fun g => by simp) hM
    (h2 hx) (h2 hy) (by simp) h with h' | h'
  · exact h'
  · rwa [mul_one] at h'

@[expose] noncomputable def oddQuot : FooteData (G ⧸ O) (T.map (QuotientGroup.mk' O)) m n :=
  D.mapOfInjOn (QuotientGroup.mk' O) (D.mk_eq_one_of_odd hO) (D.isConj_of_isConj_mk_of_odd hO)

theorem Astar_oddQuot : (D.oddQuot hO).Astar = D.Astar.map (QuotientGroup.mk' O) :=
  D.toFooteCore.Astar_mapOfInjOn _ (D.mk_eq_one_of_odd hO)

end FooteData

end CFSG.CGT.Foote81L6
