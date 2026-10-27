module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cEnv
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.P34RealCtx
public import CFSG.GH74.GLS.C3.Layer1.Thm1A7Loc
public import CFSG.GH74.GLS.C3.Layer1.Thm1P38Aut

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1A7
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P31c

section Abstract

theorem exists_mem_zpowers_of_commute_of_autLevelC' {X A : Type} [Group X] [Finite X] [Group A]
    [Finite A] (hC : AutLevelC' A) (φ : X →* MulAut A) (T P : Subgroup X) (hT2 : IsPGroup 2 ↥T)
    (hPker : ∀ p ∈ P, φ p = 1 → p = 1) (hSyl : IsSylowOf 2 (P.map φ) (innAut A))
    (hdih : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥P n) {z₀ f₀ : X}
    (hzu : ∀ w ∈ P, (∀ p ∈ P, w * p = p * w) → w = 1 ∨ w = z₀)
    (hf₀2 : orderOf f₀ = 2) (hf₀c : ∀ p ∈ P, f₀ * p = p * f₀) (hf₀out : φ f₀ ∉ innAut A)
    {c : X} (hcT : c ∈ T) (hcc : ∀ p ∈ P, c * p = p * c) :
    φ c ∈ zpowers (φ z₀) ⊔ zpowers (φ f₀) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (φ.comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hPker a a.2 ha)
  have hrange : (φ.comp P.subtype).range = P.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : ↥P ≃* ↥(P.map φ) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  obtain ⟨n, hn3, hn⟩ := hdih
  have hdihB : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥(P.map φ) n :=
    ⟨n, hn3, isDihedralTwoGroup_of_equiv e.symm hn⟩
  have hf₀1 : φ f₀ ≠ 1 := fun h => hf₀out (h ▸ (innAut A).one_mem)
  have hff : f₀ * f₀ = 1 := by
    have := pow_orderOf_eq_one f₀
    rwa [hf₀2, sq] at this
  have hσ2 : orderOf (φ f₀) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, hff, map_one]) hf₀1
  have hσc : ∀ q ∈ P.map φ, φ f₀ * q = q * φ f₀ := by
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    rw [← map_mul, ← map_mul, hf₀c q₀ hq₀]
  have hγc : ∀ q ∈ P.map φ, φ c * q = q * φ c := by
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    rw [← map_mul, ← map_mul, hcc q₀ hq₀]
  have hγ2 : ∃ k : ℕ, (φ c) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hT2 ⟨c, hcT⟩
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
    rw [← map_pow, this, map_one]
  obtain ⟨z', hz'B, hz'2, hz'c, hγ⟩ :=
    hC (P.map φ) hSyl.le hSyl hdihB (φ f₀) (φ c) hσ2 hf₀out hσc hγc hγ2
  obtain ⟨p₀, hp₀, rfl⟩ := hz'B
  have hp₀c : ∀ q ∈ P, p₀ * q = q * p₀ := by
    intro q hq
    have hPn' : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ P := fun a ha b hb =>
      P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    have hφc : φ (p₀ * q * p₀⁻¹ * q⁻¹) = 1 := by
      have hcomm := hz'c (φ q) (Subgroup.mem_map_of_mem φ hq)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h1 := hPker _ (hPn' p₀ hp₀ q hq) hφc
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hp₀1 : p₀ ≠ 1 := fun h => by
    rw [h, map_one, orderOf_one] at hz'2
    omega
  have hp₀z : p₀ = z₀ := (hzu p₀ hp₀ hp₀c).resolve_left hp₀1
  rw [hp₀z] at hγ
  exact hγ

end Abstract

section Env

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

omit [Finite G] in
theorem Env31.hTC (E : Env31 x y K T f z) : T ≤ centralizer ({x} : Set G) :=
  E.hsetup.sylowT.le

omit [Finite G] in
theorem Env31.hfC (E : Env31 x y K T f z) : f ∈ centralizer ({x} : Set G) := E.hTC E.hfT

omit [Finite G] in
theorem Env31.hKC (E : Env31 x y K T f z) : K ≤ centralizer ({x} : Set G) := E.hu2.1.1.2.1

omit [Finite G] in
theorem Env31.hf2' (E : Env31 x y K T f z) : f * f = 1 := by
  have := pow_orderOf_eq_one f
  rwa [E.hf2, sq] at this

omit [Finite G] in
theorem Env31.hz2' (E : Env31 x y K T f z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [E.hz2, sq] at this

omit [Finite G] in
theorem Env31.hx1 (E : Env31 x y K T f z) : x ≠ 1 := fun h => by
  have := E.hu2.1.1.1; rw [h, orderOf_one] at this; omega

omit [Finite G] in
theorem Env31.hz1 (E : Env31 x y K T f z) : z ≠ 1 := fun h => by
  have := E.hz2; rw [h, orderOf_one] at this; omega

theorem Env31.hxT (E : Env31 x y K T f z) : x ∈ T :=
  Back.mem_of_isSylowOf_of_central E.hsetup.sylowT (mem_centralizer_singleton_iff.2 rfl)
    (fun _ hs => mem_centralizer_singleton_iff.1 hs) E.hu2.1.1.1

omit [Finite G] in
theorem Env31.hxcommK (E : Env31 x y K T f z) : ∀ q ∈ K, q * x = x * q := fun _ hq =>
  mem_centralizer_singleton_iff.1 (E.hKC hq)

theorem Env31.hPK (E : Env31 x y K T f z) : IsSylowOf 2 (T ⊓ K) K :=
  E.hsetup.sylowT.inf_of_le_normalizer E.hKC (fun _ hc => U1a.mem_normalizer_of_norm E.hKN hc)

omit [Finite G] in
theorem Env31.hxker (E : Env31 x y K T f z) :
    Back.actHom E.hKN ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ = 1 :=
  (Back.actHom_eq_one_iff_commutator_mem E.hKN _).2 (fun k hk => by
    have : ⁅k, x⁆ = 1 := by
      rw [commutatorElement_def, E.hxcommK k hk]
      group
    rw [this]
    exact (pPrimeCoreOf 2 K).one_mem)

theorem Env31.hPker (E : Env31 x y K T f z) :
    ∀ p ∈ T ⊓ K, ∀ hp : p ∈ centralizer ({x} : Set G), Back.actHom E.hKN ⟨p, hp⟩ = 1 → p = 1 := by
  intro p hpP hpC hφ
  have hpK : p ∈ K := hpP.2
  have h1 := Back.actHom_of_mem E.hKN hpK hpC
  have h2 : MulAut.conj (QuotientGroup.mk (⟨p, hpK⟩ : ↥K) : kBar K) = MulAut.conj 1 := by
    rw [map_one, ← h1]
    exact hφ
  have h3 := E.hcen h2
  have h4 : (⟨p, hpK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h3
  have h5 : p ∈ pPrimeCoreOf 2 K := Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hpK, h4⟩
  have h6 := Back.Setup91.inf_pPrimeCoreOf_eq_bot K E.hPK.isPGroup
  have h7 : p ∈ (T ⊓ K) ⊓ pPrimeCoreOf 2 K := ⟨hpP, h5⟩
  rw [h6, Subgroup.mem_bot] at h7
  exact h7

omit [Finite G] in
theorem Env31.hxmemCMK (E : Env31 x y K T f z) : x ∈ CxK x K := by
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hker : (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom E.hKN).ker := E.hxker
  rw [Back.actHom_ker E.hKN] at hker
  exact hker

theorem Env31.hxQ (E : Env31 x y K T f z) : x ∈ T ⊓ CxK x K := ⟨E.hxT, E.hxmemCMK⟩

omit [Finite G] in
theorem Env31.hPnorm (E : Env31 x y K T f z) :
    ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K := fun t ht p hp =>
  ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), E.hKN t (E.hTC ht) p hp.2⟩

omit [Finite G] in
theorem Env31.hQnorm (E : Env31 x y K T f z) :
    ∀ t ∈ T, ∀ q ∈ T ⊓ CxK x K, t * q * t⁻¹ ∈ T ⊓ CxK x K := fun _ ht _ hq =>
  ⟨T.mul_mem (T.mul_mem ht hq.1) (T.inv_mem ht), P34Real.CMK_conj E.hKN (E.hTC ht) hq.2⟩

theorem Env31.hQcentP (E : Env31 x y K T f z) :
    ∀ q ∈ T ⊓ CxK x K, ∀ p ∈ T ⊓ K, q * p = p * q := by
  intro q hq p hp
  have hqC : q ∈ centralizer ({x} : Set G) := E.hTC hq.1
  have hφ : Back.actHom E.hKN ⟨q, hqC⟩ = 1 := by
    have : (⟨q, hqC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom E.hKN).ker := by
      rw [Back.actHom_ker E.hKN]
      exact hq.2
    exact this
  have hcom := (Back.actHom_eq_one_iff_commutator_mem E.hKN ⟨q, hqC⟩).1 hφ p hp.2
  have hPmem : ⁅p, q⁆ ∈ T ⊓ K := by
    have : ⁅p, q⁆ = p * (q * p⁻¹ * q⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact (T ⊓ K).mul_mem hp (E.hPnorm q hq.1 p⁻¹ ((T ⊓ K).inv_mem hp)) |> fun h => by
      simpa [mul_assoc] using h
  have h6 := Back.Setup91.inf_pPrimeCoreOf_eq_bot K E.hPK.isPGroup
  have h7 : ⁅p, q⁆ ∈ (T ⊓ K) ⊓ pPrimeCoreOf 2 K := ⟨hPmem, hcom⟩
  rw [h6, Subgroup.mem_bot, commutatorElement_def] at h7
  calc q * p = (p * q * p⁻¹ * q⁻¹) * (q * p) := by rw [h7]; group
    _ = p * q := by group

theorem Env31.hPQ (E : Env31 x y K T f z) : (T ⊓ K) ⊓ (T ⊓ CxK x K) = ⊥ := by
  rw [eq_bot_iff]
  rintro p ⟨hpP, hpQ⟩
  rw [Subgroup.mem_bot]
  have hpC : p ∈ centralizer ({x} : Set G) := E.hTC hpP.1
  apply E.hPker p hpP hpC
  have : (⟨p, hpC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom E.hKN).ker := by
    rw [Back.actHom_ker E.hKN]
    exact hpQ.2
  exact this

theorem Env31.hQ_unique (E : Env31 x y K T f z) :
    ∀ u ∈ T ⊓ CxK x K, u * u = 1 → u = 1 ∨ u = x := by
  intro u hu huu
  by_contra hcon
  push Not at hcon
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact huu) hcon.1
  have hcomm : u * x = x * u :=
    (mem_centralizer_singleton_iff.1 (E.hTC hu.1))
  have := U1a.two_le_pRank_of_commute (D := CxK x K) hu.2 E.hxmemCMK hu2 E.hu2.1.1.1 hcomm hcon.2
  have := E.hrk
  omega

theorem Env31.hQsyl (E : Env31 x y K T f z) : IsSylowOf 2 (T ⊓ CxK x K) (CxK x K) := by
  have hCxN : ∀ c ∈ centralizer ({x} : Set G), ∀ q ∈ CxK x K, c * q * c⁻¹ ∈ CxK x K :=
    fun c hc q hq => P34Real.CMK_conj E.hKN hc hq
  exact E.hsetup.sylowT.inf_of_le_normalizer (fun q hq => hq.1)
    (fun c hc => U1a.mem_normalizer_of_norm hCxN hc)

omit [Finite G] in
theorem Env31.hfQ (E : Env31 x y K T f z) :
    ∀ q ∈ T ⊓ CxK x K, f * q * f ∈ T ⊓ CxK x K := by
  intro q hq
  have := E.hQnorm f E.hfT q hq
  have e1 : f⁻¹ = f := inv_eq_of_mul_eq_one_right E.hf2'
  rwa [e1] at this

theorem Env31.hCTP (E : Env31 x y K T f z) :
    ∀ c ∈ T, (∀ p ∈ T ⊓ K, c * p = p * c) →
      ∃ q ∈ T ⊓ CxK x K, c = q ∨ c = z * q ∨ c = f * q ∨ c = z * f * q := by
  intro c hcT hcc
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model E.hshape
  have hC : AutLevelC' (kBar K) := autLevelC'_of_L2 hF e
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  set φ := Back.actHom E.hKN with hφ
  have hTC := E.hTC
  have hPC : T ⊓ K ≤ C := inf_le_right.trans E.hKC
  have hT2 : IsPGroup 2 ↥(T.subgroupOf C) := E.hsetup.sylowT.isPGroup.comap_subtype
  have hPker : ∀ p ∈ (T ⊓ K).subgroupOf C, φ p = 1 → p = 1 := by
    intro p hp hφp
    exact Subtype.ext (E.hPker (p : G) hp p.2 hφp)
  have hSylK : IsSylowOf 2 ((T ⊓ K).subgroupOf C) (K.subgroupOf C) := by
    have hCN : C ≤ normalizer (K : Set G) := fun c hc => U1a.mem_normalizer_of_norm E.hKN hc
    have h := E.hsetup.sylowT.inf_of_le_normalizer E.hKC hCN
    rw [← isSylowOf_map_subtype_iff C, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC, inf_eq_left.2 E.hKC]
    exact h
  have hSyl : IsSylowOf 2 (((T ⊓ K).subgroupOf C).map φ) (innAut (kBar K)) := by
    have := isSylowOf_map_hom φ hSylK
    rwa [hφ, map_actHom_K E.hKC E.hKN] at this
  have hdih : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥((T ⊓ K).subgroupOf C) n := by
    obtain ⟨n, hn3, hn⟩ := E.hdih
    exact ⟨n, hn3, isDihedralTwoGroup_of_equiv (Subgroup.subgroupOfEquivOfLe hPC) hn⟩
  have hzu : ∀ w ∈ (T ⊓ K).subgroupOf C, (∀ p ∈ (T ⊓ K).subgroupOf C, w * p = p * w) →
      w = 1 ∨ w = ⟨z, E.hTC E.hzP.1⟩ := by
    intro w hw hwc
    have hw' : (w : G) ∈ T ⊓ K := hw
    rcases E.hzu (w : G) hw' (fun p hp => by
      have := hwc ⟨p, hPC hp⟩ hp
      exact congrArg Subtype.val this) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hfC := E.hfC
  have hcC : c ∈ C := hTC hcT
  have hresult := exists_mem_zpowers_of_commute_of_autLevelC' hC φ (T.subgroupOf C)
    ((T ⊓ K).subgroupOf C) hT2 hPker hSyl hdih (z₀ := ⟨z, E.hTC E.hzP.1⟩) (f₀ := ⟨f, hfC⟩)
    hzu (by rw [Subgroup.orderOf_mk]; exact E.hf2)
    (fun p hp => by
      have hp' : (p : G) ∈ T ⊓ K := hp
      exact Subtype.ext (E.hfc p hp'))
    (E.hfout hfC) (c := ⟨c, hcC⟩) hcT
    (fun p hp => by
      have hp' : (p : G) ∈ T ⊓ K := hp
      exact Subtype.ext (hcc p hp'))
  have hzfC : (⟨z, E.hTC E.hzP.1⟩ : ↥C) * ⟨f, hfC⟩ = ⟨f, hfC⟩ * ⟨z, E.hTC E.hzP.1⟩ :=
    Subtype.ext (E.hfc z E.hzP).symm
  have hcomm : ∀ a ∈ zpowers (φ ⟨z, E.hTC E.hzP.1⟩), ∀ b ∈ zpowers (φ ⟨f, hfC⟩), a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
    have : Commute (φ ⟨z, E.hTC E.hzP.1⟩) (φ ⟨f, hfC⟩) := by
      show φ _ * φ _ = φ _ * φ _
      rw [← map_mul, ← map_mul, hzfC]
    exact (Commute.zpow_zpow this i j).eq
  obtain ⟨a, ha, b, hb, hab⟩ := Thm1P310.exists_mul_of_mem_sup hcomm hresult
  have hzz : φ ⟨z, E.hTC E.hzP.1⟩ * φ ⟨z, E.hTC E.hzP.1⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, E.hTC E.hzP.1⟩ : ↥C) * ⟨z, E.hTC E.hzP.1⟩ = 1 := Subtype.ext E.hz2'
    rw [this, map_one]
  have hff : φ ⟨f, hfC⟩ * φ ⟨f, hfC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f, hfC⟩ : ↥C) * ⟨f, hfC⟩ = 1 := Subtype.ext E.hf2'
    rw [this, map_one]
  have hza : a = 1 ∨ a = φ ⟨z, E.hTC E.hzP.1⟩ := Thm1P310.eq_one_or_eq_of_mem_zpowers hzz ha
  have hfb : b = 1 ∨ b = φ ⟨f, hfC⟩ := Thm1P310.eq_one_or_eq_of_mem_zpowers hff hb
  have hker : ∀ g : G, g ∈ T → ∀ hg : g ∈ C, φ ⟨g, hg⟩ = 1 → g ∈ T ⊓ CxK x K := by
    intro g hgT hg h1
    have h2 : (⟨g, hg⟩ : ↥C) ∈ (Back.actHom E.hKN).ker := h1
    rw [Back.actHom_ker E.hKN] at h2
    exact ⟨hgT, h2⟩
  have hwq : ∀ w : G, w ∈ T → (hw : w ∈ C) → φ ⟨w, hw⟩ = φ ⟨c, hcC⟩ →
      ∃ q ∈ T ⊓ CxK x K, c = w * q := by
    intro w hwT hw hφw
    have hwc : w⁻¹ ∈ C := C.inv_mem hw
    have hcw : w⁻¹ * c ∈ C := C.mul_mem hwc hcC
    have h1 : φ ⟨w⁻¹ * c, hcw⟩ = 1 := by
      have e1 : (⟨w⁻¹ * c, hcw⟩ : ↥C) = (⟨w, hw⟩ : ↥C)⁻¹ * ⟨c, hcC⟩ := rfl
      rw [e1, map_mul, map_inv, hφw]
      group
    refine ⟨w⁻¹ * c, hker _ (T.mul_mem (T.inv_mem hwT) hcT) hcw h1, ?_⟩
    group
  have hzT' : z ∈ T := E.hzP.1
  have hfT' : f ∈ T := E.hfT
  rcases hza with rfl | rfl <;> rcases hfb with rfl | rfl
  ·
    obtain ⟨q, hq, hcq⟩ := hwq 1 T.one_mem C.one_mem (by
      have : (⟨(1 : G), C.one_mem⟩ : ↥C) = 1 := rfl
      rw [this, map_one, hab, one_mul])
    exact ⟨q, hq, Or.inl (by rw [hcq]; group)⟩
  · obtain ⟨q, hq, hcq⟩ := hwq f hfT' hfC (by rw [hab, one_mul])
    exact ⟨q, hq, Or.inr (Or.inr (Or.inl hcq))⟩
  · obtain ⟨q, hq, hcq⟩ := hwq z hzT' (E.hTC hzT') (by rw [hab, mul_one])
    exact ⟨q, hq, Or.inr (Or.inl hcq)⟩
  · obtain ⟨q, hq, hcq⟩ := hwq (z * f) (T.mul_mem hzT' hfT') (C.mul_mem (E.hTC hzT') hfC) (by
      have e1 : (⟨z * f, C.mul_mem (E.hTC hzT') hfC⟩ : ↥C) =
          (⟨z, E.hTC hzT'⟩ : ↥C) * ⟨f, hfC⟩ := rfl
      rw [e1, map_mul, hab])
    exact ⟨q, hq, Or.inr (Or.inr (Or.inr hcq))⟩

theorem Env31.hsq_CTP
    (E : Env31 x y K T f z) :
    ∀ c ∈ T, (∀ p ∈ T ⊓ K, c * p = p * c) → c * c ∈ T ⊓ CxK x K := by
  intro c hcT hcc
  obtain ⟨q, hq, h⟩ := E.hCTP c hcT hcc
  have hzq : ∀ q' ∈ T ⊓ CxK x K, z * q' = q' * z := fun q' hq' =>
    (E.hQcentP q' hq' z E.hzP).symm
  have hzf : z * f = f * z := (E.hfc z E.hzP).symm
  have hQ : ∀ a b : G, a ∈ T ⊓ CxK x K → b ∈ T ⊓ CxK x K → a * b ∈ T ⊓ CxK x K :=
    fun a b ha hb => (T ⊓ CxK x K).mul_mem ha hb
  rcases h with rfl | rfl | rfl | rfl
  · exact hQ _ _ hq hq
  · have : z * q * (z * q) = q * q := by
      calc z * q * (z * q) = z * (q * z) * q := by group
        _ = z * (z * q) * q := by rw [← hzq q hq]
        _ = (z * z) * (q * q) := by group
        _ = q * q := by rw [E.hz2', one_mul]
    rw [this]; exact hQ _ _ hq hq
  · have : f * q * (f * q) = (f * q * f) * q := by
      calc f * q * (f * q) = f * q * f * q := by group
        _ = (f * q * f) * q := rfl
    rw [this]; exact hQ _ _ (E.hfQ q hq) hq
  · have hfq : (f * q * f) ∈ T ⊓ CxK x K := E.hfQ q hq
    have h1 : z * f * q * (z * f * q) = (f * q * f) * q := by
      calc z * f * q * (z * f * q) = z * (f * (q * z) * f) * q := by group
        _ = z * (f * (z * q) * f) * q := by rw [← hzq q hq]
        _ = z * (f * z * (q * f)) * q := by group
        _ = z * (z * f * (q * f)) * q := by rw [← hzf]
        _ = (z * z) * (f * q * f) * q := by group
        _ = (f * q * f) * q := by rw [E.hz2', one_mul]
    rw [h1]; exact hQ _ _ hfq hq

end Env

end CFSG.GH74.GLS.C3.Layer1.Thm1P31c
