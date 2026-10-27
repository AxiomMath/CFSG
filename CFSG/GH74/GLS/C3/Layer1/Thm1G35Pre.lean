module

public import CFSG.GH74.GLS.C3.Layer1.Thm1L3A7
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelLeaves
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Aux

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1G33

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G35

structure Pre35 {G : Type} [Group G] [Finite G] (x y : G) (K T V W : Subgroup G) (f z : G) :
    Prop where
  cfg : Cfg3 x y K T V W f z
  hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  hxS : IsSylowOf 2 (zpowers x) (CxK x K)
  hPK : IsSylowOf 2 (T ⊓ K) K
  hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K))
  hfout : Back.actHom hKN ⟨f, cfg.setup.sylowT.le cfg.mem.1⟩ ∉ innAut (kBar K)
  hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z
  e7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))

theorem pre35_of_rel
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hP31s : B_thm1_P31s_rel) (hP31c : B_thm1_P31c_rel)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) (hNo : NoV2Fine G)
    {x y : G} {K T V W : Subgroup G} {f z : G} (cfg : Cfg3 x y K T V W f z)
    (hA7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5)) : Pre35 x y K T V W f z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hshape := Thm1.kBar_model_of_U2 hG h102 hL34 cfg.hu2
  obtain ⟨hKN, hKuniq, -, hTdata⟩ := hP31s G hG hNo x y K cfg.hu2 hshape h5
  obtain ⟨-, ⟨n, hn3, hdih⟩, z₁, hz₁P, hz₁2, hz₁c, hz₁u⟩ := hTdata T cfg.setup
  have hz2 : orderOf z = 2 := cfg.z_mem.2.1
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z := by
    have hzz₁ : z = z₁ := by
      rcases hz₁u z cfg.z_mem.1 (fun p hp => (cfg.z_mem.2.2 p hp.1).symm) with h | h
      · exact absurd h hz1
      · exact h
    intro w hw hwc
    rcases hz₁u w hw hwc with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hzz₁.symm)
  have hfC : f ∈ centralizer ({x} : Set G) := cfg.setup.sylowT.le cfg.mem.1
  have hfFaut : P34.IsFAutL2A7 (kBar K) (Back.actHom hKN ⟨f, hfC⟩) := by
    obtain ⟨hfN, hF⟩ := thm1_FmemberF_of_rel h2hb G hG hNo x y K cfg.hu2 hshape hKN T cfg.setup f
      cfg.mem h5
    exact hF
  obtain ⟨hcen, -⟩ := kBar_autData_rel h2hb hNo cfg.hu2 hshape h5
  exact ⟨cfg, hKN, hP31c G hG hNo x y K cfg.hu2 h5,
    cfg.setup.sylowT.inf_of_le_normalizer cfg.hKx (fun c hc => U1a.mem_normalizer_of_norm hKN hc),
    hcen, not_mem_innAut_of_isFAutL2A7 hfFaut, hzu, hA7⟩

section Facts

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

theorem Pre35.hTC (E : Pre35 x y K T V W f z) : T ≤ centralizer ({x} : Set G) :=
  E.cfg.setup.sylowT.le

theorem Pre35.hfC (E : Pre35 x y K T V W f z) : f ∈ centralizer ({x} : Set G) :=
  E.hTC E.cfg.mem.1

theorem Pre35.hfP (E : Pre35 x y K T V W f z) : ∀ p ∈ T ⊓ K, f * p = p * f :=
  E.cfg.mem.2.2.1

theorem Pre35.hPker (E : Pre35 x y K T V W f z) :
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

theorem Pre35.hxker (E : Pre35 x y K T V W f z) :
    Back.actHom E.hKN ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ = 1 := by
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hxmem : x ∈ CMK (centralizer ({x} : Set G)) K := E.hxS.le (mem_zpowers x)
  have hker : (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom E.hKN).ker := by
    rw [Back.actHom_ker E.hKN]
    exact hxmem
  exact hker

theorem Pre35.card_P (E : Pre35 x y K T V W f z) : Nat.card ↥(T ⊓ K) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := E.hPK.card_eq
  have hK : Nat.card ↥K = Nat.card (pPrimeCore 2 ↥K) * Nat.card (kBar K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K), mul_comm]
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcard : Nat.card (kBar K) = 2520 := Thm1L34.card_kBar_of_alt7 E.e7
  rw [hK, hcard, Thm1L3A7.factorization_two_mul_odd hodd (by norm_num)] at h1
  rw [h1]
  have : (2520 : ℕ).factorization 2 = 3 := by
    have h2520 : (2520 : ℕ) = 2 ^ 3 * 315 := by norm_num
    rw [h2520, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [this]
  norm_num

theorem Pre35.hx2 (E : Pre35 x y K T V W f z) : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [E.cfg.hx2, sq] at this

theorem Pre35.hf2 (E : Pre35 x y K T V W f z) : f * f = 1 := by
  have := pow_orderOf_eq_one f
  rwa [E.cfg.hf2, sq] at this

theorem Pre35.hx1 (E : Pre35 x y K T V W f z) : x ≠ 1 := fun h => by
  have := E.cfg.hx2; rw [h, orderOf_one] at this; omega

theorem Pre35.hf1 (E : Pre35 x y K T V W f z) : f ≠ 1 := fun h => by
  have := E.cfg.hf2; rw [h, orderOf_one] at this; omega

theorem Pre35.hxf_ne (E : Pre35 x y K T V W f z) : x ≠ f := Ne.symm E.cfg.mem.2.2.2.1

theorem Pre35.hxcommK (E : Pre35 x y K T V W f z) : ∀ q ∈ K, q * x = x * q := fun _ hq =>
  mem_centralizer_singleton_iff.1 (E.cfg.hKx hq)

theorem Pre35.hkleinCard (E : Pre35 x y K T V W f z) :
    Nat.card ↥(zpowers x ⊔ zpowers f) = 4 :=
  P89.card_klein (by rw [sq]; exact E.hx2) (by rw [sq]; exact E.hf2) E.cfg.hxf E.hx1 E.hf1
    E.hxf_ne

theorem Pre35.hXT (E : Pre35 x y K T V W f z) : zpowers x ⊔ zpowers f ≤ T :=
  sup_le ((zpowers_le).2 E.cfg.x_mem_T) ((zpowers_le).2 E.cfg.mem.1)

theorem Pre35.hXC (E : Pre35 x y K T V W f z) :
    zpowers x ⊔ zpowers f ≤ centralizer ({f} : Set G) :=
  sup_le ((zpowers_le).2 (mem_centralizer_singleton_iff.2 E.cfg.hxf))
    ((zpowers_le).2 (mem_centralizer_singleton_iff.2 rfl))

theorem Pre35.P_inf_X (E : Pre35 x y K T V W f z) :
    (T ⊓ K) ⊓ (zpowers x ⊔ zpowers f) = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwP, hwX⟩
  rw [Subgroup.mem_bot]
  have hwK : w ∈ K := hwP.2
  have hwC : w ∈ centralizer ({x} : Set G) := E.hTC hwP.1
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hfC := E.hfC
  rcases klein_cases E.hx2 E.hf2 E.cfg.hxf hwX with h | h | h | h
  · exact h
  · exfalso
    subst h
    exact E.hx1 (E.hPker w hwP hwC E.hxker)
  · exfalso
    subst h
    apply E.hfout
    rw [Back.actHom_of_mem E.hKN hwK hfC]
    exact ⟨_, rfl⟩
  · exfalso
    apply E.hfout
    have hxfK : x * f ∈ K := h ▸ hwK
    have hxfC : x * f ∈ centralizer ({x} : Set G) := h ▸ hwC
    have h1 : Back.actHom E.hKN ⟨x * f, hxfC⟩ =
        Back.actHom E.hKN ⟨x, hxC⟩ * Back.actHom E.hKN ⟨f, hfC⟩ :=
      (Back.actHom E.hKN).map_mul ⟨x, hxC⟩ ⟨f, hfC⟩
    rw [E.hxker, one_mul] at h1
    rw [← h1, Back.actHom_of_mem E.hKN hxfK hxfC]
    exact ⟨_, rfl⟩

theorem Pre35.mul_injective (E : Pre35 x y K T V W f z) :
    Function.Injective (fun pe : ↥(T ⊓ K) × ↥(zpowers x ⊔ zpowers f) =>
      (⟨(pe.1 : G) * (pe.2 : G), T.mul_mem pe.1.2.1 (E.hXT pe.2.2)⟩ : ↥T)) := by
  rintro ⟨⟨p, hp⟩, ⟨e, he⟩⟩ ⟨⟨p', hp'⟩, ⟨e', he'⟩⟩ h
  have h1 : p * e = p' * e' := congrArg Subtype.val h
  have h2 : p'⁻¹ * p = e' * e⁻¹ := by
    calc p'⁻¹ * p = p'⁻¹ * (p * e) * e⁻¹ := by group
      _ = p'⁻¹ * (p' * e') * e⁻¹ := by rw [h1]
      _ = e' * e⁻¹ := by group
  have h3 : p'⁻¹ * p ∈ (T ⊓ K) ⊓ (zpowers x ⊔ zpowers f) :=
    ⟨(T ⊓ K).mul_mem ((T ⊓ K).inv_mem hp') hp,
      h2 ▸ (zpowers x ⊔ zpowers f).mul_mem he' ((zpowers x ⊔ zpowers f).inv_mem he)⟩
  rw [E.P_inf_X, Subgroup.mem_bot] at h3
  have hpp : p = p' := by
    have := congrArg (fun w : G => p' * w) h3
    simpa using this
  subst hpp
  have hee : e = e' := mul_left_cancel h1
  subst hee
  rfl

theorem Pre35.card_T (E : Pre35 x y K T V W f z) : Nat.card ↥T = 32 := by
  have h1 := Nat.card_le_card_of_injective _ E.mul_injective
  rw [Nat.card_prod, E.card_P, E.hkleinCard] at h1
  have h2 := Thm1L3A7.card_le_32_of_A7 E.cfg.hx2 E.cfg.setup.sylowT.isPGroup E.hTC E.cfg.hKx E.hKN
    E.e7.some E.hxS
  omega

theorem Pre35.T_decomp (E : Pre35 x y K T V W f z) :
    ∀ t ∈ T, ∃ p ∈ T ⊓ K, ∃ e ∈ zpowers x ⊔ zpowers f, t = p * e := by
  classical
  have hbij := E.mul_injective.bijective_of_nat_card_le (by
    rw [Nat.card_prod, E.card_P, E.hkleinCard, E.card_T])
  intro t ht
  obtain ⟨⟨p, e⟩, h⟩ := hbij.2 ⟨t, ht⟩
  exact ⟨p, p.2, e, e.2, (congrArg Subtype.val h).symm⟩

theorem Pre35.hTf (E : Pre35 x y K T V W f z) : ∀ t ∈ T, f * t = t * f := by
  intro t ht
  obtain ⟨p, hp, e, he, rfl⟩ := E.T_decomp t ht
  have h1 : f * p = p * f := E.hfP p hp
  have h2 : f * e = e * f := (mem_centralizer_singleton_iff.1 (E.hXC he)).symm
  calc f * (p * e) = (f * p) * e := by group
    _ = p * (f * e) := by rw [h1]; group
    _ = p * (e * f) := by rw [h2]
    _ = p * e * f := by group

theorem Pre35.hTV (E : Pre35 x y K T V W f z) : T ≤ V := fun t ht =>
  E.cfg.CTf_le t ht (E.hTf t ht)

theorem Pre35.hXcomm (E : Pre35 x y K T V W f z) {e : G} (he : e ∈ zpowers x ⊔ zpowers f) :
    ∀ q ∈ T ⊓ K, e * q = q * e := by
  have hle : zpowers x ⊔ zpowers f ≤ centralizer ((T ⊓ K : Subgroup G) : Set G) := by
    refine sup_le ((zpowers_le).2 ?_) ((zpowers_le).2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      exact fun q hq => E.hxcommK q hq.2
    · rw [Subgroup.mem_centralizer_iff]
      exact fun q hq => (E.hfP q hq).symm
  intro q hq
  exact (Subgroup.mem_centralizer_iff.1 (hle he) q hq).symm

theorem Pre35.zCenter_le (E : Pre35 x y K T V W f z) :
    ∀ c ∈ T, (∀ t ∈ T, c * t = t * c) → c ∈ zpowers z ⊔ (zpowers x ⊔ zpowers f) := by
  intro c hcT hcc
  obtain ⟨p, hp, e, he, rfl⟩ := E.T_decomp c hcT
  have hpc : ∀ q ∈ T ⊓ K, p * q = q * p := by
    intro q hq
    have h1 := hcc q hq.1
    have hex : e * q = q * e := E.hXcomm he q hq
    have h2 : p * e * q = q * (p * e) := h1
    calc p * q = p * (e * q) * e⁻¹ := by rw [hex]; group
      _ = (p * e * q) * e⁻¹ := by group
      _ = q * (p * e) * e⁻¹ := by rw [h2]
      _ = q * p := by group
  rcases E.hzu p hp hpc with hp1 | hpz
  · rw [hp1, one_mul]
    exact Subgroup.mem_sup_right he
  · rw [hpz]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers z)) (Subgroup.mem_sup_right he)

end Facts

end CFSG.GH74.GLS.C3.Layer1.Thm1G35

end
