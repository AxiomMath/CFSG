module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12Cfg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf51EndGame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace M12Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H S : Subgroup T}

theorem prod_conj (cfg : M12Cfg K z J zJ H S)
    (hm1 : sigmaNorm K ≤ Subgroup.normalizer (firstFactor K : Set T)) (hU : UniqueCosetZ K z)
    {h : T} (hne : h⁻¹ * z * h ≠ z) (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z) :
    ∃ l ∈ firstFactor K, l⁻¹ * z * l = z * (h⁻¹ * z * h) := by
  have hz := cfg.datum.unique
  have hzHt := cfg.z_mem_ht
  have hcz : h⁻¹ * z * h ∈ Subgroup.centralizer ({z} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc.symm
  have hhN : h⁻¹ ∈ Subgroup.normalizer (firstFactor K : Set T) :=
    (Subgroup.normalizer (firstFactor K : Set T)).inv_mem (hm1 (hU h (cfg.cz_le hcz)))
  obtain ⟨R₀, hR₀, k, hk, hk4, hkk⟩ := exists_orderOf_four_of_datum cfg.datum
  have hkHt : k ∈ firstFactor K := cfg.K_le_ht (hR₀.1 hk)
  have hk'Ht : h⁻¹ * k * h ∈ firstFactor K := by
    have := (Subgroup.mem_normalizer_iff.mp hhN k).mp hkHt
    rwa [inv_inv] at this
  have hz'Ht : h⁻¹ * z * h ∈ firstFactor K := by
    have := (Subgroup.mem_normalizer_iff.mp hhN z).mp hzHt
    rwa [inv_inv] at this
  have hk'4 : orderOf (h⁻¹ * k * h) = 4 := by
    rw [show h⁻¹ * k * h = MulAut.conj h⁻¹ k by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, hk4]
  have hzz'Ht : z * (h⁻¹ * z * h) ∈ firstFactor K := (firstFactor K).mul_mem hzHt hz'Ht
  set kb : SecQuot (firstFactor K) := ((⟨k, hkHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K))
    with hkb
  set kb' : SecQuot (firstFactor K) :=
    ((⟨h⁻¹ * k * h, hk'Ht⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) with hkb'
  have hkbsq : kb * kb = ((⟨z, hzHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) := by
    rw [hkb, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hkk
  have hkb'sq : kb' * kb' =
      ((⟨h⁻¹ * z * h, hz'Ht⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) := by
    rw [hkb', ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show h⁻¹ * k * h * (h⁻¹ * k * h) = h⁻¹ * z * h
    rw [← hkk]
    group
  have hzz : ((⟨z * (h⁻¹ * z * h), hzz'Ht⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) =
      kb * kb * (kb' * kb') := by
    rw [hkbsq, hkb'sq, ← QuotientGroup.mk_mul]
    rfl
  have hzz2 : z * (h⁻¹ * z * h) * (z * (h⁻¹ * z * h)) = 1 := by
    have hz'2 : (h⁻¹ * z * h) * (h⁻¹ * z * h) = 1 := by
      calc (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
        _ = 1 := by rw [hz.sq]; group
    calc z * (h⁻¹ * z * h) * (z * (h⁻¹ * z * h)) = z * ((h⁻¹ * z * h) * z) * (h⁻¹ * z * h) := by
          group
      _ = z * (z * (h⁻¹ * z * h)) * (h⁻¹ * z * h) := by rw [hc]
      _ = (z * z) * ((h⁻¹ * z * h) * (h⁻¹ * z * h)) := by group
      _ = 1 := by rw [hz.sq, hz'2, one_mul]
  have hzz1 : z * (h⁻¹ * z * h) ≠ 1 := by
    intro h1
    apply hne
    have : h⁻¹ * z * h = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact inv_eq_of_mul_eq_one_right hz.sq
  have hne' : kb' * kb' ≠ kb * kb := by
    intro heq
    have h1 : kb * kb * (kb' * kb') = 1 := by
      rw [heq, hkbsq, ← QuotientGroup.mk_mul]
      have : (⟨z, hzHt⟩ : ↥(firstFactor K)) * ⟨z, hzHt⟩ = 1 := Subtype.ext hz.sq
      rw [this]
      rfl
    rw [← hzz] at h1
    exact mk_ne_one_of_mul_self hzz'Ht hzz2 hzz1 h1
  have hcomm : kb * kb * (kb' * kb') = kb' * kb' * (kb * kb) := by
    rw [hkbsq, hkb'sq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hc
  obtain ⟨e⟩ := cfg.equiv
  obtain ⟨x, hx⟩ := m12_sq_mul_sq_conj (e kb) (e kb')
    (by rw [MulEquiv.orderOf_eq]; exact orderOf_mk_eq_four hkHt hk4)
    (by rw [MulEquiv.orderOf_eq]; exact orderOf_mk_eq_four hk'Ht hk'4)
    (fun h1 => hne' (e.injective (by rw [map_mul, map_mul]; exact h1)))
    (by simpa only [map_mul] using congrArg e hcomm)
  have hconj : ((⟨z * (h⁻¹ * z * h), hzz'Ht⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) =
      e.symm x * ((⟨z, hzHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) * (e.symm x)⁻¹ := by
    apply e.injective
    rw [hzz, ← hkbsq]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hx.symm
  obtain ⟨l, hl, hlz⟩ := exists_conj_of_mk_conj hzHt hzz'Ht hz.sq hzz2 ⟨e.symm x, hconj⟩
  exact ⟨l⁻¹, (firstFactor K).inv_mem hl, by rw [inv_inv]; exact hlz⟩

theorem prod_unique (cfg : M12Cfg K z J zJ H S)
    (hm1 : sigmaNorm K ≤ Subgroup.normalizer (firstFactor K : Set T)) (hU : UniqueCosetZ K z)
    {h : T} (hne : h⁻¹ * z * h ≠ z) (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z) :
    ∃! c : T ⧸ sigmaNorm K, (z * (h⁻¹ * z * h)) • c = c := by
  obtain ⟨haM, -⟩ := cfg.prod_basic hne hc
  obtain ⟨l, hl, hla⟩ := cfg.prod_conj hm1 hU hne hc
  refine fixesUnique_of_only_base haM fun x hx => ?_
  have h1 : (l * x)⁻¹ * z * (l * x) ∈ sigmaNorm K := by
    have e : (l * x)⁻¹ * z * (l * x) = x⁻¹ * (l⁻¹ * z * l) * x := by group
    rw [e, hla]
    exact hx
  have h2 := hU _ h1
  simpa using (sigmaNorm K).mul_mem ((sigmaNorm K).inv_mem (cfg.ht_le_sigmaNorm hl)) h2

theorem not_uniqueCoset
    [CaseIAmbient T] (h39 : Lemma39FStar) (cfg : M12Cfg K z J zJ H S)
    (hm1 : sigmaNorm K ≤ Subgroup.normalizer (firstFactor K : Set T)) : ¬ UniqueCosetZ K z :=
  fun hU => cfg.toFrameCfg.endgame_fstar h39 hU fun _ hne hc => cfg.prod_unique hm1 hU hne hc

theorem exists_t
    [CaseIAmbient T] (h39 : Lemma39FStar) (cfg : M12Cfg K z J zJ H S)
    (hm1 : sigmaNorm K ≤ Subgroup.normalizer (firstFactor K : Set T)) :
    ∃ g : T, g ∉ sigmaNorm K ∧ g⁻¹ * z * g ∈ sigmaNorm K := by
  have h := cfg.not_uniqueCoset h39 hm1
  unfold UniqueCosetZ at h
  push Not at h
  obtain ⟨g, hg1, hg2⟩ := h
  exact ⟨g, hg2, hg1⟩

theorem t_outer
    (cfg : M12Cfg K z J zJ H S) {g : T} (hg : g ∉ sigmaNorm K)
    (htN : g⁻¹ * z * g ∈ Subgroup.normalizer (firstFactor K : Set T)) :
    s26Act (firstFactor K) ⟨g⁻¹ * z * g, htN⟩ ∉ inner (SecQuot (firstFactor K)) :=
  fun hin => hg (cfg.mem_sigmaNorm_of_inner rfl htN hin)

theorem exists_fixed_pair
    (cfg : M12Cfg K z J zJ H S) {t : T} (ht2 : t * t = 1)
    (htN : t ∈ Subgroup.normalizer (firstFactor K : Set T))
    (hout : s26Act (firstFactor K) ⟨t, htN⟩ ∉ inner (SecQuot (firstFactor K))) :
    ∃ a b : T, a * b = b * a ∧ t * a = a * t ∧ t * b = b * t ∧
      (∃ l ∈ firstFactor K, l⁻¹ * z * l = a) ∧ (∃ l ∈ firstFactor K, l⁻¹ * z * l = b) ∧
      (∃ l ∈ firstFactor K, l⁻¹ * z * l = a * b) := by
  have hz := cfg.datum.unique
  have hzHt := cfg.z_mem_ht
  obtain ⟨R₀, hR₀, k, hk, hk4, hkk⟩ := exists_orderOf_four_of_datum cfg.datum
  have hkHt : k ∈ firstFactor K := cfg.K_le_ht (hR₀.1 hk)
  set zb : SecQuot (firstFactor K) := ((⟨z, hzHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K))
    with hzb
  set kb : SecQuot (firstFactor K) := ((⟨k, hkHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K))
    with hkb
  have hkbsq : kb * kb = zb := by
    rw [hkb, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hkk
  set σ := s26Act (firstFactor K) ⟨t, htN⟩ with hσ
  have hσ2 : σ * σ = 1 := by
    have : (⟨t, htN⟩ : ↥(Subgroup.normalizer (firstFactor K : Set T))) * ⟨t, htN⟩ = 1 :=
      Subtype.ext ht2
    rw [hσ, ← map_mul, this, map_one]
  obtain ⟨e⟩ := cfg.equiv
  set σ' := MulAut.congr e σ with hσ'
  have hσ'app : ∀ w, σ' w = e (σ (e.symm w)) := fun _ => rfl
  have hσ'2 : σ' * σ' = 1 := by rw [hσ', ← map_mul, hσ2, map_one]
  have hσ'out : σ' ∉ inner NativeSporadic.M12 := by
    intro h
    apply hout
    rw [← inner_map_congr e] at h
    obtain ⟨β, hβ, hβσ⟩ := h
    have : β = σ := (MulAut.congr e).injective hβσ
    exact this ▸ hβ
  obtain ⟨a', b', ha', hb', hab', ⟨xa, hxa⟩, ⟨xb, hxb⟩, ⟨xab, hxab⟩⟩ :=
    m12_outer_fixes_four σ' hσ'2 hσ'out (e kb)
      (by rw [MulEquiv.orderOf_eq]; exact orderOf_mk_eq_four hkHt hk4)
  have hfix : ∀ w, σ' w = w → σ (e.symm w) = e.symm w := by
    intro w hw
    apply e.injective
    rw [← hσ'app, hw, MulEquiv.apply_symm_apply]
  have hconjb : ∀ x w : NativeSporadic.M12, x * (e kb * e kb) * x⁻¹ = w →
      e.symm w = e.symm x * zb * (e.symm x)⁻¹ := by
    intro x w hxw
    apply e.injective
    rw [← hkbsq]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hxw.symm
  obtain ⟨x₁, hx₁⟩ := QuotientGroup.mk_surjective (e.symm xa)
  obtain ⟨y₁, hy₁⟩ := QuotientGroup.mk_surjective (e.symm xb)
  have ha₀Ht : (x₁ : T) * z * (x₁ : T)⁻¹ ∈ firstFactor K :=
    (firstFactor K).mul_mem ((firstFactor K).mul_mem x₁.2 hzHt) ((firstFactor K).inv_mem x₁.2)
  have hb₀Ht : (y₁ : T) * z * (y₁ : T)⁻¹ ∈ firstFactor K :=
    (firstFactor K).mul_mem ((firstFactor K).mul_mem y₁.2 hzHt) ((firstFactor K).inv_mem y₁.2)
  have hmka₀ : ((⟨(x₁ : T) * z * (x₁ : T)⁻¹, ha₀Ht⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) =
      e.symm a' := by
    rw [hconjb xa a' hxa, ← hx₁]
    have e1 : (⟨(x₁ : T) * z * (x₁ : T)⁻¹, ha₀Ht⟩ : ↥(firstFactor K)) = x₁ * ⟨z, hzHt⟩ * x₁⁻¹ :=
      Subtype.ext rfl
    rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hmkb₀ : ((⟨(y₁ : T) * z * (y₁ : T)⁻¹, hb₀Ht⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) =
      e.symm b' := by
    rw [hconjb xb b' hxb, ← hy₁]
    have e1 : (⟨(y₁ : T) * z * (y₁ : T)⁻¹, hb₀Ht⟩ : ↥(firstFactor K)) = y₁ * ⟨z, hzHt⟩ * y₁⁻¹ :=
      Subtype.ext rfl
    rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hinv : ∀ w : T, w * z * w⁻¹ * (w * z * w⁻¹) = 1 := by
    intro w
    calc w * z * w⁻¹ * (w * z * w⁻¹) = w * (z * z) * w⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have hab₀ := commutator_mem_of_mk_comm ha₀Ht hb₀Ht (by
    rw [hmka₀, hmkb₀, ← map_mul, ← map_mul, hab'])
  have hta₀ := commutator_mem_of_act_fix htN ha₀Ht (by rw [hmka₀]; exact hfix a' ha')
  have htb₀ := commutator_mem_of_act_fix htN hb₀Ht (by rw [hmkb₀]; exact hfix b' hb')
  obtain ⟨a, b, haHt, hbHt, haa₀, hbb₀, ha2, hb2, hab, hta, htb⟩ :=
    exists_lift_commuting_pair ht2 htN ha₀Ht hb₀Ht (hinv _) (hinv _) hab₀ hta₀ htb₀
  have hmka := (mk_eq_mk_of_inv_mul_mem haHt ha₀Ht haa₀).trans hmka₀
  have hmkb := (mk_eq_mk_of_inv_mul_mem hbHt hb₀Ht hbb₀).trans hmkb₀
  have habHt : a * b ∈ firstFactor K := (firstFactor K).mul_mem haHt hbHt
  have hab2 : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hmkab : ((⟨a * b, habHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) = e.symm (a' * b') := by
    have e1 : (⟨a * b, habHt⟩ : ↥(firstFactor K)) = ⟨a, haHt⟩ * ⟨b, hbHt⟩ := Subtype.ext rfl
    rw [e1, QuotientGroup.mk_mul, hmka, hmkb, map_mul]
  have hfin : ∀ (c : T) (hc : c ∈ firstFactor K), c * c = 1 → ∀ x w : NativeSporadic.M12,
      x * (e kb * e kb) * x⁻¹ = w →
      ((⟨c, hc⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) = e.symm w →
      ∃ l ∈ firstFactor K, l⁻¹ * z * l = c := by
    intro c hc hc2 x w hxw hcw
    obtain ⟨l, hl, hlz⟩ := exists_conj_of_mk_conj hzHt hc hz.sq hc2
      ⟨e.symm x, by rw [hcw, hconjb x w hxw]⟩
    exact ⟨l⁻¹, (firstFactor K).inv_mem hl, by rw [inv_inv]; exact hlz⟩
  exact ⟨a, b, hab, hta, htb, hfin a haHt ha2 xa a' hxa hmka, hfin b hbHt hb2 xb b' hxb hmkb,
    hfin (a * b) habHt hab2 xab (a' * b') hxab hmkab⟩

theorem false_of_pair
    (cfg : M12Cfg K z J zJ H S) {g : T} (hg : g ∉ sigmaNorm K) {a b : T} (hab : a * b = b * a)
    (hta : g⁻¹ * z * g * a = a * (g⁻¹ * z * g)) (htb : g⁻¹ * z * g * b = b * (g⁻¹ * z * g))
    (ha : ∃ l ∈ firstFactor K, l⁻¹ * z * l = a) (hb : ∃ l ∈ firstFactor K, l⁻¹ * z * l = b)
    (hab' : ∃ l ∈ firstFactor K, l⁻¹ * z * l = a * b) : False := by
  have hwN : ∀ c : T, g⁻¹ * z * g * c = c * (g⁻¹ * z * g) →
      g * c * g⁻¹ ∈ Subgroup.normalizer (firstFactor K : Set T) := by
    intro c hc
    apply cfg.cz_le_normalizer_ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * c * g⁻¹ * z = g * (c * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * c) * g⁻¹ := by rw [hc]
      _ = z * (g * c * g⁻¹) := by group
  have key : ∀ c : T, ∀ hc : g⁻¹ * z * g * c = c * (g⁻¹ * z * g),
      (∃ l ∈ firstFactor K, l⁻¹ * z * l = c) →
      s26Act (firstFactor K) ⟨g * c * g⁻¹, hwN c hc⟩ ∉
        ComponentClassification.OuterAutomorphisms.inner (SecQuot (firstFactor K)) := by
    rintro c hc ⟨l, hl, hlc⟩ hin
    have hy : (l * g⁻¹)⁻¹ * z * (l * g⁻¹) = g * c * g⁻¹ := by rw [← hlc]; group
    have h1 := cfg.mem_sigmaNorm_of_inner hy (hwN c hc) hin
    apply hg
    have hlM : l ∈ sigmaNorm K := cfg.ht_le_sigmaNorm hl
    have h2 : g⁻¹ ∈ sigmaNorm K := by
      simpa using (sigmaNorm K).mul_mem ((sigmaNorm K).inv_mem hlM) h1
    simpa using (sigmaNorm K).inv_mem h2
  have htab : g⁻¹ * z * g * (a * b) = a * b * (g⁻¹ * z * g) := by
    calc g⁻¹ * z * g * (a * b) = (g⁻¹ * z * g * a) * b := by group
      _ = a * ((g⁻¹ * z * g) * b) := by rw [hta]; group
      _ = a * b * (g⁻¹ * z * g) := by rw [htb]; group
  have hprod := cfg.mul_mem_inner (key a hta ha) (key b htb hb)
  rw [← map_mul] at hprod
  have e : (⟨g * a * g⁻¹, hwN a hta⟩ : ↥(Subgroup.normalizer (firstFactor K : Set T))) *
      ⟨g * b * g⁻¹, hwN b htb⟩ = ⟨g * (a * b) * g⁻¹, hwN (a * b) htab⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  rw [e] at hprod
  exact key (a * b) htab hab' hprod

theorem false_of_m1
    [CaseIAmbient T] (h39 : Lemma39FStar) (cfg : M12Cfg K z J zJ H S)
    (hm1 : sigmaNorm K ≤ Subgroup.normalizer (firstFactor K : Set T)) : False := by
  obtain ⟨g, hg, hgt⟩ := cfg.exists_t h39 hm1
  have htN := hm1 hgt
  have ht2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [cfg.datum.unique.sq]; group
  obtain ⟨a, b, hab, hta, htb, ha, hb, hab'⟩ :=
    cfg.exists_fixed_pair ht2 htN (cfg.t_outer hg htN)
  exact cfg.false_of_pair hg hab hta htb ha hb hab'

end M12Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
