module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Env
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Omega

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

section KeyC

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

omit [Finite G] in
theorem mem_map_conj {D : Subgroup G} {b e : G} :
    e ∈ D.map (MulAut.conj b).toMonoidHom ↔ ∃ d ∈ D, b * d * b⁻¹ = e := by
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem Env33.hS_z (E : Env33 x y K T V W f z) : z ∈ V ⊓ centralizer ({x} : Set G) :=
  ⟨E.hPV E.hzP, mem_centralizer_singleton_iff.2 (E.hxcommK z E.hzP.2)⟩

theorem Env33.hS_f (E : Env33 x y K T V W f z) : f ∈ V ⊓ centralizer ({x} : Set G) :=
  ⟨E.cfg.f_mem_V, mem_centralizer_singleton_iff.2 E.cfg.hxf.symm⟩

theorem Env33.exists_omegaS (E : Env33 x y K T V W f z) :
    ∃ (C : Type) (_ : Group C) (_ : IsCyclic C)
      (ωS : ↥(V ⊓ centralizer ({x} : Set G)) →* C),
      ωS ⟨z, E.hS_z⟩ = 1 ∧ ωS ⟨f, E.hS_f⟩ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσσ : Back.actHom E.hKN ⟨f, E.hfC⟩ * Back.actHom E.hKN ⟨f, E.hfC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f, E.hfC⟩ : ↥(centralizer ({x} : Set G))) * ⟨f, E.hfC⟩ = 1 := Subtype.ext E.hf2'
    rw [this, map_one]
  have hσ1 : Back.actHom E.hKN ⟨f, E.hfC⟩ ≠ 1 := fun h => E.hfout (h ▸ (innAut _).one_mem)
  have hσ2 : orderOf (Back.actHom E.hKN ⟨f, E.hfC⟩) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  obtain ⟨C, hC, hCc, ω, hω1, hωσ, -⟩ := omegaData_of_isFAut hσ2 E.hfFaut
  refine ⟨C, hC, hCc, ω.comp ((Back.actHom E.hKN).comp
    (Subgroup.inclusion (inf_le_right : V ⊓ centralizer ({x} : Set G) ≤ centralizer ({x} : Set G)))),
    ?_, ?_⟩
  · show ω (Back.actHom E.hKN ⟨z, (inf_le_right : V ⊓ centralizer ({x} : Set G) ≤
      centralizer ({x} : Set G)) E.hS_z⟩) = 1
    rw [Back.actHom_of_mem E.hKN E.hzP.2]
    exact hω1 _ ⟨_, rfl⟩
  · exact hωσ

theorem Env33.key_c (E : Env33 x y K T V W f z) (h8 : 8 ≤ Nat.card ↥(secD K f V))
    {b : G} (hbW : b ∈ W) (hbN : b ∈ normalizer (V : Set G)) (hbV : b ∉ V) (hb2 : b ^ 2 ∈ V) :
    b * f * b⁻¹ = z ∧ b * z * b⁻¹ = f ∧
      secD K f V ⊓ (secD K f V).map (MulAut.conj b).toMonoidHom = ⊥ ∧
      ∀ d ∈ secD K f V, ∀ e ∈ (secD K f V).map (MulAut.conj b).toMonoidHom, d * e = e * d := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := secD K f V with hD
  have hb2el : ∃ k : ℕ, b ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.cfg.sylowW.isPGroup ⟨b, hbW⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hbn : ∀ v ∈ V, b * v * b⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.1 hbN v).1 hv
  have hbn' : ∀ v ∈ V, b⁻¹ * v * b ∈ V := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.1 ((normalizer (V : Set G)).inv_mem hbN) v).1 hv
    simpa using this
  have hbf : b * f * b⁻¹ ≠ f := by
    intro h
    apply hbV
    refine mem_of_isSylowOf_of_normalizes E.cfg.sylowV ?_ hbN hb2el
    refine mem_centralizer_singleton_iff.2 ?_
    calc b * f = (b * f * b⁻¹) * b := by group
      _ = f * b := by rw [h]
  have hZb : ∀ w ∈ zCenter V, b * w * b⁻¹ ∈ zCenter V := by
    intro w hw
    refine ⟨hbn w hw.1, fun v hv => ?_⟩
    have h1 := hw.2 (b⁻¹ * v * b) (hbn' v hv)
    calc v * (b * w * b⁻¹) = b * ((b⁻¹ * v * b) * w) * b⁻¹ := by group
      _ = b * (w * (b⁻¹ * v * b)) * b⁻¹ := by rw [h1]
      _ = (b * w * b⁻¹) * v := by group
  have hZb' : ∀ w ∈ zCenter V, b⁻¹ * w * b ∈ zCenter V := by
    intro w hw
    refine ⟨hbn' w hw.1, fun v hv => ?_⟩
    have h1 := hw.2 (b * v * b⁻¹) (hbn v hv)
    calc v * (b⁻¹ * w * b) = b⁻¹ * ((b * v * b⁻¹) * w) * b := by group
      _ = b⁻¹ * (w * (b * v * b⁻¹)) * b := by rw [h1]
      _ = (b⁻¹ * w * b) * v := by group
  have hZV := E.hZV h8
  have hfZ : f ∈ zCenter V := ⟨E.cfg.f_mem_V, fun v hv => E.hVf v hv⟩
  have hbfZ : b * f * b⁻¹ ∈ zpowers z ⊔ zpowers f := by rw [← hZV]; exact hZb f hfZ
  have hzf_comm : z * f = f * z := (E.hfP z E.hzP).symm
  have hcases := klein_cases E.hz2' E.hf2' hzf_comm hbfZ
  have hbf1 : b * f * b⁻¹ ≠ 1 := by
    intro h
    apply E.hf1
    calc f = b⁻¹ * (b * f * b⁻¹) * b := by group
      _ = 1 := by rw [h]; group
  set D' := D.map (MulAut.conj b).toMonoidHom with hD'
  have hD'V : D' ≤ V := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := mem_map_conj.1 he
    exact hbn d (E.hDV hd)
  have hD'n : ∀ v ∈ V, ∀ e ∈ D', v * e * v⁻¹ ∈ D' := by
    intro v hv e he
    obtain ⟨d, hd, rfl⟩ := mem_map_conj.1 he
    refine mem_map_conj.2 ⟨(b⁻¹ * v * b) * d * (b⁻¹ * v * b)⁻¹, E.hDn _ (hbn' v hv) d hd, ?_⟩
    group
  have hDD' : D ⊓ D' = ⊥ := by
    by_contra hne
    obtain ⟨w, ⟨hwD, hwD'⟩, hw1, hwc⟩ := exists_central_of_normal' (U := D ⊓ D') (B := V) hne
      (inf_le_left.trans E.hDV) (fun v hv u hu => ⟨E.hDn v hv u hu.1, hD'n v hv u hu.2⟩) E.hV2
    have hwZ : w ∈ zCenter V := ⟨E.hDV hwD, fun v hv => hwc v hv⟩
    rw [hZV] at hwZ
    have hwf : w = f := by
      rcases klein_cases E.hz2' E.hf2' hzf_comm hwZ with h | h | h | h
      · exact absurd h hw1
      · exact absurd (h ▸ hwD) E.hzD
      · exact h
      · exfalso
        apply E.hzD
        have : z = w * f⁻¹ := by rw [h]; group
        rw [this]
        exact D.mul_mem hwD (D.inv_mem E.hfD)
    obtain ⟨d, hd, hdw⟩ := mem_map_conj.1 hwD'
    have hdZ : d ∈ zCenter V := by
      have : d = b⁻¹ * w * b := by rw [← hdw]; group
      rw [this]
      apply hZb'
      rw [hwf]
      exact hfZ
    rw [hZV] at hdZ
    have hdf : d = f := by
      rcases klein_cases E.hz2' E.hf2' hzf_comm hdZ with h | h | h | h
      · exfalso
        apply hw1
        rw [← hdw, h]
        group
      · exact absurd (h ▸ hd) E.hzD
      · exact h
      · exfalso
        apply E.hzD
        have : z = d * f⁻¹ := by rw [h]; group
        rw [this]
        exact D.mul_mem hd (D.inv_mem E.hfD)
    apply hbf
    rw [hdf] at hdw
    rw [hdw, hwf]
  have hcomm : ∀ d ∈ D, ∀ e ∈ D', d * e = e * d :=
    commute_of_inf_eq_bot E.hDV hD'V E.hDn hD'n hDD'
  have hD'S : ∀ e ∈ D', e ∈ V ⊓ centralizer ({x} : Set G) := fun e he =>
    ⟨hD'V he, mem_centralizer_singleton_iff.2 (hcomm x E.hxD e he).symm⟩
  have hfbz : b * f * b⁻¹ = z := by
    obtain ⟨C, hC, hCc, ωS, hωz, hωf⟩ := E.exists_omegaS
    have hCcomm : ∀ u v : C, u * v = v * u := fun u v => (IsCyclic.commGroup (α := C)).mul_comm u v
    obtain ⟨-, hshape⟩ := E.hDshape
    rcases hshape with ⟨h4, -⟩ | ⟨a, haD, hVa, h4, hxa, hDx, hfa⟩
    · have h4' : Nat.card ↥D = 4 := h4
      omega
    · have hfS' : b * f * b⁻¹ ∈ V ⊓ centralizer ({x} : Set G) :=
        hD'S _ (mem_map_conj.2 ⟨f, E.hfD, rfl⟩)
      have haS' : b * a * b⁻¹ ∈ V ⊓ centralizer ({x} : Set G) :=
        hD'S _ (mem_map_conj.2 ⟨a, haD, rfl⟩)
      have hxS' : b * x * b⁻¹ ∈ V ⊓ centralizer ({x} : Set G) :=
        hD'S _ (mem_map_conj.2 ⟨x, E.hxD, rfl⟩)
      have hxa_ne : x * a * x⁻¹ ≠ a := by
        intro h
        have hax : a * x = x * a := by
          calc a * x = (x * a * x⁻¹) * x := by rw [h]
            _ = x * a := by group
        have hmem := E.hCx a haD hax
        have haa : a * a = 1 := mul_self_eq_one_of_mem_klein E.hx2 E.hf2' E.cfg.hxf hmem
        have : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact haa)
        have h4' : 4 ≤ orderOf a := Nat.le_of_dvd (orderOf_pos a) h4
        have := Nat.le_of_dvd (by norm_num) this
        omega
      obtain ⟨t, ht⟩ := mem_zpowers_iff.1 (hVa x E.cfg.x_mem_V)
      obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hfa
      have hord : ∃ k : ℕ, orderOf (⟨b * a * b⁻¹, haS'⟩ : ↥(V ⊓ centralizer ({x} : Set G))) = 2 ^ k := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 E.hV2 ⟨a, E.hDV haD⟩
        refine ⟨k, ?_⟩
        rw [Subgroup.orderOf_mk]
        have h1 : orderOf (b * a * b⁻¹) = orderOf a := (MulAut.conj b).orderOf_eq a
        rw [h1]
        have h2 : orderOf (⟨a, E.hDV haD⟩ : ↥V) = orderOf a := Subgroup.orderOf_mk _ _
        rw [← h2]; exact hk
      have hkey := hom_central_involution_eq_one hCcomm
        (a := (⟨b * a * b⁻¹, haS'⟩ : ↥(V ⊓ centralizer ({x} : Set G))))
        (x := ⟨b * x * b⁻¹, hxS'⟩) (f := ⟨b * f * b⁻¹, hfS'⟩)
        (mem_zpowers_iff.2 ⟨m, Subtype.ext (by
          rw [Subgroup.coe_zpow]
          show (b * a * b⁻¹) ^ m = b * f * b⁻¹
          rw [← hm, conj_zpow])⟩)
        (Subtype.ext (by
          show b * f * b⁻¹ * (b * f * b⁻¹) = 1
          calc b * f * b⁻¹ * (b * f * b⁻¹) = b * (f * f) * b⁻¹ := by group
            _ = 1 := by rw [E.hf2']; group))
        (fun h => hbf1 (congrArg Subtype.val h)) hord
        (mem_zpowers_iff.2 ⟨t, Subtype.ext (by
          rw [Subgroup.coe_zpow]
          show (b * a * b⁻¹) ^ t = b * x * b⁻¹ * (b * a * b⁻¹) * (b * x * b⁻¹)⁻¹
          calc (b * a * b⁻¹) ^ t = b * a ^ t * b⁻¹ := conj_zpow
            _ = b * (x * a * x⁻¹) * b⁻¹ := by rw [ht]
            _ = b * x * b⁻¹ * (b * a * b⁻¹) * (b * x * b⁻¹)⁻¹ := by group)⟩)
        (fun h => hxa_ne (by
          have h1 := congrArg Subtype.val h
          have h2 : b * x * b⁻¹ * (b * a * b⁻¹) * (b * x * b⁻¹)⁻¹ = b * a * b⁻¹ := h1
          have h3 : b * (x * a * x⁻¹) * b⁻¹ = b * a * b⁻¹ := by
            calc b * (x * a * x⁻¹) * b⁻¹ = b * x * b⁻¹ * (b * a * b⁻¹) * (b * x * b⁻¹)⁻¹ := by group
              _ = b * a * b⁻¹ := h2
          have := (MulAut.conj b).injective (by simpa [MulAut.conj_apply] using h3)
          exact this))
        ωS
      rcases hcases with h | h | h | h
      · exact absurd h hbf1
      · exact h
      · exact absurd h hbf
      · exfalso
        have hprod : (⟨b * f * b⁻¹, hfS'⟩ : ↥(V ⊓ centralizer ({x} : Set G))) =
            ⟨z, E.hS_z⟩ * ⟨f, E.hS_f⟩ := Subtype.ext h
        rw [hprod, map_mul, hωz, one_mul] at hkey
        exact hωf hkey
  refine ⟨hfbz, ?_, hDD', hcomm⟩
  have hbb : b * b ∈ V := by rw [← sq]; exact hb2
  calc b * z * b⁻¹ = (b * b) * f * (b * b)⁻¹ := by rw [← hfbz]; group
    _ = f := by
      have h1 := E.hVf (b * b) hbb
      calc (b * b) * f * (b * b)⁻¹ = (f * (b * b)) * (b * b)⁻¹ := by rw [h1]
        _ = f := by group

theorem Env33.zCenter_sup_zpowers (E : Env33 x y K T V W f z) (h8 : 8 ≤ Nat.card ↥(secD K f V))
    {b : G} (hbW : b ∈ W) (hbN : b ∈ normalizer (V : Set G)) (hbV : b ∉ V) (hb2 : b ^ 2 ∈ V) :
    zpowers (z * f) = zCenter (V ⊔ zpowers b) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbf, hbz, -, -⟩ := E.key_c h8 hbW hbN hbV hb2
  have hb2el : ∃ k : ℕ, b ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.cfg.sylowW.isPGroup ⟨b, hbW⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hbfne : b * f * b⁻¹ ≠ f := by
    intro h
    have hbV' : b ∈ V := by
      refine mem_of_isSylowOf_of_normalizes E.cfg.sylowV ?_ hbN hb2el
      refine mem_centralizer_singleton_iff.2 ?_
      calc b * f = (b * f * b⁻¹) * b := by group
        _ = f * b := by rw [h]
    exact hbV hbV'
  have hzf_comm : z * f = f * z := (E.hfP z E.hzP).symm
  have hzV : z ∈ V := E.hPV E.hzP
  have hfV : f ∈ V := E.cfg.f_mem_V
  have hzZ := E.hzZ
  have hfZ : f ∈ zCenter V := ⟨hfV, fun v hv => E.hVf v hv⟩
  have hX2 : IsPGroup 2 ↥(V ⊔ zpowers b) :=
    E.hV2.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_eq_one hb2el) ((zpowers_le).2 hbN)
  have hXN : V ⊔ zpowers b ≤ normalizer (V : Set G) :=
    sup_le Subgroup.le_normalizer ((zpowers_le).2 hbN)
  have hbX : b ∈ V ⊔ zpowers b := Subgroup.mem_sup_right (mem_zpowers b)
  have hzfX : z * f ∈ V ⊔ zpowers b := Subgroup.mem_sup_left (V.mul_mem hzV hfV)
  have hbzf : b * (z * f) * b⁻¹ = z * f := by
    calc b * (z * f) * b⁻¹ = (b * z * b⁻¹) * (b * f * b⁻¹) := by group
      _ = f * z := by rw [hbz, hbf]
      _ = z * f := hzf_comm.symm
  apply le_antisymm
  · rw [zpowers_le]
    refine ⟨hzfX, fun w hw => ?_⟩
    have hw' : w ∈ zpowers b ⊔ V := by rwa [sup_comm] at hw
    obtain ⟨a, ha, v, hv, rfl⟩ := Thm1.exists_mul_of_mem_sup_of_normalizes
      (fun a ha u hu => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
        have hmem : b ^ k ∈ normalizer (V : Set G) := (normalizer (V : Set G)).zpow_mem hbN k
        exact (Subgroup.mem_normalizer_iff.1 hmem u).1 hu) hw'
    have hvz : v * z = z * v := hzZ.2 v hv
    have hvf : v * f = f * v := E.hVf v hv
    have hvzf : v * (z * f) = (z * f) * v := by
      calc v * (z * f) = (v * z) * f := by group
        _ = (z * v) * f := by rw [hvz]
        _ = z * (v * f) := by group
        _ = z * (f * v) := by rw [hvf]
        _ = (z * f) * v := by group
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    have hbk : b ^ k * (z * f) = (z * f) * b ^ k :=
      (Commute.zpow_left (show Commute b (z * f) from by
        calc b * (z * f) = (b * (z * f) * b⁻¹) * b := by group
          _ = (z * f) * b := by rw [hbzf]) k).eq
    calc b ^ k * v * (z * f) = b ^ k * (v * (z * f)) := by group
      _ = b ^ k * ((z * f) * v) := by rw [hvzf]
      _ = (b ^ k * (z * f)) * v := by group
      _ = ((z * f) * b ^ k) * v := by rw [hbk]
      _ = (z * f) * (b ^ k * v) := by group
  · intro w hw
    have hwX : w ∈ V ⊔ zpowers b := hw.1
    have hwf : w * f = f * w := (hw.2 f (Subgroup.mem_sup_left hfV)).symm
    have hw2 : ∃ k : ℕ, w ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hX2 ⟨w, hwX⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hwV : w ∈ V := mem_of_isSylowOf_of_normalizes E.cfg.sylowV
      (mem_centralizer_singleton_iff.2 hwf) (hXN hwX) hw2
    have hwZ : w ∈ zCenter V := ⟨hwV, fun h hh => hw.2 h (Subgroup.mem_sup_left hh)⟩
    rw [E.hZV h8] at hwZ
    have hwb : b * w = w * b := hw.2 b hbX
    have hbw : b * w * b⁻¹ = w := by
      calc b * w * b⁻¹ = (w * b) * b⁻¹ := by rw [hwb]
        _ = w := by group
    rcases klein_cases E.hz2' E.hf2' hzf_comm hwZ with h | h | h | h
    · rw [h]; exact (zpowers (z * f)).one_mem
    · exfalso
      rw [h] at hbw
      have hfz : f = z := hbz.symm.trans hbw
      exact hbfne (by rw [hbf]; exact hfz.symm)
    · exfalso
      rw [h] at hbw
      exact hbfne hbw
    · rw [h]; exact mem_zpowers _

end KeyC

end CFSG.GH74.GLS.C3.Layer1.Thm1G33

