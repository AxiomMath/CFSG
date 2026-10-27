module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P33f
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Idx
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Vi

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

section PureCyc

theorem exists_mem_zpowers_conj_eq {G : Type} [Group G] [Finite G] {a z₁ f : G}
    (hz₁ : z₁ * z₁ = 1) (hn : ∀ g ∈ zpowers a, z₁ * g * z₁⁻¹ ∈ zpowers a)
    (h2 : IsPGroup 2 ↥(zpowers a)) (hf2 : f * f = 1) (hf1 : f ≠ 1) (hf : f ∈ zpowers a)
    (hnc : ∃ g ∈ zpowers a, z₁ * g ≠ g * z₁) :
    ∃ g ∈ zpowers a, g * z₁ * g⁻¹ = z₁ * f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := zpowers a with hC
  have hcomm : ∀ u ∈ C, ∀ v ∈ C, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hv
    exact (Commute.zpow_zpow_self a i j).eq
  let ε : ↥C →* ↥C :=
    { toFun := fun g => ⟨z₁ * (g : G) * z₁⁻¹ * (g : G)⁻¹, C.mul_mem (hn g g.2) (C.inv_mem g.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        have h2 : z₁ * (h : G) * z₁⁻¹ * (h : G)⁻¹ ∈ C := C.mul_mem (hn h h.2) (C.inv_mem h.2)
        have h3 : (g : G)⁻¹ * (z₁ * (h : G) * z₁⁻¹ * (h : G)⁻¹) =
            (z₁ * (h : G) * z₁⁻¹ * (h : G)⁻¹) * (g : G)⁻¹ :=
          hcomm _ (C.inv_mem g.2) _ h2
        show z₁ * ((g : G) * (h : G)) * z₁⁻¹ * ((g : G) * (h : G))⁻¹ =
          z₁ * (g : G) * z₁⁻¹ * (g : G)⁻¹ * (z₁ * (h : G) * z₁⁻¹ * (h : G)⁻¹)
        calc z₁ * ((g : G) * (h : G)) * z₁⁻¹ * ((g : G) * (h : G))⁻¹
            = z₁ * (g : G) * z₁⁻¹ * (z₁ * (h : G) * z₁⁻¹ * (h : G)⁻¹) * (g : G)⁻¹ := by group
          _ = z₁ * (g : G) * z₁⁻¹ * ((g : G)⁻¹ * (z₁ * (h : G) * z₁⁻¹ * (h : G)⁻¹)) := by
              rw [h3]; group
          _ = _ := by group }
  have hne : ε.range ≠ ⊥ := by
    obtain ⟨g, hg, hgne⟩ := hnc
    intro hbot
    have h1 : ε ⟨g, hg⟩ = 1 := by
      have : ε ⟨g, hg⟩ ∈ ε.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have h2 : z₁ * g * z₁⁻¹ * g⁻¹ = 1 := congrArg Subtype.val h1
    apply hgne
    have : z₁ * g * z₁⁻¹ = g := mul_inv_eq_one.1 h2
    calc z₁ * g = (z₁ * g * z₁⁻¹) * z₁ := by group
      _ = g * z₁ := by rw [this]
  have hrange2 : IsPGroup 2 ↥ε.range :=
    h2.of_surjective ε.rangeRestrict ε.rangeRestrict_surjective
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hrange2
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hm
    exact (Subgroup.card_eq_one).1 hm
  have h2dvd : 2 ∣ Nat.card ↥ε.range := by
    rw [hm]; exact dvd_pow_self 2 hm0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥ε.range) 2 h2dvd
  have hw' : orderOf (w : ↥C) = 2 := by
    rw [← Subgroup.orderOf_coe] at hw
    simpa using hw
  have hwsq : (w : ↥C) * (w : ↥C) = 1 := by
    have := pow_orderOf_eq_one (w : ↥C)
    rwa [hw', sq] at this
  have hw1 : (w : ↥C) ≠ 1 := fun h => by rw [h, orderOf_one] at hw'; omega
  let fC : ↥C := ⟨f, hf⟩
  have hfsq : fC * fC = 1 := Subtype.ext hf2
  have hf1' : fC ≠ 1 := fun h => hf1 (congrArg Subtype.val h)
  have hcyc : IsCyclic ↥C := by rw [hC]; infer_instance
  have hwf : (w : ↥C) = fC :=
    DihedralAux.cyclic_unique_involution (G := ↥C) (a := (w : ↥C)) (b := fC) hw1 hf1' hwsq hfsq
  obtain ⟨g, hg⟩ := w.2
  refine ⟨g, g.2, ?_⟩
  have h1 : z₁ * (g : G) * z₁⁻¹ * (g : G)⁻¹ = f := by
    have := congrArg Subtype.val hg
    rw [hwf] at this
    exact this
  have hz₁inv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁
  calc (g : G) * z₁ * (g : G)⁻¹ = z₁ * (z₁⁻¹ * (g : G) * z₁) * (g : G)⁻¹ := by group
    _ = z₁ * (z₁ * (g : G) * z₁⁻¹) * (g : G)⁻¹ := by rw [hz₁inv]
    _ = z₁ * (z₁ * (g : G) * z₁⁻¹ * (g : G)⁻¹) := by group
    _ = z₁ * f := by rw [h1]

end PureCyc

section Core

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

@[expose] def Fus33 (K T : Subgroup G) (f z : G) : Prop :=
  ∀ w ∈ T ⊓ K, orderOf w = 2 → w ∉ layerI K f → IsConj w z ∧ IsConj (f * w) f

theorem Env33.false_of_conj_mul_f (E : Env33 x y K T V W f z) (hnz : ¬ IsConj z f)
    (hfus : Fus33 K T f z) {w w' : G} (hw : w ∈ T ⊓ K) (hw2 : orderOf w = 2)
    (hwI : w ∉ layerI K f) (hw' : w' ∈ T ⊓ K) (hw'2 : orderOf w' = 2) (hw'I : w' ∉ layerI K f)
    (hconj : IsConj w (w' * f)) : False := by
  obtain ⟨hwz, -⟩ := hfus w hw hw2 hwI
  obtain ⟨-, hfw'⟩ := hfus w' hw' hw'2 hw'I
  have hcomm : w' * f = f * w' := (E.hfP w' hw').symm
  rw [hcomm] at hconj
  exact hnz (hwz.symm.trans (hconj.trans hfw'))

theorem Env33.comm_D_of_fus (E : Env33 x y K T V W f z) (hnz : ¬ IsConj z f)
    (hfus : Fus33 K T f z) :
    ∀ w ∈ T ⊓ K, orderOf w = 2 → w ∉ layerI K f → ∀ d ∈ secD K f V, w * d = d * w := by
  classical
  intro w hw hw2 hwI d hd
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, sq] at this
  have hwV : w ∈ V := E.hPV hw
  have hwx : w * x = x * w := E.hxcommK w hw.2
  rcases E.hDshape.2 with ⟨-, hD⟩ | ⟨a, haD, hanorm, -, -, hdecomp, hfa⟩
  · have hle : secD K f V ≤ centralizer ({w} : Set G) := by
      rw [hD]
      refine sup_le ((zpowers_le).2 ?_) ((zpowers_le).2 ?_)
      · exact mem_centralizer_singleton_iff.2 hwx.symm
      · exact mem_centralizer_singleton_iff.2 (E.hfP w hw)
    exact (mem_centralizer_singleton_iff.1 (hle hd)).symm
  · have haV : a ∈ V := E.hDV haD
    have hwa : ∀ g ∈ zpowers a, w * g = g * w := by
      by_contra hcon
      push Not at hcon
      have hn : ∀ g ∈ zpowers a, w * g * w⁻¹ ∈ zpowers a := by
        intro g hg
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg
        rw [← conj_zpow]
        exact (zpowers a).zpow_mem (hanorm w hwV) i
      have h2 : IsPGroup 2 ↥(zpowers a) := E.hV2.to_le ((zpowers_le).2 haV)
      obtain ⟨g, -, hgw⟩ := exists_mem_zpowers_conj_eq hww hn h2 E.hf2' E.hf1 hfa hcon
      exact E.false_of_conj_mul_f hnz hfus hw hw2 hwI hw hw2 hwI (isConj_iff.2 ⟨g, hgw⟩)
    rcases hdecomp d hd with hd' | hd'
    · exact hwa d hd'
    · have h1 : Commute w x := hwx
      have h2 : Commute w (x⁻¹ * d) := hwa _ hd'
      have h3 : Commute w (x * (x⁻¹ * d)) := h1.mul_right h2
      simpa using h3.eq

theorem Env33.comm_PD (E : Env33 x y K T V W f z) (hnz : ¬ IsConj z f) (hfus : Fus33 K T f z) :
    ∀ p ∈ T ⊓ K, ∀ d ∈ secD K f V, p * d = d * p := by
  classical
  have key : ∀ u ∈ T ⊓ K, u * u = 1 → ∀ d ∈ secD K f V, u * d = d * u := by
    intro u hu huu d hd
    by_cases huI : u ∈ layerI K f
    · have hP₁D : ((T ⊓ K) ⊓ layerI K f) ⊓ secD K f V = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        have : w ∈ (T ⊓ K) ⊓ secD K f V := ⟨hw.1.1, hw.2⟩
        rw [E.hPD] at this
        exact this
      exact commute_of_inf_eq_bot (V := V) (show (T ⊓ K) ⊓ layerI K f ≤ V from fun p hp => E.hPV hp.1) E.hDV E.hP1n E.hDn hP₁D u
        ⟨hu, huI⟩ d hd
    · have hu1 : u ≠ 1 := fun h => huI (h ▸ (layerI K f).one_mem)
      have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact huu) hu1
      exact E.comm_D_of_fus hnz hfus u hu hu2 huI d hd
  intro p hp d hd
  obtain ⟨n, -, hn⟩ := E.hdih
  obtain ⟨u, hu, w, hw, huu, hww, hpuw⟩ := exists_mul_involutions_of_dihedral hn p hp
  have hu' : u ∈ T ⊓ K := hu
  have hw' : w ∈ T ⊓ K := hw
  rw [hpuw, mul_assoc, key w hw' hww d hd, ← mul_assoc, key u hu' huu d hd, mul_assoc]


theorem Env33.key_e (E : Env33 x y K T V W f z) (hnz : ¬ IsConj z f) (hfus : Fus33 K T f z) :
    ∀ v ∈ V, ∀ p ∈ T ⊓ K, v * p * v⁻¹ ∈ T ⊓ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := E.comm_PD hnz hfus
  have hinv : ∀ v ∈ V, ∀ u ∈ T ⊓ K, u * u = 1 → v * u * v⁻¹ ∈ T ⊓ K := by
    intro v hv u hu huu
    by_cases huI : u ∈ layerI K f
    · exact (E.hP1n v hv u ⟨hu, huI⟩).1
    have hu1 : u ≠ 1 := fun h => huI (h ▸ (layerI K f).one_mem)
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact huu) hu1
    have huV : u ∈ V := E.hPV hu
    have hvuV : v * u * v⁻¹ ∈ V := V.mul_mem (V.mul_mem hv huV) (V.inv_mem hv)
    obtain ⟨p', hp', d', hd', hvu⟩ := E.conj_decomp v hv u hu
    have hd'c : ∀ d ∈ secD K f V, d' * d = d * d' := by
      intro d hd
      have hd1 : v⁻¹ * d * v ∈ secD K f V := by
        simpa using E.hDn v⁻¹ (V.inv_mem hv) d hd
      have h0 := hcomm u hu (v⁻¹ * d * v) hd1
      have h1 : (v * u * v⁻¹) * d = d * (v * u * v⁻¹) := by
        calc v * u * v⁻¹ * d = v * (u * (v⁻¹ * d * v)) * v⁻¹ := by group
          _ = v * ((v⁻¹ * d * v) * u) * v⁻¹ := by rw [h0]
          _ = d * (v * u * v⁻¹) := by group
      rw [hvu] at h1
      have hp'd : p' * d = d * p' := hcomm p' hp' d hd
      calc d' * d = p'⁻¹ * (p' * d' * d) := by group
        _ = p'⁻¹ * (d * (p' * d')) := by rw [h1]
        _ = p'⁻¹ * ((d * p') * d') := by group
        _ = p'⁻¹ * ((p' * d) * d') := by rw [hp'd]
        _ = d * d' := by group
    have hsq : (p' * d') * (p' * d') = 1 := by
      rw [← hvu]
      calc v * u * v⁻¹ * (v * u * v⁻¹) = v * (u * u) * v⁻¹ := by group
        _ = 1 := by rw [huu]; group
    have hpd' : p' * d' = d' * p' := hcomm p' hp' d' hd'
    have hsq2 : p' * p' = 1 ∧ d' * d' = 1 := by
      have h1 : p' * p' * (d' * d') = 1 := by
        calc p' * p' * (d' * d') = p' * (p' * d') * d' := by group
          _ = p' * (d' * p') * d' := by rw [hpd']
          _ = (p' * d') * (p' * d') := by group
          _ = 1 := hsq
      have h2 : p' * p' = (d' * d')⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : p' * p' ∈ (T ⊓ K) ⊓ secD K f V :=
        ⟨(T ⊓ K).mul_mem hp' hp', h2 ▸ (secD K f V).inv_mem ((secD K f V).mul_mem hd' hd')⟩
      rw [E.hPD, Subgroup.mem_bot] at h3
      refine ⟨h3, ?_⟩
      rw [h3, one_mul] at h1
      exact h1
    have hp'I : p' ∉ layerI K f := by
      intro hp'I
      have hp'J : p' ∈ pumpJ K f := by
        have : p' ∈ V ⊓ pumpJ K f := by rw [E.hVJeq]; exact ⟨hp', hp'I⟩
        exact this.2
      have hρ1 : E.rho ⟨v * u * v⁻¹, hvuV⟩ ∈ innAut (kBar (pumpJ K f)) := by
        have h1 : E.rho ⟨v * u * v⁻¹, hvuV⟩ = E.rho ⟨p', E.hPV hp'⟩ * E.rho ⟨d', E.hDV hd'⟩ := by
          rw [← map_mul]
          congr 1
          exact Subtype.ext hvu
        rw [h1, (E.rho_ker ⟨d', E.hDV hd'⟩).2 hd', mul_one]
        exact E.rho_mem_inn hp'J
      have hρ2 : E.rho ⟨u, huV⟩ ∈ innAut (kBar (pumpJ K f)) := by
        have h1 : E.rho ⟨u, huV⟩ = (E.rho ⟨v, hv⟩)⁻¹ * E.rho ⟨v * u * v⁻¹, hvuV⟩ * E.rho ⟨v, hv⟩ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          apply Subtype.ext
          show u = v⁻¹ * (v * u * v⁻¹) * v
          group
        rw [h1]
        have := (inferInstance : (innAut (kBar (pumpJ K f))).Normal).conj_mem _ hρ1 (E.rho ⟨v, hv⟩)⁻¹
        simpa using this
      obtain ⟨q, hq, d, hd, hu_eq⟩ := E.inn_decomp ⟨u, huV⟩ hρ2
      have hdP : d ∈ T ⊓ K := by
        have : d = q⁻¹ * u := by
          have : u = q * d := hu_eq
          rw [this]; group
        rw [this]
        exact (T ⊓ K).mul_mem ((T ⊓ K).inv_mem hq.1) hu
      have hd1 : d ∈ (T ⊓ K) ⊓ secD K f V := ⟨hdP, hd⟩
      rw [E.hPD, Subgroup.mem_bot] at hd1
      rw [hd1, mul_one] at hu_eq
      exact huI (by rw [show u = q from hu_eq]; exact hq.2)
    have hp'1 : p' ≠ 1 := fun h => hp'I (h ▸ (layerI K f).one_mem)
    have hp'2 : orderOf p' = 2 := orderOf_eq_prime (by rw [sq]; exact hsq2.1) hp'1
    have hd'f : d' ≠ f := fun h =>
      E.false_of_conj_mul_f hnz hfus hu hu2 huI hp' hp'2 hp'I (isConj_iff.2 ⟨v, by rw [hvu, h]⟩)
    rcases E.card_secD_cases with hD4 | hD8
    ·
      by_cases hvx : v * x = x * v
      · exact E.hSnorm v hv hvx u hu
      have hvf : v * f * v⁻¹ = f := by
        have := E.hVf v hv
        calc v * f * v⁻¹ = (f * v) * v⁻¹ := by rw [this]
          _ = f := by group
      have hxv : v * x * v⁻¹ = x * f := by
        have hxvD : v * x * v⁻¹ ∈ secD K f V := E.hDn v hv x E.hxD
        have hmem : v * x * v⁻¹ ∈ zpowers x ⊔ zpowers f := E.hDeq4 hD4 ▸ hxvD
        have hne1 : v * x * v⁻¹ ≠ x := fun h => hvx (by
          calc v * x = (v * x * v⁻¹) * v := by group
            _ = x * v := by rw [h])
        have hinvx : x = v⁻¹ * (v * x * v⁻¹) * v := by group
        have hne2 : v * x * v⁻¹ ≠ 1 := fun h => E.hx1 (by rw [hinvx, h]; group)
        have hne3 : v * x * v⁻¹ ≠ f := fun h => E.hxf_ne (by
          rw [hinvx, h]
          calc v⁻¹ * f * v = v⁻¹ * (f * v) := by group
            _ = v⁻¹ * (v * f) := by rw [E.hVf v hv]
            _ = f := by group)
        rcases klein_cases E.hx2 E.hf2' E.cfg.hxf hmem with h | h | h | h
        · exact absurd h hne2
        · exact absurd h hne1
        · exact absurd h hne3
        · exact h
      have hbad : d' = x ∨ d' = x * f → False := by
        intro hdx
        have hw₁ : p'⁻¹ * u ∈ layerI K f := E.hP_index_two p' hp' u hu hp'I huI
        have hw₁P : p'⁻¹ * u ∈ T ⊓ K := (T ⊓ K).mul_mem ((T ⊓ K).inv_mem hp') hu
        have hw₁' : v * (p'⁻¹ * u) * v⁻¹ ∈ (T ⊓ K) ⊓ layerI K f :=
          E.hP1n v hv _ ⟨hw₁P, hw₁⟩
        set w₁' := v * (p'⁻¹ * u) * v⁻¹ with hw₁'def
        have hvp' : v * p' * v⁻¹ = (p' * w₁'⁻¹) * d' := by
          have h1 : v * u * v⁻¹ = (v * p' * v⁻¹) * w₁' := by rw [hw₁'def]; group
          have h2 : v * p' * v⁻¹ = (v * u * v⁻¹) * w₁'⁻¹ := by rw [h1]; group
          rw [h2, hvu]
          have h3 : w₁'⁻¹ * d' = d' * w₁'⁻¹ := hcomm w₁'⁻¹ ((T ⊓ K).inv_mem hw₁'.1) d' hd'
          calc p' * d' * w₁'⁻¹ = p' * (d' * w₁'⁻¹) := by group
            _ = p' * (w₁'⁻¹ * d') := by rw [h3]
            _ = p' * w₁'⁻¹ * d' := by group
        have hD2 : d' * (v * d' * v⁻¹) = f := by
          rcases hdx with h1 | h1
          · rw [h1, hxv]
            calc x * (x * f) = x * x * f := by group
              _ = f := by rw [E.hx2, one_mul]
          · rw [h1]
            have h2 : v * (x * f) * v⁻¹ = x := by
              calc v * (x * f) * v⁻¹ = (v * x * v⁻¹) * (v * f * v⁻¹) := by group
                _ = x * f * f := by rw [hxv, hvf]
                _ = x := by rw [mul_assoc, E.hf2', mul_one]
            rw [h2]
            calc x * f * x = x * (f * x) := by group
              _ = x * (x * f) := by rw [← E.cfg.hxf]
              _ = x * x * f := by group
              _ = f := by rw [E.hx2, one_mul]
        have hv₂x : (v * v) * x = x * (v * v) := by
          have h1 : v * (v * x * v⁻¹) * v⁻¹ = x := by
            rw [hxv]
            calc v * (x * f) * v⁻¹ = (v * x * v⁻¹) * (v * f * v⁻¹) := by group
              _ = x * f * f := by rw [hxv, hvf]
              _ = x := by rw [mul_assoc, E.hf2', mul_one]
          calc v * v * x = (v * (v * x * v⁻¹) * v⁻¹) * (v * v) := by group
            _ = x * (v * v) := by rw [h1]
        have hv₂u : (v * v) * u * (v * v)⁻¹ ∈ T ⊓ K :=
          E.hSnorm (v * v) (V.mul_mem hv hv) hv₂x u hu
        have hv₂u' : (v * v) * u * (v * v)⁻¹ = (p' * w₁'⁻¹) * f := by
          calc (v * v) * u * (v * v)⁻¹ = v * (v * u * v⁻¹) * v⁻¹ := by group
            _ = v * (p' * d') * v⁻¹ := by rw [hvu]
            _ = (v * p' * v⁻¹) * (v * d' * v⁻¹) := by group
            _ = ((p' * w₁'⁻¹) * d') * (v * d' * v⁻¹) := by rw [hvp']
            _ = (p' * w₁'⁻¹) * (d' * (v * d' * v⁻¹)) := by group
            _ = (p' * w₁'⁻¹) * f := by rw [hD2]
        have hfP : f ∈ T ⊓ K := by
          have : f = (p' * w₁'⁻¹)⁻¹ * ((v * v) * u * (v * v)⁻¹) := by rw [hv₂u']; group
          rw [this]
          exact (T ⊓ K).mul_mem ((T ⊓ K).inv_mem ((T ⊓ K).mul_mem hp'
            ((T ⊓ K).inv_mem hw₁'.1))) hv₂u
        have : f ∈ (T ⊓ K) ⊓ secD K f V := ⟨hfP, E.hfD⟩
        rw [E.hPD, Subgroup.mem_bot] at this
        exact E.hf1 this
      have hd'D : d' ∈ zpowers x ⊔ zpowers f := E.hDeq4 hD4 ▸ hd'
      rcases klein_cases E.hx2 E.hf2' E.cfg.hxf hd'D with h1 | h1 | h1 | h1
      · rw [hvu, h1, mul_one]; exact hp'
      · exact (hbad (Or.inl h1)).elim
      · exact absurd h1 hd'f
      · exact (hbad (Or.inr h1)).elim
    ·
      have hd'Z : d' ∈ zCenter (secD K f V) := ⟨hd', fun h hh => (hd'c h hh).symm⟩
      rw [E.hZD hD8] at hd'Z
      rcases mem_zpowers_of_mul_self E.hf2' hd'Z with h1 | h1
      · rw [hvu, h1, mul_one]; exact hp'
      · exact absurd h1 hd'f
  obtain ⟨n, -, hn⟩ := E.hdih
  intro v hv p hp
  obtain ⟨u, hu, w, hw, huu, hww, hpuw⟩ := exists_mul_involutions_of_dihedral hn p hp
  have hu' : u ∈ T ⊓ K := hu
  have hw' : w ∈ T ⊓ K := hw
  have : v * p * v⁻¹ = (v * u * v⁻¹) * (v * w * v⁻¹) := by rw [hpuw]; group
  rw [this]
  exact (T ⊓ K).mul_mem (hinv v hv u hu' huu) (hinv v hv w hw' hww)

end Core

end CFSG.GH74.GLS.C3.Layer1.Thm1G33
