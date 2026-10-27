module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Aux
public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Core
public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Pre
public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Rec
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk412Dih

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1G35

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

theorem Env33.false_of_card8 (E : Env33 x y K T V W f z) (hG : C3Hyp G) (hVW : V ≠ W)
    (h8 : 8 ≤ Nat.card ↥(secD K f V))
    (e7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPre : Pre35 x y K T V W f z := ⟨E.cfg, E.hKN, E.hxS, E.hPK, E.hcen, E.hfout, E.hzu, e7⟩
  have hP8 : Nat.card ↥(T ⊓ K) = 8 := hPre.card_P
  obtain ⟨hmax, hshape⟩ := E.hDshape
  set D := secD K f V with hD
  obtain ⟨a, haD, hVa, h4a, hxa, hDa, hfa⟩ : ∃ a ∈ D, (∀ v ∈ V, v * a * v⁻¹ ∈ zpowers a) ∧
      4 ∣ orderOf a ∧ x ∉ zpowers a ∧ (∀ d ∈ D, d ∈ zpowers a ∨ x⁻¹ * d ∈ zpowers a) ∧
      f ∈ zpowers a := by
    rcases hshape with ⟨h4, -⟩ | h
    · omega
    · exact h
  obtain ⟨b₀, hb₀W, hb₀N, hb₀V⟩ := exists_mem_normalizer_not_mem E.cfg.V_le_W hVW
    E.cfg.sylowW.isPGroup
  have hb₀2 : ∃ k : ℕ, b₀ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.cfg.sylowW.isPGroup ⟨b₀, hb₀W⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨b₁, hb₁, hb₁V, hb₁2⟩ := exists_pow_not_mem_sq_mem hb₀2 hb₀V
  have hb₁W : b₁ ∈ W := (zpowers_le).2 hb₀W hb₁
  have hb₁N : b₁ ∈ normalizer (V : Set G) := (zpowers_le).2 hb₀N hb₁
  have hb₁b₁ : b₁ * b₁ ∈ V := by rw [← sq]; exact hb₁2
  obtain ⟨-, -, hDD', hcomm⟩ := E.key_c h8 hb₁W hb₁N hb₁V hb₁2
  set D' : Subgroup G := D.map (MulAut.conj b₁).toMonoidHom with hD'
  have hbn : ∀ v ∈ V, b₁ * v * b₁⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.1 hb₁N v).1 hv
  have hDV : D ≤ V := E.hDV
  have hD'V : D' ≤ V := by
    rintro _ ⟨d, hd, rfl⟩
    exact hbn d (hDV hd)
  have hD'card : Nat.card ↥D' = Nat.card ↥D :=
    Subgroup.card_map_of_injective (MulAut.conj b₁).injective
  have hVle : Nat.card ↥V ≤ 8 * Nat.card ↥D := by
    let φ : ↥(T ⊓ K) × ↥D → ↥V := fun pd =>
      ⟨(pd.1 : G) * (pd.2 : G), V.mul_mem (E.hPV pd.1.2) (hDV pd.2.2)⟩
    have hsurj : Function.Surjective φ := by
      rintro ⟨v, hv⟩
      obtain ⟨p, hp, d, hd, rfl⟩ := E.hV_eq_PD hP8 v hv
      exact ⟨(⟨p, hp⟩, ⟨d, hd⟩), rfl⟩
    have := Nat.card_le_card_of_surjective φ hsurj
    rwa [Nat.card_prod, hP8] at this
  let ψ : ↥D × ↥D' → ↥V := fun de =>
    ⟨(de.1 : G) * (de.2 : G), V.mul_mem (hDV de.1.2) (hD'V de.2.2)⟩
  have hψinj : Function.Injective ψ := by
    rintro ⟨⟨d, hd⟩, ⟨e, he⟩⟩ ⟨⟨d', hd'⟩, ⟨e', he'⟩⟩ h
    have h1 : d * e = d' * e' := congrArg Subtype.val h
    obtain ⟨h2, h3⟩ := unique_decomp hDD' hd hd' he he' h1
    subst h2
    subst h3
    rfl
  have hψle : Nat.card ↥D * Nat.card ↥D ≤ Nat.card ↥V := by
    have := Nat.card_le_card_of_injective ψ hψinj
    rwa [Nat.card_prod, hD'card] at this
  have hDpos : 0 < Nat.card ↥D := Nat.card_pos
  have hD8 : Nat.card ↥D = 8 := by
    have h1 : Nat.card ↥D * Nat.card ↥D ≤ Nat.card ↥D * 8 := by omega
    have h2 := Nat.le_of_mul_le_mul_left h1 hDpos
    omega
  have hV64 : Nat.card ↥V = 64 := by
    rw [hD8] at hψle hVle
    omega
  have hψbij : Function.Bijective ψ := hψinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, hD'card, hD8, hV64])
  have hdec : ∀ v ∈ V, ∃ d ∈ D, ∃ e ∈ D', v = d * e := by
    intro v hv
    obtain ⟨⟨d, e⟩, h⟩ := hψbij.2 ⟨v, hv⟩
    exact ⟨d, d.2, e, e.2, (congrArg Subtype.val h).symm⟩
  obtain ⟨w', hw', hbsq⟩ := exists_involution_coset (D := D) (D' := D') (V := V) (b₁ := b₁) hD'
    E.hDn hb₁b₁ hDD' hcomm hdec
  set b : G := b₁ * w'⁻¹ with hb
  have hw'V : w' ∈ V := hD'V hw'
  have hbW : b ∈ W := W.mul_mem hb₁W (W.inv_mem (E.cfg.V_le_W hw'V))
  have hbN : b ∈ normalizer (V : Set G) :=
    (normalizer (V : Set G)).mul_mem hb₁N
      ((normalizer (V : Set G)).inv_mem (Subgroup.le_normalizer hw'V))
  have hbV : b ∉ V := by
    intro h
    apply hb₁V
    have := V.mul_mem h hw'V
    have e1 : b * w' = b₁ := by rw [hb]; group
    rwa [e1] at this
  have hbconj : ∀ d ∈ D, b * d * b⁻¹ = b₁ * d * b₁⁻¹ := by
    intro d hd
    have h1 := hcomm d hd w' hw'
    have hwd : w'⁻¹ * d * w' = d := by
      calc w'⁻¹ * d * w' = w'⁻¹ * (d * w') := by group
        _ = w'⁻¹ * (w' * d) := by rw [h1]
        _ = d := by group
    calc b * d * b⁻¹ = b₁ * (w'⁻¹ * d * w') * b₁⁻¹ := by rw [hb]; group
      _ = b₁ * d * b₁⁻¹ := by rw [hwd]
  have hxD : x ∈ D := E.hxD
  have hx2 : x * x = 1 := E.hx2
  have hDcard8 : Nat.card ↥D = 8 := hD8
  have ha4 : orderOf a = 4 := by
    have hdvd : orderOf a ∣ 8 := by
      have := orderOf_dvd_natCard (⟨a, haD⟩ : ↥D)
      rwa [Subgroup.orderOf_mk, hDcard8] at this
    obtain ⟨m, hm⟩ := h4a
    have hm2 : m ≤ 2 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hm0 : 0 < m := by
      have := orderOf_pos a
      omega
    interval_cases m
    · omega
    · exfalso
      have hz : zpowers a = D := Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 haD) (by
        rw [Nat.card_zpowers, hDcard8]
        omega)
      exact hxa (hz ▸ hxD)
  have hxinv : x * a * x⁻¹ = a⁻¹ :=
    conj_eq_inv ha4 (hVa x E.cfg.x_mem_V) hDa (E.hx_not_cent h8)
  have hDcl : D = closure ({a, x} : Set G) := by
    have haC : a ∈ closure ({a, x} : Set G) := subset_closure (by simp)
    have hxC : x ∈ closure ({a, x} : Set G) := subset_closure (by simp)
    apply le_antisymm
    · intro d hd
      rcases hDa d hd with h | h
      · exact (zpowers_le).2 haC h
      · have : d = x * (x⁻¹ * d) := by group
        rw [this]
        exact Subgroup.mul_mem _ hxC ((zpowers_le).2 haC h)
    · refine (Subgroup.closure_le D).2 ?_
      intro g hg
      rcases hg with rfl | hg
      · exact haD
      · rw [Set.mem_singleton_iff.1 hg]
        exact hxD
  have he₀ : Nonempty (closure ({a, x} : Set G) ≃* D8) :=
    exists_mulEquiv_dihedral_of_inverting (n := 3) (by norm_num) (by rw [ha4]; norm_num) hx2 hxinv
  let e : ↥D ≃* D8 := (MulEquiv.subgroupCongr hDcl).trans he₀.some
  have hou : orderOf (e ⟨a, haD⟩) = 4 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact ha4
  have hu4 : (e ⟨a, haD⟩) ^ 4 = 1 := by
    have := pow_orderOf_eq_one (e ⟨a, haD⟩)
    rwa [hou] at this
  have hu2 : (e ⟨a, haD⟩) ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hou]; norm_num)
  have hur : (e ⟨a, haD⟩) ^ 2 = DihedralGroup.r 2 := rot_sq _ hu4 hu2
  have hs_sq : e ⟨x, hxD⟩ * e ⟨x, hxD⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x, hxD⟩ * ⟨x, hxD⟩ : ↥D) = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hxa_sq : (a * a) ∈ zpowers a := Subgroup.mul_mem _ (mem_zpowers a) (mem_zpowers a)
  have hs1 : e ⟨x, hxD⟩ ≠ 1 := by
    intro h
    have : (⟨x, hxD⟩ : ↥D) = 1 := e.injective (by rw [h, map_one])
    exact E.hx1 (congrArg Subtype.val this)
  have hsr2 : e ⟨x, hxD⟩ ≠ DihedralGroup.r 2 := by
    intro h
    apply hxa
    have h1 : e ⟨x, hxD⟩ = e (⟨a, haD⟩ * ⟨a, haD⟩) := by
      rw [h, map_mul, ← sq, hur]
    have h2 : (⟨x, hxD⟩ : ↥D) = ⟨a, haD⟩ * ⟨a, haD⟩ := e.injective h1
    have h3 : x = a * a := congrArg Subtype.val h2
    rw [h3]
    exact hxa_sq
  have hs : alphaFn (e ⟨x, hxD⟩) = Multiplicative.ofAdd 1 := refl_of_inv _ hs_sq hs1 hsr2
  have hfaa : f = a * a := by
    have ha2 : a * a ≠ 1 := by
      intro h
      have : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
      rw [ha4] at this
      omega
    have ha4' : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
    have h2 : (a * a) * (a * a) = 1 := by
      calc (a * a) * (a * a) = a ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := ha4'
    have := IVK.DihedralAux.cyclic_unique_involution (G := ↥(zpowers a))
      (a := ⟨f, hfa⟩) (b := ⟨a * a, hxa_sq⟩) (fun h => E.hf1 (congrArg Subtype.val h))
      (fun h => ha2 (congrArg Subtype.val h)) (Subtype.ext E.hf2') (Subtype.ext h2)
    exact congrArg Subtype.val this
  have hfD : f ∈ D := E.hfD
  have hef : e ⟨f, hfD⟩ = DihedralGroup.r 2 := by
    have : (⟨f, hfD⟩ : ↥D) = ⟨a, haD⟩ * ⟨a, haD⟩ := Subtype.ext hfaa
    rw [this, map_mul, ← sq, hur]
  let ι : D8 →* G := D.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := D.subtype_injective.comp e.symm.injective
  have hmemD : ∀ u : D8, ι u ∈ D := fun u => (e.symm u).2
  have hb' : ∀ v : D8, b * ι v * b⁻¹ ∈ D' := by
    intro v
    rw [hbconj _ (hmemD v), hD']
    exact ⟨ι v, hmemD v, by simp [MulAut.conj_apply]⟩
  have hbmem : ∀ u v : D8, ι u * (b * ι v * b⁻¹) ∈ V := fun u v =>
    V.mul_mem (hDV (hmemD u)) (hD'V (hb' v))
  have hint : ∀ u v : D8, ι u = b * ι v * b⁻¹ → u = 1 := by
    intro u v h
    have h1 : ι u ∈ D ⊓ D' := ⟨hmemD u, h ▸ hb' v⟩
    rw [hDD', Subgroup.mem_bot] at h1
    exact hι (by rw [h1, map_one])
  let d : WrData G := ⟨ι, b, hbsq, hι, fun u v => hcomm _ (hmemD u) _ (hb' v), hint,
    fun u v h => hbV (by rw [h]; exact hbmem u v)⟩
  have hΨ : Function.Injective d.Ψ := d.Ψ_injective
  have hΨW : ∀ m : M35, d.Ψ m ∈ W := by
    intro m
    rw [WrData.Ψ_apply]
    refine W.mul_mem ?_ ?_
    · rw [show m.left = (m.left.1, m.left.2) from rfl, WrData.fn_apply]
      exact W.mul_mem (E.cfg.V_le_W (hDV (hmemD _))) (E.cfg.V_le_W (hD'V (hb' _)))
    · by_cases hq : m.right = 1
      · rw [hq, WrData.fg_one]
        exact W.one_mem
      · rw [WrData.fg_ne d hq]
        exact hbW
  have hVmap : Vsub.map d.Ψ = V := by
    have hle : Vsub.map d.Ψ ≤ V := by
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨u, v, rfl⟩ := exists_inl'_of_mem_Vsub hm
      rw [WrData.Ψ_inl']
      exact hbmem u v
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective hΨ, card_Vsub, hV64]
  have hιf : ι (DihedralGroup.r 2) = f := by
    show ((e.symm (DihedralGroup.r 2) : ↥D) : G) = f
    rw [e.symm_apply_eq.2 hef.symm]
  have hιx : ι (e ⟨x, hxD⟩) = x := by
    show ((e.symm (e ⟨x, hxD⟩) : ↥D) : G) = x
    rw [e.symm_apply_apply]
  have hfΨ : d.Ψ (inl' (DihedralGroup.r 2) 1) = f := by
    rw [WrData.Ψ_inl']
    show ι (DihedralGroup.r 2) * (b * ι 1 * b⁻¹) = f
    rw [map_one, mul_one, mul_inv_cancel, mul_one]
    exact hιf
  have hxΨ : d.Ψ (inl' (e ⟨x, hxD⟩) 1) = x := by
    rw [WrData.Ψ_inl']
    show ι (e ⟨x, hxD⟩) * (b * ι 1 * b⁻¹) = x
    rw [map_one, mul_one, mul_inv_cancel, mul_one]
    exact hιx
  have hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 :=
    no_normal_index_two' hG.kproper.1 hG.kproper.2.1
  exact core35 hno hΨ E.cfg.sylowW hΨW (by rw [hVmap, hfΨ]; exact E.cfg.sylowV) hs
    (fun S hS hS2 => by
      rw [hxΨ] at hS
      exact Thm1L3A7.card_le_32_of_A7 E.cfg.hx2 hS2 hS E.cfg.hKx E.hKN e7.some E.hxS)

end CFSG.GH74.GLS.C3.Layer1.Thm1G33

end
