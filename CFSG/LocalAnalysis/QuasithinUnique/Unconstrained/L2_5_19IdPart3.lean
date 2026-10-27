module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdZ
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdCase1
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdCase2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdSyl

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Part3

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G} {Ki KP : Subgroup G}

theorem zK_sq (h : Lv2518 N t zK) : zK * zK = 1 := by
  have hf := h.facts2511
  have hmem : zK ∈ centerOf N.S := by
    rw [hf.centerS_zK]
    exact Subgroup.subset_closure (by simp)
  have := hf.centerS_E4.1.2 zK hmem
  rwa [sq] at this

theorem K_perfect (N : Notation25 hs) : ⁅N.K, N.K⁆ = N.K :=
  Subgroup.isPerfect_iff.mp (BenderBranch.isQuasisimple_of_isComponentIn N.isComp).1

theorem part3_case1 (hI : Inputs2519) (h : Lv2518 N t zK) (hK0 : N.K0 = N.K) (hi : Hyp2519 N i)
    (hsh : Shape N t i Ki KP) (hne : Ki ≠ CFSG.conjugate Ki t) : Concl2519Three N t i := by
  have hf := h.facts2511
  have c := case1_of_shape hI h hi hsh hne
  have hzKK : zK ∈ N.K := hK0 ▸ hf.zK_mem
  obtain ⟨x, hx, hxz⟩ := c.exists_diag' hzKK
  have hy : t * x * t ∈ CFSG.conjugate Ki t := conj_involution_mem c.t_sq rfl hx
  have hxy : x * (t * x * t) = (t * x * t) * x :=
    BenderBranch.commute_of_commutator_eq_bot c.comm hx hy
  have hzz := zK_sq h
  have hxx : x * x = 1 := by
    have h1 : (x * x) * ((t * x * t) * (t * x * t)) = 1 * 1 := by
      calc (x * x) * ((t * x * t) * (t * x * t))
          = x * (x * (t * x * t)) * (t * x * t) := by group
        _ = x * ((t * x * t) * x) * (t * x * t) := by rw [hxy]
        _ = (x * (t * x * t)) * (x * (t * x * t)) := by group
        _ = zK * zK := by rw [hxz]
        _ = 1 * 1 := by rw [hzz, one_mul]
    exact (eq_and_eq_of_mul_eq_mul c.inf (Ki.mul_mem hx hx) Ki.one_mem
      ((CFSG.conjugate Ki t).mul_mem hy hy) (CFSG.conjugate Ki t).one_mem h1).1
  have hcomm : zK * t = t * zK := Subgroup.mem_centralizer_singleton_iff.mp (c.K_cent hzKK)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxt : x⁻¹ * t * x = t * zK := by
    rw [hxinv]
    calc x * t * x = x * (t * x * t) * t := by
          calc x * t * x = x * (t * x * (t * t)) := by rw [c.t_sq]; group
            _ = x * (t * x * t) * t := by group
      _ = zK * t := by rw [← hxz]
      _ = t * zK := hcomm
  obtain ⟨hzeq, -⟩ := h.concl2513.2.2 ⟨x, hxt⟩
  refine ⟨Ki, hsh.comp, Or.inl ⟨hne, ?_, ?_⟩, Or.inl ⟨by rw [hzeq]; exact hzKK, x, by rw [hzeq]; exact hxt⟩⟩
  · rw [← c.KP_eq, c.diag]
    exact (perfectResidualOf_of_perfect (K_perfect N)).symm
  · obtain ⟨e⟩ := c.iso
    rcases c.type with ⟨p, hp, h7, hm⟩ | hm
    · exact ⟨p, hp, h7.le, hm, Unc25Small.statedClassicalModel_psl_of_mulEquiv e hm⟩
    · exact ⟨7, isFermatOrMersenne_seven, le_rfl, psl2_seven_of_psl3_two hm,
        Unc25Small.statedClassicalModel_psl_of_mulEquiv e (psl2_seven_of_psl3_two hm)⟩

theorem part3_case2 (hI : Inputs2519Three) (h : Lv2518 N t zK) (hK0 : N.K0 = N.K)
    (hR : ∀ i' : G, Hyp2519 N i' → Rgrp2519 N i' = Subgroup.closure ({t, i'} : Set G))
    (hi : Hyp2519 N i) (hsh : Shape N t i Ki KP) (heq : Ki = CFSG.conjugate Ki t) :
    Concl2519Three N t i := by
  have hf := h.facts2511
  obtain ⟨hKP, c⟩ := case2_of_shape hI.toInputs2519 h hi hsh heq
  have hneK : N.K ≠ Ki := fun hKKi => hi.not_comp (hKKi ▸ hsh.comp)
  have hswap := exists_swap h hK0 (hR i hi) hi
  have hnoconj := not_conj_t_ti h hK0 hsh.comp c.K_le hneK hswap
  have hZ : ZCtx N.K Ki t i :=
    { t_sq := N.t_mul_self' hf
      i_sq := hi.mul_self
      ti := N.t_comm_of_mem_S hf hi.mem_S
      i_ne_one := hi.ne_one
      Ki_le_Ci := hsh.comp.1
      K_le := c.K_le
      K_le_Ct := h.concl2518.1.1
      tN := c.tN
      not_le := c.not_le_centralizer
      z2 := c.z2
      card4 := fun P hP hPt hPK hPi => card_le_four h hK0 hR hi hP hPt hPK hPi
      four := hi.card_closure h
      noconj := hnoconj }
  have hzKK : zK ∈ N.K := hK0 ▸ hf.zK_mem
  have hzz := zK_sq h
  have hZcard : Nat.card (Subgroup.center ↥Ki) ≤ 2 := hZ.card_center_le_two
  have hconj : ((PatA Ki N.K t ∧ Nat.card (Subgroup.center ↥Ki) ≤ 2) ∨
      (PatB Ki N.K t ∧ Subgroup.center ↥Ki = ⊥) ∨ PatSp4 Ki N.K ∨ PatL5 Ki N.K ∨
      (PatHS Ki N.K t ∧ Subgroup.center ↥Ki = ⊥)) →
      (N.z ∈ N.K ∧ ∃ g : G, g⁻¹ * t * g = t * N.z) := by
    intro hpat
    obtain ⟨x, -, hx⟩ := hI.conj G Ki N.K t c.quasisimple c.tN c.t_sq c.comm c.K_eq hpat zK hzKK hzz
    obtain ⟨hzeq, -⟩ := h.concl2513.2.2 ⟨x, hx⟩
    rw [hzeq]
    exact ⟨hzKK, x, hx⟩
  have hJ2HS : ∀ {Q : Type} [Group Q], Nonempty ((↥Ki ⧸ Subgroup.center ↥Ki) ≃* Q) →
      Subgroup.center ↥Ki = ⊥ → Nonempty (↥Ki ≃* Q) := by
    intro Q _ ⟨e⟩ hZ1
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm.trans e⟩
  refine ⟨Ki, hsh.comp, Or.inr ⟨c.K_eq, ?_⟩, ?_⟩
  · rcases c.pat with ⟨-, hp | hp⟩ | ⟨hA6, hp | hp | hp | hp⟩
    · exact Or.inl ⟨hp.1, hp.2.1, hZcard, hp.2.2⟩
    · have hZ1 : Subgroup.center ↥Ki = ⊥ := by
        by_contra hne
        obtain ⟨x, hx, hxt⟩ := hI.j2cover G Ki N.K t c.quasisimple c.tN c.t_sq c.comm c.K_eq hp
          hZcard i (hZ.i_mem_center hne) hi.ne_one
        exact hnoconj x hxt
      exact Or.inr (Or.inl ⟨hp.1, hJ2HS hp.2.1 hZ1, hp.2.2⟩)
    · exact Or.inr (Or.inr ⟨hA6, Or.inl hp.2⟩)
    · exact Or.inr (Or.inr ⟨hA6, Or.inr (Or.inl hp.2)⟩)
    · have hZ1 : Subgroup.center ↥Ki = ⊥ := by
        by_contra hne
        have hiK := hZ.i_mem_center hne
        obtain ⟨l, hl, hlt⟩ := hp.2.2
        have htKi : t ∈ Ki := hZ.mem_of_inner hiK.1 hl hlt
        exact hI.hscover G Ki N.K t c.quasisimple c.z2 hp.2.1 hne htKi c.t_sq c.compK hp.1
      exact Or.inr (Or.inr ⟨hA6, Or.inr (Or.inr (Or.inl (hJ2HS hp.2.1 hZ1)))⟩)
    · obtain ⟨-, φ, a, b, hab, hind⟩ := hp
      exact Or.inr (Or.inr ⟨hA6, Or.inr (Or.inr (Or.inr ⟨φ⟩))⟩)
  · rcases c.pat with ⟨-, hp | hp⟩ | ⟨hA6, hp | hp | hp | hp⟩
    · exact Or.inl (hconj (Or.inl ⟨hp, hZcard⟩))
    · have hZ1 : Subgroup.center ↥Ki = ⊥ := by
        by_contra hne
        obtain ⟨x, hx, hxt⟩ := hI.j2cover G Ki N.K t c.quasisimple c.tN c.t_sq c.comm c.K_eq hp
          hZcard i (hZ.i_mem_center hne) hi.ne_one
        exact hnoconj x hxt
      exact Or.inl (hconj (Or.inr (Or.inl ⟨hp, hZ1⟩)))
    · exact Or.inl (hconj (Or.inr (Or.inr (Or.inl hp))))
    · exact Or.inl (hconj (Or.inr (Or.inr (Or.inr (Or.inl hp)))))
    · have hZ1 : Subgroup.center ↥Ki = ⊥ := by
        by_contra hne
        have hiK := hZ.i_mem_center hne
        obtain ⟨l, hl, hlt⟩ := hp.2.2
        have htKi : t ∈ Ki := hZ.mem_of_inner hiK.1 hl hlt
        exact hI.hscover G Ki N.K t c.quasisimple c.z2 hp.2.1 hne htKi c.t_sq c.compK hp.1
      exact Or.inl (hconj (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, hZ1⟩)))))
    · obtain ⟨-, φ, a, b, hab, hind⟩ := hp
      exact Or.inr ⟨⟨φ⟩, φ, a, b, hab, hind⟩

theorem part3_2519_of_inputs (hI : Inputs2519Three) : Part3_2519 := by
  intro G _ _ T M hs N t zK h i hi hR
  have hK0 : N.K0 = N.K := k0_eq_K_of_R_eq N h hi (hR i hi)
  refine ⟨hK0, ?_⟩
  obtain ⟨Ki, KP, hsh⟩ := exists_shape hI.i32 hI.p121_3 hI.p121_5 N h hi
  by_cases heq : Ki = CFSG.conjugate Ki t
  · exact part3_case2 hI h hK0 hR hi hsh heq
  · exact part3_case1 hI.toInputs2519 h hK0 hi hsh heq

end Part3

end CFSG.QuasithinUnique.Id2519
