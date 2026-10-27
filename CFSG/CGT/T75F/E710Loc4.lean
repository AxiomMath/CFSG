module

public import CFSG.CGT.T75F.E710Loc3

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {m : ℕ}

structure Loc710 (T T₁ : Subgroup G) (x z : G) : Prop where
  xT : x ∈ T
  x1 : x ≠ 1
  zL : z ∈ normIn T₁ T
  z1 : z ≠ 1
  xz : x * z = z * x
  xzD : x * z ∉ classD T

theorem ker_le_of_two_indep {F : Type*} [Field F] {f fd : Module.Dual F (Fin 3 → F)}
    (hf : f ≠ 0) {v a : Fin 3 → F} (hfv : f v = 0) (hfa : f a = 0)
    (hind : ∀ r s : F, r • v + s • a = 0 → r = 0 ∧ s = 0) (hdv : fd v = 0) (hda : fd a = 0) :
    ∀ w, f w = 0 → fd w = 0 := by
  have hli : LinearIndependent F ![v, a] := LinearIndependent.pair_iff.2 hind
  have hS : Module.finrank F (Submodule.span F (Set.range ![v, a])) = 2 := by
    simpa using finrank_span_eq_card hli
  have hle : Submodule.span F (Set.range ![v, a]) ≤ LinearMap.ker f := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa using hfv
    · simpa using hfa
  have hker : Module.finrank F (LinearMap.ker f) = 2 := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    have h3 : Module.finrank F (Fin 3 → F) = 3 := by simp
    omega
  have heq : Submodule.span F (Set.range ![v, a]) = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hS, hker])
  intro w hw
  have hmem : w ∈ Submodule.span F (Set.range ![v, a]) := by
    rw [heq]
    exact LinearMap.mem_ker.2 hw
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hmem
  rw [Fin.sum_univ_two] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  rw [← hc, map_add, map_smul, map_smul, hdv, hda]
  simp

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

theorem mem_cfgM_of_comm (M : TModel T T₁ 3 m) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ 3 m) {x z : G} (hl : Loc710 T T₁ x z) {d : G} (hd : d ∈ normD T)
    (hdz : d * z = z * d) (hdx : d * x = x * d) : d ∈ cfgM T T₁ := by
  have hcfg := hc.sec3.cfg
  obtain ⟨hzD, hzT⟩ := mem_normD_of_mem_normIn₁ hc hl.zL hl.z1
  by_cases hdT : d ∈ T
  · exact Cfg.normIn_le_cfgM_left T T₁
      ((mem_normIn_iff_comm h63 hc hl.zL hl.z1 hdT).2 hdz.symm)
  obtain ⟨f, v, hf, hv, hfv, hdataz, hLz⟩ := exists_data_normIn₁ M h63 hc hl.zL hl.z1
  obtain ⟨fd, vd, hfdvd, hvd, hfd, hdatad⟩ := M.exists_data hd hdT
  obtain ⟨w₀, hw₀⟩ := exists_dual_apply_eq_one hf
  have hcomm : ubar M.ε d * ubar M.ε z = ubar M.ε z * ubar M.ε d := by
    rw [← ubar_mul M.ε (M.mem_H hd) (M.mem_H hzD), ← ubar_mul M.ε (M.mem_H hzD) (M.mem_H hd), hdz]
  have hrel := transvection_comm_rel hdatad hdataz hcomm w₀
  rw [hw₀, one_mul] at hrel
  have hfdv : fd v = 0 := by
    by_contra hne
    have h2 := congrArg fd hrel
    rw [map_smul, map_smul, hfdvd, smul_zero] at h2
    simp only [smul_eq_mul] at h2
    have h3 : (fd w₀ * f vd) = 0 := by
      rcases mul_eq_zero.1 h2.symm with h | h
      · exact h
      · exact absurd h hne
    rw [h3, zero_smul] at hrel
    rcases smul_eq_zero.1 hrel with h | h
    · exact hne h
    · exact hvd h
  have hxT := hl.xT
  have hfdx : fd (Multiplicative.toAdd (M.φ ⟨x, hxT⟩)) = 0 :=
    (M.comm_iff_apply_eq_zero hd hvd hdatad hxT).1 hdx
  have hfx : f (Multiplicative.toAdd (M.φ ⟨x, hxT⟩)) = 0 :=
    (M.comm_iff_apply_eq_zero hzD hv hdataz hxT).1 hl.xz.symm
  have hnotline : ¬ ∃ r : GaloisField 2 m, Multiplicative.toAdd (M.φ ⟨x, hxT⟩) = r • v := by
    intro h
    have := (hc.mem_classD_mul_iff h62 h63 M hzD hzT hf hdataz hxT).2 h
    apply hl.xzD
    rw [hl.xz]
    exact this
  have hind : ∀ r s : GaloisField 2 m, r • v + s • Multiplicative.toAdd (M.φ ⟨x, hxT⟩) = 0 →
      r = 0 ∧ s = 0 := by
    intro r s hrs
    by_cases hs : s = 0
    · subst hs
      rw [zero_smul, add_zero] at hrs
      exact ⟨(smul_eq_zero.1 hrs).resolve_right hv, rfl⟩
    · exfalso
      apply hnotline
      refine ⟨-(s⁻¹ * r), ?_⟩
      have h1 : s • Multiplicative.toAdd (M.φ ⟨x, hxT⟩) = -(r • v) :=
        eq_neg_of_add_eq_zero_right hrs
      calc Multiplicative.toAdd (M.φ ⟨x, hxT⟩)
          = s⁻¹ • (s • Multiplicative.toAdd (M.φ ⟨x, hxT⟩)) := by
            rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
        _ = s⁻¹ • (-(r • v)) := by rw [h1]
        _ = (-(s⁻¹ * r)) • v := by rw [smul_neg, smul_smul]; exact (neg_smul _ _).symm
  have hker := ker_le_of_two_indep hf hfv hfx hind hfdv hfdx
  have hfd' := apply_eq_mul_of_ker_le hker hw₀
  set c := fd w₀ with hc0
  have hc0ne : c ≠ 0 := by
    intro h0
    apply hfd
    refine LinearMap.ext fun w => ?_
    rw [hfd' w, h0, mul_zero]
    rfl
  have hfvd : f vd = 0 := by
    have h1 : fd vd = f vd * c := hfd' vd
    rw [hfdvd] at h1
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact h
    · exact absurd h hc0ne
  have hv₀ : f (c • vd) = 0 := by rw [map_smul, hfvd, smul_zero]
  obtain ⟨e, he, hdatae⟩ := exists_normIn₁_of_vec M h63 hc hf hLz hv₀
  have hubar : ubar M.ε e = ubar M.ε d := by
    apply eq_of_sact
    intro w
    rw [hdatae w, hdatad w, hfd' w, mul_smul]
  have het : e⁻¹ * d ∈ T :=
    (ubar_eq_iff M.ε (mem_hSub_of_mem_normIn₁ M hc he) (M.mem_H hd)).1 hubar
  have he1 : e ≠ 1 := by
    rintro rfl
    apply hdT
    simpa using het
  obtain ⟨heD, heT⟩ := mem_normD_of_mem_normIn₁ hc he he1
  have hdeq : d = e * (e⁻¹ * d) := by group
  have hdD : d ∈ classD T := hd.1
  have hexists : ∃ r : GaloisField 2 m,
      Multiplicative.toAdd (M.φ ⟨e⁻¹ * d, het⟩) = r • (c • vd) := by
    refine (hc.mem_classD_mul_iff h62 h63 M heD heT hf hdatae het).1 ?_
    rw [← hdeq]
    exact hdD
  obtain ⟨r, hr⟩ := hexists
  have htL : e⁻¹ * d ∈ normIn T T₁ := by
    rw [hLz _ het, hr, map_smul, hv₀, smul_zero]
  have hdLe : d = (e⁻¹ * d) * e := by
    have hcomm' : (e⁻¹ * d) * e = e * (e⁻¹ * d) := (hcfg.comm_L_L₁ htL he)
    rw [hcomm', ← hdeq]
  rw [hdLe]
  exact hcfg.mem_cfgM_iff.2 ⟨e⁻¹ * d, htL, e, he, rfl⟩

end CFSG.CGT.T75F
