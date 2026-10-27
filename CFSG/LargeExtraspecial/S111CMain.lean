module

public import CFSG.LargeExtraspecial.S111ATrans
public import CFSG.LargeExtraspecial.S111CNorm
public import CFSG.LargeExtraspecial.S111AStar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}

omit [Finite G] in
theorem eq_zero_of_mem_span_of_mem_span {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {u v w : V} (hu : u ≠ 0) (huv : u ≠ v) (h1 : w ∈ (ZMod 2) ∙ u)
    (h2 : w ∈ (ZMod 2) ∙ v) : w = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp h2
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases r with rfl | rfl
  · exact zero_smul _ _
  · rcases CFSG.RankThree.Literature.FSmith.zmod2_cases s with rfl | rfl
    · rw [zero_smul, one_smul] at hs
      exact absurd hs.symm hu
    · rw [one_smul, one_smul] at hs
      exact absurd hs.symm huv

theorem exists_Lbar_ne_of_Rbar_ne {t : S.O} (ht : t ∈ S.Lbar g) (hR : Rbar S g t ≠ S.Lbar g) :
    ∃ m : S.M, t ∈ S.Lbar ((m : G) * g) ∧ S.Lbar ((m : G) * g) ≠ S.Lbar g := by
  by_contra hcon
  push Not at hcon
  apply hR
  refine le_antisymm (sSup_le ?_) (le_sSup ⟨1, by rw [OneMemClass.coe_one, one_mul], ht⟩)
  rintro X ⟨m, rfl, hX⟩
  exact (hcon m hX).le

theorem Cfg111.Lbar_inf_Ybar_ne_bot (C : Cfg111 S g A) : S.Lbar g ⊓ Ybar S A ≠ ⊥ := by
  have H := C.hy.hyp4
  obtain ⟨t, ht, ht1, hR⟩ := C.exT
  obtain ⟨m, htm, hne⟩ := exists_Lbar_ne_of_Rbar_ne ht hR
  have hbQ := conj_mem_QG' S m.2 H.conj_mem
  have hbz := conj_ne_z' S m.2 H.conj_ne
  have hbA : (m : G) * g * S.z * ((m : G) * g)⁻¹ ∈ A := by
    refine C.mem_of_Lbar_inf_ne_bot C.mem H.conj_ne hbQ hbz fun h => ht1 ?_
    have h1 : t ∈ S.Lbar g ⊓ S.Lbar ((m : G) * g) := ⟨ht, htm⟩
    rwa [h, mem_bot] at h1
  have hcl : S.cl (g * S.z * g⁻¹) ≠ S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) :=
    fun e => hne (Lbar_eq_of_cl_eq S H.conj_mem H.conj_ne hbQ e.symm)
  have htK : t ∈ Kbar S A g := by
    refine ⟨ht, fun v hv => sub_eq_zero.mp ?_⟩
    exact eq_zero_of_mem_span_of_mem_span (cl_conj_z_ne_zero S H.conj_mem H.conj_ne) hcl
      (C.inc.apply_sub_mem_span C.mem ht hv) (C.inc.apply_sub_mem_span hbA htm hv)
  intro h
  have h1 : t ∈ S.Lbar g ⊓ Ybar S A := ⟨ht, Kbar_le_Ybar C.mem H.conj_ne htK⟩
  rw [h, mem_bot] at h1
  exact ht1 h1

theorem Cfg111.map_eq_of_commute (C : Cfg111 S g A)
    (hNC : ∀ h : G, h ∈ S.M → A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z →
      ∀ k j : G, k * S.z * k⁻¹ ∈ A → k * S.z * k⁻¹ ≠ S.z →
      j * S.z * j⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom → j * S.z * j⁻¹ ≠ S.z →
      ∀ σ ∈ S.Lbar k, ∀ τ ∈ S.Lbar j, σ ≠ 1 → τ ≠ 1 → σ * τ ≠ τ * σ)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (m : S.M)
    (hc : S.ρ m * t * (S.ρ m)⁻¹ * t = t * (S.ρ m * t * (S.ρ m)⁻¹)) :
    A.map (MulAut.conj (m : G)).toMonoidHom = A := by
  rcases C.inter m.2 with h | h
  · exact h
  have hj : (m : G) * g * S.z * ((m : G) * g)⁻¹ ∈ A.map (MulAut.conj (m : G)).toMonoidHom := by
    rw [mul_conj_z S, mem_map_conj_iff]
    simpa [mul_assoc] using C.mem
  have hτ1 : S.ρ m * t * (S.ρ m)⁻¹ ≠ 1 := fun e => ht1 (by
    have e' := congrArg (fun x => (S.ρ m)⁻¹ * x * S.ρ m) e
    simpa [mul_assoc] using e')
  exact absurd hc.symm (hNC m m.2 h g ((m : G) * g) C.mem C.hy.hyp4.conj_ne hj
    (conj_ne_z' S m.2 C.hy.hyp4.conj_ne) t ht _ (conj_mem_Lbar_mul S m ht) ht1 hτ1)

theorem Cfg111.exists_shult (C : Cfg111 S g A)
    (hNC : ∀ h : G, h ∈ S.M → A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z →
      ∀ k j : G, k * S.z * k⁻¹ ∈ A → k * S.z * k⁻¹ ≠ S.z →
      j * S.z * j⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom → j * S.z * j⁻¹ ≠ S.z →
      ∀ σ ∈ S.Lbar k, ∀ τ ∈ S.Lbar j, σ ≠ 1 → τ ≠ 1 → σ * τ ≠ τ * σ) :
    ∃ (P : Sylow 2 S.Mbar) (t : S.O), t ∈ S.Lbar g ∧ t ≠ 1 ∧
      (∀ x ∈ (P : Subgroup S.Mbar), (x : S.O) * t = t * x) ∧
      IsMulCommutative (closure {y : S.O | ∃ m ∈ S.Mbar, y = m * t * m⁻¹ ∧ y * t = t * y}) := by
  obtain ⟨P, hLP, hPN⟩ := exists_sylow_le_normalizer C.hy.hyp4.conj_mem C.hy.cons
  set P' := (P : Subgroup S.Mbar).map S.Mbar.subtype
  have hPY : P' ≤ normalizer (Ybar S A : Set S.O) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, hm⟩ := x.2
    have e : S.Mbar.subtype x = S.ρ m := hm.symm
    have hmN : S.ρ m ∈ normalizer (S.Lbar g : Set S.O) := e ▸ hPN ⟨x, hx, rfl⟩
    rw [e]
    exact mem_normalizer_Ybar (C.map_eq_of_mem_normalizer hmN)
  have hYP : Ybar S A ≤ P' :=
    le_map_sylow_of_le_normalizer P Ybar_le_Mbar (isPGroup_Ybar C.inc) hPY
  obtain ⟨t, ht, ht1, htc⟩ := exists_ne_one_commute_of_le_normalizer (P.isPGroup'.map _)
    (inf_le_right.trans hYP) C.Lbar_inf_Ybar_ne_bot
    fun x hx => mem_normalizer_inf (hPN hx) (hPY hx)
  refine ⟨P, t, ht.1, ht1, fun x hx => htc x ⟨x, hx, rfl⟩, ?_⟩
  have hsub : {y : S.O | ∃ m ∈ S.Mbar, y = m * t * m⁻¹ ∧ y * t = t * y} ⊆
      ((Ybar S A ⊓ centralizer (Ybar S A : Set S.O) : Subgroup S.O) : Set S.O) := by
    rintro _ ⟨_, ⟨m, rfl⟩, rfl, hc⟩
    have hmY := mem_normalizer_Ybar (C.map_eq_of_commute hNC ht.1 ht1 m hc)
    refine ⟨(mem_normalizer_iff.mp hmY t).mp ht.2, mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hw' : (S.ρ m)⁻¹ * w * (S.ρ m)⁻¹⁻¹ ∈ Ybar S A :=
      (mem_normalizer_iff.mp (inv_mem hmY) w).mp hw
    rw [inv_inv] at hw'
    have hc' := htc _ (hYP hw')
    calc w * (S.ρ m * t * (S.ρ m)⁻¹)
        = S.ρ m * ((S.ρ m)⁻¹ * w * S.ρ m * t) * (S.ρ m)⁻¹ := by group
      _ = S.ρ m * (t * ((S.ρ m)⁻¹ * w * S.ρ m)) * (S.ρ m)⁻¹ := by rw [hc']
      _ = S.ρ m * t * (S.ρ m)⁻¹ * w := by group
  have hle := (closure_le _).mpr hsub
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  exact (mem_centralizer_iff.mp (hle a.2).2 b (hle b.2).1).symm

end CFSG.LargeExtraspecial.S11
