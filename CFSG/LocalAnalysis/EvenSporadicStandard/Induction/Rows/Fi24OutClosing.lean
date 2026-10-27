module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutSetup

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Closing

section Algebra

variable {Y : Type} [Group Y]

theorem fi24out_conj_eq (ν : MulAut Y) (y : Y) :
    MulAut.conj y * ν * (MulAut.conj y)⁻¹ = MulAut.conj (y * (ν y)⁻¹) * ν := by
  ext z
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem fi24out_conj_commute {ν : MulAut Y} (hνν : ν * ν = 1) {y : Y}
    (h : ν (ν y * y⁻¹) = ν y * y⁻¹) :
    (MulAut.conj y * ν * (MulAut.conj y)⁻¹) * ν = ν * (MulAut.conj y * ν * (MulAut.conj y)⁻¹) := by
  have hν2 : ∀ x, ν (ν x) = x := fun x => by
    have := congrArg (fun f : MulAut Y => f x) hνν
    simpa using this
  have hwm : y * (ν y)⁻¹ = ν y * y⁻¹ := by
    have h1 : ν (ν y * y⁻¹) = y * (ν y)⁻¹ := by rw [map_mul, map_inv, hν2]
    rw [← h1]
    exact h
  have hw : ν (y * (ν y)⁻¹) = y * (ν y)⁻¹ := by
    rw [map_mul, map_inv, hν2]
    exact hwm.symm
  rw [fi24out_conj_eq]
  have e1 : MulAut.conj (y * (ν y)⁻¹) * ν * ν = MulAut.conj (y * (ν y)⁻¹) := by
    rw [mul_assoc, hνν, mul_one]
  have e2 : ν * (MulAut.conj (y * (ν y)⁻¹) * ν) = MulAut.conj (ν (y * (ν y)⁻¹)) := by
    ext z
    simp [MulAut.mul_apply, MulAut.conj_apply, hν2]
  rw [e1, e2, hw]

theorem fi24out_center_bot {L : Type} [Group L] (hq : CFSG.IsQuasisimple L) :
    center (L ⧸ center L) = ⊥ := by
  have : IsSimpleGroup (L ⧸ center L) := hq.2.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (L ⧸ center L)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

end Algebra

section Closing

variable {H : Type} [Group H] [Finite H] {N L K : Subgroup H} {t u : H}

omit [Finite H] in
theorem fi24out_normalizerAction_conj_of_mem (l : ↥L) {g : H} (hg : g ∈ normalizer (L : Set H)) :
    normalizerAction L ⟨(l : H) * g * (l : H)⁻¹,
      mul_mem (mul_mem (Subgroup.le_normalizer l.2) hg) (inv_mem (Subgroup.le_normalizer l.2))⟩ =
      MulAut.conj (l : ↥L ⧸ center ↥L) * normalizerAction L ⟨g, hg⟩ *
        (MulAut.conj (l : ↥L ⧸ center ↥L))⁻¹ := by
  have h1 : (⟨(l : H) * g * (l : H)⁻¹, mul_mem (mul_mem (Subgroup.le_normalizer l.2) hg)
      (inv_mem (Subgroup.le_normalizer l.2))⟩ : ↥(normalizer (L : Set H))) =
      ⟨(l : H), Subgroup.le_normalizer l.2⟩ * ⟨g, hg⟩ *
        (⟨(l : H), Subgroup.le_normalizer l.2⟩)⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv, fi24out_normalizerAction_of_mem]

theorem fi24out_exists_comm_conj {huN : u ∈ normalizer (L : Set H)}
    (D : Fi24OutLocalData H L K u huN)
    (hS2 : ∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2)
    (htC : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) (hut : u * t = t * u) :
    ∃ g ∈ centralizer ({t} : Set H),
      (g * u * g⁻¹) * u = u * (g * u * g⁻¹) ∧ g * u * g⁻¹ ≠ u := by
  classical
  have hLperf : commutator ↥L = ⊤ := Group.isPerfect_def.1 D.quasisimple.1
  have hZ := fi24out_center_bot D.quasisimple
  set ν := normalizerAction L ⟨u, huN⟩ with hν
  have hνν : ν * ν = 1 := act_mul_self huN D.u_sq
  obtain ⟨yb, hm1, hm2, -⟩ := D.facts.pair
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective yb
  set u₂ : H := (h : H) * u * (h : H)⁻¹ with hu₂
  have hhN : (h : H) ∈ normalizer (L : Set H) := Subgroup.le_normalizer h.2
  have hu₂N : u₂ ∈ normalizer (L : Set H) := mul_mem (mul_mem hhN huN) (inv_mem hhN)
  have hρ : normalizerAction L ⟨u₂, hu₂N⟩ =
      MulAut.conj (h : ↥L ⧸ center ↥L) * ν * (MulAut.conj (h : ↥L ⧸ center ↥L))⁻¹ :=
    fi24out_normalizerAction_conj_of_mem h huN
  have hu₂u₂ : u₂ * u₂ = 1 := by
    calc u₂ * u₂ = (h : H) * (u * u) * (h : H)⁻¹ := by rw [hu₂]; group
      _ = 1 := by rw [D.u_sq]; group
  have hht : (h : H) * t = t * (h : H) := mem_centralizer_iff.1 htC (h : H) h.2
  have hu₂t : u₂ * t = t * u₂ :=
    (((Commute.mul_left (show Commute (h : H) t from hht) (show Commute u t from hut)).mul_left
      (show Commute (h : H) t from hht).inv_left)).eq
  have hcomm : normalizerAction L ⟨u₂, hu₂N⟩ * ν = ν * normalizerAction L ⟨u₂, hu₂N⟩ := by
    rw [hρ]
    exact fi24out_conj_commute hνν hm2
  obtain ⟨e, heC, het, hec⟩ := fi24out_lift hLperf hS2 htC ht2 huN D.u_sq hut D.K_comm_u
    D.bar_eq D.facts.cent hu₂N hu₂u₂ hu₂t hcomm
  refine ⟨e * (h : H), mem_centralizer_singleton_iff.2 ?_, ?_, ?_⟩
  · calc e * (h : H) * t = e * (t * (h : H)) := by rw [mul_assoc, hht]
      _ = t * (e * (h : H)) := by rw [← mul_assoc, het, mul_assoc]
  · have : e * (h : H) * u * (e * (h : H))⁻¹ = e * u₂ * e⁻¹ := by rw [hu₂]; group
    rw [this]
    exact hec
  · intro hge
    have this : e * (h : H) * u * (e * (h : H))⁻¹ = e * u₂ * e⁻¹ := by rw [hu₂]; group
    rw [this] at hge
    have heN : e ∈ normalizer (L : Set H) := Subgroup.centralizer_le_normalizer _ heC
    have he1 : normalizerAction L ⟨e, heN⟩ = 1 :=
      (normalizerAction_eq_one_iff hLperf ⟨e, heN⟩).2 heC
    have h1 : normalizerAction L ⟨e * u₂ * e⁻¹, mul_mem (mul_mem heN hu₂N) (inv_mem heN)⟩ =
        normalizerAction L ⟨u₂, hu₂N⟩ := by
      have : (⟨e * u₂ * e⁻¹, mul_mem (mul_mem heN hu₂N) (inv_mem heN)⟩ :
          ↥(normalizer (L : Set H))) = ⟨e, heN⟩ * ⟨u₂, hu₂N⟩ * ⟨e, heN⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, he1]
      simp
    have h2 : normalizerAction L ⟨e * u₂ * e⁻¹, mul_mem (mul_mem heN hu₂N) (inv_mem heN)⟩ = ν := by
      show _ = normalizerAction L ⟨u, huN⟩
      congr 1
      exact Subtype.ext hge
    rw [h1, hρ, fi24out_conj_eq] at h2
    have h3 : MulAut.conj ((h : ↥L ⧸ center ↥L) * (ν (h : ↥L ⧸ center ↥L))⁻¹) = 1 :=
      mul_eq_right.1 h2
    have h4 := eq_one_of_conj_eq_one hZ h3
    apply hm1
    have : ν (h : ↥L ⧸ center ↥L) * (h : ↥L ⧸ center ↥L)⁻¹ =
        ((h : ↥L ⧸ center ↥L) * (ν (h : ↥L ⧸ center ↥L))⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
    rw [this, h4, inv_one]

theorem fi24out_fusedSet_eq (S : Fi24OutSetup H N L t u) (hf : Sol78Fusion u t)
    (hex : ∃ g ∈ centralizer ({t} : Set H),
      (g * u * g⁻¹) * u = u * (g * u * g⁻¹) ∧ g * u * g⁻¹ ≠ u)
    {t' : H} (ht' : t' ∈ fusedSet u t) : t' = t := by
  rcases hf t' ht' with h1 | h1
  · exact h1
  · exfalso
    have hc : IsConj t (u * t) := h1 ▸ ht'.1
    obtain ⟨g, hg, hwu, hwne⟩ := hex
    have hgt : g * t = t * g := mem_centralizer_singleton_iff.1 hg
    have hut := S.u_comm_t
    have huu := S.u_mul_self
    obtain ⟨w, hw⟩ : ∃ w, w = g * u * g⁻¹ := ⟨_, rfl⟩
    rw [← hw] at hwu hwne
    have hwt : w * t = t * w := by
      have h2 := (((show Commute g t from hgt).mul_left (show Commute u t from hut)).mul_left
        (show Commute g t from hgt).inv_left).eq
      rw [hw]
      exact h2
    have hconj : g * (u * t) * g⁻¹ = w * t := by
      calc g * (u * t) * g⁻¹ = (g * u * g⁻¹) * (g * t * g⁻¹) := by group
        _ = w * t := by rw [← hw, hgt]; group
    have hmem : w * t ∈ fusedSet u t := by
      refine ⟨hc.trans (isConj_iff.2 ⟨g, hconj⟩), ?_, ?_⟩
      · calc w * t * u = w * (t * u) := mul_assoc w t u
          _ = w * (u * t) := by rw [hut.symm]
          _ = (w * u) * t := (mul_assoc w u t).symm
          _ = (u * w) * t := by rw [hwu]
          _ = u * (w * t) := mul_assoc u w t
      · calc w * t * t = (w * t) * t := rfl
          _ = (t * w) * t := by rw [hwt]
          _ = t * (w * t) := mul_assoc t w t
    rcases hf _ hmem with h3 | h3
    · have h4 : w = 1 := mul_eq_right.1 h3
      apply ne_one_of_orderOf_eq_two S.u_order
      have h5 : u = g⁻¹ * w * g := by rw [hw]; group
      rw [h5, h4]
      group
    · exact hwne (mul_right_cancel h3)

theorem fi24out_false_of_fusion (S : Fi24OutSetup H N L t u)
    (hfused : ∀ t' ∈ fusedSet u t, t' = t) (D : Fi24OutLocalData H L K u S.u_mem)
    (hS2 : ∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2) : False := by
  classical
  have hLperf := S.perfect
  obtain ⟨g, hne, hcomm⟩ := exists_fused_commuting_involution_of_fStar S.fstar S.t_order
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : H, t₁ = g * t * g⁻¹ := ⟨_, rfl⟩
  rw [← ht₁] at hne hcomm
  have ht₁t₁ : t₁ * t₁ = 1 := by
    calc t₁ * t₁ = g * (t * t) * g⁻¹ := by rw [ht₁]; group
      _ = 1 := by rw [S.t_mul_self]; group
  have ht₁N : t₁ ∈ normalizer (L : Set H) :=
    S.centralizer_t_le (mem_centralizer_singleton_iff.2 hcomm)
  set ν := normalizerAction L ⟨u, S.u_mem⟩ with hν
  set σ := normalizerAction L ⟨t₁, ht₁N⟩ with hσ
  have hσσ : σ * σ = 1 := act_mul_self ht₁N ht₁t₁
  obtain ⟨yb, hyb⟩ := D.facts.fusion σ hσσ
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective yb
  set h' : ↥L := h⁻¹ with hh'
  set t₂ : H := (h' : H) * t₁ * (h' : H)⁻¹ with ht₂
  have hh'N : (h' : H) ∈ normalizer (L : Set H) := Subgroup.le_normalizer h'.2
  have ht₂N : t₂ ∈ normalizer (L : Set H) := mul_mem (mul_mem hh'N ht₁N) (inv_mem hh'N)
  have hρ₂ : normalizerAction L ⟨t₂, ht₂N⟩ =
      MulAut.conj (h' : ↥L ⧸ center ↥L) * σ * (MulAut.conj (h' : ↥L ⧸ center ↥L))⁻¹ :=
    fi24out_normalizerAction_conj_of_mem h' ht₁N
  have ht₂t₂ : t₂ * t₂ = 1 := by
    calc t₂ * t₂ = (h' : H) * (t₁ * t₁) * (h' : H)⁻¹ := by rw [ht₂]; group
      _ = 1 := by rw [ht₁t₁]; group
  have hh't : (h' : H) * t = t * (h' : H) := mem_centralizer_iff.1 S.t_mem (h' : H) h'.2
  have ht₂t : t₂ * t = t * t₂ :=
    (((show Commute (h' : H) t from hh't).mul_left (show Commute t₁ t from hcomm)).mul_left
      (show Commute (h' : H) t from hh't).inv_left).eq
  have hcm : normalizerAction L ⟨t₂, ht₂N⟩ * ν = ν * normalizerAction L ⟨t₂, ht₂N⟩ := by
    rw [hρ₂]
    have hC : (MulAut.conj (h' : ↥L ⧸ center ↥L)) = (MulAut.conj (h : ↥L ⧸ center ↥L))⁻¹ := by
      rw [hh', QuotientGroup.mk_inv, map_inv]
    rw [hC, inv_inv]
    set C := MulAut.conj (h : ↥L ⧸ center ↥L) with hCdef
    calc (C⁻¹ * σ * C) * ν = C⁻¹ * (σ * (C * ν * C⁻¹)) * C := by group
      _ = C⁻¹ * ((C * ν * C⁻¹) * σ) * C := by rw [hyb]
      _ = ν * (C⁻¹ * σ * C) := by group
  obtain ⟨e, heC, het, hec⟩ := fi24out_lift hLperf hS2 S.t_mem S.t_order S.u_mem S.u_mul_self
    S.u_comm_t D.K_comm_u D.bar_eq D.facts.cent ht₂N ht₂t₂ ht₂t hcm
  have hmem : e * t₂ * e⁻¹ ∈ fusedSet u t := by
    refine ⟨isConj_iff.2 ⟨e * (h' : H) * g, ?_⟩, hec, ?_⟩
    · rw [ht₂, ht₁]
      group
    · exact (((show Commute e t from het).mul_left (show Commute t₂ t from ht₂t)).mul_left
        (show Commute e t from het).inv_left).eq
  have h1 := hfused _ hmem
  apply hne
  have h2 : t₂ = t := by
    have : e⁻¹ * (e * t₂ * e⁻¹) * e = e⁻¹ * t * e := by rw [h1]
    have e1 : e⁻¹ * (e * t₂ * e⁻¹) * e = t₂ := by group
    have e2 : e⁻¹ * t * e = t := by
      have := (show Commute e t from het).inv_left.eq
      calc e⁻¹ * t * e = t * e⁻¹ * e := by rw [this]
        _ = t := by group
    rw [e1, e2] at this
    exact this
  have hh'H : (h' : H) = (h : H)⁻¹ := rfl
  calc t₁ = (h : H) * t₂ * (h : H)⁻¹ := by rw [ht₂, hh'H]; group
    _ = (h : H) * t * (h : H)⁻¹ := by rw [h2]
    _ = t := by
      have := (show Commute (h : H) t from (mem_centralizer_iff.1 S.t_mem (h : H) h.2)).eq
      rw [this]
      group

end Closing

end CFSG.EvenSporadicStandard.Induction
