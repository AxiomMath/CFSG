module

public import Mathlib.GroupTheory.Sylow

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

private lemma inf_eq_bot_of_isPGroup_two_of_odd {X : Type} [Group X] {V Ob : Subgroup X}
    (hV : IsPGroup 2 V) (hodd : Odd (Nat.card Ob)) : V ⊓ Ob = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxV, hxO⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2) (G := ↥V)).1 hV ⟨x, hxV⟩
  have hkx : orderOf x = 2 ^ k := by
    rw [Subgroup.orderOf_coe (⟨x, hxV⟩ : V), hk]
  have hdvd : 2 ^ k ∣ Nat.card Ob := by
    rw [← hkx]
    exact Subgroup.orderOf_dvd_natCard Ob hxO
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.2 hodd)
      (even_iff_two_dvd.2 (dvd_trans (dvd_pow_self 2 hk0) hdvd))
  rw [hk0, pow_zero] at hkx
  exact orderOf_eq_one_iff.1 hkx

private lemma card_sup_eq_mul_of_inf_eq_bot {X : Type} [Group X] {V Ob : Subgroup X}
    [Ob.Normal] (hdisj : V ⊓ Ob = ⊥) :
    Nat.card (V ⊔ Ob : Subgroup X) = Nat.card V * Nat.card Ob := by
  have hObV : Ob.relIndex V = Nat.card V := by
    have h := Subgroup.relIndex_mul_card Ob V
    rw [inf_comm, hdisj, Subgroup.card_bot, mul_one] at h
    exact h
  have h := Subgroup.relIndex_mul_card Ob (V ⊔ Ob)
  rw [inf_eq_left.mpr le_sup_right, Subgroup.relIndex_sup_right, hObV] at h
  exact h.symm

private lemma map_conj_eq_self_of_mem {X : Type} [Group X] {V : Subgroup X} {v : X}
    (hv : v ∈ V) : V.map (MulAut.conj v).toMonoidHom = V :=
  (Subgroup.mem_normalizer_iff_map_conj_eq).1 (Subgroup.le_normalizer hv)

private lemma map_conj_mul {X : Type} [Group X] (V : Subgroup X) (a b : X) :
    V.map (MulAut.conj (a * b)).toMonoidHom =
      (V.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private lemma coe_smul_sylow {X : Type} [Group X] {K : Subgroup X} (c : ↥K)
    (Q : Sylow 2 ↥K) :
    ((c • Q : Sylow 2 ↥K) : Subgroup ↥K) =
      (Q : Subgroup ↥K).map (MulAut.conj c).toMonoidHom := by
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

private lemma subtype_comp_conj {X : Type} [Group X] (K : Subgroup X) (c : ↥K) :
    K.subtype.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (c : X)).toMonoidHom.comp K.subtype := by
  ext x
  simp [MulAut.conj_apply]

theorem exists_mul_mem_normalizer {X : Type} [Group X] [Finite X] {V Ob : Subgroup X}
    [Ob.Normal] (hV : IsPGroup 2 V) (hodd : Odd (Nat.card Ob)) {y : X}
    (hy : ∀ v ∈ V, y * v * y⁻¹ ∈ V ⊔ Ob) :
    ∃ o ∈ Ob, o⁻¹ * y ∈ normalizer (V : Set X) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nonempty V := ⟨1⟩
  have hdisj : V ⊓ Ob = ⊥ := inf_eq_bot_of_isPGroup_two_of_odd hV hodd
  have hcardK : Nat.card (V ⊔ Ob : Subgroup X) = Nat.card V * Nat.card Ob :=
    card_sup_eq_mul_of_inf_eq_bot hdisj
  have hVrel : V.relIndex (V ⊔ Ob) = Nat.card Ob := by
    have h := Subgroup.relIndex_mul_card V (V ⊔ Ob)
    rw [inf_eq_left.mpr le_sup_left, hcardK,
      mul_comm (Nat.card V) (Nat.card Ob)] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hVndvd : ¬ 2 ∣ V.relIndex (V ⊔ Ob) := by
    rw [hVrel]
    exact fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  have hV'le : V.map (MulAut.conj y).toMonoidHom ≤ V ⊔ Ob := by
    rw [Subgroup.map_le_iff_le_comap]
    intro v hv
    rw [Subgroup.mem_comap]
    simpa [MulAut.conj_apply] using hy v hv
  have hV'pg : IsPGroup 2 (V.map (MulAut.conj y).toMonoidHom) :=
    hV.map (MulAut.conj y).toMonoidHom
  have hV'card : Nat.card (V.map (MulAut.conj y).toMonoidHom) = Nat.card V :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hV'rel : (V.map (MulAut.conj y).toMonoidHom).relIndex (V ⊔ Ob) = Nat.card Ob := by
    have h := Subgroup.relIndex_mul_card (V.map (MulAut.conj y).toMonoidHom) (V ⊔ Ob)
    rw [inf_eq_left.mpr hV'le, hcardK, hV'card,
      mul_comm (Nat.card V) (Nat.card Ob)] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hV'ndvd : ¬ 2 ∣ (V.map (MulAut.conj y).toMonoidHom).relIndex (V ⊔ Ob) := by
    rw [hV'rel]
    exact fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  have hQ : ∃ Q : Sylow 2 ↥(V ⊔ Ob),
      (Q : Subgroup ↥(V ⊔ Ob)) = V.subgroupOf (V ⊔ Ob) :=
    ⟨(hV.comap_subtype (K := V ⊔ Ob)).toSylow hVndvd, rfl⟩
  have hQ' : ∃ Q' : Sylow 2 ↥(V ⊔ Ob),
      (Q' : Subgroup ↥(V ⊔ Ob)) = (V.map (MulAut.conj y).toMonoidHom).subgroupOf (V ⊔ Ob) :=
    ⟨(hV'pg.comap_subtype (K := V ⊔ Ob)).toSylow hV'ndvd, rfl⟩
  obtain ⟨Q, hQcoe⟩ := hQ
  obtain ⟨Q', hQ'coe⟩ := hQ'
  haveI : Finite (Sylow 2 ↥(V ⊔ Ob)) := Sylow.finite_of_finiteIndex Q
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥(V ⊔ Ob)) Q Q'
  have hQmap : (Q : Subgroup ↥(V ⊔ Ob)).map (V ⊔ Ob).subtype = V := by
    rw [hQcoe, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_left]
  have hQ'map : (Q' : Subgroup ↥(V ⊔ Ob)).map (V ⊔ Ob).subtype
      = V.map (MulAut.conj y).toMonoidHom := by
    rw [hQ'coe, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hV'le]
  have hcsub : (Q : Subgroup ↥(V ⊔ Ob)).map (MulAut.conj c).toMonoidHom
      = (Q' : Subgroup ↥(V ⊔ Ob)) := by
    have h1 := congrArg (fun S : Sylow 2 ↥(V ⊔ Ob) => (S : Subgroup ↥(V ⊔ Ob))) hc
    rwa [coe_smul_sylow] at h1
  have hconjX : V.map (MulAut.conj (c : X)).toMonoidHom
      = V.map (MulAut.conj y).toMonoidHom := by
    have h2 := congrArg (Subgroup.map (V ⊔ Ob).subtype) hcsub
    rw [Subgroup.map_map, subtype_comp_conj, ← Subgroup.map_map, hQmap, hQ'map] at h2
    exact h2
  have hc_mem : (c : X) ∈ Ob ⊔ V := by
    rw [sup_comm]
    exact c.2
  obtain ⟨o, ho, v, hv, hov⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Ob) (t := V)).1 hc_mem
  have hconj_o : V.map (MulAut.conj o).toMonoidHom = V.map (MulAut.conj y).toMonoidHom := by
    rw [← hov] at hconjX
    rwa [map_conj_mul V o v, map_conj_eq_self_of_mem hv] at hconjX
  refine ⟨o, ho, (Subgroup.mem_normalizer_iff_map_conj_eq).2 ?_⟩
  show V.map (MulAut.conj (o⁻¹ * y)).toMonoidHom = V
  rw [map_conj_mul V o⁻¹ y, ← hconj_o, ← map_conj_mul V o⁻¹ o, inv_mul_cancel]
  exact map_conj_eq_self_of_mem (V := V) (v := 1) V.one_mem

end CFSG.OddStandard.SmallF3.Omega
