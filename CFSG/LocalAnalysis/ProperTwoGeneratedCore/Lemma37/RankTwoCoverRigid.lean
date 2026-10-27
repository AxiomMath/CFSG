module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

variable {J : Type*} [Group J]

@[expose] def IsRigid (x : J) : Prop :=
  ∀ g : J, g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center J → g * x * g⁻¹ = x

theorem conj_eq_of_mem_center {c : J} (hc : c ∈ Subgroup.center J) (y : J) : y * c * y⁻¹ = c := by
  rw [Subgroup.mem_center_iff.mp hc y, mul_inv_cancel_right]

theorem IsRigid.conj {x : J} (hx : IsRigid x) (y : J) : IsRigid (y * x * y⁻¹) := by
  intro g hg
  have h1 : (y⁻¹ * g * y) * x * (y⁻¹ * g * y)⁻¹ * x⁻¹ ∈ Subgroup.center J := by
    have heq : (y⁻¹ * g * y) * x * (y⁻¹ * g * y)⁻¹ * x⁻¹ =
        y⁻¹ * (g * (y * x * y⁻¹) * g⁻¹ * (y * x * y⁻¹)⁻¹) * y⁻¹⁻¹ := by group
    rw [heq, conj_eq_of_mem_center hg]
    exact hg
  calc g * (y * x * y⁻¹) * g⁻¹ = y * ((y⁻¹ * g * y) * x * (y⁻¹ * g * y)⁻¹) * y⁻¹ := by group
    _ = y * x * y⁻¹ := by rw [hx _ h1]

theorem IsRigid.mul_central {x z : J} (hx : IsRigid x) (hz : z ∈ Subgroup.center J) :
    IsRigid (x * z) := by
  intro g hg
  have hzc := Subgroup.mem_center_iff.mp hz
  have heq : g * (x * z) * g⁻¹ * (x * z)⁻¹ = g * x * g⁻¹ * x⁻¹ := by
    calc g * (x * z) * g⁻¹ * (x * z)⁻¹ = g * x * (z * g⁻¹) * z⁻¹ * x⁻¹ := by group
      _ = g * x * g⁻¹ * x⁻¹ := by rw [← hzc g⁻¹]; group
  rw [heq] at hg
  calc g * (x * z) * g⁻¹ = g * x * (z * g⁻¹) := by group
    _ = (g * x * g⁻¹) * z := by rw [← hzc g⁻¹]; group
    _ = x * z := by rw [hx g hg]

@[expose] def centralizerModCenter (x : J) : Subgroup J :=
  (Subgroup.centralizer {((x : J) : J ⧸ Subgroup.center J)}).comap
    (QuotientGroup.mk' (Subgroup.center J))

theorem mem_centralizerModCenter {x g : J} :
    g ∈ centralizerModCenter x ↔ g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center J := by
  rw [centralizerModCenter, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    QuotientGroup.mk'_apply, ← QuotientGroup.eq_one_iff (N := Subgroup.center J),
    show g * x * g⁻¹ * x⁻¹ = (g * x) * (x * g)⁻¹ by group, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, mul_inv_eq_one, QuotientGroup.mk_mul, QuotientGroup.mk_mul]

@[expose] def commutatorHom (x : J) : centralizerModCenter x →* Subgroup.center J where
  toFun g := ⟨g * x * (g : J)⁻¹ * x⁻¹, mem_centralizerModCenter.mp g.2⟩
  map_one' := by ext; simp
  map_mul' g h := by
    have hh := Subgroup.mem_center_iff.mp (mem_centralizerModCenter.mp h.2)
    have hg := Subgroup.mem_center_iff.mp (mem_centralizerModCenter.mp g.2)
    ext
    change (g : J) * h * x * ((g : J) * h)⁻¹ * x⁻¹ =
      ((g : J) * x * (g : J)⁻¹ * x⁻¹) * ((h : J) * x * (h : J)⁻¹ * x⁻¹)
    set c := (h : J) * x * (h : J)⁻¹ * x⁻¹
    calc (g : J) * h * x * ((g : J) * h)⁻¹ * x⁻¹ = (g : J) * (c * x) * (g : J)⁻¹ * x⁻¹ := by
          simp only [c]; group
      _ = c * ((g : J) * x * (g : J)⁻¹ * x⁻¹) := by rw [← mul_assoc, hh]; group
      _ = ((g : J) * x * (g : J)⁻¹ * x⁻¹) * c := hg c

variable [Finite J]

theorem isRigid_of_sylow_le (hZ : IsPGroup 2 (Subgroup.center J)) {x : J}
    (S : Sylow 2 (centralizerModCenter x))
    (hS : ∀ s ∈ (S : Subgroup (centralizerModCenter x)), (s : J) * x = x * s) : IsRigid x := by
  have hker : (S : Subgroup (centralizerModCenter x)) ≤ (commutatorHom x).ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    ext
    change (s : J) * x * (s : J)⁻¹ * x⁻¹ = 1
    rw [hS s hs, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hdvd : (commutatorHom x).ker.index ∣ 2 ^ k := by
    rw [Subgroup.index_ker, ← hk]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hone : (commutatorHom x).ker.index = 1 := by
    rcases a with _ | a
    · simpa using ha
    · exfalso
      apply S.not_dvd_index
      exact (dvd_pow_self 2 (Nat.succ_ne_zero a)).trans
        (ha ▸ Subgroup.index_dvd_of_le hker)
  rw [Subgroup.index_eq_one] at hone
  intro g hg
  have hmem : (⟨g, mem_centralizerModCenter.mpr hg⟩ : centralizerModCenter x) ∈
      (commutatorHom x).ker := by rw [hone]; exact Subgroup.mem_top _
  have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hmem)
  change g * x * g⁻¹ * x⁻¹ = 1 at h1
  exact mul_inv_eq_one.mp h1

theorem exists_ne_of_not_isRigid (hZ : IsPGroup 2 (Subgroup.center J)) {x : J}
    (hx : ¬ IsRigid x) {P : Subgroup J} (hP : IsPGroup 2 P) (hPx : ∀ p ∈ P, p * x = x * p) :
    ∃ P' : Subgroup J, IsPGroup 2 P' ∧ P ≤ P' ∧ P' ≠ P ∧ P' ≤ centralizerModCenter x := by
  set H := centralizerModCenter x
  have hPH : P ≤ H := fun p hp => mem_centralizerModCenter.mpr (by
    rw [hPx p hp, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _)
  obtain ⟨S, hS⟩ := (hP.comap_subtype (K := H)).exists_le_sylow
  refine ⟨(S : Subgroup H).map H.subtype, S.isPGroup'.map _, ?_, ?_, Subgroup.map_subtype_le _⟩
  · intro p hp
    exact ⟨⟨p, hPH hp⟩, hS hp, rfl⟩
  · intro heq
    apply hx
    refine isRigid_of_sylow_le hZ S fun s hs => hPx s ?_
    rw [← heq]
    exact ⟨s, hs, rfl⟩

theorem isRigid_of_commute_sylow (hZ : IsPGroup 2 (Subgroup.center J)) (Q : Sylow 2 J) {x : J}
    (hx : ∀ q ∈ (Q : Subgroup J), q * x = x * q) : IsRigid x := by
  by_contra hnr
  obtain ⟨P', hP', hle, hne, -⟩ := exists_ne_of_not_isRigid hZ hnr Q.isPGroup' hx
  exact hne (Q.3 hP' hle)

end CFSG.ProperTwoGeneratedCore.Lemma37
