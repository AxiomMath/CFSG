module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1SD

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3

open CFSG.ClassicalInvolution.Generic

structure SFHyp {S : Type} [Group S] (A B : Subgroup S) (r : S) (x : MulAut S) : Prop where
  quat : QuatTwinDatum A r
  twin : ∃ q ∈ Subgroup.centralizer ({r} : Set S), conjSub q A = B
  ne : B ≠ A
  sq : x * x = 1
  fixA : ∀ a ∈ A, x a = a
  onB : ∃ w ∈ B, orderOf w = 4 ∧ ∀ b ∈ B, x b = w * b * w⁻¹
  noNbr : ∀ C ∈ CoreAssembly.conjClass A, (∀ c ∈ C, x c = c) → C ≠ A →
    ¬ C ≤ Subgroup.normalizer (A : Set S)

section Transport

variable {M N : Type} [Group M] [Group N] (e : M ≃* N)

private theorem exists_of_mem_map_equiv {K : Subgroup M} {y : N} (hy : y ∈ K.map e.toMonoidHom) :
    ∃ a ∈ K, e a = y :=
  hy

private theorem mem_map_equiv_of_mem {K : Subgroup M} {a : M} (ha : a ∈ K) :
    e a ∈ K.map e.toMonoidHom :=
  Subgroup.mem_map_of_mem _ ha

private theorem mem_map_equiv_apply_iff {K : Subgroup M} {a : M} :
    e a ∈ K.map e.toMonoidHom ↔ a ∈ K := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem map_mem_centralizer {s c : M} (hc : c ∈ Subgroup.centralizer ({s} : Set M)) :
    e c ∈ Subgroup.centralizer ({e s} : Set N) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  rw [← map_mul, ← map_mul, hc]

private theorem mem_centralizer_of_map {s c : M}
    (hc : e c ∈ Subgroup.centralizer ({e s} : Set N)) :
    c ∈ Subgroup.centralizer ({s} : Set M) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  apply e.injective
  rw [map_mul, map_mul]
  exact hc

private theorem mem_normalizer_of_map {A : Subgroup M} {c : M}
    (hc : e c ∈ Subgroup.normalizer ((A.map e.toMonoidHom : Subgroup N) : Set N)) :
    c ∈ Subgroup.normalizer (A : Set M) := by
  rw [Subgroup.mem_normalizer_iff] at hc ⊢
  intro a
  have h1 := hc (e a)
  have e1 : e c * e a * (e c)⁻¹ = e (c * a * c⁻¹) := by simp
  simp only [e1, mem_map_equiv_apply_iff] at h1
  exact h1

private theorem isUniqueInvolution_map_equiv {K : Subgroup M} {s : M}
    (h : IsUniqueInvolution K s) : IsUniqueInvolution (K.map e.toMonoidHom) (e s) where
  mem := mem_map_equiv_of_mem e h.mem
  ne_one := fun h1 => h.ne_one (e.injective (h1.trans (map_one e).symm))
  sq := by rw [← map_mul, h.sq, map_one]
  unique := by
    intro y hy hy2
    obtain ⟨k, hk, rfl⟩ := exists_of_mem_map_equiv e hy
    have h2 : k * k = 1 := e.injective (by rw [map_mul, hy2, map_one])
    rcases h.unique k hk h2 with h3 | h3
    · left
      rw [h3, map_one]
    · right
      rw [h3]

theorem quatTwinDatum_map_mulEquiv {K : Subgroup M} {s : M} (h : QuatTwinDatum K s) :
    QuatTwinDatum (K.map e.toMonoidHom) (e s) := by
  obtain ⟨eK⟩ := h.q8
  refine ⟨⟨(K.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK⟩,
    isUniqueInvolution_map_equiv e h.inv, ?_, ?_⟩
  · intro c hc
    obtain ⟨c', rfl⟩ := e.surjective c
    have h1 : conjSub (e c') (K.map e.toMonoidHom) = (conjSub c' K).map e.toMonoidHom :=
      conjSub_map e.toMonoidHom c' K
    rw [h1]
    rcases h.twins c' (mem_centralizer_of_map e hc) with h2 | h2
    · left
      rw [h2]
    · right
      intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := exists_of_mem_map_equiv e hx
      obtain ⟨b, hb, rfl⟩ := exists_of_mem_map_equiv e hy
      rw [← map_mul, ← map_mul, h2 a ha b hb]
  · intro c hc
    obtain ⟨c', rfl⟩ := e.surjective c
    have h1 : conjSub (e (c' * c')) (K.map e.toMonoidHom) =
        (conjSub (c' * c') K).map e.toMonoidHom := conjSub_map e.toMonoidHom (c' * c') K
    rw [← map_mul, h1, h.sq c' (mem_centralizer_of_map e hc)]

end Transport

section Invariance

variable {S : Type} [Group S]

private theorem conj_apply_map (β x : MulAut S) (a : S) : (β * x * β⁻¹) (β a) = β (x a) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]

theorem SFHyp.map {A B : Subgroup S} {r : S} {x : MulAut S} (h : SFHyp A B r x) (β : MulAut S) :
    SFHyp (A.map β.toMonoidHom) (B.map β.toMonoidHom) (β r) (β * x * β⁻¹) where
  quat := quatTwinDatum_map_mulEquiv β h.quat
  twin := by
    obtain ⟨q, hq, rfl⟩ := h.twin
    exact ⟨β q, map_mem_centralizer β hq, conjSub_map β.toMonoidHom q A⟩
  ne := fun h1 => h.ne (Subgroup.map_injective β.injective h1)
  sq := by
    have h1 : β * x * β⁻¹ * (β * x * β⁻¹) = β * (x * x) * β⁻¹ := by group
    rw [h1, h.sq]
    group
  fixA := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := exists_of_mem_map_equiv β hy
    rw [conj_apply_map, h.fixA a ha]
  onB := by
    obtain ⟨w, hw, hw4, hwB⟩ := h.onB
    refine ⟨β w, mem_map_equiv_of_mem β hw, by rw [MulEquiv.orderOf_eq, hw4], ?_⟩
    intro y hy
    obtain ⟨b, hb, rfl⟩ := exists_of_mem_map_equiv β hy
    rw [conj_apply_map, hwB b hb, map_mul, map_mul, map_inv]
  noNbr := by
    intro C hC hfix hne hle
    obtain ⟨g, rfl⟩ := hC
    obtain ⟨g', rfl⟩ := β.surjective g
    have hCmap : conjSub (β g') (A.map β.toMonoidHom) = (conjSub g' A).map β.toMonoidHom :=
      conjSub_map β.toMonoidHom g' A
    beta_reduce at hfix hne hle
    rw [hCmap] at hfix hne hle
    refine h.noNbr (conjSub g' A) ⟨g', rfl⟩ ?_ ?_ ?_
    · intro c hc
      have h1 := hfix (β c) (mem_map_equiv_of_mem β hc)
      rw [conj_apply_map] at h1
      exact β.injective h1
    · intro h1
      exact hne (by rw [h1])
    · intro c hc
      exact mem_normalizer_of_map β (hle (mem_map_equiv_of_mem β hc))

theorem sigmaFixOm3_of_forall_false
    (h : ∀ (A B : Subgroup S) (r : S) (x : MulAut S), SFHyp A B r x → False) : SigmaFixOm3 S :=
  fun A B r x hA hB hne hx2 hxA hxB hnb =>
    (h A B r x ⟨hA, hB, hne, hx2, hxA, hxB, hnb⟩).elim

end Invariance

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3
