module

public import CFSG.Milestones.CLS_connectivity_MacWilliams_four_generator
public import CFSG.ClassicalInvolution.Basic

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

section MacWilliams

variable {F : Type} [Group F]

private theorem isElemAbelian_map_subtype {S : Subgroup F} {E' : Subgroup S} (h : IsElemAbelian 2 E') :
    IsElemAbelian 2 (E'.map S.subtype) := by
  obtain ⟨hcomm, hexp⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    have hab : (⟨a', ha'⟩ : E') * ⟨b', hb'⟩ = ⟨b', hb'⟩ * ⟨a', ha'⟩ :=
      hcomm.is_comm.comm _ _
    have h1 : a' * b' = b' * a' := congrArg Subtype.val hab
    apply Subtype.ext
    show (a : F) * (b : F) = (b : F) * (a : F)
    rw [← ha, ← hb]
    exact congrArg Subtype.val h1
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : x' ^ 2 = 1 := hexp x' hx'
    simpa using congrArg Subtype.val h1

theorem fourGenerated_of_sylow [Finite F] (S : Sylow 2 F)
    (h : ∀ P : Subgroup F, P ≤ (S : Subgroup F) →
      ∃ s : Finset F, s.card ≤ 4 ∧ Subgroup.closure (s : Set F) = P) :
    ∀ P : Subgroup F, IsPGroup 2 P →
      ∃ s : Finset F, s.card ≤ 4 ∧ Subgroup.closure (s : Set F) = P := by
  classical
  intro P hP
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq F S T
  have hT : (T : Subgroup F) = (S : Subgroup F).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hP'S : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup F) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyT : y ∈ (S : Subgroup F).map (MulAut.conj g).toMonoidHom := hT ▸ hPT hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hyT
    have e : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom s) = s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hs
  obtain ⟨X, hX4, hXcl⟩ := h _ hP'S
  refine ⟨X.image (fun x => g * x * g⁻¹), Finset.card_image_le.trans hX4, ?_⟩
  have hcoe : ((X.image (fun x => g * x * g⁻¹) : Finset F) : Set F) =
      (MulAut.conj g).toMonoidHom '' (X : Set F) := by
    rw [Finset.coe_image]
    rfl
  rw [hcoe, ← MonoidHom.map_closure, hXcl, Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [e]
    exact hy
  · intro hx
    exact ⟨x, hx, by group⟩

theorem exists_normal_elemAbelian_eight_of_not_fourGenerated [Finite F]
    (h : ¬ ∀ P : Subgroup F, IsPGroup 2 P →
      ∃ s : Finset F, s.card ≤ 4 ∧ Subgroup.closure (s : Set F) = P) (S : Sylow 2 F) :
    ∃ E : Subgroup F, E ≤ (S : Subgroup F) ∧ (E.subgroupOf (S : Subgroup F)).Normal ∧
      IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  classical
  by_contra hne
  apply h
  have hE : ∀ E' : Subgroup (S : Subgroup F), E'.Normal → IsElemAbelian 2 E' →
      Nat.card E' ≠ 8 := by
    intro E' hN hEA hc
    apply hne
    refine ⟨E'.map (S : Subgroup F).subtype, Subgroup.map_subtype_le E', ?_,
      isElemAbelian_map_subtype hEA, ?_⟩
    · have : (E'.map (S : Subgroup F).subtype).subgroupOf (S : Subgroup F) = E' :=
        Subgroup.comap_map_eq_self_of_injective (S : Subgroup F).subtype_injective E'
      rw [this]
      exact hN
    · rw [Subgroup.card_map_of_injective (S : Subgroup F).subtype_injective]
      exact hc
  have hall := CFSG.Milestones.cls_connectivity_macwilliams_four_generator
    (S : Subgroup F) S.isPGroup' hE
  refine fourGenerated_of_sylow S fun P hPS => ?_
  obtain ⟨X, hX4, hXcl⟩ := hall (P.subgroupOf (S : Subgroup F))
  refine ⟨X.image (S : Subgroup F).subtype, Finset.card_image_le.trans hX4, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hXcl]
  exact Subgroup.map_subgroupOf_eq_of_le hPS

end MacWilliams

section UniqueInvolution

variable {G : Type*} [Group G]

private theorem conj_mem_of_normal_subgroupOf {S E : Subgroup G} (hE : (E.subgroupOf S).Normal)
    {q e : G} (hq : q ∈ S) (he : e ∈ E) (heS : e ∈ S) : q * e * q⁻¹ ∈ E := by
  have h := hE.conj_mem ⟨e, heS⟩ (Subgroup.mem_subgroupOf.mpr he) ⟨q, hq⟩
  exact Subgroup.mem_subgroupOf.mp h

theorem card_lt_of_injective_of_forall_ne {α β : Type*} [Finite β] (f : α → β)
    (hf : Function.Injective f) (b : β) (hb : ∀ a, f a ≠ b) : Nat.card α < Nat.card β := by
  classical
  have := Fintype.ofFinite β
  have : Finite α := Finite.of_injective f hf
  have := Fintype.ofFinite α
  let g : α → {x : β // x ≠ b} := fun a => ⟨f a, hb a⟩
  have hg : Function.Injective g := fun a a' h => hf (congrArg Subtype.val h)
  have h1 : Fintype.card α ≤ Fintype.card {x : β // x ≠ b} := Fintype.card_le_of_injective g hg
  have h2 : Fintype.card {x : β // x ≠ b} < Fintype.card β :=
    Fintype.card_subtype_lt (p := fun x : β => x ≠ b) (x := b) (by simp)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  omega

theorem commute_of_unique_involution_of_card_le [Finite G] {Q E : Subgroup G} {z : G}
    (hQ : IsPGroup 2 Q) (hu : ∀ x ∈ Q, orderOf x = 2 → x = z)
    (hN : ∀ q ∈ Q, ∀ e ∈ E, q * e * q⁻¹ ∈ E) (hcard : Nat.card E ≤ Nat.card Q) :
    ∀ e ∈ E, z * e = e * z := by
  by_contra hne
  push Not at hne
  obtain ⟨e, heE, hze⟩ := hne
  have he1 : e ≠ 1 := by
    rintro rfl
    exact hze (by simp)
  have hstab : ∀ q ∈ Q, q * e = e * q → q = 1 := by
    intro q hq hqe
    by_contra hq1
    obtain ⟨n, hn⟩ := exists_pow_orderOf_eq_two hQ (x := (⟨q, hq⟩ : Q))
      (fun h => hq1 (congrArg Subtype.val h))
    have hn' : orderOf (q ^ n) = 2 := by
      have h := Subgroup.orderOf_coe (⟨q, hq⟩ ^ n : Q)
      rw [Subgroup.coe_pow, hn] at h
      simpa using h
    have hqn : q ^ n = z := hu (q ^ n) (Q.pow_mem hq n) hn'
    have hc : q ^ n * e = e * q ^ n := (Commute.pow_left hqe n)
    rw [hqn] at hc
    exact hze hc
  let f : Q → E := fun q => ⟨(q : G) * e * (q : G)⁻¹, hN q q.2 e heE⟩
  have hf : Function.Injective f := by
    intro q q' h
    have h1 : (q : G) * e * (q : G)⁻¹ = (q' : G) * e * (q' : G)⁻¹ := congrArg Subtype.val h
    have h2 : ((q' : G)⁻¹ * q) * e = e * ((q' : G)⁻¹ * q) := by
      calc ((q' : G)⁻¹ * q) * e = (q' : G)⁻¹ * ((q : G) * e * (q : G)⁻¹) * q := by group
        _ = (q' : G)⁻¹ * ((q' : G) * e * (q' : G)⁻¹) * q := by rw [h1]
        _ = e * ((q' : G)⁻¹ * q) := by group
    have h3 : (q' : G)⁻¹ * q = 1 := hstab _ (Q.mul_mem (Q.inv_mem q'.2) q.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3).symm
  have hne1 : ∀ q : Q, f q ≠ 1 := by
    intro q h
    have h1 : (q : G) * e * (q : G)⁻¹ = 1 := congrArg Subtype.val h
    apply he1
    have : (q : G) * e = q := mul_inv_eq_one.mp h1
    simpa using this
  have hlt := card_lt_of_injective_of_forall_ne f hf 1 hne1
  omega

theorem le_centralizer_of_normal_of_unique_involution [Finite G] {Q S E : Subgroup G} {z : G}
    (hQS : Q ≤ S) (hES : E ≤ S) (hE : (E.subgroupOf S).Normal) (hQ : IsPGroup 2 Q)
    (hu : ∀ x ∈ Q, orderOf x = 2 → x = z) (hcard : Nat.card E ≤ Nat.card Q) :
    E ≤ Subgroup.centralizer ({z} : Set G) := by
  intro e he
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (commute_of_unique_involution_of_card_le hQ hu
    (fun q hq e' he' => conj_mem_of_normal_subgroupOf hE (hQS hq) he' (hES he')) hcard e he).symm

theorem le_centralizer_of_normal_of_quaternion_sylow [Finite G] {J S E : Subgroup G} {z : G}
    (hzJ : z ∈ J) (hz : orderOf z = 2) (hcent : J ≤ Subgroup.centralizer ({z} : Set G))
    (T : Sylow 2 J)
    (hT : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hTS : (T : Subgroup J).map J.subtype ≤ S) (hES : E ≤ S) (hE : (E.subgroupOf S).Normal)
    (hcard : Nat.card E ≤ Nat.card (T : Subgroup J)) :
    E ≤ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨hU, -⟩ := unique_involution_of_quaternion_sylow hzJ hz hcent T hT
  refine le_centralizer_of_normal_of_unique_involution hTS hES hE (T.isPGroup'.map J.subtype)
    (fun x hx hx2 => ?_) (by rwa [Subgroup.card_map_of_injective J.subtype_injective])
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact hU y.1 y.2 (by simpa using hx2)

end UniqueInvolution

end CFSG.ClassicalInvolution
