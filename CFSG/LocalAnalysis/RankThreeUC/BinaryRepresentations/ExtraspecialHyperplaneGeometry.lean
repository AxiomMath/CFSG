module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.ExtraspecialHyperplaneVocabulary
public import CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace BinaryRepresentations

namespace ExtraspecialHyperplaneGeometry

open scoped commutatorElement

variable {G : Type} [Group G]

private theorem mem_centerIn_iff {H : Subgroup G} {z : G} :
    z ∈ centerIn H ↔ z ∈ H ∧ ∀ h ∈ H, h * z = z * h := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun h hh => ?_⟩
    have := Subgroup.mem_center_iff.mp hc ⟨h, hh⟩
    simpa using congrArg Subtype.val this
  · rintro ⟨hz, hc⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (by simpa using (hc g g.2)), rfl⟩

private theorem comm_mem_centerIn {p : ℕ} {H : Subgroup G} (hH : CFSG.IsExtraspecialPGroup p H)
    {g w : G} (hg : g ∈ H) (hw : w ∈ H) : g * w * g⁻¹ * w⁻¹ ∈ centerIn H := by
  have h1 : ⁅(⟨g, hg⟩ : H), (⟨w, hw⟩ : H)⁆ ∈ commutator H :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [hH.2.1] at h1
  unfold centerIn
  refine Subgroup.mem_map.mpr ⟨⁅(⟨g, hg⟩ : H), (⟨w, hw⟩ : H)⁆, h1, ?_⟩
  simp [commutatorElement_def]

theorem k_elementary [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G)
    (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    CFSG.Open.IsElemAbelian p (X ⊔ centerIn H) := by
  haveI := Fact.mk hp
  have hXc : IsMulCommutative X := by
    have := isCyclic_of_prime_card (α := X) hXp
    infer_instance
  have hcomm : (((X : Set G) ∪ (centerIn H : Set G))).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · have := (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : X) ⟨b, hb⟩)
      exact congrArg Subtype.val this
    · exact (mem_centerIn_iff.mp hb).2 a (hXH ha)
    · exact ((mem_centerIn_iff.mp ha).2 b (hXH hb)).symm
    · exact ((mem_centerIn_iff.mp ha).2 b (mem_centerIn_iff.mp hb).1).symm
  have hle : X ⊔ centerIn H ≤ H :=
    sup_le hXH (fun z hz => (mem_centerIn_iff.mp hz).1)
  refine ⟨?_, ?_⟩
  · rw [Subgroup.sup_eq_closure]
    exact Subgroup.isMulCommutative_closure hcomm
  · intro x hx
    have hxH : x ∈ H := hle hx
    have := Monoid.pow_exponent_eq_one (⟨x, hxH⟩ : H)
    rw [hexp] at this
    simpa using congrArg Subtype.val this

theorem conjClass_transport [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G)
    (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H)
    {Y : Subgroup G} (hY : Y ∈ conjClass H X) :
    ∃ h ∈ H, Y = X.map (MulAut.conj h).toMonoidHom ∧ Y ≤ X ⊔ centerIn H ∧
      Y ⊔ centerIn H = X ⊔ centerIn H := by
  obtain ⟨h, hh, rfl⟩ := hY
  have hsub : X.map (MulAut.conj h).toMonoidHom ≤ X ⊔ centerIn H := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hc := comm_mem_centerIn hH (inv_mem (hXH hx)) hh
    have e : (MulAut.conj h).toMonoidHom x = x * (x⁻¹ * h * x⁻¹⁻¹ * h⁻¹) := by
      simp [MulAut.conj_apply]; group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hc)
  refine ⟨h, hh, rfl, hsub, le_antisymm (sup_le hsub le_sup_right) (sup_le ?_ le_sup_right)⟩
  intro x hx
  have hc := comm_mem_centerIn hH hh (inv_mem (hXH hx))
  have e : x = (MulAut.conj h).toMonoidHom x * (h * x⁻¹ * h⁻¹ * (x⁻¹)⁻¹) := by
    simp [MulAut.conj_apply]; group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)) (Subgroup.mem_sup_right hc)

theorem center_notMem_conjClass [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G)
    (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    centerIn H ∉ conjClass H X := by
  intro hmem
  obtain ⟨-, -, hY, -, hsup⟩ :=
    conjClass_transport hp hp2 H hH hexp X hXH hXp hXZ hmem
  rw [sup_idem] at hsup
  have hle : X ≤ centerIn H := by
    have : X ≤ X ⊔ centerIn H := le_sup_left
    rw [← hsup] at this
    exact this
  have hcardZ : Nat.card (centerIn H) = p := by
    unfold centerIn
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hH.2.2.2
  exact hXZ (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardZ, hXp]))

private theorem card_center {p : ℕ} {H : Subgroup G} (hH : CFSG.IsExtraspecialPGroup p H) :
    Nat.card (centerIn H) = p := by
  unfold centerIn
  rw [Subgroup.card_map_of_injective H.subtype_injective]
  exact hH.2.2.2

private theorem inf_center_eq_bot {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hH : CFSG.IsExtraspecialPGroup p H) {X : Subgroup G} (hXp : Nat.card X = p)
    (hXZ : X ≠ centerIn H) [Finite G] : X ⊓ centerIn H = ⊥ := by
  have hZ := card_center hH
  have hd : Nat.card ↥(X ⊓ centerIn H) ∣ p := hXp ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hd with h1 | hp'
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have h2 : X ⊓ centerIn H = X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp', hXp])
    have hXle : X ≤ centerIn H := h2 ▸ inf_le_right
    exact hXZ (Subgroup.eq_of_le_of_card_ge hXle (by rw [hZ, hXp]))

private theorem exists_conj_ne [Finite G] {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hH : CFSG.IsExtraspecialPGroup p H) {X : Subgroup G} (hXH : X ≤ H)
    (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    ∃ h ∈ H, X.map (MulAut.conj h).toMonoidHom ≠ X := by
  by_contra hcon
  push Not at hcon
  have hbot := inf_center_eq_bot hp hH hXp hXZ
  have hle : X ≤ centerIn H := by
    intro x hx
    refine mem_centerIn_iff.mpr ⟨hXH hx, fun h hh => ?_⟩
    have hc := comm_mem_centerIn hH hh (hXH hx)
    have hmem : h * x * h⁻¹ ∈ X := by
      have : (MulAut.conj h).toMonoidHom x ∈ X.map (MulAut.conj h).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hcon h hh] at this
      simpa [MulAut.conj_apply] using this
    have hcX : h * x * h⁻¹ * x⁻¹ ∈ X := mul_mem hmem (inv_mem hx)
    have h1 : h * x * h⁻¹ * x⁻¹ ∈ X ⊓ centerIn H := ⟨hcX, hc⟩
    rw [hbot] at h1
    have h2 : h * x * h⁻¹ * x⁻¹ = 1 := h1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)
  exact hXZ (Subgroup.eq_of_le_of_card_ge hle (by rw [card_center hH, hXp]))

theorem k_card [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G)
    (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    Nat.card ↥(X ⊔ centerIn H) = p ^ 2 := by
  have hbot := inf_center_eq_bot hp hH hXp hXZ
  have hZ := card_center hH
  have hc : ∀ x ∈ X, ∀ z ∈ centerIn H, x * z = z * x :=
    fun x hx z hz => (mem_centerIn_iff.mp hz).2 x (hXH hx)
  let S : Subgroup G :=
    { carrier := {g | ∃ x ∈ X, ∃ z ∈ centerIn H, g = x * z}
      mul_mem' := by
        rintro _ _ ⟨x, hx, z, hz, rfl⟩ ⟨x', hx', z', hz', rfl⟩
        refine ⟨x * x', mul_mem hx hx', z * z', mul_mem hz hz', ?_⟩
        have := hc x' hx' z hz
        calc x * z * (x' * z') = x * (z * x') * z' := by group
          _ = x * (x' * z) * z' := by rw [← this]
          _ = _ := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, z, hz, rfl⟩
        refine ⟨x⁻¹, inv_mem hx, z⁻¹, inv_mem hz, ?_⟩
        have := hc x hx z hz
        rw [this, mul_inv_rev] }
  have hKS : X ⊔ centerIn H = S := by
    apply le_antisymm
    · refine sup_le (fun x hx => ⟨x, hx, 1, one_mem _, by simp⟩)
        (fun z hz => ⟨1, one_mem _, z, hz, by simp⟩)
    · rintro _ ⟨x, hx, z, hz, rfl⟩
      exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hz)
  let f : X × centerIn H → ↥(X ⊔ centerIn H) := fun q =>
    ⟨q.1 * q.2, mul_mem (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨z, hz⟩⟩ ⟨⟨x', hx'⟩, ⟨z', hz'⟩⟩ h
      have h1 : x * z = x' * z' := congrArg Subtype.val h
      have h2 : x'⁻¹ * x = z' * z⁻¹ := by
        calc x'⁻¹ * x = x'⁻¹ * (x * z) * z⁻¹ := by group
          _ = x'⁻¹ * (x' * z') * z⁻¹ := by rw [h1]
          _ = z' * z⁻¹ := by group
      have h3 : x'⁻¹ * x ∈ X ⊓ centerIn H :=
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hx') hx,
          by rw [h2]; exact Subgroup.mul_mem _ hz' (Subgroup.inv_mem _ hz)⟩
      rw [hbot] at h3
      have h4 : x'⁻¹ * x = 1 := h3
      have h5 : x = x' := inv_mul_eq_one.mp h4 |>.symm
      subst h5
      have h6 : z' * z⁻¹ = 1 := h2 ▸ h4
      have h7 : z = z' := (mul_inv_eq_one.mp h6).symm
      subst h7
      rfl
    · rintro ⟨k, hk⟩
      rw [hKS] at hk
      obtain ⟨x, hx, z, hz, rfl⟩ := hk
      exact ⟨(⟨x, hx⟩, ⟨z, hz⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, hXp, hZ, sq]

open scoped Pointwise in
private noncomputable def conjAct (H : Subgroup G) : MulAction H (Subgroup G) :=
  MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp H.subtype)

open scoped Pointwise in
private theorem orbit_eq (H X : Subgroup G) :
    letI := conjAct H
    MulAction.orbit H X = conjClass H X := by
  letI := conjAct H
  ext Y
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h, h.2, ?_⟩
    show (MulAut.conj (h:G)) • X = _
    rw [Subgroup.pointwise_smul_def]; rfl
  · rintro ⟨h, hh, rfl⟩
    refine ⟨⟨h, hh⟩, ?_⟩
    show (MulAut.conj h) • X = _
    rw [Subgroup.pointwise_smul_def]; rfl

private theorem sub_hyperplanes [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G)
    (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    {centerIn H} ∪ conjClass H X ⊆ hyperplanes p (X ⊔ centerIn H) := by
  have hK := k_card hp hp2 H hH hexp X hXH hXp hXZ
  have key : ∀ Y : Subgroup G, Y ≤ X ⊔ centerIn H → Nat.card Y = p →
      Y ∈ hyperplanes p (X ⊔ centerIn H) := by
    intro Y hY hYp
    refine ⟨hY, ?_⟩
    have := Subgroup.relIndex_mul_card (H := Y) (K := X ⊔ centerIn H)
    rw [inf_of_le_left hY, hYp, hK] at this
    exact Nat.eq_of_mul_eq_mul_right hp.pos (this.trans (sq p))
  rintro Y (hY | hY)
  · rw [Set.mem_singleton_iff] at hY
    subst hY
    exact key _ le_sup_right (card_center hH)
  · obtain ⟨h, hh, hY1, hY2, -⟩ := conjClass_transport hp hp2 H hH hexp X hXH hXp hXZ hY
    refine key Y hY2 ?_
    rw [hY1, Subgroup.card_map_of_injective (MulAut.conj h).injective, hXp]

theorem conjClass_card [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G)
    (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    (conjClass H X).ncard = p := by
  haveI := Fact.mk hp
  have hsub := sub_hyperplanes hp hp2 H hH hexp X hXH hXp hXZ
  have hcard : Nat.card (hyperplanes p (X ⊔ centerIn H)) = p + 1 := by
    rw [CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts.card_hyperplanes (k_elementary hp hp2 H hH hexp X hXH hXp hXZ) (n := 2) (by norm_num)
      (k_card hp hp2 H hH hexp X hXH hXp hXZ)]
    simp [Finset.sum_range_succ, add_comm]
  have hfin : (conjClass H X).Finite := Set.toFinite _
  have hle : (conjClass H X).ncard ≤ p := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_union_eq (Set.disjoint_singleton_left.mpr
      (center_notMem_conjClass hp hp2 H hH hexp X hXH hXp hXZ)) (Set.toFinite _) hfin,
      Set.ncard_singleton] at h1
    rw [Nat.card_coe_set_eq] at hcard
    rw [hcard] at h1
    omega
  obtain ⟨n, hn⟩ : ∃ n, Nat.card (conjClass H X) = p ^ n := by
    letI := conjAct H
    haveI : Finite (MulAction.orbit H X) := Set.toFinite _
    have := hH.1.card_orbit (α := Subgroup G) X
    rwa [orbit_eq] at this
  rw [Nat.card_coe_set_eq] at hn
  obtain ⟨h, hh, hne⟩ := exists_conj_ne hp hH hXH hXp hXZ
  have hp1 : (conjClass H X).ncard ≠ 1 := by
    intro h1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    have h0 : X ∈ conjClass H X := ⟨1, one_mem _, by ext; simp⟩
    have h2 : X.map (MulAut.conj h).toMonoidHom ∈ conjClass H X := ⟨h, hh, rfl⟩
    rw [ha] at h0 h2
    exact hne ((Set.mem_singleton_iff.mp h2).trans (Set.mem_singleton_iff.mp h0).symm)
  have hp2' : p < p ^ 2 := by nlinarith [hp.two_le]
  rcases n with _ | _ | n
  · exact absurd (by simpa using hn) hp1
  · simpa using hn
  · exfalso
    have : p ^ 2 ≤ p ^ (n + 1 + 1) := Nat.pow_le_pow_right hp.pos (by omega)
    omega

theorem hyperplanes_eq [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G)
    (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    hyperplanes p (X ⊔ centerIn H) = {centerIn H} ∪ conjClass H X := by
  haveI := Fact.mk hp
  have hsub := sub_hyperplanes hp hp2 H hH hexp X hXH hXp hXZ
  have hcard : Nat.card (hyperplanes p (X ⊔ centerIn H)) = p + 1 := by
    rw [CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts.card_hyperplanes (k_elementary hp hp2 H hH hexp X hXH hXp hXZ) (n := 2) (by norm_num)
      (k_card hp hp2 H hH hexp X hXH hXp hXZ)]
    simp [Finset.sum_range_succ, add_comm]
  have hcc := conjClass_card hp hp2 H hH hexp X hXH hXp hXZ
  symm
  apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
  rw [Set.ncard_union_eq (Set.disjoint_singleton_left.mpr
      (center_notMem_conjClass hp hp2 H hH hexp X hXH hXp hXZ)) (Set.toFinite _) (Set.toFinite _),
      Set.ncard_singleton, hcc]
  rw [Nat.card_coe_set_eq] at hcard
  omega

end ExtraspecialHyperplaneGeometry

end BinaryRepresentations

end CFSG.LocalAnalysis.RankThreeUC
