module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Basic
public import CFSG.Dihedral.DisconnectedInvolutionGraph.NormalSylowIntersection

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isPGroup_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    IsPGroup 2 ↥(closure ({a, b} : Set G)) := by
  have hEel := isElemAbelian_closure_pair ha hb hab
  exact fun x => ⟨1, by apply Subtype.ext; simpa using hEel.2 x x.2⟩

theorem isPGroup_zpowers_of_mem {T : Subgroup G} (hT : IsPGroup 2 ↥T) {a : G} (ha : a ∈ T) :
    IsPGroup 2 ↥(zpowers a) :=
  hT.to_le (zpowers_le.mpr ha)

theorem exists_isSylow2In_of_le [Finite G] {H A : Subgroup G} (hA : IsPGroup 2 ↥A) (hAH : A ≤ H) :
    ∃ S : Subgroup G, IsSylow2In S H ∧ A ≤ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA' : IsPGroup 2 ↥(A.subgroupOf H) := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm
  obtain ⟨Q₀, hQ₀⟩ := hA'.exists_le_sylow
  refine ⟨(Q₀ : Subgroup H).map H.subtype, ⟨map_subtype_le _, Q₀.isPGroup'.map _, ?_⟩, ?_⟩
  · have e : ((Q₀ : Subgroup H).map H.subtype).subgroupOf H = (Q₀ : Subgroup H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [Subgroup.relIndex, e]
    exact Q₀.not_dvd_index
  · intro a ha
    exact ⟨⟨a, hAH ha⟩, hQ₀ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩

theorem exists_conj_mem_of_isSylow2In [Finite G] {H S₀ : Subgroup G} (hS₀ : IsSylow2In S₀ H) {u : G}
    (hu : u ∈ H) (hu2 : ∃ n : ℕ, u ^ (2 ^ n) = 1) : ∃ i ∈ H, i⁻¹ * u * i ∈ S₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSH, hSp, hSi⟩ := hS₀
  have hSp' : IsPGroup 2 ↥(S₀.subgroupOf H) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  have hidx : ¬ 2 ∣ (S₀.subgroupOf H).index := hSi
  let P₀ : Sylow 2 ↥H := hSp'.toSylow hidx
  let u' : ↥H := ⟨u, hu⟩
  obtain ⟨n, hn⟩ := hu2
  have hu'p : IsPGroup 2 ↥(zpowers u') :=
    isPGroup_zpowers_of_pow_eq_one (G := ↥H) (a := u') (n := n) (Subtype.ext hn)
  obtain ⟨Q, hQ⟩ := hu'p.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (↥H) P₀ Q
  have hu'Q : u' ∈ (Q : Subgroup ↥H) := hQ (mem_zpowers u')
  refine ⟨(h : G), h.2, ?_⟩
  have hmem : h⁻¹ * u' * h ∈ (P₀ : Subgroup ↥H) := by
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hu'Q
    have e : (MulAut.conj h)⁻¹ • u' = h⁻¹ * u' * h := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
      simp
    rw [e] at hu'Q
    exact hu'Q
  have : h⁻¹ * u' * h ∈ S₀.subgroupOf H := by
    simpa [P₀, IsPGroup.toSylow_coe] using hmem
  exact this

theorem isSylow2In_inf_normal [Finite G] {H P N : Subgroup G} (hP : IsSylow2In P H) (hNH : N ≤ H)
    (hN : H ≤ normalizer (N : Set G)) : IsSylow2In (P ⊓ N) N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPH, hPp, hPi⟩ := hP
  have hP' : IsPGroup 2 ↥(P.subgroupOf H) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hidx : ¬ 2 ∣ (P.subgroupOf H).index := hPi
  let S : Sylow 2 ↥H := hP'.toSylow hidx
  let N' : Subgroup ↥H := N.subgroupOf H
  have hN' : N'.Normal := ⟨fun n hn g => by
    have h1 : (n : G) ∈ N := hn
    have h2 : (g : G) * n * (g : G)⁻¹ ∈ N := (mem_normalizer_iff.mp (hN g.2) n).mp h1
    exact h2⟩
  obtain ⟨R, hR⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection
    2 N' S
  have hRidx : ¬ 2 ∣ (R : Subgroup ↥N').index := R.not_dvd_index
  rw [hR] at hRidx
  refine ⟨inf_le_right, hPp.to_le inf_le_left, ?_⟩
  have hcomap : ((P ⊓ N).subgroupOf N).comap (Subgroup.subgroupOfEquivOfLe hNH).toMonoidHom =
      (S : Subgroup ↥H).subgroupOf N' := by
    ext m
    have hmN : ((m : ↥H) : G) ∈ N := m.2
    simp [Subgroup.mem_subgroupOf, S, IsPGroup.toSylow_coe]
  have hidx2 : ((P ⊓ N).subgroupOf N).index = ((S : Subgroup ↥H).subgroupOf N').index := by
    rw [← hcomap]
    exact (Subgroup.index_comap_of_surjective _ (Subgroup.subgroupOfEquivOfLe hNH).surjective).symm
  rw [Subgroup.relIndex, hidx2]
  exact hRidx

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hBA : B ≤ normalizer (A : Set G)) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let W : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        exact ⟨a₁ * (b₁ * a₂ * b₁⁻¹),
          mul_mem ha₁ ((mem_normalizer_iff.mp (hBA hb₁) a₂).mp ha₂), b₁ * b₂, mul_mem hb₁ hb₂,
          by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨b⁻¹ * a⁻¹ * b, ?_, b⁻¹, inv_mem hb, by group⟩
        have := (mem_normalizer_iff.mp (hBA (inv_mem hb)) a⁻¹).mp (inv_mem ha)
        simpa using this }
  have hle : A ⊔ B ≤ W := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact hle hx

theorem eq_of_mem_center_of_card_two {Q : Type*} [Group Q] (h : Nat.card (center Q) = 2) {p q : Q}
    (hp : p ∈ center Q) (hq : q ∈ center Q) (hp1 : p ≠ 1) (hq1 : q ≠ 1) : p = q := by
  obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp h
  have h1 : (⟨p, hp⟩ : center Q) = c := hc ⟨p, hp⟩ (fun h => hp1 (congrArg Subtype.val h))
  have h2 : (⟨q, hq⟩ : center Q) = c := hc ⟨q, hq⟩ (fun h => hq1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem mem_conjugate_iff' {g z : G} {H : Subgroup G} : z ∈ conjugate H g ↔ g * z * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have e : g * ((MulAut.conj g⁻¹).toMonoidHom k) * g⁻¹ = k := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hk
  · intro h
    refine ⟨g * z * g⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem conjugate_ne_of_not_mem_normalizer {y : G} {L : Subgroup G} (hy : y ∉ normalizer (L : Set G)) :
    conjugate L y ≠ L := by
  intro h
  apply hy
  have h1 : y⁻¹ ∈ normalizer (L : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  simpa using h1

theorem exists_conj_of_involutions_of_odd {y o : G} (hodd : Odd (orderOf o))
    (hinv : y * o * y⁻¹ = o⁻¹) : ∃ k ∈ zpowers o, k⁻¹ * y * k = y * o := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨o ^ (m + 1), pow_mem (mem_zpowers o) _, ?_⟩
  have hk2 : (o ^ (m + 1)) * (o ^ (m + 1)) = o := by
    rw [← pow_add, show m + 1 + (m + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hyk : y * o ^ (m + 1) * y⁻¹ = (o ^ (m + 1))⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  have hyk' : y * o ^ (m + 1) = (o ^ (m + 1))⁻¹ * y := by
    calc y * o ^ (m + 1) = y * o ^ (m + 1) * y⁻¹ * y := by group
      _ = (o ^ (m + 1))⁻¹ * y := by rw [hyk]
  have hyo : y * o = o⁻¹ * y := by
    calc y * o = y * o * y⁻¹ * y := by group
      _ = o⁻¹ * y := by rw [hinv]
  calc (o ^ (m + 1))⁻¹ * y * o ^ (m + 1) = (o ^ (m + 1))⁻¹ * (y * o ^ (m + 1)) := by group
    _ = (o ^ (m + 1))⁻¹ * ((o ^ (m + 1))⁻¹ * y) := by rw [hyk']
    _ = ((o ^ (m + 1)) * (o ^ (m + 1)))⁻¹ * y := by group
    _ = o⁻¹ * y := by rw [hk2]
    _ = y * o := hyo.symm

theorem mem_normalizer_sup_conjugate {y : G} (hy : y * y = 1) (L : Subgroup G) :
    y ∈ normalizer ((L ⊔ conjugate L y : Subgroup G) : Set G) := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : L.map (MulAut.conj y).toMonoidHom = conjugate L y := by
    unfold conjugate
    rw [hyinv]
  have h2 : (conjugate L y).map (MulAut.conj y).toMonoidHom = L := by
    unfold conjugate
    rw [Subgroup.map_map]
    have : (MulAut.conj y).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom = MonoidHom.id G := by
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [this, Subgroup.map_id]
  have key : (L ⊔ conjugate L y).map (MulAut.conj y).toMonoidHom = L ⊔ conjugate L y := by
    rw [Subgroup.map_sup, h1, h2, sup_comm]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key

end CFSG.GH74.GLS.Stage1.Thm2.Recip
