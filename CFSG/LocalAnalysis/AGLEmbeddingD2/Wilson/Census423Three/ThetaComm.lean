module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem fixes_of_mem_theta (hZ : Subgroup.center X = ⊥) {Y : Subgroup (MulAut X)}
    {b₀ : X} {b : Y} (hb : (b : MulAut X) = MulAut.conj b₀) {q : Y}
    (hq : q ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y))) :
    (q : MulAut X) b₀ = b₀ := by
  have hinj := conj_injective_of_center hZ
  have hqC : q ∈ Subgroup.centralizer ({b} : Set Y) := inSubgroup_theta_le _ hq
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp hqC
  have h2 : (q : MulAut X) * (b : MulAut X) = (b : MulAut X) * (q : MulAut X) :=
    congrArg Subtype.val h1
  rw [hb] at h2
  have h3 : MulAut.conj ((q : MulAut X) b₀) = MulAut.conj b₀ := by
    rw [← mulAut_mul_conj_mul_inv, h2, mul_inv_cancel_right]
  exact hinj h3

theorem mem_theta_of_mem_theta (hZ : Subgroup.center X = ⊥) {Y : Subgroup (MulAut X)}
    (hY : (MulAut.conj : X →* MulAut X).range ≤ Y) {b₀ : X} {b : Y}
    (hb : (b : MulAut X) = MulAut.conj b₀) {q : Y}
    (hq : q ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y)))
    {c : X} (hc : c ∈ Subgroup.centralizer ({b₀} : Set X)) :
    (q : MulAut X) c * c⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b₀} : Set X)) := by
  have hinj := conj_injective_of_center hZ
  set C := Subgroup.centralizer ({b} : Set Y) with hC
  set Q := inSubgroup (aschbacherSolvableCore 3) C with hQ
  have hγ : ∀ x ∈ Subgroup.centralizer ({b₀} : Set X),
      (⟨MulAut.conj x, hY ⟨x, rfl⟩⟩ : Y) ∈ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change MulAut.conj x * (b : MulAut X) = (b : MulAut X) * MulAut.conj x
    rw [hb, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hx]
  set W : Subgroup X := ((Q.map Y.subtype).comap (MulAut.conj : X →* MulAut X)) ⊓
    Subgroup.centralizer ({b₀} : Set X) with hW
  set C₀ := Subgroup.centralizer ({b₀} : Set X) with hC₀
  have hWC : W ≤ C₀ := inf_le_right
  set N := W.subgroupOf C₀ with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hn1, hn2⟩ := hn
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk, hkn⟩ := hn1
      have hgC := hγ g g.2
      refine ⟨⟨MulAut.conj (g : X), hY ⟨_, rfl⟩⟩ * k * (⟨MulAut.conj (g : X), hY ⟨_, rfl⟩⟩ : Y)⁻¹,
        conj_mem_inSubgroup_theta' hgC hk, ?_⟩
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
        rw [show ((k : MulAut X)) = MulAut.conj ((n : C₀) : X) from hkn]
        simp only [map_mul, map_inv]
    · exact (g * n * g⁻¹).2
  have hf : ∀ x y : N, (MulAut.conj ((x : C₀) : X)) = MulAut.conj ((y : C₀) : X) → x = y := by
    intro x y h1
    exact Subtype.ext (Subtype.ext (hinj h1))
  have hNs : Group.IsSolvable N := by
    have hQs : Group.IsSolvable (Q.map Y.subtype) := by
      have := isSolvable_inSubgroup_theta C
      exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective Y.subtype Q)
    let f : N →* (Q.map Y.subtype) :=
      { toFun := fun n => ⟨MulAut.conj ((n : C₀) : X), (Subgroup.mem_subgroupOf.mp n.2).1⟩
        map_one' := by ext; simp
        map_mul' := fun x y => by ext; simp }
    have hfi : Function.Injective f := by
      intro x y hxy
      exact hf x y (congrArg Subtype.val hxy)
    exact Group.isSolvable_of_isSolvable_injective hfi
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    apply not_three_dvd_card_inSubgroup_theta C
    have hcard : Nat.card N ∣ Nat.card (Q.map Y.subtype) := by
      let f : N →* (Q.map Y.subtype) :=
        { toFun := fun n => ⟨MulAut.conj ((n : C₀) : X), (Subgroup.mem_subgroupOf.mp n.2).1⟩
          map_one' := by ext; simp
          map_mul' := fun x y => by ext; simp }
      have hfi : Function.Injective f := by
        intro x y hxy
        exact hf x y (congrArg Subtype.val hxy)
      exact Subgroup.card_dvd_of_injective f hfi
    rw [Subgroup.card_map_of_injective Y.subtype_injective] at hcard
    exact h3.trans hcard
  have hle := (solvable_prime_complement_core_characterization (H := C₀)
    Nat.prime_three).2.2.2.1 N hNn hNs hN3
  have hqb₀ : (q : MulAut X) b₀ = b₀ := fixes_of_mem_theta hZ hb hq
  set w := (q : MulAut X) c * c⁻¹ with hw
  have hwW : w ∈ W := by
    refine ⟨?_, ?_⟩
    · set γ : Y := ⟨MulAut.conj c, hY ⟨c, rfl⟩⟩ with hγdef
      have hγC : γ ∈ C := hγ c hc
      refine ⟨q * (γ * q⁻¹ * γ⁻¹), mul_mem hq (conj_mem_inSubgroup_theta' hγC (inv_mem hq)), ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      change (q : MulAut X) * (MulAut.conj c * (q : MulAut X)⁻¹ * (MulAut.conj c)⁻¹) =
        MulAut.conj w
      rw [hw, map_mul, map_inv, ← mulAut_mul_conj_mul_inv]
      group
    · rw [Subgroup.mem_centralizer_singleton_iff] at hc
      show w ∈ Subgroup.centralizer ({b₀} : Set X)
      rw [Subgroup.mem_centralizer_singleton_iff, hw]
      have hqc : (q : MulAut X) (c * b₀) = (q : MulAut X) (b₀ * c) := by rw [hc]
      rw [map_mul, map_mul, hqb₀] at hqc
      have hc' : c⁻¹ * b₀ = b₀ * c⁻¹ := by
        calc c⁻¹ * b₀ = c⁻¹ * (b₀ * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * b₀) * c⁻¹ := by rw [hc]
          _ = b₀ * c⁻¹ := by group
      calc (q : MulAut X) c * c⁻¹ * b₀ = (q : MulAut X) c * (c⁻¹ * b₀) := by rw [mul_assoc]
        _ = (q : MulAut X) c * (b₀ * c⁻¹) := by rw [hc']
        _ = ((q : MulAut X) c * b₀) * c⁻¹ := by rw [mul_assoc]
        _ = (b₀ * (q : MulAut X) c) * c⁻¹ := by rw [hqc]
        _ = b₀ * ((q : MulAut X) c * c⁻¹) := by rw [mul_assoc]
  have hwN : (⟨w, hWC hwW⟩ : C₀) ∈ N := Subgroup.mem_subgroupOf.mpr hwW
  exact ⟨⟨w, hWC hwW⟩, hle hwN, rfl⟩

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
