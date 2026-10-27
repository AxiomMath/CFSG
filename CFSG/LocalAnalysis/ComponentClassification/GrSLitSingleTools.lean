module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single

public section

namespace CFSG.ComponentClassification.GrSLit.Single

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_sup {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite X] in
theorem mem_normalizer_inf {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hA, hB]

theorem odd_card_sup {A B : Subgroup X} (hA : Odd (Nat.card A)) (hB : Odd (Nat.card B))
    (hAB : A ≤ normalizer (B : Set X)) : Odd (Nat.card ↥(A ⊔ B)) :=
  Odd.of_dvd_nat (hA.mul hB) (Dvd.intro _ (GrS4.card_sup_mul_inf_eq_mul_of_normalizes hAB))

omit [Finite X] in
theorem exists_mul_of_mem_sup {A N : Subgroup X} (hAN : A ≤ normalizer (N : Set X)) {x : X}
    (hx : x ∈ A ⊔ N) : ∃ a ∈ A, ∃ n ∈ N, x = a * n := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A N hAN] at hx
  obtain ⟨a, ha, n, hn, rfl⟩ := hx
  exact ⟨a, ha, n, hn, rfl⟩

omit [Finite X] in
theorem commutatorElement_mul_mem_iff {N : Subgroup X} {y₁ y₂ n₁ n₂ : X}
    (hy₁ : y₁ ∈ normalizer (N : Set X)) (hy₂ : y₂ ∈ normalizer (N : Set X)) (hn₁ : n₁ ∈ N)
    (hn₂ : n₂ ∈ N) : ⁅y₁ * n₁, y₂ * n₂⁆ ∈ N ↔ ⁅y₁, y₂⁆ ∈ N := by
  have hu : y₂ * y₁ * y₂⁻¹ ∈ normalizer (N : Set X) := mul_mem (mul_mem hy₂ hy₁) (inv_mem hy₂)
  have hv : y₂ * y₁ ∈ normalizer (N : Set X) := mul_mem hy₂ hy₁
  have hA : (y₂ * y₁ * y₂⁻¹) * n₁ * (y₂ * y₁ * y₂⁻¹)⁻¹ ∈ N := (mem_normalizer_iff.mp hu n₁).mp hn₁
  have hB : (y₂ * y₁) * (n₂ * n₁⁻¹) * (y₂ * y₁)⁻¹ ∈ N :=
    (mem_normalizer_iff.mp hv _).mp (mul_mem hn₂ (inv_mem hn₁))
  have hC : y₂ * n₂⁻¹ * y₂⁻¹ ∈ N := (mem_normalizer_iff.mp hy₂ _).mp (inv_mem hn₂)
  have e : ⁅y₁ * n₁, y₂ * n₂⁆ = ⁅y₁, y₂⁆ * (((y₂ * y₁ * y₂⁻¹) * n₁ * (y₂ * y₁ * y₂⁻¹)⁻¹) *
      ((y₂ * y₁) * (n₂ * n₁⁻¹) * (y₂ * y₁)⁻¹) * (y₂ * n₂⁻¹ * y₂⁻¹)) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem_cancel_right (mul_mem (mul_mem hA hB) hC)

theorem eq_or_commutator_le_oddIn {L H P : Subgroup X} (hLH : L ≤ H)
    (hL : IsPComponent 2 (L.subgroupOf H)) (hPL : P ≤ L) (hLP : L ≤ normalizer (P : Set X))
    (hOP : oddIn L ≤ P) : P = L ∨ ⁅L, P⁆ ≤ oddIn L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hperf, hsimple, -⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L H hLH).mp hL
  set O : Subgroup ↥L := pPrimeCore 2 ↥L with hO
  set ψ : ↥L →* ↥L ⧸ O := QuotientGroup.mk' O with hψ
  set P' : Subgroup ↥L := P.subgroupOf L with hP'
  have hP'n : P'.Normal := (normal_subgroupOf_iff_le_normalizer hPL).mpr hLP
  have hOP' : O ≤ P' := fun x hx => hOP ⟨x, hx, rfl⟩
  have hNn : (P'.map ψ).Normal := hP'n.map ψ (QuotientGroup.mk'_surjective O)
  have hq : CFSG.Open.IsQuasisimple (↥L ⧸ O) := ⟨hperf.commutator_eq_top, hsimple⟩
  rcases Quasisimple.normal_le_center_or_eq_top hq (P'.map ψ) with hc | ht
  · right
    rw [commutator_le]
    intro l hl p hp
    have hpc : ψ ⟨p, hPL hp⟩ ∈ center (↥L ⧸ O) := hc ⟨⟨p, hPL hp⟩, hp, rfl⟩
    have h1 : ψ ⁅(⟨l, hl⟩ : ↥L), ⟨p, hPL hp⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mem_center_iff.mp hpc _
    have h2 : ⁅(⟨l, hl⟩ : ↥L), ⟨p, hPL hp⟩⁆ ∈ O := by
      rwa [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
    exact ⟨_, h2, rfl⟩
  · left
    have htop : P' = ⊤ := by
      have h1 := Subgroup.comap_map_eq ψ P'
      rw [ht, Subgroup.comap_top, hψ, QuotientGroup.ker_mk', sup_eq_left.mpr hOP'] at h1
      exact h1.symm
    refine le_antisymm hPL fun x hx => ?_
    have h2 : (⟨x, hx⟩ : ↥L) ∈ P' := htop ▸ mem_top _
    exact h2

theorem mem_coreActionKernel_of_comm {L H : Subgroup X} (hLH : L ≤ H)
    (hL : IsPComponent 2 (L.subgroupOf H)) {j : X} (hj : j ∈ normalizer (L : Set X))
    (hc : ∀ g ∈ L, ∀ k ∈ L, ⁅k, g⁻¹ * (j * g * j⁻¹)⁆ ∈ oddIn L) : j ∈ coreActionKernel L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup ↥L := pPrimeCore 2 ↥L with hO
  set ψ : ↥L →* ↥L ⧸ O := QuotientGroup.mk' O with hψ
  have hd : ∀ g ∈ L, g⁻¹ * (j * g * j⁻¹) ∈ L := fun g hg =>
    mul_mem (inv_mem hg) ((mem_normalizer_iff.mp hj g).mp hg)
  let d : ↥L → ↥L := fun g => ⟨(g : X)⁻¹ * (j * g * j⁻¹), hd g g.2⟩
  have hcen : ∀ g : ↥L, ψ (d g) ∈ center (↥L ⧸ O) := by
    intro g
    rw [mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective O q
    obtain ⟨x, hx, hxe⟩ := hc g g.2 k k.2
    have hxeq : x = ⁅k, d g⁆ := Subtype.ext hxe
    have h2 : ψ ⁅k, d g⁆ = 1 := by
      rw [← hxeq, ← MonoidHom.mem_ker, hψ, QuotientGroup.ker_mk']
      exact hx
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have hmul : ∀ g h : ↥L, ψ (d (g * h)) = ψ (d g) * ψ (d h) := by
    intro g h
    have e : d (g * h) = h⁻¹ * d g * h * d h := by
      ext
      simp only [d, coe_mul, coe_inv]
      group
    have hc' : ψ h * ψ (d g) = ψ (d g) * ψ h := mem_center_iff.mp (hcen g) (ψ h)
    rw [e, map_mul, map_mul, map_mul, map_inv]
    calc (ψ h)⁻¹ * ψ (d g) * ψ h * ψ (d h) = (ψ h)⁻¹ * (ψ h * ψ (d g)) * ψ (d h) := by
          rw [hc']; group
      _ = ψ (d g) * ψ (d h) := by group
  let F : ↥L →* ↥L ⧸ O := MonoidHom.mk' (fun g => ψ (d g)) hmul
  have hperf : Group.IsPerfect ↥L :=
    Subgroup.isPerfect_iff.mpr (GSThmB.commutator_eq_self_of_isPComponent hLH hL)
  have hker : F.ker = ⊤ := by
    rw [eq_top_iff, ← hperf.commutator_eq_top, _root_.commutator_def, commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.mp (hcen y) (F x))
  have hdO : ∀ k ∈ L, k⁻¹ * (j * k * j⁻¹) ∈ oddIn L := by
    intro k hk
    have h1 : F ⟨k, hk⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact mem_top _
    have h2 : d ⟨k, hk⟩ ∈ O := by
      rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
      exact h1
    exact ⟨_, h2, rfl⟩
  refine ⟨hj, fun k hk => ?_⟩
  have h1 := GrS4.conj_mem_oddIn_of_mem_normalizer (inv_mem hj) (inv_mem (hdO k hk))
  rwa [show j⁻¹ * (k⁻¹ * (j * k * j⁻¹))⁻¹ * j⁻¹⁻¹ = k⁻¹ * j⁻¹ * k * j by group] at h1

theorem le_of_commutator_mem {L H : Subgroup X} (hLH : L ≤ H)
    (hL : IsPComponent 2 (L.subgroupOf H)) {s : X} (hs : IsPGroup 2 (zpowers s))
    (hsL : s ∈ coreActionKernel L) {J Y : Subgroup X} (hJL : J ≤ normalizer (L : Set X))
    (hJ : ¬ J ≤ coreActionKernel L)
    (hY : ∀ g ∈ L ⊓ centralizer (zpowers s : Set X), ∀ j ∈ J, g⁻¹ * j * g * j⁻¹ ∈ Y)
    (hOY : oddIn L ≤ Y) : L ≤ Y := by
  set Cs : Subgroup X := L ⊓ centralizer (zpowers s : Set X) with hCs
  set S : Set X := {x | ∃ g ∈ Cs, ∃ j ∈ J, x = g⁻¹ * j * g * j⁻¹} with hS
  set P : Subgroup X := closure S ⊔ oddIn L with hP
  have hcov : L ≤ Cs ⊔ oddIn L :=
    FooteLit.le_inf_centralizer_sup_oddCoreIn hs (zpowers_le.mpr hsL)
  have hON : L ≤ normalizer ((oddIn L : Subgroup X) : Set X) := GrS4.self_le_normalizer_oddIn L
  have hSL : S ⊆ L := by
    rintro x ⟨g, hg, j, hj, rfl⟩
    rw [show g⁻¹ * j * g * j⁻¹ = g⁻¹ * (j * g * j⁻¹) by group]
    exact mul_mem (inv_mem hg.1) ((mem_normalizer_iff.mp (hJL hj) g).mp hg.1)
  have hPL : P ≤ L := sup_le ((closure_le L).mpr hSL) (map_subtype_le _)
  have hPY : P ≤ Y := sup_le ((closure_le Y).mpr (by
    rintro x ⟨g, hg, j, hj, rfl⟩
    exact hY g hg j hj)) hOY
  have hCsN : Cs ≤ normalizer (P : Set X) := by
    intro h hh
    refine FooteLit.mem_normalizer_of_map_conj_le ?_
    rw [hP, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨x, ⟨g, hg, j, hj, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have h1 : g * h⁻¹ ∈ Cs := mul_mem hg (inv_mem hh)
      have h2 : h⁻¹ ∈ Cs := inv_mem hh
      have e : h * (g⁻¹ * j * g * j⁻¹) * h⁻¹ = ((g * h⁻¹)⁻¹ * j * (g * h⁻¹) * j⁻¹) *
          (h⁻¹⁻¹ * j * h⁻¹ * j⁻¹)⁻¹ := by group
      rw [e]
      exact mem_sup_left (mul_mem (subset_closure ⟨_, h1, j, hj, rfl⟩)
        (inv_mem (subset_closure ⟨_, h2, j, hj, rfl⟩)))
    · rintro _ ⟨y, hy, rfl⟩
      exact mem_sup_right ((mem_normalizer_iff.mp (hON hh.1) y).mp hy)
  have hON' : oddIn L ≤ normalizer (P : Set X) := by
    intro o ho
    refine FooteLit.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : o * (x * o⁻¹ * x⁻¹) ∈ oddIn L :=
      mul_mem ho ((mem_normalizer_iff.mp (hON (hPL hx)) _).mp (inv_mem ho))
    rw [show o * x * o⁻¹ = (o * (x * o⁻¹ * x⁻¹)) * x by group]
    exact mul_mem (mem_sup_right h1) hx
  have hLN : L ≤ normalizer (P : Set X) := hcov.trans (sup_le hCsN hON')
  rcases eq_or_commutator_le_oddIn hLH hL hPL hLN le_sup_right with h | h
  · exact h ▸ hPY
  · exfalso
    apply hJ
    intro j hj
    refine mem_coreActionKernel_of_comm hLH hL (hJL hj) fun g hg k hk => ?_
    obtain ⟨c, hc, o, ho, rfl⟩ := exists_mul_of_mem_sup (hCs ▸ inf_le_left.trans hON) (hcov hg)
    have hjo : j * o * j⁻¹ ∈ oddIn L := GrS4.conj_mem_oddIn_of_mem_normalizer (hJL hj) ho
    have hmem : (c * o)⁻¹ * (j * (c * o) * j⁻¹) ∈ P := by
      rw [show (c * o)⁻¹ * (j * (c * o) * j⁻¹) = o⁻¹ * (c⁻¹ * j * c * j⁻¹) * (j * o * j⁻¹) by
        group]
      exact mul_mem (mul_mem (mem_sup_right (inv_mem ho))
        (mem_sup_left (subset_closure ⟨c, hc, j, hj, rfl⟩))) (mem_sup_right hjo)
    exact h (commutator_mem_commutator hk hmem)

end CFSG.ComponentClassification.GrSLit.Single
