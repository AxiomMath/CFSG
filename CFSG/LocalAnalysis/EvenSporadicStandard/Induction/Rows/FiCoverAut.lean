module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterTransfer
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.EvenSporadicStandard.Induction.Cover

open Subgroup CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {X : Type} [Group X]

theorem twoAdic_le_two_of_card_le_four {X : Type} [Group X] (A : Subgroup X)
    (h : Nat.card A ≤ 4) : twoAdic A ≤ 2 := by
  unfold twoAdic
  by_cases h0 : Nat.card A = 0
  · simp [h0]
  by_contra hlt
  push Not at hlt
  have hd : 2 ^ (Nat.card A).factorization 2 ∣ Nat.card A := Nat.ordProj_dvd _ _
  have h3 : 2 ^ 3 ≤ 2 ^ (Nat.card A).factorization 2 := Nat.pow_le_pow_right (by norm_num) hlt
  have h4 := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
  omega

theorem card_le_four_of_fix {Y : Type} [Group Y] [Finite Y] (hout : OutTwo Y) {Kh : Subgroup Y}
    (hC : Nat.card (centralizer (Kh : Set Y)) ≤ 2) (A : Subgroup (MulAut Y))
    (hA : ∀ α ∈ A, ∀ k ∈ Kh, α k = k) : Nat.card A ≤ 4 := by
  set I : Subgroup (MulAut Y) := A ⊓ (MulAut.conj : Y →* MulAut Y).range with hI
  have hIA : I ≤ A := inf_le_left
  have hIle : I ≤ (centralizer (Kh : Set Y)).map (MulAut.conj : Y →* MulAut Y) := by
    rintro _ ⟨hαA, l, rfl⟩
    refine ⟨l, (mem_centralizer_iff.2 ?_ : l ∈ centralizer (Kh : Set Y)), rfl⟩
    intro k hk
    have h1 : (MulAut.conj l) k = k := hA _ hαA k hk
    rw [MulAut.conj_apply] at h1
    calc k * l = (l * k * l⁻¹) * l := by rw [h1]
      _ = l * k := by group
  have hIcard : Nat.card I ≤ 2 :=
    (Subgroup.card_le_of_le hIle).trans
      ((Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)).trans hC)
  have hidx : Nat.card (A ⧸ I.subgroupOf A) ≤ 2 := by
    by_cases hall : ∀ α ∈ A, α ∈ I
    · have : Subsingleton (A ⧸ I.subgroupOf A) := by
        refine ⟨fun x y => ?_⟩
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
        rw [QuotientGroup.eq]
        exact mem_subgroupOf.2 (hall _ (mul_mem (inv_mem a.2) b.2))
      rw [Nat.card_unique]
      norm_num
    · push Not at hall
      obtain ⟨α₀, hα₀A, hα₀I⟩ := hall
      have hsurj : Function.Surjective (fun b : Bool =>
          if b then (QuotientGroup.mk (⟨α₀, hα₀A⟩ : A) : A ⧸ I.subgroupOf A)
          else QuotientGroup.mk 1) := by
        intro x
        obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective x
        have hα₀inn : ¬ ∃ l : Y, α₀ = MulAut.conj l := fun ⟨l, hl⟩ =>
          hα₀I ⟨hα₀A, l, hl.symm⟩
        rcases hout α₀ β with h | ⟨l, hl⟩ | ⟨l, hl⟩
        · exact absurd h hα₀inn
        · refine ⟨false, ?_⟩
          show QuotientGroup.mk 1 = QuotientGroup.mk β
          rw [QuotientGroup.eq]
          refine mem_subgroupOf.2 ⟨?_, l, hl.symm⟩
          simp
        · refine ⟨true, ?_⟩
          show QuotientGroup.mk ⟨α₀, hα₀A⟩ = QuotientGroup.mk β
          rw [QuotientGroup.eq]
          refine mem_subgroupOf.2 ⟨?_, l, hl.symm⟩
          simpa using mul_mem (inv_mem hα₀A) β.2
      exact (Nat.card_le_card_of_surjective _ hsurj).trans (by simp)
  have hAcard : Nat.card A ≤ 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (I.subgroupOf A)
    have h2 : Nat.card (I.subgroupOf A) = Nat.card I :=
      Nat.card_congr (subgroupOfEquivOfLe hIA).toEquiv
    rw [h1, h2]
    calc Nat.card (A ⧸ I.subgroupOf A) * Nat.card I ≤ 2 * 2 := Nat.mul_le_mul hidx hIcard
      _ = 4 := by norm_num
  exact hAcard


theorem card_autCentralizer_le_of_cover {H : Type} [Group H] [Finite H] {L K : Subgroup H}
    (hL : Group.IsPerfect ↥L) (hout : OutTwo (↥L ⧸ center ↥L))
    (hC : Nat.card (centralizer (bar (K.subgroupOf L) : Set (↥L ⧸ center ↥L))) ≤ 2) :
    Nat.card (autCentralizer L K) ≤ 4 := by
  have := hL
  set ρ := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L with hρ
  have hinj : Function.Injective ρ :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥L
  set A := autCentralizer L K with hA
  have hcard : Nat.card (A.map ρ) = Nat.card A := Subgroup.card_map_of_injective hinj
  have h2 : Nat.card (A.map ρ) ≤ 4 := by
    refine card_le_four_of_fix hout hC (A.map ρ) ?_
    rintro _ ⟨α, hα, rfl⟩ y hy
    obtain ⟨k, hk, rfl⟩ := mem_bar.1 hy
    have := hα k (Subgroup.mem_subgroupOf.1 hk)
    show CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α
      (QuotientGroup.mk' (center ↥L) k) = QuotientGroup.mk' (center ↥L) k
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk, this]
  rwa [hcard] at h2

theorem twoAdic_autCentralizer_le_of_cover {H : Type} [Group H] [Finite H] {L K : Subgroup H}
    (hL : Group.IsPerfect ↥L) (hout : OutTwo (↥L ⧸ center ↥L))
    (hC : Nat.card (centralizer (bar (K.subgroupOf L) : Set (↥L ⧸ center ↥L))) ≤ 2) :
    twoAdic (autCentralizer L K) ≤ 2 :=
  twoAdic_le_two_of_card_le_four _ (card_autCentralizer_le_of_cover hL hout hC)

theorem commutator_map_conj {K : Subgroup X} (hK : ⁅K, K⁆ = K) (g : X) :
    ⁅K.map (MulAut.conj g).toMonoidHom, K.map (MulAut.conj g).toMonoidHom⁆ =
      K.map (MulAut.conj g).toMonoidHom := by
  rw [← Subgroup.map_commutator, hK]

theorem map_conj_eq_of_bar_map_le [Finite X] {K : Subgroup X} (hK : ⁅K, K⁆ = K) {g : X}
    (h : (bar K).map (MulAut.conj (g : X ⧸ center X)).toMonoidHom ≤ bar K) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    refine le_of_perfect_le_sup_central (Z' := center X) le_rfl (commutator_map_conj hK g) ?_
    rintro _ ⟨k, hk, rfl⟩
    have hmk : ((g * k * g⁻¹ : X) : X ⧸ center X) ∈ bar K := by
      have := h (Subgroup.mem_map_of_mem _ (mk_mem_bar_of_mem hk))
      simpa [MulAut.conj_apply] using this
    obtain ⟨k', hk', z, hz, hx⟩ := mem_bar_iff_exists_mem_mul.1 hmk
    exact (mem_sup_central le_rfl).2 ⟨k', hk', z, hz, hx.symm⟩
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

theorem sup_conj_eq_top [Finite X] {K : Subgroup X} (hK : ⁅K, K⁆ = K)
    (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = (⊤ : Subgroup X))
    (hgen : ∀ y : X ⧸ center X, (bar K).map (MulAut.conj y).toMonoidHom ≠ bar K →
      bar K ⊔ (bar K).map (MulAut.conj y).toMonoidHom = (⊤ : Subgroup (X ⧸ center X)))
    {g : X} (hne : K.map (MulAut.conj g).toMonoidHom ≠ K) :
    K ⊔ K.map (MulAut.conj g).toMonoidHom = (⊤ : Subgroup X) := by
  have h1 : (bar K).map (MulAut.conj (g : X ⧸ center X)).toMonoidHom ≠ bar K := fun heq =>
    hne (map_conj_eq_of_bar_map_le hK heq.le)
  set M := K ⊔ K.map (MulAut.conj g).toMonoidHom with hM
  have hbarM : bar M = (⊤ : Subgroup (X ⧸ center X)) := by
    rw [hM]
    unfold bar
    rw [Subgroup.map_sup, map_map_conj]
    exact hgen _ h1
  have hMZ : M ⊔ center X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : (x : X ⧸ center X) ∈ bar M := hbarM ▸ Subgroup.mem_top _
    obtain ⟨m, hm, z, hz, rfl⟩ := mem_bar_iff_exists_mem_mul.1 this
    exact (mem_sup_central le_rfl).2 ⟨m, hm, z, hz, rfl⟩
  rw [eq_top_iff]
  calc (⊤ : Subgroup X) = ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := hX.symm
    _ = ⁅M ⊔ center X, M ⊔ center X⁆ := by rw [hMZ]
    _ ≤ ⁅M, M⁆ := commutator_sup_central_le le_rfl
    _ ≤ M := commutator_le_self M

end CFSG.EvenSporadicStandard.Induction.Cover
