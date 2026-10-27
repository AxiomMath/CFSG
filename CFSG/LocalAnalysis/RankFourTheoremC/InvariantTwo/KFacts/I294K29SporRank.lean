module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

variable {S : Type*} [Group S] [Finite S] {p : ℕ}

theorem exists_card_eq_pow_of_forall_pow_eq_one [Fact p.Prime] {E : Subgroup S}
    (hE : ∀ y ∈ E, y ^ p = 1) : ∃ m : ℕ, Nat.card E = p ^ m := by
  have : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE g g.2)⟩
  exact IsPGroup.iff_card.1 this

theorem pRank_top_le_pRank_centralizer_of_sylow [Fact p.Prime] {x : S} (P : Sylow p S)
    (hP : (P : Subgroup S) ≤ centralizer ({x} : Set S)) :
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) :=
  calc CFSG.Open.pRank p (⊤ : Subgroup S) = CFSG.Open.pRank p (P : Subgroup S) :=
        (CFSG.SectionRank.pRank_sylow P).1.symm
    _ ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) :=
        CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt hP

theorem three_le_pRank_centralizer_of_sylow [Fact p.Prime] {x : S} (P : Sylow p S)
    (hP : (P : Subgroup S) ≤ centralizer ({x} : Set S))
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) :=
  h3.trans (pRank_top_le_pRank_centralizer_of_sylow P hP)

theorem three_le_pRank_centralizer_of_extraspecial [Fact p.Prime] {Q Z : Subgroup S}
    (hexp : ∀ y ∈ Q, y ^ p = 1) (hZQ : Z ≤ Q) (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hZ : Nat.card Z = p) (hcomm : ∀ y ∈ Q, ∀ w ∈ Q, y * w * y⁻¹ * w⁻¹ ∈ Z)
    (hcard : p ^ 5 ≤ Nat.card Q) {x : S} (hxQ : x ∈ Q) (hxZ : x ∉ Z) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hCcard : p ^ 4 ≤ Nat.card (Q ⊓ centralizer ({x} : Set S) : Subgroup S) := by
    let ψ : Q →* Z :=
      { toFun := fun y => ⟨x * y * x⁻¹ * y⁻¹, hcomm x hxQ y y.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := by
          intro y w
          apply Subtype.ext
          have hzy : (x * (w : S) * x⁻¹ * (w : S)⁻¹) * (y : S) =
              (y : S) * (x * (w : S) * x⁻¹ * (w : S)⁻¹) := hZc _ (hcomm x hxQ w w.2) y y.2
          show x * ((y : S) * w) * x⁻¹ * ((y : S) * w)⁻¹ =
            (x * y * x⁻¹ * (y : S)⁻¹) * (x * w * x⁻¹ * (w : S)⁻¹)
          calc x * ((y : S) * w) * x⁻¹ * ((y : S) * w)⁻¹
              = (x * y * x⁻¹ * (y : S)⁻¹) * ((y : S) * (x * w * x⁻¹ * (w : S)⁻¹) * (y : S)⁻¹) := by
                group
            _ = (x * y * x⁻¹ * (y : S)⁻¹) * (x * w * x⁻¹ * (w : S)⁻¹) := by
                rw [← hzy]; group }
    have h1 := Subgroup.card_ker_mul_card_range ψ
    have h2 : Nat.card ψ.range ≤ p := hZ ▸ Subgroup.card_le_card_group _
    have h3 : p ^ 5 ≤ Nat.card ψ.ker * p := by
      calc p ^ 5 ≤ Nat.card Q := hcard
        _ = Nat.card ψ.ker * Nat.card ψ.range := h1.symm
        _ ≤ Nat.card ψ.ker * p := Nat.mul_le_mul_left _ h2
    have h4 : p ^ 4 ≤ Nat.card ψ.ker := by
      have : p ^ 4 * p ≤ Nat.card ψ.ker * p := by rwa [← pow_succ]
      exact Nat.le_of_mul_le_mul_right this hp.pos
    have hmem : ∀ y : ψ.ker, ((y : Q) : S) ∈ centralizer ({x} : Set S) := by
      intro y
      have h5 : ψ (y : Q) = 1 := y.2
      have h6 : x * ((y : Q) : S) * x⁻¹ * ((y : Q) : S)⁻¹ = 1 := congrArg Subtype.val h5
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((y : Q) : S) * x = (x * ((y : Q) : S) * x⁻¹ * ((y : Q) : S)⁻¹)⁻¹ * (x * ((y : Q) : S))
            := by group
        _ = x * ((y : Q) : S) := by rw [h6]; group
    refine h4.trans (Nat.card_le_card_of_injective
      (fun y : ψ.ker =>
        (⟨((y : Q) : S), Subgroup.mem_inf.2 ⟨(y : Q).2, hmem y⟩⟩ :
          (Q ⊓ centralizer ({x} : Set S) : Subgroup S))) ?_)
    intro a b hab
    have h7 := congrArg (fun z : (Q ⊓ centralizer ({x} : Set S) : Subgroup S) => (z : S)) hab
    exact Subtype.ext (Subtype.ext h7)
  set E₁ : Subgroup S := Subgroup.closure ((Z : Set S) ∪ {x}) with hE₁
  have hgen₁ : ∀ a ∈ (Z : Set S) ∪ {x}, a ∈ Q := by
    rintro a (ha | ha)
    · exact hZQ ha
    · rw [Set.mem_singleton_iff.1 ha]; exact hxQ
  have hE₁Q : E₁ ≤ Q := (Subgroup.closure_le _).2 hgen₁
  have hE₁C : E₁ ≤ centralizer ({x} : Set S) := by
    refine (Subgroup.closure_le _).2 fun a ha => ?_
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rcases ha with ha | ha
    · exact hZc a ha x hxQ
    · rw [Set.mem_singleton_iff.1 ha]
  have hE₁comm : IsMulCommutative E₁ := by
    refine Subgroup.isMulCommutative_closure ?_
    intro a ha b hb _
    show a * b = b * a
    rcases ha with ha | ha
    · exact hZc a ha b (hgen₁ b hb)
    · rw [Set.mem_singleton_iff.1 ha]
      rcases hb with hb | hb
      · exact (hZc b hb x hxQ).symm
      · rw [Set.mem_singleton_iff.1 hb]
  have hZE₁ : Z ≤ E₁ := fun z hz => Subgroup.subset_closure (Or.inl hz)
  have hxE₁ : x ∈ E₁ := Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨m₁, hm₁⟩ := exists_card_eq_pow_of_forall_pow_eq_one (fun y hy => hexp y (hE₁Q hy))
  have hm₁2 : 2 ≤ m₁ := by
    by_contra h
    have hle : Nat.card E₁ ≤ Nat.card Z := by
      rw [hm₁, hZ]
      calc p ^ m₁ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    exact hxZ (by rw [Subgroup.eq_of_le_of_card_ge hZE₁ hle]; exact hxE₁)
  by_cases hm₁3 : 3 ≤ m₁
  · exact hm₁3.trans (CFSG.SectionRank.le_pRank hp1 hE₁C
      ⟨hE₁comm, fun y hy => hexp y (hE₁Q hy)⟩ hm₁)
  have hm₁eq : m₁ = 2 := by omega
  have hE₁leC : E₁ ≤ Q ⊓ centralizer ({x} : Set S) := le_inf hE₁Q hE₁C
  have hlt : E₁ < Q ⊓ centralizer ({x} : Set S) := by
    refine lt_of_le_of_ne hE₁leC fun h => ?_
    have h4 : Nat.card (Q ⊓ centralizer ({x} : Set S) : Subgroup S) = p ^ 2 := by
      rw [← h, hm₁, hm₁eq]
    have h5 : p ^ 4 ≤ p ^ 2 := h4 ▸ hCcard
    have h6 : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp1 (by norm_num)
    omega
  obtain ⟨c, hcC, hcE₁⟩ := SetLike.exists_of_lt hlt
  obtain ⟨hcQ, hcx⟩ := Subgroup.mem_inf.1 hcC
  have hcx' : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.1 hcx
  set E : Subgroup S := Subgroup.closure ((E₁ : Set S) ∪ {c}) with hE
  have hE₁c : ∀ e ∈ E₁, e * c = c * e := by
    have : E₁ ≤ centralizer ({c} : Set S) := by
      refine (Subgroup.closure_le _).2 fun a ha => ?_
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rcases ha with ha | ha
      · exact hZc a ha c hcQ
      · rw [Set.mem_singleton_iff.1 ha]; exact hcx'.symm
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.1 (this he)
  have hEcomm : IsMulCommutative E := by
    refine Subgroup.isMulCommutative_closure ?_
    intro a ha b hb _
    show a * b = b * a
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact setLike_mul_comm ha hb
      · rw [Set.mem_singleton_iff.1 hb]; exact hE₁c a ha
    · rw [Set.mem_singleton_iff.1 ha]
      rcases hb with hb | hb
      · exact (hE₁c b hb).symm
      · rw [Set.mem_singleton_iff.1 hb]
  have hEQ : E ≤ Q := by
    refine (Subgroup.closure_le _).2 ?_
    rintro a (ha | ha)
    · exact hE₁Q ha
    · rw [Set.mem_singleton_iff.1 ha]; exact hcQ
  have hEC : E ≤ centralizer ({x} : Set S) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro a (ha | ha)
    · exact hE₁C ha
    · rw [Set.mem_singleton_iff.1 ha]; exact hcx
  have hE₁E : E₁ ≤ E := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have hcE : c ∈ E := Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_forall_pow_eq_one (fun y hy => hexp y (hEQ hy))
  have hm₁m : m₁ < m := by
    by_contra h
    have hle : Nat.card E ≤ Nat.card E₁ := by
      rw [hm, hm₁]; exact Nat.pow_le_pow_right hp.pos (by omega)
    exact hcE₁ (by rw [Subgroup.eq_of_le_of_card_ge hE₁E hle]; exact hcE)
  exact (by omega : 3 ≤ m).trans (CFSG.SectionRank.le_pRank hp1 hEC
    ⟨hEcomm, fun y hy => hexp y (hEQ hy)⟩ hm)

end CFSG.LocalAnalysis.RankFourTheoremC
