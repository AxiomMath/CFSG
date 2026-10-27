module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3WrAlg
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.WreathSylow

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X]

theorem Wr.eq_inv_of_sq_eq_one {w : Wr} (hwe : w.e = true) (hw2 : w * w = 1) : w.b = w.a⁻¹ := by
  rcases w with ⟨p, q, e⟩
  simp only at hwe
  subst hwe
  have h := congrArg Wr.a hw2
  simp only [Wr.mul_tt, Wr.one_def] at h
  exact eq_inv_of_mul_eq_one_right h

theorem exists_mem_conj_of_flag (f : X →* Wr) (hf : Function.Injective f)
    {A : Subgroup (Equiv.Perm (Fin 6))} (hAn : A.Normal)
    (hall : ∀ c ∈ A, ∀ d ∈ A, ∃ g : X, f g = ⟨c, d, false⟩)
    {P : Subgroup X} (hP2 : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) {w y : X} (hw2 : w * w = 1)
    (hwe : (f w).e = true) (hwP : w ∈ P) (hyP : y ∈ P) (hy2 : y * y = 1)
    (hwy : (f (w * y)).e = false ∧ (f (w * y)).a ∈ A ∧ (f (w * y)).b ∈ A) :
    ∃ c ∈ P, y = c⁻¹ * w * c := by
  have hfw2 : f w * f w = 1 := by rw [← map_mul, hw2, map_one]
  have hq : (f w).b = (f w).a⁻¹ := Wr.eq_inv_of_sq_eq_one hwe hfw2
  set N1 : Subgroup X := (Wr.leftSub A).comap f with hN1
  set N2 : Subgroup X := (Wr.rightSub A).comap f with hN2
  have hdisj : Disjoint N1 N2 := by
    rw [Subgroup.disjoint_def]
    intro g h1 h2
    have h1' := Wr.mem_leftSub_iff.1 h1
    have h2' := Wr.mem_rightSub_iff.1 h2
    apply hf
    rw [map_one]
    rcases hfg : f g with ⟨a, b, e⟩
    rw [hfg] at h1' h2'
    simp only at h1' h2'
    obtain ⟨he, -, hb⟩ := h1'
    obtain ⟨-, ha, -⟩ := h2'
    subst he hb ha
    rfl
  have hcomm : ∀ a ∈ N1, ∀ b ∈ N2, a * b = b * a := fun a ha b hb => by
    apply hf
    rw [map_mul, map_mul]
    exact Wr.leftSub_comm_rightSub A ha hb
  have hsup : N1 ⊔ N2 = (Wr.baseSub A).comap f := by
    apply le_antisymm
    · exact sup_le (Subgroup.comap_mono (Wr.leftSub_le_baseSub A))
        (Subgroup.comap_mono (Wr.rightSub_le_baseSub A))
    · intro g hg
      have hg' : f g ∈ Wr.baseSub A := hg
      have hform := Wr.baseSub_le_sup A hg'
      obtain ⟨hge, hga, hgb⟩ := Wr.mem_baseSub_iff.1 hg'
      obtain ⟨g1, hg1⟩ := hall _ hga 1 A.one_mem
      obtain ⟨g2, hg2⟩ := hall 1 A.one_mem _ hgb
      have hg1N : g1 ∈ N1 := by
        show f g1 ∈ Wr.leftSub A
        rw [hg1]
        exact Wr.mem_leftSub_iff.2 ⟨rfl, hga, rfl⟩
      have hg2N : g2 ∈ N2 := by
        show f g2 ∈ Wr.rightSub A
        rw [hg2]
        exact Wr.mem_rightSub_iff.2 ⟨rfl, rfl, hgb⟩
      have : g = g1 * g2 := by
        apply hf
        rw [map_mul, hg1, hg2, ← hform]
      rw [this]
      exact Subgroup.mul_mem_sup hg1N hg2N
  have hnorm : (N1 ⊔ N2).Normal := by
    rw [hsup]
    exact (Wr.baseSub_normal hAn).comap f
  have hswap1 : ∀ a ∈ N1, w * a * w ∈ N2 := by
    intro a ha
    have ha' := Wr.mem_leftSub_iff.1 ha
    show f (w * a * w) ∈ Wr.rightSub A
    rw [map_mul, map_mul]
    rcases hfw : f w with ⟨p, q, e⟩
    rcases hfa : f a with ⟨c, d, e'⟩
    rw [hfa] at ha'
    rw [hfw] at hwe hq
    simp only at ha' hwe hq
    obtain ⟨rfl, hc, rfl⟩ := ha'
    subst hwe hq
    refine Wr.mem_rightSub_iff.2 ⟨?_, ?_, ?_⟩
    · simp
    · simp
    · simpa [mul_assoc] using hAn.conj_mem _ hc p⁻¹
  have hswap2 : ∀ b ∈ N2, w * b * w ∈ N1 := by
    intro b hb
    have hb' := Wr.mem_rightSub_iff.1 hb
    show f (w * b * w) ∈ Wr.leftSub A
    rw [map_mul, map_mul]
    rcases hfw : f w with ⟨p, q, e⟩
    rcases hfb : f b with ⟨c, d, e'⟩
    rw [hfb] at hb'
    rw [hfw] at hwe hq
    simp only at hb' hwe hq
    obtain ⟨rfl, rfl, hd⟩ := hb'
    subst hwe hq
    refine Wr.mem_leftSub_iff.2 ⟨?_, ?_, ?_⟩
    · simp
    · simpa [mul_assoc] using hAn.conj_mem _ hd p
    · simp
  have hSyl : IsSylowOf 2 P ⊤ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isSylowOf_iff.2 ⟨le_top, hP2, by
      rw [Subgroup.relIndex_top_right]; exact hPidx⟩
  have hzx : w * y ∈ N1 ⊔ N2 := by
    rw [hsup]
    show f (w * y) ∈ Wr.baseSub A
    exact Wr.mem_baseSub_iff.2 hwy
  exact exists_mem_conj_of_wreath_sylow hSyl hnorm hdisj hcomm hw2 hswap1 hswap2 hwP hyP hy2 hzx

end CFSG.EvenSporadicStandard.M22Std
