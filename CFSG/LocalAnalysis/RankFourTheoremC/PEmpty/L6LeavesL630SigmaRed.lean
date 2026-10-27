module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630NineB
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Aux

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open Subgroup

@[expose] def KFactAltSixSub15 : Prop :=
  ∀ K : Subgroup (Equiv.Perm (Fin 6)), K ≤ alternatingGroup (Fin 6) → 15 ∣ Nat.card K →
    IsSimpleGroup K ∧ 2 ∣ Nat.card K ∧ ¬ ∀ a b : K, a * b = b * a

theorem index_alt_dvd_two (A : Subgroup (Equiv.Perm (Fin 6))) :
    ((alternatingGroup (Fin 6)).subgroupOf A).index ∣ 2 := by
  set f : A →* ℤˣ := (Equiv.Perm.sign).comp A.subtype with hf
  have hker : f.ker = (alternatingGroup (Fin 6)).subgroupOf A := by
    ext a
    simp [hf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Equiv.Perm.mem_alternatingGroup]
  rw [← hker, Subgroup.index_ker]
  have hle : f.range ≤ Subgroup.zpowers (-1 : ℤˣ) := by
    intro y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    show Equiv.Perm.sign (a : Equiv.Perm (Fin 6)) ∈ Subgroup.zpowers (-1 : ℤˣ)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (a : Equiv.Perm (Fin 6))) with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _
  calc Nat.card f.range ∣ Nat.card (Subgroup.zpowers (-1 : ℤˣ)) :=
        Subgroup.card_dvd_of_le hle
    _ = 2 := by
        rw [Nat.card_zpowers, orderOf_eq_prime (Int.units_sq _) (by decide)]

theorem sigma_section_core (hA : KFactAltSixSub15) (A : Subgroup (Equiv.Perm (Fin 6)))
    (N : Subgroup A) [N.Normal] {Γ : Type} [Group Γ] [Finite Γ] (e : (A ⧸ N) ≃* Γ)
    (h15 : 15 ∣ Nat.card Γ) :
    ∃ S : Subgroup Γ, S.Normal ∧ S.index ∣ 2 ∧ IsSimpleGroup S ∧ 2 ∣ Nat.card S ∧
      15 ∣ Nat.card S ∧ ¬ ∀ a b : S, a * b = b * a := by
  classical
  set B : Subgroup A := (alternatingGroup (Fin 6)).subgroupOf A with hBdef
  have hBn : B.Normal := inferInstance
  have hBidx : B.index ∣ 2 := index_alt_dvd_two A
  have hAcard : Nat.card A = Nat.card N * N.index := (Subgroup.card_mul_index N).symm
  have hBcard : Nat.card A = Nat.card B * B.index := (Subgroup.card_mul_index B).symm
  have hAdvd : Nat.card A ∣ 720 := by
    have := Subgroup.card_subgroup_dvd_card A
    rwa [card_perm_fin_six] at this
  have hQcard : N.index = Nat.card Γ := Nat.card_congr e.toEquiv
  have hcop : Nat.Coprime 15 B.index :=
    Nat.Coprime.coprime_dvd_right hBidx (by norm_num)
  have h15B : 15 ∣ Nat.card B := by
    apply Nat.Coprime.dvd_of_dvd_mul_right hcop
    rw [← hBcard, hAcard, hQcard]
    exact Dvd.dvd.mul_left h15 _
  set eBK : B ≃* B.map A.subtype := Subgroup.equivMapOfInjective B A.subtype A.subtype_injective
    with heBK
  have hKle : B.map A.subtype ≤ alternatingGroup (Fin 6) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp hb
  have hKcard : Nat.card (B.map A.subtype) = Nat.card B := (Nat.card_congr eBK.toEquiv).symm
  obtain ⟨hKsimple, hKeven, hKnab⟩ := hA (B.map A.subtype) hKle (by rw [hKcard]; exact h15B)
  haveI : IsSimpleGroup (B.map A.subtype) := hKsimple
  have hBsimple : IsSimpleGroup B := eBK.isSimpleGroup
  haveI : IsSimpleGroup B := hBsimple
  have hBeven : 2 ∣ Nat.card B := by rw [← hKcard]; exact hKeven
  have hBnab : ¬ ∀ a b : B, a * b = b * a := by
    intro h
    apply hKnab
    intro a b
    apply eBK.symm.injective
    simpa [map_mul] using h (eBK.symm a) (eBK.symm b)
  set T : Subgroup B := N.comap B.subtype with hTdef
  haveI hTn : T.Normal := Subgroup.Normal.comap inferInstance B.subtype
  rcases Subgroup.Normal.eq_bot_or_eq_top T with hT | hT
  ·
    set g : A →* Γ := e.toMonoidHom.comp (QuotientGroup.mk' N) with hgdef
    have hgsurj : Function.Surjective g :=
      e.surjective.comp (QuotientGroup.mk'_surjective N)
    set φ : B →* Γ := g.comp B.subtype with hφdef
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro b hb
      have h1 : e (QuotientGroup.mk' N (b : A)) = 1 := hb
      have h2 : QuotientGroup.mk' N (b : A) = 1 :=
        e.injective (by rw [map_one]; exact h1)
      have hbN : (b : A) ∈ N := (QuotientGroup.eq_one_iff _).mp h2
      have hbT : b ∈ T := hbN
      rw [hT, Subgroup.mem_bot] at hbT
      exact hbT
    set eS : B ≃* φ.range := MonoidHom.ofInjective hφinj with heS
    have hSsimple : IsSimpleGroup φ.range := eS.symm.isSimpleGroup
    have hScard : Nat.card φ.range = Nat.card B := (Nat.card_congr eS.symm.toEquiv)
    have hSnab : ¬ ∀ a b : φ.range, a * b = b * a := by
      intro h
      apply hBnab
      intro a b
      apply eS.injective
      simpa [map_mul] using h (eS a) (eS b)
    have hSn : φ.range.Normal := by
      constructor
      intro n hn y
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hn
      obtain ⟨a, rfl⟩ := hgsurj y
      refine MonoidHom.mem_range.mpr ⟨⟨a * (b : A) * a⁻¹, hBn.conj_mem _ b.2 a⟩, ?_⟩
      show g (a * (b : A) * a⁻¹) = g a * g (b : A) * (g a)⁻¹
      simp only [map_mul, map_inv]
    have hSmap : φ.range = B.map g := by
      ext y
      constructor
      · intro hy
        obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
        exact Subgroup.mem_map.mpr ⟨(b : A), b.2, rfl⟩
      · intro hy
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
        exact MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
    have hSidx : φ.range.index ∣ 2 := by
      rw [hSmap]
      exact (Subgroup.index_map_dvd B hgsurj).trans hBidx
    exact ⟨φ.range, hSn, hSidx, hSsimple, by rw [hScard]; exact hBeven,
      by rw [hScard]; exact h15B, hSnab⟩
  ·
    exfalso
    have hBN : B ≤ N := by
      intro a ha
      have hmem : (⟨a, ha⟩ : B) ∈ T := by
        rw [hT]
        exact Subgroup.mem_top _
      exact hmem
    have h15N : 15 ∣ Nat.card N := dvd_trans h15B (Subgroup.card_dvd_of_le hBN)
    have h225 : 15 * 15 ∣ Nat.card A := by
      rw [hAcard]
      exact Nat.mul_dvd_mul h15N (by rw [hQcard]; exact h15)
    have h720 := dvd_trans h225 hAdvd
    norm_num at h720

theorem sigmaSixSectionFact_of_alt (hA : KFactAltSixSub15) : SigmaSixSectionFact := by
  intro Γ _ _ hinv h15
  obtain ⟨A, N, hN, ⟨e⟩⟩ := hinv
  haveI := hN
  exact sigma_section_core hA A N e h15

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
