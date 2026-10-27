module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2GorLocal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.OddStandard.ThmC.O2.Gor

open CFSG Subgroup

section Local

variable {Q : Type} [Group Q] [Finite Q]

theorem eq_bot_of_odd (hO : pPrimeCore 2 Q = ⊥) {M H : Subgroup Q} (hM : M.Normal)
    (hHM : H ≤ M) (hMH : M ≤ normalizer (H : Set Q)) (hodd : Odd (Nat.card H)) : H = ⊥ := by
  have := hM
  have hnorm : (H.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).2 hMH
  have hcop : Nat.Coprime 2 (Nat.card (H.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv]
    exact Nat.coprime_two_left.mpr hodd
  have hle : H.subgroupOf M ≤ pPrimeCore 2 M := le_sSup ⟨hnorm, hcop⟩
  have h1 : H ≤ pPrimeCore 2 Q := by
    have := Subgroup.map_mono (f := M.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hHM] at this
    exact this.trans (pPrimeCore_normal_le M)
  rw [hO] at h1
  exact le_bot_iff.1 h1

omit [Finite Q] in
theorem gn_pCore_normal_le (M : Subgroup Q) [M.Normal] :
    (pCore 2 M).map M.subtype ≤ pCore 2 Q := by
  have hK : ((pCore 2 M).map M.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hc := (pCore_characteristic (p := 2) (G := M)).fixed (MulAut.conjNormal g)
    have : ((MulAut.conjNormal g) y : M) ∈ pCore 2 M := by
      have h2 : y ∈ (pCore 2 M).comap (MulAut.conjNormal g).toMonoidHom := by
        rw [hc]; exact hy
      exact h2
    exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩
  exact le_sSup ⟨hK, (pCore_isPGroup (p := 2) (G := M)).map M.subtype⟩

omit [Finite Q] in
theorem eq_bot_of_two (hP : pCore 2 Q = ⊥) {M H : Subgroup Q} (hM : M.Normal)
    (hHM : H ≤ M) (hMH : M ≤ normalizer (H : Set Q)) (h2 : IsPGroup 2 H) : H = ⊥ := by
  have := hM
  have hnorm : (H.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).2 hMH
  have hp2 : IsPGroup 2 (H.subgroupOf M) :=
    h2.of_equiv (Subgroup.subgroupOfEquivOfLe hHM).symm
  have hle : H.subgroupOf M ≤ pCore 2 M := le_sSup ⟨hnorm, hp2⟩
  have h1 : H ≤ pCore 2 Q := by
    have := Subgroup.map_mono (f := M.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hHM] at this
    exact this.trans (gn_pCore_normal_le M)
  rw [hP] at h1
  exact le_bot_iff.1 h1

theorem sylow_le_of_normalizedBy (hO : pPrimeCore 2 Q = ⊥) (hP : pCore 2 Q = ⊥) (R : Sylow 2 Q)
    (habel : ∀ r ∈ (R : Subgroup Q), ∀ s ∈ (R : Subgroup Q), r * s = s * r)
    (hfpf : ∀ g ∈ normalizer ((R : Subgroup Q) : Set Q),
      (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r) ∨
        (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r → r = 1))
    (N : Subgroup Q) (hNM : N ≤ normalClosure ((R : Subgroup Q) : Set Q))
    (hMN : normalClosure ((R : Subgroup Q) : Set Q) ≤ normalizer (N : Set Q)) (hN : N ≠ ⊥) :
    (R : Subgroup Q) ≤ N := by
  have hM : (normalClosure ((R : Subgroup Q) : Set Q)).Normal := inferInstance
  have hRM : (R : Subgroup Q) ≤ normalClosure ((R : Subgroup Q) : Set Q) :=
    Subgroup.le_normalClosure
  have hRN : (R : Subgroup Q) ≤ normalizer (N : Set Q) := hRM.trans hMN
  by_cases hmove : ∃ y ∈ N, y ∈ normalizer (((R : Subgroup Q) ⊓ N : Subgroup Q) : Set Q) ∧
      y ∉ centralizer (((R : Subgroup Q) ⊓ N : Subgroup Q) : Set Q)
  · obtain ⟨y, hyN, hyNorm, hyC⟩ := hmove
    exact le_of_moves R habel hfpf N hRN hyN hyNorm hyC
  · have hNC : ∀ y ∈ N, y ∈ normalizer (((R : Subgroup Q) ⊓ N : Subgroup Q) : Set Q) →
        y ∈ centralizer (((R : Subgroup Q) ⊓ N : Subgroup Q) : Set Q) := fun y hy h1 => by
      by_contra h2
      exact hmove ⟨y, hy, h1, h2⟩
    obtain ⟨O, hON, hOodd, hNO, hNOR⟩ := exists_odd_complement R habel N hRN hNC
    have hMO : normalClosure ((R : Subgroup Q) : Set Q) ≤ normalizer (O : Set Q) :=
      hMN.trans hNO
    have hO1 : O = ⊥ := eq_bot_of_odd hO hM (hON.trans hNM) hMO hOodd
    have hNR : N ≤ (R : Subgroup Q) := by
      rw [hO1, bot_sup_eq] at hNOR
      exact hNOR
    have hN2 : IsPGroup 2 N := R.isPGroup'.to_le hNR
    exact absurd (eq_bot_of_two hP hM hNM hMN hN2) hN

omit [Finite Q] in
theorem gn_mem_conj (N : Subgroup Q) (c x : Q) :
    x ∈ N.comap (MulAut.conj c).toMonoidHom ↔ c * x * c⁻¹ ∈ N := by
  rw [Subgroup.mem_comap]
  rfl

omit [Finite Q] in
theorem gn_conj_le {M N : Subgroup Q} (hM : M.Normal) (hNM : N ≤ M) (c : Q) :
    N.comap (MulAut.conj c).toMonoidHom ≤ M := by
  intro x hx
  have h1 : c * x * c⁻¹ ∈ M := hNM ((gn_mem_conj N c x).1 hx)
  have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
  have h2 := hM.conj_mem _ h1 c⁻¹
  rw [e] at h2
  exact h2

omit [Finite Q] in
theorem gn_le_normalizer_conj {M N : Subgroup Q} (hM : M.Normal)
    (hMN : M ≤ normalizer (N : Set Q)) (c : Q) :
    M ≤ normalizer ((N.comap (MulAut.conj c).toMonoidHom : Subgroup Q) : Set Q) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [gn_mem_conj, gn_mem_conj]
  have h1 := Subgroup.mem_normalizer_iff.1 (hMN (hM.conj_mem m hm c)) (c * x * c⁻¹)
  have e : c * (m * x * m⁻¹) * c⁻¹ = (c * m * c⁻¹) * (c * x * c⁻¹) * (c * m * c⁻¹)⁻¹ := by
    group
  rw [e]
  exact h1

omit [Finite Q] in
theorem gn_conj_ne_bot {N : Subgroup Q} (hN : N ≠ ⊥) (c : Q) :
    N.comap (MulAut.conj c).toMonoidHom ≠ ⊥ := by
  intro h
  apply hN
  rw [eq_bot_iff]
  intro n hn
  have h1 : c⁻¹ * n * c ∈ N.comap (MulAut.conj c).toMonoidHom := by
    rw [gn_mem_conj]
    have e : c * (c⁻¹ * n * c) * c⁻¹ = n := by group
    rw [e]
    exact hn
  rw [h, Subgroup.mem_bot] at h1
  have e : n = 1 := calc
    n = c * (c⁻¹ * n * c) * c⁻¹ := by group
    _ = 1 := by rw [h1]; group
  rw [e]
  exact Subgroup.one_mem _

theorem normalClosure_le_of_normalizedBy (hO : pPrimeCore 2 Q = ⊥) (hP : pCore 2 Q = ⊥)
    (R : Sylow 2 Q) (habel : ∀ r ∈ (R : Subgroup Q), ∀ s ∈ (R : Subgroup Q), r * s = s * r)
    (hfpf : ∀ g ∈ normalizer ((R : Subgroup Q) : Set Q),
      (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r) ∨
        (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r → r = 1))
    (N : Subgroup Q) (hNM : N ≤ normalClosure ((R : Subgroup Q) : Set Q))
    (hMN : normalClosure ((R : Subgroup Q) : Set Q) ≤ normalizer (N : Set Q)) (hN : N ≠ ⊥) :
    normalClosure ((R : Subgroup Q) : Set Q) ≤ N := by
  have hM : (normalClosure ((R : Subgroup Q) : Set Q)).Normal := inferInstance
  have key : ∀ c : Q, ∀ r ∈ (R : Subgroup Q), c * r * c⁻¹ ∈ N := fun c r hr =>
    (gn_mem_conj N c r).1 (sylow_le_of_normalizedBy hO hP R habel hfpf
      (N.comap (MulAut.conj c).toMonoidHom) (gn_conj_le hM hNM c)
      (gn_le_normalizer_conj hM hMN c) (gn_conj_ne_bot hN c) hr)
  refine (Subgroup.closure_le N).2 ?_
  intro a ha
  obtain ⟨b, hb, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 ha
  obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
  exact key c b hb

theorem normalClosure_simple (hO : pPrimeCore 2 Q = ⊥) (hP : pCore 2 Q = ⊥) (R : Sylow 2 Q)
    (hR1 : (R : Subgroup Q) ≠ ⊥)
    (habel : ∀ r ∈ (R : Subgroup Q), ∀ s ∈ (R : Subgroup Q), r * s = s * r)
    (hfpf : ∀ g ∈ normalizer ((R : Subgroup Q) : Set Q),
      (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r) ∨
        (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r → r = 1)) :
    IsSimpleGroup (normalClosure ((R : Subgroup Q) : Set Q)) ∧
      ∃ a b : normalClosure ((R : Subgroup Q) : Set Q), a * b ≠ b * a := by
  have hM : (normalClosure ((R : Subgroup Q) : Set Q)).Normal := inferInstance
  have hRM : (R : Subgroup Q) ≤ normalClosure ((R : Subgroup Q) : Set Q) :=
    Subgroup.le_normalClosure
  refine ⟨?_, ?_⟩
  · refine (Subgroup.isSimpleGroup_iff).2 ⟨?_, fun N hNM hNn => ?_⟩
    · intro h
      exact hR1 (le_bot_iff.1 (hRM.trans h.le))
    · have hMN : normalClosure ((R : Subgroup Q) : Set Q) ≤ normalizer (N : Set Q) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).1 hNn
      by_cases hN : N = ⊥
      · exact Or.inl hN
      · exact Or.inr (le_antisymm hNM
          (normalClosure_le_of_normalizedBy hO hP R habel hfpf N hNM hMN hN))
  · by_contra hcomm
    have hcomm' : ∀ a b : normalClosure ((R : Subgroup Q) : Set Q), a * b = b * a := by
      intro a b
      by_contra h
      exact hcomm ⟨a, b, h⟩
    have hMR : normalClosure ((R : Subgroup Q) : Set Q) ≤
        normalizer ((R : Subgroup Q) : Set Q) := by
      intro m hm
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (hcomm' ⟨s, hRM hs⟩ ⟨m, hm⟩)
    exact hR1 (eq_bot_of_two hP hM hRM hMR R.isPGroup')

end Local

end CFSG.OddStandard.ThmC.O2.Gor
