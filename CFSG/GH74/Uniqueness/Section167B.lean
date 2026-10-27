module

public import CFSG.GH74.Uniqueness.Section167Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem conjugate_pow_eq_self {x : X} {a : Subgroup X} (h : conjugate a x = a) (n : ℕ) :
    conjugate a (x ^ n) = a := by
  induction n with
  | zero => rw [pow_zero, conjugate_one]
  | succ n ih => rw [pow_succ, ← conjugate_conjugate, ih, h]

theorem exists_mem_conjugate_of_normal_of_ne (hD : DoublyTransitive M) {p : ℕ} (hp : p.Prime)
    {W : Subgroup X} (hW : IsMaxFixingThree M p W) {K₀ : Subgroup X}
    (hK₀N : K₀ ≤ normalizer (W : Set X)) (hK₀n : normalizer (W : Set X) ≤ normalizer (K₀ : Set X))
    {k₀ : X} (hk₀ : k₀ ∈ K₀) {a : Subgroup X} (ha : a ∈ omegaFix M (W : Set X))
    (hne : conjugate a k₀ ≠ a) :
    ∀ x ∈ omegaFix M (W : Set X), ∃ g ∈ K₀, conjugate a g = x := by
  intro x hx
  by_cases hxa : x = a
  · exact ⟨1, K₀.one_mem, by rw [conjugate_one, hxa]⟩
  · have hak : conjugate a k₀ ∈ omegaFix M (W : Set X) :=
      conjugate_mem_omegaFix_of_mem_normalizer (hK₀N hk₀) ha
    obtain ⟨n, hn, hn1, hn2⟩ := IsMaxFixingThree.twoTransitive hD hp hW a ha (conjugate a k₀) hak
      (Ne.symm hne) a ha x hx (Ne.symm hxa)
    have hn' : n⁻¹ ∈ normalizer (W : Set X) := (normalizer (W : Set X)).inv_mem hn
    have hg : n⁻¹ * k₀ * n ∈ K₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (hK₀n hn') k₀).mp hk₀
      simpa using this
    refine ⟨n⁻¹ * k₀ * n, hg, ?_⟩
    have hna : conjugate a n⁻¹ = a :=
      calc conjugate a n⁻¹ = conjugate (conjugate a n) n⁻¹ := by rw [hn1]
        _ = a := conjugate_conjugate_inv a n
    rw [conjugate_mul_mul, hna, hn2]

theorem ZDSetup.lemma167_stepB
    (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {W : Subgroup X} (hW : IsMaxFixingThree M p W) :
    ∃ s ∈ Z, s ∈ normalizer (W : Set X) := by
  classical
  obtain ⟨c⟩ := S.nonempty_conf16
  obtain ⟨-, -, -, -, he⟩ := h166 c
  by_contra hno
  push Not at hno
  have : Fact p.Prime := ⟨hp⟩
  have hdt : DoublyTransitive M := S.theorem4.1
  have h3 := hW.1.2
  obtain ⟨β, γ, hβ, hγ, hβγ⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp
    (by omega : 1 < (omegaFix M (W : Set X)).ncard)
  have hβΩ : β ∈ omega M := hβ.1
  have hγΩ : γ ∈ omega M := hγ.1
  rcases S.prodDisc.sylow_or_exists_larger hp hp2 hW hβ hγ hβγ with
    hsyl | ⟨R, hWR, hRsyl, hΩR, hRN⟩
  · obtain ⟨s, hsZ, hsN, -⟩ := S.prodDisc.exists_swap_of_isSylowOf S.invariant hp hp2 hβΩ hγΩ
      hβγ hsyl
    exact hno s hsZ hsN
  ·
    have hzh : zHull Z (normalizer (W : Set X)) = ⊥ := by
      have hempty : Z ∩ ((normalizer (W : Set X) : Subgroup X) : Set X) = ∅ := by
        ext y
        simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false,
          not_and]
        exact fun hyZ hyN => hno y hyZ hyN
      rw [zHull, hempty, Subgroup.closure_empty]
    obtain ⟨⟨O, hON, hOn, hOodd, k, hk⟩, -⟩ := he (normalizer (W : Set X)) hzh
    have hOnorm : normalizer (W : Set X) ≤ normalizer (O : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hON).mp hOn
    have hRN₁ : R ≤ normalizer (W : Set X) := hRN.le
    have hRO : R ≤ O := le_of_isPGroup_of_normal_complement hp hp2 hON hOn hk hRN.isPGroup hRN₁
    have hRβ : R ≤ β := by
      have : β ∈ omegaFix M (R : Set X) := by rw [hΩR]; exact Or.inl rfl
      exact (S.prodDisc.mem_omegaFix_iff.mp this).2
    have hRγ : R ≤ γ := by
      have : γ ∈ omegaFix M (R : Set X) := by rw [hΩR]; exact Or.inr rfl
      exact (S.prodDisc.mem_omegaFix_iff.mp this).2
    by_cases hOtriv : ∀ k₀ ∈ O, ∀ a ∈ omegaFix M (W : Set X), conjugate a k₀ = a
    ·
      have hsub : omegaFix M (W : Set X) ⊆ {β, γ} := by
        intro ω hω
        have : ω ∈ omegaFix M (R : Set X) :=
          ⟨hω.1, fun g hg => hOtriv g (hRO hg) ω hω⟩
        rw [hΩR] at this
        exact this
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_pair hβγ] at this
      omega
    · push Not at hOtriv
      obtain ⟨k₀, hk₀, a, ha, hne⟩ := hOtriv
      have htrans := exists_mem_conjugate_of_normal_of_ne hdt hp hW hON hOnorm hk₀ ha hne
      obtain ⟨g₁, hg₁, hg₁e⟩ := htrans β hβ
      obtain ⟨g₂, hg₂, hg₂e⟩ := htrans γ hγ
      set g : X := g₁⁻¹ * g₂ with hgdef
      have hgO : g ∈ O := O.mul_mem (O.inv_mem hg₁) hg₂
      have hgβ : conjugate β g = γ := by
        have hβa : conjugate β g₁⁻¹ = a := by
          rw [← hg₁e, conjugate_conjugate, mul_inv_cancel, conjugate_one]
        rw [hgdef, ← conjugate_conjugate, hβa, hg₂e]
      have hRO' : ABGLocalTools.IsSylowOf p R O := hRN.of_le hRO hON
      have hRγ' : ABGLocalTools.IsSylowOf p R (O ⊓ γ) :=
        hRO'.of_le (le_inf hRO hRγ) inf_le_left
      have hcS : ABGLocalTools.IsSylowOf p (conjugate R g) O := isSylowOf_conjugate_of_mem hRO' hgO
      have hcle : conjugate R g ≤ γ := by
        have := conjugate_mono hRβ g
        rwa [hgβ] at this
      have hcS' : ABGLocalTools.IsSylowOf p (conjugate R g) (O ⊓ γ) :=
        hcS.of_le (le_inf hcS.le hcle) inf_le_left
      obtain ⟨h₀, hh₀, hh₀R⟩ := exists_conj_of_isSylowOf hcS' hRγ'
      have hh₀O : h₀ ∈ O := (Subgroup.mem_inf.mp hh₀).1
      have hh₀γ : h₀ ∈ γ := (Subgroup.mem_inf.mp hh₀).2
      set x : X := g * h₀ with hxdef
      have hxO : x ∈ O := O.mul_mem hgO hh₀O
      have hxR : conjugate R x = R := by
        rw [hxdef, ← conjugate_conjugate]
        exact hh₀R
      have hxβ : conjugate β x = γ := by
        rw [hxdef, ← conjugate_conjugate, hgβ]
        exact (S.prodDisc.conjugate_eq_iff_mem hγΩ).mpr hh₀γ
      have hxN : x ∈ normalizer (R : Set X) := conjugate_eq_iff_mem_normalizer.mp hxR
      have hγΩR : γ ∈ omegaFix M (R : Set X) := by
        rw [hΩR]
        exact Or.inr rfl
      have hγx := conjugate_mem_omegaFix_of_mem_normalizer hxN hγΩR
      rw [hΩR] at hγx
      have hxγ : conjugate γ x = β := by
        rcases hγx with h | h
        · exact h
        · exact absurd (conjugate_injective x (hxβ.trans (Set.mem_singleton_iff.mp h).symm)) hβγ
      have hev := even_orderOf_of_swap hβγ hxβ hxγ
      have hodd : Odd (orderOf x) := Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O hxO)
      exact (Nat.not_even_iff_odd.mpr hodd) hev

theorem ZDSetup.lemma167_stepC
    (S : ZDSetup X Z M) {p : ℕ} (hp : p.Prime) {W : Subgroup X}
    (hW : IsMaxFixingThree M p W) {s : X} (hs : s ∈ Z) (hsN : s ∈ normalizer (W : Set X))
    (hfix : ∀ β ∈ omegaFix M (W : Set X), conjugate β s ≠ β)
    (hZst : IsZStarIn (normalizer (W : Set X)) s) : False := by
  classical
  have hdt : DoublyTransitive M := S.theorem4.1
  have h3 := hW.1.2
  have hs2 : s * s = 1 := S.invariant.mul_self_eq_one hs
  have hs2' : orderOf s = 2 := S.invariant.1 s hs
  obtain ⟨-, K₀, hK₀N, hK₀n, hK₀odd, hK₀⟩ := hZst
  have hK₀norm : normalizer (W : Set X) ≤ normalizer (K₀ : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀N).mp hK₀n
  have hsK₀ : s ∉ K₀ := by
    intro hsK
    have := Subgroup.orderOf_dvd_natCard K₀ hsK
    rw [hs2'] at this
    exact (Nat.not_even_iff_odd.mpr hK₀odd) (even_iff_two_dvd.mpr this)
  have hsnorm : s ∈ normalizer (K₀ : Set X) := hK₀norm hsN
  have htriv : ∀ k ∈ K₀, ∀ a ∈ omegaFix M (W : Set X), conjugate a k = a := by
    by_contra hnot
    push Not at hnot
    obtain ⟨k₀, hk₀, a, ha, hne⟩ := hnot
    have htrans := exists_mem_conjugate_of_normal_of_ne hdt hp hW hK₀N hK₀norm hk₀ ha hne
    have hb : conjugate a s ∈ omegaFix M (W : Set X) :=
      conjugate_mem_omegaFix_of_mem_normalizer hsN ha
    obtain ⟨k, hk, hkb⟩ := htrans _ hb
    set x : X := k * s with hx
    have hxa : conjugate a x = a := by
      rw [hx, ← conjugate_conjugate, hkb, conjugate_conjugate, hs2, conjugate_one]
    have hxK : x * s⁻¹ ∈ K₀ := by
      rw [hx]
      simpa using hk
    have hsk : s * k * s⁻¹ ∈ K₀ := (Subgroup.mem_normalizer_iff.mp hsnorm k).mp hk
    have hx2 : x * x ∈ K₀ := by
      have e : x * x = k * (s * k * s⁻¹) := by
        calc x * x = k * (s * k * s⁻¹) * (s * s) := by rw [hx]; group
          _ = k * (s * k * s⁻¹) := by rw [hs2, mul_one]
      rw [e]
      exact K₀.mul_mem hk hsk
    have hmodd : Odd (orderOf (x * x)) :=
      Odd.of_dvd_nat hK₀odd (Subgroup.orderOf_dvd_natCard K₀ hx2)
    obtain ⟨l, hl⟩ := hmodd
    set j : X := x ^ orderOf (x * x) with hj
    have hjj : j * j = 1 := by
      have : j * j = (x * x) ^ orderOf (x * x) := by
        rw [hj, ← pow_add, ← two_mul, pow_mul, sq]
      rw [this, pow_orderOf_eq_one]
    have hjs : j * s⁻¹ ∈ K₀ := by
      have e : j * s⁻¹ = (x * x) ^ l * (x * s⁻¹) := by
        rw [hj, hl, pow_succ, pow_mul, sq]
        group
      rw [e]
      exact K₀.mul_mem (K₀.pow_mem hx2 l) hxK
    have hj1 : j ≠ 1 := by
      intro h1
      rw [h1, one_mul] at hjs
      exact hsK₀ (by simpa using K₀.inv_mem hjs)
    have hj2 : orderOf j = 2 := orderOf_eq_prime (by rw [sq]; exact hjj) hj1
    have hcos := (CFSG.OddInversion.odd_inversion_coset_count hK₀odd hsnorm hsK₀ hs2').1
    have hjmem : j ∈ {v : X | v * s⁻¹ ∈ K₀ ∧ orderOf v = 2} := ⟨hjs, hj2⟩
    rw [hcos] at hjmem
    obtain ⟨d, hd, hjd⟩ := hjmem
    have hja : conjugate a j = a := conjugate_pow_eq_self hxa _
    rw [hjd, conjugate_mul_mul] at hja
    have hfixa : conjugate (conjugate a d⁻¹) s = conjugate a d⁻¹ := by
      have := congrArg (fun A => conjugate A d⁻¹) hja
      simpa [conjugate_conjugate] using this
    have ha' : conjugate a d⁻¹ ∈ omegaFix M (W : Set X) :=
      conjugate_mem_omegaFix_of_mem_normalizer (hK₀N (K₀.inv_mem hd)) ha
    exact hfix _ ha' hfixa
  have hcomm : ∀ n ∈ normalizer (W : Set X), ∀ a ∈ omegaFix M (W : Set X),
      conjugate (conjugate a s) n = conjugate (conjugate a n) s := by
    intro n hn a ha
    have hc' : s * n * s⁻¹ * n⁻¹ ∈ K₀ := by
      have h1 := hK₀ n hn
      have e : s * n * s⁻¹ * n⁻¹ = (n * s * n⁻¹ * s⁻¹)⁻¹ := by group
      rw [e]
      exact K₀.inv_mem h1
    have hsn : s * n = (s * n * s⁻¹ * n⁻¹) * (n * s) := by group
    rw [conjugate_conjugate, conjugate_conjugate, hsn, ← conjugate_conjugate,
      htriv _ hc' a ha]
  obtain ⟨a, ha⟩ : (omegaFix M (W : Set X)).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  have hb : conjugate a s ∈ omegaFix M (W : Set X) :=
    conjugate_mem_omegaFix_of_mem_normalizer hsN ha
  have hba : conjugate a s ≠ a := hfix a ha
  obtain ⟨x, hx, hxa, hxb⟩ : ∃ x ∈ omegaFix M (W : Set X), x ≠ a ∧ x ≠ conjugate a s := by
    by_contra hall
    push Not at hall
    have hsub : omegaFix M (W : Set X) ⊆ {a, conjugate a s} := by
      intro y hy
      by_cases hya : y = a
      · exact Or.inl hya
      · exact Or.inr (hall y hy hya)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hba.symm] at this
    omega
  obtain ⟨n, hn, hn1, hn2⟩ := IsMaxFixingThree.twoTransitive hdt hp hW a ha (conjugate a s) hb
    hba.symm a ha x hx hxa.symm
  apply hxb
  rw [← hn2, hcomm n hn a ha, hn1]

end CFSG.GH74.Uniqueness
