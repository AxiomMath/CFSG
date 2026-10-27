module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8LnModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Asm

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Final

theorem isSubnormal_trans' {G : Type*} [Group G] {H M K : Subgroup G}
    (h1 : CFSG.Open.IsSubnormal H M) (h2 : CFSG.Open.IsSubnormal M K) :
    CFSG.Open.IsSubnormal H K := by
  induction h1 with
  | refl => exact h2
  | step hle hn hsub ih => exact CFSG.Open.IsSubnormal.step hle hn (ih h2)

theorem datum_of_core {P G₀ : Type} [Group P] [Finite P] [Group G₀] [Finite G₀]
    (hZ : Subgroup.center P = ⊥) (A : Subgroup (MulAut P)) (hA : IsElemAbelian 3 A)
    (hnot : ¬ A ≤ innAutDerived P)
    (hout3 : Nat.card A ≤ 3 * Nat.card ↥(A ⊓ innAutDerived P))
    (hinner : ∀ a ∈ A ⊓ innAutDerived P, a ∈ (MulAut.conj : P →* MulAut P).range)
    (hout : ∀ a ∈ A, a ∉ (MulAut.conj : P →* MulAut P).range →
      ∀ E : Subgroup P, E ≤ fixSubgroup a → IsElemAbelian 3 E →
        CFSG.Open.pRank 3 E + 1 ≤ CFSG.Open.pRank 3 A)
    (r : ℕ) (E0 : Subgroup G₀) (hE0 : IsElemAbelian 3 E0) (hE0card : Nat.card E0 = 3 ^ r)
    (desc : ∀ b ∈ A, b ∉ innAutDerived P → ∃ ι : G₀ →* P, Function.Injective ι ∧
      (∀ v, b (ι v) = ι v) ∧ (∀ x : P, b x = x → ∀ v, x * ι v * x⁻¹ ∈ ι.range) ∧
      (∀ x : P, b x = x → x ^ 3 = 1 → x ∈ ι.range))
    (core : ∀ E : Subgroup G₀, IsElemAbelian 3 E → 3 ^ r ≤ Nat.card E →
      ∃ c ∈ E, c ≠ 1 ∧ ∃ L : Subgroup G₀, L ≤ Subgroup.centralizer ({c} : Set G₀) ∧
        CFSG.Open.IsSubnormal L (Subgroup.centralizer ({c} : Set G₀)) ∧
        CFSG.Open.IsQuasisimple L ∧ 3 ∣ Nat.card (L ⧸ Subgroup.center L)) :
    KD264F8Datum P A := by
  classical
  haveI := finite_mulAut' (P := P)
  obtain ⟨b, hbA, hbout⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨ι, hιinj, hιfix, hιnorm, hι3⟩ := desc b hbA hbout
  have hconjinj := conj_injective' hZ
  have hbnotinn : b ∉ (MulAut.conj : P →* MulAut P).range :=
    fun h => hbout (inner_le_innAutDerived _ h)
  have hbound : r + 1 ≤ CFSG.Open.pRank 3 A := by
    have hE0ab : IsElemAbelian 3 (E0.map ι) := isElemAbelian_map_gen ι hE0
    have hc : Nat.card (E0.map ι) = 3 ^ r := by
      rw [Subgroup.card_map_of_injective hιinj, hE0card]
    have h1 := hout b hbA hbnotinn (E0.map ι) (by
      rintro _ ⟨v, -, rfl⟩
      exact mem_fixSubgroup.2 (hιfix v)) hE0ab
    rwa [pRank_eq_of_card' Nat.prime_three hE0ab hc] at h1
  have hAcard := card_eq_pow_pRank hA
  let Ebar : Subgroup P := A.comap (MulAut.conj : P →* MulAut P)
  have hEbar_map : Ebar.map (MulAut.conj : P →* MulAut P) =
      (MulAut.conj : P →* MulAut P).range ⊓ A := Subgroup.map_comap_eq _ _
  have hA0le : A ⊓ innAutDerived P ≤ Ebar.map (MulAut.conj : P →* MulAut P) := by
    rw [hEbar_map]
    exact le_inf (hinner) inf_le_left
  have hcardEbar : 3 ^ r ≤ Nat.card Ebar := by
    have h1 := Subgroup.card_le_of_le hA0le
    rw [Subgroup.card_map_of_injective hconjinj] at h1
    have h2 : 3 ^ (r + 1) ≤ Nat.card A := by
      rw [hAcard]
      exact Nat.pow_le_pow_right (by norm_num) hbound
    have h3 : 3 ^ r * 3 ≤ 3 * Nat.card Ebar := by
      calc 3 ^ r * 3 = 3 ^ (r + 1) := by ring
        _ ≤ Nat.card A := h2
        _ ≤ 3 * Nat.card ↥(A ⊓ innAutDerived P) := hout3
        _ ≤ 3 * Nat.card Ebar := Nat.mul_le_mul_left _ h1
    omega
  have hEbar_ab : IsElemAbelian 3 Ebar := by
    refine isElemAbelian_of_map_injective _ hconjinj ?_
    exact isElemAbelian_of_le (by rw [hEbar_map]; exact inf_le_right) hA
  have hEbar_fix : ∀ x ∈ Ebar, b x = x := by
    intro x hx
    have hcomm : Commute b (MulAut.conj x) := kd264F8_commute hA hbA hx
    have h1 : MulAut.conj (b x) = MulAut.conj x := by
      rw [← mulAut_conj_conj, hcomm.eq]
      group
    exact hconjinj h1
  have hEbar_ι : Ebar ≤ ι.range := by
    intro x hx
    have hx3 : x ^ 3 = 1 := by
      apply hconjinj
      rw [map_pow, map_one]
      exact hA.2 _ hx
    exact hι3 x (hEbar_fix x hx) hx3
  let Et : Subgroup G₀ := Ebar.comap ι
  have hEt_map : Et.map ι = Ebar := Subgroup.map_comap_eq_self hEbar_ι
  have hEt_card : 3 ^ r ≤ Nat.card Et := by
    rw [← Subgroup.card_map_of_injective (K := Et) hιinj, hEt_map]
    exact hcardEbar
  have hEt_ab : IsElemAbelian 3 Et :=
    isElemAbelian_of_map_injective ι hιinj (by rw [hEt_map]; exact hEbar_ab)
  obtain ⟨ct, hctE, hct1, L, hLc, hLs, hLq, hLd⟩ := core Et hEt_ab hEt_card
  set x : P := ι ct with hx
  have hxE : x ∈ Ebar := by
    have : ι ct ∈ Et.map ι := Subgroup.mem_map_of_mem ι hctE
    rwa [hEt_map] at this
  have hcA : MulAut.conj x ∈ A := hxE
  have hfixc : ∀ g, g ∈ Subgroup.centralizer ({ct} : Set G₀) → MulAut.conj x (ι g) = ι g := by
    intro g hg
    have h1 : ct * g = g * ct := Subgroup.mem_centralizer_iff.1 hg ct (Set.mem_singleton _)
    have h2 : ct * g * ct⁻¹ = g := by rw [h1]; group
    rw [MulAut.conj_apply, hx, ← map_inv, ← map_mul, ← map_mul, h2]
  set M : Subgroup P := (Subgroup.centralizer ({ct} : Set G₀)).map ι with hM
  have hMb : M ≤ fixSubgroup b := by
    rintro _ ⟨g, -, rfl⟩
    exact mem_fixSubgroup.2 (hιfix g)
  have hMc : M ≤ fixSubgroup (MulAut.conj x) := by
    rintro _ ⟨g, hg, rfl⟩
    exact mem_fixSubgroup.2 (hfixc g hg)
  have hMT := kd264F8_le_fixSubgroup_iInf hMb hMc
  refine ⟨b, hbA, MulAut.conj x, hcA, hbout, inner_le_innAutDerived _ ⟨x, rfl⟩, ?_, L.map ι,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hct1
    apply hιinj
    rw [map_one]
    exact hconjinj (h.trans (map_one _).symm)
  · rintro _ ⟨l, hl, rfl⟩
    exact mem_fixSubgroup.2 (hιfix l)
  · rintro _ ⟨l, hl, rfl⟩
    exact mem_fixSubgroup.2 (hfixc l (hLc hl))
  ·
    have hHM : CFSG.Open.IsSubnormal (L.map ι) M := hLs.map ι
    have hMTn : (M.subgroupOf (⨅ f ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (MulAut.conj x),
        fixSubgroup f)).Normal := by
      constructor
      intro n hn t
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨g, hg, hgn⟩ := hn
      have ht := t.2
      have htb : b (t : P) = t := by
        have := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ht b)
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
        exact mem_fixSubgroup.1 this
      have htc : MulAut.conj x (t : P) = t := by
        have := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ht (MulAut.conj x))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        exact mem_fixSubgroup.1 this
      obtain ⟨v, hv⟩ := hιnorm t htb g
      have hvc : v ∈ Subgroup.centralizer ({ct} : Set G₀) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        apply hιinj
        have h1 : MulAut.conj x (ι v) = ι v := by
          rw [hv, map_mul, map_mul, map_inv, htc, hfixc g hg]
        rw [MulAut.conj_apply, hx] at h1
        rw [map_mul, map_mul]
        have h2 : ι ct * ι v * (ι ct)⁻¹ = ι v := h1
        calc ι ct * ι v = ι ct * ι v * (ι ct)⁻¹ * ι ct := by group
          _ = ι v * ι ct := by rw [h2]
      refine ⟨v, hvc, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hgn, ← hv]
    have hMsub : CFSG.Open.IsSubnormal M (⨅ f ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (MulAut.conj x),
        fixSubgroup f) := CFSG.Open.IsSubnormal.step hMT hMTn (CFSG.Open.IsSubnormal.refl _)
    exact isSubnormal_trans' hHM hMsub
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (L.equivMapOfInjective ι hιinj) hLq
  · rw [← card_quotient_center_of_equiv (L.equivMapOfInjective ι hιinj)]
    exact hLd

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Asm

end
