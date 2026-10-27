module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36P
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32E
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSwapA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem t_mem_coreActionKernel_of_sup (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) : t ∈ UnbalancedLayer.coreActionKernel M := by
  have hCt := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    hCt (mem_centralizer_singleton_iff.mpr rfl)
  exact mem_coreActionKernel_of_sup_centralizer (hHN htH) S.pair.1.2.1 hsup

theorem fixedLayer_eq_of_sup (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) : GSLit.fixedLayer M (zpowers t) = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have htK := S.t_mem_coreActionKernel_of_sup h33 h35 hT13 hML hSch hHN hsup
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hMpc).2.2
  have hMsub : (M.subgroupOf H).IsSubnormal := hMpc.choose_spec.2.1
  have hE : zpowers t ≤ UnbalancedLayer.coreActionKernel M := zpowers_le.mpr htK
  have hE2 : IsPGroup 2 (zpowers t) := isPGroup_zpowers_of_mul_self ht2
  have hEH : zpowers t ≤ H := zpowers_le.mpr htH
  have hcen : H ⊓ centralizer ((zpowers t : Subgroup X) : Set X) = centralizer ({t} : Set X) := by
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    exact inf_eq_right.mpr hCt
  have hpc := GSLit.fixedLayer_isPComponent hMH hMsub hEH hE hE2 hMq
  rw [hcen] at hpc
  have hle := GSLit.fixedLayer_le_inf M (zpowers t)
  have hLM : GSLit.fixedLayer M (zpowers t) ≤ M := hle.trans inf_le_left
  have hLC : GSLit.fixedLayer M (zpowers t) ≤ centralizer ({t} : Set X) := by
    have h1 := hle.trans inf_le_right
    rwa [UnbalancedLayer.centralizer_zpowers_eq] at h1
  obtain ⟨hsupL, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hE hE2
  obtain ⟨θL, -⟩ := exists_coreQuot_of_sup hLM hsupL θ
  have hCt' : centralizer ((zpowers t : Subgroup X) : Set X) = centralizer ({t} : Set X) :=
    UnbalancedLayer.centralizer_zpowers_eq t
  have hT1 : zpowers t ≠ ⊥ := by
    intro h
    have h1 := S.pair.1.1
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at h1
    exact absurd h1 (by decide)
  have hL₁ : FooteLit.IsTwoComponentIn (GSLit.fixedLayer M (zpowers t))
      (centralizer ((zpowers t : Subgroup X) : Set X)) := by
    rw [hCt']
    exact ⟨hLC, hpc⟩
  have hL₂ : FooteLit.IsTwoComponentIn J (centralizer ((zpowers t : Subgroup X) : Set X)) := by
    rw [hCt']
    exact ⟨S.pair.1.2.1, S.pair.1.2.2.1⟩
  exact Sol78H.eq_of_isTwoComponentIn_centralizer_alt hT13 hML hSch S.nonab S.kProper S.unbal
    S.notU S.pair.2.1 S.pair.2.2.1 ⟨t, J, S.pair.1⟩ S.pair.2.2.2.1 hT1 hE2 hL₁ hL₂ ⟨θL⟩ ⟨e⟩

theorem layer_facts_of_sup (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {Q : Subgroup X}
    (hQH : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hQK : Q ≤ UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q) (htQ : t ∈ Q) :
    GSLit.fixedLayer M Q ≤ J ∧ GSLit.fixedLayer M Q ≤ centralizer (Q : Set X) ∧
      IsPComponent 2 ((GSLit.fixedLayer M Q).subgroupOf (centralizer (Q : Set X))) ∧
      ∃ θL : ↥(GSLit.fixedLayer M Q) ⧸ pPrimeCore 2 ↥(GSLit.fixedLayer M Q) ≃*
          alternatingGroup (Fin n),
        ∀ (x : ↥(GSLit.fixedLayer M Q)) (hx : (x : X) ∈ J),
          θL (x : ↥(GSLit.fixedLayer M Q) ⧸ pPrimeCore 2 ↥(GSLit.fixedLayer M Q)) =
            e ((⟨x, hx⟩ : J) : J ⧸ pPrimeCore 2 J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hMpc).2.2
  have hMsub : (M.subgroupOf H).IsSubnormal := hMpc.choose_spec.2.1
  have hJeq := S.fixedLayer_eq_of_sup h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup
  have hCQ : centralizer (Q : Set X) ≤ H :=
    (centralizer_le (Set.singleton_subset_iff.mpr htQ)).trans hCt
  obtain ⟨hLJ, hsupJ⟩ := GSLit.fixedLayer_nested hMq hQK hQ2 (zpowers_le.mpr htQ)
  rw [hJeq] at hLJ hsupJ
  obtain ⟨θL, hθL⟩ := exists_coreQuot_of_sup hLJ hsupJ e
  have hpc := GSLit.fixedLayer_isPComponent hMH hMsub hQH hQK hQ2 hMq
  rw [inf_eq_right.mpr hCQ] at hpc
  exact ⟨hLJ, (GSLit.fixedLayer_le_inf M Q).trans inf_le_right, hpc, θL, fun x _ => hθL x⟩

theorem normalizer_le_of_sup (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {Q : Subgroup X}
    (hQH : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hQK : Q ≤ UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q) (htQ : t ∈ Q) :
    normalizer (Q : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have hJH : J ≤ H := S.le_normalizer_completion h33 h35
  set L := GSLit.fixedLayer M Q with hLdef
  obtain ⟨hLJ, hLC, hpc, θL, hθL⟩ :=
    S.layer_facts_of_sup h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup hQH hQK hQ2 htQ
  have hQ1 : Q ≠ ⊥ := by
    intro h
    have h1 := htQ
    rw [h, mem_bot] at h1
    have h2 := S.pair.1.1
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hNL : normalizer (Q : Set X) ≤ normalizer (L : Set X) :=
    Sol78H.normalizer_le_normalizer_of_isTwoComponentIn_centralizer_alt hT13 hML hSch S.nonab
      S.kProper S.unbal S.notU S.pair.2.1 S.pair.2.2.1 ⟨t, J, S.pair.1⟩ S.pair.2.2.2.1 hQ1 hQ2
      ⟨hLC, hpc⟩ ⟨θL⟩
  obtain ⟨F, hFL, hFk, DF, hDF, hFs⟩ := exists_four_subgroup_of_alt L (by omega) θL
  have hFJ : F ≤ J := hFL.trans hLJ
  have hFsJ : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω := by
    intro x hx ω hω
    have h1 := hFs ⟨x, hFL hx⟩ hx ω hω
    rwa [hθL ⟨x, hFL hx⟩ x.2] at h1
  have hFW := S.completion_eq_of_four h33 h35 hFJ hFk hDF hFsJ
  have hFH : normalizer (F : Set X) ≤ H := by
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  obtain ⟨hF4, hF2⟩ := card_sq_of_klein hFk
  have hFsq : ∀ x ∈ F, x * x = 1 := fun x hx => by rw [← sq]; exact hF2 x hx
  intro y hy
  have hyL := hNL hy
  obtain ⟨hFyL, D', hD', hFys⟩ := exists_support_conj (by omega) θL hFL hDF hFs hyL
  have hFy4 : Nat.card (F.map (MulAut.conj y).toMonoidHom) = 4 := by
    rw [card_map_of_injective (MulAut.conj y).injective, hF4]
  have hFysq : ∀ x ∈ F.map (MulAut.conj y).toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hFsq x hx, map_one]
  obtain ⟨j, hjL, hj⟩ := exists_conj_four_subgroup (by omega) θL hFyL hFL hFy4 hF4 hFysq hFsq
    hD' hDF hFys hFs
  have hjy : j * y ∈ normalizer (F : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    calc F.map (MulAut.conj (j * y)).toMonoidHom =
        (F.map (MulAut.conj y).toMonoidHom).map (MulAut.conj j).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          ext z
          simp [MulAut.conj_apply, mul_assoc]
      _ = F := hj
  have h1 := mul_mem (inv_mem (hJH (hLJ hjL))) (hFH hjy)
  rwa [inv_mul_cancel_left] at h1

end Sig36

end CFSG.ComponentClassification.SolMax
