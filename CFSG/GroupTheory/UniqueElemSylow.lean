module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

open scoped Pointwise

namespace CFSG.GroupTheory

@[expose] def UniqueElemSylow (p k : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow p G, ∃! A : Subgroup G, A ≤ P ∧ CFSG.Open.IsElemAbelian p A ∧ Nat.card A = p ^ k

variable {p k : ℕ} {G H : Type*} [Group G] [Group H]

private theorem UniqueElemSylow.disjoint_zpowers_of_card [Finite G] [Fact p.Prime] {E : Subgroup G}
    {y : G} (hy : y ∉ E) (hcard : Nat.card (Subgroup.zpowers y) = p) :
    Disjoint E (Subgroup.zpowers y) := by
  rw [disjoint_iff]
  have hdvd : Nat.card (E ⊓ Subgroup.zpowers y : Subgroup G) ∣ p := by
    have h := Subgroup.card_dvd_of_le (inf_le_right : E ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers y)
    rwa [hcard] at h
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp'
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : E ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard, hp'])
    exact hy (heq.ge (Subgroup.mem_zpowers y)).1

private theorem UniqueElemSylow.zpowers_le_normalizer_of_commute {E : Subgroup G} {y : G}
    (hcomm : ∀ a ∈ E, a * y = y * a) :
    Subgroup.zpowers y ≤ Subgroup.normalizer (E : Set G) := by
  have hcent : Subgroup.zpowers y ≤ Subgroup.centralizer (E : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hcomm a ha) m).eq
  exact hcent.trans (Subgroup.centralizer_le_normalizer (E : Set G))

private theorem UniqueElemSylow.exists_pair_card_pow_of_lt [Finite G] [Fact p.Prime]
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) {n : ℕ} (hn : Nat.card E = p ^ n)
    (hk : 1 ≤ k) (hkltn : k < n) :
    ∃ H K : Subgroup G, H ≤ E ∧ K ≤ E ∧ CFSG.Open.IsElemAbelian p H ∧
      CFSG.Open.IsElemAbelian p K ∧ Nat.card H = p ^ k ∧ Nat.card K = p ^ k ∧ H ≠ K := by
  have hp := (Fact.out : p.Prime)
  have hdvdE : p ^ k ∣ Nat.card E := by
    rw [hn]
    exact Nat.pow_dvd_pow p hkltn.le
  obtain ⟨H, hHcard, -, hHE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (p := p) (n := k)
    (H := ⊥) (L := E) hp (by simp) hdvdE bot_le
  have hdvdH : p ^ (k - 1) ∣ Nat.card H := by
    rw [hHcard]
    exact Nat.pow_dvd_pow p (Nat.sub_le k 1)
  obtain ⟨H₁, hH₁card, -, hH₁H⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (p := p)
    (n := k - 1) (H := ⊥) (L := H) hp (by simp) hdvdH bot_le
  have hHne : H ≠ E := by
    intro hHEeq
    have hpow : p ^ k = p ^ n := by rw [← hHcard, hHEeq, hn]
    exact (ne_of_lt ((Nat.pow_lt_pow_iff_right hp.one_lt).mpr hkltn)) hpow
  obtain ⟨y, hyE, hyH⟩ := Set.not_subset.mp (lt_of_le_of_ne hHE hHne).2
  have hy1 : y ≠ 1 := fun h1 => hyH (h1 ▸ H.one_mem)
  have hyord : orderOf y = p := orderOf_eq_prime (hE.2 y hyE) hy1
  have hWcard : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hyord]
  have hdisj : Disjoint H₁ (Subgroup.zpowers y) :=
    UniqueElemSylow.disjoint_zpowers_of_card (fun hy => hyH (hH₁H hy)) hWcard
  have hH₁ea : CFSG.Open.IsElemAbelian p H₁ := hE.mono (hH₁H.trans hHE)
  have hWea : CFSG.Open.IsElemAbelian p (Subgroup.zpowers y) :=
    CFSG.Open.isElemAbelian_zpowers (hE.2 y hyE)
  have hcomm_y : ∀ a ∈ H₁, a * y = y * a :=
    fun a ha => hE.comm (hHE (hH₁H ha)) hyE
  have hWnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (H₁ : Set G) :=
    UniqueElemSylow.zpowers_le_normalizer_of_commute hcomm_y
  have hcomm : ∀ a ∈ H₁, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hcomm_y a ha) m).eq
  refine ⟨H, H₁ ⊔ Subgroup.zpowers y, hHE, ?_, hE.mono hHE, ?_, hHcard, ?_, ?_⟩
  · exact sup_le (hH₁H.trans hHE) (Subgroup.zpowers_le.mpr hyE)
  · exact hH₁ea.sup_of_commute hWea hcomm
  · rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer H₁
      (Subgroup.zpowers y) hWnorm hdisj, hH₁card, hWcard, ← pow_succ, Nat.sub_add_cancel hk]
  · intro heq
    have hyK : y ∈ H₁ ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    exact hyH (heq.symm ▸ hyK)

theorem UniqueElemSylow.exists_conj_eq [Finite G] [Fact p.Prime] (h : UniqueElemSylow p k G)
    {A B : Subgroup G} (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ k)
    (hB : CFSG.Open.IsElemAbelian p B) (hBc : Nat.card B = p ^ k) :
    ∃ g : G, B = A.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨PA, hAPA⟩ := hA.isPGroup.exists_le_sylow
  obtain ⟨PB, hBPB⟩ := hB.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PA PB
  have hA'le : A.map (MulAut.conj g).toMonoidHom ≤ PB := by
    have hsmul : (MulAut.conj g • (PA : Subgroup G)) =
        (PA : Subgroup G).map (MulAut.conj g).toMonoidHom := rfl
    rw [← hg, Sylow.coe_subgroup_smul, hsmul]
    exact Subgroup.map_mono hAPA
  obtain ⟨E, hEQ, huniq⟩ := h PB
  have hBQ : B ≤ PB ∧ CFSG.Open.IsElemAbelian p B ∧ Nat.card B = p ^ k := ⟨hBPB, hB, hBc⟩
  have hAQ : A.map (MulAut.conj g).toMonoidHom ≤ PB ∧
      CFSG.Open.IsElemAbelian p (A.map (MulAut.conj g).toMonoidHom) ∧
      Nat.card (A.map (MulAut.conj g).toMonoidHom) = p ^ k :=
    ⟨hA'le, hA.map _, (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hAc⟩
  exact ⟨g, (huniq B hBQ).trans (huniq (A.map (MulAut.conj g).toMonoidHom) hAQ).symm⟩

theorem UniqueElemSylow.pRank_le [Finite G] [Fact p.Prime] (hk : 1 ≤ k)
    (h : UniqueElemSylow p k G) : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ k := by
  have hp := (Fact.out : p.Prime)
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E _ hE
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := hE.isPGroup.exists_card_eq
  have hkltn : k < n := by
    rw [hn] at hlt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  obtain ⟨H, K, hHE, hKE, hHea, hKea, hHcard, hKcard, hHK⟩ :=
    UniqueElemSylow.exists_pair_card_pow_of_lt hE hn hk hkltn
  obtain ⟨P, hEP⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨E₀, hE₀Q, huniq⟩ := h P
  exact hHK ((huniq H ⟨hHE.trans hEP, hHea, hHcard⟩).trans
    (huniq K ⟨hKE.trans hEP, hKea, hKcard⟩).symm)

theorem UniqueElemSylow.exists_conj_mem [Finite G] [Fact p.Prime] (hk : 1 ≤ k)
    (h : UniqueElemSylow p k G)
    (hrank : ∀ x : G, orderOf x = p → k ≤ CFSG.Open.pRank p (Subgroup.centralizer {x}))
    {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ k)
    {x : G} (hx : orderOf x = p) : ∃ g : G, g * x * g⁻¹ ∈ A := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨E₀, hE₀C, hE₀ea, hE₀card⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.centralizer ({x} : Set G))
  have hmeq : CFSG.Open.pRank p (Subgroup.centralizer ({x} : Set G)) = k :=
    le_antisymm (le_trans (CFSG.SectionRank.pRank_mono hp.one_lt le_top)
      (UniqueElemSylow.pRank_le hk h)) (hrank x hx)
  have hE₀card' : Nat.card E₀ = p ^ k := by rw [hE₀card, hmeq]
  have hxE₀ : x ∈ E₀ := by
    by_contra hxE₀
    have hxpow : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hWcard : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
    have hdisj : Disjoint E₀ (Subgroup.zpowers x) :=
      UniqueElemSylow.disjoint_zpowers_of_card hxE₀ hWcard
    have hcomm_y : ∀ a ∈ E₀, a * x = x * a := fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (hE₀C ha) x (Set.mem_singleton x)).symm
    have hWnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (E₀ : Set G) :=
      UniqueElemSylow.zpowers_le_normalizer_of_commute hcomm_y
    have hcomm : ∀ a ∈ E₀, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
      intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_right (hcomm_y a ha) m).eq
    have hKea : CFSG.Open.IsElemAbelian p (E₀ ⊔ Subgroup.zpowers x) :=
      hE₀ea.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hxpow) hcomm
    have hKcard : Nat.card (E₀ ⊔ Subgroup.zpowers x : Subgroup G) = p ^ (k + 1) := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E₀
        (Subgroup.zpowers x) hWnorm hdisj, hE₀card', hWcard, ← pow_succ]
    have hle : k + 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_top hKea hKcard
    exact absurd (UniqueElemSylow.pRank_le hk h) (by omega)
  obtain ⟨g, hg⟩ := UniqueElemSylow.exists_conj_eq h hE₀ea hE₀card' hA hAc
  refine ⟨g, ?_⟩
  rw [hg]
  exact ⟨x, hxE₀, by simp [MulAut.conj_apply]⟩

theorem UniqueElemSylow.of_mulEquiv (e : G ≃* H) (h : UniqueElemSylow p k G) :
    UniqueElemSylow p k H := by
  intro Q
  let P : Sylow p G := Q.comapOfInjective e.toMonoidHom e.injective (by simp)
  have hPcoe : (P : Subgroup G) = Q.comap e.toMonoidHom := by simp [P]
  obtain ⟨E, hEQ, huniq⟩ := h P
  refine ⟨E.map e.toMonoidHom, ?_, ?_⟩
  · refine ⟨?_, hEQ.2.1.map e.toMonoidHom, ?_⟩
    · rw [Subgroup.map_le_iff_le_comap, ← hPcoe]
      exact hEQ.1
    · exact (Subgroup.card_map_of_injective e.injective).trans hEQ.2.2
  · intro A hA
    have hA'le : A.comap e.toMonoidHom ≤ P := by
      rw [hPcoe]
      exact fun a ha => hA.1 ha
    have hA'ea : CFSG.Open.IsElemAbelian p (A.comap e.toMonoidHom) := hA.2.1.comap e.injective
    have hA'card : Nat.card (A.comap e.toMonoidHom) = p ^ k := by
      rw [Subgroup.comap_equiv_eq_map_symm' e A, Subgroup.card_map_of_injective e.symm.injective]
      exact hA.2.2
    have hA'eq : A.comap e.toMonoidHom = E := huniq _ ⟨hA'le, hA'ea, hA'card⟩
    calc A = (A.comap e.toMonoidHom).map e.toMonoidHom :=
          (Subgroup.map_comap_eq_self_of_surjective e.surjective A).symm
      _ = E.map e.toMonoidHom := by rw [hA'eq]

theorem UniqueElemSylow.of_forall_sylow_mulEquiv [Finite G] {M : Type*} [Group M]
    (hM : ∃! A : Subgroup M, CFSG.Open.IsElemAbelian p A ∧ Nat.card A = p ^ k)
    (h : ∀ P : Sylow p G, Nonempty (P ≃* M)) : UniqueElemSylow p k G := by
  intro P
  obtain ⟨A_M, hA_M, huniq_M⟩ := hM
  obtain ⟨e⟩ := h P
  refine ⟨(A_M.comap e.toMonoidHom).map (P : Subgroup G).subtype, ?_, ?_⟩
  · refine ⟨Subgroup.map_subtype_le _, (hA_M.1.comap e.injective).map _, ?_⟩
    rw [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective,
      Subgroup.comap_equiv_eq_map_symm' e A_M, Subgroup.card_map_of_injective e.symm.injective]
    exact hA_M.2
  · intro A hA
    let A_M' : Subgroup M := (A.subgroupOf P).map e.toMonoidHom
    have hAM'ea : CFSG.Open.IsElemAbelian p A_M' := (hA.2.1.subgroupOf P).map e.toMonoidHom
    have hAM'card : Nat.card A_M' = p ^ k := by
      rw [Subgroup.card_map_of_injective e.injective]
      have h1 : (A.subgroupOf P).map (P : Subgroup G).subtype = A := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA.1]
      have h2 : Nat.card (A.subgroupOf P) = Nat.card A := by
        have hc : Nat.card ((A.subgroupOf P).map (P : Subgroup G).subtype) =
            Nat.card (A.subgroupOf P) :=
          Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective
        rw [h1] at hc
        exact hc.symm
      rw [h2, hA.2.2]
    have hAM'eq : A_M' = A_M := huniq_M A_M' ⟨hAM'ea, hAM'card⟩
    have hsub : A.subgroupOf P = A_M.comap e.toMonoidHom := by
      rw [← hAM'eq]
      exact (Subgroup.comap_map_eq_self_of_injective e.injective (A.subgroupOf P)).symm
    have hAeq : A = (A.subgroupOf P).map (P : Subgroup G).subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA.1]
    rw [hAeq, hsub]

end CFSG.GroupTheory
