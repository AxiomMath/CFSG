module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78HAltPairGen
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L315a
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem mem_normalizer_inf_of_mem {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [mem_inf, mem_inf, hA h, hB h]

theorem isTwoComponentIn_oddResidualIn [Finite X] {J P : Subgroup X} (hJP : J ≤ P)
    (hJn : P ≤ normalizer (J : Set X)) {n : ℕ} (hn : 8 ≤ n)
    (θJ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) :
    FooteLit.IsTwoComponentIn (FooteLit.oddResidualIn J) P ∧
      FooteLit.oddResidualIn J ⊔ FooteLit.oddCoreIn J = J ∧
      Nonempty (↥(FooteLit.oddResidualIn J) ⧸ pPrimeCore 2 ↥(FooteLit.oddResidualIn J) ≃*
        alternatingGroup (Fin n)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := FooteLit.oddResidualIn J with hK
  have hKJ : K ≤ J := FooteLit.oddResidualIn_le J
  have hKn : P ≤ normalizer (K : Set X) := fun p hp =>
    Sol78H.mem_normalizer_oddResidualIn (hJn hp)
  have hsupK : K ⊔ FooteLit.oddCoreIn J = J := by
    set W := K ⊔ FooteLit.oddCoreIn J with hW
    have hWJ : W ≤ J := sup_le hKJ (map_subtype_le _)
    have hJW : J ≤ normalizer (W : Set X) :=
      Sol76T13.le_normalizer_sup (hJP.trans hKn) (Sol76.le_normalizer_oddCoreIn J)
    have hWn : (W.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hWJ).mpr hJW
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using (by omega : 5 ≤ n))
    have : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := θJ.isSimpleGroup
    set π := QuotientGroup.mk' (pPrimeCore 2 ↥J) with hπ
    have hmapn : ((W.subgroupOf J).map π).Normal :=
      Subgroup.Normal.map hWn π (QuotientGroup.mk'_surjective _)
    rcases hmapn.eq_bot_or_eq_top with hbot | htop
    ·
      exfalso
      have hKO : K ≤ FooteLit.oddCoreIn J := by
        intro k hk
        have hkW : (⟨k, hKJ hk⟩ : ↥J) ∈ W.subgroupOf J := mem_subgroupOf.mpr (mem_sup_left hk)
        have h1 : π ⟨k, hKJ hk⟩ = 1 := by
          have := mem_map_of_mem π hkW
          rw [hbot, mem_bot] at this
          exact this
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact ⟨_, h1, rfl⟩
      have h2J : 2 ∣ Nat.card ↥J := by
        have h1 : 2 ∣ Nat.card (↥J ⧸ pPrimeCore 2 ↥J) := by
          rw [Nat.card_congr θJ.toEquiv]
          exact Sol78H.two_dvd_card_alternatingGroup hn
        exact h1.trans (Subgroup.card_quotient_dvd_card _)
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2J
      have hxK : (x : X) ∈ K :=
        subset_closure ⟨x.2, 1, by rw [pow_one, Subgroup.orderOf_coe, hx]⟩
      have h1 := orderOf_dvd_natCard (⟨x, hKO hxK⟩ : FooteLit.oddCoreIn J)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx] at h1
      exact absurd (Nat.Coprime.eq_one_of_dvd (Sol76.coprime_card_oddCoreIn J) h1) (by norm_num)
    ·
      have hker : pPrimeCore 2 ↥J ≤ W.subgroupOf J := fun y hy =>
        mem_subgroupOf.mpr (mem_sup_right ⟨y, hy, rfl⟩)
      have h1 : W.subgroupOf J = ⊤ := by
        have h2 := congrArg (Subgroup.comap π) htop
        rwa [comap_map_eq, QuotientGroup.ker_mk', comap_top, sup_eq_left.mpr hker] at h2
      apply le_antisymm hWJ
      intro j hj
      have := h1 ▸ mem_top (⟨j, hj⟩ : ↥J)
      exact mem_subgroupOf.mp this
  obtain ⟨φK⟩ := Sol78H.nonempty_coreQuot_equiv_of_sup hKJ hsupK
  set θK := φK.trans θJ with hθK
  have hKP : K ≤ P := hKJ.trans hJP
  have hKres : FooteLit.oddResidualIn K = K := Sol76T13.oddResidualIn_oddResidualIn J
  have hprim : CatalogueBPrimeJoin.primeResidual 2 ↥K = ⊤ := by
    have h1 := Sol76.oddResidualIn_eq_map_primeResidual K
    rw [hKres] at h1
    apply Subgroup.map_injective K.subtype_injective
    rw [← h1, ← MonoidHom.range_eq_map, range_subtype]
  have hq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) := by
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using (by omega : 5 ≤ n))
    exact LocalCores.isQuasisimple_of_mulEquiv θK.symm
      (LocalCores.isQuasisimple_of_isSimpleGroup (SolAltLit.alternating_nonabelian (by omega))).1
  have hKn' : (K.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hKP).mpr hKn
  exact ⟨⟨hKP, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K P hKP).mpr
    ⟨hKn'.isSubnormal, hprim, hq⟩⟩, hsupK, ⟨θK⟩⟩

end CFSG.ComponentClassification.SolMax
