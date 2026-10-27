module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1G2Par
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Tr
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1BT
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Types

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.Sec66T
  CFSG.Timmesfeld.ExceptionalOrders

section Native

variable (K : Type) [Field K]

theorem aut_eq_one_g2 {r : ℕ} [Fact r.Prime] [Finite K] (hK : ringChar K ≠ 2)
    (b : MulAut ↥(adjointGroup Tag.G2 K)) (hb : ¬ r ∣ orderOf b)
    {a a' : Fin Tag.G2.rank} (hne : a ≠ a') (hfix : ∀ q ∈ QG K {a}, b q = q) [CharP K r] :
    b = 1 := by
  have hBle : ∀ c, BG K ≤ PG K {c} := fun c => by
    rw [← PG_empty K]
    exact (PG_le_iff K _ _).2 (Set.empty_subset _)
  have hJne : ∀ c : Fin Tag.G2.rank, ({c} : Set (Fin Tag.G2.rank)) ≠ Set.univ := by
    intro c h
    have hex : ∀ c : Fin Tag.G2.rank, ∃ x : Fin Tag.G2.rank, x ≠ c := by decide
    obtain ⟨x, hx⟩ := hex c
    have hxc : x ∈ ({c} : Set (Fin Tag.G2.rank)) := by
      rw [h]
      exact Set.mem_univ x
    exact hx (Set.mem_singleton_iff.1 hxc)
  have hMne : PG K {a} ≠ PG K {a'} := fun h => hne (Set.singleton_subset_singleton.1
    ((PG_le_iff K _ _).1 h.le))
  refine aut_eq_one_of_two_maximals b hb (B := BG K) (isCoatom_PG_singleton K a)
    (isCoatom_PG_singleton K a') hMne (hBle a) (hBle a') ?_ (QG_ne_bot K (hJne a))
    (QG_isPGroup K r _) (PG_normalizes K) (PG_selfCentralizing K (hJne a))
    (QG_isPGroup K r _) (QG_le_BG K _) (PG_normalizes K)
    (PG_selfCentralizing K (hJne a')) (no_normal_pGroup_G2 K r hK) hfix
  intro A hA hBA
  obtain ⟨c, rfl⟩ := coatom_eq_PG K hA hBA
  rcases two_elements_G2 a a' (Ne.symm hne) c with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem e1Core_g2_native {r : ℕ} [Fact r.Prime] [Finite K] [CharP K r] (hK : ringChar K ≠ 2)
    (hBT : LieType.BorelTits.Holds ↥(adjointGroup Tag.G2 K) r) :
    E1Core r ↥(adjointGroup Tag.G2 K) := by
  intro b hb1 hbr hHH E hE hinv
  by_contra hne
  obtain ⟨M, S, hM, hS, hR⟩ := e1_engine hBT b hHH hE hinv hne
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := g2Sub_borel_le_adjointGroup
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := le_sup_right.trans hBC
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index r hUC card_posUnipotent
  have hUc := IsPGroup.toSylow_coe hUp hUi
  obtain ⟨g, hg⟩ := g2Sub_exists_conj_le (hUp.toSylow hUi) S (BG K) M
    (by rw [hUc]; exact g2Sub_borel_le_normalizer) hS
  have hM' : IsCoatom (M.comap (MulAut.conj g).toMonoidHom) :=
    isCoatom_comap_mulAut _ hM
  obtain ⟨a, ha⟩ := coatom_eq_PG K hM' hg
  obtain ⟨a', hne'⟩ : ∃ a' : Fin Tag.G2.rank, a ≠ a' := by
    have hex : ∀ c : Fin Tag.G2.rank, ∃ x : Fin Tag.G2.rank, c ≠ x := by decide
    exact hex a
  set b' : MulAut ↥(adjointGroup Tag.G2 K) := (MulAut.conj g)⁻¹ * b * MulAut.conj g with hb'
  have hRp : IsPGroup r ↥((QG K {a}).map (MulAut.conj g).toMonoidHom) :=
    (QG_isPGroup K r {a}).map _
  have hRM : (QG K {a}).map (MulAut.conj g).toMonoidHom ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : x ∈ M.comap (MulAut.conj g).toMonoidHom := by
      rw [ha]
      exact QG_le_PG K {a} hx
    exact hxP
  have hMR : M ≤ Subgroup.normalizer (((QG K {a}).map (MulAut.conj g).toMonoidHom :
      Subgroup _) : Set _) := by
    refine le_normalizer_of_conj_mem ?_
    rintro m hm _ ⟨q, hq, rfl⟩
    have hm' : (MulAut.conj g) ((MulAut.conj g)⁻¹ m) = m := (MulAut.conj g).apply_symm_apply m
    have hn : (MulAut.conj g)⁻¹ m ∈ PG K {a} := by
      rw [← ha]
      show (MulAut.conj g) ((MulAut.conj g)⁻¹ m) ∈ M
      rw [hm']
      exact hm
    refine ⟨(MulAut.conj g)⁻¹ m * q * ((MulAut.conj g)⁻¹ m)⁻¹, PG_normalizes K _ hn q hq, ?_⟩
    show (MulAut.conj g) ((MulAut.conj g)⁻¹ m * q * ((MulAut.conj g)⁻¹ m)⁻¹) =
      m * (MulAut.conj g) q * m⁻¹
    rw [map_mul, map_mul, map_inv, hm']
  have hfix : ∀ q ∈ QG K {a}, b' q = q := by
    intro q hq
    have h1 := hR _ hRp hRM hMR ((MulAut.conj g) q) ⟨q, hq, rfl⟩
    simp only [hb', MulAut.mul_apply]
    rw [h1]
    exact (MulAut.conj g).symm_apply_apply q
  have hb'ord : ¬ r ∣ orderOf b' := by
    have : orderOf b' = orderOf b := by
      refine (SemiconjBy.orderOf_eq (MulAut.conj g)⁻¹ ?_).symm
      show (MulAut.conj g)⁻¹ * b = ((MulAut.conj g)⁻¹ * b * MulAut.conj g) * (MulAut.conj g)⁻¹
      group
    rw [this]
    exact hbr
  have hb'1 := aut_eq_one_g2 K hK b' hb'ord hne' hfix
  apply hb1
  have h1 : b = MulAut.conj g * b' * (MulAut.conj g)⁻¹ := by rw [hb']; group
  rw [h1, hb'1]
  group

end Native

section Top


theorem e1_g2 : E1Type FG2d := by
  intro r Y _ _ hr hr2 hF b hb1 hbr hHH E hE hinv
  obtain ⟨f, hf, hm⟩ := hF
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.exists_equiv_of_lieModel hm
  have : CharP F r := finite_field_prime_power_characteristic hr hf hcard
  have hodd : ringChar F ≠ 2 := by
    rw [ringChar.eq F r]
    exact hr2
  have hBT : LieType.BorelTits.Holds Y r := holds_of_lieModel hm (by decide)
  have hBT' : LieType.BorelTits.Holds ↥(adjointGroup Tag.G2 F) r :=
    LieType.BorelTits.Holds.of_mulEquiv e hBT
  exact E1Core.of_mulEquiv e (e1Core_g2_native F hodd hBT') b hb1 hbr hHH E hE hinv

end Top

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
