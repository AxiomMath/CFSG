module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8FramePsi
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8FrameAbstract
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeAut
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public noncomputable section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

open CFSG.Open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.OmegaEightMinus CFSG.AGLEmbedding

theorem countP_range_eq_sum (n : ℕ) (p : ℕ → Bool) :
    (List.range n).countP p = ∑ i ∈ Finset.range n, if p i = true then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]
    cases h : p n <;> simp [List.countP_cons, h]

theorem suppA_eq {t : Array ℕ} {g : Equiv.Perm (Fin 136)} (h : Rep 136 t g) :
    suppA t = g.support.card := by
  rw [suppA, countP_range_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun i => if (t[i]! != i) = true then 1 else 0) 136,
    Equiv.Perm.support, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx := h x
  by_cases hgx : g x = x
  · have : t[(x : ℕ)]! = (x : ℕ) := by rw [hx, hgx]
    simp [hgx, this]
  · have : t[(x : ℕ)]! ≠ (x : ℕ) := by
      rw [hx]
      exact fun e => hgx (Fin.ext e)
    simp [hgx, this]

@[expose] def sixP : Fin 6 → Equiv.Perm (Fin 136) :=
  ![betaP 0, (betaP 0)⁻¹, betaP 1, (betaP 1)⁻¹, betaP 2, (betaP 2)⁻¹]

theorem rep_six (k : Fin 6) :
    Rep 136 sixArrs[(k : ℕ)]! (sixP k) := by
  have r : ∀ i < 3, Rep 136 betaArrs[i]! (betaP i) := fun i hi => rep_beta hi
  have ri : ∀ i < 3, Rep 136 (invCand 136 betaArrs[i]!) (betaP i)⁻¹ := fun i hi =>
    EvenSporadicStandard.HSStd.PumpTC7.rep_invCand_of_rep (rep_beta hi)
  fin_cases k
  · exact r 0 (by norm_num)
  · exact ri 0 (by norm_num)
  · exact r 1 (by norm_num)
  · exact ri 1 (by norm_num)
  · exact r 2 (by norm_num)
  · exact ri 2 (by norm_num)

theorem sixP_mem (k : Fin 6) : sixP k ∈ J0 := by
  have h : ∀ i < 3, betaP i ∈ J0 := fun i hi => betaP_mem_J0 hi
  fin_cases k
  · exact h 0 (by norm_num)
  · exact J0.inv_mem (h 0 (by norm_num))
  · exact h 1 (by norm_num)
  · exact J0.inv_mem (h 1 (by norm_num))
  · exact h 2 (by norm_num)
  · exact J0.inv_mem (h 2 (by norm_num))

theorem sixP_injective : Function.Injective sixP := by
  intro k l hkl
  by_contra hne
  have h := mem_ok.2.2.2.2.2.2.2.2.2 k k.2 l l.2 (fun e => hne (Fin.ext e))
  rw [← Bool.not_eq_true, eqA_iff (rep_six k) (rep_six l)] at h
  exact h hkl

theorem setOf_eq_range :
    {x : Equiv.Perm (Fin 136) | x ∈ J0 ∧ x.support.card = 108} = Set.range sixP := by
  ext x
  constructor
  · rintro ⟨hx, h108⟩
    obtain ⟨a, ha, b, hb, c, hc, hrep⟩ := exists_rep_of_mem_J0 hx
    have hs : notSix (prod3 136 j0Levels a b c) = false :=
      (elt_ok ha hb hc).2.2.1.1 (by rw [suppA_eq hrep, h108])
    rw [notSix, ← Bool.not_eq_true, allLt_iff] at hs
    push Not at hs
    obtain ⟨k, hk, hk''⟩ := hs
    have hk' : eqA 136 (prod3 136 j0Levels a b c) sixArrs[k]! = true := by simpa using hk''
    exact ⟨⟨k, hk⟩, (eq_of_eqA hrep (rep_six ⟨k, hk⟩) hk').symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨sixP_mem k, by rw [← suppA_eq (rep_six k)]; exact mem_ok.2.2.2.2.2.2.2.2.1 k k.2⟩

@[expose] def nGenP (i : ℕ) : Equiv.Perm (Fin 136) := permOfArr 136 nGens[i]!

@[expose] def nWordP (w : List ℕ) : Equiv.Perm (Fin 136) := (w.map nGenP).prod

theorem rep_nGen {i : ℕ} (hi : i < 3) :
    Rep 136 nGens[i]! (nGenP i) := by
  interval_cases i
  · exact rep_c
  · exact (rep_permOfArr mem_ok.2.2.2.1).1
  · exact (rep_permOfArr mem_ok.2.2.2.2.1).1

theorem nGenP_mem_omegaT {i : ℕ}
    (hi : i < 3) : nGenP i ∈ omegaT := by
  interval_cases i
  · exact cP_mem_omegaT
  · exact mem_omegaT_of_sift (rep_nGen (by norm_num)) mem_ok.2.1
  · exact mem_omegaT_of_sift (rep_nGen (by norm_num)) mem_ok.2.2.1

theorem mem_normalizer_J0 {g : Equiv.Perm (Fin 136)}
    (h : ∀ i < 3, g * betaP i * g⁻¹ ∈ J0) : g ∈ Subgroup.normalizer (J0 : Set _) := by
  have hle : J0.map (MulAut.conj g).toMonoidHom ≤ J0 := by
    calc J0.map (MulAut.conj g).toMonoidHom =
          (Subgroup.closure {g' | ∃ i < 3, betaP i = g'}).map (MulAut.conj g).toMonoidHom := by
          rw [← J0_eq]
      _ ≤ J0 := by
        rw [MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
        show g * betaP i * g⁻¹ ∈ J0
        exact h i hi
  have heq : J0.map (MulAut.conj g).toMonoidHom = J0 :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hle ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      have e : g * z * g⁻¹ = g * y * g⁻¹ := hzy
      simpa using e
    rwa [← this]

theorem nGenP_mem_normalizer {i : ℕ} (hi : i < 3) :
    nGenP i ∈ Subgroup.normalizer (J0 : Set (Equiv.Perm (Fin 136))) := by
  refine mem_normalizer_J0 fun j hj => mem_J0_of_sift ?_ (mem_ok.2.2.2.2.2.1 i hi j hj)
  exact rep_compA (rep_compA (rep_nGen hi) (rep_beta hj))
    (EvenSporadicStandard.HSStd.PumpTC7.rep_invCand_of_rep (rep_nGen hi))

theorem rep_nWord :
    ∀ w : List ℕ, (∀ i ∈ w, i < 3) → Rep 136 (nWordA w) (nWordP w)
  | [], _ => by
    rw [nWordA, nWordP, List.map_nil, List.prod_nil]
    exact rep_idA
  | i :: w, hw => by
    rw [nWordA, nWordP, List.map_cons, List.prod_cons]
    exact rep_compA (rep_nGen (hw i List.mem_cons_self))
      (rep_nWord w fun j hj => hw j (List.mem_cons_of_mem i hj))

theorem nWordP_mem :
    ∀ w : List ℕ, (∀ i ∈ w, i < 3) →
      nWordP w ∈ omegaT ∧ nWordP w ∈ Subgroup.normalizer (J0 : Set (Equiv.Perm (Fin 136)))
  | [], _ => by
    rw [nWordP, List.map_nil, List.prod_nil]
    exact ⟨omegaT.one_mem, Subgroup.one_mem _⟩
  | i :: w, hw => by
    rw [nWordP, List.map_cons, List.prod_cons]
    have hi := hw i List.mem_cons_self
    obtain ⟨h1, h2⟩ := nWordP_mem w fun j hj => hw j (List.mem_cons_of_mem i hj)
    exact ⟨omegaT.mul_mem (nGenP_mem_omegaT hi) h1,
      Subgroup.mul_mem _ (nGenP_mem_normalizer hi) h2⟩

theorem rep_conjA {g x : Array ℕ} {G X : Equiv.Perm (Fin 136)} (hg : Rep 136 g G)
    (hx : Rep 136 x X) : Rep 136 (conjA g x) (G * X * G⁻¹) :=
  rep_compA (rep_compA hg hx) (EvenSporadicStandard.HSStd.PumpTC7.rep_invCand_of_rep hg)

theorem sep_J0
    {x : Equiv.Perm (Fin 136)} (hx : x ∈ J0) (hx1 : x ≠ 1) (hx108 : x.support.card ≠ 108) :
    ∃ m : Fin 4 → Equiv.Perm (Fin 136),
      (∀ k, m k ∈ omegaT ∧ m k ∈ Subgroup.normalizer (J0 : Set (Equiv.Perm (Fin 136)))) ∧
      ∀ k l, k ≠ l → m k * x * (m k)⁻¹ ≠ m l * x * (m l)⁻¹ ∧
        m k * x * (m k)⁻¹ ≠ m l * x⁻¹ * (m l)⁻¹ := by
  obtain ⟨a, ha, b, hb, c, hc, hrep⟩ := exists_rep_of_mem_J0 hx
  set xa := prod3 136 j0Levels a b c
  have hsep : sepOK xa (pick4 xa) = true := by
    rcases (elt_ok ha hb hc).2.2.2.2 with h | h | h
    · exact absurd (eq_of_eqA hrep rep_idA h) hx1
    · exact absurd (by rw [← suppA_eq hrep]; exact h) hx108
    · exact h
  set ws := pick4 xa
  simp only [sepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    allLt_iff, Bool.or_eq_true, Bool.not_eq_true'] at hsep
  obtain ⟨⟨hlen, hlet⟩, hd⟩ := hsep
  have hletk : ∀ k : Fin 4, ∀ i ∈ ws[(k : ℕ)]!, i < 3 := fun k i hi => by
    have hk : (k : ℕ) < ws.length := by rw [hlen]; exact k.2
    rw [getElem!_pos ws (k : ℕ) hk] at hi
    exact hlet _ (List.getElem_mem hk) i hi
  refine ⟨fun k => nWordP ws[(k : ℕ)]!, fun k => nWordP_mem _ (hletk k), fun k l hkl => ?_⟩
  have hk := rep_conjA (rep_nWord _ (hletk k)) hrep
  have hl := rep_conjA (rep_nWord _ (hletk l)) hrep
  have hl' := rep_conjA (rep_nWord _ (hletk l))
    (EvenSporadicStandard.HSStd.PumpTC7.rep_invCand_of_rep hrep)
  rcases hd k k.2 l l.2 with h | ⟨h1, h2⟩
  · exact absurd (Fin.ext h) hkl
  · refine ⟨fun e => ?_, fun e => ?_⟩
    · rw [← Bool.not_eq_true, eqA_iff hk hl] at h1
      exact h1 e
    · rw [← Bool.not_eq_true, eqA_iff hk hl'] at h2
      exact h2 e

theorem betaP_one_eq : betaP 1 = cP * betaP 0 * cP⁻¹ :=
  (eq_of_eqA (rep_conjA rep_c (rep_beta (by norm_num))) (rep_beta (by norm_num))
    mem_ok.2.2.2.2.2.2.1).symm

theorem betaP_two_eq : betaP 2 = cP * betaP 1 * cP⁻¹ :=
  (eq_of_eqA (rep_conjA rep_c (rep_beta (by norm_num))) (rep_beta (by norm_num))
    mem_ok.2.2.2.2.2.2.2.1).symm

theorem hasW_six (k : Fin 6) :
    HasW (sixP k) := by
  have h0 := hasW_beta_zero
  have h1 : HasW (betaP 1) := betaP_one_eq ▸ hasW_conj h0 cP_mem_omegaT
  have h2 : HasW (betaP 2) := betaP_two_eq ▸ hasW_conj h1 cP_mem_omegaT
  fin_cases k
  · exact h0
  · exact hasW_inv h0
  · exact h1
  · exact hasW_inv h1
  · exact h2
  · exact hasW_inv h2

theorem frameProps_J0 :
    FrameProps (fun g : Equiv.Perm (Fin 136) => g.support.card) 108 omegaT J0 where
  one_ne := by simp
  ncard_eq := by
    rw [setOf_eq_range, Set.ncard_range_of_injective sixP_injective, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  le_closure := by
    rw [setOf_eq_range, J0_eq]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨i, hi, rfl⟩
    interval_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨4, rfl⟩
  sep := fun x hx hx1 hx108 => sep_J0 hx hx1 hx108
  simple := fun x hx h108 => by
    have hmem : x ∈ {x : Equiv.Perm (Fin 136) | x ∈ J0 ∧ x.support.card = 108} := ⟨hx, h108⟩
    rw [setOf_eq_range] at hmem
    obtain ⟨k, rfl⟩ := hmem
    exact hasW_six k

theorem aut_holds (α : MulAut omegaT) (z : omegaT) :
    ((α z : omegaT) : Equiv.Perm (Fin 136)).support.card =
      (z : Equiv.Perm (Fin 136)).support.card := by
  obtain ⟨a, rfl⟩ := autEquiv.surjective α
  rw [autEquiv_apply, Equiv.Perm.card_support_conj]

theorem bridge_holds (L : Type) [Group L]
    (d : TauCeti.ValidLieTypeIndex) (hd : IsOmegaMinusTwoIndex 4 d)
    (he : Nonempty (L ≃* CatGroup d)) : Nonempty (L ≃* omegaT) := by
  obtain ⟨e⟩ := he
  rcases d with ⟨i, hi⟩
  obtain ⟨q, hqp, hqe, hiq⟩ := hd
  simp only at hiq
  subst hiq
  have hmodel :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hi hqp e
  rw [hqp, hqe] at hmodel
  exact nonempty_mulEquiv_omegaT (Or.inl ⟨by decide, hmodel⟩)

theorem omega8FrameModel_holds :
    Omega8FrameModel where
  card := card_omegaT
  frame := ⟨J0, T0, J0_le_T0, T0_le_omegaT, card_T0, isElemAbelian_J0, card_J0,
    fun _ h1 h2 h3 => eq_J0_of_le_T0 h1 h2 h3, frameProps_J0⟩
  aut := aut_holds
  bridge := bridge_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem kFactOmega8Frame_holds :
    KFactOmega8Frame :=
  Omega8Frame.kFactOmega8Frame_of_model Omega8Frame.omega8FrameModel_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
