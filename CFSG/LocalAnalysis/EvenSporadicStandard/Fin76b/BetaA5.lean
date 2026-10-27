module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaHom

public section

namespace CFSG.EvenSporadicStandard.Fin76b.Beta

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.HypOne

theorem piA5J2_even : ∀ l < 2, ∃ σ ∈ alternatingGroup (Fin 5), Rep 5 piA5J2[l]! σ := by
  intro l hl
  interval_cases l
  · refine ⟨Equiv.swap (0 : Fin 5) 4 * Equiv.swap 2 3, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      simp [Equiv.Perm.sign_mul]
    · intro i hi
      interval_cases i <;> decide
  · refine ⟨Equiv.swap (1 : Fin 5) 3 * Equiv.swap 3 4, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      simp [Equiv.Perm.sign_mul]
    · intro i hi
      interval_cases i <;> decide

theorem piA5J3_even : ∀ l < 2, ∃ σ ∈ alternatingGroup (Fin 5), Rep 5 piA5J3[l]! σ := by
  intro l hl
  interval_cases l
  · refine ⟨Equiv.swap (0 : Fin 5) 3 * Equiv.swap 2 4, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      simp [Equiv.Perm.sign_mul]
    · intro i hi
      interval_cases i <;> decide
  · refine ⟨Equiv.swap (0 : Fin 5) 2 * Equiv.swap 2 1, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      simp [Equiv.Perm.sign_mul]
    · intro i hi
      interval_cases i <;> decide

theorem a5_of_check {n : ℕ} (hn : n < 2 ^ 32) {X : Subgroup (Equiv.Perm (Fin n))}
    {aT bT tT : Table} {pg : Array Table}
    (hpg : ∀ l < 2, ∃ σ ∈ alternatingGroup (Fin 5), Rep 5 pg[l]! σ)
    (hchk : a5HomCheck n aT bT tT pg = true) (haX : tp n aT ∈ X) (hbX : tp n bT ∈ X) :
    ∃ B : Subgroup (Equiv.Perm (Fin n)), B ≤ X ∧
      B ≤ centralizer ({tp n tT} : Set (Equiv.Perm (Fin n))) ∧ tp n aT ∈ B ∧ tp n bT ∈ B ∧
      Nonempty (↥B ≃* alternatingGroup (Fin 5)) := by
  classical
  simp only [a5HomCheck, Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩ := hchk
  set gens : Array Table := #[aT, bT] with hgens
  set E := mulClosureH n gens 100 with hE
  set elts := E.1 with helts
  set img := treeImgN 5 pg E.2.1 E.2.2 elts.size with himg
  have hsz : elts.size = 60 := h9
  have h1' := h1
  rw [Array.all_eq_true'] at h1'
  simp only [Bool.and_eq_true] at h1'
  have hgA : ∀ x ∈ gens, permOK n x = true := fun x hx => (h1' x hx).1
  have hginv : ∀ x ∈ gens, invOK n x (invT n x) = true := fun x hx => (h1' x hx).2
  obtain ⟨hErep, hcov, hKcard⟩ := enum_spec hn hgA hginv h6 (closedOK_of_closedOKH h8) h7
  have haT : aT ∈ gens := by simp [hgens]
  have hbT : bT ∈ gens := by simp [hgens]
  have ra := rep_tp (hgA aT haT)
  have rb := rep_tp (hgA bT hbT)
  have rt := rep_tp h2
  have hgset : tp n '' {x | x ∈ gens} = {tp n aT, tp n bT} := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp [hgens] at hx
      rcases hx with rfl | rfl <;> simp
    · rintro (rfl | rfl)
      · exact ⟨aT, haT, rfl⟩
      · exact ⟨bT, hbT, rfl⟩
  set K : Subgroup (Equiv.Perm (Fin n)) := closure (tp n '' {x | x ∈ gens}) with hK
  have haK : tp n aT ∈ K := subset_closure ⟨aT, haT, rfl⟩
  have hbK : tp n bT ∈ K := subset_closure ⟨bT, hbT, rfl⟩
  have h5' := h5
  rw [Array.all_eq_true'] at h5'
  have hKX : K ≤ X := by
    rw [hK, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    simp [hgens] at hx
    rcases hx with rfl | rfl
    · exact haX
    · exact hbX
  have hKt : K ≤ centralizer ({tp n tT} : Set (Equiv.Perm (Fin n))) := by
    rw [hK, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_centralizer_singleton_iff.2 ((commTT_iff rt (rep_tp (hgA x hx))).1 (h5' x hx)).symm
  have hKcard' : Nat.card ↥K = 60 := by rw [hKcard, hsz]
  have hrepL : List.Forall₂ (Rep n) elts.toList (elts.toList.map (tablePerm n)) := by
    rw [List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro T hT
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
    have := (hErep k hk).1
    rwa [getElem!_pos elts k hk] at this
  have hnodup := nodup_of_hkeysDistinct hrepL h7
  have huniq : ∀ a b, a < elts.size → b < elts.size → ∀ x : Equiv.Perm (Fin n),
      Rep n elts[a]! x → Rep n elts[b]! x → a = b := by
    intro a b ha hb x hax hbx
    have hl : (elts.toList.map (tablePerm n)).length = elts.size := by simp
    refine (hnodup.getElem_inj_iff (i := a) (j := b) (hi := by rw [hl]; exact ha)
      (hj := by rw [hl]; exact hb)).1 ?_
    simp only [List.getElem_map, Array.getElem_toList]
    rw [← getElem!_pos elts a ha, ← getElem!_pos elts b hb, tablePerm_eq hax, tablePerm_eq hbx]
  let idxOf : Equiv.Perm (Fin n) → ℕ := fun x =>
    if h : x ∈ K then Classical.choose (hcov x h) else 0
  have hidx : ∀ x ∈ K, idxOf x < elts.size ∧ Rep n elts[idxOf x]! x := by
    intro x hx
    simp only [idxOf, hx, dite_true]
    exact Classical.choose_spec (hcov x hx)
  have himgrep : ∀ k < elts.size, Rep 5 img[k]! (tp 5 img[k]!) := by
    intro k hk
    have h11a := h11
    rw [Array.all_eq_true'] at h11a
    exact rep_tp (h11a _ (getElem!_mem_array (by rw [h10]; exact hk)))
  have hpgrep : ∀ l < 2, Rep 5 pg[l]! (tp 5 pg[l]!) := by
    intro l hl
    have h4a := h4
    rw [Array.all_eq_true'] at h4a
    exact rep_tp (h4a _ (getElem!_mem_array (by rw [h3]; exact hl)))
  let gg : Fin 2 → Equiv.Perm (Fin n) := ![tp n aT, tp n bT]
  let φ : Fin 2 → Equiv.Perm (Fin 5) := fun l => tp 5 pg[(l : ℕ)]!
  have hgg_rep : ∀ l : Fin 2, Rep n gens[(l : ℕ)]! (gg l) := by
    intro l
    fin_cases l
    · exact ra
    · exact rb
  have hggK : ∀ l : Fin 2, gg l ∈ K := by
    intro l
    fin_cases l
    · exact haK
    · exact hbK
  let F : Equiv.Perm (Fin n) → Equiv.Perm (Fin 5) := fun x => tp 5 img[idxOf x]!
  have hcayP : ∀ x ∈ K, ∀ l : Fin 2, F (x * gg l) = F x * φ l := by
    intro x hx l
    obtain ⟨hk, hxk⟩ := hidx x hx
    have hxg : x * gg l ∈ K := mul_mem hx (hggK l)
    have h13a := h13
    rw [List.all_eq_true] at h13a
    have h13b := h13a (idxOf x) (List.mem_range.2 hk)
    rw [List.all_eq_true] at h13b
    have h13c := h13b l (List.mem_range.2 l.2)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h13c
    obtain ⟨hjlt, himgj⟩ := h13c
    obtain ⟨-, hjeq⟩ := idxTH_spec hjlt
    have hrepc : Rep n (compT n elts[idxOf x]! gens[(l : ℕ)]!) (x * gg l) :=
      Rep.compT hxk (hgg_rep l)
    have hrepj : Rep n elts[idxTH n elts (hashIndex n elts) (compT n elts[idxOf x]!
        gens[(l : ℕ)]!)]! (x * gg l) := rep_of_tblEq hrepc (tblEq_symm' hjeq)
    have hjk : idxOf (x * gg l) = idxTH n elts (hashIndex n elts) (compT n elts[idxOf x]!
        gens[(l : ℕ)]!) := huniq _ _ (hidx _ hxg).1 hjlt _ (hidx _ hxg).2 hrepj
    show tp 5 img[idxOf (x * gg l)]! = tp 5 img[idxOf x]! * φ l
    rw [hjk]
    have hrc : Rep 5 (compT 5 img[idxOf x]! pg[(l : ℕ)]!) (tp 5 img[idxOf x]! * φ l) :=
      Rep.compT (himgrep _ hk) (hpgrep l l.2)
    exact rep_unique (himgrep _ hjlt) (rep_of_tblEq hrc himgj)
  have hF1 : F 1 = 1 := by
    obtain ⟨hk, hrep⟩ := hidx 1 K.one_mem
    have h6a := h6
    simp only [mulTreeOK, Bool.and_eq_true, decide_eq_true_eq] at h6a
    have hr0 : Rep n elts[0]! (1 : Equiv.Perm (Fin n)) := rep_of_tblEq (Rep.idT hn) h6a.1.2
    have h0lt : 0 < elts.size := by omega
    have h0 : idxOf 1 = 0 := huniq _ _ hk h0lt 1 hrep hr0
    show tp 5 img[idxOf 1]! = 1
    rw [h0]
    exact rep_unique (himgrep 0 h0lt) (rep_of_tblEq (Rep.idT (by norm_num)) h12)
  have hFker : ∀ x ∈ K, F x = 1 → x = 1 := by
    intro x hx hF
    obtain ⟨hk, hrep⟩ := hidx x hx
    have h14a := h14
    rw [List.all_eq_true] at h14a
    have hb := h14a _ (List.mem_range.2 hk)
    simp only [beq_iff_eq] at hb
    have hA : tblEq 5 img[idxOf x]! (idT 5) = true :=
      (tblEq_idT_iff (by norm_num) (himgrep _ hk)).2 hF
    rw [hb] at hA
    exact (tblEq_idT_iff hn hrep).1 hA
  let gens' : Fin 2 → ↥K := ![⟨tp n aT, haK⟩, ⟨tp n bT, hbK⟩]
  have hgen' : closure (Set.range gens') = ⊤ := by
    have hpre : Set.range gens' = (Subtype.val : ↥K → Equiv.Perm (Fin n)) ⁻¹'
        ({tp n aT, tp n bT} : Set (Equiv.Perm (Fin n))) := by
      ext ⟨y, hy⟩
      simp only [Set.mem_range, Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨l, hl⟩
        fin_cases l
        · exact Or.inl (congrArg Subtype.val hl).symm
        · exact Or.inr (congrArg Subtype.val hl).symm
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hpre]
    have := Subgroup.closure_closure_coe_preimage
      (k := ({tp n aT, tp n bT} : Set (Equiv.Perm (Fin n))))
    rw [← hgset] at this ⊢
    exact this
  let Fk : ↥K → Equiv.Perm (Fin 5) := fun c => F c.1
  have hFk1 : Fk 1 = 1 := hF1
  have hFkgen : ∀ c l, Fk (c * gens' l) = Fk c * φ l := by
    intro c l
    show F (c.1 * (gens' l).1) = F c.1 * φ l
    have hgl : (gens' l).1 = gg l := by
      fin_cases l <;> rfl
    rw [hgl]
    exact hcayP _ c.2 l
  have hFkmul := hom_of_cayley gens' φ hgen' Fk hFk1 hFkgen
  let π₀ : ↥K →* Equiv.Perm (Fin 5) :=
    { toFun := Fk
      map_one' := hFk1
      map_mul' := hFkmul }
  have hπ₀gen : ∀ l, π₀ (gens' l) = φ l := by
    intro l
    show Fk (gens' l) = φ l
    have := hFkgen 1 l
    rw [one_mul, hFk1, one_mul] at this
    exact this
  have hφalt : ∀ l : Fin 2, φ l ∈ alternatingGroup (Fin 5) := by
    intro l
    obtain ⟨σ, hσ, hrσ⟩ := hpg l l.2
    have : tp 5 pg[(l : ℕ)]! = σ := rep_unique (hpgrep l l.2) hrσ
    show tp 5 pg[(l : ℕ)]! ∈ alternatingGroup (Fin 5)
    rw [this]
    exact hσ
  have hAlt : ∀ c, π₀ c ∈ alternatingGroup (Fin 5) := by
    have hle : (⊤ : Subgroup ↥K) ≤ (alternatingGroup (Fin 5)).comap π₀ := by
      rw [← hgen', closure_le]
      rintro _ ⟨l, rfl⟩
      show π₀ (gens' l) ∈ alternatingGroup (Fin 5)
      rw [hπ₀gen]
      exact hφalt l
    intro c
    exact hle (mem_top c)
  let π : ↥K →* alternatingGroup (Fin 5) := π₀.codRestrict (alternatingGroup (Fin 5)) hAlt
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : F x.1 = 1 := by
      have := congrArg Subtype.val hx
      exact this
    exact Subtype.ext (hFker x.1 x.2 hx')
  have hAltcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  have hbij : Function.Bijective π :=
    hπinj.bijective_of_nat_card_le (by rw [hKcard', hAltcard])
  exact ⟨K, hKX, hKt, haK, hbK, ⟨MulEquiv.ofBijective π hbij⟩⟩


theorem a5HomCheck_permOK {n : ℕ} {aT bT tT : Table} {pg : Array Table}
    (hchk : a5HomCheck n aT bT tT pg = true) :
    permOK n aT = true ∧ permOK n bT = true ∧ permOK n tT = true := by
  simp only [a5HomCheck, Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hchk
  rw [Array.all_eq_true'] at h1
  simp only [Bool.and_eq_true] at h1
  exact ⟨(h1 aT (by simp)).1, (h1 bT (by simp)).1, h2⟩

end CFSG.EvenSporadicStandard.Fin76b.Beta
