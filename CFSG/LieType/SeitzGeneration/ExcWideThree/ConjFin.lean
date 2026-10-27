module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.ConjFinWords
public import CFSG.LieType.SeitzGeneration.ExcWideThree.ConjFinWit
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagFinMain
public import CFSG.LieType.Chevalley.TwistMap

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration.ExcHighThree

section Soundness

@[expose] def rfRhoPerm : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

theorem rfRho_eq_rfRhoPerm (i : Fin Tag.E6.rank) :
    rfRho (i : ℕ) = ((rfRhoPerm i : Fin Tag.E6.rank) : ℕ) := by
  revert i
  decide

@[expose] def InvFixedZ (v : WeylGroup Tag.E6) (κ : Fin Tag.E6.rank → ℤ) : Prop :=
  ∀ i : Fin Tag.E6.rank, (3 : ℤ) ∣
    (∑ j, κ j * (v⁻¹ • (Pi.single (rfRhoPerm i) 1 : Fin Tag.E6.rank → ℤ)) j) -
      ∑ j, κ j * (v⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) j

theorem InvFixedZ.congr {v : WeylGroup Tag.E6} {κ κ' : Fin Tag.E6.rank → ℤ}
    (h : InvFixedZ v κ) (hc : ∀ j, (3 : ℤ) ∣ κ j - κ' j) : InvFixedZ v κ' := by
  intro i
  have key : ∀ u : Fin Tag.E6.rank → ℤ, (3 : ℤ) ∣ ∑ j, (κ j - κ' j) * u j :=
    fun u => Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (hc j) _
  have h1 := key (v⁻¹ • (Pi.single (rfRhoPerm i) 1 : Fin Tag.E6.rank → ℤ))
  have h2 := key (v⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
  simp only [sub_mul, Finset.sum_sub_distrib] at h1 h2
  have := h i
  omega

theorem InvFixedZ.lin {v : WeylGroup Tag.E6} {κ₁ κ₂ : Fin Tag.E6.rank → ℤ} (a b : ℤ)
    (h₁ : InvFixedZ v κ₁) (h₂ : InvFixedZ v κ₂) :
    InvFixedZ v (fun j => a * κ₁ j + b * κ₂ j) := by
  intro i
  have e : ∀ u : Fin Tag.E6.rank → ℤ, ∑ j, (a * κ₁ j + b * κ₂ j) * u j =
      a * ∑ j, κ₁ j * u j + b * ∑ j, κ₂ j * u j := fun u => by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, e]
  obtain ⟨c₁, hc₁⟩ := h₁ i
  obtain ⟨c₂, hc₂⟩ := h₂ i
  exact ⟨a * c₁ + b * c₂, by linear_combination a * hc₁ + b * hc₂⟩

theorem rfConjCols_eq (ω : List (Fin Tag.E6.rank)) (w : WeylGroup Tag.E6) :
    rfConjCols (ω.map fun i : Fin Tag.E6.rank => (i : ℕ)) (rfCols w) =
      rfCols ((coxeterSystem Tag.E6).wordProd ω * w * ((coxeterSystem Tag.E6).wordProd ω)⁻¹) := by
  set v := (coxeterSystem Tag.E6).wordProd ω with hv
  unfold rfConjCols
  rw [rfVCols_reverse_eq_rfCols, rfVCols_eq_rfCols]
  apply List.ext_getElem
  · simp [rfCols]
  · intro n h1 h2
    have hn : n < Tag.E6.rank := by simpa [rfCols] using h2
    have hC : (rfCols (v * w * v⁻¹))[n]'h2 =
        List.ofFn ((v * w * v⁻¹) • (Pi.single (⟨n, hn⟩ : Fin Tag.E6.rank) 1 :
          Fin Tag.E6.rank → ℤ)) :=
      rfCols_getElem _ ⟨n, hn⟩
    have hV : (rfCols v⁻¹)[n]'(by simpa [rfCols] using hn) =
        List.ofFn (v⁻¹ • (Pi.single (⟨n, hn⟩ : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ)) :=
      rfCols_getElem _ ⟨n, hn⟩
    rw [hC, List.getElem_map, hV, rfLincombZ_cols w, rfLincombZ_cols v, mul_smul, mul_smul]

theorem rfCols_getD (x : WeylGroup Tag.E6) (c : Fin Tag.E6.rank) :
    (rfCols x).getD (c : ℕ) [] = List.ofFn (x • (Pi.single c 1 : Fin Tag.E6.rank → ℤ)) := by
  have hc : (c : ℕ) < (rfCols x).length := by simp [rfCols]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some,
    rfCols_getElem x c]

theorem rfCols_getD_getD (x : WeylGroup Tag.E6) (c d : Fin Tag.E6.rank) :
    ((rfCols x).getD (c : ℕ) []).getD (d : ℕ) 0 =
      (x • (Pi.single c 1 : Fin Tag.E6.rank → ℤ)) d := by
  rw [rfCols_getD]
  simp [List.getD_eq_getElem?_getD]

theorem weylTwist_eq_of_comm (x : WeylGroup TwistTag.E6.tag)
    (hcomm : ∀ a b : Fin TwistTag.E6.tag.rank,
      (x • (Pi.single (TwistTag.E6.perm a) 1 : Fin TwistTag.E6.tag.rank → ℤ)) b =
        (x • (Pi.single a 1 : Fin TwistTag.E6.tag.rank → ℤ)) (TwistTag.E6.perm b)) :
    weylTwist TwistTag.E6 x = x := by
  have hinv : ∀ c : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm (TwistTag.E6.perm c) = c := by
    intro c
    revert c
    decide
  apply ext_single
  intro j
  funext i
  have h1 := weylTwist_smul_permLattice (t := TwistTag.E6) x
    (Pi.single (TwistTag.E6.perm.symm j) 1 : Fin TwistTag.E6.tag.rank → ℤ)
  rw [permLattice_single, Equiv.apply_symm_apply] at h1
  rw [h1]
  have hs : ∀ c : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm.symm c = TwistTag.E6.perm c :=
    fun c => by rw [Equiv.symm_apply_eq, hinv]
  have h3 := hcomm (TwistTag.E6.perm.symm j) i
  rw [Equiv.apply_symm_apply] at h3
  show (x • (Pi.single (TwistTag.E6.perm.symm j) 1 : Fin TwistTag.E6.tag.rank → ℤ))
    (TwistTag.E6.perm.symm i) = _
  rw [hs i, ← h3]

theorem weylTwist_eq_of_rfRhoComm (x : WeylGroup Tag.E6) (h : rfRhoComm (rfCols x) = true) :
    weylTwist TwistTag.E6 x = x := by
  have hcomm : ∀ a b : Fin Tag.E6.rank,
      (x • (Pi.single (rfRhoPerm a) 1 : Fin Tag.E6.rank → ℤ)) b =
        (x • (Pi.single a 1 : Fin Tag.E6.rank → ℤ)) (rfRhoPerm b) := by
    intro a b
    have h' := List.all_eq_true.1 h a.val (List.mem_range.2 a.2)
    have h'' := List.all_eq_true.1 h' b.val (List.mem_range.2 b.2)
    simp only [beq_iff_eq] at h''
    rw [rfRho_eq_rfRhoPerm a, rfRho_eq_rfRhoPerm b] at h''
    rw [← rfCols_getD_getD x (rfRhoPerm a) b, ← rfCols_getD_getD x a (rfRhoPerm b)]
    exact h''
  exact weylTwist_eq_of_comm x fun a b => hcomm a b

theorem invFixedZ_of_rfInvFix (ω : List (Fin Tag.E6.rank)) {κ : List ℕ}
    (hκ : κ.length = Tag.E6.rank)
    (h : rfInvFix (ω.map fun i : Fin Tag.E6.rank => (i : ℕ)) κ = true) :
    InvFixedZ ((coxeterSystem Tag.E6).wordProd ω)
      (fun j : Fin Tag.E6.rank => ((κ.getD (j : ℕ) 0 : ℕ) : ℤ)) := by
  intro i
  have h' := List.all_eq_true.1 h i.val (List.mem_range.2 i.2)
  simp only [beq_iff_eq] at h'
  rw [rfRho_eq_rfRhoPerm i, rfVCols_reverse_eq_rfCols] at h'
  have hmc := rf_map_cast_eq_ofFn κ hκ
  have e1 : ∀ c : Fin Tag.E6.rank,
      rfDotL (κ.map fun x : ℕ => (x : ℤ))
        ((rfCols (((coxeterSystem Tag.E6).wordProd ω)⁻¹)).getD (c : ℕ) []) =
      ∑ j : Fin Tag.E6.rank, ((κ.getD (j : ℕ) 0 : ℕ) : ℤ) *
        (((coxeterSystem Tag.E6).wordProd ω)⁻¹ • (Pi.single c 1 : Fin Tag.E6.rank → ℤ)) j := by
    intro c
    rw [rfCols_getD, hmc, rfDotL_ofFn]
  rw [e1, e1] at h'
  exact Int.dvd_of_emod_eq_zero h'

theorem rfHTable_words_lt : ∀ t ∈ rfHTable, ∀ n ∈ t.2.2, n < 6 := by
  decide +kernel

theorem exists_fin_word : ∀ ω : List ℕ, (∀ n ∈ ω, n < 6) →
    ∃ ω' : List (Fin Tag.E6.rank), ω'.map (fun i : Fin Tag.E6.rank => (i : ℕ)) = ω
  | [], _ => ⟨[], rfl⟩
  | n :: ω, h => by
    obtain ⟨ω', hω'⟩ := exists_fin_word ω fun m hm => h m (List.mem_cons_of_mem _ hm)
    exact ⟨⟨n, h n List.mem_cons_self⟩ :: ω', by simp [hω']⟩

theorem e6_regular_elliptic_conj (w : WeylGroup Tag.E6) (k₁ k₂ : Fin Tag.E6.rank → ℕ)
    (hreg : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      ¬ ((3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧ (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ)))
    (hfix₁ : ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
      (∑ i, (k₁ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k₁ t : ℤ))
    (hfix₂ : ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
      (∑ i, (k₂ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k₂ t : ℤ)) :
    (∃ l : Fin Tag.E6.rank → ℤ, l ≠ 0 ∧
        ∀ v : Fin Tag.E6.rank → ℤ, ∑ i, l i * (w • v) i = ∑ i, l i * v i) ∨
      ∃ ω : List (Fin Tag.E6.rank),
        InvFixedZ ((coxeterSystem Tag.E6).wordProd ω) (fun j => (k₁ j : ℤ)) ∧
        InvFixedZ ((coxeterSystem Tag.E6).wordProd ω) (fun j => (k₂ j : ℤ)) ∧
        weylTwist TwistTag.E6 ((coxeterSystem Tag.E6).wordProd ω * w *
            ((coxeterSystem Tag.E6).wordProd ω)⁻¹) =
          (coxeterSystem Tag.E6).wordProd ω * w * ((coxeterSystem Tag.E6).wordProd ω)⁻¹ ∧
        ∃ (m : Fin Tag.E6.rank → ℤ) (k₀ : Fin Tag.E6.rank → ℕ),
          (∀ j : Fin Tag.E6.rank, (3 : ℤ) ∣ (∑ l, Tag.E6.cartan l j * m l) - (k₀ j : ℤ)) ∧
          (∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
            (∑ i, (k₀ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k₀ t : ℤ)) ∧
          ¬ ∀ i, (3 : ℤ) ∣ (w • m) i - m i := by
  classical
  set K₁ : List ℕ := List.ofFn fun i : Fin Tag.E6.rank => k₁ i % 3 with hK₁
  set K₂ : List ℕ := List.ofFn fun i : Fin Tag.E6.rank => k₂ i % 3 with hK₂
  have hK₁len : K₁.length = Tag.E6.rank := by simp [hK₁]
  have hK₂len : K₂.length = Tag.E6.rank := by simp [hK₂]
  have hK₁3 : ∀ x ∈ K₁, x < 3 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact Nat.mod_lt _ (by norm_num)
  have hK₂3 : ∀ x ∈ K₂, x < 3 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact Nat.mod_lt _ (by norm_num)
  have hf₁ : RfFixes w K₁ := rfFixes_of_fin w k₁ hfix₁
  have hf₂ : RfFixes w K₂ := rfFixes_of_fin w k₂ hfix₂
  have hregpos : ∀ a ∈ posRoots e6ArtifactRoots,
      ¬ (rootDot a K₁ % 3 = 0 ∧ rootDot a K₂ % 3 = 0) := by
    rintro a ha ⟨h1, h2⟩
    have haA : a ∈ e6ArtifactRoots := (List.mem_filter.1 ha).1
    have hal : a.length = Tag.E6.rank := length_of_mem_artifactRoots (τ := Tag.E6) haA
    have hα : List.ofFn (fun i : Fin Tag.E6.rank => a.getD (i : ℕ) 0) = a := rf_ofFn_getD a hal
    have hroot : IsRoot Tag.E6 (fun i : Fin Tag.E6.rank => a.getD (i : ℕ) 0) :=
      isRoot_iff_mem_artifactRoots.2 (by rw [hα]; exact haA)
    rw [← hα, hK₁, rootDot_ofFn] at h1
    rw [← hα, hK₂, rootDot_ofFn] at h2
    exact hreg _ hroot ⟨three_dvd_sum_of_mod _ k₁ h1, three_dvd_sum_of_mod _ k₂ h2⟩
  obtain ⟨p, hp, hpe⟩ := rfCover_sound hK₁len hK₂len hK₁3 hK₂3 hregpos
  obtain ⟨hp1, hp2, hp13, hp23⟩ := rfPlaneBases_wf p hp
  have hr6 : Tag.E6.rank = 6 := rfl
  have hl₁₂ : K₁.length = K₂.length := by rw [hK₁len, hK₂len]
  have hlp : p.1.length = p.2.length := by rw [hp1, hp2]
  have hp1' : p.1.length = Tag.E6.rank := hp1.trans hr6.symm
  have hp2' : p.2.length = Tag.E6.rank := hp2.trans hr6.symm
  have hbitK : ∀ (v : List ℕ) (a b : ℕ), a < 3 → b < 3 → comb a b K₁ K₂ = v →
      Nat.testBit (planeBits K₁ K₂) (vecIdx v) = true := by
    intro v a b ha hb hv
    exact (planeBits_spec hl₁₂ (by rw [← hv, length_comb hl₁₂]) (by rw [← hv]; exact comb_lt)).2
      ⟨a, b, ha, hb, hv⟩
  have hbitP : ∀ (v : List ℕ) (a b : ℕ), a < 3 → b < 3 → comb a b p.1 p.2 = v →
      Nat.testBit (planeBits p.1 p.2) (vecIdx v) = true := by
    intro v a b ha hb hv
    exact (planeBits_spec hlp (by rw [← hv, length_comb hlp]) (by rw [← hv]; exact comb_lt)).2
      ⟨a, b, ha, hb, hv⟩
  have hK₁ab : ∃ a b, a < 3 ∧ b < 3 ∧ comb a b p.1 p.2 = K₁ := by
    have h := hbitK K₁ 1 0 (by norm_num) (by norm_num) (rf_comb_one_zero K₁ K₂ hl₁₂ hK₁3)
    rw [← hpe] at h
    exact (planeBits_spec hlp (hK₁len.trans (hr6.trans hp1.symm)) hK₁3).1 h
  have hK₂ab : ∃ a b, a < 3 ∧ b < 3 ∧ comb a b p.1 p.2 = K₂ := by
    have h := hbitK K₂ 0 1 (by norm_num) (by norm_num) (rf_comb_zero_one K₁ K₂ hl₁₂ hK₂3)
    rw [← hpe] at h
    exact (planeBits_spec hlp (hK₂len.trans (hr6.trans hp1.symm)) hK₂3).1 h
  have hp1K : ∃ a b, a < 3 ∧ b < 3 ∧ comb a b K₁ K₂ = p.1 := by
    have h := hbitP p.1 1 0 (by norm_num) (by norm_num) (rf_comb_one_zero p.1 p.2 hlp hp13)
    rw [hpe] at h
    exact (planeBits_spec hl₁₂ (hp1.trans (hr6.trans hK₁len.symm)) hp13).1 h
  have hp2K : ∃ a b, a < 3 ∧ b < 3 ∧ comb a b K₁ K₂ = p.2 := by
    have h := hbitP p.2 0 1 (by norm_num) (by norm_num) (rf_comb_zero_one p.1 p.2 hlp hp23)
    rw [hpe] at h
    exact (planeBits_spec hl₁₂ (hp2.trans (hr6.trans hK₁len.symm)) hp23).1 h
  have hfp1 : RfFixes w p.1 := by
    obtain ⟨a, b, -, -, hab⟩ := hp1K
    rw [← hab]
    exact rfFixes_comb w hK₁len hK₂len a b hf₁ hf₂
  have hfp2 : RfFixes w p.2 := by
    obtain ⟨a, b, -, -, hab⟩ := hp2K
    rw [← hab]
    exact rfFixes_comb w hK₁len hK₂len a b hf₁ hf₂
  obtain ⟨t, ht, hte⟩ : ∃ t ∈ rfHTable, (t.1, t.2.1) = p := by
    have hmem : p ∈ rfHTable.map (fun t => (t.1, t.2.1)) := by
      rw [rfHTable_planes]
      exact hp
    obtain ⟨t, ht, hte⟩ := List.mem_map.1 hmem
    exact ⟨t, ht, hte⟩
  have hchk := List.all_eq_true.1 rfHPlanes_true t ht
  have ht1 : t.1 = p.1 := congrArg Prod.fst hte
  have ht2 : t.2.1 = p.2 := congrArg Prod.snd hte
  rw [ht1, ht2] at hchk
  obtain ⟨ω, hω⟩ := exists_fin_word t.2.2 (rfHTable_words_lt t ht)
  unfold rfHPlaneCheck at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨hinv1, hinv2⟩, hleaves⟩ := hchk
  have hmem := mem_rfLeaves ((List.range 6).map (rfCands p.1 p.2)) (rfCols w) []
    (rfCols_validFrom w hp1' hp2' hfp1 hfp2)
  have hcl : (rfCols w).length = 6 := by
    unfold rfCols; rw [List.length_ofFn]; rfl
  rw [List.nil_append, hcl] at hmem
  have hok := List.all_eq_true.1 hleaves _ hmem
  unfold rfHLeafOK at hok
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hok
  rcases hok with (hc | hfix) | ⟨hcomm, hwit⟩
  · exact absurd (rfCCond_rfCols w) (by simp [hc])
  · exact Or.inl (exists_fixed_of_rfHasFix w hfix)
  · right
    rw [← hω] at hinv1 hinv2 hcomm
    have hI1 := invFixedZ_of_rfInvFix ω hp1' hinv1
    have hI2 := invFixedZ_of_rfInvFix ω hp2' hinv2
    have hmodK : ∀ (k : Fin Tag.E6.rank → ℕ) (a b : ℕ),
        (comb a b p.1 p.2 = List.ofFn fun i : Fin Tag.E6.rank => k i % 3) →
        InvFixedZ ((coxeterSystem Tag.E6).wordProd ω) (fun j => (k j : ℤ)) := by
      intro k a b hab
      refine (InvFixedZ.lin (v := (coxeterSystem Tag.E6).wordProd ω) (a : ℤ) (b : ℤ) hI1 hI2).congr
        (fun j => ?_)
      have h1 := rfFx_getD_comb a b p.1 p.2 hlp (j : ℕ)
      rw [hab, rfFx_getD_ofFn k j] at h1
      show (3 : ℤ) ∣ ((a : ℤ) * ((p.1.getD (j : ℕ) 0 : ℕ) : ℤ) +
        (b : ℤ) * ((p.2.getD (j : ℕ) 0 : ℕ) : ℤ)) - (k j : ℤ)
      omega
    refine ⟨ω, ?_, ?_, ?_, ?_⟩
    · obtain ⟨a, b, -, -, hab⟩ := hK₁ab
      exact hmodK k₁ a b hab
    · obtain ⟨a, b, -, -, hab⟩ := hK₂ab
      exact hmodK k₂ a b hab
    · exact weylTwist_eq_of_rfRhoComm _ (by rw [← rfConjCols_eq ω w]; exact hcomm)
    · exact exists_witness_of_rfWitness w hwit

end Soundness

end CFSG.LieType.SeitzGeneration.ExcWideThree
