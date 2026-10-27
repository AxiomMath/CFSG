module

public import CFSG.LieType.SeitzGeneration.UnitaryHyperNonsplitCore
public import CFSG.LieType.SeitzGeneration.UnitaryHyperDiag
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open TauCeti CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
  URankThree Nonsplit Centers CFSG.Assembly.LowTwoRank

section Main

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem hyperClosure_eq_top_nonsplit (hU : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hpq1 : ¬ p ∣ ℓ ^ f + 1) (hpq : ¬ p ∣ ℓ ^ f - 1)
    {A : Subgroup (SUid σ₀ n)} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) (hcard : Nat.card A = p ^ 3) :
    hyperClosure p ⊤ A = ⊤ := by
  classical
  have hσ := isUnitaryInvolution hU
  have hfp : Fact p.Prime := ⟨hp⟩
  have hAfin : Finite A :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  have : Fintype A := Fintype.ofFinite A
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h1 := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hU.prime hp).mp h1).symm
  have hcastK : ∀ (B : Subgroup (SUid σ₀ n)) [Fintype B] (k : ℕ), Nat.card B = p ^ k →
      (Fintype.card B : K) ≠ 0 := fun B _ k hk => by
    rw [Fintype.card_eq_nat_card, hk]
    push_cast
    exact pow_ne_zero k hpK
  have hAK : (Fintype.card A : K) ≠ 0 := hcastK A 3 hcard
  have he3 := three_le_ordNegQ hp hp5 hU.prime hpℓ hU.one_le hpq1 hpq
  set H := hyperClosure p ⊤ A with hHdef
  set ρ := act σ₀ n with hρ
  have hcardF : ∀ F : Subgroup (SUid σ₀ n), F ≤ A → F.relIndex A = p → Nat.card F = p ^ 2 := by
    intro F hFA hF
    have h := Subgroup.relIndex_mul_card F A
    rw [inf_of_le_left hFA, hF, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h]; ring)
  have hFfin : ∀ F : Subgroup (SUid σ₀ n), F ≤ A → Finite F := fun F hFA =>
    Finite.of_injective (Subgroup.inclusion hFA) (Subgroup.inclusion_injective hFA)
  have hfixA : ∀ F : Subgroup (SUid σ₀ n), F ≤ A →
      HyperBlocks.fixSub ρ F = HyperBlocks.fixSub ρ A ⊔ HyperBlocks.block ρ A F :=
    fun F hFA => HyperBlocks.fixSub_eq_sup ρ hAK hFA
  have hfixAnti : ∀ F F' : Subgroup (SUid σ₀ n), F ≤ F' →
      HyperBlocks.fixSub ρ F' ≤ HyperBlocks.fixSub ρ F := fun F F' h v hv g hg => hv g (h hg)
  have hcenF : ∀ F : Subgroup (SUid σ₀ n), F ≤ A → F.relIndex A = p →
      AllCenters H (HyperBlocks.fixSub ρ F) := fun F hFA hF v hv hvi =>
    isCenter_of_mem_fixSub hσ.invol hFA hF hv hvi
  have hcenL : ∀ L : Subgroup (SUid σ₀ n), L ≤ A → L ≠ ⊥ →
      AllCenters H (HyperBlocks.fixSub ρ L) := by
    intro L hLA hL
    have : Finite L := hFfin L hLA
    have : Fintype L := Fintype.ofFinite L
    have hLc : ∃ k, Nat.card L = p ^ k := by
      have hdvd : Nat.card L ∣ p ^ 3 := hcard ▸ Subgroup.card_dvd_of_le hLA
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      exact ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hLc
    set U := HyperBlocks.fixSub ρ L with hUdef
    have hBl : ((idForm hU n).domRestrict₁₂ U U).SeparatingLeft := by
      intro w hw
      refine Subtype.ext (eq_zero_of_fixSub (hcastK L k hk) w.2 fun w' hw' => ?_)
      have := hw ⟨w', hw'⟩
      rw [LinearMap.domRestrict₁₂_apply, idForm_eq_herm] at this
      exact this
    obtain ⟨m, x, hx, hspan⟩ : ∃ (m : ℕ) (x : Fin m → Fin n → K), ONExt.IsON σ₀ x ∧
        Submodule.span K (Set.range x) = U := by
      obtain ⟨b, hb⟩ := hU.exists_orthonormal_basis ((idForm_isSymm hU n).domRestrict U) hBl
      refine ⟨_, fun i => (b i : Fin n → K), fun i j => ?_, ?_⟩
      · have := hb i j
        rw [LinearMap.domRestrict₁₂_apply, idForm_eq_herm] at this
        exact this
      · have h1 : Submodule.span K (Set.range fun i => (b i : Fin n → K)) =
            (Submodule.span K (Set.range b)).map U.subtype := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
        rw [h1, b.span_eq, Submodule.map_top, Submodule.range_subtype]
    have hmemU : ∀ c, orthoEmb x c ∈ U := fun c => hspan.le (orthoEmb_mem_span x c)
    have hAU : ∀ a ∈ A, ∀ c, ∃ d, a • orthoEmb x c = orthoEmb x d := by
      intro a ha c
      have h1 : a • orthoEmb x c ∈ U := smul_mem_fixSub hcomm hLA ha (hmemU c)
      obtain ⟨d, hd⟩ := (mem_span_range_iff x _).1 (hspan.ge h1)
      exact ⟨d, hd.symm⟩
    obtain ⟨y₀, hy₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hL
    have hy₀U : ∀ c, (y₀ : SUid σ₀ n) • orthoEmb x c = orthoEmb x c := fun c =>
      (hmemU c) y₀ y₀.2
    have hy₀1 : (y₀ : SUid σ₀ n) ≠ 1 := fun h => hy₀ (Subtype.ext h)
    have hAll := allCenters_of_fix hU hp hp5 hpℓ hpq1 hpq hcomm hexp hcard hx hAU (hLA y₀.2)
      hy₀1 hy₀U
    rwa [hspan] at hAll
  have hbb : ∀ F F' : Subgroup (SUid σ₀ n), F ≤ A → F.relIndex A = p → F' ≤ A →
      F'.relIndex A = p → F ≠ F' → ∀ u ∈ HyperBlocks.block ρ A F,
        ∀ v ∈ HyperBlocks.block ρ A F', herm σ₀ u v = 0 := by
    intro F F' hFA hF hF'A hF' hne u hu v hv
    have : Finite F := hFfin F hFA
    have : Fintype F := Fintype.ofFinite F
    exact herm_block_block hAK (hcastK F 2 (hcardF F hFA hF)) hcomm hFA hF'A
      (HyperBlocks.sup_eq_of_ne_relIndex_prime hp hFA hF'A hF hF' hne) hu hv
  have hfb : ∀ F : Subgroup (SUid σ₀ n), ∀ u ∈ HyperBlocks.fixSub ρ A,
      ∀ v ∈ HyperBlocks.block ρ A F, herm σ₀ u v = 0 := fun F u hu v hv =>
    herm_fixSub_block hAK hu hv
  have hdimB : ∀ F : Subgroup (SUid σ₀ n), F ≤ A → F.relIndex A = p →
      HyperBlocks.block ρ A F ≠ ⊥ → ordNegQ ℓ f p ≤ Module.finrank K (HyperBlocks.block ρ A F) := by
    intro F hFA hF hne
    have : Finite F := hFfin F hFA
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨y, hyA, hyF⟩ : ∃ y ∈ A, y ∉ F := by
      by_contra hcon
      push Not at hcon
      have hAF : A ≤ F := fun y hy => hcon y hy
      have h1 : F.relIndex A = 1 := Subgroup.relIndex_eq_one.mpr hAF
      rw [hF] at h1
      exact hp.one_lt.ne' h1
    have hdvd := ordNegQ_dvd_finrank_block hU hp hpℓ hAK (hcastK F 2 (hcardF F hFA hF)) hcomm hFA
      hF hyA hyF (hexp y hyA)
    exact Nat.le_of_dvd (Submodule.one_le_finrank_iff.mpr hne) hdvd
  have hdimOK : ∀ (W : Submodule K (Fin n → K)), ordNegQ ℓ f p ≤ Module.finrank K W →
      (4 ≤ Module.finrank K W ∨ (3 ≤ Module.finrank K W ∧ ∃ s : K, s ≠ 0 ∧ σ₀ s * s ≠ 1)) := by
    intro W hle
    by_cases hq : ℓ ^ f = 2
    · left
      have := four_le_ordNegQ_of_two hp (by omega : 3 < p) hpℓ hU.prime hq
      omega
    · right
      refine ⟨by omega, ?_⟩
      obtain ⟨s, hs0, hs⟩ := exists_norm_ne_one hU hq
      exact ⟨s, hs0, by rw [unitaryInvolution_eq_bar hU]; exact hs⟩
  have hsum : ∀ v : Fin n → K, v ∈ ⨆ (F : Subgroup (SUid σ₀ n)) (_ : F ≤ A ∧ F.relIndex A = p),
      HyperBlocks.fixSub ρ F := by
    intro v
    have hcommA : ∀ a b : A, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
    have hexpA : ∀ a : A, a ^ p = 1 := fun a => Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hexp a a.2)
    have h := mem_iSup_hyperFixed_top hpK hcommA hexpA (ρ.comp A.subtype) ⊤
      (fun _ _ _ => Submodule.mem_top) (k := 3) (by norm_num) hcard (Submodule.mem_top (x := v))
    refine (iSup₂_le fun F' hF' => ?_ : (⨆ (F' : Subgroup A) (_ : F'.index = p),
      hyperFixed (ρ.comp A.subtype) F' ⊓ ⊤) ≤ _) h
    refine le_iSup₂_of_le (F'.map A.subtype) ⟨Subgroup.map_subtype_le _, ?_⟩ ?_
    · have hsub : (F'.map A.subtype).subgroupOf A = F' :=
        Subgroup.comap_map_eq_self_of_injective A.subtype_injective F'
      rw [Subgroup.relIndex, hsub]
      exact hF'
    · intro w hw y hy
      obtain ⟨y', hy', rfl⟩ := hy
      exact (mem_hyperFixed.1 hw.1) y' hy'
  let ι := {F : Subgroup (SUid σ₀ n) // (F ≤ A ∧ F.relIndex A = p) ∧ HyperBlocks.block ρ A F ≠ ⊥}
  have : Finite ι := Finite.of_injective (fun i : ι => (i.1 : Set (SUid σ₀ n)))
    (fun a b h => Subtype.ext (SetLike.coe_injective h))
  have : Fintype ι := Fintype.ofFinite ι
  have hfixle : ∀ F : Subgroup (SUid σ₀ n), F ≤ A → F.relIndex A = p →
      HyperBlocks.block ρ A F = ⊥ → HyperBlocks.fixSub ρ F ≤ HyperBlocks.fixSub ρ A := by
    intro F hFA _ hb
    rw [hfixA F hFA, hb, sup_bot_eq]
  have hne : Nonempty ι := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hall : ∀ v : Fin n → K, v ∈ HyperBlocks.fixSub ρ A := by
      intro v
      refine (iSup₂_le fun F hF => ?_ : (⨆ (F : Subgroup (SUid σ₀ n))
        (_ : F ≤ A ∧ F.relIndex A = p), HyperBlocks.fixSub ρ F) ≤ HyperBlocks.fixSub ρ A) (hsum v)
      refine hfixle F hF.1 hF.2 ?_
      by_contra hb
      exact hemp.elim ⟨F, hF, hb⟩
    have hA1 : A ≤ ⊥ := fun a ha => Subgroup.mem_bot.mpr (ext_smul σ₀ fun v => by
      rw [one_smul]
      exact hall v a ha)
    have h1 : Nat.card A = 1 := by
      rw [le_bot_iff.mp hA1]
      exact Subgroup.card_bot
    rw [hcard] at h1
    exact absurd h1 (Nat.one_lt_pow (by norm_num) hp.one_lt).ne'
  obtain ⟨i₁⟩ := hne
  let W : ι → Submodule K (Fin n → K) := fun i =>
    if i = i₁ then HyperBlocks.fixSub ρ i.1 else HyperBlocks.block ρ A i.1
  have hWle : ∀ i, W i ≤ HyperBlocks.fixSub ρ i.1 := fun i => by
    simp only [W]
    split_ifs
    · exact le_rfl
    · exact inf_le_left
  have hWsup : ∀ i, W i ≤ HyperBlocks.fixSub ρ A ⊔ HyperBlocks.block ρ A i.1 := fun i =>
    (hWle i).trans (hfixA i.1 i.2.1.1).le
  have hWblk : ∀ i, HyperBlocks.block ρ A i.1 ≤ W i := fun i => by
    simp only [W]
    split_ifs
    · exact inf_le_left
    · exact le_rfl
  have hWi₁ : W i₁ = HyperBlocks.fixSub ρ i₁.1 := by simp [W]
  have hWne : ∀ i, i ≠ i₁ → W i = HyperBlocks.block ρ A i.1 := fun i hi => by simp [W, hi]
  have horthA : ∀ i j : ι, i ≠ j → ∀ u ∈ HyperBlocks.fixSub ρ A ⊔ HyperBlocks.block ρ A i.1,
      ∀ v ∈ HyperBlocks.block ρ A j.1, herm σ₀ u v = 0 := by
    intro i j hij u hu v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [herm_add_left, hfb _ a ha v hv, hbb i.1 j.1 i.2.1.1 i.2.1.2 j.2.1.1 j.2.1.2
      (fun h => hij (Subtype.ext h)) b hb v hv, add_zero]
  have horth : ∀ i j : ι, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, herm σ₀ u v = 0 := by
    intro i j hij u hu v hv
    by_cases hj : j = i₁
    · have hi : i ≠ i₁ := fun h => hij (h.trans hj.symm)
      rw [hWne i hi] at hu
      exact herm_eq_zero_comm σ₀ hσ.invol (horthA j i (Ne.symm hij) v (hWsup j hv) u hu)
    · rw [hWne j hj] at hv
      exact horthA i j hij u (hWsup i hu) v hv
  have hON : ∀ i, HasONBasis σ₀ (W i) := by
    intro i
    have hF := i.2.1
    have : Finite i.1 := hFfin i.1 hF.1
    have : Fintype i.1 := Fintype.ofFinite i.1
    have hFK := hcastK i.1 2 (hcardF i.1 hF.1 hF.2)
    have hsep : ((idForm hU n).domRestrict₁₂ (W i) (W i)).SeparatingLeft := by
      intro w hw
      have hw' : ∀ w' ∈ W i, herm σ₀ (w : Fin n → K) w' = 0 := fun w' hw'' => by
        have := hw ⟨w', hw''⟩
        rw [LinearMap.domRestrict₁₂_apply, idForm_eq_herm] at this
        exact this
      refine Subtype.ext ?_
      by_cases hi : i = i₁
      · have hwi : (w : Fin n → K) ∈ HyperBlocks.fixSub ρ i.1 := hWle i w.2
        refine eq_zero_of_fixSub hFK hwi fun w' hw'' => hw' w' ?_
        have : W i = HyperBlocks.fixSub ρ i.1 := by rw [hi]; exact hWi₁
        rw [this]
        exact hw''
      · have hwi : (w : Fin n → K) ∈ HyperBlocks.block ρ A i.1 := (hWne i hi).le w.2
        refine eq_zero_of_block hσ.invol hAK hFK hF.1 hwi fun w' hw'' => hw' w' ?_
        rw [hWne i hi]
        exact hw''
    refine hasONBasis_of_separatingLeft hU (W i) hsep (hdimOK (W i) ?_)
    exact (hdimB i.1 hF.1 hF.2 i.2.2).trans (Submodule.finrank_mono (hWblk i))
  have hA : ∀ i, AllCenters H (W i) := fun i v hv hvi =>
    hcenF i.1 i.2.1.1 i.2.1.2 v (hWle i hv) hvi
  have hiso : ∀ i, ∃ w ∈ W i, w ≠ 0 ∧ herm σ₀ w w = 0 := by
    intro i
    obtain ⟨m', y, hy, hyspan, hm'⟩ := hON i
    have hm2 : 2 ≤ m' := by rcases hm' with h | ⟨h, -⟩ <;> omega
    obtain ⟨c, hc0, hci⟩ := exists_isotropic_ne_zero hσ hm2
    refine ⟨orthoEmb y c, hyspan ▸ orthoEmb_mem_span y c, fun h0 => hc0 ?_, ?_⟩
    · exact ONExt.orthoEmb_injective hy (by rw [h0, map_zero])
    · rw [herm_orthoEmb hy]
      exact hci
  have hmix : ∀ i j : ι, i ≠ j → ∃ w₁ ∈ W i, ∃ w₂ ∈ W j, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧
      IsCenter H (w₁ + w₂) := by
    intro i j hij
    have hne' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    obtain ⟨w₁, hw₁, hw₁0, hw₁i⟩ := hiso i
    obtain ⟨w₂, hw₂, hw₂0, hw₂i⟩ := hiso j
    set L := i.1 ⊓ j.1 with hLdef
    have hLA : L ≤ A := inf_le_left.trans i.2.1.1
    have hLbot : L ≠ ⊥ := by
      intro hbot
      have hle := Subgroup.relIndex_inf_le (H := i.1) (K := j.1) (L := A)
      rw [i.2.1.2, j.2.1.2, ← hLdef, hbot] at hle
      have hbotA : (⊥ : Subgroup (SUid σ₀ n)).relIndex A = p ^ 3 := by
        rw [Subgroup.relIndex_bot_left, hcard]
      rw [hbotA] at hle
      have : p ^ 3 ≤ p ^ 2 := by simpa [pow_two] using hle
      have h2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num : 2 < 3)
      omega
    have hW₁L : W i ≤ HyperBlocks.fixSub ρ L := (hWle i).trans (hfixAnti L i.1 inf_le_left)
    have hW₂L : W j ≤ HyperBlocks.fixSub ρ L := (hWle j).trans (hfixAnti L j.1 inf_le_right)
    refine ⟨w₁, hw₁, w₂, hw₂, hw₁0, hw₂0, hcenL L hLA hLbot _
      (Submodule.add_mem _ (hW₁L hw₁) (hW₂L hw₂)) ?_⟩
    rw [herm_add_left, herm_add_right, herm_add_right, hw₁i, hw₂i, horth i j hij w₁ hw₁ w₂ hw₂,
      horth j i (Ne.symm hij) w₂ hw₂ w₁ hw₁]
    ring
  have htop : ⨆ i, W i = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    refine (iSup₂_le fun F hF => ?_ : (⨆ (F : Subgroup (SUid σ₀ n))
      (_ : F ≤ A ∧ F.relIndex A = p), HyperBlocks.fixSub ρ F) ≤ ⨆ i, W i) (hsum v)
    rw [hfixA F hF.1]
    refine sup_le ?_ ?_
    · refine le_trans ?_ (le_iSup W i₁)
      rw [hWi₁]
      exact hfixAnti _ _ i₁.2.1.1
    · by_cases hb : HyperBlocks.block ρ A F = ⊥
      · rw [hb]
        exact bot_le
      · exact (hWblk ⟨F, hF, hb⟩).trans (le_iSup W ⟨F, hF, hb⟩)
  have hn4 : 4 ≤ n := by
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 2)
      (by rw [hcard]; exact pow_dvd_pow p (by norm_num))
    let ε : SUid σ₀ n ≃* unitarySU ℓ f K n :=
      MulEquiv.subgroupCongr (suid_unitaryInvolution_eq hU n)
    let E' : Subgroup (unitarySU ℓ f K n) := (P.map A.subtype).map ε.toMonoidHom
    have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
      rintro _ ⟨_, ⟨a, -, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, ← map_pow, show a ^ p = 1 from Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact hexp a a.2), map_one, map_one]
    have hE'card : Nat.card E' = p ^ 2 := by
      rw [Subgroup.card_map_of_injective ε.injective,
        Subgroup.card_map_of_injective A.subtype_injective, hP]
    have := CFSG.RankThree.PartOne.CTP.two_mul_ordNegQ_le hU hp hpℓ E' hE'exp hE'card
    omega
  have : Nonempty ι := ⟨i₁⟩
  exact Centers.eq_top_of_blocks hσ hn4 W hON horth hA hmix htop

end Main

variable {ℓ f p : ℕ} {K : Type} [Field K]

theorem hyperGen_statedProj_unitary_nonsplit (h : UnitaryFieldData ℓ f K) {n : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hpq1 : ¬ p ∣ ℓ ^ f + 1) (hpq : ¬ p ∣ ℓ ^ f - 1)
    {E : Subgroup (StatedProj (StatedSU (n + 1) (ℓ ^ f) K))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) :
    HyperGen p (⊤ : Subgroup (StatedProj (StatedSU (n + 1) (ℓ ^ f) K))) E := by
  classical
  have hfin := h.finite
  have hfp : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  have hker : ¬ p ∣ Nat.card (projSUid h (n + 1)).ker := by
    rw [card_ker_projSUid h (by omega)]
    exact fun hd => hpq1 (hd.trans (Nat.gcd_dvd_right _ _))
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨A, hAE, hAdis, hAcomm, hAexp, hAcard⟩ :=
    exists_lift_elemAbelian (projSUid h (n + 1)) (projSUid_surjective h (n + 1)) hker hcomm hE.2
  have htop := hyperClosure_eq_top_nonsplit h hp hp5 hpℓ hpq1 hpq hAcomm hAexp
    (hAcard.trans hcard)
  intro k _
  obtain ⟨g, rfl⟩ := projSUid_surjective h (n + 1) k
  have hg : g ∈ hyperClosure p ⊤ A := by
    rw [htop]
    exact Subgroup.mem_top g
  exact map_hyperClosure_le_of_lift hAE hAdis ⟨g, hg, rfl⟩

theorem seitzHyperLie_unitary_nonsplit : SeitzHyperLie fun d p _ => UNonsplitPrime d p := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hlist E₀ hE hcard ⟨m, q, hd, hpq, hpq1⟩
  simp only at hd
  subst hd
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
    (ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
    (ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have hqc := card_twistedA m q hv
  have hpℓ : p ≠ ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ := hpd
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    have hp3 : p = 3 := by
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hp (by decide)
    subst hp3
    have h3 : 3 ∣ q.card := by omega
    rw [PrimePower.card_def] at h3
    have hq3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    exact hpℓ (hq3.trans (LieTypeIndex.characteristic_twistedA m q).symm)
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  have hE' : IsElemAbelian p (E₀.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hcard' : Nat.card (E₀.map e.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  exact hyperGen_top_of_mulEquiv e (hyperGen_statedProj_unitary_nonsplit hU hp hp5 hpℓ
    (by rw [hqc]; exact hpq1) (by rw [hqc]; exact hpq) hE' hcard')

theorem unitaryHyperExNonsplit : UnitaryHyperExNonsplit := seitzHyperLie_unitary_nonsplit.toEx

theorem hyperExFor_unitary : HyperExFor fun d => IsUnitaryIndex' d.1 :=
  hyperExFor_unitary_of_nonsplit unitaryHyperExNonsplit

theorem hyperExFor_classical_of_orthogonal (ho : HyperExFor fun d => IsOrthogonalIndex d.1) :
    HyperExFor fun d => IsClassicalIndex d.1 :=
  hyperExFor_classical' hyperExFor_unitary ho

end CFSG.LieType.SeitzGeneration
