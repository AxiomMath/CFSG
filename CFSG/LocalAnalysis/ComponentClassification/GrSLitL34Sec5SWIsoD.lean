module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoE
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIso
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoCount

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso CFSG.LieType.Multipliers.L34


namespace WStd

variable {G : Type} [Group G] [Finite G] {J S : Subgroup G} {hSN : S ≤ normalizer (J : Set G)}

theorem exists_not_mem_of_alt (D : WStd J S hSN) (hJ : ⁅J, J⁆ = J) (hS2 : IsPGroup 2 S)
    {E₁ : Subgroup G} (hE₁S : E₁ ≤ S) (hE₁K : E₁ ≤ withKernel J) (hE₁ : IsElemTwo E₁)
    (h4 : Nat.card E₁ = 4) {k : ℕ} (hk : k < 64)
    (hψE₁ : ∀ w (hw : w ∈ E₁), D.ψ ⟨w, hE₁S hw⟩ = 1 ∨ D.ψ ⟨w, hE₁S hw⟩ = wordPerm (tg k))
    {f : G} (hf : f ∈ S) (hf2 : f * f = 1) (hfK : f ∉ withKernel J)
    (hfc : ∀ e ∈ E₁, e * f = f * e) {t i : ℕ} (ht : t < 64) (hi : i < 36)
    (hβ : ∀ x : MElt, x.1 < 64 → betaHat J (hSN hf) (nfM D.l x) = nfM D.l (betaYM t i x))
    (halt : (∃ x ∈ fixInvs D.kb t i, eqKB D.kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x) = true ∧
        x.1 ≠ 0 ∧ x.1 ≠ k) ∨
      (∃ a ∈ (fixInvs D.kb t i).filter (fun x =>
          eqKB D.kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        ∃ b ∈ (fixInvs D.kb t i).filter (fun x =>
          eqKB D.kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        ∃ c ∈ (fixInvs D.kb t i).filter (fun x =>
          eqKB D.kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        ∃ d ∈ (fixInvs D.kb t i).filter (fun x =>
          eqKB D.kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        eqKB D.kb b a = false ∧ eqKB D.kb c a = false ∧ eqKB D.kb c b = false ∧
          eqKB D.kb d a = false ∧ eqKB D.kb d b = false ∧ eqKB D.kb d c = false)) :
    ∃ p ∈ S ⊓ withKernel J, p * p = 1 ∧ (∀ g ∈ E₁ ⊔ zpowers f, p * g = g * p) ∧
      p ∉ E₁ ⊔ zpowers f := by
  obtain ⟨hFK, -, -⟩ := sup_zpowers_inf_withKernel hE₁ hE₁K hf2 hfK hfc
  have hmemE₁ : ∀ p ∈ J, p ∈ E₁ ⊔ zpowers f → p ∈ E₁ := fun p hp hpF => by
    rw [← hFK]
    exact mem_inf.mpr ⟨hpF, mem_sup_left hp⟩
  rcases halt with ⟨x, hx, hxk, hx0, hxk'⟩ | h4'
  · obtain ⟨p, hpS, hpJ, hp2, -, hpc, hψp, -⟩ :=
      D.exists_of_model hJ hS2 hE₁S hk hψE₁ hf ht hi hβ hx hxk
    refine ⟨p, mem_inf.mpr ⟨hpS, mem_sup_left hpJ⟩, hp2, hpc, fun hpF => ?_⟩
    have hpE₁ := hmemE₁ p hpJ hpF
    have hx64 : x.1 < 64 := lt_of_mem_allM (mem_fixInvs.mp hx).1
    rcases hψE₁ p hpE₁ with h1 | h1
    · rw [hψp, ← wordPerm_tg_zero'] at h1
      exact hx0 (tg_injective hx64 (by norm_num) h1)
    · rw [hψp] at h1
      exact hxk' (tg_injective hx64 hk h1)
  · obtain ⟨a, ha, b, hb, c, hc, d, hd, hba, hca, hcb, hda, hdb, hdc⟩ := h4'
    have hmk : ∀ x ∈ (fixInvs D.kb t i).filter (fun x =>
        eqKB D.kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        x.1 < 64 ∧ ∃ p, ∃ hpS : p ∈ S, ∃ hpJ : p ∈ J, p * p = 1 ∧ p ≠ 1 ∧
          (∀ g ∈ E₁ ⊔ zpowers f, p * g = g * p) ∧ jq J ⟨p, hpJ⟩ = nfM D.l x := by
      intro x hx
      obtain ⟨hxF, hxk⟩ := List.mem_filter.mp hx
      obtain ⟨p, hpS, hpJ, hp2, hp1, hpc, -, hpe⟩ :=
        D.exists_of_model hJ hS2 hE₁S hk hψE₁ hf ht hi hβ hxF hxk
      exact ⟨lt_of_mem_allM (mem_fixInvs.mp hxF).1, p, hpS, hpJ, hp2, hp1, hpc, hpe⟩
    obtain ⟨ha64, pa, hpaS, hpaJ, hpa2, hpa1, hpac, hpae⟩ := hmk a ha
    obtain ⟨hb64, pb, hpbS, hpbJ, hpb2, hpb1, hpbc, hpbe⟩ := hmk b hb
    obtain ⟨hc64, pc, hpcS, hpcJ, hpc2, hpc1, hpcc, hpce⟩ := hmk c hc
    obtain ⟨hd64, pd, hpdS, hpdJ, hpd2, hpd1, hpdc, hpde⟩ := hmk d hd
    have hne : ∀ {x y : MElt} {px py : G} (hpxJ : px ∈ J) (hpyJ : py ∈ J), x.1 < 64 →
        y.1 < 64 → jq J ⟨px, hpxJ⟩ = nfM D.l x → jq J ⟨py, hpyJ⟩ = nfM D.l y →
        eqKB D.kb y x = false → px ≠ py := by
      intro x y px py hpxJ hpyJ hx hy hpx hpy hyx hxy
      subst hxy
      have h3 : nfM D.l y = nfM D.l x := by rw [← hpx, ← hpy]
      rw [← eqKB_iff D.hQ D.hkb hy hx] at h3
      rw [h3] at hyx
      exact Bool.noConfusion hyx
    have hab := hne hpaJ hpbJ ha64 hb64 hpae hpbe hba
    have hac := hne hpaJ hpcJ ha64 hc64 hpae hpce hca
    have hbc := hne hpbJ hpcJ hb64 hc64 hpbe hpce hcb
    have had := hne hpaJ hpdJ ha64 hd64 hpae hpde hda
    have hbd := hne hpbJ hpdJ hb64 hd64 hpbe hpde hdb
    have hcd := hne hpcJ hpdJ hc64 hd64 hpce hpde hdc
    by_contra hall
    push Not at hall
    have hin : ∀ p (hpS : p ∈ S) (hpJ : p ∈ J), p * p = 1 →
        (∀ g ∈ E₁ ⊔ zpowers f, p * g = g * p) → p ∈ E₁ := fun p hpS hpJ hp2 hpc =>
      hmemE₁ p hpJ (hall p (mem_inf.mpr ⟨hpS, mem_sup_left hpJ⟩) hp2 hpc)
    have h5 := length_le_card (H := E₁) (l := [1, pa, pb, pc, pd])
      (by simp [Ne.symm hpa1, Ne.symm hpb1, Ne.symm hpc1, Ne.symm hpd1, hab, hac, hbc, had, hbd,
        hcd])
      (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact hin _ hpaS hpaJ hpa2 hpac
        · exact hin _ hpbS hpbJ hpb2 hpbc
        · exact hin _ hpcS hpcJ hpc2 hpcc
        · exact hin _ hpdS hpdJ hpd2 hpdc)
    rw [h4] at h5
    simp at h5

end WStd


theorem l34WCriterionDFact_of_certs : L34WCriterionDFact := by
  intro G _ _ J S hJ hL hT hS2 hSN E hES hE h4 hEC hiso
  obtain ⟨D⟩ := exists_wStd hJ hL hT hSN
  have hE₁E : E ⊓ withKernel J ≤ E := inf_le_left
  have hE₁S : E ⊓ withKernel J ≤ S := hE₁E.trans hES
  have hE₁K : E ⊓ withKernel J ≤ withKernel J := inf_le_right
  have hE₁ : IsElemTwo (E ⊓ withKernel J) := hE.1.mono hE₁E
  obtain ⟨c, hcEC, hc1⟩ : ∃ c ∈ E ⊓ coreActionKernel J, c ≠ 1 := by
    have hne : E ⊓ coreActionKernel J ≠ ⊥ := by
      intro h
      rw [h, card_bot] at hEC
      omega
    exact (Subgroup.bot_or_exists_ne_one _).resolve_left hne
  have hcE₁ : c ∈ E ⊓ withKernel J :=
    mem_inf.mpr ⟨(mem_inf.mp hcEC).1, mem_sup_right (mem_inf.mp hcEC).2⟩
  obtain ⟨k, hk, hψE₁, hk0⟩ :=
    D.exists_k hJ hS2 hE₁S hE₁K h4 hcE₁ (mem_inf.mp hcEC).2 hc1
  have hcase : ∀ f (hf : f ∈ S), f * f = 1 → f ∉ withKernel J →
      (∀ e ∈ E ⊓ withKernel J, e * f = f * e) →
      ∃ t < 64, ∃ i < 36, (D.ψ ⟨f, hf⟩)⁻¹ = yPerm t i ∧ (t, i) ∈ outerInvs ∧
        (∀ x : MElt, x.1 < 64 → betaHat J (hSN hf) (nfM D.l x) = nfM D.l (betaYM t i x)) ∧
        repInS.contains i = false ∧ yPerm t i * yPerm t i = 1 ∧ liftsKB D.kb i = true ∧
        k ∈ kVals t i := by
    intro f hf hf2 hfK hfc
    obtain ⟨t, ht, i, hi, hy, hl, hβ⟩ := D.model hf
    have ho := D.mem_outerInvs hJ hf hf2 hfK ht hi hy
    obtain ⟨hS, h2⟩ := D.outer_spec hJ hf hf2 hfK hi hy
    have hkv : k ∈ kVals t i := D.mem_kVals hf ht hi hβ hk (by
      rcases hk0 with h0 | ⟨w, hw, -, hψw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨w, hE₁S hw, hE₁.2 w hw, (hfc w hw).symm, hψw⟩)
    exact ⟨t, ht, i, hi, hy, ho, hβ, hS, h2, hl, hkv⟩
  have hbad : ∀ e (he : e ∈ E), e ∉ withKernel J → ∃ t < 64, ∃ i < 36,
      (D.ψ ⟨e, hES he⟩)⁻¹ = yPerm t i ∧ (t, i) ∈ outerInvs ∧ k ≠ 0 ∧
      typeOf t i = expType D.kb ∧ (kbZero D.kb = true ∨ kbCyc D.kb = true) ∧
      (kbFull D.kb = true ∨
        ∃ a ∈ (fixInvs D.kb t i).filter (fun x =>
          eqKB D.kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        ∃ b ∈ (fixInvs D.kb t i).filter (fun x =>
          eqKB D.kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        ∃ c ∈ (fixInvs D.kb t i).filter (fun x =>
          eqKB D.kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        eqKB D.kb b a = false ∧ eqKB D.kb c a = false ∧ eqKB D.kb c b = false) ∧
      ∀ x : MElt, x.1 < 64 → betaHat J (hSN (hES he)) (nfM D.l x) = nfM D.l (betaYM t i x) := by
    intro e he heK
    have hec : ∀ w ∈ E ⊓ withKernel J, w * e = e * w := fun w hw => hE.1.1 w (hE₁E hw) e he
    obtain ⟨t, ht, i, hi, hy, ho, hβ, hS, h2, hl, hkv⟩ := hcase e (hES he) (hE.1.2 e he) heK hec
    have hEeq : E ⊓ withKernel J ⊔ zpowers e = E := eq_sup_zpowers hE h4 he heK
    rcases dCase_spec D.hkbL ht hi hS h2 hl hkv with ha | hb | hc
    · exfalso
      obtain ⟨p, hp, hp2, hpc, hpF⟩ := D.exists_not_mem_of_alt hJ hS2 hE₁S hE₁K hE₁ h4 hk hψE₁
        (hES he) (hE.1.2 e he) heK hec ht hi hβ (Or.inl ha)
      rw [hEeq] at hpc hpF
      exact hpF (hiso p hp hp2 hpc)
    · exfalso
      obtain ⟨p, hp, hp2, hpc, hpF⟩ := D.exists_not_mem_of_alt hJ hS2 hE₁S hE₁K hE₁ h4 hk hψE₁
        (hES he) (hE.1.2 e he) heK hec ht hi hβ (Or.inr hb)
      rw [hEeq] at hpc hpF
      exact hpF (hiso p hp hp2 hpc)
    · exact ⟨t, ht, i, hi, hy, ho, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hβ⟩
  obtain ⟨e₀, he₀E, he₀K⟩ : ∃ e₀ ∈ E, e₀ ∉ withKernel J := by
    by_contra hne
    push Not at hne
    have h1 := Subgroup.card_le_of_le (fun g hg => mem_inf.mpr ⟨hg, hne g hg⟩ :
      E ≤ E ⊓ withKernel J)
    rw [hE.2, h4] at h1
    norm_num at h1
  obtain ⟨t₀, ht₀, i₀, hi₀, hy₀, ho₀, hk1, hlab₀, hZt, hthree, hβ₀⟩ := hbad e₀ he₀E he₀K
  have hC2 : Nat.card ↥(E ⊓ coreActionKernel J) = 2 := by
    rcases hk0 with h0 | ⟨w₀, hw₀, hw₀C, -⟩
    · exact absurd h0 hk1
    have hle : E ⊓ coreActionKernel J ≤ E ⊓ withKernel J := inf_le_inf_left _ le_sup_right
    have hdvd : Nat.card ↥(E ⊓ coreActionKernel J) ∣ 4 := h4 ▸ Subgroup.card_dvd_of_le hle
    have hne4 : Nat.card ↥(E ⊓ coreActionKernel J) ≠ 4 := fun h => hw₀C (by
      have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h, h4])
      rw [← heq] at hw₀
      exact (mem_inf.mp hw₀).2)
    have hle4 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(E ⊓ coreActionKernel J) = n at hEC hdvd hne4 hle4 ⊢
    interval_cases n <;> first | rfl | exact absurd rfl hne4 | (norm_num at hdvd)
  have hbadT : L34WBadType J S E := by
    by_cases hz : kbZero D.kb = true
    · right
      refine ⟨D.card_Z_of_kbZero hS2 hz, fun e he heK => ?_⟩
      obtain ⟨t, -, i, hi, hy, -, -, hlab, -, -, -⟩ := hbad e he heK
      simp only [expType, hz, ↓reduceIte] at hlab
      exact D.isL34Field_of_label (hES he) (hE.1.2 e he) heK hi hy hlab
    · left
      have hcyc : kbCyc D.kb = true := hZt.resolve_left hz
      refine ⟨D.isCyclic_Z_of_kbCyc hS2 hcyc, fun e he heK => ?_⟩
      obtain ⟨t, -, i, hi, hy, -, -, hlab, -, -, -⟩ := hbad e he heK
      simp only [expType, hz, Bool.false_eq_true, ↓reduceIte] at hlab
      exact D.isL34Unitary_of_label (hES he) (hE.1.2 e he) heK hi hy hlab
  have hEJ : S ⊓ zStarIn J ≠ ⊥ → E ⊓ withKernel J ≤ J := by
    intro hZ
    have hnf : kbFull D.kb ≠ true := fun hf => hZ (D.Z_eq_bot_of_kbFull hS2 hf)
    obtain ⟨a, ha, b, hb, c', hc', hba, hca, hcb⟩ := hthree.resolve_left hnf
    have hEeq : E ⊓ withKernel J ⊔ zpowers e₀ = E := eq_sup_zpowers hE h4 he₀E he₀K
    have hmk : ∀ x ∈ (fixInvs D.kb t₀ i₀).filter (fun x =>
        eqKB D.kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        x.1 < 64 ∧ ∃ p, ∃ hpJ : p ∈ J, p ∈ E ∧ p ≠ 1 ∧ jq J ⟨p, hpJ⟩ = nfM D.l x := by
      intro x hx
      obtain ⟨hxF, hxk⟩ := List.mem_filter.mp hx
      obtain ⟨p, hpS, hpJ, hp2, hp1, hpc, -, hpe⟩ :=
        D.exists_of_model hJ hS2 hE₁S hk hψE₁ (hES he₀E) ht₀ hi₀ hβ₀ hxF hxk
      rw [hEeq] at hpc
      exact ⟨lt_of_mem_allM (mem_fixInvs.mp hxF).1, p, hpJ,
        hiso p (mem_inf.mpr ⟨hpS, mem_sup_left hpJ⟩) hp2 hpc, hp1, hpe⟩
    obtain ⟨ha64, pa, hpaJ, hpaE, hpa1, hpae⟩ := hmk a ha
    obtain ⟨hb64, pb, hpbJ, hpbE, hpb1, hpbe⟩ := hmk b hb
    obtain ⟨hc64, pc, hpcJ, hpcE, hpc1, hpce⟩ := hmk c' hc'
    have hne : ∀ {x y : MElt} {px py : G} (hpxJ : px ∈ J) (hpyJ : py ∈ J), x.1 < 64 →
        y.1 < 64 → jq J ⟨px, hpxJ⟩ = nfM D.l x → jq J ⟨py, hpyJ⟩ = nfM D.l y →
        eqKB D.kb y x = false → px ≠ py := by
      intro x y px py hpxJ hpyJ hx hy hpx hpy hyx hxy
      subst hxy
      have h3 : nfM D.l y = nfM D.l x := by rw [← hpx, ← hpy]
      rw [← eqKB_iff D.hQ D.hkb hy hx] at h3
      rw [h3] at hyx
      exact Bool.noConfusion hyx
    have hab := hne hpaJ hpbJ ha64 hb64 hpae hpbe hba
    have hac := hne hpaJ hpcJ ha64 hc64 hpae hpce hca
    have hbc := hne hpbJ hpcJ hb64 hc64 hpbe hpce hcb
    have hEJle : E ⊓ J ≤ E ⊓ withKernel J := inf_le_inf_left _ le_sup_left
    have h4' := length_le_card (H := E ⊓ J) (l := [1, pa, pb, pc])
      (by simp [Ne.symm hpa1, Ne.symm hpb1, Ne.symm hpc1, hab, hac, hbc])
      (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact mem_inf.mpr ⟨hpaE, hpaJ⟩
        · exact mem_inf.mpr ⟨hpbE, hpbJ⟩
        · exact mem_inf.mpr ⟨hpcE, hpcJ⟩)
    have heq := Subgroup.eq_of_le_of_card_ge hEJle (by rw [h4]; simpa using h4')
    rw [← heq]
    exact inf_le_right
  refine ⟨⟨hC2, hbadT, hEJ⟩, fun s hsS hs2 hsc hsE => ?_⟩
  have hsK : s ∉ withKernel J := fun h => hsE (hiso s (mem_inf.mpr ⟨hsS, h⟩) hs2 hsc)
  have hsc₁ : ∀ e ∈ E ⊓ withKernel J, e * s = s * e := fun e he => (hsc e (hE₁E he)).symm
  obtain ⟨t, ht, i, hi, hy, -, hβ, hS, h2, hl, hkv⟩ := hcase s hsS hs2 hsK hsc₁
  have he₀s : e₀ * s = s * e₀ := (hsc e₀ he₀E).symm
  have he₀sK : e₀ * s ∉ withKernel J := by
    intro h
    apply hsE
    have h2 : (e₀ * s) * (e₀ * s) = 1 := by
      calc (e₀ * s) * (e₀ * s) = e₀ * (s * e₀) * s := by group
        _ = e₀ * (e₀ * s) * s := by rw [he₀s]
        _ = (e₀ * e₀) * (s * s) := by group
        _ = 1 := by rw [hE.1.2 e₀ he₀E, hs2, one_mul]
    have hc : ∀ e ∈ E, (e₀ * s) * e = e * (e₀ * s) := fun e he => by
      calc (e₀ * s) * e = e₀ * (s * e) := by group
        _ = e₀ * (e * s) := by rw [hsc e he]
        _ = (e₀ * e) * s := by group
        _ = (e * e₀) * s := by rw [hE.1.1 e₀ he₀E e he]
        _ = e * (e₀ * s) := by group
    have h1 := hiso (e₀ * s) (mem_inf.mpr ⟨mul_mem (hES he₀E) hsS, h⟩) h2 hc
    have h3 := mul_mem (inv_mem he₀E) h1
    rwa [inv_mul_cancel_left] at h3
  rcases dCase_spec D.hkbL ht hi hS h2 hl hkv with ha | hb | hc
  · exact D.exists_not_mem_of_alt hJ hS2 hE₁S hE₁K hE₁ h4 hk hψE₁ hsS hs2 hsK hsc₁ ht hi hβ
      (Or.inl ha)
  · exact D.exists_not_mem_of_alt hJ hS2 hE₁S hE₁K hE₁ h4 hk hψE₁ hsS hs2 hsK hsc₁ ht hi hβ
      (Or.inr hb)
  · exfalso
    have hcomm : D.ψ ⟨s, hsS⟩ * D.ψ ⟨e₀, hES he₀E⟩ =
        D.ψ ⟨e₀, hES he₀E⟩ * D.ψ ⟨s, hsS⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext he₀s.symm
    obtain ⟨-, -, hS₀, h2₀⟩ := outer_of_mem ho₀
    refine typeOf_ne ht₀ hi₀ ht hi hS₀ hS h2₀ h2 ?_ ?_ (hlab₀.trans hc.2.1.symm)
    · rw [← hy₀, ← hy, ← mul_inv_rev, ← mul_inv_rev, hcomm]
    · rw [← hy₀, ← hy, ← mul_inv_rev, ← map_mul]
      intro hS'
      apply he₀sK
      have h1 := GrS4.mem_withKernel_of_realization_mem_S hJ hSN D.hQ.qsurj D.hQ.ker D.hψ
        (⟨s, hsS⟩ * ⟨e₀, hES he₀E⟩) ((inv_mem_iff).mp hS')
      simpa [he₀s] using h1

end CFSG.ComponentClassification.GrSLit.GrS5S
