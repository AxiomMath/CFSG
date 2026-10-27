module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Cover

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

namespace Thm46Data

variable {M₁ M₂ : Subgroup G}

omit [Finite G] in
theorem oddCoreIn_le_normalizer (hd : Thm46Data L M₁ M₂) {M : Subgroup G}
    (hM : M = M₁ ∨ M = M₂) : oddCoreIn (M₁ ⊔ M₂) ≤ normalizer (M : Set G) := by
  intro x hx
  have hxD : x ∈ M₁ ⊔ M₂ := map_subtype_le _ hx
  rcases hM with rfl | rfl
  · exact hd.toThm46Pair.le_normalizer hxD
  · rw [sup_comm] at hxD
    exact hd.toThm46Pair.symm.le_normalizer hxD

theorem mem_coreActionKernel_of_centralizes (h : FooteSec4 G L) (hd : Thm46Data L M₁ M₂)
    {M : Subgroup G} (hM : M = M₁ ∨ M = M₂) {t : G}
    (ht : ∀ a ∈ M ⊔ oddCoreIn (M₁ ⊔ M₂), t⁻¹ * a⁻¹ * t * a ∈ oddCoreIn (M₁ ⊔ M₂)) :
    t ∈ coreActionKernel M := by
  set D := M₁ ⊔ M₂ with hD
  set A := M ⊔ oddCoreIn D with hA
  have hMF : IsFooteM L M := by rcases hM with rfl | rfl; exacts [hd.hM₁, hd.hM₂]
  have hMD : M ≤ D := by rcases hM with rfl | rfl; exacts [le_sup_left, le_sup_right]
  have hDM : D ≤ normalizer (M : Set G) := by
    rcases hM with rfl | rfl
    · exact hd.toThm46Pair.le_normalizer
    · rw [hD, sup_comm]; exact hd.toThm46Pair.symm.le_normalizer
  have htA : t ∈ normalizer (A : Set G) := by
    have h1 : t⁻¹ ∈ normalizer (A : Set G) := by
      refine mem_normalizer_of_map_conj_le ?_
      rintro _ ⟨a, ha, rfl⟩
      show t⁻¹ * a * t⁻¹⁻¹ ∈ A
      have h2 := ht a⁻¹ (inv_mem ha)
      rw [inv_inv] at h2
      rw [inv_inv, show t⁻¹ * a * t = t⁻¹ * a * t * a⁻¹ * a by group]
      exact mul_mem (mem_sup_right h2) ha
    simpa using inv_mem h1
  have htM : t ∈ normalizer (M : Set G) := by
    refine mem_normalizer_of_map_conj_le ?_
    have hres : M.map (MulAut.conj t).toMonoidHom ≤
        oddResidualIn (M.map (MulAut.conj t).toMonoidHom) := by
      rw [← map_oddResidualIn_hom]
      exact map_mono (hMF.le_oddResidualIn h)
    refine le_of_le_sup_odd hres (hd.oddCoreIn_le_normalizer hM) (odd_card_oddCoreIn D) ?_
    rw [sup_comm, ← hA, ← map_conj_eq_of_mem_normalizer htA]
    exact map_mono le_sup_left
  refine ⟨htM, fun j hj => ?_⟩
  have h1 := ht j⁻¹ (mem_sup_left (inv_mem hj))
  rw [inv_inv] at h1
  have hjD : j⁻¹ ∈ normalizer ((oddCoreIn D : Subgroup G) : Set G) :=
    mem_normalizer_oddCoreIn (Subgroup.le_normalizer (inv_mem (hMD hj)))
  have h2 := (mem_normalizer_iff.mp hjD _).mp h1
  have hjM : j⁻¹ * t⁻¹ * j * t ∈ M := by
    have h3 : t⁻¹ * j * t ∈ M := by
      have h4 := (mem_normalizer_iff.mp (inv_mem htM) j).mp hj
      rwa [inv_inv] at h4
    rw [show j⁻¹ * t⁻¹ * j * t = j⁻¹ * (t⁻¹ * j * t) by group]
    exact mul_mem (inv_mem hj) h3
  have hle : M ⊓ oddCoreIn D ≤ oddCoreIn M := by
    rcases hM with rfl | rfl
    · exact hd.toThm46Pair.inf_oddCoreIn_le
    · exact hd.toThm46Pair.inf_oddCoreIn_le'
  refine hle (mem_inf.mpr ⟨hjM, ?_⟩)
  rwa [show j⁻¹ * (t⁻¹ * j * t * j⁻¹) * j⁻¹⁻¹ = j⁻¹ * t⁻¹ * j * t by group] at h2

theorem mem_normalizer_of_sup (h : FooteSec4 G L)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hcalc : FooteSmallCentralizers)
    (hd : Thm46Data L M₁ M₂) {M : Subgroup G} (hM : M = M₁ ∨ M = M₂) {g : G} {X : Subgroup G}
    (hXg : X ≤ (normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G)).map (MulAut.conj g⁻¹).toMonoidHom)
    (hcov : ∀ a ∈ M ⊔ oddCoreIn (M₁ ⊔ M₂), ∃ x ∈ X, ∃ o ∈ oddCoreIn (M₁ ⊔ M₂), a = x * o) :
    g ∈ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G) := by
  set D := M₁ ⊔ M₂ with hD
  set A := M ⊔ oddCoreIn D with hA
  have hMF : IsFooteM L M := by rcases hM with rfl | rfl; exacts [hd.hM₁, hd.hM₂]
  have hMD : M ≤ D := by rcases hM with rfl | rfl; exacts [le_sup_left, le_sup_right]
  have hAD : A ≤ D := sup_le hMD (map_subtype_le _)
  set X₀ := X ⊓ A with hX₀
  set X₁ := oddResidualIn X₀ with hX₁
  have hX₀D : X₀ ≤ D := inf_le_right.trans hAD
  have hX₁res : X₁ ≤ oddResidualIn X₁ := (closure_le _).mpr fun x hx =>
    mem_oddResidualIn (mem_oddResidualIn hx.1 hx.2) hx.2
  have hX₁M : X₁ ≤ M := le_of_le_sup_odd hX₁res (hd.oddCoreIn_le_normalizer hM)
    (odd_card_oddCoreIn D) ((oddResidualIn_le _).trans (inf_le_right.trans (by
      rw [hA, sup_comm])))
  set π := QuotientGroup.mk' (pPrimeCore 2 D) with hπ
  have hres_map : ∀ Y : Subgroup G, Y ≤ D →
      (oddResidualIn (Y.subgroupOf D)).map D.subtype = oddResidualIn Y := by
    intro Y hYD
    rw [map_oddResidualIn_hom, map_subgroupOf_eq_of_le hYD]
  have hMres : M.subgroupOf D ≤ oddResidualIn (M.subgroupOf D) := by
    intro x hx
    have h1 : (x : G) ∈ oddResidualIn M := hMF.le_oddResidualIn h hx
    rw [← hres_map M hMD] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    rwa [show y = x from Subtype.ext hyx] at hy
  have hMX : (M.subgroupOf D).map π ≤ (X₀.subgroupOf D).map π := by
    rintro _ ⟨⟨m, hmD⟩, hm, rfl⟩
    obtain ⟨x, hx, o, ho, hmo⟩ := hcov m (mem_sup_left hm)
    have hxA : x ∈ A := by
      rw [show x = m * o⁻¹ by rw [hmo]; group]
      exact mul_mem (mem_sup_left hm) (mem_sup_right (inv_mem ho))
    refine ⟨⟨x, hAD hxA⟩, mem_inf.mpr ⟨hx, hxA⟩, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨o', ho', hoe⟩ := mem_map.mp ho
    have e1 : (⟨x, hAD hxA⟩ : D)⁻¹ * ⟨m, hmD⟩ = o' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hmo, ← hoe]
      simp
    rw [e1]
    exact ho'
  have hMX₁ : (M.subgroupOf D).map π ≤ (oddResidualIn (X₀.subgroupOf D)).map π := by
    rw [map_oddResidualIn_hom]
    calc (M.subgroupOf D).map π ≤ (oddResidualIn (M.subgroupOf D)).map π := map_mono hMres
      _ = oddResidualIn ((M.subgroupOf D).map π) := map_oddResidualIn_hom _ _
      _ ≤ oddResidualIn ((X₀.subgroupOf D).map π) := oddResidualIn_mono hMX
  have hcovM : M ≤ X₁ ⊔ oddCoreIn M := by
    intro m hm
    obtain ⟨y, hy, hym⟩ := hMX₁ ⟨⟨m, hMD hm⟩, hm, rfl⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hym
    have hyX₁ : (y : G) ∈ X₁ := by
      rw [hX₁, ← hres_map X₀ hX₀D]
      exact ⟨y, hy, rfl⟩
    have hyM : (y : G) ∈ M := hX₁M hyX₁
    have hle : M ⊓ oddCoreIn D ≤ oddCoreIn M := by
      rcases hM with rfl | rfl
      · exact hd.toThm46Pair.inf_oddCoreIn_le
      · exact hd.toThm46Pair.inf_oddCoreIn_le'
    have ho : (y : G)⁻¹ * m ∈ oddCoreIn M := hle (mem_inf.mpr ⟨mul_mem (inv_mem hyM) hm,
      ⟨_, hym, by simp⟩⟩)
    rw [show m = (y : G) * ((y : G)⁻¹ * m) by group]
    exact mul_mem (mem_sup_left hyX₁) (mem_sup_right ho)
  have hX₁p : ⁅X₁, X₁⁆ = X₁ := commutator_eq_of_cover hX₁M hX₁res hcovM (hMF.commutator_eq h)
  have hX₁g : X₁.map (MulAut.conj g).toMonoidHom ≤ normalizer (D : Set G) := by
    have hX₁X : X₁ ≤ X := (oddResidualIn_le X₀).trans inf_le_left
    have h1 := map_mono (f := (MulAut.conj g).toMonoidHom) (hX₁X.trans hXg)
    rwa [map_conj_map_conj_inv] at h1
  exact hd.mem_normalizer_of_cover h hK hcalc hM hX₁M hX₁p hcovM hX₁g

theorem mem_normalizer_of_centralizes (h : FooteSec4 G L)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hcalc : FooteSmallCentralizers)
    (hd : Thm46Data L M₁ M₂) {M M' : Subgroup G} (hM : M = M₁ ∨ M = M₂) (hM' : M' = M₁ ∨ M' = M₂)
    {t g : G} (ht2 : ∃ k : ℕ, t ^ (2 ^ k) = 1) (ht1 : t ≠ 1)
    (ht : t ∈ coreActionKernel M) (htg : g⁻¹ * t * g ∈ coreActionKernel M') :
    g ∈ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := M₁ ⊔ M₂ with hD
  obtain ⟨k, hk⟩ := ht2
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hn1 : 1 ≤ n := by
    by_contra h0
    push Not at h0
    have : n = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hn
    exact ht1 hn
  set t₀ := t ^ (2 ^ (n - 1)) with ht₀
  have ht₀2 : orderOf t₀ = 2 := by
    rw [ht₀, orderOf_pow_of_dvd (pow_pos (by norm_num) _).ne'
      (by rw [hn]; exact pow_dvd_pow 2 (by omega)), hn, Nat.pow_div (by omega) (by norm_num),
      show n - (n - 1) = 1 by omega, pow_one]
  have ht₀C : t₀ ∈ coreActionKernel M := pow_mem ht _
  have hconj : ∀ y : G, g⁻¹ * y * g = MulAut.conj g⁻¹ y := fun y => by simp
  have htg₀ : g⁻¹ * t₀ * g ∈ coreActionKernel M' := by
    rw [hconj, ht₀, map_pow, ← hconj]
    exact pow_mem htg _
  have htg₀2 : orderOf (g⁻¹ * t₀ * g) = 2 := by
    rw [show g⁻¹ * t₀ * g = MulAut.conj g⁻¹ t₀ by simp, MulEquiv.orderOf_eq, ht₀2]
  have hFM : ∀ {N : Subgroup G}, (N = M₁ ∨ N = M₂) → ∀ {x : G}, orderOf x = 2 →
      x ∈ coreActionKernel N → footeF L x ≤ N := by
    intro N hN x hx hxC
    rcases hN with rfl | rfl
    · exact (centralizer_le_normalizer_of_mem h hd.hM₁ hd.hM₂ hd.hN (hd.odd h) hd.hfour₂ hx
        hxC).2
    · exact (centralizer_le_normalizer_of_mem h hd.hM₂ hd.hM₁ hd.hN.symm
        (by rw [inf_comm]; exact hd.odd h) hd.hfour₁ hx hxC).2
  have hMF : IsFooteM L M := by rcases hM with rfl | rfl; exacts [hd.hM₁, hd.hM₂]
  obtain ⟨-, hcovM, hBmax, -⟩ := foote_lemma_4_5_i h hMF ht₀2 ht₀C
  have hX : footeF L t₀ ≤ M := hFM hM ht₀2 ht₀C
  have hXp : ⁅footeF L t₀, footeF L t₀⁆ = footeF L t₀ :=
    GSThmB.commutator_eq_self_of_isPComponent hBmax.1.2.1 hBmax.1.2.2
  have hXg : (footeF L t₀).map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (D : Set G) := by
    have h1 : (footeF L t₀).map (MulAut.conj g⁻¹).toMonoidHom = footeF L (g⁻¹ * t₀ * g) := by
      rw [footeF_conj h.huniq]
      unfold conjugate
      rfl
    rw [h1]
    refine (hFM hM' htg₀2 htg₀).trans ?_
    rcases hM' with rfl | rfl
    · exact le_sup_left.trans Subgroup.le_normalizer
    · exact le_sup_right.trans Subgroup.le_normalizer
  have h2 := hd.mem_normalizer_of_cover h hK hcalc hM hX hXp hcovM hXg
  simpa using inv_mem h2

theorem normalizer_ne_top (h : FooteSec4 G L) (hd : Thm46Data L M₁ M₂) :
    normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G) ≠ ⊤ := by
  have := h.simple
  intro htop
  have hDn : (M₁ ⊔ M₂).Normal := normalizer_eq_top_iff.mp htop
  have hne₁ : M₁ ≠ ⊥ := fun h1 => hd.hM₁.not_odd h (by rw [h1, card_bot]; exact odd_one)
  have hne₂ : M₂ ≠ ⊥ := fun h1 => hd.hM₂.not_odd h (by rw [h1, card_bot]; exact odd_one)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ (M₁ ⊔ M₂) hDn with h1 | h1
  · exact hne₁ (eq_bot_iff.mpr (h1 ▸ le_sup_left))
  have hM₁n : M₁.Normal := normalizer_eq_top_iff.mp
    (eq_top_iff.mpr (h1 ▸ hd.toThm46Pair.le_normalizer))
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ M₁ hM₁n with h2 | h2
  · exact hne₁ h2
  obtain ⟨W, hW, hWM⟩ := hd.hM₁.exists_isKleinFour h
  obtain ⟨w, hw, hw1, -⟩ := exists_ne_of_isKleinFour hW 1
  have hw2 : orderOf w = 2 := orderOf_eq_prime (sq_eq_one_of_isKleinFour hW hw) hw1
  have hna : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hd.hM₁.exists_mul_ne h
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a', b', fun h3 => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, show a' * b' = b' * a' from
      Subtype.ext h3]
  have hC := coreActionKernel_top_eq_bot hna hw2
  rw [← h2] at hC
  exact hne₂ (eq_bot_iff.mpr (hC ▸ hd.h21))

end Thm46Data

theorem foote_theorem_4_6 (h : FooteSec4 G L) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {M₁ M₂ : Subgroup G} (hM₁ : IsFooteM L M₁)
    (hM₂ : IsFooteM L M₂) (hc : ⁅M₁, M₂⁆ ≤ M₁ ⊓ M₂)
    {F₁ : Subgroup G} (hF₁2 : ∀ x ∈ F₁, x ^ 2 = 1) (hF₁8 : Nat.card F₁ = 8)
    (hF₁ : F₁ ≤ coreActionKernel M₁ ⊓ normalizer (M₂ : Set G))
    {F₂ : Subgroup G} (hF₂2 : ∀ x ∈ F₂, x ^ 2 = 1) (hF₂8 : Nat.card F₂ = 8)
    (hF₂ : F₂ ≤ coreActionKernel M₂ ⊓ normalizer (M₁ : Set G)) : M₁ = M₂ := by
  have := h.simple
  by_contra hne
  rcases foote_thm46_pair h hM₁ hM₂ hc with heq | ⟨hcO, h12, h21⟩
  · exact hne heq
  have hp : Thm46Pair L M₁ M₂ := ⟨hM₁, hM₂, hne, hcO, h12, h21⟩
  obtain ⟨hnab, -, hfour₁⟩ := exists_card_eight_le_coreActionKernel h hE8 hM₁ hM₂
    (hcO.trans inf_le_left) h21 hF₁2 hF₁8 hF₁
  obtain ⟨-, -, hfour₂⟩ := exists_card_eight_le_coreActionKernel h hE8 hM₂ hM₁
    (by rw [commutator_comm]; exact hcO.trans inf_le_right) h12 hF₂2 hF₂8 hF₂
  have hN₂₁ := normalizer_le_normalizer_of_four h hM₁ hM₂ (fun x hx => (h21 hx).1) hfour₁
  have hN₁₂ := normalizer_le_normalizer_of_four h hM₂ hM₁ (fun x hx => (h12 hx).1) hfour₂
  have hd : Thm46Data L M₁ M₂ :=
    { toThm46Pair := hp, hN := le_antisymm hN₁₂ hN₂₁, hfour₁ := hfour₁, hfour₂ := hfour₂,
      hnab := hnab }
  set D := M₁ ⊔ M₂ with hD
  set Mi : Fin 2 → Subgroup G := ![M₁, M₂] with hMi
  have hMi' : ∀ i, Mi i = M₁ ∨ Mi i = M₂ := by
    intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hMiF : ∀ i, IsFooteM L (Mi i) := fun i => by
    rcases hMi' i with e | e <;> rw [e]; exacts [hM₁, hM₂]
  have hMiD : ∀ i, Mi i ≤ D := fun i => by
    rcases hMi' i with e | e <;> rw [e]; exacts [le_sup_left, le_sup_right]
  have hOD : ∀ i, oddCoreIn (Mi i) ≤ oddCoreIn D := fun i => by
    rcases hMi' i with e | e <;> rw [e]; exacts [hp.oddCoreIn_le, hp.oddCoreIn_le']
  have hDO : ∀ i, Mi i ⊓ oddCoreIn D ≤ oddCoreIn (Mi i) := fun i => by
    rcases hMi' i with e | e <;> rw [e]; exacts [hp.inf_oddCoreIn_le, hp.inf_oddCoreIn_le']
  set Abar : Fin 2 → Subgroup (D ⧸ Open.aschbacherThm5OddCore D) := fun i => footeAbar D (Mi i)
    with hAbar
  have hpre : ∀ i, Open.aschbacherThm5Preimage D (Abar i) = Mi i ⊔ oddCoreIn D :=
    fun i => preimage_footeAbar (hMiD i)
  have hcore := aschbacherThm5Core_eq D
  have hinjM : ∀ i j, Mi i ⊔ oddCoreIn D = Mi j ⊔ oddCoreIn D → Mi i = Mi j := by
    intro i j hij
    have hle : ∀ i j, Mi i ⊔ oddCoreIn D = Mi j ⊔ oddCoreIn D → Mi i ≤ Mi j := by
      intro i j hij
      refine le_of_le_sup_odd ((hMiF i).le_oddResidualIn h)
        (hd.oddCoreIn_le_normalizer (hMi' j)) (odd_card_oddCoreIn D) ?_
      rw [sup_comm, ← hij]
      exact le_sup_left
    exact le_antisymm (hle i j hij) (hle j i hij.symm)
  have hinj : Function.Injective Abar := by
    intro i j hij
    have h1 := hinjM i j (by rw [← hpre, ← hpre, hij])
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h1 hne
    · exact absurd h1.symm hne
    · rfl
  have hss : ∀ i, Open.aschbacherThm5IsSemisimple (Abar i) := fun i =>
    ⟨1, fun _ => Abar i, one_pos, fun _ => ⟨le_rfl, open_isQuasisimple_footeAbar h (hMiF i)
      (hMiD i) (hOD i) (hDO i)⟩, fun l m hlm => absurd (Subsingleton.elim l m) hlm,
      iSup_const⟩
  have hcommM : ∀ i j, i ≠ j → ⁅Mi i, Mi j⁆ ≤ oddCoreIn D := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact (hcO.trans inf_le_left).trans hp.oddCoreIn_le
    · show ⁅M₂, M₁⁆ ≤ oddCoreIn D
      rw [commutator_comm]
      exact (hcO.trans inf_le_left).trans hp.oddCoreIn_le
    · exact absurd rfl hij
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x := by
    intro i j hij x hx y hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have h1 : (a * b * a⁻¹ * b⁻¹ : D) ∈ Open.aschbacherThm5OddCore D := by
      rw [aschbacherThm5OddCore_eq, mem_pPrimeCore_iff_mem_oddCoreIn]
      have h2 := hcommM i j hij (commutator_mem_commutator ha hb)
      rw [commutatorElement_def] at h2
      exact h2
    have h3 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h3
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    calc (a : D ⧸ Open.aschbacherThm5OddCore D) * b =
        (a : D ⧸ Open.aschbacherThm5OddCore D) * b * (a : D ⧸ Open.aschbacherThm5OddCore D)⁻¹ *
          (b : D ⧸ Open.aschbacherThm5OddCore D)⁻¹ * (b * a) := by group
      _ = b * a := by rw [h3, one_mul]
  have hsupD : M₁.subgroupOf D ⊔ M₂.subgroupOf D = ⊤ := by
    apply map_injective D.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hsup : ⨆ i, Abar i = ⊤ := by
    refine eq_top_iff.mpr ?_
    calc (⊤ : Subgroup (D ⧸ Open.aschbacherThm5OddCore D))
        = (M₁.subgroupOf D ⊔ M₂.subgroupOf D).map
            (QuotientGroup.mk' (Open.aschbacherThm5OddCore D)) := by
          rw [hsupD, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      _ = Abar 0 ⊔ Abar 1 := by rw [Subgroup.map_sup]; rfl
      _ ≤ ⨆ i, Abar i := sup_le (le_iSup Abar 0) (le_iSup Abar 1)
  have hperm : ∀ x ∈ normalizer (D : Set G), ∀ i, ∃ j,
      (Open.aschbacherThm5Preimage D (Abar i)).map (MulAut.conj x).toMonoidHom =
        Open.aschbacherThm5Preimage D (Abar j) := by
    intro x hx i
    have hOx : (oddCoreIn D).map (MulAut.conj x).toMonoidHom = oddCoreIn D :=
      map_conj_eq_of_mem_normalizer (mem_normalizer_oddCoreIn hx)
    rw [hpre, Subgroup.map_sup, hOx]
    rcases hp.map_conj_mem h hx (hMi' i) with e | e
    · exact ⟨0, by rw [hpre, e]; rfl⟩
    · exact ⟨1, by rw [hpre, e]; rfl⟩
  have hi : ∀ (i j : Fin 2) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ center G →
      Open.aschbacherThm5Centralizes (Open.aschbacherThm5Core D)
        (Open.aschbacherThm5Preimage D (Abar i)) t →
      Open.aschbacherThm5Centralizes (Open.aschbacherThm5Core D)
        (Open.aschbacherThm5Preimage D (Abar j)) (g⁻¹ * t * g) →
      g ∈ normalizer (D : Set G) := by
    intro i j t g ht2 htZ hti htj
    rw [hcore, hpre] at hti htj
    have ht1 : t ≠ 1 := fun h1 => htZ (h1 ▸ one_mem _)
    exact hd.mem_normalizer_of_centralizes h hK hcalc (hMi' i) (hMi' j) ht2 ht1
      (hd.mem_coreActionKernel_of_centralizes h (hMi' i) hti)
      (hd.mem_coreActionKernel_of_centralizes h (hMi' j) htj)
  have hii : ∀ (i : Fin 2) (g : G) (X : Subgroup G),
      X ≤ (normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ Open.aschbacherThm5Preimage D (Abar i), ∃ x ∈ X,
        ∃ o ∈ Open.aschbacherThm5Core D, a = x * o) →
      g ∈ normalizer (D : Set G) := by
    intro i g X hXg hcov
    rw [hcore, hpre] at hcov
    exact hd.mem_normalizer_of_sup h hK hcalc (hMi' i) hXg hcov
  rcases hA5 G D 2 (by norm_num) Abar hinj hss hcomm hsup hperm hi hii
    (hd.normalizer_ne_top h) with h1 | ⟨-, h2⟩
  · omega
  obtain ⟨-, hrk, -⟩ := h2 0 1 (by decide)
  rw [hpre] at hrk
  obtain ⟨W, hW, hWM⟩ := hM₁.exists_isKleinFour h
  have h3 : 2 ≤ Open.pRank 2 (Mi 0 ⊔ oddCoreIn D) :=
    SectionRank.le_pRank one_lt_two ((hWM.trans (le_of_eq rfl)).trans le_sup_left)
      ⟨@IsKleinFour.isMulCommutative W _ hW, fun x hx => sq_eq_one_of_isKleinFour hW hx⟩
      (by rw [hW.card_four]; norm_num)
  omega

end CFSG.ComponentClassification.FooteLit
