module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootIrrCoord

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

namespace CoreIrr

variable {K : Type} [Field K]

@[expose] def orbVec (σ : K ≃+* K) (γ : Dr) (c : K) : Rv K :=
  fun x => if x = γ then c else if x = rhoD γ then σ c else 0

@[expose] def Good (σ : K ≃+* K) (N : AddSubgroup (Rv K)) (γ : Dr) : Prop :=
  ∀ c : K, (rhoD γ = γ → σ c = c) → orbVec σ γ c ∈ N

private theorem rho_injective {x y : Dr} (h : rhoD x = rhoD y) : x = y := by
  have := congrArg rhoD h
  rwa [rho_rho, rho_rho] at this

private theorem single_eq_smul (γ : Dr) (s : K) :
    (Pi.single γ s : Rv K) = s • (Pi.single γ (1 : K) : Rv K) := by
  funext x
  by_cases hx : x = γ
  · subst hx
    simp
  · simp [Pi.single_eq_of_ne hx]

private theorem orbVec_fixed (σ : K ≃+* K) {γ : Dr} (h : rhoD γ = γ) (c : K) :
    orbVec σ γ c = Pi.single γ c := by
  funext x
  by_cases hx : x = γ
  · subst hx
    simp [orbVec]
  · simp [orbVec, hx, h, Pi.single_eq_of_ne hx]

private theorem orbVec_moved (σ : K ≃+* K) {γ : Dr} (h : rhoD γ ≠ γ) (c : K) :
    orbVec σ γ c = c • Pi.single γ (1 : K) + σ c • Pi.single (rhoD γ) (1 : K) := by
  funext x
  by_cases hx : x = γ
  · subst hx
    simp [orbVec, Pi.single_apply, h.symm]
  · by_cases hx' : x = rhoD γ
    · subst hx'
      simp [orbVec, Pi.single_apply, hx]
    · simp [orbVec, Pi.single_apply, hx, hx']

theorem orbVec_mem_rphi {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) {γ : Dr} {c : K}
    (hc : rhoD γ = γ → σ c = c) : orbVec σ γ c ∈ RPhi K σ := by
  intro x
  show orbVec σ γ c (rhoD x) = σ (orbVec σ γ c x)
  rcases eq_or_ne x γ with rfl | h1
  · by_cases h2 : rhoD x = x
    · rw [h2]
      simp [orbVec, hc h2]
    · simp [orbVec, h2]
  · rcases eq_or_ne x (rhoD γ) with rfl | h3
    · simp [orbVec, rho_rho, h1, hσσ]
    · have h4 : rhoD x ≠ γ := fun h => h3 (by rw [← h, rho_rho])
      have h5 : rhoD x ≠ rhoD γ := fun h => h1 (rho_injective h)
      simp [orbVec, h1, h3, h4, h5]

theorem good_rho {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) {N : AddSubgroup (Rv K)} {γ : Dr}
    (h : Good σ N γ) : Good σ N (rhoD γ) := by
  intro c hc
  have hc' : rhoD γ = γ → σ c = c := fun h' => hc (congrArg rhoD h')
  have key : orbVec σ (rhoD γ) c = orbVec σ γ (σ c) := by
    funext x
    simp only [orbVec, rho_rho, hσσ]
    by_cases h1 : x = rhoD γ
    · by_cases h2 : x = γ
      · rw [if_pos h1, if_pos h2, hc' (h1.symm.trans h2)]
      · rw [if_pos h1, if_neg h2, if_pos h1]
    · by_cases h2 : x = γ
      · rw [if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
  rw [key]
  refine h (σ c) fun h' => ?_
  have := hc' h'
  simp [this]

private theorem refl_eq_iff {a : Fin TwistTag.E6.foldedTag.rank} (ha : a ≠ 3) (x y : Dr) :
    reflD a x = y ↔ x = reflD a y := by
  constructor
  · intro h
    rw [← h, refl_invol a ha x]
  · intro h
    rw [h, refl_invol a ha y]

theorem unsign {σ : K ≃+* K} {u w : Rv K} (hu : u ∈ RPhi K σ) (hw : w ∈ RPhi K σ)
    {ε : Dr → K} (hε : ∀ x, ε x = 1 ∨ ε x = -1) (huw : ∀ x, w x = ε x * u x) {y : Dr}
    (hy : ∀ x, x ≠ y → x ≠ rhoD y → u x = 0) : u = w ∨ u = -w := by
  have hσε : ∀ x, σ (ε x) = ε x := fun x => by rcases hε x with h | h <;> simp [h]
  have he2 : ε y * ε y = 1 := by rcases hε y with h | h <;> simp [h]
  have key : ε (rhoD y) * u (rhoD y) = ε y * u (rhoD y) := by
    have h1 := hw y
    have h2 := hu y
    rw [huw (rhoD y), huw y, map_mul, hσε, ← h2] at h1
    exact h1
  have hclaim : ∀ x, u x = ε y * w x := by
    intro x
    by_cases h1 : x = y
    · subst h1
      rw [huw, ← mul_assoc, he2, one_mul]
    · by_cases h2 : x = rhoD y
      · subst h2
        rw [huw, key, ← mul_assoc, he2, one_mul]
      · rw [hy x h1 h2, huw, hy x h1 h2]
        simp
  rcases hε y with he | he
  · left
    funext x
    rw [hclaim x, he, one_mul]
  · right
    funext x
    rw [hclaim x, he]
    simp

theorem good_refl {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) {N : AddSubgroup (Rv K)}
    (hΦ : N ≤ RPhi K σ) {a : Fin TwistTag.E6.foldedTag.rank} (ha : a ≠ 3)
    (hW : ∃ ε : Dr → K, (∀ γ, ε γ = 1 ∨ ε γ = -1) ∧
      ∀ v ∈ N, (fun γ => ε γ * v (reflD a γ)) ∈ N)
    {γ : Dr} (hg : Good σ N γ) : Good σ N (reflD a γ) := by
  obtain ⟨ε, hε, hεN⟩ := hW
  intro c hc
  have hc' : rhoD γ = γ → σ c = c := fun h => hc (by rw [refl_rho a ha, h])
  have hw := hεN _ (hg c hc')
  have hu : orbVec σ (reflD a γ) c ∈ RPhi K σ := orbVec_mem_rphi hσσ hc
  have huw : ∀ x, (fun x => ε x * orbVec σ γ c (reflD a x)) x =
      ε x * orbVec σ (reflD a γ) c x := by
    intro x
    simp only [orbVec, refl_eq_iff ha, refl_rho a ha]
  rcases unsign hu (hΦ hw) hε huw (y := reflD a γ)
      (fun x h1 h2 => by simp [orbVec, h1, h2]) with h | h
  · rw [h]
    exact hw
  · rw [h]
    exact N.neg_mem hw

private theorem seed_core {σ : K ≃+* K} {N : AddSubgroup (Rv K)}
    (hY : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ c : K, (a = 2 → σ c = c) →
      ∀ v ∈ N, yorb K σ a c v ∈ N)
    {a : Fin TwistTag.E6.foldedTag.rank} (ha : a ≠ 3) (ha2 : a ≠ 2)
    {i₀ i₁ : Fin TwistTag.E6.tag.rank}
    (hyorb : ∀ (c : K) (v : Rv K), yorb K σ a c v = yop K i₀ c (yop K i₁ (σ c) v))
    {γ δ γ'' : Dr} (hγ : Good σ N γ) (hγ'' : Good σ N γ'') (hγf : rhoD γ = γ)
    (hγ''f : rhoD γ'' = γ'') (hne : rhoD δ ≠ δ) (hσσ : ∀ c, σ (σ c) = c)
    (h₁ : δ.1 + Pi.single i₀ 1 = γ.1) (h₂ : (rhoD δ).1 + Pi.single i₁ 1 = γ.1)
    (h₃ : γ''.1 + Pi.single i₀ 1 = (rhoD δ).1) (c : K) : orbVec σ δ c ∈ N := by
  have s1 : (Pi.single γ (1 : K) : Rv K) ∈ N := by
    have := hγ 1 (fun _ => map_one σ)
    rwa [orbVec_fixed σ hγf] at this
  have hfix : σ (c * σ c) = c * σ c := by rw [map_mul, hσσ, mul_comm]
  have s2 : (c * σ c) • (Pi.single γ'' (1 : K) : Rv K) ∈ N := by
    have := hγ'' (c * σ c) (fun _ => hfix)
    rwa [orbVec_fixed σ hγ''f, single_eq_smul] at this
  have s3 := hY a ha c (fun h => absurd h ha2) _ s1
  rw [hyorb, yop_comp_single i₀ i₁ c (σ c) 1 h₁ h₂ h₃] at s3
  have : orbVec σ δ c = Pi.single γ (1 : K) + c • Pi.single δ (1 : K) +
      σ c • Pi.single (rhoD δ) (1 : K) + (c * σ c) • Pi.single γ'' (1 : K) - Pi.single γ (1 : K) -
        (c * σ c) • Pi.single γ'' (1 : K) := by
    rw [orbVec_moved σ hne]
    abel
  rw [this]
  exact N.sub_mem (N.sub_mem s3 s1) s2

theorem good_seed {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) {N : AddSubgroup (Rv K)}
    (hY : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ c : K, (a = 2 → σ c = c) →
      ∀ v ∈ N, yorb K σ a c v ∈ N)
    (hfix : ∀ γ : Dr, rhoD γ = γ → Good σ N γ) {δ : Dr} (hδ : δ ∈ seeds) : Good σ N δ := by
  obtain ⟨γ, hγ, p, hp, h1, h2, hne, γ'', hγ'', h3⟩ := seeds_spec hδ
  intro c _
  simp only [pairData, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact seed_core hY (a := 0) (by decide) (by decide) (i₀ := 0) (i₁ := 5) (fun c v => rfl)
      (hfix γ hγ) (hfix γ'' hγ'') hγ hγ'' hne hσσ h1 h2 h3 c
  · exact seed_core hY (a := 1) (by decide) (by decide) (i₀ := 2) (i₁ := 4) (fun c v => rfl)
      (hfix γ hγ) (hfix γ'' hγ'') hγ hγ'' hne hσσ h1 h2 h3 c

private theorem good_applyWord {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) {N : AddSubgroup (Rv K)}
    (hΦ : N ≤ RPhi K σ)
    (hW : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∃ ε : Dr → K,
      (∀ γ, ε γ = 1 ∨ ε γ = -1) ∧ ∀ v ∈ N, (fun γ => ε γ * v (reflD a γ)) ∈ N) :
    ∀ w : List (Fin TwistTag.E6.foldedTag.rank), (∀ a ∈ w, a ≠ 3) → ∀ x : Dr, Good σ N x →
      Good σ N (applyWord w x) := by
  intro w
  induction w with
  | nil => exact fun _ _ h => h
  | cons a w ih =>
    exact fun hw x hx => ih (fun b hb => hw b (List.mem_cons_of_mem a hb)) _
      (good_refl hσσ hΦ (hw a List.mem_cons_self) (hW a (hw a List.mem_cons_self)) hx)

theorem good_all {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) {N : AddSubgroup (Rv K)}
    (hΦ : N ≤ RPhi K σ)
    (hY : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ c : K, (a = 2 → σ c = c) →
      ∀ v ∈ N, yorb K σ a c v ∈ N)
    (hW : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∃ ε : Dr → K,
      (∀ γ, ε γ = 1 ∨ ε γ = -1) ∧ ∀ v ∈ N, (fun γ => ε γ * v (reflD a γ)) ∈ N)
    (htop : Good σ N topD) : ∀ γ, Good σ N γ := by
  have hfix : ∀ γ : Dr, rhoD γ = γ → Good σ N γ := fun γ hγ => by
    obtain ⟨w, hw, rfl⟩ := fixed_reach γ hγ
    exact good_applyWord hσσ hΦ hW w (fixedWords_ne w hw) topD htop
  have hseed : ∀ δ ∈ seeds, Good σ N δ := fun δ hδ => good_seed hσσ hY hfix hδ
  have hcov : ∀ γ ∈ covered, Good σ N γ := by
    intro γ hγ
    simp only [covered, Finset.mem_union, Finset.mem_image] at hγ
    rcases hγ with (h | h) | ⟨x, hx, rfl⟩
    · exact hfix γ (Finset.mem_filter.1 h).2
    · exact hseed γ h
    · exact good_rho hσσ (hseed x hx)
  have hrefl : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ γ : Dr,
      reflD a γ ∈ covered → Good σ N γ := fun a ha γ h => by
    have := good_refl hσσ hΦ ha (hW a ha) (hcov _ h)
    rwa [refl_invol a ha] at this
  intro γ
  rcases all_reach γ with h | h | h | h
  · exact hcov γ h
  · exact hrefl 0 (by decide) γ h
  · exact hrefl 1 (by decide) γ h
  · exact hrefl 2 (by decide) γ h

private theorem sub_orbVec_apply {σ : K ≃+* K} {v : Rv K} (hv : v ∈ RPhi K σ) (γ x : Dr) :
    (v - orbVec σ γ (v γ)) x = if x = γ ∨ x = rhoD γ then 0 else v x := by
  by_cases h1 : x = γ
  · subst h1
    simp [orbVec]
  · by_cases h2 : x = rhoD γ
    · subst h2
      simp [orbVec, h1, hv γ]
    · simp [orbVec, h1, h2]

theorem rphi_le_of_good {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) {N : AddSubgroup (Rv K)}
    (hgood : ∀ γ, Good σ N γ) : RPhi K σ ≤ N := by
  intro v hv
  suffices H : ∀ s : Finset Dr, ∀ v ∈ RPhi K σ, (∀ x ∉ s, v x = 0) → v ∈ N from
    H Finset.univ v hv (fun x hx => absurd (Finset.mem_univ x) hx)
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro v hv hvs
    rcases s.eq_empty_or_nonempty with hs | ⟨γ, hγ⟩
    · have : v = 0 := funext fun x => hvs x (by simp [hs])
      rw [this]
      exact N.zero_mem
    · have hc : rhoD γ = γ → σ (v γ) = v γ := fun h => by
        have := hv γ
        rw [h] at this
        exact this.symm
      have hwN : orbVec σ γ (v γ) ∈ N := hgood γ (v γ) hc
      have hwR : orbVec σ γ (v γ) ∈ RPhi K σ := orbVec_mem_rphi hσσ hc
      have hv' : v - orbVec σ γ (v γ) ∈ RPhi K σ := sub_mem hv hwR
      have hsub : ∀ x ∉ (s.erase γ).erase (rhoD γ), (v - orbVec σ γ (v γ)) x = 0 := by
        intro x hx
        rw [sub_orbVec_apply hv]
        by_cases h : x = γ ∨ x = rhoD γ
        · rw [if_pos h]
        · rw [if_neg h]
          apply hvs
          intro hxs
          exact hx (Finset.mem_erase.2 ⟨fun h' => h (Or.inr h'),
            Finset.mem_erase.2 ⟨fun h' => h (Or.inl h'), hxs⟩⟩)
      have hss : (s.erase γ).erase (rhoD γ) ⊂ s :=
        Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset _ _) (Finset.erase_ssubset hγ)
      have h2 := ih _ hss _ hv' hsub
      have h3 : v = (v - orbVec σ γ (v γ)) + orbVec σ γ (v γ) := by abel
      rw [h3]
      exact N.add_mem h2 hwN

end CoreIrr

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
