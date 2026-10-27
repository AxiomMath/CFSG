module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP3

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapN9

theorem fixedLayer_data [Finite X] {C J : Subgroup X} {n : ℕ} (hJC : J ≤ C)
    (hJpc : IsPComponent 2 (J.subgroupOf C))
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρJ : IsPermAction θ ρJ) {b : X}
    (hbN : b ∈ normalizer (J : Set X)) (hb2 : b * b = 1)
    (h4 : (ρJ ⟨b, hbN⟩).support.card ≤ 4) (h5 : 5 ≤ n - (ρJ ⟨b, hbN⟩).support.card)
    {N : Subgroup X} (hN : N = GSLit.fixedLayer J (zpowers b)) :
    N ≤ C ⊓ centralizer ({b} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (C ⊓ centralizer ({b} : Set X))) ∧
      (∀ (x : X) (hx : x ∈ J), x * b = b * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        (coreImage θ hx).support ⊆ (ρJ ⟨b, hbN⟩).supportᶜ →
          x ∈ N) ∧
      (∀ x ∈ N, ∃ hx : x ∈ J,
        (coreImage θ hx).support ⊆ (ρJ ⟨b, hbN⟩).supportᶜ) ∧
      ∃ χ : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup ↥((ρJ ⟨b, hbN⟩).supportᶜ : Finset (Fin n)),
        ∀ (x : ↥N) (hx : (x : X) ∈ J),
          Perm.ofSubtype ((χ (x : ↥N ⧸ pPrimeCore 2 ↥N) : alternatingGroup _) :
            Perm ↥((ρJ ⟨b, hbN⟩).supportᶜ : Finset (Fin n))) = coreImage θ hx := by
  classical
  subst hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Jb, hJb, hJbpc, hmem, hsupp, χ, hχ⟩ :=
    exists_fixed_component_of_perm hJC hJpc hρJ hbN hb2 h5
  obtain ⟨hflC, hflpc, -⟩ := fixedLayer_facts_of_perm hJC hJpc hρJ hbN hb2 h4 h5
  have hJbC : Jb ≤ C ⊓ centralizer ({b} : Set X) := le_inf ((hJb.trans inf_le_left).trans hJC)
    (hJb.trans inf_le_right)
  have hperf : ⁅Jb, Jb⁆ = Jb := UnbalancedCorr.commutator_eq_of_isPComponent hJbC hJbpc
  have hq : Nontrivial (↥Jb ⧸ pPrimeCore 2 ↥Jb) := by
    obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ hJbC).mp hJbpc
    exact LocalCores.isQuasisimple_nontrivial hq
  have hle : Jb ≤ GSLit.fixedLayer J (zpowers b) := by
    unfold GSLit.fixedLayer
    rw [centralizer_zpowers_eq' b]
    have hpc : IsPComponent 2 (Jb.subgroupOf (J ⊓ centralizer ({b} : Set X))) :=
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hJb (inf_le_inf_right _ hJC) hJbpc
    have h1 : Jb.subgroupOf (J ⊓ centralizer ({b} : Set X)) ≤
        pLayer ↥(J ⊓ centralizer ({b} : Set X)) 2 := le_sSup hpc
    intro x hx
    exact ⟨⟨x, hJb hx⟩, h1 hx, rfl⟩
  have heq : Jb = GSLit.fixedLayer J (zpowers b) :=
    eq_of_isPComponent_of_le_inf hJbC hflC hJbpc hflpc le_rfl hle hperf hq
  rw [← heq]
  exact ⟨hJbC, hJbpc, hmem, hsupp, χ, hχ⟩

theorem eq_fixedLayer_of_le [Finite X] {C J : Subgroup X} {n : ℕ} (hJC : J ≤ C)
    (hJpc : IsPComponent 2 (J.subgroupOf C))
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρJ : IsPermAction θ ρJ) (hn : 4 ≤ n)
    {b : X} (hbN : b ∈ normalizer (J : Set X)) (hb2 : b * b = 1)
    (h4 : (ρJ ⟨b, hbN⟩).support.card ≤ 4) (h5 : 5 ≤ n - (ρJ ⟨b, hbN⟩).support.card)
    {N : Subgroup X} (hNC : N ≤ centralizer ({b} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({b} : Set X)))) (hNJ : N ≤ J) :
    N = GSLit.fixedLayer J (zpowers b) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hflC, hflpc, hmem, -, -⟩ := fixedLayer_data hJC hJpc hρJ hbN hb2 h4 h5 rfl
  have hNC' : N ≤ C ⊓ centralizer ({b} : Set X) := le_inf (hNJ.trans hJC) hNC
  have hNpc' : IsPComponent 2 (N.subgroupOf (C ⊓ centralizer ({b} : Set X))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hNC' inf_le_right hNpc
  have hperf : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  obtain ⟨-, hres, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ hNC).mp hNpc
  have hNN : N ≤ normalizer (J : Set X) := hNJ.trans le_normalizer
  have h2 : ∀ x ∈ N, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ GSLit.fixedLayer J (zpowers b) := by
    intro x hx hk
    refine hmem x (hNJ hx) (mem_centralizer_singleton_iff.mp (hNC hx)) hk ?_
    intro ω hω
    rw [Finset.mem_compl]
    intro hωb
    have h1 := fix_support_rho_of_perfect hbN hb2 h4 hNN hNC hperf hx ω hωb
    rw [hρJ.apply_of_mem hn ⟨x, hNJ hx⟩] at h1
    exact (Perm.mem_support.mp hω) h1
  have hle : N ≤ GSLit.fixedLayer J (zpowers b) := by
    have h3 : CatalogueBPrimeJoin.primeResidual 2 ↥N ≤
        (GSLit.fixedLayer J (zpowers b)).subgroupOf N := by
      refine sSup_le fun P hP => ?_
      intro p hp
      obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
      rw [mem_subgroupOf]
      refine h2 p p.2 ⟨k, ?_⟩
      have h4' := congrArg (fun z : ↥P => ((z : ↥N) : X)) hk
      simpa using h4'
    intro x hx
    have h5' : (⟨x, hx⟩ : ↥N) ∈ CatalogueBPrimeJoin.primeResidual 2 ↥N := by
      rw [hres]
      exact mem_top _
    exact h3 h5'
  exact eq_of_isPComponent_of_le_inf hNC' hflC hNpc' hflpc le_rfl hle hperf
    (LocalCores.isQuasisimple_nontrivial hq)

theorem mem_normalizer_zpowers_of_commute {b y : X} (hyb : y * b = b * y) :
    y ∈ normalizer ((zpowers b : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have h1 : y * b ^ k * y⁻¹ = b ^ k := by
      rw [(Commute.zpow_right hyb k).eq, mul_inv_cancel_right]
    rw [h1]
    exact zpow_mem (mem_zpowers b) k
  · intro hz
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz
    have h1 : z = y⁻¹ * b ^ k * y := by rw [hk]; group
    rw [h1]
    have h2 : y⁻¹ * b ^ k * y = b ^ k := by
      rw [(Commute.zpow_right (Commute.inv_left hyb) k).eq, inv_mul_cancel_right]
    rw [h2]
    exact zpow_mem (mem_zpowers b) k

theorem exists_odd_of_fixedLayer [Finite X] {C J : Subgroup X} {n : ℕ} (hJC : J ≤ C)
    (hJpc : IsPComponent 2 (J.subgroupOf C))
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρJ : IsPermAction θ ρJ) (hn : 4 ≤ n)
    {b : X} (hbN : b ∈ normalizer (J : Set X)) (hb2 : b * b = 1)
    (h4 : (ρJ ⟨b, hbN⟩).support.card = 4) (h5 : 5 ≤ n - (ρJ ⟨b, hbN⟩).support.card)
    {N : Subgroup X} (hN : N = GSLit.fixedLayer J (zpowers b))
    {θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin 5)}
    {ρN : ↥(normalizer (N : Set X)) →* Perm (Fin 5)} (hρN : IsPermAction θN ρN) :
    ∃ h ∈ J, h * b = b * h ∧ ∃ hhN : h ∈ normalizer (N : Set X), Perm.sign (ρN ⟨h, hhN⟩) = -1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNJ : N ≤ J := by
    rw [hN]
    exact (GSLit.fixedLayer_le_inf J (zpowers b)).trans inf_le_left
  set σ := ρJ ⟨b, hbN⟩ with hσdef
  obtain ⟨-, -, -, hsupp, χ, hχ⟩ := fixedLayer_data hJC hJpc hρJ hbN hb2 h4.le h5 hN
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    rw [show (⟨b, hbN⟩ : ↥(normalizer (J : Set X))) * ⟨b, hbN⟩ = 1 from Subtype.ext hb2, map_one]
  obtain ⟨a, ha⟩ : σ.support.Nonempty := by
    rw [← Finset.card_pos, h4]
    norm_num
  have ha' : σ a ≠ a := Perm.mem_support.mp ha
  have hσσ : σ (σ a) = a := by
    have h1 := congrArg (fun p : Perm (Fin n) => p a) hσ2
    simpa [Perm.mul_apply] using h1
  have hfix : 1 < (σ.supportᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hfix
  rw [Finset.mem_compl, Perm.mem_support, not_not] at hc hd
  set π : Perm (Fin n) := swap a (σ a) * swap c d with hπdef
  have hπA : π ∈ alternatingGroup (Fin n) := by
    rw [Perm.mem_alternatingGroup, hπdef, map_mul, Perm.sign_swap (Ne.symm ha'),
      Perm.sign_swap hcd]
    decide
  have e1 : σ * swap a (σ a) = swap a (σ a) * σ := by
    rw [Equiv.mul_swap_eq_swap_mul, hσσ, swap_comm]
  have e2 : σ * swap c d = swap c d * σ := by
    rw [Equiv.mul_swap_eq_swap_mul, hc, hd]
  have hπσ : π * σ = σ * π := by
    calc π * σ = swap a (σ a) * (swap c d * σ) := by rw [hπdef, mul_assoc]
      _ = swap a (σ a) * σ * swap c d := by rw [← e2, mul_assoc]
      _ = σ * π := by rw [← e1, hπdef, mul_assoc]
  obtain ⟨x, hxC, hxθ⟩ := hρJ.exists_lift hbN hb2 (b := ⟨π, hπA⟩) hπσ
  have hxb : (x : X) * b = b * x := mem_centralizer_singleton_iff.mp hxC
  have hxN : (x : X) ∈ normalizer (N : Set X) := by
    rw [hN]
    exact GSLit.mem_normalizer_fixedLayer (le_normalizer x.2)
      (mem_normalizer_zpowers_of_commute hxb)
  refine ⟨x, x.2, hxb, hxN, ?_⟩
  by_contra hsign
  have hs1 : Perm.sign (ρN ⟨x, hxN⟩) = 1 := by
    rcases Int.units_eq_one_or (Perm.sign (ρN ⟨x, hxN⟩)) with h | h
    · exact h
    · exact absurd h hsign
  obtain ⟨q, hq⟩ := θN.surjective ⟨ρN ⟨x, hxN⟩, by rw [Perm.mem_alternatingGroup]; exact hs1⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  have hρm : ρN ⟨m, le_normalizer m.2⟩ = ρN ⟨x, hxN⟩ := by
    rw [hρN.apply_of_mem (by norm_num) m, hq]
  set z := (m : X)⁻¹ * x with hzdef
  have hzN : z ∈ normalizer (N : Set X) := mul_mem (inv_mem (le_normalizer m.2)) hxN
  have hz1 : ρN ⟨z, hzN⟩ = 1 := by
    have h1 : (⟨z, hzN⟩ : ↥(normalizer (N : Set X))) =
        (⟨m, le_normalizer m.2⟩)⁻¹ * ⟨x, hxN⟩ := rfl
    rw [h1, map_mul, map_inv, hρm, inv_mul_cancel]
  have hzK := hρN.mem_coreActionKernel hzN hz1
  have hmJ : (m : X) ∈ J := hNJ m.2
  have hzJN : z ∈ normalizer (J : Set X) :=
    mul_mem (inv_mem (le_normalizer hmJ)) (le_normalizer x.2)
  have hρO : ∀ (o : ↥N), o ∈ pPrimeCore 2 ↥N → ∀ (hoJ : (o : X) ∈ J),
      ρJ ⟨o, le_normalizer hoJ⟩ = 1 := by
    intro o ho hoJ
    rw [hρJ.apply_of_mem hn ⟨o, hoJ⟩]
    change coreImage θ hoJ = 1
    rw [← hχ o hoJ, (QuotientGroup.eq_one_iff o).mpr ho, map_one]
    ext ω
    simp
  have hcomm : ∀ g ∈ fixAlt σ,
      ρJ ⟨z, hzJN⟩ * (g : Perm (Fin n)) = (g : Perm (Fin n)) * ρJ ⟨z, hzJN⟩ := by
    intro g hg
    obtain ⟨a₀, rfl⟩ := hg
    obtain ⟨q', hq'⟩ := χ.surjective a₀
    obtain ⟨m', rfl⟩ := QuotientGroup.mk_surjective q'
    have hm'J : (m' : X) ∈ J := hNJ m'.2
    have hg' : ((alternatingGroup.ofSubtype σ.supportᶜ a₀ : alternatingGroup (Fin n)) :
        Perm (Fin n)) = ρJ ⟨m', le_normalizer hm'J⟩ := by
      rw [hρJ.apply_of_mem hn ⟨m', hm'J⟩]
      change _ = coreImage θ hm'J
      rw [← hχ m' hm'J, hq']
      rfl
    rw [hg']
    obtain ⟨o, ho, hoeq⟩ := hzK.2 m' m'.2
    have hoJ : (o : X) ∈ J := hNJ o.2
    have hρo := hρO o ho hoJ
    have h1 : (⟨o, le_normalizer hoJ⟩ : ↥(normalizer (J : Set X))) =
        (⟨m', le_normalizer hm'J⟩)⁻¹ * (⟨z, hzJN⟩)⁻¹ * ⟨m', le_normalizer hm'J⟩ * ⟨z, hzJN⟩ :=
      Subtype.ext hoeq
    rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv] at hρo
    calc ρJ ⟨z, hzJN⟩ * ρJ ⟨m', le_normalizer hm'J⟩ =
        ρJ ⟨z, hzJN⟩ * ρJ ⟨m', le_normalizer hm'J⟩ * ((ρJ ⟨m', le_normalizer hm'J⟩)⁻¹ *
          (ρJ ⟨z, hzJN⟩)⁻¹ * ρJ ⟨m', le_normalizer hm'J⟩ * ρJ ⟨z, hzJN⟩) := by rw [hρo, mul_one]
      _ = ρJ ⟨m', le_normalizer hm'J⟩ * ρJ ⟨z, hzJN⟩ := by group
  have hzfix : ∀ ω, ω ∉ σ.support → ρJ ⟨z, hzJN⟩ ω = ω := fun ω hω =>
    apply_eq_of_commute_fixAlt (by omega) hcomm hω
  have hρz : ρJ ⟨z, hzJN⟩ = (ρJ ⟨m, le_normalizer hmJ⟩)⁻¹ * π := by
    have h1 : (⟨z, hzJN⟩ : ↥(normalizer (J : Set X))) =
        (⟨m, le_normalizer hmJ⟩)⁻¹ * ⟨x, le_normalizer x.2⟩ := rfl
    rw [h1, map_mul, map_inv, hρJ.apply_of_mem hn x, hxθ]
  obtain ⟨hmJ', hms⟩ := hsupp m m.2
  have hρm' : ρJ ⟨m, le_normalizer hmJ⟩ = coreImage θ hmJ' := hρJ.apply_of_mem hn ⟨m, hmJ'⟩
  set μ := ρJ ⟨m, le_normalizer hmJ⟩ with hμdef
  have hμs : ∀ ω ∈ σ.support, μ ω = ω := by
    intro ω hω
    by_contra hne
    have h1 : ω ∈ (coreImage θ hmJ').support := by rw [← hρm']; exact Perm.mem_support.mpr hne
    exact (Finset.mem_compl.mp (hms h1)) hω
  have hfixσ : ∀ ω, ω ∉ σ.support → σ (swap c d ω) = swap c d ω := by
    intro ω hω
    rw [Perm.mem_support, not_not] at hω
    by_cases hωc : ω = c
    · rw [hωc, swap_apply_left, hd]
    · by_cases hωd : ω = d
      · rw [hωd, swap_apply_right, hc]
      · rw [swap_apply_of_ne_of_ne hωc hωd, hω]
  have hμ : μ = swap c d := by
    ext ω
    by_cases hω : ω ∈ σ.support
    · have h1 : ω ≠ c := fun h => (Perm.mem_support.mp hω) (h ▸ hc)
      have h2 : ω ≠ d := fun h => (Perm.mem_support.mp hω) (h ▸ hd)
      rw [hμs ω hω, swap_apply_of_ne_of_ne h1 h2]
    · have h1 := hzfix ω hω
      rw [hρz, Perm.mul_apply, Perm.inv_eq_iff_eq] at h1
      rw [← h1, hπdef, Perm.mul_apply]
      have hf := hfixσ ω hω
      have hne1 : swap c d ω ≠ a := by
        intro h
        rw [h] at hf
        exact ha' hf
      have hne2 : swap c d ω ≠ σ a := by
        intro h
        rw [h, hσσ] at hf
        exact ha' hf.symm
      rw [swap_apply_of_ne_of_ne hne1 hne2]
  have hμA : μ ∈ alternatingGroup (Fin n) := by rw [hρm']; exact coreImage_mem θ hmJ'
  rw [hμ, Perm.mem_alternatingGroup, Perm.sign_swap hcd] at hμA
  exact absurd hμA (by decide)

end SwapN9

end CFSG.ComponentClassification.SolMax
