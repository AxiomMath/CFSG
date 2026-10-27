module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
  (signalizerTrivialAlt_holds)

theorem a10_sigTriv : SignalizerTrivialX IsA10Type 5 := by
  refine signalizerTrivialX_of_on Nat.prime_five ?_
  intro K _ _ hK
  obtain ⟨-, ⟨e⟩⟩ := hK
  exact signalizerTrivialAlt_holds 5 Nat.prime_five (by norm_num) K ⟨e⟩

theorem a10_of_cycleType {σ : Equiv.Perm (Fin 10)} (h : σ.cycleType = {5, 5}) :
    σ ^ 5 = 1 ∧ ∀ x, σ x ≠ x := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  constructor
  · rw [Equiv.Perm.pow_prime_eq_one_iff]
    intro c hc
    rw [h] at hc
    simpa using hc
  · intro x hx
    have hsum := Equiv.Perm.sum_cycleType σ
    rw [h] at hsum
    have hcard : σ.support.card = Fintype.card (Fin 10) := by
      rw [Fintype.card_fin, ← hsum]
      simp
    have huniv := Finset.eq_univ_of_card σ.support hcard
    have hxs : x ∈ σ.support := by
      rw [huniv]
      exact Finset.mem_univ x
    exact (Equiv.Perm.mem_support.mp hxs) hx

theorem a10_sq_eq_one_of_closure_comm {G : Type*} [Group G] {S : Set G}
    (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hs : ∀ x ∈ S, x ^ 2 = 1) :
    ∀ g ∈ Subgroup.closure S, g ^ 2 = 1 := by
  have h1 : ∀ g ∈ Subgroup.closure S, ∀ s ∈ S, s * g = g * s := by
    intro g hg s hs'
    have : Subgroup.closure S ≤ Subgroup.centralizer {s} := by
      rw [Subgroup.closure_le]
      intro x hx y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hc y hs' x hx
    exact this hg s rfl
  have h2 : ∀ g ∈ Subgroup.closure S, ∀ h ∈ Subgroup.closure S, h * g = g * h := by
    intro g hg h hh
    have : Subgroup.closure S ≤ Subgroup.centralizer {g} := by
      rw [Subgroup.closure_le]
      intro x hx y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (h1 y hg x hx).symm
    exact (this hh g rfl).symm
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := h2 y hy x hx
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem a10_pow_fixed {σ : Equiv.Perm (Fin 10)} (h5 : σ ^ 5 = 1) (hfix : ∀ x, σ x ≠ x)
    {x : Fin 10} {m : ℕ} (hm : (σ ^ m) x = x) : 5 ∣ m := by
  by_contra hn
  have hmod : ∀ n : ℕ, σ ^ n = σ ^ (n % 5) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, h5, one_pow, one_mul]
  have hcop : Nat.Coprime m 5 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hn)
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
  apply hfix x
  have h1 : (σ ^ (m * a)) x = x := by
    rw [pow_mul]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hm a
  rwa [hmod (m * a), ha, pow_one] at h1

theorem a10_core_perm {σ : Equiv.Perm (Fin 10)} (h5 : σ ^ 5 = 1) (hfix : ∀ x, σ x ≠ x) :
    ∃ V : Subgroup (Equiv.Perm (Fin 10)), (∀ g ∈ V, g ^ 2 = 1) ∧ (∀ g ∈ V, σ * g * σ⁻¹ ∈ V) ∧
      ∃ v ∈ V, Equiv.Perm.sign v = 1 ∧ σ * v ≠ v * σ := by
  have hmod : ∀ n : ℕ, σ ^ n = σ ^ (n % 5) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, h5, one_pow, one_mul]
  have horb : ∀ (x : Fin 10) (i j : ℕ), (σ ^ i) x = (σ ^ j) x → i % 5 = j % 5 := by
    have key : ∀ (x : Fin 10) (i d : ℕ), (σ ^ i) x = (σ ^ (i + d)) x → i % 5 = (i + d) % 5 := by
      intro x i d h
      have h' : (σ ^ d) ((σ ^ i) x) = (σ ^ i) x := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm, ← h]
      have := a10_pow_fixed h5 hfix h'
      omega
    intro x i j h
    rcases le_total i j with hij | hij
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      exact key x i d h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      exact (key x j d h.symm).symm
  obtain ⟨b⟩ : Nonempty (Fin 10) := inferInstance
  obtain ⟨b', hb'⟩ : ∃ b' : Fin 10, ∀ n : ℕ, (σ ^ n) b ≠ b' := by
    have hlt : ((Finset.range 5).image (fun n => (σ ^ n) b)).card <
        (Finset.univ : Finset (Fin 10)).card := by
      calc _ ≤ (Finset.range 5).card := Finset.card_image_le
        _ = 5 := Finset.card_range 5
        _ < 10 := by norm_num
        _ = _ := by simp
    obtain ⟨b', -, hb'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨b', fun n hn => hb' ?_⟩
    rw [Finset.mem_image]
    exact ⟨n % 5, Finset.mem_range.mpr (Nat.mod_lt n (by norm_num)), by rw [← hmod n]; exact hn⟩
  have hcross : ∀ i j : ℕ, (σ ^ i) b ≠ (σ ^ j) b' := by
    intro i j h
    apply hb' (4 * j + i)
    have h1 : (σ ^ (4 * j)) ((σ ^ i) b) = (σ ^ (4 * j)) ((σ ^ j) b') := by rw [h]
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_add] at h1
    have h2 : σ ^ (4 * j + j) = 1 := by
      rw [show 4 * j + j = 5 * j by ring, pow_mul, h5, one_pow]
    rw [h1, h2, Equiv.Perm.one_apply]
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ → Equiv.Perm (Fin 10),
      ∀ k, τ k = Equiv.swap ((σ ^ k) b) ((σ ^ k) b') := ⟨_, fun k => rfl⟩
  have hτσ : ∀ k, σ * τ k * σ⁻¹ = τ (k + 1) := by
    intro k
    rw [hτ, hτ, ← Equiv.swap_apply_apply]
    simp [pow_succ']
  have hτper : ∀ k, τ k = τ (k % 5) := by
    intro k
    rw [hτ, hτ, hmod k]
  have hτsq : ∀ k, τ k ^ 2 = 1 := by
    intro k
    rw [hτ, sq, Equiv.swap_mul_self]
  have hcomm : ∀ i j, Commute (τ i) (τ j) := by
    intro i j
    by_cases hij : i % 5 = j % 5
    · rw [hτper i, hτper j, hij]
    · have hd : Equiv.Perm.Disjoint (τ i) (τ j) := by
        intro x
        by_cases hx : x = (σ ^ i) b ∨ x = (σ ^ i) b'
        · right
          rw [hτ j]
          apply Equiv.swap_apply_of_ne_of_ne
          · rcases hx with rfl | rfl
            · exact fun h => hij (horb b i j h)
            · exact fun h => hcross j i h.symm
          · rcases hx with rfl | rfl
            · exact fun h => hcross i j h
            · exact fun h => hij (horb b' i j h)
        · left
          rw [hτ i]
          apply Equiv.swap_apply_of_ne_of_ne
          · exact fun h => hx (Or.inl h)
          · exact fun h => hx (Or.inr h)
      exact hd.commute
  let S : Set (Equiv.Perm (Fin 10)) := Set.range fun k : ℕ => τ k * τ (k + 1)
  have hS_comm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    exact (((hcomm k l).mul_right (hcomm k (l + 1))).mul_left
      ((hcomm (k + 1) l).mul_right (hcomm (k + 1) (l + 1)))).eq
  have hS_sq : ∀ x ∈ S, x ^ 2 = 1 := by
    rintro _ ⟨k, rfl⟩
    show (τ k * τ (k + 1)) ^ 2 = 1
    rw [(hcomm k (k + 1)).mul_pow, hτsq, hτsq, one_mul]
  refine ⟨Subgroup.closure S, a10_sq_eq_one_of_closure_comm hS_comm hS_sq, ?_, τ 0 * τ 1,
    ?_, ?_, ?_⟩
  · intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      apply Subgroup.subset_closure
      refine ⟨k + 1, ?_⟩
      have h : σ * (τ k * τ (k + 1)) * σ⁻¹ = (σ * τ k * σ⁻¹) * (σ * τ (k + 1) * σ⁻¹) := by
        group
      show τ (k + 1) * τ (k + 1 + 1) = σ * (τ k * τ (k + 1)) * σ⁻¹
      rw [h, hτσ k, hτσ (k + 1)]
    | one => simp
    | mul x y hx hy ihx ihy =>
      have : σ * (x * y) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹) := by group
      rw [this]
      exact mul_mem ihx ihy
    | inv x hx ihx =>
      have : σ * x⁻¹ * σ⁻¹ = (σ * x * σ⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem ihx
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · rw [Equiv.Perm.sign_mul, hτ 0, hτ 1, Equiv.Perm.sign_swap (hcross 0 0),
      Equiv.Perm.sign_swap (hcross 1 1)]
    rfl
  · intro heq
    have h1 : σ * (τ 0 * τ 1) * σ⁻¹ = τ 0 * τ 1 := by rw [heq]; group
    have h2 : σ * (τ 0 * τ 1) * σ⁻¹ = τ 1 * τ 2 := by
      calc σ * (τ 0 * τ 1) * σ⁻¹ = (σ * τ 0 * σ⁻¹) * (σ * τ 1 * σ⁻¹) := by group
        _ = τ 1 * τ 2 := by rw [hτσ 0, hτσ 1]
    have h3 : τ 1 * τ 2 = τ 0 * τ 1 := h2.symm.trans h1
    have h4 := congrArg (fun f => f b) h3
    have hb1 : b ≠ (σ ^ 1) b := fun h => absurd (horb b 0 1 (by simpa using h)) (by norm_num)
    have hb2 : b ≠ (σ ^ 2) b := fun h => absurd (horb b 0 2 (by simpa using h)) (by norm_num)
    have hcb1 : b ≠ (σ ^ 1) b' := fun h => hcross 0 1 (by simpa using h)
    have hcb2 : b ≠ (σ ^ 2) b' := fun h => hcross 0 2 (by simpa using h)
    have e1 : τ 1 b = b := by
      rw [hτ]; exact Equiv.swap_apply_of_ne_of_ne hb1 hcb1
    have e2 : τ 2 b = b := by
      rw [hτ]; exact Equiv.swap_apply_of_ne_of_ne hb2 hcb2
    have e0 : τ 0 b = b' := by
      rw [hτ]; simp
    simp only [Equiv.Perm.mul_apply, e1, e2, e0] at h4
    exact hcross 0 0 (by simpa using h4)

theorem a10_exists_invariant_twoGroup (u : alternatingGroup (Fin 10))
    (hu : ((u : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).cycleType = {5, 5}) :
    ∃ V : Subgroup (alternatingGroup (Fin 10)), IsPGroup 2 V ∧
      u ∈ Subgroup.normalizer (V : Set (alternatingGroup (Fin 10))) ∧ ∃ v ∈ V, u * v ≠ v * u := by
  obtain ⟨h5, hfix⟩ := a10_of_cycleType hu
  obtain ⟨V', hsq, hnorm, v, hvV, hvsign, hvne⟩ := a10_core_perm h5 hfix
  have hvA : v ∈ alternatingGroup (Fin 10) := Equiv.Perm.mem_alternatingGroup.mpr hvsign
  refine ⟨V'.subgroupOf (alternatingGroup (Fin 10)), ?_, ?_, ⟨v, hvA⟩, hvV, ?_⟩
  · intro g
    refine ⟨1, ?_⟩
    have h := hsq ((g : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) g.2
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  · apply Subgroup.mem_normalizer_fintype
    intro n hn
    have hn' : ((n : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) ∈ V' := hn
    have h := hnorm _ hn'
    show ((u * n * u⁻¹ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) ∈ V'
    simpa using h
  · intro h
    apply hvne
    have := congrArg Subtype.val h
    simpa using this

theorem a10_inner_core (X : Type) [Group X] [Finite X] (K : Subgroup X)
    (e : ↥K ≃* alternatingGroup (Fin 10)) (U₀ : Subgroup X) (hUc : Nat.card U₀ = 5)
    (u : X) (huU : u ∈ U₀) (huK : u ∈ K)
    (hct : ((e ⟨u, huK⟩ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).cycleType = {5, 5}) :
    U₀ ≤ K ∧ ∃ V : Subgroup X, V ≤ K ∧ IsPGroup 2 V ∧ U₀ ≤ normalizer (V : Set X) ∧
      ∃ v ∈ V, ∃ u ∈ U₀, u * v ≠ v * u := by
  have hu1 : u ≠ 1 := by
    intro h1
    have h2 : (⟨u, huK⟩ : K) = 1 := Subtype.ext h1
    rw [h2, map_one] at hct
    simp at hct
  have hord : orderOf u = 5 := by
    have h1 : orderOf (⟨u, huU⟩ : U₀) ∣ Nat.card U₀ := orderOf_dvd_natCard _
    rw [hUc, Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  have hUz : Subgroup.zpowers u = U₀ := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr huU
    · rw [hUc, Nat.card_zpowers, hord]
  refine ⟨hUz ▸ Subgroup.zpowers_le.mpr huK, ?_⟩
  obtain ⟨V, hVp, hVn, v, hvV, hvne⟩ := a10_exists_invariant_twoGroup (e ⟨u, huK⟩) hct
  refine ⟨(V.map e.symm.toMonoidHom).map K.subtype, Subgroup.map_subtype_le _,
    (hVp.map e.symm.toMonoidHom).map K.subtype, ?_,
    ((e.symm v : K) : X), ⟨e.symm v, ⟨v, hvV, rfl⟩, rfl⟩, u, huU, ?_⟩
  · rw [← hUz, Subgroup.zpowers_le]
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨y, ⟨w, hw, rfl⟩, rfl⟩ := hn
    have hw' := (Subgroup.mem_normalizer_iff.mp hVn w).mp hw
    refine ⟨e.symm (e ⟨u, huK⟩ * w * (e ⟨u, huK⟩)⁻¹), ⟨_, hw', rfl⟩, ?_⟩
    simp
  · intro h
    apply hvne
    have h1 : (⟨u, huK⟩ : K) * e.symm v = e.symm v * ⟨u, huK⟩ := Subtype.ext h
    have h2 := congrArg e h1
    simpa using h2

theorem a10_lemma45 : Lemma45Facts IsA10Type 5 A10Shape := by
  refine lemma45Facts_of_inner Nat.prime_five (by norm_num) ?_
  intro X _ _ K hK R U₀ hUR hUe hUc hshape
  obtain ⟨e, u, huUK, huK, hct⟩ := hshape
  exact a10_inner_core X K e U₀ hUc u huUK.1 huK hct

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
