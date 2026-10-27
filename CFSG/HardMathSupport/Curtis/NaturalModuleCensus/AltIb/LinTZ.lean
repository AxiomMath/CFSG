module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinCore
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinAux
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinLift

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinCell

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ToralCensus CFSG.RankThree.CALinearPlane CFSG.QuasithinUnique
  CFSG.AGLEmbedding.LieOut
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open scoped commutatorElement

section Scalar

variable {K : Type} [Field K]

theorem eq_smul_one_of_card_one {κ : Type} [Fintype κ] [DecidableEq κ] (hk : Fintype.card κ = 1)
    (M : Matrix κ κ K) : ∃ c : K, M = c • (1 : Matrix κ κ K) := by
  obtain ⟨i⟩ : Nonempty κ := Fintype.card_pos_iff.1 (by omega)
  refine ⟨M i i, ?_⟩
  have hs : Subsingleton κ := Fintype.card_le_one_iff_subsingleton.1 hk.le
  ext a b
  rw [Subsingleton.elim a i, Subsingleton.elim b i]
  simp

theorem scalar_of_perfect_gl_card_two {κ : Type} [Fintype κ] [DecidableEq κ]
    (hk : Fintype.card κ = 2) {S : Subgroup (GL κ K)} (hS : ⁅S, S⁆ = S) (hne : S ≠ ⊥)
    {y : Matrix κ κ K} (hy : ∀ s ∈ S, y * (s : Matrix κ κ K) = (s : Matrix κ κ K) * y) :
    ∃ c : K, y = c • (1 : Matrix κ κ K) := by
  set e : κ ≃ Fin 2 := Fintype.equivFinOfCardEq hk with he
  set R : Matrix κ κ K ≃ₐ[K] Matrix (Fin 2) (Fin 2) K := Matrix.reindexAlgEquiv K K e with hR
  let f : GL κ K →* Matrix (Fin 2) (Fin 2) K :=
    R.toAlgHom.toMonoidHom.comp (Units.coeHom (Matrix κ κ K))
  have hf : ∀ g : GL κ K, f g = R (g : Matrix κ κ K) := fun g => rfl
  obtain ⟨c, hc⟩ := sl2_central_of_perfect_hom f hS (y := R y) (fun v hv => by
    rw [hf, ← map_mul, ← map_mul, hy v hv]) (by
    obtain ⟨⟨s, hs⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    refine ⟨s, hs, fun h => hs1 (Subtype.ext (Units.ext ?_))⟩
    rw [hf] at h
    have := R.injective (h.trans (map_one R).symm)
    simpa using this)
  refine ⟨c, R.injective ?_⟩
  rw [hc, map_smul, map_one]

end Scalar


section Roots

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem card_filter_pow_eq_le {p : ℕ} (hp : 0 < p) (γ : K) :
    (Finset.univ.filter fun z : K => z ^ p = γ).card ≤ p := by
  calc _ ≤ (Polynomial.nthRoots p γ).toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        simpa [Polynomial.mem_nthRoots hp] using hz
    _ ≤ Multiset.card (Polynomial.nthRoots p γ) := Multiset.toFinset_card_le _
    _ ≤ p := Polynomial.card_nthRoots p γ

theorem exists_missing_root {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    {m : ℕ} (hm : m = p - 1) (ξ : Fin m → K) (hinj : Function.Injective ξ)
    (hξ : ∀ i, ξ i ^ p = 1) :
    ∃ l : K, l ∉ Set.range ξ ∧ l * ∏ i, ξ i = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hd : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hd
  set z : K := (ζ : K) with hz
  have hzord : orderOf z = p := by rw [hz, orderOf_units, hζ]
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  set Rt : Finset K := Finset.univ.filter fun w : K => w ^ p = 1 with hRt
  set Rz : Finset K := (Finset.range p).image fun k => z ^ k with hRz
  have hinjz : Set.InjOn (fun k : ℕ => z ^ k) (Finset.range p : Set ℕ) := by
    intro a ha b hb hab
    exact pow_injOn_Iio_orderOf (by simpa [hzord] using ha) (by simpa [hzord] using hb) hab
  have hRzc : Rz.card = p := by rw [hRz, Finset.card_image_of_injOn hinjz, Finset.card_range]
  have hRzt : Rz ⊆ Rt := by
    intro w hw
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hw
    simp only [hRt, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← pow_mul, mul_comm, pow_mul, hzp, one_pow]
  have hRtle : Rt.card ≤ p := card_filter_pow_eq_le hp.pos 1
  have hEq : Rz = Rt := Finset.eq_of_subset_of_card_le hRzt (by omega)
  have hRtc : Rt.card = p := by rw [← hEq]; exact hRzc
  have hprod : ∏ r ∈ Rt, r = 1 := by
    rw [← hEq, hRz, Finset.prod_image hinjz, Finset.prod_pow_eq_pow_sum]
    obtain ⟨t, ht⟩ : ∃ t, p = 2 * t + 1 := by
      obtain ⟨t, ht⟩ := (hp.odd_of_ne_two hp2)
      exact ⟨t, ht⟩
    have hs := Finset.sum_range_id_mul_two p
    have hs' : ∑ i ∈ Finset.range p, i = p * t := by
      have : (∑ i ∈ Finset.range p, i) * 2 = p * t * 2 := by
        rw [hs]
        have : p - 1 = 2 * t := by omega
        rw [this]; ring
      omega
    rw [hs', pow_mul, hzp, one_pow]
  set T : Finset K := Finset.univ.image ξ with hT
  have hTt : T ⊆ Rt := by
    intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
    simpa [hRt] using hξ i
  have hTc : T.card = p - 1 := by
    rw [hT, Finset.card_image_of_injective _ hinj]
    simp [hm]
  have hsd : (Rt \ T).card = 1 := by
    rw [Finset.card_sdiff_of_subset hTt, hRtc, hTc]
    have := hp.one_lt
    omega
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 hsd
  have hlmem : l ∈ Rt \ T := by rw [hl]; exact Finset.mem_singleton_self l
  refine ⟨l, fun hr => (Finset.mem_sdiff.1 hlmem).2 ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hr
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  · have h1 := Finset.prod_sdiff hTt (f := fun w : K => w)
    rw [hl, Finset.prod_singleton, hprod, hT, Finset.prod_image (fun i _ j _ h => hinj h)] at h1
    exact h1

end Roots


section TZ

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem eq_one_of_two_blocks_trivial {I : Set ℕ}
    (hsz : ∀ a b (_ : IsConsecutiveCut n I a b), b - a ≤ 2)
    {V : Subgroup (SpecialLinearGroup (Fin n) K)} (hVQ : V ≤ flagStabilizer n K I)
    (hV : ⁅V, V⁆ = V) {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ V) {m : ℕ} (hm : (m : K) ≠ 0)
    (hgm : g ^ m = 1)
    (hall : ∀ a b (h : IsConsecutiveCut n I a b), b - a = 2 →
      blockHomGL h ⟨g, hVQ hg⟩ = 1) : g = 1 := by
  set Q := flagStabilizer n K I with hQ
  have hV' : ⁅V.subgroupOf Q, V.subgroupOf Q⁆ = V.subgroupOf Q := commutator_subgroupOf_eq hVQ hV
  have hperf : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (ρ : ↥Q →* GL κ K),
      ⁅(V.subgroupOf Q).map ρ, (V.subgroupOf Q).map ρ⁆ = (V.subgroupOf Q).map ρ := by
    intro κ _ _ ρ
    rw [← Subgroup.map_commutator, hV']
  refine eq_one_of_blocks_trivial_pow (hVQ hg) hm hgm fun a b h => ?_
  by_cases hk2 : b - a = 2
  · exact (blockHomGL_eq_one_iff h ⟨g, hVQ hg⟩).1 (hall a b h hk2)
  · have hle : Fintype.card (Fin (b - a)) ≤ 1 := by
      have := hsz a b h
      simp only [Fintype.card_fin]
      omega
    have hbot := perfect_eq_bot_of_card_le_one (K := K) hle (hperf (blockHomGL h))
    have hmem : blockHomGL h ⟨g, hVQ hg⟩ ∈ (V.subgroupOf Q).map (blockHomGL h) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (blockHomGL_eq_one_iff h ⟨g, hVQ hg⟩).1 hmem

theorem cut_inj {m : ℕ} {c : ℕ → ℕ} (hmono : ∀ i < m, c i < c (i + 1)) {i j : ℕ} (hi : i ≤ m)
    (hj : j ≤ m) (h : c i = c j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := cuts_le_of_mono hmono (i := i + 1) (j := j) hlt hj
    have h2 := hmono i (by omega)
    omega
  · have h1 := cuts_le_of_mono hmono (i := j + 1) (j := i) hgt hi
    have h2 := hmono j (by omega)
    omega

theorem sum_cut_sizes {m : ℕ} {c : ℕ → ℕ} (hmono : ∀ i < m, c i < c (i + 1)) {k : ℕ} (hk : k ≤ m) :
    ∑ i ∈ Finset.range k, (c (i + 1) - c i) = c k - c 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 := cuts_le_of_mono hmono (i := 0) (j := k) (Nat.zero_le _) (by omega)
    have h2 := hmono k (by omega)
    omega

theorem false_of_tz {I : Set ℕ} (hne : I.Nonempty) (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) (hpq : p ∣ Nat.card K - 1) (hpn : p ∣ n)
    (hA1 : CoverA1 n K I p) (hA2 : CoverA2 n K I p)
    {x : SpecialLinearGroup (Fin n) K} {γ : K}
    (hxγ : (x : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) γ)
    (hγ : n = p → γ = 1)
    (hfix : Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)) ≤
      flagStabilizer n K I)
    {V : Subgroup (SpecialLinearGroup (Fin n) K)} (hVQ : V ≤ flagStabilizer n K I)
    (hVx : V ≤ Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)))
    (hV : ⁅V, V⁆ = V) (hpV : p ∣ Nat.card V) : False := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp0 : (p : K) ≠ 0 := natCast_ne_zero_of_odd_charTwo hpodd
  have hK4 : 4 ≤ Nat.card K := by
    rcases card_eq_two_or_four_le (K := K) with h2 | h4
    · rw [h2] at hpq
      have : p ≤ 1 := Nat.le_of_dvd one_pos (by simpa using hpq)
      rcases hp57 with rfl | rfl <;> omega
    · exact h4
  have hn0 : 0 < n := by
    obtain ⟨i, hi⟩ := hne
    have := (hI i hi).2
    omega
  set Q := flagStabilizer n K I with hQ
  have hxQ : x ∈ Q := hfix (Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff] at hh
    rw [hh])
  set x' : ↥Q := ⟨x, hxQ⟩ with hx'
  have hV' : ⁅V.subgroupOf Q, V.subgroupOf Q⁆ = V.subgroupOf Q := commutator_subgroupOf_eq hVQ hV
  have hγ0 : γ ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hxγ
    have h2 : (x : Matrix (Fin n) (Fin n) K).det = 1 := x.2
    have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
    rw [Matrix.det_pow, h2, h0] at h1
    simp [Matrix.scalar_apply] at h1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpV
  have hgp : (g : SpecialLinearGroup (Fin n) K) ^ p = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  have hg1 : (g : SpecialLinearGroup (Fin n) K) ≠ 1 := fun h => by
    have : g = 1 := Subtype.ext h
    rw [this, orderOf_one] at hg
    exact hp.ne_one hg.symm
  have hsz : ∀ a b (h : IsConsecutiveCut n I a b), b - a ≤ 2 := fun a b h =>
    block_size_le_two hp57 hpq hA1 h (sub_lt_of_isConsecutiveCut hI hne h)
  obtain ⟨a₀, b₀, h₀, hk₀, hg₀⟩ : ∃ a b, ∃ h : IsConsecutiveCut n I a b, b - a = 2 ∧
      blockHomGL h ⟨g, hVQ g.2⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hg1 (eq_one_of_two_blocks_trivial hsz hVQ hV g.2 hp0 hgp fun a b h hk =>
      hcon a b h hk)
  have huniq : ∀ a b (h : IsConsecutiveCut n I a b), b - a = 2 → (a, b) = (a₀, b₀) :=
    fun a b h hk => two_blocks_eq hne hI hp57 hpq hK4 hA2 h h₀ hk hk₀
  have hxV' : ∀ v ∈ V.subgroupOf Q, v * x' = x' * v := by
    intro v hv
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 (hVx (Subgroup.mem_subgroupOf.1 hv)) x
      (Set.mem_singleton x)
    exact this.symm
  have hscal : ∀ a b (h : IsConsecutiveCut n I a b), ∃ ξ : K,
      cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1 =
        ξ • (1 : Matrix (Fin (b - a)) (Fin (b - a)) K) := by
    intro a b h
    by_cases hk : b - a = 2
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (huniq a b h hk)
      refine scalar_of_perfect_gl_card_two (κ := Fin (b - a)) (by simp [hk])
        (S := (V.subgroupOf Q).map (blockHomGL h)) (by rw [← Subgroup.map_commutator, hV']) ?_ ?_
      · intro hbot
        have hmem : blockHomGL h ⟨g, hVQ g.2⟩ ∈ (V.subgroupOf Q).map (blockHomGL h) :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 g.2)
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hg₀ hmem
      · rintro _ ⟨v, hv, rfl⟩
        rw [← coe_blockHomGL h x', ← Units.val_mul, ← Units.val_mul,
          ← map_mul, ← map_mul, hxV' v hv]
    · have h1 := hsz a b h
      have h2 := h.1
      exact eq_smul_one_of_card_one (by simp; omega) _
  obtain ⟨m, c, hc0, hcm, hcons, hsurj⟩ := exists_cuts_enum n I
  have hmono : ∀ i < m, c i < c (i + 1) := fun i hi => (hcons i hi).1
  have hscal' : ∀ i : Fin m, ∃ ξ : K, ξ ^ p = γ ∧
      cutBlock (x : Matrix (Fin n) (Fin n) K) (c i) (c (i + 1)) (hcons i i.2).2.1 =
        ξ • (1 : Matrix (Fin (c (i + 1) - c i)) (Fin (c (i + 1) - c i)) K) := by
    intro i
    obtain ⟨ξ, hξ⟩ := hscal (c i) (c (i + 1)) (hcons i i.2)
    refine ⟨ξ, ?_, hξ⟩
    have hpow := map_pow (cutBlockHom (K := K) (hcons i i.2)) x' p
    rw [cutBlockHom_apply, cutBlockHom_apply] at hpow
    change cutBlock ((x ^ p : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) (c i)
      (c (i + 1)) (hcons i i.2).2.1 =
      cutBlock (x : Matrix (Fin n) (Fin n) K) (c i) (c (i + 1)) (hcons i i.2).2.1 ^ p at hpow
    rw [Matrix.SpecialLinearGroup.coe_pow, hxγ, hξ, smul_pow, one_pow] at hpow
    have h' := congrFun (congrFun hpow ⟨0, by have := (hcons i i.2).1; omega⟩)
      ⟨0, by have := (hcons i i.2).1; omega⟩
    rw [cutBlock_apply] at h'
    simpa [Matrix.scalar_apply] using h'.symm
  choose ξ hξp hξb using hscal'
  have hξ0 : ∀ i, ξ i ≠ 0 := fun i h => hγ0 (by rw [← hξp i, h, zero_pow hp.ne_zero])
  have hinj : Function.Injective ξ := by
    intro i j hij
    by_contra hne'
    have hij' : (i : ℕ) ≠ j := fun h => hne' (Fin.ext h)
    rcases lt_or_gt_of_ne hij' with hlt | hgt
    · exact false_of_scalarBlocks hpodd hxQ (hξ0 i) (by rw [hxγ, hξp i]) hfix (hcons i i.2)
        (hcons j j.2) (cuts_le_of_mono hmono (i := i + 1) (j := j) (by omega) j.2.le)
        (hξb i) (by rw [hξb j, ← hij])
    · exact false_of_scalarBlocks hpodd hxQ (hξ0 j) (by rw [hxγ, hξp j]) hfix (hcons j j.2)
        (hcons i i.2) (cuts_le_of_mono hmono (i := j + 1) (j := i) (by omega) i.2.le)
        (hξb j) (by rw [hξb i, hij])
  have hmle : m ≤ p := by
    have h1 : (Finset.univ.image ξ).card = m := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    have h2 : Finset.univ.image ξ ⊆ Finset.univ.filter fun z : K => z ^ p = γ := by
      intro w hw
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
      simpa using hξp i
    have h3 := card_filter_pow_eq_le hp.pos γ
    calc m = (Finset.univ.image ξ).card := h1.symm
      _ ≤ _ := Finset.card_le_card h2
      _ ≤ p := h3
  obtain ⟨i₀, hi₀, hca, hcb⟩ := hsurj a₀ b₀ h₀
  have hsize : ∀ i < m, c (i + 1) - c i = if i = i₀ then 2 else 1 := by
    intro i hi
    have h1 := hmono i hi
    have h2 := hsz _ _ (hcons i hi)
    by_cases hii : i = i₀
    · subst hii
      simp [hca, hcb, hk₀]
    · simp only [hii, ↓reduceIte]
      have : c (i + 1) - c i ≠ 2 := by
        intro h3
        obtain ⟨e1, -⟩ := Prod.mk.inj (huniq _ _ (hcons i hi) h3)
        exact hii (cut_inj hmono hi.le hi₀.le (by rw [e1, hca]))
      omega
  have hnm : n = m + 1 := by
    have h1 := sum_cut_sizes hmono (k := m) le_rfl
    rw [hcm, hc0, Finset.sum_congr rfl fun i hi => hsize i (Finset.mem_range.1 hi)] at h1
    have h2 : ∑ i ∈ Finset.range m, (if i = i₀ then 2 else 1) =
        ∑ i ∈ Finset.range m, (1 + if i = i₀ then 1 else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> rfl
    rw [h2, Finset.sum_add_distrib, Finset.sum_ite_eq'] at h1
    simp [hi₀] at h1
    omega
  have hnp : n = p := by
    obtain ⟨t, ht⟩ := hpn
    have h2 := hp.two_le
    rcases t with _ | _ | t
    · omega
    · omega
    · nlinarith
  have hγ1 := hγ hnp
  have hm' : m = p - 1 := by omega
  obtain ⟨l, hl, hlprod⟩ := exists_missing_root hp hp2 hpq hm' ξ hinj (fun i => by
    rw [hξp i, hγ1])
  set i₀' : Fin m := ⟨i₀, hi₀⟩ with hi₀'
  have hdet := det_eq_prod_cutBlock_det hxQ hc0 hcm hcons
  rw [x.2] at hdet
  have hdet2 : ∏ a : Fin m, (cutBlock (x : Matrix (Fin n) (Fin n) K) (c a) (c (a + 1))
      (hcons a a.2).2.1).det = (∏ a, ξ a) * ξ i₀' := by
    rw [Finset.prod_congr rfl fun a _ => by
      rw [hξb a, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hsize a a.2]]
    have : ∀ a : Fin m, ξ a ^ (if (a : ℕ) = i₀ then 2 else 1) =
        ξ a * if a = i₀' then ξ a else 1 := by
      intro a
      by_cases h : a = i₀'
      · subst h
        simp [hi₀', pow_two]
      · have h' : (a : ℕ) ≠ i₀ := fun h'' => h (Fin.ext h'')
        simp [h, h']
    rw [Finset.prod_congr rfl fun a _ => this a, Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  rw [hdet2] at hdet
  have hne0 : ∏ a, ξ a ≠ 0 := fun h => by
    rw [h, mul_zero] at hlprod
    exact zero_ne_one hlprod
  have : ξ i₀' = l := by
    apply mul_left_cancel₀ hne0
    rw [← hdet, mul_comm (∏ a, ξ a) l, hlprod]
  exact hl ⟨i₀', this⟩

end TZ


section Center

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem center_entry {n : ℕ} {z : SpecialLinearGroup (Fin n) K}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K)) (i : Fin n) :
    Matrix.scalar (Fin n) ((z : Matrix (Fin n) (Fin n) K) i i) = (z : Matrix (Fin n) (Fin n) K) ∧
      ((z : Matrix (Fin n) (Fin n) K) i i) ^ n = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have : (z : Matrix (Fin n) (Fin n) K) i i = r := by
    rw [← hrz]
    simp [Matrix.scalar_apply]
  rw [this]
  exact ⟨hrz, by simpa using hr⟩

theorem card_center_SL_le {n : ℕ} (hn : 0 < n) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) K)) ≤ n := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set i : Fin n := ⟨0, hn⟩
  let φ : ↥(Subgroup.center (SpecialLinearGroup (Fin n) K)) → {r : K // r ^ n = 1} := fun z =>
    ⟨(z : SpecialLinearGroup (Fin n) K).1 i i, (center_entry z.2 i).2⟩
  have hφ : Function.Injective φ := by
    intro z w h
    have h1 : (z : SpecialLinearGroup (Fin n) K).1 i i = (w : SpecialLinearGroup (Fin n) K).1 i i :=
      congrArg Subtype.val h
    refine Subtype.ext (Subtype.ext ?_)
    rw [← (center_entry z.2 i).1, ← (center_entry w.2 i).1, h1]
  calc _ ≤ Nat.card {r : K // r ^ n = 1} := Nat.card_le_card_of_injective φ hφ
    _ = (Finset.univ.filter fun r : K => r ^ n = 1).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ n := card_filter_pow_eq_le hn 1

theorem dvd_of_dvd_card_center_SL {n p : ℕ} (hp : p.Prime) (hn : 0 < n)
    (h : p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) K))) :
    p ∣ n ∧ p ∣ Nat.card K - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p h
  set i : Fin n := ⟨0, hn⟩
  obtain ⟨hsc, hrn⟩ := center_entry z.2 i
  set r : K := (z : SpecialLinearGroup (Fin n) K).1 i i with hr
  have hzp : (z : SpecialLinearGroup (Fin n) K) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have hz1 : (z : SpecialLinearGroup (Fin n) K) ≠ 1 := fun h1 => by
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    exact hp.ne_one hz.symm
  have hrp : r ^ p = 1 := by
    have h1 : (z : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hzp, Matrix.SpecialLinearGroup.coe_one]
    rw [← hsc, ← map_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa [Matrix.scalar_apply] using h2
  have hr1 : r ≠ 1 := fun h1 => hz1 (Subtype.ext (by
    rw [← hsc, h1, map_one, Matrix.SpecialLinearGroup.coe_one]))
  have hord : orderOf r = p := orderOf_eq_prime hrp hr1
  refine ⟨hord ▸ orderOf_dvd_of_pow_eq_one hrn, ?_⟩
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, zero_pow hp.ne_zero] at hrp; exact zero_ne_one hrp
  have hu : orderOf (Units.mk0 r hr0) = p := by
    rw [← hord, ← orderOf_units]
    rfl
  have := orderOf_dvd_natCard (Units.mk0 r hr0)
  rw [hu, Nat.card_units] at this
  exact this

theorem ker_eq_bot_of_center_dvd {n p : ℕ} (hp : p.Prime) (hn : n = p) {M : Type*} [Group M]
    {σ : SpecialLinearGroup (Fin n) K →* M} (hσs : Function.Surjective σ)
    (hker : σ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hM : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = ⊤) (hpZ : p ∣ Nat.card (Subgroup.center M)) :
    σ.ker = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := hn ▸ hp.pos
  set Z := Subgroup.center (SpecialLinearGroup (Fin n) K) with hZ
  have hcen : Subgroup.center M = Z.map σ := center_eq_map_center hσs hker hM
  have hpZ' : p ∣ Nat.card Z := by
    rw [hcen] at hpZ
    exact hpZ.trans (Subgroup.card_map_dvd Z σ)
  have hZc : Nat.card Z = p := by
    have : Nat.card Z ≤ n := card_center_SL_le (K := K) hn0
    have h2 := Nat.le_of_dvd Nat.card_pos hpZ'
    omega
  have : Fact (Nat.card ↥Z).Prime := ⟨by rw [hZc]; exact hp⟩
  by_contra hne
  rcases (σ.ker.subgroupOf Z).eq_bot_or_eq_top_of_prime_card with hb | ht
  · apply hne
    rw [eq_bot_iff]
    intro k hk
    have : (⟨k, hker hk⟩ : ↥Z) ∈ σ.ker.subgroupOf Z := hk
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · have hZk : Z ≤ σ.ker := fun z hz => by
      have : (⟨z, hz⟩ : ↥Z) ∈ σ.ker.subgroupOf Z := by rw [ht]; trivial
      exact this
    have hbot : Z.map σ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨z, hz, rfl⟩
      exact hZk hz
    rw [hcen, hbot, Subgroup.card_bot] at hpZ
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpZ)

end Center

section GroupLemmas

variable {Y : Type*} [Group Y]

theorem le_inf_centralizer_of_not_dvd [Finite Y] {L V E : Subgroup Y} {p : ℕ} (hp : p.Prime)
    (hVL : V ≤ L) (hpV : ¬ p ∣ Nat.card V) (hE : ∀ e ∈ E, e ^ p = 1)
    (hEV : E ≤ V ⊔ (L ⊓ Subgroup.centralizer (L : Set Y))) :
    E ≤ L ⊓ Subgroup.centralizer (L : Set Y) := by
  set Z : Subgroup Y := L ⊓ Subgroup.centralizer (L : Set Y) with hZ
  have hcomm : ∀ w ∈ L, ∀ z ∈ Z, w * z = z * w := fun w hw z hz =>
    Subgroup.mem_centralizer_iff.1 hz.2 w hw
  have hconj : ∀ w ∈ L, ∀ z ∈ Z, w * z * w⁻¹ = z := fun w hw z hz => by
    rw [hcomm w hw z hz, mul_assoc, mul_inv_cancel, mul_one]
  have hVn : V ≤ Subgroup.normalizer (Z : Set Y) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro z
    show z ∈ Z ↔ v * z * v⁻¹ ∈ Z
    constructor
    · intro hz
      rw [hconj v (hVL hv) z hz]
      exact hz
    · intro hz
      have h2 : z = v * z * v⁻¹ := by
        calc z = v⁻¹ * (v * z * v⁻¹) * v⁻¹⁻¹ := by group
          _ = v * z * v⁻¹ := hconj v⁻¹ (L.inv_mem (hVL hv)) _ hz
      rw [h2]
      exact hz
  intro e he
  have h1 := hEV he
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVn] at h1
  obtain ⟨v, hv, z, hz, rfl⟩ := h1
  have hvz : Commute v z := hcomm v (hVL hv) z hz
  have hpe := hE _ he
  rw [hvz.mul_pow] at hpe
  have hvp : v ^ p ^ 1 ∈ Z := by
    rw [pow_one]
    have : v ^ p = (z ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hpe
    rw [this]
    exact Z.inv_mem (Z.pow_mem hz p)
  have hord : orderOf v ∣ Nat.card V := by
    have := orderOf_dvd_natCard (⟨v, hv⟩ : ↥V)
    simpa [Subgroup.orderOf_mk] using this
  exact Z.mul_mem (mem_of_pow_mem_of_coprime hp hord hpV hvp) hz

theorem not_isCyclic_of_exponent [Finite Y] {E : Subgroup Y} {p : ℕ} (hp : p.Prime)
    (hE : ∀ e ∈ E, e ^ p = 1) (hc : Nat.card E = p ^ 2) : ¬ IsCyclic ↥E := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h0 := orderOf_eq_card_of_forall_mem_zpowers hg
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE g g.2))
  rw [h0, hc] at h1
  have := Nat.le_of_dvd hp.pos h1
  nlinarith [hp.two_le]

end GroupLemmas


section Cell

@[expose] def AltA1 {Y : Type} [Group Y] (J : Subgroup Y) (p : ℕ) : Prop :=
  ∀ X : Subgroup Y, X ≤ J → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X

@[expose] def AltA2 {Y : Type} [Group Y] (J : Subgroup Y) (p : ℕ) : Prop :=
  ∀ X₁ X₂ : Subgroup Y, X₁ ≤ J → X₂ ≤ J → CFSG.Open.IsQuasisimple ↥X₁ →
    CFSG.Open.IsQuasisimple ↥X₂ → X₂ ≤ Subgroup.centralizer (X₁ : Set Y) →
    p ∣ Nat.card X₁ → p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
    NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {K : Type} [Field K] [Finite K]
  [CharP K 2] {n : ℕ}

omit [Finite Y] [Finite K] [CharP K 2] in
theorem centralizer_le_flagStabilizer_of_fix
    {σ : SpecialLinearGroup (Fin n) K →* ↥L} {I : Set ℕ}
    (hQ : (J.subgroupOf L).comap σ = flagStabilizer n K I) {x : Y}
    (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) {xh : SpecialLinearGroup (Fin n) K}
    (hxh : ((σ xh : ↥L) : Y) = x) :
    Subgroup.centralizer ({xh} : Set (SpecialLinearGroup (Fin n) K)) ≤ flagStabilizer n K I := by
  intro g hg
  have hc := Subgroup.mem_centralizer_iff.1 hg xh (Set.mem_singleton xh)
  have h1 : σ xh * σ g = σ g * σ xh := by rw [← map_mul, ← map_mul, hc]
  have h2 : x * ((σ g : ↥L) : Y) = ((σ g : ↥L) : Y) * x := by
    rw [← hxh]
    exact congrArg Subtype.val h1
  have h3 : x * ((σ g : ↥L) : Y) * x⁻¹ = ((σ g : ↥L) : Y) := by
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
  rw [← hQ]
  exact Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 (hfix _ (σ g).2 h3))


theorem false_of_tz_cell {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    {σ : SpecialLinearGroup (Fin n) K →* ↥L} (hσs : Function.Surjective σ)
    (hker : σ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hLperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤) {I : Set ℕ} (hne : I.Nonempty)
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hQ : (J.subgroupOf L).comap σ = flagStabilizer n K I)
    (hJL : J ≤ L) (hA1 : AltA1 J p) (hA2 : AltA2 J p) {x : Y} (hxL : x ∈ L) (hxp : x ^ p = 1)
    (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) {V E : Subgroup Y} (hVJ : V ≤ J)
    (hVx : V ≤ Subgroup.centralizer ({x} : Set Y)) (hV : ⁅V, V⁆ = V)
    (hEV : E ≤ V ⊔ (L ⊓ Subgroup.centralizer (L : Set Y))) (hE : ∀ e ∈ E, e ^ p = 1)
    (hEc : Nat.card E = p ^ 2) (hpZ : p ∣ Nat.card (Subgroup.center ↥L)) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by
    obtain ⟨i, hi⟩ := hne
    have := (hI i hi).2
    omega
  have hcen : Subgroup.center ↥L = (Subgroup.center (SpecialLinearGroup (Fin n) K)).map σ :=
    center_eq_map_center hσs hker hLperf
  have hpZ' : p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) K)) := by
    rw [hcen] at hpZ
    exact hpZ.trans (Subgroup.card_map_dvd _ σ)
  obtain ⟨hpn, hpq⟩ := dvd_of_dvd_card_center_SL hp hn0 hpZ'
  set σ' : SpecialLinearGroup (Fin n) K →* Y := L.subtype.comp σ with hσ'
  have hker' : σ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
    ker_subtype_comp_le hker
  have hQle : flagStabilizer n K I ≤ J.comap σ' := by
    intro g hg
    rw [← hQ] at hg
    exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hg)
  have hA1c : CoverA1 n K I p := coverA1_of_hom σ' hker' hQle hA1
  have hA2c : CoverA2 n K I p := coverA2_of_hom σ' hker' hQle hA2
  obtain ⟨xh, hxh⟩ := hσs ⟨x, hxL⟩
  have hxh' : ((σ xh : ↥L) : Y) = x := by rw [hxh]
  obtain ⟨W, -, hW, hWmap, hWQ, hWx, -, -, -⟩ := lift_core_cover hσs hker hp hVJ (hVJ.trans hJL)
    hV hVx hxh' (E := ⊥) (IsPGroup.of_card (n := 0) (by simp)) bot_le
  rw [hQ] at hWQ
  have hfixc := centralizer_le_flagStabilizer_of_fix hQ hfix hxh'
  have hxhp : xh ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
    refine hker ?_
    rw [MonoidHom.mem_ker, map_pow, hxh]
    exact Subtype.ext (by simpa using hxp)
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hxhp
  have hxγ : (xh : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) r := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← hr]
  have hγ : n = p → r = 1 := by
    intro hnp
    have hk := ker_eq_bot_of_center_dvd hp hnp hσs hker hLperf hpZ
    have h1 : xh ^ p = 1 := by
      have : xh ^ p ∈ σ.ker := by
        rw [MonoidHom.mem_ker, map_pow, hxh]
        exact Subtype.ext (by simpa using hxp)
      rw [hk, Subgroup.mem_bot] at this
      exact this
    have h2 : Matrix.scalar (Fin n) r = 1 := by
      rw [hr, h1, Matrix.SpecialLinearGroup.coe_one]
    have h3 := congrFun (congrFun h2 ⟨0, hn0⟩) ⟨0, hn0⟩
    simpa [Matrix.scalar_apply] using h3
  have hpW : ¬ p ∣ Nat.card W := fun hpW =>
    false_of_tz hne hI hp57 hpq hpn hA1c hA2c hxγ hγ hfixc hWQ hWx hW hpW
  have hpV : ¬ p ∣ Nat.card V := fun hpV => hpW (hpV.trans (hWmap ▸ Subgroup.card_map_dvd W σ'))
  have hEZ := le_inf_centralizer_of_not_dvd hp (hVJ.trans hJL) hpV hE hEV
  have hZc : IsCyclic ↥(L ⊓ Subgroup.centralizer (L : Set Y)) := by
    rw [inf_centralizer_eq_map_center]
    have := isCyclic_center_of_cover hσs hker hLperf
    exact isCyclic_of_surjective (L.subtype.subgroupMap (Subgroup.center ↥L))
      (MonoidHom.subgroupMap_surjective _ _)
  have hEcyc : IsCyclic ↥E :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEZ).toMonoidHom (MulEquiv.surjective _)
  exact not_isCyclic_of_exponent hp hE hEc hEcyc

end Cell

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinCell
