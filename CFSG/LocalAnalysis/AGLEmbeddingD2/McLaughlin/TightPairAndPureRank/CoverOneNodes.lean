module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverA2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycNodes

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding.BlockCyc CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.Open
  CFSG.HallHigman
open scoped commutatorElement

section Elem

variable {Q : Type*} [Group Q]

theorem exists_E9_le_of_two_elements {e₁ e₂ : Q} (hc : Commute e₁ e₂) (h₁ : e₁ ^ 3 = 1)
    (h₂ : e₂ ^ 3 = 1) (hi : ∀ i j : ℕ, i < 3 → j < 3 → e₁ ^ i * e₂ ^ j = 1 → i = 0 ∧ j = 0) :
    ∃ E : Subgroup Q, E ≤ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ ∧ IsElemAbelian 3 E ∧
      Nat.card E = 9 := by
  set R : Subgroup Q := Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ with hR
  let f₁ : R := ⟨e₁, Subgroup.mem_sup_left (Subgroup.mem_zpowers e₁)⟩
  let f₂ : R := ⟨e₂, Subgroup.mem_sup_right (Subgroup.mem_zpowers e₂)⟩
  have hc' : Commute f₁ f₂ := Subtype.ext hc.eq
  have h₁' : f₁ ^ 3 = 1 := Subtype.ext (by simpa [f₁] using h₁)
  have h₂' : f₂ ^ 3 = 1 := Subtype.ext (by simpa [f₂] using h₂)
  have hi' : ∀ i j : ℕ, i < 3 → j < 3 → f₁ ^ i * f₂ ^ j = 1 → i = 0 ∧ j = 0 := by
    intro i j hi3 hj3 h
    exact hi i j hi3 hj3 (by simpa [f₁, f₂] using congrArg Subtype.val h)
  obtain ⟨E', hE'⟩ := hasE9_of_two_elements hc' h₁' h₂' hi'
  refine ⟨E'.map R.subtype, ?_, isElemAbelian_map _ hE'.1, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective R.subtype_injective, hE'.2]
    norm_num

end Elem

section Nodes

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem exists_E9_le_of_commuting_orders (π : K →* Y) (hcen : ∀ z ∈ π.ker, z ∈ Subgroup.center K)
    {a₁ a₂ b₁ b₂ : K} (h₁ : a₁ ^ 3 = 1) (h₂ : a₂ ^ 3 = 1) (hcomm : a₁ * a₂ = a₂ * a₁)
    (hb : Commute b₂ a₁) (hb₂ : ¬ Commute b₂ a₂) (hb₁ : ¬ Commute b₁ a₁) :
    ∃ E : Subgroup Y, E ≤ Subgroup.zpowers (π a₁) ⊔ Subgroup.zpowers (π a₂) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hgen : ∀ (a x : K), a ^ 3 = 1 → ∀ k : ℕ, 0 < k → k < 3 → Commute x (a ^ k) →
      Commute x a := by
    intro a x ha k hk0 hk3 hx
    interval_cases k
    · simpa using hx
    · have : a = (a ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, ha, one_mul]
      rw [this]
      exact hx.pow_right 2
  refine exists_E9_le_of_two_elements (e₁ := π a₁) (e₂ := π a₂) ?_ ?_ ?_ ?_
  · show π a₁ * π a₂ = π a₂ * π a₁
    rw [← map_mul, ← map_mul, hcomm]
  · rw [← map_pow, h₁, map_one]
  · rw [← map_pow, h₂, map_one]
  · intro s t hs ht hst
    have hker : a₁ ^ s * a₂ ^ t ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_pow, map_pow]
      exact hst
    have hz := Subgroup.mem_center_iff.1 (hcen _ hker)
    have ht0 : t = 0 := by
      by_contra ht0
      have hc1 : Commute b₂ (a₁ ^ s) := hb.pow_right s
      have hc2 : Commute b₂ (a₁ ^ s * a₂ ^ t) := hz b₂
      have hxjt : Commute b₂ (a₂ ^ t) := by
        have : a₂ ^ t = (a₁ ^ s)⁻¹ * (a₁ ^ s * a₂ ^ t) := by group
        rw [this]
        exact hc1.inv_right.mul_right hc2
      exact hb₂ (hgen a₂ b₂ h₂ t (Nat.pos_of_ne_zero ht0) ht hxjt)
    subst ht0
    have hs0 : s = 0 := by
      by_contra hs0
      have hc2 : Commute b₁ (a₁ ^ s) := by
        have := hz b₁
        rw [pow_zero, mul_one] at this
        exact this
      exact hb₁ (hgen a₁ b₁ h₁ s (Nat.pos_of_ne_zero hs0) hs hc2)
    exact ⟨hs0, rfl⟩

theorem exists_E9_of_nodes (h : BorelQuotient D n H π M) {i j : Fin D.rank}
    (hc : D.cartan i j = 0) (hij : i ≠ j) (hi : HasOrderThree D i) (hj : HasOrderThreeNC D j) :
    ∃ E : Subgroup Y, E ≤ (rankOne D.rootGroup i).map π ⊔ (rankOne D.rootGroup j).map π ∧
      IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨xi, hxi, yi, hyi, hi3, ci, hinc⟩ := hi
  obtain ⟨xj, hxj, yj, hyj, hj3, hjnc⟩ := hj
  have hcomm := commutes_rankOne_of_cartan_eq_zero h.extras hij hc
  have hXi : xi ∈ rankOne D.rootGroup i := Subgroup.mem_sup_left hxi
  have hYi : yi ∈ rankOne D.rootGroup i := Subgroup.mem_sup_right hyi
  have hXj : xj ∈ rankOne D.rootGroup j := Subgroup.mem_sup_left hxj
  have hYj : yj ∈ rankOne D.rootGroup j := Subgroup.mem_sup_right hyj
  have hAi : xi * yi ∈ rankOne D.rootGroup i := Subgroup.mul_mem _ hXi hYi
  have hAj : xj * yj ∈ rankOne D.rootGroup j := Subgroup.mul_mem _ hXj hYj
  obtain ⟨E, hE, hel, hcard⟩ := exists_E9_le_of_commuting_orders π h.ker_central
    (a₁ := xi * yi) (a₂ := xj * yj) (b₁ := ci) (b₂ := xj) hi3 hj3 (hcomm _ hAi _ hAj)
    (hcomm _ hAi _ hXj).symm hjnc (fun hc' => hinc hc'.symm)
  refine ⟨E, hE.trans (sup_le_sup ?_ ?_), hel, hcard⟩
  · exact (Subgroup.zpowers_le).2 ⟨_, hAi, rfl⟩
  · exact (Subgroup.zpowers_le).2 ⟨_, hAj, rfl⟩

end Nodes

section Over2

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y}

theorem borelQuotient_torus_eq_bot (h : BorelQuotient D n H π 1) (k : Fin D.rank) : H k = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  have := h.torus_pow k g hg
  rw [pow_one] at this
  exact this

theorem borelQuotient_injective (h : BorelQuotient D n H π 1) : Function.Injective π := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  have := h.ker_pow z hz
  rw [pow_one] at this
  exact this

theorem not_isPSolvable_map_A2 (h : BorelQuotient D n H π 1)
    (h6 : ∀ i, Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    (h3 : ∀ i, HasOrderThree D i) {i j : Fin D.rank} (hij : i ≠ j) (hAij : D.cartan i j = -1)
    (hAji : D.cartan j i = -1)
    (hperf : ⁅rankOne D.rootGroup i ⊔ rankOne D.rootGroup j,
      rankOne D.rootGroup i ⊔ rankOne D.rootGroup j⁆ =
        rankOne D.rootGroup i ⊔ rankOne D.rootGroup j) :
    ¬ IsPSolvable 3 ↥((rankOne D.rootGroup i ⊔ rankOne D.rootGroup j).map π) := by
  intro hs
  have hker : π.ker ≤ Subgroup.center K := fun z hz => h.ker_central z hz
  have hU2 : IsPGroup 2 (posUnipotent D) :=
    Lie.posUnipotent_isPGroup_of h.extras h.pGroup
  have hnot9 := not_nine_dvd_card_rankOne_sup h.ct h.extras (borelQuotient_torus_eq_bot h) hU2 h6 hij hAij hAji
  set V : Subgroup K := rankOne D.rootGroup i ⊔ rankOne D.rootGroup j with hV
  obtain ⟨u, hu, hord⟩ := exists_order_three_map (π := π) (h3 i) hker
  have hu' : u ∈ V.map π := Subgroup.map_mono (le_sup_left (b := rankOne D.rootGroup j)) hu
  have h3dvd : 3 ∣ Nat.card (V.map π) := by
    have := Subgroup.orderOf_dvd_natCard _ hu'
    rwa [hord] at this
  have h9 : ¬ 9 ∣ Nat.card (V.map π) := fun h9 => hnot9 (h9.trans (Subgroup.card_map_dvd _ _))
  exact false_of_perfect_three_pSolvable hs (map_commutator_self_eq π hperf) h3dvd h9

theorem false_of_orth_adj (h : BorelQuotient D n H π 1) {exc : Fin D.rank → Fin D.rank → Prop}
    (hL : TwoLevi D exc) (h3 : ∀ i, HasOrderThree D i) (h3nc : ∀ i, HasOrderThreeNC D i)
    (h6 : ∀ i, Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    (hA2 : ∀ i j, i ≠ j → D.cartan i j ≠ 0 → ¬ exc i j →
      D.cartan i j = -1 ∧ D.cartan j i = -1)
    (hexc : ∀ i j, exc i j → ¬ IsPSolvable 3 ↥(rankOne D.rootGroup i ⊔ rankOne D.rootGroup j))
    {C : Subgroup Y} (hC : SolvFree C) {u w a b : Fin D.rank} (huw : u ≠ w)
    (hu0 : D.cartan u w = 0) (hab : a ≠ b) (hab0 : D.cartan a b ≠ 0)
    (hu : (rankOne D.rootGroup u).map π ≤ C) (hw : (rankOne D.rootGroup w).map π ≤ C)
    (ha : (rankOne D.rootGroup a).map π ≤ C) (hb : (rankOne D.rootGroup b).map π ≤ C) : False := by
  obtain ⟨E, hE, hel, hcard⟩ := exists_E9_of_nodes h hu0 huw (h3 u) (h3nc w)
  have hEC : E ≤ C := hE.trans (sup_le hu hw)
  have hVns : ¬ IsPSolvable 3 ↥((rankOne D.rootGroup a ⊔ rankOne D.rootGroup b).map π) := by
    by_cases he : exc a b
    · exact fun hs => hexc a b he (Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
        (Subgroup.equivMapOfInjective _ π (borelQuotient_injective h)).symm hs)
    · obtain ⟨h1, h2⟩ := hA2 a b hab hab0 he
      have hna : ⁅rankOne D.rootGroup a, rankOne D.rootGroup a⁆ ≠ rankOne D.rootGroup a :=
        Lie.commutator_ne_self_of_card_six (h6 a).1
      have hnb : ⁅rankOne D.rootGroup b, rankOne D.rootGroup b⁆ ≠ rankOne D.rootGroup b :=
        Lie.commutator_ne_self_of_card_six (h6 b).1
      rcases hL.pair a b hab hab0 hna hnb with hperf | hexc'
      · exact not_isPSolvable_map_A2 h h6 h3 hab h1 h2 hperf
      · exact absurd hexc' he
  have hVC : (rankOne D.rootGroup a ⊔ rankOne D.rootGroup b).map π ≤ C := by
    rw [Subgroup.map_sup]; exact sup_le ha hb
  exact hVns (hC E _ hEC hVC hel hcard)

theorem exists_E27_of_nodes (h : BorelQuotient D n H π 1) (h3 : ∀ i, HasOrderThree D i)
    (h6 : ∀ i, Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    {i j l : Fin D.rank} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (hij0 : D.cartan i j = 0)
    (hil0 : D.cartan i l = 0) (hjl0 : D.cartan j l = 0) :
    ∃ E : Subgroup Y, E ≤ (rankOne D.rootGroup i).map π ⊔ (rankOne D.rootGroup j).map π ⊔
      (rankOne D.rootGroup l).map π ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcij := commutes_rankOne_of_cartan_eq_zero h.extras hij hij0
  have hcil := commutes_rankOne_of_cartan_eq_zero h.extras hil hil0
  have hcjl := commutes_rankOne_of_cartan_eq_zero h.extras hjl hjl0
  obtain ⟨ci, hci, hci1, hci3⟩ := exists_order_three_rankOne (h3 i)
  obtain ⟨cj, hcj, hcj1, hcj3⟩ := exists_order_three_rankOne (h3 j)
  obtain ⟨cl, hcl, hcl1, hcl3⟩ := exists_order_three_rankOne (h3 l)
  obtain ⟨E, hE, hEel, hEc⟩ := exists_elemAbelian_card_nine (h6 i).1 (h6 i).2 hcij hci hcj hci1 hcj1
    hci3 hcj3
  have hcomm : ∀ x ∈ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j, ∀ c ∈ rankOne D.rootGroup l,
      x * c = c * x := Lie.commute_sup_of hcil hcjl
  have hyC : cl ∈ Subgroup.centralizer (E : Set K) :=
    Subgroup.mem_centralizer_iff.2 fun g hg => hcomm g (hE hg) cl hcl
  have hzC : Subgroup.zpowers cl ≤ Subgroup.centralizer (E : Set K) := Subgroup.zpowers_le.2 hyC
  have hel : IsElemAbelian 3 (E ⊔ Subgroup.zpowers cl) :=
    CFSG.AGLEmbedding.isElemAbelian_sup_zpowers_of_mem_centralizer hEel hyC hcl3
  have hinf : E ⊓ Subgroup.zpowers cl = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzE, hzc⟩
    have hzL : z ∈ rankOne D.rootGroup l := (Subgroup.zpowers_le.2 hcl) hzc
    refine Subgroup.mem_bot.2 (Lie.eq_one_of_central_of_card_six (h6 l).1 (h6 l).2 hzL
      fun x hx => hcomm z (hE hzE) x hx)
  have hcard : Nat.card (E ⊔ Subgroup.zpowers cl : Subgroup K) = 27 := by
    have hn : Subgroup.zpowers cl ≤ Subgroup.normalizer (E : Set K) :=
      Lie.le_normalizer_of_commute (A := E) (B := Subgroup.zpowers cl) fun a ha b hb =>
        Subgroup.mem_centralizer_iff.1 (hzC hb) a ha
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hn
    rw [hinf, Subgroup.card_bot, mul_one, hEc, Nat.card_zpowers, orderOf_eq_prime hcl3 hcl1] at h1
    omega
  have hinj : Function.Injective π := borelQuotient_injective h
  refine ⟨(E ⊔ Subgroup.zpowers cl).map π, ?_, isElemAbelian_map π hel, ?_⟩
  · have hle : E ⊔ Subgroup.zpowers cl ≤
        rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ⊔ rankOne D.rootGroup l :=
      sup_le (hE.trans le_sup_left) (Subgroup.zpowers_le.2 (Subgroup.mem_sup_right hcl))
    refine (Subgroup.map_mono hle).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_sup]
  · rw [Subgroup.card_map_of_injective hinj, hcard]

theorem false_of_triple (h : BorelQuotient D n H π 1) {exc : Fin D.rank → Fin D.rank → Prop}
    (hL : TwoLevi D exc) (h3 : ∀ i, HasOrderThree D i) (h3nc : ∀ i, HasOrderThreeNC D i)
    (h6 : ∀ i, Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    (hA2 : ∀ i j, i ≠ j → D.cartan i j ≠ 0 → ¬ exc i j →
      D.cartan i j = -1 ∧ D.cartan j i = -1)
    (hexc : ∀ i j, exc i j → ¬ IsPSolvable 3 ↥(rankOne D.rootGroup i ⊔ rankOne D.rootGroup j))
    (htri : ∀ i j l : Fin D.rank, i ≠ j → i ≠ l → j ≠ l → D.cartan i j ≠ 0 → D.cartan j l ≠ 0 →
      D.cartan i l ≠ 0 → False)
    {C : Subgroup Y} (hC : SolvFree C) (hC27 : E27Free C) {i j l : Fin D.rank} (hij : i ≠ j)
    (hil : i ≠ l) (hjl : j ≠ l) (hi : (rankOne D.rootGroup i).map π ≤ C)
    (hj : (rankOne D.rootGroup j).map π ≤ C) (hl : (rankOne D.rootGroup l).map π ≤ C) : False := by
  have key := fun {u w a b : Fin D.rank} (huw : u ≠ w) (hu0 : D.cartan u w = 0) (hab : a ≠ b)
      (hab0 : D.cartan a b ≠ 0) (hu : (rankOne D.rootGroup u).map π ≤ C)
      (hw : (rankOne D.rootGroup w).map π ≤ C) (ha : (rankOne D.rootGroup a).map π ≤ C)
      (hb : (rankOne D.rootGroup b).map π ≤ C) =>
    false_of_orth_adj h hL h3 h3nc h6 hA2 hexc hC huw hu0 hab hab0 hu hw ha hb
  by_cases h1 : D.cartan i j = 0 <;> by_cases h2 : D.cartan i l = 0 <;>
    by_cases h4 : D.cartan j l = 0
  · obtain ⟨E, hE, hel, hcard⟩ := exists_E27_of_nodes h h3 h6 hij hil hjl h1 h2 h4
    exact hC27 E (hE.trans (sup_le (sup_le hi hj) hl)) hel (by omega)
  · exact key hij h1 hjl h4 hi hj hj hl
  · exact key hij h1 hil h2 hi hj hi hl
  · exact key hij h1 hil h2 hi hj hi hl
  · exact key hil h2 hij h1 hi hl hi hj
  · exact key hil h2 hij h1 hi hl hi hj
  · exact key hjl h4 hij h1 hj hl hi hj
  · exact htri i j l hij hil hjl h1 h4 h2

theorem false_of_five_nodes (h : BorelQuotient D n H π 1) {exc : Fin D.rank → Fin D.rank → Prop}
    (hL : TwoLevi D exc) (h3 : ∀ i, HasOrderThree D i) (h3nc : ∀ i, HasOrderThreeNC D i)
    (h6 : ∀ i, Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    (hA2 : ∀ i j, i ≠ j → D.cartan i j ≠ 0 → ¬ exc i j →
      D.cartan i j = -1 ∧ D.cartan j i = -1)
    (hexc : ∀ i j, exc i j → ¬ IsPSolvable 3 ↥(rankOne D.rootGroup i ⊔ rankOne D.rootGroup j))
    (htri : ∀ i j l : Fin D.rank, i ≠ j → i ≠ l → j ≠ l → D.cartan i j ≠ 0 → D.cartan j l ≠ 0 →
      D.cartan i l ≠ 0 → False)
    {C₁ C₂ : Subgroup Y} (hC₁ : SolvFree C₁) (hC₁' : E27Free C₁) (hC₂ : SolvFree C₂)
    (hC₂' : E27Free C₂)
    (hcov : ∀ i, (rankOne D.rootGroup i).map π ≤ C₁ ∨ (rankOne D.rootGroup i).map π ≤ C₂)
    (hrank : 5 ≤ D.rank) : False := by
  classical
  let ι : Fin 5 → Fin D.rank := fun k => ⟨k.val, by omega⟩
  have hι : ∀ {a b : Fin 5}, a ≠ b → ι a ≠ ι b := fun hab e => hab (Fin.ext (by
    have := congrArg Fin.val e
    simpa [ι] using this))
  let c : Fin 5 → Bool := fun k => decide ((rankOne D.rootGroup (ι k)).map π ≤ C₁)
  obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card c (n := 2) (by simp)
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.1 hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hd
  cases y
  · have hn : ∀ k, c k = false → (rankOne D.rootGroup (ι k)).map π ≤ C₂ := by
      intro k hk
      have : ¬ (rankOne D.rootGroup (ι k)).map π ≤ C₁ := by simpa [c] using hk
      exact (hcov _).resolve_left this
    exact false_of_triple h hL h3 h3nc h6 hA2 hexc htri hC₂ hC₂' (hι hab) (hι had) (hι hbd)
      (hn a ha) (hn b hb) (hn d hd)
  · have hn : ∀ k, c k = true → (rankOne D.rootGroup (ι k)).map π ≤ C₁ := by
      intro k hk
      simpa [c] using hk
    exact false_of_triple h hL h3 h3nc h6 hA2 hexc htri hC₁ hC₁' (hι hab) (hι had) (hι hbd)
      (hn a ha) (hn b hb) (hn d hd)

end Over2

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
