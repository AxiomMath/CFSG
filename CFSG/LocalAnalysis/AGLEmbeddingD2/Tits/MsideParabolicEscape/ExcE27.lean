module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.CommutingOrderThreeTriple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverBig
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverE9

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.QuasithinUnique CFSG.Open
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

theorem not_mem_of_inverted {G : Type*} [Group G] {u t : G} {S : Subgroup G}
    (hu : orderOf u = 3) (hS : ∀ s ∈ S, t * s = s * t) (hinv : t * u * t⁻¹ = u⁻¹) : u ∉ S := by
  intro huS
  have h1 : t * u * t⁻¹ = u := by rw [hS u huS]; group
  rw [h1] at hinv
  have h2 : u ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.2 hinv
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hu] at this
  omega

variable {W : Type} [Group W] [Finite W] {K Y : Type} [Group K] [Finite K] [Group Y]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem node_lift {L A : Subgroup W} {π : K →* ↥L ⧸ Subgroup.center ↥L}
    (hsq : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, x ^ 2 = 1) {m : Fin D.rank}
    (hm : (rankOne D.rootGroup m).map π ≤
      (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
    {x y : K} (hx : x ∈ D.rootGroup (Pi.single m 1)) (hy : y ∈ D.rootGroup (-Pi.single m 1))
    (ho : orderOf (π (x * y)) = 3) :
    ∃ b v : ↥L, (v : W) ∈ A ∧ (b : W) ∈ A ∧ QuotientGroup.mk' (Subgroup.center ↥L) b = π y ∧
      QuotientGroup.mk' (Subgroup.center ↥L) v = π (x * y) ∧ v ^ 3 = 1 ∧ b * v * b⁻¹ = v⁻¹ := by
  have hroot : (Pi.single m 1 : Fin D.rank → ℤ) ∈ D.roots ∧
      (-Pi.single m 1 : Fin D.rank → ℤ) ∈ D.roots :=
    ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).single_mem m,
      (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem m)⟩
  have hLi : ∀ x ∈ D.rootGroup (Pi.single m 1), x ∈ rankOne D.rootGroup m :=
    fun x hx => le_sup_left (b := D.rootGroup (-Pi.single m 1)) hx
  have hLi' : ∀ x ∈ D.rootGroup (-Pi.single m 1), x ∈ rankOne D.rootGroup m :=
    fun x hx => le_sup_right (a := D.rootGroup (Pi.single m 1)) hx
  set q := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  obtain ⟨a, ha, haq⟩ := hm ⟨x, hLi x hx, rfl⟩
  obtain ⟨b, hb, hbq⟩ := hm ⟨y, hLi' y hy, rfl⟩
  have hsq' : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, π x ^ 2 = 1 := fun γ hγ x hx => by
    rw [← map_pow, hsq γ hγ x hx, map_one]
  have hqker : q.ker ≤ Subgroup.center ↥L := by rw [hq, QuotientGroup.ker_mk']
  have hab : q (a * b) = π (x * y) := by rw [map_mul, haq, hbq, map_mul]
  obtain ⟨v, hv_mem, hvq, hv3, hvinv⟩ := exists_threeLift q hqker
    (a := a) (b := b) (by rw [haq]; exact hsq' _ hroot.1 x hx)
    (by rw [hbq]; exact hsq' _ hroot.2 y hy) (by rw [hab]; exact ho)
  refine ⟨b, v, ?_, Subgroup.mem_subgroupOf.1 hb, hbq, by rw [hvq, hab], hv3, hvinv⟩
  have h : Subgroup.closure {a, b} ≤ A.comap L.subtype := by
    rw [Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | rfl
    · exact Subgroup.mem_subgroupOf.1 ha
    · exact Subgroup.mem_subgroupOf.1 hb
  exact h hv_mem

theorem false_of_triple_in_cover {L A : Subgroup W} (hL : IsComponentOf L ⊤)
    (hE : ∀ E : Subgroup W, E ≤ A ⊓ L → IsPGroup 3 E → ¬ IsCyclic E → Nat.card E = 9)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (hπ : BorelQuotient D n H π M)
    (hsq : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, x ^ 2 = 1)
    (hord : ∀ k : Fin D.rank, ∃ x ∈ D.rootGroup (Pi.single k 1),
      ∃ y ∈ D.rootGroup (-Pi.single k 1), orderOf (π (x * y)) = 3)
    {i j k : Fin D.rank} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (cij : D.cartan i j = 0) (cik : D.cartan i k = 0) (cjk : D.cartan j k = 0)
    (hi : (rankOne D.rootGroup i).map π ≤
      (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
    (hj : (rankOne D.rootGroup j).map π ≤
      (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
    (hk : (rankOne D.rootGroup k).map π ≤
      (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set q := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  have hqker : q.ker ≤ Subgroup.center ↥L := by rw [hq, QuotientGroup.ker_mk']
  have hroot : ∀ m : Fin D.rank, (Pi.single m 1 : Fin D.rank → ℤ) ∈ D.roots ∧
      (-Pi.single m 1 : Fin D.rank → ℤ) ∈ D.roots := fun m =>
    ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).single_mem m,
      (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem m)⟩
  have hLi : ∀ m : Fin D.rank, ∀ x ∈ D.rootGroup (Pi.single m 1), x ∈ rankOne D.rootGroup m :=
    fun m x hx => le_sup_left (b := D.rootGroup (-Pi.single m 1)) hx
  have hLi' : ∀ m : Fin D.rank, ∀ x ∈ D.rootGroup (-Pi.single m 1), x ∈ rankOne D.rootGroup m :=
    fun m x hx => le_sup_right (a := D.rootGroup (Pi.single m 1)) hx
  have hC : ∀ {m m' : Fin D.rank}, m ≠ m' → D.cartan m m' = 0 → ∀ u ∈ rankOne D.rootGroup m,
      ∀ w ∈ rankOne D.rootGroup m', π u * π w = π w * π u := fun hmm' hc u hu w hw => by
    rw [← map_mul, ← map_mul,
      commutes_rankOne_of_cartan_eq_zero hπ.extras hmm' hc u hu w hw]
  obtain ⟨xi, hxi, yi, hyi, hoi⟩ := hord i
  obtain ⟨xj, hxj, yj, hyj, hoj⟩ := hord j
  obtain ⟨xk, hxk, yk, hyk, hok⟩ := hord k
  obtain ⟨bi, vi, hvi_A, hbi_A, hbiq, hviq, hvi3, hvi_inv⟩ := node_lift hsq hi hxi hyi hoi
  obtain ⟨bj, vj, hvj_A, hbj_A, hbjq, hvjq, hvj3, hvj_inv⟩ := node_lift hsq hj hxj hyj hoj
  obtain ⟨bk, vk, hvk_A, hbk_A, hbkq, hvkq, hvk3, hvk_inv⟩ := node_lift hsq hk hxk hyk hok
  have hxyi : xi * yi ∈ rankOne D.rootGroup i :=
    Subgroup.mul_mem _ (hLi i xi hxi) (hLi' i yi hyi)
  have hxyj : xj * yj ∈ rankOne D.rootGroup j :=
    Subgroup.mul_mem _ (hLi j xj hxj) (hLi' j yj hyj)
  have hxyk : xk * yk ∈ rankOne D.rootGroup k :=
    Subgroup.mul_mem _ (hLi k xk hxk) (hLi' k yk hyk)
  set ui := π (xi * yi) with hui
  set uj := π (xj * yj) with huj
  set uk := π (xk * yk) with huk
  have cij' : ui * uj = uj * ui := hC hij cij _ hxyi _ hxyj
  have cik' : ui * uk = uk * ui := hC hik cik _ hxyi _ hxyk
  have cjk' : uj * uk = uk * uj := hC hjk cjk _ hxyj _ hxyk
  have bcomm : ∀ {m m' : Fin D.rank}, m ≠ m' → D.cartan m m' = 0 → ∀ (w : K),
      w ∈ rankOne D.rootGroup m' → ∀ u ∈ rankOne D.rootGroup m, π u * π w = π w * π u :=
    fun hmm' hc w hw u hu => hC hmm' hc u hu w hw
  have hvij : vi * vj = vj * vi := by
    refine commute_of_inverted q hqker hvj3 hvj_inv ?_ ?_
    · rw [map_mul, map_mul, hviq, hvjq]; exact cij'
    · rw [map_mul, map_mul, hbjq, hviq]
      exact (hC hij cij _ hxyi _ (hLi' j yj hyj)).symm
  have hvik : vi * vk = vk * vi := by
    refine commute_of_inverted q hqker hvk3 hvk_inv ?_ ?_
    · rw [map_mul, map_mul, hviq, hvkq]; exact cik'
    · rw [map_mul, map_mul, hbkq, hviq]
      exact (hC hik cik _ hxyi _ (hLi' k yk hyk)).symm
  have hvjk : vj * vk = vk * vj := by
    refine commute_of_inverted q hqker hvk3 hvk_inv ?_ ?_
    · rw [map_mul, map_mul, hvjq, hvkq]; exact cjk'
    · rw [map_mul, map_mul, hbkq, hvjq]
      exact (hC hjk cjk _ hxyj _ (hLi' k yk hyk)).symm
  have hoi' : orderOf ui = 3 := hoi
  have hoj' : orderOf uj = 3 := hoj
  have hok' : orderOf uk = 3 := hok
  have hinv : ∀ {m : Fin D.rank} {x y : K}, x ∈ D.rootGroup (Pi.single m 1) →
      y ∈ D.rootGroup (-Pi.single m 1) → π x * π (x * y) * (π x)⁻¹ = (π (x * y))⁻¹ := by
    intro m x y hx hy
    have hx2 : π x ^ 2 = 1 := by rw [← map_pow, hsq _ (hroot m).1 x hx, map_one]
    have hy2 : π y ^ 2 = 1 := by rw [← map_pow, hsq _ (hroot m).2 y hy, map_one]
    have hxi' : (π x)⁻¹ = π x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx2)
    have hyi' : (π y)⁻¹ = π y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hy2)
    rw [map_mul, mul_inv_rev, hxi', hyi']
    calc π x * (π x * π y) * π x = π x ^ 2 * π y * π x := by simp [pow_two, mul_assoc]
      _ = π y * π x := by rw [hx2, one_mul]
  have hnot_j : uj ∉ Subgroup.zpowers ui := by
    refine not_mem_of_inverted (t := π xj) hoj' ?_ (hinv hxj hyj)
    intro s hs
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    have : π xj * ui = ui * π xj := (hC hij cij _ hxyi _ (hLi j xj hxj)).symm
    exact ((Commute.zpow_right (show Commute (π xj) ui from this) m).eq)
  have hnot_k : uk ∉ Subgroup.closure {ui, uj} := by
    have hXi : π xk * ui = ui * π xk := (hC hik cik _ hxyi _ (hLi k xk hxk)).symm
    have hXj : π xk * uj = uj * π xk := (hC hjk cjk _ hxyj _ (hLi k xk hxk)).symm
    have hcl : Subgroup.closure {ui, uj} ≤ Subgroup.centralizer {π xk} := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      rcases ht with rfl | rfl
      · exact hXi
      · exact hXj
    exact not_mem_of_inverted (t := π xk) hok'
      (fun s hs => Subgroup.mem_centralizer_iff.1 (hcl hs) (π xk) rfl) (hinv hxk hyk)
  have hxy : (vi : W) * vj = vj * vi := congrArg Subtype.val hvij
  have hxz : (vi : W) * vk = vk * vi := congrArg Subtype.val hvik
  have hyz : (vj : W) * vk = vk * vj := congrArg Subtype.val hvjk
  have hx3 : (vi : W) ^ 3 = 1 := by simpa using congrArg Subtype.val hvi3
  have hy3 : (vj : W) ^ 3 = 1 := by simpa using congrArg Subtype.val hvj3
  have hz3 : (vk : W) ^ 3 = 1 := by simpa using congrArg Subtype.val hvk3
  have hinj : ∀ a b : ℕ, (vi : W) ^ a * (vj : W) ^ b = 1 → 3 ∣ a ∧ 3 ∣ b := by
    intro a b h
    have h' : vi ^ a * vj ^ b = 1 := Subtype.ext (by simpa using h)
    have h'' := congrArg q h'
    rw [map_mul, map_pow, map_pow, hviq, hvjq, map_one] at h''
    exact three_dvd_of_pow_mul_pow_eq_one hoi' hoj' hnot_j h''
  have hE'card : Nat.card (Subgroup.closure {(vi : W), (vj : W)}) = 9 :=
    card_closure_pair hxy hx3 hy3 hinj
  set E : Subgroup W := Subgroup.closure {(vi : W), (vj : W), (vk : W)} with hEdef
  have hE'le : Subgroup.closure {(vi : W), (vj : W)} ≤ E := by
    refine Subgroup.closure_mono ?_
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht ⊢
    tauto
  have hEle : E ≤ A ⊓ L := by
    rw [hEdef, Subgroup.closure_le]
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨hvi_A, vi.2⟩
    · exact ⟨hvj_A, vj.2⟩
    · exact ⟨hvk_A, vk.2⟩
  have hpow : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    obtain ⟨a, b, c, rfl⟩ := OrdinaryProofs.CommutingOrderThreeTriple.exists_normalForm_of_mem
      (show Commute (vi : W) vj from hxy) (show Commute (vi : W) vk from hxz)
      (show Commute (vj : W) vk from hyz) he
    exact OrdinaryProofs.CommutingOrderThreeTriple.pow_three_eq_one_of_normalForm
      (show Commute (vi : W) vj from hxy) (show Commute (vi : W) vk from hxz)
      (show Commute (vj : W) vk from hyz) hx3 hy3 hz3 a b c
  have hPG : IsPGroup 3 E := by
    intro g
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hpow g.1 g.2)
    exact ⟨1, by simpa using hg3⟩
  have hcardE : 9 ≤ Nat.card E := by
    rw [← hE'card]
    exact Subgroup.card_le_of_le hE'le
  have hnc : ¬ IsCyclic E := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have h1 : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hpow g.1 g.2)
    have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have h9 := hE E hEle hPG hnc
  have heq : Subgroup.closure {(vi : W), (vj : W)} = E :=
    Subgroup.eq_of_le_of_card_ge hE'le (by rw [hE'card, h9])
  have hz : (vk : W) ∈ Subgroup.closure {(vi : W), (vj : W)} := by
    rw [heq]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨a, b, hab⟩ := exists_pow_mul_pow_of_mem_closure hxy hx3 hy3 hz
  have hvk' : vk = vi ^ a * vj ^ b := Subtype.ext (by simpa using hab)
  apply hnot_k
  rw [← hvkq, hvk', map_mul, map_pow, map_pow, hviq, hvjq]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem false_of_cover_triple {L S₀ A₁ A₂ : Subgroup W} (hL : IsComponentOf L ⊤)
    (hS : IsSylowTwoOf S₀ L) (hcov : CoveredByTwo L S₀ A₁ A₂)
    (h1 : CFSG.HallHigman.IsPSolvable 3 ↥A₁) (h2 : CFSG.HallHigman.IsPSolvable 3 ↥A₂)
    (hE : ∀ E : Subgroup W, (E ≤ A₁ ⊓ L ∨ E ≤ A₂ ⊓ L) → IsPGroup 3 E → ¬ IsCyclic E →
      Nat.card E = 9)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M)
    (hsq : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, x ^ 2 = 1)
    (hord : ∀ {π' : K →* ↥L ⧸ Subgroup.center ↥L}, BorelQuotient D n H π' M →
      ∀ k : Fin D.rank, ∃ x ∈ D.rootGroup (Pi.single k 1), ∃ y ∈ D.rootGroup (-Pi.single k 1),
        orderOf (π' (x * y)) = 3)
    (hfam : ∀ {π' : K →* ↥L ⧸ Subgroup.center ↥L}, BorelQuotient D n H π' M →
      ∀ c : Fin D.rank → Bool,
        (∃ i j, i ≠ j ∧ c i = c j ∧ ¬ CFSG.HallHigman.IsPSolvable 3
          ↥((rankOne D.rootGroup i ⊔ rankOne D.rootGroup j).map π')) ∨
        (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ D.cartan i j = 0 ∧ D.cartan i k = 0 ∧
          D.cartan j k = 0 ∧ c i = c j ∧ c j = c k)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π', hπ', hT⟩ := exists_borelQuotient_conj hS h
  have hnode := cover_of_borelQuotient hS hcov hπ' hT
  set q := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  let c : Fin D.rank → Bool :=
    fun i => decide ((rankOne D.rootGroup i).map π' ≤ (A₁.subgroupOf L).map q)
  rcases hfam hπ' c with ⟨i, j, hij, hc, hns⟩ | ⟨i, j, k, hij, hik, hjk, cij, cik, cjk, hc1, hc2⟩
  · apply hns
    rw [Subgroup.map_sup]
    by_cases hi1 : (rankOne D.rootGroup i).map π' ≤ (A₁.subgroupOf L).map q
    · have hj1 : (rankOne D.rootGroup j).map π' ≤ (A₁.subgroupOf L).map q := by
        have : c j = true := by rw [← hc]; simp [c, hi1]
        simpa [c] using this
      exact OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
        (isPSolvable_map_subgroupOf L h1) (sup_le hi1 hj1)
    · have hi2 := (hnode i).resolve_left hi1
      have hj1 : ¬ (rankOne D.rootGroup j).map π' ≤ (A₁.subgroupOf L).map q := by
        have : c j = false := by rw [← hc]; simp [c, hi1]
        simpa [c] using this
      have hj2 := (hnode j).resolve_left hj1
      exact OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
        (isPSolvable_map_subgroupOf L h2) (sup_le hi2 hj2)
  · by_cases hi1 : (rankOne D.rootGroup i).map π' ≤ (A₁.subgroupOf L).map q
    · have hj1 : (rankOne D.rootGroup j).map π' ≤ (A₁.subgroupOf L).map q := by
        have : c j = true := by rw [← hc1]; simp [c, hi1]
        simpa [c] using this
      have hk1 : (rankOne D.rootGroup k).map π' ≤ (A₁.subgroupOf L).map q := by
        have : c k = true := by rw [← hc2]; simpa [c] using hj1
        simpa [c] using this
      exact false_of_triple_in_cover hL (fun E hE1 hp hnc => hE E (Or.inl hE1) hp hnc) hπ' hsq
        (hord hπ') hij hik hjk cij cik cjk hi1 hj1 hk1
    · have hi2 := (hnode i).resolve_left hi1
      have hj1 : ¬ (rankOne D.rootGroup j).map π' ≤ (A₁.subgroupOf L).map q := by
        have : c j = false := by rw [← hc1]; simp [c, hi1]
        simpa [c] using this
      have hk1 : ¬ (rankOne D.rootGroup k).map π' ≤ (A₁.subgroupOf L).map q := by
        have : c k = false := by rw [← hc2]; simpa [c] using hj1
        simpa [c] using this
      exact false_of_triple_in_cover hL (fun E hE1 hp hnc => hE E (Or.inr hE1) hp hnc) hπ' hsq
        (hord hπ') hij hik hjk cij cik cjk hi2 ((hnode j).resolve_left hj1)
        ((hnode k).resolve_left hk1)

theorem exists_orderThree_of_hasOrderThree {π : K →* Y} (hπ : BorelQuotient D n H π M)
    {k : Fin D.rank} (h3 : HasOrderThree D k) :
    ∃ x ∈ D.rootGroup (Pi.single k 1), ∃ y ∈ D.rootGroup (-Pi.single k 1),
      orderOf (π (x * y)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx, y, hy, h3, c, hc⟩ := h3
  refine ⟨x, hx, y, hy, orderOf_eq_prime (by rw [← map_pow, h3, map_one]) (fun h1 => hc ?_)⟩
  exact ((Subgroup.mem_center_iff.1 (hπ.ker_central _ (MonoidHom.mem_ker.2 h1)) c)).symm

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional
