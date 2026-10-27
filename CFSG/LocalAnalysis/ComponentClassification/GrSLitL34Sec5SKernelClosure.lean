module

public import CFSG.GroupTheory.ElementaryAbelianNormalizerBound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeW

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.ClassicalInvolution.Balance (TwoBalancedWrt)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_inf_centralizer_of_sq {S A : Subgroup G} {y u : G} (hAS : A ≤ S)
    (hA : IsElemTwo A) (hA8 : 8 ≤ Nat.card A) (hyA : y ∈ normalizer (A : Set G))
    (hy2 : ∀ e ∈ A, y * y * e = e * (y * y)) (huS : u ∈ S) (hu2 : u * u = 1)
    (huy : u * y = y * u) (huA : ∀ e ∈ A ⊓ centralizer ({y} : Set G), u * e = e * u)
    (hunA : u ∉ A) :
    3 ≤ pRank 2 ↥(S ⊓ centralizer ({y} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := A ⊓ centralizer ({y} : Set G)
  have hCe : IsElemTwo C := hA.mono inf_le_left
  have hC4 : 4 ≤ Nat.card C := by
    have hAe : IsElementaryAbelian 2 ↥A :=
      { is_comm := ⟨fun x y => Subtype.ext (hA.1 x x.2 y y.2)⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (by
            show (x : G) ^ 2 = 1
            rw [pow_two]
            exact hA.2 x x.2) }
    refine (le_card_of_le_card_sq hCe.isPGroup).1 ?_
    refine hA8.trans (CFSG.GroupTheory.card_le_card_inf_centralizer_sq hyA ?_)
    rw [mem_centralizer_iff]
    intro e he
    rw [pow_two]
    exact (hy2 e he).symm
  have huC : u ∉ C := fun h => hunA (mem_inf.mp h).1
  have hcomm : ∀ x ∈ C, ∀ z ∈ zpowers u, x * z = z * x :=
    commute_symm (commute_zpowers_left (K := C) (fun z hz => huA z hz))
  have hDe : IsElemTwo (C ⊔ zpowers u) := hCe.sup (isElemTwo_zpowers hu2) hcomm
  have hD8 : 8 ≤ Nat.card ↥(C ⊔ zpowers u) := by
    have h := two_mul_card_le_of_not_mem (H := C) (K := C ⊔ zpowers u)
      le_sup_left (mem_sup_right (mem_zpowers u)) huC
    omega
  have hDle : C ⊔ zpowers u ≤ S ⊓ centralizer ({y} : Set G) := by
    refine le_inf ?_ ?_
    · exact sup_le (inf_le_left.trans hAS) (zpowers_le.mpr huS)
    · exact sup_le inf_le_right (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr huy))
  exact three_le_pRank_of_le hDe hD8 hDle

theorem three_le_pRank_inf_centralizer_of_involution {S A : Subgroup G} {y : G} (hAS : A ≤ S)
    (hA : IsElemTwo A) (hA8 : 8 ≤ Nat.card A) (hyA : y ∈ normalizer (A : Set G)) (hyS : y ∈ S)
    (hy2 : y * y = 1) :
    3 ≤ pRank 2 ↥(S ⊓ centralizer ({y} : Set G)) := by
  by_cases hy : y ∈ A
  · have hAle : A ≤ S ⊓ centralizer ({y} : Set G) := by
      refine le_inf hAS ?_
      intro e he
      rw [mem_centralizer_singleton_iff]
      exact hA.1 e he y hy
    exact three_le_pRank_of_le hA hA8 hAle
  · exact three_le_pRank_inf_centralizer_of_sq hAS hA hA8 hyA
      (fun e _ => by rw [hy2, one_mul, mul_one]) hyS hy2 rfl
      (fun e he => (mem_centralizer_singleton_iff.mp (mem_inf.mp he).2).symm) hy

theorem conj_mem_inf_of_sq_induction {S A K M : Subgroup G} (hS : IsPGroup 2 S) (hAS : A ≤ S)
    (hSA : S ≤ normalizer (A : Set G)) (hA : IsElemTwo A) (hA8 : 8 ≤ Nat.card A)
    (hMK : M ≤ normalizer (K : Set G)) (hKA : ∀ b ∈ S ⊓ K, ∀ e ∈ A, b * e = e * b)
    (hAK : A ⊓ K = ⊥)
    (hfus : ∀ x ∈ S, ∀ g : G, g⁻¹ * x * g ∈ S →
      3 ≤ pRank 2 ↥(S ⊓ centralizer ({x} : Set G)) →
      3 ≤ pRank 2 ↥(S ⊓ centralizer ({g⁻¹ * x * g} : Set G)) →
      ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m) :
    ∀ x ∈ S ⊓ K, ∀ g : G, g⁻¹ * x * g ∈ S → g⁻¹ * x * g ∈ S ⊓ K := by
  have key : ∀ n : ℕ, ∀ x : G, orderOf x = 2 ^ n → x ∈ S ⊓ K →
      ∀ g : G, g⁻¹ * x * g ∈ S → g⁻¹ * x * g ∈ K := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hxord hx g hyS
      have hrx : 3 ≤ pRank 2 ↥(S ⊓ centralizer ({x} : Set G)) := by
        refine three_le_pRank_of_le hA hA8 (le_inf hAS ?_)
        intro e he
        rw [mem_centralizer_singleton_iff]
        exact (hKA x hx e he).symm
      have step : 3 ≤ pRank 2 ↥(S ⊓ centralizer ({g⁻¹ * x * g} : Set G)) →
          g⁻¹ * x * g ∈ K := by
        intro hry
        obtain ⟨m, hm, hmy⟩ := hfus x hx.1 g hyS hrx hry
        rw [hmy]
        exact (mem_normalizer_iff''.mp (hMK hm) x).mp hx.2
      by_cases hn0 : n = 0
      · subst n
        have hx1 : x = 1 := orderOf_eq_one_iff.mp (by simpa using hxord)
        rw [hx1]
        simp
      by_cases hn1 : n = 1
      · have hx2 : x * x = 1 := by
          rw [← pow_two]
          rw [show (2 : ℕ) = 2 ^ n by rw [hn1]; norm_num, ← hxord]
          exact pow_orderOf_eq_one x
        have hy2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
          calc (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
            _ = 1 := by rw [hx2]; group
        exact step (three_le_pRank_inf_centralizer_of_involution hAS hA hA8
          (hSA hyS) hyS hy2)
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        have hyord : orderOf (g⁻¹ * x * g) = orderOf x := by
          have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
          rw [MulAut.conj_apply] at h
          simpa using h
        have hx2ord : orderOf (x ^ 2) = 2 ^ (k + 1) := by
          have hdvd : 2 ∣ orderOf x := by
            rw [hxord]
            exact dvd_pow_self 2 (by omega)
          rw [orderOf_pow_of_dvd (by norm_num) hdvd, hxord,
            Nat.pow_div (show 1 ≤ k + 2 by omega) (by norm_num),
            show k + 2 - 1 = k + 1 by omega]
        have hy2S : (g⁻¹ * x * g) * (g⁻¹ * x * g) ∈ S := by
          rw [← pow_two]
          exact pow_mem hyS 2
        have hy2K : (g⁻¹ * x * g) * (g⁻¹ * x * g) ∈ K := by
          have h := ih (k + 1) (by omega) (x ^ 2) hx2ord (pow_mem hx 2) g (by
            rw [show g⁻¹ * x ^ 2 * g = (g⁻¹ * x * g) * (g⁻¹ * x * g) by
              rw [pow_two]; group]
            exact hy2S)
          rwa [show g⁻¹ * x ^ 2 * g = (g⁻¹ * x * g) * (g⁻¹ * x * g) by
            rw [pow_two]; group] at h
        have hy2SK : (g⁻¹ * x * g) * (g⁻¹ * x * g) ∈ S ⊓ K := mem_inf.mpr ⟨hy2S, hy2K⟩
        set u : G := (g⁻¹ * x * g) ^ (2 ^ (k + 1)) with hudef
        have hu_eq : u = ((g⁻¹ * x * g) * (g⁻¹ * x * g)) ^ (2 ^ k) := by
          rw [hudef, show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ, Nat.mul_comm],
            pow_mul, pow_two]
        have huSK : u ∈ S ⊓ K := by
          rw [hu_eq]
          exact pow_mem hy2SK (2 ^ k)
        have hu2 : u * u = 1 := by
          rw [← pow_two, hudef, ← pow_mul,
            show 2 ^ (k + 1) * 2 = 2 ^ (k + 2) by rw [← pow_succ]]
          rw [show 2 ^ (k + 2) = orderOf (g⁻¹ * x * g) by rw [hyord, hxord]]
          exact pow_orderOf_eq_one _
        have hu1 : u ≠ 1 := by
          rw [hudef]
          exact pow_ne_one_of_lt_orderOf (x := g⁻¹ * x * g) (n := 2 ^ (k + 1))
            (by positivity)
            (by rw [hyord, hxord]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
        have huy : u * (g⁻¹ * x * g) = (g⁻¹ * x * g) * u := by
          rw [hudef]
          exact (Commute.pow_self (g⁻¹ * x * g) (2 ^ (k + 1))).eq
        have huA : ∀ e ∈ A ⊓ centralizer ({g⁻¹ * x * g} : Set G), u * e = e * u :=
          fun e he => hKA u huSK e (mem_inf.mp he).1
        have hunA : u ∉ A := by
          intro huA'
          have hu_bot : u ∈ A ⊓ K := mem_inf.mpr ⟨huA', (mem_inf.mp huSK).2⟩
          rw [hAK] at hu_bot
          exact hu1 (mem_bot.mp hu_bot)
        exact step (three_le_pRank_inf_centralizer_of_sq hAS hA hA8 (hSA hyS)
          (fun e he => hKA _ hy2SK e he) (mem_inf.mp huSK).1 hu2 huy huA hunA)
  intro x hx g hyS
  obtain ⟨k, hk⟩ := hS ⟨x, hx.1⟩
  have hxpow : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (orderOf_dvd_of_pow_eq_one hxpow)
  exact mem_inf.mpr ⟨hyS, key n x hn hx g hyS⟩

theorem conj_eq_of_threeConnected_in
    {A S : Subgroup G}
    (hB : ∀ E : Subgroup G, E ≤ S → IsElemTwo E → TwoBalancedWrt E)
    (hA : IsElemTwo A)
    (h16 : 16 ≤ Nat.card A) (hSyl : IsSylowTwoIn S (normalizer (wGroup A : Set G)))
    (h3 : IsThreeConnected S) :
    ∀ x ∈ S, ∀ g : G, g⁻¹ * x * g ∈ S →
      3 ≤ pRank 2 ↥(S ⊓ centralizer ({x} : Set G)) →
      3 ≤ pRank 2 ↥(S ⊓ centralizer ({g⁻¹ * x * g} : Set G)) →
      ∃ m ∈ normalizer (wGroup A : Set G), g⁻¹ * x * g = m⁻¹ * x * m := by
  obtain ⟨⟨T, hT⟩, hfus⟩ := sylow_and_fusion_of_threeConnected_in hB hA h16 hSyl h3
  intro x hx g hy hrx hry
  obtain ⟨c, hc⟩ := exists_extremal_conj ⟨T, hT⟩ hx
  obtain ⟨m₁, hm₁, h₁⟩ := hfus _ x hx hc ⟨c, rfl⟩ hrx
  obtain ⟨m₂, hm₂, h₂⟩ := hfus _ (g⁻¹ * x * g) hy hc ⟨g⁻¹ * c, by group⟩ hry
  refine ⟨m₁⁻¹ * m₂, mul_mem (inv_mem hm₁) hm₂, ?_⟩
  rw [h₂]
  conv_rhs => rw [h₁]
  group

theorem conj_eq_of_threeConnected (hB : GWTwoBalanced G) {A S : Subgroup G} (hA : IsElemTwo A)
    (h16 : 16 ≤ Nat.card A) (hSyl : IsSylowTwoIn S (normalizer (wGroup A : Set G)))
    (h3 : IsThreeConnected S) :
    ∀ x ∈ S, ∀ g : G, g⁻¹ * x * g ∈ S →
      3 ≤ pRank 2 ↥(S ⊓ centralizer ({x} : Set G)) →
      3 ≤ pRank 2 ↥(S ⊓ centralizer ({g⁻¹ * x * g} : Set G)) →
      ∃ m ∈ normalizer (wGroup A : Set G), g⁻¹ * x * g = m⁻¹ * x * m :=
  conj_eq_of_threeConnected_in
    (fun _ _ hE => twoBalancedWrt_of_gwTwoBalanced hB hE) hA h16 hSyl h3

theorem conj_mem_inf_of_threeConnected_in
    {A₁ S A K : Subgroup G}
    (hB : ∀ E : Subgroup G, E ≤ S → IsElemTwo E → TwoBalancedWrt E)
    (hA₁ : IsElemTwo A₁) (h16 : 16 ≤ Nat.card A₁)
    (hSyl : IsSylowTwoIn S (normalizer (wGroup A₁ : Set G))) (h3 : IsThreeConnected S)
    (hAS : A ≤ S) (hSA : S ≤ normalizer (A : Set G)) (hA : IsElemTwo A) (hA8 : 8 ≤ Nat.card A)
    (hMK : normalizer (wGroup A₁ : Set G) ≤ normalizer (K : Set G))
    (hKA : ∀ b ∈ S ⊓ K, ∀ e ∈ A, b * e = e * b) (hAK : A ⊓ K = ⊥) :
    ∀ x ∈ S ⊓ K, ∀ g : G, g⁻¹ * x * g ∈ S → g⁻¹ * x * g ∈ S ⊓ K := by
  have hS2 : IsPGroup 2 S := hSyl.isPGroup
  exact conj_mem_inf_of_sq_induction (M := normalizer (wGroup A₁ : Set G))
    hS2 hAS hSA hA hA8 hMK hKA hAK
    (conj_eq_of_threeConnected_in hB hA₁ h16 hSyl h3)

theorem conj_mem_inf_of_threeConnected (hB : GWTwoBalanced G) {A₁ S A K : Subgroup G}
    (hA₁ : IsElemTwo A₁) (h16 : 16 ≤ Nat.card A₁)
    (hSyl : IsSylowTwoIn S (normalizer (wGroup A₁ : Set G))) (h3 : IsThreeConnected S)
    (hAS : A ≤ S) (hSA : S ≤ normalizer (A : Set G)) (hA : IsElemTwo A) (hA8 : 8 ≤ Nat.card A)
    (hMK : normalizer (wGroup A₁ : Set G) ≤ normalizer (K : Set G))
    (hKA : ∀ b ∈ S ⊓ K, ∀ e ∈ A, b * e = e * b) (hAK : A ⊓ K = ⊥) :
    ∀ x ∈ S ⊓ K, ∀ g : G, g⁻¹ * x * g ∈ S → g⁻¹ * x * g ∈ S ⊓ K :=
  conj_mem_inf_of_threeConnected_in
    (fun _ _ hE => twoBalancedWrt_of_gwTwoBalanced hB hE)
    hA₁ h16 hSyl h3 hAS hSA hA hA8 hMK hKA hAK

private theorem le_of_perfect_le_sup {X : Type*} [Group X] {J C N : Subgroup X}
    (hJ : ⁅J, J⁆ = J) (hCN : C ≤ normalizer (N : Set X))
    (hC : Group.IsSolvable ↥C) (hJCN : J ≤ C ⊔ N) : J ≤ N := by
  by_contra hJN
  let _ : Group.IsSolvable ↥C := hC
  set M : Subgroup X := C ⊔ N with hM
  have hMN : M ≤ normalizer (N : Set X) := sup_le hCN le_normalizer
  have hNM : N ≤ M := le_sup_right
  have : (N.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  set π := QuotientGroup.mk' (N.subgroupOf M) with hπ
  have hsurj : Function.Surjective (π.comp (Subgroup.inclusion (le_sup_left : C ≤ M))) := by
    intro q
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf M) q
    have hm' := hm
    rw [hM, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right C N hCN] at hm'
    obtain ⟨c, hc, n, hn, rfl⟩ := hm'
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    show ((Subgroup.inclusion le_sup_left ⟨c, hc⟩ : M)⁻¹ * ⟨c * n, hm⟩ : M) ∈ N.subgroupOf M
    rw [Subgroup.mem_subgroupOf]
    simpa using hn
  have hsol : Group.IsSolvable (↥M ⧸ N.subgroupOf M) :=
    Group.isSolvable_of_surjective hsurj
  have hJM : J ≤ M := by
    rw [hM]
    exact hJCN
  set ψ := π.comp (Subgroup.inclusion hJM) with hψ
  have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
  have hperf : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hsolr : Group.IsSolvable ψ.range := inferInstance
  have hsub : Subsingleton ψ.range := by
    by_contra hn
    rw [not_subsingleton_iff_nontrivial] at hn
    have : Nontrivial ψ.range := hn
    exact Group.IsPerfect.not_isSolvable (G := ψ.range) hsolr
  have hJN' : J ≤ N := by
    intro x hx
    have h1 : ψ ⟨x, hx⟩ = 1 := by
      have := Subsingleton.elim (⟨ψ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : ψ.range) 1
      exact congrArg Subtype.val this
    rw [hψ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  exact hJN hJN'

private theorem isSylowTwoIn_of_not_dvd {X : Type*} [Group X] {P H : Subgroup X}
    (hPH : P ≤ H) (hP : IsPGroup 2 P) (h : ¬ 2 ∣ P.relIndex H) : IsSylowTwoIn P H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨hPH, (hP.of_equiv (subgroupOfEquivOfLe hPH).symm).toSylow h, rfl⟩

private theorem exists_conj_mem_of_isSylowTwoIn {X : Type*} [Group X] [Finite X]
    {S H : Subgroup X} (hS : IsSylowTwoIn S H) {x : X} (hxH : x ∈ H)
    (hx : IsPGroup 2 (zpowers x)) : ∃ g ∈ H, g⁻¹ * x * g ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, P, hP⟩ := hS
  have hx' : IsPGroup 2 (zpowers (⟨x, hxH⟩ : H)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(zpowers x))).mp hx
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, ← orderOf_coe, ← Nat.card_zpowers]
    exact hk
  obtain ⟨Q, hQ⟩ := hx'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
  refine ⟨(g⁻¹ : H), (g⁻¹ : H).2, ?_⟩
  have hmem : (⟨x, hxH⟩ : H) ∈ (Q : Subgroup H) := hQ (mem_zpowers _)
  have h1 : g * ⟨x, hxH⟩ * g⁻¹ ∈ (P : Subgroup H) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mpr ⟨_, hmem, rfl⟩
  rw [hP, Subgroup.mem_subgroupOf] at h1
  simpa [inv_inv] using h1

theorem le_oddIn_of_stronglyClosed_inf (hGold : GoldschmidtStronglyClosedInput)
    (hG : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a)
    {M H K S P : Subgroup G} (hS : ∃ T : Sylow 2 G, (T : Subgroup G) = S) (hSM : S ≤ M)
    (hHM : H ≤ M) (hKM : K ≤ M) (hMH : M ≤ normalizer (H : Set G))
    (hMK : M ≤ normalizer (K : Set G)) (hNH : oddIn M ≤ H) (hHK : ⁅H, K⁆ ≤ oddIn M)
    (hPH : P ≤ H) (hPperf : ⁅P, P⁆ = P) (hPeven : Even (Nat.card P))
    (hcl : ∀ x ∈ S ⊓ K, ∀ g : G, g⁻¹ * x * g ∈ S → g⁻¹ * x * g ∈ S ⊓ K) :
    K ≤ oddIn M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hS
  have hS2 : IsPGroup 2 S := hT ▸ T.isPGroup'
  have hMnormN : M ≤ normalizer (oddIn M : Set G) := by
    have h :=
      CFSG.ComponentClassification.UnbalancedGS.normalizer_le_normalizer_map_of_characteristic
        M (pPrimeCore 2 M)
    simpa [oddIn] using le_normalizer.trans h
  have hNodd : Odd (Nat.card (oddIn M)) := by
    rw [oddIn, Subgroup.card_map_of_injective M.subtype_injective]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := M))
  have hNO : oddIn M ≤ FooteLit.oddCoreIn H :=
    FooteLit.le_oddCoreIn hNH (hHM.trans hMnormN) hNodd
  have hOHM : FooteLit.oddCoreIn H ≤ M :=
    (map_subtype_le (pPrimeCore 2 H)).trans hHM
  have hMnormOH : M ≤ normalizer (FooteLit.oddCoreIn H : Set G) := by
    have h :=
      CFSG.ComponentClassification.UnbalancedGS.normalizer_le_normalizer_map_of_characteristic
        H (pPrimeCore 2 H)
    exact hMH.trans (by simpa [FooteLit.oddCoreIn] using h)
  have hOodd : Odd (Nat.card (FooteLit.oddCoreIn H)) := FooteLit.odd_card_oddCoreIn H
  have hON : FooteLit.oddCoreIn H ≤ oddIn M := by
    have h := FooteLit.le_oddCoreIn hOHM hMnormOH hOodd
    simpa [FooteLit.oddCoreIn, oddIn] using h
  have hHeq : oddIn M = FooteLit.oddCoreIn H := le_antisymm hNO hON
  let B : Subgroup G := S ⊓ K
  have hB2 : IsPGroup 2 B := hS2.to_le inf_le_left
  have hBcore : B ≤ CFSG.ComponentClassification.UnbalancedLayer.coreActionKernel H := by
    intro b hb
    obtain ⟨hbS, hbK⟩ := mem_inf.mp hb
    refine CFSG.ComponentClassification.UnbalancedLayer.mem_coreActionKernel.mpr
      ⟨hMH (hKM hbK), ?_⟩
    intro j hj
    have hcomm : j⁻¹ * b⁻¹ * j * b ∈ ⁅H, K⁆ := by
      have hc := Subgroup.commutator_mem_commutator (H₁ := H) (H₂ := K)
        (inv_mem hj) (inv_mem hbK)
      rwa [commutatorElement_def, inv_inv, inv_inv] at hc
    exact hNO (hHK hcomm)
  have hBbot : B = ⊥ := by
    by_contra hBne
    have htopF : GeneralizedFitting.subgroup G = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
    let eF : GeneralizedFitting.subgroup G ≃* G :=
      (MulEquiv.subgroupCongr htopF).trans topEquiv
    have hsF : IsSimpleGroup (GeneralizedFitting.subgroup G) := eF.isSimpleGroup
    have hnF : ∃ u v : GeneralizedFitting.subgroup G, u * v ≠ v * u := by
      obtain ⟨u, v, huv⟩ := hna
      exact ⟨eF.symm u, eF.symm v, fun huv' =>
        huv (eF.symm.injective (by rw [map_mul, map_mul, huv']))⟩
    have hBT : B ≤ (T : Subgroup G) := by
      rw [hT]
      exact inf_le_left
    have hclosed : ∀ a ∈ B, ∀ g : G,
        g⁻¹ * a * g ∈ (T : Subgroup G) → g⁻¹ * a * g ∈ B := by
      intro a ha g hg
      exact hcl a ha g (by rwa [hT] at hg)
    have hsolvCB : Group.IsSolvable ↥(centralizer (B : Set G)) :=
      hGold G hsF hnF T B hBT hBne hclosed
    let C : Subgroup G := H ⊓ centralizer (B : Set G)
    have hCsolv : Group.IsSolvable ↥C := by
      have : Group.IsSolvable ↥(centralizer (B : Set G)) := hsolvCB
      exact Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (inf_le_right : C ≤ centralizer (B : Set G)))
    have hHle : H ≤ C ⊔ FooteLit.oddCoreIn H := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ :=
        FooteLit.exists_mem_centralizer_of_le_coreActionKernel hB2 hBcore hx
      have hxy : x = y * (y⁻¹ * x) := by group
      rw [hxy]
      exact mul_mem (mem_sup_left (show y ∈ C from mem_inf.mpr ⟨hy.1, hy.2⟩))
        (mem_sup_right hyx)
    have hHleN : H ≤ C ⊔ oddIn M := by
      rw [hHeq]
      exact hHle
    have hPCN : P ≤ C ⊔ oddIn M := hPH.trans hHleN
    have hCN : C ≤ normalizer (oddIn M : Set G) :=
      inf_le_left.trans (hHM.trans hMnormN)
    have hPN : P ≤ oddIn M :=
      le_of_perfect_le_sup hPperf hCN hCsolv hPCN
    have hPodd : Odd (Nat.card P) :=
      Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hPN)
    exact (Nat.not_even_iff_odd.mpr hPodd) hPeven
  have hKodd : Odd (Nat.card K) := by
    rw [← Nat.not_even_iff_odd]
    intro hKeven
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := K) 2
      (even_iff_two_dvd.mp hKeven)
    have hxne : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hxord
      omega
    have hx2 : x * x = 1 := by
      rw [← pow_two, ← hxord]
      exact pow_orderOf_eq_one x
    let k : G := x
    have hkK : k ∈ K := x.2
    have hkM : k ∈ M := hKM hkK
    have hkne : k ≠ 1 := by
      intro h
      exact hxne (Subtype.ext h)
    have hkord : orderOf k = 2 := by
      rw [show k = (x : G) from rfl, orderOf_coe, hxord]
    have hkp : IsPGroup 2 (zpowers k) :=
      IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, hkord]; norm_num)
    have hSM' : IsSylowTwoIn S M := by
      refine isSylowTwoIn_of_not_dvd hSM hS2 ?_
      intro h2
      have hdvd : 2 ∣ S.index := h2.trans (Subgroup.relIndex_dvd_index_of_le hSM)
      exact T.not_dvd_index (by rwa [← hT] at hdvd)
    obtain ⟨m, hmM, hmS⟩ := exists_conj_mem_of_isSylowTwoIn hSM' hkM hkp
    have hmK : m⁻¹ * k * m ∈ K := by
      have h := (Subgroup.mem_normalizer_iff.mp (hMK (inv_mem hmM)) k).mp hkK
      simpa [inv_inv] using h
    have hbot : m⁻¹ * k * m ∈ (⊥ : Subgroup G) := by
      rw [← hBbot]
      exact mem_inf.mpr ⟨hmS, hmK⟩
    have hk1 : k = 1 := by
      have h1 : m⁻¹ * k * m = 1 := by simpa using hbot
      calc k = m * (m⁻¹ * k * m) * m⁻¹ := by group
        _ = 1 := by rw [h1]; group
    exact hkne hk1
  have hKnorm : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK
  have hKcop : Nat.Coprime 2 (Nat.card (K.subgroupOf M)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv]
    exact Nat.coprime_two_left.mpr hKodd
  have hKcore : K.subgroupOf M ≤ pPrimeCore 2 M :=
    CFSG.le_pPrimeCore_of_normal_coprime hKnorm hKcop
  intro x hx
  have hxmap : x ∈ (K.subgroupOf M).map M.subtype := by
    rw [Subgroup.map_subgroupOf_eq_of_le hKM]
    exact hx
  exact Subgroup.map_mono hKcore hxmap

end CFSG.ComponentClassification.GrSLit.L34Sec5S
