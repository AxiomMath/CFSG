module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.MaximalCatalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerE1Weak

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open scoped commutatorElement
open Subgroup CFSG.LocalCores

theorem c3_three_mul_card_dvd {H : Type} [Group H] [Finite H] (N : Subgroup H) (y : H)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hc : ∀ n ∈ N, y * n = n * y) (hn : y ∉ N) :
    3 * Nat.card N ∣ Nat.card H := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hY : Nat.card (zpowers y) = 3 := by rw [Nat.card_zpowers, hord]
  let f : N × zpowers y →* H :=
    MonoidHom.noncommCoprod N.subtype (zpowers y).subtype (fun n t => by
      obtain ⟨k, hk⟩ := t.2
      have hk' : y ^ k = (t : H) := hk
      show (n : H) * t = t * n
      rw [← hk']
      have h : Commute y (n : H) := hc n n.2
      exact ((Commute.zpow_left h k).symm).eq)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨n, t⟩ h
    have h' : (n : H) * (t : H) = 1 := by simpa [f] using h
    have htn : (t : H) ∈ N := by
      have : (t : H) = (n : H)⁻¹ := eq_inv_of_mul_eq_one_right h'
      rw [this]; exact N.inv_mem n.2
    have ht1 : (t : H) = 1 := by
      obtain ⟨k, hk0⟩ := t.2
      have hk : y ^ k = (t : H) := hk0
      have hk3 : y ^ k = y ^ (k % 3) := by
        have := zpow_mod_orderOf y k
        rw [hord] at this
        simpa using this.symm
      rw [← hk, hk3] at htn ⊢
      have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases this with h0 | h1 | h2
      · rw [h0]; simp
      · rw [h1] at htn; simp at htn; exact absurd htn hn
      · rw [h2] at htn
        simp only [zpow_ofNat] at htn
        exfalso; apply hn
        have : y = (y ^ 2) ^ 2 := by
          rw [show (y ^ 2) ^ 2 = y ^ 3 * y by group, hy3, one_mul]
        rw [this]; exact N.pow_mem htn 2
    have hn1 : (n : H) = 1 := by rw [ht1, mul_one] at h'; exact h'
    exact Prod.ext (Subtype.ext hn1) (Subtype.ext ht1)
  have := Subgroup.card_dvd_of_injective f hinj
  rwa [Nat.card_prod, hY, mul_comm] at this

section Core

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem c3_center_trivial {M : Type} [Group M] (hMs : IsSimpleGroup M)
    (hMna : ∃ a b : M, a * b ≠ b * a) (m : M) (hm : ∀ m' : M, m' * m = m * m') : m = 1 := by
  have hn : (center M).Normal := inferInstance
  rcases hMs.eq_bot_or_eq_top_of_normal (center M) with h | h
  · have : m ∈ center M := mem_center_iff.2 fun g => hm g
    rwa [h, mem_bot] at this
  · exfalso
    obtain ⟨a, b, hab⟩ := hMna
    exact hab ((mem_center_iff.1 (h ▸ mem_top b)) a)

theorem c3_main (M X : Subgroup Γ) (hMs : IsSimpleGroup ↥M) (hMna : ∃ a b : ↥M, a * b ≠ b * a)
    (hM3 : 2 ≤ (Nat.card M).factorization 3)
    (hXc : ∀ x ∈ X, ∀ m ∈ M, x * m = m * x) (hX9 : 9 ∣ Nat.card X) (hX3 : ∀ x ∈ X, x ^ 3 = 1)
    (hΓ : (Nat.card Γ).factorization 3 ≤ 4) (hML : M ≤ CFSG.layer Γ) :
    ∃ K : Subgroup Γ, CFSG.IsComponent K ∧ M ≤ K := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set L := CFSG.layer Γ with hL
  have hLchar : L.Characteristic := layer_characteristic
  have hLn : L.Normal := inferInstance
  let e := layerCentralQuotientEquiv Γ
  let F : ↥L →* (∀ K : ComponentIndex Γ, ↥K.1 ⧸ center ↥K.1) :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' (center ↥L))
  have hF1 : ∀ a : ↥L, F a = 1 ↔ a ∈ center ↥L := by
    intro a
    simp only [F, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ e.symm.injective, QuotientGroup.eq_one_iff]
  let incl : ↥M →* ↥L := Subgroup.inclusion hML
  let φ : ∀ K : ComponentIndex Γ, ↥M →* (↥K.1 ⧸ center ↥K.1) :=
    fun K => (Pi.evalMonoidHom _ K).comp (F.comp incl)
  have hdich : ∀ K, Function.Injective (φ K) ∨ ∀ m, φ K m = 1 := by
    intro K
    rcases hMs.eq_bot_or_eq_top_of_normal (φ K).ker with h | h
    · exact Or.inl ((MonoidHom.ker_eq_bot_iff _).1 h)
    · exact Or.inr fun m => MonoidHom.mem_ker.1 (h ▸ mem_top m)
  let v : ComponentIndex Γ → ℕ := fun K => (Nat.card (↥K.1 ⧸ center ↥K.1)).factorization 3
  have hsumL : ∑ K, v K + (Nat.card (center ↥L)).factorization 3 =
      (Nat.card ↥L).factorization 3 := by
    have h1 : Nat.card ↥L = Nat.card (↥L ⧸ center ↥L) * Nat.card (center ↥L) :=
      card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card (↥L ⧸ center ↥L) =
        ∏ K : ComponentIndex Γ, Nat.card (↥K.1 ⧸ center ↥K.1) := by
      rw [← Nat.card_pi]; exact (Nat.card_congr e.toEquiv).symm
    rw [h1, h2, Nat.factorization_mul (Finset.prod_ne_zero_iff.2 fun K _ => Nat.card_pos.ne')
      Nat.card_pos.ne', Finsupp.add_apply, Nat.factorization_prod (fun K _ => Nat.card_pos.ne'),
      Finsupp.finsetSum_apply]
  have hLΓ : (Nat.card ↥L).factorization 3 ≤ 4 :=
    (factorization_le_of_dvd' Nat.card_pos.ne' (Subgroup.card_subgroup_dvd_card L)).trans hΓ
  have hex : ∃ K, Function.Injective (φ K) := by
    by_contra hno
    push Not at hno
    obtain ⟨a, b, hab⟩ := hMna
    apply hab
    have hcen : ∀ m : ↥M, incl m ∈ center ↥L := by
      intro m
      rw [← hF1]
      funext K
      rcases hdich K with h | h
      · exact absurd h (hno K)
      · exact h m
    have := mem_center_iff.1 (hcen b) (incl a)
    exact Subtype.ext (by simpa [incl] using congrArg Subtype.val this)
  have htwo : ∀ K₁ K₂ : ComponentIndex Γ, Function.Injective (φ K₁) →
      Function.Injective (φ K₂) → K₁ = K₂ := by
    intro K₁ K₂ h₁ h₂
    by_contra hne
    have hvK : ∀ K, Function.Injective (φ K) → 2 ≤ v K := by
      intro K hK
      have hd : Nat.card M ∣ Nat.card (↥K.1 ⧸ center ↥K.1) :=
        Subgroup.card_dvd_of_injective _ hK
      exact hM3.trans (factorization_le_of_dvd' Nat.card_pos.ne' hd)
    have hpair : v K₁ + v K₂ ≤ ∑ K, v K := by
      have := Finset.sum_le_sum_of_subset (f := v) (Finset.subset_univ {K₁, K₂})
      rwa [Finset.sum_pair hne] at this
    have htriple : ∀ K, K ≠ K₁ → K ≠ K₂ → v K₁ + v K₂ + v K ≤ ∑ K, v K := by
      intro K h1 h2
      have := Finset.sum_le_sum_of_subset (f := v) (Finset.subset_univ {K, K₁, K₂})
      rw [Finset.sum_insert (by simp [h1, h2]), Finset.sum_pair hne] at this
      omega
    have hv1 := hvK K₁ h₁
    have hv2 := hvK K₂ h₂
    have hzero : ∀ K, K ≠ K₁ → K ≠ K₂ → v K = 0 := fun K h1 h2 => by
      have := htriple K h1 h2
      omega
    have hZ0 : (Nat.card (center ↥L)).factorization 3 = 0 := by omega
    have hsum4 : ∑ K, v K = 4 := by omega
    have hvK12 : v K₁ = 2 ∧ v K₂ = 2 := by omega
    have hidx : (L.index).factorization 3 = 0 := by
      have h1 : Nat.card ↥L * L.index = Nat.card Γ := Subgroup.card_mul_index L
      have h2 : (Nat.card ↥L * L.index).factorization 3 = (Nat.card Γ).factorization 3 := by
        rw [h1]
      rw [Nat.factorization_mul Nat.card_pos.ne' (Subgroup.index_ne_zero_of_finite), Finsupp.add_apply] at h2
      omega
    have hXL : ∀ x ∈ X, x ∈ L := by
      intro x hx
      by_contra hxL
      have hq3 : ((x : Γ ⧸ L)) ^ 3 = 1 := by rw [← QuotientGroup.mk_pow, hX3 x hx]; rfl
      have hq1 : ((x : Γ ⧸ L)) ≠ 1 := fun h => hxL (QuotientGroup.eq_one_iff x |>.1 h)
      have hord : orderOf ((x : Γ ⧸ L)) = 3 := orderOf_eq_prime hq3 hq1
      have hdvd : 3 ∣ L.index := by
        rw [Subgroup.index_eq_card, ← hord]
        exact _root_.orderOf_dvd_natCard _
      have := (Nat.Prime.dvd_iff_one_le_factorization (by norm_num : Nat.Prime 3)
        Subgroup.index_ne_zero_of_finite).1 hdvd
      omega
    have hXZ : ∀ x (hx : x ∈ X), (⟨x, hXL x hx⟩ : ↥L) ∈ center ↥L := by
      intro x hx
      rw [← hF1]
      set xL : ↥L := ⟨x, hXL x hx⟩ with hxL
      funext K
      have hc3 : (F xL K) ^ 3 = 1 := by
        have : F (xL ^ 3) = 1 := by
          have : xL ^ 3 = 1 := Subtype.ext (hX3 x hx)
          rw [this, map_one]
        have h' := congrFun (show F xL ^ 3 = 1 by rw [← map_pow]; exact this) K
        simpa using h'
      have hcomm : ∀ m : ↥M, F xL K * φ K m = φ K m * F xL K := by
        intro m
        have : xL * incl m = incl m * xL := Subtype.ext (hXc x hx m m.2)
        have h' := congrFun (show F xL * F (incl m) = F (incl m) * F xL by
          rw [← map_mul, ← map_mul, this]) K
        exact h'
      by_cases hK : K = K₁ ∨ K = K₂
      · have hinj : Function.Injective (φ K) := by rcases hK with rfl | rfl <;> assumption
        by_contra hc1
        have hnot : F xL K ∉ (φ K).range := by
          rintro ⟨m₀, hm₀⟩
          apply hc1
          rw [← hm₀]
          have : m₀ = 1 := c3_center_trivial hMs hMna m₀ fun m' => by
            apply hinj
            rw [map_mul, map_mul, hm₀]
            exact (hcomm m').symm
          rw [this, map_one]; rfl
        have hdvd := c3_three_mul_card_dvd (φ K).range (F xL K) hc3 hc1
          (fun n hn => by obtain ⟨m, rfl⟩ := hn; exact hcomm m) hnot
        have hcr : Nat.card (φ K).range = Nat.card M :=
          Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
        rw [hcr] at hdvd
        have h6 := factorization_le_of_dvd' (p := 3) (Nat.card_pos.ne') hdvd
        rw [Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply] at h6
        have h7 : (3 : ℕ).factorization 3 = 1 := by
          rw [Nat.Prime.factorization_self (by norm_num)]
        have h8 : v K = 2 := by rcases hK with rfl | rfl <;> omega
        change _ ≤ v K at h6
        omega
      · push Not at hK
        have hv0 := hzero K hK.1 hK.2
        by_contra hc1
        have hord : orderOf (F xL K) = 3 := orderOf_eq_prime hc3 hc1
        have hdvd : 3 ∣ Nat.card (↥K.1 ⧸ center ↥K.1) := hord ▸ _root_.orderOf_dvd_natCard _
        have := (Nat.Prime.dvd_iff_one_le_factorization (by norm_num : Nat.Prime 3)
          Nat.card_pos.ne').1 hdvd
        change 1 ≤ v K at this
        omega
    have hXle : X ≤ L := fun x hx => hXL x hx
    let ι : ↥X →* ↥(center ↥L) :=
      (Subgroup.inclusion hXle).codRestrict (center ↥L) (fun x => hXZ x x.2)
    have hι : Function.Injective ι := by
      intro a b h
      have := congrArg (fun y : ↥(center ↥L) => ((y : ↥L) : Γ)) h
      exact Subtype.ext this
    have hd9 : 9 ∣ Nat.card (center ↥L) := hX9.trans (Subgroup.card_dvd_of_injective ι hι)
    have := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 3)
      (Nat.card_pos.ne' : Nat.card (center ↥L) ≠ 0) (k := 2)).1 (by simpa using hd9)
    omega
  obtain ⟨K₀, hK₀⟩ := hex
  refine ⟨K₀.1, K₀.2, ?_⟩
  have hothers : ∀ K, K ≠ K₀ → ∀ m, φ K m = 1 := fun K hK =>
    (hdich K).resolve_left (fun h => hK (htwo K K₀ h hK₀))
  have hdec : ∀ m : ↥M, ∃ k : ↥K₀.1, ∃ z ∈ center ↥L,
      incl m = z * (⟨k, component_le_layer K₀.2 k.2⟩ : ↥L) := by
    intro m
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (φ K₀ m)
    have hFm : F (incl m) = Pi.mulSingle K₀ (k : ↥K₀.1 ⧸ center ↥K₀.1) := by
      funext K
      by_cases hKK : K = K₀
      · subst hKK
        rw [Pi.mulSingle_eq_same]
        exact hk.symm
      · rw [Pi.mulSingle_eq_of_ne hKK]
        exact hothers K hKK m
    have h2 : e (F (incl m)) = ((incl m : ↥L) : ↥L ⧸ center ↥L) := by
      simp [F, e]
    rw [hFm, layerCentralQuotientEquiv_mulSingle] at h2
    have h3 := QuotientGroup.eq.1 h2
    refine ⟨k, _, h3, ?_⟩
    have hw := mem_center_iff.1 h3 (⟨k, component_le_layer K₀.2 k.2⟩ : ↥L)
    rw [← hw]; group
  have hperf : commutator ↥M = ⊤ := by
    rcases hMs.eq_bot_or_eq_top_of_normal (commutator ↥M) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hMna
      apply hab
      have : ⁅a, b⁆ ∈ commutator ↥M := by
        rw [_root_.commutator_def]; exact commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h
  have hcomm : commutator ↥M ≤ K₀.1.comap M.subtype := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨k1, z1, hz1, h1⟩ := hdec a
    obtain ⟨k2, z2, hz2, h2⟩ := hdec b
    have h4 : ⁅incl a, incl b⁆ =
        ⁅(⟨k1, component_le_layer K₀.2 k1.2⟩ : ↥L), (⟨k2, component_le_layer K₀.2 k2.2⟩ : ↥L)⁆ := by
      rw [h1, h2]; exact commutatorElement_mul_central_of_mem hz1 hz2 _ _
    have h5 := congrArg (fun y : ↥L => (y : Γ)) h4
    have hk : ((⁅k1, k2⁆ : ↥K₀.1) : Γ) ∈ K₀.1 := (⁅k1, k2⁆ : ↥K₀.1).2
    show ((⁅a, b⁆ : ↥M) : Γ) ∈ K₀.1
    simp only [incl, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inclusion] at h5 hk ⊢
    rw [h5]
    exact hk
  intro m hm
  exact hcomm (hperf ▸ mem_top (⟨m, hm⟩ : ↥M))

end Core

section Assembly

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.Solomon78

theorem c3_nonabelian_of_simple {H : Type} [Group H] [Finite H] (hs : IsSimpleGroup H)
    (hc : ¬ (Nat.card H).Prime) : ∃ a b : H, a * b ≠ b * a := by
  by_contra hno
  push Not at hno
  let _ : CommGroup H := { ‹Group H› with mul_comm := fun a b => hno a b }
  exact hc IsSimpleGroup.prime_card

theorem c3_layerIn_le {G : Type} [Group G] (U : Subgroup G) :
    layerIn U ≤ (CFSG.layer ↥U).map U.subtype := by
  refine sSup_le fun M hM => ?_
  have hM' : IsCompIn M U := hM
  rw [← Subgroup.map_subgroupOf_eq_of_le hM'.1]
  exact Subgroup.map_mono (CFSG.LocalCores.component_le_layer hM'.2)

theorem c3_subgroupOf_le_layer {G : Type} [Group G] {U A : Subgroup G} (hA : A ≤ layerIn U) :
    A.subgroupOf U ≤ CFSG.layer ↥U := by
  intro a ha
  have h1 : (a : G) ∈ (CFSG.layer ↥U).map U.subtype :=
    c3_layerIn_le U (hA (Subgroup.mem_subgroupOf.1 ha))
  obtain ⟨y, hy, hya⟩ := h1
  have : y = a := Subtype.ext hya
  rwa [← this]

theorem c3_centralizer_sup {G : Type} [Group G] (u u₁ : G) :
    centralizer ((zpowers u ⊔ zpowers u₁ : Subgroup G) : Set G) =
      centralizer ({u} : Set G) ⊓ centralizer ({u₁} : Set G) := by
  refine le_antisymm (le_inf (Subgroup.centralizer_le ?_) (Subgroup.centralizer_le ?_)) ?_
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (le_sup_left : zpowers x ≤ _) (mem_zpowers x)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (le_sup_right : zpowers x ≤ zpowers u ⊔ zpowers x) (mem_zpowers x)
  · rintro g ⟨hg1, hg2⟩
    have hle : (zpowers u ⊔ zpowers u₁ : Subgroup G) ≤ centralizer ({g} : Set G) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_singleton_iff.1 hg1).symm
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_singleton_iff.1 hg2).symm
    rw [mem_centralizer_iff]
    intro h hh
    exact mem_centralizer_singleton_iff.1 (hle hh)

theorem c3_centralizer_zpowers {G : Type} [Group G] (u : G) :
    centralizer ((zpowers u : Subgroup G) : Set G) = centralizer ({u} : Set G) := by
  refine le_antisymm (Subgroup.centralizer_le ?_) (fun g hg => ?_)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact mem_zpowers x
  · rw [mem_centralizer_singleton_iff] at hg
    rw [mem_centralizer_iff]
    rintro h ⟨k, rfl⟩
    exact ((Commute.zpow_left (show Commute u g from hg.symm) k)).eq

theorem c3_isPGroup_klein {G : Type} [Group G] [Finite G] (u u₁ : G) (hu : orderOf u = 2)
    (hu₁ : orderOf u₁ = 2) (hcomm : u * u₁ = u₁ * u) :
    IsPGroup 2 ↥(zpowers u ⊔ zpowers u₁) := by
  have hT : IsPGroup 2 ↥(zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; norm_num)
  have hN : u₁ ∈ normalizer ((zpowers u : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _
      (show u₁ ∈ centralizer ((zpowers u : Subgroup G) : Set G) from ?_)
    rw [mem_centralizer_iff]
    rintro h ⟨k, rfl⟩
    exact ((Commute.zpow_left (show Commute u u₁ from hcomm) k)).eq
  have hs2 : u₁ ^ 2 ∈ zpowers u := by
    have : u₁ ^ 2 = 1 := by rw [← hu₁]; exact pow_orderOf_eq_one u₁
    rw [this]; exact one_mem _
  exact isPGroup_sup_zpowers hT hN hs2

theorem c3_isPGroup_zpowers {G : Type} [Group G] (u : G) (hu : orderOf u = 2) :
    IsPGroup 2 ↥(zpowers u) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; norm_num)

theorem isCompIn_of_balance {G : Type} [Group G] [Finite G]
    (h15 : FS79Lemma15Sec G) (hO : CFSG.oddCore G = ⊥)
    (hKG : KGHS3) (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (h3 : (Nat.card G).factorization 3 ≤ 4)
    (u u₁ : G) (hu : orderOf u = 2) (hu₁ : orderOf u₁ = 2) (hcomm : u * u₁ = u₁ * u)
    (_hne : u ≠ u₁) (hU : centralizer ({u₁} : Set G) ≠ ⊤)
    (A : Subgroup G) (hA : Nonempty (↥A ≃* alternatingGroup (Fin 6)))
    (hAF : A ≤ centralizer ({u} : Set G) ⊓ centralizer ({u₁} : Set G))
    (hAn : ∀ g ∈ centralizer ({u} : Set G) ⊓ centralizer ({u₁} : Set G),
      g ∈ normalizer (A : Set G))
    (X : Subgroup G) (hX9 : Nat.card X = 9) (hX3 : ∀ a ∈ X, a ^ 3 = 1)
    (_hXA : ∀ a ∈ X, ∀ b ∈ A, a * b = b * a) (_hXu : ∀ a ∈ X, a * u = u * a)
    (hXu₁ : ∀ a ∈ X, a * u₁ = u₁ * a)
    (M : Subgroup G) (hM : IsSporadic ↥M .HS) (hMJ : M ≤ centralizer (X : Set G) ⊓ centralizer ({u₁} : Set G))
    (_hperf : ∀ H : Subgroup G, H ≤ centralizer (X : Set G) ⊓ centralizer ({u₁} : Set G) →
      ⁅H, H⁆ = H → H ≤ M)
    (hAM : A ≤ M) :
    IsCompIn M (centralizer ({u₁} : Set G)) := by
  classical
  set U := centralizer ({u₁} : Set G) with hUdef
  have hMU : M ≤ U := fun m hm => (hMJ hm).2
  have hXU : X ≤ U := fun x hx => mem_centralizer_singleton_iff.2 (hXu₁ x hx)
  have hAU : A ≤ U := fun a ha => (hAF ha).2
  obtain ⟨eA⟩ := hA
  have hA6 : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hA6na : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
    refine c3_nonabelian_of_simple hA6 ?_
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
    norm_num
  have hAq : CFSG.IsQuasisimple ↥A := by
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv eA.symm ?_
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hA6na).1
  set F : Subgroup G := zpowers u ⊔ zpowers u₁ with hFdef
  have hCF : centralizer (F : Set G) = centralizer {u} ⊓ centralizer {u₁} :=
    c3_centralizer_sup u u₁
  have hAcomp : IsCompIn A (centralizer (F : Set G)) := by
    rw [hCF]
    exact isCompIn_of_normal hAF hAq (normal_subgroupOf_of_le_normalizer hAn)
  have hF2 : IsPGroup 2 ↥F := c3_isPGroup_klein u u₁ hu hu₁ hcomm
  have hT2 : IsPGroup 2 ↥(zpowers u₁) := c3_isPGroup_zpowers u₁ hu₁
  have hTF : zpowers u₁ ≤ F := le_sup_right
  have hlay : layerIn (centralizer (F : Set G)) ≤ layerIn U := by
    obtain ⟨hF1, hF2'⟩ := h15.at hKP F hF2
    obtain ⟨-, hT2'⟩ := h15.at hKP (zpowers u₁) hT2
    have e1 := hF2' hO
    have e2 := hT2' hO
    have e3 := hF1 (zpowers u₁) hTF
    rw [c3_centralizer_zpowers] at e2 e3
    rw [← e1, ← e2]
    exact e3
  have hAlayer : A ≤ layerIn U := le_trans (le_sSup hAcomp) hlay
  obtain ⟨eM⟩ := hM
  have hHSs : IsSimpleGroup NativeSporadic.HS := CFSG.Sporadic.HS.isSimpleGroup_HS
  have hMs : IsSimpleGroup ↥M := (MulEquiv.isSimpleGroup_congr eM).2 hHSs
  have hMcard : Nat.card ↥M = 44352000 := by
    rw [Nat.card_congr eM.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  have hMna : ∃ a b : ↥M, a * b ≠ b * a :=
    c3_nonabelian_of_simple hMs (by rw [hMcard]; norm_num)
  have hM3 : 2 ≤ (Nat.card M).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 3) Nat.card_pos.ne').1
      (by rw [hMcard]; norm_num : 3 ^ 2 ∣ Nat.card M)
  have hMq : CFSG.IsQuasisimple ↥M ∧ center ↥M = ⊥ :=
    have := hMs
    CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hMna
  have eMU : ↥(M.subgroupOf U) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMU
  have hM's : IsSimpleGroup ↥(M.subgroupOf U) := (MulEquiv.isSimpleGroup_congr eMU).2 hMs
  have hM'na : ∃ a b : ↥(M.subgroupOf U), a * b ≠ b * a :=
    c3_nonabelian_of_simple hM's (by rw [Nat.card_congr eMU.toEquiv, hMcard]; norm_num)
  have hM'L : M.subgroupOf U ≤ CFSG.layer ↥U := by
    have hch : (CFSG.layer ↥U).Characteristic := CFSG.LocalCores.layer_characteristic
    have hn : ((CFSG.layer ↥U).subgroupOf (M.subgroupOf U)).Normal := inferInstance
    rcases hM's.eq_bot_or_eq_top_of_normal ((CFSG.layer ↥U).subgroupOf (M.subgroupOf U)) with h | h
    · exfalso
      have := CFSG.LocalCores.isQuasisimple_nontrivial hAq
      obtain ⟨a, ha1⟩ := exists_ne (1 : ↥A)
      have haU : (⟨(a : G), hAU a.2⟩ : ↥U) ∈ M.subgroupOf U :=
        Subgroup.mem_subgroupOf.2 (hAM a.2)
      have hmem : (⟨⟨(a : G), hAU a.2⟩, haU⟩ : ↥(M.subgroupOf U)) ∈
          (CFSG.layer ↥U).subgroupOf (M.subgroupOf U) :=
        Subgroup.mem_subgroupOf.2
          (c3_subgroupOf_le_layer hAlayer (Subgroup.mem_subgroupOf.2 a.2))
      rw [h, Subgroup.mem_bot] at hmem
      apply ha1
      have := congrArg (fun y : ↥(M.subgroupOf U) => ((y : ↥U) : G)) hmem
      exact Subtype.ext this
    · rw [Subgroup.subgroupOf_eq_top] at h
      exact h
  have hXU' : ∀ x ∈ X.subgroupOf U, ∀ m ∈ M.subgroupOf U, x * m = m * x := by
    intro x hx m hm
    apply Subtype.ext
    exact (mem_centralizer_iff.1 (hMJ (Subgroup.mem_subgroupOf.1 hm)).1) _
      (Subgroup.mem_subgroupOf.1 hx)
  have hΓ : (Nat.card ↥U).factorization 3 ≤ 4 :=
    (factorization_le_of_dvd' Nat.card_pos.ne' (Subgroup.card_subgroup_dvd_card U)).trans h3
  obtain ⟨K, hK, hMK⟩ := c3_main (M.subgroupOf U) (X.subgroupOf U) hM's hM'na
    (by rw [Nat.card_congr eMU.toEquiv]; exact hM3) hXU'
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXU).toEquiv, hX9])
    (fun x hx => Subtype.ext (hX3 x (Subgroup.mem_subgroupOf.1 hx))) hΓ hM'L
  have hKU : IsCompIn (K.map U.subtype) U := by
    refine ⟨Subgroup.map_subtype_le K, ?_⟩
    show CFSG.IsComponent (Subgroup.comap U.subtype (K.map U.subtype))
    rw [Subgroup.comap_map_eq_self_of_injective U.subtype_injective]
    exact hK
  have hMK' : M ≤ K.map U.subtype := fun m hm =>
    ⟨⟨m, hMU hm⟩, hMK (Subgroup.mem_subgroupOf.2 hm), rfl⟩
  have hKtop : K.map U.subtype ≠ ⊤ := fun h =>
    hU (top_le_iff.1 (h ▸ Subgroup.map_subtype_le K))
  have hq : IsSporadic (↥M ⧸ center ↥M) .HS :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hMq.2).trans QuotientGroup.quotientBot).trans eM⟩
  have heq : M = K.map U.subtype :=
    eq_of_le_of_catalog hKP h3 hKG hMq.1 hKU.isQuasisimple hKtop hMK' hq
  rw [heq]
  exact hKU

end Assembly

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
