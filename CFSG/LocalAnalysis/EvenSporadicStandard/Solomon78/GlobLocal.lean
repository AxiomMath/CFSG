module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma39

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open CFSG.ComponentClassification.PerfectAutomorphisms

variable {G : Type} [Group G]

theorem exists_mul_zpow_of_mem_sup {K : Subgroup G} {u : G} (hu : ∀ k ∈ K, k * u = u * k)
    {x : G} (hx : x ∈ K ⊔ zpowers u) : ∃ k ∈ K, ∃ n : ℤ, x = k * u ^ n := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 0, by simp⟩
    · obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
      exact ⟨1, one_mem _, n, by simp⟩
  | one => exact ⟨1, one_mem _, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k₁, hk₁, n₁, rfl⟩ := hx
    obtain ⟨k₂, hk₂, n₂, rfl⟩ := hy
    refine ⟨k₁ * k₂, mul_mem hk₁ hk₂, n₁ + n₂, ?_⟩
    have hcom : Commute u k₂ := (hu k₂ hk₂).symm
    have hc : u ^ n₁ * k₂ = k₂ * u ^ n₁ := (hcom.zpow_left n₁).eq
    rw [zpow_add]
    calc k₁ * u ^ n₁ * (k₂ * u ^ n₂) = k₁ * (u ^ n₁ * k₂) * u ^ n₂ := by simp only [mul_assoc]
      _ = k₁ * (k₂ * u ^ n₁) * u ^ n₂ := by rw [hc]
      _ = k₁ * k₂ * (u ^ n₁ * u ^ n₂) := by simp only [mul_assoc]
  | inv x _ hx =>
    obtain ⟨k, hk, n, rfl⟩ := hx
    refine ⟨k⁻¹, inv_mem hk, -n, ?_⟩
    have hcom : Commute u k⁻¹ := (hu k⁻¹ (inv_mem hk)).symm
    have hc : (u ^ n)⁻¹ * k⁻¹ = k⁻¹ * (u ^ n)⁻¹ :=
      ((hcom.zpow_left n).inv_left).eq
    rw [mul_inv_rev, zpow_neg]
    exact hc

@[expose] def InducedByCentralizer (L K : Subgroup G) (u : G) : Prop :=
  ∀ g ∈ centralizer ({u} : Set G), g ∈ normalizer (K : Set G) →
    ∃ c ∈ L ⊓ centralizer ({u} : Set G), ∀ k ∈ K, g * k * g⁻¹ = c * k * c⁻¹

theorem sol78Fusion39_of_induced {L K : Subgroup G} {u : G} (hu : ∀ k ∈ K, k * u = u * k)
    (hN : ∀ g ∈ centralizer ({u} : Set G), g ∈ normalizer (K : Set G))
    (h : InducedByCentralizer L K u) : Sol78Fusion39 L K u := by
  intro v hv g hg
  obtain ⟨k, hk, n, rfl⟩ := exists_mul_zpow_of_mem_sup hu hv.1.1
  obtain ⟨c, hc, hck⟩ := h g hg (hN g hg)
  refine ⟨c, hc, ?_⟩
  have hgu : g * u ^ n * g⁻¹ = u ^ n := by
    have h1 : g * u = u * g := mem_centralizer_singleton_iff.1 hg
    have h2 : Commute g (u ^ n) := (Commute.zpow_right (show Commute g u from h1) n)
    rw [h2.eq]
    group
  have hcu : c * u ^ n * c⁻¹ = u ^ n := by
    have h1 : c * u = u * c := mem_centralizer_singleton_iff.1 hc.2
    have h2 : Commute c (u ^ n) := (Commute.zpow_right (show Commute c u from h1) n)
    rw [h2.eq]
    group
  calc g * (k * u ^ n) * g⁻¹ = (g * k * g⁻¹) * (g * u ^ n * g⁻¹) := by group
    _ = (c * k * c⁻¹) * u ^ n := by rw [hck k hk, hgu]
    _ = (c * k * c⁻¹) * (c * u ^ n * c⁻¹) := by rw [hcu]
    _ = c * (k * u ^ n) * c⁻¹ := by group


theorem inducedByCentralizer_of_forall_aut {L K : Subgroup G} {u : G}
    (h : ∀ α : MulAut K, ∃ c ∈ L ⊓ centralizer ({u} : Set G),
      ∀ k : K, ((α k : K) : G) = c * (k : G) * c⁻¹) : InducedByCentralizer L K u := by
  intro g hg hgN
  obtain ⟨c, hc, hck⟩ := h (K.normalizerMonoidHom ⟨g, hgN⟩)
  exact ⟨c, hc, fun k hk => hck ⟨k, hk⟩⟩


theorem inducedByCentralizer_of_allInner {L K : Subgroup G} {u : G} (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k)
    (hinn : ∀ α : MulAut K, ∃ c ∈ K, ∀ k : K, ((α k : K) : G) = c * (k : G) * c⁻¹) :
    InducedByCentralizer L K u :=
  inducedByCentralizer_of_forall_aut fun α => by
    obtain ⟨c, hc, h⟩ := hinn α
    exact ⟨c, ⟨hKL hc, mem_centralizer_singleton_iff.2 (hKu c hc)⟩, h⟩

variable [Finite G]

theorem sol78Generate_of_maximal {L K : Subgroup G} {u : G} (hKL : K ≤ L)
    (hu : u ∈ centralizer (K : Set G)) (hu2 : orderOf u = 2)
    (hZ : ∀ z ∈ (center K).map K.subtype, z * z = 1 → z = 1 ∨ z = u)
    (hmax : ∀ M : Subgroup G, K ≤ M → M ≤ L → M = K ∨ M = L) : Sol78Generate L K u := by
  intro l hl hw
  obtain ⟨v, hv, hwv, -⟩ := hw
  have hu' : ∀ k ∈ K, k * u = u * k := fun k hk => mem_centralizer_iff.1 hu k hk
  have huu : u * u = 1 := by
    have : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    rwa [pow_two] at this
  have hne : K.map (conjHom l) ≠ K := by
    intro heq
    have hwK : ∀ k ∈ K, k * (l * u * l⁻¹) = (l * u * l⁻¹) * k := by
      intro k hk
      have hk' := conj_inv_mem_of_map_eq heq hk
      have h1 := hu' _ hk'
      calc k * (l * u * l⁻¹) = l * ((l⁻¹ * k * l) * u) * l⁻¹ := by group
        _ = l * (u * (l⁻¹ * k * l)) * l⁻¹ := by rw [h1]
        _ = (l * u * l⁻¹) * k := by group
    have hvK : ∀ k ∈ K, k * v = v * k := by
      intro k hk
      have h2 : v = u * (l * u * l⁻¹) := by
        rw [hwv, ← mul_assoc, huu, one_mul]
      rw [h2, ← mul_assoc, hu' k hk, mul_assoc, hwK k hk, ← mul_assoc]
    obtain ⟨k₀, hk₀, n, hvn⟩ := exists_mul_zpow_of_mem_sup hu' hv.1.1
    have hk₀c : ∀ k ∈ K, k₀ * k = k * k₀ := by
      intro k hk
      have hcu : Commute u k := (hu' k hk).symm
      have hcv : Commute v k := (hvK k hk).symm
      have hk0 : k₀ = v * u ^ (-n) := by rw [hvn, mul_assoc, ← zpow_add]; simp
      rw [hk0]
      exact (hcv.mul_left (hcu.zpow_left (-n))).eq
    have hkz : k₀ ∈ (center K).map K.subtype := mem_center_map_iff.2 ⟨hk₀, hk₀c⟩
    have hun : u ^ n = 1 ∨ u ^ n = u := by
      have h : u ^ (n % 2) = u ^ n := by simpa [hu2] using zpow_mod_orderOf u n
      rcases Int.emod_two_eq_zero_or_one n with h0 | h1
      · left
        rw [← h, h0]
        simp
      · right
        rw [← h, h1]
        simp
    rcases hun with h1 | h1
    · apply hv.1.2.1
      have hvk : v = k₀ := by rw [hvn, h1, mul_one]
      rw [hvk]
      exact hkz
    · have hv1 : v = k₀ * u := by rw [hvn, h1]
      have hvv : v * v = 1 := by
        have : v ^ 2 = 1 := by rw [← hv.1.2.2]; exact pow_orderOf_eq_one v
        rwa [pow_two] at this
      have hkk : k₀ * k₀ = 1 := by
        have h2 : v * v = k₀ * k₀ * (u * u) := by
          rw [hv1]
          calc k₀ * u * (k₀ * u) = k₀ * (u * k₀) * u := by simp only [mul_assoc]
            _ = k₀ * (k₀ * u) * u := by rw [hu' k₀ hk₀]
            _ = k₀ * k₀ * (u * u) := by simp only [mul_assoc]
        rwa [h2, huu, mul_one] at hvv
      rcases hZ k₀ hkz hkk with h0 | h0
      · have hv_eq : v = u := by rw [hv1, h0, one_mul]
        have hw1 : l * u * l⁻¹ = 1 := by rw [hwv, hv_eq, huu]
        have hu1 : u = 1 := by
          have := congrArg (fun x => l⁻¹ * x * l) hw1
          simpa [mul_assoc] using this
        rw [hu1, orderOf_one] at hu2
        exact absurd hu2 (by decide)
      · have hv_eq : v = 1 := by rw [hv1, h0, huu]
        have h2 := hv.1.2.2
        rw [hv_eq, orderOf_one] at h2
        exact absurd h2 (by decide)
  have hM1 : K ≤ K ⊔ K.map (conjHom l) := le_sup_left
  have hM2 : K ⊔ K.map (conjHom l) ≤ L := by
    refine sup_le hKL ?_
    rintro _ ⟨k, hk, rfl⟩
    exact mul_mem (mul_mem hl (hKL hk)) (inv_mem hl)
  rcases hmax _ hM1 hM2 with h | h
  · exfalso
    have hle : K.map (conjHom l) ≤ K := le_sup_right.trans h.le
    have : K.map (conjHom l) = K := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective (conjHom_injective l)]
    exact hne this
  · exact h


theorem twoAdic_mono {A B : Subgroup G} (h : A ≤ B) : twoAdic A ≤ twoAdic B := by
  unfold twoAdic
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
    (Subgroup.card_dvd_of_le h) 2

theorem exists_mem_normalizer_not_mem_of_lt {S T : Subgroup G} (hT : IsPGroup 2 T) (hST : S < T) :
    ∃ w ∈ T, w ∈ normalizer (S : Set G) ∧ w ∉ S := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnc : NormalizerCondition T := Group.normalizerCondition_of_isNilpotent (G := T)
  have hS' : S.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact absurd htop (not_le_of_gt hST)
  have hlt := hnc _ hS'
  obtain ⟨x, hxN, hxS⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, ?_, fun hx => hxS (Subgroup.mem_subgroupOf.2 hx)⟩
  have hxsub : x ∈ (normalizer (S : Set G)).subgroupOf T := by
    rw [Subgroup.subgroupOf_normalizer_eq hST.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.1 hxsub


theorem vPairs_nonempty_of_sylow {L K S T : Subgroup G} {u : G}
    (hu2 : orderOf u = 2) (huS : u ∈ S)
    (hSL : S ≤ L ⊓ centralizer ({u} : Set G)) (hSmax : ∀ S' : Subgroup G,
      S' ≤ L ⊓ centralizer ({u} : Set G) → IsPGroup 2 S' → S ≤ S' → S' = S)
    (hTL : T ≤ L) (hT : IsPGroup 2 T) (hST : S < T)
    (hZS : ∀ z ∈ S, (∀ s ∈ S, z * s = s * z) → z ∈ K ⊔ zpowers u)
    (hZK : ∀ z ∈ (center K).map K.subtype, z * z = 1 → z = 1 ∨ z = u)
    (hR : twoAdic K ≤ twoAdic (S ⊓ K)) : (vPairs L K u).Nonempty := by
  have huu : u * u = 1 := by
    have : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    rwa [pow_two] at this
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    exact absurd hu2 (by decide)
  have hSu : ∀ s ∈ S, s * u = u * s := fun s hs =>
    mem_centralizer_singleton_iff.1 (hSL hs).2
  obtain ⟨w, hwT, hwN, hwS⟩ := exists_mem_normalizer_not_mem_of_lt hT hST
  have hwL : w ∈ L := hTL hwT
  have hwS' : ∀ s ∈ S, w⁻¹ * s * w ∈ S := by
    intro s hs
    refine (mem_normalizer_iff.1 hwN (w⁻¹ * s * w)).2 ?_
    have : w * (w⁻¹ * s * w) * w⁻¹ = s := by group
    rw [this]
    exact hs
  have hu'S : w * u * w⁻¹ ∈ S := (mem_normalizer_iff.1 hwN u).1 huS
  have hu'c : ∀ s ∈ S, s * (w * u * w⁻¹) = (w * u * w⁻¹) * s := by
    intro s hs
    have h1 := hSu _ (hwS' s hs)
    calc s * (w * u * w⁻¹) = w * ((w⁻¹ * s * w) * u) * w⁻¹ := by group
      _ = w * (u * (w⁻¹ * s * w)) * w⁻¹ := by rw [h1]
      _ = (w * u * w⁻¹) * s := by group
  have hne : w * u * w⁻¹ ≠ u := by
    intro heq
    have hwu : w ∈ centralizer ({u} : Set G) := by
      refine mem_centralizer_singleton_iff.2 ?_
      calc w * u = (w * u * w⁻¹) * w := by group
        _ = u * w := by rw [heq]
    have hle : S ⊔ zpowers w ≤ L ⊓ centralizer ({u} : Set G) :=
      sup_le hSL (zpowers_le.2 (mem_inf.2 ⟨hwL, hwu⟩))
    have hp : IsPGroup 2 ↥(S ⊔ zpowers w) :=
      hT.to_le (sup_le hST.le (zpowers_le.2 hwT))
    have h2 := hSmax _ hle hp le_sup_left
    exact hwS (h2 ▸ (le_sup_right : zpowers w ≤ S ⊔ zpowers w) (mem_zpowers w))
  obtain ⟨u', hu'⟩ : ∃ u' : G, u' = w * u * w⁻¹ := ⟨_, rfl⟩
  rw [← hu'] at hu'S hu'c hne
  have hu'u' : u' * u' = 1 := by
    rw [hu']
    calc w * u * w⁻¹ * (w * u * w⁻¹) = w * (u * u) * w⁻¹ := by group
      _ = 1 := by rw [huu]; group
  have huu' : u * u' = u' * u := (hSu u' hu'S).symm
  have hu'1 : u' ≠ 1 := by
    intro h1
    rw [hu'] at h1
    have : u = 1 := by
      have := congrArg (fun x => w⁻¹ * x * w) h1
      simpa [mul_assoc] using this
    exact hu1 this
  obtain ⟨v, hv⟩ : ∃ v : G, v = u * u' := ⟨_, rfl⟩
  have hvS : v ∈ S := by rw [hv]; exact mul_mem huS hu'S
  have hvc : ∀ s ∈ S, v * s = s * v := by
    intro s hs
    have h1 : s * u = u * s := hSu s hs
    have h2 := hu'c s hs
    rw [hv]
    calc u * u' * s = u * (u' * s) := by rw [mul_assoc]
      _ = u * (s * u') := by rw [← h2]
      _ = (u * s) * u' := by rw [← mul_assoc]
      _ = (s * u) * u' := by rw [h1]
      _ = s * (u * u') := by rw [mul_assoc]
  have hvv : v * v = 1 := by
    rw [hv]
    calc u * u' * (u * u') = u * (u' * u) * u' := by simp only [mul_assoc]
      _ = u * (u * u') * u' := by rw [huu']
      _ = (u * u) * (u' * u') := by simp only [mul_assoc]
      _ = 1 := by rw [huu, hu'u', one_mul]
  have hv1 : v ≠ 1 := by
    intro h1
    apply hne
    have : u * u' = u * u := by rw [← hv, h1, huu]
    exact mul_left_cancel this
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rwa [pow_two]) hv1
  have hvK : v ∈ K ⊔ zpowers u := hZS v hvS hvc
  have hvZ : v ∉ (center K).map K.subtype := by
    intro hz
    rcases hZK v hz hvv with h | h
    · exact hv1 h
    · apply hu'1
      have : u * u' = u * 1 := by rw [← hv, h, mul_one]
      exact mul_left_cancel this
  have hvmax : v ∈ vMaximal K u := by
    refine ⟨⟨hvK, hvZ, hvo⟩, fun v' _ => ?_⟩
    calc twoAdic (K ⊓ centralizer ({v'} : Set G)) ≤ twoAdic K := twoAdic_mono inf_le_left
      _ ≤ twoAdic (S ⊓ K) := hR
      _ ≤ twoAdic (K ⊓ centralizer ({v} : Set G)) := by
        refine twoAdic_mono fun x hx => ⟨hx.2, ?_⟩
        exact mem_centralizer_singleton_iff.2 (hvc x hx.1).symm
  refine ⟨u * v, v, hvmax, rfl, w, hwL, ?_⟩
  calc w * u * w⁻¹ = u' := hu'.symm
    _ = u * (u * u') := by rw [← mul_assoc, huu, one_mul]
    _ = u * v := by rw [hv]


theorem exists_inner_of_perfect_of_quotient_inner {K : Type*} [Group K] [Group.IsPerfect K]
    (h : ∀ β : MulAut (K ⧸ center K), ∃ x : K ⧸ center K, ∀ y, β y = x * y * x⁻¹)
    (α : MulAut K) : ∃ c : K, ∀ k : K, α k = c * k * c⁻¹ := by
  obtain ⟨xb, hx⟩ := h (onCenterQuotient α)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  refine ⟨x, fun k => ?_⟩
  have hβ : (MulAut.conj x⁻¹).toMonoidHom.comp α.toMonoidHom = MonoidHom.id K := by
    refine hom_eq_id_of_central_displacement _ fun y => ?_
    rw [← QuotientGroup.eq_one_iff]
    have h1 := hx (QuotientGroup.mk y)
    have h2 : onCenterQuotient α (QuotientGroup.mk y) = QuotientGroup.mk (α y) :=
      onCenterQuotient_apply_mk α y
    rw [h2] at h1
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulAut.conj_apply, inv_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
    group
  have := congrArg (fun f : K →* K => f k) hβ
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    MulAut.conj_apply, inv_inv, MonoidHom.id_apply] at this
  calc α k = x * (x⁻¹ * α k * x) * x⁻¹ := by group
    _ = x * k * x⁻¹ := by rw [this]


end CFSG.EvenSporadicStandard.Solomon78
