module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Fusion
public import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralHall
public import CFSG.LocalAnalysis.RankTwoShapes.OrderSixtyFour
public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution

public section

namespace CFSG.LyonsUnitaryFour

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_third_mem_four {Z : Subgroup G} (hZcard : Nat.card Z = 4) (z : G) :
    ∃ u ∈ Z, u ≠ 1 ∧ u ≠ z := by
  by_contra h
  push Not at h
  have hsub : (Z : Set G) ⊆ {1, z} := by
    intro w hw
    by_cases hw1 : w = 1
    · simp [hw1]
    · simp [h w hw hw1]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hZ' : (Z : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hZcard
  rw [hZ'] at hle
  have h2 : ({1, z} : Set G).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
  omega

theorem mem_four_cases {Z : Subgroup G} (hZcard : Nat.card Z = 4) (hZexp : ∀ w ∈ Z, w ^ 2 = 1)
    {z u : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1) (huZ : u ∈ Z) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∀ w ∈ Z, w = 1 ∨ w = z ∨ w = u ∨ w = u * z := by
  have huzZ : u * z ∈ Z := Z.mul_mem huZ hzZ
  have huz1 : u * z ≠ 1 := by
    intro h
    have : u = z⁻¹ := eq_inv_of_mul_eq_one_left h
    apply huz
    rw [this]
    exact (eq_inv_of_mul_eq_one_left (by rw [← sq]; exact hZexp z hzZ)).symm
  have huzu : u * z ≠ u := fun h => hz1 (mul_left_cancel (h.trans (mul_one u).symm))
  have huzz : u * z ≠ z := fun h => hu1 (mul_right_cancel (h.trans (one_mul z).symm))
  intro w hw
  exact CFSG.RankTwoShapes.mem_of_card_eq_four hZcard Z.one_mem
    hzZ huZ huzZ hz1.symm hu1.symm huz1.symm huz.symm huzz.symm huzu.symm hw

theorem sq_conj_eq_of_fix_four {Z : Subgroup G} (hZcard : Nat.card Z = 4)
    (hZexp : ∀ w ∈ Z, w ^ 2 = 1) {z n : G}
    (hzZ : z ∈ Z) (hz1 : z ≠ 1) (hn : ∀ w ∈ Z, n * w * n⁻¹ ∈ Z) (hnz : n * z * n⁻¹ = z) :
    ∀ w ∈ Z, n ^ 2 * w * (n ^ 2)⁻¹ = w := by
  classical
  obtain ⟨u, huZ, hu1, huz⟩ := exists_third_mem_four hZcard z
  have hmem := mem_four_cases hZcard hZexp hzZ hz1 huZ hu1 huz
  have hconj_mul : ∀ a b : G, n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by
    intro a b; group
  have hnu : n * u * n⁻¹ = u ∨ n * u * n⁻¹ = u * z := by
    rcases hmem _ (hn u huZ) with h | h | h | h
    · exfalso
      apply hu1
      have := congrArg (fun x => n⁻¹ * x * n) h
      simpa [mul_assoc] using this
    · exfalso
      apply huz
      have := congrArg (fun x => n⁻¹ * x * n) (h.trans hnz.symm)
      simpa [mul_assoc] using this
    · exact Or.inl h
    · exact Or.inr h
  have hsq2 : n ^ 2 * u * (n ^ 2)⁻¹ = u := by
    rcases hnu with h | h
    · calc n ^ 2 * u * (n ^ 2)⁻¹ = n * (n * u * n⁻¹) * n⁻¹ := by rw [sq]; group
        _ = u := by rw [h, h]
    · calc n ^ 2 * u * (n ^ 2)⁻¹ = n * (n * u * n⁻¹) * n⁻¹ := by rw [sq]; group
        _ = n * (u * z) * n⁻¹ := by rw [h]
        _ = (n * u * n⁻¹) * (n * z * n⁻¹) := hconj_mul u z
        _ = u * z * z := by rw [h, hnz]
        _ = u := by rw [mul_assoc, ← sq, hZexp z hzZ, mul_one]
  have hsqz : n ^ 2 * z * (n ^ 2)⁻¹ = z := by
    calc n ^ 2 * z * (n ^ 2)⁻¹ = n * (n * z * n⁻¹) * n⁻¹ := by rw [sq]; group
      _ = z := by rw [hnz, hnz]
  intro w hw
  rcases hmem w hw with rfl | rfl | rfl | rfl
  · group
  · exact hsqz
  · exact hsq2
  · rw [show n ^ 2 * (u * z) * (n ^ 2)⁻¹ = (n ^ 2 * u * (n ^ 2)⁻¹) * (n ^ 2 * z * (n ^ 2)⁻¹) by
      group, hsq2, hsqz]

omit [Finite G] in
theorem mem_map_center_iff {S : Subgroup G} {x : G} :
    x ∈ (Subgroup.center S).map S.subtype ↔ x ∈ S ∧ ∀ s ∈ S, s * x = x * s := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun s hs => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨s, hs⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxS, hx⟩
    refine ⟨⟨x, hxS⟩, Subgroup.mem_center_iff.mpr fun s => Subtype.ext (hx s s.2), rfl⟩

omit [Finite G] in
theorem conj_mem_map_center {S : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (S : Set G))
    {w : G} (hw : w ∈ (Subgroup.center S).map S.subtype) :
    n * w * n⁻¹ ∈ (Subgroup.center S).map S.subtype := by
  rw [mem_map_center_iff] at hw ⊢
  obtain ⟨hwS, hw⟩ := hw
  refine ⟨(Subgroup.mem_normalizer_iff.mp hn w).mp hwS, fun s hs => ?_⟩
  have hs' : n⁻¹ * s * n ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) s).mp hs
    simpa using this
  have h := hw _ hs'
  calc s * (n * w * n⁻¹) = n * ((n⁻¹ * s * n) * w) * n⁻¹ := by group
    _ = n * (w * (n⁻¹ * s * n)) * n⁻¹ := by rw [h]
    _ = n * w * n⁻¹ * s := by group

theorem normalizer_fix_centralizes_center_four (S : Sylow 2 G)
    (hZcard : Nat.card ((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) = 4)
    (hZexp : ∀ w ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, w ^ 2 = 1)
    {z : G} (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (hz1 : z ≠ 1) {n : G} (hn : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hnz : n * z * n⁻¹ = z) :
    ∀ w ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, n * w * n⁻¹ = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZ
  have hsq := sq_conj_eq_of_fix_four hZcard hZexp hzZ hz1
    (fun w hw => conj_mem_map_center hn hw) hnz
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  have hxS : n ^ m ∈ (S : Subgroup G) := by
    have hp : IsPGroup 2 (Subgroup.zpowers (n ^ m)) := by
      apply IsPGroup.of_card (n := a)
      rw [Nat.card_zpowers, orderOf_pow' n (by obtain ⟨k, rfl⟩ := hm; omega), hord,
        Nat.gcd_mul_left_left]
      · obtain ⟨k, rfl⟩ := hm
        rw [Nat.mul_div_cancel _ (by omega)]
    have hmem : n ^ m ∈ Subgroup.zpowers (n ^ m) ⊓ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
      ⟨Subgroup.mem_zpowers _, Subgroup.pow_mem _ hn _⟩
    have h2 : n ^ m ∈ Subgroup.zpowers (n ^ m) ⊓ (S : Subgroup G) := by
      rw [← hp.inf_normalizer_sylow S]
      exact hmem
    exact h2.2
  intro w hw
  have hwc : n ^ m * w * (n ^ m)⁻¹ = w := by
    have := ((mem_map_center_iff.mp hw).2 _ hxS).symm
    rw [← this]; group
  obtain ⟨k, rfl⟩ := hm
  have hn_eq : n = ((n ^ 2) ^ k)⁻¹ * n ^ (2 * k + 1) := by
    rw [pow_succ n (2 * k), pow_mul]; group
  have hpowk : ∀ j : ℕ, (n ^ 2) ^ j * w * ((n ^ 2) ^ j)⁻¹ = w := by
    intro j
    induction j with
    | zero => group
    | succ j ih =>
      calc (n ^ 2) ^ (j + 1) * w * ((n ^ 2) ^ (j + 1))⁻¹
          = (n ^ 2) ^ j * (n ^ 2 * w * (n ^ 2)⁻¹) * ((n ^ 2) ^ j)⁻¹ := by group
        _ = w := by rw [hsq w hw, ih]
  have hinvk : ((n ^ 2) ^ k)⁻¹ * w * ((n ^ 2) ^ k) = w := by
    have := hpowk k
    calc ((n ^ 2) ^ k)⁻¹ * w * ((n ^ 2) ^ k)
        = ((n ^ 2) ^ k)⁻¹ * ((n ^ 2) ^ k * w * ((n ^ 2) ^ k)⁻¹) * ((n ^ 2) ^ k) := by
          rw [this]
      _ = w := by group
  calc n * w * n⁻¹ = ((n ^ 2) ^ k)⁻¹ * (n ^ (2 * k + 1) * w * (n ^ (2 * k + 1))⁻¹) *
        ((n ^ 2) ^ k) := by
        nth_rewrite 1 [hn_eq]
        nth_rewrite 2 [hn_eq]
        group
    _ = w := by rw [hwc, hinvk]
theorem conj_eq_of_mem_center_four (S : Sylow 2 G)
    (hZcard : Nat.card ((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) = 4)
    (hZexp : ∀ w ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, w ^ 2 = 1)
    {z : G} (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (hz1 : z ≠ 1) {c u : G} (hc : c * z = z * c)
    (hu : u ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (hcu : c * u * c⁻¹ ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) :
    c * u * c⁻¹ = u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZ
  set v := c * u * c⁻¹ with hv
  set H := Subgroup.centralizer ({v} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) with hH
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · exact ((mem_map_center_iff.mp hcu).2 s hs)
    · exact ((mem_map_center_iff.mp hzZ).2 s hs)
  set Q := (S : Subgroup G).map (MulAut.conj c).toMonoidHom with hQ
  have hQH : Q ≤ H := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hsu := (mem_map_center_iff.mp hu).2 s hs
    have hsz := (mem_map_center_iff.mp hzZ).2 s hs
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · calc c * s * c⁻¹ * v = c * (s * u) * c⁻¹ := by rw [hv]; group
        _ = c * (u * s) * c⁻¹ := by rw [hsu]
        _ = v * (c * s * c⁻¹) := by rw [hv]; group
    · have hcz : c⁻¹ * z = z * c⁻¹ := by
        calc c⁻¹ * z = c⁻¹ * (z * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * z) * c⁻¹ := by rw [hc]
          _ = z * c⁻¹ := by group
      calc c * s * c⁻¹ * z = c * s * (z * c⁻¹) := by rw [mul_assoc (c * s), hcz]
        _ = c * (s * z) * c⁻¹ := by group
        _ = c * (z * s) * c⁻¹ := by rw [hsz]
        _ = (c * z) * s * c⁻¹ := by group
        _ = z * (c * s * c⁻¹) := by rw [hc]; group
  have hQp : IsPGroup 2 Q := S.isPGroup'.map _
  obtain ⟨h, hhH, hh⟩ := exists_conj_le_sylow_of_le S hSH hQH hQp
  set n := h * c with hn
  have hnS : (S : Subgroup G).map (MulAut.conj n).toMonoidHom = (S : Subgroup G) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨s, hs, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have := hh (c * s * c⁻¹) ⟨s, hs, by simp⟩
      rw [hn]
      convert this using 1
      group
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have hnN : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    mem_normalizer_of_map_conj_eq hnS
  have hhv : h * v = v * h := Subgroup.mem_centralizer_singleton_iff.mp hhH.1
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp hhH.2
  have hnz : n * z * n⁻¹ = z := by
    calc n * z * n⁻¹ = h * (c * z) * c⁻¹ * h⁻¹ := by rw [hn]; group
      _ = h * z * h⁻¹ := by rw [hc]; group
      _ = z := by rw [hhz]; group
  have hnu : n * u * n⁻¹ = v := by
    calc n * u * n⁻¹ = h * v * h⁻¹ := by rw [hn, hv]; group
      _ = v := by rw [hhv]; group
  rw [← hnu]
  exact normalizer_fix_centralizes_center_four S hZcard hZexp hzZ hz1 hnN hnz u hu
theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] : Odd (Nat.card (CFSG.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.oddCore X ≤ CFSG.pPrimeCore 2 X :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  have hge : CFSG.pPrimeCore 2 X ≤ CFSG.oddCore X :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mp hN.2⟩
  rw [le_antisymm hle hge]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem oddCore_quotient_central_two {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hNc : N ≤ Subgroup.center X) (hN2 : IsPGroup 2 N) :
    (CFSG.oddCore X).map (QuotientGroup.mk' N) = CFSG.oddCore (X ⧸ N) ∧
      (CFSG.oddCore (X ⧸ N)).comap (QuotientGroup.mk' N) = N ⊔ CFSG.oddCore X ∧
      N ⊓ CFSG.oddCore X = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  obtain ⟨a, ha⟩ := hN2.exists_card_eq
  set L := (CFSG.oddCore (X ⧸ N)).comap π with hL
  have hNL : N ≤ L := by
    intro x hx
    rw [hL, Subgroup.mem_comap, hπ, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _
  have hLnormal : L.Normal := (CFSG.oddCore_normal (X ⧸ N)).comap π
  have hodd_coprime : ∀ m : ℕ, Odd m → Nat.Coprime m (Nat.card N) := by
    intro m hm
    rw [ha]
    exact Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hm)
  have hKL : CFSG.oddCore X ≤ L := by
    rw [hL, ← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨(CFSG.oddCore_normal X).map π hπs, ?_⟩
    exact Odd.of_dvd_nat (odd_card_oddCore X) (Subgroup.card_map_dvd _ _)
  set A := N.subgroupOf L with hA
  have hAc : A ≤ Subgroup.center L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have := Subgroup.mem_center_iff.mp (hNc (Subgroup.mem_subgroupOf.mp hx)) (g : X)
    simpa using this
  have hAcard : Nat.card A = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
  set φ : L →* X ⧸ N := π.comp L.subtype with hφ
  have hker : φ.ker = A := by
    ext x
    rw [MonoidHom.mem_ker, hA, Subgroup.mem_subgroupOf, hφ, MonoidHom.comp_apply, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hrange : φ.range ≤ CFSG.oddCore (X ⧸ N) := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  have hidx_odd : Odd A.index := by
    rw [← hker, Subgroup.index_ker]
    exact Odd.of_dvd_nat (odd_card_oddCore _) (Subgroup.card_dvd_of_le hrange)
  have hcop : Nat.Coprime (Nat.card A) A.index := by
    rw [hAcard]
    exact (hodd_coprime _ hidx_odd).symm
  obtain ⟨K₀, hK₀card, hAK₀, -, hK₀mem, -, -⟩ := central_hall_direct_complement A hAc hcop
  set n := A.index with hn
  set K₁ := K₀.map L.subtype with hK₁
  have hK₁normal : K₁.Normal := by
    refine ⟨fun k hk g => ?_⟩
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    have hmemL : g * (k₀ : X) * g⁻¹ ∈ L := hLnormal.conj_mem _ k₀.2 g
    refine ⟨⟨_, hmemL⟩, (hK₀mem _).mpr ?_, rfl⟩
    apply Subtype.ext
    have h1 : (k₀ : X) ^ n = 1 := by
      have := congrArg Subtype.val ((hK₀mem k₀).mp hk₀)
      simpa using this
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [conj_pow, h1]
    group
  have hK₁odd : Odd (Nat.card K₁) := by
    rw [hK₁, Subgroup.card_map_of_injective L.subtype_injective, hK₀card]
    exact hidx_odd
  have hK₁le : K₁ ≤ CFSG.oddCore X := le_sSup ⟨hK₁normal, hK₁odd⟩
  have hleK₁ : CFSG.oddCore X ≤ K₁ := by
    intro k hk
    set ℓ : L := ⟨k, hKL hk⟩ with hℓ
    have hord : Odd (orderOf ℓ) := by
      rw [hℓ, Subgroup.orderOf_mk]
      exact CFSG.Adapters.odd_orderOf_of_mem_oddCore hk
    have hdvd : orderOf ℓ ∣ Nat.card A * n := by
      rw [Subgroup.card_mul_index]
      exact orderOf_dvd_natCard ℓ
    have hdvdn : orderOf ℓ ∣ n := by
      rw [hAcard] at hdvd
      exact (hodd_coprime _ hord).dvd_of_dvd_mul_left hdvd
    have hℓK₀ : ℓ ∈ K₀ := (hK₀mem ℓ).mpr (orderOf_dvd_iff_pow_eq_one.mp hdvdn)
    exact ⟨ℓ, hℓK₀, rfl⟩
  have hK₁eq : K₁ = CFSG.oddCore X := le_antisymm hK₁le hleK₁
  have hANormal : A.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_center_iff.mp (hAc hx) g, mul_inv_cancel_right]
    exact hx
  have hdecomp : ∀ x ∈ L, ∃ y ∈ N, ∃ k ∈ CFSG.oddCore X, y * k = x := by
    intro x hx
    have hmem : (⟨x, hx⟩ : L) ∈ ((A ⊔ K₀ : Subgroup L) : Set L) := by
      rw [hAK₀]; exact Subgroup.mem_top _
    rw [Subgroup.normal_mul] at hmem
    obtain ⟨y, hy, k, hk, hyk⟩ := hmem
    refine ⟨y, Subgroup.mem_subgroupOf.mp hy, k, hK₁eq ▸ ⟨k, hk, rfl⟩, ?_⟩
    have := congrArg Subtype.val hyk
    simpa using this
  have hLeq : L = N ⊔ CFSG.oddCore X := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, k, hk, rfl⟩ := hdecomp x hx
      exact Subgroup.mul_mem_sup hy hk
    · exact sup_le hNL hKL
  refine ⟨?_, hLeq, ?_⟩
  · apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]; exact hKL
    · intro y hy
      obtain ⟨x, rfl⟩ := hπs y
      obtain ⟨y', hy', k, hk, hxe⟩ := hdecomp x hy
      refine ⟨k, hk, ?_⟩
      rw [← hxe, map_mul, hπ, QuotientGroup.mk'_apply (N := N) y',
        (QuotientGroup.eq_one_iff y').mpr hy', one_mul]
  · rw [eq_bot_iff]
    intro x ⟨hxN, hxK⟩
    rw [Subgroup.mem_bot]
    have hord : Odd (orderOf x) := CFSG.Adapters.odd_orderOf_of_mem_oddCore hxK
    have hdvd : orderOf x ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hodd_coprime _ hord) hdvd)
omit [Finite G] in
@[expose] def centralizerLine (z : G) : Subgroup (Subgroup.centralizer ({z} : Set G)) :=
  Subgroup.zpowers ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

omit [Finite G] in
theorem centralizerLine_le_center (z : G) :
    centralizerLine z ≤ Subgroup.center (Subgroup.centralizer ({z} : Set G)) := by
  rw [centralizerLine, Subgroup.zpowers_le]
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp g.2

instance centralizerLine_normal (z : G) : (centralizerLine z).Normal := by
  refine ⟨fun a ha g => ?_⟩
  rw [Subgroup.mem_center_iff.mp (centralizerLine_le_center z ha) g, mul_inv_cancel_right]
  exact ha

omit [Finite G] in
theorem mem_zpowers_of_sq_eq_one {x y : G} (hy : y ^ 2 = 1) :
    x ∈ Subgroup.zpowers y ↔ x = 1 ∨ x = y := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hy' : y ^ (2 : ℤ) = 1 := by exact_mod_cast hy
    rw [zpow_eq_zpow_emod k hy']
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
theorem central_four_involution_centralizer_oddCore (S : Sylow 2 G)
    (hZcard : Nat.card (Subgroup.center (S : Subgroup G)) = 4)
    (hZexp : ∀ w ∈ Subgroup.center (S : Subgroup G), w ^ 2 = 1)
    (hinv : ∀ t : (S : Subgroup G), orderOf t = 2 → t ∈ Subgroup.center (S : Subgroup G))
    (z : (S : Subgroup G)) (hzZ : z ∈ Subgroup.center (S : Subgroup G)) (hz1 : z ≠ 1) :
    (∀ c ∈ Subgroup.centralizer ({(z : G)} : Set G),
        ∃ d ∈ Subgroup.centralizer
            (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
              Set G),
          ∃ k ∈ (CFSG.oddCore (Subgroup.centralizer ({(z : G)} : Set G))).map
              (Subgroup.centralizer ({(z : G)} : Set G)).subtype, c = d * k) ∧
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype).subgroupOf
          (Subgroup.centralizer ({(z : G)} : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({(z : G)} : Set G)))) ≤
        Subgroup.center (Subgroup.centralizer ({(z : G)} : Set G) ⧸
          CFSG.oddCore (Subgroup.centralizer ({(z : G)} : Set G))) ∧
      (CFSG.oddCore (Subgroup.centralizer ({(z : G)} : Set G))).map
          (QuotientGroup.mk' (centralizerLine (z : G))) =
        CFSG.oddCore (Subgroup.centralizer ({(z : G)} : Set G) ⧸ centralizerLine (z : G)) ∧
      (CFSG.oddCore (Subgroup.centralizer ({(z : G)} : Set G) ⧸ centralizerLine (z : G))).comap
          (QuotientGroup.mk' (centralizerLine (z : G))) =
        centralizerLine (z : G) ⊔ CFSG.oddCore (Subgroup.centralizer ({(z : G)} : Set G)) ∧
      centralizerLine (z : G) ⊓ CFSG.oddCore (Subgroup.centralizer ({(z : G)} : Set G)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZ
  set C := Subgroup.centralizer ({(z : G)} : Set G) with hC
  have hZcardG : Nat.card Z = 4 := by
    rw [hZ, Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective, hZcard]
  have hZexpG : ∀ w ∈ Z, w ^ 2 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have h := congrArg Subtype.val (hZexp y hy)
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  have hzZG : (z : G) ∈ Z := ⟨z, hzZ, rfl⟩
  have hz1G : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hinvG : ∀ t ∈ (S : Subgroup G), orderOf t = 2 → t ∈ Z := by
    intro t ht hord
    exact ⟨⟨t, ht⟩, hinv ⟨t, ht⟩ (by rw [Subgroup.orderOf_mk]; exact hord), rfl⟩
  have hZcomm : ∀ w ∈ Z, ∀ s ∈ (S : Subgroup G), s * w = w * s := fun w hw =>
    (mem_map_center_iff.mp hw).2
  have hZS : ∀ w ∈ Z, w ∈ (S : Subgroup G) := fun w hw => (mem_map_center_iff.mp hw).1
  obtain ⟨u, huZ, hu1, huz⟩ := exists_third_mem_four hZcardG (z : G)
  have hcases := mem_four_cases hZcardG hZexpG hzZG hz1G huZ hu1 huz
  have hZD : Z ≤ Subgroup.centralizer (Z : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro w' hw'
    exact hZcomm w hw w' (hZS w' hw')
  have hcentZ : ∀ d : G, d * z = z * d → d * u = u * d →
      d ∈ Subgroup.centralizer (Z : Set G) := by
    intro d hdz hdu
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hcases w hw with rfl | rfl | rfl | rfl
    · simp
    · exact hdz.symm
    · exact hdu.symm
    · calc u * z * d = u * (d * z) := by rw [mul_assoc, hdz]
        _ = d * (u * z) := by rw [← mul_assoc, ← hdu, mul_assoc]
  have hzC : (z : G) ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hSC : (S : Subgroup G) ≤ C := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hZcomm _ hzZG s hs)
  have hZC : ∀ w ∈ Z, w ∈ C := fun w hw => hSC (hZS w hw)
  set N := centralizerLine (z : G) with hN
  set zC : C := ⟨(z : G), hzC⟩ with hzCdef
  have hNdef : N = Subgroup.zpowers zC := rfl
  have hzC2 : zC ^ 2 = 1 := Subtype.ext (hZexpG _ hzZG)
  have hzCord : orderOf zC = 2 := orderOf_eq_prime hzC2 (fun h => hz1G (congrArg Subtype.val h))
  have hmemN : ∀ x : C, x ∈ N ↔ x = 1 ∨ x = zC := fun x => mem_zpowers_of_sq_eq_one hzC2
  have hNcard : Nat.card N = 2 := by rw [hNdef, Nat.card_zpowers, hzCord]
  have hN2 : IsPGroup 2 N := IsPGroup.of_card (n := 1) (by rw [hNcard, pow_one])
  obtain ⟨hmapK, hcomapK, hinfK⟩ :=
    oddCore_quotient_central_two N (centralizerLine_le_center (z : G)) hN2
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hNG : ∀ x : C, x ∈ N → (x : G) ∈ Z := by
    intro x hx
    rcases (hmemN x).mp hx with rfl | rfl
    · exact Z.one_mem
    · exact hzZG
  have hπeq : ∀ x y : C, π x = π y ↔ x⁻¹ * y ∈ N := by
    intro x y
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have huC : u ∈ C := hZC u huZ
  set uC : C := ⟨u, huC⟩ with huCdef
  have huN : uC ∉ N := by
    rw [hmemN]
    rintro (h | h)
    · exact hu1 (congrArg Subtype.val h)
    · exact huz (congrArg Subtype.val h)
  have huC2 : uC ^ 2 = 1 := Subtype.ext (hZexpG u huZ)
  set SC : Sylow 2 C := S.subtype hSC with hSCdef
  have hmemSC : ∀ x : C, x ∈ (SC : Subgroup C) ↔ (x : G) ∈ (S : Subgroup G) := by
    intro x
    rw [hSCdef, Sylow.coe_subtype, Subgroup.mem_subgroupOf]
  set Sbar : Sylow 2 (C ⧸ N) := SC.mapSurjective hπs with hSbardef
  have hmemSbar : ∀ y : C ⧸ N, y ∈ (Sbar : Subgroup (C ⧸ N)) ↔
      ∃ x : C, (x : G) ∈ (S : Subgroup G) ∧ π x = y := by
    intro y
    rw [hSbardef, Sylow.coe_mapSurjective, Subgroup.mem_map]
    simp only [hmemSC]
    exact Iff.rfl
  have huS : (u : G) ∈ (S : Subgroup G) := hZS u huZ
  set ubar : (Sbar : Subgroup (C ⧸ N)) := ⟨π uC, (hmemSbar _).mpr ⟨uC, huS, rfl⟩⟩ with hubardef
  have hubarZ : ubar ∈ Subgroup.center (Sbar : Subgroup (C ⧸ N)) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    obtain ⟨x, hxS, hx⟩ := (hmemSbar _).mp s.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx]
    show π x * π uC = π uC * π x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hZcomm u huZ x hxS)
  have hubar2 : orderOf ubar = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      show (π uC) ^ 2 = 1
      rw [← map_pow, huC2, map_one]
    · intro h
      apply huN
      have h' : π 1 = π uC := by
        rw [map_one]; exact (congrArg Subtype.val h).symm
      have := (hπeq 1 uC).mp h'
      rwa [inv_one, one_mul] at this
  have hwc : ∀ g : C ⧸ N, g⁻¹ * (ubar : C ⧸ N) * g ∈ (Sbar : Subgroup (C ⧸ N)) →
      g⁻¹ * (ubar : C ⧸ N) * g = ubar := by
    intro g hg
    obtain ⟨c, rfl⟩ := hπs g
    have hconj : (π c)⁻¹ * (ubar : C ⧸ N) * π c = π (c⁻¹ * uC * c) := by
      rw [map_mul, map_mul, map_inv]
    rw [hconj] at hg ⊢
    obtain ⟨x, hxS, hx⟩ := (hmemSbar _).mp hg
    have hxN : x⁻¹ * (c⁻¹ * uC * c) ∈ N := (hπeq _ _).mp hx
    have hcS : ((c⁻¹ * uC * c : C) : G) ∈ (S : Subgroup G) := by
      have h1 : (c⁻¹ * uC * c : C) = x * (x⁻¹ * (c⁻¹ * uC * c)) := by group
      rw [h1, Subgroup.coe_mul]
      exact Subgroup.mul_mem _ hxS (hZS _ (hNG _ hxN))
    have hcS' : (c : G)⁻¹ * u * c ∈ (S : Subgroup G) := hcS
    have hord : orderOf ((c : G)⁻¹ * u * c) = 2 := by
      have : (c : G)⁻¹ * u * c = MulAut.conj (c : G)⁻¹ u := by simp
      rw [this, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (hZexpG u huZ) hu1
    have hZ' : (c : G)⁻¹ * u * c ∈ Z := hinvG _ hcS' hord
    have hcz : (c : G)⁻¹ * z = z * (c : G)⁻¹ :=
      Subgroup.mem_centralizer_singleton_iff.mp (C.inv_mem c.2)
    have heq := conj_eq_of_mem_center_four S hZcardG hZexpG hzZG hz1G hcz huZ
      (by rw [inv_inv]; exact hZ')
    rw [inv_inv] at heq
    show π (c⁻¹ * uC * c) = π uC
    congr 1
    exact Subtype.ext heq
  obtain ⟨hfac, -⟩ :=
    CFSG.Milestones.glauberman_zStar_central_sylow_involution Sbar ubar hubarZ hubar2 hwc
  have hNle : N ≤ (CFSG.oddCore (C ⧸ N)).comap π := by
    rw [hcomapK]; exact le_sup_left
  have hDK : ∀ c : C, ∃ d : C, (d : G) ∈ Subgroup.centralizer (Z : Set G) ∧
      ∃ k ∈ CFSG.oddCore C, c = d * k := by
    intro c
    obtain ⟨cb, hcb, kb, hkb, hceq⟩ := hfac (π c)
    obtain ⟨d₀, rfl⟩ := hπs cb
    obtain ⟨ℓ₀, rfl⟩ := hπs kb
    have hcomm : π d₀ * π uC = π uC * π d₀ := Subgroup.mem_centralizer_singleton_iff.mp hcb
    have hd₀u : π (d₀ * uC * d₀⁻¹) = π uC := by
      rw [map_mul, map_mul, map_inv, hcomm]
      group
    have hmN : uC⁻¹ * (d₀ * uC * d₀⁻¹) ∈ N := (hπeq _ _).mp hd₀u.symm
    have hconjZ : (d₀ : G) * u * (d₀ : G)⁻¹ ∈ Z := by
      have h2 : ((d₀ * uC * d₀⁻¹ : C) : G) = u * ((uC⁻¹ * (d₀ * uC * d₀⁻¹) : C) : G) := by
        show _ = ((uC : C) : G) * _
        rw [← Subgroup.coe_mul, mul_inv_cancel_left]
      have h3 : ((d₀ * uC * d₀⁻¹ : C) : G) ∈ Z := by
        rw [h2]; exact Z.mul_mem huZ (hNG _ hmN)
      exact h3
    have hd₀z : (d₀ : G) * z = z * d₀ := Subgroup.mem_centralizer_singleton_iff.mp d₀.2
    have hfix := conj_eq_of_mem_center_four S hZcardG hZexpG hzZG hz1G hd₀z huZ hconjZ
    have hd₀u' : (d₀ : G) * u = u * d₀ := by
      calc (d₀ : G) * u = ((d₀ : G) * u * (d₀ : G)⁻¹) * d₀ := by group
        _ = u * d₀ := by rw [hfix]
    have hd₀D := hcentZ _ hd₀z hd₀u'
    have hm : (d₀ * ℓ₀)⁻¹ * c ∈ N := by
      apply (hπeq _ _).mp
      rw [map_mul, hceq]
    have hℓm : ℓ₀ * ((d₀ * ℓ₀)⁻¹ * c) ∈ ((N ⊔ CFSG.oddCore C : Subgroup C) : Set C) := by
      rw [SetLike.mem_coe, ← hcomapK]
      exact Subgroup.mul_mem _ hkb (hNle hm)
    rw [Subgroup.normal_mul, Set.mem_mul] at hℓm
    obtain ⟨y, hy, k, hk, hyk⟩ := hℓm
    refine ⟨d₀ * y, ?_, k, hk, ?_⟩
    · rw [Subgroup.coe_mul]
      exact Subgroup.mul_mem _ hd₀D (hZD (hNG y hy))
    · calc c = d₀ * (ℓ₀ * ((d₀ * ℓ₀)⁻¹ * c)) := by group
        _ = d₀ * (y * k) := by rw [hyk]
        _ = d₀ * y * k := by group
  have hcentral : (Z.subgroupOf C).map (QuotientGroup.mk' (CFSG.oddCore C)) ≤
      Subgroup.center (C ⧸ CFSG.oddCore C) := by
    rintro _ ⟨w, hw', rfl⟩
    have hw : (w : G) ∈ Z := hw'
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore C) g
    obtain ⟨d, hdD, k, hk, rfl⟩ := hDK c
    have hdw : d * w = w * d :=
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hdD) w hw).symm
    have hdw' : d⁻¹ * w * d = w := by
      rw [mul_assoc, ← hdw, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have h1 : (d * k * w)⁻¹ * (w * (d * k)) = (w⁻¹ * k⁻¹ * w) * k := by
      calc (d * k * w)⁻¹ * (w * (d * k)) = w⁻¹ * k⁻¹ * (d⁻¹ * w * d) * k := by group
        _ = (w⁻¹ * k⁻¹ * w) * k := by rw [hdw']
    rw [h1]
    refine Subgroup.mul_mem _ ?_ hk
    have := (CFSG.oddCore_normal C).conj_mem _ (Subgroup.inv_mem _ hk) w⁻¹
    simpa using this
  refine ⟨fun c hc => ?_, hcentral, hmapK, hcomapK, hinfK⟩
  obtain ⟨d, hdD, k, hk, hcdk⟩ := hDK ⟨c, hc⟩
  exact ⟨d, hdD, k, ⟨k, hk, rfl⟩, congrArg Subtype.val hcdk⟩

end CFSG.LyonsUnitaryFour
