module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineI

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem mem_fiveClosure_of_mul_self [Finite X] {L : Subgroup X}
    (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin 5)) {w₀ z : X}
    (hLw : L ≤ centralizer ({w₀} : Set X)) (hLz : L ≤ centralizer ({z} : Set X))
    (hw2 : IsPGroup 2 (zpowers w₀)) (hz2 : z * z = 1) (hwz : w₀ * z = z * w₀)
    {v : X} (hvL : v ∈ L) (hv2 : v * v = 1) : v ∈ fiveClosure L w₀ z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρL, hρL⟩ := exists_isPermAction (M := L) (by norm_num) (by norm_num) θL
  have hcen : ∀ {u : X}, L ≤ centralizer ({u} : Set X) →
      u ∈ normalizer (L : Set X) ∧ u ∈ UnbalancedLayer.coreActionKernel L := by
    intro u hLu
    have huC : u ∈ centralizer (L : Set X) := by
      rw [mem_centralizer_iff]
      intro x hx
      exact (mem_centralizer_singleton_iff.mp (hLu hx))
    have huN : u ∈ normalizer (L : Set X) := Subgroup.centralizer_le_normalizer _ huC
    refine ⟨huN, UnbalancedLayer.mem_coreActionKernel.mpr ⟨huN, fun x hx => ?_⟩⟩
    have hxu : x * u = u * x := mem_centralizer_singleton_iff.mp (hLu hx)
    have h1 : x⁻¹ * u⁻¹ * x * u = 1 := by
      calc x⁻¹ * u⁻¹ * x * u = x⁻¹ * u⁻¹ * (x * u) := by group
        _ = x⁻¹ * u⁻¹ * (u * x) := by rw [hxu]
        _ = 1 := by group
    rw [h1]
    exact one_mem _
  obtain ⟨hwN, hwK⟩ := hcen hLw
  obtain ⟨hzN, hzK⟩ := hcen hLz
  have hρw : ρL ⟨w₀, hwN⟩ = 1 := hρL.eq_one_of_mem_coreActionKernel (by norm_num) hwK
  set P := fiveClosure L w₀ z with hPdef
  have hPL : P ≤ L := (fiveClosure_le L w₀ z).trans (inf_le_left.trans inf_le_left)
  have himg := hρL.fixAlt_le_image_fiveClosure (by norm_num) hwN hw2 hzN hz2 hwz hzK
    (by rw [hρw, Perm.support_one, Finset.card_empty])
  have hcov : ∀ b : alternatingGroup (Fin 5), ∃ x : ↥L, (x : X) ∈ P ∧
      θL (x : ↥L ⧸ pPrimeCore 2 ↥L) = b := by
    intro b
    have hb : b ∈ fixAlt (ρL ⟨w₀, hwN⟩) := by
      rw [mem_fixAlt, hρw, Perm.support_one, Finset.compl_empty]
      exact Finset.subset_univ _
    obtain ⟨y, hy, hyb⟩ := himg b hb
    have hyP : (y : X) ∈ P := hy
    have hyL : (y : X) ∈ L := hPL hyP
    refine ⟨⟨y, hyL⟩, hyP, Subtype.ext ?_⟩
    rw [← hyb, ← hρL.apply_of_mem (by norm_num) ⟨y, hyL⟩]
  have hsup : P ⊔ (pPrimeCore 2 ↥L).map L.subtype = L := sup_core_eq_of_cover θL hPL hcov
  have hLP : L ≤ normalizer (P : Set X) := fun c hc =>
    mem_normalizer_fiveClosure hc (hLw hc) (hLz hc)
  set P' := P.subgroupOf L with hP'def
  have hP'n : P'.Normal := normal_subgroupOf_of_le_normalizer hLP
  set π := QuotientGroup.mk' P' with hπdef
  have hsup' : P' ⊔ pPrimeCore 2 ↥L = ⊤ := by
    have h2 : (P ⊔ (pPrimeCore 2 ↥L).map L.subtype).subgroupOf L = ⊤ := by
      rw [hsup]
      exact subgroupOf_self L
    rwa [subgroupOf_sup hPL (map_subtype_le _), subgroupOf_map_subtype_self] at h2
  have hOtop : (pPrimeCore 2 ↥L).map π = ⊤ := by
    have h2 := congrArg (Subgroup.map π) hsup'
    rwa [Subgroup.map_sup, hπdef, QuotientGroup.map_mk'_self, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  have hodd : Odd (Nat.card (↥L ⧸ P')) := by
    have h1 : Nat.card ((pPrimeCore 2 ↥L).map π) ∣ Nat.card (pPrimeCore 2 ↥L) :=
      Subgroup.card_map_dvd _ _
    rw [hOtop, Subgroup.card_top] at h1
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
  have hord : orderOf (π ⟨v, hvL⟩) = 1 := by
    have h1 : orderOf (π ⟨v, hvL⟩) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [sq, ← map_mul]
      have h2 : (⟨v, hvL⟩ : ↥L) * ⟨v, hvL⟩ = 1 := Subtype.ext hv2
      rw [h2, map_one]
    have h2 : orderOf (π ⟨v, hvL⟩) ∣ Nat.card (↥L ⧸ P') := orderOf_dvd_natCard _
    have h3 : Odd (orderOf (π ⟨v, hvL⟩)) := hodd.of_dvd_nat h2
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h3
      exact absurd h3 (by decide)
  rw [orderOf_eq_one_iff, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hord
  exact hord

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}

theorem false_of_fiveClosure_cover (S : Sig36 X t J 9 e E D) (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) {s : X}
    (hs2 : IsPGroup 2 (zpowers s)) (hsH : s ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hs1 : ρ ⟨s, hHN hsH⟩ ≠ 1) {N : Subgroup X} (hNs : N ≤ centralizer ({s} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({s} : Set X))))
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin 9)) {z : X}
    (hzN : z ∈ normalizer (N : Set X)) (hz2 : z * z = 1)
    (hCz : centralizer ({z} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {L : Subgroup X} {w₀ : X}
    (hgen : ∀ w : X, w ∈ L → w ∈ centralizer ({w₀} : Set X) → w ∈ centralizer ({z} : Set X) →
      w ∈ normalizer (N : Set X))
    {e₁ e₂ : X} (he₁ : e₁ ∈ fiveClosure L w₀ z) (he₂ : e₂ ∈ fiveClosure L w₀ z)
    (he₁2 : e₁ * e₁ = 1) (he₂2 : e₂ * e₂ = 1) (he12 : e₁ * e₂ = e₂ * e₁)
    (hCe : ∀ y : X, y ∈ centralizer ({e₁} : Set X) → y ∈ centralizer ({e₂} : Set X) →
      y ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  obtain ⟨ρN, hρN⟩ := exists_isPermAction (M := N) (by norm_num) (by norm_num) θN
  have hPN : fiveClosure L w₀ z ≤ normalizer (N : Set X) := by
    rw [fiveClosure, closure_le]
    rintro w ⟨hwL, hws, hwz, -⟩
    exact hgen w hwL hws hwz
  have he₁N : e₁ ∈ normalizer (N : Set X) := hPN he₁
  have he₂N : e₂ ∈ normalizer (N : Set X) := hPN he₂
  set ζ := ρN ⟨z, hzN⟩ with hζdef
  have hζ2 : ζ * ζ = 1 := by
    rw [hζdef, ← map_mul]
    have h1 : (⟨z, hzN⟩ : ↥(normalizer (N : Set X))) * ⟨z, hzN⟩ = 1 := Subtype.ext hz2
    rw [h1, map_one]
  have hfive : ∀ T : Subgroup (Perm (Fin 9)),
      (∀ π : Perm (Fin 9), π ^ 5 = 1 → π * ζ = ζ * π → π ∈ T) →
      ∀ y ∈ fiveClosure L w₀ z, ∀ hy : y ∈ normalizer (N : Set X), ρN ⟨y, hy⟩ ∈ T := by
    intro T hT y hy hyN
    have h1 : fiveClosure L w₀ z ≤ (T.comap ρN).map (normalizer (N : Set X)).subtype := by
      rw [fiveClosure, closure_le]
      rintro w ⟨hwL, hws, hwz, j, hwj⟩
      refine ⟨⟨w, hgen w hwL hws hwz⟩, hT _ ?_ ?_, rfl⟩
      · have h2 : (⟨w, hgen w hwL hws hwz⟩ : ↥(normalizer (N : Set X))) ^ 5 ^ j = 1 := by
          apply Subtype.ext
          show w ^ 5 ^ j = 1
          rw [← hwj, pow_orderOf_eq_one]
        exact pow_five_of_pow_five_pow (k := j) (by rw [← map_pow, h2, map_one])
      · rw [hζdef, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.mp hwz)
    obtain ⟨w, hw, hwy⟩ := h1 hy
    have h2 : w = ⟨y, hyN⟩ := Subtype.ext hwy
    rw [← h2]
    exact hw
  set Y : Subgroup X := (N ⊓ centralizer ({z} : Set X)) ⊔
    (N ⊓ centralizer ({e₁} : Set X) ⊓ centralizer ({e₂} : Set X)) with hYdef
  have hYN : Y ≤ N := sup_le inf_le_left (inf_le_left.trans inf_le_left)
  have hYH : Y ≤ H := by
    refine sup_le (inf_le_right.trans hCz) fun y hy => ?_
    rw [mem_inf, mem_inf] at hy
    exact hCe y hy.1.2 hy.2
  have hY₁ : ∀ x : ↥N, (x : X) ∈ centralizer ({z} : Set X) → (x : X) ∈ Y :=
    fun x hx => mem_sup_left (mem_inf.mpr ⟨x.2, hx⟩)
  have hY₂ : ∀ x : ↥N, (x : X) ∈ centralizer ({e₁} : Set X) →
      (x : X) ∈ centralizer ({e₂} : Set X) → (x : X) ∈ Y :=
    fun x hx₁ hx₂ => mem_sup_right (mem_inf.mpr ⟨mem_inf.mpr ⟨x.2, hx₁⟩, hx₂⟩)
  have hcov : ∀ b : alternatingGroup (Fin 9), ∃ x : ↥N, (x : X) ∈ Y ∧
      θN (x : ↥N ⧸ pPrimeCore 2 ↥N) = b := by
    by_cases hζ1 : ζ = 1
    · intro b
      obtain ⟨x, hxz, hxb⟩ := hρN.exists_lift hzN hz2 (b := b)
        (by rw [show ρN ⟨z, hzN⟩ = 1 from hζ1, mul_one, one_mul])
      exact ⟨x, hY₁ x hxz, hxb⟩
    by_cases hF5 : ζ.supportᶜ.card < 5
    · have hv : ∀ y ∈ fiveClosure L w₀ z, ∀ hy : y ∈ normalizer (N : Set X), ρN ⟨y, hy⟩ = 1 :=
        fun y hy hyN => mem_bot.mp (hfive ⊥ (fun π h5 hc =>
          mem_bot.mpr (eq_one_of_pow_five_of_commute hζ2 h5 hc hF5)) y hy hyN)
      intro b
      obtain ⟨x, hx₁, hx₂, hxb⟩ := hρN.exists_lift_of_two_two he₁N
        (isPGroup_zpowers_of_mul_self he₁2) he₂N he₂2 he12 (b := b)
        (by rw [hv e₁ he₁ he₁N, mul_one, one_mul]) (by rw [hv e₂ he₂ he₂N, mul_one, one_mul])
      exact ⟨x, hY₂ x hx₁ hx₂, hxb⟩
    push Not at hF5
    have hG2 : 2 ≤ ζ.support.card := by
      have h1 : ζ.support.card ≠ 0 := fun h => hζ1 (Perm.card_support_eq_zero.mp h)
      have h2 := Perm.card_support_ne_one ζ
      omega
    have hfix : ∀ y ∈ fiveClosure L w₀ z, ∀ hy : y ∈ normalizer (N : Set X),
        ∀ w ∈ ζ.support, ρN ⟨y, hy⟩ w = w := by
      intro y hy hyN w hw
      have h1 := hfive (fixingSubgroup (Perm (Fin 9)) (ζ.support : Set (Fin 9)))
        (fun π h5 hc => by
          rw [mem_fixingSubgroup_iff]
          intro v hv
          rw [Perm.smul_def]
          by_contra hne
          exact Finset.mem_compl.mp
            (support_subset_of_pow_five_of_commute hζ2 h5 hc (Perm.mem_support.mpr hne)) hv)
        y hy hyN
      rw [mem_fixingSubgroup_iff] at h1
      have h2 := h1 w hw
      rwa [Perm.smul_def] at h2
    set v₁ := ρN ⟨e₁, he₁N⟩ with hv₁def
    set v₂ := ρN ⟨e₂, he₂N⟩ with hv₂def
    have hv₁2 : v₁ * v₁ = 1 := by
      rw [hv₁def, ← map_mul]
      have h1 : (⟨e₁, he₁N⟩ : ↥(normalizer (N : Set X))) * ⟨e₁, he₁N⟩ = 1 := Subtype.ext he₁2
      rw [h1, map_one]
    have hv₂2 : v₂ * v₂ = 1 := by
      rw [hv₂def, ← map_mul]
      have h1 : (⟨e₂, he₂N⟩ : ↥(normalizer (N : Set X))) * ⟨e₂, he₂N⟩ = 1 := Subtype.ext he₂2
      rw [h1, map_one]
    have hv12 : v₁ * v₂ = v₂ * v₁ := by
      rw [hv₁def, hv₂def, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext he12
    have hpres : ∀ v : Perm (Fin 9), v * v = 1 → (∀ w ∈ ζ.support, v w = w) →
        ∀ x, v x ∈ ζ.supportᶜ ↔ x ∈ ζ.supportᶜ := by
      intro v hv hvf x
      rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
      constructor
      · intro hx
        have h2 : v (v x) = x := by rw [← Perm.mul_apply, hv, Perm.one_apply]
        rw [hvf _ hx] at h2
        rw [← h2]
        exact hx
      · intro hx
        rw [hvf x hx]
        exact hx
    have hodd : Odd ζ.supportᶜ.card := by
      have h1 : ζ ^ 2 ^ 1 = 1 := by rw [pow_one, sq, hζ2]
      have h2 := Perm.card_compl_support_modEq h1
      rw [Fintype.card_fin] at h2
      have h3 : ζ.supportᶜ.card % 2 = 9 % 2 := h2
      rw [Nat.odd_iff]
      omega
    have hfix₁ := hfix e₁ he₁ he₁N
    have hfix₂ := hfix e₂ he₂ he₂N
    obtain ⟨p, hpF, hp₁, hp₂⟩ := exists_common_fixed_of_odd hodd hv₁2 hv₂2 hv12
      (hpres v₁ hv₁2 hfix₁) (hpres v₂ hv₂2 hfix₂)
    set πN : ↥N →* alternatingGroup (Fin 9) :=
      θN.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥N)) with hπNdef
    set B : Subgroup (Perm (Fin 9)) :=
      ((Y.subgroupOf N).map πN).map (alternatingGroup (Fin 9)).subtype with hBdef
    have hmemB : ∀ (c : Perm (Fin 9)) (hc : c ∈ alternatingGroup (Fin 9)) (x : ↥N),
        (x : X) ∈ Y → θN (x : ↥N ⧸ pPrimeCore 2 ↥N) = ⟨c, hc⟩ → c ∈ B :=
      fun c hc x hxY hxc => ⟨⟨c, hc⟩, ⟨x, mem_subgroupOf.mpr hxY, hxc⟩, rfl⟩
    have hAB : alternatingGroup (Fin 9) ≤ B := by
      refine alternatingGroup_le_of_fix_and_point (G := ζ.support) hG2 (by omega)
        (Finset.mem_compl.mp hpF) ?_ ?_
      · intro u v w huv hvw huw hu hv hw
        obtain ⟨x, hxz, hxb⟩ := hρN.exists_lift hzN hz2
          (b := ⟨_, swap_mul_swap_mem_alternatingGroup huv hvw⟩)
          (swap_mul_swap_commute (Perm.notMem_support.mp hu) (Perm.notMem_support.mp hv)
            (Perm.notMem_support.mp hw))
        exact hmemB _ _ x (hY₁ x hxz) hxb
      · intro u v w huv hvw huw hu hv hw
        have hf : ∀ y, (y ∈ ζ.support ∨ y = p) → v₁ y = y ∧ v₂ y = y := by
          rintro y (hy | rfl)
          · exact ⟨hfix₁ y hy, hfix₂ y hy⟩
          · exact ⟨hp₁, hp₂⟩
        obtain ⟨hu₁, hu₂⟩ := hf u hu
        obtain ⟨hv₁', hv₂'⟩ := hf v hv
        obtain ⟨hw₁, hw₂⟩ := hf w hw
        obtain ⟨x, hx₁, hx₂, hxb⟩ := hρN.exists_lift_of_two_two he₁N
          (isPGroup_zpowers_of_mul_self he₁2) he₂N he₂2 he12
          (b := ⟨_, swap_mul_swap_mem_alternatingGroup huv hvw⟩)
          (swap_mul_swap_commute hu₁ hv₁' hw₁) (swap_mul_swap_commute hu₂ hv₂' hw₂)
        exact hmemB _ _ x (hY₂ x hx₁ hx₂) hxb
    intro b
    obtain ⟨b', ⟨x, hx, hxb'⟩, hb'⟩ := hAB b.2
    refine ⟨x, mem_subgroupOf.mp hx, ?_⟩
    have h1 : b' = b := Subtype.ext hb'
    rw [← h1]
    exact hxb'
  exact S.false_of_cover_of_centralizer_of_isPComponent h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ
    hρ hs2 hsH hs1 hNs hNpc θN hYN hYH (sup_core_eq_of_cover θN hYN hcov)

end Sig36

end CFSG.ComponentClassification.SolMax
