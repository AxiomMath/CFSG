module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L34Cert
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bInputsB
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBTwoFactorImage

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem exists_zpow_conj_eq_of_odd {u c : G} (hu : u * u = 1) (huc : (u * c) * (u * c) = 1)
    (hc : Odd (orderOf c)) : ∃ n : ℤ, (c ^ n)⁻¹ * (u * c) * c ^ n = u := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hucu : u * c * u = c⁻¹ := by
    have h1 : u * c * u * c = 1 := by rw [← huc]; group
    calc u * c * u = u * c * u * c * c⁻¹ := by group
      _ = c⁻¹ := by rw [h1, one_mul]
  have hpow : ∀ j : ℤ, u * c ^ j * u = c ^ (-j) := by
    intro j
    have h1 : u * c ^ j * u⁻¹ = (u * c * u⁻¹) ^ j := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [huinv] at h1
    rw [h1, hucu, inv_zpow']
  obtain ⟨k, hk⟩ := hc
  refine ⟨-((k : ℤ) + 1), ?_⟩
  have e1 : c * c ^ (-((k : ℤ) + 1)) = c ^ (-(k : ℤ)) := by
    rw [← zpow_one_add]
    congr 1
    ring
  have e2 : u * c ^ (-(k : ℤ)) = c ^ (k : ℤ) * u := by
    have h2 := hpow (-(k : ℤ))
    rw [neg_neg] at h2
    calc u * c ^ (-(k : ℤ)) = u * c ^ (-(k : ℤ)) * u * u := by rw [mul_assoc _ u u, hu, mul_one]
      _ = c ^ (k : ℤ) * u := by rw [h2]
  have e3 : c ^ ((k : ℤ) + 1) * c ^ (k : ℤ) = 1 := by
    rw [← zpow_add]
    have h3 : ((k : ℤ) + 1) + k = ((orderOf c : ℕ) : ℤ) := by rw [hk]; push_cast; ring
    rw [h3, zpow_natCast, pow_orderOf_eq_one]
  calc (c ^ (-((k : ℤ) + 1)))⁻¹ * (u * c) * c ^ (-((k : ℤ) + 1)) =
        c ^ ((k : ℤ) + 1) * (u * (c * c ^ (-((k : ℤ) + 1)))) := by
        rw [zpow_neg, inv_inv]
        group
    _ = c ^ ((k : ℤ) + 1) * (u * c ^ (-(k : ℤ))) := by rw [e1]
    _ = c ^ ((k : ℤ) + 1) * (c ^ (k : ℤ) * u) := by rw [e2]
    _ = u := by rw [← mul_assoc, e3, one_mul]

theorem exists_odd_mul_twoPow (c : G) (hc : 0 < orderOf c) :
    ∃ c₁ ∈ zpowers c, ∃ c₂ ∈ zpowers c, c = c₁ * c₂ ∧ Odd (orderOf c₁) ∧
      ∃ n : ℕ, c₂ ^ 2 ^ n = 1 := by
  obtain ⟨e, w, hw, hm⟩ := Nat.exists_eq_two_pow_mul_odd hc.ne'
  have hcop : Nat.Coprime (2 ^ e) w :=
    Nat.Coprime.pow_left e (Nat.prime_two.coprime_iff_not_dvd.2 hw.not_two_dvd_nat)
  have hgcd : Int.gcd (2 ^ e : ℕ) w = 1 := hcop
  set x := Int.gcdA (2 ^ e : ℕ) w
  set y := Int.gcdB (2 ^ e : ℕ) w
  have hxy : ((2 ^ e : ℕ) : ℤ) * x + (w : ℤ) * y = 1 := by
    rw [← Int.gcd_eq_gcd_ab, hgcd]
    rfl
  have hord : c ^ ((orderOf c : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  refine ⟨c ^ ((2 ^ e : ℕ) * x), zpow_mem (mem_zpowers c) _, c ^ ((w : ℤ) * y),
    zpow_mem (mem_zpowers c) _, ?_, ?_, e, ?_⟩
  · rw [← zpow_add, hxy, zpow_one]
  · apply Odd.of_dvd_nat hw
    apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul]
    have : ((2 ^ e : ℕ) : ℤ) * x * (w : ℤ) = ((orderOf c : ℕ) : ℤ) * x := by
      rw [hm]; push_cast; ring
    rw [this, zpow_mul, hord, one_zpow]
  · rw [← zpow_natCast, ← zpow_mul]
    have : (w : ℤ) * y * ((2 ^ e : ℕ) : ℤ) = ((orderOf c : ℕ) : ℤ) * y := by
      rw [hm]; push_cast; ring
    rw [this, zpow_mul, hord, one_zpow]

end General

section Local

variable {H : Type} [Group H]

theorem fixedLayer_commutator_eq (J E : Subgroup H) :
    ⁅GSLit.fixedLayer J E, GSLit.fixedLayer J E⁆ = GSLit.fixedLayer J E := by
  unfold GSLit.fixedLayer
  rw [← Subgroup.map_commutator, UnbalancedCorr.pLayer_two_isPerfect]

theorem commutatorElement_mem_oddCoreIn {K : Subgroup H} {k g : H} (hk : k ∈ K)
    (hg : g ∈ coreActionKernel K) : ⁅k, g⁆ ∈ (pPrimeCore 2 K).map K.subtype := by
  have hg' := inv_mem hg
  rw [mem_coreActionKernel] at hg'
  have h1 := hg'.2 k⁻¹ (inv_mem hk)
  rw [commutatorElement_def]
  convert h1 using 1
  group

variable [Finite H]

theorem odd_orderOf_of_mem_oddCoreIn {K : Subgroup H} {z : H}
    (hz : z ∈ (pPrimeCore 2 K).map K.subtype) : Odd (orderOf z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy, rfl⟩ := hz
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 K)) := pPrimeCore_coprime_card
  have hodd : Odd (Nat.card (pPrimeCore 2 K)) :=
    Nat.odd_iff.2 (by
      rcases Nat.even_or_odd (Nat.card (pPrimeCore 2 K)) with he | ho
      · exact absurd (Nat.Coprime.coprime_dvd_right (even_iff_two_dvd.1 he) hcop)
          (by norm_num)
      · exact Nat.odd_iff.1 ho)
  have h1 : orderOf (y : H) = orderOf (⟨y, hy⟩ : pPrimeCore 2 K) :=
    (Subgroup.orderOf_coe y).trans (Subgroup.orderOf_coe (⟨y, hy⟩ : pPrimeCore 2 K))
  rw [subtype_apply, h1]
  exact Odd.of_dvd_nat hodd (orderOf_dvd_natCard _)

variable (h : Hyp52 H)

theorem mem_fixedLayer_of_mem_D {z : H} (hzD : z ∈ h.D) (hzS : ∀ s ∈ h.S, s * z = z * s)
    (hz2 : orderOf z = 2) : z ∈ GSLit.fixedLayer h.J h.B := by
  rw [GSLit.fixedLayer_eq_closure h.isQuasisimple_J h.B_le_coreActionKernel h.isPGroup_B]
  refine subset_closure ⟨mem_inf.2 ⟨h.D_le_J hzD, ?_⟩, 1, by rw [hz2, pow_one]⟩
  rw [mem_centralizer_iff]
  intro b hb
  exact hzS b (h.B_le_S hb)

theorem fixedLayer_le_K (hKa : conjugate h.K h.a = h.K) : GSLit.fixedLayer h.J h.B ≤ h.K :=
  (B5a.fixedLayer_le_V h).trans (h.V_eq_K hKa).le

theorem fixedLayer_le_centralizer_a : GSLit.fixedLayer h.J h.B ≤ centralizer ({h.a} : Set H) :=
  (GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_left.trans h.J_le)

theorem mem_B_of_mem_coreActionKernel' (hKa : conjugate h.K h.a = h.K) {w : H} (hwW : w ∈ h.W)
    (hwK : w ∈ coreActionKernel h.K) (hw2 : ∃ n : ℕ, w ^ 2 ^ n = 1) : w ∈ h.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBC, R₀, hR₀⟩ := sylowKernelStatement H h
  have hwK' : w ∈ coreActionKernel h.V := by rw [h.V_eq_K hKa]; exact hwK
  have hw2' : IsPGroup 2 (zpowers w) := by
    obtain ⟨n, hn⟩ := hw2
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨n, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hn, one_zpow]
  set X : Subgroup H := zpowers w ⊔ h.B with hX
  have hX2 : IsPGroup 2 X := hw2'.to_sup_of_normal_right' h.isPGroup_B (zpowers_le.mpr hwW)
  have hXC : X ≤ coreActionKernel h.V := sup_le (zpowers_le.mpr hwK') hBC
  obtain ⟨Q, hQ⟩ := (hX2.comap_subtype (K := coreActionKernel h.V)).exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup ↥(coreActionKernel h.V)) = Nat.card h.B := by
    rw [Sylow.card_eq_multiplicity Q, ← Sylow.card_eq_multiplicity R₀, hR₀,
      ← Subgroup.card_map_of_injective (coreActionKernel h.V).subtype_injective,
      subgroupOf_map_subtype, inf_of_le_left hBC]
  have h3 : Nat.card (X.subgroupOf (coreActionKernel h.V)) = Nat.card X := by
    rw [← Subgroup.card_map_of_injective (coreActionKernel h.V).subtype_injective,
      subgroupOf_map_subtype, inf_of_le_left hXC]
  have hcard : Nat.card X ≤ Nat.card h.B := by
    rw [← h3, ← hQcard]
    exact Subgroup.card_le_of_le hQ
  have hXB : h.B = X := eq_of_le_of_card_ge le_sup_right hcard
  rw [hXB]
  exact mem_sup_left (mem_zpowers w)

omit [Finite H] in
theorem oddBarConj_mk_eq_conj (K : Subgroup H) {k : H} (hk : k ∈ K)
    (hkN : k ∈ normalizer (K : Set H)) :
    oddBarConj K ⟨k, hkN⟩ = MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : OddBar K) := by
  ext x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem inducedHom_conj {Y : Type*} [Group Y] (y : Y) :
    GH74.KGroups.inducedHom (MulAut.conj y) = MulAut.conj (QuotientGroup.mk y : Y ⧸ center Y) := by
  ext x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem congr_conj {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z) (y : Y) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext x
  simp [MulAut.congr_apply]

theorem cfProp23L34 : CFProp23L34 := by
  intro H _ _ h hrow z hzD hzS hz2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hKa, -, hL34⟩ := hrow
  have hzJB := mem_fixedLayer_of_mem_D h hzD hzS hz2
  have hJBK := fixedLayer_le_K h hKa
  have hzK : z ∈ h.K := hJBK hzJB
  have haN : h.a ∈ normalizer (h.K : Set H) := mem_normalizer_of_conjugate_eq hKa
  have hKN : h.K ≤ normalizer (h.K : Set H) := le_normalizer
  have hza : z * h.a = h.a * z := h.comm_a (h.D_le_S hzD)
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzodd : ¬ Odd (orderOf z) := by rw [hz2]; decide
  have hperf : Group.IsPerfect (OddBar h.K) := h.isQuasisimple_K.1
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hLie : Blueprint.LieModel ((OddBar h.K) ⧸ center (OddBar h.K)) .PSL 3 2 2 :=
    lieModel_of_mulEquiv_ne_zero eZ.symm (by norm_num) hL34
  obtain ⟨ψ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hLie
  obtain ⟨eR, heR, -⟩ := PSL3Four.full_automorphism_action
  set F : MulAut (OddBar h.K) →* PSL3Four.R :=
    eR.symm.toMonoidHom.comp ((MulAut.congr ψ).toMonoidHom.comp GH74.KGroups.inducedHom)
    with hF
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply GH74.KGroups.inducedHom_injective hperf
    apply (MulAut.congr ψ).injective
    exact eR.symm.injective hxy
  set ρ : ↥(normalizer (h.K : Set H)) →* PSL3Four.R := F.comp (oddBarConj h.K) with hρ
  have hρker : ∀ w, ρ w = 1 → (w : H) ∈ coreActionKernel h.K := by
    intro w hw
    apply mem_coreActionKernel_of_oddBarConj_eq_one
    apply hFinj
    rw [map_one]
    exact hw
  set sK : ↥h.K → PSL3Four.S := fun k =>
    ψ (QuotientGroup.mk (QuotientGroup.mk k : OddBar h.K)) with hsK
  have hρK : ∀ (k : H) (hk : k ∈ h.K),
      ((ρ ⟨k, hKN hk⟩ : PSL3Four.R) : Equiv.Perm (Fin 42)) =
        (sK ⟨k, hk⟩ : Equiv.Perm (Fin 42)) := by
    intro k hk
    have hcon : eR ⟨(sK ⟨k, hk⟩ : Equiv.Perm (Fin 42)), PSL3Four.S_le_R (sK ⟨k, hk⟩).2⟩ =
        MulAut.conj (sK ⟨k, hk⟩) := by
      ext t
      rw [heR]
      rfl
    have h1 : ρ ⟨k, hKN hk⟩ =
        ⟨(sK ⟨k, hk⟩ : Equiv.Perm (Fin 42)), PSL3Four.S_le_R (sK ⟨k, hk⟩).2⟩ := by
      apply eR.injective
      rw [hcon]
      simp only [hρ, hF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
      rw [oddBarConj_mk_eq_conj h.K hk, inducedHom_conj, congr_conj]
    rw [h1]
  have hρKS : ∀ (k : H) (hk : k ∈ h.K),
      ((ρ ⟨k, hKN hk⟩ : PSL3Four.R) : Equiv.Perm (Fin 42)) ∈ PSL3Four.S := fun k hk => by
    rw [hρK k hk]
    exact (sK ⟨k, hk⟩).2
  have hρsurj : ∀ s ∈ PSL3Four.S, ∃ (k : H) (hk : k ∈ h.K),
      ((ρ ⟨k, hKN hk⟩ : PSL3Four.R) : Equiv.Perm (Fin 42)) = s := by
    intro s hs
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ψ.symm ⟨s, hs⟩)
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨k, k.2, ?_⟩
    rw [hρK k k.2]
    have : sK ⟨(k : H), k.2⟩ = ⟨s, hs⟩ := by
      simp only [hsK]
      rw [show (⟨(k : H), k.2⟩ : ↥h.K) = k from rfl, hx, MulEquiv.apply_symm_apply]
    rw [this]
  set r : PSL3Four.R := ρ ⟨h.a, haN⟩ with hr
  have hr2 : (r : Equiv.Perm (Fin 42)) * r = 1 := by
    rw [← Subgroup.coe_mul, hr, ← map_mul]
    have : (⟨h.a, haN⟩ : ↥(normalizer (h.K : Set H))) * ⟨h.a, haN⟩ = 1 := Subtype.ext ha2
    rw [this, map_one, Subgroup.coe_one]
  set zr : PSL3Four.R := ρ ⟨z, hKN hzK⟩ with hzr
  have hzrS : (zr : Equiv.Perm (Fin 42)) ∈ PSL3Four.S := hρKS z hzK
  have hzr2 : (zr : Equiv.Perm (Fin 42)) * zr = 1 := by
    rw [← Subgroup.coe_mul, hzr, ← map_mul]
    have : (⟨z, hKN hzK⟩ : ↥(normalizer (h.K : Set H))) * ⟨z, hKN hzK⟩ = 1 := Subtype.ext hz2'
    rw [this, map_one, Subgroup.coe_one]
  have hrz : (r : Equiv.Perm (Fin 42)) * zr = zr * r := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hr, hzr, ← map_mul, ← map_mul]
    have : (⟨h.a, haN⟩ : ↥(normalizer (h.K : Set H))) * ⟨z, hKN hzK⟩ =
        ⟨z, hKN hzK⟩ * ⟨h.a, haN⟩ := Subtype.ext hza.symm
    rw [this]
  have hrS : (r : Equiv.Perm (Fin 42)) ∉ PSL3Four.S := by
    intro hrS
    by_cases hr1 : (r : Equiv.Perm (Fin 42)) = 1
    ·
      have haK : h.a ∈ coreActionKernel h.K := hρker ⟨h.a, haN⟩ (Subtype.ext hr1)
      have hle : ⁅h.K, zpowers h.a⁆ ≤ (pPrimeCore 2 h.K).map h.K.subtype := by
        rw [commutator_le]
        intro k hk g hg
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
        exact commutatorElement_mem_oddCoreIn hk (zpow_mem haK n)
      have hcomm := h.commutator_eq
      have hV : layerIn (normalizer (h.B : Set H)) = h.K := h.V_eq_K hKa
      rw [hV] at hcomm
      have hzc : z ∈ ⁅h.K, zpowers h.a⁆ := by rw [hcomm]; exact hzK
      exact hzodd (odd_orderOf_of_mem_oddCoreIn (hle hzc))
    ·
      have hJBN : GSLit.fixedLayer h.J h.B ≤ normalizer (h.K : Set H) := hJBK.trans hKN
      set φ : ↥(GSLit.fixedLayer h.J h.B) →* Equiv.Perm (Fin 42) :=
        PSL3Four.R.subtype.comp (ρ.comp (Subgroup.inclusion hJBN)) with hφ
      have hperfJ : Group.IsPerfect ↥(GSLit.fixedLayer h.J h.B) :=
        UnbalancedGS.isPerfect_of_commutator_eq (fixedLayer_commutator_eq _ _)
      have hX : ⁅φ.range, φ.range⁆ = φ.range :=
        UnbalancedGS.commutator_range_eq_of_perfect hperfJ φ
      have hXle : φ.range ≤ centralizer {(r : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S := by
        rintro _ ⟨j, rfl⟩
        have hjK : (j : H) ∈ h.K := hJBK j.2
        have hja : (j : H) * h.a = h.a * j :=
          mem_centralizer_singleton_iff.mp (fixedLayer_le_centralizer_a h j.2)
        refine mem_inf.2 ⟨?_, ?_⟩
        · rw [mem_centralizer_singleton_iff]
          show ((ρ ⟨j, hJBN j.2⟩ : PSL3Four.R) : Equiv.Perm (Fin 42)) * r =
            r * (ρ ⟨j, hJBN j.2⟩ : PSL3Four.R)
          rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hr, ← map_mul, ← map_mul]
          have : (⟨j, hJBN j.2⟩ : ↥(normalizer (h.K : Set H))) * ⟨h.a, haN⟩ =
              ⟨h.a, haN⟩ * ⟨j, hJBN j.2⟩ := Subtype.ext hja
          rw [this]
        · exact hρKS j hjK
      have hbot := eq_bot_of_le_centralizer hrS hr2 hr1 hXle hX
      have hJBC : ∀ j ∈ GSLit.fixedLayer h.J h.B, j ∈ coreActionKernel h.K := by
        intro j hj
        apply hρker ⟨j, hJBN hj⟩
        apply Subtype.ext
        have : φ ⟨j, hj⟩ ∈ φ.range := ⟨_, rfl⟩
        rw [hbot, mem_bot] at this
        exact this
      have hle : ⁅GSLit.fixedLayer h.J h.B, GSLit.fixedLayer h.J h.B⁆ ≤
          (pPrimeCore 2 h.K).map h.K.subtype := by
        rw [commutator_le]
        intro j₁ hj₁ j₂ hj₂
        exact commutatorElement_mem_oddCoreIn (hJBK hj₁) (hJBC j₂ hj₂)
      rw [fixedLayer_commutator_eq] at hle
      exact hzodd (odd_orderOf_of_mem_oddCoreIn (hle hzJB))
  have hr1 : (r : Equiv.Perm (Fin 42)) ≠ 1 := fun h1 => hrS (h1 ▸ one_mem _)
  have hrz1 : (r : Equiv.Perm (Fin 42)) * zr ≠ 1 := by
    intro h1
    apply hrS
    have : (r : Equiv.Perm (Fin 42)) = (zr : Equiv.Perm (Fin 42))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_mem hzrS
  have hrz2 : (r : Equiv.Perm (Fin 42)) * zr * (r * zr) = 1 := by
    calc (r : Equiv.Perm (Fin 42)) * zr * (r * zr) = r * (zr * r) * zr := by group
      _ = r * (r * zr) * zr := by rw [hrz]
      _ = (r * r) * (zr * zr) := by group
      _ = 1 := by rw [hr2, hzr2, one_mul]
  obtain ⟨y, hyS, hy⟩ := conj_of_mul_mem_S r.2 (mul_mem r.2 zr.2) hr2 hrz2 hr1 hrz1
    (by rw [inv_mul_cancel_left]; exact hzrS)
  obtain ⟨g₁, hg₁K, hg₁⟩ := hρsurj y hyS
  set c := (h.a * z)⁻¹ * (g₁ * h.a * g₁⁻¹) with hc
  have hcN : c ∈ normalizer (h.K : Set H) :=
    mul_mem (inv_mem (mul_mem haN (hKN hzK)))
      (mul_mem (mul_mem (hKN hg₁K) haN) (inv_mem (hKN hg₁K)))
  have hcker : c ∈ coreActionKernel h.K := by
    apply hρker ⟨c, hcN⟩
    have e1 : (⟨c, hcN⟩ : ↥(normalizer (h.K : Set H))) =
        (⟨h.a, haN⟩ * ⟨z, hKN hzK⟩)⁻¹ * (⟨g₁, hKN hg₁K⟩ * ⟨h.a, haN⟩ * ⟨g₁, hKN hg₁K⟩⁻¹) :=
      Subtype.ext rfl
    rw [e1, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [hg₁, ← hr, ← hzr, ← hy]
    group
  have hcK : c ∈ h.K := by
    have e2 : c = z⁻¹ * (h.a⁻¹ * g₁ * h.a) * g₁⁻¹ := by rw [hc]; group
    rw [e2]
    refine mul_mem (mul_mem (inv_mem hzK) ?_) (inv_mem hg₁K)
    have := (mem_normalizer_iff.mp (inv_mem haN) g₁).mp hg₁K
    simpa using this
  obtain ⟨c₁, hc₁, c₂, hc₂, hcc, hc₁odd, n₂, hn₂⟩ :=
    exists_odd_mul_twoPow c (orderOf_pos c)
  have hzpK : zpowers c ≤ h.K := zpowers_le.mpr hcK
  have hKW : h.K ≤ h.W := h.isPComponent_K.1
  have hc₂B : c₂ ∈ h.B :=
    mem_B_of_mem_coreActionKernel' h hKa (hKW (hzpK hc₂))
      ((zpowers_le.mpr hcker) hc₂) ⟨n₂, hn₂⟩
  have hBn : (h.B.subgroupOf h.W).Normal := Subgroup.normal_in_normalizer
  set π : ↥h.W →* ↥h.W ⧸ h.B.subgroupOf h.W := QuotientGroup.mk' _ with hπ
  have haW : h.a ∈ h.W := h.a_mem_normalizer
  have hzW : z ∈ h.W := hKW hzK
  have hg₁W : g₁ ∈ h.W := hKW hg₁K
  have hc₁W : c₁ ∈ h.W := hKW (hzpK hc₁)
  have hc₂W : c₂ ∈ h.W := hKW (hzpK hc₂)
  set u : ↥h.W ⧸ h.B.subgroupOf h.W := π ⟨h.a * z, mul_mem haW hzW⟩ with hu
  set cc : ↥h.W ⧸ h.B.subgroupOf h.W := π ⟨c₁, hc₁W⟩ with hcc'
  have hc₂1 : π ⟨c₂, hc₂W⟩ = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hc₂B
  have hconjW : g₁ * h.a * g₁⁻¹ ∈ h.W := mul_mem (mul_mem hg₁W haW) (inv_mem hg₁W)
  have htu : π ⟨g₁ * h.a * g₁⁻¹, hconjW⟩ = u * cc := by
    have e3 : (⟨g₁ * h.a * g₁⁻¹, hconjW⟩ : ↥h.W) =
        ⟨h.a * z, mul_mem haW hzW⟩ * ⟨c₁, hc₁W⟩ * ⟨c₂, hc₂W⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [show h.a * z * c₁ * c₂ = h.a * z * (c₁ * c₂) by group, ← hcc, hc]
      group
    rw [e3, map_mul, map_mul, hc₂1, mul_one]
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul, ← map_one π]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    calc h.a * z * (h.a * z) = h.a * (z * h.a) * z := by group
      _ = h.a * (h.a * z) * z := by rw [hza]
      _ = (h.a * h.a) * (z * z) := by group
      _ = 1 := by rw [ha2, hz2', one_mul]
  have hucc2 : u * cc * (u * cc) = 1 := by
    rw [← htu, ← map_mul, ← map_one π]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    calc g₁ * h.a * g₁⁻¹ * (g₁ * h.a * g₁⁻¹) = g₁ * (h.a * h.a) * g₁⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hc₁odd' : Odd (orderOf (⟨c₁, hc₁W⟩ : ↥h.W)) := by rwa [Subgroup.orderOf_mk]
  have hccodd : Odd (orderOf cc) := Odd.of_dvd_nat hc₁odd' (orderOf_map_dvd π _)
  obtain ⟨n, hn⟩ := exists_zpow_conj_eq_of_odd hu2 hucc2 hccodd
  set o : H := c₁ ^ n with ho
  have hoW : o ∈ h.W := zpow_mem hc₁W n
  have hoK : o ∈ h.K := hzpK (zpow_mem hc₁ n)
  have hπo : π ⟨o, hoW⟩ = cc ^ n := by
    rw [hcc', ← map_zpow]
    rfl
  have hX'W : o⁻¹ * (g₁ * h.a * g₁⁻¹) * o ∈ h.W := mul_mem (mul_mem (inv_mem hoW) hconjW) hoW
  have hfin : π ⟨o⁻¹ * (g₁ * h.a * g₁⁻¹) * o, hX'W⟩ = u := by
    have e4 : (⟨o⁻¹ * (g₁ * h.a * g₁⁻¹) * o, hX'W⟩ : ↥h.W) =
        (⟨o, hoW⟩ : ↥h.W)⁻¹ * ⟨g₁ * h.a * g₁⁻¹, hconjW⟩ * ⟨o, hoW⟩ := Subtype.ext rfl
    rw [e4, map_mul, map_mul, map_inv, hπo, htu, hn]
  have hyB : (h.a * z)⁻¹ * (o⁻¹ * (g₁ * h.a * g₁⁻¹) * o) ∈ h.B := by
    have h5 := QuotientGroup.eq.mp hfin.symm
    simpa [mem_subgroupOf] using h5
  refine ⟨g₁⁻¹ * o, mul_mem (inv_mem hg₁K) hoK, _, hyB, ?_⟩
  group

end Local

end CFSG.ComponentClassification.CatFactsL4U4
