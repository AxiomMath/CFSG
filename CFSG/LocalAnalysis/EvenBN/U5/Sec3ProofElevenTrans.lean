module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Nine
public import CFSG.LocalAnalysis.EvenBN.Common.NaturalModuleBridge

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.Timmesfeld
open scoped MatrixGroups

section S311aAbstract

variable {G' : Type*} [Group G'] [Finite G'] {k₂ : Type} [Field k₂] [Finite k₂]

theorem s311a_torus {n : ℕ} (hk : Nat.card k₂ = 2 ^ n) (hn : 1 ≤ n) {X P' : Subgroup G'}
    (ψ : X ≃* SL(2, k₂)) (hP : IsSylowOf 2 P' X) :
    ∃ J : Subgroup G', J ≤ X ∧ J ≤ normalizer (P' : Set G') ∧ Nat.card J = 2 ^ n - 1 := by
  obtain ⟨x, hx, hPx⟩ := Prelim.exists_conj_of_isSylowOf
    (Prelim.isSylowOf_ofSL_upperUnipotent hk hn ψ) hP
  have hnorm : ∀ t ∈ Prelim.ofSL ψ (Common.torusSL k₂), ∀ r ∈ Prelim.ofSL ψ (upperUnipotent k₂),
      t * r * t⁻¹ ∈ Prelim.ofSL ψ (upperUnipotent k₂) := by
    intro t ht r hr
    obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := ht
    obtain ⟨μ, rfl⟩ := Common.mem_torusSL_iff.1 hs
    have h10 : ((Common.diagSL μ : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) 1 0 = 0 := by
      simp [Common.coe_diagSL]
    have hm := Prelim.ofSL_map_conj ψ (upperUnipotent k₂) (ψ.symm (Common.diagSL μ))
    rw [MulEquiv.apply_symm_apply, Prelim.map_conj_upperUnipotent_of_eq_zero h10] at hm
    have : (ψ.symm (Common.diagSL μ) : G') * r * (ψ.symm (Common.diagSL μ) : G')⁻¹ ∈
        (Prelim.ofSL ψ (upperUnipotent k₂)).map (MulAut.conj (ψ.symm (Common.diagSL μ) : G')).toMonoidHom :=
      ⟨r, hr, by simp [MulAut.conj_apply]⟩
    rw [← hm] at this
    exact this
  refine ⟨(Prelim.ofSL ψ (Common.torusSL k₂)).map (MulAut.conj x).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact X.mul_mem (X.mul_mem hx (Prelim.ofSL_le ψ _ ht)) (X.inv_mem hx)
  · rintro _ ⟨t, ht, rfl⟩
    refine mem_normalizer_fintype fun p hp => ?_
    rw [hPx] at hp ⊢
    obtain ⟨r, hr, rfl⟩ := hp
    refine ⟨t * r * t⁻¹, hnorm t ht r hr, ?_⟩
    simp [MulAut.conj_apply]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, Prelim.card_ofSL,
      Common.card_torusSL, hk]

theorem s311a_abstract {n : ℕ} (hk : Nat.card k₂ = 2 ^ n) (hn : 2 ≤ n)
    {X V P' Q' : Subgroup G'} (ψ : X ≃* SL(2, k₂))
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hXV : X ≤ normalizer (V : Set G'))
    (hcard : Nat.card V = (2 ^ n) ^ 2) (hnc : ¬ X ≤ centralizer (V : Set G'))
    (hP : IsSylowOf 2 P' X) (hQV : Q' ≤ V) (hQP : Q' ≤ centralizer (P' : Set G'))
    (hQcard : Nat.card Q' = 2 ^ n) :
    ∃ J : Subgroup G', J ≤ X ∧ J ≤ normalizer (P' : Set G') ∧ Nat.card J = 2 ^ n - 1 ∧
      ∀ x ∈ V, x ∉ Q' → ∀ y ∈ V, y ∉ Q' → ∃ j ∈ J, (j * x * j⁻¹) * y⁻¹ ∈ Q' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP k₂ 2 := U4.charP_two_of_card hk
  have hPX : P' ≤ X := hP.le
  have hPcard : Nat.card P' = Nat.card k₂ := by
    rw [hk]; exact Prelim.card_of_isSylowOf hk (by omega) ψ hP
  have hfixP : 2 ^ n ≤ Nat.card (V ⊓ centralizer (P' : Set G') : Subgroup G') := by
    rw [← hQcard]
    exact Subgroup.card_le_of_le (le_inf hQV hQP)
  obtain ⟨-, hVc, hVtrans, hVstab, -⟩ :=
    Common.natural_module_of_card_le hk hn ψ hcomm hXV hcard hnc hPX hPcard hfixP
  have hQeq : Q' = V ⊓ centralizer (P' : Set G') := by
    refine Subgroup.eq_of_le_of_card_ge (le_inf hQV hQP) ?_
    rw [hVc, hQcard]
  obtain ⟨J, hJX, hJP, hJcard⟩ := s311a_torus hk (by omega) ψ hP
  have hJodd : Odd (Nat.card J) := by
    rw [hJcard, ← hk]; exact Common.odd_card_sub_one
  have hcop2 : ∀ {o : ℕ}, Odd o → ∀ m : ℕ, Nat.Coprime o (2 ^ m) := fun {o} ho m =>
    Nat.Coprime.pow_right m (Nat.coprime_two_left.2 ho).symm
  have hfix : ∀ j ∈ J, j ≠ 1 → ∀ v ∈ V, j * v = v * j → v = 1 := by
    intro j hj hj1 v hv hjv
    by_contra hv1
    have hpos : 1 < Nat.card (V ⊓ centralizer (P' : Set G') : Subgroup G') := by
      rw [hVc]; exact Nat.one_lt_two_pow (by omega)
    obtain ⟨a, haV, ha1⟩ : ∃ a ∈ V ⊓ centralizer (P' : Set G'), a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hb : (V ⊓ centralizer (P' : Set G')) = ⊥ :=
        eq_bot_iff.2 fun z hz => Subgroup.mem_bot.2 (hcon z hz)
      rw [hb, Subgroup.card_bot] at hpos
      omega
    obtain ⟨x, hx, hxa⟩ := hVtrans a (Subgroup.mem_inf.1 haV).1 v hv ha1 hv1
    have hjX : x⁻¹ * j * x ∈ X ⊓ centralizer ({a} : Set G') := by
      refine Subgroup.mem_inf.2 ⟨X.mul_mem (X.mul_mem (X.inv_mem hx) (hJX hj)) hx,
        mem_centralizer_singleton_iff.2 ?_⟩
      have e : a = x⁻¹ * v * x := by rw [← hxa]; group
      rw [e]
      calc x⁻¹ * j * x * (x⁻¹ * v * x) = x⁻¹ * (j * v) * x := by group
        _ = x⁻¹ * (v * j) * x := by rw [hjv]
        _ = x⁻¹ * v * x * (x⁻¹ * j * x) := by group
    rw [hVstab a haV ha1] at hjX
    have h2 : orderOf (x⁻¹ * j * x) ∣ 2 ^ n := by
      have := Subgroup.orderOf_dvd_natCard P' hjX
      rwa [hPcard, hk] at this
    have h3 : orderOf (x⁻¹ * j * x) = orderOf j := by
      have := orderOf_injective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective j
      simpa [MulAut.conj_apply] using this
    rw [h3] at h2
    have h4 : orderOf j ∣ 2 ^ n - 1 := by
      have := Subgroup.orderOf_dvd_natCard J hj
      rwa [hJcard] at this
    have hodd : Odd (2 ^ n - 1) := by rw [← hk]; exact Common.odd_card_sub_one
    have h5 : Nat.Coprime (2 ^ n - 1) (2 ^ n) := hcop2 hodd n
    have h6 : orderOf j = 1 :=
      Nat.eq_one_of_dvd_coprimes h5.symm h2 h4
    exact hj1 (orderOf_eq_one_iff.1 h6)
  have hJV : J ≤ normalizer (V : Set G') := hJX.trans hXV
  have hJQ : J ≤ normalizer (Q' : Set G') := by
    rw [hQeq]
    intro j hj
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.1 hz
    refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hJV hj) z).1 hzV,
      mem_centralizer_iff.2 fun p hp => ?_⟩
    have hp' : j⁻¹ * p * j ∈ P' := by
      have := (mem_normalizer_iff.1 (inv_mem (hJP hj)) p).1 hp
      simpa using this
    have h1 := mem_centralizer_iff.1 hzC _ hp'
    calc p * (j * z * j⁻¹) = j * ((j⁻¹ * p * j) * z) * j⁻¹ := by group
      _ = j * (z * (j⁻¹ * p * j)) * j⁻¹ := by rw [h1]
      _ = (j * z * j⁻¹) * p := by group
  have hsolv : Group.IsSolvable V := isSolvable_of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2)
  have hVNQ : V ≤ normalizer (Q' : Set G') := by
    intro v hv
    refine mem_normalizer_fintype fun z hz => ?_
    have hvz : v * z * v⁻¹ = z := by
      have := hcomm v hv z (hQV hz)
      calc v * z * v⁻¹ = z * v * v⁻¹ := by rw [this]
        _ = z := by group
    rw [hvz]; exact hz
  have hsemireg : ∀ s ∈ J, ∀ x ∈ V, x⁻¹ * (s * x * s⁻¹) ∈ Q' → s = 1 ∨ x ∈ Q' := by
    intro s hs x hx hsx
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    · right
      have hpow : ∀ i : ℕ, x⁻¹ * (s ^ i * x * (s ^ i)⁻¹) ∈ Q' := by
        intro i
        induction i with
        | zero => simp
        | succ i ih =>
          have e : x⁻¹ * (s ^ (i + 1) * x * (s ^ (i + 1))⁻¹) =
              (x⁻¹ * (s * x * s⁻¹)) * (s * (x⁻¹ * (s ^ i * x * (s ^ i)⁻¹)) * s⁻¹) := by
            group
          rw [e]
          exact mul_mem hsx ((mem_normalizer_iff.1 (hJQ hs) _).1 ih)
      have hzp : ∀ t ∈ Subgroup.zpowers s, x⁻¹ * (t * x * t⁻¹) ∈ Q' := by
        intro t ht
        obtain ⟨i, rfl⟩ := mem_powers_iff_mem_zpowers.2 ht
        exact hpow i
      have hSM : Subgroup.zpowers s ≤ normalizer (V : Set G') := Subgroup.zpowers_le.2 (hJV hs)
      have hSN : Subgroup.zpowers s ≤ normalizer (Q' : Set G') := Subgroup.zpowers_le.2 (hJQ hs)
      have hodd : Odd (orderOf s) := Odd.of_dvd_nat hJodd (Subgroup.orderOf_dvd_natCard J hs)
      have hcop : (Nat.card (Subgroup.zpowers s)).Coprime (Nat.card V) := by
        rw [Nat.card_zpowers, hcard]
        exact Nat.Coprime.pow_right 2 (hcop2 hodd n)
      obtain ⟨c, hc, n', hn', hxc⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime hQV hVNQ
        hSM hSN hsolv hcop hx hzp
      have hcV := (Subgroup.mem_inf.1 hc).1
      have hcs : s * c = c * s :=
        mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 s (Subgroup.mem_zpowers s)
      have hc1 : c = 1 := hfix s hs hs1 c hcV hcs
      rw [hxc, hc1, one_mul]
      exact hn'
  haveI hQn : (Q'.subgroupOf V).Normal := ⟨fun z hz g => by
    have hc : (g : G') * z * (g : G')⁻¹ = z := by
      have := hcomm g g.2 z z.2
      calc (g : G') * z * (g : G')⁻¹ = z * g * (g : G')⁻¹ := by rw [this]
        _ = z := by group
    rw [mem_subgroupOf] at hz ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc]; exact hz⟩
  have hCcard : Nat.card (↥V ⧸ Q'.subgroupOf V) = 2 ^ n := by
    have h1 := Subgroup.card_mul_index (Q'.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQV).toEquiv, hQcard, hcard] at h1
    have hpos : 0 < 2 ^ n := by positivity
    have : (Q'.subgroupOf V).index = 2 ^ n := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [h1, sq]
    rw [← Subgroup.index_eq_card]
    exact this
  refine ⟨J, hJX, hJP, hJcard, ?_⟩
  intro x hx hxQ y hy hyQ
  let f : J → (↥V ⧸ Q'.subgroupOf V) := fun j =>
    QuotientGroup.mk ⟨(j : G') * x * (j : G')⁻¹, (mem_normalizer_iff.1 (hJV j.2) x).1 hx⟩
  have hconj : ∀ (j : J) (z : G'), (j : G') * z * (j : G')⁻¹ ∈ Q' → z ∈ Q' := by
    intro j z hz
    have := (mem_normalizer_iff.1 (inv_mem (hJQ j.2)) _).1 hz
    simpa [mul_assoc] using this
  have hf_ne : ∀ j, f j ≠ 1 := by
    intro j h1
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    exact hxQ (hconj j x (mem_subgroupOf.1 h2))
  have hf_inj : Function.Injective f := by
    intro j j' hjj'
    have h1 := mem_subgroupOf.1 (QuotientGroup.eq.1 hjj')
    have h1' := (mem_normalizer_iff.1 (inv_mem (hJQ j.2)) _).1 h1
    have h2 : x⁻¹ * (((j : G')⁻¹ * (j' : G')) * x * ((j : G')⁻¹ * (j' : G'))⁻¹) ∈ Q' := by
      convert h1' using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rcases hsemireg _ (J.mul_mem (J.inv_mem j.2) j'.2) x hx h2 with hs | hs
    · exact Subtype.ext (inv_mul_eq_one.1 hs)
    · exact absurd hs hxQ
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype (↥V ⧸ Q'.subgroupOf V) := Fintype.ofFinite _
  have hS₁card : (Finset.univ.image f).card = 2 ^ n - 1 := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, ← Nat.card_eq_fintype_card,
      hJcard]
  have hsub : Finset.univ.image f ⊆ Finset.univ.erase 1 := by
    intro c hc
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_erase.2 ⟨hf_ne j, Finset.mem_univ _⟩
  have hE : (Finset.univ.erase (1 : ↥V ⧸ Q'.subgroupOf V)).card = 2 ^ n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hCcard]
  have hEq : Finset.univ.image f = Finset.univ.erase 1 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hS₁card, hE])
  have hyC : (QuotientGroup.mk ⟨y, hy⟩ : ↥V ⧸ Q'.subgroupOf V) ∈ Finset.univ.erase 1 := by
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    intro h1
    exact hyQ (mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1))
  rw [← hEq] at hyC
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hyC
  refine ⟨j, j.2, ?_⟩
  have h1 := mem_subgroupOf.1 (QuotientGroup.eq.1 hj)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  have hy' : y ∈ V := hy
  have hjx : (j : G') * x * (j : G')⁻¹ ∈ V := (mem_normalizer_iff.1 (hJV j.2) x).1 hx
  have hcm : y * ((j : G') * x * (j : G')⁻¹) = ((j : G') * x * (j : G')⁻¹) * y := hcomm y hy' _ hjx
  have e : (j : G') * x * (j : G')⁻¹ * y⁻¹ = (((j : G') * x * (j : G')⁻¹)⁻¹ * y)⁻¹ := by
    calc (j : G') * x * (j : G')⁻¹ * y⁻¹
        = y⁻¹ * (y * ((j : G') * x * (j : G')⁻¹)) * y⁻¹ := by group
      _ = y⁻¹ * (((j : G') * x * (j : G')⁻¹) * y) * y⁻¹ := by rw [hcm]
      _ = (((j : G') * x * (j : G')⁻¹)⁻¹ * y)⁻¹ := by group
  rw [e]
  exact inv_mem h1

end S311aAbstract

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

section S311aFacts

variable (hp : d.CaseHyp) (k : d.Know10) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
  (hP : d.P ≤ S)
include hp k hS hP

theorem s311a_D_le_S : d.D ≤ S := (k.s9_1 S hS hP).1.symm ▸ le_sup_right

theorem s311a_E_le_S : d.E ≤ S := (k.s9_1 S hS hP).1.symm ▸ le_sup_left

theorem s311a_S_le_N_D : S ≤ normalizer (d.D : Set G) := by
  haveI : (d.D.subgroupOf S).Characteristic := (k.s9_1 S hS hP).2.2
  haveI : (d.D.subgroupOf S).Normal := inferInstance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (s311a_D_le_S hp k hS hP)).1 inferInstance

theorem s311a_F_le_D : d.F ≤ d.D := by
  have h := (k.s9_2 S hS hP).2.2.2.1
  rw [← h]
  exact inf_le_left

theorem s311a_N_D_le_N_F : normalizer (d.D : Set G) ≤ normalizer (d.F : Set G) := by
  have h := (k.s9_2 S hS hP).2.2.2.1
  rw [← h]
  exact normalizer_le_normalizer_centerIn d.D

theorem s311a_S_le_N_F : S ≤ normalizer (d.F : Set G) :=
  (s311a_S_le_N_D hp k hS hP).trans (s311a_N_D_le_N_F hp k hS hP)

theorem s311a_M₁_le_N_D : d.M₁ ≤ normalizer (d.D : Set G) := by
  have h1 : d.M₁ ≤ d.L₁ := by rw [k.s9_3.1]; exact le_sup_right
  exact h1.trans (hp.hyp.L₁_le_normalizer_D)

theorem s311a_M₁_le_N_F : d.M₁ ≤ normalizer (d.F : Set G) :=
  (s311a_M₁_le_N_D hp k hS hP).trans (s311a_N_D_le_N_F hp k hS hP)

theorem s311a_M₁_inf_D : d.M₁ ⊓ d.D = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : z ∈ d.D ⊓ centralizer (d.I₁ : Set G) :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hz).2, d.M₁_le_centralizer_I₁ (Subgroup.mem_inf.1 hz).1⟩
  rw [k.s9e.centralizer_I₁] at hz'
  exact hz'

theorem s311a_R_sylow : IsSylowOf 2 (S ⊓ d.M₁) d.M₁ := (k.s10_2 S hS hP).1.2

theorem s311a_S_eq : S = d.D ⊔ (S ⊓ d.M₁) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨h12, -⟩⟩ := k.s10_1 S hS hP
  rw [← (k.s10_2 S hS hP).1.1]
  exact h12

theorem s311a_card_Q : Nat.card ((d.E ⊓ d.D) ⊔ d.F : Subgroup G) = (2 ^ f) ^ 12 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -, -⟩ := k.s10_1 S hS hP
  have hQ : (d.E ⊓ d.D) ⊔ d.F = d.F ⊔ (S ⊓ centralizer (d.I₅ : Set G)) := by
    rw [sup_comm]; exact h10
  rw [hQ]
  have hFS : d.F ≤ S := (s311a_F_le_D hp k hS hP).trans (s311a_D_le_S hp k hS hP)
  have hC₅N : S ⊓ centralizer (d.I₅ : Set G) ≤ normalizer (d.F : Set G) :=
    inf_le_left.trans (s311a_S_le_N_F hp k hS hP)
  have h1 := Common.card_sup_mul_card_inf_eq hC₅N
  have h2 : (d.F ⊓ (S ⊓ centralizer (d.I₅ : Set G))) = d.F ⊓ centralizer (d.I₅ : Set G) := by
    ext z
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hFS h.1, h.2⟩⟩
  rw [h2, (k.s10_o S hS hP).cF₅, (k.s10_o S hS hP).c₅, hp.hyp.card_F hp.gms] at h1
  have hpos : 0 < (2 ^ f) ^ 2 := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring

theorem s311a_not_D_le_Q : ¬ d.D ≤ (d.E ⊓ d.D) ⊔ d.F := by
  intro h
  have h1 := Subgroup.card_le_of_le h
  rw [k.s9e.card_D, s311a_card_Q hp k hS hP] at h1
  have hf2 : 2 ≤ f := hp.hyp.setting.two_le
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have h4 : (2 ^ f) ^ 12 < (2 ^ f) ^ 16 := Nat.pow_lt_pow_right hq (by norm_num)
  omega

end S311aFacts

theorem s311a_comm_aux {Γ : Type*} [Group Γ] {a b c : Γ} (hac : a * c = c * a)
    (hbc : b * c = c * b) : (a * b)⁻¹ * (c * (a * b) * c⁻¹) = 1 := by
  have h : c * (a * b) * c⁻¹ = a * b := by
    calc c * (a * b) * c⁻¹ = (c * a) * b * c⁻¹ := by group
      _ = (a * c) * b * c⁻¹ := by rw [hac]
      _ = a * (c * b) * c⁻¹ := by group
      _ = a * (b * c) * c⁻¹ := by rw [hbc]
      _ = a * b := by group
  rw [h]
  group

section S311aBar

variable (hp : d.CaseHyp) (k : d.Know10) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
  (hP : d.P ≤ S)
include hp k hS hP

theorem s311a_D_le_N_F : d.D ≤ normalizer (d.F : Set G) :=
  (s311a_D_le_S hp k hS hP).trans (s311a_S_le_N_F hp k hS hP)

theorem s311a_Q_le_D : (d.E ⊓ d.D) ⊔ d.F ≤ d.D :=
  sup_le inf_le_right (s311a_F_le_D hp k hS hP)

theorem s311a_bar_D_sq : ∀ v ∈ bar d.F d.D, v * v = 1 := by
  rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
  have hx2 : x * x ∈ d.F := (k.s9_2 S hS hP).2.2.2.2 x (mem_subgroupOf.1 hx)
  rw [← map_mul]
  exact proj_eq_one_iff.2 hx2

theorem s311a_bar_D_comm : ∀ a ∈ bar d.F d.D, ∀ b ∈ bar d.F d.D, a * b = b * a :=
  fun _ ha _ hb => Common.mul_comm_of_mul_self (s311a_bar_D_sq hp k hS hP) ha hb

theorem s311a_card_bar_D : Nat.card (bar d.F d.D) = (2 ^ (4 * f)) ^ 2 := by
  have h := card_bar_mul (s311a_F_le_D hp k hS hP) (s311a_D_le_N_F hp k hS hP)
  rw [k.s9e.card_D, hp.hyp.card_F hp.gms] at h
  have hpos : 0 < (2 ^ f) ^ 8 := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h]
  ring

theorem s311a_card_bar_Q : Nat.card (bar d.F ((d.E ⊓ d.D) ⊔ d.F)) = 2 ^ (4 * f) := by
  have hQN : (d.E ⊓ d.D) ⊔ d.F ≤ normalizer (d.F : Set G) :=
    (s311a_Q_le_D hp k hS hP).trans (s311a_D_le_N_F hp k hS hP)
  have h := card_bar_mul (le_sup_right : d.F ≤ (d.E ⊓ d.D) ⊔ d.F) hQN
  rw [s311a_card_Q hp k hS hP, hp.hyp.card_F hp.gms] at h
  have hpos : 0 < (2 ^ f) ^ 8 := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h]
  ring

theorem s311a_proj_inj {m m' : G} (hm : m ∈ d.M₁) (hm' : m' ∈ d.M₁)
    (h : proj d.F ⟨m, s311a_M₁_le_N_F hp k hS hP hm⟩ =
      proj d.F ⟨m', s311a_M₁_le_N_F hp k hS hP hm'⟩) : m = m' := by
  have h1 := proj_eq_proj_iff.1 h
  have h2 : m⁻¹ * m' ∈ d.M₁ ⊓ d.D :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hm) hm', s311a_F_le_D hp k hS hP h1⟩
  rw [s311a_M₁_inf_D hp k hS hP, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.1 h2

theorem s311a_bar_Q_le_centralizer : bar d.F ((d.E ⊓ d.D) ⊔ d.F) ≤
    centralizer ((bar d.F (S ⊓ d.M₁) : Subgroup (Bar d.F)) : Set (Bar d.F)) := by
  rintro _ ⟨⟨q, hqN⟩, hq, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨⟨r, hrN⟩, hr, rfl⟩
  have hq' : q ∈ (d.E ⊓ d.D) ⊔ d.F := mem_subgroupOf.1 hq
  have hr' : r ∈ S ⊓ d.M₁ := mem_subgroupOf.1 hr
  have hqS : q ∈ S ⊓ centralizerSection S d.F := by rw [k.s10_3 S hS hP]; exact hq'
  have hcs := (Subgroup.mem_inf.1 hqS).2.2.2 r (Subgroup.mem_inf.1 hr').1
  have hmem : r⁻¹ * (q * r * q⁻¹) ∈ normalizer (d.F : Set G) :=
    mul_mem (inv_mem hrN) (mul_mem (mul_mem hqN hrN) (inv_mem hqN))
  have h1 : proj d.F ⟨r⁻¹ * (q * r * q⁻¹), hmem⟩ = 1 := proj_eq_one_iff.2 hcs
  have e : (⟨r⁻¹ * (q * r * q⁻¹), hmem⟩ : normalizer (d.F : Set G)) =
      (⟨r, hrN⟩ : normalizer (d.F : Set G))⁻¹ * ((⟨q, hqN⟩ : normalizer (d.F : Set G)) *
        ⟨r, hrN⟩ * (⟨q, hqN⟩ : normalizer (d.F : Set G))⁻¹) := rfl
  rw [e, map_mul, map_inv, map_mul, map_mul, map_inv] at h1
  have h2 := inv_mul_eq_one.1 h1
  calc proj d.F ⟨r, hrN⟩ * proj d.F ⟨q, hqN⟩
      = (proj d.F ⟨q, hqN⟩ * proj d.F ⟨r, hrN⟩ * (proj d.F ⟨q, hqN⟩)⁻¹) * proj d.F ⟨q, hqN⟩ := by
        rw [← h2]
    _ = proj d.F ⟨q, hqN⟩ * proj d.F ⟨r, hrN⟩ := by group

theorem s311a_not_X_le_centralizer : ¬ bar d.F d.M₁ ≤
    centralizer ((bar d.F d.D : Subgroup (Bar d.F)) : Set (Bar d.F)) := by
  intro hXC
  apply s311a_not_D_le_Q hp k hS hP
  intro dd hdd
  have hddS := s311a_D_le_S hp k hS hP hdd
  have hddN : dd ∈ normalizer (d.F : Set G) := s311a_D_le_N_F hp k hS hP hdd
  rw [← k.s10_3 S hS hP]
  refine Subgroup.mem_inf.2 ⟨hddS, Subgroup.le_normalizer hddS, hddN, fun x hx => ?_⟩
  have hxD : x ∈ d.D ⊔ (S ⊓ d.M₁) := (s311a_S_eq hp k hS hP) ▸ hx
  have hRD : S ⊓ d.M₁ ≤ normalizer (d.D : Set G) :=
    inf_le_right.trans (s311a_M₁_le_N_D hp k hS hP)
  obtain ⟨d', hd', r, hr, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hRD hxD
  have hd'N : d' ∈ normalizer (d.F : Set G) := s311a_D_le_N_F hp k hS hP hd'
  have hrN : r ∈ normalizer (d.F : Set G) := s311a_M₁_le_N_F hp k hS hP (Subgroup.mem_inf.1 hr).2
  have hmem : (d' * r)⁻¹ * (dd * (d' * r) * dd⁻¹) ∈ normalizer (d.F : Set G) :=
    mul_mem (inv_mem (mul_mem hd'N hrN)) (mul_mem (mul_mem hddN (mul_mem hd'N hrN)) (inv_mem hddN))
  refine (proj_eq_one_iff (A := d.F) (x := ⟨(d' * r)⁻¹ * (dd * (d' * r) * dd⁻¹), hmem⟩)).1 ?_
  have e : (⟨(d' * r)⁻¹ * (dd * (d' * r) * dd⁻¹), hmem⟩ : normalizer (d.F : Set G)) =
      ((⟨d', hd'N⟩ : normalizer (d.F : Set G)) * ⟨r, hrN⟩)⁻¹ *
        ((⟨dd, hddN⟩ : normalizer (d.F : Set G)) * ((⟨d', hd'N⟩ : normalizer (d.F : Set G)) *
          ⟨r, hrN⟩) * (⟨dd, hddN⟩ : normalizer (d.F : Set G))⁻¹) := rfl
  rw [e, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv]
  have hV1 : proj d.F ⟨d', hd'N⟩ ∈ bar d.F d.D := proj_mem_bar hd'
  have hV2 : proj d.F ⟨dd, hddN⟩ ∈ bar d.F d.D := proj_mem_bar hdd
  have hX : proj d.F ⟨r, hrN⟩ ∈ bar d.F d.M₁ := proj_mem_bar (Subgroup.mem_inf.1 hr).2
  have hac : proj d.F ⟨d', hd'N⟩ * proj d.F ⟨dd, hddN⟩ = proj d.F ⟨dd, hddN⟩ * proj d.F ⟨d', hd'N⟩ :=
    s311a_bar_D_comm hp k hS hP _ hV1 _ hV2
  have hbc : proj d.F ⟨r, hrN⟩ * proj d.F ⟨dd, hddN⟩ = proj d.F ⟨dd, hddN⟩ * proj d.F ⟨r, hrN⟩ :=
    (mem_centralizer_iff.1 (hXC hX) _ hV2).symm
  exact s311a_comm_aux hac hbc

end S311aBar

theorem s311a_isSylowOf_map {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    [Fact p.Prime] {P K : Subgroup X} (h : IsSylowOf p P K) (f : X →* Y) :
    IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

section S311aCore

variable (hp : d.CaseHyp) (k : d.Know10) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
  (hP : d.P ≤ S)
include hp k hS hP

theorem s311a_mem_N_E {g : G} (hg : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer (d.E : Set G) := by
  refine mem_normalizer_fintype fun e he => ?_
  set α : MulAut S := S.normalizerMonoidHom ⟨g, hg⟩ with hα
  have hchar := (k.s9_1 S hS hP).2.1
  have hfix : (d.E.subgroupOf S).comap α.toMonoidHom = d.E.subgroupOf S := hchar.fixed α
  have heS : e ∈ S := s311a_E_le_S hp k hS hP he
  have hmem : (⟨e, heS⟩ : S) ∈ (d.E.subgroupOf S).comap α.toMonoidHom := by
    rw [hfix]; exact he
  have : (α ⟨e, heS⟩ : G) ∈ d.E := hmem
  simpa [hα] using this

theorem s311a_bar_R_sylow : IsSylowOf 2 (bar d.F (S ⊓ d.M₁)) (bar d.F d.M₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM₁N := s311a_M₁_le_N_F hp k hS hP
  have hRN : S ⊓ d.M₁ ≤ normalizer (d.F : Set G) := inf_le_right.trans hM₁N
  have h1 : IsSylowOf 2 ((S ⊓ d.M₁).subgroupOf (normalizer (d.F : Set G)))
      (d.M₁.subgroupOf (normalizer (d.F : Set G))) := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (normalizer (d.F : Set G))).1 ?_
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hRN,
      inf_eq_left.2 hM₁N]
    exact s311a_R_sylow hp k hS hP
  exact s311a_isSylowOf_map h1 (proj d.F)

theorem s311a_exists_iso : Nonempty (↥d.M₁ ≃* ↥(bar d.F d.M₁)) := by
  let φ : ↥d.M₁ →* Bar d.F := (proj d.F).comp (Subgroup.inclusion (s311a_M₁_le_N_F hp k hS hP))
  have hinj : Function.Injective φ := by
    intro a b hab
    exact Subtype.ext (s311a_proj_inj hp k hS hP a.2 b.2 hab)
  have hrange : φ.range = bar d.F d.M₁ := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact proj_mem_bar a.2
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z.1, mem_subgroupOf.1 hz⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem s311a_core {k₂ : Type} [Field k₂] [Fintype k₂]
    (hk₂ : Fintype.card k₂ = ((2 ^ f) ^ 2) ^ 2) (ψ : d.M₁ ≃* SL(2, k₂)) :
    ∃ J : Subgroup G, Odd (Nat.card J) ∧
      J ≤ normalizer (S : Set G) ⊓ normalizer (d.F : Set G) ⊓ normalizer (d.E : Set G) ⊓
        normalizer (d.D : Set G) ∧
      ∀ x ∈ d.D, x ∉ (d.E ⊓ d.D) ⊔ d.F → ∀ y ∈ d.D, y ∉ (d.E ⊓ d.D) ⊔ d.F →
        ∃ j ∈ J, (j * x * j⁻¹) * y⁻¹ ∈ (d.E ⊓ d.D) ⊔ d.F := by
  classical
  obtain ⟨e⟩ := s311a_exists_iso hp k hS hP
  have hk : Nat.card k₂ = 2 ^ (4 * f) := by
    rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, ← pow_mul]; ring_nf
  haveI : CharP k₂ 2 := U4.charP_two_of_card hk
  have hf2 : 2 ≤ f := hp.hyp.setting.two_le
  have hn : 2 ≤ 4 * f := by omega
  have hM₁N := s311a_M₁_le_N_F hp k hS hP
  have hM₁ND := s311a_M₁_le_N_D hp k hS hP
  have hDN := s311a_D_le_N_F hp k hS hP
  have hFD := s311a_F_le_D hp k hS hP
  have hQD := s311a_Q_le_D hp k hS hP
  have hFQ : d.F ≤ (d.E ⊓ d.D) ⊔ d.F := le_sup_right
  obtain ⟨Jb, hJbX, hJbP, hJbcard, hJbtrans⟩ := s311a_abstract (V := bar d.F d.D)
    (P' := bar d.F (S ⊓ d.M₁)) (Q' := bar d.F ((d.E ⊓ d.D) ⊔ d.F)) hk hn (e.symm.trans ψ)
    (s311a_bar_D_comm hp k hS hP) (bar_le_normalizer_bar hFD hM₁ND)
    (s311a_card_bar_D hp k hS hP) (s311a_not_X_le_centralizer hp k hS hP)
    (s311a_bar_R_sylow hp k hS hP) (bar_mono hQD) (s311a_bar_Q_le_centralizer hp k hS hP)
    (s311a_card_bar_Q hp k hS hP)
  have hJ1 : ∀ j ∈ lift Jb ⊓ d.M₁, ∃ hjN : j ∈ normalizer (d.F : Set G),
      j ∈ d.M₁ ∧ proj d.F ⟨j, hjN⟩ ∈ Jb := by
    intro j hj
    obtain ⟨hjl, hjM⟩ := Subgroup.mem_inf.1 hj
    obtain ⟨hjN, hjJ⟩ := mem_lift_iff.1 hjl
    exact ⟨hjN, hjM, hjJ⟩
  have hJ2 : ∀ b ∈ Jb, ∃ j ∈ lift Jb ⊓ d.M₁, ∃ hjN : j ∈ normalizer (d.F : Set G),
      proj d.F ⟨j, hjN⟩ = b := by
    intro b hb
    obtain ⟨z, hz, rfl⟩ := hJbX hb
    exact ⟨z.1, Subgroup.mem_inf.2 ⟨mem_lift_of_proj_mem hb, mem_subgroupOf.1 hz⟩, z.2, rfl⟩
  have hJcard : Nat.card ↥(lift Jb ⊓ d.M₁) = Nat.card Jb := by
    have key : ∀ j : ↥(lift Jb ⊓ d.M₁), ∃ b : Jb, ∃ hjN : (j : G) ∈ normalizer (d.F : Set G),
        (b : Bar d.F) = proj d.F ⟨j, hjN⟩ := by
      intro j
      obtain ⟨hjN, -, hjJ⟩ := hJ1 j j.2
      exact ⟨⟨_, hjJ⟩, hjN, rfl⟩
    choose g hgN hgeq using key
    refine Nat.card_eq_of_bijective g ⟨?_, ?_⟩
    · intro j j' hjj'
      have h1 : proj d.F ⟨j, hgN j⟩ = proj d.F ⟨j', hgN j'⟩ := by
        rw [← hgeq j, ← hgeq j', hjj']
      obtain ⟨-, hjM, -⟩ := hJ1 j j.2
      obtain ⟨-, hjM', -⟩ := hJ1 j' j'.2
      exact Subtype.ext (s311a_proj_inj hp k hS hP hjM hjM' h1)
    · intro b
      obtain ⟨j, hj, hjN, hjb⟩ := hJ2 b b.2
      refine ⟨⟨j, hj⟩, Subtype.ext ?_⟩
      rw [hgeq ⟨j, hj⟩]
      exact hjb
  have hJodd : Odd (Nat.card ↥(lift Jb ⊓ d.M₁)) := by
    rw [hJcard, hJbcard, ← hk]
    exact Common.odd_card_sub_one
  have hJM : lift Jb ⊓ d.M₁ ≤ d.M₁ := inf_le_right
  have hJR : lift Jb ⊓ d.M₁ ≤ normalizer ((S ⊓ d.M₁ : Subgroup G) : Set G) := by
    intro j hj
    obtain ⟨hjN, hjM, hjJ⟩ := hJ1 j hj
    refine mem_normalizer_fintype fun r hr => ?_
    have hrM : r ∈ d.M₁ := (Subgroup.mem_inf.1 hr).2
    have hrN : r ∈ normalizer (d.F : Set G) := hM₁N hrM
    have hmem : j * r * j⁻¹ ∈ d.M₁ := mul_mem (mul_mem hjM hrM) (inv_mem hjM)
    have hmemN : j * r * j⁻¹ ∈ normalizer (d.F : Set G) := hM₁N hmem
    have hπr : proj d.F ⟨r, hrN⟩ ∈ bar d.F (S ⊓ d.M₁) := proj_mem_bar hr
    have hπ : proj d.F ⟨j * r * j⁻¹, hmemN⟩ ∈ bar d.F (S ⊓ d.M₁) := by
      have e : (⟨j * r * j⁻¹, hmemN⟩ : normalizer (d.F : Set G)) =
          ⟨j, hjN⟩ * ⟨r, hrN⟩ * ⟨j, hjN⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.1 (hJbP hjJ) _).1 hπr
    obtain ⟨z, hz, hzeq⟩ := hπ
    have hzR : (z : G) ∈ S ⊓ d.M₁ := mem_subgroupOf.1 hz
    have := s311a_proj_inj hp k hS hP (Subgroup.mem_inf.1 hzR).2 hmem hzeq
    rw [← this]
    exact hzR
  have hJS : lift Jb ⊓ d.M₁ ≤ normalizer (S : Set G) := by
    intro j hj
    have h1 : j ∈ normalizer ((d.D ⊔ (S ⊓ d.M₁) : Subgroup G) : Set G) :=
      Common.mem_normalizer_sup (hM₁ND (hJM hj)) (hJR hj)
    rwa [← s311a_S_eq hp k hS hP] at h1
  have hJE : ∀ j ∈ lift Jb ⊓ d.M₁, j ∈ normalizer (d.E : Set G) := fun j hj =>
    s311a_mem_N_E hp k hS hP (hJS hj)
  refine ⟨lift Jb ⊓ d.M₁, hJodd, fun j hj => ?_, ?_⟩
  · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hJS hj, hM₁N (hJM hj)⟩,
      hJE j hj⟩, hM₁ND (hJM hj)⟩
  · intro x hx hxQ y hy hyQ
    have hxN : x ∈ normalizer (d.F : Set G) := hDN hx
    have hyN : y ∈ normalizer (d.F : Set G) := hDN hy
    have hπx : proj d.F ⟨x, hxN⟩ ∈ bar d.F d.D := proj_mem_bar hx
    have hπy : proj d.F ⟨y, hyN⟩ ∈ bar d.F d.D := proj_mem_bar hy
    have hπxQ : proj d.F ⟨x, hxN⟩ ∉ bar d.F ((d.E ⊓ d.D) ⊔ d.F) := fun h =>
      hxQ ((mem_bar_iff hFQ ⟨x, hxN⟩).1 h)
    have hπyQ : proj d.F ⟨y, hyN⟩ ∉ bar d.F ((d.E ⊓ d.D) ⊔ d.F) := fun h =>
      hyQ ((mem_bar_iff hFQ ⟨y, hyN⟩).1 h)
    obtain ⟨jb, hjb, hjmem⟩ := hJbtrans _ hπx hπxQ _ hπy hπyQ
    obtain ⟨j, hj, hjN, hjb⟩ := hJ2 jb hjb
    obtain ⟨-, hjM, -⟩ := hJ1 j hj
    refine ⟨j, hj, ?_⟩
    have hmemN : j * x * j⁻¹ * y⁻¹ ∈ normalizer (d.F : Set G) :=
      mul_mem (mul_mem (mul_mem hjN hxN) (inv_mem hjN)) (inv_mem hyN)
    rw [← mem_bar_iff hFQ ⟨j * x * j⁻¹ * y⁻¹, hmemN⟩]
    have e : (⟨j * x * j⁻¹ * y⁻¹, hmemN⟩ : normalizer (d.F : Set G)) =
        ⟨j, hjN⟩ * ⟨x, hxN⟩ * ⟨j, hjN⟩⁻¹ * ⟨y, hyN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hjb]
    exact hjmem

end S311aCore

end Data

section Certified

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec311Trans_of_hyp (hp : d.CaseHyp) (k : d.Know10) : d.Sec311Trans := by
  intro S hS hP hnot
  rcases (hp.hyp.sec3_5_three_iso_all hp.gms hp.gmsL).or with hA | ⟨k₂, _, _, hk₂, ψ, -⟩
  · exact absurd hA hnot
  · exact s311a_core hp k hS hP hk₂ ψ

end Data

namespace CaseBParts

theorem sec311Trans : Sec311TransStatement :=
  fun _ _ _ _ _ _ _ _ hp k => Data.sec311Trans_of_hyp hp k

end CaseBParts

end Certified

end CFSG.LocalAnalysis.EvenBN.U5
