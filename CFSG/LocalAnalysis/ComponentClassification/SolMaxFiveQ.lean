module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveP

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem exists_odd_pow_two_pow {G : Type*} [Group G] [Finite G] (z : G) :
    ∃ m : ℕ, Odd m ∧ ∃ k : ℕ, orderOf (z ^ m) = 2 ^ k := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨m, hm, k, ?_⟩
  rw [orderOf_pow_of_dvd hm.pos.ne' ⟨2 ^ k, by rw [hkm, mul_comm]⟩, hkm,
    Nat.mul_div_cancel _ hm.pos]

theorem pow_odd_of_mul_self {G : Type*} [Monoid G] {z : G} (hz : z * z = 1) {m : ℕ}
    (hm : Odd m) : z ^ m = z := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, hz, one_pow, one_mul]

variable {X : Type} [Group X]

theorem exists_beta_of_four (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J Jc M E₀ : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 9) (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9))
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin 9)} (hρJ : IsPermAction θ ρJ)
    {c e₀ a : X} (he₀ : e₀ ∈ J) (hc2 : c * c = 1) (htc : t * c = c * t)
    (hcN : c ∈ normalizer (J : Set X)) (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hs4 : (coreImage θ he₀).support.card = 4)
    (hCtN : centralizer ({t} : Set X) ≤ normalizer (J : Set X))
    (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Jc = ⊤)
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = coreImage θ hx)
    (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X)))) (hJcM : Jc ≤ M)
    (hJcperf : ⁅Jc, Jc⁆ = Jc) (hJcq : Nontrivial (↥Jc ⧸ pPrimeCore 2 ↥Jc))
    {θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 7)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 7)} (hρ : IsPermAction θM ρ)
    {τ : Perm (Fin 7)} (hτ5 : 7 - τ.support.card = 5)
    (hJcτ : ∀ (z : X) (hz : z ∈ Jc), ρ ⟨z, le_normalizer (hJcM hz)⟩ ∈
      (fixAlt τ).map (alternatingGroup (Fin 7)).subtype)
    (hsurj : ∀ b ∈ fixAlt τ, ∃ (z : X) (hz : z ∈ Jc),
      ρ ⟨z, le_normalizer (hJcM hz)⟩ = (b : Perm (Fin 7)))
    (hO : ∀ (z : X) (hz : z ∈ Jc), z ∈ coreNOf Jc → ρ ⟨z, le_normalizer (hJcM hz)⟩ = 1)
    (htM : t ∈ normalizer (M : Set X)) (htJc : Jc ≤ centralizer ({t} : Set X))
    (hρt1 : ρ ⟨t, htM⟩ ≠ 1) (haJc : a ∈ Jc) (ha2 : a * a = 1) (hat : a * t = t * a)
    (haM : a ∈ normalizer (M : Set X)) (h3 : (ρ ⟨a, haM⟩).supportᶜ.card = 3)
    (hE₀ : E₀ ≤ J ⊓ centralizer ({c} : Set X) ⊓ centralizer ({a} : Set X))
    (hE₀k : Nonempty (E₀ ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hE₀s : ∀ (x : X) (hx : x ∈ J), x ∈ E₀ →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).support) :
    ∃ β : X, orderOf β = 2 ∧ β * c = c * β ∧ β * a = a * β ∧ β * t = t * β ∧
      (∃ hβJ : β ∈ normalizer (J : Set X), (ρJ ⟨β, hβJ⟩).support.card = 2 ∧
        (ρJ ⟨β, hβJ⟩).support ⊆ (coreImage θ he₀).support) ∧
      ∃ hβM : β ∈ normalizer (M : Set X), ρ ⟨β, hβM⟩ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t * t = 1 := by rw [← sq, ← hpair.1.1, pow_orderOf_eq_one]
  have hJCt : J ≤ centralizer ({t} : Set X) := hpair.1.2.1
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcC : Jc ≤ centralizer ({c} : Set X) := hJcJ.trans inf_le_right
  have hJcN : Jc ≤ normalizer (M : Set X) := fun z hz => le_normalizer (hJcM hz)
  have haJ : a ∈ J := hJcJ' haJc
  have hac : a * c = c * a := mem_centralizer_singleton_iff.mp (hJcC haJc)
  obtain ⟨g, hgM, hgt, hga, hgJ, hgsign⟩ := exists_odd_of_four hρJ he₀ hcN hce hs4 hJCt hCtN
    hJcJ hres hinv hsubP χ hχ hMC hMpc hJcM hJcperf hJcq hρ hτ5 hJcτ hsurj hO htM ht2 htJc
    hρt1 haJc ha2 hat haM h3 hE₀ hE₀k hE₀s
  have hgc : g * c = c * g := mem_centralizer_singleton_iff.mp (hMC hgM)
  have hρJc : ρJ ⟨c, hcN⟩ = coreImage θ he₀ :=
    hρJ.apply_eq_coreImage_of_acts (by norm_num) hcN he₀ hce
  have hρJa : ρJ ⟨a, le_normalizer haJ⟩ = coreImage θ haJ :=
    hρJ.apply_of_mem (by norm_num) ⟨a, haJ⟩
  obtain ⟨haJ', haF'⟩ := hsubP a haJc
  have haF : (coreImage θ haJ).support ⊆ (coreImage θ he₀).supportᶜ := haF'
  have hσ2 : (coreImage θ he₀) * (coreImage θ he₀) = 1 := by
    rw [← hρJc, ← map_mul]
    convert map_one ρJ
    exact Subtype.ext hc2
  obtain ⟨d₁, hd₁⟩ : (coreImage θ he₀).support.Nonempty := by
    rw [← Finset.card_pos, hs4]
    norm_num
  have hd₁ne : d₁ ≠ (coreImage θ he₀) d₁ := fun h => (Perm.mem_support.mp hd₁) h.symm
  set δ : Perm (Fin 9) := swap d₁ ((coreImage θ he₀) d₁) with hδdef
  have hδsupp : δ.support ⊆ (coreImage θ he₀).support := by
    rw [hδdef, Perm.support_swap hd₁ne]
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h
    · rw [h]
      exact hd₁
    · rw [h]
      exact Perm.apply_mem_support.mpr hd₁
  have hδcard : δ.support.card = 2 := Perm.card_support_swap hd₁ne
  have hδsign : Perm.sign δ = -1 := Perm.sign_swap hd₁ne
  have hδ2 : δ * δ = 1 := swap_mul_self _ _
  have hδ1 : δ ≠ 1 := fun h => by
    rw [h, Perm.support_one, Finset.card_empty] at hδcard
    omega
  have hδσ : δ * coreImage θ he₀ = coreImage θ he₀ * δ := swap_apply_commute hσ2 d₁
  have hδa : δ * coreImage θ haJ = coreImage θ haJ * δ := by
    refine (Perm.Disjoint.commute ?_).eq
    rw [Perm.disjoint_iff_disjoint_support]
    exact Finset.disjoint_of_subset_left hδsupp
      (Finset.disjoint_of_subset_right haF disjoint_compl_right)
  set π := ρJ ⟨g, hgJ⟩ with hπdef
  have hcommJ : ∀ {w : X} (hw : w ∈ normalizer (J : Set X)), g * w = w * g →
      π * ρJ ⟨w, hw⟩ = ρJ ⟨w, hw⟩ * π := by
    intro w hw hgw
    rw [hπdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgw
  have hπc : π * (coreImage θ he₀) = (coreImage θ he₀) * π := by
    rw [← hρJc]
    exact hcommJ hcN hgc
  have hπa : π * coreImage θ haJ = coreImage θ haJ * π := by
    rw [← hρJa]
    exact hcommJ _ hga
  have hπinv : ∀ σ : Perm (Fin 9), π * σ = σ * π → π⁻¹ * σ = σ * π⁻¹ := fun σ h => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_assoc, mul_inv_cancel, mul_one]
  have hwA : π⁻¹ * δ ∈ alternatingGroup (Fin 9) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, hgsign, hδsign,
      Int.units_mul_self]
  set w : alternatingGroup (Fin 9) := ⟨π⁻¹ * δ, hwA⟩ with hwdef
  have hwc : (w : Perm (Fin 9)) * ρJ ⟨c, hcN⟩ = ρJ ⟨c, hcN⟩ * w := by
    rw [hρJc]
    change π⁻¹ * δ * (coreImage θ he₀) = (coreImage θ he₀) * (π⁻¹ * δ)
    rw [mul_assoc, hδσ, ← mul_assoc, hπinv _ hπc, mul_assoc]
  have hwa : (w : Perm (Fin 9)) * ρJ ⟨a, le_normalizer haJ⟩ =
      ρJ ⟨a, le_normalizer haJ⟩ * w := by
    rw [hρJa]
    change π⁻¹ * δ * coreImage θ haJ = coreImage θ haJ * (π⁻¹ * δ)
    rw [mul_assoc, hδa, ← mul_assoc, hπinv _ hπa, mul_assoc]
  obtain ⟨x, hxc, hxa, hxw⟩ := hρJ.exists_lift_of_two_two hcN
    (isPGroup_zpowers_of_mul_self hc2) (le_normalizer haJ) ha2 hac.symm hwc hwa
  have hxc' : (x : X) * c = c * x := mem_centralizer_singleton_iff.mp hxc
  have hxa' : (x : X) * a = a * x := mem_centralizer_singleton_iff.mp hxa
  have hxt : (x : X) * t = t * x := mem_centralizer_singleton_iff.mp (hJCt x.2)
  have hβ₀J : g * (x : X) ∈ normalizer (J : Set X) := mul_mem hgJ (le_normalizer x.2)
  have hρJβ₀ : ρJ ⟨g * x, hβ₀J⟩ = δ := by
    have h1 : (⟨g * x, hβ₀J⟩ : ↥(normalizer (J : Set X))) =
        ⟨g, hgJ⟩ * ⟨x, le_normalizer x.2⟩ := rfl
    rw [h1, map_mul, ← hπdef, hρJ.apply_of_mem (by norm_num) x, hxw]
    change π * (π⁻¹ * δ) = δ
    group
  have hcomm : ∀ {u : X}, g * u = u * g → (x : X) * u = u * x → g * x * u = u * (g * x) :=
    fun {u} h1 h2 => by rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hβ₀c : g * x * c = c * (g * x) := hcomm hgc hxc'
  have hβ₀a : g * x * a = a * (g * x) := hcomm hga hxa'
  have hβ₀t : g * x * t = t * (g * x) := hcomm hgt hxt
  obtain ⟨hβ₀Jc, hβ₀K⟩ := mem_coreActionKernel_of_support_subset hρJ he₀ hJcJ hres hinv hsubP χ
    hχ hβ₀J hβ₀c (by rw [hρJβ₀]; exact hδsupp)
  have hβ₀M : g * (x : X) ∈ normalizer (M : Set X) :=
    mem_normalizer_of_mem_normalizer_Jc hMC hMpc hJcM hJcperf hJcq
      (mem_centralizer_singleton_iff.mpr hβ₀c) hβ₀Jc
  have hτle : τ.support.card ≤ 7 := by
    have := Finset.card_le_univ τ.support
    rwa [Fintype.card_fin] at this
  have hτ2 : τ.support.card = 2 := by omega
  have hfix : ∀ {u : X} (huN : u ∈ normalizer (M : Set X)),
      u ∈ UnbalancedLayer.coreActionKernel Jc → (ρ ⟨u, huN⟩).support ⊆ τ.support := by
    intro u huN huK v hv
    by_contra hvτ
    exact (Perm.mem_support.mp hv)
      (apply_eq_of_mem_cak_of_onto hJcN (by omega) hsurj hO huN huK hvτ)
  have htK : t ∈ UnbalancedLayer.coreActionKernel Jc := mem_cak_of_forall_commute
    fun z hz => (mem_centralizer_singleton_iff.mp (htJc hz)).symm
  have hρts := hfix htM htK
  have htKJ : t ∈ UnbalancedLayer.coreActionKernel J := mem_cak_of_forall_commute
    fun z hz => (mem_centralizer_singleton_iff.mp (hJCt hz)).symm
  have hρJt : ρJ ⟨t, htKJ.1⟩ = 1 := hρJ.eq_one_of_mem_coreActionKernel (by norm_num) htKJ
  have hρt2 : ρ ⟨t, htM⟩ * ρ ⟨t, htM⟩ = 1 := by
    rw [← map_mul]
    convert map_one ρ
    exact Subtype.ext ht2
  obtain ⟨β₁, hβ₁J, hβ₁M, hρJβ₁, hρβ₁, hβ₁c, hβ₁a, hβ₁t⟩ :
      ∃ (β₁ : X) (hβ₁J : β₁ ∈ normalizer (J : Set X)) (hβ₁M : β₁ ∈ normalizer (M : Set X)),
        ρJ ⟨β₁, hβ₁J⟩ = δ ∧ ρ ⟨β₁, hβ₁M⟩ = 1 ∧ β₁ * c = c * β₁ ∧ β₁ * a = a * β₁ ∧
          β₁ * t = t * β₁ := by
    by_cases h1 : ρ ⟨g * x, hβ₀M⟩ = 1
    · exact ⟨g * x, hβ₀J, hβ₀M, hρJβ₀, h1, hβ₀c, hβ₀a, hβ₀t⟩
    have h2 : ρ ⟨g * x, hβ₀M⟩ = ρ ⟨t, htM⟩ :=
      eq_of_support_subset_pair hτ2 (hfix hβ₀M hβ₀K) hρts h1 hρt1
    refine ⟨g * x * t, mul_mem hβ₀J htKJ.1, mul_mem hβ₀M htM, ?_, ?_, ?_, ?_, ?_⟩
    · have h3 : (⟨g * x * t, mul_mem hβ₀J htKJ.1⟩ : ↥(normalizer (J : Set X))) =
          ⟨g * x, hβ₀J⟩ * ⟨t, htKJ.1⟩ := rfl
      rw [h3, map_mul, hρJβ₀, hρJt, mul_one]
    · have h3 : (⟨g * x * t, mul_mem hβ₀M htM⟩ : ↥(normalizer (M : Set X))) =
          ⟨g * x, hβ₀M⟩ * ⟨t, htM⟩ := rfl
      rw [h3, map_mul, h2, hρt2]
    · rw [mul_assoc, htc, ← mul_assoc, hβ₀c, mul_assoc]
    · rw [mul_assoc, ← hat, ← mul_assoc, hβ₀a, mul_assoc]
    · rw [← mul_assoc t, ← hβ₀t]
  obtain ⟨m, hmodd, k, hk⟩ := exists_odd_pow_two_pow β₁
  have hβ₂J : β₁ ^ m ∈ normalizer (J : Set X) := pow_mem hβ₁J m
  have hβ₂M : β₁ ^ m ∈ normalizer (M : Set X) := pow_mem hβ₁M m
  have hρJβ₂ : ρJ ⟨β₁ ^ m, hβ₂J⟩ = δ := by
    have h1 : (⟨β₁ ^ m, hβ₂J⟩ : ↥(normalizer (J : Set X))) = ⟨β₁, hβ₁J⟩ ^ m := rfl
    rw [h1, map_pow, hρJβ₁, pow_odd_of_mul_self hδ2 hmodd]
  have hρβ₂ : ρ ⟨β₁ ^ m, hβ₂M⟩ = 1 := by
    have h1 : (⟨β₁ ^ m, hβ₂M⟩ : ↥(normalizer (M : Set X))) = ⟨β₁, hβ₁M⟩ ^ m := rfl
    rw [h1, map_pow, hρβ₁, one_pow]
  have hβ₂c : β₁ ^ m * c = c * β₁ ^ m := ((show Commute β₁ c from hβ₁c).pow_left m).eq
  have hβ₂a : β₁ ^ m * a = a * β₁ ^ m := ((show Commute β₁ a from hβ₁a).pow_left m).eq
  have hβ₂t : β₁ ^ m * t = t * β₁ ^ m := ((show Commute β₁ t from hβ₁t).pow_left m).eq
  obtain rfl | rfl | hk2 : k = 0 ∨ k = 1 ∨ 2 ≤ k := by omega
  ·
    exfalso
    rw [pow_zero, orderOf_eq_one_iff] at hk
    apply hδ1
    rw [← hρJβ₂]
    have h1 : (⟨β₁ ^ m, hβ₂J⟩ : ↥(normalizer (J : Set X))) = 1 := Subtype.ext hk
    rw [h1, map_one]
  · refine ⟨β₁ ^ m, by rw [hk, pow_one], hβ₂c, hβ₂a, hβ₂t, ⟨hβ₂J, ?_, ?_⟩, hβ₂M, hρβ₂⟩
    · rw [hρJβ₂]
      exact hδcard
    · rw [hρJβ₂]
      exact hδsupp
  exfalso
  have hkk : 2 ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hyo : orderOf ((β₁ ^ m) ^ 2 ^ (k - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (hk ▸ pow_dvd_pow 2 (Nat.sub_le k 1)), hk, hkk,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hyJ : (β₁ ^ m) ^ 2 ^ (k - 1) ∈ normalizer (J : Set X) := pow_mem hβ₂J _
  have hyM : (β₁ ^ m) ^ 2 ^ (k - 1) ∈ normalizer (M : Set X) := pow_mem hβ₂M _
  have hρJy : ρJ ⟨_, hyJ⟩ = 1 := by
    have h1 : (⟨(β₁ ^ m) ^ 2 ^ (k - 1), hyJ⟩ : ↥(normalizer (J : Set X))) =
        ⟨β₁ ^ m, hβ₂J⟩ ^ 2 ^ (k - 1) := rfl
    rw [h1, map_pow, hρJβ₂]
    obtain ⟨j, hj⟩ : 2 ∣ 2 ^ (k - 1) := dvd_pow_self 2 (by omega)
    rw [hj, pow_mul, sq, hδ2, one_pow]
  have hρy : ρ ⟨_, hyM⟩ = 1 := by
    have h1 : (⟨(β₁ ^ m) ^ 2 ^ (k - 1), hyM⟩ : ↥(normalizer (M : Set X))) =
        ⟨β₁ ^ m, hβ₂M⟩ ^ 2 ^ (k - 1) := rfl
    rw [h1, map_pow, hρβ₂, one_pow]
  have hyK : (β₁ ^ m) ^ 2 ^ (k - 1) ∈ UnbalancedLayer.coreActionKernel J :=
    hρJ.mem_coreActionKernel hyJ hρJy
  have hyc : (β₁ ^ m) ^ 2 ^ (k - 1) * c = c * (β₁ ^ m) ^ 2 ^ (k - 1) :=
    ((show Commute (β₁ ^ m) c from hβ₂c).pow_left _).eq
  have hyt : (β₁ ^ m) ^ 2 ^ (k - 1) * t = t * (β₁ ^ m) ^ 2 ^ (k - 1) :=
    ((show Commute (β₁ ^ m) t from hβ₂t).pow_left _).eq
  have hya : a * (β₁ ^ m) ^ 2 ^ (k - 1) = (β₁ ^ m) ^ 2 ^ (k - 1) * a :=
    ((show Commute (β₁ ^ m) a from hβ₂a).pow_left _).eq.symm
  have ha1 : coreImage θ haJ ≠ 1 := by
    intro h
    have h1 : θ ((⟨a, haJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    have h2 : orderOf (⟨⟨a, haJ⟩, h1⟩ : ↥(pPrimeCore 2 ↥J)) ∣ Nat.card (pPrimeCore 2 ↥J) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h2
    have hodd : Odd (orderOf a) :=
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h2
    have h4 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ha2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5
    · have ha1' : a = 1 := orderOf_eq_one_iff.mp h5
      have h6 : ρ ⟨a, haM⟩ = 1 := by
        have : (⟨a, haM⟩ : ↥(normalizer (M : Set X))) = 1 := Subtype.ext ha1'
        rw [this, map_one]
      rw [h6, Perm.support_one, Finset.compl_empty, Finset.card_univ, Fintype.card_fin] at h3
      omega
    · rw [h5] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr even_two)
  exact false_of_kernel_involution hPump hN1 h13 hML hSch hnab hKP hunb hnU hpair θ he₀ hc2 hcN
    hce hs4 hMC hρ le_rfl hyo hyt hyc hyK hyM
    (by rw [hρy, Perm.support_one, Finset.card_empty, Nat.sub_zero]) haJ (hJcM haJc) ha2 hya
    ha1 (by rw [hρy, Perm.support_one, Finset.compl_empty]; exact Finset.subset_univ _)

end CFSG.ComponentClassification.SolMax
