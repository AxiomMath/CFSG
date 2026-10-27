module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHe9A
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP2
import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP3

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_conj_of_four_support {m : ℕ} (hm : 6 ≤ m) {D : Finset (Fin m)} (hD : D.card = 4)
    {u v : alternatingGroup (Fin m)} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huD : ∀ ω ∉ D, (u : Perm (Fin m)) ω = ω) (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hvD : ∀ ω ∉ D, (v : Perm (Fin m)) ω = ω) :
    ∃ g : alternatingGroup (Fin m), g * u * g⁻¹ = v := by
  classical
  have key : ∀ w : alternatingGroup (Fin m), w * w = 1 → w ≠ 1 →
      (∀ ω ∉ D, (w : Perm (Fin m)) ω = ω) →
      (w : Perm (Fin m)).cycleType = Multiset.replicate 2 2 ∧
        (w : Perm (Fin m)).support.card = 4 := by
    intro w hw2 hw1 hwD
    have hw2' : (w : Perm (Fin m)) * (w : Perm (Fin m)) = 1 := congrArg Subtype.val hw2
    have hw1' : (w : Perm (Fin m)) ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hord : orderOf (w : Perm (Fin m)) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hw2') hw1'
    obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (by rw [hord]; exact Nat.prime_two)
    rw [hord] at hk
    have hsum := Perm.sum_cycleType (w : Perm (Fin m))
    rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hsub : (w : Perm (Fin m)).support ⊆ D := by
      intro ω hω
      by_contra hωD
      exact (Perm.mem_support.mp hω) (hwD ω hωD)
    have hle : (w : Perm (Fin m)).support.card ≤ 4 := (Finset.card_le_card hsub).trans hD.le
    have hne2 : (w : Perm (Fin m)).support.card ≠ 2 := by
      intro h2
      have hsw := (Perm.card_support_eq_two.mp h2).sign_eq
      rw [Perm.mem_alternatingGroup.mp w.2] at hsw
      exact absurd hsw (by decide)
    have hk1 : k = 1 := by omega
    subst hk1
    exact ⟨hk, by omega⟩
  obtain ⟨hcu, hsu⟩ := key u hu2 hu1 huD
  obtain ⟨hcv, -⟩ := key v hv2 hv1 hvD
  have hc : IsConj (u : Perm (Fin m)) (v : Perm (Fin m)) :=
    Perm.isConj_iff_cycleType_eq.mpr (hcu.trans hcv.symm)
  exact isConj_iff.mp (alternatingGroup.isConj_of hc (by rw [hsu, Fintype.card_fin]; omega))

namespace He9

open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

theorem layer_facts_of_held
    [Finite X] {e₁ : X} (he₁2 : e₁ * e₁ = 1) {N : Subgroup X}
    (he₁N : e₁ ∈ normalizer (N : Set X)) (hNperf : ⁅N, N⁆ = N) {L₀ : Subgroup X}
    (hL₀ : L₀ ≤ N ⊓ centralizer ({e₁} : Set X))
    (hL₀pc : IsPComponent 2 (L₀.subgroupOf (N ⊓ centralizer ({e₁} : Set X))))
    (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 7))
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* Blueprint.NativeSporadic.He) :
    ∃ (s : MulAut (↥N ⧸ pPrimeCore 2 ↥N)) (L : Subgroup (↥N ⧸ pPrimeCore 2 ↥N)),
      L = Sol78.layerOfFixed s ∧ s = coreQuotAut N ⟨e₁, he₁N⟩ ∧ orderOf s = 2 ∧
      Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* Blueprint.NativeSporadic.He) ∧
      (L₀.subgroupOf N).map (QuotientGroup.mk' (pPrimeCore 2 ↥N)) = L ∧
      Nat.card (center ↥L) = 3 ∧ pPrimeCore 2 ↥L = center ↥L ∧
      ∃ eL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin 7),
        ∀ (l : X) (hl : l ∈ L₀) (hlN : l ∈ N)
          (hlL : ((⟨l, hlN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) ∈ L),
          eL ((⟨_, hlL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) =
            χ ((⟨l, hl⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 ↥N with hOdef
  have hNc : commutator ↥N = ⊤ := by
    apply map_injective N.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hNperf
  obtain ⟨ψb⟩ := nonempty_coreQuot_held hNc ψ
  have hL₀N : L₀ ≤ N := hL₀.trans inf_le_left
  set s := coreQuotAut N ⟨e₁, he₁N⟩ with hsdef
  have he₁inv : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right he₁2
  have hs2 : s * s = 1 := by
    ext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O q
    change s (s (y : ↥N ⧸ O)) = (y : ↥N ⧸ O)
    rw [hsdef, coreQuotAut_mk, coreQuotAut_mk]
    congr 1
    apply Subtype.ext
    change e₁ * (e₁ * (y : X) * e₁⁻¹) * e₁⁻¹ = y
    rw [he₁inv]
    calc e₁ * (e₁ * (y : X) * e₁) * e₁ = (e₁ * e₁) * y * (e₁ * e₁) := by group
      _ = y := by rw [he₁2]; group
  have hS := FiveFHe.hasOddA_fixedSubgroup_oddQuotAction he₁N he₁2 hL₀ hL₀pc χ
  rw [oddQuotAction_eq_coreQuotAut] at hS
  have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  obtain ⟨Θ', hΘ'⟩ := He11.exists_mulEquiv_heAutU hA7
    (alt_nonabelian_of_card (by rw [Nat.card_fin]; norm_num)) (ψb.trans heEquivP) s hs2 hS
  have hy : heAutU ∈ heAutGroup := heAutU_mem_heAutGroup
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, map_one] at hΘ'
    have h1 : heConjR (1 : heAutGroup) = heConjR ⟨heAutU, hy⟩ := by rw [map_one, hΘ']
    have h2 : heAutU = 1 :=
      (congrArg Subtype.val (ctbh_full_automorphism_permutation_model.1.1 h1)).symm
    exact heAutU_not_mem (by rw [h2]; exact one_mem heP)
  have hso : orderOf s = 2 := orderOf_eq_prime (by rw [sq, hs2]) hs1
  set L := Sol78.layerOfFixed s with hLdef
  have hL₀bL : (L₀.subgroupOf N).map (QuotientGroup.mk' O) ≤ L :=
    map_le_layerOfFixed he₁N he₁2 hL₀ hL₀pc
  have hLne : L ≠ ⊥ := by
    intro h
    have : Nontrivial (alternatingGroup (Fin 7)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; norm_num)
    have : Nontrivial (↥L₀ ⧸ pPrimeCore 2 ↥L₀) := χ.toEquiv.nontrivial
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥L₀ ⧸ pPrimeCore 2 ↥L₀)
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : QuotientGroup.mk' O (inclusion hL₀N l) ∈ L := hL₀bL ⟨_, l.2, rfl⟩
    rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨w, hw, hwl⟩ := inf_pPrimeCore_le hL₀N (mem_inf.mpr ⟨l.2, ⟨_, h1, rfl⟩⟩)
    have h2 : w = l := Subtype.ext hwl
    rw [h2] at hw
    exact hq ((QuotientGroup.eq_one_iff _).mpr hw)
  obtain ⟨φL⟩ := nonempty_layerOfFixed_equiv_heOuterD Θ' s hy hΘ' hLne
  have hLcard : Nat.card L = 7560 := by rw [Nat.card_congr φL.toEquiv, card_heOuterD]
  have hZ3 : Nat.card (center ↥L) = 3 := by
    rw [Nat.card_congr (centerCongr φL).toEquiv, card_center_heOuterD]
  have hOZ : pPrimeCore 2 ↥L = center ↥L := by
    apply map_injective (f := φL.toMonoidHom) φL.injective
    have hc : (center ↥L).map φL.toMonoidHom = center ↥heOuterD := map_center_eq φL
    rw [pPrimeCore_map_iso 2 φL, HeGen.pPrimeCore_heOuterD, hc]
  have hLperf : ⁅L, L⁆ = L := by
    rw [hLdef, HeGen.layerOfFixed_eq_layerIn]
    exact HeGen.layerIn_perfect _
  have hLc : commutator ↥L = ⊤ := by
    apply map_injective L.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hLperf
  have hlamL : ∀ l : ↥L₀, QuotientGroup.mk' O (inclusion hL₀N l) ∈ L := fun l =>
    hL₀bL ⟨_, l.2, rfl⟩
  set lam : ↥L₀ →* ↥L :=
    ((QuotientGroup.mk' O).comp (inclusion hL₀N)).codRestrict L hlamL with hlamdef
  have hlamk : Odd (Nat.card lam.ker) := by
    let j : lam.ker →* O := ((inclusion hL₀N).comp lam.ker.subtype).codRestrict O fun l => by
      have h1 : lam (l : ↥L₀) = 1 := l.2
      have h2 : QuotientGroup.mk' O (inclusion hL₀N (l : ↥L₀)) = 1 := congrArg Subtype.val h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hj : Function.Injective j := fun a b h => by
      have h' : (((a : ↥L₀) : X)) = ((b : ↥L₀) : X) := congrArg (fun z : O => ((z : ↥N) : X)) h
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (card_dvd_of_injective j hj)
  have hLq : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ≤ Nat.card (alternatingGroup (Fin 7)) := by
    have h1 := card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥L)
    have h3 : Nat.card ↥(pPrimeCore 2 ↥L) = 3 := by rw [hOZ, hZ3]
    rw [hLcard, h3] at h1
    rw [hA7]
    omega
  have hlams : Function.Surjective lam :=
    surjective_of_card_coreQuot_le lam hlamk hLc hOZ χ hLq
  obtain ⟨eL, heL⟩ := exists_coreQuot_equiv_of_surjective lam hlams hlamk (by norm_num) χ
  refine ⟨s, L, rfl, rfl, hso, ⟨ψb⟩, le_antisymm hL₀bL fun z hz => ?_, hZ3, hOZ, eL,
    fun l hl hlN hlL => ?_⟩
  · obtain ⟨l, hl⟩ := hlams ⟨z, hz⟩
    exact ⟨inclusion hL₀N l, l.2, congrArg Subtype.val hl⟩
  · have h1 : lam ⟨l, hl⟩ = ⟨_, hlL⟩ := Subtype.ext rfl
    rw [← h1, heL]

theorem le_of_held_pump_of_centralizer
    [Finite X] {H : Subgroup X}
    {e₁ : X} (he₁2 : e₁ * e₁ = 1) {N : Subgroup X} (he₁N : e₁ ∈ normalizer (N : Set X))
    (hNperf : ⁅N, N⁆ = N) (hCH : N ⊓ centralizer ({e₁} : Set X) ≤ H) (hOH : coreNOf N ≤ H)
    {L₀ : Subgroup X} (hL₀ : L₀ ≤ N ⊓ centralizer ({e₁} : Set X))
    (hL₀pc : IsPComponent 2 (L₀.subgroupOf (N ⊓ centralizer ({e₁} : Set X))))
    (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 7))
    (Fb : Subgroup (↥N ⧸ pPrimeCore 2 ↥N))
    (hFbL₀ : ∀ x ∈ Fb, ∃ (l : X) (_ : l ∈ L₀) (hlN : l ∈ N),
      ((⟨l, hlN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = x)
    (hFb4 : Nat.card Fb = 4) (hFbsq : ∀ x ∈ Fb, x * x = 1) {DY : Finset (Fin 7)}
    (hDY : DY.card = 4)
    (hFbY : ∀ (l : X) (hl : l ∈ L₀) (hlN : l ∈ N),
      ((⟨l, hlN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) ∈ Fb → ∀ y ∉ DY,
      ((χ ((⟨l, hl⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin 7)) :
        Perm (Fin 7)) y = y)
    (hC : ∀ x ∈ Fb, x ≠ 1 → ∀ y : ↥N,
      (y : ↥N ⧸ pPrimeCore 2 ↥N) * x = x * (y : ↥N ⧸ pPrimeCore 2 ↥N) → (y : X) ∈ H)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* Blueprint.NativeSporadic.He) : N ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 ↥N with hOdef
  have hL₀H : L₀ ≤ H := hL₀.trans hCH
  have hOH' : ∀ z : ↥N, z ∈ O → (z : X) ∈ H := fun z hz => hOH ⟨z, hz, rfl⟩
  obtain ⟨s, L, hLdef, -, hso, ⟨ψb⟩, hL₀L, hZ3, hOZ, eL, heL⟩ :=
    layer_facts_of_held he₁2 he₁N hNperf hL₀ hL₀pc χ ψ
  have hLperf : ⁅L, L⁆ = L := by
    rw [hLdef, HeGen.layerOfFixed_eq_layerIn]
    exact HeGen.layerIn_perfect _
  have hT : Sol78.IsTripleCoverAltSeven L :=
    ⟨hLperf, hZ3, ⟨(QuotientGroup.quotientMulEquivOfEq hOZ.symm).trans eL⟩⟩
  have hFbL : Fb ≤ L := by
    intro x hx
    obtain ⟨l, hl, hlN, rfl⟩ := hFbL₀ x hx
    rw [← hL₀L]
    exact ⟨⟨l, hlN⟩, hl, rfl⟩
  have hsupp : ∀ z : ↥L, (z : ↥N ⧸ O) ∈ Fb → ∀ ω ∉ DY,
      ((eL (z : ↥L ⧸ pPrimeCore 2 ↥L) : alternatingGroup (Fin 7)) : Perm (Fin 7)) ω = ω := by
    intro z hz ω hω
    obtain ⟨l, hl, hlN, hlz⟩ := hFbL₀ _ hz
    have hlL : ((⟨l, hlN⟩ : ↥N) : ↥N ⧸ O) ∈ L := by
      rw [hlz]
      exact z.2
    have hz' : z = ⟨_, hlL⟩ := Subtype.ext hlz.symm
    rw [hz', heL l hl hlN hlL]
    exact hFbY l hl hlN (by rw [hlz]; exact hz) ω hω
  have hgen : L ⊔ normalizer (Fb : Set (↥N ⧸ O)) = ⊤ := by
    subst hLdef
    exact HeGen.heldGenerationInput (↥N ⧸ O) ⟨ψb⟩ s hso 7 (Or.inr hT) eL Fb hFbL
      (klein_of_card_sq hFb4 hFbsq) ⟨DY, hDY, hsupp⟩
  have hZ1 : ∀ c ∈ center ↥L, c * c = 1 → c = 1 := by
    intro c hc hc2
    have h3 : (⟨c, hc⟩ : center ↥L) ^ 3 = 1 := by
      rw [← hZ3]
      exact pow_card_eq_one'
    have h3' : c ^ 3 = 1 := congrArg Subtype.val h3
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [h3', hc2]; group
  have htrans : ∀ x₁ ∈ Fb, x₁ ≠ 1 → ∀ x₂ ∈ Fb, x₂ ≠ 1 → ∃ ℓ ∈ L, ℓ * x₁ * ℓ⁻¹ = x₂ := by
    intro x₁ hx₁ hx₁1 x₂ hx₂ hx₂1
    set y₁ : ↥L := ⟨x₁, hFbL hx₁⟩ with hy₁def
    set y₂ : ↥L := ⟨x₂, hFbL hx₂⟩ with hy₂def
    have hy₁2 : y₁ * y₁ = 1 := Subtype.ext (hFbsq x₁ hx₁)
    have hy₂2 : y₂ * y₂ = 1 := Subtype.ext (hFbsq x₂ hx₂)
    have himg : ∀ y : ↥L, y * y = 1 → y ≠ 1 →
        eL (y : ↥L ⧸ pPrimeCore 2 ↥L) * eL (y : ↥L ⧸ pPrimeCore 2 ↥L) = 1 ∧
          eL (y : ↥L ⧸ pPrimeCore 2 ↥L) ≠ 1 := by
      intro y hy2 hy1
      refine ⟨by rw [← map_mul, ← QuotientGroup.mk_mul, hy2, QuotientGroup.mk_one, map_one], ?_⟩
      intro h
      rw [map_eq_one_iff _ eL.injective, QuotientGroup.eq_one_iff, hOZ] at h
      exact hy1 (hZ1 y h hy2)
    obtain ⟨hu2, hu1⟩ := himg y₁ hy₁2 (fun h => hx₁1 (congrArg Subtype.val h))
    obtain ⟨hv2, hv1⟩ := himg y₂ hy₂2 (fun h => hx₂1 (congrArg Subtype.val h))
    obtain ⟨g, hg⟩ := exists_conj_of_four_support (by norm_num) hDY hu2 hu1 (hsupp y₁ hx₁) hv2
      hv1 (hsupp y₂ hx₂)
    obtain ⟨q, hq⟩ := eL.surjective g
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    have hc : ℓ * y₁ * ℓ⁻¹ * y₂⁻¹ ∈ center ↥L := by
      rw [← hOZ, ← QuotientGroup.eq_one_iff, ← map_eq_one_iff _ eL.injective,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, map_mul, map_mul, map_mul, map_inv, map_inv, hq, hg,
        mul_inv_cancel]
    set c := ℓ * y₁ * ℓ⁻¹ * y₂⁻¹ with hcdef
    have hcomm : ∀ g : ↥L, g * c = c * g := mem_center_iff.mp hc
    have h1 : ℓ * y₁ * ℓ⁻¹ = c * y₂ := by rw [hcdef]; group
    have hc2 : c * c = 1 := by
      have h3 : (c * y₂) * (c * y₂) = 1 := by
        rw [← h1]
        calc ℓ * y₁ * ℓ⁻¹ * (ℓ * y₁ * ℓ⁻¹) = ℓ * (y₁ * y₁) * ℓ⁻¹ := by group
          _ = 1 := by rw [hy₁2]; group
      calc c * c = (c * y₂) * (c * y₂) * (y₂ * y₂)⁻¹ := by
            rw [show (c * y₂) * (c * y₂) = c * (y₂ * c) * y₂ by group, hcomm y₂]
            group
        _ = 1 := by rw [h3, hy₂2]; group
    have hc1 := hZ1 c hc hc2
    refine ⟨ℓ, ℓ.2, ?_⟩
    have h2 : ℓ * y₁ * ℓ⁻¹ = y₂ := by rw [h1, hc1, one_mul]
    exact congrArg Subtype.val h2
  set Y := (H.subgroupOf N).map (QuotientGroup.mk' O) with hYdef
  have hLY : L ≤ Y := by
    intro z hz
    rw [← hL₀L] at hz
    obtain ⟨g, hg, rfl⟩ := hz
    exact ⟨g, hL₀H hg, rfl⟩
  have hNFY : normalizer (Fb : Set (↥N ⧸ O)) ≤ Y := by
    intro z hz
    obtain ⟨x₁, hx₁, hx₁1⟩ : ∃ x ∈ Fb, x ≠ 1 := by
      rcases Fb.bot_or_exists_ne_one with h | h
      · rw [h, Subgroup.card_bot] at hFb4
        exact absurd hFb4 (by norm_num)
      · exact h
    have hx₂ : z * x₁ * z⁻¹ ∈ Fb := (mem_normalizer_iff.mp hz x₁).mp hx₁
    have hx₂1 : z * x₁ * z⁻¹ ≠ 1 := by
      intro h
      apply hx₁1
      calc x₁ = z⁻¹ * (z * x₁ * z⁻¹) * z := by group
        _ = 1 := by rw [h]; group
    obtain ⟨ℓ, hℓL, hℓ⟩ := htrans x₁ hx₁ hx₁1 _ hx₂ hx₂1
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective O (ℓ⁻¹ * z)
    have hyc : (y : ↥N ⧸ O) * x₁ = x₁ * (y : ↥N ⧸ O) := by
      change QuotientGroup.mk' O y * x₁ = x₁ * QuotientGroup.mk' O y
      rw [hy]
      calc ℓ⁻¹ * z * x₁ = ℓ⁻¹ * (z * x₁ * z⁻¹) * z := by group
        _ = ℓ⁻¹ * (ℓ * x₁ * ℓ⁻¹) * z := by rw [← hℓ]
        _ = x₁ * (ℓ⁻¹ * z) := by group
    have hyY : ℓ⁻¹ * z ∈ Y := ⟨y, hC x₁ hx₁ hx₁1 y hyc, hy⟩
    have h1 := mul_mem (hLY hℓL) hyY
    rwa [mul_inv_cancel_left] at h1
  have hYtop : Y = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le hLY hNFY
  intro n hn
  obtain ⟨h, hh, hhn⟩ : QuotientGroup.mk' O ⟨n, hn⟩ ∈ Y := hYtop ▸ mem_top _
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hhn
  have h1 : h⁻¹ * ⟨n, hn⟩ ∈ O := QuotientGroup.eq.mp hhn
  have h2 := mul_mem (show (h : X) ∈ H from hh) (hOH' _ h1)
  simpa using h2

theorem le_coreActionKernel_of_held
    [Finite X] {r e₀ : X}
    (he₀r : e₀ ∈ centralizer ({r} : Set X)) (he₀o : orderOf e₀ = 2) {A B N : Subgroup X}
    (hNC : N ≤ centralizer ({r} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))))
    (hfix : N.map (MulAut.conj e₀).toMonoidHom = N) (hA : A ≤ N ⊓ centralizer ({e₀} : Set X))
    (hApc : IsPComponent 2 (A.subgroupOf (N ⊓ centralizer ({e₀} : Set X))))
    (χ : ↥A ⧸ pPrimeCore 2 ↥A ≃* alternatingGroup (Fin 7))
    (hBC : B ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hBpc : IsPComponent 2
      (B.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    (hBA : ∀ x ∈ B, ∀ z ∈ A, x * z * x⁻¹ * z⁻¹ ∈ (pPrimeCore 2 ↥A).map A.subtype)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* Blueprint.NativeSporadic.He) :
    B ≤ UnbalancedLayer.coreActionKernel N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq, ← he₀o, pow_orderOf_eq_one]
  have he₀N : e₀ ∈ normalizer (N : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
  have hNperf : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  obtain ⟨N₃, hN₃C, hN₃pc, hcover, -⟩ := exists_pump_in he₀r he₀o hBC hBpc
  obtain ⟨hN₃xC, hN₃xpc⟩ := isPComponent_conj hN₃C hN₃pc he₀r
  by_cases hN₃ : N₃ = N ∨ N₃.map (MulAut.conj e₀).toMonoidHom = N
  · exfalso
    have hN₃N : N₃ = N := by
      rcases hN₃ with h | h
      · exact h
      · rw [← SwapP2.conjBy_conjBy_of_mul_self N₃ he₀2]
        change (N₃.map (MulAut.conj e₀).toMonoidHom).map (MulAut.conj e₀).toMonoidHom = N
        rw [h, hfix]
    have hBN : B ≤ N := by
      have h1 := hcover
      rwa [hN₃N, hfix, sup_idem] at h1
    have hB' : B ≤ N ⊓ centralizer ({e₀} : Set X) := le_inf hBN (hBC.trans inf_le_right)
    have hBpc' : IsPComponent 2 (B.subgroupOf (N ⊓ centralizer ({e₀} : Set X))) :=
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hB' (inf_le_inf_right _ hNC) hBpc
    obtain ⟨s, L, hLdef, hsdef, -, -, hAL, hZ3, hOZ, eL, heL⟩ :=
      layer_facts_of_held he₀2 he₀N hNperf hA hApc χ ψ
    set O := pPrimeCore 2 ↥N with hOdef
    have hBL : (B.subgroupOf N).map (QuotientGroup.mk' O) ≤ L := by
      rw [hLdef, hsdef]
      exact map_le_layerOfFixed he₀N he₀2 hB' hBpc'
    have hAN : A ≤ N := hA.trans inf_le_left
    have hBZ : ∀ (x : X) (hx : x ∈ B), ((⟨x, hBN hx⟩ : ↥N) : ↥N ⧸ O) ∈
        (center ↥L).map L.subtype := by
      intro x hx
      have hxL : ((⟨x, hBN hx⟩ : ↥N) : ↥N ⧸ O) ∈ L := hBL ⟨⟨x, hBN hx⟩, hx, rfl⟩
      refine ⟨⟨_, hxL⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, ← hOZ, ← QuotientGroup.eq_one_iff, ← map_eq_one_iff _ eL.injective]
      have hc : ∀ g : alternatingGroup (Fin 7),
          eL ((⟨_, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) * g =
            g * eL ((⟨_, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) := by
        intro g
        obtain ⟨q, hq⟩ := χ.surjective g
        obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
        have hzL : ((⟨z, hAN z.2⟩ : ↥N) : ↥N ⧸ O) ∈ L := by
          rw [← hAL]
          exact ⟨⟨z, hAN z.2⟩, z.2, rfl⟩
        have hzg : eL ((⟨_, hzL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) = g := by
          rw [heL z z.2 (hAN z.2) hzL, ← hq]
        obtain ⟨w, hw, hwe⟩ := hBA x hx z z.2
        have hwL : ((⟨_, hAN w.2⟩ : ↥N) : ↥N ⧸ O) ∈ L := by
          rw [← hAL]
          exact ⟨⟨_, hAN w.2⟩, w.2, rfl⟩
        have hw1 : eL ((⟨_, hwL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) = 1 := by
          rw [heL w w.2 (hAN w.2) hwL, map_eq_one_iff _ χ.injective, QuotientGroup.eq_one_iff]
          exact hw
        have hwc : (⟨_, hwL⟩ : ↥L) = ⟨_, hxL⟩ * ⟨_, hzL⟩ * ⟨_, hxL⟩⁻¹ * ⟨_, hzL⟩⁻¹ := by
          apply Subtype.ext
          change ((⟨(w : X), hAN w.2⟩ : ↥N) : ↥N ⧸ O) = _
          have h1 : (⟨(w : X), hAN w.2⟩ : ↥N) = ⟨x, hBN hx⟩ * ⟨z, hAN z.2⟩ *
              (⟨x, hBN hx⟩ : ↥N)⁻¹ * (⟨z, hAN z.2⟩ : ↥N)⁻¹ := Subtype.ext hwe
          rw [h1]
          rfl
        rw [hwc, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_inv, map_mul, map_mul, map_mul, map_inv,
          map_inv, hzg] at hw1
        calc eL ((⟨_, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) * g =
            (eL ((⟨_, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) * g *
              (eL ((⟨_, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L))⁻¹ * g⁻¹) *
              (g * eL ((⟨_, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L)) := by group
          _ = g * eL ((⟨_, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) := by rw [hw1, one_mul]
      have hZ7 := alternatingGroup.center_eq_bot (α := Fin 7) (by rw [Nat.card_fin]; norm_num)
      have h1 : eL ((⟨_, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∈
          center (alternatingGroup (Fin 7)) := mem_center_iff.mpr fun g => (hc g).symm
      rw [hZ7, mem_bot] at h1
      exact h1
    set f : ↥B →* ↥N ⧸ O := (QuotientGroup.mk' O).comp (inclusion hBN) with hfdef
    have hfr : f.range ≤ (center ↥L).map L.subtype := by
      rintro _ ⟨x, rfl⟩
      exact hBZ x x.2
    have hfr3 : Nat.card f.range ∣ 3 := by
      have h1 := card_dvd_of_le hfr
      rwa [card_map_of_injective L.subtype_injective, hZ3] at h1
    have hfk : Odd (Nat.card f.ker) := by
      let j : f.ker →* O := ((inclusion hBN).comp f.ker.subtype).codRestrict O fun x => by
        have h1 : QuotientGroup.mk' O (inclusion hBN (x : ↥B)) = 1 := x.2
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have hj : Function.Injective j := fun a b h => by
        have h' : (((a : ↥B) : X)) = ((b : ↥B) : X) := congrArg (fun z : O => ((z : ↥N) : X)) h
        exact Subtype.ext (Subtype.ext h')
      exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
        (card_dvd_of_injective j hj)
    have hcardB : Nat.card ↥B = Nat.card f.range * Nat.card f.ker := by
      rw [card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    have hodd : Odd (Nat.card ↥B) := by
      rw [hcardB]
      exact Nat.odd_mul.mpr ⟨(Nat.odd_iff.mpr (by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hfr3 with h | h <;>
          rw [h])), hfk⟩
    have h2 := two_dvd_card_of_isPComponent_in hBC hBpc
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · push Not at hN₃
    obtain ⟨h1, h2⟩ := hN₃
    have hK1 : N₃ ≤ UnbalancedLayer.coreActionKernel N :=
      GSThmB.B5a.le_coreActionKernel_of_ne hNC hN₃C hNpc hN₃pc (Ne.symm h1)
    have hK2 : N₃.map (MulAut.conj e₀).toMonoidHom ≤ UnbalancedLayer.coreActionKernel N :=
      GSThmB.B5a.le_coreActionKernel_of_ne hNC hN₃xC hNpc hN₃xpc (Ne.symm h2)
    exact hcover.trans (sup_le hK1 hK2)

end He9

namespace SwapP2

theorem le_of_held
    [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
    {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
    {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin 11)} {r : X} {N₁ : Subgroup X}
    (hs : Setting t J 11 e E D M) (hd : Data t J 11 e E D M e₀ F DF r)
    (hFH : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E)
    (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    (hOr : core (centralizer ({r} : Set X)) ≤ Hn E)
    (hP : PumpData M e₀ r N₁) (hfix : conjBy N₁ e₀ = N₁)
    (ψ : ↥N₁ ⧸ Open.fusionZStar ↥N₁ ≃* Blueprint.NativeSporadic.He)
    (hside : ∀ f ∈ F, ∃ a ∈ fixA M e₀ r, f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel N₁ ∧
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M) :
    N₁ ≤ Hn E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by norm_num) (by norm_num) θ
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  have hJN : J ≤ normalizer (M : Set X) := le_normalizer_of_swap htH hs.le hs.pc hs.swap hs.diag
  obtain ⟨π, hπ⟩ := S.exists_perm_compat_of_swap hs.cent hs.le hs.pc hs.swap hs.diag hρ
  have he₀J : e₀ ∈ J := S.le hd.e₀E
  have he₀N : e₀ ∈ normalizer (M : Set X) := hJN he₀J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀4 : (ρ ⟨e₀, he₀N⟩).support.card = 4 := by
    rw [hπ e₀ he₀J he₀N, Perm.card_support_conj]
    exact S.card_support_coreImage_E hd.e₀E hd.e₀1
  obtain ⟨hAle, hApc, ⟨χA⟩⟩ :=
    fixedLayer_facts_of_perm hs.le hs.pc hρ he₀N he₀2 he₀4.le (by omega)
  set A := GSLit.fixedLayer M (zpowers e₀) with hAdef
  have hAM : A ≤ M := (GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left
  have hAe : A ≤ centralizer ({e₀} : Set X) := hAle.trans inf_le_right
  have hAMe : A ≤ M ⊓ centralizer ({e₀} : Set X) := le_inf hAM hAe
  have hApcM : IsPComponent 2 (A.subgroupOf (M ⊓ centralizer ({e₀} : Set X))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hAMe (inf_le_inf_right _ hs.le) hApc
  obtain ⟨-, hAres, hAq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 A _ hAMe).mp hApcM
  have hAperf : ⁅A, A⁆ = A := UnbalancedCorr.commutator_eq_of_isPComponent hAMe hApcM
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hrK : r ∈ UnbalancedLayer.coreActionKernel M := hMtK hd.rM
  have hre₀ : r ∈ centralizer ({e₀} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀
  have hrA : r ∈ normalizer (A : Set X) := by
    refine GSLit.mem_normalizer_fixedLayer hrK.1 (centralizer_le_normalizer _ ?_)
    rw [centralizer_zpowers_eq' e₀]
    exact hre₀
  have hrKA : r ∈ UnbalancedLayer.coreActionKernel A := mem_coreActionKernel_of_le hAM hrK hrA
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have hArA : fixA M e₀ r ≤ A := (GSLit.fixedLayer_le_inf A (zpowers r)).trans inf_le_left
  obtain ⟨Φ, hΦ⟩ := exists_fixedLayer_coreQuot_equiv hAq (zpowers_le.mpr hrKA) hR2
  have hcardA : Fintype.card ↥((ρ ⟨e₀, he₀N⟩).supportᶜ : Finset (Fin 11)) = 11 - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, he₀4]
  obtain ⟨τM, hτM, ψM, hψM⟩ := exists_image_equiv (M := M) (Je := A) (by omega) (by omega)
    (by omega) θ hρ (hAM.trans le_normalizer) hAres hAperf hcardA χA
    (exists_rho_ne_one (by omega) hρ hAM (LocalCores.isQuasisimple_nontrivial hAq))
    (Or.inr ⟨e₀, he₀N, he₀2, hAM, hAe, hApcM⟩)
  have he₀N₁ : e₀ ∈ normalizer (N₁ : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
  have hArN : fixA M e₀ r ≤ N₁ := by
    have h1 := hP.cover
    rwa [hfix, sup_idem] at h1
  have hlayer : IsPComponent 2 ((fixA M e₀ r).subgroupOf (N₁ ⊓ centralizer ({e₀} : Set X))) := by
    have h1 := hP.layer
    rwa [hfix, sup_idem] at h1
  have hAre : fixA M e₀ r ≤ centralizer ({e₀} : Set X) := hArA.trans hAe
  have hArY : fixA M e₀ r ≤ N₁ ⊓ centralizer ({e₀} : Set X) := le_inf hArN hAre
  have hN₁perf : ⁅N₁, N₁⁆ = N₁ := UnbalancedCorr.commutator_eq_of_isPComponent hP.le hP.pc
  have hOH : coreNOf N₁ ≤ Hn E := (pPrimeCore_le_of_isPComponent hP.le hP.pc).trans hOr
  have hArNM : ∀ a ∈ fixA M e₀ r, a ∈ normalizer (M : Set X) := fun a ha =>
    (hAM.trans le_normalizer) (hArA ha)
  obtain ⟨φM, hφM⟩ := exists_fixAlt_equiv τM
  have hβ : Fintype.card ↥(τM.supportᶜ : Finset (Fin 11)) = 7 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    omega
  set σ := Fintype.equivFinOfCardEq hβ with hσdef
  set χ : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin 7) :=
    (Φ.trans (ψM.trans φM.symm)).trans σ.altCongrHom with hχdef
  have hχ : ∀ (a : ↥(fixA M e₀ r)) (y : Fin 7),
      ρ ⟨a, hArNM a a.2⟩ ((σ.symm y : ↥(τM.supportᶜ : Finset (Fin 11))) : Fin 11) =
        ((σ.symm y : ↥(τM.supportᶜ : Finset (Fin 11))) : Fin 11) →
      ((χ (a : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r)) : alternatingGroup (Fin 7)) :
        Perm (Fin 7)) y = y := by
    intro a y hay
    set p := φM.symm (ψM (Φ (a : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r)))) with hpdef
    have hp : Perm.ofSubtype (p : Perm ↥(τM.supportᶜ : Finset (Fin 11))) =
        ρ ⟨a, hArNM a a.2⟩ := by
      rw [← hφM p, hpdef, MulEquiv.apply_symm_apply, hΦ a (hArA a.2), hψM]
    have h1 : (p : Perm _) (σ.symm y) = σ.symm y := by
      apply Subtype.ext
      rw [← Perm.ofSubtype_apply_of_mem _ (σ.symm y).2, hp]
      exact hay
    change σ ((p : Perm _) (σ.symm y)) = y
    rw [h1, Equiv.apply_symm_apply]
  set DFπ := DF.map π.toEmbedding with hDFπdef
  have hρF : ∀ f (hf : f ∈ F), ∀ ω ∉ DFπ, ρ ⟨f, hJN (hd.FJ hf)⟩ ω = ω := by
    intro f hf ω hω
    have h1 : π⁻¹ ω ∉ DF := fun h => hω (Finset.mem_map_equiv.mpr h)
    have h2 : coreImage e (hd.FJ hf) (π⁻¹ ω) = π⁻¹ ω := hd.Fs ⟨f, hd.FJ hf⟩ hf _ h1
    rw [hπ f (hd.FJ hf) (hJN (hd.FJ hf)), Perm.mul_apply, Perm.mul_apply, h2]
    exact π.apply_symm_apply ω
  set DY₀ : Finset (Fin 7) := Finset.univ.filter
    (fun y => ((σ.symm y : ↥(τM.supportᶜ : Finset (Fin 11))) : Fin 11) ∈ DFπ) with hDY₀def
  have hDY₀ : DY₀.card ≤ 4 := by
    have h1 : DY₀.card ≤ DFπ.card := Finset.card_le_card_of_injOn
      (fun y => ((σ.symm y : ↥(τM.supportᶜ : Finset (Fin 11))) : Fin 11))
      (fun y hy => (Finset.mem_filter.mp hy).2)
      (fun y₁ _ y₂ _ h => σ.symm.injective (Subtype.ext h))
    rwa [hDFπdef, Finset.card_map, hd.DFc] at h1
  obtain ⟨DY, hDY₀Y, hDY⟩ := Finset.exists_superset_card_eq hDY₀ (by simp)
  set O₁ := pPrimeCore 2 ↥N₁ with hO₁def
  have hN₁c : commutator ↥N₁ = ⊤ := by
    apply map_injective N₁.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hN₁perf
  obtain ⟨ψb⟩ := nonempty_coreQuot_held hN₁c ψ
  have hcl : ∀ x : ↥N₁ ⧸ O₁, (∀ y : ↥N₁ ⧸ O₁, x * y = y * x) → x = 1 := by
    intro x hx
    have hHe : IsSimpleGroup Blueprint.NativeSporadic.He := Sporadic.He.isSimpleGroup_He
    have hZ : center Blueprint.NativeSporadic.He = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Blueprint.NativeSporadic.He) with
        h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := GrSLit.exists_mul_ne_held
        have ha : a ∈ center Blueprint.NativeSporadic.He := by
          rw [h]
          exact mem_top a
        exact absurd (mem_center_iff.mp ha b).symm hab
    have h1 : ψb x ∈ center Blueprint.NativeSporadic.He := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := ψb.surjective y
      rw [← map_mul, ← map_mul, hx y']
    rw [hZ, mem_bot] at h1
    exact ψb.injective (by rw [h1, map_one])
  have hconj_inj : Function.Injective (MulAut.conj : (↥N₁ ⧸ O₁) →* MulAut (↥N₁ ⧸ O₁)) := by
    intro x₁ x₂ h
    have h1 : x₂⁻¹ * x₁ = 1 := by
      apply hcl
      intro z
      have h2 := congrArg (fun φ : MulAut (↥N₁ ⧸ O₁) => φ z) h
      simp only [MulAut.conj_apply] at h2
      calc x₂⁻¹ * x₁ * z = x₂⁻¹ * (x₁ * z * x₁⁻¹) * x₁ := by group
        _ = x₂⁻¹ * (x₂ * z * x₂⁻¹) * x₁ := by rw [h2]
        _ = z * (x₂⁻¹ * x₁) := by group
    calc x₁ = x₂ * (x₂⁻¹ * x₁) := by group
      _ = x₂ := by rw [h1, mul_one]
  have hFN : F ≤ normalizer (N₁ : Set X) := by
    intro f hf
    obtain ⟨a, ha, hfaN, -⟩ := hside f hf
    have h1 : f = (f * a⁻¹) * a := by group
    rw [h1]
    exact mul_mem hfaN.1 (le_normalizer (hArN ha))
  have hFsq : ∀ f ∈ F, f * f = 1 := fun f hf => by
    rw [← sq]
    exact (card_sq_of_klein hd.Fk).2 f hf
  have hinner : ∀ (a : X) (ha : a ∈ N₁), TBLit.oddQuotAction N₁ ⟨a, le_normalizer ha⟩ =
      MulAut.conj ((⟨a, ha⟩ : ↥N₁) : ↥N₁ ⧸ O₁) := by
    intro a ha
    ext q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [TBLit.oddQuotAction_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
  have hact : ∀ f (hf : f ∈ F), ∃ a ∈ fixA M e₀ r, ∃ haN : a ∈ N₁,
      TBLit.oddQuotAction N₁ ⟨f, hFN hf⟩ = MulAut.conj ((⟨a, haN⟩ : ↥N₁) : ↥N₁ ⧸ O₁) ∧
        f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M := by
    intro f hf
    obtain ⟨a, ha, hfaN, hfaM⟩ := hside f hf
    refine ⟨a, ha, hArN ha, ?_, hfaM⟩
    have h1 : TBLit.oddQuotAction N₁ ⟨f * a⁻¹, hfaN.1⟩ = 1 :=
      (mem_coreActionKernel_iff_oddQuotAction hfaN.1).mp hfaN
    have h2 : (⟨f, hFN hf⟩ : ↥(normalizer (N₁ : Set X))) =
        ⟨f * a⁻¹, hfaN.1⟩ * ⟨a, le_normalizer (hArN ha)⟩ := Subtype.ext (by simp)
    rw [h2, map_mul, h1, one_mul, hinner]
  have hρfa : ∀ (f a : X) (hf : f ∈ F) (ha : a ∈ fixA M e₀ r),
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M →
      ρ ⟨f, hJN (hd.FJ hf)⟩ = ρ ⟨a, hArNM a ha⟩ := by
    intro f a hf ha hfaM
    have h1 := hρ.eq_one_of_mem_coreActionKernel (by omega) hfaM
    have h2 : (⟨f * a⁻¹, hfaM.1⟩ : ↥(normalizer (M : Set X))) =
        ⟨f, hJN (hd.FJ hf)⟩ * (⟨a, hArNM a ha⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
    rw [h2, map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  set Fb : Subgroup (↥N₁ ⧸ O₁) :=
    ((F.subgroupOf (normalizer (N₁ : Set X))).map (TBLit.oddQuotAction N₁)).comap
      (MulAut.conj : (↥N₁ ⧸ O₁) →* MulAut (↥N₁ ⧸ O₁)) with hFbdef
  have hmemFb : ∀ x : ↥N₁ ⧸ O₁, x ∈ Fb ↔ ∃ f ∈ F, ∃ hf : f ∈ normalizer (N₁ : Set X),
      TBLit.oddQuotAction N₁ ⟨f, hf⟩ = MulAut.conj x := by
    intro x
    constructor
    · rintro ⟨g, hg, hgx⟩
      exact ⟨g, hg, g.2, hgx⟩
    · rintro ⟨f, hf, hfN, hfx⟩
      exact ⟨⟨f, hfN⟩, hf, hfx⟩
  have hFbA : ∀ x ∈ Fb, ∃ f ∈ F, ∃ a ∈ fixA M e₀ r, ∃ haN : a ∈ N₁,
      x = ((⟨a, haN⟩ : ↥N₁) : ↥N₁ ⧸ O₁) ∧ f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M := by
    intro x hx
    obtain ⟨f, hf, hfN, hfx⟩ := (hmemFb x).mp hx
    obtain ⟨a, ha, haN, hfa, hfaM⟩ := hact f hf
    exact ⟨f, hf, a, ha, haN, hconj_inj (hfx.symm.trans hfa), hfaM⟩
  have hinj : F.subgroupOf (normalizer (N₁ : Set X)) ⊓ (TBLit.oddQuotAction N₁).ker = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgF, hgk⟩
    rw [mem_bot]
    by_contra hg1
    have hgF' : (g : X) ∈ F := hgF
    have hg1' : (g : X) ≠ 1 := fun h => hg1 (Subtype.ext h)
    obtain ⟨a, ha, haN, hfa, hfaM⟩ := hact g hgF'
    have h1 : MulAut.conj ((⟨a, haN⟩ : ↥N₁) : ↥N₁ ⧸ O₁) = 1 := by
      rw [← hfa]
      exact hgk
    have h2 : ((⟨a, haN⟩ : ↥N₁) : ↥N₁ ⧸ O₁) = 1 := hconj_inj (h1.trans (map_one _).symm)
    rw [QuotientGroup.eq_one_iff] at h2
    have haodd : Odd (orderOf a) := by
      have h4 := orderOf_dvd_natCard (⟨⟨a, haN⟩, h2⟩ : ↥O₁)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h4
      exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h4 pPrimeCore_coprime_card)
    have hgJ : (g : X) ∈ J := hd.FJ hgF'
    have hρga := hρfa g a hgF' ha hfaM
    have hρ1 : ρ ⟨g, hJN hgJ⟩ = 1 := by
      obtain ⟨k, hk⟩ := haodd
      have h5 : ρ ⟨a, hArNM a ha⟩ ^ orderOf a = 1 := by
        rw [← map_pow]
        have h6 : (⟨a, hArNM a ha⟩ : ↥(normalizer (M : Set X))) ^ orderOf a = 1 :=
          Subtype.ext (pow_orderOf_eq_one a)
        rw [h6, map_one]
      have h7 : ρ ⟨a, hArNM a ha⟩ * ρ ⟨a, hArNM a ha⟩ = 1 := by
        rw [← hρga, ← map_mul]
        have h8 : (⟨g, hJN hgJ⟩ : ↥(normalizer (M : Set X))) * ⟨g, hJN hgJ⟩ = 1 :=
          Subtype.ext (hFsq _ hgF')
        rw [h8, map_one]
      rw [hk, pow_succ, pow_mul, sq, h7, one_pow, one_mul] at h5
      rw [hρga, h5]
    have h8 : (ρ ⟨g, hJN hgJ⟩).support.card = 4 := by
      rw [hπ g hgJ (hJN hgJ), Perm.card_support_conj]
      exact card_support_coreImage_of_four e hgJ (hFsq _ hgF') hg1' hd.DFc (hd.Fs ⟨g, hgJ⟩ hgF')
    rw [hρ1, Perm.support_one, Finset.card_empty] at h8
    exact absurd h8 (by norm_num)
  have hrange : (F.subgroupOf (normalizer (N₁ : Set X))).map (TBLit.oddQuotAction N₁) ≤
      (MulAut.conj : (↥N₁ ⧸ O₁) →* MulAut (↥N₁ ⧸ O₁)).range := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, -, haN, hfa, -⟩ := hact g hg
    exact ⟨_, hfa.symm⟩
  have hFb4 : Nat.card Fb = 4 := by
    have h1 : Nat.card Fb = Nat.card (Fb.map MulAut.conj) :=
      (card_map_of_injective hconj_inj).symm
    rw [h1, hFbdef, Subgroup.map_comap_eq_self hrange, card_map_of_inf_ker _ _ hinj,
      Nat.card_congr (subgroupOfEquivOfLe hFN).toEquiv, (card_sq_of_klein hd.Fk).1]
  have hFbsq : ∀ x ∈ Fb, x * x = 1 := by
    intro x hx
    obtain ⟨f, hf, hfN, hfx⟩ := (hmemFb x).mp hx
    apply hconj_inj
    rw [map_mul, ← hfx, ← map_mul, map_one]
    have h2 : (⟨f, hfN⟩ : ↥(normalizer (N₁ : Set X))) * ⟨f, hfN⟩ = 1 := Subtype.ext (hFsq f hf)
    rw [h2, map_one]
  have hFbY : ∀ (l : X) (hl : l ∈ fixA M e₀ r) (hlN : l ∈ N₁),
      ((⟨l, hlN⟩ : ↥N₁) : ↥N₁ ⧸ O₁) ∈ Fb → ∀ y ∉ DY,
      ((χ ((⟨l, hl⟩ : ↥(fixA M e₀ r)) : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r)) :
        alternatingGroup (Fin 7)) : Perm (Fin 7)) y = y := by
    intro l hl hlN hlF y hy
    obtain ⟨f, hf, a, ha, haN, hla, hfaM⟩ := hFbA _ hlF
    have hlaO : ((⟨l, hl⟩ : ↥(fixA M e₀ r)) : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r)) =
        ((⟨a, ha⟩ : ↥(fixA M e₀ r)) : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r)) := by
      rw [QuotientGroup.eq]
      have h1 : (⟨l, hlN⟩ : ↥N₁)⁻¹ * ⟨a, haN⟩ ∈ O₁ := QuotientGroup.eq.mp hla
      have h2 : l⁻¹ * a ∈ fixA M e₀ r ⊓ (pPrimeCore 2 ↥N₁).map N₁.subtype :=
        mem_inf.mpr ⟨mul_mem (inv_mem hl) ha, ⟨_, h1, rfl⟩⟩
      obtain ⟨w, hw, hwe⟩ := inf_pPrimeCore_le hArN h2
      have h3 : w = (⟨l, hl⟩ : ↥(fixA M e₀ r))⁻¹ * ⟨a, ha⟩ := Subtype.ext hwe
      rw [← h3]
      exact hw
    rw [hlaO]
    refine hχ ⟨a, ha⟩ y ?_
    change ρ ⟨a, hArNM a ha⟩ _ = _
    rw [← hρfa f a hf ha hfaM]
    refine hρF f hf _ fun h => hy (hDY₀Y ?_)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hC : ∀ x ∈ Fb, x ≠ 1 → ∀ y : ↥N₁,
      (y : ↥N₁ ⧸ O₁) * x = x * (y : ↥N₁ ⧸ O₁) → (y : X) ∈ Hn E := by
    intro x hx hx1 y hyx
    obtain ⟨f, hf, hfN, hfx⟩ := (hmemFb x).mp hx
    have hf1 : f ≠ 1 := by
      rintro rfl
      apply hx1
      apply hconj_inj
      rw [← hfx, map_one]
      exact map_one _
    have hfix' : (y : ↥N₁ ⧸ O₁) ∈ Open.signalizerFixedSubgroup (coreQuotAut N₁ ⟨f, hfN⟩) := by
      change coreQuotAut N₁ ⟨f, hfN⟩ (y : ↥N₁ ⧸ O₁) = (y : ↥N₁ ⧸ O₁)
      rw [← He9.oddQuotAction_eq_coreQuotAut, hfx, MulAut.conj_apply, ← hyx]
      group
    obtain ⟨w, hwC, hwy⟩ := fixed_le_map_centralizer hfN (hFsq f hf) hfix'
    have hwH : (w : X) ∈ Hn E := hFH f hf hf1 hwC
    have h1 : w⁻¹ * y ∈ O₁ := QuotientGroup.eq.mp hwy
    have h2 : ((w⁻¹ * y : ↥N₁) : X) ∈ Hn E := hOH ⟨_, h1, rfl⟩
    have h3 := mul_mem hwH h2
    simpa using h3
  exact He9.le_of_held_pump_of_centralizer he₀2 he₀N₁ hN₁perf (inf_le_right.trans he₀H) hOH
    hArY hlayer χ Fb (fun x hx => by
      obtain ⟨-, -, a, ha, haN, hla, -⟩ := hFbA x hx
      exact ⟨a, ha, haN, hla.symm⟩) hFb4 hFbsq hDY hFbY hC ψ

end SwapP2

end CFSG.ComponentClassification.SolMax
