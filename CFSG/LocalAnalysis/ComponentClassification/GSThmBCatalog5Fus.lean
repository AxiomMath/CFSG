module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CenterData
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OuterRow

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def CF23Exception (N J : Type) [Group N] [Group J] : Prop :=
  (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧ Nonempty (J ≃* alternatingGroup (Fin n)) ∧
      (Nonempty (N ≃* alternatingGroup (Fin (n + 2))) ∨
        Nonempty (N ≃* alternatingGroup (Fin (n + 4))))) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel J .PSL 2 p (2 * f) ∧
      (Blueprint.LieModel N .PSL 4 p f ∨ Blueprint.LieModel N .PSU 4 p f ∨
        (∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel N .POmegaMinus 4 p e) ∨
        Blueprint.LieModel N .PSp 2 p f)) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel J .PSL 2 p f ∧
      Blueprint.LieModel N .PSL 2 p (2 * f))

@[expose] def CF23InnerFusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal →
    centralizer (N : Set G) = ⊥ → GSRestricted ↥N →
    ∀ (α : G) (J : Subgroup G), orderOf α = 2 → J ≤ N →
      J ≤ centralizer ({α} : Set G) → IsComponent (J.subgroupOf (centralizer ({α} : Set G))) →
      IsStandardSubgroup J →
      ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p f) ∨
        Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7))) →
      Odd (Nat.card (center ↥J)) → ¬ CF23Exception ↥N (↥J ⧸ center ↥J) →
      ∀ ζ ∈ J, orderOf ζ = 2 → ∃ γ ∈ N, γ⁻¹ * α * γ = α * ζ

@[expose] def Hyp52.Fus23Concl {H : Type} [Group H] [Finite H] (h : Hyp52 H) : Prop :=
  ∃ z : H, z ∈ h.D ∧ (∀ s ∈ h.S, s * z = z * s) ∧ orderOf z = 2 ∧ z ∉ h.P ∧
    ∃ g ∈ h.W, g⁻¹ * h.a * g = h.a * z

theorem Hyp52.fus23ConclW_of_fus23Concl {H : Type} [Group H] [Finite H] {h : Hyp52 H}
    (hc : h.Fus23Concl) : h.Fus23ConclW := by
  obtain ⟨z, hzD, hzS, -, hzP, g, hgW, hg⟩ := hc
  have haz : h.a * z ∈ h.S := mul_mem h.a_mem_S (h.D_le_S hzD)
  have hazP : h.a * z ∉ h.P := fun hP =>
    hzP (by simpa using mul_mem (inv_mem h.a_mem_P) hP)
  refine ⟨g, hgW, hg ▸ haz, hg ▸ hazP, ?_⟩
  rw [hg]
  refine mem_inf.mpr ⟨mul_mem (subset_closure (Set.mem_union_right _ rfl))
    (subset_closure (Set.mem_union_left _ hzD)), ?_⟩
  rw [mem_centralizer_singleton_iff]
  rw [mul_assoc, ← hzS h.x h.x_mem, ← mul_assoc, h.x_comm_a.symm, mul_assoc]

@[expose] def CF23L34Step : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), ¬ h.Table54 →
    Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2 → h.Fus23ConclW

@[expose] def CF23CoverStep : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), ¬ h.Table54 →
    center (OddBar h.K) ≠ ⊥ →
    (Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f) → h.Fus23ConclW

namespace Fus23

open CatFactsL4U4 CatFactsL4U4.OutInv

variable {H : Type} [Group H] [Finite H]

theorem exists_z (h : Hyp52 H) (hZJ : center (OddBar h.J) = ⊥) :
    ∃ z : H, z ∈ h.D ∧ (∀ s ∈ h.S, s * z = z * s) ∧ orderOf z = 2 ∧ z ∉ h.P := by
  obtain ⟨z, hzD, hzS, hz2⟩ := h.exists_involution_D_center
  refine ⟨z, hzD, hzS, hz2, fun hzP => ?_⟩
  have h1 : z ∈ h.D ⊓ h.P := mem_inf.mpr ⟨hzD, hzP⟩
  rw [h.D_inf_P_eq_bot hZJ, mem_bot] at h1
  rw [h1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem eq_one_of_mem_B_zStar (h : Hyp52 H) (hZK : center (OddBar h.K) = ⊥) {y : H}
    (hy : y ∈ h.B ⊓ (Open.fusionZStar ↥h.K).map h.K.subtype) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hyB, hyZ⟩ := mem_inf.mp hy
  rw [map_fusionZStar_eq] at hyZ
  have hodd := odd_orderOf_of_mem_oddCoreIn (inf_coreActionKernel_le_of_center_eq_bot hZK hyZ)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp h.isPGroup_B) ⟨y, hyB⟩
  rw [Subgroup.orderOf_mk] at hn
  rw [hn] at hodd
  rcases n with _ | n
  · rw [pow_zero] at hn
    exact orderOf_eq_one_iff.mp hn
  · exfalso
    rw [pow_succ] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)

section Eq

variable {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

include hKa in
theorem odd_card_center_Jhat (hZJ : center (OddBar h.J) = ⊥) :
    Odd (Nat.card (center ↥(Jhat hKa))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJBW : GSLit.fixedLayer h.J h.B ≤ h.W := (fixedLayer_le_K h hKa).trans (K_le_W h)
  have h1 : Nat.card (Jhat hKa) ∣ Nat.card (GSLit.fixedLayer h.J h.B) := by
    have h2 : Nat.card (Jhat hKa) ∣ Nat.card (wbarImage h.B (GSLit.fixedLayer h.J h.B)) :=
      Subgroup.card_map_dvd _ _
    have h3 : Nat.card (wbarImage h.B (GSLit.fixedLayer h.J h.B)) ∣
        Nat.card ((GSLit.fixedLayer h.J h.B).subgroupOf h.W) := Subgroup.card_map_dvd _ _
    rw [Nat.card_congr (subgroupOfEquivOfLe hJBW).toEquiv] at h3
    exact h2.trans h3
  obtain ⟨e1, -⟩ := exists_oddBar_JB_equiv h
  obtain ⟨eJ⟩ := nonempty_Jhat_equiv hKa hZJ
  have hJB := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B))
  have hJh := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(Jhat hKa))
  rw [Nat.card_congr e1.toEquiv] at hJB
  rw [Nat.card_congr eJ.toEquiv] at hJh
  rw [hJB, hJh] at h1
  have hpos : 0 < Nat.card (OddBar h.J) := Nat.card_pos
  exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    (Nat.dvd_of_mul_dvd_mul_left hpos h1)

include hKa in
theorem exists_conj_of_inner {z : H} (hzK : z ∈ h.K) (hza : z * h.a = h.a * z)
    (hz2 : z * z = 1) {γ : ↥(GAut hKa)} (hγN : γ ∈ NL hKa)
    (hγ : γ⁻¹ * phi hKa (abar h) * γ =
      phi hKa (abar h) * phi hKa (wbarMk h.B ⟨z, K_le_W h hzK⟩)) :
    ∃ g ∈ h.K, ∃ y ∈ h.B ⊓ (Open.fusionZStar ↥h.K).map h.K.subtype,
      g⁻¹ * h.a * g = h.a * z * y := by
  rw [mem_subgroupOf] at hγN
  obtain ⟨l, hl⟩ := hγN
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective l
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  set aw : h.W := ⟨h.a, h.a_mem_normalizer⟩ with haw
  set zw : h.W := ⟨z, K_le_W h hzK⟩ with hzw
  set kw : h.W := ⟨k, K_le_W h k.2⟩ with hkw
  have h1 : rhoL hKa (kw⁻¹ * aw * kw) = rhoL hKa (aw * zw) := by
    have h2 := congrArg (fun g : ↥(GAut hKa) => (g : MulAut (LK h))) hγ
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [← hl] at h2
    rw [map_mul, map_mul, map_inv, map_mul, hkw, rhoL_of_mem_K]
    exact h2
  have h3 : rhoL hKa ((aw * zw)⁻¹ * (kw⁻¹ * aw * kw)) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h4 := (rhoL_eq_one_iff hKa _).mp h3
  have hcker : (h.a * z)⁻¹ * ((k : H)⁻¹ * h.a * (k : H)⁻¹⁻¹) ∈ coreActionKernel h.K := by
    rw [inv_inv]
    simpa [haw, hzw, hkw] using h4
  exact exists_conj_eq_of_mem_kernel hKa hzK hza hz2 (inv_mem k.2) hcker

include hKa in
theorem concl_of_eq (hI : CF23InnerFusion) (hT : ¬ h.Table54)
    (hZK : center (OddBar h.K) = ⊥) (hZJ : center (OddBar h.J) = ⊥)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f) : h.Fus23ConclW := by
  refine Hyp52.fus23ConclW_of_fus23Concl ?_
  obtain ⟨eN⟩ := nonempty_NL_equiv hKa
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  obtain ⟨eJ⟩ := nonempty_Jhat_equiv hKa hZJ
  let eK : OddBar h.K ≃* LK h :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZK.symm)
  have hres : GSRestricted ↥(NL hKa) := by
    rcases h.type_K with hr | ⟨hne, -⟩
    · exact OddQuot.gsRestricted_of_mulEquiv (eZ.symm.trans eN.symm) hr
    · exact absurd hKa hne
  have hJt : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (↥(Jhat hKa) ⧸ center ↥(Jhat hKa)) .PSL 2 p f) ∨
      Nonempty (↥(Jhat hKa) ⧸ center ↥(Jhat hKa) ≃* alternatingGroup (Fin 7)) := by
    rcases hJ with hA | ⟨p, f, hp, hp2, hf, hq, hm⟩
    · obtain ⟨e7⟩ := hA
      exact Or.inr ⟨eJ.trans e7⟩
    · exact Or.inl ⟨p, f, hp, hp2, hf, hq, OddQuot.lieModel_of_equiv eJ.symm hm⟩
  have hexc : ¬ CF23Exception ↥(NL hKa) (↥(Jhat hKa) ⧸ center ↥(Jhat hKa)) := by
    intro hE
    unfold CF23Exception at hE
    rcases hE with ⟨n, hn, ⟨e1⟩, hN⟩ | ⟨p, f, hp, hp2, hf, hm, hN⟩ |
        ⟨p, f, hp, hp2, hf, hq, hm, hN⟩
    · refine hT (Or.inl ⟨n, hn, ⟨eJ.symm.trans e1⟩, Or.inl ⟨hKa, ?_⟩⟩)
      rcases hN with hN | hN
      · obtain ⟨e2⟩ := hN
        exact Or.inl ⟨(eK.trans eN.symm).trans e2⟩
      · obtain ⟨e2⟩ := hN
        exact Or.inr ⟨(eK.trans eN.symm).trans e2⟩
    · have hmJ := OddQuot.lieModel_of_equiv eJ hm
      rcases hN with hN | hN | ⟨e, he, hN⟩ | hN
      · exact hT (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hmJ, hKa,
          Or.inl (OddQuot.lieModel_of_equiv (eN.trans eZ) hN)⟩))))
      · exact hT (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hmJ, hKa,
          Or.inr (Or.inl (OddQuot.lieModel_of_equiv (eN.trans eZ) hN))⟩))))
      · exact hT (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hmJ, hKa,
          Or.inr (Or.inr ⟨e, he, OddQuot.lieModel_of_equiv (eN.trans eZ) hN⟩)⟩))))
      · exact hT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨p, f, hp, hp2, hf, hmJ, hKa, OddQuot.lieModel_of_equiv (eN.trans eK.symm) hN⟩))))))
    · have hmJ := OddQuot.lieModel_of_equiv eJ hm
      have hmK := OddQuot.lieModel_of_equiv (eN.trans eK.symm) hN
      exact hT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, f, hp, hp2, hf, hq, hmJ, hKa, hmK⟩)))))
  obtain ⟨z, hzD, hzS, hz2, hzP⟩ := exists_z h hZJ
  refine ⟨z, hzD, hzS, hz2, hzP, ?_⟩
  have hzJB := mem_fixedLayer_of_mem_D h hzD hzS hz2
  have hzK : z ∈ h.K := fixedLayer_le_K h hKa hzJB
  have hza : z * h.a = h.a * z := h.comm_a (h.D_le_S hzD)
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  set ζ : ↥(GAut hKa) := phi hKa (wbarMk h.B ⟨z, K_le_W h hzK⟩) with hζ
  have hζJ : ζ ∈ Jhat hKa := ⟨wbarMk h.B ⟨z, K_le_W h hzK⟩, ⟨⟨z, K_le_W h hzK⟩, hzJB, rfl⟩, rfl⟩
  obtain ⟨γ, hγN, hγ⟩ : ∃ γ ∈ NL hKa, γ⁻¹ * phi hKa (abar h) * γ = phi hKa (abar h) * ζ := by
    by_cases hζ1 : ζ = 1
    · exact ⟨1, one_mem _, by rw [hζ1]; group⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hζ2 : ζ * ζ = 1 := by
        rw [hζ, ← map_mul, ← map_mul, ← map_one (phi hKa), ← map_one (wbarMk h.B)]
        congr 2
        exact Subtype.ext hz2'
      have hζo : orderOf ζ = 2 := orderOf_eq_prime (by rw [sq]; exact hζ2) hζ1
      exact hI _ (NL hKa) (NL_normal hKa) (centralizer_NL hKa) hres _ _ (orderOf_phi_abar' hKa)
        (Jhat_le_NL hKa) (Jhat_component hKa).1 (Jhat_component hKa).2 (Jhat_standard hKa) hJt
        (odd_card_center_Jhat hKa hZJ) hexc ζ hζJ hζo
  obtain ⟨g, hgK, y, hy, hg⟩ := exists_conj_of_inner hKa hzK hza hz2' hγN hγ
  refine ⟨g, K_le_W h hgK, ?_⟩
  rw [hg, eq_one_of_mem_B_zStar h hZK hy, mul_one]

end Eq

theorem concl_of_ne (h : Hyp52 H) (hKa : conjugate h.K h.a ≠ h.K)
    (hZK : center (OddBar h.K) = ⊥) (hZJ : center (OddBar h.J) = ⊥) : h.Fus23Concl := by
  obtain ⟨z, hzD, hzS, hz2, hzP⟩ := exists_z h hZJ
  refine ⟨z, hzD, hzS, hz2, hzP, ?_⟩
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have hainv : h.a⁻¹ = h.a := inv_eq_of_mul_eq_one_right ha2
  have hzJB := mem_fixedLayer_of_mem_D h hzD hzS hz2
  have hzV : z ∈ h.K ⊔ conjugate h.K h.a := by
    rw [h.layer_eq_K]
    exact B5a.fixedLayer_le_V h hzJB
  have hza : z * h.a = h.a * z := h.comm_a (h.D_le_S hzD)
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  obtain ⟨hVK, -, hO1, hO2⟩ := IdxKa.sup_facts h
  have hKaN : conjugate h.K h.a ≤ normalizer (h.K : Set H) := le_sup_right.trans hVK
  obtain ⟨k, hk, k', hk', hkk'⟩ := IdxKa.exists_mul_of_mem_sup hKaN hzV
  obtain ⟨hKaW, hKac⟩ := IdxKa.isPComponent_Ka h
  have hKW : h.K ≤ h.W := h.isPComponent_K.1
  have hKaC : conjugate h.K h.a ≤ coreActionKernel h.K :=
    B5a.le_coreActionKernel_of_ne hKW hKaW h.isPComponent_K.2 hKac (Ne.symm hKa)
  have hKC : h.K ≤ coreActionKernel (conjugate h.K h.a) :=
    B5a.le_coreActionKernel_of_ne hKaW hKW hKac h.isPComponent_K.2 hKa
  have hm : h.a⁻¹ * k⁻¹ * h.a ∈ conjugate h.K h.a := conj_mem_conjugate (inv_mem hk) h.a
  have hn : h.a⁻¹ * k' * h.a ∈ h.K := by
    have h1 := mem_conjugate_iff.mp hk'
    rw [hainv] at h1 ⊢
    exact h1
  have R1 : h.a⁻¹ * (k * k') * h.a = k * k' := by
    rw [hkk', mul_assoc, hza, inv_mul_cancel_left]
  have R2 : (k * k') * (k * k') = 1 := by rw [hkk']; exact hz2'
  have hm' : h.a⁻¹ * k⁻¹ * h.a = (h.a⁻¹ * k' * h.a) * k'⁻¹ * k⁻¹ := by
    calc h.a⁻¹ * k⁻¹ * h.a = (h.a⁻¹ * k' * h.a) * (h.a⁻¹ * (k * k') * h.a)⁻¹ := by group
      _ = (h.a⁻¹ * k' * h.a) * k'⁻¹ * k⁻¹ := by rw [R1]; group
  have hk'2 : k' * k' = k' * k⁻¹ * k'⁻¹ * k⁻¹ := by
    calc k' * k' = k' * k⁻¹ * k'⁻¹ * k⁻¹ * ((k * k') * (k * k')) := by group
      _ = k' * k⁻¹ * k'⁻¹ * k⁻¹ := by rw [R2, mul_one]
  obtain ⟨c, hc⟩ : ∃ c : H, c = (h.a * z)⁻¹ * (k⁻¹ * h.a * k) := ⟨_, rfl⟩
  have hcK : c = k'⁻¹ * (k⁻¹ * (h.a⁻¹ * k⁻¹ * h.a) * k⁻¹⁻¹) := by
    rw [hc, ← hkk']
    group
  have hcV : c ∈ h.K ⊔ conjugate h.K h.a := by
    rw [hcK]
    exact mul_mem (inv_mem (mem_sup_right hk')) (mul_mem (mul_mem (inv_mem (mem_sup_left hk))
      (mem_sup_right hm)) (inv_mem (inv_mem (mem_sup_left hk))))
  have hcC : c ∈ coreActionKernel h.K := by
    rw [hcK]
    exact mul_mem (inv_mem (hKaC hk'))
      (OutInv.conj_mem_coreActionKernel (inv_mem (le_normalizer hk)) (hKaC hm))
  have hcCa : c ∈ coreActionKernel (conjugate h.K h.a) := by
    have e : c = (k'⁻¹ * (k⁻¹ * (h.a⁻¹ * k' * h.a)) * k'⁻¹⁻¹) *
        (k' * k⁻¹ * k'⁻¹ * k⁻¹)⁻¹ := by
      rw [← hk'2, hcK, hm']
      group
    rw [e]
    refine mul_mem (OutInv.conj_mem_coreActionKernel (inv_mem (le_normalizer hk'))
      (mul_mem (inv_mem (hKC hk)) (hKC hn))) (inv_mem ?_)
    exact mul_mem (OutInv.conj_mem_coreActionKernel (le_normalizer hk') (inv_mem (hKC hk)))
      (inv_mem (hKC hk))
  obtain ⟨c₁, hc₁, c₂, hc₂, hc12⟩ := IdxKa.exists_mul_of_mem_sup hKaN hcV
  have hc₁O : c₁ ∈ oddCoreIn h.K := by
    have e : c₁ = c * c₂⁻¹ := by rw [← hc12]; group
    have h1 : c₁ ∈ coreActionKernel h.K := by
      rw [e]
      exact mul_mem hcC (inv_mem (hKaC hc₂))
    exact inf_coreActionKernel_le_of_center_eq_bot hZK (mem_inf.mpr ⟨hc₁, h1⟩)
  have hc₂C : c₂ ∈ coreActionKernel (conjugate h.K h.a) := by
    have e : c₂ = c₁⁻¹ * c := by rw [← hc12]; group
    rw [e]
    exact mul_mem (inv_mem (hKC hc₁)) hcCa
  have hKaa : conjugate (conjugate h.K h.a) h.a = h.K := by
    rw [← IdxKa.conjugate_mul, ha2, IdxKa.conjugate_one]
  have hd : h.a⁻¹ * c₂ * h.a ∈ oddCoreIn h.K := by
    have h1 := B5a.conj_mem_coreActionKernel_conjugate hc₂C h.a
    rw [hKaa] at h1
    have h2 : h.a⁻¹ * c₂ * h.a ∈ h.K := by
      have h3 := mem_conjugate_iff.mp hc₂
      rw [hainv] at h3 ⊢
      exact h3
    exact inf_coreActionKernel_le_of_center_eq_bot hZK (mem_inf.mpr ⟨h2, h1⟩)
  have haN : h.a ∈ normalizer ((oddCoreIn (h.K ⊔ conjugate h.K h.a) : Subgroup H) : Set H) := by
    rw [h.layer_eq_K]
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _
      (OddQuot.le_normalizer_layerIn h.W h.a_mem_normalizer)
  have hc₂O : c₂ ∈ oddCoreIn (h.K ⊔ conjugate h.K h.a) := by
    have h1 := (mem_normalizer_iff.mp haN (h.a⁻¹ * c₂ * h.a)).mp (hO1 hd)
    rwa [show h.a * (h.a⁻¹ * c₂ * h.a) * h.a⁻¹ = c₂ by group] at h1
  have hcO : c ∈ oddCoreIn (h.K ⊔ conjugate h.K h.a) := by
    rw [← hc12]
    exact mul_mem (hO1 hc₁O) hc₂O
  have hcodd : Odd (orderOf c) := odd_orderOf_of_mem_oddCoreIn hcO
  have hd2 : (h.a * z) * (h.a * z) = 1 := by
    calc h.a * z * (h.a * z) = h.a * (z * h.a) * z := by group
      _ = h.a * (h.a * z) * z := by rw [hza]
      _ = (h.a * h.a) * (z * z) := by group
      _ = 1 := by rw [ha2, hz2', one_mul]
  have hdc : (h.a * z) * c = k⁻¹ * h.a * k := by rw [hc]; group
  have hdc2 : ((h.a * z) * c) * ((h.a * z) * c) = 1 := by
    rw [hdc]
    calc k⁻¹ * h.a * k * (k⁻¹ * h.a * k) = k⁻¹ * (h.a * h.a) * k := by group
      _ = 1 := by rw [ha2]; group
  obtain ⟨n, hn⟩ := exists_zpow_conj_eq_of_odd hd2 hdc2 hcodd
  refine ⟨k * c ^ n, mul_mem (hKW hk) (zpow_mem ((sup_le hKW hKaW) hcV) n), ?_⟩
  calc (k * c ^ n)⁻¹ * h.a * (k * c ^ n) = (c ^ n)⁻¹ * (k⁻¹ * h.a * k) * c ^ n := by group
    _ = (c ^ n)⁻¹ * ((h.a * z) * c) * c ^ n := by rw [hdc]
    _ = h.a * z := hn

theorem concl_of_small (hI : CF23InnerFusion) (h3 : CF23CoverStep) (h : Hyp52 H)
    (hT : ¬ h.Table54)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f) : h.Fus23ConclW := by
  have hZJ : center (OddBar h.J) = ⊥ := by
    rcases hJ with hA | ⟨p, f, -, -, -, -, hm⟩
    · obtain ⟨e⟩ := hA
      exact IdxRed.center_eq_bot_of_alt (by norm_num) e
    · exact IdxRed.center_eq_bot_of_psl2 hm
  by_cases hZK : center (OddBar h.K) = ⊥
  · by_cases hKa : conjugate h.K h.a = h.K
    · exact concl_of_eq hKa hI hT hZK hZJ hJ
    · exact Hyp52.fus23ConclW_of_fus23Concl (concl_of_ne h hKa hZK hZJ)
  · exact h3 H h hT hZK hJ

end Fus23

theorem cfProp23Fusion_of (hI : CF23InnerFusion) (h1 : CF23L34Step) (h3 : CF23CoverStep) :
    CFProp23Fusion := by
  intro H _ _ h hT
  show h.Fus23ConclW
  rcases h.smallType with hA | hL | hL34
  · exact Fus23.concl_of_small hI h3 h hT (Or.inl hA)
  · exact Fus23.concl_of_small hI h3 h hT (Or.inr hL)
  · exact h1 H h hT hL34

end CFSG.ComponentClassification.GSThmB
