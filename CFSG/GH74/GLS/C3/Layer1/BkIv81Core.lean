module

public import CFSG.GH74.GLS.C3.Layer1.BkIv81Aux
public import CFSG.GH74.GLS.C3.Layer1.BkIv81Layer
public import CFSG.LocalAnalysis.ComponentClassification.GSLitFixedLayer
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic12
public import CFSG.GH74.GLS.C3.Layer1.Back91Core
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.LocalAnalysis.ComponentClassification.GSLitReach

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
  CFSG.ComponentClassification.UnbalancedLayer CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_fixedLayer {M L : Subgroup G} {u : G} (hL : IsPCompIn 2 M L)
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (huC : u ∈ CMK M L) (hu : orderOf u = 2) :
    ∃ K₀ : Subgroup G, K₀ ≤ L ∧ K₀ ≤ centralizer ({u} : Set G) ∧
      IsPCompIn 2 (M ⊓ centralizer ({u} : Set G)) K₀ ∧ L ≤ K₀ ⊔ pPrimeCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨huM, huL, huO, hucomm⟩ := U1a.mem_CMK_iff.1 huC
  have hLM : L ≤ M := hL.1
  have hJq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := TwoThin.isQuasisimple_hat hL
  have hcomm : ∀ j ∈ L, j⁻¹ * u⁻¹ * j * u ∈ (pPrimeCore 2 ↥L).map L.subtype := by
    intro j hj
    have h := (U1a.mem_CMK_iff.1 (inv_mem huC)).2.2.2 j⁻¹ (inv_mem hj)
    have e : ⁅j⁻¹, u⁻¹⁆ = j⁻¹ * u⁻¹ * j * u := by simp [commutatorElement_def]
    rw [e] at h
    exact h
  have huker : zpowers u ≤ coreActionKernel L := by
    rw [Subgroup.zpowers_le]
    exact ⟨huL, hcomm⟩
  have hE2 : IsPGroup 2 ↥(zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  have hnormal : (L.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLM]
    exact fun h k hh hk => hLn k hk h hh
  have hcen : centralizer ((zpowers u : Subgroup G) : Set G) = centralizer ({u} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hPC := ComponentClassification.GSLit.fixedLayer_isPComponent hLM hnormal.isSubnormal
    (zpowers_le.mpr huM) huker hE2 hJq
  rw [hcen] at hPC
  have hle := ComponentClassification.GSLit.fixedLayer_le_inf L (zpowers u)
  rw [hcen] at hle
  obtain ⟨hsup, -⟩ := ComponentClassification.GSLit.fixedLayer_sup_pPrimeCore hJq huker hE2
  refine ⟨ComponentClassification.GSLit.fixedLayer L (zpowers u), hle.trans inf_le_left,
    hle.trans inf_le_right, ⟨hle.trans (inf_le_inf_right _ hLM), hPC⟩, ?_⟩
  exact hsup.ge


theorem even_card_of_isPCompIn {M L : Subgroup G} (hL : IsPCompIn 2 M L) : Even (Nat.card L) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hsolv : Group.IsSolvable ↥L := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨-, hsimple, a, b, hab⟩ := TwoThin.isQuasisimple_hat hL
  have h1 : Group.IsSolvable (↥L ⧸ pPrimeCore 2 ↥L) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  have h2 : Group.IsSolvable ((↥L ⧸ pPrimeCore 2 ↥L) ⧸ center (↥L ⧸ pPrimeCore 2 ↥L)) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr h2 a b)

omit [Finite G] in
theorem mem_normalizer_of_commute {R : Subgroup G} {u : G} (h : ∀ r ∈ R, u * r = r * u) :
    u ∈ normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    have : u * r * u⁻¹ = r := by rw [h r hr]; group
    rw [this]; exact hr
  · intro hr
    have h2 := h _ hr
    have : u * r * u⁻¹ = r := by
      have h3 : u * (u * r * u⁻¹) = (u * r * u⁻¹) * u := h _ hr
      have : u * r * u⁻¹ * u = u * r := by group
      rw [this] at h3
      exact mul_left_cancel h3
    rwa [this] at hr


theorem frattini_wrap {M L S : Subgroup G} (hLM : L ≤ M) (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hS : IsSylowOf 2 S L) : ∀ n ∈ M, ∃ m ∈ L, ∃ x ∈ normalizer (S : Set G), n = m * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := isSylowOf_iff.mp hS
  exact Stage1.Thm3.Sec8.Basic.exists_mul_mem_normalizer (p := 2) hLM hLn h.1 h.2.1 h.2.2

theorem key_normalized (hG : IsSimpleGroup G) {M L Q : Subgroup G} (hM : IsCoatom M)
    (hL : IsPCompIn 2 M L) (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hQ : IsSylowOf 2 Q (CMK M L)) (hΓ : gammaK 2 Q 1 ≤ M) {g : G}
    (hR : conjugate Q g ⊓ M ≠ ⊥) (hRn : conjugate Q g ⊓ M ≤ normalizer (Q : Set G))
    (hLg : L ≤ conjugate M g) : g ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ M := hL.1
  have hL0 : L ≠ ⊥ := by
    intro h
    have := even_card_of_isPCompIn hL
    rw [h, Subgroup.card_bot] at this
    exact absurd this (by decide)
  have hNL : normalizer (L : Set G) = M := normalizer_eq_of_coatom hG hM hLM hLn hL0
  have hM0 : M ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ hLM))
  have hNM : normalizer (M : Set G) = M := normalizer_eq_self_of_coatom hG hM hM0
  set R := conjugate Q g ⊓ M with hRdef
  have hQ2 : IsPGroup 2 Q := hQ.isPGroup
  have hR2 : IsPGroup 2 R := (isPGroup_conjugate' hQ2 g).to_le inf_le_left
  have hQne : Q ≠ ⊥ := by
    intro h
    apply hR
    rw [hRdef, h]
    simp [conjugate]
  obtain ⟨u, huQ, hu2, huR, -⟩ := exists_involution_central hQ2 hR2 hQne hRn
  have huC : u ∈ CMK M L := hQ.le huQ
  have huM : u ∈ M := (U1a.mem_CMK_iff.1 huC).1
  have hCu : centralizer ({u} : Set G) ≤ M := (U1a.centralizer_le_gammaK huQ hu2).trans hΓ
  have huX : u ∈ conjugate M g := by
    have h1 : normalizer (R : Set G) ≤ conjugate M g :=
      normalizer_le_conjugate hΓ inf_le_left (one_le_pRank_of_ne_bot hR2 hR)
    exact h1 (mem_normalizer_of_commute huR)
  obtain ⟨K₀, hK₀L, hK₀C, hK₀P, hK₀cov⟩ := exists_fixedLayer hL hLn huC hu2
  set X := conjugate M g with hXdef
  have hK₀X : K₀ ≤ X ⊓ centralizer ({u} : Set G) := le_inf (hK₀L.trans hLg) hK₀C
  have hXC : X ⊓ centralizer ({u} : Set G) ≤ M ⊓ centralizer ({u} : Set G) :=
    le_inf (inf_le_right.trans hCu) inf_le_right
  have hK₀P' : IsPCompIn 2 (X ⊓ centralizer ({u} : Set G)) K₀ := isPCompIn_of_le hK₀P hK₀X hXC
  have hcX : cmap g X = M := cmap_cancel g M
  set u' := g * u * g⁻¹ with hu'
  have hu'M : u' ∈ M := mem_conjugate_iff'.mp huX
  have hu'2 : orderOf u' = 2 := by
    rw [← hu2]
    exact MulEquiv.orderOf_eq (MulAut.conj g) u
  have hinf : cmap g (X ⊓ centralizer ({u} : Set G)) = M ⊓ centralizer ({u'} : Set G) := by
    rw [cmap, Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, ← cmap, hcX]
    congr 1
    have := ComponentClassification.GSLit.map_centralizer_singleton (MulAut.conj g) u
    rw [this]
    simp [hu', MulAut.conj_apply]
  have hK₀P'' : IsPCompIn 2 (M ⊓ centralizer ({u'} : Set G)) (cmap g K₀) := by
    have := isPCompIn_cmap hK₀P' g
    rwa [hinf] at this
  have hK₀'le : cmap g K₀ ≤ M ⊓ centralizer ({u'} : Set G) := hK₀P''.1
  rcases dichotomy_sub hL hLn hu'2 hu'M hK₀P'' with h | h
  ·
    have hK₀'L : cmap g K₀ ≤ L := by
      refine le_of_perfect_of_le_sup_odd (perfect_of_isPCompIn hK₀P'')
        (TwoThin.card_pPrimeCoreOf_odd M) ?_ h
      intro x hx
      exact U1a.mem_normalizer_of_norm hLn (TwoThin.pPrimeCoreOf_le M hx)
    set L₁ := cmap g L with hL₁
    have hL₁M : L₁ ≤ M := by
      intro y hy
      have h1 : g⁻¹ * y * g ∈ L := mem_cmap.mp hy
      have h2 := hLg h1
      rw [mem_conjugate_iff'] at h2
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rwa [e] at h2
    have hK₀L₁ : cmap g K₀ ≤ L₁ := Subgroup.map_mono hK₀L
    have hperf₁ : ⁅L₁, L₁⁆ = L₁ := by
      rw [hL₁, cmap, ← Subgroup.map_commutator, perfect_of_isPCompIn hL]
    have hO₁ : Odd (Nat.card ↥(cmap g (pPrimeCoreOf 2 L))) := by
      rw [cmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact TwoThin.card_pPrimeCoreOf_odd L
    have hOn : cmap g (pPrimeCoreOf 2 L) ≤ normalizer ((L ⊓ L₁ : Subgroup G) : Set G) := by
      intro o ho
      have hoL₁ : o ∈ L₁ := Subgroup.map_mono (TwoThin.pPrimeCoreOf_le L) ho
      have hoM := hL₁M hoL₁
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyL, hyL₁⟩
        exact ⟨hLn o hoM y hyL, L₁.mul_mem (L₁.mul_mem hoL₁ hyL₁) (L₁.inv_mem hoL₁)⟩
      · rintro ⟨hyL, hyL₁⟩
        refine ⟨?_, ?_⟩
        · have := hLn o⁻¹ (M.inv_mem hoM) _ hyL
          simpa [mul_assoc] using this
        · have := L₁.mul_mem (L₁.mul_mem (L₁.inv_mem hoL₁) hyL₁) hoL₁
          simpa [mul_assoc] using this
    have hcov₁ : L₁ ≤ (L ⊓ L₁) ⊔ cmap g (pPrimeCoreOf 2 L) := by
      have h1 : L₁ ≤ cmap g K₀ ⊔ cmap g (pPrimeCoreOf 2 L) := by
        rw [← Subgroup.map_sup]
        exact Subgroup.map_mono hK₀cov
      exact h1.trans (sup_le_sup_right (le_inf hK₀'L hK₀L₁) _)
    have hL₁N' : L₁ ≤ L ⊓ L₁ := le_of_perfect_of_le_sup_odd hperf₁ hO₁ hOn hcov₁
    have hL₁L : L₁ ≤ L := hL₁N'.trans inf_le_left
    have hLeq : L₁ = L := Subgroup.eq_of_le_of_card_ge hL₁L (by
      rw [hL₁, cmap, Subgroup.card_map_of_injective (MulAut.conj g).injective])
    have hgN : g ∈ normalizer (L : Set G) := by
      have e : ∀ h : G, g * h * g⁻¹ ∈ L₁ ↔ h ∈ L := fun h => by
        rw [hL₁, mem_cmap]
        have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
        rw [e]
      rw [hLeq] at e
      rw [Subgroup.mem_normalizer_iff]
      intro h
      exact (e h).symm
    rw [hNL] at hgN
    exact hgN
  ·
    have hK₀'C : cmap g K₀ ≤ CMK M L := by
      intro k hk
      have hkM : k ∈ M := (hK₀'le hk).1
      refine U1a.mem_CMK_iff.2 ⟨hkM, U1a.mem_normalizer_of_norm hLn hkM,
        U1a.mem_normalizer_pPrimeCoreOf hLn hkM, fun l hl => ?_⟩
      have h1 : ⁅k, l⁆ ∈ pPrimeCoreOf 2 M := h (Subgroup.commutator_mem_commutator hk hl)
      have h2 : ⁅k, l⁆ ∈ L := by
        rw [commutatorElement_def]
        exact L.mul_mem (hLn k hkM l hl) (L.inv_mem hl)
      have h3 : ⁅k, l⁆ ∈ pPrimeCoreOf 2 L := inf_pPrimeCoreOf_le' hLM ⟨h2, h1⟩
      rw [← commutatorElement_inv k l]
      exact (pPrimeCoreOf 2 L).inv_mem h3
    obtain ⟨S, hS⟩ := exists_isSylowOf 2 K₀
    have hcover : IsSylowOf 2 S L :=
      isSylowOf_of_cover hK₀L (TwoThin.pPrimeCoreOf_le L) (TwoThin.card_pPrimeCoreOf_odd L)
        (fun l hl o ho => TwoThin.pPrimeCoreOf_normalized L hl ho) hK₀cov hS
    have hS2 : IsPGroup 2 S := hS.isPGroup
    have hSne : S ≠ ⊥ := by
      intro hb
      have hc := hcover.card_eq
      rw [hb, Subgroup.card_bot] at hc
      have hev := even_iff_two_dvd.mp (even_card_of_isPCompIn hL)
      have hpos : 0 < (Nat.card L).factorization 2 :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hev
      have : 2 ≤ 2 ^ (Nat.card L).factorization 2 := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (Nat.card L).factorization 2 := Nat.pow_le_pow_right (by norm_num) hpos
      omega
    have hS'K : cmap g S ≤ CMK M L := (Subgroup.map_mono hS.le).trans hK₀'C
    have hS'2 : IsPGroup 2 (cmap g S) := hS2.map (MulAut.conj g).toMonoidHom
    obtain ⟨k, hk, hkS'⟩ :=
      C3.Layer2.exists_mem_conj_le_of_isSylowOf hQ hS'K hS'2
    have hS'Q : cmap g S ≤ conjugate Q k⁻¹ := by
      intro y hy
      rw [mem_conjugate_iff']
      simpa using hkS' y hy
    have hSne' : cmap g S ≠ ⊥ := by
      intro hb
      apply hSne
      exact (Subgroup.map_eq_bot_iff_of_injective S
        (show Function.Injective (MulAut.conj g).toMonoidHom from (MulAut.conj g).injective)).mp hb
    have hkM : k ∈ M := (U1a.mem_CMK_iff.1 hk).1
    have hN' : normalizer (cmap g S : Set G) ≤ M := by
      have := normalizer_le_conjugate hΓ hS'Q (one_le_pRank_of_ne_bot hS'2 hSne')
      rwa [conjugate_of_mem (M.inv_mem hkM)] at this
    have hNS : normalizer (S : Set G) ≤ X := by
      intro x hx
      rw [hXdef, mem_conjugate_iff']
      apply hN'
      rw [Subgroup.mem_normalizer_iff] at hx ⊢
      intro y
      rw [mem_cmap, mem_cmap]
      have hxy := hx (g⁻¹ * y * g)
      have e : g⁻¹ * (g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹) * g = x * (g⁻¹ * y * g) * x⁻¹ := by group
      rw [e]
      exact hxy
    have hfr := C3.Layer1.Bk.frattini_wrap hLM hLn hcover
    have hMX : M ≤ X := by
      intro n hn
      obtain ⟨m, hm, x, hx, rfl⟩ := hfr n hn
      exact X.mul_mem (hLg hm) (hNS hx)
    have hMXeq : M = X := Subgroup.eq_of_le_of_card_ge hMX (by rw [hXdef, card_conjugate'])
    have hgN : g ∈ normalizer (M : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have : g * h * g⁻¹ ∈ M ↔ h ∈ X := mem_conjugate_iff'.symm
      rw [this, ← hMXeq]
    rw [hNM] at hgN
    exact hgN

end CFSG.GH74.GLS.C3.Layer1.Bk
