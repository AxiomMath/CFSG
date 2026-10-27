module

public import CFSG.CGT.Foote81L6.Normalizer.GLemma10
public import CFSG.CGT.Foote81L6.Normalizer.GLemma9
public import CFSG.CGT.Foote81L6.Normalizer.Lemma11Core
public import CFSG.CGT.Foote81L6.TStruct.CentZ
public import CFSG.CGT.Foote81L6.Normalizer.SymFive

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open Subgroup CFSG.Quasithin Equiv
open scoped IsMulCommutative

theorem lemma11Hyp_of {V X : Type*} [CommGroup V] [Group X] (hV : ∀ v : V, v * v = 1)
    (hcard : Nat.card V = 2 ^ 6) {ρ : X →* MulAut V} (hρ : Function.Injective ρ) {d₀ d₁ : X}
    {b₀ b₁ : V} (hd₀ : IsTransvectionWith (ρ d₀) b₀) (hd₀1 : ρ d₀ ≠ 1)
    (hd₁ : IsTransvectionWith (ρ d₁) b₁) (hd₁1 : ρ d₁ ≠ 1) (hb : b₀ ≠ b₁) {x₀ x₁ : X}
    (h3₀ : x₀ ^ 3 = 1) (h3₁ : x₁ ^ 3 = 1) (hinv₀ : d₀ * x₀ * d₀⁻¹ = x₀⁻¹)
    (hinv₁ : d₁ * x₁ * d₁⁻¹ = x₁⁻¹) (hc₁ : x₁ * d₀ = d₀ * x₁) (hc₀ : x₀ * d₁ = d₁ * x₀)
    (hcomm' : x₀ * x₁ = x₁ * x₀)
    (hcore : pPrimeCore 2 X = Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁) {τ : X}
    (hτ : τ * d₀ * τ⁻¹ = d₁) (hO : pPrimeCore 2 X ≠ ⊥) :
    Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNO := (inferInstance : (pPrimeCore 2 X).Normal)
  have hx₀O : x₀ ∈ pPrimeCore 2 X := by
    rw [hcore]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x₀)
  have hx₁O : x₁ ∈ pPrimeCore 2 X := by
    rw [hcore]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x₁)
  have hτ₀ : τ * x₀ * τ⁻¹ ∈ Subgroup.zpowers x₁ := by
    have hmem : τ * x₀ * τ⁻¹ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₀ := by
      rw [sup_comm, ← hcore]; exact hNO.conj_mem x₀ hx₀O τ
    refine mem_zpowers_of_inverted_of_mem_sup hcomm'.symm h3₀ hinv₁ hc₀ hmem ?_
    rw [← hτ]
    calc τ * d₀ * τ⁻¹ * (τ * x₀ * τ⁻¹) * (τ * d₀ * τ⁻¹)⁻¹ = τ * (d₀ * x₀ * d₀⁻¹) * τ⁻¹ := by
          group
      _ = (τ * x₀ * τ⁻¹)⁻¹ := by rw [hinv₀]; group
  have hτ₁ : τ⁻¹ * x₁ * τ ∈ Subgroup.zpowers x₀ := by
    have hmem : τ⁻¹ * x₁ * τ ∈ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁ := by
      rw [← hcore]
      have := hNO.conj_mem x₁ hx₁O τ⁻¹
      rwa [inv_inv] at this
    refine mem_zpowers_of_inverted_of_mem_sup hcomm' h3₁ hinv₀ hc₁ hmem ?_
    have hd₀' : d₀ = τ⁻¹ * d₁ * τ := by rw [← hτ]; group
    rw [hd₀']
    calc τ⁻¹ * d₁ * τ * (τ⁻¹ * x₁ * τ) * (τ⁻¹ * d₁ * τ)⁻¹ = τ⁻¹ * (d₁ * x₁ * d₁⁻¹) * τ := by
          group
      _ = (τ⁻¹ * x₁ * τ)⁻¹ := by rw [hinv₁]; group
  have hboth : x₀ = 1 → x₁ = 1 := by
    intro h0
    rw [h0, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hτ₁
    calc x₁ = τ * (τ⁻¹ * x₁ * τ) * τ⁻¹ := by group
      _ = 1 := by rw [hτ₁]; group
  have hboth' : x₁ = 1 → x₀ = 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hτ₀
    calc x₀ = τ⁻¹ * (τ * x₀ * τ⁻¹) * τ := by group
      _ = 1 := by rw [hτ₀]; group
  have hx₀1 : x₀ ≠ 1 := by
    intro h0
    apply hO
    rw [hcore, h0, hboth h0, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
  have hx₁1 : x₁ ≠ 1 := fun h1 => hx₀1 (hboth' h1)
  exact ⟨hρ, hV, hcard, hd₀, hd₁, hd₀1, hd₁1, hb, orderOf_eq_prime h3₀ hx₀1,
    orderOf_eq_prime h3₁ hx₁1, hcomm', hcore, hinv₀, hinv₁, hc₁.symm, hc₀.symm, hτ⟩

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteCore G (T : Subgroup G) 2 n)

theorem tvInput_holds : TvInput D := fun _ hE _ _ hx hxN htv hmove =>
  D.transvection_E64 hE hx hxN htv hmove

include D in
theorem quotInput_holds : QuotInput (T : Subgroup G) := fun _ hE => D.normalizer_E64_quot rfl hE

theorem swapInput_holds : SwapInput D := fun _ hE _ _ _ hd₀ hd₀E hd₁ hd₁E hτ hτE =>
  D.swap_d rfl hE hd₀ hd₀E hd₁ hd₁E hτ hτE

theorem lemma10_holds (hnA : ¬ StronglyInvolutionClosed D.A (T : Subgroup G))
    (hnAs : ¬ StronglyInvolutionClosed D.Astar (T : Subgroup G)) (hHig : HigmanHyp)
    (hSylN : SylNInput (T : Subgroup G)) (hL4 : Lemma4Input D)
    (hL5 : Lemma5Input (T : Subgroup G))
    {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F) [IsMulCommutative ↥F] {d₀ d₁ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F) :
    ∀ k : NBar.Q F, Odd (orderOf k) →
      k * NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ =
        NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ * k →
      k * NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ =
        NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ * k →
      ∀ v : ↥F, NBar.ρ F (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩) v = v →
        NBar.ρ F (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩) v = v →
        NBar.ρ F k v = v :=
  lemma10 D hnA hnAs hHig hSylN (tvInput_holds D) (quotInput_holds D) (swapInput_holds D)
    (D.sylow_centralizer_Z rfl) (nonempty_T₁_equiv D) hL4 hL5 hF hd₀ hd₀F hd₁ hd₁F

theorem dichotomy (hnA : ¬ StronglyInvolutionClosed D.A (T : Subgroup G))
    (hnAs : ¬ StronglyInvolutionClosed D.Astar (T : Subgroup G)) (hHig : HigmanHyp)
    (hSylN : SylNInput (T : Subgroup G)) (hL3 : ¬ IsConj D.b₀ D.b) (hL4 : Lemma4Input D)
    (hL5 : Lemma5Input (T : Subgroup G))
    {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F) [IsMulCommutative ↥F] {d₀ d₁ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
    (hd₀N : d₀ ∈ normalizer (F : Set G))
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F)
    (hd₁N : d₁ ∈ normalizer (F : Set G)) :
    (HasNormalPComplement 2 (NBar.Q F) ∧ ∃ x₀ x₁ : NBar.Q F,
      pPrimeCore 2 (NBar.Q F) = zpowers x₀ ⊔ zpowers x₁ ∧
      x₀ * NBar.π F ⟨d₁, hd₁N⟩ = NBar.π F ⟨d₁, hd₁N⟩ * x₀ ∧
      x₁ * NBar.π F ⟨d₀, hd₀N⟩ = NBar.π F ⟨d₀, hd₀N⟩ * x₁ ∧
      (pPrimeCore 2 (NBar.Q F) ≠ ⊥ → ∀ t' (ht' : t' ∈ (T : Subgroup G) ⊓ normalizer (F : Set G)),
        t' * t' = 1 → t' * D.t⁻¹ ∈ D.T₁ →
        Lemma11Hyp (NBar.ρ F) (NBar.π F ⟨d₀, hd₀N⟩) (NBar.π F ⟨d₁, hd₁N⟩) x₀ x₁
          (NBar.π F ⟨t', (mem_inf.1 ht').2⟩) ⟨D.b₀, D.b₀_mem_E64 hF⟩ ⟨D.b₁, D.b₁_mem_E64 hF⟩)) ∨
    ((∀ h ∈ (T : Subgroup G), F ≠ (D.Frep 0 1).map (MulAut.conj h).toMonoidHom) ∧
      ∀ v : ↥F, (v : G) ∈ D.A ⊔ zpowers D.b → (∃ g : NBar.Q F, NBar.ρ F g v ≠ v) →
        ∃ x₀ : NBar.Q F, orderOf x₀ = 3 ∧ NBar.π F ⟨d₁, hd₁N⟩ * x₀ = x₀ * NBar.π F ⟨d₁, hd₁N⟩ ∧
          NBar.ρ F x₀ v ≠ v) := by
  classical
  haveI := hF.finite
  obtain ⟨Q, hQ⟩ := hSylN F hF
  have h := tvHyp D hF (tvInput_holds D) (quotInput_holds D) (swapInput_holds D) hQ hd₀ hd₀F hd₁
    hd₁F
  have hL10 := lemma10_holds D hnA hnAs hHig hSylN hL4 hL5 hF hd₀ hd₀F hd₁ hd₁F
  obtain ⟨htv₀, hd₀1⟩ := isTransvectionWith_d₀ D hF hd₀ hd₀F
  obtain ⟨htv₁, hd₁1⟩ := isTransvectionWith_d₁ D hF hd₁ hd₁F
  have hb : (⟨D.b₀, D.b₀_mem_E64 hF⟩ : ↥F) ≠ ⟨D.b₁, D.b₁_mem_E64 hF⟩ := by
    intro h'
    have hb' : D.b₀ = D.b₁ := congrArg Subtype.val h'
    have : D.b₀ ∈ D.B₀ ⊓ D.B₁ := mem_inf.2 ⟨D.b₀_mem, hb' ▸ D.b₁_mem⟩
    rw [D.B₀_inf_B₁, mem_bot] at this
    exact D.b₀_ne_one this
  by_cases hnc : HasNormalPComplement 2 (NBar.Q F)
  ·
    left
    refine ⟨hnc, ?_⟩
    have hL3' : ∀ g : NBar.Q F, NBar.ρ F g ⟨D.b₀, D.b₀_mem_E64 hF⟩ ≠
        ⟨D.b₀, D.b₀_mem_E64 hF⟩ * ⟨D.b₁, D.b₁_mem_E64 hF⟩ := by
      intro g hg
      obtain ⟨gN, rfl⟩ := NBar.π_surjective F g
      apply hL3
      have h1 := congrArg Subtype.val hg
      rw [NBar.ρ_π] at h1
      exact isConj_iff.2 ⟨gN, h1⟩
    obtain ⟨x₀, x₁, h3₀, h3₁, hinv₀, hinv₁, hc₁, hc₀, hcomm', -, hcore⟩ :=
      lemma8_improved h.sq_eq_one h.injective htv₀ hd₀1 htv₁ hd₁1 hb h.dihedral_facts.1 hL3' hL10
    refine ⟨x₀, x₁, hcore, hc₀, hc₁, fun hO t' ht' _ ht't => ?_⟩
    have ht'₁ : t' ∉ D.T₁ := fun h1 => D.t_not_mem_T₀ (D.T₁_le_T₀ (by
      have : D.t = (t' * D.t⁻¹)⁻¹ * t' := by group
      rw [this]
      exact mul_mem (inv_mem ht't) h1))
    have hτ := conj_d₀_eq_d₁ D hF (swapInput_holds D) hd₀ hd₀F hd₁ hd₁F ⟨t', (mem_inf.1 ht').2⟩
      (mem_inf.1 ht').1 ht'₁
    exact lemma11Hyp_of h.sq_eq_one h.card_eq h.injective htv₀ hd₀1 htv₁ hd₁1 hb h3₀ h3₁ hinv₀
      hinv₁ hc₁ hc₀ hcomm' hcore hτ hO
  ·
    right
    obtain ⟨hO, -⟩ := TvHyp.lemma9_improved h hnc hHig hL10
    have hDz := h.dihedral_facts.2.1
    have hcard8 := h.card_sylow
    have hD2 : IsPGroup 2 ↥(NBar.sylowImage F Q : Subgroup (NBar.Q F)) :=
      (NBar.sylowImage F Q).isPGroup'
    have hstab : ∀ v : ↥F, ∀ g : NBar.Q F,
        g ∈ (MulAction.stabilizer (MulAut ↥F) v).comap (NBar.ρ F) ↔ NBar.ρ F g v = v := by
      intro v g
      rw [mem_comap, MulAction.mem_stabilizer_iff]
      rfl
    rcases h.isSymDirect hnc hHig with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
    · have htop : Subgroup.normalClosure ({NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩} :
          Set (NBar.Q F)) = ⊤ := by
        have := hφ.sup_eq
        rwa [hO, sup_bot_eq] at this
      refine ⟨ne_map_Frep01 D hF hd₀ hd₀F hd₁ hd₁F (Or.inl rfl) hφ hO, ?_⟩
      rintro v hv ⟨g, hg⟩
      exfalso
      apply hg
      exact fix_of_sym_four D hF hd₀ hd₀F hd₁ hd₁F (Or.inl rfl) hφ hO hQ hDz hcard8
        (hφ.le_normalClosure_of_isPGroup hD2) hφ.normalClosureEquiv g (htop ▸ mem_top g) v hv
    · have htop : Subgroup.normalClosure ({NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩} :
          Set (NBar.Q F)) = ⊤ := by
        have := hφ.sup_eq
        rwa [hO, sup_bot_eq] at this
      refine ⟨ne_map_Frep01 D hF hd₀ hd₀F hd₁ hd₁F (Or.inr rfl) hφ hO, ?_⟩
      rintro v hv ⟨g, hg⟩
      obtain ⟨M, hMX₀, hDM, hM₀, hM₁, ⟨ψ⟩⟩ := hφ.exists_sym_four hD2 hDz
      have hMH : M ≤ (MulAction.stabilizer (MulAut ↥F) v).comap (NBar.ρ F) := fun m hm =>
        (hstab v m).2 (fix_of_sym_four D hF hd₀ hd₀F hd₁ hd₁F (Or.inr rfl) hφ hO hQ hDz hcard8
          hDM ψ m hm v hv)
      have hX₀H : ¬ Subgroup.normalClosure
          ({NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩} : Set (NBar.Q F)) ≤
          (MulAction.stabilizer (MulAut ↥F) v).comap (NBar.ρ F) := fun hle =>
        hg ((hstab v g).1 (hle (htop ▸ mem_top g)))
      obtain ⟨x₀, -, hx₀H, hord, hc₁, -⟩ := hφ.exists_not_mem hMX₀ hM₀ hM₁ ψ hMH hX₀H
      exact ⟨x₀, hord, hc₁.symm, fun hfix => hx₀H ((hstab v x₀).2 hfix)⟩

end CFSG.CGT.Foote81L6.Normalizer
