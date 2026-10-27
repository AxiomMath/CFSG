module

public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.TwoSubgroup
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma57
public import CFSG.LocalAnalysis.GL83PartI.I_33

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

@[expose] def Lemma26Plus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ¬ IsWeaklyBalancedWrt 3 2 B →
      ∃ (D : Subgroup G) (b : G) (L : Subgroup G), Lemma24Setup 3 B D b L ∧
        Lemma24Conclusion B D b L ∧ b ∈ bClosure B L ∧
        barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L) ∧
        ∀ Lᵢ : Subgroup G, IsBConjugate B L Lᵢ → b ∈ Lᵢ

theorem commutator_sup_le_of_normalized {X N L K₁ K₂ : Subgroup G}
    (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (h₁ : K₁ ≤ X) (h₂ : K₂ ≤ X)
    (hc₁ : ⁅L, K₁⁆ ≤ N) (hc₂ : ⁅L, K₂⁆ ≤ N) : ⁅L, K₁ ⊔ K₂⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have key : a ∈ X ∧ x * a * x⁻¹ * a⁻¹ ∈ N := by
    rw [Subgroup.sup_eq_closure] at ha
    induction ha using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨h₁ hy, (Subgroup.commutator_le.1 hc₁) x hx y hy⟩
      · exact ⟨h₂ hy, (Subgroup.commutator_le.1 hc₂) x hx y hy⟩
    | one => exact ⟨one_mem _, by simp⟩
    | mul y z _ _ ihy ihz =>
      refine ⟨mul_mem ihy.1 ihz.1, ?_⟩
      have h : x * (y * z) * x⁻¹ * (y * z)⁻¹ =
          (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
      rw [h]
      exact N.mul_mem ihy.2 (hN y ihy.1 _ ihz.2)
    | inv y _ ihy =>
      refine ⟨inv_mem ihy.1, ?_⟩
      have h : x * y⁻¹ * x⁻¹ * (y⁻¹)⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y := by group
      rw [h]
      have := hN y⁻¹ (inv_mem ihy.1) _ (N.inv_mem ihy.2)
      simpa using this
  exact key.2

theorem mem_normalizer_of_le_centralizer_singleton {b : G} {L : Subgroup G}
    (h : L ≤ Subgroup.centralizer ({b} : Set G)) : b ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hcb : ∀ y ∈ L, b * y * b⁻¹ = y := fun y hy => by
    have : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.1 (h hy)
    rw [← this]; group
  constructor
  · intro hx; rw [hcb x hx]; exact hx
  · intro hx
    have hc : (b * x * b⁻¹) * b = b * (b * x * b⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 (h hx)
    have h1 : b * x = b * (b * x * b⁻¹) := by
      rw [inv_mul_cancel_right] at hc; exact hc
    have h2 : x = b * x * b⁻¹ := mul_left_cancel h1
    rw [h2]; exact hx

theorem prop22_of_lemmas (hFT : InputFeitThompson) (h24 : Lemma24) (h26 : Lemma26Plus)
    (h27 : Lemma27) (h28 : Lemma28) (h29 : Lemma29) : Prop22 := by
  intro G _ _ m p hS
  by_contra hno
  have hno' : ∀ B : Subgroup G, IsBZeroMax p B → ¬ IsWeaklyBalancedWrt p 2 B := by
    intro B hB hw
    exact hno ⟨B, hB, hw⟩
  have hp3' : 3 ≤ p := by
    have h2 := hS.prime.two_le
    have h3 := hS.ne_two
    omega
  obtain ⟨B₀, hB₀⟩ :=
    CFSG.HardMathSupport.Solomon.Proving.exists_isBZeroMax_of_not_glaDeltaZero hS.not_deltaZero
  have hB₀1 : IsBOneMax p B₀ :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax hp3' hB₀
  have hnot₀ := hno' B₀ hB₀
  have hex : ∃ D : Subgroup G, IsEkIn p 2 B₀ D ∧ ∃ b ∈ B₀, b ≠ 1 ∧
      ¬ delta2At p B₀ D b ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) := by
    by_contra hcon
    push Not at hcon
    exact hnot₀ fun D hD b hb hb1 => hcon D hD b hb hb1
  obtain ⟨D₀, hD₀, b₀, hb₀, hb₀1, hX₀⟩ := hex
  obtain ⟨hp, -, -⟩ := h24 G m p hS B₀ hB₀1 hnot₀ D₀ hD₀ b₀ hb₀ hb₀1 hX₀
  subst hp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimple := hS.simple
  obtain ⟨D, b, L, hset, hconc, hbK, hcen, hbL⟩ := h26 G m hS B₀ hB₀ hnot₀
  have hBel : IsElemAbelian 3 B₀ := hB₀.1.1
  have hbB : b ∈ B₀ := hset.mem
  have hb1 : b ≠ 1 := hset.ne_one
  have hcomm : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x := fun x hx y hy => elemAbelian_comm hBel hx hy
  have hCbne : Subgroup.centralizer ({b} : Set G) ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hb1
  have hBCb : B₀ ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx b hbB)
  have hcompL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L := hset.isComp
  have hnotNL : ¬ B₀ ≤ Subgroup.normalizer (L : Set G) :=
    not_le_normalizer_of_relIndex_eq_three hconc.1
  obtain ⟨L₂, L₃, ⟨g₂, hg₂, hL₂⟩, ⟨g₃, hg₃, hL₃⟩, h12, h13, h23, -⟩ :=
    exists_three_conjugates hBel.1 hconc.1
  have hconj : ∀ g ∈ B₀, GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) (GLBConj g L) := by
    intro g hg
    have := glaPComponent_gLBConj g hcompL
    rwa [gLBConj_centralizer_singleton_of_commute (hcomm g hg b hbB)] at this
  have hnotN : ∀ g ∈ B₀, ¬ B₀ ≤ Subgroup.normalizer (GLBConj g L : Set G) := by
    intro g hg
    rw [le_normalizer_gLBConj_iff hBel.1 hg]
    exact hnotNL
  have hL₂c : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L₂ := hL₂ ▸ hconj g₂ hg₂
  have hL₃c : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L₃ := hL₃ ▸ hconj g₃ hg₃
  have hL₂n : ¬ B₀ ≤ Subgroup.normalizer (L₂ : Set G) := hL₂ ▸ hnotN g₂ hg₂
  have hL₃n : ¬ B₀ ≤ Subgroup.normalizer (L₃ : Set G) := hL₃ ▸ hnotN g₃ hg₃
  have hbL₂ : b ∈ L₂ := hbL L₂ ⟨g₂, hg₂, hL₂⟩
  have hbL₃ : b ∈ L₃ := hbL L₃ ⟨g₃, hg₃, hL₃⟩
  have hrank : CFSG.Open.pRank 3 B₀ = GLATwoLocalRank 3 G :=
    pRank_eq_of_card Nat.prime_three hBel hB₀.1.2.1
  obtain ⟨Bs, hBsX, hBsel, hBsrank, hBsnorm, hBsJ⟩ :=
    h29 G m hS B₀ hBel hrank (Subgroup.centralizer ({b} : Set G)) hBCb hCbne
  have hzp : IsElemAbelian 3 (Subgroup.zpowers b) :=
    isElemAbelian_mono hBel (Subgroup.zpowers_le.2 hbB)
  have hBs_cent : Bs ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    intro x hx
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 (hBsX hx)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact (Commute.zpow_left (show Commute b x from hxb.symm) n).eq
  have hB'el : IsElemAbelian 3 (Bs ⊔ Subgroup.zpowers b) :=
    isElemAbelian_sup_of_commute hBsel hzp hBs_cent
  have hbB' : b ∈ Bs ⊔ Subgroup.zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hbC : b ∈ Subgroup.centralizer ({b} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hB'X : Bs ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({b} : Set G) :=
    sup_le hBsX (Subgroup.zpowers_le.2 hbC)
  have hB'norm : ∀ L' : Subgroup G, GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L' →
      Bs ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (L' : Set G) := by
    intro L' hL'
    refine sup_le (hBsnorm L' hL') (Subgroup.zpowers_le.2 ?_)
    exact mem_normalizer_of_le_centralizer_singleton hL'.1
  have hB'rank : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 (Bs ⊔ Subgroup.zpowers b) :=
    calc GLATwoLocalRank 3 G = CFSG.Open.pRank 3 B₀ := hrank.symm
      _ ≤ CFSG.Open.pRank 3 Bs := hBsrank
      _ ≤ _ := CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_sup_left
  obtain ⟨a₂, ha₂, ha₂n⟩ := IsConcreteLE.not_le_iff_exists.1 (hBsJ L₂ hL₂c hL₂n)
  obtain ⟨a₃, ha₃, ha₃n⟩ := IsConcreteLE.not_le_iff_exists.1 (hBsJ L₃ hL₃c hL₃n)
  have hbO₂ : b ∈ oPrimePOf 3 L₂ := mem_oPrimePOf_of_forall_comm Nat.prime_three hbL₂ fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hL₂c.1 hy)).symm
  have ha₂zp : a₂ ∉ Subgroup.zpowers b := fun h =>
    ha₂n ((Subgroup.zpowers_le.2 hbO₂) h)
  have hL₃₂ : L₃ ⊓ L₂ ≤ oPrimePOf 3 L₃ :=
    inf_le_oPrimePOf_of_ne Nat.prime_three hL₃c hL₂c h23.symm
  have ha₃zp : a₃ ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers a₂ := fun h => by
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers a₂ ≤ L₂ :=
      sup_le (Subgroup.zpowers_le.2 hbL₂) (Subgroup.zpowers_le.2 ha₂.2)
    exact ha₃n (hL₃₂ ⟨ha₃.2, hle h⟩)
  have hmemB' : ∀ x ∈ Bs, x ∈ Bs ⊔ Subgroup.zpowers b := fun x hx => Subgroup.mem_sup_left hx
  have hcB' : ∀ x ∈ Bs ⊔ Subgroup.zpowers b, ∀ y ∈ Bs ⊔ Subgroup.zpowers b, x * y = y * x :=
    fun x hx y hy => elemAbelian_comm hB'el hx hy
  obtain ⟨hEel, hEcard⟩ := exists_isElemAbelian_card_three_of_independent
    (hcB' b hbB' a₂ (hmemB' a₂ ha₂.1)) (hcB' b hbB' a₃ (hmemB' a₃ ha₃.1))
    (hcB' a₂ (hmemB' a₂ ha₂.1) a₃ (hmemB' a₃ ha₃.1))
    (hB'el.2 b hbB') (hB'el.2 a₂ (hmemB' a₂ ha₂.1)) (hB'el.2 a₃ (hmemB' a₃ ha₃.1))
    hb1 ha₂zp ha₃zp
  have hEA : Subgroup.zpowers b ⊔ Subgroup.zpowers a₂ ⊔ Subgroup.zpowers a₃ ≤
      (Bs ⊔ Subgroup.zpowers b) ⊓ (L₂ ⊔ L₃) := by
    refine le_inf (sup_le (sup_le (Subgroup.zpowers_le.2 hbB')
      (Subgroup.zpowers_le.2 (hmemB' a₂ ha₂.1))) (Subgroup.zpowers_le.2 (hmemB' a₃ ha₃.1))) ?_
    exact sup_le (sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_sup_left hbL₂))
      (Subgroup.zpowers_le.2 (Subgroup.mem_sup_left ha₂.2)))
      (Subgroup.zpowers_le.2 (Subgroup.mem_sup_right ha₃.2))
  have hAel : IsElemAbelian 3 ((Bs ⊔ Subgroup.zpowers b) ⊓ (L₂ ⊔ L₃)) :=
    isElemAbelian_mono hB'el inf_le_left
  obtain ⟨k, hk⟩ := exists_card_eq_pow (GL83.isPGroup_of_isElemAbelian hAel)
  have hk3 : 3 ≤ k := by
    have h1 := CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hEA hEel hEcard
    have h2 := pRank_eq_of_card Nat.prime_three hAel hk
    omega
  have hAEk : IsEkIn 3 k (Bs ⊔ Subgroup.zpowers b) ((Bs ⊔ Subgroup.zpowers b) ⊓ (L₂ ⊔ L₃)) :=
    ⟨inf_le_left, hAel, hk⟩
  have hNcore : ∀ x ∈ Subgroup.centralizer ({b} : Set G), ∀ n ∈ GLAPPrimeCoreOf 3
      (Subgroup.centralizer ({b} : Set G)), x * n * x⁻¹ ∈ GLAPPrimeCoreOf 3
        (Subgroup.centralizer ({b} : Set G)) := fun x hx n hn => mem_gLAPPrimeCoreOf_conj hn hx
  have hLA : ⁅L, (Bs ⊔ Subgroup.zpowers b) ⊓ (L₂ ⊔ L₃)⁆ ≤
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) :=
    (Subgroup.commutator_mono le_rfl inf_le_right).trans
      (commutator_sup_le_of_normalized hNcore hL₂c.1 hL₃c.1
        (commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hcompL hL₂c h12)
        (commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hcompL hL₃c h13))
  have hN2 := exists_twoGroup_normalized_of_centralizes hFT Nat.prime_three (by norm_num) hcompL
    (inf_le_left.trans hB'X) (GL83.isPGroup_of_isElemAbelian hAel) hLA
  have hbA : b ∈ (Bs ⊔ Subgroup.zpowers b) ⊓ (L₂ ⊔ L₃) := ⟨hbB', Subgroup.mem_sup_left hbL₂⟩
  have hcore : ∀ a ∈ (Bs ⊔ Subgroup.zpowers b) ⊓ (L₂ ⊔ L₃), a ≠ 1 →
      b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G)) := by
    intro a ha ha1
    have hord : orderOf a = 3 := orderOf_eq_prime (hB'el.2 a ha.1) ha1
    exact h27 G m hS B₀ hB₀ b hbB hb1 L hcompL hnotNL hbK
      (Or.inl ⟨D, hset, hconc, hcen⟩) L₂ L₃ ⟨g₂, hg₂, hL₂⟩ ⟨g₃, hg₃, hL₃⟩ a ha.2 hord
  have h28' := h28 G m hS (Bs ⊔ Subgroup.zpowers b) hB'el hB'rank b hbB' hb1
    ((Bs ⊔ Subgroup.zpowers b) ⊓ (L₂ ⊔ L₃)) k hk3 hAEk hN2 hbA hcore
    (fun L' hL' => hB'norm L' hL')
  exact hno' _ h28'.1 h28'.2

end CFSG.HardMathSupport.Solomon.LocalBalance
