module

public import CFSG.ClassicalInvolution.Q3.TL3T31
public import CFSG.ClassicalInvolution.Q3.TL4D1Thin

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

section Ident

variable {Δ : Set (Subgroup G)} {P : Set (Subgroup G)} {n : ℕ}

theorem aeIdent_comm_of_map_comm (hΩ : HypOmegaGen Δ) (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ)
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P)
    (hne : L₁ ≠ L₂)
    (hc : ∀ x ∈ (L₁.subgroupOf (pSpan P)).map I.φ, ∀ y ∈ (L₂.subgroupOf (pSpan P)).map I.φ,
      x * y = y * x) :
    ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : ∀ {L : Subgroup G}, L ∈ P → IsPGroup 2 ((L.subgroupOf (pSpan P)).map I.φ) :=
    fun hL => ((h2 _ (hPΔ hL)).of_equiv (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).symm).map _
  have hN : (L₁.subgroupOf (pSpan P)).map I.φ ≤
      Subgroup.normalizer ((L₂.subgroupOf (pSpan P)).map I.φ : Set (AE.AEQ n)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hc x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 := hc x hx _ hy
      have h2' : x * y * x⁻¹ = y :=
        mul_left_cancel (h1.trans (show x * y * x⁻¹ * x = x * y by group))
      rwa [h2'] at hy
  set S := (L₁.subgroupOf (pSpan P)).map I.φ ⊔ (L₂.subgroupOf (pSpan P)).map I.φ with hSdef
  have hS2 : IsPGroup 2 ↥S := (hm h₁).to_sup_of_normal_right' (hm h₂) hN
  have hQ2 : IsPGroup 2 ((S.comap I.φ).map (pSpan P).subtype) :=
    (hS2.comap_of_ker_isPGroup I.φ hk).map _
  have hLQ : ∀ {L : Subgroup G}, L ∈ P → (L.subgroupOf (pSpan P)).map I.φ ≤ S →
      L ≤ (S.comap I.φ).map (pSpan P).subtype := by
    intro L hL hLS l hl
    exact ⟨⟨l, le_pSpan hL hl⟩, hLS (I.mem_map hL hl), rfl⟩
  exact TL4.commutes_of_le_two hΩ h2 (hPΔ h₁) (hPΔ h₂) hne hQ2 (hLQ h₁ le_sup_left)
    (hLQ h₂ le_sup_right)

theorem aeIdent_eq_of_map_eq (hΩ : HypOmegaGen Δ) (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ)
    (hn : 5 ≤ n) (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P)
    (he : (L₁.subgroupOf (pSpan P)).map I.φ = (L₂.subgroupOf (pSpan P)).map I.φ) : L₁ = L₂ := by
  obtain ⟨α, h, b, hlab⟩ := I.label L₁ h₁
  exact TL4.eq_of_map_le_memBar hΩ h2 hn I.φ hk (hPΔ h₁) (hPΔ h₂) (le_pSpan h₁) (le_pSpan h₂) hlab
    he.le

end Ident

variable {r : ℕ} {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp r IH Ω K J)
include hS

theorem conj_orb_eq {g : G} (hg : conjSub g K ∈ orbOf (TC.nbrAdj Ω) K J) :
    conjSub g '' orbOf (TC.nbrAdj Ω) K J = orbOf (TC.nbrAdj Ω) (conjSub g K) K := by
  have hF := hS.graphFam'
  have hKJ' : TC.nbrAdj Ω K (conjSub g K) := adj_of_mem_orbOf hF.graph hS.adj hg
  have hJ'Ω : conjSub g K ∈ Ω := hF.mem (hF.graph.symm hKJ')
  have horb : orbOf (TC.nbrAdj Ω) K (conjSub g K) = orbOf (TC.nbrAdj Ω) K J :=
    orbOf_eq_of_mem hg
  have h1 : orbOf (TC.nbrAdj Ω) (conjSub g K) K ∈ maxOrbs (TC.nbrAdj Ω) (conjSub g K) :=
    orbOf_mem_maxOrbs hF hKJ' (by rw [horb]; exact hS.max)
  have h2 : conjSub g '' orbOf (TC.nbrAdj Ω) K J ∈ maxOrbs (TC.nbrAdj Ω) (conjSub g K) :=
    isMaxOrb_conj hF hS.max g
  exact maxOrb_unique hF hJ'Ω h2 h1

theorem mem_conj_orb {g : G} (hg : conjSub g K ∈ orbOf (TC.nbrAdj Ω) K J) :
    K ∈ conjSub g '' orbOf (TC.nbrAdj Ω) K J := by
  rw [hS.conj_orb_eq hg]
  exact mem_orbOf_self _ K

theorem conjSub_orb_of_mem_normalizer {y : G} (hy : conjSub y K = K) :
    conjSub y '' orbOf (TC.nbrAdj Ω) K J = orbOf (TC.nbrAdj Ω) K J := by
  have hF := hS.graphFam'
  have h1 := isMaxOrb_conj hF hS.max y
  rw [hy] at h1
  exact maxOrb_unique hF hS.adj.1 h1 hS.max

theorem mem_normalizer_orb_of_conjSub {y : G} (hy : conjSub y K = K) :
    y ∈ Subgroup.normalizer ((pSpan (orbOf (TC.nbrAdj Ω) K J) : Subgroup G) : Set G) := by
  have hy' : conjSub y⁻¹ K = K := by
    calc conjSub y⁻¹ K = conjSub y⁻¹ (conjSub y K) := by rw [hy]
      _ = K := conjSub_inv_conjSub y K
  have hP : ∀ {c : G}, conjSub c K = K → ∀ L ∈ orbOf (TC.nbrAdj Ω) K J,
      conjSub c L ∈ orbOf (TC.nbrAdj Ω) K J := fun hc L hL => by
    rw [← hS.conjSub_orb_of_mem_normalizer hc]
    exact ⟨L, hL, rfl⟩
  exact mem_normalizer_pSpan (hP hy) (hP hy')

theorem oddCore_orb_eq_bot :
    classicalInvolutionOddCore ↥(pSpan (orbOf (TC.nbrAdj Ω) K J)) = ⊥ := by
  have hK : K ∈ Ω := hS.adj.1
  have hN : pSpan (omegaNbr Ω K) ≤
      Subgroup.normalizer ((pSpan (orbOf (TC.nbrAdj Ω) K J) : Subgroup G) : Set G) :=
    fun l hl => mem_normalizer_pSpan (fun L hL => CSetting.conjSub_mem_orb hK hl hL)
      (fun L hL => CSetting.conjSub_mem_orb hK (Subgroup.inv_mem _ hl) hL)
  apply oddCore_eq_bot_of_oddCoreImg
  have h1 := oddCoreImg_le_of_le_normalizer hS.pSpan_orb_le hN
  rw [hS.toCHypG.oddCoreImg_pSpan_omegaNbr_eq_bot hK] at h1
  exact le_bot_iff.mp h1

theorem orb_subset_omega : orbOf (TC.nbrAdj Ω) K J ⊆ Ω := fun _ hM => (hS.orb_subset hM).1

theorem conj_orb_subset_omega (g : G) : conjSub g '' orbOf (TC.nbrAdj Ω) K J ⊆ Ω := by
  rintro _ ⟨M, hM, rfl⟩
  exact hS.hyp.conjInvariant g M (hS.orb_subset_omega hM)

end CHyp

section ConjIdent

variable {P : Set (Subgroup G)} {n : ℕ}

omit [Finite G] in
theorem AEIdent.map_conjSub (I : AEIdent P n) (x : ↥(pSpan P)) {L : Subgroup G} (k : AE.AEQ n) (hk : k ∈ (L.subgroupOf (pSpan P)).map I.φ) :
    I.φ x * k * (I.φ x)⁻¹ ∈ ((conjSub (x : G) L).subgroupOf (pSpan P)).map I.φ := by
  obtain ⟨l, hl, rfl⟩ := hk
  refine ⟨x * l * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
  show (x : G) * (l : G) * (x : G)⁻¹ ∈ conjSub (x : G) L
  exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hl)

end ConjIdent

section Lift

variable {Δ : Set (Subgroup G)} {P : Set (Subgroup G)} {n : ℕ}

theorem AEIdent.exists_y (hΩ : HypOmegaGen Δ) (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (hn : 5 ≤ n) (I : AEIdent P n)
    (hk : IsPGroup 2 I.φ.ker) {L : Subgroup G} (hL : L ∈ P) {α : Finset (Fin n)}
    {h : α.card = 4} {b : Bool} (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α h b) :
    ∃ y : ↥(pSpan P), I.φ y = AE.yBar α h ∧ (∃ a : ℕ, y ^ 3 ^ a = 1) ∧
      (∀ z : G, IsUniqueInvolution L z → (y : G) * z = z * y) ∧ conjSub (y : G) L = L := by
  have hrange : AE.yBar α h ∈ I.φ.range := by
    rw [I.range_eq]
    exact AE.yBar_mem α h
  obtain ⟨y, hy₀, a, hya⟩ := I.toLabel.exists_lift_pow_three hrange (AE.yBar_pow_three α h)
  have hy : I.φ y = AE.yBar α h := hy₀
  refine ⟨y, hy, ⟨a, hya⟩, fun z hz => ?_, ?_⟩
  ·
    set w : ↥(pSpan P) := ⟨z, le_pSpan hL hz.mem⟩ with hw
    have hmem : I.φ w ∈ AE.memBar α h b := by
      rw [← hlab]
      exact I.mem_map hL hz.mem
    have hsq : I.φ w * I.φ w = 1 := by
      rw [← map_mul, show w * w = 1 from Subtype.ext hz.sq, map_one]
    have hc : I.toLabel.φ y * I.toLabel.φ w = I.toLabel.φ w * I.toLabel.φ y := by
      show I.φ y * I.φ w = I.φ w * I.φ y
      rw [hy]
      rcases AE.eq_of_mem_memBar_mul_self hn hmem hsq with h1 | h1
      · rw [h1, mul_one, one_mul]
      · rw [h1]
        exact AE.yBar_comm_zBar α h
    have := I.toLabel.comm_of_pow_three hk hya hc
    exact congrArg Subtype.val this
  ·
    have hyL : conjSub (y : G) L ∈ P := hinv L hL y y.2
    have hle : (L.subgroupOf (pSpan P)).map I.φ ≤
        ((conjSub (y : G) L).subgroupOf (pSpan P)).map I.φ := by
      rw [hlab]
      intro m hm
      have hy2 : (AE.yBar α h)⁻¹ = AE.yBar α h * AE.yBar α h := by
        rw [inv_eq_iff_mul_eq_one, ← AE.yBar_pow_three α h, pow_succ, pow_two, mul_assoc]
      have e : (AE.yBar α h)⁻¹ * m * AE.yBar α h =
          AE.yBar α h * (AE.yBar α h * m * (AE.yBar α h)⁻¹) * (AE.yBar α h)⁻¹ := by
        calc (AE.yBar α h)⁻¹ * m * AE.yBar α h =
            (AE.yBar α h * AE.yBar α h) * m * (AE.yBar α h * AE.yBar α h)⁻¹ := by
              rw [← hy2, inv_inv]
          _ = _ := by group
      have hm' : (AE.yBar α h)⁻¹ * m * AE.yBar α h ∈ AE.memBar α h b := by
        rw [e]
        exact AE.yBar_conj_mem_memBar α h b _ (AE.yBar_conj_mem_memBar α h b m hm)
      rw [← hlab] at hm'
      have := I.map_conjSub y _ hm'
      rw [hy] at this
      have e2 : AE.yBar α h * ((AE.yBar α h)⁻¹ * m * AE.yBar α h) * (AE.yBar α h)⁻¹ = m := by
        group
      rwa [e2] at this
    exact (TL4.eq_of_map_le_memBar hΩ h2 hn I.φ hk (hPΔ hL) (hPΔ hyL) (le_pSpan hL)
      (le_pSpan hyL) hlab hle).symm

end Lift

section Model

variable {n : ℕ}

theorem memBar_twin_comm (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∀ x ∈ AE.memBar α h b, ∀ y ∈ AE.memBar α h (!b), x * y = y * x := by
  have key : ∀ x ∈ AE.memBar α h true, ∀ y ∈ AE.memBar α h false, x * y = y * x := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, AE.comm_kQ_kQStar a ha c hc]
  cases b
  · intro x hx y hy
    exact (key y hy x hx).symm
  · exact key

theorem eq_or_disjoint_of_comm {α β : Finset (Fin n)} {h : α.card = 4} {h' : β.card = 4}
    {b c : Bool} (hc : ∀ x ∈ AE.memBar α h b, ∀ y ∈ AE.memBar β h' c, x * y = y * x) :
    α = β ∨ Disjoint α β := by
  by_cases hab : α = β
  · exact Or.inl hab
  · exact Or.inr (AE.disjoint_of_zBar_comm hab fun y hy => hc _ (AE.zBar_mem_memBar α h b) y hy)

end Model

section Lift2

variable {Δ : Set (Subgroup G)} {P : Set (Subgroup G)} {n : ℕ}

theorem AEIdent.conjSub_eq_of_map_eq_yBar (hΩ : HypOmegaGen Δ) (h2 : ∀ L ∈ Δ, IsPGroup 2 L)
    (hPΔ : P ⊆ Δ) (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (hn : 5 ≤ n)
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {L : Subgroup G} (hL : L ∈ P)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α h b) {y : ↥(pSpan P)}
    (hy : I.φ y = AE.yBar α h) : conjSub (y : G) L = L := by
  have hyL : conjSub (y : G) L ∈ P := hinv L hL y y.2
  have hle : (L.subgroupOf (pSpan P)).map I.φ ≤
      ((conjSub (y : G) L).subgroupOf (pSpan P)).map I.φ := by
    rw [hlab]
    intro m hm
    have hy2 : (AE.yBar α h)⁻¹ = AE.yBar α h * AE.yBar α h := by
      rw [inv_eq_iff_mul_eq_one, ← AE.yBar_pow_three α h, pow_succ, pow_two, mul_assoc]
    have e : (AE.yBar α h)⁻¹ * m * AE.yBar α h =
        AE.yBar α h * (AE.yBar α h * m * (AE.yBar α h)⁻¹) * (AE.yBar α h)⁻¹ := by
      calc (AE.yBar α h)⁻¹ * m * AE.yBar α h =
          (AE.yBar α h * AE.yBar α h) * m * (AE.yBar α h * AE.yBar α h)⁻¹ := by
            rw [← hy2, inv_inv]
        _ = _ := by group
    have hm' : (AE.yBar α h)⁻¹ * m * AE.yBar α h ∈ AE.memBar α h b := by
      rw [e]
      exact AE.yBar_conj_mem_memBar α h b _ (AE.yBar_conj_mem_memBar α h b m hm)
    rw [← hlab] at hm'
    have := I.map_conjSub y _ hm'
    rw [hy] at this
    have e2 : AE.yBar α h * ((AE.yBar α h)⁻¹ * m * AE.yBar α h) * (AE.yBar α h)⁻¹ = m := by
      group
    rwa [e2] at this
  exact (TL4.eq_of_map_le_memBar hΩ h2 hn I.φ hk (hPΔ hL) (hPΔ hyL) (le_pSpan hL)
    (le_pSpan hyL) hlab hle).symm

end Lift2

structure Data128 (Ω : Set (Subgroup G)) (K J : Subgroup G) (g : G) (Ks : Subgroup G) (y : G) :
    Prop where
  hg : conjSub g K = J
  Ks_mem : Ks ∈ conjSub g '' orbOf (TC.nbrAdj Ω) K J
  Ks_ne : Ks ≠ K
  comm : ∀ a ∈ K, ∀ b ∈ Ks, a * b = b * a
  y_pow : ∃ a : ℕ, y ^ 3 ^ a = 1
  y_mem : y ∈ pSpan (conjSub g '' orbOf (TC.nbrAdj Ω) K J)
  y_z : ∀ z : G, IsUniqueInvolution K z → y * z = z * y
  y_K : conjSub y K = K
  y_Ks : conjSub y Ks = Ks
  y_not_K : ¬ ∀ k ∈ K, y * k = k * y
  y_not_Ks : ¬ ∀ k ∈ Ks, y * k = k * y
  y_perp : ∀ M ∈ orbOf (TC.nbrAdj Ω) K J, M ∈ KPerp Ω J → M ≠ Ks → ∀ m ∈ M, y * m = m * y
  zz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs →
    ∀ x ∈ pSpan (conjSub g '' orbOf (TC.nbrAdj Ω) K J), x * (zs * z) = (zs * z) * x

omit [Finite G] in
theorem comm_conjSub {L L' : Subgroup G} (h : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) (g : G) :
    ∀ a ∈ conjSub g L, ∀ b ∈ conjSub g L', a * b = b * a := by
  intro a ha b hb
  have ha' := mem_conjSub_iff.mp ha
  have hb' := mem_conjSub_iff.mp hb
  have e := h _ ha' _ hb'
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [e]
    _ = b * a := by group

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
include hS

theorem exists_data128 {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) :
    ∃ g : G, ∃ Ks : Subgroup G, ∃ y : G, Data128 Ω K J g Ks y ∧
      ∃ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool)
        (y₀ : ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))), I.φ y₀ = AE.yBar α h ∧
        (y₀ : G) = g⁻¹ * y * g ∧ conjSub g⁻¹ K ∈ orbOf (TC.nbrAdj Ω) K J ∧
        conjSub g⁻¹ Ks ∈ orbOf (TC.nbrAdj Ω) K J ∧
        ((conjSub g⁻¹ K).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
          AE.memBar α h b ∧
        ((conjSub g⁻¹ Ks).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
          AE.memBar α h (!b) := by
  classical
  revert I
  set π := orbOf (TC.nbrAdj Ω) K J with hπ
  intro I
  have hF := hS.graphFam'
  have hK : K ∈ Ω := hS.adj.1
  have hJπ : J ∈ π := mem_orbOf_self K J
  have hJΩ : J ∈ Ω := hS.orb_subset_omega hJπ
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hS.card L hL]; norm_num
  obtain ⟨g, hg⟩ := hS.trans K hK J hJΩ
  have hgπ : conjSub g K ∈ π := hg ▸ hJπ
  obtain ⟨L₀, hL₀, hL₀K⟩ := hS.mem_conj_orb hgπ
  have hPΩ : π ⊆ Ω := hS.orb_subset_omega
  have hinv : ∀ L ∈ π, ∀ x ∈ pSpan π, conjSub x L ∈ π := fun L hL x hx =>
    CSetting.conjSub_mem_orb hK (hS.pSpan_orb_le hx) hL
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot
  obtain ⟨α, h, b, hlab⟩ := I.label L₀ hL₀
  obtain ⟨L₁, hL₁, hlab₁⟩ := I.label_surj α h (!b)
  obtain ⟨y₀, hy₀, ⟨a, hy₀pow⟩, hy₀z, hy₀L⟩ := I.exists_y hS.hyp hS.two hPΩ hinv hn hk hL₀ hlab
  have hy₀L₁ := I.conjSub_eq_of_map_eq_yBar hS.hyp hS.two hPΩ hinv hn hk hL₁ hlab₁ hy₀
  have hne : AE.memBar α h b ≠ AE.memBar α h (!b) := by
    cases b
    · exact (AE.memBar_true_ne_false hn α h).symm
    · exact AE.memBar_true_ne_false hn α h
  have hL₀₁ : L₀ ≠ L₁ := fun e => hne (by rw [← hlab, ← hlab₁, e])
  have hcomm₀ : ∀ x ∈ L₀, ∀ y ∈ L₁, x * y = y * x :=
    aeIdent_comm_of_map_comm hS.hyp hS.two hPΩ I hk hL₀ hL₁ hL₀₁
      (by rw [hlab, hlab₁]; exact memBar_twin_comm α h b)
  have hKL₀ : conjSub g⁻¹ K = L₀ := by rw [← hL₀K, conjSub_inv_conjSub]
  have hy₀pow' : (y₀ : G) ^ 3 ^ a = 1 := by
    have := congrArg Subtype.val hy₀pow
    rwa [Subgroup.coe_pow] at this
  have hJK : TC.nbrAdj Ω J K := hF.graph.symm hS.adj
  have horbg : conjSub g '' π = orbOf (TC.nbrAdj Ω) J K := by
    rw [hS.conj_orb_eq hgπ, hg]
  have hpg : ∀ x ∈ pSpan π, g * x * g⁻¹ ∈ pSpan (conjSub g '' π) := fun x hx => by
    have := (pSpanConj g π ⟨x, hx⟩).2
    rwa [pSpanConj_apply] at this
  have hXgJ : pSpan (conjSub g '' π) ≤ Subgroup.centralizer (J : Set G) := by
    rw [horbg]
    refine (pSpan_le fun L hL => le_pSpan (adj_of_mem_orbOf hF.graph hJK hL).2).trans ?_
    exact pSpan_omegaNbr_le_centralizer hS.hyp hS.two hJΩ
  refine ⟨g, conjSub g L₁, g * y₀ * g⁻¹, ⟨hg, ⟨L₁, hL₁, rfl⟩, ?_, ?_, ⟨a, ?_⟩, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩, α, h, b, y₀, hy₀, by group, hKL₀ ▸ hL₀, by rw [conjSub_inv_conjSub]; exact hL₁,
    by rw [hKL₀]; exact hlab, by rw [conjSub_inv_conjSub]; exact hlab₁⟩
  ·
    intro e
    exact hL₀₁ (conjSub_injective g (hL₀K.trans e.symm))
  ·
    rw [← hL₀K]
    exact comm_conjSub hcomm₀ g
  · rw [conj_pow, hy₀pow', mul_one, mul_inv_cancel]
  · exact hpg _ y₀.2
  ·
    intro z hz
    have hz' : IsUniqueInvolution L₀ (g⁻¹ * z * g⁻¹⁻¹) := hKL₀ ▸ hz.conj g⁻¹
    have e := hy₀z _ hz'
    calc g * y₀ * g⁻¹ * z = g * ((y₀ : G) * (g⁻¹ * z * g⁻¹⁻¹)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g⁻¹⁻¹) * (y₀ : G)) * g⁻¹ := by rw [e]
      _ = z * (g * y₀ * g⁻¹) := by group
  ·
    rw [← hL₀K, conjSub_mul, conjSub_mul, conjSub_inv_conjSub, hy₀L]
  · rw [conjSub_mul, conjSub_mul, conjSub_inv_conjSub, hy₀L₁]
  ·
    intro hc
    obtain ⟨x, hx, hxne⟩ := AE.yBar_not_comm_memBar hn α h b
    rw [← hlab] at hx
    obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL₀ hx
    apply hxne
    rw [← hy₀, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    have hgl : g * l * g⁻¹ ∈ K := hL₀K ▸ conj_mem_conjSub hl
    have e := hc _ hgl
    show (y₀ : G) * l = l * y₀
    calc (y₀ : G) * l = g⁻¹ * ((g * y₀ * g⁻¹) * (g * l * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * l * g⁻¹) * (g * y₀ * g⁻¹)) * g := by rw [e]
      _ = l * y₀ := by group
  ·
    intro hc
    obtain ⟨x, hx, hxne⟩ := AE.yBar_not_comm_memBar hn α h (!b)
    rw [← hlab₁] at hx
    obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL₁ hx
    apply hxne
    rw [← hy₀, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    have hgl : g * l * g⁻¹ ∈ conjSub g L₁ := conj_mem_conjSub hl
    have e := hc _ hgl
    show (y₀ : G) * l = l * y₀
    calc (y₀ : G) * l = g⁻¹ * ((g * y₀ * g⁻¹) * (g * l * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * l * g⁻¹) * (g * y₀ * g⁻¹)) * g := by rw [e]
      _ = l * y₀ := by group
  ·
    intro M hMπ hMperp hMKs m hm
    have hy : g * y₀ * g⁻¹ ∈ pSpan (conjSub g '' π) := hpg _ y₀.2
    rcases Set.mem_insert_iff.mp hMperp with rfl | hMJ
    · exact ((Subgroup.mem_centralizer_iff.mp (hXgJ hy)) m hm).symm
    · by_cases hMg : M ∈ conjSub g '' π
      · obtain ⟨M', hM', rfl⟩ := hMg
        have hMK : ∀ x ∈ K, ∀ y ∈ conjSub g M', x * y = y * x :=
          comm_of_mem_omegaNbr hS.hyp hS.two hK (hS.orb_subset hMπ)
        have hM'L₀ : ∀ x ∈ L₀, ∀ y ∈ M', x * y = y * x := by
          have := comm_conjSub hMK g⁻¹
          rwa [hKL₀, conjSub_inv_conjSub] at this
        obtain ⟨β, h', c, hlab'⟩ := I.label M' hM'
        have hc : ∀ x ∈ AE.memBar α h b, ∀ y ∈ AE.memBar β h' c, x * y = y * x := by
          rw [← hlab, ← hlab']
          rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hM'L₀ _ (Subgroup.mem_subgroupOf.mp hu) _
            (Subgroup.mem_subgroupOf.mp hv))
        rcases eq_or_disjoint_of_comm hc with hαβ | hd
        · exfalso
          subst hαβ
          have hcb : c = b ∨ c = !b := by cases b <;> cases c <;> simp
          rcases hcb with rfl | rfl
          · have := aeIdent_eq_of_map_eq hS.hyp hS.two hPΩ hn I hk hL₀ hM' (hlab.trans hlab'.symm)
            subst this
            rw [hL₀K] at hMπ
            exact (hS.orb_subset hMπ).2.1 rfl
          · have := aeIdent_eq_of_map_eq hS.hyp hS.two hPΩ hn I hk hL₁ hM'
              (hlab₁.trans hlab'.symm)
            subst this
            exact hMKs rfl
        · have hm' : g⁻¹ * m * g ∈ M' := by
            have := mem_conjSub_iff.mp hm
            simpa using this
          set w : ↥(pSpan π) := ⟨g⁻¹ * m * g, le_pSpan hM' hm'⟩ with hw
          have hcw : I.toLabel.φ y₀ * I.toLabel.φ w = I.toLabel.φ w * I.toLabel.φ y₀ := by
            show I.φ y₀ * I.φ w = I.φ w * I.φ y₀
            rw [hy₀]
            exact AE.yBar_comm_memBar_of_disjoint hd c _ (by rw [← hlab']; exact I.mem_map hM' hm')
          have e := congrArg Subtype.val (I.toLabel.comm_of_pow_three hk hy₀pow hcw)
          change (y₀ : G) * (g⁻¹ * m * g) = (g⁻¹ * m * g) * y₀ at e
          calc g * y₀ * g⁻¹ * m = g * ((y₀ : G) * (g⁻¹ * m * g)) * g⁻¹ := by group
            _ = g * ((g⁻¹ * m * g) * (y₀ : G)) * g⁻¹ := by rw [e]
            _ = m * (g * y₀ * g⁻¹) := by group
      ·
        have hJM : TC.nbrAdj Ω J M := ⟨hJΩ, hMJ⟩
        have hle : pSpan (conjSub g '' π) ≤ Subgroup.centralizer (M : Set G) := by
          rw [horbg]
          refine pSpan_le fun N hN => ?_
          have hJN : TC.nbrAdj Ω J N := adj_of_mem_orbOf hF.graph hJK hN
          have hnot : M ∉ orbOf (TC.nbrAdj Ω) J N := by
            rw [orbOf_eq_of_mem hN, ← horbg]
            exact hMg
          have hNM := hS.sepHyp hJN hJM hnot
          intro x hx
          exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
            (comm_of_mem_omegaNbr hS.hyp hS.two hNM.1 hNM.2 x hx y hy).symm
        exact ((Subgroup.mem_centralizer_iff.mp (hle hy)) m hm).symm
  ·
    intro z zs hz hzs x hx
    have hz' : IsUniqueInvolution L₀ (g⁻¹ * z * g⁻¹⁻¹) := hKL₀ ▸ hz.conj g⁻¹
    have hzs' : IsUniqueInvolution L₁ (g⁻¹ * zs * g⁻¹⁻¹) := by
      have := hzs.conj g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have e1 := I.map_eq_zBar hn hL₀ (h8 L₀ (hPΩ hL₀)) hlab hz'
    have e2 := I.map_eq_zBar hn hL₁ (h8 L₁ (hPΩ hL₁)) hlab₁ hzs'
    set w : ↥(pSpan π) := ⟨g⁻¹ * zs * g⁻¹⁻¹, le_pSpan hL₁ hzs'.mem⟩ *
      ⟨g⁻¹ * z * g⁻¹⁻¹, le_pSpan hL₀ hz'.mem⟩ with hw
    have hwk : w ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, hw, map_mul, e1, e2, AE.zBar_mul_self]
    have hwc := Subgroup.mem_center_iff.mp (I.ker_le hwk)
    have hx₀ : g⁻¹ * x * g ∈ pSpan π := by
      have := ((pSpanConj g π).symm ⟨x, hx⟩).2
      rwa [pSpanConj_symm_apply] at this
    have e := congrArg Subtype.val (hwc ⟨g⁻¹ * x * g, hx₀⟩)
    change (g⁻¹ * x * g) * ((g⁻¹ * zs * g⁻¹⁻¹) * (g⁻¹ * z * g⁻¹⁻¹)) =
      ((g⁻¹ * zs * g⁻¹⁻¹) * (g⁻¹ * z * g⁻¹⁻¹)) * (g⁻¹ * x * g) at e
    calc x * (zs * z) = g * ((g⁻¹ * x * g) * ((g⁻¹ * zs * g⁻¹⁻¹) * (g⁻¹ * z * g⁻¹⁻¹))) * g⁻¹ := by
          group
      _ = g * (((g⁻¹ * zs * g⁻¹⁻¹) * (g⁻¹ * z * g⁻¹⁻¹)) * (g⁻¹ * x * g)) * g⁻¹ := by rw [e]
      _ = zs * z * x := by group

end CHyp

@[expose] def AE3Rigid (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Δ : Set (Subgroup G)), HypOmegaGen Δ →
    (∀ L ∈ Δ, IsPGroup 2 L) → (∀ L ∈ Δ, Nat.card L = 8) →
    ∀ (P : Set (Subgroup G)), P ⊆ Δ → ∀ (I : AEIdent P n),
    IsPGroup 2 I.φ.ker → ∀ a : G, (∃ k : ℕ, a ^ 3 ^ k = 1) → (∀ M ∈ P, conjSub a M ∈ P) →
    a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G) →
    ∀ (γ : Finset (Fin n)) (_ : γ.card = 4) (M₀ : Subgroup G),
    (∀ M ∈ P, ∀ (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool),
      (M.subgroupOf (pSpan P)).map I.φ = AE.memBar β hβ c → (β = γ ∨ Disjoint β γ) → M ≠ M₀ →
      ∀ m ∈ M, a * m = m * a) →
    ∀ x ∈ pSpan P, a * x = x * a

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
include hS

theorem mem_kPerp_of_label {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    {γ : Finset (Fin n)} {hγ : γ.card = 4} {c : Bool}
    (hlabJ : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = AE.memBar γ hγ c)
    {M : Subgroup G} (hM : M ∈ orbOf (TC.nbrAdj Ω) K J) {β : Finset (Fin n)} {hβ : β.card = 4}
    {c' : Bool}
    (hlab : (M.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = AE.memBar β hβ c')
    (hβγ : β = γ ∨ Disjoint β γ) : M ∈ KPerp Ω J := by
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hPΩ := hS.orb_subset_omega
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot
  by_cases hMJ : M = J
  · rw [hMJ]
    exact Set.mem_insert _ _
  refine Set.mem_insert_of_mem _ ((TC.mem_omegaNbr_iff hS.hyp hS.two).mpr ⟨hPΩ hM, hMJ, ?_⟩)
  have hc : ∀ x ∈ AE.memBar β hβ c', ∀ y ∈ AE.memBar γ hγ c, x * y = y * x := by
    rcases hβγ with rfl | hd
    · have hcc : c' = c ∨ c' = !c := by cases c <;> cases c' <;> simp
      rcases hcc with rfl | rfl
      · exfalso
        exact hMJ (aeIdent_eq_of_map_eq hS.hyp hS.two hPΩ hn I hk hM hJπ (hlab.trans hlabJ.symm))
      · intro x hx y hy
        have := memBar_twin_comm β hβ c y hy x hx
        exact this.symm
    · exact AE.comm_memBar_of_disjoint hd c' c
  have hcomm := aeIdent_comm_of_map_comm hS.hyp hS.two hPΩ I hk hM hJπ hMJ
    (by rw [hlab, hlabJ]; exact hc)
  exact le_normalizer_of_comm hcomm

theorem y_comm_of_rigid {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    (hM1 : AE3Rigid n) {g : G} {Ks : Subgroup G} {y : G} (hD : Data128 Ω K J g Ks y) :
    ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y := by
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot
  obtain ⟨γ, hγ, c, hlabJ⟩ := I.label J hJπ
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hS.card L hL]; norm_num
  have hperm : ∀ M ∈ orbOf (TC.nbrAdj Ω) K J, conjSub y M ∈ orbOf (TC.nbrAdj Ω) K J :=
    fun M hM => by
      rw [← hS.conjSub_orb_of_mem_normalizer hD.y_K]
      exact ⟨M, hM, rfl⟩
  refine hM1 G Ω hS.hyp hS.two h8 _ hS.orb_subset_omega I hk y hD.y_pow hperm
    (hS.mem_normalizer_orb_of_conjSub hD.y_K) γ hγ Ks ?_
  intro M hM β hβ c' hlab hβγ hMKs
  exact hD.y_perp M hM (hS.mem_kPerp_of_label hn I hlabJ hM hlab hβγ) hMKs

theorem ks_comm_of_not_mem {g : G} {Ks : Subgroup G} {y : G} (hD : Data128 Ω K J g Ks y)
    (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J) :
    Ks ∈ omegaNbr Ω K ∧ ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x := by
  have hF := hS.graphFam'
  have hK : K ∈ Ω := hS.adj.1
  have hKsΩ : Ks ∈ Ω := hS.conj_orb_subset_omega g hD.Ks_mem
  have hKsK : Ks ∈ omegaNbr Ω K :=
    (TC.mem_omegaNbr_iff hS.hyp hS.two).mpr ⟨hKsΩ, hD.Ks_ne,
      le_normalizer_of_comm fun x hx y hy => (hD.comm y hy x hx).symm⟩
  refine ⟨hKsK, ?_⟩
  have hle : pSpan (orbOf (TC.nbrAdj Ω) K J) ≤ Subgroup.centralizer (Ks : Set G) := by
    refine pSpan_le fun N hN => ?_
    have hKN : TC.nbrAdj Ω K N := adj_of_mem_orbOf hF.graph hS.adj hN
    have hnot : Ks ∉ orbOf (TC.nbrAdj Ω) K N := by
      rw [orbOf_eq_of_mem hN]
      exact hKsπ
    have hNKs := hS.sepHyp hKN ⟨hK, hKsK⟩ hnot
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun k hk =>
      (comm_of_mem_omegaNbr hS.hyp hS.two hNKs.1 hNKs.2 x hx k hk).symm
  intro x hx k hk
  exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) k hk).symm

theorem ks_comm_of_y_comm {g : G} {Ks : Subgroup G} {y : G} (hD : Data128 Ω K J g Ks y)
    (hy : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y) :
    Ks ∈ omegaNbr Ω K ∧ Ks ∉ orbOf (TC.nbrAdj Ω) K J ∧
      ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x := by
  have hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J := by
    intro h
    apply hD.y_not_Ks
    intro k hk
    exact hy k (le_pSpan h hk)
  obtain ⟨hKsK, hKs⟩ := hS.ks_comm_of_not_mem hD hKsπ
  exact ⟨hKsK, hKsπ, hKs⟩

theorem z_eq_of_ks_comm {g : G} {Ks : Subgroup G} {y : G} (hD : Data128 Ω K J g Ks y)
    (hKs : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x)
    {z zs : G} (hz : IsUniqueInvolution K z) (hzs : IsUniqueInvolution Ks zs) : zs = z := by
  have hF := hS.graphFam'
  have hK : K ∈ Ω := hS.adj.1
  set f := zs * z with hf
  have hKX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), x * z = z * x := by
    have hle : pSpan (orbOf (TC.nbrAdj Ω) K J) ≤ Subgroup.centralizer (K : Set G) :=
      hS.pSpan_orb_le.trans (pSpan_omegaNbr_le_centralizer hS.hyp hS.two hK)
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) z hz.mem).symm
  have hfX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), x * f = f * x := by
    intro x hx
    have e1 := hKs x hx zs hzs.mem
    have e2 := hKX x hx
    calc x * f = x * zs * z := by rw [hf, mul_assoc]
      _ = zs * x * z := by rw [e1]
      _ = zs * (x * z) := by rw [mul_assoc]
      _ = zs * (z * x) := by rw [e2]
      _ = f * x := by rw [hf, mul_assoc]
  have horbg : conjSub g '' orbOf (TC.nbrAdj Ω) K J = orbOf (TC.nbrAdj Ω) J K := by
    rw [hS.conj_orb_eq (by rw [hD.hg]; exact mem_orbOf_self K J), hD.hg]
  have hfXg : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) J K), x * f = f * x := by
    rw [← horbg]
    exact hD.zz z zs hz hzs
  have hgen := le_iSup_of_maxOrb hF hS.adj hS.max
  have hC : pSpan Ω ≤ Subgroup.centralizer ({f} : Set G) := by
    refine pSpan_le fun L hL => (hgen L hL).trans (iSup₂_le fun M hM => ?_)
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hM with hM | hM
    · exact hfX x (le_pSpan hM hx)
    · exact hfXg x (le_pSpan hM hx)
  rw [hS.gen] at hC
  have hfc : f ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subgroup.mem_centralizer_singleton_iff.mp (hC (Subgroup.mem_top x))
  rw [hS.center, Subgroup.mem_bot] at hfc
  calc zs = zs * z * z := by rw [mul_assoc, hz.sq, mul_one]
    _ = z := by rw [← hf, hfc, one_mul]

end CHyp

end CFSG.ClassicalInvolution.Q3.TC.Thin
