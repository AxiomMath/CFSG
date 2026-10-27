module

public import CFSG.ClassicalInvolution.Q3.TL3T13
public import CFSG.ClassicalInvolution.Q3.AE.E64

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G]

structure AELabel (P : Set (Subgroup G)) (n : ℕ) where
  φ : ↥(pSpan P) →* AE.AEQ n
  ker_le : φ.ker ≤ Subgroup.center ↥(pSpan P)
  label : ∀ L ∈ P, ∃ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
    (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b

@[expose] def AEIdent.toLabel {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) : AELabel P n :=
  ⟨I.φ, I.ker_le, I.label⟩

@[expose] def AEIdentOn.toLabel {P : Set (Subgroup G)} {n : ℕ} {𝒜 : Set (Finset (Fin n))}
    {H : Subgroup (AE.AEQ n)} (I : AEIdentOn P n 𝒜 H) : AELabel P n :=
  ⟨I.φ, I.ker_le, fun L hL => by
    obtain ⟨α, -, h, b, hlab⟩ := I.label L hL
    exact ⟨α, h, b, hlab⟩⟩

@[expose] def AELabel.twinRel {P : Set (Subgroup G)} {n : ℕ} (J : AELabel P n)
    (L L' : Subgroup G) : Prop :=
  L ∈ P ∧ L' ∈ P ∧ ∃ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
    (L.subgroupOf (pSpan P)).map J.φ = AE.memBar α h b ∧
      (L'.subgroupOf (pSpan P)).map J.φ = AE.memBar α h (!b)

namespace AELabel

variable {P : Set (Subgroup G)} {n : ℕ} (J : AELabel P n)

theorem mem_map {L : Subgroup G} (hL : L ∈ P) {l : G} (hl : l ∈ L) :
    J.φ ⟨l, le_pSpan hL hl⟩ ∈ (L.subgroupOf (pSpan P)).map J.φ :=
  ⟨⟨l, le_pSpan hL hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩

theorem exists_of_mem_map {L : Subgroup G} (hL : L ∈ P) {x : AE.AEQ n}
    (hx : x ∈ (L.subgroupOf (pSpan P)).map J.φ) :
    ∃ l : G, ∃ hl : l ∈ L, J.φ ⟨l, le_pSpan hL hl⟩ = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩

theorem comm_of_pow_three (hk : IsPGroup 2 J.φ.ker) {y w : ↥(pSpan P)} {a : ℕ}
    (hy : y ^ 3 ^ a = 1) (h : J.φ y * J.φ w = J.φ w * J.φ y) : y * w = w * y := by
  set c := w⁻¹ * (y * w * y⁻¹) with hc
  have hcker : c ∈ J.φ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_inv, map_mul, map_mul, map_inv, h]
    group
  have hyw : y * w * y⁻¹ = w * c := by rw [hc]; group
  have hpow : ∀ k : ℕ, y ^ k * w * (y ^ k)⁻¹ = w * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : y * c ^ k * y⁻¹ = c ^ k := by
        have := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ (J.ker_le hcker) k) y
        rw [this]
        group
      calc y ^ (k + 1) * w * (y ^ (k + 1))⁻¹ = y * (y ^ k * w * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']
            group
        _ = (y * w * y⁻¹) * (y * c ^ k * y⁻¹) := by rw [ih]; group
        _ = w * c ^ (k + 1) := by rw [hyw, hck, pow_succ', mul_assoc]
  have hc3 : c ^ 3 ^ a = 1 := by
    have := hpow (3 ^ a)
    rw [hy, one_mul, inv_one, mul_one] at this
    exact mul_left_cancel (this.symm.trans (mul_one w).symm)
  obtain ⟨j, hj⟩ := hk ⟨c, hcker⟩
  have hj' : c ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    rwa [Subgroup.coe_pow] at this
  have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow a j (by norm_num))
    (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hj')
  have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
  calc y * w = (y * w * y⁻¹) * y := by group
    _ = w * y := by rw [hyw, hc1, mul_one]

variable [Finite G]

theorem isPGroup_ker (hO : classicalInvolutionOddCore ↥(pSpan P) = ⊥) : IsPGroup 2 J.φ.ker :=
  (isPGroup_center_of_corefree hO).to_le J.ker_le

theorem exists_lift_pow_three {x : AE.AEQ n} (hx : x ∈ J.φ.range) (hx3 : x ^ 3 = 1) :
    ∃ y : ↥(pSpan P), J.φ y = x ∧ ∃ a : ℕ, y ^ 3 ^ a = 1 := by
  obtain ⟨y₀, rfl⟩ := hx
  obtain ⟨a, r, hr, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y₀).ne' 3 (by norm_num)
  refine ⟨y₀ ^ (r * r), ?_, a, ?_⟩
  · have hr2 : r * r % 3 = 1 := by
      have : r % 3 = 1 ∨ r % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [map_pow, pow_eq_pow_mod _ hx3, hr2, pow_one]
  · rw [← pow_mul, show r * r * 3 ^ a = (3 ^ a * r) * r by ring, ← hN, pow_mul,
      pow_orderOf_eq_one, one_pow]

end AELabel

section Conj

@[expose] noncomputable def phiConj {P : Set (Subgroup G)} {n : ℕ} (φ : ↥(pSpan P) →* AE.AEQ n)
    (g : G) : ↥(pSpan (conjSub g '' P)) →* AE.AEQ n :=
  φ.comp (pSpanConj g P).symm.toMonoidHom

theorem phiConj_apply {P : Set (Subgroup G)} {n : ℕ} (φ : ↥(pSpan P) →* AE.AEQ n) (g : G)
    (y : ↥(pSpan (conjSub g '' P))) : phiConj φ g y = φ ((pSpanConj g P).symm y) := by
  rw [phiConj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

theorem phiConj_apply_conj {P : Set (Subgroup G)} {n : ℕ} (φ : ↥(pSpan P) →* AE.AEQ n) (g : G)
    (x : ↥(pSpan P)) : phiConj φ g (pSpanConj g P x) = φ x := by
  rw [phiConj_apply, MulEquiv.symm_apply_apply]

theorem phi_map_conj {P : Set (Subgroup G)} {n : ℕ} (φ : ↥(pSpan P) →* AE.AEQ n) (g : G)
    {L : Subgroup G} :
    ((conjSub g L).subgroupOf (pSpan (conjSub g '' P))).map (phiConj φ g) =
      (L.subgroupOf (pSpan P)).map φ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(pSpanConj g P).symm y, ?_, (phiConj_apply φ g y).symm⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, pSpanConj_symm_apply]
    exact mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hy)
  · rintro ⟨w, hw, rfl⟩
    refine ⟨pSpanConj g P w, ?_, phiConj_apply_conj φ g w⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, pSpanConj_apply]
    exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hw)

noncomputable def AEIdentOn.conj {P : Set (Subgroup G)} {n : ℕ} {𝒜 : Set (Finset (Fin n))}
    {H : Subgroup (AE.AEQ n)} (I : AEIdentOn P n 𝒜 H) (g : G) :
    AEIdentOn (conjSub g '' P) n 𝒜 H where
  φ := phiConj I.φ g
  range_eq := by
    refine Eq.trans ?_ I.range_eq
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(pSpanConj g P).symm y, (phiConj_apply I.φ g y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨pSpanConj g P y, phiConj_apply_conj I.φ g y⟩
  ker_le := by
    intro x hx
    have hx' : (pSpanConj g P).symm x ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, ← phiConj_apply]
      exact hx
    have hc := Subgroup.mem_center_iff.mp (I.ker_le hx')
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (pSpanConj g P) (hc ((pSpanConj g P).symm y))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  label := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨α, hα, h, b, hlab⟩ := I.label L hL
    exact ⟨α, hα, h, b, (phi_map_conj I.φ g).trans hlab⟩
  label_surj := by
    intro α hα h b
    obtain ⟨L, hL, hlab⟩ := I.label_surj α hα h b
    exact ⟨conjSub g L, ⟨L, hL, rfl⟩, (phi_map_conj I.φ g).trans hlab⟩

noncomputable def AEIdentOn.ofEq {P P' : Set (Subgroup G)} (hP : P = P') {n : ℕ}
    {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AE.AEQ n)} (I : AEIdentOn P n 𝒜 H) :
    AEIdentOn P' n 𝒜 H :=
  hP ▸ I

end Conj

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

theorem ThinStd.label_commutes_of_map_le {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {n : ℕ}
    (J : AELabel P n) (hk : IsPGroup 2 J.φ.ker) {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P)
    (hne : L₁ ≠ L₂) {S : Subgroup (AE.AEQ n)} (hS2 : IsPGroup 2 S)
    (h₁S : (L₁.subgroupOf (pSpan P)).map J.φ ≤ S) (h₂S : (L₂.subgroupOf (pSpan P)).map J.φ ≤ S) :
    ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  have hQ2 : IsPGroup 2 ((S.comap J.φ).map (pSpan P).subtype) :=
    (hS2.comap_of_ker_isPGroup J.φ hk).map _
  have hLQ : ∀ {L : Subgroup G}, L ∈ P → (L.subgroupOf (pSpan P)).map J.φ ≤ S →
      L ≤ (S.comap J.φ).map (pSpan P).subtype := by
    intro L hL hLS l hl
    exact ⟨⟨l, le_pSpan hL hl⟩, hLS (J.mem_map hL hl), rfl⟩
  exact hS.commutes_of_le (hPΩ h₁) (hPΩ h₂) hne hQ2 (hLQ h₁ h₁S) (hLQ h₂ h₂S)

omit [Finite G] in
theorem ThinStd.label_isPGroup_map {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {n : ℕ}
    (J : AELabel P n) {L : Subgroup G} (hL : L ∈ P) :
    IsPGroup 2 ((L.subgroupOf (pSpan P)).map J.φ) :=
  ((hS.two L (hPΩ hL)).of_equiv (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).symm).map _

theorem ThinStd.label_eq_of_map_le {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {n : ℕ} (hn : 5 ≤ n)
    (J : AELabel P n) (hk : IsPGroup 2 J.φ.ker) {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P)
    (hle : (L₁.subgroupOf (pSpan P)).map J.φ ≤ (L₂.subgroupOf (pSpan P)).map J.φ) :
    L₁ = L₂ := by
  by_contra hne
  have hc := hS.label_commutes_of_map_le hPΩ J hk h₁ h₂ hne (hS.label_isPGroup_map hPΩ J h₂)
    hle le_rfl
  obtain ⟨α, h, b, hlab⟩ := J.label L₁ h₁
  obtain ⟨x, hx, x', hx', hxx'⟩ := AE.exists_not_comm_memBar hn α h b
  rw [← hlab] at hx hx'
  obtain ⟨l, hl, rfl⟩ := J.exists_of_mem_map h₁ hx
  obtain ⟨l', hl', hl'e⟩ := J.exists_of_mem_map h₂ (hle hx')
  apply hxx'
  rw [← hl'e, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc l hl l' hl')

theorem ThinStd.label_commutes_of_map_comm {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {n : ℕ}
    (J : AELabel P n) (hk : IsPGroup 2 J.φ.ker) {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P)
    (hne : L₁ ≠ L₂)
    (hc : ∀ x ∈ (L₁.subgroupOf (pSpan P)).map J.φ, ∀ y ∈ (L₂.subgroupOf (pSpan P)).map J.φ,
      x * y = y * x) :
    ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  have hN : (L₁.subgroupOf (pSpan P)).map J.φ ≤
      Subgroup.normalizer ((L₂.subgroupOf (pSpan P)).map J.φ : Set (AE.AEQ n)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hc x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 := hc x hx _ hy
      have h2 : x * y * x⁻¹ = y :=
        mul_left_cancel (h1.trans (show x * y * x⁻¹ * x = x * y by group))
      rwa [h2] at hy
  have hsup := (hS.label_isPGroup_map hPΩ J h₁).to_sup_of_normal_right'
    (hS.label_isPGroup_map hPΩ J h₂) hN
  exact hS.label_commutes_of_map_le hPΩ J hk h₁ h₂ hne hsup le_sup_left le_sup_right

theorem ThinStd.label_disjoint_of_comm {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {n : ℕ}
    (hn : 5 ≤ n) (J : AELabel P n) (hk : IsPGroup 2 J.φ.ker) {L L' : Subgroup G} (hL : L ∈ P)
    (hL' : L' ∈ P) {u : G} (hu : IsUniqueInvolution L u) {α : Finset (Fin n)} {h : α.card = 4}
    {b : Bool} (hlab : (L.subgroupOf (pSpan P)).map J.φ = AE.memBar α h b)
    (hlab' : (L'.subgroupOf (pSpan P)).map J.φ = AE.memBar α h (!b))
    {L'' : Subgroup G} (hL'' : L'' ∈ P) (hne1 : L'' ≠ L) (hne2 : L'' ≠ L')
    (hcomm : ∀ x ∈ L, ∀ w ∈ L'', x * w = w * x) {β : Finset (Fin n)} {h'' : β.card = 4}
    {c : Bool} (hlab'' : (L''.subgroupOf (pSpan P)).map J.φ = AE.memBar β h'' c) :
    Disjoint α β := by
  have hβ : α ≠ β := by
    rintro rfl
    by_cases hcb : c = b
    · subst hcb
      exact hne1 (hS.label_eq_of_map_le hPΩ hn J hk hL'' hL (le_of_eq (hlab''.trans hlab.symm)))
    · have hcb' : c = !b := by cases b <;> cases c <;> simp_all
      subst hcb'
      exact hne2 (hS.label_eq_of_map_le hPΩ hn J hk hL'' hL' (le_of_eq (hlab''.trans hlab'.symm)))
  have hz := phi_map_eq_zBar J.φ hn hL (hS.card L (hPΩ hL)) hlab hu
  refine AE.disjoint_of_zBar_comm (h := h) (h' := h'') hβ (c := c) fun y hy => ?_
  rw [← hlab''] at hy
  obtain ⟨w, hw, rfl⟩ := J.exists_of_mem_map hL'' hy
  rw [← hz, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm u hu.mem w hw)

theorem ThinStd.aeTwinRel_of_label {A : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (J : AELabel {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} n)
    (hO : classicalInvolutionOddCore ↥(pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}) = ⊥)
    (hpart : ∀ L, MaxAdj (nbrAdj Ω) A L → ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map J.φ =
        AE.memBar α h b → ∃ L', MaxAdj (nbrAdj Ω) A L' ∧
          (L'.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map J.φ =
            AE.memBar α h (!b))
    (hy : ∀ L, MaxAdj (nbrAdj Ω) A L → ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map J.φ =
        AE.memBar α h b → ∃ y ∈ J.φ.range, y ^ 3 = 1 ∧ y * AE.zBar α h = AE.zBar α h * y ∧
          (∀ x ∈ AE.memBar α h (!b), y * x * y⁻¹ ∈ AE.memBar α h (!b)) ∧
          (∃ x ∈ AE.memBar α h (!b), y * x ≠ x * y) ∧
          ∀ L'', MaxAdj (nbrAdj Ω) A L'' → ∀ (β : Finset (Fin n)) (h' : β.card = 4) (c : Bool),
            (L''.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map J.φ =
              AE.memBar β h' c → Disjoint α β → ∀ x ∈ AE.memBar β h' c, y * x = x * y) :
    AETwinRel Ω A J.twinRel := by
  have hPΩ : {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} ⊆ Ω := fun M hM => hM.1.2.1
  have hk := J.isPGroup_ker hO
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro L L' ⟨hL, hL', α, h, b, hlab, hlab'⟩
    obtain ⟨hne, hker⟩ := phi_twins J.φ hn hL hL' (hS.card L (hPΩ hL)) (hS.card L' (hPΩ hL'))
      hlab hlab'
    refine ⟨hL, hL', hne, fun u u' hu hu' M hM m hm => ?_⟩
    have := Subgroup.mem_center_iff.mp (J.ker_le (hker u u' hu hu')) ⟨m, le_pSpan hM hm⟩
    exact (congrArg Subtype.val this).symm
  ·
    intro L hL
    obtain ⟨α, h, b, hlab⟩ := J.label L hL
    obtain ⟨L', hL', hlab'⟩ := hpart L hL α h b hlab
    exact ⟨L', hL, hL', α, h, b, hlab, hlab'⟩
  ·
    rintro L L' ⟨hL, hL', α, h, b, hlab, hlab'⟩ L'' hL'' hne1 hne2 hcomm
    obtain ⟨u, hu⟩ := (hS.hyp.omega1 L (hPΩ hL)).1
    obtain ⟨β, h'', c, hlab''⟩ := J.label L'' hL''
    have hd := hS.label_disjoint_of_comm hPΩ hn J hk hL hL' hu hlab hlab' hL'' hne1 hne2 hcomm
      hlab''
    refine hS.label_commutes_of_map_comm hPΩ J hk hL' hL'' (Ne.symm hne2) ?_
    rw [hlab', hlab'']
    exact AE.comm_memBar_of_disjoint hd (!b) c
  ·
    rintro L L' a ⟨hL, hL', α, h, b, hlab, hlab'⟩ ha l hl
    have hmem := J.mem_map hL hl
    rw [hlab] at hmem
    obtain ⟨m, hm, hme⟩ := hmem
    obtain ⟨m', hm', hmm'⟩ := AE.memAt_mul_vec α h b m hm
    have hm'mem : AE.mkQ n m' ∈
        (L'.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map J.φ := by
      rw [hlab']
      exact ⟨m', hm', rfl⟩
    obtain ⟨l', hl', hl'e⟩ := J.exists_of_mem_map hL' hm'mem
    refine ⟨l', hl', ?_⟩
    have hVn : ((AE.vecSub n).map (AE.mkQ n)).Normal :=
      AE.vecSub_normal.map _ (QuotientGroup.mk'_surjective _)
    have hlF : l⁻¹ * l' ∈ (((AE.vecSub n).map (AE.mkQ n)).comap J.φ).map
        (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}).subtype := by
      refine ⟨⟨l, le_pSpan hL hl⟩⁻¹ * ⟨l', le_pSpan hL' hl'⟩, ?_, rfl⟩
      show J.φ (⟨l, le_pSpan hL hl⟩⁻¹ * ⟨l', le_pSpan hL' hl'⟩) ∈ (AE.vecSub n).map (AE.mkQ n)
      rw [map_mul, map_inv, hl'e, ← hme, ← map_inv, ← map_mul]
      exact ⟨_, hmm', rfl⟩
    have hFn : ∀ x ∈ pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}, ∀ q ∈
        (((AE.vecSub n).map (AE.mkQ n)).comap J.φ).map
          (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}).subtype,
        x * q * x⁻¹ ∈ (((AE.vecSub n).map (AE.mkQ n)).comap J.φ).map
          (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}).subtype := by
      intro x hx q hq
      obtain ⟨q', hq', rfl⟩ := hq
      refine ⟨⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹, ?_, rfl⟩
      show J.φ (⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹) ∈ (AE.vecSub n).map (AE.mkQ n)
      rw [map_mul, map_mul, map_inv]
      exact hVn.conj_mem _ hq' _
    have hV2 : IsPGroup 2 ((AE.vecSub n).map (AE.mkQ n)) := by
      rintro ⟨_, v, hv, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, pow_one, pow_two, ← map_mul, AE.vecSub_mul_self hv, map_one]
      rfl
    exact hS.le_Qz_of_normal ha (Subgroup.map_subtype_le _) hFn
      ((hV2.comap_of_ker_isPGroup J.φ hk).map _) hlF
  ·
    rintro L L' u ⟨hL, hL', α, h, b, hlab, hlab'⟩ hu
    obtain ⟨a, ha⟩ := (hS.hyp.omega1 A hL.1.1).1
    obtain ⟨yb, hyb, hyb3, hybz, hybn, ⟨x₀, hx₀, hx₀y⟩, hybc⟩ := hy L hL α h b hlab
    obtain ⟨y, hyyb, k, hyk⟩ := J.exists_lift_pow_three hyb hyb3
    have hz := phi_map_eq_zBar J.φ hn hL (hS.card L (hPΩ hL)) hlab hu
    refine ⟨(y : G), y.2, ⟨k, ?_⟩, ?_, ?_, ?_, ?_⟩
    · have := congrArg Subtype.val hyk
      rwa [Subgroup.coe_pow] at this
    · have := J.comm_of_pow_three hk hyk (w := ⟨u, le_pSpan hL hu.mem⟩)
        (by rw [hyyb, hz]; exact hybz)
      exact congrArg Subtype.val this
    · have hL'y : MaxAdj (nbrAdj Ω) A (conjSub (y : G) L') :=
        hS.maxAdj_conj_of_mem hL' ha (hS.pSpan_le_centralizer ha y.2)
      have hle : ((conjSub (y : G) L').subgroupOf
          (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map J.φ ≤
          (L'.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map J.φ := by
        intro x hx
        obtain ⟨x', hx', rfl⟩ := J.exists_of_mem_map hL'y hx
        have h1 : (y : G)⁻¹ * x' * y ∈ L' := mem_conjSub_iff.mp hx'
        have h2 : J.φ ⟨x', le_pSpan hL'y hx'⟩ =
            J.φ y * J.φ ⟨(y : G)⁻¹ * x' * y, le_pSpan hL' h1⟩ * (J.φ y)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          apply Subtype.ext
          show x' = (y : G) * ((y : G)⁻¹ * x' * y) * (y : G)⁻¹
          group
        have h3 := J.mem_map hL' h1
        rw [hlab'] at h3 ⊢
        rw [h2, hyyb]
        exact hybn _ h3
      exact mem_normalizer_of_conjSub_eq (hS.label_eq_of_map_le hPΩ hn J hk hL'y hL' hle)
    · rw [← hlab'] at hx₀
      obtain ⟨l', hl', rfl⟩ := J.exists_of_mem_map hL' hx₀
      refine ⟨l', hl', fun he => hx₀y ?_⟩
      rw [← hyyb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext he
    · intro L'' hL'' hne1 hne2 hcomm w hw
      obtain ⟨β, h'', c, hlab''⟩ := J.label L'' hL''
      have hd := hS.label_disjoint_of_comm hPΩ hn J hk hL hL' hu hlab hlab' hL'' hne1 hne2
        hcomm hlab''
      have h3 := J.mem_map hL'' hw
      rw [hlab''] at h3
      have := J.comm_of_pow_three hk hyk (w := ⟨w, le_pSpan hL'' hw⟩)
        (by rw [hyyb]; exact hybc L'' hL'' β h'' c hlab'' hd _ h3)
      exact congrArg Subtype.val this


omit [Finite G] hS in
theorem _root_.CFSG.ClassicalInvolution.Q3.AE.eq_of_memBar_eq {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    {α β : Finset (Fin n)} {h : α.card = 4} {h' : β.card = 4} {b c : Bool}
    (he : AE.memBar α h b = AE.memBar β h' c) : α = β := by
  have hmem : AE.zBar α h ∈ AE.memBar β h' c := he ▸ AE.zBar_mem_memBar α h b
  rcases AE.eq_of_mem_memBar_mul_self hn hmem (AE.zBar_mul_self α h) with h1 | h1
  · exact absurd h1 (AE.zBar_ne_one hn α h)
  · exact AE.eq_of_zBar_eq hn8 h1

theorem ThinStd.aeTwinRel_e64 {A : Subgroup G}
    (I : AEIdentOn {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} 7 AE.e64Sets AE.e64Sub)
    (hO : classicalInvolutionOddCore ↥(pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}) = ⊥) :
    AETwinRel Ω A I.toLabel.twinRel := by
  have hlabel : ∀ L, MaxAdj (nbrAdj Ω) A L → ∀ (α : Finset (Fin 7)) (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map I.φ =
        AE.memBar α h b → α ∈ AE.e64Sets := by
    intro L hL α h b hlab
    obtain ⟨α', hα', h', b', hlab'⟩ := I.label L hL
    have := AE.eq_of_memBar_eq (by norm_num) (by norm_num) (hlab.symm.trans hlab')
    rw [this]
    exact hα'
  refine hS.aeTwinRel_of_label (by norm_num) I.toLabel hO ?_ ?_
  · intro L hL α h b hlab
    exact I.label_surj α (hlabel L hL α h b hlab) h (!b)
  · intro L hL α h b hlab
    have hα := hlabel L hL α h b hlab
    obtain ⟨y, hy, hy3, hyz, hyn, hynt⟩ := AE.e64_yElt hα h
    refine ⟨y, ?_, hy3, hyz, hyn (!b), hynt (!b), ?_⟩
    · show y ∈ I.φ.range
      rw [I.range_eq]
      exact hy
    · intro L'' hL'' β h' c hlab'' hd
      exfalso
      have hβ := hlabel L'' hL'' β h' c hlab''
      by_cases hαβ : α = β
      · subst hαβ
        have : α = ∅ := (Finset.disjoint_self_iff_empty α).mp hd
        rw [this, Finset.card_empty] at h
        exact absurd h (by norm_num)
      · exact AE.e64Sets_not_disjoint hα hβ hαβ hd

end CFSG.ClassicalInvolution.Q3.TC.Thin

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


theorem tightCaseE64Leaf_holds (n : ℕ) : TightCaseE64Leaf n := by
  intro Y _ _ R S t hL hO hconn hsep hall ⟨I⟩
  have hS := hL.thinStd hO hconn hsep
  have huniq := hL.datum.isUniqueInvolution_core
  have hOC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : Y) ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y)) := ⟨x, hx, rfl⟩
    unfold TightOddCent at hO
    rw [hO, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hOK := hS.oddCore_pSpan_eq_bot huniq hOC
  have hα0 : ({0, 1, 3} : Finset (Fin 7))ᶜ ∈ AE.e64Sets := ⟨_, by simp [AE.fanoLines], rfl⟩
  obtain ⟨N, hN, -⟩ := I.label_surj _ hα0 (AE.fanoLines_compl_card _ (by simp [AE.fanoLines]))
    true
  refine hS.false_of_aeTwinRel hL.center hall hN (hS.aeTwinRel_e64 I hOK) fun L hL' => ?_
  obtain ⟨g, rfl⟩ := hS.trans L hL'.1.2.1
  exact ⟨_, hS.aeTwinRel_e64 (TC.Thin.AEIdentOn.ofEq (hS.maxAdjSet_conj _ g).symm (I.conj g))
    (hS.oddCore_pSpan_conj hOK g)⟩

variable {n : ℕ} in
theorem tightCaseBLeaf_of_indep (h : TightIndepLeaf n) : TightCaseBLeaf n := by
  intro Y _ _ R S t hL hO hconn hsep hall M N N' hN hN' hne u u' hu hu' hc hNN'
  exact h Y R S t hL hO hconn hsep hall M hN.1.1 N N' hN hN' hne hNN'.1

variable {n : ℕ} in
theorem tightIndepLeaf_of_thmD3' (hD : TC.Thin.TightThmD3) (h29 : TightCase29Leaf n) :
    TightIndepLeaf n :=
  tightIndepLeaf_of_thmD3 hD (tightCaseE64Leaf_holds n) h29

end Cit3

end CFSG.ClassicalInvolution.Q3
