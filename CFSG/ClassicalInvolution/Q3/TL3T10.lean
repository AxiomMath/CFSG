module

public import CFSG.ClassicalInvolution.Q3.TL3T9
public import CFSG.ClassicalInvolution.Q3.AE.Twins

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G]

structure AEIdent (P : Set (Subgroup G)) (n : ℕ) where
  φ : ↥(pSpan P) →* AE.AEQ n
  range_eq : φ.range = (AE.aeSub n).map (AE.mkQ n)
  ker_le : φ.ker ≤ Subgroup.center ↥(pSpan P)
  label : ∀ L ∈ P, ∃ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
    (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b
  label_surj : ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool), ∃ L ∈ P,
    (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b

namespace AEIdent

variable {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n)

theorem mem_map {L : Subgroup G} (hL : L ∈ P) {l : G} (hl : l ∈ L) :
    I.φ ⟨l, le_pSpan hL hl⟩ ∈ (L.subgroupOf (pSpan P)).map I.φ :=
  ⟨⟨l, le_pSpan hL hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩

theorem exists_of_mem_map {L : Subgroup G} (hL : L ∈ P) {x : AE.AEQ n}
    (hx : x ∈ (L.subgroupOf (pSpan P)).map I.φ) :
    ∃ l : G, ∃ hl : l ∈ L, I.φ ⟨l, le_pSpan hL hl⟩ = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩

theorem comm_of_pow_three (hk : IsPGroup 2 I.φ.ker) {y w : ↥(pSpan P)} {a : ℕ}
    (hy : y ^ 3 ^ a = 1) (h : I.φ y * I.φ w = I.φ w * I.φ y) : y * w = w * y := by
  set c := w⁻¹ * (y * w * y⁻¹) with hc
  have hcker : c ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_inv, map_mul, map_mul, map_inv, h]
    group
  have hyw : y * w * y⁻¹ = w * c := by rw [hc]; group
  have hpow : ∀ k : ℕ, y ^ k * w * (y ^ k)⁻¹ = w * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : y * c ^ k * y⁻¹ = c ^ k := by
        have := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ (I.ker_le hcker) k) y
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

theorem isPGroup_ker (hO : classicalInvolutionOddCore ↥(pSpan P) = ⊥) : IsPGroup 2 I.φ.ker :=
  (isPGroup_center_of_corefree hO).to_le I.ker_le

theorem exists_lift_pow_three {x : AE.AEQ n} (hx : x ∈ I.φ.range) (hx3 : x ^ 3 = 1) :
    ∃ y : ↥(pSpan P), I.φ y = x ∧ ∃ a : ℕ, y ^ 3 ^ a = 1 := by
  obtain ⟨y₀, rfl⟩ := hx
  obtain ⟨a, r, hr, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y₀).ne' 3 (by norm_num)
  refine ⟨y₀ ^ (r * r), ?_, a, ?_⟩
  · have hr2 : r * r % 3 = 1 := by
      have : r % 3 = 1 ∨ r % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [map_pow, pow_eq_pow_mod _ hx3, hr2, pow_one]
  · rw [← pow_mul, show r * r * 3 ^ a = (3 ^ a * r) * r by ring, ← hN, pow_mul,
      pow_orderOf_eq_one, one_pow]

theorem injOn (hn : 5 ≤ n) {L : Subgroup G} (hL : L ∈ P) (h8 : Nat.card L = 8)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α h b) {l₁ l₂ : G} (h₁ : l₁ ∈ L)
    (h₂ : l₂ ∈ L) (he : I.φ ⟨l₁, le_pSpan hL h₁⟩ = I.φ ⟨l₂, le_pSpan hL h₂⟩) : l₁ = l₂ := by
  let f : ↥(L.subgroupOf (pSpan P)) → ↥(AE.memBar α h b) := fun x =>
    ⟨I.φ x, by rw [← hlab]; exact ⟨x, x.2, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← hlab] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  have hcard : Nat.card ↥(L.subgroupOf (pSpan P)) ≤ Nat.card ↥(AE.memBar α h b) := by
    rw [AE.natCard_memBar hn, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).toEquiv,
      h8]
  have hinj := (hf.bijective_of_nat_card_le hcard).1
  have := @hinj ⟨⟨l₁, le_pSpan hL h₁⟩, Subgroup.mem_subgroupOf.mpr h₁⟩
    ⟨⟨l₂, le_pSpan hL h₂⟩, Subgroup.mem_subgroupOf.mpr h₂⟩ (Subtype.ext he)
  exact congrArg (fun x : ↥(L.subgroupOf (pSpan P)) => ((x : ↥(pSpan P)) : G)) this

theorem map_eq_zBar (hn : 5 ≤ n) {L : Subgroup G} (hL : L ∈ P) (h8 : Nat.card L = 8)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α h b) {u : G}
    (hu : IsUniqueInvolution L u) : I.φ ⟨u, le_pSpan hL hu.mem⟩ = AE.zBar α h := by
  have hmem : I.φ ⟨u, le_pSpan hL hu.mem⟩ ∈ AE.memBar α h b := by
    rw [← hlab]
    exact I.mem_map hL hu.mem
  have hsq : I.φ ⟨u, le_pSpan hL hu.mem⟩ * I.φ ⟨u, le_pSpan hL hu.mem⟩ = 1 := by
    rw [← map_mul, ← map_one I.φ]
    congr 1
    exact Subtype.ext hu.sq
  rcases AE.eq_of_mem_memBar_mul_self hn hmem hsq with h1 | h1
  · exfalso
    apply hu.ne_one
    have : I.φ ⟨u, le_pSpan hL hu.mem⟩ = I.φ ⟨1, le_pSpan hL L.one_mem⟩ := by
      rw [h1]
      exact (map_one I.φ).symm
    exact I.injOn hn hL h8 hlab hu.mem L.one_mem this
  · exact h1

end AEIdent

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

theorem ThinStd.commutes_of_map_le {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {n : ℕ}
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P)
    (hne : L₁ ≠ L₂) {S : Subgroup (AE.AEQ n)} (hS2 : IsPGroup 2 S)
    (h₁S : (L₁.subgroupOf (pSpan P)).map I.φ ≤ S) (h₂S : (L₂.subgroupOf (pSpan P)).map I.φ ≤ S) :
    ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  have hQ2 : IsPGroup 2 ((S.comap I.φ).map (pSpan P).subtype) :=
    (hS2.comap_of_ker_isPGroup I.φ hk).map _
  have hLQ : ∀ {L : Subgroup G}, L ∈ P → (L.subgroupOf (pSpan P)).map I.φ ≤ S →
      L ≤ (S.comap I.φ).map (pSpan P).subtype := by
    intro L hL hLS l hl
    exact ⟨⟨l, le_pSpan hL hl⟩, hLS (I.mem_map hL hl), rfl⟩
  exact hS.commutes_of_le (hPΩ h₁) (hPΩ h₂) hne hQ2 (hLQ h₁ h₁S) (hLQ h₂ h₂S)

omit [Finite G] in
theorem ThinStd.isPGroup_map {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {n : ℕ} (I : AEIdent P n)
    {L : Subgroup G} (hL : L ∈ P) : IsPGroup 2 ((L.subgroupOf (pSpan P)).map I.φ) :=
  ((hS.two L (hPΩ hL)).of_equiv (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).symm).map _

theorem ThinStd.eq_of_map_le {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P)
    (hle : (L₁.subgroupOf (pSpan P)).map I.φ ≤ (L₂.subgroupOf (pSpan P)).map I.φ) : L₁ = L₂ := by
  by_contra hne
  have hc := hS.commutes_of_map_le hPΩ I hk h₁ h₂ hne (hS.isPGroup_map hPΩ I h₂) hle le_rfl
  obtain ⟨α, h, b, hlab⟩ := I.label L₁ h₁
  obtain ⟨x, hx, x', hx', hxx'⟩ := AE.exists_not_comm_memBar hn α h b
  rw [← hlab] at hx hx'
  obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map h₁ hx
  obtain ⟨l', hl', hl'e⟩ := I.exists_of_mem_map h₂ (hle hx')
  apply hxx'
  rw [← hl'e, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc l hl l' hl')

theorem ThinStd.commutes_of_map_comm {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {n : ℕ}
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P)
    (hne : L₁ ≠ L₂)
    (hc : ∀ x ∈ (L₁.subgroupOf (pSpan P)).map I.φ, ∀ y ∈ (L₂.subgroupOf (pSpan P)).map I.φ,
      x * y = y * x) :
    ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
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
      have h2 : x * y * x⁻¹ = y :=
        mul_left_cancel (h1.trans (show x * y * x⁻¹ * x = x * y by group))
      rwa [h2] at hy
  have hsup := (hS.isPGroup_map hPΩ I h₁).to_sup_of_normal_right' (hS.isPGroup_map hPΩ I h₂) hN
  exact hS.commutes_of_map_le hPΩ I hk h₁ h₂ hne hsup le_sup_left le_sup_right

theorem ThinStd.map_eq_twin {A : Subgroup G} {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (I : AEIdent {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} n) (hk : IsPGroup 2 I.φ.ker)
    {L L' : Subgroup G} (hL : MaxAdj (nbrAdj Ω) A L) (hL' : MaxAdj (nbrAdj Ω) A L')
    (hne : L ≠ L') {u u' : G} (hu : IsUniqueInvolution L u) (hu' : IsUniqueInvolution L' u')
    (hc : CentX Ω A (u * u')) {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map I.φ =
      AE.memBar α h b) :
    (L'.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map I.φ =
      AE.memBar α h (!b) := by
  have hPΩ : {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} ⊆ Ω := fun M hM => hM.1.2.1
  obtain ⟨α', h', b', hlab'⟩ := I.label L' hL'
  have hz := I.map_eq_zBar hn hL (hS.card L (hPΩ hL)) hlab hu
  have hz' := I.map_eq_zBar hn hL' (hS.card L' (hPΩ hL')) hlab' hu'
  have hαα' : α = α' := by
    refine AE.eq_of_zBar_mul_comm hn8 (h := h) (h' := h') fun γ hγ c x hx => ?_
    obtain ⟨M, hM, hMlab⟩ := I.label_surj γ hγ c
    rw [← hMlab] at hx
    obtain ⟨m, hm, rfl⟩ := I.exists_of_mem_map hM hx
    have key : (⟨u, le_pSpan hL hu.mem⟩ * ⟨u', le_pSpan hL' hu'.mem⟩ :
        ↥(pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})) *
        ⟨m, le_pSpan hM hm⟩ = ⟨m, le_pSpan hM hm⟩ * (⟨u, le_pSpan hL hu.mem⟩ *
          ⟨u', le_pSpan hL' hu'.mem⟩) :=
      Subtype.ext (comm_of_mem_pSpan (le_pSpan hM hm) hc)
    calc (AE.zBar α h * AE.zBar α' h') * I.φ ⟨m, le_pSpan hM hm⟩ =
        I.φ ((⟨u, le_pSpan hL hu.mem⟩ * ⟨u', le_pSpan hL' hu'.mem⟩) * ⟨m, le_pSpan hM hm⟩) := by
          rw [map_mul, map_mul, hz, hz']
      _ = I.φ (⟨m, le_pSpan hM hm⟩ * (⟨u, le_pSpan hL hu.mem⟩ * ⟨u', le_pSpan hL' hu'.mem⟩)) := by
          rw [key]
      _ = I.φ ⟨m, le_pSpan hM hm⟩ * (AE.zBar α h * AE.zBar α' h') := by
          rw [map_mul, map_mul, hz, hz']
  subst hαα'
  have hb : b' = !b := by
    by_contra hb
    have hbb : b' = b := by cases b <;> cases b' <;> simp_all
    subst hbb
    exact hne (hS.eq_of_map_le hPΩ hn I hk hL hL' (le_of_eq (hlab.trans hlab'.symm)))
  rw [hlab', hb]

theorem ThinStd.disjoint_of_comm {A : Subgroup G} {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (I : AEIdent {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} n) (hk : IsPGroup 2 I.φ.ker)
    {L L' : Subgroup G} (hL : MaxAdj (nbrAdj Ω) A L) (hL' : MaxAdj (nbrAdj Ω) A L')
    (hne : L ≠ L') {u u' : G} (hu : IsUniqueInvolution L u) (hu' : IsUniqueInvolution L' u')
    (hc : CentX Ω A (u * u')) {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map I.φ =
      AE.memBar α h b)
    {L'' : Subgroup G} (hL'' : MaxAdj (nbrAdj Ω) A L'') (hne1 : L'' ≠ L) (hne2 : L'' ≠ L')
    (hcomm : ∀ x ∈ L, ∀ w ∈ L'', x * w = w * x) {β : Finset (Fin n)} {h'' : β.card = 4}
    {c : Bool}
    (hlab'' : (L''.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map I.φ =
      AE.memBar β h'' c) :
    Disjoint α β := by
  have hPΩ : {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} ⊆ Ω := fun M hM => hM.1.2.1
  have hlab' := hS.map_eq_twin hn hn8 I hk hL hL' hne hu hu' hc hlab
  have hβ : α ≠ β := by
    rintro rfl
    by_cases hcb : c = b
    · subst hcb
      exact hne1 (hS.eq_of_map_le hPΩ hn I hk hL'' hL (le_of_eq (hlab''.trans hlab.symm)))
    · have hcb' : c = !b := by cases b <;> cases c <;> simp_all
      subst hcb'
      exact hne2 (hS.eq_of_map_le hPΩ hn I hk hL'' hL' (le_of_eq (hlab''.trans hlab'.symm)))
  have hz := I.map_eq_zBar hn hL (hS.card L (hPΩ hL)) hlab hu
  refine AE.disjoint_of_zBar_comm (h := h) (h' := h'') hβ (c := c) fun y hy => ?_
  rw [← hlab''] at hy
  obtain ⟨w, hw, rfl⟩ := I.exists_of_mem_map hL'' hy
  rw [← hz, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm u hu.mem w hw)

theorem ThinStd.aeTwinAt_of_aeIdent {A : Subgroup G} {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (I : AEIdent {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} n)
    (hO : classicalInvolutionOddCore ↥(pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}) = ⊥) :
    AETwinAt Ω A := by
  set P := {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} with hP
  have hPΩ : P ⊆ Ω := fun M hM => hM.1.2.1
  have hk := I.isPGroup_ker hO
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro L hL
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    obtain ⟨L', hL', hlab'⟩ := I.label_surj α h (!b)
    refine ⟨L', hL', fun heq => ?_, fun u u' hu hu' => ?_⟩
    · subst heq
      rw [hlab] at hlab'
      cases b
      · exact AE.memBar_true_ne_false hn α h hlab'.symm
      · exact AE.memBar_true_ne_false hn α h hlab'
    · have hz := I.map_eq_zBar hn hL (hS.card L (hPΩ hL)) hlab hu
      have hz' := I.map_eq_zBar hn hL' (hS.card L' (hPΩ hL')) hlab' hu'
      have hker : (⟨u, le_pSpan hL hu.mem⟩ * ⟨u', le_pSpan hL' hu'.mem⟩ : ↥(pSpan P)) ∈
          I.φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, hz, hz']
        exact AE.zBar_mul_self α h
      intro M hM m hm
      have := Subgroup.mem_center_iff.mp (I.ker_le hker) ⟨m, le_pSpan hM hm⟩
      exact (congrArg Subtype.val this).symm
  ·
    intro L L' u u' hL hL' hne hu hu' hc L'' hL'' hne1 hne2 hcomm
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    have hlab' := hS.map_eq_twin hn hn8 I hk hL hL' hne hu hu' hc hlab
    obtain ⟨β, h'', c, hlab''⟩ := I.label L'' hL''
    have hd := hS.disjoint_of_comm hn hn8 I hk hL hL' hne hu hu' hc hlab hL'' hne1 hne2 hcomm
      hlab''
    refine hS.commutes_of_map_comm hPΩ I hk hL' hL'' (Ne.symm hne2) ?_
    rw [hlab', hlab'']
    exact AE.comm_memBar_of_disjoint hd (!b) c
  ·
    intro L L' u u' a hL hL' hne hu hu' hc ha l hl
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    have hlab' := hS.map_eq_twin hn hn8 I hk hL hL' hne hu hu' hc hlab
    have hmem := I.mem_map hL hl
    rw [hlab] at hmem
    obtain ⟨m, hm, hme⟩ := hmem
    obtain ⟨m', hm', hmm'⟩ := AE.memAt_mul_vec α h b m hm
    have hm'mem : AE.mkQ n m' ∈ (L'.subgroupOf (pSpan P)).map I.φ := by
      rw [hlab']
      exact ⟨m', hm', rfl⟩
    obtain ⟨l', hl', hl'e⟩ := I.exists_of_mem_map hL' hm'mem
    refine ⟨l', hl', ?_⟩
    have hVn : ((AE.vecSub n).map (AE.mkQ n)).Normal :=
      AE.vecSub_normal.map _ (QuotientGroup.mk'_surjective _)
    have hlF : l⁻¹ * l' ∈ (((AE.vecSub n).map (AE.mkQ n)).comap I.φ).map (pSpan P).subtype := by
      refine ⟨⟨l, le_pSpan hL hl⟩⁻¹ * ⟨l', le_pSpan hL' hl'⟩, ?_, rfl⟩
      show I.φ (⟨l, le_pSpan hL hl⟩⁻¹ * ⟨l', le_pSpan hL' hl'⟩) ∈ (AE.vecSub n).map (AE.mkQ n)
      rw [map_mul, map_inv, hl'e, ← hme, ← map_inv, ← map_mul]
      exact ⟨_, hmm', rfl⟩
    have hFn : ∀ x ∈ pSpan P, ∀ q ∈ (((AE.vecSub n).map (AE.mkQ n)).comap I.φ).map
        (pSpan P).subtype, x * q * x⁻¹ ∈ (((AE.vecSub n).map (AE.mkQ n)).comap I.φ).map
          (pSpan P).subtype := by
      intro x hx q hq
      obtain ⟨q', hq', rfl⟩ := hq
      refine ⟨⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹, ?_, rfl⟩
      show I.φ (⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹) ∈ (AE.vecSub n).map (AE.mkQ n)
      rw [map_mul, map_mul, map_inv]
      exact hVn.conj_mem _ hq' _
    have hV2 : IsPGroup 2 ((AE.vecSub n).map (AE.mkQ n)) := by
      rintro ⟨_, v, hv, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, pow_one, pow_two, ← map_mul, AE.vecSub_mul_self hv, map_one]
      rfl
    exact hS.le_Qz_of_normal ha (Subgroup.map_subtype_le _) hFn
      ((hV2.comap_of_ker_isPGroup I.φ hk).map _) hlF
  ·
    intro L L' u u' hL hL' hne hu hu' hc
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    have hlab' := hS.map_eq_twin hn hn8 I hk hL hL' hne hu hu' hc hlab
    obtain ⟨a, ha⟩ := (hS.hyp.omega1 A hL.1.1).1
    have hrange : AE.yBar α h ∈ I.φ.range := by
      rw [I.range_eq]
      exact AE.yBar_mem α h
    obtain ⟨y, hy, k, hyk⟩ := I.exists_lift_pow_three hrange (AE.yBar_pow_three α h)
    have hz := I.map_eq_zBar hn hL (hS.card L (hPΩ hL)) hlab hu
    refine ⟨(y : G), y.2, ⟨k, ?_⟩, ?_, ?_, ?_, ?_⟩
    · have := congrArg Subtype.val hyk
      rwa [Subgroup.coe_pow] at this
    · have := I.comm_of_pow_three hk hyk (w := ⟨u, le_pSpan hL hu.mem⟩)
        (by rw [hy, hz]; exact AE.yBar_comm_zBar α h)
      exact congrArg Subtype.val this
    · have hL'y : MaxAdj (nbrAdj Ω) A (conjSub (y : G) L') :=
        hS.maxAdj_conj_of_mem hL' ha (hS.pSpan_le_centralizer ha y.2)
      have hle : ((conjSub (y : G) L').subgroupOf (pSpan P)).map I.φ ≤
          (L'.subgroupOf (pSpan P)).map I.φ := by
        intro x hx
        obtain ⟨x', hx', rfl⟩ := I.exists_of_mem_map hL'y hx
        have h1 : (y : G)⁻¹ * x' * y ∈ L' := mem_conjSub_iff.mp hx'
        have h2 : I.φ ⟨x', le_pSpan hL'y hx'⟩ =
            I.φ y * I.φ ⟨(y : G)⁻¹ * x' * y, le_pSpan hL' h1⟩ * (I.φ y)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          apply Subtype.ext
          show x' = (y : G) * ((y : G)⁻¹ * x' * y) * (y : G)⁻¹
          group
        have h3 := I.mem_map hL' h1
        rw [hlab'] at h3 ⊢
        rw [h2, hy]
        exact AE.yBar_conj_mem_memBar α h (!b) _ h3
      exact mem_normalizer_of_conjSub_eq (hS.eq_of_map_le hPΩ hn I hk hL'y hL' hle)
    · obtain ⟨x, hx, hxy⟩ := AE.yBar_not_comm_memBar hn α h (!b)
      rw [← hlab'] at hx
      obtain ⟨l', hl', rfl⟩ := I.exists_of_mem_map hL' hx
      refine ⟨l', hl', fun he => hxy ?_⟩
      rw [← hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext he
    · intro L'' hL'' hne1 hne2 hcomm w hw
      obtain ⟨β, h'', c, hlab''⟩ := I.label L'' hL''
      have hd := hS.disjoint_of_comm hn hn8 I hk hL hL' hne hu hu' hc hlab hL'' hne1 hne2 hcomm
        hlab''
      have h3 := I.mem_map hL'' hw
      rw [hlab''] at h3
      have := I.comm_of_pow_three hk hyk (w := ⟨w, le_pSpan hL'' hw⟩)
        (by rw [hy]; exact AE.yBar_comm_memBar_of_disjoint hd c _ h3)
      exact congrArg Subtype.val this

theorem ThinStd.false_of_triangle_of_aeIdent
    (hall : ∀ M N : Subgroup G, MaxAdj (nbrAdj Ω) M N → ThinAt Ω M N)
    {M N N' : Subgroup G} {m n : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8) (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (IM : AEIdent {L : Subgroup G | MaxAdj (nbrAdj Ω) M L} m)
    (IN : AEIdent {L : Subgroup G | MaxAdj (nbrAdj Ω) N L} n)
    (hOM : classicalInvolutionOddCore ↥(pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L}) = ⊥)
    (hON : classicalInvolutionOddCore ↥(pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) N L}) = ⊥)
    (hN : MaxAdj (nbrAdj Ω) M N) (hN' : MaxAdj (nbrAdj Ω) M N') (hne : N ≠ N')
    {u u' : G} (hu : IsUniqueInvolution N u) (hu' : IsUniqueInvolution N' u')
    (hc : CentX Ω M (u * u')) (hNN' : MaxAdj (nbrAdj Ω) N N') : False :=
  hS.false_of_triangle_of_aeTwin hall (hS.aeTwinAt_of_aeIdent hm hm8 IM hOM)
    (hS.aeTwinAt_of_aeIdent hn hn8 IN hON) hN hN' hne hu hu' hc hNN'

end CFSG.ClassicalInvolution.Q3.TC.Thin
