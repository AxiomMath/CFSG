module

public import CFSG.ClassicalInvolution.Q3.TL4D1Pack
public import CFSG.ClassicalInvolution.Q3.TL3T14
public import CFSG.ClassicalInvolution.Q3.TL4D1Thin

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

omit [Finite G] in
theorem mem_of_pow_two_mem {H : Subgroup G} {g : G} (ho : Odd (orderOf g)) {j : ℕ}
    (hg : g ^ 2 ^ j ∈ H) : g ∈ H := by
  rcases Nat.lt_or_ge 1 (orderOf g) with h1 | h1
  · have hcop : Nat.Coprime (2 ^ j) (orderOf g) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr ho)
    obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have : g = (g ^ 2 ^ j) ^ t := by rw [← pow_mul, ← pow_mod_orderOf, ht, pow_one]
    rw [this]
    exact H.pow_mem hg t
  · have : g = 1 := by
      obtain ⟨t, ht⟩ := ho
      exact orderOf_eq_one_iff.mp (by omega)
    rw [this]
    exact H.one_mem

section Ident

variable (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J) (h8 : ∀ J ∈ Δ, Nat.card J = 8)
  {P : Set (Subgroup G)} (hPΔ : P ⊆ Δ) (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
  {n : ℕ} (hn : 5 ≤ n) {𝒜 : Set (Finset (Fin n))} {M : Subgroup (AE.AEQ n)}
  (I : AEIdentOn P n 𝒜 M) (hk : IsPGroup 2 I.φ.ker)

include hΩ h2 h8 hPΔ hinv hn hk in
theorem le_oddGen_of_ident (hM3 : ModelThree 𝒜 M) {L : Subgroup G} (hL : L ∈ P) :
    L ≤ oddGen (pSpan P) := by
  set X := pSpan P with hX
  obtain ⟨α, hα, h, b, hlab⟩ := I.label L hL
  obtain ⟨yb, hybM, hyb3, hybn, hybcl⟩ := hM3 α hα h b
  have hybr : yb ∈ I.φ.range := by rw [I.range_eq]; exact hybM
  obtain ⟨y, hyφ, a, hya⟩ := I.toLabel.exists_lift_pow_three hybr hyb3
  have hyφ' : I.φ y = yb := hyφ
  have hyo : Odd (orderOf (y : G)) := by
    refine (Odd.pow (by decide : Odd 3) : Odd (3 ^ a)).of_dvd_nat
      (orderOf_dvd_of_pow_eq_one ?_)
    have := congrArg Subtype.val hya
    simpa using this
  have hyL : conjSub (y : G) L = L := by
    have hL' := hinv L hL y y.2
    obtain ⟨α', -, h', b', hlab'⟩ := I.label _ hL'
    refine eq_of_map_le_memBar hΩ h2 hn I.φ hk (hPΔ hL') (hPΔ hL) (le_pSpan hL')
      (le_pSpan hL) hlab' ?_
    rintro _ ⟨⟨x, hxX⟩, hx, rfl⟩
    have hx' : x ∈ conjSub (y : G) L := hx
    rw [mem_conjSub_iff] at hx'
    have hmem : I.φ (y⁻¹ * ⟨x, hxX⟩ * y) ∈ (L.subgroupOf X).map I.φ :=
      ⟨_, Subgroup.mem_subgroupOf.mpr (by simpa using hx'), rfl⟩
    rw [hlab] at hmem ⊢
    have h1 := hybn _ hmem
    rw [map_mul, map_mul, map_inv, hyφ'] at h1
    convert h1 using 1
    group
  have hyl : ∀ l ∈ L, (y : G) * l⁻¹ * (y : G)⁻¹ ∈ L := fun l hl => by
    have := conj_mem_conjSub (n := (y : G)) (L.inv_mem hl)
    rwa [hyL] at this
  set J₀ : Subgroup G := Subgroup.closure {x | ∃ l ∈ L, x = l * y * l⁻¹ * (y : G)⁻¹} with hJ₀
  have hJ₀L : J₀ ≤ L := (Subgroup.closure_le _).mpr fun x ⟨l, hl, hx⟩ => by
    rw [hx, show l * (y : G) * l⁻¹ * (y : G)⁻¹ = l * ((y : G) * l⁻¹ * (y : G)⁻¹) by group]
    exact L.mul_mem hl (hyl l hl)
  have hJ₀O : J₀ ≤ oddGen X := (Subgroup.closure_le _).mpr fun x ⟨l, hl, hx⟩ => by
    have hlX : l ∈ X := le_pSpan hL hl
    have hc : l * (y : G) * l⁻¹ ∈ oddGen X := by
      refine mem_oddGen (X.mul_mem (X.mul_mem hlX y.2) (X.inv_mem hlX)) ?_
      have h1 := orderOf_injective (MulAut.conj l).toMonoidHom (MulAut.conj l).injective y
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      rw [h1]
      exact hyo
    rw [hx]
    exact Subgroup.mul_mem _ hc (mem_oddGen (X.inv_mem y.2) (by rw [orderOf_inv]; exact hyo))
  refine le_trans ?_ hJ₀O
  intro l hl
  have hφl : I.φ ⟨l, le_pSpan hL hl⟩ ∈ AE.memBar α h b := by
    rw [← hlab]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hcl : Subgroup.closure {x | ∃ k ∈ AE.memBar α h b, x = k * yb * k⁻¹ * yb⁻¹} ≤
      (J₀.subgroupOf X).map I.φ := by
    refine (Subgroup.closure_le _).mpr fun x ⟨k, hk', hx⟩ => ?_
    rw [← hlab] at hk'
    obtain ⟨⟨l', hl'X⟩, hl', rfl⟩ := hk'
    refine ⟨⟨l', hl'X⟩ * y * ⟨l', hl'X⟩⁻¹ * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨l', Subgroup.mem_subgroupOf.mp hl', by simp⟩
    · rw [hx, map_mul, map_mul, map_mul, map_inv, map_inv, hyφ']
  obtain ⟨⟨j, hjX⟩, hj, hje⟩ := hcl (hybcl hφl)
  have hjJ₀ : j ∈ J₀ := Subgroup.mem_subgroupOf.mp hj
  have hjl : j = l := phi_injOn I.φ hn hL (h8 L (hPΔ hL)) hlab (hJ₀L hjJ₀) hl hje
  rw [← hjl]
  exact hjJ₀

omit [Finite G] in
include hk in
theorem eq_of_map_eq_of_ident (hodd : pSpan P ≤ oddGen (pSpan P)) {N : Subgroup G}
    (hNX : N ≤ pSpan P) (hmap : (N.subgroupOf (pSpan P)).map I.φ = M) : N = pSpan P := by
  refine le_antisymm hNX (hodd.trans ((Subgroup.closure_le _).mpr ?_))
  rintro g ⟨hgX, hgo⟩
  have hφg : I.φ ⟨g, hgX⟩ ∈ (N.subgroupOf (pSpan P)).map I.φ := by
    have h1 : I.φ ⟨g, hgX⟩ ∈ I.φ.range := ⟨_, rfl⟩
    rw [I.range_eq] at h1
    exact hmap.ge h1
  obtain ⟨⟨m, hmX⟩, hm, hme⟩ := hφg
  set c : ↥(pSpan P) := ⟨m, hmX⟩⁻¹ * ⟨g, hgX⟩ with hc
  have hcker : c ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_inv, hme, inv_mul_cancel]
  obtain ⟨j, hj⟩ := hk ⟨c, hcker⟩
  have hcj : c ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hgc : (⟨g, hgX⟩ : ↥(pSpan P)) = ⟨m, hmX⟩ * c := by rw [hc]; group
  have hcomm : Commute (⟨m, hmX⟩ : ↥(pSpan P)) c :=
    Subgroup.mem_center_iff.mp (I.ker_le hcker) ⟨m, hmX⟩
  have hpow : (⟨g, hgX⟩ : ↥(pSpan P)) ^ 2 ^ j = ⟨m, hmX⟩ ^ 2 ^ j := by
    rw [hgc, hcomm.mul_pow, hcj, mul_one]
  have hgN : g ^ 2 ^ j ∈ N := by
    have := congrArg Subtype.val hpow
    simp only [Subgroup.coe_pow] at this
    rw [this]
    exact N.pow_mem (Subgroup.mem_subgroupOf.mp hm) _
  exact mem_of_pow_two_mem hgo hgN

include hΩ h2 h8 hPΔ hinv hn hk in
theorem D1Pack.of_ident (hMn : ModelNormal M) (hMp : ModelPerfect M) (hM3 : ModelThree 𝒜 M)
    (hPne : P.Nonempty) : D1Pack (pSpan P) := by
  set X := pSpan P with hX
  have hodd : X ≤ oddGen X :=
    pSpan_le fun L hL => le_oddGen_of_ident hΩ h2 h8 hPΔ hinv hn I hk hM3 hL
  have hrange : M ≤ I.φ.range := I.range_eq.ge
  refine ⟨fun N hNX hNn => ?_, ?_, hodd, ?_⟩
  · have hle : (N.subgroupOf X).map I.φ ≤ M :=
      (Subgroup.map_le_range _ _).trans I.range_eq.le
    have hnorm : ∀ m ∈ M, ∀ t ∈ (N.subgroupOf X).map I.φ,
        m * t * m⁻¹ ∈ (N.subgroupOf X).map I.φ := by
      rintro m hm _ ⟨t, ht, rfl⟩
      obtain ⟨x, rfl⟩ := hrange hm
      refine ⟨x * t * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp only [map_mul, map_inv]⟩
      simpa using hNn x x.2 t (Subgroup.mem_subgroupOf.mp ht)
    rcases hMn _ hle hnorm with h2' | heq
    · left
      have h1 : IsPGroup 2 (((N.subgroupOf X).map I.φ).comap I.φ) :=
        h2'.comap_of_ker_isPGroup I.φ hk
      exact (h1.to_le (Subgroup.le_comap_map _ _)).of_equiv (Subgroup.subgroupOfEquivOfLe hNX)
    · exact Or.inr (eq_of_map_eq_of_ident I hk hodd hNX heq)
  · have hcX : ⁅X, X⁆ ≤ X := Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
    refine eq_of_map_eq_of_ident I hk hodd hcX (le_antisymm ?_ ?_)
    · exact (Subgroup.map_le_range _ _).trans I.range_eq.le
    · refine hMp.ge.trans (Subgroup.commutator_le.mpr fun m₁ hm₁ m₂ hm₂ => ?_)
      obtain ⟨x₁, rfl⟩ := hrange hm₁
      obtain ⟨x₂, rfl⟩ := hrange hm₂
      refine ⟨⁅x₁, x₂⁆, Subgroup.mem_subgroupOf.mpr ?_, map_commutatorElement I.φ x₁ x₂⟩
      have := Subgroup.commutator_mem_commutator x₁.2 x₂.2
      simpa [commutatorElement_def] using this
  · intro h2X
    obtain ⟨L, hL⟩ := hPne
    obtain ⟨⟨u, hu⟩, -⟩ := hΩ.omega1 L (hPΔ hL)
    have hbot : oddGen X ≤ ⊥ := (Subgroup.closure_le _).mpr fun g ⟨hgX, hgo⟩ => by
      obtain ⟨j, hj⟩ := h2X ⟨g, hgX⟩
      have hj' : g ^ 2 ^ j = 1 := by
        have := congrArg Subtype.val hj
        simpa using this
      exact eq_one_of_odd_of_pow_two hgo hj'
    exact hu.ne_one (Subgroup.mem_bot.mp (hbot (hodd (le_pSpan hL hu.mem))))

end Ident

end CFSG.ClassicalInvolution.Q3.TL4
