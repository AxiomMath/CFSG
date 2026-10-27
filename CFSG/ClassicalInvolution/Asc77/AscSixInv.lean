module

public import CFSG.ClassicalInvolution.Asc77.HypOmegaBasic
public import CFSG.ClassicalInvolution.Asc77.WP1Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem exists_fixed_conjSub {H : Subgroup G} (hH : IsPGroup 2 H) {𝔛 : Set (Subgroup G)}
    (hinv : ∀ h ∈ H, ∀ X ∈ 𝔛, conjSub h X ∈ 𝔛) (hodd : ¬ 2 ∣ Nat.card ↥𝔛) :
    ∃ X ∈ 𝔛, ∀ h ∈ H, conjSub h X = X := by
  let inst : MulAction ↥H ↥𝔛 :=
    { smul := fun h X => ⟨conjSub (h : G) X.1, hinv h h.2 X.1 X.2⟩
      one_smul := fun X => Subtype.ext (conjSub_one X.1)
      mul_smul := fun h h' X => Subtype.ext (conjSub_mul (h : G) (h' : G) X.1) }
  obtain ⟨⟨X, hX⟩, hfix⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card (↥𝔛) hodd
  refine ⟨X, hX, fun h hh => ?_⟩
  exact congrArg Subtype.val (hfix ⟨h, hh⟩)

theorem IsSylow2In.conj {V P : Subgroup G} (h : IsSylow2In V P) (g : G) :
    IsSylow2In (conjSub g V) (conjSub g P) := by
  refine ⟨conjSub_mono h.1, isPGroup_conjSub g h.2.1, fun V' hV'P hV'2 hle => ?_⟩
  have h1 : conjSub g⁻¹ V' ≤ P := by
    have := conjSub_mono (n := g⁻¹) hV'P
    rwa [conjSub_inv_conjSub] at this
  have h2 : V ≤ conjSub g⁻¹ V' := (conjSub_le_iff g).mp hle
  have h3 := h.2.2 _ h1 (isPGroup_conjSub g⁻¹ hV'2) h2
  calc V' = conjSub g (conjSub g⁻¹ V') := (conjSub_conjSub_inv g V').symm
    _ = conjSub g V := by rw [h3]

theorem exists_invariant_cyclic_order_four [Finite G] {P T : Subgroup G} (hP : IsPGroup 2 P)
    (hTP : T ≤ P) (hTn : ∀ p ∈ P, conjSub p T = T) {z : G} (hz : IsUniqueInvolution T z)
    (h4 : 4 ≤ Nat.card T) :
    ∃ A ≤ T, IsCyclic ↥A ∧ Nat.card A = 4 ∧ ∀ p ∈ P, conjSub p A = A := by
  classical
  have hz2 : z * z = 1 := hz.sq
  have hzc : ∀ p ∈ P, p * z * p⁻¹ = z := fun p hp => hz.conj_eq (hTn p hp)
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz.ne_one
  have hzP : z ∈ P := hTP hz.mem
  set zP : ↥P := ⟨z, hzP⟩ with hzPdef
  have hzPord : orderOf zP = 2 := by rw [hzPdef, Subgroup.orderOf_mk]; exact hzord
  have hzPc : zP ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : G) * z = z * (g : G)
    have := hzc g g.2
    calc (g : G) * z = (g * z * (g : G)⁻¹) * g := by group
      _ = z * g := by rw [this]
  set Z : Subgroup ↥P := Subgroup.zpowers zP with hZ
  have hZn : Z.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzPc)
  have hZcard : Nat.card Z = 2 := by rw [hZ, Nat.card_zpowers, hzPord]
  set T' : Subgroup ↥P := T.subgroupOf P with hT'
  have hT'n : T'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hT', Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * n * (g : G)⁻¹ ∈ conjSub (g : G) T := conj_mem_conjSub hn
    rw [hTn g g.2] at h1
    exact h1
  have hT'card : Nat.card T' = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv
  have hPP : IsPGroup 2 ↥P := hP
  have hQ2 : IsPGroup 2 (↥P ⧸ Z) := hPP.to_quotient Z
  have hnil : Group.IsNilpotent (↥P ⧸ Z) := hQ2.isNilpotent
  set Tb : Subgroup (↥P ⧸ Z) := T'.map (QuotientGroup.mk' Z) with hTb
  have hTbn : Tb.Normal := Subgroup.Normal.map hT'n _ (QuotientGroup.mk'_surjective Z)
  have hTbne : Tb ≠ ⊥ := by
    intro hbot
    have hle : T' ≤ Z := by
      intro t ht
      have : QuotientGroup.mk' Z t ∈ Tb := ⟨t, ht, rfl⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have := Subgroup.card_le_of_le hle
    omega
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hTbne
  set S₀ : Subgroup (↥P ⧸ Z) := Tb ⊓ Subgroup.center (↥P ⧸ Z) with hS₀
  have hS₀2 : IsPGroup 2 ↥S₀ := hQ2.to_subgroup S₀
  have hS₀card : 2 ∣ Nat.card ↥S₀ := by
    rcases hS₀2.card_eq_or_dvd with h1 | h1
    · exfalso
      apply hne
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have h2 : (⟨x, hx⟩ : ↥S₀) = 1 := (Nat.card_eq_one_iff_unique.mp h1).1.elim _ _
      exact congrArg Subtype.val h2
    · exact h1
  obtain ⟨xh, hxh⟩ := exists_prime_orderOf_dvd_card' 2 hS₀card
  set xb : ↥P ⧸ Z := (xh : ↥P ⧸ Z) with hxb
  have hxbord : orderOf xb = 2 := by rw [hxb, Subgroup.orderOf_coe]; exact hxh
  have hxbT : xb ∈ Tb := (xh.2).1
  have hxbc : xb ∈ Subgroup.center (↥P ⧸ Z) := (xh.2).2
  obtain ⟨x', hx'T', hx'⟩ := hxbT
  have hxbne : xb ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxbord
    omega
  have hxbsq : xb * xb = 1 := by
    have := pow_orderOf_eq_one xb
    rwa [hxbord, pow_two] at this
  have hx'q : (QuotientGroup.mk x' : ↥P ⧸ Z) = xb := hx'
  obtain ⟨x, hxdef⟩ : ∃ x : G, x = ((x' : ↥P) : G) := ⟨_, rfl⟩
  have hxT : x ∈ T := hxdef ▸ Subgroup.mem_subgroupOf.mp hx'T'
  have hzP2 : zP * zP = 1 := by
    have := pow_orderOf_eq_one zP
    rwa [hzPord, pow_two] at this
  have hZsq : ∀ y ∈ Z, y * y = 1 := by
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hzP2, one_zpow]
  have hxsq1 : (x * x) * (x * x) = 1 := by
    rw [hxdef]
    have hmem : x' * x' ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hx'q, hxbsq]
    have := hZsq _ hmem
    exact congrArg Subtype.val this
  have hx1 : x ≠ 1 := by
    intro h
    apply hxbne
    rw [← hx'q]
    have : x' = 1 := Subtype.ext (hxdef ▸ h)
    rw [this]
    rfl
  have hxz : x ≠ z := by
    intro h
    apply hxbne
    rw [← hx'q]
    have : x' = zP := Subtype.ext (hxdef ▸ h)
    have hmem : x' ∈ Z := this ▸ Subgroup.mem_zpowers zP
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  have hxx : x * x = z := by
    rcases hz.unique (x * x) (T.mul_mem hxT hxT) hxsq1 with h | h
    · exfalso
      rcases hz.unique x hxT h with h' | h'
      · exact hx1 h'
      · exact hxz h'
    · exact h
  have hxord : orderOf x = 4 := by
    have h4' : x ^ 2 ^ (1 + 1) = 1 := by
      have : x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [show 2 ^ (1 + 1) = 4 by norm_num, this, hxsq1]
    have h2' : ¬ x ^ 2 ^ 1 = 1 := by
      intro h
      have : x * x = 1 := by rw [pow_one, pow_two] at h; exact h
      rw [hxx] at this
      exact hz.ne_one this
    have := orderOf_eq_prime_pow h2' h4'
    rwa [show 2 ^ (1 + 1) = 4 by norm_num] at this
  have hxzmem : x * z ∈ Subgroup.zpowers x := by
    have : x * z = x ^ 3 := by rw [← hxx]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 3
  have hcomm : ∀ p ∈ P, p⁻¹ * x * p ∈ Subgroup.zpowers x := by
    intro p hp
    have hcen := Subgroup.mem_center_iff.mp hxbc (QuotientGroup.mk ⟨p, hp⟩)
    have h1 : (QuotientGroup.mk (⟨p, hp⟩ : ↥P) : ↥P ⧸ Z) * (QuotientGroup.mk x' : ↥P ⧸ Z) =
        (QuotientGroup.mk x' : ↥P ⧸ Z) * (QuotientGroup.mk (⟨p, hp⟩ : ↥P) : ↥P ⧸ Z) := by
      rw [hx'q]
      exact hcen
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    have h3 : (x⁻¹ * p⁻¹ * x * p) * (x⁻¹ * p⁻¹ * x * p) = 1 := by
      have := congrArg Subtype.val (hZsq _ h1)
      simpa [hxdef, mul_assoc] using this
    have h4 : x⁻¹ * p⁻¹ * x * p ∈ T := by
      have hpxp : p⁻¹ * x * p ∈ T := by
        have h5 : p⁻¹ * x * (p⁻¹)⁻¹ ∈ conjSub p⁻¹ T := conj_mem_conjSub hxT
        rw [hTn p⁻¹ (P.inv_mem hp)] at h5
        simpa using h5
      have := T.mul_mem (T.inv_mem hxT) hpxp
      simpa [mul_assoc] using this
    rcases hz.unique _ h4 h3 with h6 | h6
    · have : p⁻¹ * x * p = x := by
        have : x * (x⁻¹ * p⁻¹ * x * p) = x * 1 := by rw [h6]
        simpa [mul_assoc] using this
      rw [this]
      exact Subgroup.mem_zpowers x
    · have : p⁻¹ * x * p = x * z := by
        have : x * (x⁻¹ * p⁻¹ * x * p) = x * z := by rw [h6]
        simpa [mul_assoc] using this
      rw [this]
      exact hxzmem
  refine ⟨Subgroup.zpowers x, Subgroup.zpowers_le.mpr hxT, inferInstance, ?_, fun p hp => ?_⟩
  · rw [Nat.card_zpowers, hxord]
  · have hfwd : ∀ q ∈ P, ∀ w ∈ Subgroup.zpowers x, q⁻¹ * w * q ∈ Subgroup.zpowers x := by
      intro q hq w hw
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have : q⁻¹ * x ^ m * q = (q⁻¹ * x * q) ^ m := by
        have h1 : q⁻¹ * x * q = (MulAut.conj q⁻¹) x := by simp
        have h2 : q⁻¹ * x ^ m * q = (MulAut.conj q⁻¹) (x ^ m) := by simp
        rw [h1, h2, map_zpow]
      rw [this]
      exact Subgroup.zpow_mem _ (hcomm q hq) _
    ext y
    rw [mem_conjSub_iff]
    constructor
    · intro hy
      have h2 := hfwd p⁻¹ (P.inv_mem hp) _ hy
      have : p⁻¹⁻¹ * (p⁻¹ * y * p) * p⁻¹ = y := by group
      rwa [this] at h2
    · intro hy
      exact hfwd p hp y hy

end CFSG.ClassicalInvolution.Asc77
