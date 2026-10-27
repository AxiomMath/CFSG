module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTLinkA
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Lift
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrPerf
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Stmt
public import CFSG.GH74.GLS.Stage2.Local.P27.QIdArith
public import CFSG.Sporadic.SmallOddCore.McLLocal
public import CFSG.Sporadic.Schreier.LyOuter

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem not_isL2_of_card_btw {Z : Type} [Group Z] {N a : ℕ} (hZ : Nat.card Z = N)
    (h1 : a * (a ^ 2 - 1) / 2 < N) (h2 : N < (a + 1) * ((a + 1) ^ 2 - 1) / 2) :
    ¬ IVK.IsL2 Z (fun r => Odd r ∧ 5 ≤ r) := by
  rintro ⟨F, _, _, ⟨hr, -⟩, ⟨f⟩⟩
  have hL : IVK.IsL2 Z (fun r => r = Nat.card F) := ⟨F, inferInstance, inferInstance, rfl, ⟨f⟩⟩
  have hc := P27.QId.card_isL2 hr hL
  rw [hZ] at hc
  rcases le_or_gt (Nat.card F) a with h | h
  · have := Nat.div_le_div_right (c := 2)
      (Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1))
    omega
  · have h' : a + 1 ≤ Nat.card F := h
    have := Nat.div_le_div_right (c := 2)
      (Nat.mul_le_mul h' (Nat.sub_le_sub_right (Nat.pow_le_pow_left h' 2) 1))
    omega

theorem not_kindFactorAll_of_card_btw {k : Kind} (hk : IsClassicalKind k) {Z : Type} [Group Z]
    {N : ℕ} (hZ : Nat.card Z = N) (a : ℕ) (h1 : a * (a ^ 2 - 1) / 2 < N)
    (h2 : N < (a + 1) * ((a + 1) ^ 2 - 1) / 2) (h7 : ¬ N ∣ 2520) : ¬ KindFactorAll k Z := by
  have hL := not_isL2_of_card_btw hZ h1 h2
  have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  rcases hk with rfl | ⟨ε, rfl⟩
  · exact hL
  · rintro (h | h)
    · exact hL h
    · exact h7 (hZ ▸ hA7 ▸ h.card_dvd)

theorem false_of_bad_section {k : Kind} {Y : Type} [Group Y] (hinv : InvSecGroup k Y)
    {s : Y} (hs : orderOf s = 2) {G₀ : Type} [Group G₀] [Group.IsPerfect G₀] (ρ : G₀ →* Y)
    (hρ : Function.Injective ρ) (hcomm : ∀ g, s * ρ g = ρ g * s) {Z : Type} [Group Z]
    [IsSimpleGroup Z] (f : G₀ →* Z) (hf : Function.Surjective f)
    (hZ : ∃ a b : Z, a * b ≠ b * a) (hbad : ¬ KindFactorAll k Z) : False := by
  obtain ⟨A, _, _, J, -, ⟨eJ⟩, hall⟩ := hinv
  let ψ : ↥J →* Y := eJ.toMonoidHom.comp (QuotientGroup.mk' (center ↥J))
  have hψ : Function.Surjective ψ := eJ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (QuotientGroup.mk' (center ↥J)) x = 1 := by
      apply eJ.injective
      rw [map_one]
      exact hx
    exact (QuotientGroup.eq_one_iff x).mp h1
  obtain ⟨x, hx2, ⟨U, φ, hφ⟩⟩ := exists_involution_section ψ hψ hker hs ρ hρ hcomm
  exact hbad (hall x hx2 Z (not_isSolvable_of_simple hZ) ⟨U, f.comp φ, hf.comp hφ⟩)

section McL

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier


theorem mcl_bad {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .McL) :
    ∃ (s : Y) (G₀ : Type) (_ : Group G₀) (_ : Group.IsPerfect G₀) (ρ : G₀ →* Y)
      (Z : Type) (_ : Group Z) (_ : IsSimpleGroup Z) (f : G₀ →* Z),
      orderOf s = 2 ∧ Function.Injective ρ ∧ (∀ g, s * ρ g = ρ g * s) ∧
        Function.Surjective f ∧ Nat.card Z = 20160 ∧ ∃ a b : Z, a * b ≠ b * a := by
  obtain ⟨e⟩ := hY
  let E : Y ≃* ↥mclP := e.trans mclPermEquiv
  obtain ⟨hrange, -⟩ := mclRho_range
  obtain ⟨hsimple, hnab⟩ := mclX_simple
  set X := genGroup 35 mclXGens mclXPerm with hX
  have hCP : mclCt ≤ mclP := inf_le_left
  set D : Subgroup ↥mclCt := perfCore ⊤ with hD
  have hDperf : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr (commutator_perfCore _)
  have hmemX : ∀ c : ↥mclCt, mclRho c ∈ X := fun c => hrange ▸ ⟨c, rfl⟩
  let f₀ : ↥mclCt →* ↥X := mclRho.codRestrict X hmemX
  have hf₀ : Function.Surjective f₀ := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨c, rfl⟩ := hy
    exact ⟨c, rfl⟩
  have : IsSimpleGroup ↥X := hsimple
  have hXperf : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = (⊤ : Subgroup ↥X) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆
      with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hc : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ :=
        Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot] at hc
      exact commutatorElement_eq_one_iff_mul_comm.mp hc
    · exact h
  have hDmap : D.map f₀ = ⊤ := by
    have := map_perfCore_comap_of_subnormal f₀ hf₀ ⊤ Subgroup.IsSubnormal.top hXperf
    rwa [Subgroup.comap_top] at this
  refine ⟨E.symm ⟨mclT0, mclT0_facts.1⟩, ↥D, inferInstance, hDperf,
    E.symm.toMonoidHom.comp ((Subgroup.inclusion hCP).comp D.subtype), ↥X, inferInstance,
    hsimple, f₀.comp D.subtype, ?_, ?_, ?_, ?_, card_mclX, hnab⟩
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact mclT0_facts.2.1
  · exact E.symm.injective.comp ((Subgroup.inclusion_injective hCP).comp D.subtype_injective)
  · intro d
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp (mem_inf.mp (d : ↥mclCt).2).2).symm
  · intro y
    have hy : y ∈ D.map f₀ := by rw [hDmap]; exact mem_top y
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨⟨d, hd⟩, rfl⟩

end McL

section Ly


theorem ly_bad {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .Ly) :
    ∃ (s : Y) (G₀ : Type) (_ : Group G₀) (_ : Group.IsPerfect G₀) (ρ : G₀ →* Y)
      (Z : Type) (_ : Group Z) (_ : IsSimpleGroup Z) (f : G₀ →* Z),
      orderOf s = 2 ∧ Function.Injective ρ ∧ (∀ g, s * ρ g = ρ g * s) ∧
        Function.Surjective f ∧ Nat.card Z = 19958400 ∧ ∃ a b : Z, a * b ≠ b * a := by
  obtain ⟨e⟩ := hY
  have hc : Nat.card Y = 51765179004000000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ly.card_Ly
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 (by rw [hc]; norm_num)
  obtain ⟨hq, -, ⟨eA⟩⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ t ht
  refine ⟨t, ↥(centralizer ({t} : Set Y)), inferInstance, hq.1,
    (centralizer ({t} : Set Y)).subtype, _, inferInstance, hq.2.1,
    QuotientGroup.mk' (center ↥(centralizer ({t} : Set Y))), ht,
    (centralizer ({t} : Set Y)).subtype_injective, fun g => ?_,
    QuotientGroup.mk'_surjective _, ?_, hq.2.2⟩
  · exact (mem_centralizer_singleton_iff.mp g.2).symm
  · rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]

end Ly

theorem excl_mcly {k : Kind} (hk : IsClassicalKind k) {Y : Type} [Group Y] (hF : FMcLy Y)
    (hinv : InvSecGroup k Y) : False := by
  rcases hF with hM | hL
  · obtain ⟨s, G₀, _, _, ρ, Z, _, _, f, hs, hρ, hcomm, hf, hcard, hZ⟩ := mcl_bad hM
    exact false_of_bad_section hinv hs ρ hρ hcomm f hf hZ
      (not_kindFactorAll_of_card_btw hk hcard 34 (by norm_num) (by norm_num) (by norm_num))
  · obtain ⟨s, G₀, _, _, ρ, Z, _, _, f, hs, hρ, hcomm, hf, hcard, hZ⟩ := ly_bad hL
    exact false_of_bad_section hinv hs ρ hρ hcomm f hf hZ
      (not_kindFactorAll_of_card_btw hk hcard 341 (by norm_num) (by norm_num) (by norm_num))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
