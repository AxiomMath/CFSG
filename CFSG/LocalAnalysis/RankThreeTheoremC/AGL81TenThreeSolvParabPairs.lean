module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreeBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroProductSolv
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Small
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymSub

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.SolvParab

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

@[expose] def SymThreePairs (Γ : Type) [Group Γ] : Prop :=
  ∀ T₁ T₂ : Subgroup Γ, IsSubnormal T₁ ⊤ → IsSubnormal T₂ ⊤ →
    Nonempty (↥T₁ ≃* Equiv.Perm (Fin 3)) → Nonempty (↥T₂ ≃* Equiv.Perm (Fin 3)) →
      T₁ = T₂ ∨ ⁅T₁, T₂⁆ = ⊥

private theorem injective_of_ker_le_center {Λ Γ : Type} [Group Λ] [Group Γ] (ψ : Λ →* Γ)
    (hc : ψ.ker ≤ center Λ) {T : Subgroup Λ} (e : ↥T ≃* Equiv.Perm (Fin 3)) :
    Function.Injective (ψ.comp T.subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : (x : Λ) ∈ center Λ := hc (MonoidHom.mem_ker.mpr hx)
  have h : ∀ y : Equiv.Perm (Fin 3), e x * y = y * e x := by
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_center_iff.mp hxc (z : Λ)).symm
  exact (MulEquiv.map_eq_one_iff e).mp (CFSG.perm_eq_one_of_forall_commute (by simp) h)

theorem nonempty_map_mulEquiv {Λ Γ : Type} [Group Λ] [Group Γ] {ψ : Λ →* Γ} {T : Subgroup Λ}
    (e : ↥T ≃* Equiv.Perm (Fin 3)) (hinj : Function.Injective (ψ.comp T.subtype)) :
    Nonempty (↥(T.map ψ) ≃* Equiv.Perm (Fin 3)) := by
  have hr : (ψ.comp T.subtype).range = T.map ψ := by
    rw [MonoidHom.range_comp, range_subtype]
  exact ⟨(MulEquiv.subgroupCongr hr.symm).trans ((MonoidHom.ofInjective hinj).symm.trans e)⟩

private theorem eq_of_map_le {Λ Γ : Type} [Group Λ] [Group Γ] [Finite Λ] (ψ : Λ →* Γ)
    (hc : ψ.ker ≤ center Λ) (ho : Odd (Nat.card ψ.ker)) {T₁ T₂ : Subgroup Λ}
    (h₁ : IsSubnormal T₁ ⊤) (e₁ : ↥T₁ ≃* Equiv.Perm (Fin 3)) (e₂ : ↥T₂ ≃* Equiv.Perm (Fin 3))
    (h : T₁.map ψ ≤ T₂.map ψ) : T₁ = T₂ := by
  obtain ⟨-, -, -, -, -, ⟨s, hsT, hs2, hs1⟩, -⟩ := Sym.symThree_data ⟨e₁⟩
  obtain ⟨y, hy, hys⟩ := h (mem_map_of_mem ψ hsT)
  set k := y⁻¹ * s with hk
  have hkker : k ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hk, map_mul, map_inv, hys, inv_mul_cancel]
  have hkc : ∀ g : Λ, g * k = k * g := mem_center_iff.mp (hc hkker)
  have hsyk : s = y * k := by rw [hk, mul_inv_cancel_left]
  have hyk : y ^ 2 * k ^ 2 = 1 := by
    have e2 : (y * k) ^ 2 = y ^ 2 * k ^ 2 := by
      calc (y * k) ^ 2 = y * (k * y) * k := by rw [sq]; group
        _ = y * (y * k) * k := by rw [hkc y]
        _ = y ^ 2 * k ^ 2 := by rw [sq, sq]; group
    rw [← e2, ← hsyk, hs2]
  have hk2T : k ^ 2 ∈ T₂ := by
    rw [eq_inv_of_mul_eq_one_right hyk]
    exact T₂.inv_mem (T₂.pow_mem hy 2)
  have hk2 : k ^ 2 = 1 := by
    have h1 : (ψ.comp T₂.subtype) ⟨k ^ 2, hk2T⟩ = (ψ.comp T₂.subtype) 1 := by
      rw [map_one, MonoidHom.comp_apply, Subgroup.coe_subtype, map_pow,
        MonoidHom.mem_ker.mp hkker, one_pow]
    simpa using congrArg Subtype.val (injective_of_ker_le_center ψ hc e₂ h1)
  have hkn : k ^ Nat.card ψ.ker = 1 := by
    simpa using congrArg Subtype.val (pow_card_eq_one' (G := ψ.ker) (x := ⟨k, hkker⟩))
  have hk1 : k = 1 := CFSG.AGLEmbedding.SymThreeCentralExt.eq_one_of_sq_of_pow_odd ho hkn hk2
  have hsT₂ : s ∈ T₂ := by
    rw [hsyk, hk1, mul_one]
    exact hy
  exact Sym.eq_of_shared_involution ⟨e₁⟩ ⟨e₂⟩ h₁ hsT hsT₂ hs2 hs1

private theorem exists_lift {Λ Γ : Type} [Group Λ] [Group Γ] [Finite Λ] (ψ : Λ →* Γ)
    (hψ : Function.Surjective ψ) (hc : ψ.ker ≤ center Λ) (ho : Odd (Nat.card ψ.ker))
    {T : Subgroup Γ} (hT : IsSubnormal T ⊤) (e : ↥T ≃* Equiv.Perm (Fin 3)) :
    ∃ T' : Subgroup Λ, IsSubnormal T' ⊤ ∧ Nonempty (↥T' ≃* Equiv.Perm (Fin 3)) ∧
      T'.map ψ = T := by
  set C : Subgroup Λ := T.comap ψ with hC
  set f : ↥C →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (ψ.subgroupComap T) with hf
  have hfs : Function.Surjective f :=
    e.surjective.comp (ψ.subgroupComap_surjective_of_surjective T hψ)
  have hfker : ∀ x : ↥C, x ∈ f.ker ↔ (x : Λ) ∈ ψ.ker := by
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hf, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, ← Subtype.val_inj]
    rfl
  have hc' : ∀ k ∈ f.ker, ∀ q : ↥C, k * q = q * k := fun k hk q =>
    Subtype.ext (mem_center_iff.mp (hc ((hfker k).mp hk)) q).symm
  have hkerC : ψ.ker ≤ C := fun x hx => by
    rw [hC, mem_comap, MonoidHom.mem_ker.mp hx]
    exact one_mem T
  have hfk : f.ker = ψ.ker.subgroupOf C := by
    ext x
    rw [hfker, mem_subgroupOf]
  have ho' : Odd (Nat.card f.ker) := by
    rw [hfk, Nat.card_congr (subgroupOfEquivOfLe hkerC).toEquiv]
    exact ho
  obtain ⟨T₀, hT₀n, ⟨e₀⟩, -⟩ :=
    CFSG.AGLEmbedding.SymThreeCentralExt.exists_normal_symThree f hfs hc' ho'
  set T' : Subgroup Λ := T₀.map C.subtype with hT'
  have e' : ↥T' ≃* Equiv.Perm (Fin 3) :=
    (T₀.equivMapOfInjective C.subtype C.subtype_injective).symm.trans e₀
  refine ⟨T', ?_, ⟨e'⟩, ?_⟩
  · have hCs : IsSubnormal C ⊤ := by
      have h := hT.comap ψ
      rwa [comap_top] at h
    refine IsSubnormal.step (map_subtype_le T₀) ?_ hCs
    rw [hT', show (T₀.map C.subtype).subgroupOf C = T₀ from
      comap_map_eq_self_of_injective C.subtype_injective T₀]
    exact hT₀n
  · have hle : T'.map ψ ≤ T := by
      rintro _ ⟨x, ⟨y, -, rfl⟩, rfl⟩
      exact y.2
    have hinj := injective_of_ker_le_center ψ hc e'
    have hcard : Nat.card ↥(T'.map ψ) = Nat.card ↥T' := by
      have hr : (ψ.comp T'.subtype).range = T'.map ψ := by
        rw [MonoidHom.range_comp, range_subtype]
      rw [← hr]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    haveI : Finite ↥T := Finite.of_equiv _ e.symm.toEquiv
    refine eq_of_le_of_card_ge hle ?_
    rw [hcard, SymThree.card_eq_six_of_mulEquiv e', SymThree.card_eq_six_of_mulEquiv e]

theorem SymThreePairs.of_surjective {Λ Γ : Type} [Group Λ] [Group Γ] [Finite Λ] (ψ : Λ →* Γ)
    (hψ : Function.Surjective ψ) (hc : ψ.ker ≤ center Λ) (ho : Odd (Nat.card ψ.ker))
    (h : SymThreePairs Λ) : SymThreePairs Γ := by
  intro T₁ T₂ h₁ h₂ ⟨e₁⟩ ⟨e₂⟩
  obtain ⟨S₁, hS₁, hb₁, hm₁⟩ := exists_lift ψ hψ hc ho h₁ e₁
  obtain ⟨S₂, hS₂, hb₂, hm₂⟩ := exists_lift ψ hψ hc ho h₂ e₂
  rcases h S₁ S₂ hS₁ hS₂ hb₁ hb₂ with heq | hcomm
  · left
    rw [← hm₁, ← hm₂, heq]
  · right
    rw [← hm₁, ← hm₂, ← map_commutator, hcomm, Subgroup.map_bot]

theorem SymThreePairs.of_mulEquiv {Λ Γ : Type} [Group Λ] [Group Γ] [Finite Λ] (e : Λ ≃* Γ)
    (h : SymThreePairs Λ) : SymThreePairs Γ := by
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  refine h.of_surjective e.toMonoidHom e.surjective (by rw [hker]; exact bot_le) ?_
  rw [hker, card_bot]
  exact odd_one

theorem SymThreePairs.of_le {Γ : Type} [Group Γ] (H : Subgroup Γ)
    (hH : ∀ T : Subgroup Γ, IsSubnormal T ⊤ → Nonempty (↥T ≃* Equiv.Perm (Fin 3)) → T ≤ H)
    (h : SymThreePairs ↥H) : SymThreePairs Γ := by
  intro T₁ T₂ h₁ h₂ hb₁ hb₂
  have hsub : ∀ {T : Subgroup Γ}, IsSubnormal T ⊤ → T ≤ H → IsSubnormal (T.subgroupOf H) ⊤ := by
    intro T hT hTH
    have h1 := hT.inf_of_le (le_top : H ≤ ⊤)
    rw [inf_eq_left.mpr hTH] at h1
    exact IsSubnormal.of_mathlib ((Open.IsSubnormal.iff_subgroupOf hTH).mp h1)
  have hiso : ∀ {T : Subgroup Γ}, T ≤ H → Nonempty (↥T ≃* Equiv.Perm (Fin 3)) →
      Nonempty (↥(T.subgroupOf H) ≃* Equiv.Perm (Fin 3)) :=
    fun hTH ⟨e⟩ => ⟨(subgroupOfEquivOfLe hTH).trans e⟩
  have hmap : ∀ {T : Subgroup Γ}, T ≤ H → (T.subgroupOf H).map H.subtype = T :=
    fun hTH => by rw [subgroupOf_map_subtype, inf_eq_left.mpr hTH]
  have hle₁ := hH T₁ h₁ hb₁
  have hle₂ := hH T₂ h₂ hb₂
  rcases h _ _ (hsub h₁ hle₁) (hsub h₂ hle₂) (hiso hle₁ hb₁) (hiso hle₂ hb₂) with heq | hcomm
  · left
    rw [← hmap hle₁, ← hmap hle₂, heq]
  · right
    rw [← hmap hle₁, ← hmap hle₂, ← map_commutator, hcomm, Subgroup.map_bot]

theorem SymThreePairs.of_odd {Γ : Type} [Group Γ] (h : ¬ 2 ∣ Nat.card Γ) : SymThreePairs Γ := by
  rintro T₁ - - - ⟨e₁⟩ -
  exfalso
  apply h
  have h6 : 2 ∣ Nat.card T₁ := by
    rw [SymThree.card_eq_six_of_mulEquiv e₁]
    norm_num
  exact h6.trans (card_subgroup_dvd_card T₁)

theorem SymThreePairs.of_eq_top {Γ : Type} [Group Γ]
    (h : ∀ T : Subgroup Γ, IsSubnormal T ⊤ → Nonempty (↥T ≃* Equiv.Perm (Fin 3)) → T = ⊤) :
    SymThreePairs Γ :=
  fun T₁ T₂ h₁ h₂ hb₁ hb₂ => Or.inl ((h T₁ h₁ hb₁).trans (h T₂ h₂ hb₂).symm)

theorem symThreePairs_pi {ι : Type} [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    (h : ∀ X : Subgroup (∀ i, G i), IsSubnormal X ⊤ → Nonempty (↥X ≃* Equiv.Perm (Fin 3)) →
      ∃ i, X = (⊤ : Subgroup (G i)).map (MonoidHom.mulSingle G i)) :
    SymThreePairs (∀ i, G i) := by
  intro T₁ T₂ h₁ h₂ hb₁ hb₂
  obtain ⟨i, hi⟩ := h T₁ h₁ hb₁
  obtain ⟨j, hj⟩ := h T₂ h₂ hb₂
  by_cases hij : i = j
  · subst hij
    exact Or.inl (hi.trans hj.symm)
  · right
    rw [commutator_eq_bot_iff_le_centralizer, hi, hj]
    rintro _ ⟨x, -, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, -, rfl⟩
    exact (Pi.mulSingle_commute hij x y).eq.symm

theorem symThreePairs_of_card_dvd {J : Type} [Group J] [Finite J] {Z : Subgroup J} [Z.Normal]
    (hZ : Z ≤ center J) (hZo : Odd (Nat.card Z)) (h96 : Nat.card (J ⧸ Z) ∣ 96) :
    SymThreePairs (J ⧸ CFSG.pCore 2 J) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := J ⧸ CFSG.pCore 2 J
  set π : J →* R := QuotientGroup.mk' (CFSG.pCore 2 J) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Zb : Subgroup R := Z.map π with hZb
  haveI hZbn : Zb.Normal := Subgroup.Normal.map inferInstance π hπs
  have hZbc : Zb ≤ center R := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := hπs g
    rw [← map_mul, ← map_mul, mem_center_iff.mp (hZ hz) x]
  have hZbo : Odd (Nat.card Zb) := hZo.of_dvd_nat (card_map_dvd Z π)
  set ρ : R →* R ⧸ Zb := QuotientGroup.mk' Zb with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hρker : ρ.ker = Zb := QuotientGroup.ker_mk' Zb
  have hO : CFSG.pCore 2 R = ⊥ := CZeroProduct.pCore_quotient_pCore_eq_bot 2
  have hO' : CFSG.pCore 2 (R ⧸ Zb) = ⊥ := by
    set M : Subgroup R := (CFSG.pCore 2 (R ⧸ Zb)).comap ρ with hM
    have hMn : M.Normal := CFSG.pCore_normal.comap ρ
    have hZM : Zb ≤ M := by
      intro z hz
      rw [hM, mem_comap, show ρ z = 1 from by rw [← MonoidHom.mem_ker, hρker]; exact hz]
      exact one_mem _
    haveI : (Zb.subgroupOf M).Normal := hZbn.subgroupOf M
    have hq : IsPGroup 2 (↥M ⧸ Zb.subgroupOf M) :=
      ParabCensus.isPGroup_quotient_subgroupOf_comap hρs hρker.symm CFSG.pCore_isPGroup
    have hle := ParabCensus.le_sup_pCore_two_of_central_odd_quotient_two hMn hZM hZbc hZbo hq
    rw [hO, sup_bot_eq] at hle
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hρs x
    have hy : y ∈ Zb := hle hx
    rw [mem_bot, ← MonoidHom.mem_ker, hρker]
    exact hy
  have hcard : Nat.card (R ⧸ Zb) ∣ 96 := by
    set χ : J →* R ⧸ Zb := ρ.comp π with hχ
    have hχs : Function.Surjective χ := hρs.comp hπs
    have hZχ : Z ≤ χ.ker := by
      intro z hz
      rw [MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hρker]
      exact mem_map_of_mem π hz
    have h1 : Nat.card (R ⧸ Zb) = χ.ker.index := by
      rw [index_eq_card]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective χ hχs).toEquiv).symm
    rw [h1]
    exact (index_dvd_of_le hZχ).trans (by rwa [index_eq_card])
  have hO3 : Nat.card (CFSG.pCore 3 (R ⧸ Zb)) ∣ 3 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 3) (G := R ⧸ Zb))
    have hdvd : 3 ^ n ∣ 96 := hn ▸ (card_subgroup_dvd_card _).trans hcard
    have hn1 : n ≤ 1 := by
      by_contra hn2
      have h9 : 3 ^ 2 ∣ 96 := (pow_dvd_pow 3 (by omega)).trans hdvd
      norm_num at h9
    rw [hn]
    exact (pow_dvd_pow 3 hn1).trans (by norm_num)
  have hρc : ρ.ker ≤ center R := by rw [hρker]; exact hZbc
  have hρo : Odd (Nat.card ρ.ker) := by rw [hρker]; exact hZbo
  have himg : ∀ {T : Subgroup R}, IsSubnormal T ⊤ → (↥T ≃* Equiv.Perm (Fin 3)) →
      IsSubnormal (T.map ρ) ⊤ ∧ Nonempty (↥(T.map ρ) ≃* Equiv.Perm (Fin 3)) := by
    intro T hT e
    refine ⟨?_, nonempty_map_mulEquiv e (injective_of_ker_le_center ρ hρc e)⟩
    have h := hT.map ρ
    rwa [map_top_of_surjective ρ hρs] at h
  intro T₁ T₂ h₁ h₂ ⟨e₁⟩ ⟨e₂⟩
  left
  obtain ⟨hs₁, ⟨f₁⟩⟩ := himg h₁ e₁
  obtain ⟨hs₂, ⟨f₂⟩⟩ := himg h₂ e₂
  obtain ⟨a, ha, ha1, ha3, -, -, -⟩ := Sym.symThree_data ⟨f₁⟩
  obtain ⟨b, hb, hb1, hb3, -, -, -⟩ := Sym.symThree_data ⟨f₂⟩
  have haO := Sym.mem_pCore_three ⟨f₁⟩ hs₁ ha ha3 ha1
  have hbO := Sym.mem_pCore_three ⟨f₂⟩ hs₂ hb hb3 hb1
  have hza : zpowers a = CFSG.pCore 3 (R ⧸ Zb) := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr haO) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
    exact Nat.le_of_dvd (by norm_num) hO3
  have hbT : b ∈ T₁.map ρ := (zpowers_le.mpr ha) (hza ▸ hbO)
  have hU : T₁.map ρ = T₂.map ρ :=
    Sym.eq_of_shared_three (Sym.eq_bot_of_subnormal_isPGroup_two hO') ⟨f₁⟩ ⟨f₂⟩ hs₁ hs₂ hbT hb
      hb3 hb1
  exact eq_of_map_le ρ hρc hρo h₁ e₁ e₂ hU.le

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.SolvParab
