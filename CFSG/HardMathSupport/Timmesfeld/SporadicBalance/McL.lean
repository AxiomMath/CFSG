module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.Sporadic.Recognition.McLASCert

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.ComponentClassification.OuterAutomorphisms

theorem card_centralizer_eq_card_inf {K M : Type*} [Group K] [Group M] (P : Subgroup M)
    (e : K ≃* P) (y : K) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set K)) =
      Nat.card ↥(P ⊓ Subgroup.centralizer ({((e y : P) : M)} : Set M)) := by
  set f : K →* M := P.subtype.comp e.toMonoidHom with hf
  have hinj : Function.Injective f := P.subtype_injective.comp e.injective
  have hc := map_inf_centralizer_of_injective f hinj ⊤ y
  have hrange : (⊤ : Subgroup K).map f = P := by
    rw [← MonoidHom.range_eq_map, hf, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [top_inf_eq, hrange] at hc
  have hfy : f y = ((e y : P) : M) := rfl
  rw [hfy] at hc
  rw [← hc]
  exact (Subgroup.card_map_of_injective hinj).symm

theorem card_centralizer_involution_McL
    (t : NativeSporadic.McL) (ht : orderOf t = 2) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set NativeSporadic.McL)) = 40320 := by
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ := mcl_involution_centralizers
  have hle : mclP ≤ mclR := (mcl_autModel).le
  obtain ⟨t', ht'def⟩ : ∃ t' : Equiv.Perm (Fin 275),
      t' = ((mclPermEquiv t : mclP) : Equiv.Perm (Fin 275)) := ⟨_, rfl⟩
  have ht'o : orderOf t' = 2 := by
    rw [ht'def, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  have htP : t' ∈ mclP := by rw [ht'def]; exact (mclPermEquiv t).2
  obtain ⟨r, hr, g, hg, hgt⟩ := hcover t' (hle htP) ht'o
  obtain ⟨-, -, hout, -, hcent, -⟩ := hrows r hr
  have hrepP : tp 275 r.rep ∈ mclP := by
    have : tp 275 r.rep = g⁻¹ * t' * g := by rw [hgt]; group
    rw [this]
    exact mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hg) htP) hg
  have houtf : r.outer = false := by
    by_contra h
    exact (hout.1 (by simpa using h)) hrepP
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      [(false, 22275, 40320), (true, 113400, 7920)] := by
    rw [← hmap]
    exact List.mem_map_of_mem hr
  rw [houtf] at hmem
  simp only [List.mem_cons, Prod.mk.injEq, Bool.false_eq_true, false_and, List.not_mem_nil,
    or_false, true_and] at hmem
  obtain ⟨-, hco⟩ := hmem
  have h1 := @card_centralizer_eq_card_inf NativeSporadic.McL (Equiv.Perm (Fin 275))
    inferInstance inferInstance mclP mclPermEquiv t
  rw [← ht'def] at h1
  have h2 : Nat.card ↥(mclP ⊓ Subgroup.centralizer ({t'} : Set (Equiv.Perm (Fin 275)))) =
      Nat.card ↥(mclP ⊓ Subgroup.centralizer ({tp 275 r.rep} : Set (Equiv.Perm (Fin 275)))) := by
    rw [hgt]
    exact card_cent_conj (P := mclP) (t := tp 275 r.rep) hg
  rw [h1]
  exact h2.trans (hcent.trans hco)

theorem card_centralizer_order_five_McL
    (w : NativeSporadic.McL) (hw : orderOf w = 5) :
    Nat.card ↥(Subgroup.centralizer ({w} : Set NativeSporadic.McL)) = 750 ∨
      Nat.card ↥(Subgroup.centralizer ({w} : Set NativeSporadic.McL)) = 25 := by
  obtain ⟨x₁, x₂, -, -, c₁, c₂, -, hall⟩ := mcl_two_classes_order_five_of_certificate
  rcases hall w hw with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    left
    rw [← c₁, ← hc, card_centralizer_conj]
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    right
    rw [← c₂, ← hc, card_centralizer_conj]

theorem card_isPGroup_three_le_McL
    (w : NativeSporadic.McL) (hw : (orderOf w).Prime) (hdvd : orderOf w ∣ 40)
    (Q : Subgroup NativeSporadic.McL) (hQ : IsPGroup 3 Q)
    (hle : Q ≤ Subgroup.centralizer ({w} : Set NativeSporadic.McL)) : Nat.card Q ≤ 9 := by
  have hcard := Subgroup.card_dvd_of_le hle
  have h25 : orderOf w = 2 ∨ orderOf w = 5 := by
    have h40 : orderOf w ∣ 2 ^ 3 * 5 := by norm_num; exact hdvd
    rcases (Nat.Prime.dvd_mul hw).1 h40 with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hw Nat.prime_two).1 (hw.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hw Nat.prime_five).1 h)
  rcases h25 with h | h
  · rw [card_centralizer_involution_McL w h] at hcard
    exact card_le_of_isPGroup_of_dvd Nat.prime_three hQ (e := 2) (by norm_num) hcard
  · rcases card_centralizer_order_five_McL w h with h5 | h5
    · rw [h5] at hcard
      have := card_le_of_isPGroup_of_dvd Nat.prime_three hQ (e := 1) (by norm_num) hcard
      omega
    · rw [h5] at hcard
      have := card_le_of_isPGroup_of_dvd Nat.prime_three hQ (e := 0) (by norm_num) hcard
      omega

theorem oPrimeCoreTrivialAt_McL :
    OPrimeCoreTrivialAt 3 NativeSporadic.McL := by
  obtain ⟨x₁, x₂, o₁, o₂, c₁, c₂, -, hall⟩ := mcl_two_classes_order_three_of_certificate
  have h₁ : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x₁} : Set NativeSporadic.McL)) = ⊥ :=
    gLAPPrimeCoreOf_eq_bot_of_card_bound Nat.prime_three (a := 6) (r := 40) (m := 9)
      (by rw [c₁]; norm_num) (by norm_num) (by norm_num) fun w hw hdvd Q hQ hle =>
        card_isPGroup_three_le_McL w hw hdvd Q hQ hle
  have h₂ : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x₂} : Set NativeSporadic.McL)) = ⊥ :=
    gLAPPrimeCoreOf_eq_bot_of_card_bound Nat.prime_three (a := 5) (r := 4) (m := 9)
      (by rw [c₂]; norm_num) (by norm_num) (by norm_num) fun w hw hdvd Q hQ hle =>
        card_isPGroup_three_le_McL w hw (hdvd.trans (by norm_num)) Q hQ hle
  intro y hy
  rcases hall y hy with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine (gLAPPrimeCoreOf_centralizer_conj c y).1 ?_
    rw [hc]
    exact h₁
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine (gLAPPrimeCoreOf_centralizer_conj c y).1 ?_
    rw [hc]
    exact h₂

theorem noOuterFixesCentralizer_McL :
    NoOuterFixesCentralizer 3 NativeSporadic.McL := by
  intro σ hσ2 hσ s hs
  by_contra hno
  push Not at hno
  obtain ⟨-, -, hfix⟩ := mcl_outer_involutions_of_certificate
  have hσ1 : σ ≠ 1 := fun h => hσ (h ▸ (innerAut _).one_mem)
  have hord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  obtain ⟨e⟩ := hfix σ hord hσ
  have hle : Subgroup.centralizer ({s} : Set NativeSporadic.McL) ≤ mclFixed σ := by
    intro t ht
    exact mem_fixedSubgroup.2 (hno t (Subgroup.mem_centralizer_singleton_iff.1 ht).symm)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M11] at hdvd
  obtain ⟨x₁, x₂, o₁, o₂, c₁, c₂, -, hall⟩ := mcl_two_classes_order_three_of_certificate
  rcases hall s hs with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← card_centralizer_conj c s, hc, c₁] at hdvd
    norm_num at hdvd
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← card_centralizer_conj c s, hc, c₂] at hdvd
    norm_num at hdvd

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
