module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeSubgroupConj
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.E6One

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType CFSG.StandardType.NoOffE6Three CFSG.StandardType.TableBExc.E6Three

variable {K : Type} [Field K] [Finite K]

theorem map_hatAut_le_vAd_of_le_xHat {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {E : Subgroup (hatGroup .E6 K)}
    (hEX : E.map (hatGroup .E6 K).subtype ≤ xHat .E6 K modelHomE6.range)
    (hE : IsElemAbelian 3 (E.map (hatAut .E6 K)))
    (h6 : 3 ^ 6 ≤ Nat.card (E.map (hatAut .E6 K))) :
    E.map (hatAut .E6 K) ≤ vAd ζ hζ := by
  have : Finite (hatGroup .E6 K) := finite_hatGroup
  have hker : ∀ p ∈ E, hatAut .E6 K p = 1 → p = 1 := fun p hp h1 =>
    eq_one_of_hatAut_eq_one (xHat_le_monoHat _ (hEX ⟨p, hp, rfl⟩)) h1
  have hEab : ∀ p ∈ E, ∀ p' ∈ E, p * p' = p' * p := by
    intro p hp p' hp'
    have h1 : hatAut .E6 K (p * p' * (p' * p)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul,
        TableB.IsElemAbelian.comm hE (⟨p, hp, rfl⟩ : hatAut .E6 K p ∈ E.map (hatAut .E6 K))
          ⟨p', hp', rfl⟩, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hker _ (mul_mem (mul_mem hp hp') (inv_mem (mul_mem hp' hp))) h1)
  have hE3 : ∀ p ∈ E, p ^ 3 = 1 := fun p hp =>
    hker _ (pow_mem hp 3) (by rw [map_pow]; exact hE.2 _ ⟨p, hp, rfl⟩)
  have hEel : IsElemAbelian 3 E := ⟨⟨⟨fun a b => Subtype.ext (hEab a a.2 b b.2)⟩⟩, hE3⟩
  set E' : Subgroup (ModGL .E6 K) := E.map (hatGroup .E6 K).subtype with hE'
  have hE'el : IsElemAbelian 3 E' := TableB.isElemAbelian_map hEel _
  have hcard : Nat.card E' = Nat.card (E.map (hatAut .E6 K)) := by
    rw [hE', Subgroup.card_map_of_injective (hatGroup .E6 K).subtype_injective,
      card_map_eq_of_ker _ hker]
  have : Finite E' := Finite.of_surjective (fun p : E => (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩ : E'))
    (by rintro ⟨_, ⟨p, hp, rfl⟩⟩; exact ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨A, -, hA, hfixA, hcount, hbotA⟩ :=
    card_le_mul_card_diagKernel_of_le_xHat (τ := .E6) (p := 3) hζo hζ hE'el hEX
  have hA1 : A = ⊥ := by
    by_contra hA1
    have hoff := NoOffRest.actNoOffender_adPerm_E6 A hA hA1
    have hle : Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        rootDiagUnit .E6 (zetaVec ζ hζ x) ∈ E'} ≤
        Nat.card {v : Fin Tag.E6.rank → ZMod 3 // ∀ a ∈ A, adPerm .E6 3 a v = v} :=
      Nat.card_le_card_of_injective (fun x => ⟨x.1, fun a ha => hfixA a ha x.1 x.2⟩)
        (fun a b h => Subtype.ext (congrArg (fun v => (v.1 : Fin Tag.E6.rank → ZMod 3)) h))
    have hV : Nat.card (Fin Tag.E6.rank → ZMod 3) = 3 ^ 6 := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      rfl
    rw [hV] at hoff
    have h1 : 3 ^ 6 ≤ Nat.card A * Nat.card {v : Fin Tag.E6.rank → ZMod 3 //
        ∀ a ∈ A, adPerm .E6 3 a v = v} :=
      (h6.trans_eq hcard.symm).trans (hcount.trans (Nat.mul_le_mul_left _ hle))
    omega
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨x, hx⟩ := hbotA hA1 (p : ModGL .E6 K) ⟨p, hp, rfl⟩
  refine ⟨Multiplicative.ofAdd x, ?_⟩
  have hp' : p = ⟨rootDiagUnit .E6 (zetaVec ζ hζ x), rootDiagUnit_mem_hatGroup _⟩ :=
    Subtype.ext hx
  rw [hp', hatAut_rootDiagUnit_eq_rootDiagAutHom]
  rfl

theorem exists_conj_forall_eq_vAd (h3 : 3 ∣ Nat.card K - 1) {ζ : Kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {P : Subgroup (MulAut (adjointGroup .E6 K))} (hP : IsPGroup 3 P)
    (hPI : P ≤ (hatAut .E6 K).range) :
    ∃ γ ∈ (hatAut .E6 K).range, ∀ X : Subgroup (MulAut (adjointGroup .E6 K)), X ≤ P →
      IsElemAbelian 3 X → 3 ^ 6 ≤ Nat.card X → X.map (MulAut.conj γ).toMonoidHom = vAd ζ hζ := by
  have := Fact.mk Nat.prime_three
  have : Finite (hatGroup .E6 K) := finite_hatGroup
  set κ := hatAut .E6 K with hκ
  set Y : Subgroup (hatGroup .E6 K) := P.comap κ with hY
  set f : Y →* P := (κ.comp Y.subtype).codRestrict P (fun y => y.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨x, rfl⟩ := hPI hφ
    exact ⟨⟨x, hφ⟩, rfl⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 3 Y))
  have hQ : (Q₀ : Subgroup Y).map f = ⊤ :=
    ((Q₀.mapSurjective hfs).is_maximal' (hP.to_subgroup ⊤) le_top).symm
  set P₀ : Subgroup (hatGroup .E6 K) := (Q₀ : Subgroup Y).map Y.subtype with hP₀
  have hP₀3 : IsPGroup 3 P₀ := Q₀.isPGroup'.map _
  have hP₀P : P₀.map κ = P := by
    have hcomp : κ.comp Y.subtype = P.subtype.comp f := MonoidHom.ext fun _ => rfl
    rw [hP₀, Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨c, hc⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    (not_three_dvd_index_xHat h3) hP₀3
  set P' := P₀.map (MulAut.conj c).toMonoidHom with hP'
  have hP'P : P'.map κ = P.map (MulAut.conj (κ c)).toMonoidHom := by
    have hcomp : κ.comp (MulAut.conj c).toMonoidHom = (MulAut.conj (κ c)).toMonoidHom.comp κ :=
      MonoidHom.ext fun p => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
          map_inv]
    rw [hP', Subgroup.map_map, hcomp, ← Subgroup.map_map, hP₀P]
  refine ⟨κ c, ⟨c, rfl⟩, fun X hXP hX h6 => ?_⟩
  set X' := X.map (MulAut.conj (κ c)).toMonoidHom with hX'
  have hX'c : Nat.card X' = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj (κ c)).injective
  have hX'P : X' ≤ P'.map κ := hP'P ▸ Subgroup.map_mono hXP
  set E := P' ⊓ X'.comap κ with hE
  have hEX' : E.map κ = X' := by
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨p, hp, rfl⟩
      exact hp.2
    · obtain ⟨p, hp, rfl⟩ := hX'P hy
      exact ⟨p, ⟨hp, hy⟩, rfl⟩
  have hX'el : IsElemAbelian 3 X' := TableB.isElemAbelian_map hX _
  have hle : X' ≤ vAd ζ hζ := by
    have hEX : E.map (hatGroup .E6 K).subtype ≤ xHat .E6 K modelHomE6.range := by
      rintro _ ⟨p, hp, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hc hp.1)
    have hEel : IsElemAbelian 3 (E.map κ) := by rw [hEX']; exact hX'el
    have hE6 : 3 ^ 6 ≤ Nat.card (E.map κ) := by rw [hEX', hX'c]; exact h6
    rw [← hEX']
    exact map_hatAut_le_vAd_of_le_xHat hζo hζ hEX hEel hE6
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_vAd hζo hζ, hX'c]; exact h6)

theorem eq_of_le_of_isPGroup (h3 : 3 ∣ Nat.card K - 1)
    {P : Subgroup (MulAut (adjointGroup .E6 K))} (hP : IsPGroup 3 P)
    {X Y : Subgroup (MulAut (adjointGroup .E6 K))} (hXI : X ≤ (hatAut .E6 K).range)
    (hYI : Y ≤ (hatAut .E6 K).range) (hXP : X ≤ P) (hYP : Y ≤ P) (hX : IsElemAbelian 3 X)
    (hY : IsElemAbelian 3 Y) (hXc : Nat.card X = 3 ^ 6) (hYc : Nat.card Y = 3 ^ 6) : X = Y := by
  have := Fact.mk Nat.prime_three
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact h3)
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  obtain ⟨γ, -, hγ⟩ := exists_conj_forall_eq_vAd h3 hζo hζ (hP.to_le inf_le_left)
    (inf_le_right : P ⊓ (hatAut .E6 K).range ≤ _)
  exact Subgroup.map_injective (MulAut.conj γ).injective
    ((hγ X (le_inf hXP hXI) hX hXc.ge).trans (hγ Y (le_inf hYP hYI) hY hYc.ge).symm)

theorem card_le_of_le_hatAut (h3 : 3 ∣ Nat.card K - 1)
    {X : Subgroup (MulAut (adjointGroup .E6 K))} (hX : IsElemAbelian 3 X)
    (hXI : X ≤ (hatAut .E6 K).range) : Nat.card X ≤ 3 ^ 6 := by
  have := Fact.mk Nat.prime_three
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact h3)
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  by_contra h
  obtain ⟨γ, -, hγ⟩ := exists_conj_eq_vAd h3 hζo hζ hX hXI (Nat.le_of_lt (not_le.mp h))
  have hc : Nat.card (X.map (MulAut.conj γ).toMonoidHom) = Nat.card (vAd (K := K) ζ hζ) := by
    rw [hγ]
  rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective, card_vAd hζo hζ] at hc
  omega

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.E6One

end
