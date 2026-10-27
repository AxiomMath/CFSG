module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4PlaneCentralizer
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4OuterSigma
public import CFSG.RankThree.PartOne.F106.OddRadTits
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)


section Pure

private theorem s265f_conj_injective {Q : Type} [Group Q] (hZ : Subgroup.center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun φ : MulAut Q => φ y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * g = (g * y * g⁻¹) * g := by rw [h]
      _ = g * y := by group
  rw [hZ] at hmem
  exact Subgroup.mem_bot.1 hmem

private theorem s265f_isElemAbelian_comap {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    (hf : Function.Injective f) {U : Subgroup H} (hU : IsElemAbelian p U) :
    IsElemAbelian p (U.comap f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hf
    have h := hU.1.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩
    have h' := congrArg Subtype.val h
    simpa [map_mul] using h'
  · apply hf
    rw [map_pow, map_one]
    exact hU.2 _ hx

end Pure

section Cert


open CFSG.HardMathSupport.Malle.LocalAction in
private theorem s265f_plane_cent_solvable {Q : Type} [Group Q] {F : Type} [Field F] [Finite F] [CharP F F4.prime]
    (hF : Nat.card F = 2 ^ (2 * 2 + 1)) (eΓ : Q ≃* F4.reeGamma F 2) (E : Subgroup Q)
    (hE : IsElemAbelian 5 E) (h25 : Nat.card E = 25) :
    Group.IsSolvable ↥(Subgroup.centralizer (E : Set Q)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set E' : Subgroup (F4.reeGamma F 2) := E.map eΓ.toMonoidHom with hE'
  have hE'ab : IsElemAbelian 5 E' := CFSG.SectionRank.isElemAbelian_map hE eΓ.toMonoidHom
  have hE'card : Nat.card E' = 5 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective eΓ.injective, h25]
    norm_num
  have hEp : IsPGroup 5 E' := fun x => ⟨1, Subtype.ext (by simpa using hE'ab.2 x x.2)⟩
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have hcent := centralizer_plane_eq_sylow hF P E' hEP hE'ab hE'card
  have hmem : ∀ g : ↥(Subgroup.centralizer (E : Set Q)), eΓ g ∈ (P : Subgroup (F4.reeGamma F 2)) := by
    intro g
    rw [← hcent, Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have h := Subgroup.mem_centralizer_iff.1 g.2 e he
    show eΓ e * eΓ g = eΓ g * eΓ e
    rw [← map_mul, ← map_mul]
    exact congrArg eΓ h
  let f : ↥(Subgroup.centralizer (E : Set Q)) →* ↥(P : Subgroup (F4.reeGamma F 2)) :=
    (eΓ.toMonoidHom.comp (Subgroup.centralizer (E : Set Q)).subtype).codRestrict _ hmem
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (eΓ.injective (congrArg Subtype.val h))
  haveI : Group.IsNilpotent ↥(P : Subgroup (F4.reeGamma F 2)) := (P.isPGroup').isNilpotent
  exact Group.isSolvable_of_isSolvable_injective hf

private theorem s265f_caseII {Q : Type} [Group Q] (hmodel : ReeTitsModel Q .twistedF4 2 5)
    {τ : MulAut Q} (hτ : orderOf τ = 5) (hτi : τ ∉ inner Q) {γ : Q} (hγ : orderOf γ = 5)
    (hγτ : τ γ = γ) (Y : Subgroup Q) (hYτ : ∀ y ∈ Y, τ y = y) (hYγ : ∀ y ∈ Y, γ * y = y * γ) :
    Group.IsSolvable ↥Y := by
  obtain ⟨hadm, a, hfa, K, hKf, hKfin, hK, ⟨e0⟩⟩ := hmodel
  have ha : a = 2 := by omega
  subst ha
  have hK' : Nat.card K = 2 ^ (2 * 2 + 1) := by simpa using hK
  obtain ⟨-, b, hb, k, _, _, _, hk, ⟨eF⟩⟩ :=
    FR.Res.ree_fix_equiv (by norm_num : 1 ≤ 2) hK' Nat.prime_five (by norm_num) e0 τ hτ hτi
  have hb0 : b = 0 := by omega
  subst hb0
  have hk2 : Nat.card k = 2 := by simpa using hk
  have hγmem : γ ∈ FP.fixSub τ := FP.mem_fixSub.2 hγτ
  set x : F4.reeGamma k 0 := eF ⟨γ, hγmem⟩ with hx
  have hxord : orderOf x = 5 := by
    have h1 : orderOf (eF.toMonoidHom ⟨γ, hγmem⟩) = orderOf (⟨γ, hγmem⟩ : ↥(FP.fixSub τ)) :=
      orderOf_injective eF.toMonoidHom eF.injective _
    have h2 : orderOf (⟨γ, hγmem⟩ : ↥(FP.fixSub τ)) = 5 := (Subgroup.orderOf_mk γ hγmem).trans hγ
    exact h1.trans h2
  haveI hsol := CFSG.RankThree.PartOne.F106.solvable_centralizer_ree_zero hk2 x hxord
  have hYle : Y ≤ FP.fixSub τ := fun y hy => FP.mem_fixSub.2 (hYτ y hy)
  let ρ0 : ↥Y →* ↥(F4.reeGamma k 0) := eF.toMonoidHom.comp (Subgroup.inclusion hYle)
  have hρ0 : ∀ y : ↥Y, ρ0 y ∈ Subgroup.centralizer ({x} : Set (F4.reeGamma k 0)) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff]
    show eF (Subgroup.inclusion hYle y) * eF ⟨γ, hγmem⟩ = eF ⟨γ, hγmem⟩ * eF (Subgroup.inclusion hYle y)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hYγ y y.2).symm
  let ρ := ρ0.codRestrict _ hρ0
  have hρinj : Function.Injective ρ := fun a b h =>
    Subtype.ext (by
      have h1 : ρ0 a = ρ0 b := congrArg Subtype.val h
      have h2 : Subgroup.inclusion hYle a = Subgroup.inclusion hYle b := eF.injective h1
      exact congrArg (fun z : ↥(FP.fixSub τ) => (z : Q)) h2)
  exact Group.isSolvable_of_isSolvable_injective hρinj

theorem s265f_tits_core {Q : Type} [Group Q] (hmodel : ReeTitsModel Q .twistedF4 2 5)
    (Ē : Subgroup (MulAut Q)) (hĒ : IsElemAbelian 5 Ē) (h25 : 25 ≤ Nat.card Ē)
    (Y : Subgroup Q) (hY : ∀ y ∈ Y, ∀ ψ ∈ Ē, ψ y = y) : Group.IsSolvable ↥Y := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hQfin, -, -, -, -, hiso⟩ := large_Ree_model_Schreier Q 2 5 hmodel
  obtain ⟨hadm, a, hfa, F, hFf, hFfin, hF, ⟨e'⟩⟩ := id hmodel
  have ha : a = 2 := by omega
  subst ha
  have hF' : Nat.card F = 2 ^ (2 * 2 + 1) := by simpa using hF
  haveI : CharP F F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hF
  obtain ⟨eΓ⟩ := hiso 2 F rfl hF ⟨e'⟩
  have hZ : Subgroup.center Q = ⊥ := by
    have hZΓ := large_Ree_fixed_group_center_trivial 2 F hF'
    refine eq_bot_iff.2 fun g hg => ?_
    have hmem : eΓ g ∈ Subgroup.center (F4.reeGamma F 2) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨q, rfl⟩ := eΓ.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg eΓ (Subgroup.mem_center_iff.1 hg q)
    rw [hZΓ, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (eΓ.injective (by rw [hmem, map_one]))
  have hOut : Nat.card (Outer Q) ∣ 5 := by
    obtain ⟨-, hOutn⟩ := CFSG.AGLEmbedding.outer_reeGamma (a := 2) (K := F) (by norm_num) hF'
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eΓ).toEquiv]
    simpa using hOutn
  have hinj := s265f_conj_injective hZ
  by_cases hinn : Ē ≤ inner Q
  ·
    set Ē₀ : Subgroup Q := Ē.comap (MulAut.conj : Q →* MulAut Q) with hĒ₀
    have hmap : Ē₀.map (MulAut.conj : Q →* MulAut Q) = Ē := Subgroup.map_comap_eq_self hinn
    have hĒ₀ab : IsElemAbelian 5 Ē₀ := s265f_isElemAbelian_comap _ hinj hĒ
    have hcard : Nat.card Ē₀ = Nat.card Ē := by
      rw [← hmap, Subgroup.card_map_of_injective hinj]
    have hle : Nat.card Ē₀ ≤ 25 := by
      have hE' : IsElemAbelian 5 (Ē₀.map eΓ.toMonoidHom) :=
        CFSG.SectionRank.isElemAbelian_map hĒ₀ab eΓ.toMonoidHom
      have := CFSG.HardMathSupport.Malle.LocalAction.card_le_twentyfive_of_elemAbelian_reeGamma hF' _ hE'
      rwa [Subgroup.card_map_of_injective eΓ.injective] at this
    have h25' : Nat.card Ē₀ = 25 := by omega
    haveI := s265f_plane_cent_solvable hF' eΓ Ē₀ hĒ₀ab h25'
    have hYle : Y ≤ Subgroup.centralizer (Ē₀ : Set Q) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have h := hY y hy (MulAut.conj e) (Subgroup.mem_comap.1 he)
      simp only [MulAut.conj_apply] at h
      calc e * y = (e * y * e⁻¹) * e := by group
        _ = y * e := by rw [h]
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYle)
      (Subgroup.inclusion_injective hYle)
  ·
    obtain ⟨τ, hτE, hτi⟩ := SetLike.not_le_iff_exists.1 hinn
    have hτ5 : τ ^ 5 = 1 := hĒ.2 τ hτE
    have hτ1 : τ ≠ 1 := fun h => hτi (h ▸ Subgroup.one_mem _)
    have hτord : orderOf τ = 5 := orderOf_eq_prime hτ5 hτ1
    let ψ : ↥Ē →* Outer Q :=
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner Q)).comp Ē.subtype
    have hker : ψ.ker ≠ ⊥ := by
      intro hbot
      have h1 := Subgroup.card_ker_mul_card_range ψ
      rw [hbot, Subgroup.card_bot, one_mul] at h1
      have h2 : Nat.card ψ.range ∣ 5 := (Subgroup.card_subgroup_dvd_card ψ.range).trans hOut
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hker
    have hu₀E : (u.1 : MulAut Q) ∈ Ē := u.1.2
    have hu₀inner : (u.1 : MulAut Q) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Q :=
      (QuotientGroup.eq_one_iff _).1 u.2
    have hu₀1 : (u.1 : MulAut Q) ≠ 1 := fun h => hu1 (Subtype.ext (Subtype.ext h))
    obtain ⟨γ, hγ⟩ := hu₀inner
    have hγ5 : γ ^ 5 = 1 := by
      apply hinj
      rw [map_pow, map_one, hγ]
      exact hĒ.2 _ hu₀E
    have hγ1 : γ ≠ 1 := by
      rintro rfl
      apply hu₀1
      rw [← hγ, map_one]
    have hγord : orderOf γ = 5 := orderOf_eq_prime hγ5 hγ1
    have hcomm : τ * (u.1 : MulAut Q) = (u.1 : MulAut Q) * τ := by
      have := hĒ.1.is_comm.comm ⟨τ, hτE⟩ ⟨(u.1 : MulAut Q), hu₀E⟩
      exact congrArg Subtype.val this
    have hτγ : τ γ = γ := by
      apply hinj
      have h1 : (MulAut.conj (τ γ) : MulAut Q) = τ * MulAut.conj γ * τ⁻¹ := by
        apply MulEquiv.ext
        intro q
        simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv]
      rw [h1, hγ, hcomm, mul_inv_cancel_right]
    have hYτ : ∀ y ∈ Y, τ y = y := fun y hy => hY y hy τ hτE
    have hYγ : ∀ y ∈ Y, γ * y = y * γ := by
      intro y hy
      have h := hY y hy _ hu₀E
      rw [← hγ] at h
      simp only [MulAut.conj_apply] at h
      calc γ * y = (γ * y * γ⁻¹) * γ := by group
        _ = y * γ := by rw [h]
    exact s265f_caseII hmodel hτord hτi hγord hτγ Y hYτ hYγ

end Cert

end CFSG.LocalAnalysis.GLTheoremA.S265

end
