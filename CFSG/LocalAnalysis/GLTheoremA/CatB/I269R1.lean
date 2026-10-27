module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Red
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.UniquenessCase.UCKP3Y
public import CFSG.RankThree.PartOne.S12.ModelTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.LocalAnalysis.UniquenessCase.UCK

namespace I269R

set_option linter.unusedSectionVars false

theorem isSolvable_of_card_dvd {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
  have hsub : (Nat.card G).primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hdvd, -⟩ := hp
    have h2 : p ∣ 2 ^ a * 3 ^ b := hdvd.trans h
    rcases (Nat.Prime.dvd_mul hpp).1 h2 with h3 | h3
    · have := hpp.dvd_of_dvd_pow h3
      rw [(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 this]
      simp
    · have := hpp.dvd_of_dvd_pow h3
      rw [(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 this]
      simp
  calc (Nat.card G).primeFactors.card ≤ ({2, 3} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 2 := by decide

section U38


theorem no_E9_centralizes_nineteen (E : Subgroup U38G) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 9) (z : U38G) (hz : orderOf z = 19) (hc : ∀ e ∈ E, e * z = z * e) :
    False := by
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hG : ¬ 19 ^ 2 ∣ Nat.card U38G := by rw [card_U38G]; norm_num
  have h19 : orderOf (⟨X19, X19_mem⟩ : U38G) = 19 := by
    rw [← Subgroup.orderOf_coe]; exact X19_order
  obtain ⟨g, hg⟩ := exists_conj_mem_zpowers hG hz h19
  have hgo : orderOf (g * z * g⁻¹) = 19 := (orderOf_conj_group g z).trans hz
  have hle : Subgroup.zpowers (g * z * g⁻¹) ≤ Subgroup.zpowers (⟨X19, X19_mem⟩ : U38G) :=
    Subgroup.zpowers_le.2 hg
  have heq : Subgroup.zpowers (g * z * g⁻¹) = Subgroup.zpowers (⟨X19, X19_mem⟩ : U38G) :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hgo, h19])
  have hX : (⟨X19, X19_mem⟩ : U38G) ∈ Subgroup.zpowers (g * z * g⁻¹) := by
    rw [heq]; exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hX
  have hsub : E.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ({(⟨X19, X19_mem⟩ : U38G)} : Set U38G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : Commute (g * e * g⁻¹) (g * z * g⁻¹) := by
      unfold Commute SemiconjBy
      calc g * e * g⁻¹ * (g * z * g⁻¹) = g * (e * z) * g⁻¹ := by group
        _ = g * (z * e) * g⁻¹ := by rw [hc e he]
        _ = g * z * g⁻¹ * (g * e * g⁻¹) := by group
    have := (hcomm.zpow_right k).eq
    rw [hk] at this
    simpa [MulAut.conj_apply] using this
  have hdvd := Subgroup.card_dvd_of_le hsub
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard,
    card_centralizer_subtype U38G ⟨X19, X19_mem⟩, X19_centralizer_card] at hdvd
  omega

theorem X7_mem_X' : X7 ∈ X' := (fixCheck_spec checks_of_certificate419001.1).1

theorem exists_fix_pair : ∃ p q : Fin 513, p ≠ q ∧ X7 p = p ∧ X7 q = q ∧
    ∀ r, X7 r = r → r = p ∨ r = q := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, hne, hall⟩ := Nat.card_eq_two_iff.1 X7_fixed
  refine ⟨p, q, fun h => hne (Subtype.ext h), hp, hq, fun r hr => ?_⟩
  have : (⟨r, hr⟩ : {r : Fin 513 // X7 r = r}) ∈
      ({⟨p, hp⟩, ⟨q, hq⟩} : Set {r : Fin 513 // X7 r = r}) := by
    rw [hall]; trivial
  rcases this with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem fixes_pair_of_commute {β : Equiv.Perm (Fin 513)} (hβ3 : β ^ 3 = 1) (hc : β * X7 = X7 * β)
    {p q : Fin 513} (hne : p ≠ q) (hp : X7 p = p) (hq : X7 q = q)
    (hall : ∀ r, X7 r = r → r = p ∨ r = q) : β p = p ∧ β q = q :=
  fixes_pair_of_cube_comm hβ3 hc hne hp hq hall

theorem conj_injective_X' : Function.Injective (MulAut.conj : ↥X' →* MulAut ↥X') := by
  intro t t' h
  have h1 : ∀ s : ↥X', rhoU38 (⟨s, X'_le_U38G s.2⟩ : U38G) = MulAut.conj s := fun s =>
    MulEquiv.ext fun x => Subtype.ext (by rw [rhoU38_apply, MulAut.conj_apply]; rfl)
  have h2 := rhoU38_injective ((h1 t).trans (h.trans (h1 t').symm))
  have h3 : (t : Equiv.Perm (Fin 513)) = t' := Subtype.mk.inj h2
  exact Subtype.ext h3

theorem no_E9_fixes_seven (E : Subgroup (MulAut ↥X')) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 9) (y : ↥X') (hy : orderOf y = 7) (hfix : ∀ α ∈ E, α y = y) : False := by
  have hinj := conj_injective_X'
  have hinner : E ≤ (MulAut.conj : ↥X' →* MulAut ↥X').range := fun α hα => by
    obtain ⟨t, -, ht⟩ := yFixClaim_psu38 α (hE.2 α hα) y hy (hfix α hα)
    exact ⟨t, MulEquiv.ext fun w => by rw [MulAut.conj_apply]; exact (ht w).symm⟩
  set Ei : Subgroup ↥X' := E.comap (MulAut.conj : ↥X' →* MulAut ↥X') with hEidef
  have hmap : Ei.map (MulAut.conj : ↥X' →* MulAut ↥X') = E := Subgroup.map_comap_eq_self hinner
  have hcardEi : Nat.card Ei = 9 := by
    have := Subgroup.card_map_of_injective (K := Ei) hinj
    rw [hmap, hcard] at this
    exact this.symm
  have hEi3 : ∀ t ∈ Ei, t ^ 3 = 1 := by
    intro t ht
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ ht
  have hEic : ∀ t ∈ Ei, t * y * t⁻¹ = y := fun t ht => by
    have := hfix _ ht
    rwa [MulAut.conj_apply] at this
  obtain ⟨p, q, hpq, hp, hq, hall⟩ := exists_fix_pair
  obtain ⟨g, hg⟩ := exists_conj_X7 X7_mem_X' y hy
  have hyo : orderOf (y : Equiv.Perm (Fin 513)) = 7 := by rw [Subgroup.orderOf_coe]; exact hy
  have hle : Ei.map (MulAut.conj g).toMonoidHom ≤
      MulAction.stabilizer ↥X' p ⊓ MulAction.stabilizer ↥X' q := by
    rintro _ ⟨t, ht, rfl⟩
    have hcomm : Commute (((g * t * g⁻¹ : ↥X')) : Equiv.Perm (Fin 513))
        ((g : Equiv.Perm (Fin 513)) * y * (g : Equiv.Perm (Fin 513))⁻¹) := by
      have h1 : (t : Equiv.Perm (Fin 513)) * y * (t : Equiv.Perm (Fin 513))⁻¹ = y :=
        congrArg Subtype.val (hEic t ht)
      unfold Commute SemiconjBy
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have h2 : (t : Equiv.Perm (Fin 513)) * y = y * t := by
        calc (t : Equiv.Perm (Fin 513)) * y = (t * y * (t : Equiv.Perm (Fin 513))⁻¹) * t := by group
          _ = y * t := by rw [h1]
      calc (g : Equiv.Perm (Fin 513)) * t * (g : Equiv.Perm (Fin 513))⁻¹ *
            ((g : Equiv.Perm (Fin 513)) * y * (g : Equiv.Perm (Fin 513))⁻¹)
          = g * (t * y) * (g : Equiv.Perm (Fin 513))⁻¹ := by group
        _ = g * (y * t) * (g : Equiv.Perm (Fin 513))⁻¹ := by rw [h2]
        _ = (g : Equiv.Perm (Fin 513)) * y * (g : Equiv.Perm (Fin 513))⁻¹ *
            ((g : Equiv.Perm (Fin 513)) * t * (g : Equiv.Perm (Fin 513))⁻¹) := by group
    have hX7c := commute_X7_of_conj hyo hg hcomm
    have h3 : (((g * t * g⁻¹ : ↥X')) : Equiv.Perm (Fin 513)) ^ 3 = 1 := by
      have : (g * t * g⁻¹ : ↥X') ^ 3 = 1 := by
        rw [conj_pow, hEi3 t ht]; group
      exact congrArg Subtype.val this
    obtain ⟨h1, h2⟩ := fixes_pair_of_commute h3 hX7c.eq hpq hp hq hall
    exact Subgroup.mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 h1, MulAction.mem_stabilizer_iff.2 h2⟩
  have h2trans : ∀ a b a' b' : Fin 513, a ≠ b → a' ≠ b' → ∃ g : ↥X', g • a = a' ∧ g • b = b' := by
    intro a b a' b' hab hab'
    obtain ⟨g, hg, h1, h2⟩ := X'_twoTransitive a b a' b' hab hab'
    exact ⟨⟨g, hg⟩, h1, h2⟩
  have hpair := card_pairStabilizer (H := ↥X') (Ω := Fin 513) h2trans hpq
  rw [Nat.card_fin, card_X'] at hpair
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardEi] at hdvd
  generalize Nat.card ↥(MulAction.stabilizer ↥X' p ⊓ MulAction.stabilizer ↥X' q) = X at hpair hdvd
  omega

theorem e9Solv_X' : E9Solv ↥X' := by
  intro E hE hcard
  haveI : Finite ↥X' := inferInstance
  have hbij := rhoU38_bijective (X := ↥X') nonempty_X'_equiv_projSU
  let ρ' : U38G ≃* MulAut ↥X' := MulEquiv.ofBijective rhoU38 hbij
  have h19 : ¬ 19 ∣ Nat.card (i269Fix E) := by
    intro h
    haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(i269Fix E)) 19 h
    have hz' : orderOf (z : ↥X') = 19 := by rw [Subgroup.orderOf_coe]; exact hz
    have hzf : ∀ α ∈ E, α (z : ↥X') = z := mem_i269Fix.1 z.2
    set zΓ : U38G := ⟨((z : ↥X') : Equiv.Perm (Fin 513)), X'_le_U38G (z : ↥X').2⟩ with hzΓ
    have hzΓo : orderOf zΓ = 19 := by
      rw [← Subgroup.orderOf_coe]
      show orderOf (((z : ↥X') : Equiv.Perm (Fin 513))) = 19
      rw [Subgroup.orderOf_coe]; exact hz'
    refine no_E9_centralizes_nineteen (E.map ρ'.symm.toMonoidHom) (hE.map _) ?_ zΓ hzΓo ?_
    · rw [Subgroup.card_map_of_injective ρ'.symm.injective, hcard]
    · rintro _ ⟨α, hα, rfl⟩
      apply Subtype.ext
      have h1 := hzf α hα
      have h2 : ((ρ' (ρ'.symm α) (z : ↥X') : ↥X') : Equiv.Perm (Fin 513)) =
          ((α (z : ↥X') : ↥X') : Equiv.Perm (Fin 513)) := by
        rw [ρ'.apply_symm_apply]
      rw [h1] at h2
      have h3 : ((ρ' (ρ'.symm α) (z : ↥X') : ↥X') : Equiv.Perm (Fin 513)) =
          ((ρ'.symm α : U38G) : Equiv.Perm (Fin 513)) * ((z : ↥X') : Equiv.Perm (Fin 513)) *
            ((ρ'.symm α : U38G) : Equiv.Perm (Fin 513))⁻¹ := rhoU38_apply _ _
      rw [h3] at h2
      show ((ρ'.symm α : U38G) : Equiv.Perm (Fin 513)) * ((z : ↥X') : Equiv.Perm (Fin 513)) =
        ((z : ↥X') : Equiv.Perm (Fin 513)) * ((ρ'.symm α : U38G) : Equiv.Perm (Fin 513))
      calc ((ρ'.symm α : U38G) : Equiv.Perm (Fin 513)) * ((z : ↥X') : Equiv.Perm (Fin 513))
          = (((ρ'.symm α : U38G) : Equiv.Perm (Fin 513)) * ((z : ↥X') : Equiv.Perm (Fin 513)) *
            ((ρ'.symm α : U38G) : Equiv.Perm (Fin 513))⁻¹) *
              ((ρ'.symm α : U38G) : Equiv.Perm (Fin 513)) := by group
        _ = _ := by rw [h2]
  have h7 : ¬ 7 ∣ Nat.card (i269Fix E) := by
    intro h
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(i269Fix E)) 7 h
    have hy' : orderOf (y : ↥X') = 7 := by rw [Subgroup.orderOf_coe]; exact hy
    exact no_E9_fixes_seven E hE hcard (y : ↥X') hy' (mem_i269Fix.1 y.2)
  have hdvd : Nat.card (i269Fix E) ∣ 2 ^ 9 * 3 ^ 4 := by
    have h1 : Nat.card (i269Fix E) ∣ 5515776 := by
      rw [← card_X']; exact Subgroup.card_subgroup_dvd_card _
    have hc7 : Nat.Coprime (Nat.card (i269Fix E)) 7 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h7).symm
    have hc19 : Nat.Coprime (Nat.card (i269Fix E)) 19 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h19).symm
    have h2 : Nat.card (i269Fix E) ∣ 2 ^ 9 * 3 ^ 4 * 7 * 19 := by
      rw [show 2 ^ 9 * 3 ^ 4 * 7 * 19 = 5515776 by norm_num]; exact h1
    exact hc19.dvd_of_dvd_mul_right (hc7.dvd_of_dvd_mul_right h2)
  exact isSolvable_of_card_dvd hdvd

end U38

end I269R

section Certs


theorem e9Solv_u3eight (S : Type) [Group S] (h : catalogIs S S9.isU3eight) : E9Solv S := by
  have hX : Nonempty (S ≃* ↥(CFSG.PGLModel.projSU 3 2 3)) := by
    obtain ⟨e⟩ := CatB.bridge_u3eight h
    have hP : CFSG.PGLModel.projImage (CFSG.Open.StatedSU 3 (2 ^ 3) (GaloisField 2 6)) =
        CFSG.PGLModel.projSU 3 2 3 :=
      CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 3 2 3
    exact ⟨e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivProjImage _ hP)⟩
  obtain ⟨eX⟩ := nonempty_equiv_X' hX
  exact I269R.e9Solv_X'.of_mulEquiv eX

end Certs

end CFSG.LocalAnalysis.GLTheoremA

end
