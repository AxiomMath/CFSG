module

public import CFSG.GH74.Uniqueness.SU.KInputs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Lifts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.AlternatingFactsThreeCycles

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup Equiv CFSG.ProperTwoGeneratedCore.Lemma37
open CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

abbrev stab8 : Subgroup (alternatingGroup (Fin 9)) :=
  MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9)

@[expose] noncomputable def altEightEmbed : alternatingGroup (Fin 8) →* alternatingGroup (Fin 9) :=
  ((Perm.extendDomainHom finEightEquiv).comp (alternatingGroup (Fin 8)).subtype).codRestrict _
    fun σ => by
      rw [Perm.mem_alternatingGroup, MonoidHom.comp_apply, Perm.extendDomainHom_apply,
        Perm.sign_extendDomain]
      exact σ.2

theorem altEightEmbed_injective : Function.Injective altEightEmbed := fun _ _ hab =>
  Subtype.ext (Perm.extendDomainHom_injective finEightEquiv (congrArg Subtype.val hab))

theorem range_altEightEmbed : altEightEmbed.range = stab8 := by
  ext g
  constructor
  · rintro ⟨σ, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change (Perm.extendDomain (σ : Perm (Fin 8)) finEightEquiv) 8 = 8
    exact Perm.extendDomain_apply_not_subtype _ _ (by simp)
  · intro hg
    rw [MulAction.mem_stabilizer_iff] at hg
    have h8 : (g : Perm (Fin 9)) 8 = 8 := hg
    obtain ⟨g', hg'⟩ := exists_extendDomain_eq h8
    have hsign : Perm.sign g' = 1 := by
      have := g.2
      rw [Perm.mem_alternatingGroup, ← hg', Perm.sign_extendDomain] at this
      exact this
    exact ⟨⟨g', hsign⟩, Subtype.ext hg'⟩

@[expose] noncomputable def stab8Equiv : alternatingGroup (Fin 8) ≃* stab8 :=
  (MonoidHom.ofInjective altEightEmbed_injective).trans
    (MulEquiv.subgroupCongr range_altEightEmbed)


theorem nonabelian_alt8 : ∃ a b : alternatingGroup (Fin 8), a * b ≠ b * a := by
  refine ⟨⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨swap 0 1 * swap 1 3, Perm.mem_alternatingGroup.mpr (by decide)⟩, ?_⟩
  intro h
  have := congrArg Subtype.val h
  revert this
  decide

theorem center_alt8 {g : alternatingGroup (Fin 8)} (hg : g ∈ center (alternatingGroup (Fin 8))) :
    g = 1 := by
  have hA8 : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  rcases hA8.eq_bot_or_eq_top_of_normal (center (alternatingGroup (Fin 8))) with h | h
  · rw [h] at hg
    exact mem_bot.mp hg
  · exfalso
    obtain ⟨a, b, hab⟩ := nonabelian_alt8
    apply hab
    have := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    exact this

theorem genA_mem_stab8 : aNineSylowGenA ∈ stab8 := by
  rw [MulAction.mem_stabilizer_iff]
  unfold aNineSylowGenA
  change (swap 0 1 * swap 2 3 : Perm (Fin 9)) 8 = 8
  decide

variable {J : Type} [Group J]

theorem isTwoAlt_comap_stabilizer (hJ : IsTwoANine J)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 9)) :
    IsTwoAlt ↥(stab8.comap (proj e)) 8 := by
  classical
  have hfin : Finite J := hJ.finite
  have hfin' : Finite (stab8.comap (proj e)) := inferInstance
  set B : Subgroup J := stab8.comap (proj e) with hB
  have hz : zbar J ∈ B := by
    rw [hB, Subgroup.mem_comap, hJ.proj_zbar e]; exact one_mem _
  let z' : B := ⟨zbar J, hz⟩
  let ρ : B →* stab8 := (proj e).subgroupComap stab8
  have hρval : ∀ b : B, ((ρ b : stab8) : alternatingGroup (Fin 9)) = proj e (b : J) := fun _ => rfl
  have hρsurj : Function.Surjective ρ := by
    rintro ⟨s, hs⟩
    obtain ⟨j, hj⟩ := proj_surjective e s
    exact ⟨⟨j, by rw [hB, Subgroup.mem_comap, hj]; exact hs⟩, Subtype.ext hj⟩
  have hρker : ∀ b : B, ρ b = 1 ↔ b = 1 ∨ b = z' := by
    intro b
    have h1 : ρ b = 1 ↔ proj e (b : J) = 1 := by
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h
    rw [h1, proj_eq_one_iff, hJ.mem_center_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have hz'c : z' ∈ center B := Subgroup.mem_center_iff.mpr fun x =>
    Subtype.ext (hJ.commute_zbar (x : J)).eq
  have hcen : center B = ρ.ker := by
    ext b
    rw [MonoidHom.mem_ker, hρker]
    constructor
    · intro hb
      have hbc : ρ b ∈ center stab8 := by
        rw [Subgroup.mem_center_iff]
        intro s
        obtain ⟨x, rfl⟩ := hρsurj s
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hb x]
      have h1 : stab8Equiv.symm (ρ b) = 1 := by
        apply center_alt8
        rw [Subgroup.mem_center_iff]
        intro g
        have := Subgroup.mem_center_iff.mp hbc (stab8Equiv g)
        apply stab8Equiv.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact this
      have h2 : ρ b = 1 := by
        have := congrArg stab8Equiv h1
        rwa [MulEquiv.apply_symm_apply, map_one] at this
      exact (hρker b).mp h2
    · rintro (h | h)
      · rw [h]; exact one_mem _
      · rw [h]; exact hz'c
  have hcard : Nat.card (center B) = 2 := by
    rw [Nat.card_eq_two_iff' (1 : center B)]
    refine ⟨⟨z', hz'c⟩, ?_, ?_⟩
    · intro h
      exact hJ.zbar_ne_one (congrArg (fun x : center B => ((x : B) : J)) h)
    · intro y hy
      have hy' : (y : B) = 1 ∨ (y : B) = z' := by
        have : (y : B) ∈ ρ.ker := hcen ▸ y.2
        exact (hρker _).mp this
      rcases hy' with h | h
      · exact absurd (Subtype.ext h) hy
      · exact Subtype.ext h
  have hA8s : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA8p : Group.IsPerfect (alternatingGroup (Fin 8)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  have hSp : Group.IsPerfect stab8 :=
    Group.IsPerfect.ofSurjective (f := stab8Equiv.toMonoidHom) stab8Equiv.surjective
  let ψ : B ⧸ center B ≃* alternatingGroup (Fin 8) :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      ((QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj).trans stab8Equiv.symm)
  have hperf : Group.IsPerfect B := by
    rw [Group.isPerfect_def]
    show (⁅(⊤ : Subgroup B), ⊤⁆ : Subgroup B) = ⊤
    set P : Subgroup B := ⁅(⊤ : Subgroup B), ⊤⁆ with hP
    have hSp' : (⁅(⊤ : Subgroup stab8), ⊤⁆ : Subgroup stab8) = ⊤ := Group.isPerfect_def.mp hSp
    have hmap : P.map ρ = ⊤ := by
      rw [hP, Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hρsurj]
      exact hSp'
    by_contra hPtop
    have hzP : z' ∉ P := by
      intro hzP
      apply hPtop
      rw [eq_top_iff]
      intro b _
      obtain ⟨p, hp, hpb⟩ : ρ b ∈ P.map ρ := by rw [hmap]; trivial
      have h1 : ρ (p⁻¹ * b) = 1 := by rw [map_mul, map_inv, hpb, inv_mul_cancel]
      rcases (hρker _).mp h1 with h | h
      · have : b = p := by rw [inv_mul_eq_one] at h; exact h.symm
        rw [this]; exact hp
      · have : b = p * z' := by rw [← h]; group
        rw [this]; exact P.mul_mem hp hzP
    obtain ⟨p, hp, hpδ⟩ : (⟨aNineSylowGenA, genA_mem_stab8⟩ : stab8) ∈ P.map ρ := by
      rw [hmap]; trivial
    have hgg : aNineSylowGenA * aNineSylowGenA = 1 := by
      refine Subtype.ext ?_
      unfold aNineSylowGenA
      change (swap 0 1 * swap 2 3 : Perm (Fin 9)) * (swap 0 1 * swap 2 3) = 1
      decide
    have hρpp : ρ (p * p) = 1 := by
      rw [map_mul, hpδ]
      exact Subtype.ext hgg
    have hpp : p * p = 1 := by
      rcases (hρker _).mp hρpp with h | h
      · exact h
      · exact absurd (h ▸ P.mul_mem hp hp) hzP
    have hct : ((proj e (p : J) : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2} := by
      have := congrArg Subtype.val (hρval p)
      rw [hpδ] at this
      rw [← this]
      exact cycleType_aNineSylowGenA
    have hsq := hJ.sq_eq_zbar_of_cycleType_two_two e hct
    have hpp' : ((p : B) : J) ^ 2 = 1 := by
      rw [sq]; exact congrArg Subtype.val hpp
    exact hJ.zbar_ne_one (hsq.symm.trans hpp')
  have hsimp : IsSimpleGroup (B ⧸ center B) := ψ.isSimpleGroup
  obtain ⟨a₀, b₀, hab₀⟩ := nonabelian_alt8
  refine ⟨⟨hperf, hsimp, ψ.symm a₀, ψ.symm b₀, fun h => hab₀ (ψ.symm.injective ?_)⟩, hfin', hcard,
    ⟨ψ⟩⟩
  rw [map_mul, map_mul]
  exact h

end CFSG.GH74.Uniqueness.SU.K.R6
