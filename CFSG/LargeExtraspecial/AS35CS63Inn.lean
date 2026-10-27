module

public import CFSG.LargeExtraspecial.AS35CS63Aut
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld CFSG.ComponentClassification

namespace S63

variable {X : Type} [Group X]

noncomputable abbrev piU (ζ : X) : ↥(normalClosure ({ζ} : Set X)) →* UZ ζ :=
  QuotientGroup.mk' _

@[expose] def zetaU (ζ : X) : ↥(normalClosure ({ζ} : Set X)) :=
  ⟨ζ, subset_normalClosure (Set.mem_singleton ζ)⟩

theorem piU_surjective (ζ : X) : Function.Surjective (piU ζ) := QuotientGroup.mk'_surjective _

theorem center_UZ_eq_bot {ζ : X} (hs : IsSimpleGroup (UZ ζ)) : center (UZ ζ) = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (UZ ζ)) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative (UZ ζ) := ⟨⟨fun a b => mem_center_iff.mp (h ▸ mem_top b) a⟩⟩
    have hp := (Group.is_simple_iff_prime_card (α := UZ ζ)).mp hs
    have : Fact (Nat.card (UZ ζ)).Prime := ⟨hp⟩
    have : IsCyclic (UZ ζ) := isCyclic_of_prime_card rfl
    have hU : IsMulCommutative ↥(normalClosure ({ζ} : Set X)) :=
      (piU ζ).isMulCommutative_of_isCyclic_of_ker_le_center (by rw [QuotientGroup.ker_mk'])
    have htop : center ↥(normalClosure ({ζ} : Set X)) = ⊤ :=
      eq_top_iff.mpr fun a _ => mem_center_iff.mpr fun b => hU.is_comm.comm b a
    obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
    obtain ⟨a, rfl⟩ := piU_surjective ζ a
    obtain ⟨b, rfl⟩ := piU_surjective ζ b
    apply hab
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, htop]
    exact mem_top _

theorem conj_injective {ζ : X} (hs : IsSimpleGroup (UZ ζ)) :
    Function.Injective (MulAut.conj : UZ ζ →* MulAut (UZ ζ)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [mem_bot]
  have hc : a ∈ center (UZ ζ) := mem_center_iff.mpr fun b => by
    have h := congrArg (fun φ : MulAut (UZ ζ) => φ b) (MonoidHom.mem_ker.mp ha)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc b * a = a * b * a⁻¹ * a := by rw [h]
      _ = a * b := by group
  rw [center_UZ_eq_bot hs, mem_bot] at hc
  exact hc

@[expose] noncomputable def Finn (ζ : X) (F : Subgroup X) : Subgroup X :=
  F ⊓ (OuterAutomorphisms.inner (UZ ζ)).comap (SmithConf.conjAut ζ)

theorem Finn_le (ζ : X) (F : Subgroup X) : Finn ζ F ≤ F := inf_le_left

theorem conjAut_apply (ζ : X) (x : X) (u : ↥(normalClosure ({ζ} : Set X))) :
    SmithConf.conjAut ζ x (piU ζ u) =
      piU ζ ⟨x * u * x⁻¹, normalClosure_normal.conj_mem _ u.2 x⟩ := by
  rfl

variable {ζ : X} {F : Subgroup X}

theorem conjAut_of_mem_U (u : ↥(normalClosure ({ζ} : Set X))) :
    SmithConf.conjAut ζ (u : X) = MulAut.conj (piU ζ u) := by
  ext ℓ
  obtain ⟨v, rfl⟩ := piU_surjective ζ ℓ
  rw [conjAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

namespace SmithConf

variable (hs : IsSimpleGroup (UZ ζ))

@[expose] noncomputable def iota : ↥(Finn ζ F) →* UZ ζ :=
  (MonoidHom.ofInjective (conj_injective hs)).symm.toMonoidHom.comp
    (((SmithConf.conjAut ζ).comp (Finn ζ F).subtype).codRestrict
      (MulAut.conj : UZ ζ →* MulAut (UZ ζ)).range (fun f => (mem_inf.mp f.2).2))

theorem conj_iota (f : ↥(Finn ζ F)) :
    MulAut.conj (iota hs f) = SmithConf.conjAut ζ (f : X) :=
  MonoidHom.apply_ofInjective_symm (conj_injective hs) _

theorem iota_conj (f : ↥(Finn ζ F)) (u : ↥(normalClosure ({ζ} : Set X))) :
    iota hs f * piU ζ u * (iota hs f)⁻¹ =
      piU ζ ⟨(f : X) * u * (f : X)⁻¹, normalClosure_normal.conj_mem _ u.2 _⟩ := by
  rw [← conjAut_apply, ← conj_iota hs f, MulAut.conj_apply]

end SmithConf

namespace SmithConf

variable (hC : SmithConf ζ F) (hs : IsSimpleGroup (UZ ζ))
include hC hs

theorem iota_injective [Finite X] : Function.Injective (iota (F := F) hs) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro f hf
  rw [mem_bot]
  have h1 : SmithConf.conjAut ζ (f : X) = 1 := by
    rw [← conj_iota hs f, MonoidHom.mem_ker.mp hf, map_one]
  exact Subtype.ext (hC.eq_one_of_conjAut_eq_one hs (Finn_le ζ F f.2) h1)

omit hC in
theorem iota_of_mem_U (f : ↥(Finn ζ F)) (hfU : (f : X) ∈ normalClosure ({ζ} : Set X)) :
    iota hs f = piU ζ ⟨f, hfU⟩ := by
  apply conj_injective hs
  rw [conj_iota hs f]
  ext ℓ
  obtain ⟨u, rfl⟩ := piU_surjective ζ ℓ
  rw [conjAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

omit hs in
theorem zeta_mem_Finn : ζ ∈ Finn ζ F := by
  refine ⟨hC.hyp.zeta_mem, ?_⟩
  change SmithConf.conjAut ζ ζ ∈ (MulAut.conj : UZ ζ →* MulAut (UZ ζ)).range
  refine ⟨piU ζ (zetaU ζ), ?_⟩
  ext ℓ
  obtain ⟨u, rfl⟩ := piU_surjective ζ ℓ
  rw [conjAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem exists_lift_of_comm {c : UZ ζ} (hc : c * piU ζ (zetaU ζ) = piU ζ (zetaU ζ) * c) :
    ∃ u : ↥(normalClosure ({ζ} : Set X)), piU ζ u = c ∧ (u : X) * ζ = ζ * u := by
  obtain ⟨u, rfl⟩ := piU_surjective ζ c
  refine ⟨u, rfl, ?_⟩
  have hζ := not_mem_ZU_of_simple hs
  have h1 : u * zetaU ζ * u⁻¹ * (zetaU ζ)⁻¹ ∈ center ↥(normalClosure ({ζ} : Set X)) := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_mul, map_mul,
      map_inv, map_inv, hc]
    group
  have hw : ((u * zetaU ζ * u⁻¹ * (zetaU ζ)⁻¹ : ↥(normalClosure ({ζ} : Set X))) : X) ∈ ZU ζ :=
    ⟨_, h1, rfl⟩
  have h2 := hC.star.eq_one_of_mul_mem_center hζ (y := (u : X) * ζ * (u : X)⁻¹)
    (isConj_iff.mpr ⟨u, rfl⟩) hw (by
      change (u : X) * ζ * (u : X)⁻¹ = (u : X) * ζ * (u : X)⁻¹ * ζ⁻¹ * ζ
      group)
  change (u : X) * ζ * (u : X)⁻¹ * ζ⁻¹ = 1 at h2
  calc (u : X) * ζ = (u : X) * ζ * (u : X)⁻¹ * ζ⁻¹ * (ζ * u) := by group
    _ = ζ * u := by rw [h2, one_mul]

omit hs in
theorem conj_mem_Finn {u : X} (huU : u ∈ normalClosure ({ζ} : Set X)) (hu : u * ζ = ζ * u)
    {f : X} (hf : f ∈ Finn ζ F) : u * f * u⁻¹ ∈ Finn ζ F := by
  refine ⟨hC.hyp.conj_mem u (mem_centralizer_singleton_iff.mpr hu) f hf.1, ?_⟩
  change SmithConf.conjAut ζ (u * f * u⁻¹) ∈ OuterAutomorphisms.inner (UZ ζ)
  rw [map_mul, map_mul, map_inv]
  have hu' : SmithConf.conjAut ζ u ∈ OuterAutomorphisms.inner (UZ ζ) := by
    refine ⟨piU ζ ⟨u, huU⟩, ?_⟩
    ext ℓ
    obtain ⟨v, rfl⟩ := piU_surjective ζ ℓ
    rw [conjAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  exact mul_mem (mul_mem hu' hf.2) (inv_mem hu')

theorem iota_conj_mem {u : ↥(normalClosure ({ζ} : Set X))} (hu : (u : X) * ζ = ζ * u)
    (f : ↥(Finn ζ F)) :
    iota hs ⟨(u : X) * f * (u : X)⁻¹, hC.conj_mem_Finn u.2 hu f.2⟩ =
      piU ζ u * iota hs f * (piU ζ u)⁻¹ := by
  apply conj_injective hs
  rw [conj_iota hs]
  change SmithConf.conjAut ζ ((u : X) * f * (u : X)⁻¹) =
    MulAut.conj (piU ζ u * iota hs f * (piU ζ u)⁻¹)
  simp only [map_mul, map_inv, conj_iota, conjAut_of_mem_U]

omit hC in
theorem iota_comm_zeta (f : ↥(Finn ζ F)) (hfz : (f : X) * ζ = ζ * f) :
    iota hs f * piU ζ (zetaU ζ) = piU ζ (zetaU ζ) * iota hs f := by
  have h := iota_conj hs f (zetaU ζ)
  have e : (⟨(f : X) * ζ * (f : X)⁻¹, normalClosure_normal.conj_mem _ (zetaU ζ).2 _⟩ :
      ↥(normalClosure ({ζ} : Set X))) = zetaU ζ := Subtype.ext (by
    change (f : X) * ζ * (f : X)⁻¹ = ζ
    rw [hfz]; group)
  change iota hs f * piU ζ (zetaU ζ) * (iota hs f)⁻¹ = piU ζ ⟨(f : X) * ζ * (f : X)⁻¹, _⟩ at h
  rw [e] at h
  calc iota hs f * piU ζ (zetaU ζ) = iota hs f * piU ζ (zetaU ζ) * (iota hs f)⁻¹ * iota hs f := by
        group
    _ = piU ζ (zetaU ζ) * iota hs f := by rw [h]

end SmithConf

theorem exists_card_extraspecial {P : Type*} [Group P] [Finite P]
    (hP : IsExtraspecialPGroup 2 P) : ∃ w : ℕ, Nat.card P = 2 ^ (1 + 2 * w) := by
  let _ := GroupTheory.extraspecialQuotientModule hP
  have : Module.Finite (ZMod 2) (Additive (Abelianization P)) := Module.Finite.of_finite
  have hnd := RankThree.Literature.FSmith.extraspecialQuadForm_nondegenerate hP
  have halt : (RankThree.Literature.FSmith.extraspecialQuadForm hP).polarBilin.IsAlt :=
    fun v => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact RankThree.OrthogonalInvolutions.polar_self_eq_zero _ v
  obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank halt hnd
  refine ⟨m, ?_⟩
  have h1 := card_eq_card_quotient_mul_card_subgroup (commutator P)
  have h2 : Nat.card (P ⧸ commutator P) = 2 ^ (m + m) := by
    change Nat.card (Additive (Abelianization P)) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hm]
  rw [h1, h2, hP.2.1, hP.2.2.2]
  ring

namespace SmithConf

variable [Finite X] (hC : SmithConf ζ F)
include hC

theorem card_le_mul_card_Finn {k : ℕ}
    (hk : ∀ H : Subgroup (OuterAutomorphisms.Outer (UZ ζ)), (∀ h ∈ H, h * h = 1) →
      Nat.card H ≤ k) :
    Nat.card F ≤ k * Nat.card (Finn ζ F) := by
  set β : ↥F →* OuterAutomorphisms.Outer (UZ ζ) :=
    (QuotientGroup.mk' (OuterAutomorphisms.inner (UZ ζ))).comp
      ((SmithConf.conjAut ζ).comp F.subtype) with hβ
  have hker : β.ker = (Finn ζ F).subgroupOf F := by
    ext f
    rw [MonoidHom.mem_ker, hβ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact ⟨fun h => ⟨f.2, h⟩, fun h => h.2⟩
  have hrange : ∀ h ∈ β.range, h * h = 1 := by
    rintro _ ⟨f, rfl⟩
    rw [← map_mul, ← MonoidHom.mem_ker, hker, mem_subgroupOf]
    have hsq := RankThree.Literature.FSmith.sq_mem_center hC.hyp.extraspecial f
    rw [pow_two] at hsq
    rcases (hC.mem_center_F_iff (f * f).2).mp hsq with h | h
    · rw [show ((f * f : ↥F) : X) = 1 from h]
      exact one_mem _
    · rw [show ((f * f : ↥F) : X) = ζ from h]
      exact hC.zeta_mem_Finn
  have h1 := card_mul_index β.ker
  rw [index_ker, hker] at h1
  have h2 : Nat.card ((Finn ζ F).subgroupOf F) = Nat.card (Finn ζ F) :=
    Nat.card_congr (subgroupOfEquivOfLe (Finn_le ζ F)).toEquiv
  rw [h2] at h1
  calc Nat.card F = Nat.card (Finn ζ F) * Nat.card β.range := by
        rw [← h1]
    _ ≤ Nat.card (Finn ζ F) * k := Nat.mul_le_mul_left _ (hk _ hrange)
    _ = k * Nat.card (Finn ζ F) := mul_comm _ _

end SmithConf

end S63

end CFSG.LargeExtraspecial
