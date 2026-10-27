module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDeletedSplit
public import CFSG.Quasithin.Background.G2SL2

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Basic

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem isInvariant_commGL_self (L : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) L (commGL L ⊤) := by
  intro g hg u hu
  have h1 := commSub_map (ρ := MonoidHom.id (V ≃ₗ[ZMod 2] V)) (H := L) (g := g)
    (Subgroup.le_normalizer hg) (⊤ : Submodule (ZMod 2) V)
  have h2 : (⊤ : Submodule (ZMod 2) V).map ((MonoidHom.id (V ≃ₗ[ZMod 2] V)) g : V →ₗ[ZMod 2] V) =
      ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top]
    exact (g : V ≃ₗ[ZMod 2] V).surjective
  rw [h2] at h1
  have h3 : commGL L ⊤ = (commGL L ⊤).map (g : V →ₗ[ZMod 2] V) := h1
  show g u ∈ commGL L ⊤
  rw [h3]
  exact ⟨u, hu, rfl⟩

theorem fixIn_eq_bot_of_inf_eq_bot {L : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
    (hZ : I ⊓ fixGL L = ⊥) : fixIn L I = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have h1 : (w : V) ∈ I ⊓ fixGL L := ⟨w.2, hw⟩
  rw [hZ] at h1
  exact (Submodule.mem_bot _).2 (Subtype.ext ((Submodule.mem_bot _).1 h1))

end Basic

section Excl

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] {F : Type} [Field F] [Fintype F]
  [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]

omit [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] in
theorem thetaL_surjective (L : Subgroup (V ≃ₗ[ZMod 2] V))
    (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F)) : Function.Surjective (thetaL L α) := by
  intro g
  obtain ⟨q, rfl⟩ := α.surjective g
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨l, rfl⟩

theorem not_natData_and_delData {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {L A A' : Subgroup (V ≃ₗ[ZMod 2] V)} (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F))
    (hN : NatData L A α) (hD : DelData n L A' α) : False := by
  obtain ⟨-, -, βN, hNc, -⟩ := hN
  obtain ⟨hn2, hZ, -, βD, ψ, hDc, hDθ, -, -⟩ := hD
  have hk : Fintype.card F = 4 := by rw [hF, hn2]; norm_num
  have hbot := fixIn_eq_bot_of_inf_eq_bot hZ
  let e : (↥(commGL L ⊤) ⧸ fixIn L (commGL L ⊤)) ≃ₗ[ZMod 2] ↥(commGL L ⊤) :=
    Submodule.quotEquivOfEqBot _ hbot
  refine natural_not_equiv_deleted hk
    ⟨(βN.symm.trans e.toAddEquiv).trans βD.toAddEquiv, fun g v => ?_⟩
  obtain ⟨l, rfl⟩ := thetaL_surjective L α g
  let w := βN.symm v
  let u : ↥(commGL L ⊤) := e w
  have hw : w = Submodule.Quotient.mk u := (e.symm_apply_apply w).symm.trans rfl
  let u' : ↥(commGL L ⊤) := ⟨(l : V ≃ₗ[ZMod 2] V) (u : V), isInvariant_commGL_self L l l.2 u u.2⟩
  have h1 : βN (Submodule.Quotient.mk u') =
      (thetaL L α l : Matrix (Fin 2) (Fin 2) F).mulVec v := by
    rw [hNc l u u' rfl, ← hw]
    simp [w]
  have h2 : (βN.symm.trans e.toAddEquiv).trans βD.toAddEquiv (thetaL L α l • v) = βD u' := by
    have : thetaL L α l • v = βN (Submodule.Quotient.mk u') := by rw [h1]; rfl
    rw [this]
    simp [e, u']
  rw [h2]
  have h3 := hDc ⟨l, Subgroup.mem_sup_left l.2⟩ u u' rfl
  rw [h3, hDθ l]
  show _ = SL2Modules.permAct _ ((βD (e (βN.symm v)) : _) : ℙ F (Fin 2 → F) → ZMod 2)
  rfl

end Excl

section VSplit

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F]

theorem odd_index_natData {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {L A : Subgroup (V ≃ₗ[ZMod 2] V)} (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F))
    (hc : Subgroup.center ↥L = ⊥) (hN : NatData L A α) : Odd (A.subgroupOf L).index := by
  classical
  obtain ⟨hAL, hAcard, -⟩ := hN
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hinj := thetaL_injective α hc
  have hsurj := thetaL_surjective L α
  have hLcard : Nat.card ↥L = Nat.card SL(2, F) :=
    Nat.card_congr (MulEquiv.ofBijective (thetaL L α) ⟨hinj, hsurj⟩).toEquiv
  have hSL : Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
    CFSG.Quasithin.SL2Model.card_SL2
  have hAsub : Nat.card ↥(A.subgroupOf L) = Nat.card F := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hAcard, Nat.card_eq_fintype_card]
  have hidx : (A.subgroupOf L).index = Nat.card F ^ 2 - 1 := by
    have h1 := (A.subgroupOf L).index_mul_card
    rw [hAsub, hLcard, hSL] at h1
    have hpos : 0 < Nat.card F := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm] at h1; exact h1)
  have hodd : Odd (A.subgroupOf L).index := by
    rw [hidx, Nat.card_eq_fintype_card, hF]
    have he : Even ((2 ^ n) ^ 2) := Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by norm_num⟩
    have h2 : 2 ≤ (2 ^ n) ^ 2 := by
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hn
      nlinarith
    rw [Nat.odd_iff]
    rw [Nat.even_iff] at he
    omega
  exact hodd

theorem V_split_natural {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {L A : Subgroup (V ≃ₗ[ZMod 2] V)} (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F))
    (hc : Subgroup.center ↥L = ⊥) (hN : NatData L A α) (hV : commGL L ⊤ ⊔ fixGL A = ⊤) :
    commGL L ⊤ ⊔ fixGL L = ⊤ := by
  classical
  have hodd := odd_index_natData hn hF α hc hN
  let π : V →ₗ[ZMod 2] (V ⧸ commGL L ⊤) := (commGL L ⊤).mkQ
  let ρE : Representation (ZMod 2) ↥L V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp L.subtype
  let ρM : Representation (ZMod 2) ↥L (V ⧸ commGL L ⊤) := 1
  have hπ : ∀ g e, π (ρE g e) = ρM g (π e) := by
    intro g e
    show Submodule.Quotient.mk ((g : V ≃ₗ[ZMod 2] V) e) = Submodule.Quotient.mk e
    rw [Submodule.Quotient.eq]
    exact mem_commSub_of (ρ := MonoidHom.id (V ≃ₗ[ZMod 2] V)) g.2 Submodule.mem_top
  have hsurjπ : LinearMap.range (π.comp (fixGL A).subtype) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hv : v ∈ commGL L ⊤ ⊔ fixGL A := by rw [hV]; trivial
    obtain ⟨i, hi, c, hc', rfl⟩ := Submodule.mem_sup.1 hv
    refine ⟨⟨c, hc'⟩, ?_⟩
    show Submodule.Quotient.mk c = Submodule.Quotient.mk (i + c)
    rw [Submodule.Quotient.eq]
    have : c - (i + c) = -i := by abel
    rw [this]
    exact Submodule.neg_mem _ hi
  obtain ⟨σ₀, hσ₀⟩ := LinearMap.exists_rightInverse_of_surjective (π.comp (fixGL A).subtype) hsurjπ
  let σ : (V ⧸ commGL L ⊤) →ₗ[ZMod 2] V := (fixGL A).subtype.comp σ₀
  have hσ : ∀ m, π (σ m) = m := fun m => by
    have := congrArg (fun f => f m) hσ₀
    exact this
  have hσT : ∀ t ∈ A.subgroupOf L, ∀ m, σ (ρM t m) = ρE t (σ m) := by
    intro t ht m
    have h1 : (σ₀ m : V) ∈ fixGL A := (σ₀ m).2
    exact (h1 t.1 ht).symm
  obtain ⟨j, hj1, hj2⟩ := equivariant_section_of_odd_index ρM ρE π hπ (A.subgroupOf L) hodd σ hσ hσT
  rw [eq_top_iff]
  intro v _
  have hjfix : ∀ m, j m ∈ fixGL L := fun m l hl => by
    have := hj2 ⟨l, hl⟩ m
    exact this.symm
  have hmem : v - j (π v) ∈ commGL L ⊤ := by
    have : π (v - j (π v)) = 0 := by rw [map_sub, hj1, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  have : v = (v - j (π v)) + j (π v) := by abel
  rw [this]
  exact Submodule.add_mem_sup hmem (hjfix _)

variable [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] in
theorem V_split_deleted {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {L A : Subgroup (V ≃ₗ[ZMod 2] V)} (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F))
    (hc : Subgroup.center ↥L = ⊥) (hD : DelData n L A α) :
    commGL L ⊤ ⊔ fixGL L = ⊤ := by
  classical
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  obtain ⟨hn2, -, -, β, ψ, hcompat, hψθ, hψL, -⟩ := hD
  have hk : Fintype.card F = 4 := by rw [hF, hn2]; norm_num
  have h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5 := by rw [card_projectiveLine, hk]
  have hcharF : CharP F 2 := charP_two_of_card_eq hF
  have hmemAlt : ∀ l : ↥L, ψ ⟨l, Subgroup.mem_sup_left l.2⟩ ∈ alternatingGroup (ℙ F (Fin 2 → F)) := by
    intro l
    rw [← hψL]
    exact ⟨⟨l, Subgroup.mem_sup_left l.2⟩, l.2, rfl⟩
  let ψL : ↥L →* ↥(alternatingGroup (ℙ F (Fin 2 → F))) :=
    ((ψ.comp (Subgroup.inclusion le_sup_left)).codRestrict _ hmemAlt)
  have hψLapp : ∀ l : ↥L, ((ψL l : ↥(alternatingGroup (ℙ F (Fin 2 → F)))) :
      Equiv.Perm (ℙ F (Fin 2 → F))) = ψ ⟨l, Subgroup.mem_sup_left l.2⟩ := fun l => rfl
  have hinjψL : Function.Injective ψL := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : ψ ⟨l, Subgroup.mem_sup_left l.2⟩ = 1 := by
      rw [← hψLapp, hl]; rfl
    rw [hψθ l] at h1
    have h2 : thetaL L α l = 1 := act_injective (k := F)
      (show MulAction.toPermHom SL(2, F) (ℙ F (Fin 2 → F)) (thetaL L α l) =
        MulAction.toPermHom SL(2, F) (ℙ F (Fin 2 → F)) 1 by rw [map_one]; exact h1)
    exact Subgroup.mem_bot.2 (thetaL_injective α hc (by rw [h2, map_one]))
  have hsurjψL : Function.Surjective ψL := by
    intro s
    have hs : (s : Equiv.Perm (ℙ F (Fin 2 → F))) ∈
        (L.subgroupOf (L ⊔ A)).map ψ := by rw [hψL]; exact s.2
    obtain ⟨x, hx, hxs⟩ := hs
    refine ⟨⟨x.1, hx⟩, Subtype.ext ?_⟩
    rw [hψLapp]
    exact hxs
  let eψ : ↥L ≃* ↥(alternatingGroup (ℙ F (Fin 2 → F))) := MulEquiv.ofBijective ψL ⟨hinjψL, hsurjψL⟩
  let ρV : Representation (ZMod 2) ↥(alternatingGroup (ℙ F (Fin 2 → F))) V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (L.subtype.comp eψ.symm.toMonoidHom)
  let ι : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))) →ₗ[ZMod 2] V :=
    (commGL L ⊤).subtype.comp β.symm.toLinearMap
  have hι : Function.Injective ι := (commGL L ⊤).injective_subtype.comp β.symm.injective
  have hιeq : ∀ s x, ι (deletedRep (alternatingGroup (ℙ F (Fin 2 → F))) (ℙ F (Fin 2 → F)) s x) =
      ρV s (ι x) := by
    intro s x
    obtain ⟨l, rfl⟩ := eψ.surjective s
    have hρ : ρV (eψ l) (ι x) = (l : V ≃ₗ[ZMod 2] V) (ι x) := by
      show ((eψ.symm (eψ l) : ↥L) : V ≃ₗ[ZMod 2] V) (ι x) = _
      rw [MulEquiv.symm_apply_apply]
    rw [hρ]
    let u : ↥(commGL L ⊤) := β.symm x
    let u' : ↥(commGL L ⊤) := ⟨(l : V ≃ₗ[ZMod 2] V) (u : V), isInvariant_commGL_self L l l.2 u u.2⟩
    have h1 := hcompat ⟨l, Subgroup.mem_sup_left l.2⟩ u u' rfl
    have h2 : β.symm (deletedRep (alternatingGroup (ℙ F (Fin 2 → F))) (ℙ F (Fin 2 → F)) (eψ l) x) = u' := by
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [deletedRep_apply, h1]
      have hperm : MulAction.toPerm (eψ l) = ψ ⟨l, Subgroup.mem_sup_left l.2⟩ :=
        Equiv.ext fun a => congrArg (fun σ : Equiv.Perm (ℙ F (Fin 2 → F)) => σ a) (hψLapp l)
      rw [hperm]
      simp only [u, LinearEquiv.apply_symm_apply]
    show ((β.symm (deletedRep _ _ (eψ l) x) : ↥(commGL L ⊤)) : V) = _
    rw [h2]
    rfl
  obtain ⟨P, hP1, hP2⟩ := deleted_retraction h5 ρV ι hι hιeq
  rw [eq_top_iff]
  intro v _
  have hk0 : P (v - ι (P v)) = 0 := by rw [map_sub, hP1, sub_self]
  have hkfix : v - ι (P v) ∈ fixGL L := by
    intro l hl
    have h1 : P ((l : V ≃ₗ[ZMod 2] V) (v - ι (P v))) = 0 := by
      have := hP2 (eψ ⟨l, hl⟩) (v - ι (P v))
      have hρ : ρV (eψ ⟨l, hl⟩) (v - ι (P v)) = l (v - ι (P v)) := by
        show ((eψ.symm (eψ ⟨l, hl⟩) : ↥L) : V ≃ₗ[ZMod 2] V) _ = _
        rw [MulEquiv.symm_apply_apply]
      rw [hρ, hk0] at this
      rw [this, map_zero]
    have hmem : l (v - ι (P v)) - (v - ι (P v)) ∈ commGL L ⊤ :=
      mem_commSub_of (ρ := MonoidHom.id (V ≃ₗ[ZMod 2] V)) hl Submodule.mem_top
    have h2 : P (l (v - ι (P v)) - (v - ι (P v))) = 0 := by rw [map_sub, h1, hk0, sub_zero]
    set y : ↥(commGL L ⊤) := ⟨_, hmem⟩ with hy
    have h3 : ι (β y) = l (v - ι (P v)) - (v - ι (P v)) := by
      show ((β.symm (β y) : ↥(commGL L ⊤)) : V) = _
      rw [LinearEquiv.symm_apply_apply]
    rw [← h3, hP1] at h2
    have h4 : β y = 0 := h2
    have h5' : y = 0 := β.injective (by rw [h4, map_zero])
    have : l (v - ι (P v)) - (v - ι (P v)) = 0 := by
      have := congrArg Subtype.val h5'
      exact this
    exact sub_eq_zero.1 this
  have hI : ι (P v) ∈ commGL L ⊤ := (β.symm (P v)).2
  have : v = ι (P v) + (v - ι (P v)) := by abel
  rw [this]
  exact Submodule.add_mem_sup hI hkfix

end VSplit

end CFSG.QuasithinUnique.Setup.Lift
