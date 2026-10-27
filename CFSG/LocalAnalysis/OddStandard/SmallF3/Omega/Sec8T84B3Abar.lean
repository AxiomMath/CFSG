module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Ker
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B1Set

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace B89

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

@[expose] noncomputable def gE (hE : Sec8E G t L S z g B E) :
    ↥(L.subgroupOf (normalizer (B : Set G))) →* MulAut ↥E :=
  (RedAct.redHom (setupE hE)).comp (A3.toN hE.ctx)

@[expose] noncomputable def Abar (hE : Sec8E G t L S z g B E) : Subgroup (MulAut ↥E) :=
  (gE hE).range

theorem gE_eq (hE : Sec8E G t L S z g B E) (m : ↥(L.subgroupOf (normalizer (B : Set G)))) :
    gE hE m = rhoG hE ((m : ↥(normalizer (B : Set G))) : G) :=
  (rhoG_eq hE _).symm

theorem mem_subgroupOf_of {m : G} (hmL : m ∈ L) (hm : m ∈ normalizer (B : Set G)) :
    (⟨m, hm⟩ : ↥(normalizer (B : Set G))) ∈ L.subgroupOf (normalizer (B : Set G)) :=
  Subgroup.mem_subgroupOf.mpr hmL

theorem rhoG_mem_Abar (hE : Sec8E G t L S z g B E) {m : G} (hmL : m ∈ L)
    (hm : m ∈ normalizer (B : Set G)) : rhoG hE m ∈ Abar hE :=
  ⟨⟨⟨m, hm⟩, mem_subgroupOf_of hmL hm⟩, (gE_eq hE _).symm ▸ rfl⟩

theorem exists_of_mem_Abar (hE : Sec8E G t L S z g B E) {a : MulAut ↥E} (ha : a ∈ Abar hE) :
    ∃ m ∈ L, m ∈ normalizer (B : Set G) ∧ a = rhoG hE m := by
  obtain ⟨m, rfl⟩ := ha
  exact ⟨((m : ↥(normalizer (B : Set G))) : G), Subgroup.mem_subgroupOf.mp m.2, m.1.2,
    gE_eq hE m⟩

theorem fHom_eq_one_of_fix (hE : Sec8E G t L S z g B E) (h8B : Asc82Lemma8B)
    (m : ↥(L.subgroupOf (normalizer (B : Set G))))
    (hm : ∀ e : ↥E, (e : G) ∈ B → gE hE m e = e) : A3.fHom L B m = 1 := by
  ext x
  have h1 := rhoG_B hE h8B
    (sec8t84a1_L_norm_le hE.ctx ⟨Subgroup.mem_subgroupOf.mp m.2, m.1.2⟩).1
    ⟨(x : G), B_le_E hE x.2⟩ x.2
  rw [← gE_eq hE m, hm _ x.2] at h1
  rw [A3.fHom_apply_coe]
  simpa using h1.symm

theorem gE_eq_one_of_fHom (F : Sec8T84Base) (hE : Sec8E G t L S z g B E)
    (m : ↥(L.subgroupOf (normalizer (B : Set G)))) (hm : A3.fHom L B m = 1) :
    gE hE m = 1 := by
  have hmL : ((m : ↥(normalizer (B : Set G))) : G) ∈ L := Subgroup.mem_subgroupOf.mp m.2
  have hcent : ((m : ↥(normalizer (B : Set G))) : G) ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : ((m : ↥(normalizer (B : Set G))) : G) * b *
        ((m : ↥(normalizer (B : Set G))) : G)⁻¹ = b := by
      have h2 := A3.fHom_apply_coe L B m ⟨b, hb⟩
      rw [hm] at h2
      simpa using h2.symm
    calc b * ((m : ↥(normalizer (B : Set G))) : G)
        = (((m : ↥(normalizer (B : Set G))) : G) * b *
            ((m : ↥(normalizer (B : Set G))) : G)⁻¹) * ((m : ↥(normalizer (B : Set G))) : G) := by
          rw [h1]
      _ = ((m : ↥(normalizer (B : Set G))) : G) * b := by group
  have hmem : ((m : ↥(normalizer (B : Set G))) : G) ∈ B ⊔ centerIn L := by
    rw [← (A3.aut_B_of F hE.ctx).2.2]
    exact ⟨hmL, hcent⟩
  have hcomm : ∀ x ∈ B, ∀ y ∈ centerIn L, x * y = y * x := by
    intro x hx y hy
    exact (((sec4_mem_centerIn_iff y).mp hy).2 x (hE.ctx.B_le hx).1).symm
  obtain ⟨b, hb, c, hc, hbc⟩ := A3.exists_mul_of_comm hcomm hmem
  have hcO : c ∈ oddCoreIn (Nsub8 t B) :=
    A3.centerIn_le_oddCoreIn_N F.h8A hE.ctx (A3.isOm6M_ctx hE.ctx) hc
  have hbN : b ∈ Nsub8 t B := sec8t84a1_A_le_N (sec8t84a1_B_le_A hb)
  have hcN : c ∈ Nsub8 t B := (oddCoreIn_normal (Nsub8 t B)).1 hcO
  rw [gE_eq, hbc, rhoG_mul hE hbN hcN, rhoG_of_mem_E hE (B_le_E hE hb), rhoG_of_mem_O hE hcO,
    mul_one]

theorem ker_gE_eq (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) :
    (gE hE).ker = (A3.fHom L B).ker := by
  ext m
  exact ⟨fun h => fHom_eq_one_of_fix hE F.h8B m (fun e _ => by rw [show gE hE m = 1 from h]; rfl),
    fun h => gE_eq_one_of_fHom F hE m h⟩

theorem Abar_equiv_H1 (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) :
    Nonempty (↥(Abar hE) ≃* ↥(autIn L B)) :=
  ⟨(QuotientGroup.quotientKerEquivRange (gE hE)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_gE_eq F hE)).trans
      ((QuotientGroup.quotientKerEquivRange (A3.fHom L B)).trans
        (MulEquiv.subgroupCongr (A3.fHom_range L B))))⟩

theorem Abar_equiv_A6 (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) :
    Nonempty (↥(Abar hE) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e1⟩ := Abar_equiv_H1 F hE
  obtain ⟨e2⟩ := (A3.aut_B_of F hE.ctx).1
  exact ⟨e1.trans e2⟩

theorem Abar_faithful (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) {a : MulAut ↥E}
    (ha : a ∈ Abar hE) (h : ∀ e : ↥E, (e : G) ∈ B → a e = e) : a = 1 := by
  obtain ⟨m, rfl⟩ := ha
  have h1 : A3.fHom L B m = 1 := fHom_eq_one_of_fix hE F.h8B m h
  have h2 : m ∈ (A3.fHom L B).ker := h1
  rw [← ker_gE_eq F hE] at h2
  exact h2

theorem Abar_comm_u (hE : Sec8E G t L S z g B E) {a : MulAut ↥E} (ha : a ∈ Abar hE) :
    a * rhoG hE t = rhoG hE t * a := by
  obtain ⟨m, hmL, hm, rfl⟩ := exists_of_mem_Abar hE ha
  obtain ⟨hmN, hmC⟩ := sec8t84a1_L_norm_le hE.ctx ⟨hmL, hm⟩
  have hmt : m * t = t * m := Subgroup.mem_centralizer_singleton_iff.mp hmC
  rw [← rhoG_mul hE hmN t_mem_N, ← rhoG_mul hE t_mem_N hmN, hmt]

theorem u_not_mem_Abar (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) :
    rhoG hE t ∉ Abar hE := fun h =>
  rhoG_t_ne_one hE (Abar_faithful F hE h fun e he => (rhoG_t_fix_iff hE e).mpr he)

end B89

end CFSG.OddStandard.SmallF3.Omega
