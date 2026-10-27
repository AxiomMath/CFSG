module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Card
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Ker

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Sec10A2Psi (S : Subgroup G) (g : G) (K1 K2 : Subgroup G)
    (f : ↥(S ⊔ zpowers g) →* MulAut ↥(K1 ⊔ K2)) : Subgroup (MulAut ↥(K1 ⊔ K2)) :=
  (f.comp (Subgroup.inclusion (le_sup_left : S ≤ S ⊔ zpowers g))).range

variable [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} {g : G}
  {f : ↥(S ⊔ zpowers g) →* MulAut ↥(K1 ⊔ K2)}

theorem sec10A2_mem_Psi {y : ↥(S ⊔ zpowers g)} (hy : (y : G) ∈ S) :
    f y ∈ Sec10A2Psi S g K1 K2 f :=
  ⟨⟨(y : G), hy⟩, rfl⟩

theorem sec10A2_Psi_le : Sec10A2Psi S g K1 K2 f ≤ f.range := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, rfl⟩

theorem sec10A2_Phi_pgroup (hctx : Sec10A2Ctx G t L S z K1 K2 g) : IsPGroup 2 ↥f.range :=
  (sec10A2_T_pgroup hctx).of_surjective f.rangeRestrict f.rangeRestrict_surjective

theorem sec10A2_g_not_mem_S (h3 : Asc82Sec3Res10) (hctx : Sec10A2Ctx G t L S z K1 K2 g) :
    g ∉ S := fun hg => hctx.not_M (sec10A2_S_le_M h3 hctx.toSec10Ctx hg)

theorem sec10A2_Psi_relIndex (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g)
    (hfs : Sec10A2Act t z K1 K2 (S ⊔ zpowers g) f) :
    (Sec10A2Psi S g K1 K2 f).relIndex f.range = 2 := by
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
  have hgi : g⁻¹ ∈ S ⊔ zpowers g :=
    (S ⊔ zpowers g).inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  refine ⟨f ⟨g⁻¹, hgi⟩, ⟨_, rfl⟩, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    have hs' : f ⟨(s : G), Subgroup.mem_sup_left s.2⟩ = f ⟨g⁻¹, hgi⟩ := hs
    have hker : f ((⟨g⁻¹, hgi⟩ : ↥(S ⊔ zpowers g))⁻¹ *
        ⟨(s : G), Subgroup.mem_sup_left s.2⟩) = 1 := by
      rw [map_mul, map_inv, hs', inv_mul_cancel]
    have hS := sec10A2_ker_le_S h3 h hf hb hctx hfs hker
    have hS' : g * (s : G) ∈ S := by simpa using hS
    exact sec10A2_g_not_mem_S h3 hctx (by simpa using S.mul_mem hS' (S.inv_mem s.2))
  · rintro _ ⟨y, rfl⟩
    rcases sec10A2_T_cases hb hctx (y : G) y.2 with hy | hy
    · exact Or.inr (sec10A2_mem_Psi hy)
    · refine Or.inl ?_
      have := sec10A2_mem_Psi (f := f) (y := ⟨g⁻¹, hgi⟩ * y) hy
      rwa [map_mul] at this

theorem sec10A2_Psi_card (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g)
    (hfs : Sec10A2Act t z K1 K2 (S ⊔ zpowers g) f) :
    64 ≤ Nat.card ↥(Sec10A2Psi S g K1 K2 f) := by
  classical
  let fS : ↥S →* MulAut ↥(K1 ⊔ K2) :=
    f.comp (Subgroup.inclusion (le_sup_left : S ≤ S ⊔ zpowers g))
  have hmem : ∀ u : ↥fS.ker, ((u : ↥S) : G) ∈ ({1, t, z, t * z} : Finset G) := by
    intro u
    have h1 : f ⟨((u : ↥S) : G), Subgroup.mem_sup_left (u : ↥S).2⟩ = 1 := u.2
    have := sec10A2_ker_S h3 h hf hb hctx hfs
      (u := ⟨((u : ↥S) : G), Subgroup.mem_sup_left (u : ↥S).2⟩) (u : ↥S).2 h1
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hker : Nat.card ↥fS.ker ≤ 4 := by
    have hinj : Function.Injective (fun u : ↥fS.ker =>
        (⟨((u : ↥S) : G), hmem u⟩ : ↥({1, t, z, t * z} : Finset G))) := by
      intro u v huv
      have h' := congrArg Subtype.val huv
      exact Subtype.ext (Subtype.ext h')
    calc Nat.card ↥fS.ker ≤ Nat.card ↥({1, t, z, t * z} : Finset G) :=
          Nat.card_le_card_of_injective _ hinj
      _ = ({1, t, z, t * z} : Finset G).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ 4 := Finset.card_le_four
  have hS256 := sec10A2_card_S h hf hb hctx
  have h1 := Subgroup.card_ker_mul_card_range fS
  have hPsi : Nat.card ↥(Sec10A2Psi S g K1 K2 f) = Nat.card ↥fS.range := rfl
  by_contra hlt
  have hlt' : Nat.card ↥fS.range ≤ 63 := by omega
  have := Nat.mul_le_mul hker hlt'
  omega

theorem sec10A2_Psi_inner (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g)
    (hfs : Sec10A2Act t z K1 K2 (S ⊔ zpowers g) f) :
    ∀ q : ↥(K1 ⊔ K2), (q : G) ∈ twoCoreIn (K1 ⊔ K2) →
      MulAut.conj q ∈ Sec10A2Psi S g K1 K2 f := by
  intro q hq
  have hqS : (q : G) ∈ S := (sec10J_Q_le hf.pockets5 hb hctx.toSec10Ctx hq).1
  let y : ↥(S ⊔ zpowers g) := ⟨(q : G), Subgroup.mem_sup_left hqS⟩
  have hD := sec10A2_split h3 h hf hb hctx.toSec10Ctx
  have hfy : f y = MulAut.conj q := by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [hD.act_conj f hfs y q.2 k]
    rfl
  rw [← hfy]
  exact sec10A2_mem_Psi hqS

theorem sec10A2_Psi_swap (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g)
    (hfs : Sec10A2Act t z K1 K2 (S ⊔ zpowers g) f) :
    ∃ σ ∈ Sec10A2Psi S g K1 K2 f, ∀ k : ↥(K1 ⊔ K2), (k : G) ∈ K1 →
      ((σ k : ↥(K1 ⊔ K2)) : G) ∈ K2 := by
  obtain ⟨s, hsP, hsK⟩ := sec10A2_exists_swap_elem hf hb hctx.toSec10Ctx
  have hsS : s ∈ S := hsP.1
  have hsC : s ∈ L ⊓ centralizer ({z} : Set G) :=
    ⟨hsP.2, Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central s hsS)⟩
  have hsw := sec10A2_swap hf hb hctx.toSec10Ctx s hsC hsK
  let y : ↥(S ⊔ zpowers g) := ⟨s, Subgroup.mem_sup_left hsS⟩
  have hD := sec10A2_split h3 h hf hb hctx.toSec10Ctx
  refine ⟨f y, sec10A2_mem_Psi hsS, fun k hk => ?_⟩
  have hk2 : s * (k : G) * s⁻¹ ∈ K2 := hsw (k : G) hk
  have hact := hD.act_eq_of_spec f hfs (y := y) (k := k)
    (k' := ⟨s * (k : G) * s⁻¹, Subgroup.mem_sup_right hk2⟩) (n := 1)
    (oddCoreIn (secK0 t z)).one_mem (by simp [y])
  rw [hact]
  exact hk2

end CFSG.OddStandard.SmallF3.Omega
