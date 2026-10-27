module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.B69K

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Cooperstein.Coordinator

structure AltNatData {S : Type} [CommGroup S] (G Lt : Subgroup (MulAut S)) (hLG : Lt ≤ G) (m : ℕ) where
  θ : ↥G →* Equiv.Perm (Fin m)
  π : S ≃* Multiplicative (altHeart m)
  inj : Function.Injective θ
  alt_le : alternatingGroup (Fin m) ≤ (θ.comp (Subgroup.inclusion hLG)).range
  equiv : ∀ (g : ↥G) (s : S),
    Multiplicative.toAdd (π ((g : MulAut S) s)) = altAct (θ g) (Multiplicative.toAdd (π s))

section Stmts

variable {S : Type} [CommGroup S] [Finite S] {G Lt : Subgroup (MulAut S)} {hLG : Lt ≤ G} {m : ℕ}

theorem natdata_isInv_commV (L : Subgroup (MulAut S)) : XMod.IsInv ↥L (commV L) := by
  intro a l hl
  exact CFSG.Quasithin.commV_apply_mem_of_mem a.2 hl

theorem natdata_mem_normalizer {L : Subgroup (MulAut S)} {g : MulAut S} (hg : g ∈ L) :
    g ∈ Subgroup.normalizer (L : Set (MulAut S)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => L.mul_mem (L.mul_mem hg hy) (L.inv_mem hg), fun hy => by
    simpa [mul_assoc] using L.mul_mem (L.mul_mem (L.inv_mem hg) hy) hg⟩

theorem natdata_isInv_fixV (L : Subgroup (MulAut S)) : XMod.IsInv ↥L (fixV L) := by
  intro a s hs
  exact CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer (natdata_mem_normalizer a.2) hs

theorem natdata_false_of_trivial (L : Subgroup (MulAut S)) (hm : 9 ≤ m)
    (hiso : Nonempty (↥L ≃* alternatingGroup (Fin m)))
    (h : ∀ v : S, ∀ x ∈ L, x v = v) : False := by
  obtain ⟨e⟩ := hiso
  have hx : ∀ y : ↥L, y = 1 := fun y =>
    Subtype.ext (MulEquiv.ext fun v => by simpa using h v y.1 y.2)
  obtain ⟨a, b, c, hab, hbc, hac⟩ : ∃ a b c : Fin m, a ≠ b ∧ b ≠ c ∧ a ≠ c :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp, by simp, by simp⟩
  have hσ : Equiv.swap a b * Equiv.swap b c ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hbc]
    rfl
  have hσa : (Equiv.swap a b * Equiv.swap b c) a = b := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
  have ht : (⟨Equiv.swap a b * Equiv.swap b c, hσ⟩ : alternatingGroup (Fin m)) = 1 := by
    have h1 : e.symm ⟨Equiv.swap a b * Equiv.swap b c, hσ⟩ = 1 := hx _
    have h2 := congrArg e h1
    rwa [MulEquiv.apply_symm_apply, map_one] at h2
  have h3 : (Equiv.swap a b * Equiv.swap b c) a = a :=
    congrArg (fun z : alternatingGroup (Fin m) => (z : Equiv.Perm (Fin m)) a) ht
  rw [hσa] at h3
  exact hab h3.symm

theorem natural_data_of_gf2 (hGF2 : GF2EightFive) (hS2 : ∀ s : S, s ^ 2 = 1)
    (hF : Lt = quasithinGenFitting G) (hLG : Lt ≤ G) (hm : 9 ≤ m)
    (hiso : Nonempty (↥Lt ≃* alternatingGroup (Fin m)))
    (hoff : ∃ A, IsFFStarOffender G A) (hirr : XMod.IsIrrSec ↥Lt (⊥ : Subgroup S) ⊤) :
    Nonempty (AltNatData G Lt hLG m) := by
  have hA : IsAltNaturalSection Lt (commV G) m := by
    rcases hGF2 S hS2 G Lt hF m (Or.inr hm) hiso hoff with h | ⟨h7, -⟩
    · exact h
    · exfalso
      omega
  have hnat : IsAltNaturalSection Lt (commV Lt) m :=
    isAltNaturalSection_commV_of_le hLG (by omega) hA
  obtain ⟨θ, π', hπ'surj, hker, halt, hequiv, hinj⟩ :=
    exists_permRep_of_isAltNaturalSection hF hLG (by omega) (by omega) hiso hnat
  obtain ⟨-, hJ⟩ := hirr
  have hcomm : commV Lt = ⊤ := by
    rcases hJ (commV Lt) (natdata_isInv_commV Lt) bot_le le_top with h | h
    · have htriv : ∀ v : S, ∀ x ∈ Lt, x v = v := by
        intro v x hx
        have hmem := CFSG.HardMathSupport.Cooperstein.Coordinator.apply_mul_inv_mem_commV hx v
        rw [h, Subgroup.mem_bot] at hmem
        exact mul_inv_eq_one.mp hmem
      exact (natdata_false_of_trivial Lt hm hiso htriv).elim
    · exact h
  have hfix : fixV Lt = ⊥ := by
    rcases hJ (fixV Lt) (natdata_isInv_fixV Lt) bot_le le_top with h | h
    · exact h
    · have htriv : ∀ v : S, ∀ x ∈ Lt, x v = v := by
        intro v x hx
        have hv : v ∈ fixV Lt := by
          rw [h]
          exact Subgroup.mem_top v
        exact CFSG.Quasithin.mem_fixV.mp hv x hx
      exact (natdata_false_of_trivial Lt hm hiso htriv).elim
  obtain ⟨e1, he1⟩ : ∃ e1 : ↥(commV Lt) ≃* S, ∀ x : ↥(commV Lt), e1 x = (x : S) :=
    ⟨(MulEquiv.subgroupCongr hcomm).trans Subgroup.topEquiv, fun x => by
      first
        | rfl
        | simp [MulEquiv.trans_apply, Subgroup.topEquiv_apply, MulEquiv.subgroupCongr_apply]⟩
  have hbij : Function.Bijective (π'.comp e1.symm.toMonoidHom) := by
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_one]
      intro s hs
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hs
      have hmem : e1.symm s ∈ π'.ker := MonoidHom.mem_ker.mpr hs
      rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hfix, Subgroup.mem_bot] at hmem
      obtain ⟨-, h1⟩ := hmem
      calc s = e1 (e1.symm s) := (e1.apply_symm_apply s).symm
        _ = ((e1.symm s : ↥(commV Lt)) : S) := he1 (e1.symm s)
        _ = 1 := h1
    · intro y
      obtain ⟨u, hu⟩ := hπ'surj y
      refine ⟨e1 u, ?_⟩
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact hu
  obtain ⟨π, hπ⟩ : ∃ π : S ≃* Multiplicative (altHeart m), ∀ s, π s = π' (e1.symm s) :=
    ⟨MulEquiv.ofBijective _ hbij, fun s => by
      first
        | rfl
        | simp [MulEquiv.ofBijective_apply]⟩
  have hequivar : ∀ (g : ↥G) (s : S),
      Multiplicative.toAdd (π ((g : MulAut S) s)) = altAct (θ g) (Multiplicative.toAdd (π s)) := by
    intro g s
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π' (e1.symm s)))
    have huS : ((e1.symm s : ↥(commV Lt)) : S) = s :=
      (he1 (e1.symm s)).symm.trans (e1.apply_symm_apply s)
    have hvS : ((e1.symm ((g : MulAut S) s) : ↥(commV Lt)) : S) = (g : MulAut S) s :=
      (he1 (e1.symm ((g : MulAut S) s))).symm.trans (e1.apply_symm_apply _)
    have hE := hequiv g (e1.symm s) (e1.symm ((g : MulAut S) s)) (by rw [hvS, huS]) x hx.symm
    rw [hπ, hπ, hE, ← hx, altAct_mk]
  exact ⟨⟨θ, π, hinj, halt, hequivar⟩⟩

end Stmts

end CFSG.Quasithin.B69K
