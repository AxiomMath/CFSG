module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107E32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Over
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

section Lr

variable {G : Type} [Group G]

@[expose] def lrSub (L S : Subgroup G) (hSN : S ≤ normalizer (L : Set G)) {r : G} (hrS : r ∈ S)
    (hr2 : r * r = 1) : Subgroup G where
  carrier := {x | ∃ l ∈ S ⊓ L, x = l ∨ x = l * r}
  one_mem' := ⟨1, Subgroup.one_mem _, Or.inl rfl⟩
  mul_mem' := by
    have hc : ∀ l ∈ S ⊓ L, r * l * r ∈ S ⊓ L := by
      intro l hl
      obtain ⟨hlS, hlL⟩ := Subgroup.mem_inf.1 hl
      refine Subgroup.mem_inf.2 ⟨S.mul_mem (S.mul_mem hrS hlS) hrS, ?_⟩
      have h := (Subgroup.mem_normalizer_iff.1 (hSN hrS) l).1 hlL
      rwa [inv_eq_of_mul_eq_one_right hr2] at h
    rintro a b ⟨l1, hl1, ha⟩ ⟨l2, hl2, hb⟩
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
    · exact ⟨l1 * l2, (S ⊓ L).mul_mem hl1 hl2, Or.inl rfl⟩
    · exact ⟨l1 * l2, (S ⊓ L).mul_mem hl1 hl2, Or.inr (mul_assoc _ _ _).symm⟩
    · refine ⟨l1 * (r * l2 * r), (S ⊓ L).mul_mem hl1 (hc l2 hl2), Or.inr ?_⟩
      simp only [mul_assoc, hr2, mul_one]
    · refine ⟨l1 * (r * l2 * r), (S ⊓ L).mul_mem hl1 (hc l2 hl2), Or.inl ?_⟩
      simp only [mul_assoc]
  inv_mem' := by
    have hc : ∀ l ∈ S ⊓ L, r * l * r ∈ S ⊓ L := by
      intro l hl
      obtain ⟨hlS, hlL⟩ := Subgroup.mem_inf.1 hl
      refine Subgroup.mem_inf.2 ⟨S.mul_mem (S.mul_mem hrS hlS) hrS, ?_⟩
      have h := (Subgroup.mem_normalizer_iff.1 (hSN hrS) l).1 hlL
      rwa [inv_eq_of_mul_eq_one_right hr2] at h
    rintro a ⟨l, hl, ha⟩
    rcases ha with ha | ha <;> rw [ha]
    · exact ⟨l⁻¹, (S ⊓ L).inv_mem hl, Or.inl rfl⟩
    · refine ⟨r * l⁻¹ * r, hc _ ((S ⊓ L).inv_mem hl), Or.inr ?_⟩
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hr2]
      simp only [mul_assoc, hr2, mul_one]

variable {L S : Subgroup G} {hSN : S ≤ normalizer (L : Set G)} {r : G} {hrS : r ∈ S}
  {hr2 : r * r = 1}

theorem inf_le_lrSub : S ⊓ L ≤ lrSub L S hSN hrS hr2 := fun l hl => ⟨l, hl, Or.inl rfl⟩

theorem lrSub_le : lrSub L S hSN hrS hr2 ≤ S := by
  rintro x ⟨l, hl, rfl | rfl⟩
  · exact (Subgroup.mem_inf.1 hl).1
  · exact S.mul_mem (Subgroup.mem_inf.1 hl).1 hrS

theorem exists_char {N : Subgroup G} {t : G} (htS : t ∈ S) (htc : ∀ x ∈ S, x * t = t * x)
    (ht2 : t * t = 1) (hNS : N ≤ S) (htN : t ∉ N) (hcov : ∀ x ∈ S, x ∈ N ∨ x * t ∈ N) :
    ∃ c : ↥S →* ℤˣ, (∀ x : ↥S, c x = 1 ↔ (x : G) ∈ N) ∧ c ⟨t, htS⟩ = -1 := by
  classical
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  refine ⟨{ toFun := fun x => if (x : G) ∈ N then 1 else -1
            map_one' := if_pos N.one_mem
            map_mul' := ?_ }, ?_, ?_⟩
  · intro x y
    show (if ((x : G) * (y : G)) ∈ N then (1 : ℤˣ) else -1) =
      (if (x : G) ∈ N then 1 else -1) * (if (y : G) ∈ N then 1 else -1)
    by_cases hx : (x : G) ∈ N <;> by_cases hy : (y : G) ∈ N
    · have h : (x : G) * y ∈ N := N.mul_mem hx hy
      simp [hx, hy, h]
    · have h : (x : G) * y ∉ N := fun h => hy (by simpa using N.mul_mem (N.inv_mem hx) h)
      simp [hx, hy, h]
    · have h : (x : G) * y ∉ N := fun h => hx (by simpa using N.mul_mem h (N.inv_mem hy))
      simp [hx, hy, h]
    · have hx' := (hcov x x.2).resolve_left hx
      have hy' := (hcov y y.2).resolve_left hy
      have h : (x : G) * y ∈ N := by
        have h := N.mul_mem hx' hy'
        have e : (x : G) * t * ((y : G) * t) = (x : G) * y := by
          calc (x : G) * t * ((y : G) * t) = (x : G) * (t * (y : G)) * t := by
                simp only [mul_assoc]
            _ = (x : G) * ((y : G) * t) * t := by rw [← htc y y.2]
            _ = (x : G) * (y : G) * (t * t) := by simp only [mul_assoc]
            _ = (x : G) * y := by rw [ht2, mul_one]
        rwa [e] at h
      simp [hx, hy, h]
  · intro x
    show (if (x : G) ∈ N then (1 : ℤˣ) else -1) = 1 ↔ _
    by_cases hx : (x : G) ∈ N
    · simp [hx]
    · simp [hx, hne]
  · show (if t ∈ N then (1 : ℤˣ) else -1) = -1
    exact if_neg htN

end Lr

namespace PspFrame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {F : PspFrame L} {t : G}
  {S : Subgroup G} (h : Setup107 L t S)

namespace Setup107

section Split

variable
  (hFP : F.img (S ⊓ L) = QT0.originalSubgroup) {r : G}
  (hrS : r ∈ S) (hr2 : r * r = 1) (hrT0 : F.phiG r ∉ QT0.originalSubgroup)

include h hFP hrT0 in
theorem t_not_mem_lr : t ∉ lrSub L S h.S_le_N hrS hr2 := by
  rintro ⟨l, hl, e | e⟩
  · obtain ⟨hlS, hlL⟩ := Subgroup.mem_inf.1 hl
    have htL : t ∈ L := e ▸ hlL
    have h1 : F.ψ ⟨t, htL⟩ = 1 := by
      rw [← F.phiG_psi ⟨t, htL⟩]
      exact h.phiG_t
    have h2 := F.ψ_injective (h1.trans (map_one F.ψ).symm)
    exact h.t_ne (by simpa using congrArg Subtype.val h2)
  · obtain ⟨hlS, hlL⟩ := Subgroup.mem_inf.1 hl
    have h1 : F.phiG t = F.phiG l * F.phiG r := by
      rw [e]
      exact F.phiG_mul (h.S_le_N hlS) (h.S_le_N hrS)
    rw [h.phiG_t, F.phiG_psi ⟨l, hlL⟩] at h1
    have h2 : F.phiG r = (F.ψ ⟨l, hlL⟩)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
    apply hrT0
    rw [h2, ← hFP]
    exact (F.img (S ⊓ L)).inv_mem (PspFrame.psi_mem_img.2 hl)

include h hFP hrT0 in
theorem cover_lr {x : G} (hx : x ∈ S) :
    x ∈ lrSub L S h.S_le_N hrS hr2 ∨ x * t ∈ lrSub L S h.S_le_N hrS hr2 := by
  have hN := h.S_le_N
  have hxim : F.phiG x ∈ F.imgS S S := (F.mem_imgS hN).2 ⟨x, hx, hx, rfl⟩
  have hrim : F.phiG r ∈ F.imgS S S := (F.mem_imgS hN).2 ⟨r, hrS, hrS, rfl⟩
  have hlift : ∀ a ∈ QT0.originalSubgroup, ∃ l ∈ S ⊓ L, F.phiG l = a := by
    intro a ha
    rw [← hFP] at ha
    obtain ⟨l, hl, rfl⟩ := PspFrame.mem_img.1 ha
    exact ⟨l, hl, F.phiG_psi l⟩
  by_cases hxT0 : F.phiG x ∈ QT0.originalSubgroup
  · obtain ⟨l, hl, hlx⟩ := hlift _ hxT0
    rcases (h.phiG_eq_iff (Subgroup.mem_inf.1 hl).1 hx).1 hlx with e | e
    · exact Or.inl ⟨l, hl, Or.inl e⟩
    · refine Or.inr ⟨l, hl, Or.inl ?_⟩
      rw [e, mul_assoc, h.t_sq, mul_one]
  · obtain ⟨a, ha, hax⟩ := Mo107.exists_mul_over (h.T0_le_imgS hFP) (h.imgS_le_A (F := F) S)
      (h.isPGroup_imgS (F := F) (le_refl S)) hrim hrT0 hxim hxT0
    obtain ⟨l, hl, hla⟩ := hlift a ha
    have hlr : F.phiG (l * r) = F.phiG x := by
      rw [F.phiG_mul (hN (Subgroup.mem_inf.1 hl).1) (hN hrS), hla, hax]
    rcases (h.phiG_eq_iff (S.mul_mem (Subgroup.mem_inf.1 hl).1 hrS) hx).1 hlr with e | e
    · exact Or.inl ⟨l, hl, Or.inr e⟩
    · refine Or.inr ⟨l, hl, Or.inr ?_⟩
      rw [e, mul_assoc, h.t_sq, mul_one]

include h hFP hrS hr2 hrT0 in
theorem exists_split :
    ∃ Φ : ↥S →* P45 × ℤˣ, Function.Injective Φ ∧ (∀ x : ↥S, (Φ x).1 = F.phiG x) ∧
      Φ ⟨t, h.t_mem⟩ = (1, -1) ∧ (∀ x : ↥S, (x : G) ∈ L → (Φ x).2 = 1) ∧
      ∀ p ∈ F.imgS S S, ∀ e : ℤˣ, ∃ x : ↥S, Φ x = (p, e) := by
  have hcs : ∀ a b : ℤˣ, a ≠ b → a * -1 = b := by
    intro a b hab
    rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
      first | exact absurd rfl hab | simp
  obtain ⟨c, hc1, hct⟩ := exists_char h.t_mem h.t_comm h.t_sq
    (lrSub_le (hSN := h.S_le_N) (hrS := hrS) (hr2 := hr2))
    (h.t_not_mem_lr hFP hrS hr2 hrT0) fun x hx => h.cover_lr hFP hrS hr2 hrT0 hx
  let phiS : ↥S →* P45 := F.φ.comp (Subgroup.inclusion h.S_le_N)
  have hphiS : ∀ x : ↥S, phiS x = F.phiG x := fun x => (F.phiG_of_mem (h.S_le_N x.2)).symm
  refine ⟨phiS.prod c, ?_, fun x => hphiS x, ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : phiS x = phiS y := congrArg Prod.fst hxy
    have h2 : c x = c y := congrArg Prod.snd hxy
    rw [hphiS, hphiS] at h1
    rcases (h.phiG_eq_iff x.2 y.2).1 h1 with e | e
    · exact Subtype.ext e.symm
    · exfalso
      have e' : y = x * ⟨t, h.t_mem⟩ := Subtype.ext e
      rw [e', map_mul, hct] at h2
      rcases Int.units_eq_one_or (c x) with h3 | h3 <;> rw [h3] at h2 <;> revert h2 <;> decide
  · exact Prod.ext (by rw [MonoidHom.prod_apply, hphiS]; exact h.phiG_t) hct
  · intro x hx
    exact (hc1 x).2 (inf_le_lrSub (hSN := h.S_le_N) (hrS := hrS) (hr2 := hr2)
      (Subgroup.mem_inf.2 ⟨x.2, hx⟩))
  · intro p hp e
    obtain ⟨x0, -, hx0S, hx0p⟩ := (F.mem_imgS h.S_le_N).1 hp
    by_cases hce : c ⟨x0, hx0S⟩ = e
    · exact ⟨⟨x0, hx0S⟩, Prod.ext (by rw [MonoidHom.prod_apply, hphiS]; exact hx0p) hce⟩
    · refine ⟨⟨x0, hx0S⟩ * ⟨t, h.t_mem⟩, Prod.ext ?_ ?_⟩
      · rw [MonoidHom.prod_apply, hphiS]
        show F.phiG (x0 * t) = p
        rw [F.phiG_mul (h.S_le_N hx0S) h.t_mem_N, h.phiG_t, mul_one, hx0p]
      · show c (⟨x0, hx0S⟩ * ⟨t, h.t_mem⟩) = e
        rw [map_mul, hct]
        exact hcs _ _ hce

end Split

end Setup107

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
