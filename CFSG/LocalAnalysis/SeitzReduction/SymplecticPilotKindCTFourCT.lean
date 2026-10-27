module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTRigid

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

theorem exists_plane_four_numeric : ∀ a b : Fin 9, ¬(a.val = 1 ∧ b.val = 5) →
    ¬(a.val = 5 ∧ b.val = 1) → ∃ k : Fin 4,
      (a.val / 2 ≠ k.val ∨ 8 ≤ a.val) ∧ ((a.val + 1) / 2 ≠ k.val ∨ 8 ≤ a.val + 1) ∧
        (b.val / 2 ≠ k.val ∨ 8 ≤ b.val) ∧ ((b.val + 1) / 2 ≠ k.val ∨ 8 ≤ b.val + 1) := by
  decide

theorem notMem_planeCoordsQ2_four {ε : ℕ} {a : Fin (2 * 4 + ε)} {k : Fin 4}
    (h : a.val / 2 ≠ k.val ∨ 8 ≤ a.val) : a ∉ planeCoordsQ2 ε ({k} : Finset (Fin 4)) := by
  rw [mem_planeCoordsQ2_iff]
  rintro ⟨hlt, h2⟩
  rw [Finset.mem_singleton] at h2
  have h3 := congrArg Fin.val h2
  simp only at h3
  omega

theorem exists_plane_notMem_four {ε m : ℕ} (h : m + 1 = 2 * 4 + ε) (hε : ε ≤ 1)
    (J : Finset (Fin m)) (hJ : J.card ≤ 2) (hJ₀ : ∀ a ∈ J, ∀ b ∈ J, ¬(a.val = 1 ∧ b.val = 5)) :
    ∃ k : Fin 4, ∀ j ∈ J, finCongr h j.castSucc ∉ planeCoordsQ2 ε {k} ∧
      finCongr h j.succ ∉ planeCoordsQ2 ε {k} := by
  have hm : m ≤ 8 := by omega
  have key : ∀ a b : Fin m, ¬(a.val = 1 ∧ b.val = 5) → ¬(a.val = 5 ∧ b.val = 1) →
      ∃ k : Fin 4, ∀ j : Fin m, (j = a ∨ j = b) →
        finCongr h j.castSucc ∉ planeCoordsQ2 ε {k} ∧ finCongr h j.succ ∉ planeCoordsQ2 ε {k} := by
    intro a b h1 h2
    obtain ⟨k, hka⟩ := exists_plane_four_numeric ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ h1 h2
    refine ⟨k, fun j hj => ?_⟩
    have hc : (finCongr h j.castSucc).val = j.val := by simp
    have hs : (finCongr h j.succ).val = j.val + 1 := by simp
    rcases hj with rfl | rfl
    · exact ⟨notMem_planeCoordsQ2_four (by rw [hc]; exact hka.1),
        notMem_planeCoordsQ2_four (by rw [hs]; exact hka.2.1)⟩
    · exact ⟨notMem_planeCoordsQ2_four (by rw [hc]; exact hka.2.2.1),
        notMem_planeCoordsQ2_four (by rw [hs]; exact hka.2.2.2)⟩
  rcases Nat.lt_or_ge J.card 2 with hlt | hge
  · rcases Nat.lt_or_ge J.card 1 with h0 | h1
    · have hJe : J = ∅ := Finset.card_eq_zero.1 (by omega)
      subst hJe
      exact ⟨0, fun j hj => by simp at hj⟩
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 (show J.card = 1 by omega)
      obtain ⟨k, hk⟩ := key a a (fun h' => by obtain ⟨h1, h2⟩ := h'; omega)
        (fun h' => by obtain ⟨h1, h2⟩ := h'; omega)
      exact ⟨k, fun j hj => hk j (Or.inl (Finset.mem_singleton.1 hj))⟩
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (show J.card = 2 by omega)
    obtain ⟨k, hk⟩ := key a b (hJ₀ a (by simp) b (by simp))
      (fun h' => hJ₀ b (by simp) a (by simp) ⟨h'.2, h'.1⟩)
    exact ⟨k, fun j hj => hk j (by simpa using hj)⟩

theorem map_levi_singleton_le {K : Type} [Field K] {N ε m : ℕ} (h : m + 1 = 2 * N + ε)
    (j : Fin m) :
    (CFSG.LieType.Universal.SpecialLinear.levi m K {j}).map (q2CastSL h).toMonoidHom ≤
      blockSpecialLinear ({finCongr h j.castSucc, finCongr h j.succ} :
        Finset (Fin (2 * N + ε))) := by
  rw [CFSG.LieType.Universal.SpecialLinear.levi, Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hi => ?_
  rw [Finset.mem_singleton] at hi
  subst hi
  rw [Subgroup.map_iSup]
  refine iSup_le fun s => ?_
  rintro _ ⟨x, hx, rfl⟩
  cases s
  · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ x).1 hx
    rw [MulEquiv.coe_toMonoidHom, q2CastSL_transvection]
    exact LinearPilot.transvection_mem_blockSpecialLinear _ (by simp) (by simp) c
  · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ x).1 hx
    rw [MulEquiv.coe_toMonoidHom, q2CastSL_transvection]
    exact LinearPilot.transvection_mem_blockSpecialLinear _ (by simp) (by simp) c

theorem subset_singleton_or_of_subset_pair {α : Type*} [DecidableEq α] {a b : α}
    {I : Finset α} (hI : I ⊆ {a, b}) (hne : I ≠ {a, b}) : I ⊆ {a} ∨ I ⊆ {b} := by
  by_cases hb : b ∈ I
  · right
    intro j hj
    rcases Finset.mem_insert.1 (hI hj) with rfl | h
    · exfalso
      exact hne (Finset.Subset.antisymm hI (by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hj
        · rw [Finset.mem_singleton.1 hx]
          exact hb))
    · exact h
  · left
    intro j hj
    rcases Finset.mem_insert.1 (hI hj) with rfl | h
    · exact Finset.mem_singleton_self _
    · rw [Finset.mem_singleton.1 h] at hj
      exact absurd hj hb

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {ε : ℕ} {e : L ≃* StatedSp 4 K}

theorem exists_ct_linRow_four_of_agree [Finite K] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hε : ε ≤ 1) (P : ∀ k : Fin 4, CtLinParam ε e k) (hagree : CtLinParamAgree P)
    (hcomm : ∀ x ∈ blockSpecialLinear ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))),
      ∀ y ∈ blockSpecialLinear ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))),
      ∀ (hx : x ∈ q2Block ε K {2}) (hy : y ∈ q2Block ε K {0}),
        Commute ((P 2).Φ ⟨x, hx⟩) ((P 0).Φ ⟨y, hy⟩)) :
    ∃ ψ : SpecialLinearGroup (Fin (2 * 4 + ε)) K →* G, ψ.range = spGlobal e ∧
      ψ.ker ≤ center (SpecialLinearGroup (Fin (2 * 4 + ε)) K) ∧
      CFSG.IsQuasisimple (spGlobal e) ∧ Odd (Nat.card (center (spGlobal e))) ∧
      LieModel (spGlobal e ⧸ center (spGlobal e)) .PSL (2 * 4 + ε) 2 f := by
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = 2 * 4 + ε := ⟨2 * 4 + ε - 1, by omega⟩
  have hm7 : 7 ≤ m := by omega
  set j₁ : Fin m := ⟨1, by omega⟩ with hj₁
  set j₅ : Fin m := ⟨5, by omega⟩ with hj₅
  have hj15 : j₁ ≠ j₅ := fun h => by simp [hj₁, hj₅, Fin.ext_iff] at h
  set J₀ : Finset (Fin m) := {j₁, j₅} with hJ₀def
  have hJ₀card : J₀.card = 2 := by rw [hJ₀def, Finset.card_pair hj15]
  have hgood : ∀ J : {J : Finset (Fin m) // J.card ≤ 2}, J.1 ≠ J₀ →
      ∀ a ∈ J.1, ∀ b ∈ J.1, ¬(a.val = 1 ∧ b.val = 5) := by
    intro J hJ a ha b hb ⟨h1, h5⟩
    apply hJ
    have ha' : a = j₁ := Fin.ext h1
    have hb' : b = j₅ := Fin.ext h5
    rw [ha'] at ha
    rw [hb'] at hb
    symm
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ha
      · rw [Finset.mem_singleton.1 hx]
        exact hb
    · rw [Finset.card_pair hj15]
      exact J.2
  choose kJ hkJ using fun (J : {J : Finset (Fin m) // J.card ≤ 2}) (h : J.1 ≠ J₀) =>
    exists_plane_notMem_four hm hε J.1 J.2 (hgood J h)
  have hKle : ∀ (J : {J : Finset (Fin m) // J.card ≤ 2}) (h : J.1 ≠ J₀)
      (x : SpecialLinearGroup (Fin (m + 1)) K),
      x ∈ (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J →
        q2CastSL hm x ∈ q2Block ε K {kJ J h} := by
    intro J h x hxJ
    have hx : x ∈ CFSG.LieType.Universal.SpecialLinear.levi m K J.1 := by
      rw [← CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
      exact hxJ
    exact map_levi_le_q2Block hm (hkJ J h) ⟨x, hx, rfl⟩
  have hmono : ∀ {I I' : Finset (Fin m)}, I ⊆ I' →
      CFSG.LieType.CurtisTits.levi (CFSG.LieType.Universal.SpecialLinear.rootGroup m K) I ≤
        CFSG.LieType.CurtisTits.levi (CFSG.LieType.Universal.SpecialLinear.rootGroup m K) I' :=
    fun h => biSup_mono fun j hj => h hj
  have hJ1card : ({j₁} : Finset (Fin m)).card ≤ 2 := by simp
  have hJ5card : ({j₅} : Finset (Fin m)).card ≤ 2 := by simp
  set J₁ : {J : Finset (Fin m) // J.card ≤ 2} := ⟨{j₁}, hJ1card⟩ with hJ₁
  set J₅ : {J : Finset (Fin m) // J.card ≤ 2} := ⟨{j₅}, hJ5card⟩ with hJ₅
  have hJ₁ne : J₁.1 ≠ J₀ := fun h => by
    have := congrArg Finset.card h
    rw [Finset.card_singleton, hJ₀def, Finset.card_pair hj15] at this
    omega
  have hJ₅ne : J₅.1 ≠ J₀ := fun h => by
    have := congrArg Finset.card h
    rw [Finset.card_singleton, hJ₀def, Finset.card_pair hj15] at this
    omega
  set A := (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J₁ with hA
  set B := (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J₅ with hB
  have hI₁ : ({finCongr hm j₁.castSucc, finCongr hm j₁.succ} : Finset (Fin (2 * 4 + ε))) =
      {ctF 4 ε 0, ctE 4 ε 1} := by
    rw [show finCongr hm j₁.castSucc = ctF 4 ε 0 from Fin.ext (by simp [hj₁]),
      show finCongr hm j₁.succ = ctE 4 ε 1 from Fin.ext (by simp [hj₁])]
  have hI₅ : ({finCongr hm j₅.castSucc, finCongr hm j₅.succ} : Finset (Fin (2 * 4 + ε))) =
      {ctF 4 ε 2, ctE 4 ε 3} := by
    rw [show finCongr hm j₅.castSucc = ctF 4 ε 2 from Fin.ext (by simp [hj₅]),
      show finCongr hm j₅.succ = ctE 4 ε 3 from Fin.ext (by simp [hj₅])]
  have hAblk : ∀ a ∈ A, q2CastSL hm a ∈
      blockSpecialLinear ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))) := by
    intro a ha
    have ha' : a ∈ CFSG.LieType.Universal.SpecialLinear.levi m K {j₁} := by
      rw [← CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
      exact ha
    rw [← hI₁]
    exact map_levi_singleton_le hm j₁ ⟨a, ha', rfl⟩
  have hBblk : ∀ b ∈ B, q2CastSL hm b ∈
      blockSpecialLinear ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))) := by
    intro b hb
    have hb' : b ∈ CFSG.LieType.Universal.SpecialLinear.levi m K {j₅} := by
      rw [← CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
      exact hb
    rw [← hI₅]
    exact map_levi_singleton_le hm j₅ ⟨b, hb', rfl⟩
  have hdisjI : Disjoint ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε)))
      {ctF 4 ε 2, ctE 4 ε 3} := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with h | h <;>
      · have := congrArg Fin.val h
        simp at this
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    intro a ha b hb
    have h1 := LinearPilot.commute_blockSpecialLinear_of_disjoint hdisjI (hAblk a ha) (hBblk b hb)
    have h2 : q2CastSL hm (a * b) = q2CastSL hm (b * a) := by
      rw [map_mul, map_mul]
      exact h1.eq
    exact (q2CastSL hm).injective h2
  have hdisjAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxB⟩
    have h1 := blockSpecialLinear_inf_le _ _ ⟨hAblk x hxA, hBblk x hxB⟩
    rw [Finset.disjoint_iff_inter_eq_empty.1 hdisjI, LinearPilot.blockSpecialLinear_empty] at h1
    rw [Subgroup.mem_bot]
    exact (q2CastSL hm).injective (by rw [map_one]; exact Subgroup.mem_bot.1 h1)
  have hlevi₀ : ∀ J : {J : Finset (Fin m) // J.card ≤ 2}, J.1 = J₀ →
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J = A ⊔ B := by
    intro J hJ
    change CFSG.LieType.CurtisTits.levi _ J.1 = _
    rw [hJ, hJ₀def]
    exact F4Pilot.levi_pair (CFSG.LieType.Universal.SpecialLinear.rootGroup m K) j₁ j₅
  have hsub2 : ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))) ⊆
      (planeCoordsQ2 ε ({2} : Finset (Fin 4)))ᶜ := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_compl]
    rcases ha with rfl | rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
  have hsub0 : ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))) ⊆
      (planeCoordsQ2 ε ({0} : Finset (Fin 4)))ᶜ := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_compl]
    rcases ha with rfl | rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
  set fA : A →* G := (P (kJ J₁ hJ₁ne)).Φ.comp
    (((q2CastSL hm).toMonoidHom.comp A.subtype).codRestrict _ fun a => hKle J₁ hJ₁ne a a.2)
    with hfA
  set gB : B →* G := (P (kJ J₅ hJ₅ne)).Φ.comp
    (((q2CastSL hm).toMonoidHom.comp B.subtype).codRestrict _ fun b => hKle J₅ hJ₅ne b b.2)
    with hgB
  have hfA2 : ∀ a : A, fA a = (P 2).Φ ⟨q2CastSL hm a,
      LinearPilot.blockSpecialLinear_mono hsub2 (hAblk a a.2)⟩ :=
    fun a => hagree _ _ _ (hKle J₁ hJ₁ne a a.2) _
  have hgB0 : ∀ b : B, gB b = (P 0).Φ ⟨q2CastSL hm b,
      LinearPilot.blockSpecialLinear_mono hsub0 (hBblk b b.2)⟩ :=
    fun b => hagree _ _ _ (hKle J₅ hJ₅ne b b.2) _
  have hfg : ∀ a b, Commute (fA a) (gB b) := by
    intro a b
    rw [hfA2, hgB0]
    exact hcomm _ (hAblk a a.2) _ (hBblk b b.2) _ _
  set ρ : ↥(A ⊔ B) →* G := F4Pilot.supLift hcommAB hdisjAB fA gB hfg with hρ
  have hρA : ∀ a : A, ρ ⟨a, mem_sup_left a.2⟩ = fA a := F4Pilot.supLift_apply_left _ _ hfg
  have hρB : ∀ b : B, ρ ⟨b, mem_sup_right b.2⟩ = gB b := F4Pilot.supLift_apply_right _ _ hfg
  obtain ⟨φ, hφne, hφ0⟩ : ∃ φ : ∀ J : {J : Finset (Fin m) // J.card ≤ 2},
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J →* G,
      (∀ (J : {J : Finset (Fin m) // J.card ≤ 2}) (h : J.1 ≠ J₀) x,
        φ J x = (P (kJ J h)).Φ ⟨q2CastSL hm x, hKle J h x x.2⟩) ∧
      ∀ (J : {J : Finset (Fin m) // J.card ≤ 2}) (h : J.1 = J₀) x,
        φ J x = ρ ⟨x, (hlevi₀ J h).le x.2⟩ := by
    refine ⟨fun J => if h : J.1 = J₀ then ρ.comp (Subgroup.inclusion (hlevi₀ J h).le)
      else (P (kJ J h)).Φ.comp (((q2CastSL hm).toMonoidHom.comp (Subgroup.subtype _)).codRestrict
        _ fun x => hKle J h x x.2), fun J h x => ?_, fun J h x => ?_⟩
    · simp only [dite_eq_right h]
      rfl
    · simp only [dite_eq_left h]
      rfl
  have hcomp : CFSG.LieType.CurtisTits.IsCompatible
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam φ := by
    intro I J hIJ x y hxy
    have hIJ' : I.1 ⊆ J.1 := hIJ
    by_cases hJ : J.1 = J₀
    · by_cases hI : I.1 = J₀
      · have hIJeq : I = J := Subtype.ext (hI.trans hJ.symm)
        subst hIJeq
        exact congrArg (φ I) (Subtype.ext hxy)
      · rw [hφne I hI, hφ0 J hJ]
        rcases subset_singleton_or_of_subset_pair (a := j₁) (b := j₅)
          (show I.1 ⊆ J₀ from hJ ▸ hIJ') hI with h1 | h5
        · have hyA : (y : SpecialLinearGroup (Fin (m + 1)) K) ∈ A :=
            hxy ▸ hmono h1 x.2
          have h2 := hρA ⟨y, hyA⟩
          refine Eq.trans ?_ h2.symm
          change _ = (P (kJ J₁ hJ₁ne)).Φ ⟨q2CastSL hm y, hKle J₁ hJ₁ne y hyA⟩
          rw [hagree (kJ I hI) (kJ J₁ hJ₁ne) _ (hKle I hI x x.2)
            (hxy ▸ hKle J₁ hJ₁ne y hyA)]
          congr 2
          rw [hxy]
        · have hyB : (y : SpecialLinearGroup (Fin (m + 1)) K) ∈ B :=
            hxy ▸ hmono h5 x.2
          have h2 := hρB ⟨y, hyB⟩
          refine Eq.trans ?_ h2.symm
          change _ = (P (kJ J₅ hJ₅ne)).Φ ⟨q2CastSL hm y, hKle J₅ hJ₅ne y hyB⟩
          rw [hagree (kJ I hI) (kJ J₅ hJ₅ne) _ (hKle I hI x x.2)
            (hxy ▸ hKle J₅ hJ₅ne y hyB)]
          congr 2
          rw [hxy]
    · have hI : I.1 ≠ J₀ := fun hI => hJ (Finset.eq_of_subset_of_card_le (hI ▸ hIJ')
        (J.2.trans hJ₀card.ge)).symm
      rw [hφne I hI, hφne J hJ]
      have hx' : q2CastSL hm (x : SpecialLinearGroup (Fin (m + 1)) K) ∈ q2Block ε K {kJ J hJ} :=
        hxy ▸ hKle J hJ y y.2
      rw [hagree (kJ I hI) (kJ J hJ) _ (hKle I hI x x.2) hx']
      congr 2
      rw [hxy]
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J →* G₀ :=
    fun J => (φ J).codRestrict G₀ (hle J) with hφ'
  have hcomp' : CFSG.LieType.CurtisTits.IsCompatible
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam φ' :=
    fun I J hIJ x y hxy => Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    have hm0 : 0 < m := by omega
    set j₀ : Fin m := ⟨0, hm0⟩ with hj₀
    set J₀' : {J : Finset (Fin m) // J.card ≤ 2} := ⟨{j₀}, by simp⟩ with hJ₀'
    have hJ₀'ne : J₀'.1 ≠ J₀ := fun h => by
      have := congrArg Finset.card h
      rw [Finset.card_singleton, hJ₀card] at this
      omega
    have hx₀ : SpecialLinearGroup.transvection
        (show j₀.castSucc < j₀.succ from Fin.castSucc_lt_succ).ne (1 : K) ∈
        (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J₀' := by
      have h1 : SpecialLinearGroup.transvection
          (show j₀.castSucc < j₀.succ from Fin.castSucc_lt_succ).ne (1 : K) ∈
          CFSG.LieType.CurtisTits.levi (CFSG.LieType.Universal.SpecialLinear.rootGroup m K)
            ({j₀} : Finset (Fin m)) := by
        rw [CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
        have hlevi : CFSG.LieType.Universal.SpecialLinear.fundamentalRootSubgroup m K j₀ true ≤
            CFSG.LieType.Universal.SpecialLinear.levi m K {j₀} :=
          le_iSup_of_le j₀ (le_iSup_of_le (Finset.mem_singleton_self j₀)
            (le_iSup (fun s => CFSG.LieType.Universal.SpecialLinear.fundamentalRootSubgroup m K j₀
              s) true))
        exact hlevi (CFSG.LieType.Universal.SpecialLinear.transvection_mem_rootSubgroup _ 1)
      exact h1
    refine ⟨J₀', ⟨_, hx₀⟩, fun h => ?_⟩
    have h1 : (P (kJ J₀' hJ₀'ne)).Φ ⟨q2CastSL hm (SpecialLinearGroup.transvection
        (show j₀.castSucc < j₀.succ from Fin.castSucc_lt_succ).ne (1 : K)),
        hKle J₀' hJ₀'ne _ hx₀⟩ = 1 := by
      have h0 := congrArg Subtype.val h
      rw [← hφne J₀' hJ₀'ne ⟨_, hx₀⟩]
      exact h0
    set p₀ : Fin 4 := ⟨0, by omega⟩ with hp₀
    have hpk : p₀ ≠ kJ J₀' hJ₀'ne := by
      intro hpk
      have h2 := (hkJ J₀' hJ₀'ne j₀ (Finset.mem_singleton_self j₀)).1
      rw [← hpk] at h2
      apply h2
      rw [mem_planeCoordsQ2_iff]
      exact ⟨by simp [hj₀], by simp [hp₀, hj₀]⟩
    have hy := longBlock_mem_spBlock (K := K) (show p₀ ∈ ({kJ J₀' hJ₀'ne} : Finset (Fin 4))ᶜ by
      simpa using hpk) (CFSG.LieType.Steinberg.sl2Upper 1)
    have hcast : q2CastSL hm (SpecialLinearGroup.transvection
        (show j₀.castSucc < j₀.succ from Fin.castSucc_lt_succ).ne (1 : K)) =
        ctEmbed ε (longBlock K 4 p₀ (CFSG.LieType.Steinberg.sl2Upper 1)) := by
      rw [q2CastSL_transvection, ctEmbed_longBlock, pairEmbed_sl2Upper]
      congr 1
    have h3 : (⟨q2CastSL hm (SpecialLinearGroup.transvection
        (show j₀.castSucc < j₀.succ from Fin.castSucc_lt_succ).ne (1 : K)), hKle J₀' hJ₀'ne _ hx₀⟩ :
        q2Block ε K {kJ J₀' hJ₀'ne}) = ⟨_, ctEmbed_mem_q2Block_iff.2 hy⟩ := Subtype.ext hcast
    rw [h3, (P (kJ J₀' hJ₀'ne)).N1 _ hy] at h1
    have h4 : e.symm (longBlock K 4 p₀ (CFSG.LieType.Steinberg.sl2Upper 1)) = 1 :=
      Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h4
    have h5 : CFSG.LieType.Steinberg.sl2Upper (1 : K) = 1 :=
      longBlock_injective p₀ (h4.trans (map_one _).symm)
    have h6 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h5
    simp [CFSG.LieType.Steinberg.sl2Upper] at h6
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 f :=
    ⟨Nat.prime_two, by omega, by omega, fun h => by simp at h; omega, fun h => by simp at h; omega⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_specialLinear.{0} (F := K) hadm hKc
      (by omega : 3 ≤ m)
  obtain ⟨ψ₀, hψ₀, hsurj, hker, hqs, -, -, hLM⟩ := hrec G₀ φ' hcomp' hgen' hnt
  set ψ : SpecialLinearGroup (Fin (2 * 4 + ε)) K →* G :=
    (G₀.subtype.comp ψ₀).comp (q2CastSL hm).symm.toMonoidHom with hψdef
  have hψrange : ψ.range = G₀ := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hψφ : ∀ J (x : (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J),
      ψ (q2CastSL hm x) = φ J x := by
    intro J x
    change ((ψ₀ ((q2CastSL hm).symm (q2CastSL hm x)) : G₀) : G) = _
    rw [MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val (hψ₀ J x)
  have hψker : ψ.ker ≤ center (SpecialLinearGroup (Fin (2 * 4 + ε)) K) := by
    intro z hz
    have hz₀ : (q2CastSL hm).symm z ∈ ψ₀.ker := by
      rw [MonoidHom.mem_ker]
      apply G₀.subtype_injective
      rw [map_one]
      exact hz
    have hc := hker hz₀
    rw [mem_center_iff] at hc ⊢
    intro g
    have := hc ((q2CastSL hm).symm g)
    apply (q2CastSL hm).symm.injective
    rw [map_mul, map_mul]
    exact this
  have hneLe : ∀ (J : {J : Finset (Fin m) // J.card ≤ 2}) (hJ : J.1 ≠ J₀)
      (x : SpecialLinearGroup (Fin (m + 1)) K)
      (hx : x ∈ (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J),
      (P (kJ J hJ)).Φ ⟨q2CastSL hm x, hKle J hJ x hx⟩ ∈ spGlobal e := by
    intro J hJ x hxJ
    set k := kJ J hJ with hk
    set A' : Subgroup (SpecialLinearGroup (Fin (2 * 4 + ε)) K) :=
      ((spGlobal e).comap (P k).Φ).map (q2Block ε K {k}).subtype with hA'
    have hAle : (CFSG.LieType.Universal.SpecialLinear.levi m K J.1).map
        (q2CastSL hm).toMonoidHom ≤ A' := by
      unfold CFSG.LieType.Universal.SpecialLinear.levi
      rw [Subgroup.map_iSup]
      refine iSup_le fun j => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hj => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun s => ?_
      rintro _ ⟨y, hy, rfl⟩
      have hab : finCongr hm j.castSucc ≠ finCongr hm j.succ := fun h =>
        (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne ((finCongr hm).injective h)
      have hba : (finCongr hm j.succ).val = (finCongr hm j.castSucc).val + 1 := by simp
      have key := (P k).transvection_adjacent_mem_spGlobal hK4 hε (by omega) hab hba
        (hkJ J hJ j hj).1 (hkJ J hJ j hj).2
      cases s
      · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ y).1 hy
        rw [MulEquiv.coe_toMonoidHom, q2CastSL_transvection]
        have hmem := transvection_mem_q2Block hab.symm (hkJ J hJ j hj).2 (hkJ J hJ j hj).1 c
        exact ⟨⟨_, hmem⟩, (key c (transvection_mem_q2Block hab (hkJ J hJ j hj).1
          (hkJ J hJ j hj).2 c) hmem).2, rfl⟩
      · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ y).1 hy
        rw [MulEquiv.coe_toMonoidHom, q2CastSL_transvection]
        have hmem := transvection_mem_q2Block hab (hkJ J hJ j hj).1 (hkJ J hJ j hj).2 c
        exact ⟨⟨_, hmem⟩, (key c hmem
          (transvection_mem_q2Block hab.symm (hkJ J hJ j hj).2 (hkJ J hJ j hj).1 c)).1, rfl⟩
    have hx : x ∈ CFSG.LieType.Universal.SpecialLinear.levi m K J.1 :=
      (CFSG.LieType.Universal.SpecialLinear.levi_rootGroup (m := m) (F := K) J.1) ▸ hxJ
    obtain ⟨y, hy, hyx⟩ := hAle ⟨_, hx, rfl⟩
    have hy' : (⟨q2CastSL hm x, hKle J hJ x hxJ⟩ : q2Block ε K {k}) = y := Subtype.ext hyx.symm
    rw [hy']
    exact hy
  have hG₀le : G₀ ≤ spGlobal e := by
    refine iSup_le fun J => ?_
    by_cases hJ : J.1 = J₀
    · have h1 : (φ J).range ≤ ρ.range := by
        rintro _ ⟨x, rfl⟩
        rw [hφ0 J hJ]
        exact ⟨_, rfl⟩
      refine h1.trans ?_
      rw [hρ, F4Pilot.range_supLift]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact hneLe J₁ hJ₁ne a a.2
      · rintro _ ⟨b, rfl⟩
        exact hneLe J₅ hJ₅ne b b.2
    · rintro _ ⟨x, rfl⟩
      rw [hφne J hJ]
      exact hneLe J hJ x x.2
  have hEk : ∀ k : Fin 4, neighbourCore e k ≤ G₀ := by
    intro k
    obtain ⟨j, hj⟩ : ∃ j : Fin m, j.val = 2 * k.val := ⟨⟨2 * k.val, by have := k.2; omega⟩, rfl⟩
    set J : {J : Finset (Fin m) // J.card ≤ 2} := ⟨{j}, by simp⟩ with hJ
    have hJne : J.1 ≠ J₀ := fun h => by
      have := congrArg Finset.card h
      rw [Finset.card_singleton, hJ₀card] at this
      omega
    have hkk : kJ J hJne ≠ k := by
      intro hkk
      have h1 := (hkJ J hJne j (Finset.mem_singleton_self j)).1
      rw [hkk] at h1
      apply h1
      rw [mem_planeCoordsQ2_iff]
      refine ⟨by have := k.2; simp only [finCongr_apply, Fin.val_cast, Fin.val_castSucc]; omega,
        ?_⟩
      rw [Finset.mem_singleton]
      exact Fin.ext (by simp only [finCongr_apply, Fin.val_cast, Fin.val_castSucc]; omega)
    have hψx : ∀ x ∈ spBlock K ({k} : Finset (Fin 4)),
        ψ (ctEmbed ε x) = ((e.symm x : L) : G) := by
      intro x hx
      have hc : ctEmbed ε x ∈ (CFSG.LieType.Universal.SpecialLinear.levi m K {j}).map
          (q2CastSL hm).toMonoidHom := by
        refine blockSpecialLinear_plane_le_map_levi hm k j hj ?_
        have := ctEmbed_mem_blockSpecialLinear_planeCoordsQ2 (ε := ε) hx
        rwa [planeCoordsQ2_singleton] at this
      obtain ⟨x₀, hx₀, hx₀c⟩ := hc
      have hx₀' : x₀ ∈ (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J := by
        have h1 : x₀ ∈ CFSG.LieType.CurtisTits.levi
            (CFSG.LieType.Universal.SpecialLinear.rootGroup m K) ({j} : Finset (Fin m)) := by
          rw [CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
          exact hx₀
        exact h1
      have hxk : x ∈ spBlock K ({kJ J hJne} : Finset (Fin 4))ᶜ :=
        spBlock_mono (by simpa using hkk) hx
      rw [MulEquiv.coe_toMonoidHom] at hx₀c
      have h1 := hψφ J ⟨x₀, hx₀'⟩
      change ψ (q2CastSL hm x₀) = _ at h1
      rw [← hx₀c, h1, hφne J hJne ⟨x₀, hx₀'⟩]
      have h2 : (⟨q2CastSL hm (x₀ : SpecialLinearGroup (Fin (m + 1)) K), hKle J hJne x₀ hx₀'⟩ :
          q2Block ε K {kJ J hJne}) = ⟨ctEmbed ε x, ctEmbed_mem_q2Block_iff.2 hxk⟩ :=
        Subtype.ext hx₀c
      rw [h2]
      exact (P (kJ J hJne)).N1 x hxk
    have hblock : (q2Block ε K {k}).map ψ ≤ neighbourCore e k := by
      refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        rw [mem_centralizer_iff]
        intro g hg
        obtain ⟨x, hx, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
        have hx' : x ∈ spBlock K ({k} : Finset (Fin 4)) := by
          rw [spBlock_singleton]
          exact rootTorusSp_le_longRootSp2 k hx
        rw [← hψx x hx', ← map_mul, ← map_mul]
        congr 1
        exact (LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right
          (ctEmbed_mem_blockSpecialLinear_planeCoordsQ2 (ε := ε) hx') hz).eq
      · have hcard : 3 ≤ ((planeCoordsQ2 ε ({k} : Finset (Fin 4)))ᶜ).card := by
          rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_singleton, Fintype.card_fin]
          omega
        rw [← map_commutator, commutator_q2Block_eq hcard]
    have hcardE : Nat.card (neighbourCore e k) ≤ Nat.card ((q2Block ε K {k}).map ψ) := by
      have hinj : Function.Injective (ψ.comp (q2Block ε K {k}).subtype) := by
        intro x y hxy
        apply Subtype.ext
        refine injOn_blockSpecialLinear_of_ker_le_center hψker
          (j := q2Coord 4 ε (Sum.inl (Sum.inl k))) ?_ x.2 y.2 hxy
        rw [Finset.mem_compl, not_not, q2Coord_mem_planeCoordsQ2, inPlanes_inl]
        simp
      have h1 : Nat.card ((q2Block ε K {k}).map ψ) = Nat.card (q2Block ε K {k}) := by
        have h2 : (q2Block ε K {k}).map ψ = (ψ.comp (q2Block ε K {k}).subtype).range := by
          rw [MonoidHom.range_comp, range_subtype]
        rw [h2]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      rw [h1, ← (P k).range_eq]
      exact Nat.card_le_card_of_surjective _ (P k).Φ.rangeRestrict_surjective
    have heq := Subgroup.eq_of_le_of_card_ge hblock hcardE
    rw [← heq, ← hψrange]
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  have hG₀eq : G₀ = spGlobal e := le_antisymm hG₀le
    ((spGlobal_le_iSup_neighbourCore (by omega) e).trans (iSup_le hEk))
  clear_value G₀
  subst hG₀eq
  refine ⟨ψ, hψrange, hψker, hqs,
    odd_card_center_of_surjective_specialLinear hKc (by omega) (by omega) hsurj hker, ?_⟩
  rw [← hm]
  exact hLM

theorem spGlobalCoverType_four_of_ctLinParamAgree [Finite K] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {κ : Sp2mKind} (hκ : (κ = .linearEven ∧ ε = 0) ∨ (κ = .linearOdd ∧ ε = 1))
    (P : ∀ k : Fin 4, CtLinParam ε e k) (hagree : CtLinParamAgree P)
    (hcomm : ∀ x ∈ blockSpecialLinear ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))),
      ∀ y ∈ blockSpecialLinear ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))),
      ∀ (hx : x ∈ q2Block ε K {2}) (hy : y ∈ q2Block ε K {0}),
        Commute ((P 2).Φ ⟨x, hx⟩) ((P 0).Φ ⟨y, hy⟩)) :
    SpGlobalCoverType e f κ := by
  have hε : ε ≤ 1 := by rcases hκ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  obtain ⟨-, -, -, hqs, hodd, hLM⟩ := exists_ct_linRow_four_of_agree hKc hf hε P hagree hcomm
  refine ⟨hqs, hodd, ?_⟩
  rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hLM
  · exact hLM

end Recognition

end CFSG.SeitzReduction.SymplecticPilot
