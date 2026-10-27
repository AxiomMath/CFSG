module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Pair
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsidePrelim

section Abstract

variable {W : Type*} [CommGroup W]

theorem map_commV_conjAut (g : MulAut W) (L : Subgroup (MulAut W)) :
    (commV L).map g.toMonoidHom = commV (B1.conjAut g L) := by
  unfold commV
  rw [MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨x, hx, v, rfl⟩, rfl⟩
    refine ⟨g * x * g⁻¹, ?_, g v, ?_⟩
    · rw [B1.mem_conjAut]; simpa [mul_assoc] using hx
    · simp [mul_assoc]
  · rintro ⟨y, hy, v, rfl⟩
    rw [B1.mem_conjAut] at hy
    refine ⟨_, ⟨g⁻¹ * y * g, hy, g⁻¹ v, rfl⟩, ?_⟩
    simp [mul_assoc]

theorem exists_mem_eq_on_commV {L : Subgroup (MulAut W)} (hnat : ActsAsNaturalL2 L (commV L))
    {s : MulAut W} (hs : (commV L).map s.toMonoidHom = commV L) :
    ∃ ℓ ∈ L, ∀ u ∈ commV L, ℓ u = s u := by
  obtain ⟨e, φ, hact⟩ := hnat
  have hsU : ∀ u ∈ commV L, s u ∈ commV L := fun u hu => hs ▸ Subgroup.mem_map_of_mem _ hu
  have hsinv : ∀ u ∈ commV L, s⁻¹ u ∈ commV L := by
    intro u hu
    have : u ∈ (commV L).map s.toMonoidHom := hs.symm ▸ hu
    obtain ⟨u', hu', rfl⟩ := this
    simpa using hu'
  let ρ : ↥(commV L) ≃* ↥(commV L) :=
    { toFun := fun u => ⟨s u, hsU u u.2⟩
      invFun := fun u => ⟨s⁻¹ u, hsinv u u.2⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  let ψ : MulAut (Multiplicative (Fin 2 → ZMod 2)) := (φ.symm.trans ρ).trans φ
  obtain ⟨g, hg⟩ := B1.slHom_surjective ψ
  refine ⟨(e.symm g : L), (e.symm g).2, fun u hu => ?_⟩
  have hu' : ((e.symm g : L) : MulAut W) u ∈ commV L := commV_invariant_of_mem (e.symm g).2 hu
  have h1 := hact (e.symm g) ⟨u, hu⟩ hu'
  rw [MulEquiv.apply_symm_apply] at h1
  have h2 : Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec
      (Multiplicative.toAdd (φ ⟨u, hu⟩))) = ψ (φ ⟨u, hu⟩) := by
    rw [← hg]; rfl
  have h3 : ψ (φ ⟨u, hu⟩) = φ ⟨s u, hsU u hu⟩ := by
    simp [ψ, ρ]
  have := φ.injective (h1.trans (h2.trans h3))
  exact congrArg Subtype.val this

theorem mem_iSup_of_acts {I : Finset (Subgroup (MulAut W))} (hI : S3Family I) {s : MulAut W}
    (hfix : ∀ f ∈ fixV (⨆ L ∈ I, L), s f = f)
    (hstab : ∀ L ∈ I, (commV L).map s.toMonoidHom = commV L) : s ∈ ⨆ L ∈ I, L := by
  classical
  have claim : ∀ J : Finset (Subgroup (MulAut W)), J ⊆ I →
      ∃ y ∈ ⨆ L ∈ J, L, (∀ L ∈ J, ∀ u ∈ commV L, y u = s u) ∧
        (∀ L ∈ I, L ∉ J → ∀ u ∈ commV L, y u = u) := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, Subgroup.one_mem _, by simp, fun L _ _ u _ => by simp⟩
    | insert L₀ J hL₀ ih =>
      intro hJI
      have hL₀I : L₀ ∈ I := hJI (Finset.mem_insert_self _ _)
      obtain ⟨y, hy, hy1, hy2⟩ := ih ((Finset.subset_insert _ _).trans hJI)
      obtain ⟨ℓ, hℓ, hℓs⟩ := exists_mem_eq_on_commV (hI.nat L₀ hL₀I) (hstab L₀ hL₀I)
      have hmono : (⨆ L ∈ J, L) ≤ ⨆ L ∈ insert L₀ J, L :=
        iSup₂_le fun L hL => le_iSup₂_of_le L (Finset.mem_insert_of_mem hL) le_rfl
      refine ⟨y * ℓ, Subgroup.mul_mem _ (hmono hy) (Subgroup.mem_iSup_of_mem L₀
        (Subgroup.mem_iSup_of_mem (Finset.mem_insert_self _ _) hℓ)), ?_, ?_⟩
      · intro L hL u hu
        rcases Finset.mem_insert.1 hL with rfl | hLJ
        · show y (ℓ u) = s u
          rw [← hℓs u hu]
          exact hy2 L hL₀I hL₀ _ (commV_invariant_of_mem hℓ hu)
        · have hne : L ≠ L₀ := fun h => hL₀ (h ▸ hLJ)
          have hLI : L ∈ I := hJI (Finset.mem_insert_of_mem hLJ)
          show y (ℓ u) = s u
          rw [hI.fixes_commV hLI hL₀I hne hℓ hu]
          exact hy1 L hLJ u hu
      · intro L hL hLn u hu
        have hne : L ≠ L₀ := fun h => hLn (h ▸ Finset.mem_insert_self _ _)
        have hLJ : L ∉ J := fun h => hLn (Finset.mem_insert_of_mem h)
        show y (ℓ u) = u
        rw [hI.fixes_commV hL hL₀I hne hℓ hu]
        exact hy2 L hL hLJ u hu
  obtain ⟨y, hy, hy1, -⟩ := claim I le_rfl
  set c : MulAut W := y⁻¹ * s with hc
  have hfixy : ∀ f ∈ fixV (⨆ L ∈ I, L), y f = f := fun f hf => hf y hy
  have hcfix : fixV (⨆ L ∈ I, L) ⊔ ⨆ L ∈ I, commV L ≤ fixedBy c := by
    refine sup_le (fun f hf => ?_) (iSup₂_le fun L hL u hu => ?_)
    · rw [mem_fixedBy, hc, MulAut.mul_apply, hfix f hf]
      have := hfixy f hf
      calc y⁻¹ f = y⁻¹ (y f) := by rw [this]
        _ = f := by simp
    · rw [mem_fixedBy, hc, MulAut.mul_apply, ← hy1 L hL u hu]
      simp
  have hc1 : c = 1 := by
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixedBy c := hcfix (by rw [hI.top]; exact Subgroup.mem_top v)
    rw [MulAut.one_apply]; exact mem_fixedBy.1 hv
  have : s = y := by
    have : y⁻¹ * s = 1 := hc1
    exact (inv_mul_eq_one.1 this).symm
  rw [this]; exact hy

theorem exists_ne_one_fixed [Finite W] {P : Subgroup (MulAut W)} (hP : IsPGroup 2 P)
    {U : Subgroup W} (hU : Nat.card U = 4) (hinv : ∀ p ∈ P, ∀ u ∈ U, p u ∈ U) :
    ∃ w ∈ U, w ≠ 1 ∧ ∀ p ∈ P, p w = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction ↥P ↥U :=
    { smul := fun p u => ⟨(p : MulAut W) u, hinv _ p.2 _ u.2⟩
      one_smul := fun u => Subtype.ext (by
        show ((1 : ↥P) : MulAut W) (u : W) = u
        simp)
      mul_smul := fun p q u => Subtype.ext (by
        show ((p * q : ↥P) : MulAut W) (u : W) = (p : MulAut W) ((q : MulAut W) (u : W))
        simp) }
  have hmod := hP.card_modEq_card_fixedPoints (α := ↥U)
  rw [hU] at hmod
  have hmem : (1 : ↥U) ∈ MulAction.fixedPoints ↥P ↥U := fun p => Subtype.ext (by
    show (p : MulAut W) (1 : W) = 1
    simp)
  have hpos : 0 < Nat.card (MulAction.fixedPoints ↥P ↥U) := Nat.card_pos_iff.2 ⟨⟨⟨1, hmem⟩⟩, inferInstance⟩
  have hev : 2 ∣ Nat.card (MulAction.fixedPoints ↥P ↥U) := by
    have h := hmod
    simp only [Nat.ModEq] at h
    omega
  have h2 : 2 ≤ Nat.card (MulAction.fixedPoints ↥P ↥U) := Nat.le_of_dvd hpos hev
  obtain ⟨⟨w, hw⟩, hw1⟩ : ∃ w : MulAction.fixedPoints ↥P ↥U, w ≠ ⟨1, hmem⟩ := by
    by_contra hcon
    push Not at hcon
    have : Nat.card (MulAction.fixedPoints ↥P ↥U) ≤ 1 := by
      have : Subsingleton (MulAction.fixedPoints ↥P ↥U) := ⟨fun a b => (hcon a).trans (hcon b).symm⟩
      exact Finite.card_le_one_iff_subsingleton.2 this
    omega
  refine ⟨w.1, w.2, fun h => hw1 (Subtype.ext (Subtype.ext h)), fun p hp => ?_⟩
  have h := congrArg Subtype.val (hw ⟨p, hp⟩)
  exact h

end Abstract

theorem isElemAbelian_closure {G : Type*} [Group G] {p : ℕ} {s : Set G}
    (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) (hp : ∀ a ∈ s, a ^ p = 1) :
    IsElemAbelian p (Subgroup.closure s) := CFSG.Open.IsElemAbelian.closure_of_commute hc hp

section GroupLevel

variable {G : Type} [Group G] [Finite G]

theorem mem_omegaOneCenter_of_centralizes {T V : Subgroup G} (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    {v : G} (hv : v ∈ V) (hcent : ∀ j ∈ thompsonJ T, j * v = v * j) :
    v ∈ omegaOneCenterOf (thompsonJ T) := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  have hAJ : A ≤ thompsonJ T := B6.le_thompsonJ hA
  have hv2 : v ^ 2 = 1 := hV.2 v hv
  set B : Subgroup G := Subgroup.closure ((A : Set G) ∪ {v}) with hB
  have hBel : IsElemAbelian 2 B := by
    refine isElemAbelian_closure ?_ ?_
    · rintro a (ha | rfl) b (hb | rfl)
      · exact congrArg Subtype.val (hA.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      · exact hcent a (hAJ ha)
      · exact (hcent b (hAJ hb)).symm
      · rfl
    · rintro a (ha | rfl)
      · exact hA.2.1.2 a ha
      · exact hv2
  have hBT : B ≤ T := (Subgroup.closure_le T).2 (by
    rintro a (ha | rfl)
    · exact hA.1 ha
    · exact hVT hv)
  have hAB : A ≤ B := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have hBA : Nat.card B ≤ Nat.card A := hA.2.2 B hBT hBel
  have hAeq : A = B := Subgroup.eq_of_le_of_card_ge hAB hBA
  have hvA : v ∈ A := hAeq ▸ Subgroup.subset_closure (Or.inr rfl)
  refine Subgroup.subset_closure ⟨⟨hAJ hvA, ?_⟩, hv2⟩
  exact Subgroup.mem_centralizer_iff.2 fun j hj => hcent j hj

theorem S3Family.mem_commV_of_mem_iSup {W : Type*} [CommGroup W]
    {I : Finset (Subgroup (MulAut W))} (hI : S3Family I) {L : Subgroup (MulAut W)} (hL : L ∈ I)
    {p : MulAut W} (hp : p ∈ ⨆ L' ∈ I, L') {u : W} (hu : u ∈ commV L) : p u ∈ commV L := by
  let S : Subgroup (MulAut W) :=
    { carrier := {p | ∀ u ∈ commV L, p u ∈ commV L ∧ p⁻¹ u ∈ commV L}
      one_mem' := fun u hu => ⟨by simpa using hu, by simpa using hu⟩
      mul_mem' := fun {a b} ha hb u hu => by
        refine ⟨?_, ?_⟩
        · exact (ha _ (hb u hu).1).1
        · have := (hb _ (ha u hu).2).2
          simpa [mul_inv_rev] using this
      inv_mem' := fun {a} ha u hu => ⟨(ha u hu).2, by simpa using (ha u hu).1⟩ }
  have hle : (⨆ L' ∈ I, L') ≤ S := by
    refine iSup₂_le fun L' hL' ℓ hℓ u hu => ?_
    by_cases h : L' = L
    · subst h
      exact ⟨commV_invariant_of_mem hℓ hu, commV_invariant_of_mem (L'.inv_mem hℓ) hu⟩
    · refine ⟨?_, ?_⟩
      · rw [hI.fixes_commV hL hL' (Ne.symm h) hℓ hu]; exact hu
      · rw [hI.fixes_commV hL hL' (Ne.symm h) (L'.inv_mem hℓ) hu]; exact hu
  exact (hle hp u hu).1

theorem autI_baum_le_autI_thompsonJ {M T V : Subgroup G} {hU : IsElemAbelian 2 V}
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T M) (hVT : V ≤ T)
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L)
    (hJTM : thompsonJ T ≤ thompsonJ M)
    (hperm : ∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) :
    autI hU (baum T) ≤ autI hU (thompsonJ M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := (mem_autI hU).1 hφ
  have hgT : (g : G) ∈ T := (inf_le_left : baum T ≤ T) hg
  have hgM : (g : G) ∈ M := hT.1 hgT
  have hgA : convI hU g ∈ autI hU M := (mem_autI hU).2 ⟨g, hgM, rfl⟩
  have hJT2 : IsPGroup 2 (thompsonJ T) := hT.2.1.to_le (B6.thompsonJ_le T)
  have hPY : autI hU (thompsonJ T) ≤ ⨆ L ∈ I, L := hJM ▸ autI_mono hU hJTM
  have hE : ∀ v : IntMod V hU, (∀ p ∈ autI hU (thompsonJ T), p v = v) → convI hU g v = v := by
    intro v hv
    have hcent : ∀ j ∈ thompsonJ T, j * v.val = v.val * j := by
      intro j hj
      have hjN : j ∈ Subgroup.normalizer (V : Set G) := hMN (hT.1 (B6.thompsonJ_le T hj))
      have := hv (convI hU ⟨j, hjN⟩) (convI_mem_autI hU hj hjN)
      have h2 := congrArg (fun x : IntMod V hU => x.val) this
      simp only [convI_apply_val] at h2
      calc j * v.val = j * v.val * j⁻¹ * j := by group
        _ = v.val * j := by rw [h2]
    have hvE := mem_omegaOneCenter_of_centralizes hU hVT v.2 hcent
    have hgE : (g : G) ∈ Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
      (inf_le_right : baum T ≤ _) hg
    have hcomm := Subgroup.mem_centralizer_iff.1 hgE _ hvE
    apply Subtype.ext
    show (convI hU g v).val = v.val
    have hcomm' : (g : G) * v.val = v.val * (g : G) := hcomm.symm
    rw [convI_apply_val, hcomm']
    group
  have hfix : ∀ f ∈ fixV (⨆ L ∈ I, L), convI hU g f = f := fun f hf =>
    hE f (fun p hp => hf p (hPY hp))
  have : Finite (IntMod V hU) := inferInstanceAs (Finite V)
  have hstab : ∀ L ∈ I, (commV L).map (convI hU g).toMonoidHom = commV L := by
    intro L hL
    obtain ⟨e, φ, -⟩ := hI.nat L hL
    have hcard : Nat.card (commV L) = 4 := by
      rw [Nat.card_congr φ.toEquiv]
      simp [Nat.card_eq_fintype_card]
    obtain ⟨w, hwU, hw1, hwfix⟩ := exists_ne_one_fixed (isPGroup_autI hU hJT2) hcard
      (fun p hp u hu => hI.mem_commV_of_mem_iSup hL (hPY hp) hu)
    have hwg : convI hU g w = w := hE w hwfix
    have hconj : B1.conjAut (convI hU g) L ∈ I := hperm _ hgA L hL
    have hmap := map_commV_conjAut (convI hU g) L
    by_cases hLc : B1.conjAut (convI hU g) L = L
    · rw [hmap, hLc]
    · exfalso
      have hwm : w ∈ (commV L).map (convI hU g).toMonoidHom := ⟨w, hwU, hwg⟩
      rw [hmap] at hwm
      have hbot := hI.commV_inf_commV hL hconj (Ne.symm hLc)
      have : w ∈ commV L ⊓ commV (B1.conjAut (convI hU g) L) := ⟨hwU, hwm⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hw1 this
  have := mem_iSup_of_acts hI hfix hstab
  rw [← hJM] at this
  exact this

end GroupLevel

open CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers

theorem ffBaumStar : FFBaumStar := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl hperm hfam
  have hF : CharTwo M := hc.glob.charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  have hVT : conjClosure (quasithinOmegaOneCenter T) M ≤ T :=
    hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
  exact autI_baum_le_autI_thompsonJ hMN hT hVT hfam hJM
    (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT) hperm


end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
