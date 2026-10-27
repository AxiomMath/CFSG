module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6Nine
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTU6
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6Big

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

@[expose] def U6ThreeDvdComp : Prop :=
  ∀ (T : Type) [Group T], catalogIs T S9.isU6two → ∀ α : MulAut T, α ^ 3 = 1 → α ≠ 1 →
    ∀ L : Subgroup T, CFSG.Open.IsComponentOf L (fixSub α) → 3 ∣ Nat.card ↥L

theorem nonempty_S6_of_isU6two {T : Type} [Group T] (h : catalogIs T S9.isU6two) :
    Nonempty (T ≃* LevelLieU6.S6) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S9.isU6two, onLie] at hi
  | alternating n hn => simp [S9.isU6two, onLie] at hi
  | sporadic s => simp [S9.isU6two, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r <;> simp [S9.isU6two, onLie] at hi
      exact LevelLieU6.bridge_u6two_stated hv ((TauCeti.PrimePower.card_def q).trans hi) e
    | _ => simp [S9.isU6two, onLie] at hi

theorem conj_pow_apply {T S : Type} [Group T] [Group S] (e : T ≃* S) (α : MulAut T) (n : ℕ) (x : S) :
    ((e.symm.trans (α.trans e)) ^ n) x = e ((α ^ n) (e.symm x)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
    congr 1
    simp

theorem psimple_nonempty_equiv_quotCenter {G : Type} [Group G] (p : ℕ) (L : Subgroup G)
    (hL : CFSG.Open.IsQuasisimple ↥L) (hnt : Nontrivial (PSimple p L)) :
    Nonempty (PSimple p L ≃* (↥L ⧸ Subgroup.center ↥L)) := by
  let π : ↥L →* PQuot p L := QuotientGroup.mk' (GLAPPrimeCore p ↥L)
  let W : Subgroup ↥L := (Subgroup.center (PQuot p L)).comap π
  have hWn : W.Normal := Subgroup.Normal.comap inferInstance π
  have hZW : Subgroup.center ↥L ≤ W := by
    intro z hz
    show π z ∈ Subgroup.center (PQuot p L)
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥L) q
    have hzx : z * x = x * z := (Subgroup.mem_center_iff.1 hz x).symm
    show π x * π z = π z * π x
    rw [← map_mul, ← map_mul, hzx]
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (W.map (QuotientGroup.mk' (Subgroup.center ↥L)))
      with hb | ht
  · have hWeq : Subgroup.center ↥L = W := by
      have h1 := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (Subgroup.center ↥L)) (H := W)
        (by rw [QuotientGroup.ker_mk']; exact hZW)
      rw [hb, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at h1
      exact h1
    let f : ↥L →* PSimple p L := (QuotientGroup.mk' (Subgroup.center (PQuot p L))).comp π
    have hfs : Function.Surjective f :=
      (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
    have hker : f.ker = Subgroup.center ↥L := by
      ext x
      rw [MonoidHom.mem_ker, hWeq]
      exact QuotientGroup.eq_one_iff (π x)
    let e : ↥L ⧸ Subgroup.center ↥L ≃* PSimple p L :=
      (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective f hfs)
    exact ⟨e.symm⟩
  · exfalso
    have hWtop : W = ⊤ := by
      have h1 := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (Subgroup.center ↥L)) (H := W)
        (by rw [QuotientGroup.ker_mk']; exact hZW)
      rw [ht, Subgroup.comap_top] at h1
      exact h1.symm
    have hZQ : Subgroup.center (PQuot p L) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥L) q
      have hx : x ∈ W := by rw [hWtop]; exact Subgroup.mem_top x
      exact hx
    have hsub : Subsingleton (PSimple p L) := by
      constructor
      intro a b
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, hZQ]
      exact Subgroup.mem_top _
    exact (not_nontrivial_iff_subsingleton.2 hsub) hnt

theorem u6Glap_typed (β : MulAut LevelLieU6.S6) (h3 : β ^ 3 = 1) (h1 : β ≠ 1)
    {I : Subgroup LevelLieU6.S6} (hI : GLAPComponent 3 (fixSubgroup β) I) :
    catalogIs (PSimple 3 I) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S10.isL2eight i) := by
  haveI := isSimple_S6
  obtain ⟨B, hB, ⟨c, hBc⟩, hβB⟩ := exists_unitary_of_pow_three β h3
  by_cases hsc : ∃ c : F4ˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 6) c
  · exfalso
    apply h1
    obtain ⟨c₀, hc₀⟩ := hsc
    ext x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.one_apply]
    refine hβB u u ?_
    rw [hc₀, ← (commute_scalar c₀ (u : GL (Fin 6) F4)).eq, mul_inv_cancel_right]
  · obtain ⟨J, hJ, ⟨e⟩⟩ := exists_component_transfer β ⟨B, hB⟩ hβB hI
    refine catalogIs_of_mulEquiv e.symm ?_
    by_cases h3B : (B : GL (Fin 6) F4) ^ 3 = 1
    · exact KSubT.catalogIs_mono (fun i hi => hi.elim Or.inl (fun h => Or.inr (Or.inl h)))
        (typed_cube_one ⟨B, hB⟩ (Subtype.ext h3B) hsc hJ)
    · have hc1 : c ≠ 1 := fun h => h3B (by rw [hBc, h, map_one])
      exact KSubT.catalogIs_mono (fun i hi => Or.inr (Or.inr hi)) (typed_nine ⟨B, hB⟩ hc1 hBc hJ)

theorem u6CompRes_of_threeDvd (h3d : U6ThreeDvdComp) : U6CompRes := by
  intro T _ hT α hα3 hα1 L hL
  obtain ⟨e⟩ := nonempty_S6_of_isU6two hT
  let α₆ : MulAut LevelLieU6.S6 := e.symm.trans (α.trans e)
  have hα₆3 : α₆ ^ 3 = 1 := by
    apply MulEquiv.ext
    intro x
    rw [conj_pow_apply, hα3, MulAut.one_apply, MulAut.one_apply, MulEquiv.apply_symm_apply]
  have hα₆1 : α₆ ≠ 1 := by
    intro h
    apply hα1
    apply MulEquiv.ext
    intro t
    have hx : ∀ x, e (α (e.symm x)) = x := fun x => by
      have := congrArg (fun f : MulAut LevelLieU6.S6 => f x) h
      simpa [α₆] using this
    have ht := hx (e t)
    rw [MulEquiv.symm_apply_apply] at ht
    rw [MulAut.one_apply]
    exact e.injective ht
  have hfix : fixSubgroup α₆ = (fixSub α).map e.toMonoidHom := by
    ext x
    rw [mem_fixSubgroup, Subgroup.mem_map_equiv, mem_fixSub]
    show e (α (e.symm x)) = x ↔ α (e.symm x) = e.symm x
    constructor
    · intro h
      have := congrArg e.symm h
      simpa using this
    · intro h
      rw [h]
      simp
  let eL : ↥L ≃* ↥(L.map e.toMonoidHom) := Subgroup.equivMapOfInjective L e.toMonoidHom e.injective
  have hL6 : CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (fixSubgroup α₆) := by
    rw [hfix]
    exact isComponentOf_map_mulEquiv hL e
  have hd : 3 ∣ Nat.card ↥(L.map e.toMonoidHom) := by
    rw [← Nat.card_congr eL.toEquiv]
    exact h3d T hT α hα3 hα1 L hL
  have hG : GLAPComponent 3 (fixSubgroup α₆) (L.map e.toMonoidHom) :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148L.glaPComponent_three_of_isComponentOf hL6 hd
  have hty := u6Glap_typed α₆ hα₆3 hα₆1 hG
  haveI : IsSimpleGroup (PSimple 3 (L.map e.toMonoidHom)) :=
    (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hG).2
  obtain ⟨eP⟩ := psimple_nonempty_equiv_quotCenter 3 (L.map e.toMonoidHom) hL6.2.2 inferInstance
  have h6 : catalogIs (↥(L.map e.toMonoidHom) ⧸ Subgroup.center ↥(L.map e.toMonoidHom))
      (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S10.isL2eight i) :=
    catalogIs_of_mulEquiv eP hty
  let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* (↥(L.map e.toMonoidHom) ⧸ Subgroup.center ↥(L.map e.toMonoidHom)) :=
    QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥(L.map e.toMonoidHom)) eL
      (Subgroup.map_center_eq eL)
  exact catalogIs_of_mulEquiv eQ.symm h6

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
