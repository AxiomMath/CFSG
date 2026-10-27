module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact35
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37Common
public import CFSG.Quasithin.Background.FFC10A
public import CFSG.CGT.Timmesfeld75.L2Aut
import CFSG.Open.MatrixFixedVectors

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (fixV commV IsElemAbelian2 ffJ IsFFStarOffender BinaryNaturalSL FFModel
  IsSylowIn natAct)
open CFSG.Quasithin.H (StdMod natAut natImage natNorm matAut IsSemilinear linSub toAddMap)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset PstarSet)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL specialLinearGroupEquivStatedSL_coe)
open scoped MatrixGroups

variable {W : Type} [CommGroup W]


private theorem card_le_of_forall_mulVec_eq {K : Type} [Field K] [Finite K]
    {a : Matrix (Fin 2) (Fin 2) K} (ha : a ≠ 1) (S : AddSubgroup (Fin 2 → K))
    (hS : ∀ x ∈ S, a.mulVec x = x) : Nat.card S ≤ Nat.card K := by
  have hinj : Function.Injective (fun x : S =>
      (⟨(x : Fin 2 → K), hS x x.2⟩ : {v : Fin 2 → K // a.mulVec v = v})) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {v : Fin 2 → K // a.mulVec v = v} => (z : Fin 2 → K)) h)
  exact (Nat.card_le_card_of_injective _ hinj).trans
    (CFSG.Open.StatedAPI.card_mulVec_fixed_le ha)



section Section

variable {U Z : Subgroup W} {M : Type} [CommGroup M]

private noncomputable def secFun (f : ↥U →* M) (hfs : Function.Surjective f) (y : MulAut W)
    (hyU : ∀ u ∈ U, y u ∈ U) (x : M) : M :=
  f ⟨y ((hfs x).choose : W), hyU _ (hfs x).choose.2⟩

private theorem secFun_apply (f : ↥U →* M) (hfs : Function.Surjective f)
    (hfk : ∀ u : ↥U, f u = 1 ↔ (u : W) ∈ Z) (y : MulAut W) (hyU : ∀ u ∈ U, y u ∈ U)
    (hyZ : ∀ z ∈ Z, y z ∈ Z) (u : ↥U) :
    secFun f hfs y hyU (f u) = f ⟨y u, hyU _ u.2⟩ := by
  unfold secFun
  have hcu : f (hfs (f u)).choose = f u := (hfs (f u)).choose_spec
  have h1 : (((hfs (f u)).choose * u⁻¹ : ↥U) : W) ∈ Z :=
    (hfk _).mp (by rw [map_mul, map_inv, hcu, mul_inv_cancel])
  have h2 := hyZ _ h1
  have h3 : f (⟨y ((hfs (f u)).choose : W), hyU _ (hfs (f u)).choose.2⟩ *
      (⟨y u, hyU _ u.2⟩ : ↥U)⁻¹) = 1 := by
    rw [hfk]
    simpa [map_mul, map_inv] using h2
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3

private noncomputable def secAut (f : ↥U →* M) (hfs : Function.Surjective f)
    (hfk : ∀ u : ↥U, f u = 1 ↔ (u : W) ∈ Z) (y : MulAut W) (hyU : ∀ u ∈ U, y u ∈ U)
    (hyU' : ∀ u ∈ U, y⁻¹ u ∈ U) (hyZ : ∀ z ∈ Z, y z ∈ Z) (hyZ' : ∀ z ∈ Z, y⁻¹ z ∈ Z) :
    MulAut M where
  toFun := secFun f hfs y hyU
  invFun := secFun f hfs y⁻¹ hyU'
  left_inv := fun x => by
    obtain ⟨u, rfl⟩ := hfs x
    rw [secFun_apply f hfs hfk _ _ hyZ, secFun_apply f hfs hfk _ _ hyZ']
    congr 1
    ext
    simp
  right_inv := fun x => by
    obtain ⟨u, rfl⟩ := hfs x
    rw [secFun_apply f hfs hfk _ _ hyZ', secFun_apply f hfs hfk _ _ hyZ]
    congr 1
    ext
    simp
  map_mul' := fun x x' => by
    obtain ⟨u, rfl⟩ := hfs x
    obtain ⟨u', rfl⟩ := hfs x'
    rw [← map_mul, secFun_apply f hfs hfk _ _ hyZ, secFun_apply f hfs hfk _ _ hyZ,
      secFun_apply f hfs hfk _ _ hyZ, ← map_mul]
    congr 1
    ext
    simp

private theorem secAut_apply (f : ↥U →* M) (hfs : Function.Surjective f)
    (hfk : ∀ u : ↥U, f u = 1 ↔ (u : W) ∈ Z) (y : MulAut W) (hyU : ∀ u ∈ U, y u ∈ U)
    (hyU' : ∀ u ∈ U, y⁻¹ u ∈ U) (hyZ : ∀ z ∈ Z, y z ∈ Z) (hyZ' : ∀ z ∈ Z, y⁻¹ z ∈ Z)
    (u : ↥U) : secAut f hfs hfk y hyU hyU' hyZ hyZ' (f u) = f ⟨y u, hyU _ u.2⟩ :=
  secFun_apply f hfs hfk y hyU hyZ u

private noncomputable def secHom (f : ↥U →* M) (hfs : Function.Surjective f)
    (hfk : ∀ u : ↥U, f u = 1 ↔ (u : W) ∈ Z) {Y : Subgroup (MulAut W)}
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) (hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y z ∈ Z) : ↥Y →* MulAut M where
  toFun y := secAut f hfs hfk y (hYU y y.2) (hYU _ (Y.inv_mem y.2)) (hYZ y y.2)
    (hYZ _ (Y.inv_mem y.2))
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨u, rfl⟩ := hfs x
    exact secAut_apply f hfs hfk _ _ _ _ _ u
  map_mul' y y' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨u, rfl⟩ := hfs x
    simp only [MulAut.mul_apply, secAut_apply]
    rfl

private theorem secHom_apply (f : ↥U →* M) (hfs : Function.Surjective f)
    (hfk : ∀ u : ↥U, f u = 1 ↔ (u : W) ∈ Z) {Y : Subgroup (MulAut W)}
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) (hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y z ∈ Z) (y : ↥Y) (u : ↥U) :
    secHom f hfs hfk hYU hYZ y (f u) = f ⟨(y : MulAut W) u, hYU y y.2 u u.2⟩ :=
  secAut_apply f hfs hfk (y : MulAut W) (hYU y y.2) (hYU _ (Y.inv_mem y.2)) (hYZ y y.2)
    (hYZ _ (Y.inv_mem y.2)) u

variable [Finite W]

private theorem card_le_mul_card_map_fixV [Finite M] {A : Subgroup (MulAut W)}
    (hoff : Nat.card W ≤ Nat.card A * Nat.card (fixV A)) (f : ↥U →* M)
    (hfs : Function.Surjective f) :
    Nat.card M ≤ Nat.card A * Nat.card (((fixV A).subgroupOf U).map f) := by
  set C := fixV A with hCdef
  have hU : Nat.card U = Nat.card M * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfs).toEquiv]
  have hCU : Nat.card (C.subgroupOf U) ≤
      Nat.card f.ker * Nat.card ((C.subgroupOf U).map f) := by
    let g : ↥(C.subgroupOf U) →* M := f.comp (C.subgroupOf U).subtype
    have h1 : Nat.card (C.subgroupOf U) = Nat.card g.range * Nat.card g.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
    have h2 : g.range = (C.subgroupOf U).map f := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h3 : Nat.card g.ker ≤ Nat.card f.ker := by
      refine Nat.card_le_card_of_injective
        (fun x => (⟨((x : ↥(C.subgroupOf U)) : ↥U), x.2⟩ : ↥f.ker)) ?_
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥f.ker => (z : ↥U)) h
    rw [h1, h2, mul_comm]
    exact Nat.mul_le_mul_right _ h3
  have hprod : Nat.card U * Nat.card C ≤ Nat.card W * Nat.card (C.subgroupOf U) := by
    have h1 := Subgroup.relIndex_mul_card C U
    have h2 : C.relIndex U ≤ C.index := by
      rw [← Subgroup.relIndex_top_right]
      exact Subgroup.relIndex_le_of_le_right le_top
        (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
    have h3 := Subgroup.index_mul_card C
    have h4 : Nat.card ↥(C ⊓ U) = Nat.card (C.subgroupOf U) := by
      rw [← Subgroup.inf_subgroupOf_right]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
    rw [← h4]
    calc Nat.card U * Nat.card C = C.relIndex U * Nat.card ↥(C ⊓ U) * Nat.card C := by rw [h1]
      _ ≤ C.index * Nat.card ↥(C ⊓ U) * Nat.card C := by gcongr
      _ = Nat.card W * Nat.card ↥(C ⊓ U) := by rw [← h3]; ring
  have hpos : 0 < Nat.card f.ker * Nat.card C := Nat.mul_pos Nat.card_pos Nat.card_pos
  have key : Nat.card M * (Nat.card f.ker * Nat.card C) ≤
      Nat.card A * Nat.card ((C.subgroupOf U).map f) * (Nat.card f.ker * Nat.card C) := by
    calc Nat.card M * (Nat.card f.ker * Nat.card C) = Nat.card U * Nat.card C := by rw [hU]; ring
      _ ≤ Nat.card W * Nat.card (C.subgroupOf U) := hprod
      _ ≤ (Nat.card A * Nat.card C) * (Nat.card f.ker * Nat.card ((C.subgroupOf U).map f)) :=
          Nat.mul_le_mul hoff hCU
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right key hpos

end Section

variable [Finite W]

theorem subgroupOf_normal_of_isSubnormal_of_isSLn {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hsn : (L.subgroupOf Y).IsSubnormal) {m : ℕ} (hm : 2 ≤ m) (hL : IsSLn ↥L 2 m)
    (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥) : (L.subgroupOf Y).Normal := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    CFSG.QuasithinUnique.Setup.SL2Modules.charP_two_of_card_eq
      (by rw [Fintype.card_eq_nat_card, hK])
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
  have := CFSG.LocalAnalysis.RankThreeUC.S15.K421SpSLProof.isSimpleGroup_sl2_charTwo h4
  have hs : IsSimpleGroup ↥(L.subgroupOf Y) :=
    MulEquiv.isSimpleGroup (((Subgroup.subgroupOfEquivOfLe hLY).trans e).trans
      (specialLinearGroupEquivStatedSL 2 K).symm)
  refine normal_of_isSubnormal_of_centralizer_eq_bot hs ?_ hsn
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hyC : (y : MulAut W) ∈ Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
    refine ⟨y.2, fun l hl => ?_⟩
    have := hy ⟨l, hLY hl⟩ (Subgroup.mem_subgroupOf.mpr hl)
    exact congrArg Subtype.val this
  rw [hC, Subgroup.mem_bot] at hyC
  exact Subtype.ext hyC

omit [Finite W] in
private theorem mem_commV_of_normal {Y L : Subgroup (MulAut W)} (hLn : (L.subgroupOf Y).Normal)
    (hLY : L ≤ Y) {y : MulAut W} (hy : y ∈ Y) {u : W} (hu : u ∈ commV L) : y u ∈ commV L := by
  have hconj : ∀ x ∈ L, y * x * y⁻¹ ∈ L := by
    intro x hx
    have h1 := hLn.conj_mem ⟨x, hLY hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hy⟩
    simpa using Subgroup.mem_subgroupOf.mp h1
  have hle : commV L ≤ (commV L).comap (y : MulAut W).toMonoidHom := by
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    show y (x v * v⁻¹) ∈ commV L
    refine Subgroup.subset_closure ⟨y * x * y⁻¹, hconj x hx, y v, ?_⟩
    simp [MulAut.mul_apply]
  exact hle hu

omit [Finite W] in
private theorem mem_fixV_of_normal {Y L : Subgroup (MulAut W)} (hLn : (L.subgroupOf Y).Normal)
    (hLY : L ≤ Y) {y : MulAut W} (hy : y ∈ Y) {z : W} (hz : z ∈ fixV L) : y z ∈ fixV L := by
  intro x hx
  have h1 := hLn.conj_mem ⟨x, hLY hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y⁻¹, Y.inv_mem hy⟩
  have h2 : y⁻¹ * x * y ∈ L := by simpa using Subgroup.mem_subgroupOf.mp h1
  have h3 := hz _ h2
  calc x (y z) = y ((y⁻¹ * x * y) z) := by simp [MulAut.mul_apply]
    _ = y z := by rw [h3]

omit [Finite W] in
private theorem natSection_psiL {K : Type} [Field K] [Finite K]
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (π : ↥(CFSG.Open.StatedSL 2 K) →* ↥L) (hπs : Function.Surjective π)
    (ψ : ↥Y →* MulAut (StdMod (Fin 2) K))
    (hψπ : ∀ γ : ↥(CFSG.Open.StatedSL 2 K),
      ψ ⟨(π γ : MulAut W), hLY (π γ).2⟩ = natAut (CFSG.Open.StatedSL 2 K) γ) :
    (L.subgroupOf Y).map ψ = natImage (CFSG.Open.StatedSL 2 K) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨y, Subgroup.mem_subgroupOf.mp hy⟩
    refine ⟨γ, ?_⟩
    rw [← hψπ γ]
    congr 1
    have h1 : ((π γ : ↥L) : MulAut W) = (y : MulAut W) := congrArg Subtype.val hγ
    exact Subtype.ext h1
  · rintro ⟨γ, rfl⟩
    exact ⟨⟨(π γ : MulAut W), hLY (π γ).2⟩, Subgroup.mem_subgroupOf.mpr (π γ).2, hψπ γ⟩

omit [Finite W] in
private theorem natSection_psi_inj {K : Type} [Field K] [Finite K]
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥)
    (π : ↥(CFSG.Open.StatedSL 2 K) →* ↥L) (hπs : Function.Surjective π)
    (ψ : ↥Y →* MulAut (StdMod (Fin 2) K))
    (hψπ : ∀ γ : ↥(CFSG.Open.StatedSL 2 K),
      ψ ⟨(π γ : MulAut W), hLY (π γ).2⟩ = natAut (CFSG.Open.StatedSL 2 K) γ)
    (hnatinj : Function.Injective (natAut (CFSG.Open.StatedSL 2 K))) :
    Function.Injective ψ := by
  refine (injective_iff_map_eq_one ψ).mpr fun y hy => ?_
  have hyC : (y : MulAut W) ∈ Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
    refine ⟨y.2, fun l hl => ?_⟩
    have hcL : (y : MulAut W) * l * (y : MulAut W)⁻¹ * l⁻¹ ∈ L := by
      have h1 := hLn.conj_mem ⟨l, hLY hl⟩ (Subgroup.mem_subgroupOf.mpr hl) y
      exact L.mul_mem (by simpa using Subgroup.mem_subgroupOf.mp h1) (L.inv_mem hl)
    obtain ⟨γ, hγ⟩ := hπs ⟨_, hcL⟩
    have hψc : ψ ⟨_, hLY hcL⟩ = 1 := by
      have : (⟨_, hLY hcL⟩ : ↥Y) = y * ⟨l, hLY hl⟩ * y⁻¹ * ⟨l, hLY hl⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hy]
      group
    have hγ1 : γ = 1 := by
      have h1 : natAut (CFSG.Open.StatedSL 2 K) γ = 1 := by
        rw [← hψπ γ, ← hψc]
        congr 1
        have h2 : ((π γ : ↥L) : MulAut W) =
            (y : MulAut W) * l * (y : MulAut W)⁻¹ * l⁻¹ := congrArg Subtype.val hγ
        exact Subtype.ext h2
      exact (map_eq_one_iff _ hnatinj).mp h1
    have hc1 : (y : MulAut W) * l * (y : MulAut W)⁻¹ * l⁻¹ = 1 := by
      have := congrArg Subtype.val hγ
      rw [hγ1, map_one] at this
      exact this.symm
    calc l * y = ((y : MulAut W) * l * (y : MulAut W)⁻¹ * l⁻¹)⁻¹ * (y * l) := by group
      _ = y * l := by rw [hc1, inv_one, one_mul]
  rw [hC, Subgroup.mem_bot] at hyC
  exact Subtype.ext hyC

omit [Finite W] in
private theorem natSection_psiN {K : Type} [Field K]
    {Y L : Subgroup (MulAut W)} (hLn : (L.subgroupOf Y).Normal)
    (ψ : ↥Y →* MulAut (StdMod (Fin 2) K))
    (hψL : (L.subgroupOf Y).map ψ = natImage (CFSG.Open.StatedSL 2 K)) :
    ψ.range ≤ natNorm (CFSG.Open.StatedSL 2 K) := by
  show ψ.range ≤ Subgroup.normalizer
    ((natImage (CFSG.Open.StatedSL 2 K) : Subgroup (MulAut (StdMod (Fin 2) K))) :
      Set (MulAut (StdMod (Fin 2) K)))
  rw [← hψL]
  have h1 := Subgroup.le_normalizer_map (H := L.subgroupOf Y) ψ
  rw [Subgroup.normalizer_eq_top_iff.mpr hLn, ← MonoidHom.range_eq_map] at h1
  exact h1

omit [Finite W] in
private theorem exists_natSection {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥)
    {m : ℕ} (hnat : BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ m ∧
      ∃ (f : ↥(commV L) →* StdMod (Fin 2) K) (ψ : ↥Y →* MulAut (StdMod (Fin 2) K)),
        Function.Surjective f ∧ (∀ u, f u = 1 ↔ (u : W) ∈ fixV L) ∧
        (∀ (y : ↥Y) (u : ↥(commV L)) (h : (y : MulAut W) u ∈ commV L),
          f ⟨_, h⟩ = ψ y (f u)) ∧
        Function.Injective ψ ∧
        (L.subgroupOf Y).map ψ = natImage (CFSG.Open.StatedSL 2 K) ∧
        ψ.range ≤ natNorm (CFSG.Open.StatedSL 2 K) := by
  classical
  obtain ⟨K, _, _, hK, π₀, hreal⟩ := hnat
  obtain ⟨f, hfs, hfk₀, hfe₀⟩ := CFSG.Quasithin.G64.exists_natMap hreal
  let π : ↥(CFSG.Open.StatedSL 2 K) →* ↥L := π₀
  have hπs : Function.Surjective π := hreal.1
  have hfk : ∀ u : ↥(commV L), f u = 1 ↔ (u : W) ∈ fixV L := by
    intro u
    rw [hfk₀]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have hYU : ∀ y ∈ Y, ∀ u ∈ commV L, y u ∈ commV L :=
    fun y hy u hu => mem_commV_of_normal hLn hLY hy hu
  have hYZ : ∀ y ∈ Y, ∀ z ∈ fixV L, y z ∈ fixV L :=
    fun y hy z hz => mem_fixV_of_normal hLn hLY hy hz
  set ψ := secHom f hfs hfk hYU hYZ with hψdef
  have hψf : ∀ (y : ↥Y) (u : ↥(commV L)) (h : (y : MulAut W) u ∈ commV L),
      f ⟨_, h⟩ = ψ y (f u) := fun y u h => (secHom_apply f hfs hfk hYU hYZ y u).symm
  have hψπ : ∀ γ : ↥(CFSG.Open.StatedSL 2 K),
      ψ ⟨(π γ : MulAut W), hLY (π γ).2⟩ = natAut (CFSG.Open.StatedSL 2 K) γ := by
    intro γ
    refine MulEquiv.ext fun x => ?_
    obtain ⟨u, rfl⟩ := hfs x
    rw [← hψf _ u (hYU _ (hLY (π γ).2) u u.2)]
    exact hfe₀ γ u _
  have hnatinj : Function.Injective (natAut (CFSG.Open.StatedSL 2 K)) :=
    CFSG.Quasithin.H.matHom_injective.comp Subtype.val_injective
  have hψL := natSection_psiL hLY π hπs ψ hψπ
  have hψinj := natSection_psi_inj hLY hLn hC π hπs ψ hψπ hnatinj
  have hψN := natSection_psiN hLn ψ hψL
  exact ⟨K, inferInstance, inferInstance, hK, f, ψ, hfs, hfk, hψf, hψinj, hψL, hψN⟩

theorem le_of_mem_gomiOset_of_isSLn {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) {m : ℕ} (hm : 2 ≤ m)
    (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥)
    (hnat : BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m) {A : Subgroup (MulAut W)}
    (hA : A ∈ gomiOset Y) : A ≤ L := by
  classical
  obtain ⟨K, _, _, hK, f, ψ, hfs, hfk, hψf, hψinj, hψL, hψN⟩ := exists_natSection hLY hLn hC hnat
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    CFSG.QuasithinUnique.Setup.SL2Modules.charP_two_of_card_eq
      (by rw [Fintype.card_eq_nat_card, hK])
  obtain ⟨hAY, -, hAel, hAoff⟩ := hA
  set E := (A.subgroupOf Y).map ψ with hEdef
  have hEN : E ≤ natNorm (CFSG.Open.StatedSL 2 K) := (Subgroup.map_le_range ψ _).trans hψN
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hAel.2 _ (Subgroup.mem_subgroupOf.mp ha))
    rw [this, map_one]
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAel.1 _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))
  have hEA : Nat.card E = Nat.card A := by
    rw [hEdef, Subgroup.card_map_of_injective hψinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv
  have hfixE : ((fixV A).subgroupOf (commV L)).map f ≤ fixV E := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨a, ha, rfl⟩
    have hau : (a : MulAut W) u = u :=
      Subgroup.mem_subgroupOf.mp hu _ (Subgroup.mem_subgroupOf.mp ha)
    rw [← hψf a u (by rw [hau]; exact u.2)]
    congr 1
    exact Subtype.ext hau
  have hoff : Nat.card (StdMod (Fin 2) K) ≤ Nat.card E * Nat.card (fixV E) := by
    calc Nat.card (StdMod (Fin 2) K)
        ≤ Nat.card A * Nat.card (((fixV A).subgroupOf (commV L)).map f) :=
          card_le_mul_card_map_fixV hAoff f hfs
      _ ≤ Nat.card E * Nat.card (fixV E) := by
          rw [hEA]
          exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hfixE)
  have hle := CFSG.Quasithin.B69.le_natImage_of_offender (by omega : 1 ≤ m) hK hEN hE2 hEc hoff
  intro a ha
  have hmem : ψ ⟨a, hAY ha⟩ ∈ natImage (CFSG.Open.StatedSL 2 K) :=
    hle ⟨⟨a, hAY ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  rw [← hψL] at hmem
  obtain ⟨l, hl, hll⟩ := hmem
  have h1 := hψinj hll
  have h2 := Subgroup.mem_subgroupOf.mp hl
  rw [h1] at h2; exact h2

private theorem exists_isFFStarOffender_of_isSylowIn {Y S : Subgroup (MulAut W)}
    (hS : IsSylowIn 2 S Y) (hP : (Pset Y).Nonempty) : ∃ B, IsFFStarOffender S B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hB⟩ := hP
  have hB' : IsFFStarOffender Y B := hB
  have hBp : IsPGroup 2 (B.subgroupOf Y) := by
    intro b
    have h1 := hB'.2.2.1.2 _ (Subgroup.mem_subgroupOf.mp b.2)
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using h1))⟩
  obtain ⟨Q, hBQ⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y Q hS.toSylow
  have h1 := CFSG.Quasithin.isFFStarOffender_map_conj hB' g.2
  refine ⟨B.map (MulAut.conj (g : MulAut W)).toMonoidHom, ?_, h1.2⟩
  rintro _ ⟨b, hb, rfl⟩
  have hbY : b ∈ Y := hB'.1 hb
  have hbQ : (⟨b, hbY⟩ : ↥Y) ∈ (Q : Subgroup ↥Y) := hBQ (Subgroup.mem_subgroupOf.mpr hb)
  have h2 : MulAut.conj g • (⟨b, hbY⟩ : ↥Y) ∈ ((g • Q : Sylow 2 ↥Y) : Subgroup ↥Y) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hbQ
  rw [hg, IsSylowIn.coe_toSylow] at h2
  have h3 := Subgroup.mem_subgroupOf.mp h2
  simpa [MulAut.smul_def, MulAut.conj_apply] using h3

omit [Finite W] in
private theorem mem_gomiOset_of_isFFStarOffender {X A : Subgroup (MulAut W)}
    (hA : IsFFStarOffender X A) : A ∈ gomiOset X := by
  refine ⟨hA.1, hA.2.1, hA.2.2.1, ?_⟩
  have h1 := hA.2.2.2 ⊥ bot_le
  have h2 : Nat.card (fixV (⊥ : Subgroup (MulAut W))) = Nat.card W := by
    have : fixV (⊥ : Subgroup (MulAut W)) = ⊤ := by
      ext v
      simp only [Subgroup.mem_top, iff_true]
      intro x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      rfl
    rw [this]
    exact Subgroup.card_top
  rw [Subgroup.card_bot, one_mul, h2] at h1
  exact h1

private theorem eq_one_of_pow_two_pow_eq_one {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) {d : Kˣ} {k : ℕ} (hd : d ^ 2 ^ k = 1) : d = 1 := by
  have h1 : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hd
  have h2 : orderOf d ∣ 2 ^ m - 1 := by
    have := orderOf_dvd_natCard d
    rwa [Nat.card_units, hK] at this
  have hm : 1 ≤ m := by
    have := Finite.one_lt_card (α := K)
    rw [hK] at this
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at this
    · exact h
  have hodd : ¬ 2 ∣ 2 ^ m - 1 := by
    have h3 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    have h4 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  have hcop : Nat.Coprime (2 ^ k) (2 ^ m - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h5 : orderOf d ∣ Nat.gcd (2 ^ k) (2 ^ m - 1) := Nat.dvd_gcd h1 h2
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h5
  exact h5

omit [Finite W] in
private theorem natImage_and_card_le_of_fix_of_mem_of_ne_one {K : Type} [Field K] [Fintype K]
    [CharP K 2] {Y L : Subgroup (MulAut W)} {m : ℕ} (hK : Nat.card K = 2 ^ m)
    {ψ : ↥Y →* MulAut (StdMod (Fin 2) K)}
    (hψL : (L.subgroupOf Y).map ψ = natImage (CFSG.Open.StatedSL 2 K))
    (hψinj : Function.Injective ψ) :
    (∀ l : ↥Y, (l : MulAut W) ∈ L →
      ∃ γ : ↥(CFSG.Open.StatedSL 2 K), ψ l = natAut (CFSG.Open.StatedSL 2 K) γ) ∧
    ∀ l : ↥Y, (l : MulAut W) ∈ L → l ≠ 1 → ∀ (X : Subgroup (StdMod (Fin 2) K)),
      (∀ x ∈ X, ψ l x = x) → Nat.card X ≤ 2 ^ m := by
  have hψmat : ∀ l : ↥Y, (l : MulAut W) ∈ L →
      ∃ γ : ↥(CFSG.Open.StatedSL 2 K), ψ l = natAut (CFSG.Open.StatedSL 2 K) γ := by
    intro l hl
    have : ψ l ∈ natImage (CFSG.Open.StatedSL 2 K) := by
      rw [← hψL]
      exact ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    obtain ⟨γ, hγ⟩ := this
    exact ⟨γ, hγ.symm⟩
  refine ⟨hψmat, fun l hl hl1 X hX => ?_⟩
  obtain ⟨γ, hγ⟩ := hψmat l hl
  have hγ1 : ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
    intro h
    apply hl1
    apply hψinj
    rw [hγ, map_one]
    have : γ = 1 := Subtype.ext (Units.ext h)
    rw [this, map_one]
  have h1 := card_le_of_forall_mulVec_eq hγ1 (Subgroup.toAddSubgroup X) fun x hx => by
    have := hX _ hx
    rw [hγ] at this
    exact congrArg Multiplicative.toAdd this
  rw [← hK]
  exact h1

private theorem le_inf_of_isFFStarOffender {Y S L : Subgroup (MulAut W)} {m : ℕ}
    (hS : IsSylowIn 2 S Y) (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hm : 2 ≤ m)
    (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥)
    (hnat : BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m) :
    ∀ A, IsFFStarOffender S A → A ≤ S ⊓ L := by
  intro A hA
  have hAY : IsFFStarOffender Y A := ⟨hA.1.trans hS.le, hA.2⟩
  exact le_inf hA.1 (le_of_mem_gomiOset_of_isSLn hLY hLn hm hC hnat
    (mem_gomiOset_of_isFFStarOffender hAY))

private theorem pow_le_card_of_isFFStarOffender {K : Type} [Field K] [Fintype K] [CharP K 2]
    {Y S L : Subgroup (MulAut W)} {m : ℕ} (hLY : L ≤ Y)
    (hTL : S ⊓ L ≤ L) {f : ↥(commV L) →* StdMod (Fin 2) K}
    (hfs : Function.Surjective f)
    {ψ : ↥Y →* MulAut (StdMod (Fin 2) K)}
    (hψf : ∀ (y : ↥Y) (u : ↥(commV L)) (h : (y : MulAut W) u ∈ commV L),
      f ⟨_, h⟩ = ψ y (f u))
    (hfixL : ∀ l : ↥Y, (l : MulAut W) ∈ L → l ≠ 1 →
      ∀ (X : Subgroup (StdMod (Fin 2) K)), (∀ x ∈ X, ψ l x = x) → Nat.card X ≤ 2 ^ m)
    (hPT : ∀ A, IsFFStarOffender S A → A ≤ S ⊓ L)
    (hcardM : Nat.card (StdMod (Fin 2) K) = 2 ^ m * 2 ^ m) :
    ∀ A, IsFFStarOffender S A → 2 ^ m ≤ Nat.card A := by
  intro A hA
  have hAT := hPT A hA
  have h1 := card_le_mul_card_map_fixV (mem_gomiOset_of_isFFStarOffender hA).2.2.2 f hfs
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.2.1
  have haL : (a : MulAut W) ∈ L := hTL (hAT a.2)
  have haY : (a : MulAut W) ∈ Y := hLY haL
  have h2 : Nat.card (((fixV A).subgroupOf (commV L)).map f) ≤ 2 ^ m := by
    refine hfixL ⟨a, haY⟩ haL
      (fun h => ha1 (Subtype.ext (show (a : MulAut W) = 1 from congrArg Subtype.val h))) _ ?_
    rintro _ ⟨u, hu, rfl⟩
    have hau : (a : MulAut W) u = u := Subgroup.mem_subgroupOf.mp hu _ a.2
    rw [← hψf ⟨a, haY⟩ u (by rw [hau]; exact u.2)]
    congr 1
    exact Subtype.ext hau
  rw [hcardM] at h1
  have h3 : 2 ^ m * 2 ^ m ≤ Nat.card A * 2 ^ m := h1.trans (Nat.mul_le_mul_left _ h2)
  exact Nat.le_of_mul_le_mul_right h3 (by positivity)

private theorem card_le_pow_of_isPGroup_inf {Y S L : Subgroup (MulAut W)} {m : ℕ}
    (hm : 2 ≤ m) (hS : IsSylowIn 2 S Y) (hL : IsSLn ↥L 2 m) (hTS : S ⊓ L ≤ S)
    (hTL : S ⊓ L ≤ L) : Nat.card ↥(S ⊓ L) ≤ 2 ^ m := by
  set T := S ⊓ L
  obtain ⟨K', _, _, hK', ⟨e⟩⟩ := hL
  have hLcard : Nat.card L = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr (e.trans (specialLinearGroupEquivStatedSL 2 K').symm).toEquiv,
      CFSG.GorensteinWalter.sl2_card_formula K', hK']
  have hTp : IsPGroup 2 T := hS.isPGroup.to_le hTS
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTp
  have hdvd : Nat.card ↥T ∣ Nat.card L := Subgroup.card_dvd_of_le hTL
  rw [hk, hLcard] at hdvd
  have hodd : ¬ 2 ∣ (2 ^ m) ^ 2 - 1 := by
    have h3 : 2 ∣ (2 ^ m) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
    have h4 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hcop : Nat.Coprime (2 ^ k) ((2 ^ m) ^ 2 - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  rw [hk]
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

private theorem three_two_ffJ {Y S L : Subgroup (MulAut W)} {m : ℕ}
    (hS : IsSylowIn 2 S Y) (hP : (Pset Y).Nonempty)
    (hPT : ∀ A, IsFFStarOffender S A → A ≤ S ⊓ L)
    (hPcard : ∀ A, IsFFStarOffender S A → 2 ^ m ≤ Nat.card A)
    (hTcard : Nat.card ↥(S ⊓ L) ≤ 2 ^ m) :
    ffJ S = S ⊓ L ∧ Nat.card ↥(S ⊓ L) = 2 ^ m ∧ IsFFStarOffender S (S ⊓ L) := by
  obtain ⟨B, hB⟩ := exists_isFFStarOffender_of_isSylowIn hS hP
  have hBT : B = S ⊓ L :=
    Subgroup.eq_of_le_of_card_ge (hPT B hB) (hTcard.trans (hPcard B hB))
  have hTP : IsFFStarOffender S (S ⊓ L) := hBT ▸ hB
  refine ⟨le_antisymm (iSup₂_le fun A hA => hPT A hA) (le_iSup₂_of_le (S ⊓ L) hTP le_rfl), ?_⟩
  exact ⟨le_antisymm hTcard (hPcard _ hTP), hTP⟩

omit [Finite W] in
private theorem three_two_left_Xle {K : Type} [Field K] [Fintype K] [CharP K 2]
    {Y L : Subgroup (MulAut W)}
    {f : ↥(commV L) →* StdMod (Fin 2) K}
    {ψ : ↥Y →* MulAut (StdMod (Fin 2) K)}
    (hψf : ∀ (y : ↥Y) (u : ↥(commV L)) (h : (y : MulAut W) u ∈ commV L),
      f ⟨_, h⟩ = ψ y (f u))
    {T : Subgroup (MulAut W)} (hTL : T ≤ L) (hLY : L ≤ Y) (t : T)
    {γ₀ : ↥(CFSG.Open.StatedSL 2 K)}
    (hγ₀ : ψ ⟨t, hLY (hTL t.2)⟩ = natAut (CFSG.Open.StatedSL 2 K) γ₀) :
    Subgroup.toAddSubgroup' (((fixV T).subgroupOf (commV L)).map f) ≤
      (LinearMap.ker (Matrix.mulVecLin ((γ₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) -
        LinearMap.id)).toAddSubgroup := by
  intro x hx
  rw [Subgroup.mem_toAddSubgroup'] at hx
  obtain ⟨u, hu, hux⟩ := hx
  have htu : (t : MulAut W) u = u := Subgroup.mem_subgroupOf.mp hu _ t.2
  have h1 : ψ ⟨t, hLY (hTL t.2)⟩ (f u) = f u := by
    rw [← hψf ⟨t, hLY (hTL t.2)⟩ u (by rw [htu]; exact u.2)]
    congr 1
    exact Subtype.ext htu
  rw [hγ₀] at h1
  have h2 := congrArg Multiplicative.toAdd h1
  have h3 : Multiplicative.toAdd (f u) = x := by rw [hux]; rfl
  rw [Submodule.mem_toAddSubgroup]
  refine LinearMap.mem_ker.mpr ?_
  rw [LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply, sub_eq_zero]
  rw [← h3]
  exact h2

omit [Finite W] in
private theorem three_two_left_line {K : Type} [Field K] [Fintype K] [CharP K 2]
    {Y S L : Subgroup (MulAut W)} {m : ℕ} (hK : Nat.card K = 2 ^ m)
    {f : ↥(commV L) →* StdMod (Fin 2) K}
    {ψ : ↥Y →* MulAut (StdMod (Fin 2) K)}
    (hψf : ∀ (y : ↥Y) (u : ↥(commV L)) (h : (y : MulAut W) u ∈ commV L),
      f ⟨_, h⟩ = ψ y (f u)) (hψinj : Function.Injective ψ)
    (hψmat : ∀ l : ↥Y, (l : MulAut W) ∈ L →
      ∃ γ : ↥(CFSG.Open.StatedSL 2 K), ψ l = natAut (CFSG.Open.StatedSL 2 K) γ)
    {T : Subgroup (MulAut W)} (hTP : IsFFStarOffender S T) (hTL : T ≤ L) (hLY : L ≤ Y)
    (hXcard : 2 ^ m ≤ Nat.card (((fixV T).subgroupOf (commV L)).map f)) :
    ∃ (ℓ : Submodule K (Fin 2 → K)),
      Nat.card ℓ ≤ 2 ^ m ∧
        (∀ v ∈ ℓ, Multiplicative.ofAdd v ∈ ((fixV T).subgroupOf (commV L)).map f) ∧
        Nat.card (((fixV T).subgroupOf (commV L)).map f) = Nat.card ℓ := by
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTP.2.1
  have htL : (t : MulAut W) ∈ L := hTL t.2
  have htY : (t : MulAut W) ∈ Y := hLY htL
  obtain ⟨γ₀, hγ₀⟩ := hψmat ⟨t, htY⟩ htL
  have hγ₀1 : ((γ₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
    intro h
    apply ht1
    have h1 : γ₀ = 1 := Subtype.ext (Units.ext h)
    have h2 : ψ ⟨t, htY⟩ = ψ 1 := by rw [hγ₀, h1, map_one, map_one]
    exact Subtype.ext (show (t : MulAut W) = 1 from congrArg Subtype.val (hψinj h2))
  set ℓ := LinearMap.ker (Matrix.mulVecLin ((γ₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) -
    LinearMap.id) with hℓdef
  set X : Subgroup (StdMod (Fin 2) K) := ((fixV T).subgroupOf (commV L)).map f with hXdef
  set X' : AddSubgroup (Fin 2 → K) := Subgroup.toAddSubgroup' X with hX'def
  have hXℓ : X' ≤ ℓ.toAddSubgroup := by
    rw [hX'def, hXdef]
    exact three_two_left_Xle hψf hTL hLY t hγ₀
  have hℓcard : Nat.card ℓ ≤ 2 ^ m := by
    rw [Module.natCard_eq_pow_finrank (K := K), hK, ← pow_mul]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr
      (by have := finrank_ker_mulVecLin_sub_id_le_one hγ₀1; nlinarith)
  have hX'card : Nat.card ↥X' = Nat.card ↥X := rfl
  have hℓcard' : Nat.card ↥ℓ.toAddSubgroup = Nat.card ↥ℓ := rfl
  have hXeq : X' = ℓ.toAddSubgroup :=
    AddSubgroup.eq_of_le_of_card_ge hXℓ (by omega)
  have hXcard_eq : Nat.card ↥X = Nat.card ↥ℓ := by rw [← hX'card, hXeq]; rfl
  refine ⟨ℓ, hℓcard, ?_, hXcard_eq⟩
  intro v hv
  have h1 : v ∈ X' := by rw [hXeq]; exact hv
  exact h1

private theorem three_two_left_nonzero {K : Type} [Field K] [Fintype K]
    {m : ℕ} (hm : 2 ≤ m) {X : Subgroup (StdMod (Fin 2) K)} (ℓ : Submodule K (Fin 2 → K))
    (hℓcard : Nat.card ℓ ≤ 2 ^ m) (hXcard : 2 ^ m ≤ Nat.card X)
    (hXcard_eq : Nat.card X = Nat.card ℓ) :
    ∃ (v₀ : Fin 2 → K), v₀ ∈ ℓ ∧ v₀ ≠ 0 := by
  by_contra h
  push Not at h
  have h1 : ℓ = ⊥ := (Submodule.eq_bot_iff ℓ).mpr h
  have h2 : Nat.card ℓ = 1 := by rw [h1]; exact Nat.card_unique
  have h3 : Nat.card X = 1 := by rw [hXcard_eq, h2]
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr hm
  omega

omit [Finite W] in
private theorem three_two_left_fix {K : Type} [Field K]
    {Y : Subgroup (MulAut W)} {ψ : ↥Y →* MulAut (StdMod (Fin 2) K)}
    {X : Subgroup (StdMod (Fin 2) K)} {ℓ : Submodule K (Fin 2 → K)}
    {s : MulAut W} (hsY : s ∈ Y) (hmemX : ∀ v ∈ ℓ, Multiplicative.ofAdd v ∈ X)
    (hsX : ∀ x ∈ X, ψ ⟨s, hsY⟩ x = x) :
    ∀ v ∈ ℓ, toAddMap (ψ ⟨s, hsY⟩) v = v := by
  intro v hv
  show Multiplicative.toAdd (ψ ⟨s, hsY⟩ (Multiplicative.ofAdd v)) = v
  rw [hsX _ (hmemX v hv)]
  rfl

omit [Finite W] in
private theorem three_two_left_mem {K : Type} [Field K] [Fintype K] [CharP K 2]
    {Y S L : Subgroup (MulAut W)} {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (hS : IsSylowIn 2 S Y) {ψ : ↥Y →* MulAut (StdMod (Fin 2) K)}
    (hψN : ψ.range ≤ natNorm (CFSG.Open.StatedSL 2 K))
    (hψL : (L.subgroupOf Y).map ψ = natImage (CFSG.Open.StatedSL 2 K))
    (hψinj : Function.Injective ψ) {s : MulAut W} (hsY : s ∈ Y) (hsS : s ∈ S)
    {ℓ : Submodule K (Fin 2 → K)} {v₀ : Fin 2 → K}
    (hv₀ : v₀ ∈ ℓ) (hv₀0 : v₀ ≠ 0)
    (hfixℓ : ∀ v ∈ ℓ, toAddMap (ψ ⟨s, hsY⟩) v = v) :
    s ∈ L := by
  obtain ⟨σ, hσ⟩ := CFSG.Quasithin.H.exists_semilinear
    (CFSG.Quasithin.H.hasScalarCommutant_statedSL (K := K) le_rfl) (hψN ⟨⟨s, hsY⟩, rfl⟩)
  have hσ1 : σ = RingEquiv.refl K := by
    ext c
    have h1 := hσ c v₀
    rw [hfixℓ _ (ℓ.smul_mem c hv₀), hfixℓ _ hv₀] at h1
    have h2 : (σ c - c) • v₀ = 0 := by rw [sub_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact (sub_eq_zero.mp h3)
    · exact absurd h3 hv₀0
  rw [hσ1] at hσ
  obtain ⟨g, hg⟩ :=
    CFSG.Quasithin.H.exists_matAut_of_mem_linSub (show ψ ⟨s, hsY⟩ ∈ linSub from hσ)
  obtain ⟨k, hk⟩ := hS.isPGroup ⟨s, hsS⟩
  have hgk : g ^ 2 ^ k = 1 := by
    apply CFSG.Quasithin.H.matHom_injective
    rw [map_pow, map_one, CFSG.Quasithin.H.matHom_apply, ← hg, ← map_pow]
    have : (⟨s, hsY⟩ : ↥Y) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [this, map_one]
  have hdet : Matrix.GeneralLinearGroup.det g = 1 :=
    eq_one_of_pow_two_pow_eq_one hK (by rw [← map_pow, hgk, map_one])
  have hgSL : g ∈ CFSG.Open.StatedSL 2 K := by
    apply CFSG.Open.StatedAPI.mem_statedSL_of_det
    have := congrArg Units.val hdet
    simpa using this
  have hmem : ψ ⟨s, hsY⟩ ∈ natImage (CFSG.Open.StatedSL 2 K) := ⟨⟨g, hgSL⟩, hg.symm⟩
  rw [← hψL] at hmem
  obtain ⟨l, hl, hll⟩ := hmem
  have h1 := hψinj hll
  have h2 := Subgroup.mem_subgroupOf.mp hl
  rw [h1] at h2; exact h2

private theorem three_two_left_setup {K : Type} [Field K] [Fintype K] [CharP K 2]
    {Y S L T : Subgroup (MulAut W)} {m : ℕ} (hS : IsSylowIn 2 S Y)
    (hTP : IsFFStarOffender S T) {f : ↥(commV L) →* StdMod (Fin 2) K}
    (hfs : Function.Surjective f)
    (hcardM : Nat.card (StdMod (Fin 2) K) = 2 ^ m * 2 ^ m) (hTq : Nat.card ↥T = 2 ^ m)
    {ψ : ↥Y →* MulAut (StdMod (Fin 2) K)}
    (hψf : ∀ (y : ↥Y) (u : ↥(commV L)) (h : (y : MulAut W) u ∈ commV L),
      f ⟨_, h⟩ = ψ y (f u))
    {s : MulAut W} (hsS : s ∈ S)
    (hsfix : s ∈ fixingSubgroup (MulAut W) ((commV L ⊓ fixV T : Subgroup W) : Set W)) :
    2 ^ m ≤ Nat.card ↥(((fixV T).subgroupOf (commV L)).map f) ∧
      ∀ x ∈ ((fixV T).subgroupOf (commV L)).map f, ψ ⟨s, hS.le hsS⟩ x = x := by
  have hXcard : 2 ^ m ≤ Nat.card ↥(((fixV T).subgroupOf (commV L)).map f) := by
    have h1 := card_le_mul_card_map_fixV (mem_gomiOset_of_isFFStarOffender hTP).2.2.2 f hfs
    rw [hcardM, hTq] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  refine ⟨hXcard, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hsu : s u = u := by
    have h1 := (mem_fixingSubgroup_iff (MulAut W)).mp hsfix (u : W)
      (Subgroup.mem_inf.mpr ⟨u.2, Subgroup.mem_subgroupOf.mp hu⟩)
    simpa [MulAut.smul_def] using h1
  rw [← hψf ⟨s, hS.le hsS⟩ u (by rw [hsu]; exact u.2)]
  congr 1
  exact Subtype.ext hsu

private theorem gomiFact37Three_of_two_le
    {Y S L : Subgroup (MulAut W)} {m : ℕ} (hm : 2 ≤ m) (hP : (Pset Y).Nonempty)
    (hS : IsSylowIn 2 S Y) (hLY : L ≤ Y) (hsn : (L.subgroupOf Y).IsSubnormal)
    (hL : IsSLn ↥L 2 m) (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥)
    (hnat : BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m) : gomiCSP S L = S ⊓ L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn := subgroupOf_normal_of_isSubnormal_of_isSLn hLY hsn hm hL hC
  obtain ⟨K, _, _, hK, f, ψ, hfs, hfk, hψf, hψinj, hψL, hψN⟩ := exists_natSection hLY hLn hC hnat
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    CFSG.QuasithinUnique.Setup.SL2Modules.charP_two_of_card_eq
      (by rw [Fintype.card_eq_nat_card, hK])
  have hq : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
  have hcardM : Nat.card (StdMod (Fin 2) K) = 2 ^ m * 2 ^ m := by
    rw [CFSG.Quasithin.H.card_stdMod, Fintype.card_fin, hK, pow_two]
  set T := S ⊓ L with hTdef
  have hTS : T ≤ S := inf_le_left
  have hTL : T ≤ L := inf_le_right
  obtain ⟨hψmat, hfixL⟩ := natImage_and_card_le_of_fix_of_mem_of_ne_one hK hψL hψinj
  have hPT := le_inf_of_isFFStarOffender hS hLY hLn hm hC hnat
  have hPcard := pow_le_card_of_isFFStarOffender hLY hTL hfs hψf hfixL hPT hcardM
  have hTcard := card_le_pow_of_isPGroup_inf hm hS hL hTS hTL
  have hffJ := three_two_ffJ hS hP hPT hPcard hTcard
  have hJ := hffJ.1
  have hTq : Nat.card ↥T = 2 ^ m := by rw [hTdef]; exact hffJ.2.1
  have hTP : IsFFStarOffender S T := by rw [hTdef]; exact hffJ.2.2
  have hgomi : gomiCSP S L =
      S ⊓ fixingSubgroup (MulAut W) ((commV L ⊓ fixV T : Subgroup W) : Set W) := by
    unfold gomiCSP
    rw [hJ]
  rw [hgomi]
  apply le_antisymm
  · intro s hs
    obtain ⟨hsS, hsfix⟩ := Subgroup.mem_inf.mp hs
    refine ⟨hsS, ?_⟩
    have hsY : s ∈ Y := hS.le hsS
    obtain ⟨hXcard, hsX⟩ :=
      three_two_left_setup hS hTP hfs hcardM hTq hψf hsS hsfix
    obtain ⟨ℓ, hℓcard, hmemX, hXcard_eq⟩ :=
      three_two_left_line hK hψf hψinj hψmat hTP hTL hLY hXcard
    obtain ⟨v₀, hv₀, hv₀0⟩ := three_two_left_nonzero hm ℓ hℓcard hXcard hXcard_eq
    have hfixℓ := three_two_left_fix hsY hmemX hsX
    exact three_two_left_mem hK hS hψN hψL hψinj hsY hsS hv₀ hv₀0 hfixℓ
  · intro s hs
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hs).1, ?_⟩
    refine (mem_fixingSubgroup_iff (MulAut W)).mpr fun v hv => ?_
    simpa [MulAut.smul_def] using (Subgroup.mem_inf.mp hv).2 s hs

private theorem three_one_fieldAut {F : Type} [Field F] [Fintype F]
    (hFc : Fintype.card F = 2 ^ 1) : ∀ σ : F ≃+* F, σ = RingEquiv.refl F := by
  classical
  intro σ
  ext x
  have hx : x = 0 ∨ x = 1 := by
    by_contra h
    push Not at h
    have h01 : (0 : F) ≠ 1 := zero_ne_one
    have h1 : ({x, 0, 1} : Finset F).card ≤ Fintype.card F := Finset.card_le_univ _
    rw [hFc, Finset.card_insert_of_notMem (by simp [h.1, h.2]), Finset.card_pair h01] at h1
    omega
  rcases hx with rfl | rfl
  · simp
  · simp

omit [Finite W] in
private theorem three_one_norm {F : Type} [Field F] [Fintype F] [CharP F 2]
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (θ : ↥L ≃* SL(2, F))
    (hσ1 : ∀ σ : F ≃+* F, σ = RingEquiv.refl F)
    (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥) :
    ∀ k ∈ Y, (∀ l ∈ L, k * l * k⁻¹ ∈ L) → (∀ l ∈ L, k⁻¹ * l * k ∈ L) → k ∈ L := by
  intro k hkY hk hk'
  let φ : ↥L ≃* ↥L :=
    { toFun := fun l => ⟨k * l * k⁻¹, hk l l.2⟩
      invFun := fun l => ⟨k⁻¹ * l * k, hk' l l.2⟩
      left_inv := fun l => Subtype.ext (by simp [mul_assoc])
      right_inv := fun l => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun l l' => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨g, σ, hα⟩ := CFSG.CGT.Timmesfeld75.exists_eq_conj_sl2FieldAut (θ.symm.trans (φ.trans θ))
  rw [hσ1 σ, CFSG.CGT.Timmesfeld75.sl2FieldAut_refl] at hα
  set l₀ : ↥L := θ.symm g with hl₀
  have hconj : ∀ l : ↥L, k * l * k⁻¹ = l₀ * l * l₀⁻¹ := by
    intro l
    have h1 := hα (θ l)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.refl_apply] at h1
    have h2 := congrArg θ.symm h1
    rw [MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at h2
    have h3 := congrArg Subtype.val h2
    simpa [φ] using h3
  have hcomm : (l₀ : MulAut W)⁻¹ * k ∈ Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
    refine ⟨Y.mul_mem (Y.inv_mem (hLY l₀.2)) hkY, fun l hl => ?_⟩
    have h1 : k * l * k⁻¹ = (l₀ : MulAut W) * l * (l₀ : MulAut W)⁻¹ := by
      have := hconj ⟨l, hl⟩
      simpa using this
    calc l * ((l₀ : MulAut W)⁻¹ * k) =
          (l₀ : MulAut W)⁻¹ * ((l₀ : MulAut W) * l * (l₀ : MulAut W)⁻¹) * k := by group
      _ = (l₀ : MulAut W)⁻¹ * (k * l * k⁻¹) * k := by rw [h1]
      _ = (l₀ : MulAut W)⁻¹ * k * l := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcomm
  rw [← hcomm]
  exact l₀.2

omit [Finite W] in
private theorem three_one_normal {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hsn : (L.subgroupOf Y).IsSubnormal)
    (hnorm : ∀ k ∈ Y, (∀ l ∈ L, k * l * k⁻¹ ∈ L) → (∀ l ∈ L, k⁻¹ * l * k ∈ L) → k ∈ L) :
    (L.subgroupOf Y).Normal ∧ Y ≤ L := by
  set H := L.subgroupOf Y with hHdef
  have hnormY : ∀ k : ↥Y, k ∈ Subgroup.normalizer (H : Set ↥Y) → (k : MulAut W) ∈ L := by
    intro k hk
    have hk' := Subgroup.inv_mem _ hk
    refine hnorm k k.2 (fun l hl => ?_) (fun l hl => ?_)
    · have h1 := (Subgroup.mem_normalizer_iff.mp hk ⟨l, hLY hl⟩).mp
        (Subgroup.mem_subgroupOf.mpr hl)
      simpa using Subgroup.mem_subgroupOf.mp h1
    · have h1 := (Subgroup.mem_normalizer_iff.mp hk' ⟨l, hLY hl⟩).mp
        (Subgroup.mem_subgroupOf.mpr hl)
      simpa using Subgroup.mem_subgroupOf.mp h1
  have hHnorm : H.Normal := by
    suffices key : ∀ K : Subgroup ↥Y, K.IsSubnormal → H ≤ K → (H.subgroupOf K).Normal →
        H.Normal by
      rcases Subgroup.IsSubnormal.iff_eq_top_or_exists.mp hsn with h | ⟨K, hHK, hK, hN⟩
      · rw [h]
        exact Subgroup.normal_top
      · exact key K hK hHK.le hN
    intro K hK
    induction hK with
    | top =>
      intro hle hN
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle, top_le_iff] at hN
      exact Subgroup.normalizer_eq_top_iff.mp hN
    | step K K' hKK' _ hKn ih =>
      intro hHK hHn
      have hKN := (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hHn
      have hKH : K ≤ H := fun k hk => Subgroup.mem_subgroupOf.mpr (hnormY k (hKN hk))
      have hKeq : K = H := le_antisymm hKH hHK
      subst hKeq
      exact ih hKK' hKn
  have hYL : Y ≤ L := by
    intro y hy
    have h1 : (⟨y, hy⟩ : ↥Y) ∈ Subgroup.normalizer (H : Set ↥Y) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hHnorm]
      exact Subgroup.mem_top _
    exact hnormY _ h1
  exact ⟨hHnorm, hYL⟩

private theorem gomiFact37Three_one {Y S L : Subgroup (MulAut W)} (hP : (Pset Y).Nonempty)
    (hS : IsSylowIn 2 S Y) (hLY : L ≤ Y) (hsn : (L.subgroupOf Y).IsSubnormal)
    (hL : IsSLn ↥L 2 1) (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥) :
    gomiCSP S L = S ⊓ L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ 1 := by rw [Fintype.card_eq_nat_card, hF]
  have : CharP F 2 := CFSG.QuasithinUnique.Setup.SL2Modules.charP_two_of_card_eq hFc
  set θ : ↥L ≃* SL(2, F) := e.trans (specialLinearGroupEquivStatedSL 2 F).symm with hθ
  have hσ1 := three_one_fieldAut hFc
  have hnorm := three_one_norm hLY θ hσ1 hC
  obtain ⟨-, hYL⟩ := three_one_normal hLY hsn hnorm
  have hSL : S ≤ L := hS.le.trans hYL
  have hLcard : Nat.card L = 6 := by
    rw [Nat.card_congr θ.toEquiv, CFSG.GorensteinWalter.sl2_card_formula F, hF]
    norm_num
  have hScard : Nat.card S ≤ 2 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS.isPGroup
    have hdvd : Nat.card S ∣ 6 := hLcard ▸ Subgroup.card_dvd_of_le hSL
    rw [hk] at hdvd ⊢
    have h3 : (2 : ℕ) ^ k ∣ 2 := by
      have hcop : Nat.Coprime (2 ^ k) 3 :=
        Nat.Coprime.pow_left k (by norm_num)
      exact hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
    exact Nat.le_of_dvd (by norm_num) h3
  obtain ⟨B, hB⟩ := exists_isFFStarOffender_of_isSylowIn hS hP
  have hBcard : 2 ≤ Nat.card B := by
    have := (Subgroup.one_lt_card_iff_ne_bot B).mpr hB.2.1
    omega
  have hBS : B = S := Subgroup.eq_of_le_of_card_ge hB.1 (hScard.trans hBcard)
  have hSP : IsFFStarOffender S S := hBS ▸ hB
  have hSJ : S ≤ ffJ S := le_iSup₂_of_le S hSP le_rfl
  rw [inf_eq_left.mpr hSL]
  apply le_antisymm inf_le_left
  intro s hs
  refine Subgroup.mem_inf.mpr ⟨hs, (mem_fixingSubgroup_iff (MulAut W)).mpr fun v hv => ?_⟩
  have := (Subgroup.mem_inf.mp hv).2 s (hSJ hs)
  simpa [MulAut.smul_def] using this

theorem gomiFact37Three_holds : GomiFact37Three := by
  intro W _ _ hW Y S L m hm hP hS hLY hsn hL hC hnat
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    exact gomiFact37Three_one hP hS hLY hsn hL hC
  · exact gomiFact37Three_of_two_le hm2 hP hS hLY hsn hL hC hnat

end CFSG.GroupTheory

end
