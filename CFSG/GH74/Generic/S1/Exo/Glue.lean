module

public import CFSG.GH74.Generic.S1.Exo.Setup
public import CFSG.GH74.Generic.S1.Exo.NbDefs
public import CFSG.GH74.GLS.TwoThin.G.Reduction
public import CFSG.GH74.GLS.AssemblyBridge
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

theorem proj_injective_of_quasisimple {v : G} {B : Subgroup G} (hBv : B ≤ centralizer ({v} : Set G))
    (hq : IsQuasisimple ↥B) (hZ : ∀ z ∈ center ↥B, z * z = 1) (he : ∃ e ∈ B, e * e = 1 ∧ e ≠ 1) :
    Function.Injective ((proj v).comp (Subgroup.inclusion hBv)) := by
  set φ₀ : ↥B →* CentralizerBar v := (proj v).comp (Subgroup.inclusion hBv) with hφ₀
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker φ₀) with hk | hk
  · exfalso
    obtain ⟨e, heB, he2, he1⟩ := he
    have h1 : φ₀ ⟨e, heB⟩ = 1 := by
      have : (⟨e, heB⟩ : ↥B) ∈ φ₀.ker := by rw [hk]; trivial
      exact this
    exact he1 (S45.eq_one_of_proj_eq_one_of_sq (hBv heB) h1 he2)
  · rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    have hbZ : b ∈ center ↥B := hk hb
    have hb2 : b * b = 1 := hZ b hbZ
    have h1 : φ₀ b = 1 := hb
    exact Subtype.ext (S45.eq_one_of_proj_eq_one_of_sq (hBv b.2) h1 (congrArg Subtype.val hb2))

theorem exists_mulEquiv_barSub {v : G} {B : Subgroup G} (hBv : B ≤ centralizer ({v} : Set G))
    (hq : IsQuasisimple ↥B) (hZ : ∀ z ∈ center ↥B, z * z = 1) (he : ∃ e ∈ B, e * e = 1 ∧ e ≠ 1) :
    ∃ φ : ↥B ≃* ↥(S45.barSub v B),
      ∀ b : ↥B, ((φ b : ↥(S45.barSub v B)) : CentralizerBar v) = proj v ⟨(b : G), hBv b.2⟩ := by
  have hinj := proj_injective_of_quasisimple hBv hq hZ he
  set φ₀ : ↥B →* CentralizerBar v := (proj v).comp (Subgroup.inclusion hBv) with hφ₀
  have hrange : φ₀.range = S45.barSub v B := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact S45.proj_mem_barSub (hBv j.2) j.2
    · intro hy
      obtain ⟨g, hg, hgJ, rfl⟩ := S45.mem_barSub.1 hy
      exact ⟨⟨g, hgJ⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun b => rfl⟩

theorem center_eq_zpowers_of_card_two {B : Type*} [Group B] [Finite B] {e : B}
    (hcard : Nat.card (center B) = 2) (he : e ∈ center B) (he1 : e ≠ 1) :
    center B = Subgroup.zpowers e := by
  have hord : orderOf e = 2 := by
    have h1 : orderOf e ∣ 2 := hcard ▸ Subgroup.orderOf_dvd_natCard (center B) he
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) he1
    · exact h
  have hle : Subgroup.zpowers e ≤ center B := (Subgroup.zpowers_le).2 he
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, Nat.card_zpowers, hord]


section Blocks

variable (mo : ModelOps S) {y c : G} (D : LayerData y S)

@[expose] noncomputable def blkA : Subgroup G := (mo.ops.blk 0 1).map D.ι

@[expose] noncomputable def blkB : Subgroup G := (mo.ops.blk 2 3).map D.ι

theorem blkA_quasi : IsQuasisimple ↥(blkA mo D) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((mo.ops.blk 0 1).equivMapOfInjective D.ι D.ι_injective) (mo.blkq 0 1 (by decide))

theorem blkB_quasi : IsQuasisimple ↥(blkB mo D) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((mo.ops.blk 2 3).equivMapOfInjective D.ι D.ι_injective) (mo.blkq 2 3 (by decide))

theorem blkA_comm_blkB : ∀ a ∈ blkA mo D, ∀ b ∈ blkB mo D, a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, mo.ops.commute 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a ha b hb]

theorem blkA_le_cent (hDc : D.ι mo.z0 = c) : blkA mo D ≤ centralizer ({c} : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_singleton_iff, ← hDc, ← map_mul, ← map_mul, mo.z0_cent a ha]

theorem blkB_le_cent (hDc : D.ι mo.z0 = c) : blkB mo D ≤ centralizer ({c} : Set G) := by
  rintro _ ⟨b, hb, rfl⟩
  rw [mem_centralizer_singleton_iff, ← hDc, ← map_mul, ← map_mul,
    mo.ops.commute 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) b hb mo.z0 mo.z0_mem]

theorem c_mem_blkA (hDc : D.ι mo.z0 = c) : c ∈ blkA mo D := ⟨mo.z0, mo.z0_mem, hDc⟩

theorem ι_neg_mul_z0 (hDc : D.ι mo.z0 = c) (hy : orderOf y = 2) (hyK : xbar y ∈ D.K) :
    D.ι (mo.neg * mo.z0) = y * c := by
  rw [map_mul, ι_neg_eq mo D hy hyK, hDc]

theorem yc_mem_blkB (hDc : D.ι mo.z0 = c) (hy : orderOf y = 2) (hyK : xbar y ∈ D.K) :
    y * c ∈ blkB mo D := by
  refine ⟨mo.neg * mo.z0, mo.pf.neg_mul 2 3 0 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) mo.neg (mo.neg_mem_center) mo.neg_sq mo.neg_ne mo.z0 mo.z0_mem mo.z0_sq
    mo.z0_ne, ?_⟩
  exact ι_neg_mul_z0 mo D hDc hy hyK

end Blocks


section Normalize

variable (mo : ModelOps S)

theorem exists_layer_with_z0 (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) (e : ↥K ≃* ↥S) {c : G}
    (hc : c ∈ centralizer ({x} : Set G)) (hc2 : orderOf c = 2)
    (hcL : (⟨c, hc⟩ : ↥(centralizer ({x} : Set G))) ∈ liftL x K) (hcne : barOf hc ≠ xbar x) :
    ∃ D : LayerData x S, D.K = K ∧ D.ι mo.z0 = c := by
  classical
  have hx : orderOf x = 2 := hset.inv
  have hxK : xbar x ∈ K := hset.shape.2
  set D₀ := layerOf hExact hset hfront e with hD₀
  obtain ⟨s, hs⟩ : ∃ s : ↥S, D₀.ι s = c := by
    refine ⟨D₀.liftIso.symm ⟨⟨c, hc⟩, hcL⟩, ?_⟩
    have h1 : D₀.ιC (D₀.liftIso.symm ⟨⟨c, hc⟩, hcL⟩) = ⟨c, hc⟩ := by
      change (((D₀.liftIso (D₀.liftIso.symm ⟨⟨c, hc⟩, hcL⟩)) : ↥(liftL x D₀.K)) :
        ↥(centralizer ({x} : Set G))) = _
      rw [MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val h1
  have hc2' : c * c = 1 := by rw [← sq, ← hc2]; exact pow_orderOf_eq_one c
  have hs2 : s * s = 1 := D₀.ι_injective (by rw [map_mul, hs, hc2', map_one])
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc2
    omega
  have hs1 : s ≠ 1 := fun h => hc1 (by rw [← hs, h, map_one])
  have hsneg : s ≠ mo.neg := by
    intro h
    apply hcne
    have hcx : c = x := by rw [← hs, h]; exact ι_neg_eq mo D₀ hx hxK
    subst hcx
    rfl
  obtain ⟨P, hP⟩ := mo.norm s hs2 hs1 hsneg
  refine ⟨D₀.conjIso (MulAut.conj P), rfl, ?_⟩
  rw [LayerData.conjIso_ι, MulAut.conj_symm_apply, ← hs]
  congr 1
  rw [← hP]
  group

end Normalize


section Global

variable (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) (hkgh : KGH G)
  {c : G} (hc2 : orderOf c = 2)

include hs hn hc2 in
omit [Finite G] in
theorem barC_proper : centralizer ({c} : Set G) ≠ ⊤ := GLS.centralizer_involution_ne_top hs hn hc2

theorem barC_core : pPrimeCore 2 (CentralizerBar c) = ⊥ :=
  CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two

include hgen in
theorem barC_gen4 : Gen4 (CentralizerBar c) := TwoThin.gen4_barQ hgen c

include hs hn hkgh hc2 in
theorem barC_kgroup : IsKGroupNative (CentralizerBar c) :=
  CFSG.SectionRank.IsKGroupCat.quotient
    (isKGroupNative_of_kgh hkgh (barC_proper hs hn hc2)) (pPrimeCore 2 ↥(centralizer ({c} : Set G)))

include hs hn hkgh hc2 in
omit [Finite G] in
theorem barC_gh : ∀ (A : Subgroup (CentralizerBar c)) (B : Subgroup ↥A) [B.Normal],
    IsSimpleGroup (↥A ⧸ B) → (∃ a b : ↥A ⧸ B, a * b ≠ b * a) → GHList (↥A ⧸ B) := by
  intro A B _ hsimple hnonab
  set C : Subgroup G := centralizer ({c} : Set G) with hC
  let π : ↥C →* CentralizerBar c := QuotientGroup.mk' (pPrimeCore 2 ↥C)
  let Apre : Subgroup ↥C := A.comap π
  let H : Subgroup G := Apre.map C.subtype
  have hHle : H ≤ C := by
    rintro _ ⟨c', -, rfl⟩
    exact c'.2
  have hH : H ≠ ⊤ := fun h => barC_proper hs hn hc2 (top_le_iff.1 (h ▸ hHle))
  let e₁ : ↥Apre ≃* ↥H := Apre.equivMapOfInjective C.subtype C.subtype_injective
  let q : ↥Apre →* ↥A := (π.comp Apre.subtype).codRestrict A fun k => k.2
  have hq' : Function.Surjective q := by
    intro k
    obtain ⟨c', hc'⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥C) (k : CentralizerBar c)
    exact ⟨⟨c', show π c' ∈ A by rw [hc']; exact k.2⟩, Subtype.ext hc'⟩
  let f : ↥H →* ↥A ⧸ B := ((QuotientGroup.mk' B).comp q).comp e₁.symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((QuotientGroup.mk'_surjective _).comp hq').comp e₁.symm.surjective
  exact ghList_of_surjection hkgh hH f hf hsimple hnonab

end Global



theorem natCard_center_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (center A) = Nat.card (center B) := by
  have h1 : (center A).map e.toMonoidHom = center B := Subgroup.map_center_eq e
  rw [← h1]
  exact (Nat.card_congr ((center A).equivMapOfInjective e.toMonoidHom e.injective).toEquiv)

section Fields

variable (mo : ModelOps S) {y c : G} (D : LayerData y S)

theorem blk_center_card (a b : Fin 4) (hab : a ≠ b) : Nat.card (center ↥(mo.ops.blk a b)) = 2 := by
  obtain ⟨F₀, _, _, hF₀, ⟨e⟩⟩ := mo.blk_model a b hab
  have h2 : (2 : F₀) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF₀]; exact mo.qM_odd)
  rw [← natCard_center_eq_of_mulEquiv e]
  exact natCard_center_sl2_eq_two h2

theorem blkA_center_card : Nat.card (center ↥(blkA mo D)) = 2 := by
  change Nat.card (center ↥((mo.ops.blk 0 1).map D.ι)) = 2
  rw [← natCard_center_eq_of_mulEquiv ((mo.ops.blk 0 1).equivMapOfInjective D.ι D.ι_injective)]
  exact blk_center_card mo 0 1 (by decide)

theorem blkB_center_card : Nat.card (center ↥(blkB mo D)) = 2 := by
  change Nat.card (center ↥((mo.ops.blk 2 3).map D.ι)) = 2
  rw [← natCard_center_eq_of_mulEquiv ((mo.ops.blk 2 3).equivMapOfInjective D.ι D.ι_injective)]
  exact blk_center_card mo 2 3 (by decide)

theorem c_mem_center_blkA (hDc : D.ι mo.z0 = c) :
    (⟨c, c_mem_blkA mo D hDc⟩ : ↥(blkA mo D)) ∈ center ↥(blkA mo D) := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨_, ⟨a, ha, rfl⟩⟩
  apply Subtype.ext
  change D.ι a * c = c * D.ι a
  rw [← hDc, ← map_mul, ← map_mul, mo.z0_cent a ha]

theorem blkA_center_eq (hDc : D.ι mo.z0 = c) (hc1 : c ≠ 1) :
    center ↥(blkA mo D) = zpowers (⟨c, c_mem_blkA mo D hDc⟩ : ↥(blkA mo D)) :=
  center_eq_zpowers_of_card_two (blkA_center_card mo D) (c_mem_center_blkA mo D hDc)
    (fun h => hc1 (congrArg Subtype.val h))

theorem yc_mem_center_blkB (hDc : D.ι mo.z0 = c) (hy : orderOf y = 2) (hyK : xbar y ∈ D.K) :
    (⟨y * c, yc_mem_blkB mo D hDc hy hyK⟩ : ↥(blkB mo D)) ∈ center ↥(blkB mo D) := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨_, ⟨b, hb, rfl⟩⟩
  apply Subtype.ext
  change D.ι b * (y * c) = (y * c) * D.ι b
  rw [← ι_neg_mul_z0 mo D hDc hy hyK, ← map_mul, ← map_mul]
  congr 1
  have h1 := Subgroup.mem_center_iff.1 (mo.neg_mem_center) b
  have h2 := mo.ops.commute 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) b hb mo.z0 mo.z0_mem
  calc b * (mo.neg * mo.z0) = (b * mo.neg) * mo.z0 := by rw [mul_assoc]
    _ = (mo.neg * b) * mo.z0 := by rw [h1]
    _ = mo.neg * (b * mo.z0) := by rw [mul_assoc]
    _ = mo.neg * (mo.z0 * b) := by rw [h2]
    _ = (mo.neg * mo.z0) * b := by rw [mul_assoc]

theorem blkB_center_eq (hDc : D.ι mo.z0 = c) (hy : orderOf y = 2) (hyK : xbar y ∈ D.K)
    (hyc1 : y * c ≠ 1) :
    center ↥(blkB mo D) = zpowers (⟨y * c, yc_mem_blkB mo D hDc hy hyK⟩ : ↥(blkB mo D)) :=
  center_eq_zpowers_of_card_two (blkB_center_card mo D) (yc_mem_center_blkB mo D hDc hy hyK)
    (fun h => hyc1 (congrArg Subtype.val h))

end Fields


section JFields

variable (mo : ModelOps S) {x c : G} (D : LayerData x S)

theorem eq_one_or_of_mem_zpowers_of_sq {B : Type*} [Group B] {e z : B} (he : e * e = 1) (he1 : e ≠ 1)
    (hz : z ∈ Subgroup.zpowers e) : z = 1 ∨ z = e := by
  have hord : orderOf e = 2 := orderOf_eq_prime (by rw [pow_two]; exact he) he1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rw [← zpow_mod_orderOf, hord]
  push_cast
  rcases hk with h | h <;> rw [h] <;> simp


end JFields

section BarSubGeneric

theorem barSub_cent {c : G} {B : Subgroup G} (hBv : B ≤ centralizer ({c} : Set G))
    (hq : IsQuasisimple ↥B) {e : G} (heB : e ∈ B) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hcen : center ↥B = Subgroup.zpowers (⟨e, heB⟩ : ↥B)) :
    ∀ a ∈ S45.barSub c B, (∀ b ∈ S45.barSub c B, a * b = b * a) →
      a = 1 ∨ a = proj c ⟨e, hBv heB⟩ := by
  have he2' : (⟨e, heB⟩ : ↥B) * ⟨e, heB⟩ = 1 := Subtype.ext he2
  have he1' : (⟨e, heB⟩ : ↥B) ≠ 1 := fun h => he1 (congrArg Subtype.val h)
  have hZ : ∀ z ∈ center ↥B, z * z = 1 := by
    intro z hz
    rw [hcen] at hz
    rcases eq_one_or_of_mem_zpowers_of_sq he2' he1' hz with h | h
    · rw [h, one_mul]
    · rw [h]; exact he2'
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_barSub hBv hq hZ ⟨e, heB, he2, he1⟩
  intro a ha hcomm
  set a₀ : ↥B := φ.symm ⟨a, ha⟩ with ha₀
  have haφ : (φ a₀ : CentralizerBar c) = a := by
    rw [ha₀, MulEquiv.apply_symm_apply]
  have ha₀c : a₀ ∈ center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro b₀
    apply φ.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    change (φ b₀ : CentralizerBar c) * (φ a₀ : CentralizerBar c) =
      (φ a₀ : CentralizerBar c) * (φ b₀ : CentralizerBar c)
    rw [haφ]
    exact (hcomm _ (φ b₀).2).symm
  rw [hcen] at ha₀c
  rcases eq_one_or_of_mem_zpowers_of_sq he2' he1' ha₀c with h | h
  · left
    rw [← haφ, h, map_one]
    rfl
  · right
    rw [← haφ, h, hφ]

theorem barSub_hasSL2Model {c : G} {B : Subgroup G} (hBv : B ≤ centralizer ({c} : Set G))
    (hq : IsQuasisimple ↥B) (hZ : ∀ z ∈ center ↥B, z * z = 1) (he : ∃ e ∈ B, e * e = 1 ∧ e ≠ 1)
    {q : ℕ} {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = q)
    (e : SL(2, F₀) ≃* ↥B) : HasSL2Model ↥(S45.barSub c B) (fun r => r = q) := by
  obtain ⟨φ, -⟩ := exists_mulEquiv_barSub hBv hq hZ he
  exact ⟨F₀, inferInstance, inferInstance, hF₀,
    ⟨(e.trans φ).symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F₀).symm.symm⟩⟩


omit [Finite G] in
theorem barSub_sup_le {c : G} {A B : Subgroup G} (hA : A ≤ centralizer ({c} : Set G))
    (hB : B ≤ centralizer ({c} : Set G)) :
    S45.barSub c (A ⊔ B) ≤ S45.barSub c A ⊔ S45.barSub c B := by
  unfold S45.barSub
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem perfect_le_barSub_resCent {c u : G} (hu : u ∈ centralizer ({c} : Set G)) (hu2 : u * u = 1)
    {M : Subgroup (CentralizerBar c)} (hM : ⁅M, M⁆ = M)
    (hMc : M ≤ centralizer ({proj c ⟨u, hu⟩} : Set (CentralizerBar c))) :
    M ≤ S45.barSub c (resCent ({u, c} : Set G)) := by
  classical
  set C : Subgroup G := centralizer ({c} : Set G) with hC
  set Yc : Subgroup ↥C := (centralizer ({u} : Set G)).subgroupOf C with hYc
  set P : Subgroup ↥C := Yc ⊓ M.comap (proj c) with hP
  let f : ↥P →* ↥M := ((proj c).comp P.subtype).codRestrict M fun p => p.2.2
  have hf : Function.Surjective f := by
    intro m
    have hm1 : m.1 * proj c ⟨u, hu⟩ = proj c ⟨u, hu⟩ * m.1 :=
      (mem_centralizer_singleton_iff.1 (hMc m.2))
    obtain ⟨g, hg1, hg2⟩ := proj_cent c (u := (⟨u, hu⟩ : ↥C))
      (by apply Subtype.ext; exact hu2) m.1 hm1
    refine ⟨⟨g, ⟨?_, ?_⟩⟩, Subtype.ext hg2⟩
    · change (g : G) ∈ centralizer ({u} : Set G)
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hg1
    · show proj c g ∈ M
      rw [hg2]; exact m.2
  have hperfM : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr hM
  have h1 := finite_perfectResidual_surjects_to_perfect_image f hf
  set Q' : Subgroup ↥C := perfectResidualOf P with hQ'
  set Q : Subgroup G := Q'.map C.subtype with hQ
  have hQ'perf : ⁅Q', Q'⁆ = Q' := perfectResidualOf_perfect P
  have hQperf : ⁅Q, Q⁆ = Q := by
    rw [hQ, ← Subgroup.map_commutator, hQ'perf]
  have hQ'P : Q' ≤ P := Subgroup.map_subtype_le _
  have hQc : Q ≤ centralizer ({u, c} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl
    · have := (hQ'P hq).1
      change (q : G) ∈ centralizer ({h} : Set G) at this
      exact (mem_centralizer_singleton_iff.1 this).symm
    · exact (mem_centralizer_singleton_iff.1 q.2).symm
  have hQres : Q ≤ resCent ({u, c} : Set G) := le_resCent hQc hQperf
  intro m hm
  have hmM : m ∈ M := hm
  have hmtop : (⟨m, hmM⟩ : ↥M) ∈ Subgroup.map f (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥P) := by rw [h1]; trivial
  obtain ⟨l, hl, hlm⟩ := hmtop
  have hlQ' : (l : ↥C) ∈ Q' := ⟨l, hl, rfl⟩
  refine S45.mem_barSub.2 ⟨(l : ↥C), (l : ↥C).2, hQres ⟨(l : ↥C), hlQ', rfl⟩, ?_⟩
  have := congrArg Subtype.val hlm
  exact this


omit [Finite G] in
theorem barSub_le_cent {c u : G} (hu : u ∈ centralizer ({c} : Set G)) {B : Subgroup G}
    (hBu : B ≤ centralizer ({u} : Set G)) :
    S45.barSub c B ≤ centralizer ({proj c ⟨u, hu⟩} : Set (CentralizerBar c)) := by
  intro y hy
  obtain ⟨b, hb, hbB, rfl⟩ := S45.mem_barSub.1 hy
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.1 (hBu hbB)

theorem barSub_normal_in_cent {c u : G} (hu : u ∈ centralizer ({c} : Set G)) (hu2 : u * u = 1)
    {B : Subgroup G} (hBc : B ≤ centralizer ({c} : Set G))
    (hnorm : ∀ g ∈ centralizer ({c} : Set G) ⊓ centralizer ({u} : Set G), ∀ b ∈ B, g * b * g⁻¹ ∈ B) :
    ((S45.barSub c B).subgroupOf
      (centralizer ({proj c ⟨u, hu⟩} : Set (CentralizerBar c)))).Normal := by
  constructor
  intro n hn g'
  have hn' : (n : CentralizerBar c) ∈ S45.barSub c B := hn
  obtain ⟨b, hb, hbB, hbn⟩ := S45.mem_barSub.1 hn'
  have hg'1 : (g' : CentralizerBar c) * proj c ⟨u, hu⟩ = proj c ⟨u, hu⟩ * (g' : CentralizerBar c) :=
    mem_centralizer_singleton_iff.1 g'.2
  obtain ⟨g, hg1, hg2⟩ := proj_cent c (u := (⟨u, hu⟩ : ↥(centralizer ({c} : Set G))))
    (by apply Subtype.ext; exact hu2) (g' : CentralizerBar c) hg'1
  have hgu : (g : G) ∈ centralizer ({u} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hg1
  have hgb : (g : G) * b * (g : G)⁻¹ ∈ B := hnorm g ⟨g.2, hgu⟩ b hbB
  have hgbC : (g : G) * b * (g : G)⁻¹ ∈ centralizer ({c} : Set G) := hBc hgb
  show ((g' * n * g'⁻¹ : ↥(centralizer ({proj c ⟨u, hu⟩} : Set (CentralizerBar c)))) :
    CentralizerBar c) ∈ S45.barSub c B
  have : ((g' * n * g'⁻¹ : ↥(centralizer ({proj c ⟨u, hu⟩} : Set (CentralizerBar c)))) :
      CentralizerBar c) = proj c ⟨(g : G) * b * (g : G)⁻¹, hgbC⟩ := by
    change (g' : CentralizerBar c) * (n : CentralizerBar c) * (g' : CentralizerBar c)⁻¹ = _
    rw [← hg2, ← hbn]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [this]
  exact S45.proj_mem_barSub hgbC hgb

theorem isComponent_barSub_cent {c u : G} (hu : u ∈ centralizer ({c} : Set G)) (hu2 : u * u = 1)
    {B : Subgroup G} (hBc : B ≤ centralizer ({c} : Set G)) (hBu : B ≤ centralizer ({u} : Set G))
    (hq : IsQuasisimple ↥B) (hZ : ∀ z ∈ center ↥B, z * z = 1) (he : ∃ e ∈ B, e * e = 1 ∧ e ≠ 1)
    (hnorm : ∀ g ∈ centralizer ({c} : Set G) ⊓ centralizer ({u} : Set G), ∀ b ∈ B, g * b * g⁻¹ ∈ B) :
    IsComponent ((S45.barSub c B).subgroupOf
      (centralizer ({proj c ⟨u, hu⟩} : Set (CentralizerBar c)))) := by
  obtain ⟨φ, -⟩ := exists_mulEquiv_barSub hBc hq hZ he
  have hle := barSub_le_cent hu hBu
  refine ⟨?_, (barSub_normal_in_cent hu hu2 hBc hnorm).isSubnormal⟩
  have hqJ : IsQuasisimple ↥(S45.barSub c B) := CFSG.LocalCores.isQuasisimple_of_mulEquiv φ hq
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hqJ

end BarSubGeneric


section Assembly

variable (mo : ModelOps S) {x c : G} (D : LayerData x S)

theorem blk_normalized (hDc : D.ι mo.z0 = c) :
    (∀ g ∈ centralizer ({c} : Set G) ⊓ centralizer ({x} : Set G), ∀ b ∈ blkA mo D, g * b * g⁻¹ ∈ blkA mo D) ∧
    (∀ g ∈ centralizer ({c} : Set G) ⊓ centralizer ({x} : Set G), ∀ b ∈ blkB mo D, g * b * g⁻¹ ∈ blkB mo D) := by
  have hn := layerPair_normal mo.ops mo.pf mo.blkq D (a := 2) (b := 3) (c := 0) (d := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) mo.z0_mem mo.z0_sq
    mo.z0_ne mo.z0_cent
  rw [hDc] at hn
  refine ⟨fun g hg b hb => ?_, fun g hg b hb => ?_⟩
  · have := (hn g ⟨hg.2, hg.1⟩).2
    have h2 : g * b * g⁻¹ ∈ ((mo.ops.blk 0 1).map D.ι).map (MulAut.conj g).toMonoidHom :=
      ⟨b, hb, by simp [MulAut.conj_apply]⟩
    rw [this] at h2
    exact h2
  · have := (hn g ⟨hg.2, hg.1⟩).1
    have h2 : g * b * g⁻¹ ∈ ((mo.ops.blk 2 3).map D.ι).map (MulAut.conj g).toMonoidHom :=
      ⟨b, hb, by simp [MulAut.conj_apply]⟩
    rw [this] at h2
    exact h2


theorem nbhdHyp_of_classical (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G)
    (hkgh : KGH G) (hx : orderOf x = 2) (hxK : xbar x ∈ D.K) (hDc : D.ι mo.z0 = c) (hc2 : orderOf c = 2)
    (hcx : c ≠ x) (hq5 : 5 ≤ mo.qM)
    (hgrowth : ¬ layer (CentralizerBar c) ≤ S45.barSub c (resCent ({x, c} : Set G))) :
    ∃ (y : CentralizerBar c) (J₂ J₄ : Subgroup (CentralizerBar c)),
      NbhdHyp (CentralizerBar c) mo.qM (xbar c) y J₂ J₄ := by
  classical
  have hcC : c ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hcx' : c ∈ centralizer ({x} : Set G) := hDc ▸ D.ι_mem_cent _
  have hxc : x ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.2
    (mem_centralizer_singleton_iff.1 hcx').symm
  have hxcC : x * c ∈ centralizer ({c} : Set G) := Subgroup.mul_mem _ hxc hcC
  have hc2' : c * c = 1 := by rw [← sq, ← hc2]; exact pow_orderOf_eq_one c
  have hx2' : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc2
    omega
  have hcomm : x * c = c * x := (mem_centralizer_singleton_iff.1 hcx').symm
  have hxc2 : (x * c) * (x * c) = 1 := by
    calc x * c * (x * c) = x * (c * x) * c := by group
      _ = x * (x * c) * c := by rw [← hcomm]
      _ = (x * x) * (c * c) := by group
      _ = 1 := by rw [hx2', hc2', one_mul]
  have hxc1 : x * c ≠ 1 := by
    intro h
    have : x = c⁻¹ := eq_inv_of_mul_eq_one_left h
    apply hcx
    rw [this]
    exact eq_inv_of_mul_eq_one_left hc2'
  have hBA := blkA_le_cent mo D hDc
  have hBB := blkB_le_cent mo D hDc
  have hqA := blkA_quasi mo D
  have hqB := blkB_quasi mo D
  have hcA := c_mem_blkA mo D hDc
  have hycB := yc_mem_blkB mo D hDc hx hxK
  have hcenA := blkA_center_eq mo D hDc hc1
  have hcenB := blkB_center_eq mo D hDc hx hxK hxc1
  have hZA : ∀ z ∈ center ↥(blkA mo D), z * z = 1 := by
    intro z hz
    rw [hcenA] at hz
    have h2 : (⟨c, hcA⟩ : ↥(blkA mo D)) * ⟨c, hcA⟩ = 1 := Subtype.ext hc2'
    rcases eq_one_or_of_mem_zpowers_of_sq h2 (fun h => hc1 (congrArg Subtype.val h)) hz with h | h
    · rw [h, one_mul]
    · rw [h]; exact h2
  have hZB : ∀ z ∈ center ↥(blkB mo D), z * z = 1 := by
    intro z hz
    rw [hcenB] at hz
    have h2 : (⟨x * c, hycB⟩ : ↥(blkB mo D)) * ⟨x * c, hycB⟩ = 1 := Subtype.ext hxc2
    rcases eq_one_or_of_mem_zpowers_of_sq h2 (fun h => hxc1 (congrArg Subtype.val h)) hz with h | h
    · rw [h, one_mul]
    · rw [h]; exact h2
  have heA : ∃ e ∈ blkA mo D, e * e = 1 ∧ e ≠ 1 := ⟨c, hcA, hc2', hc1⟩
  have heB : ∃ e ∈ blkB mo D, e * e = 1 ∧ e ≠ 1 := ⟨x * c, hycB, hxc2, hxc1⟩
  obtain ⟨hnA, hnB⟩ := blk_normalized mo D hDc
  have hBAx : blkA mo D ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨a, -, rfl⟩
    exact D.ι_mem_cent a
  have hBBx : blkB mo D ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨a, -, rfl⟩
    exact D.ι_mem_cent a
  set ybar : CentralizerBar c := proj c ⟨x * c, hxcC⟩ with hybar
  have hwy : xbar c * ybar = proj c ⟨x, hxc⟩ := by
    change proj c ⟨c, hcC⟩ * proj c ⟨x * c, hxcC⟩ = proj c ⟨x, hxc⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change c * (x * c) = x
    calc c * (x * c) = (c * x) * c := by rw [mul_assoc]
      _ = (x * c) * c := by rw [← hcomm]
      _ = x * (c * c) := by rw [mul_assoc]
      _ = x := by rw [hc2', mul_one]
  refine ⟨ybar, S45.barSub c (blkA mo D), S45.barSub c (blkB mo D), ?_⟩
  obtain ⟨F₀, _, _, hF₀, ⟨e₀⟩⟩ := mo.blk_model 0 1 (by decide)
  obtain ⟨F₁, _, _, hF₁, ⟨e₁⟩⟩ := mo.blk_model 2 3 (by decide)
  have hmodA : HasSL2Model ↥(S45.barSub c (blkA mo D)) (fun r => r = mo.qM) :=
    barSub_hasSL2Model hBA hqA hZA heA hF₀
      (e₀.trans ((mo.ops.blk 0 1).equivMapOfInjective D.ι D.ι_injective))
  have hmodB : HasSL2Model ↥(S45.barSub c (blkB mo D)) (fun r => r = mo.qM) :=
    barSub_hasSL2Model hBB hqB hZB heB hF₁
      (e₁.trans ((mo.ops.blk 2 3).equivMapOfInjective D.ι D.ι_injective))
  have hcentA := barSub_cent hBA hqA hcA hc2' hc1 hcenA
  have hcentB := barSub_cent hBB hqB hycB hxc2 hxc1 hcenB
  have hres_le : S45.barSub c (resCent ({x, c} : Set G)) ≤
      S45.barSub c (blkA mo D) ⊔ S45.barSub c (blkB mo D) := by
    have h1 : resCent ({x, c} : Set G) ≤ blkB mo D ⊔ blkA mo D := resCent_le_pair mo D hDc
    refine (S45.barSub_mono h1).trans ?_
    refine (barSub_sup_le hBB hBA).trans ?_
    rw [sup_comm]
  have hPair := layerPair_isPCompIn mo.ops mo.pf mo.blkq D (a := 2) (b := 3) (c := 0) (d := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) mo.z0_mem mo.z0_sq
    mo.z0_ne mo.z0_cent
  rw [hDc] at hPair
  have hlayB : S45.barSub c (blkB mo D) ≤ layer (CentralizerBar c) :=
    barSub_le_layer_of_isPCompIn hx hxc hPair.1
  have hlayA : S45.barSub c (blkA mo D) ≤ layer (CentralizerBar c) :=
    barSub_le_layer_of_isPCompIn hx hxc hPair.2
  have hx2'' : x * x = 1 := hx2'
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hybar_sq : ybar * ybar = 1 := by
    rw [hybar, ← map_mul]
    have : (⟨x * c, hxcC⟩ : ↥(centralizer ({c} : Set G))) * ⟨x * c, hxcC⟩ = 1 := Subtype.ext hxc2
    rw [this, map_one]
  have hybar_ne : ybar ≠ 1 := fun h => hxc1 (S45.eq_one_of_proj_eq_one_of_sq hxcC h hxc2)
  have hw_ne_y : xbar c ≠ ybar := by
    intro h
    have h1 : proj c ⟨x, hxc⟩ = 1 := by
      rw [← hwy, ← h]
      exact xbar_mul_self hc2
    exact hx1 (S45.eq_one_of_proj_eq_one_of_sq hxc h1 hx2')
  have hcenterB := yc_mem_center_blkB mo D hDc hx hxK
  have balx : ∀ L : Subgroup ↥(centralizer ({proj c ⟨x, hxc⟩} : Set (CentralizerBar c))),
      IsComponent L → L.map (centralizer ({proj c ⟨x, hxc⟩} : Set (CentralizerBar c))).subtype ≤
        S45.barSub c (blkA mo D) ⊔ S45.barSub c (blkB mo D) := by
    intro L hL
    have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
    have hMperf : ⁅L.map (centralizer ({proj c ⟨x, hxc⟩} : Set (CentralizerBar c))).subtype,
        L.map (centralizer ({proj c ⟨x, hxc⟩} : Set (CentralizerBar c))).subtype⁆ =
        L.map (centralizer ({proj c ⟨x, hxc⟩} : Set (CentralizerBar c))).subtype := by
      rw [← Subgroup.map_commutator, hLperf]
    have hMc : L.map (centralizer ({proj c ⟨x, hxc⟩} : Set (CentralizerBar c))).subtype ≤
        centralizer ({proj c ⟨x, hxc⟩} : Set (CentralizerBar c)) := by
      rintro _ ⟨l, -, rfl⟩
      exact l.2
    exact (perfect_le_barSub_resCent hxc hx2' hMperf hMc).trans hres_le
  have hBperf : ⁅blkA mo D ⊔ blkB mo D, blkA mo D ⊔ blkB mo D⁆ = blkA mo D ⊔ blkB mo D := by
    have hA : ⁅blkA mo D, blkA mo D⁆ = blkA mo D := by
      rw [blkA, ← Subgroup.map_commutator, mo.ops.perfect 0 1 (by decide)]
    have hB : ⁅blkB mo D, blkB mo D⁆ = blkB mo D := by
      rw [blkB, ← Subgroup.map_commutator, mo.ops.perfect 2 3 (by decide)]
    exact commutator_sup_self hA hB
  have hBres : blkA mo D ⊔ blkB mo D ≤ resCent ({x, c} : Set G) := by
    refine le_resCent ?_ hBperf
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rcases hh with rfl | rfl
      · exact (mem_centralizer_singleton_iff.1 (hBAx ha)).symm
      · exact (mem_centralizer_singleton_iff.1 (hBA ha)).symm
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rcases hh with rfl | rfl
      · exact (mem_centralizer_singleton_iff.1 (hBBx ha)).symm
      · exact (mem_centralizer_singleton_iff.1 (hBB ha)).symm
  have hgrowth' : ¬ layer (CentralizerBar c) ≤
      S45.barSub c (blkA mo D) ⊔ S45.barSub c (blkB mo D) := fun h =>
    hgrowth (h.trans (sup_le (S45.barSub_mono (le_sup_left.trans hBres))
      (S45.barSub_mono (le_sup_right.trans hBres))))
  refine
    { odd := mo.qM_odd
      five := hq5
      core := barC_core
      gen4 := barC_gen4 hgen
      kgroup := barC_kgroup hs hn hkgh hc2
      gh := barC_gh hs hn hkgh hc2
      w_central := fun h => xbar_comm c h
      w_sq := xbar_mul_self hc2
      w_ne_one := xbar_ne_one hc2
      y_sq := hybar_sq
      y_ne_one := hybar_ne
      w_ne_y := hw_ne_y
      w_mem := S45.proj_mem_barSub hcC hcA
      y_mem := S45.proj_mem_barSub hxcC hycB
      y_cent := ?_
      sl₂ := hmodA
      sl₄ := hmodB
      cent₂ := hcentA
      cent₄ := hcentB
      comm := ?_
      comp₂ := ?_
      comp₄ := ?_
      bal := ?_
      le_layer := sup_le hlayA hlayB
      growth := hgrowth' }
  · intro b hb
    obtain ⟨g, hg, hgB, rfl⟩ := S45.mem_barSub.1 hb
    rw [hybar, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := Subgroup.mem_center_iff.1 hcenterB ⟨g, hgB⟩
    exact (congrArg Subtype.val this).symm
  · intro a ha b hb
    obtain ⟨g, hg, hgA, rfl⟩ := S45.mem_barSub.1 ha
    obtain ⟨g', hg', hgB', rfl⟩ := S45.mem_barSub.1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact blkA_comm_blkB mo D g hgA g' hgB'
  · rw [hwy]
    exact isComponent_barSub_cent hxc hx2' hBA hBAx hqA hZA heA hnA
  · rw [hwy]
    exact isComponent_barSub_cent hxc hx2' hBB hBBx hqB hZB heB hnB
  · rw [hwy]
    intro L hL
    have := balx L hL
    exact this

end Assembly


end CFSG.GH74.Generic.S1.Exo
