module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Main
public import CFSG.ClassicalInvolution.Q3.TL4OddBasic
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight

namespace Vtx

theorem mulAut_eq_one_of_central {P : Type*} [Group P] (hP : Group.IsPerfect P) (α : MulAut P)
    (h : ∀ q, q⁻¹ * α q ∈ Subgroup.center P) : α = 1 := by
  let δ : P →* Subgroup.center P :=
    { toFun := fun q => ⟨q⁻¹ * α q, h q⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hc := Subgroup.mem_center_iff.1 (h x) y⁻¹
        show (x * y)⁻¹ * α (x * y) = x⁻¹ * α x * (y⁻¹ * α y)
        calc (x * y)⁻¹ * α (x * y) = y⁻¹ * (x⁻¹ * α x) * α y := by simp [mul_assoc]
          _ = x⁻¹ * α x * y⁻¹ * α y := by rw [hc]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by simp [mul_assoc] }
  have hker : commutator P ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hP.commutator_eq_top] at hker
  ext q
  have hq : δ q = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top q))
  have := congrArg Subtype.val hq
  simp only [OneMemClass.coe_one] at this
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 this).symm

theorem mulAut_mul_conj_mul_inv {P : Type*} [Group P] (σ : MulAut P) (x : P) :
    σ * MulAut.conj x * σ⁻¹ = MulAut.conj (σ x) := by
  ext y
  simp [MulAut.conj_apply]

variable {Q : Type} [Group Q] [Finite Q]

theorem natCard_inducedAutOn_le (L : Subgroup Q) : Nat.card ↥(inducedAutOn L) ≤ Nat.card Q :=
  (Nat.card_le_card_of_surjective _
    (MonoidHom.rangeRestrict_surjective (conjOnNormalizer L))).trans
    (Subgroup.card_le_card_group _)

theorem oddCore_inducedAutOn_eq_bot {L : Subgroup Q} (hL : IsComponent L) :
    classicalInvolutionOddCore ↥(inducedAutOn L) = ⊥ := by
  set X' := inducedAutOn L with hX'
  set O := classicalInvolutionOddCore ↥X' with hOdef
  have hOn : O.Normal := classicalInvolutionOddCore_normal _
  have hInn : Q3NM.innSubgroup ↥L ≤ X' := innSubgroup_le_inducedAutOn L
  let φ : ↥L →* ↥X' := (MulAut.conj : ↥L →* MulAut ↥L).codRestrict X' fun l => hInn ⟨l, rfl⟩
  have hφ : ∀ l, ((φ l : ↥X') : MulAut ↥L) = MulAut.conj l := fun _ => rfl
  have hker : ∀ l : ↥L, φ l = 1 ↔ l ∈ Subgroup.center ↥L := by
    intro l
    constructor
    · intro h1
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun α : ↥X' => (α : MulAut ↥L) g) h1
      simp only [hφ, MulAut.conj_apply, OneMemClass.coe_one, MulAut.one_apply] at this
      calc g * l = (l * g * l⁻¹) * l := by rw [this]
        _ = l * g := by group
    · intro hl
      apply Subtype.ext
      ext g
      simp only [hφ, MulAut.conj_apply, OneMemClass.coe_one, MulAut.one_apply]
      rw [← Subgroup.mem_center_iff.mp hl g]
      group
  have hM : ∀ l : ↥L, φ l ∈ O → φ l = 1 := by
    intro l hl
    have hMn : (O.comap φ).Normal := hOn.comap φ
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hL.1 hMn with htop | hle
    · exfalso
      have h1 : φ.range ≤ O := by
        rintro _ ⟨m, rfl⟩
        have hm : m ∈ O.comap φ := htop ▸ Subgroup.mem_top m
        exact hm
      have h2 : Odd (Nat.card φ.range) :=
        (CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat (Subgroup.card_dvd_of_le h1)
      have hkerZ : φ.ker = Subgroup.center ↥L := by
        ext m
        exact hker m
      have h3 : Nat.card φ.range = Nat.card (↥L ⧸ Subgroup.center ↥L) := by
        rw [← hkerZ]
        exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
      have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
      have h4 := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even
        hL.1.2.2).1
      rw [h3] at h2
      exact (Nat.not_even_iff_odd.mpr h2) h4
    · exact (hker l).mpr (hle hl)
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  have hcen : ∀ l : ↥L, l⁻¹ * (α : MulAut ↥L) l ∈ Subgroup.center ↥L := by
    intro l
    have e1 : α * φ l * α⁻¹ = φ ((α : MulAut ↥L) l) :=
      Subtype.ext (mulAut_mul_conj_mul_inv _ _)
    have hmem : φ ((α : MulAut ↥L) l * l⁻¹) ∈ O := by
      rw [map_mul, map_inv, ← e1]
      have h1 : φ l * α⁻¹ * (φ l)⁻¹ ∈ O := hOn.conj_mem _ (O.inv_mem hα) (φ l)
      have h2 := O.mul_mem hα h1
      simpa [mul_assoc] using h2
    have hc := (hker _).mp (hM _ hmem)
    have hcl : (α : MulAut ↥L) l * l⁻¹ * l = l * ((α : MulAut ↥L) l * l⁻¹) :=
      (Subgroup.mem_center_iff.mp hc l).symm
    have e2 : l⁻¹ * (α : MulAut ↥L) l = (α : MulAut ↥L) l * l⁻¹ := by
      calc l⁻¹ * (α : MulAut ↥L) l = l⁻¹ * ((α : MulAut ↥L) l * l⁻¹ * l) := by group
        _ = l⁻¹ * (l * ((α : MulAut ↥L) l * l⁻¹)) := by rw [hcl]
        _ = (α : MulAut ↥L) l * l⁻¹ := by group
    rw [e2]
    exact hc
  exact Subtype.ext (mulAut_eq_one_of_central hL.1.1 _ hcen)

@[expose] noncomputable def autCenterQuot (P : Type*) [Group P] :
    MulAut P →* MulAut (P ⧸ Subgroup.center P) where
  toFun α := QuotientGroup.congr (Subgroup.center P) (Subgroup.center P) α
    (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' α β := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

theorem autCenterQuot_mk {P : Type*} [Group P] (α : MulAut P) (x : P) :
    autCenterQuot P α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  rfl

theorem autCenterQuot_injective {P : Type*} [Group P] (hP : Group.IsPerfect P) :
    Function.Injective (autCenterQuot P) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  refine mulAut_eq_one_of_central hP α fun q => ?_
  have h1 := congrArg (fun φ : MulAut (P ⧸ Subgroup.center P) => φ (QuotientGroup.mk q)) hα
  simp only [autCenterQuot_mk, MulAut.one_apply] at h1
  exact QuotientGroup.eq.mp h1.symm

theorem autCenterQuot_conj {P : Type*} [Group P] (l : P) :
    autCenterQuot P (MulAut.conj l) = MulAut.conj (QuotientGroup.mk l) := by
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem autOddFree_of_quot_center {P : Type} [Group P] [Finite P] (hP : Group.IsPerfect P)
    (h : Q3NM.AutOddFree (P ⧸ Subgroup.center P)) : Q3NM.AutOddFree P := by
  intro 𝒳 hinn f hf
  have : Finite (MulAut P) :=
    Finite.of_injective (fun α : MulAut P => (α : P → P)) fun _ _ e => MulEquiv.ext (congrFun e)
  have hρ := autCenterQuot_injective hP
  have hinn' : Q3NM.innSubgroup (P ⧸ Subgroup.center P) ≤ 𝒳.map (autCenterQuot P) := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective m
    exact ⟨MulAut.conj l, hinn ⟨l, rfl⟩, autCenterQuot_conj l⟩
  let ε : ↥𝒳 ≃* ↥(𝒳.map (autCenterQuot P)) := 𝒳.equivMapOfInjective _ hρ
  have hf' : orderOf (ε f) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hf
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv ε f (h _ hinn' (ε f) hf')

theorem typeRFam_of_tightDatum {Y : Type} [Group Y] [Finite Y] {r : ℕ} {R : Subgroup Y}
    {S : Sylow 2 ↥R} {t : Y} (hd : TightDatum R S t)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    TypeRFam r (CoreAssembly.conjClass (tightCore R)) := by
  have hΩ := hd.hypOmegaGen
  have hnt : ∀ L ∈ CoreAssembly.conjClass (tightCore R),
      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) L, L' = L := by
    intro L hL'
    refine noTwins_of_mem hΩ.conjInvariant (fun _ h => h) ?_ hL'
    rw [hd.twinSet_eq]
    exact fun K' hK' => hK'
  refine ⟨hΩ, hd.classicalClause, ?_, ?_, ?_, hnt⟩
  · rintro _ ⟨g, rfl⟩
    exact twoGroup_conjSub (twoGroup_of_le (tightCore_le R) hd.twoGroup) g
  · rintro _ ⟨g, rfl⟩ P hP
    have hP' : IsSylow2In (conjSub g⁻¹ P) (tightCore R) := by
      have := hP.conj g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have hS'R := isSylow2In_map_sylow R S
    have hS'K : ((S : Subgroup R).map R.subtype) ≤ tightCore R := fun s hs =>
      Subgroup.subset_closure ⟨hS'R.1 hs, hS'R.2.1.to_le (Subgroup.zpowers_le.mpr hs)⟩
    have hS'K0 : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) :=
      ⟨hS'K, hS'R.2.1, fun V hV hV2 hle => hS'R.2.2 V (hV.trans (tightCore_le R)) hV2 hle⟩
    obtain ⟨k, -, hk⟩ := Thompson.exists_conj_of_isSylow2In hP' hS'K0
    obtain ⟨eS⟩ := hq
    have hk' : conjSub (k * g⁻¹) P = (S : Subgroup R).map R.subtype := by
      rw [conjSub_mul, hk]
    exact ⟨((P.equivMapOfInjective (MulAut.conj (k * g⁻¹)).toMonoidHom
      (MulAut.conj (k * g⁻¹)).injective).trans (MulEquiv.subgroupCongr hk')).trans
      (((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans eS)⟩
  · intro L hL' w hw
    exact centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hL' (hnt L hL') hw

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
