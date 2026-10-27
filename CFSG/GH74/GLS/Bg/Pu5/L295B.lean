module

public import CFSG.GH74.GLS.Bg.Pu5.L295C
public import CFSG.GH74.GLS.Bg.Pu5.BalBDiag
public import CFSG.GH74.GLS.Bg.Pu5.BalStatements
public import CFSG.GH74.GLS.Balance.Lift
public import CFSG.GH74.GLS.Balance.Reduce
public import CFSG.GH74.GLS.Balance.SL23Ext

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm2.Recip.BalanceSolv CFSG.GH74.GLS.Bg.Iii2 CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG.ABGLocalTools CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement MatrixGroups

namespace L295B

section Core

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowOf_zinv {K : Subgroup G} {z : G} (hzK : z ∈ normalizer (K : Set G))
    (hz : z * z = 1) :
    ∃ P : Subgroup G, IsSylowOf 2 P K ∧ ∀ p ∈ P, z * p * z⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : ∃ n : ℕ, z ^ (2 ^ n) = 1 := ⟨1, by rw [pow_one, pow_two]; exact hz⟩
  have hKK : K ≤ K ⊔ zpowers z := le_sup_left
  have hKN : K ⊔ zpowers z ≤ normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (zpowers_le.2 hzK)
  obtain ⟨P', hP', hzP'⟩ := exists_isSylowOf_ge' (K := K ⊔ zpowers z) (X := zpowers z) le_sup_right
    (isPGroup_zpowers_of_pow_eq_one hz2)
  have hzP : z ∈ P' := hzP' (mem_zpowers z)
  refine ⟨P' ⊓ K, hP'.inf_of_le_normalizer hKK hKN, fun p hp => ⟨?_, ?_⟩⟩
  · exact P'.mul_mem (P'.mul_mem hzP hp.1) (P'.inv_mem hzP)
  · exact (mem_normalizer_iff.mp hzK p).mp hp.2

theorem exists_conj_forall_mem {K P X : Subgroup G} (hP : IsSylowOf 2 P K) (hXK : X ≤ K)
    (hX : IsPGroup 2 ↥X) : ∃ g ∈ K, ∀ x ∈ X, g⁻¹ * x * g ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨S, hS⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq K Q S
  refine ⟨(n : G), n.2, fun x hx => ?_⟩
  have hxS : (⟨x, hXK hx⟩ : K) ∈ (S : Subgroup K) := hS hx
  rw [← hn, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply] at hxS
  exact ⟨_, hxS, rfl⟩

omit [Finite G] in
theorem comm_mem_of_normalizer {L : Subgroup G} {p z : G} (hp : p ∈ L)
    (hz : z ∈ normalizer (L : Set G)) : ⁅p, z⁆ ∈ L := by
  have e : ⁅p, z⁆ = p * (z * p⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact mul_mem hp ((mem_normalizer_iff.mp hz p⁻¹).mp (inv_mem hp))

@[expose] def commSub (N : Subgroup G) (z : G) : Subgroup G where
  carrier := {g | g ∈ normalizer (N : Set G) ∧ ⁅g, z⁆ ∈ N}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hgz⟩ ⟨hh, hhz⟩
    refine ⟨mul_mem hg hh, ?_⟩
    have e : ⁅g * h, z⁆ = g * ⁅h, z⁆ * g⁻¹ * ⁅g, z⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem ((mem_normalizer_iff.mp hg _).mp hhz) hgz
  inv_mem' := by
    rintro g ⟨hg, hgz⟩
    refine ⟨inv_mem hg, ?_⟩
    have e : ⁅g⁻¹, z⁆ = g⁻¹ * ⁅g, z⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (mem_normalizer_iff.mp (inv_mem hg) _).mp (inv_mem hgz)

theorem exists_noncomm_zfixed {L Cu : Subgroup G} {z : G} (hzL : z ∈ normalizer (L : Set G))
    (hzC : z ∈ Cu) (hz : z * z = 1) {P₀ : Subgroup G} (hP₀L : P₀ ≤ L) (hP₀C : P₀ ≤ Cu)
    (hP₀2 : IsPGroup 2 ↥P₀) (hnc : ∃ a ∈ P₀, ∃ b ∈ P₀, a * b ≠ b * a)
    (hcomm : ∀ p ∈ P₀, ⁅p, z⁆ ∈ pPrimeCoreOf 2 Cu) :
    ∃ P : Subgroup G, P ≤ L ∧ IsPGroup 2 ↥P ∧ (∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) ∧
      ∀ p ∈ P, z * p = p * z := by
  set O : Subgroup G := pPrimeCoreOf 2 Cu with hO
  set N : Subgroup G := O ⊓ L with hN
  have hOn : ∀ g ∈ Cu, g ∈ normalizer (O : Set G) := fun g hg =>
    TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer hg)
  have hNn : ∀ g, g ∈ normalizer (O : Set G) → g ∈ normalizer (L : Set G) →
      g ∈ normalizer (N : Set G) := by
    intro g h1 h2
    rw [mem_normalizer_iff] at h1 h2 ⊢
    intro h
    rw [hN, mem_inf, mem_inf, h1 h, h2 h]
  have hzN : z ∈ normalizer (N : Set G) := hNn z (hOn z hzC) hzL
  have hpN : ∀ p ∈ P₀, p ∈ normalizer (N : Set G) := fun p hp =>
    hNn p (hOn p (hP₀C hp)) (le_normalizer (hP₀L hp))
  have hND : N ≤ commSub N z := by
    intro n hn
    refine ⟨le_normalizer hn, ?_⟩
    have e : ⁅n, z⁆ = n * (z * n⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem hn ((mem_normalizer_iff.mp hzN n⁻¹).mp (N.inv_mem hn))
  have hPD : P₀ ≤ commSub N z := by
    intro p hp
    exact ⟨hpN p hp, ⟨hcomm p hp, comm_mem_of_normalizer (hP₀L hp) hzL⟩⟩
  have hED : N ⊔ P₀ ≤ commSub N z := sup_le hND hPD
  have hEL : N ⊔ P₀ ≤ L := sup_le inf_le_right hP₀L
  have hmap : (N ⊔ P₀).map (MulAut.conj z).toMonoidHom ≤ N ⊔ P₀ := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      exact Subgroup.mem_sup_left (by simpa [MulAut.conj_apply] using (mem_normalizer_iff.mp hzN n).mp hn)
    · rintro _ ⟨p, hp, rfl⟩
      have h1 : ⁅z, p⁆ ∈ N := by
        rw [← commutatorElement_inv]
        exact N.inv_mem (hPD hp).2
      have e : (MulAut.conj z).toMonoidHom p = ⁅z, p⁆ * p := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem_sup h1 hp
  have hmap' : (N ⊔ P₀).map (MulAut.conj z).toMonoidHom = N ⊔ P₀ :=
    Subgroup.eq_of_le_of_card_ge hmap
      (by rw [Subgroup.card_map_of_injective (MulAut.conj z).injective])
  have hzE : z ∈ normalizer ((N ⊔ P₀ : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hmap'
  obtain ⟨P, hPS, hPz⟩ := exists_isSylowOf_zinv hzE hz
  have hP2 : IsPGroup 2 ↥P := hPS.isPGroup
  have hPE : P ≤ N ⊔ P₀ := hPS.le
  have hPcomm : ∀ p ∈ P, z * p = p * z := by
    intro p hp
    have h1 : ⁅p, z⁆ ∈ N := (hED (hPE hp)).2
    have h2 : ⁅p, z⁆ ∈ P := by
      have e : ⁅p, z⁆ = p * (z * p⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact P.mul_mem hp (hPz p⁻¹ (P.inv_mem hp))
    have h3 : ⁅p, z⁆ ∈ P ⊓ pPrimeCoreOf 2 Cu := ⟨h2, (inf_le_left : N ≤ O) h1⟩
    rw [inf_pPrimeCoreOf_eq_bot hP2, Subgroup.mem_bot] at h3
    exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
  refine ⟨P, hPE.trans hEL, hP2, ?_, hPcomm⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨g, -, hg⟩ := exists_conj_forall_mem hPS (le_sup_right : P₀ ≤ N ⊔ P₀) hP₀2
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  apply hab
  have h := hcon _ (hg a ha) _ (hg b hb)
  have e1 : g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
  have e2 : g⁻¹ * b * g * (g⁻¹ * a * g) = g⁻¹ * (b * a) * g := by group
  rw [e1, e2] at h
  exact mul_left_cancel (mul_right_cancel h)

theorem exists_fixed_noncomm {L P : Subgroup G} {z : G} (hzL : z ∈ normalizer (L : Set G))
    (hPL : P ≤ L) (hP2 : IsPGroup 2 ↥P) (hnc : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a)
    (hPz : ∀ p ∈ P, z * p = p * z) :
    ∃ W : Subgroup (Hat L), IsPGroup 2 ↥W ∧ (¬ ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) ∧
      ∀ w ∈ W, phi L z hzL w = w := by
  refine ⟨hatImg L P, ?_, ?_, ?_⟩
  · have hS' : IsPGroup 2 ↥(P.subgroupOf L) :=
      hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
    have e : hatImg L P = (P.subgroupOf L).map (hatMk L) := by
      ext x
      rw [mem_hatImg, Subgroup.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
    rw [e]
    exact hS'.map (hatMk L)
  · intro hW
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    apply hab
    have h := hW _ (hatMk_mem_hatImg hPL ha) _ (hatMk_mem_hatImg hPL hb)
    rw [← map_mul, ← map_mul] at h
    exact eq_of_hatMk_eq hPL hP2 (P.mul_mem ha hb) (P.mul_mem hb ha) h
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := mem_hatImg.1 hw
    rw [phi_mk]
    congr 1
    apply Subtype.ext
    show z * (p : G) * z⁻¹ = p
    rw [hPz p hp]
    group

end Core

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_nonsolv_lift {a b : G} (hb : orderOf b = 2) {K : Subgroup G}
    (hKC : IsPCompIn 2 (centralizer ({a} : Set G)) K) (hbN : b ∈ normalizer (K : Set G))
    (hL' : ∃ L' : Subgroup ↥(fixedSubgroup (Hat K) (phi K b hbN)), IsPComponent 2 L') :
    ∃ Λ : Subgroup G, IsPCompIn 2 (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)) Λ ∧
      Λ ≤ K ⊓ centralizer ({b} : Set G) := by
  obtain ⟨L', hL'⟩ := hL'
  set X : Subgroup G := K ⊓ centralizer ({b} : Set G) with hX
  have hL'2 : TwoComponents.IsTwoComponent L' := (CatalogueBAlternating.pComponent_two_iff L').mp hL'
  obtain ⟨Λz, hΛz, hΛzmap⟩ := OddKernelTwoComponents.exists_lift (fixedRestrict K hbN)
    (fixedRestrict_surjective K hb hbN) (odd_card_ker_fixedRestrict K hbN) L' hL'2
  set Λ : Subgroup G := Λz.map X.subtype with hΛdef
  have hΛX : Λ ≤ X := Subgroup.map_subtype_le Λz
  have hsub : Λ.subgroupOf X = Λz :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective Λz
  have hΛpc : IsPCompIn 2 X Λ := TwoThin.isPCompIn_two_iff.mpr ⟨hΛX, by rw [hsub]; exact hΛz⟩
  refine ⟨Λ, ?_, hΛX⟩
  set W := centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) with hW
  have hXW : X ≤ W := le_inf ((inf_le_left : X ≤ K).trans hKC.1) inf_le_right
  refine TwoThin.isPCompIn_two_iff.mpr ⟨hΛX.trans hXW, ?_⟩
  have hKsub : (K.subgroupOf (centralizer ({a} : Set G))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (TwoThin.isPCompIn_two_iff.mp hKC).2.1
      Subgroup.IsSubnormal.top
  have hsubW : (X.subgroupOf W).IsSubnormal := by
    have h1 := TwoThin.isSubnormal_inf_subgroupOf hKsub (inf_le_left : W ≤ centralizer ({a} : Set G))
    have h2 : X.subgroupOf W = K.subgroupOf W := by
      ext c
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, hX]
      exact ⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.mp c.2).2⟩⟩
    rwa [h2]
  exact TwoComponentTransport.extend_nested Λ _ W hΛX hXW hsubW (TwoThin.isPCompIn_two_iff.mp hΛpc).2

theorem sylow_noncomm_of_pcomp {X Λ L P₀ : Subgroup G} (hΛ : IsPCompIn 2 X Λ) (hΛL : Λ ≤ L)
    (hL1 : pRank 2 ↥L = 1) (hP₀ : IsSylowOf 2 P₀ Λ) : ∃ a ∈ P₀, ∃ b ∈ P₀, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hT⟩ := hP₀.exists_sylow_eq_subgroupOf
  have hno := IVK.Lifted.noCommInv_of_pRank hL1
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions
      ↥(T : Subgroup ↥Λ) := by
    intro u v huv
    have hu : orderOf (((u.1 : ↥(T : Subgroup ↥Λ)) : ↥Λ) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact u.2
    have hv : orderOf (((v.1 : ↥(T : Subgroup ↥Λ)) : ↥Λ) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact v.2
    have hu' : orderOf (⟨(((u.1 : ↥(T : Subgroup ↥Λ)) : ↥Λ) : G), hΛL (u.1 : ↥Λ).2⟩ : ↥L) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hu
    have hv' : orderOf (⟨(((v.1 : ↥(T : Subgroup ↥Λ)) : ↥Λ) : G), hΛL (v.1 : ↥Λ).2⟩ : ↥L) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hv
    have h := hno _ _ hu' hv' (Subtype.ext (congrArg (fun w : ↥(T : Subgroup ↥Λ) =>
      (((w : ↥Λ) : G)) ) huv))
    have h2 : (((u.1 : ↥(T : Subgroup ↥Λ)) : ↥Λ) : G) = (((v.1 : ↥(T : Subgroup ↥Λ)) : ↥Λ) : G) :=
      congrArg (Subtype.val : ↥L → G) h
    exact Subtype.ext (Subtype.ext (Subtype.ext h2))
  have hcommT : ∀ a b : ↥(T : Subgroup ↥Λ), a * b = b * a := by
    intro a b
    have ha : (((a : ↥Λ) : G)) ∈ P₀ := by
      have : (a : ↥Λ) ∈ P₀.subgroupOf Λ := hT ▸ a.2
      exact this
    have hb : (((b : ↥Λ) : G)) ∈ P₀ := by
      have : (b : ↥Λ) ∈ P₀.subgroupOf Λ := hT ▸ b.2
      exact this
    exact Subtype.ext (Subtype.ext (hcon _ ha _ hb))
  let _ : CommGroup ↥(T : Subgroup ↥Λ) :=
    { (inferInstance : Group ↥(T : Subgroup ↥Λ)) with mul_comm := hcommT }
  have hcyc : IsCyclic ↥(T : Subgroup ↥Λ) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_abelian_two_group_cyclic _ T.isPGroup' hrank
  have hsolv : Group.IsSolvable ↥Λ := isSolvable_of_isCyclic_sylow_two T hcyc
  have hq := TwoThin.isQuasisimple_hat hΛ
  have : Group.IsSolvable (↥Λ ⧸ pPrimeCore 2 ↥Λ) := inferInstance
  exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq this


theorem exists_solv_data {G : Type} [Group G] [Finite G] {x y : G}
    (hxy : Commute x y) {L : Subgroup G} (hLC : IsPCompIn 2 (centralizer ({x} : Set G)) L)
    (hy : orderOf y = 2) (hyN : y ∈ normalizer (L : Set G))
    (hsolv : HasSolvableTwoComponentSL23 ↥(fixedSubgroup (↥L ⧸ pPrimeCore 2 ↥L)
      (inducedQuotAut L (pPrimeCore 2 ↥L) ⟨y, hyN⟩))) :
    ∃ (V P₀ : Subgroup G),
      Balance.IsSolvTwoCompSL23In (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) V ∧
      P₀ ≤ L ⊓ centralizer ({y} : Set G) ∧ P₀ ≤ V ∧ IsPGroup 2 ↥P₀ ∧
      ∃ a ∈ P₀, ∃ b ∈ P₀, a * b ≠ b * a := by
  classical
  have hLCx : L ≤ centralizer ({x} : Set G) := hLC.1
  have hLsub : (L.subgroupOf (centralizer ({x} : Set G))).IsSubnormal := by
    obtain ⟨-, -, hsub, -⟩ := hLC.2
    exact hsub
  set Cy : Subgroup G := centralizer ({y} : Set G) with hCy
  set x' : ↥Cy := Balance.xC hxy with hx'
  set C' : Subgroup ↥Cy := centralizer ({x'} : Set ↥Cy) with hC'
  set Hg : Subgroup (Hat L) := fixedSubgroup (Hat L) (phi L y hyN) with hHg
  set q : ↥Hg →* ↥Hg ⧸ pPrimeCore 2 ↥Hg := QuotientGroup.mk' (pPrimeCore 2 ↥Hg) with hq
  obtain ⟨W, hWsub, ⟨eW⟩⟩ := (Balance.hasSolvableTwoComponentSL23_iff _).mp hsolv
  let f : ↥C' →* ↥(centralizer ({x} : Set G)) :=
    (Cy.subtype.comp C'.subtype).codRestrict (centralizer ({x} : Set G)) (fun g => by
      have h1 := mem_centralizer_singleton_iff.mp g.2
      have h2 := congrArg Subtype.val h1
      exact mem_centralizer_singleton_iff.mpr h2)
  set U : Subgroup ↥C' := (L.subgroupOf (centralizer ({x} : Set G))).comap f with hU
  have hUsub : U.IsSubnormal := hLsub.comap f
  have hmemU : ∀ u : ↥C', u ∈ U ↔ (((u : ↥Cy)) : G) ∈ L := fun u => Iff.rfl
  let j : ↥U →* ↥(L ⊓ Cy) :=
    ((Cy.subtype.comp C'.subtype).comp U.subtype).codRestrict (L ⊓ Cy) (fun u =>
      ⟨(hmemU _).mp u.2, ((u : ↥C') : ↥Cy).2⟩)
  have hjinj : Function.Injective j := by
    intro a b hab
    have h : (((j a : ↥(L ⊓ Cy)) : G)) = ((j b : ↥(L ⊓ Cy)) : G) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  have hjsurj : Function.Surjective j := by
    rintro ⟨a, haL, haCy⟩
    have hax : a * x = x * a := mem_centralizer_singleton_iff.mp (hLCx haL)
    have hC'mem : (⟨a, haCy⟩ : ↥Cy) ∈ C' := by
      rw [hC', mem_centralizer_singleton_iff]
      exact Subtype.ext hax
    exact ⟨⟨⟨⟨a, haCy⟩, hC'mem⟩, haL⟩, rfl⟩
  let r : ↥(L ⊓ Cy) →* ↥Hg := fixedRestrict L hyN
  have hrsurj : Function.Surjective r := fixedRestrict_surjective L hy hyN
  have hrodd : Odd (Nat.card r.ker) := odd_card_ker_fixedRestrict L hyN
  let ψ : ↥U →* ↥Hg ⧸ pPrimeCore 2 ↥Hg := q.comp (r.comp j)
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hψsurj : Function.Surjective ψ := hqsurj.comp (hrsurj.comp hjsurj)
  have hjker : Odd (Nat.card j.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff j).mpr hjinj, Subgroup.card_bot]
    exact odd_one
  have hrjodd : Odd (Nat.card (r.comp j).ker) := Balance.odd_card_ker_comp j r hjsurj hjker hrodd
  have hqker : Odd (Nat.card q.ker) := by
    rw [hq, QuotientGroup.ker_mk']
    exact TwoThin.odd_card_pPrimeCore _
  have hψodd : Odd (Nat.card ψ.ker) :=
    Balance.odd_card_ker_comp (r.comp j) q (hrsurj.comp hjsurj) hrjodd hqker
  have hψker : ∀ u : ↥U, ψ u = 1 → ((u : ↥C') : ↥C') ∈ pPrimeCore 2 ↥C' := by
    intro u hu
    have hle : ψ.ker ≤ pPrimeCore 2 ↥U :=
      le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hψodd⟩
    have hmem : u ∈ pPrimeCore 2 ↥U := hle (MonoidHom.mem_ker.mpr hu)
    exact CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hUsub ⟨u, hmem, rfl⟩
  set Vt : Subgroup ↥C' := (W.comap ψ).map U.subtype with hVt
  have hVtsub : Vt.IsSubnormal := by
    refine Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le _) ?_ hUsub
    have h1 : (Vt.subgroupOf U) = W.comap ψ :=
      Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
    rw [h1]
    exact hWsub.comap ψ
  let eV : ↥(W.comap ψ) ≃* ↥Vt := (W.comap ψ).equivMapOfInjective U.subtype U.subtype_injective
  let χ : ↥Vt →* SL(2, ZMod 3) :=
    eW.toMonoidHom.comp ((ψ.subgroupComap W).comp eV.symm.toMonoidHom)
  have hχsurj : Function.Surjective χ := by
    intro s
    obtain ⟨w, hw⟩ := eW.surjective s
    obtain ⟨u, hu⟩ := hψsurj (w : ↥Hg ⧸ pPrimeCore 2 ↥Hg)
    refine ⟨eV ⟨u, by rw [Subgroup.mem_comap, hu]; exact w.2⟩, ?_⟩
    show eW ((ψ.subgroupComap W) (eV.symm (eV _))) = s
    rw [MulEquiv.symm_apply_apply, ← hw]
    congr 1
    exact Subtype.ext hu
  have hχker : ∀ n : ↥Vt, χ n = 1 → (n : ↥C') ∈ pPrimeCore 2 ↥C' := by
    intro n hn
    have h1 : (ψ.subgroupComap W) (eV.symm n) = 1 := eW.map_eq_one_iff.mp hn
    have h2 : ψ ((eV.symm n : ↥(W.comap ψ)) : ↥U) = 1 := by
      have := congrArg Subtype.val h1
      exact this
    have h3 := hψker _ h2
    have h4 : (n : ↥C') = (((eV.symm n : ↥(W.comap ψ)) : ↥U) : ↥C') := by
      conv_lhs => rw [← eV.apply_symm_apply n]
      rfl
    rw [h4]
    exact h3
  have hV := Balance.isSolvTwoCompSL23_of_subnormal Vt hVtsub χ hχsurj hχker
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) with hA
  have hmemA : ∀ c : ↥C', (((c : ↥Cy)) : G) ∈ A := by
    intro c
    refine ⟨?_, c.1.2⟩
    have h1 := mem_centralizer_singleton_iff.mp c.2
    have h2 := congrArg Subtype.val h1
    exact mem_centralizer_singleton_iff.mpr h2
  let ι : ↥C' →* ↥A := (Cy.subtype.comp C'.subtype).codRestrict A hmemA
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h : (((ι a : ↥A)) : G) = ((ι b : ↥A) : G) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have hιsurj : Function.Surjective ι := by
    rintro ⟨g, hgx, hgy⟩
    have hC'mem : (⟨g, hgy⟩ : ↥Cy) ∈ C' := by
      rw [hC', mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hgx)
    exact ⟨⟨⟨g, hgy⟩, hC'mem⟩, rfl⟩
  have hιodd : Odd (Nat.card ι.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff ι).mpr hιinj, Subgroup.card_bot]
    exact odd_one
  have hVA : Balance.IsSolvTwoCompSL23 ↥A ((Vt ⊔ pPrimeCore 2 ↥C').map ι) :=
    Balance.isSolvTwoCompSL23_map ι hιsurj hιodd hV
  have hVG : Balance.IsSolvTwoCompSL23In A (((Vt ⊔ pPrimeCore 2 ↥C').map ι).map A.subtype) :=
    ⟨Subgroup.map_subtype_le _, by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
      exact hVA⟩
  have hχkerodd : Odd (Nat.card χ.ker) := by
    let incl : ↥χ.ker →* ↥(pPrimeCore 2 ↥C') :=
      { toFun := fun n => ⟨(n.1 : ↥C'), hχker n.1 (MonoidHom.mem_ker.mp n.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective incl := by
      intro a b h
      have h1 : ((a.1 : ↥Vt) : ↥C') = ((b.1 : ↥Vt) : ↥C') :=
        congrArg (fun w : ↥(pPrimeCore 2 ↥C') => (w : ↥C')) h
      exact Subtype.ext (Subtype.ext h1)
    exact (TwoThin.odd_card_pPrimeCore ↥C').of_dvd_nat (Subgroup.card_dvd_of_injective incl hinj)
  let E : Balance.SL23.Ext ↥Vt := ⟨χ, hχsurj, hχkerodd⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥Vt) := inferInstance
  obtain ⟨a, ha, b, hb, hab⟩ := E.nonab T.isPGroup' (E.card_sylow T)
  let ψG : ↥Vt →* G := (A.subtype.comp ι).comp Vt.subtype
  have hψGinj : Function.Injective ψG :=
    Subtype.val_injective.comp (hιinj.comp (Subtype.val_injective))
  have hψGval : ∀ t : ↥Vt, ψG t = (((t : ↥C') : ↥Cy) : G) := fun t => rfl
  refine ⟨((Vt ⊔ pPrimeCore 2 ↥C').map ι).map A.subtype, (T : Subgroup ↥Vt).map ψG, hVG, ?_, ?_,
    T.isPGroup'.map ψG, ⟨ψG a, Subgroup.mem_map_of_mem _ ha, ψG b, Subgroup.mem_map_of_mem _ hb,
      fun h => hab (hψGinj (by rw [map_mul, map_mul]; exact h))⟩⟩
  · rintro _ ⟨t, -, rfl⟩
    refine ⟨?_, ((t : ↥C') : ↥Cy).2⟩
    rw [hψGval]
    exact (hmemU (t : ↥C')).mp (Subgroup.map_subtype_le _ t.2)
  · rintro _ ⟨t, -, rfl⟩
    exact ⟨ι (t : ↥C'), ⟨(t : ↥C'), Subgroup.mem_sup_left t.2, rfl⟩, rfl⟩


end Lift

end L295B

theorem l295b_of (hP0 : P0S) (hBL0 : BL0S) (hBL0s : BL0sS) (hL294a : L294a) (h2A7 : II4_2A7)
    (h44 : II4_44) : L295bS := by
  intro G _ _ z t S K U hcfg hN L hL u hu hu2 hF
  have hG : IsKProperSimple G := hcfg.cfg.simple
  have hLC : IsPCompIn 2 (centralizer ({t} : Set G)) L := rr_pcomp hL
  have ht2 : orderOf t = 2 := rr_ord hL
  have hz2 : orderOf z = 2 := hcfg.cfg.hz
  have hzz : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have hzU : z ∈ U := hcfg.hzU
  have hzN : z ∈ normalizer (L : Set G) := hN L hL hzU
  obtain ⟨huN, hFa⟩ := hF
  have huz : u * z = z * u := Subgroup.mem_centralizer_singleton_iff.1 (hcfg.mem_cent_z hu)
  have hut : u ∈ centralizer ({t} : Set G) := hcfg.mem_cent_t hu
  have hut' : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.1 hut
  have hzCu : z ∈ centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 huz.symm
  have hzCtu : z ∈ centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) :=
    ⟨hcfg.mem_cent_t hzU, hzCu⟩
  have hZ : z ∈ zStar (rigidProduct u) := hP0 G z t S K U hcfg u hu hu2
  obtain ⟨P₀, hP₀L, hP₀2, hP₀nc, hP₀c⟩ : ∃ P₀ : Subgroup G,
      P₀ ≤ L ⊓ centralizer ({u} : Set G) ∧ IsPGroup 2 ↥P₀ ∧
      (∃ a ∈ P₀, ∃ b ∈ P₀, a * b ≠ b * a) ∧
      ∀ p ∈ P₀, ⁅p, z⁆ ∈ pPrimeCoreOf 2 (centralizer ({u} : Set G)) := by
    obtain ⟨-, -, -, -, hcomp | hsolv⟩ := hFa
    · obtain ⟨Λ, hΛW, hΛX⟩ := L295B.exists_nonsolv_lift hu2 hLC huN hcomp
      obtain ⟨P₀, hP₀⟩ := exists_isSylowOf 2 Λ
      refine ⟨P₀, hP₀.le.trans hΛX, hP₀.isPGroup,
        L295B.sylow_noncomm_of_pcomp hΛW (hΛX.trans inf_le_left) hL.2 hP₀, fun p hp => ?_⟩
      exact hBL0 G hG t u ht2 hu2 hut Λ (le_sSup hΛW) z hzCtu hZ p (hP₀.le hp)
    · obtain ⟨V, P₀, hV, hP₀L, hP₀V, hP₀2, hnc⟩ :=
        L295B.exists_solv_data (Commute.symm hut') hLC hu2 huN hsolv
      refine ⟨P₀, hP₀L, hP₀2, hnc, fun p hp => ?_⟩
      have h2 : ∃ k : ℕ, p ^ (2 ^ k) = 1 := by
        obtain ⟨k, hk⟩ := hP₀2 ⟨p, hp⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      exact hBL0s G hG t u ht2 hu2 hut V hV z hzCtu hZ p
        (Balance.mem_oPrimeResidualOf_of_two_element (hP₀V hp) h2)
  obtain ⟨P, hPL, hP2, hPnc, hPz⟩ := L295B.exists_noncomm_zfixed hzN hzCu hzz
    (hP₀L.trans inf_le_left) (hP₀L.trans inf_le_right) hP₀2 hP₀nc hP₀c
  obtain ⟨W, hW2, hWnc, hWφ⟩ := L295B.exists_fixed_noncomm hzN hPL hP2 hPnc hPz
  have hO : HatOK (Hat L) := L295C.hatOK_of_rigid h44 hG hL
  have hφz2 : phi L z hzN * phi L z hzN = 1 := phi_mul_self L hzN hzz
  rcases ii4_43e h2A7 hO (phi L z hzN) hφz2 W hW2 hWnc hWφ with h1 | h1
  · have hzc : z ∈ cSec L := (phi_eq_one_iff L hzN).1 h1
    exact (hL294a G z t S hcfg.cfg).2 L hL (inducesFAut_of_mem_cSec hG ht2 hLC hL.2 hzc)
  · exact (hL294a G z t S hcfg.cfg).2 L hL ⟨hzN, h1⟩

end CFSG.GH74.GLS.Bg.Pu5
