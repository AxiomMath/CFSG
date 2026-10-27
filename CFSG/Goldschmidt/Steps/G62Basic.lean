module

import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
public import CFSG.Walter.Bender1970.S3.Setup
import CFSG.Walter.Bender1970.S3.PCore

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.Walter
open CFSG.GorensteinWalter hiding oddCoreOf

namespace G62

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_ne_top [IsSimpleGroup G] {K X : Subgroup G} (hK1 : K ≠ ⊥) (hKX : K ≤ X)
    (hX : X ≠ ⊤) : Subgroup.normalizer (K : Set G) ≠ ⊤ := by
  intro h
  have hn : K.Normal := Subgroup.normalizer_eq_top_iff.mp h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h' | h'
  · exact hK1 h'
  · exact hX (top_le_iff.mp (h' ▸ hKX))

omit [Finite G] in
theorem normalizer_eq_of_le_normalizer [IsSimpleGroup G] {M K : Subgroup G} (hM : IsCoatom M)
    (hKM : K ≤ M) (hK1 : K ≠ ⊥) (hMK : M ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup.normalizer (K : Set G) = M :=
  normalizer_eq_of_nontrivial_normal_in_coatom inferInstance hM hKM hK1
    (Subgroup.normal_subgroupOf_of_le_normalizer hMK)

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : K.map (MulAut.conj g).toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff''.mp hg x).mp hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {K : Subgroup G} {g : G}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom :=
      ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    rwa [h] at h1
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by
      have := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [mul_assoc] using this
    rwa [← this]

theorem not_mem_of_isPGroup {X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : IsPGroup p X) {a : G} (ha : orderOf a = 2) : a ∉ X := by
  intro haX
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have h1 := Subgroup.orderOf_dvd_natCard X haX
  rw [hk, ha] at h1
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)

theorem odd_card_of_isPGroup {X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : IsPGroup p X) : Odd (Nat.card X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

section Setting

variable {S : Sylow 2 G} {A : Subgroup G}

theorem centralizer_ne_top (hset : GoldSetting G S A) {s : G} (hs : s ≠ 1) :
    Subgroup.centralizer ({s} : Set G) ≠ ⊤ := by
  have := hset.isSimpleGroup
  intro h
  obtain ⟨x, y, hxy⟩ := hset.nonabelian
  have hz : s ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({s} : Set G) := h ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h' | h'
  · rw [h'] at hz
    exact hs (Subgroup.mem_bot.mp hz)
  · apply hxy
    have hy : y ∈ Subgroup.center G := h' ▸ Subgroup.mem_top y
    exact Subgroup.mem_center_iff.mp hy x

theorem benderM_nonempty (hset : GoldSetting G S A) {s : G} (hs : s ≠ 1) :
    (benderM s).Nonempty := by
  classical
  set C := Subgroup.centralizer ({s} : Set G)
  set 𝒦 : Set (Subgroup G) := {K | IsCoatom K ∧ C ≤ K}
  have hne : 𝒦.Nonempty := by
    rcases eq_top_or_exists_le_coatom C with h | ⟨K, hK, hCK⟩
    · exact absurd h (centralizer_ne_top hset hs)
    · exact ⟨K, hK, hCK⟩
  by_cases hfp : ∃ K : Subgroup G, IsCoatom K ∧ C ≤ K ∧ HasFixedPointFreeCore s K
  · obtain ⟨K, hK, hCK, hKfp⟩ := hfp
    exact ⟨K, hK, hCK, Or.inl hKfp⟩
  · push Not at hfp
    obtain ⟨K, ⟨hK, hCK⟩, hmax⟩ := Set.exists_max_image 𝒦
      (fun K => Nat.card (componentLayerOf K)) (Set.toFinite 𝒦) hne
    exact ⟨K, hK, hCK, Or.inr ⟨fun K' hK' hCK' => hfp K' hK' hCK',
      fun K' hK' hCK' => hmax K' ⟨hK', hCK'⟩⟩⟩

theorem isSStarIn_of_le (hset : GoldSetting G S A) {X : Subgroup G} (hX : X ≠ ⊤) (hAX : A ≤ X) :
    IsSStarIn X A := by
  obtain ⟨g, hle, hS⟩ := hset.sstar X hX
  rw [inf_eq_left.mpr hAX] at hle
  have heq : A = conjSub g A := Subgroup.eq_of_le_of_card_ge hle (card_conjSub g A).le
  rwa [← heq, inf_eq_left.mpr hAX] at hS

theorem le_centralizer (hset : GoldSetting G S A) : A ≤ Subgroup.centralizer (A : Set G) :=
  Subgroup.le_centralizer_iff_isMulCommutative.mpr hset.elem.1

end Setting

omit [Finite G] in
theorem map_subtype_normalizer_subgroupOf {X U : Subgroup G} (hUX : U ≤ X) :
    (Subgroup.normalizer ((U.subgroupOf X : Subgroup X) : Set X)).map X.subtype =
      X ⊓ Subgroup.normalizer (U : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hUX, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem isPGroup_generalizedFitting_inf_normalizer {X U : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hX : IsPGroup p (generalizedFittingSubgroupOf X)) (hUX : U ≤ X) (hU : IsPGroup p U) :
    IsPGroup p (generalizedFittingSubgroupOf (X ⊓ Subgroup.normalizer (U : Set G))) := by
  have hX' : IsPGroup p (generalizedFittingSubgroupOf (⊤ : Subgroup X)) := by
    have e : generalizedFittingSubgroupOf (⊤ : Subgroup X) ≃* generalizedFittingSubgroupOf X :=
      ((generalizedFittingSubgroupOf (⊤ : Subgroup X)).equivMapOfInjective X.subtype
        X.subtype_injective).trans
        (MulEquiv.subgroupCongr (generalizedFittingSubgroupOf_subgroup_top_eq X))
    exact hX.of_equiv e.symm
  have hU' : IsPGroup p (U.subgroupOf X) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUX).symm
  have h := (bender1970_1_8_centralizerNormalizer_pGroup (G := X) p hp hX' _ hU').2
  have hmap := h.map X.subtype
  rwa [generalizedFittingSubgroupOf_map_subtype', map_subtype_normalizer_subgroupOf hUX] at hmap

theorem isPGroup_fstar_normalizer_of_mem_goldA [IsSimpleGroup G] {a : G} {H Y : Subgroup G}
    (hH : IsCoatom H) (hH1 : H ≠ ⊥) {p : ℕ} (hp : p.Prime)
    (hF : IsPGroup p (generalizedFittingSubgroupOf H)) (hY : Y ∈ goldA a H) :
    IsPGroup p (generalizedFittingSubgroupOf (Subgroup.normalizer (Y : Set G))) := by
  obtain ⟨hY1, hYF, -, -, hYmax⟩ := hY
  have hYH : Y ≤ H := hYF.trans (generalizedFittingSubgroupOf_le H)
  have hYp : IsPGroup p Y := hF.to_le hYF
  obtain ⟨M, hMco, hNM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (Y : Set G))).resolve_left
      (normalizer_ne_top hY1 hYH hH.1)
  have key : ∀ K : Subgroup G, Y ≤ K → Subgroup.normalizer (Y : Set G) ≤ K →
      IsPGroup p (generalizedFittingSubgroupOf K) →
      IsPGroup p (generalizedFittingSubgroupOf (Subgroup.normalizer (Y : Set G))) := by
    intro K hYK hNK hK
    have h := isPGroup_generalizedFitting_inf_normalizer hp hK hYK hYp
    rwa [inf_eq_right.mpr hNK] at h
  rcases hYmax M hMco hNM with h | ⟨q, hq, hqM, hqH⟩
  · rw [h] at hNM
    exact key H hYH hNM hF
  · have hqp : q = p :=
      eq_of_isPGroup_of_isPGroup hq hp hqH hF (generalizedFittingSubgroupOf_ne_bot hH1)
    rw [hqp] at hqM
    exact key M (Subgroup.le_normalizer.trans hNM) hNM hqM

theorem le_of_inf_normalizer_le {p : ℕ} [Fact p.Prime] {P Q : Subgroup G} (hQ : IsPGroup p Q)
    (hPQ : P ≤ Q) (h : Q ⊓ Subgroup.normalizer (P : Set G) ≤ P) : Q ≤ P := by
  by_contra hQP
  set IP : Subgroup Q := P.subgroupOf Q
  have hIPne : IP ≠ ⊤ := by
    intro htop
    apply hQP
    intro x hxQ
    have hx : (⟨x, hxQ⟩ : Q) ∈ IP := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : IP < Subgroup.normalizer (IP : Set Q) :=
    Group.normalizerCondition_of_isNilpotent IP (lt_of_le_of_ne le_top hIPne)
  obtain ⟨x, hxN, hxIP⟩ := IsConcreteLE.exists_of_lt hlt
  have hxNorm : (x : G) ∈ Subgroup.normalizer (P : Set G) := by
    have hxsub : x ∈ (Subgroup.normalizer (P : Set G)).subgroupOf Q := by
      rw [Subgroup.subgroupOf_normalizer_eq hPQ]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  exact hxIP (Subgroup.mem_subgroupOf.mpr (h ⟨x.2, hxNorm⟩))

omit [Finite G] in
theorem zj_le (P : Subgroup G) : CFSG.Glauberman.ZJ P ≤ P :=
  (CFSG.Glauberman.zjCharacteristicFunctor 2).K_le P

theorem zj_ne_bot {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P) (hP1 : P ≠ ⊥) :
    CFSG.Glauberman.ZJ P ≠ ⊥ :=
  (CFSG.Glauberman.zjCharacteristicFunctor p).K_nontrivial P hP hP1

omit [Finite G] in
theorem normalizer_le_normalizer_zj (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (CFSG.Glauberman.ZJ P : Set G) := by
  intro g hg
  have h := (CFSG.Glauberman.zjCharacteristicFunctor 2).K_conj P g
  rw [map_conj_eq_of_mem_normalizer hg] at h
  exact mem_normalizer_of_map_conj_eq h.symm

omit [Finite G] in
theorem mem_sigN_iff_of_le {A X Y P : Subgroup G} {p : ℕ}
    (hX : Subgroup.centralizer (A : Set G) ≤ X) (hY : Subgroup.centralizer (A : Set G) ≤ Y)
    (hPX : P ≤ X) (hPY : P ≤ Y) : P ∈ sigN X A p ↔ P ∈ sigN Y A p := by
  simp only [sigN, Set.mem_ofPred_eq, inf_eq_right.mpr hX, inf_eq_right.mpr hY]
  exact ⟨fun h => ⟨hPY, h.2⟩, fun h => ⟨hPX, h.2⟩⟩

omit [Finite G] in
theorem maximal_sigN_of_le {A X Y P : Subgroup G} {p : ℕ}
    (hX : Subgroup.centralizer (A : Set G) ≤ X) (hXY : X ≤ Y)
    (hP : Maximal (· ∈ sigN Y A p) P) (hPX : P ≤ X) : Maximal (· ∈ sigN X A p) P := by
  have hY : Subgroup.centralizer (A : Set G) ≤ Y := hX.trans hXY
  refine ⟨(mem_sigN_iff_of_le hX hY hPX (hPX.trans hXY)).mpr hP.1, fun Q hQ hPQ => ?_⟩
  have hQX : Q ≤ X := hQ.1
  exact hP.2 ((mem_sigN_iff_of_le hX hY hQX (hQX.trans hXY)).mp hQ) hPQ

theorem maximal_sigN_of_forall {A X P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hP : P ∈ sigN X A p)
    (h : ∀ Q ∈ sigN X A p, P ≤ Q → Q ≤ Subgroup.normalizer (P : Set G) → Q ≤ P) :
    Maximal (· ∈ sigN X A p) P := by
  refine ⟨hP, fun Q hQ hPQ => ?_⟩
  obtain ⟨hQX, hQp, hAQ, hQC⟩ := hQ
  obtain ⟨-, -, hAP, -⟩ := hP
  have hQ' : Q ⊓ Subgroup.normalizer (P : Set G) ∈ sigN X A p := by
    refine ⟨inf_le_left.trans hQX, hQp.to_le inf_le_left, fun x hx => ?_, ?_⟩
    · exact CFSG.Walter.mem_normalizer_inf (hAQ hx) (Subgroup.le_normalizer (hAP hx))
    · exact (inf_le_inf_right _ inf_le_left).trans hQC
  have hle := h _ hQ' (le_inf hPQ Subgroup.le_normalizer) inf_le_right
  exact le_of_inf_normalizer_le hQp hPQ hle

omit [Finite G] in
theorem le_oddCoreOf {H N : Subgroup G} (hNH : N ≤ H) (hN : H ≤ Subgroup.normalizer (N : Set G))
    (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf H := by
  have hodd' : Odd (Nat.card (N.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  have hle : N.subgroupOf H ≤ goldschmidtOddCore H :=
    le_sSup ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hN, hodd'⟩
  have hm := Subgroup.map_mono (f := H.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hNH] at hm

omit [Finite G] in
theorem oddCoreOf_eq_self_of_odd {P : Subgroup G} (hodd : Odd (Nat.card P)) :
    oddCoreOf P = P := by
  have htop : goldschmidtOddCore P = ⊤ :=
    top_le_iff.mp (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  rw [oddCoreOf, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem eq_componentLayerOf_sup_of_isPGroup {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hPp : IsPGroup p P) (hodd : Odd (Nat.card P)) :
    P = componentLayerOf P ⊔ oddCoreOf (CFSG.fittingSubgroupOf P) := by
  have : Fact p.Prime := ⟨hp⟩
  have hE : componentLayerOf P = ⊥ :=
    componentLayerOf_eq_bot_of_isPGroup P hp (hPp.to_le (generalizedFittingSubgroupOf_le P))
  rw [hE, fittingSubgroupOf_eq_self_of_isNilpotent hPp.isNilpotent, bot_sup_eq,
    oddCoreOf_eq_self_of_odd hodd]

omit [Finite G] in
theorem commutator_self_le (K : Subgroup G) : ⁅K, K⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)

omit [Finite G] in
theorem fstarZero_le (H : Subgroup G) : fstarZero H ≤ generalizedFittingSubgroupOf H :=
  sup_le ((commutator_self_le _).trans le_sup_left) inf_le_left

omit [Finite G] in
theorem inf_centralizer_fstarZero_le (H : Subgroup G) :
    generalizedFittingSubgroupOf H ⊓ Subgroup.centralizer (fstarZero H : Set G) ≤
      fstarZero H := by
  intro x hx
  have hle : ⁅CFSG.fittingSubgroupOf H, CFSG.fittingSubgroupOf H⁆ ≤ fstarZero H := le_sup_left
  have hx' : x ∈ generalizedFittingSubgroupOf H ⊓
      Subgroup.centralizer
        ((⁅CFSG.fittingSubgroupOf H, CFSG.fittingSubgroupOf H⁆ : Subgroup G) : Set G) :=
    ⟨hx.1, Subgroup.centralizer_le hle hx.2⟩
  exact (le_sup_right : _ ≤ fstarZero H) hx'

omit [Finite G] in
theorem le_normalizer_fstarZero (H : Subgroup G) :
    H ≤ Subgroup.normalizer (fstarZero H : Set G) := by
  intro h hh
  have hF : h ∈ Subgroup.normalizer (CFSG.fittingSubgroupOf H : Set G) :=
    le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn H) hh
  have hFF := CFSG.Walter.mem_normalizer_commutator hF hF
  have hFs : h ∈ Subgroup.normalizer (generalizedFittingSubgroupOf H : Set G) :=
    le_normalizer_of_isNormalIn (generalizedFittingSubgroupOf_isNormalIn H) hh
  exact CFSG.Walter.mem_normalizer_sup hFF
    (CFSG.Walter.mem_normalizer_inf hFs (normalizer_le_normalizer_centralizer_subgroup _ hFF))

theorem commutator_fstarZero_ne_bot {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : IsPGroup p (generalizedFittingSubgroupOf H)) {a : G} (haH : a ∈ H)
    (ha : orderOf a = 2) : ⁅fstarZero H, Subgroup.zpowers a⁆ ≠ ⊥ := by
  intro h
  have hPB := fstarZero_le H
  have hK : pResidualOf (Subgroup.zpowers a) p = Subgroup.zpowers a :=
    Bender35.pResidualOf_zpowers_eq hp
      (by rw [ha]; exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hBn : H ≤ Subgroup.normalizer (generalizedFittingSubgroupOf H : Set G) :=
    le_normalizer_of_isNormalIn (generalizedFittingSubgroupOf_isNormalIn H)
  have hcent := bender1970_1_1_thompson p hp (fstarZero H) (Subgroup.zpowers a)
    (generalizedFittingSubgroupOf H) (hF.to_le hPB) hF hK (hPB.trans Subgroup.le_normalizer)
    (Subgroup.zpowers_le.mpr (hBn haH)) h
    (le_bot_iff.mp ((Subgroup.commutator_mono (inf_centralizer_fstarZero_le H) le_rfl).trans
      h.le))
  have haC : a ∈ Subgroup.centralizer (generalizedFittingSubgroupOf H : Set G) :=
    hcent (Subgroup.mem_zpowers a)
  exact not_mem_of_isPGroup hp hp2 hF ha
    (Bender35.inf_centralizer_le_generalizedFitting H ⟨haH, haC⟩)

theorem exists_hyperplane_commutator_ne_bot {A D : Subgroup G} (hA : IsElemAbelian 2 A)
    {t : G} (htA : t ∈ A) (ht1 : t ≠ 1) (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (hDodd : Odd (Nat.card D)) (htD : ⁅Subgroup.zpowers t, D⁆ ≠ ⊥) :
    ∃ A₁ : Subgroup G, A₁ ≤ A ∧ (A₁.subgroupOf A).index = 2 ∧
      ⁅Subgroup.zpowers t, D ⊓ Subgroup.centralizer (A₁ : Set G)⁆ ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAcomm := hA.1
  have : IsElementaryAbelian 2 A :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hA.2 x x.2) }
  have : Nontrivial A := ⟨⟨⟨t, htA⟩, 1, fun h => ht1 (congrArg Subtype.val h)⟩⟩
  let _ : MulDistribMulAction A D := Subgroup.conjMulDistribMulActionOfLeNormalizer A D hAD
  have hp : ¬ 2 ∣ Nat.card D := fun h => (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr h)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := D) hp
  by_contra hcon
  push Not at hcon
  apply htD
  rw [commutator_zpowers_eq_bot_iff]
  set Ct : Subgroup D := (Subgroup.centralizer ({t} : Set G)).comap D.subtype
  have hle : ⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B D ≤ Ct := by
    refine iSup₂_le fun B hB => ?_
    set R : Subgroup G := B.map A.subtype
    have hRA : R ≤ A := Subgroup.map_subtype_le B
    have hRi : (R.subgroupOf A).index = 2 := by
      have hRB : R.subgroupOf A = B :=
        Subgroup.comap_map_eq_self_of_injective A.subtype_injective B
      rw [hRB]
      exact hB
    have h := hcon R hRA hRi
    rw [commutator_zpowers_eq_bot_iff] at h
    intro x hx
    refine Subgroup.mem_centralizer_singleton_iff.mpr (h x ⟨x.2, ?_⟩)
    show (x : G) ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hbx := congrArg Subtype.val (hx ⟨b, hb⟩)
    change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at hbx
    calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
      _ = (x : G) * (b : G) := by rw [hbx]
  rw [hgen, top_le_iff] at hle
  intro x hx
  have hxC : (⟨x, hx⟩ : D) ∈ Ct := hle ▸ Subgroup.mem_top _
  exact Subgroup.mem_centralizer_singleton_iff.mp hxC

end G62

end CFSG.Goldschmidt
