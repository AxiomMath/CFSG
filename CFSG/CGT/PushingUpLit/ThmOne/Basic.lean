module

public import CFSG.CGT.PushingUpLit.BlocksCommute
public import CFSG.CGT.PushingUpLit.Glue.RadicalSylow
public import CFSG.CGT.PushingUpLit.SixThreeShort
public import CFSG.CGT.PushingUpLit.EightOneRel

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem blockU_commutator_eq_self {X : Subgroup G} (hX : oResidualTwo ↥X = ⊤) :
    ⁅blockU X, X⁆ = blockU X :=
  SixThree.commutator_commutator_eq (SubTwo.noTwoQuotient_of_oResidualTwo hX)
    (isPGroup_oTwoIn X) (SixThree.le_normalizer_oTwoIn X)

theorem blockU_mul_comm {X : Subgroup G} (hX : IsShortGroup ↥X) {a b : G} (ha : a ∈ blockU X)
    (hb : b ∈ blockU X) : a * b = b * a :=
  blockU_comm_of_short hX a ha b (blockU_le_oTwoIn X hb)

theorem sq_mem_blockZ_of_isShortGroup {X : Subgroup G} (hX : IsShortGroup ↥X) {u : G}
    (hu : u ∈ blockU X) : u ^ 2 ∈ blockZ X := by
  let S : Subgroup G :=
    { carrier := {g | ∃ v ∈ blockU X, v ^ 2 = g}
      one_mem' := ⟨1, one_mem _, one_pow 2⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, mul_mem ha hb, Commute.mul_pow (blockU_mul_comm hX ha hb) 2⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, inv_mem ha, inv_pow a 2⟩ }
  have hSU : S ≤ blockU X := by
    rintro _ ⟨v, hv, rfl⟩
    exact pow_mem hv 2
  have hSn : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    rintro g hg _ ⟨v, hv, rfl⟩
    exact ⟨g * v * g⁻¹, conj_mem_blockU hg hv, by rw [conj_pow]⟩
  have hXS : X ≤ Subgroup.normalizer (S : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => hSn g (Subgroup.le_normalizer hg) s hs,
      fun hs => by simpa [mul_assoc] using hSn g⁻¹ (Subgroup.le_normalizer (X.inv_mem hg)) _ hs⟩
  have hXZ : X ≤ Subgroup.normalizer (blockZ X : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun z =>
      ⟨fun hz => conj_mem_blockZ (Subgroup.le_normalizer hg) hz, fun hz => by
        simpa [mul_assoc] using conj_mem_blockZ (Subgroup.le_normalizer (X.inv_mem hg)) hz⟩
  have hXT : X ≤ Subgroup.normalizer ((S ⊔ blockZ X : Subgroup G) : Set G) :=
    (le_inf hXS hXZ).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  rcases blockU_irred_of_short hX (S ⊔ blockZ X) le_sup_right (sup_le hSU (blockZ_le_blockU X))
      (fun g hg n hn => (Subgroup.mem_normalizer_iff.mp (hXT hg) n).mp hn) with h | h
  · rw [← h]
    exact Subgroup.mem_sup_left ⟨u, hu, rfl⟩
  · exfalso
    have hZC : blockZ X ≤ Subgroup.centralizer (S : Set G) := fun z hz =>
      Subgroup.mem_centralizer_iff.mpr fun s hs =>
        blockU_mul_comm hX (hSU hs) (blockZ_le_blockU X hz)
    have hZS : blockZ X ≤ Subgroup.normalizer (S : Set G) :=
      hZC.trans (Subgroup.centralizer_le_normalizer _)
    have hZX : ⁅blockZ X, X⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun z hz => hz.2
    have hUS : blockU X ≤ S := by
      calc blockU X = ⁅blockU X, X⁆ := (blockU_commutator_eq_self hX.residual_eq).symm
        _ = ⁅blockZ X ⊔ S, X⁆ := by rw [← h, sup_comm]
        _ ≤ ⁅blockZ X, X⁆ ⊔ S :=
          CFSG.RankThree.PartTwo.Sec6.commutator_sup_le_of_le_normalizer hZS hXS
        _ = S := by rw [hZX, bot_sup_eq]
    have hsurj : Function.Surjective (fun v : ↥(blockU X) => v ^ 2) := by
      rintro ⟨w, hw⟩
      obtain ⟨v, hv, hvw⟩ := hUS hw
      exact ⟨⟨v, hv⟩, Subtype.ext (by simp [hvw])⟩
    have hinj := Finite.injective_iff_surjective.mpr hsurj
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hU2 : IsPGroup 2 ↥(blockU X) := (isPGroup_oTwoIn X).to_le (blockU_le_oTwoIn X)
    have hnt : Nontrivial ↥(blockU X) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr (blockU_ne_bot_of_short hX)
    obtain ⟨n, hn, hcard⟩ := hU2.nontrivial_iff_card.mp hnt
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(blockU X)) 2
      (by rw [hcard]; exact dvd_pow_self 2 (by omega))
    have h1 : z ^ 2 = (1 : ↥(blockU X)) ^ 2 := by rw [one_pow, ← hz, pow_orderOf_eq_one]
    rw [hinj h1, orderOf_one] at hz
    exact absurd hz (by norm_num)

theorem pow_two_eq_one_of_mem_blockU {X : Subgroup G} (hX : IsShortGroup ↥X) {v : G}
    (hv : v ∈ blockU X) : v ^ 2 = 1 := by
  let E : Subgroup G :=
    { carrier := {u | u ∈ blockU X ∧ u ^ 2 = 1}
      one_mem' := ⟨one_mem _, one_pow 2⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        exact ⟨mul_mem ha hb, by
          rw [Commute.mul_pow (blockU_mul_comm hX ha hb) 2, ha2, hb2, one_mul]⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        exact ⟨inv_mem ha, by rw [inv_pow, ha2, inv_one]⟩ }
  have hle : ⁅blockU X, X⁆ ≤ E := by
    refine Subgroup.commutator_le.2 fun u hu l hl => ?_
    have hb : l * u⁻¹ * l⁻¹ ∈ blockU X :=
      conj_mem_blockU (Subgroup.le_normalizer hl) (inv_mem hu)
    have hz : l * u ^ 2 * l⁻¹ = u ^ 2 := by
      rw [Subgroup.mem_centralizer_iff.1 (sq_mem_blockZ_of_isShortGroup hX hu).2 l hl,
        mul_inv_cancel_right]
    have hmem : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
    refine ⟨by rw [hmem]; exact mul_mem hu hb, ?_⟩
    show ⁅u, l⁆ ^ 2 = 1
    have hi : l * (u ^ 2)⁻¹ * l⁻¹ = (u ^ 2)⁻¹ := by
      rw [show l * (u ^ 2)⁻¹ * l⁻¹ = (l * u ^ 2 * l⁻¹)⁻¹ by group, hz]
    rw [hmem, Commute.mul_pow (blockU_mul_comm hX hu hb), conj_pow, inv_pow, hi, mul_inv_cancel]
  rw [← blockU_commutator_eq_self hX.residual_eq] at hv
  exact (hle hv).2

omit [Finite G] in
theorem commutator_mem_blockU_of_mem_centralizerModCore {X : Subgroup G}
    (hX : oResidualTwo ↥X = ⊤) {g : G} (hg : g ∈ centralizerModCore X) {x : G} (hx : x ∈ X) :
    g * x * g⁻¹ * x⁻¹ ∈ blockU X := by
  let N : Subgroup ↥(oTwoIn X) := (blockU X).subgroupOf (oTwoIn X)
  have hN : N.Normal := by
    refine ⟨fun n hn q => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using conj_mem_blockU (Subgroup.le_normalizer (oTwoIn_le X q.2)) hn
  let f : ↥X → ↥(oTwoIn X) ⧸ N := fun y =>
    QuotientGroup.mk ⟨g * y * g⁻¹ * (y : G)⁻¹, hg.2 y y.2⟩
  have hf : ∀ a b : ↥X, f (a * b) = f a * f b := by
    intro a b
    show QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hw : (g * b * g⁻¹ * (b : G)⁻¹)⁻¹ ∈ oTwoIn X := inv_mem (hg.2 b b.2)
    have hmem : ⁅(a : G), (g * b * g⁻¹ * (b : G)⁻¹)⁻¹⁆ ∈ blockU X := by
      have := Subgroup.commutator_mem_commutator a.2 hw
      rwa [Subgroup.commutator_comm] at this
    convert hmem using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  let φ : ↥X →* ↥(oTwoIn X) ⧸ N := MonoidHom.mk' f hf
  have hker : φ.ker = ⊤ := by
    have hp : IsPGroup 2 (↥(oTwoIn X) ⧸ N) := (isPGroup_oTwoIn X).to_quotient N
    have hp' : IsPGroup 2 (↥X ⧸ φ.ker) :=
      (hp.to_subgroup φ.range).of_equiv (QuotientGroup.quotientKerEquivRange φ).symm
    have hle : oResidualTwo ↥X ≤ φ.ker := sInf_le ⟨inferInstance, hp'⟩
    rwa [hX, top_le_iff] at hle
  have h1 : (⟨x, hx⟩ : ↥X) ∈ φ.ker := by
    rw [hker]
    trivial
  have h2 : (QuotientGroup.mk ⟨g * x * g⁻¹ * x⁻¹, hg.2 x hx⟩ : ↥(oTwoIn X) ⧸ N) = 1 := h1
  have h3 : (⟨g * x * g⁻¹ * x⁻¹, hg.2 x hx⟩ : ↥(oTwoIn X)) ∈ N :=
    (QuotientGroup.eq_one_iff _).mp h2
  exact h3

omit [Finite G] in
theorem mem_centralizerModCore_iff_blockU {X : Subgroup G} (hX : oResidualTwo ↥X = ⊤) {g : G} :
    g ∈ centralizerModCore X ↔
      g ∈ Subgroup.normalizer (X : Set G) ∧ ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ blockU X :=
  ⟨fun hg => ⟨hg.1, fun _ hx => commutator_mem_blockU_of_mem_centralizerModCore hX hg hx⟩,
    fun h => ⟨h.1, fun x hx => blockU_le_oTwoIn X (h.2 x hx)⟩⟩

theorem le_normalizer_of_isSubnormal_of_isPGroup {X M P : Subgroup G} (hX : oResidualTwo ↥X = ⊤)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) (hP : IsPGroup 2 P) (hPM : P ≤ M)
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) : P ≤ Subgroup.normalizer (X : Set G) :=
  SubTwo.le_normalizer_of_isSubnormal_sup (SubTwo.noTwoQuotient_of_oResidualTwo hX) hP hXP
    (CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (sup_le hXM hPM) hsub)

theorem oTwoIn_le_normalizer_of_isSubnormal {X M : Subgroup G} (hX : oResidualTwo ↥X = ⊤)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) :
    oTwoIn M ≤ Subgroup.normalizer (X : Set G) :=
  le_normalizer_of_isSubnormal_of_isPGroup hX hXM hsub (isPGroup_oTwoIn M) (oTwoIn_le M)
    (hXM.trans (SixThree.le_normalizer_oTwoIn M))

theorem le_centralizerModCore_of_isSubnormal {X M P : Subgroup G} (hX : oResidualTwo ↥X = ⊤)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) (hP : IsPGroup 2 P) (hPM : P ≤ M)
    (hMP : M ≤ Subgroup.normalizer (P : Set G)) : P ≤ centralizerModCore X := by
  have hPX := le_normalizer_of_isSubnormal_of_isPGroup hX hXM hsub hP hPM (hXM.trans hMP)
  have hXP : X ⊓ P ≤ oTwoIn X :=
    SixThree.le_oTwoIn_of_isPGroup inf_le_left (hP.to_le inf_le_right)
      ((le_inf Subgroup.le_normalizer (hXM.trans hMP)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  refine fun p hp => ⟨hPX hp, fun x hx => hXP ⟨?_, ?_⟩⟩
  · exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPX hp) x).mp hx) (X.inv_mem hx)
  · have h1 : x * p⁻¹ * x⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hMP (hXM hx)) _).mp (P.inv_mem hp)
    rw [show p * x * p⁻¹ * x⁻¹ = p * (x * p⁻¹ * x⁻¹) by group]
    exact P.mul_mem hp h1

theorem oTwoIn_le_centralizerModCore_of_isSubnormal {X M : Subgroup G} (hX : oResidualTwo ↥X = ⊤)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) : oTwoIn M ≤ centralizerModCore X :=
  le_centralizerModCore_of_isSubnormal hX hXM hsub (isPGroup_oTwoIn M) (oTwoIn_le M)
    (SixThree.le_normalizer_oTwoIn M)

theorem le_of_isSylowOf_centralizerModCore_inf {X M P R : Subgroup G} (hX : oResidualTwo ↥X = ⊤)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) (hP : IsPGroup 2 P) (hPM : P ≤ M)
    (hMP : M ≤ Subgroup.normalizer (P : Set G))
    (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M)) : P ≤ R :=
  Nine.le_of_isSylowOf_of_normal hR hP
    (le_inf (le_centralizerModCore_of_isSubnormal hX hXM hsub hP hPM hMP) hPM)
    (inf_le_right.trans hMP)

theorem oTwoIn_le_of_isSylowOf_centralizerModCore_inf {X M R : Subgroup G}
    (hX : oResidualTwo ↥X = ⊤) (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M)) : oTwoIn M ≤ R :=
  le_of_isSylowOf_centralizerModCore_inf hX hXM hsub (isPGroup_oTwoIn M) (oTwoIn_le M)
    (SixThree.le_normalizer_oTwoIn M) hR

theorem oTwoIn_self_le_of_isSylowOf_centralizerModCore_inf {X M R : Subgroup G} (hXM : X ≤ M)
    (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M)) : oTwoIn X ≤ R :=
  Nine.le_of_isSylowOf_of_normal hR (isPGroup_oTwoIn X)
    (le_inf (Glue.oTwoIn_le_centralizerModCore X) ((oTwoIn_le X).trans hXM))
    ((inf_le_left.trans (Glue.centralizerModCore_le_normalizer X)).trans
      (normalizer_le_normalizer_oTwoIn X))

omit [Finite G] in
theorem le_normalizer_of_oTwoIn_le_of_le_centralizerModCore {X R : Subgroup G}
    (hOR : oTwoIn X ≤ R) (hRC : R ≤ centralizerModCore X) :
    X ≤ Subgroup.normalizer (R : Set G) := by
  have key : ∀ y ∈ X, ∀ r ∈ R, y⁻¹ * r * y ∈ R := by
    intro y hy r hr
    have h1 := (hRC (inv_mem hr)).2 y⁻¹ (inv_mem hy)
    rw [show y⁻¹ * r * y = r * (r⁻¹ * y⁻¹ * r⁻¹⁻¹ * y⁻¹⁻¹) by group]
    exact mul_mem hr (hOR h1)
  intro y hy
  refine Subgroup.mem_normalizer_iff.mpr fun r => ⟨fun hr => ?_, fun hr => ?_⟩
  · simpa using key y⁻¹ (inv_mem hy) r hr
  · simpa [mul_assoc] using key y hy _ hr

omit [Finite G] in
theorem normalizer_oTwoIn_eq_of_isMaximalTwoLocal {M : Subgroup G}
    (hM : CFSG.IsMaximalTwoLocal M) : Subgroup.normalizer (oTwoIn M : Set G) = M := by
  have hle : M ≤ Subgroup.normalizer (oTwoIn M : Set G) := SixThree.le_normalizer_oTwoIn M
  have hne : oTwoIn M ≠ ⊥ := fun h => pCore_ne_bot_of_isPLocal hM.1
    ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h)
  by_contra hneq
  exact hM.2 _ (lt_of_le_of_ne hle (Ne.symm hneq))
    (isPLocal_normalizer_of_isPGroup (isPGroup_oTwoIn M) hne)

omit [Finite G] in
theorem blockU_conjugate (X : Subgroup G) (a : G) :
    blockU (conjugate X a) = conjugate (blockU X) a := by
  have h := EightOneRel.map_shortU_map_subtype (MulAut.conj a⁻¹).toMonoidHom
    (MulAut.conj a⁻¹).injective X
  rw [map_shortU_subtype, map_shortU_subtype] at h
  exact h

theorem inf_normalizer_blockU_le_normalizer {M X : Subgroup G} (hM : IsCharacteristicP 2 ↥M)
    (hX : IsBlockOfInX M X) :
    M ⊓ Subgroup.normalizer (blockU X : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  rintro g ⟨hgM, hgU⟩
  have hY : IsBlockOfInX M (conjugate X g⁻¹) :=
    ⟨CFSG.GroupTheory.conjugate_le_of_mem hX.1 (M.inv_mem hgM),
      isSubnormal_conjugate hX.2.1 (M.inv_mem hgM), inClassX_conjugate hX.2.2 g⁻¹⟩
  by_cases hYX : conjugate X g⁻¹ = X
  · refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hYX, ThreeFromEight.mem_conjugate_iff]
      simpa [mul_assoc] using hx
    · rw [← hYX, ThreeFromEight.mem_conjugate_iff] at hx
      simpa [mul_assoc] using hx
  · exfalso
    have hcomm := distinct_blocks_commute_of_isBlockOfInX hM hX hY (Ne.symm hYX)
    have hUY : blockU X ≤ conjugate X g⁻¹ := by
      have h1 : blockU (conjugate X g⁻¹) = blockU X := by
        rw [blockU_conjugate, ThreeFromEight.conjugate_eq_self_of_mem_normalizer (inv_mem hgU)]
      rw [← h1]
      exact blockU_le _
    have hbot : ⁅blockU X, X⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ⁅blockU X, X⁆ ≤ ⁅conjugate X g⁻¹, X⁆ := Subgroup.commutator_mono hUY le_rfl
        _ = ⁅X, conjugate X g⁻¹⁆ := Subgroup.commutator_comm _ _
        _ = ⊥ := hcomm
    rw [blockU_commutator_eq_self hX.2.2.1.residual_eq] at hbot
    exact blockU_ne_bot_of_short hX.2.2.1 hbot

theorem inOmega_conjugate {X : Subgroup G} (h : InOmega X) (g : G) : InOmega (conjugate X g) := by
  obtain ⟨hX, N, hN, hXN, hsub⟩ := h
  exact ⟨inClassX_conjugate hX g, conjugate N g, isMaximalTwoLocal_map_conj hN g⁻¹,
    CFSG.GroupTheory.conjugate_mono g hXN, CFSG.GroupTheory.isSubnormal_subgroupOf_conjugate g hsub⟩

theorem arrowMaximal_conjugate {X : Subgroup G}
    (hmax : ∀ Y : Subgroup G, InOmega Y → Arrow X Y → Y = X) (g : G) :
    ∀ Y : Subgroup G, InOmega Y → Arrow (conjugate X g) Y → Y = conjugate X g := by
  intro Y hY hXY
  have h1 : Arrow X (conjugate Y g⁻¹) := by
    have := arrow_conj hXY g⁻¹
    rwa [CFSG.GroupTheory.conjugate_conjugate, mul_inv_cancel, ThreeFromEight.conjugate_one]
      at this
  have h2 := hmax _ (inOmega_conjugate hY g⁻¹) h1
  calc Y = conjugate (conjugate Y g⁻¹) g := by
        rw [CFSG.GroupTheory.conjugate_conjugate, inv_mul_cancel, ThreeFromEight.conjugate_one]
    _ = conjugate X g := by rw [h2]

end CFSG.CGT.PushingUpLit.ThmOne
