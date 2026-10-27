module

public import CFSG.Goldschmidt.Steps.G36Basic
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Goldschmidt.StatementsG
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification
open scoped commutatorElement

theorem isSubnormal_map {G G' : Type*} [Group G] [Group G'] (f : G →* G') {H K : Subgroup G}
    (h : CFSG.Open.IsSubnormal H K) : CFSG.Open.IsSubnormal (H.map f) (K.map f) :=
  h.map f

theorem isSubnormal_of_subgroupOf {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (h : (H.subgroupOf K).IsSubnormal) : CFSG.Open.IsSubnormal H K := by
  have h1 := isSubnormal_map K.subtype (Components.chain_of_mathlib_subnormal h)
  rwa [Subgroup.map_subgroupOf_eq_of_le hHK, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h1

section TwoElements

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_mem_sup_of_odd {L O : Subgroup G} (hO : Odd (Nat.card O))
    (hLO : ∀ l ∈ L, ∀ o ∈ O, l * o = o * l) {x : G} (hx : x ∈ L ⊔ O) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ L := by
  have hLN : L ≤ Subgroup.normalizer (O : Set G) := by
    intro l hl
    apply mem_normalizer_of_conj_mem
    intro o ho
    rw [hLO l hl o ho, mul_inv_cancel_right]
    exact ho
  have hx' : x ∈ ((L ⊔ O : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L O hLN] at hx'
  obtain ⟨l, hl, o, ho, rfl⟩ := Set.mem_mul.mp hx'
  have hc : Commute l o := hLO l hl o ho
  have hpow : (l * o) ^ Nat.card O = l ^ Nat.card O := by
    rw [hc.mul_pow, orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard O ho), mul_one]
  have hcop : Nat.Coprime (Nat.card O) (orderOf (l * o)) := by
    have hdvd : orderOf (l * o) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    exact Nat.Coprime.coprime_dvd_right hdvd
      (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hO))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, hpow]
  exact L.pow_mem (L.pow_mem hl _) _

end TwoElements

section Component

variable {G : Type} [Group G] [Finite G]

theorem odd_card_goldschmidtOddCore (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (goldschmidtOddCore H)) := by
  have := CFSG.pPrimeCore_coprime_card (p := 2) (G := H)
  rw [goldschmidtOddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp this

theorem component_barOf {H A L : Subgroup G}
    (hL : GorensteinWalter.IsComponentOf L (normalClosureIn H A)) :
    L ≤ H ∧ (∀ l ∈ L, ∀ o ∈ oddCoreOf H, l * o = o * l) ∧
      CFSG.Open.IsComponentOf (barOf H L) (barOf H (normalClosureIn H A)) := by
  classical
  set K := normalClosureIn H A with hKdef
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hLK : L ≤ K := hL.1
  have hLH : L ≤ H := hLK.trans hKH
  set L' := L.subgroupOf H with hL'def
  set K' := K.subgroupOf H with hK'def
  have hK'n : K'.Normal := by
    have : K' = Subgroup.normalClosure ((A.subgroupOf H : Subgroup H) : Set H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
    infer_instance
  have hL'K' : L' ≤ K' := fun x hx => hLK hx
  have hsubL'K' : (L'.subgroupOf K').IsSubnormal := by
    let e : K ≃* K' := (Subgroup.subgroupOfEquivOfLe hKH).symm
    have hmap : (L.subgroupOf K).map e.toMonoidHom = L'.subgroupOf K' := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hx
        refine ⟨e.symm x, hx, ?_⟩
        simp
    rw [← hmap]
    exact hL.2.1.map e.surjective
  have hL'sub : L'.IsSubnormal := Subgroup.IsSubnormal.trans hL'K' hsubL'K' hK'n.isSubnormal
  have hLq : GorensteinWalter.IsQuasisimple L := hL.2.2
  let eL : L' ≃* L := Subgroup.subgroupOfEquivOfLe hLH
  have hL'q : CFSG.IsQuasisimple L' := by
    have hLq' : CFSG.IsQuasisimple L :=
      ⟨⟨hLq.2.1⟩, hLq.2.2, CFSG.Walter.IsQuasisimple.exists_mul_ne_mul hLq⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hLq'
  have hL'comp : CFSG.IsComponent L' := ⟨hL'q, hL'sub⟩
  have hOodd := odd_card_goldschmidtOddCore H
  have hOsol : Group.IsSolvable (goldschmidtOddCore H) := CFSG.Milestones.odd_order_solvable hOodd
  have hOcomm : ⁅L', goldschmidtOddCore H⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hOsol
      (goldschmidtOddCore_normal H).isSubnormal).1 L' hL'comp
  have hLO : ∀ l ∈ L, ∀ o ∈ oddCoreOf H, l * o = o * l := by
    intro l hl o ho
    obtain ⟨o', ho', rfl⟩ := ho
    have h1 : ⁅(⟨l, hLH hl⟩ : H), o'⁆ ∈ ⁅L', goldschmidtOddCore H⁆ :=
      Subgroup.commutator_mem_commutator hl ho'
    rw [hOcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact congrArg Subtype.val h1
  refine ⟨hLH, hLO, Subgroup.map_mono hL'K', ?_, ?_⟩
  · exact isSubnormal_map (QuotientGroup.mk' (goldschmidtOddCore H))
      (isSubnormal_of_subgroupOf hL'K' hsubL'K')
  · have hnot : ¬ L' ≤ (QuotientGroup.mk' (goldschmidtOddCore H)).ker := by
      rw [QuotientGroup.ker_mk']
      intro hle
      have h2 : 2 ∣ Nat.card L := CFSG.Walter.IsQuasisimple.two_dvd_card hLq
      have h3 : Nat.card L' ∣ Nat.card (goldschmidtOddCore H) := Subgroup.card_dvd_of_le hle
      rw [Nat.card_congr eL.toEquiv] at h3
      exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr (h2.trans h3))
    have hq := CFSG.LocalCores.isQuasisimple_map hL'q (QuotientGroup.mk' (goldschmidtOddCore H))
      hnot
    exact ⟨hq.1.commutator_eq_top, hq.2.1⟩

end Component

section Lemmas

variable {G : Type*} [Group G]

theorem preOf_barOf {H L : Subgroup G} (hLH : L ≤ H) :
    preOf H (barOf H L) = L ⊔ oddCoreOf H := by
  rw [preOf, barOf, Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hLH]
  rfl

theorem le_normalizer_map_subtype {M : Subgroup G} (X : Subgroup M) [X.Normal] :
    M ≤ Subgroup.normalizer ((X.map M.subtype : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨x', hx', rfl⟩
    refine ⟨⟨m, hm⟩ * x' * ⟨m, hm⟩⁻¹, Subgroup.Normal.conj_mem inferInstance x' hx' _, ?_⟩
    simp
  · rintro ⟨x', hx', hxe⟩
    have hx : x ∈ M := by
      have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
      rw [this, ← hxe]
      exact M.mul_mem (M.mul_mem (M.inv_mem hm) x'.2) hm
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    have h1 := Subgroup.Normal.conj_mem inferInstance x' hx' (⟨m, hm⟩ : M)⁻¹
    have h2 : (⟨m, hm⟩ : M)⁻¹ * x' * (⟨m, hm⟩ : M)⁻¹⁻¹ = ⟨x, hx⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [show (x' : G) = m * x * m⁻¹ from hxe]
      group
    rwa [h2] at h1

end Lemmas

section TypeTransfer

variable {P : Type} [Group P] [Finite P]

theorem isGoldType_of_top (hP : CFSG.Open.IsQuasisimple P)
    (hO : goldschmidtOddCore P ≤ Subgroup.center P)
    (h : IsGoldTypeI (⊤ : Subgroup (P ⧸ goldschmidtOddCore P)) ∨
      IsGoldTypeII (⊤ : Subgroup (P ⧸ goldschmidtOddCore P))) :
    IsGoldTypeI P ∨ IsGoldTypeII P := by
  classical
  set O := goldschmidtOddCore P with hOdef
  set Q := P ⧸ O
  set ψ := QuotientGroup.mk' O with hψdef
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective O
  have : Group.IsPerfect P := ⟨hP.1⟩
  have hker : ψ.ker ≤ Subgroup.center P := by rw [QuotientGroup.ker_mk']; exact hO
  have hZQ' : (Subgroup.center P).map ψ = Subgroup.center Q :=
    Quasisimple.center_map_of_central_kernel ψ hψs hker
  let e1 : (⊤ : Subgroup Q) ⧸ Subgroup.center (⊤ : Subgroup Q) ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (Subgroup.map_center_eq _)
  let e2 : Q ⧸ Subgroup.center Q ≃* P ⧸ Subgroup.center P :=
    (QuotientGroup.congr ((Subgroup.center P).map ψ) (Subgroup.center Q) (MulEquiv.refl _)
      (by simpa using hZQ')).symm.trans
      (QuotientGroup.quotientQuotientEquivQuotient O (Subgroup.center P) hO)
  let e := e1.trans e2
  rcases h with hI | ⟨hodd, hII⟩
  · left
    rcases hI with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
    · exact Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩
    · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
    · exact Or.inr (Or.inr ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · right
    refine ⟨?_, ?_⟩
    ·
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcardQ : Nat.card (Subgroup.center Q) = Nat.card (Subgroup.center (⊤ : Subgroup Q)) := by
        rw [← Subgroup.map_center_eq (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q),
          Subgroup.card_map_of_injective (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).injective]
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro h2
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2 h2
      have hz2 : (z : P) ^ 2 = 1 := by
        rw [← Subgroup.orderOf_coe] at hz
        rw [← hz, pow_orderOf_eq_one]
      have hz1 : (z : P) ≠ 1 := by
        intro h1
        rw [← Subgroup.orderOf_coe, h1, orderOf_one] at hz
        omega
      have hψz : ψ z ∈ Subgroup.center Q := hZQ' ▸ ⟨z, z.2, rfl⟩
      have hψz1 : ψ z ≠ 1 := by
        rw [hψdef, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
        intro hzO
        exact hz1 (eq_one_of_pow_two_pow_eq_one (odd_card_goldschmidtOddCore P) hzO
          (k := 1) (by rw [pow_one]; exact hz2))
      have hord : orderOf (⟨ψ z, hψz⟩ : Subgroup.center Q) = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact orderOf_eq_prime (by rw [← map_pow, hz2, map_one]) hψz1
      have h2Q : 2 ∣ Nat.card (Subgroup.center Q) := hord ▸ orderOf_dvd_natCard _
      rw [hcardQ] at h2Q
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2Q)
    · rcases hII with ⟨p, f, hp, hpodd, hf, h5, h8, ⟨g⟩⟩ | hJR
      · exact Or.inl ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e.symm.trans g⟩⟩
      · exact Or.inr (CFSG.Walter.IsTypeJR.of_mulEquiv e hJR)

end TypeTransfer

section SStarFacts

variable {G : Type} [Group G] [Finite G]

theorem sstar_facts {K L B T : Subgroup G} (hK : K = L) (hLqO : CFSG.Open.IsQuasisimple L)
    (hL2 : 2 ∣ Nat.card L)
    (hbar : barOf K B = CFSG.Open.pCore 2 (K ⧸ goldschmidtOddCore K) ⊔
      Omega1 (barOf K T ⊓ goldschmidtLayer (K ⧸ goldschmidtOddCore K)))
    (htype : ∀ L₁ : Subgroup (K ⧸ goldschmidtOddCore K), IsComponentOf L₁ ⊤ →
      IsGoldTypeI L₁ ∨ IsGoldTypeII L₁)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) :
    (∀ z ∈ Subgroup.center L, ∀ k : ℕ, z ^ 2 ^ k = 1 → (z : G) ∈ B) ∧
      (IsGoldTypeI L ∨ IsGoldTypeII L) := by
  classical
  subst hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOK : goldschmidtOddCore K ≤ Subgroup.center K := by
    rcases Quasisimple.normal_le_center_or_eq_top hLqO (goldschmidtOddCore K) with h1 | h1
    · exact h1
    · exfalso
      have h3 := odd_card_goldschmidtOddCore K
      rw [h1, Subgroup.card_top] at h3
      exact (Nat.not_even_iff_odd.mpr h3) (even_iff_two_dvd.mpr hL2)
  refine ⟨?_, ?_⟩
  · intro z hz k hk
    have hzQ : QuotientGroup.mk' (goldschmidtOddCore K) z ∈
        CFSG.Open.pCore 2 (K ⧸ goldschmidtOddCore K) := by
      refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore 2
        (Subgroup.zpowers (QuotientGroup.mk' _ z)) ?_ ?_ (Subgroup.mem_zpowers _)
      · apply Subgroup.normal_of_le_center
        rw [Subgroup.zpowers_le]
        exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) ⟨z, hz, rfl⟩
      · rintro ⟨w, hw⟩
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        refine ⟨k, Subtype.ext ?_⟩
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
          zpow_mul, zpow_natCast, ← map_pow, hk, map_one, one_zpow]
    have hzbar : QuotientGroup.mk' _ z ∈ barOf K B := by
      rw [hbar]
      exact Subgroup.mem_sup_left hzQ
    obtain ⟨a', ha', hae⟩ := hzbar
    have hw : a'⁻¹ * z ∈ goldschmidtOddCore K := by
      rw [← QuotientGroup.eq]
      exact hae
    have ha'2 : a' ^ 2 = 1 := Subtype.ext (by simpa using hB2 _ ha')
    have hcomm' : Commute a'⁻¹ z := (Subgroup.mem_center_iff.mp hz a'⁻¹)
    have hw2 : (a'⁻¹ * z) ^ 2 ^ (1 + k) = 1 :=
      pow_two_pow_mul_eq_one hcomm' (by rw [pow_one, inv_pow, ha'2, inv_one]) hk
    have h1 := eq_one_of_pow_two_pow_eq_one (odd_card_goldschmidtOddCore K) hw hw2
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact ha'
  · have hQq : CFSG.Open.IsQuasisimple (K ⧸ goldschmidtOddCore K) :=
      Quasisimple.central_quotient hLqO _ hOK
    have htop : IsComponentOf (⊤ : Subgroup (K ⧸ goldschmidtOddCore K)) ⊤ :=
      ⟨le_rfl, CFSG.Open.IsSubnormal.refl ⊤, Components.quasisimple_of_equiv Subgroup.topEquiv hQq⟩
    exact isGoldType_of_top hLqO hOK (htype ⊤ htop)

end SStarFacts

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_g36Hyp (h31 : S_G31) {H A L : Subgroup G} (hS : IsSStarIn H A)
    (hE : IsElemAbelian 2 A) (hL : GorensteinWalter.IsComponentOf L (normalClosureIn H A)) :
    (∀ a ∈ A, ∃ a₁ ∈ A ⊓ L, ∃ a₂ ∈ A ⊓ Subgroup.centralizer (L : Set G), a = a₁ * a₂) ∧
      ∃ T₀ : Sylow 2 L, G36Hyp L (A.subgroupOf L) T₀ ∧ (IsGoldTypeI L ∨ IsGoldTypeII L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLH, hLO, hLbar⟩ := component_barOf hL
  have hLq : GorensteinWalter.IsQuasisimple L := hL.2.2
  have hLqO : CFSG.Open.IsQuasisimple L := ⟨hLq.2.1, hLq.2.2⟩
  have hperf : Group.IsPerfect L := ⟨hLq.2.1⟩
  have hL2 : 2 ∣ Nat.card L := CFSG.Walter.IsQuasisimple.two_dvd_card hLq
  obtain ⟨hSM, hMeq, hAdec⟩ := (h31 G H A hS).1 (barOf H L) hLbar
  rw [preOf_barOf hLH] at hSM hMeq hAdec
  set O := oddCoreOf H with hOdef
  set M := L ⊔ O with hMdef
  have hOodd : Odd (Nat.card O) := by
    rw [hOdef, oddCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
    exact odd_card_goldschmidtOddCore H
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hAM : A ⊓ M = A ⊓ L := by
    apply le_antisymm
    · intro a ha
      refine ⟨ha.1, mem_of_mem_sup_of_odd hOodd hLO ha.2 (k := 1) ?_⟩
      rw [pow_one]
      exact hE.2 a ha.1
    · exact inf_le_inf_left _ le_sup_left
  have hAC : A ⊓ preOf H (Subgroup.centralizer (barOf H L : Set (H ⧸ goldschmidtOddCore H))) ≤
      Subgroup.centralizer (L : Set G) := by
    rintro a ⟨haA, ⟨a', ha', rfl⟩⟩
    have ha2 : (a' : G) ^ 2 = 1 := hE.2 _ haA
    have hcomm : ∀ l ∈ L, l * (a' : G) * l⁻¹ * (a' : G)⁻¹ ∈ O := by
      intro l hl
      have hlL : QuotientGroup.mk' (goldschmidtOddCore H) (⟨l, hLH hl⟩ : H) ∈ barOf H L :=
        ⟨⟨l, hLH hl⟩, hl, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp ha' _ hlL
      have h2 : (⟨l, hLH hl⟩ : H) * a' * (⟨l, hLH hl⟩ : H)⁻¹ * a'⁻¹ ∈ goldschmidtOddCore H := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
        have h1' : (⟨l, hLH hl⟩ : H) * (a' : H ⧸ goldschmidtOddCore H) =
            (a' : H ⧸ goldschmidtOddCore H) * (⟨l, hLH hl⟩ : H) := h1
        rw [h1']
        group
      exact ⟨_, h2, rfl⟩
    have hX : ⁅L, Subgroup.zpowers (a' : G)⁆ ≤ O := by
      rw [Subgroup.commutator_le]
      intro l hl g hg
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have ha2' : (a' : G) ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, ha2]
      rcases Int.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have : (a' : G) ^ (i + i) = 1 := by rw [← two_mul, zpow_mul, ha2', one_zpow]
        rw [this, commutatorElement_one_right]
        exact O.one_mem
      · have : (a' : G) ^ (2 * i + 1) = a' := by
          rw [zpow_add, zpow_mul, ha2', one_zpow, one_mul, zpow_one]
        rw [this, commutatorElement_def]
        exact hcomm l hl
    have hdouble : ⁅⁅L, Subgroup.zpowers (a' : G)⁆, L⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.commutator_mono hX le_rfl).trans ?_
      rw [Subgroup.commutator_le]
      intro o ho l hl
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (hLO l hl o ho).symm
    have h3 := CFSG.LocalCores.perfect_double_commutator hperf hdouble
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h4 : ⁅l, (a' : G)⁆ ∈ ⁅L, Subgroup.zpowers (a' : G)⁆ :=
      Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers _)
    rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h4
    exact h4
  have hdecomp : ∀ a ∈ A, ∃ a₁ ∈ A ⊓ L, ∃ a₂ ∈ A ⊓ Subgroup.centralizer (L : Set G),
      a = a₁ * a₂ := by
    intro a ha
    rw [hAdec, hAM] at ha
    set X := A ⊓ preOf H (Subgroup.centralizer (barOf H L : Set (H ⧸ goldschmidtOddCore H)))
    have hnorm : X ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
      intro x hx
      apply mem_normalizer_of_conj_mem
      intro b hb
      rw [hAcomm x hx.1 b hb.1, mul_inv_cancel_right]
      exact hb
    have ha' : a ∈ ((A ⊓ L ⊔ X : Subgroup G) : Set G) := ha
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at ha'
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Set.mem_mul.mp ha'
    exact ⟨a₁, ha₁, a₂, ⟨ha₂.1, hAC ha₂⟩, rfl⟩
  refine ⟨hdecomp, ?_⟩
  have hMnormL : M ≤ Subgroup.normalizer (L : Set G) := by
    apply sup_le Subgroup.le_normalizer
    intro o ho
    apply mem_normalizer_of_conj_mem
    intro l hl
    rw [← hLO l hl o ho, mul_inv_cancel_right]
    exact hl
  set N := normalClosureIn M (A ⊓ M) with hNdef
  have hNnorm : M ≤ Subgroup.normalizer (N : Set G) := le_normalizer_map_subtype _
  have hNL : N ≤ L := by
    have hLMn : (L.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hMnormL
    have h1 : Subgroup.normalClosure (((A ⊓ M).subgroupOf M : Subgroup M) : Set M) ≤
        L.subgroupOf M := by
      apply Subgroup.normalClosure_le_normal
      intro x hx
      have hx' : (x : G) ∈ A ⊓ M := hx
      rw [hAM] at hx'
      exact hx'.2
    rintro _ ⟨x, hx, rfl⟩
    exact h1 hx
  have hcontra : (∀ x ∈ N, ∀ l ∈ L, x * l = l * x) → False := by
    intro hNc
    have hNM : N ≤ M := Subgroup.map_subtype_le _
    have hOMn : M ≤ Subgroup.normalizer ((oddCoreOf M : Subgroup G) : Set G) :=
      le_normalizer_map_subtype _
    have hsup : goldschmidtOddCore M ⊔ N.subgroupOf M = ⊤ := by
      rw [eq_top_iff]
      intro m _
      have hm : (m : G) ∈ ((N ⊔ oddCoreOf M : Subgroup G) : Set G) := by
        rw [← hMeq]
        exact m.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right N (oddCoreOf M) (hNM.trans hOMn)] at hm
      obtain ⟨n, hn, o, ho, hno⟩ := Set.mem_mul.mp hm
      obtain ⟨o', ho', rfl⟩ := ho
      have hnM : n ∈ M := hNM hn
      have hm' : m = ⟨n, hnM⟩ * o' := Subtype.ext (by rw [Subgroup.coe_mul]; exact hno.symm)
      rw [hm']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (show (⟨n, hnM⟩ : M) ∈ N.subgroupOf M
        from hn)) (Subgroup.mem_sup_left ho')
    have hN'comm : IsMulCommutative (N.subgroupOf M) :=
      ⟨⟨fun x y => Subtype.ext (Subtype.ext (hNc _ x.2 _ (hNL y.2)))⟩⟩
    have hcomm : commutator M ≤ goldschmidtOddCore M :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hN'comm
    have hL'perf : Group.IsPerfect (L.subgroupOf M) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ M)).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have hL'le : L.subgroupOf M ≤ commutator M := by
      calc L.subgroupOf M = ⁅L.subgroupOf M, L.subgroupOf M⁆ :=
            (Subgroup.isPerfect_iff.mp hL'perf).symm
        _ ≤ ⁅(⊤ : Subgroup M), ⊤⁆ := Subgroup.commutator_mono le_top le_top
        _ = commutator M := (commutator_def M).symm
    have h3 : Nat.card (L.subgroupOf M) ∣ Nat.card (goldschmidtOddCore M) :=
      Subgroup.card_dvd_of_le (hL'le.trans hcomm)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ M)).toEquiv] at h3
    exact (Nat.not_even_iff_odd.mpr (odd_card_goldschmidtOddCore M))
      (even_iff_two_dvd.mpr (hL2.trans h3))
  have hN : N = L := by
    have hNLn : (N.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr (le_sup_left.trans hNnorm)
    rcases Quasisimple.normal_le_center_or_eq_top hLqO (N.subgroupOf L) with hc | htop
    · refine (hcontra fun x hx l hl => ?_).elim
      have := Subgroup.mem_center_iff.mp
        (hc (show (⟨x, hNL hx⟩ : L) ∈ N.subgroupOf L from hx)) ⟨l, hl⟩
      exact (congrArg Subtype.val this).symm
    · apply le_antisymm hNL
      intro l hl
      have : (⟨l, hl⟩ : L) ∈ N.subgroupOf L := htop ▸ Subgroup.mem_top _
      exact this
  have hAL : ¬ A.subgroupOf L ≤ Subgroup.center L := by
    intro hc
    apply hcontra
    set ZL := (Subgroup.center L).map L.subtype with hZLdef
    have hZLL : ZL ≤ L := Subgroup.map_subtype_le _
    have hZLnorm : M ≤ Subgroup.normalizer (ZL : Set G) := by
      intro m hm
      apply mem_normalizer_of_conj_mem
      rintro _ ⟨z, hz, rfl⟩
      have hmz : m * (z : G) * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hMnormL hm) z).mp z.2
      refine ⟨⟨_, hmz⟩, Subgroup.mem_center_iff.mpr fun l => Subtype.ext ?_, rfl⟩
      have hml : m⁻¹ * (l : G) * m ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (L : Set G)).inv_mem (hMnormL hm)) l).mp l.2
        simpa using this
      have hzc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨_, hml⟩)
      simp only [Subgroup.coe_mul] at hzc ⊢
      calc (l : G) * (m * z * m⁻¹) = m * ((m⁻¹ * l * m) * z) * m⁻¹ := by group
        _ = m * (z * (m⁻¹ * l * m)) * m⁻¹ := by rw [hzc]
        _ = m * z * m⁻¹ * l := by group
    have hZLn : (ZL.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hZLL.trans le_sup_left)).mpr hZLnorm
    have h1 : Subgroup.normalClosure (((A ⊓ M).subgroupOf M : Subgroup M) : Set M) ≤
        ZL.subgroupOf M := by
      apply Subgroup.normalClosure_le_normal
      intro x hx
      have hx' : (x : G) ∈ A ⊓ M := hx
      rw [hAM] at hx'
      exact ⟨⟨x, hx'.2⟩, hc hx'.1, rfl⟩
    intro x hx l hl
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨z, hz, hze⟩ := h1 hx'
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)
    rw [← hze]
    exact this.symm
  obtain ⟨-, -, T', hT'syl, hAT', hcl', hK'⟩ := hSM
  have hN' : normalClosureIn M (A ⊓ M) = L := hN
  dsimp only at hK'
  obtain ⟨-, -, hbar, htype⟩ := hK'
  obtain ⟨hctwo, htypeL⟩ := sstar_facts hN' hLqO hL2 hbar htype (fun b hb => hE.2 b hb.1)
  have hT'L : T' ≤ L := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one hT'syl.2.1 hx
    exact mem_of_mem_sup_of_odd hOodd hLO (hT'syl.1 hx) hk
  let eT : T'.subgroupOf L ≃* T' := Subgroup.subgroupOfEquivOfLe hT'L
  let T₀ : Sylow 2 L :=
    { toSubgroup := T'.subgroupOf L
      isPGroup' := hT'syl.2.1.of_equiv eT.symm
      is_maximal' := by
        intro Q hQ hle
        have hle' : T' ≤ Q.map L.subtype := fun x hx => ⟨⟨x, hT'L hx⟩, hle hx, rfl⟩
        have hQM : Q.map L.subtype ≤ M := (Subgroup.map_subtype_le Q).trans le_sup_left
        have heq := hT'syl.2.2 (Q.map L.subtype) hQM (hQ.map L.subtype) hle'
        apply le_antisymm _ hle
        intro x hx
        have hx' : (x : G) ∈ Q.map L.subtype := ⟨x, hx, rfl⟩
        rw [heq] at hx'
        exact hx' }
  refine ⟨T₀, ⟨hLqO, ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hAcomm _ x.2 _ y.2))⟩⟩,
    fun x hx => Subtype.ext (hE.2 _ hx)⟩, fun x hx => hAT' ⟨hx, Subgroup.mem_sup_left x.2⟩, ?_,
    hAL, fun z hz k hk => (hctwo z hz k hk).1⟩, htypeL⟩
  intro a ha g hg
  exact (hcl' (a : G) ⟨ha, Subgroup.mem_sup_left a.2⟩ (g : G) (Subgroup.mem_sup_left g.2) hg).1

end Main

end CFSG.Goldschmidt
