module

public import CFSG.GH74.Generic.BProg.B1.PilotS1Facts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS3
open CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

section SL2Three

variable {F : Type} [Field F] [Finite F]

theorem isSolvable_sl2_three (hF3 : Nat.card F = 3) : Group.IsSolvable SL(2, F) := by
  have : Group.IsSolvable (GL (Fin 2) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable F
      (Or.inr hF3)
  exact Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective

@[expose] noncomputable def slMapEquiv {R S : Type} [CommRing R] [CommRing S] (f : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map f.toRingHom)
    (Matrix.SpecialLinearGroup.map f.symm.toRingHom)
    (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
    (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])

theorem nonempty_slEquiv_zmod_three (hF3 : Nat.card F = 3) :
    Nonempty (SL(2, F) ≃* SL(2, ZMod 3)) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let φ : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
    (by rw [← Nat.card_eq_fintype_card]; exact hF3)
  exact ⟨slMapEquiv φ.symm⟩

end SL2Three

theorem inf_pPrimeCore_eq_one_of_sl2 {H : Type*} [Group H] [Finite H] {M : Subgroup H} {F : Type}
    [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 ≤ Nat.card F) (e : ↥M ≃* SL(2, F)) :
    ∀ m ∈ M, m ∈ pPrimeCore 2 H → m = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥M := (pPrimeCore 2 H).subgroupOf M with hNdef
  have hN : N.Normal := Subgroup.Normal.subgroupOf (inferInstance : (pPrimeCore 2 H).Normal) M
  have hNodd : Odd (Nat.card ↥N) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 (even_iff_two_dvd.1 hne)
    have hmem : (((n : ↥M)) : H) ∈ pPrimeCore 2 H := n.2
    have hodd' := odd_orderOf_of_mem_pPrimeCore hmem
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hn] at hodd'
    exact absurd hodd' (by decide)
  have hbot := normal_odd_of_equiv_sl2 hodd h3 e N hN hNodd
  intro m hm hmO
  have : (⟨m, hm⟩ : ↥M) ∈ N := hmO
  rw [hbot, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

section Three

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Y : Subgroup X} {z u : X}
  {J₁ J₂ : Subgroup X}

theorem SplitAt.pPrimeCore_eq_bot_three (hF3 : Nat.card F = 3) (h : SplitAt F Y z u J₁ J₂) :
    pPrimeCore 2 ↥(centralizer ({u} : Set X) ⊓ Y) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card F) := by rw [hF3]; decide
  have h3 : 3 ≤ Nat.card F := by omega
  set H : Subgroup X := centralizer ({u} : Set X) ⊓ Y with hH
  have hJ₁H : J₁ ≤ H := h.le₁
  have hJ₂H : J₂ ≤ H := h.le₂
  set A₁ : Subgroup ↥H := J₁.subgroupOf H with hA₁
  set A₂ : Subgroup ↥H := J₂.subgroupOf H with hA₂
  set O : Subgroup ↥H := pPrimeCore 2 ↥H with hO
  obtain ⟨e₁⟩ := h.equiv₁
  obtain ⟨e₂⟩ := h.equiv₂
  have e₁' : ↥A₁ ≃* SL(2, F) := (Subgroup.subgroupOfEquivOfLe hJ₁H).trans e₁
  have e₂' : ↥A₂ ≃* SL(2, F) := (Subgroup.subgroupOfEquivOfLe hJ₂H).trans e₂
  have hZ₁ : Nat.card ↥(center ↥A₁) = 2 := natCard_center_of_equiv_sl2 hodd e₁'
  have hZ₂ : Nat.card ↥(center ↥A₂) = 2 := natCard_center_of_equiv_sl2 hodd e₂'
  have hO₁ : ∀ m ∈ A₁, m ∈ O → m = 1 := inf_pPrimeCore_eq_one_of_sl2 hodd h3 e₁'
  have hO₂ : ∀ m ∈ A₂, m ∈ O → m = 1 := inf_pPrimeCore_eq_one_of_sl2 hodd h3 e₂'
  have hA₁₂ : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb =>
    Subtype.ext (h.commute a ha b hb)
  have hsq : ∀ (A : Subgroup ↥H), Nat.card ↥(center ↥A) = 2 → ∀ a ∈ A,
      (∀ b ∈ A, a * b = b * a) → a ^ 2 = 1 := by
    intro A hZ a ha hac
    have hz : (⟨a, ha⟩ : ↥A) ∈ center ↥A := Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (hac g g.2).symm
    have := pow_card_eq_one' (G := ↥(center ↥A)) (x := ⟨⟨a, ha⟩, hz⟩)
    rw [hZ] at this
    have h2 := congrArg (fun t : ↥(center ↥A) => (((t : ↥A) : ↥H) : H)) this
    simpa using h2
  have hYO : ∀ m ∈ A₁ ⊔ A₂, m ∈ O → m = 1 := by
    intro m hm hmO
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hA₁₂ hm
    have hc12 : Commute a₁ a₂ := hA₁₂ a₁ ha₁ a₂ ha₂
    have hconj : ∀ a : ↥H, ⁅a, a₁ * a₂⁆ ∈ O := by
      intro a
      rw [commutatorElement_def]
      exact O.mul_mem (Subgroup.Normal.conj_mem inferInstance _ hmO a) (O.inv_mem hmO)
    have hcomm_mem : ∀ (A : Subgroup ↥H) (a b : ↥H), a ∈ A → b ∈ A → ⁅a, b⁆ ∈ A := by
      intro A a b ha hb
      rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
    have hc₁ : ∀ a ∈ A₁, a₁ * a = a * a₁ := by
      intro a ha
      have h2 : ⁅a, a₁ * a₂⁆ = ⁅a, a₁⁆ := by
        rw [hc12.eq]
        exact commutator_mul_right_of_commute hc12.symm (hA₁₂ a ha a₂ ha₂).symm
      have h3' : ⁅a, a₁⁆ = 1 := hO₁ _ (hcomm_mem A₁ a a₁ ha ha₁) (h2 ▸ hconj a)
      exact ((commutatorElement_eq_one_iff_mul_comm.1 h3').symm)
    have hc₂ : ∀ a ∈ A₂, a₂ * a = a * a₂ := by
      intro a ha
      have h2 : ⁅a, a₁ * a₂⁆ = ⁅a, a₂⁆ :=
        commutator_mul_right_of_commute hc12 (hA₁₂ a₁ ha₁ a ha)
      have h3' : ⁅a, a₂⁆ = 1 := hO₂ _ (hcomm_mem A₂ a a₂ ha ha₂) (h2 ▸ hconj a)
      exact ((commutatorElement_eq_one_iff_mul_comm.1 h3').symm)
    have h1 : a₁ ^ 2 = 1 := hsq A₁ hZ₁ a₁ ha₁ hc₁
    have h2 : a₂ ^ 2 = 1 := hsq A₂ hZ₂ a₂ ha₂ hc₂
    have hm2 : (a₁ * a₂) ^ 2 = 1 := by rw [hc12.mul_pow, h1, h2, one_mul]
    have hodd' := odd_orderOf_of_mem_pPrimeCore hmO
    have hdvd : orderOf (a₁ * a₂) ∣ 2 := orderOf_dvd_of_pow_eq_one hm2
    have : orderOf (a₁ * a₂) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h' | h'
      · exact h'
      · rw [h'] at hodd'; exact absurd hodd' (by decide)
    exact orderOf_eq_one_iff.1 this
  rw [eq_bot_iff]
  intro o ho
  have hosq : o * o ∈ A₁ ⊔ A₂ := by
    obtain ⟨j₁, hj₁, j₂, hj₂, hjj⟩ := mem_sup_of_commute h.commute
      (h.sq_mem (by omega) (o : X) o.2.2 (Subgroup.mem_centralizer_singleton_iff.1 o.2.1))
    have : o * o = (⟨j₁, hJ₁H hj₁⟩ : ↥H) * ⟨j₂, hJ₂H hj₂⟩ := Subtype.ext hjj
    rw [this]
    exact Subgroup.mul_mem_sup hj₁ hj₂
  have hoo : o * o = 1 := hYO _ hosq (O.mul_mem ho ho)
  have hodd' := odd_orderOf_of_mem_pPrimeCore ho
  have hdvd : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hoo)
  have : orderOf o = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h' | h'
    · exact h'
    · rw [h'] at hodd'; exact absurd hodd' (by decide)
  rw [orderOf_eq_one_iff.1 this]
  exact Subgroup.one_mem _

theorem SplitAt.pLayerOf_eq_bot_three (hF3 : Nat.card F = 3) (h : SplitAt F Y z u J₁ J₂) :
    pLayerOf 2 (centralizer ({u} : Set X) ⊓ Y) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup X := centralizer ({u} : Set X) ⊓ Y with hH
  have hJ₁H : J₁ ≤ H := h.le₁
  have hJ₂H : J₂ ≤ H := h.le₂
  set A₁ : Subgroup ↥H := J₁.subgroupOf H with hA₁
  set A₂ : Subgroup ↥H := J₂.subgroupOf H with hA₂
  set O : Subgroup ↥H := pPrimeCore 2 ↥H with hO
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπ
  obtain ⟨e₁⟩ := h.equiv₁
  obtain ⟨e₂⟩ := h.equiv₂
  have e₁' : ↥A₁ ≃* SL(2, F) := (Subgroup.subgroupOfEquivOfLe hJ₁H).trans e₁
  have e₂' : ↥A₂ ≃* SL(2, F) := (Subgroup.subgroupOfEquivOfLe hJ₂H).trans e₂
  have hsl : Group.IsSolvable SL(2, F) := isSolvable_sl2_three hF3
  have hs₁ : Group.IsSolvable ↥A₁ := Group.isSolvable_of_isSolvable_injective
    (f := e₁'.toMonoidHom) e₁'.injective
  have hs₂ : Group.IsSolvable ↥A₂ := Group.isSolvable_of_isSolvable_injective
    (f := e₂'.toMonoidHom) e₂'.injective
  have hsolvMap : ∀ (A : Subgroup ↥H), Group.IsSolvable ↥A → Group.IsSolvable ↥(A.map π) := by
    intro A hA
    let φ : ↥A →* ↥(A.map π) := (π.comp A.subtype).codRestrict (A.map π) (fun a => ⟨a, a.2, rfl⟩)
    have hφ : Function.Surjective φ := by
      rintro ⟨_, a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    exact Group.isSolvable_of_surjective hφ
  have hA₁n : A₁.Normal := h.normal₁
  have hA₂n : A₂.Normal := h.normal₂
  have hA₁₂ : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb =>
    Subtype.ext (h.commute a ha b hb)
  refine sSup_eq_bot.2 fun L' hL' => ?_
  exfalso
  have hLH : L' ≤ H := hL'.1
  have hcomp : IsPComponent 2 (L'.subgroupOf H) := hL'.2
  set Lg : Subgroup ↥H := L'.subgroupOf H with hLg
  have hperf : ⁅Lg, Lg⁆ = Lg :=
    Subgroup.isPerfect_iff.1
      (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hcomp)
  obtain ⟨Kb, hKb, -, hmap, -⟩ := hcomp
  have hLY : Lg ≤ A₁ ⊔ A₂ := by
    have h2 : ⁅Lg, Lg⁆ ≤ A₁ ⊔ A₂ := by
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨j₁, hj₁, j₂, hj₂, hjj⟩ := mem_sup_of_commute h.commute
        (h.comm (g₁ : X) g₁.2.2 (g₂ : X) g₂.2.2 (Subgroup.mem_centralizer_singleton_iff.1 g₁.2.1)
          (Subgroup.mem_centralizer_singleton_iff.1 g₂.2.1))
      have : ⁅g₁, g₂⁆ = (⟨j₁, hJ₁H hj₁⟩ : ↥H) * ⟨j₂, hJ₂H hj₂⟩ := Subtype.ext hjj
      rw [this]
      exact Subgroup.mul_mem_sup hj₁ hj₂
    rwa [hperf] at h2
  have hN₁ : (A₁.map π).Normal := hA₁n.map π (QuotientGroup.mk'_surjective O)
  have hN₂ : (A₂.map π).Normal := hA₂n.map π (QuotientGroup.mk'_surjective O)
  have hK1 : ⁅Kb, A₁.map π⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer (hsolvMap A₁ hs₁) hN₁.isSubnormal).1 Kb hKb
  have hK2 : ⁅Kb, A₂.map π⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer (hsolvMap A₂ hs₂) hN₂.isSubnormal).1 Kb hKb
  have hc₁ : ∀ k ∈ Kb, ∀ g ∈ A₁.map π, k * g = g * k := fun k hk g hg =>
    (commutatorElement_eq_one_iff_mul_comm.1
      (Subgroup.mem_bot.1 (hK1 ▸ Subgroup.commutator_mem_commutator hk hg)))
  have hc₂ : ∀ k ∈ Kb, ∀ g ∈ A₂.map π, k * g = g * k := fun k hk g hg =>
    (commutatorElement_eq_one_iff_mul_comm.1
      (Subgroup.mem_bot.1 (hK2 ▸ Subgroup.commutator_mem_commutator hk hg)))
  have hab : ∀ k ∈ Kb, ∀ k' ∈ Kb, k * k' = k' * k := by
    intro k hk k' hk'
    rw [← hmap] at hk'
    obtain ⟨ℓ, hℓ, rfl⟩ := hk'
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hA₁₂ (hLY hℓ)
    have e1 := hc₁ k hk (π a₁) ⟨a₁, ha₁, rfl⟩
    have e2 := hc₂ k hk (π a₂) ⟨a₂, ha₂, rfl⟩
    rw [map_mul, ← mul_assoc, e1, mul_assoc, e2, mul_assoc]
  obtain ⟨-, -, a', b', hab'⟩ := hKb.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
  have hba : a * b = b * a := Subtype.ext (hab a a.2 b b.2)
  exact hab' (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hba])

theorem SplitAt.isSolv2CompIn₁ (hF3 : Nat.card F = 3) (h : SplitAt F Y z u J₁ J₂) :
    IsSolv2CompIn (centralizer ({u} : Set X) ⊓ Y) J₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup X := centralizer ({u} : Set X) ⊓ Y with hH
  have hJ₁H : J₁ ≤ H := h.le₁
  set A₁ : Subgroup ↥H := J₁.subgroupOf H with hA₁
  set O : Subgroup ↥H := pPrimeCore 2 ↥H with hO
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπ
  obtain ⟨e₁⟩ := h.equiv₁
  have e₁' : ↥A₁ ≃* SL(2, F) := (Subgroup.subgroupOfEquivOfLe hJ₁H).trans e₁
  have hObot : pPrimeCore 2 ↥H = ⊥ := h.pPrimeCore_eq_bot_three hF3
  have hinj : ∀ m ∈ A₁, m ∈ π.ker → m = 1 := fun m _ hm => by
    rw [hπ, QuotientGroup.ker_mk'] at hm
    have hm' : m ∈ pPrimeCore 2 ↥H := hm
    rw [hObot, Subgroup.mem_bot] at hm'
    exact hm'
  obtain ⟨φ⟩ := nonempty_slEquiv_zmod_three hF3
  refine ⟨A₁.map π, (h.normal₁.map π (QuotientGroup.mk'_surjective O)).isSubnormal, ⟨?_⟩, ?_⟩
  · exact ((CFSG.ClassicalInvolution.Models.Transfer.mulEquivMap hinj).symm.trans e₁').trans φ
  · rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', hObot, sup_bot_eq, hA₁,
      Subgroup.map_subgroupOf_eq_of_le hJ₁H]

theorem SplitAt.pPrimeCore_J₁_eq_bot_three (hF3 : Nat.card F = 3) (h : SplitAt F Y z u J₁ J₂) :
    pPrimeCore 2 ↥J₁ = ⊥ := by
  obtain ⟨e₁⟩ := h.equiv₁
  have hodd : Odd (Nat.card F) := by rw [hF3]; decide
  have := inf_pPrimeCore_eq_one_of_sl2 (H := ↥J₁) (M := ⊤) hodd (by omega)
    (Subgroup.topEquiv.trans e₁)
  rw [Subgroup.eq_bot_iff_forall]
  intro m hm
  exact this m trivial hm

theorem SplitAt.pPrimeCoreOf_eq_bot_three (hF3 : Nat.card F = 3) (h : SplitAt F Y z u J₁ J₂) :
    pPrimeCoreOf 2 J₁ = ⊥ := by
  unfold pPrimeCoreOf
  rw [h.pPrimeCore_J₁_eq_bot_three hF3, Subgroup.map_bot]

theorem SplitAt.isSolv2CompIn_self (hF3 : Nat.card F = 3) (h : SplitAt F Y z u J₁ J₂) :
    IsSolv2CompIn J₁ J₁ := by
  obtain ⟨e₁⟩ := h.equiv₁
  obtain ⟨φ⟩ := nonempty_slEquiv_zmod_three hF3
  have hbot := h.pPrimeCore_J₁_eq_bot_three hF3
  refine ⟨⊤, Subgroup.IsSubnormal.top, ⟨?_⟩, ?_⟩
  · exact (Subgroup.topEquiv.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans
      QuotientGroup.quotientBot)).trans (e₁.trans φ)
  · rw [Subgroup.comap_top, Subgroup.map_top, Subgroup.range_subtype]

theorem SplitAt.extLayer2_eq_three (hF3 : Nat.card F = 3) (h : SplitAt F Y z u J₁ J₂) :
    extLayer2 J₁ = J₁ := by
  obtain ⟨e₁⟩ := h.equiv₁
  unfold extLayer2
  have hsl : Group.IsSolvable SL(2, F) := isSolvable_sl2_three hF3
  have hsJ : Group.IsSolvable ↥J₁ := Group.isSolvable_of_isSolvable_injective
    (f := e₁.toMonoidHom) e₁.injective
  have hpl : pLayerOf 2 J₁ = ⊥ := by
    refine sSup_eq_bot.2 fun L' hL' => ?_
    exact (CFSG.ComponentClassification.CatalogueBGeneralLinear.no_pComponent_of_solvable 2 _
      hL'.2).elim
  have hsolv : solvLayer2 J₁ = J₁ := by
    refine le_antisymm (iSup₂_le fun L hL => ?_) (le_iSup₂_of_le J₁ (h.isSolv2CompIn_self hF3) le_rfl)
    obtain ⟨Lb, -, -, rfl⟩ := hL
    exact Subgroup.map_subtype_le _
  rw [hpl, hsolv, bot_sup_eq]

end Three

theorem isSubnormalIn_of_normal {X : Type*} [Group X] {A P : Subgroup X} (hAP : A ≤ P)
    (hn : (A.subgroupOf P).Normal) : CFSG.IsSubnormalIn A P := by
  refine ⟨1, ![A, P], rfl, rfl, fun i => ?_, fun i => ?_⟩
  · fin_cases i
    exact hAP
  · fin_cases i
    exact hn

section Three2

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Y : Subgroup X} {z : X}

theorem Split1Like.subtermRel_three (hF3 : Nat.card F = 3) (hY : Split1Like F Y z)
    (hCY : ∀ w ∈ centralizer (Y : Set X), w = 1 ∨ w = z) {u : X} (hu : u ∈ Y)
    {J₁ J₂ : Subgroup X} (hS : SplitAt F Y z u J₁ J₂) : SubtermRel Y u J₁ := by
  have hsubn : CFSG.IsSubnormalIn J₁ (centralizer ({u} : Set X) ⊓ Y) :=
    isSubnormalIn_of_normal hS.le₁ hS.normal₁
  refine ⟨hS.ord, Subgroup.le_normalizer hu, Or.inr ⟨hS.isSolv2CompIn₁ hF3, J₁, ?_, ?_, ?_, ?_⟩⟩
  · rw [hS.pPrimeCoreOf_eq_bot_three hF3, sup_bot_eq]
  · rw [hS.pPrimeCoreOf_eq_bot_three hF3, inf_bot_eq]
  · rw [hS.pPrimeCoreOf_eq_bot_three hF3]
    exact Subgroup.commutator_bot_right _
  · intro z' hz' hz'2
    rcases hY.cases_of_mem hCY hu hS hz' hz'2 with h1 | h1 | h1
    · right; rw [h1]; exact hY.z_mem_centralizer
    · left; rw [h1]; exact hsubn
    · left; rw [h1, hY.centralizer_mul_eq]; exact hsubn

end Three2

end CFSG.GH74.Generic.BProg.B1.PilotS1
