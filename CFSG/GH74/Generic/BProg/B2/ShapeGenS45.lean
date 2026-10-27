module

public import CFSG.GH74.Generic.BProg.B1.PilotS4Facts
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87ReeCent
public import CFSG.Walter.AStar.Basic

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B1.PilotS4 CFSG.GH74.Generic.BProg.B1.PilotS5
  CFSG.Walter CFSG.Walter.J1Props CFSG.Open Subgroup
open scoped commutatorElement

@[expose] def ShapeGenFor (Pr : ∀ (Kt : Type) [Group Kt], Prop) (n : ℕ) : Prop :=
  ∀ (Kt : Type) [Group Kt] [Finite Kt], Pr Kt → ∀ B : Subgroup Kt, CFSG.IsElementaryAbelian 2 ↥B →
    Nat.card ↥B = n → (⨆ (b : Kt) (_ : b ∈ B ∧ b ∉ center Kt), centralizer ({b} : Set Kt)) = ⊤

namespace ShapeGenS45

section Gen

variable {X : Type*} [Group X]

@[expose] def cenGen (P : Set X) : Subgroup X :=
  ⨆ (b : X) (_ : b ∈ P), centralizer ({b} : Set X)

theorem le_cenGen {P : Set X} {b : X} (hb : b ∈ P) : centralizer ({b} : Set X) ≤ cenGen P :=
  le_iSup₂_of_le b hb le_rfl

theorem sq_eq_one_of_mem {B : Subgroup X} [CFSG.IsElementaryAbelian 2 ↥B] {b : X} (hb : b ∈ B) :
    b * b = 1 := by
  have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) b hb
  rwa [pow_two] at this

theorem orderOf_eq_two_of_mem {B : Subgroup X} [CFSG.IsElementaryAbelian 2 ↥B] {b : X} (hb : b ∈ B)
    (h1 : b ≠ 1) : orderOf b = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact sq_eq_one_of_mem hb) h1

theorem exists_ne_one_of_card_four [Finite X] {B : Subgroup X} (hcard : Nat.card ↥B = 4) :
    ∃ b ∈ B, b ≠ 1 := by
  by_contra h
  push Not at h
  have hB : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 h
  rw [hB, Subgroup.card_bot] at hcard
  omega

theorem exists_ne_one_ne_of_card_four [Finite X] {B : Subgroup X} [CFSG.IsElementaryAbelian 2 ↥B]
    (hcard : Nat.card ↥B = 4) {b : X} (hb : b ∈ B) (h1 : b ≠ 1) : ∃ b' ∈ B, b' ≠ 1 ∧ b' ≠ b := by
  have hle : ¬ B ≤ zpowers b := by
    intro hle
    have h2 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_two_of_mem hb h1, hcard] at h2
    omega
  obtain ⟨b', hb', hb'n⟩ := IsConcreteLE.not_le_iff_exists.1 hle
  exact ⟨b', hb', fun h => hb'n (h ▸ one_mem _), fun h => hb'n (h ▸ mem_zpowers b)⟩

theorem commutator_mem_of_index_two {Y : Type*} [Group Y] (N : Subgroup Y) (hN : N.index = 2)
    (a b : Y) : ⁅a, b⁆ ∈ N := by
  have : N.Normal := Subgroup.normal_of_index_eq_two hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (Y ⧸ N) :=
    isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card, hN])
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_commute]
  exact mul_comm' _ _

theorem no_index_two (P : Set X) (H : Subgroup X) (hH : H = cenGen P) (hP1 : ∀ b ∈ P, b ≠ 1)
    (hP2 : ∀ b ∈ P, b * b = 1)
    (hPc : ∀ b ∈ P, ∀ b' ∈ P, b * b' = b' * b) (hPm : ∀ b ∈ P, ∀ b' ∈ P, b ≠ b' → b * b' ∈ P)
    (hPe : ∀ b ∈ P, ∃ b' ∈ P, b' ≠ b)
    (hloc : ∀ b ∈ P, ∃ L : Subgroup X, L ≤ centralizer ({b} : Set X) ∧
      centralizer ({b} : Set X) = zpowers b ⊔ L ∧ ⁅L, L⁆ = L) :
    ∀ N : Subgroup ↥H, N.index ≠ 2 := by
  intro N hN
  set M : Subgroup X := N.map H.subtype with hM
  have hMc : ∀ x ∈ H, ∀ y ∈ H, ⁅x, y⁆ ∈ M := by
    intro x hx y hy
    refine ⟨⁅(⟨x, hx⟩ : ↥H), ⟨y, hy⟩⁆, commutator_mem_of_index_two N hN _ _, ?_⟩
    simp [commutatorElement_def]
  have hord : ∀ b ∈ P, orderOf b = 2 := fun b hb =>
    orderOf_eq_prime (by rw [pow_two]; exact hP2 b hb) (hP1 b hb)
  have hdata : ∀ b ∈ P, ∃ L : Subgroup X, L ≤ M ∧ L ≤ centralizer ({b} : Set X) ∧
      centralizer ({b} : Set X) = zpowers b ⊔ L := by
    intro b hb
    obtain ⟨L, hLC, hCeq, hLp⟩ := hloc b hb
    have hLH : L ≤ H := hLC.trans (hH ▸ le_cenGen hb)
    refine ⟨L, ?_, hLC, hCeq⟩
    calc L = ⁅L, L⁆ := hLp.symm
      _ ≤ M := Subgroup.commutator_le.2 fun x hx y hy => hMc x (hLH hx) y (hLH hy)
  have hstep : ∀ b ∈ P, ∀ b' ∈ P, b ≠ b' → b' ∈ M ∨ b * b' ∈ M := by
    intro b hb b' hb' _
    obtain ⟨L, hLM, hLC, hCeq⟩ := hdata b hb
    have hb'C : b' ∈ zpowers b ⊔ L := by
      rw [← hCeq]
      exact Subgroup.mem_centralizer_singleton_iff.2 (hPc b' hb' b hb)
    rcases mem_sup_zpowers_of_two (hord b hb) hLC hb'C with ⟨l, hl, hl'⟩ | ⟨l, hl, hl'⟩
    · left
      rw [hl']; exact hLM hl
    · right
      have : b * b' = l := by rw [hl', ← mul_assoc, hP2 b hb, one_mul]
      rw [this]; exact hLM hl
  have hbM : ∀ b ∈ P, b ∈ M := by
    intro b hb
    obtain ⟨b', hb', hne⟩ := hPe b hb
    by_contra hbM
    have hcomm : b' * b = b * b' := hPc b' hb' b hb
    have hA : b * b' ∈ M := by
      rcases hstep b' hb' b hb hne with h1 | h1
      · exact absurd h1 hbM
      · rwa [hcomm] at h1
    have hne2 : b * b' ≠ b := fun h => hP1 b' hb' (by simpa using h)
    have hB' : b' ∈ M := by
      rcases hstep (b * b') (hPm b hb b' hb' hne.symm) b hb hne2 with h1 | h1
      · exact absurd h1 hbM
      · have : b * b' * b = b' := by
          rw [mul_assoc, hcomm, ← mul_assoc, hP2 b hb, one_mul]
        rwa [this] at h1
    apply hbM
    have : b * b' * b' = b := by rw [mul_assoc, hP2 b' hb', mul_one]
    rw [← this]
    exact M.mul_mem hA hB'
  have hCM : ∀ b ∈ P, centralizer ({b} : Set X) ≤ M := by
    intro b hb g hg
    obtain ⟨L, hLM, hLC, hCeq⟩ := hdata b hb
    rw [hCeq] at hg
    rcases mem_sup_zpowers_of_two (hord b hb) hLC hg with ⟨l, hl, hl'⟩ | ⟨l, hl, hl'⟩
    · rw [hl']; exact hLM hl
    · rw [hl']; exact M.mul_mem (hbM b hb) (hLM hl)
  have hHM : H ≤ M := by
    rw [hH]
    exact iSup₂_le fun b hb => hCM b hb
  have htop : N = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hHM x.2
    have : y = x := Subtype.ext hyx
    rw [← this]; exact hy
  rw [htop, Subgroup.index_top] at hN
  exact absurd hN (by norm_num)

theorem eq_one_of_central_of_simple {L : Type*} [Group L] [IsSimpleGroup L]
    (hnc : ∃ a b : L, a * b ≠ b * a) {l : L} (hl : ∀ x : L, x * l = l * x) : l = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
  · have : l ∈ Subgroup.center L := Subgroup.mem_center_iff.2 hl
    rwa [h, Subgroup.mem_bot] at this
  · obtain ⟨a, b, hab⟩ := hnc
    exfalso
    apply hab
    have : b ∈ Subgroup.center L := by rw [h]; exact Subgroup.mem_top b
    exact (Subgroup.mem_center_iff.1 this a)

theorem centralizer_ne_of_ne {n : ℕ} (hs : SplitGrp n X) {b₁ b₂ : X} (ho1 : orderOf b₁ = 2)
    (h2 : b₂ ≠ 1) (h12 : b₂ ≠ b₁) :
    centralizer ({b₁} : Set X) ≠ centralizer ({b₂} : Set X) := by
  intro heq
  obtain ⟨L, hL⟩ := hs.split b₁ ho1
  have := hL.simple
  have hc1 : ∀ x ∈ L, x * b₁ = b₁ * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (hL.le_cent hx)
  have hc2 : ∀ x ∈ L, x * b₂ = b₂ * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (heq ▸ hL.le_cent hx)
  have hcentral : ∀ l ∈ L, (∀ x ∈ L, x * l = l * x) → l = 1 := by
    intro l hl hcomm
    have := eq_one_of_central_of_simple (L := ↥L) hL.nonabelian (l := ⟨l, hl⟩)
      (fun x => Subtype.ext (hcomm x x.2))
    exact congrArg Subtype.val this
  have hb₂C : b₂ ∈ zpowers b₁ ⊔ L := by
    rw [← hL.eq_sup, heq]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  rcases mem_sup_zpowers_of_two ho1 hL.le_cent hb₂C with ⟨l, hl, hl'⟩ | ⟨l, hl, hl'⟩
  · exact h2 (hl' ▸ hcentral l hl fun x hx => by rw [← hl']; exact hc2 x hx)
  · have hl1 : l = 1 := by
      refine hcentral l hl fun x hx => ?_
      have h3 := hc2 x hx
      rw [hl', ← mul_assoc, hc1 x hx, mul_assoc, mul_assoc] at h3
      exact mul_left_cancel h3
    exact h12 (by rw [hl', hl1, mul_one])

end Gen

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem mem_center_iff_of_equiv (e : X ≃* Y) (b : X) : e b ∈ center Y ↔ b ∈ center X := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff] at h ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e g)
  · intro h
    rw [Subgroup.mem_center_iff] at h ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, h g']

theorem gen_of_equiv (e : X ≃* Y) (B : Subgroup X)
    (h : (⨆ (b : Y) (_ : b ∈ B.map e.toMonoidHom ∧ b ∉ center Y), centralizer ({b} : Set Y)) = ⊤) :
    (⨆ (b : X) (_ : b ∈ B ∧ b ∉ center X), centralizer ({b} : Set X)) = ⊤ := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_top_of_surjective _ e.surjective, ← h]
  simp only [Subgroup.map_iSup]
  have hc : ∀ b : X, (centralizer ({b} : Set X)).map e.toMonoidHom = centralizer ({e b} : Set Y) :=
    fun b => CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' e b
  simp only [hc]
  rw [← e.toEquiv.iSup_comp (g := fun b' : Y =>
    ⨆ (_ : b' ∈ B.map e.toMonoidHom ∧ b' ∉ center Y), centralizer ({b'} : Set Y))]
  refine iSup_congr fun b => ?_
  refine iSup_congr_Prop ?_ fun _ => rfl
  show (b ∈ B ∧ b ∉ center X) ↔ (e b ∈ B.map e.toMonoidHom ∧ e b ∉ center Y)
  rw [mem_center_iff_of_equiv e b]
  exact and_congr (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm Iff.rfl

end Transport

section J1


theorem gen_walterJ1 (B : Subgroup walterJ1) [CFSG.IsElementaryAbelian 2 ↥B]
    (hcard : Nat.card ↥B = 4) :
    (⨆ (b : walterJ1) (_ : b ∈ B ∧ b ∉ center walterJ1), centralizer ({b} : Set walterJ1)) = ⊤ := by
  have hcen := walterJ1_center
  set P : Set walterJ1 := {b | b ∈ B ∧ b ≠ 1} with hPdef
  have hPeq : {b | b ∈ B ∧ b ∉ center walterJ1} = P := by
    ext b
    constructor
    · rintro ⟨hb, hbc⟩
      exact ⟨hb, fun h => hbc (h ▸ one_mem _)⟩
    · rintro ⟨hb, hb1⟩
      exact ⟨hb, fun h => hb1 (hcen b (Subgroup.mem_center_iff.1 h))⟩
  change cenGen {b | b ∈ B ∧ b ∉ center walterJ1} = ⊤
  rw [hPeq]
  set H := cenGen P with hH
  have hP1 : ∀ b ∈ P, b ≠ 1 := fun b hb => hb.2
  have hP2 : ∀ b ∈ P, b * b = 1 := fun b hb => sq_eq_one_of_mem hb.1
  have hPc : ∀ b ∈ P, ∀ b' ∈ P, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨b, hb.1⟩ : ↥B) ⟨b', hb'.1⟩)
  have hPm : ∀ b ∈ P, ∀ b' ∈ P, b ≠ b' → b * b' ∈ P := by
    intro b hb b' hb' hne
    refine ⟨B.mul_mem hb.1 hb'.1, fun h => hne ?_⟩
    rw [← inv_eq_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (hP2 b hb)]
  have hPe : ∀ b ∈ P, ∃ b' ∈ P, b' ≠ b := fun b hb => by
    obtain ⟨b', hb', h1, h2⟩ := exists_ne_one_ne_of_card_four hcard hb.1 hb.2
    exact ⟨b', ⟨hb', h1⟩, h2⟩
  have hloc : ∀ b ∈ P, ∃ L : Subgroup walterJ1, L ≤ centralizer ({b} : Set walterJ1) ∧
      centralizer ({b} : Set walterJ1) = zpowers b ⊔ L ∧ ⁅L, L⁆ = L := by
    intro b hb
    have ho := orderOf_eq_two_of_mem hb.1 hb.2
    obtain ⟨L, hLC, hbL, hCeq, ⟨eA⟩⟩ := walterJ1_split b ho
    have hsplit : IsSplit 60 b L (centralizer ({b} : Set walterJ1)) :=
      IsSplit.of_equiv_alternating ho hLC hbL hCeq eA
    have : Group.IsPerfect ↥L := hsplit.quasisimple.1
    exact ⟨L, hLC, hCeq, Subgroup.commutator_eq_self⟩
  have hidx := no_index_two P H hH hP1 hP2 hPc hPm hPe hloc
  obtain ⟨b₁, hb₁, h1⟩ := exists_ne_one_of_card_four hcard
  have hb₁P : b₁ ∈ P := ⟨hb₁, h1⟩
  have ho1 : orderOf b₁ = 2 := orderOf_eq_two_of_mem hb₁ h1
  obtain ⟨L, hLC, hbL, hCeq, ⟨eA⟩⟩ := walterJ1_split b₁ ho1
  have hCH : centralizer ({b₁} : Set walterJ1) ≤ H := le_cenGen hb₁P
  have hLH : L ≤ H := hLC.trans hCH
  have hb₁H : b₁ ∈ H := hCH (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hcentM : centralizer ({(⟨b₁, hb₁H⟩ : ↥H)} : Set ↥H) =
      zpowers (⟨b₁, hb₁H⟩ : ↥H) ⊔ L.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hLH]
    change _ = zpowers b₁ ⊔ L
    rw [← hCeq]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy))
    · intro hx
      refine ⟨⟨x, hCH hx⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_), rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.1 hx
  let JM : JankoHyp₀ ↥H :=
    { index_ne_two := hidx
      abelian_sylow := hasAbelianSylowTwo.subgroup H
      t := ⟨b₁, hb₁H⟩
      orderOf_t := by rw [Subgroup.orderOf_mk]; exact ho1
      F := L.subgroupOf H
      le_centralizer := by
        intro x hx
        refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
        exact Subgroup.mem_centralizer_singleton_iff.1 (hLC (Subgroup.mem_subgroupOf.1 hx))
      t_not_mem := fun h => hbL (Subgroup.mem_subgroupOf.1 h)
      centralizer_eq := hcentM
      iso := (Subgroup.subgroupOfEquivOfLe hLH).trans eA }
  obtain ⟨eH⟩ := JM.nonempty_mulEquiv_walterJ1
  rw [← Subgroup.card_eq_iff_eq_top]
  exact Nat.card_congr eH.toEquiv

end J1

end ShapeGenS45

theorem shapeGen_5 : ShapeGenFor QShape5 4 := by
  intro Kt _ _ hQ B hB hcard
  have hQ' : CFSG.Blueprint.NativeSporadic.IsSporadic Kt .J1 := hQ
  obtain ⟨e₀⟩ := hQ'
  let e : Kt ≃* walterJ1 := e₀.trans walterJ1EquivNative.symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hB
  have : CFSG.IsElementaryAbelian 2 ↥(B.map e.toMonoidHom) :=
    CFSG.IsElementaryAbelian.map e.toMonoidHom
  have hcard' : Nat.card ↥(B.map e.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard]
  exact ShapeGenS45.gen_of_equiv e B (ShapeGenS45.gen_walterJ1 (B.map e.toMonoidHom) hcard')

section Ree


theorem shapeGen_4 : ShapeGenFor QShape4 4 := by
  intro Kt _ _ hQ B hB hcard
  have := hB
  obtain ⟨n, hsplit⟩ := splitGrp_of_qShape4 hQ
  have hcen : ∀ z : Kt, (∀ g : Kt, g * z = z * g) → z = 1 := hsplit.center
  obtain ⟨f, hf⟩ := hQ
  have hT := reeTitsModel_of_lieModel hf
  obtain ⟨b₁, hb₁, h1⟩ := ShapeGenS45.exists_ne_one_of_card_four hcard
  obtain ⟨b₂, hb₂, h2, h12⟩ := ShapeGenS45.exists_ne_one_ne_of_card_four hcard hb₁ h1
  have ho1 := ShapeGenS45.orderOf_eq_two_of_mem hb₁ h1
  have ho2 := ShapeGenS45.orderOf_eq_two_of_mem hb₂ h2
  have hle : ∀ b ∈ B, b ≠ 1 → centralizer ({b} : Set Kt) ≤
      ⨆ (b : Kt) (_ : b ∈ B ∧ b ∉ center Kt), centralizer ({b} : Set Kt) := fun b hb hb1 =>
    le_iSup₂_of_le b ⟨hb, fun hc => hb1 (hcen b (Subgroup.mem_center_iff.1 hc))⟩ le_rfl
  by_contra hne
  have hco1 := (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.ree_involution_centralizer hT ho1).1
  have hco2 := (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.ree_involution_centralizer hT ho2).1
  have e1 := (hco1.le_iff.1 (hle b₁ hb₁ h1)).resolve_left hne
  have e2 := (hco2.le_iff.1 (hle b₂ hb₂ h2)).resolve_left hne
  exact ShapeGenS45.centralizer_ne_of_ne hsplit ho1 h2 h12 (e1.symm.trans e2)

end Ree

end CFSG.GH74.Generic.BProg.B2
