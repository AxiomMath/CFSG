module

public import CFSG.GH74.Generic.BProg.B3.Obs
public import CFSG.GH74.Generic.BProg.B3.S1SplitAux
public import CFSG.GH74.Generic.BProg.B1.PilotS1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS1
open CFSG.GH74.Generic.BProg.B3.S1SplitAux
open scoped MatrixGroups commutatorElement

section Structures

variable {G : Type} [Group G]

structure S1SplitMod (K A : Subgroup G) (x u : G) (J₁ J₂ : Subgroup G) : Prop where
  comp₁ : IsPCompIn 2 (K ⊓ centralizer ({u} : Set G)) J₁
  comp₂ : IsPCompIn 2 (K ⊓ centralizer ({u} : Set G)) J₂
  ne : J₁ ≠ J₂
  u_mem : u ∈ J₁
  xu_mem : x * u ∈ J₂
  layer : pLayerOf 2 (K ⊓ centralizer ({u} : Set G)) = J₁ ⊔ J₂
  commute : ∀ g ∈ J₁, ∀ h ∈ J₂, ⁅g, h⁆ ∈ pPrimeCoreOf 2 J₁ ⊓ pPrimeCoreOf 2 J₂
  sl2 : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Odd (Fintype.card F) ∧ 5 ≤ Fintype.card F ∧
    Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* SL(2, F)) ∧ Nonempty (↥J₂ ⧸ pPrimeCore 2 ↥J₂ ≃* SL(2, F))
  A_norm : A ≤ normalizer (J₁ : Set G) ⊓ normalizer (J₂ : Set G)
  A_act : ∀ c ∈ A, c ∉ closure ({u, x} : Set G) →
    c ∉ centralizerSection J₁ (pPrimeCoreOf 2 J₁) ∧ c ∉ centralizerSection J₂ (pPrimeCoreOf 2 J₂)

end Structures

section Shape

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem s1_basic (hc : Ctx21 G x K A a D J) (h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) :
    x ∈ K ∧ A ≤ K ∧ x ∈ A ∧
      ∀ w ∈ centralizer ((imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)),
        w = 1 ∨ w = CFSG.GH74.L5U5.xbar x := by
  obtain ⟨P, _, F', _, _, z₀, ⟨eP⟩, hP⟩ := B1.PilotS1.exists_grpS1_of_shape1 h1
  have hx2 := hc.circ.1.1.1.1
  have hK := hc.circ.1.1.1.2.2
  obtain ⟨hxK, -, -, hY, hCY, he8⟩ := B1.PilotS1.shape1_data hc.hyp.gen4 hx2 hK eP hP h1
  obtain ⟨hAK, hAel, hA8⟩ := B1.PilotS1.source_le hxK hc.src
  obtain ⟨hxA, -⟩ := B1.PilotS1.exists_y_of_e8 hx2 hK he8 hAK hAel hA8
  exact ⟨hxK, hAK, hxA, hCY⟩

end Shape

namespace S1Split

section Phi

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def phiHom (x u : G) {K : Subgroup G}
    (hKC : K ≤ centralizer ({x} : Set G)) :
    ↥(K ⊓ centralizer ({u} : Set G)) →* CentralizerBar x :=
  (proj x).comp (Subgroup.inclusion (inf_le_left.trans hKC))

theorem odd_card_ker_phiHom (x u : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) :
    Odd (Nat.card (phiHom x u hKC).ker) := by
  have h := B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion (inf_le_left.trans hKC :
      K ⊓ centralizer ({u} : Set G) ≤ centralizer ({x} : Set G)))
    (Subgroup.inclusion_injective _) (pPrimeCore 2 ↥(centralizer ({x} : Set G)))
    (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)
  have h' : ¬ 2 ∣ Nat.card (phiHom x u hKC).ker := h
  exact Nat.odd_iff.2 (by omega)

theorem range_phiHom (x : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) {u : G}
    (huK : u ∈ K) (hu2 : orderOf u = 2) :
    (phiHom x u hKC).range = centralizer ({bar x u} : Set (CentralizerBar x)) ⊓ imgBar x K := by
  have huC : u ∈ centralizer ({x} : Set G) := hKC huK
  ext c
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, mem_imgBar.2 ⟨⟨h, hKC hh.1⟩, hh.1, rfl⟩⟩
    rw [bar_of_mem huC]
    show proj x ⟨h, hKC hh.1⟩ * proj x ⟨u, huC⟩ = proj x ⟨u, huC⟩ * proj x ⟨h, hKC hh.1⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hh.2)
  · rintro ⟨hc1, hc2⟩
    obtain ⟨g, hgK, hgc⟩ := mem_imgBar.1 hc2
    set fK : ↥K →* CentralizerBar x := (proj x).comp (Subgroup.inclusion hKC) with hfK
    have hkerK : Odd (Nat.card fK.ker) := by
      have h := B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hKC)
        (Subgroup.inclusion_injective _) (pPrimeCore 2 ↥(centralizer ({x} : Set G)))
        (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)
      have h' : ¬ 2 ∣ Nat.card fK.ker := h
      exact Nat.odd_iff.2 (by omega)
    have hordK : orderOf (⟨u, huK⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
    have hfKu : fK ⟨u, huK⟩ = bar x u := by rw [bar_of_mem huC]; rfl
    have hct : c * fK ⟨u, huK⟩ = fK ⟨u, huK⟩ * c := by
      rw [hfKu]; exact Subgroup.mem_centralizer_singleton_iff.1 hc1
    obtain ⟨k, hk1, hk2⟩ := exists_commuting_lift fK hkerK hordK (c := c) ⟨⟨g, hgK⟩, hgc⟩ hct
    refine ⟨⟨(k : G), k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, hk1⟩
    exact congrArg Subtype.val hk2

theorem odd_card_ker_fK (x : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) :
    Odd (Nat.card ((proj x).comp (Subgroup.inclusion hKC)).ker) := by
  have h := B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hKC)
    (Subgroup.inclusion_injective _) (pPrimeCore 2 ↥(centralizer ({x} : Set G)))
    (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)
  have h' : ¬ 2 ∣ Nat.card ((proj x).comp (Subgroup.inclusion hKC)).ker := h
  exact Nat.odd_iff.2 (by omega)

theorem ker_fK_le (x : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) :
    ((proj x).comp (Subgroup.inclusion hKC)).ker ≤ pPrimeCore 2 ↥K := by
  have hnorm : ((proj x).comp (Subgroup.inclusion hKC)).ker.Normal := inferInstance
  exact le_sSup (show ((proj x).comp (Subgroup.inclusion hKC)).ker ∈
      {N : Subgroup ↥K | N.Normal ∧ Nat.Coprime 2 (Nat.card N)} from
    ⟨hnorm, Nat.coprime_two_left.2 (odd_card_ker_fK x hKC)⟩)

end Phi

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_s1SplitMod {x : G} {K A : Subgroup G} {F' : Type} [Field F'] [Finite F']
    (hodd : Odd (Nat.card F')) (hbig : 4 ≤ Nat.card F')
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hY : Split1Like F' (imgBar x K) (xbar x))
    (hxK : x ∈ K) (hAK : A ≤ K) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hxA : x ∈ A)
    {u : G} (huA : u ∈ A) (hu1 : u ≠ 1) (hux : u ≠ x) :
    ∃ J₁ J₂ : Subgroup G, S1SplitMod K A x u J₁ J₂ ∧ pPrimeCoreOf 2 J₁ ≤ pPrimeCoreOf 2 K ∧
      pPrimeCoreOf 2 J₂ ≤ pPrimeCoreOf 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have huK : u ∈ K := hAK huA
  have huC : u ∈ centralizer ({x} : Set G) := hKC huK
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hAsq u huA) hu1
  obtain ⟨hub, hub1, hub2⟩ := bar_facts hKC huK hu2
  have hubx : bar x u ≠ xbar x := by
    intro h
    apply hux
    refine B1.PilotS1.eq_of_proj_eq huC hxC (hAcomm u huA x hxA) (hAsq u huA) (hAsq x hxA) ?_
    rw [← bar_of_mem huC]; exact h
  obtain ⟨Jb₁, Jb₂, hS⟩ := hY.split (bar x u) hub hub2 hubx
  set Hg : Subgroup G := K ⊓ centralizer ({u} : Set G) with hHg
  set φ : ↥Hg →* CentralizerBar x := phiHom x u hKC with hφ
  have hker : Odd (Nat.card φ.ker) := odd_card_ker_phiHom x u hKC
  have hrange : φ.range = centralizer ({bar x u} : Set (CentralizerBar x)) ⊓ imgBar x K :=
    range_phiHom x hKC huK hu2
  have h₁ : IsPCompIn 2 φ.range Jb₁ := by rw [hrange]; exact hS.isPCompIn₁ hodd hbig
  have h₂ : IsPCompIn 2 φ.range Jb₂ := by rw [hrange]; exact hS.isPCompIn₂ hodd hbig
  have hall : ∀ M : Subgroup (CentralizerBar x), IsPCompIn 2 φ.range M → M = Jb₁ ∨ M = Jb₂ := by
    intro M hM
    rw [hrange] at hM
    exact eq_or_eq_of_isPCompIn hodd hbig hS hM
  obtain ⟨e₁⟩ := hS.equiv₁
  obtain ⟨e₂⟩ := hS.equiv₂
  have huHg : u ∈ Hg := ⟨huK, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hxuc : u * x = x * u := hAcomm u huA x hxA
  have hxuHg : x * u ∈ Hg := ⟨K.mul_mem hxK huK, Subgroup.mem_centralizer_singleton_iff.2 (by
    calc (x * u) * u = x * (u * u) := mul_assoc _ _ _
      _ = u * (x * u) := by rw [hAsq u huA, ← mul_assoc, hxuc, mul_assoc, hAsq u huA]
      )⟩
  have hφu : φ ⟨u, huHg⟩ = bar x u := (bar_of_mem huC).symm
  have hφxu : φ ⟨x * u, hxuHg⟩ = xbar x * bar x u := by
    have : (⟨x * u, hKC hxuHg.1⟩ : ↥(centralizer ({x} : Set G))) = ⟨x, hxC⟩ * ⟨u, huC⟩ := rfl
    show proj x ⟨x * u, hKC hxuHg.1⟩ = _
    rw [this, map_mul, ← bar_of_mem huC]
    rfl
  have hne : liftComp Hg φ Jb₁ ≠ liftComp Hg φ Jb₂ := by
    intro heq
    have e1 := map_liftComp hker h₁
    have e2 := map_liftComp hker h₂
    rw [heq] at e1
    have hJ : Jb₁ = Jb₂ := e1.symm.trans e2
    exact hub1 (Subgroup.disjoint_def.1 hS.disj hS.u_mem (hJ ▸ hS.u_mem))
  have hAHg : ∀ c ∈ A, c ∈ Hg := fun c hc =>
    ⟨hAK hc, Subgroup.mem_centralizer_singleton_iff.2 (hAcomm c hc u huA)⟩
  have hφc_mem : ∀ (c : G) (hc : c ∈ A), φ ⟨c, hAHg c hc⟩ ∈
      centralizer ({bar x u} : Set (CentralizerBar x)) ⊓ imgBar x K := fun c hc => by
    rw [← hrange]; exact ⟨_, rfl⟩
  have hnorm : ∀ Jb : Subgroup (CentralizerBar x),
      (∀ a ∈ imgBar x K, a * bar x u = bar x u * a → ∀ j ∈ Jb, a * j * a⁻¹ ∈ Jb) →
      ∀ c ∈ A, c ∈ normalizer (liftComp Hg φ Jb : Set G) := by
    intro Jb hn c hc
    refine mem_normalizer_liftComp (hAHg c hc) ?_
    have hmem := hφc_mem c hc
    exact mem_normalizer_of_norm hn hmem.2 (Subgroup.mem_centralizer_singleton_iff.1 hmem.1)
  have hxx : x * x = 1 := hAsq x hxA
  have hclx : x ∈ closure ({u, x} : Set G) :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton x))
  have hclu : u ∈ closure ({u, x} : Set G) := subset_closure (Set.mem_insert u _)
  have hact : ∀ Jb : Subgroup (CentralizerBar x), IsPCompIn 2 φ.range Jb → ↥Jb ≃* SL(2, F') →
      (∀ d ∈ imgBar x K, d * d = 1 → (∀ j ∈ Jb, d * j = j * d) →
        d = 1 ∨ d = xbar x ∨ d = bar x u ∨ d = xbar x * bar x u) →
      ∀ c ∈ A, c ∉ closure ({u, x} : Set G) →
        c ∉ centralizerSection (liftComp Hg φ Jb) (pPrimeCoreOf 2 (liftComp Hg φ Jb)) := by
    intro Jb hJ e hinv c hcA hc hcs
    have hcHg := hAHg c hcA
    have hcC : c ∈ centralizer ({x} : Set G) := hKC (hAK hcA)
    have hcomm : ∀ q ∈ Jb, φ ⟨c, hcHg⟩ * q = q * φ ⟨c, hcHg⟩ := by
      intro q hq
      rw [← map_liftComp hker hJ] at hq
      obtain ⟨y, hy, rfl⟩ := hq
      have h1 := hcs.2.2 (y : G) hy
      have hoH : ⁅(y : G), c⁆ ∈ Hg := (⁅y, (⟨c, hcHg⟩ : ↥Hg)⁆ : ↥Hg).2
      have h2 := map_pPrimeCoreOf_liftComp hker hJ e hodd hbig h1 hoH
      have h3 : φ ⟨⁅(y : G), c⁆, hoH⟩ = ⁅φ y, φ ⟨c, hcHg⟩⁆ := by
        have : (⟨⁅(y : G), c⁆, hoH⟩ : ↥Hg) = ⁅y, (⟨c, hcHg⟩ : ↥Hg)⁆ := rfl
        rw [this, map_commutatorElement]
      rw [h3] at h2
      exact (commutatorElement_eq_one_iff_mul_comm.1 h2).symm
    have hdd : φ ⟨c, hcHg⟩ * φ ⟨c, hcHg⟩ = 1 := by
      rw [← map_mul]
      have : (⟨c, hcHg⟩ : ↥Hg) * ⟨c, hcHg⟩ = 1 := Subtype.ext (hAsq c hcA)
      rw [this, map_one]
    have key := hinv _ (hφc_mem c hcA).2 hdd hcomm
    have hceq : ∀ b : G, b ∈ A → ∀ hbC : b ∈ centralizer ({x} : Set G),
        φ ⟨c, hcHg⟩ = proj x ⟨b, hbC⟩ → c = b := fun b hbA hbC h =>
      B1.PilotS1.eq_of_proj_eq hcC hbC (hAcomm c hcA b hbA) (hAsq c hcA) (hAsq b hbA) h
    apply hc
    rcases key with h | h | h | h
    · have := hceq 1 A.one_mem (Subgroup.one_mem _) (by rw [h]; exact (map_one (proj x)).symm)
      rw [this]; exact Subgroup.one_mem _
    · have := hceq x hxA hxC (by rw [h]; rfl)
      rw [this]; exact hclx
    · have := hceq u huA huC (by rw [h, bar_of_mem huC])
      rw [this]; exact hclu
    · have := hceq (x * u) (A.mul_mem hxA huA) (hKC hxuHg.1) (h.trans hφxu.symm)
      rw [this]; exact Subgroup.mul_mem _ hclx hclu
  have hcore : ∀ Jb : Subgroup (CentralizerBar x), IsPCompIn 2 φ.range Jb → ↥Jb ≃* SL(2, F') →
      pPrimeCoreOf 2 (liftComp Hg φ Jb) ≤ pPrimeCoreOf 2 K := by
    intro Jb hJ e o ho
    obtain ⟨o', ho', rfl⟩ := ho
    have hoHg : (o' : G) ∈ Hg := liftComp_le Jb o'.2
    have h1 := map_pPrimeCoreOf_liftComp hker hJ e hodd hbig ⟨o', ho', rfl⟩ hoHg
    have hoK : (o' : G) ∈ K := hoHg.1
    exact ⟨⟨(o' : G), hoK⟩, ker_fK_le x hKC (MonoidHom.mem_ker.2 h1), rfl⟩
  let _ : Fintype F' := Fintype.ofFinite F'
  have hcardF : Fintype.card F' = Nat.card F' := (Nat.card_eq_fintype_card).symm
  refine ⟨liftComp Hg φ Jb₁, liftComp Hg φ Jb₂, ?_, hcore Jb₁ h₁ e₁, hcore Jb₂ h₂ e₂⟩
  exact
    { comp₁ := isPCompIn_liftComp hker h₁
      comp₂ := isPCompIn_liftComp hker h₂
      ne := hne
      u_mem := mem_liftComp huHg (by rw [hφu]; exact hS.u_mem) (hAsq u huA)
      xu_mem := mem_liftComp hxuHg (by rw [hφxu]; exact hS.zu_mem) (by
        calc (x * u) * (x * u) = x * (u * x) * u := by group
          _ = x * (x * u) * u := by rw [hxuc]
          _ = (x * x) * (u * u) := by group
          _ = 1 := by rw [hxx, hAsq u huA, one_mul])
      layer := pLayerOf_eq_sup hker h₁ h₂ hall
      commute := commutator_mem_cores (isPCompIn_liftComp hker h₁) (isPCompIn_liftComp hker h₂) hne
      sl2 := ⟨F', inferInstance, inferInstance, by rw [hcardF]; exact hodd,
        by rw [hcardF]; rcases hodd with ⟨k, hk⟩; omega,
        quot_liftComp_equiv hker h₁ e₁ hodd hbig, quot_liftComp_equiv hker h₂ e₂ hodd hbig⟩
      A_norm := fun c hc => Subgroup.mem_inf.2 ⟨hnorm Jb₁ hS.norm₁ c hc, hnorm Jb₂ hS.norm₂ c hc⟩
      A_act := fun c hc hcl => ⟨hact Jb₁ h₁ e₁ hS.invol c hc hcl,
        hact Jb₂ h₂ e₂ (invol_swap hodd hbig hY hS hub hubx) c hc hcl⟩ }

end Main

end S1Split

section Bridge

variable {G : Type} [Group G] {K A : Subgroup G} {x u : G} {J₁ J₂ : Subgroup G}

theorem S1SplitMod.x_mem_sup (hS : S1SplitMod K A x u J₁ J₂) : x ∈ J₁ ⊔ J₂ := by
  have h : x = (x * u) * u⁻¹ := by group
  rw [h]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hS.xu_mem)
    (Subgroup.inv_mem _ (Subgroup.mem_sup_left hS.u_mem))

theorem S1SplitMod.x_mem_layer (hS : S1SplitMod K A x u J₁ J₂) :
    x ∈ pLayerOf 2 (K ⊓ centralizer ({u} : Set G)) := by
  rw [hS.layer]; exact hS.x_mem_sup

variable [Finite G]

end Bridge

section Final

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem s1_split_mod (hc : Ctx21 G x K A a D J)
    (h1 : B1.PilotS1.QShape1Big (↥K ⧸ pPrimeCore 2 ↥K)) {u : G} (huA : u ∈ A) (hu1 : u ≠ 1)
    (hux : u ≠ x) : ∃ J₁ J₂ : Subgroup G, S1SplitMod K A x u J₁ J₂ := by
  obtain ⟨P, _, F', _, _, z₀, ⟨eP⟩, hodd, hbig, hP⟩ := B1.PilotS1.exists_grpS1_of_big h1
  have hx2 : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  obtain ⟨hxK, -, -, hY, -, he8⟩ := B1.PilotS1.shape1_data hc.hyp.gen4 hx2 hK eP hP
    (B1.PilotS1.QShape1Big.qShape1 h1)
  obtain ⟨hAK, hAel, hA8⟩ := B1.PilotS1.source_le hxK hc.src
  obtain ⟨hxA, -⟩ := B1.PilotS1.exists_y_of_e8 hx2 hK he8 hAK hAel hA8
  obtain ⟨J₁, J₂, hS, -⟩ := S1Split.exists_s1SplitMod hodd hbig hK hY hxK hAK hAel hxA huA hu1 hux
  exact ⟨J₁, J₂, hS⟩

end Final

end CFSG.GH74.Generic.BProg.B3
