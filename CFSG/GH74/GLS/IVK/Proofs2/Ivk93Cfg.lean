module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Ord
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.RankThree.SubgroupLists.SL2Perfect
public import CFSG.GH74.GLS.Stage2.Final.ModelTransport

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.ComponentClassification CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

structure Ivk93Cfg {J : Type} [Group J] [Finite J] (x : J) (q : ℕ) (L₁ L₂ : Subgroup J) :
    Prop where
  ord : orderOf x = 2
  odd : Odd q
  five : 5 ≤ q
  ne : L₁ ≠ L₂
  comp₁ : IsPCompIn 2 (centralizer ({x} : Set J)) L₁
  comp₂ : IsPCompIn 2 (centralizer ({x} : Set J)) L₂
  mem₁ : x ∈ L₁
  mem₂ : x ∈ L₂
  sl₁ : HasSL2Model (↥L₁ ⧸ pPrimeCore 2 ↥L₁) (fun r => r = q)
  sl₂ : HasSL2Model (↥L₂ ⧸ pPrimeCore 2 ↥L₂) (fun r => r = q)

theorem exists_sl2_equiv_of_hasSL2Model {K : Type} [Group K] {q : ℕ}
    (hK : HasSL2Model K (fun r => r = q)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧ Nonempty (SL(2, F) ≃* K) := by
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := hK
  exact ⟨F, inferInstance, inferInstance, hFq,
    ⟨(specialLinearGroupEquivStatedSL 2 F).trans e.symm⟩⟩

theorem card_of_hasSL2Model {K : Type} [Group K] {q : ℕ}
    (hK : HasSL2Model K (fun r => r = q)) : Nat.card K = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model hK
  rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hFq]

theorem commute_map_of_ne_pComponent {X : Type*} [Group X] [Finite X] {K L : Subgroup X}
    (hK : IsPComponent 2 K) (hL : IsPComponent 2 L) (hne : K ≠ L) {k l : X} (hk : k ∈ K)
    (hl : l ∈ L) :
    QuotientGroup.mk' (pPrimeCore 2 X) k * QuotientGroup.mk' (pPrimeCore 2 X) l =
      QuotientGroup.mk' (pPrimeCore 2 X) l * QuotientGroup.mk' (pPrimeCore 2 X) k := by
  obtain ⟨-, -, hc, -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two K L hK hL).2 hne
  obtain ⟨-, -, hs, -, -⟩ := id hK
  have hcO : ⁅K, L⁆ ≤ pPrimeCore 2 X := by
    refine hc.trans (inf_le_left.trans ?_)
    rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs]
    exact inf_le_right
  have hmem : ⁅k, l⁆ ∈ pPrimeCore 2 X := hcO (commutator_mem_commutator hk hl)
  have h1 : QuotientGroup.mk' (pPrimeCore 2 X) ⁅k, l⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem card_mul_le_of_commute {Q : Type*} [Group Q] [Finite Q] (A₁ A₂ : Subgroup Q)
    (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hi : Nat.card ↥(A₁ ⊓ A₂) ≤ 2) :
    Nat.card ↥A₁ * Nat.card ↥A₂ ≤ 2 * Nat.card Q := by
  let φ : ↥A₁ × ↥A₂ →* Q :=
    { toFun := fun p => (p.1 : Q) * (p.2 : Q)
      map_one' := by simp
      map_mul' := fun p r => by
        have h1 : (p.2 : Q) * (r.1 : Q) = (r.1 : Q) * (p.2 : Q) := (hc r.1 r.1.2 p.2 p.2.2).symm
        show (p.1 : Q) * (r.1 : Q) * ((p.2 : Q) * (r.2 : Q)) =
          (p.1 : Q) * (p.2 : Q) * ((r.1 : Q) * (r.2 : Q))
        calc (p.1 : Q) * (r.1 : Q) * ((p.2 : Q) * (r.2 : Q))
            = (p.1 : Q) * ((r.1 : Q) * (p.2 : Q)) * (r.2 : Q) := by simp only [mul_assoc]
          _ = (p.1 : Q) * ((p.2 : Q) * (r.1 : Q)) * (r.2 : Q) := by rw [h1]
          _ = (p.1 : Q) * (p.2 : Q) * ((r.1 : Q) * (r.2 : Q)) := by simp only [mul_assoc] }
  have h1 : Nat.card (↥A₁ × ↥A₂) = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at this
    exact this
  have h2 : Nat.card ↥φ.ker ≤ 2 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun u : ↥φ.ker => (⟨((u : ↥A₁ × ↥A₂).1 : Q), ?_⟩ : ↥(A₁ ⊓ A₂))) ?_) hi
    · refine ⟨(u : ↥A₁ × ↥A₂).1.2, ?_⟩
      have hu : ((u : ↥A₁ × ↥A₂).1 : Q) * ((u : ↥A₁ × ↥A₂).2 : Q) = 1 := u.2
      have : ((u : ↥A₁ × ↥A₂).1 : Q) = ((u : ↥A₁ × ↥A₂).2 : Q)⁻¹ := eq_inv_of_mul_eq_one_left hu
      rw [this]
      exact A₂.inv_mem (u : ↥A₁ × ↥A₂).2.2
    · intro u v huv
      have h1' : ((u : ↥A₁ × ↥A₂).1 : Q) = ((v : ↥A₁ × ↥A₂).1 : Q) := by
        have := congrArg (fun w : ↥(A₁ ⊓ A₂) => (w : Q)) huv
        exact this
      have hu : ((u : ↥A₁ × ↥A₂).1 : Q) * ((u : ↥A₁ × ↥A₂).2 : Q) = 1 := u.2
      have hv : ((v : ↥A₁ × ↥A₂).1 : Q) * ((v : ↥A₁ × ↥A₂).2 : Q) = 1 := v.2
      have h2' : ((u : ↥A₁ × ↥A₂).2 : Q) = ((v : ↥A₁ × ↥A₂).2 : Q) := by
        have := hu.trans hv.symm
        rw [h1'] at this
        exact mul_left_cancel this
      apply Subtype.ext
      exact Prod.ext (Subtype.ext h1') (Subtype.ext h2')
  have h3 : Nat.card ↥φ.range ≤ Nat.card Q := Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [← Nat.card_prod, h1]
  calc Nat.card ↥φ.range * Nat.card ↥φ.ker ≤ Nat.card Q * 2 := Nat.mul_le_mul h3 h2
    _ = 2 * Nat.card Q := by ring

theorem isPComponent_subgroupOf_map_iff' {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) {L X : Subgroup A} (hLX : L ≤ X) :
    IsPComponent 2 (L.subgroupOf X) ↔
      IsPComponent 2 ((L.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom)) := by
  set f : X ≃* X.map e.toMonoidHom := X.equivMapOfInjective e.toMonoidHom e.injective with hf
  rw [(LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two f).1]
  congr! 1
  ext ⟨y, hy⟩
  simp only [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨⟨x, hxX⟩, hxL, hxy⟩
    refine ⟨x, hxL, ?_⟩
    have := congrArg Subtype.val hxy
    exact this
  · rintro ⟨x, hxL, rfl⟩
    exact ⟨⟨x, hLX hxL⟩, hxL, rfl⟩

theorem map_centralizer_singleton_equiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B) (x : A) :
    (centralizer ({x} : Set A)).map e.toMonoidHom = centralizer ({e x} : Set B) := by
  ext y
  obtain ⟨y, rfl⟩ := e.surjective y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  simp only [MulEquiv.symm_apply_apply]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    exact e.injective (by rw [map_mul, map_mul, h])

theorem isCentralInvolution_of_equiv {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) {x : G} (hx : IsCentralInvolution x) : IsCentralInvolution (e x) := by
  obtain ⟨h2, S, hxS, hxc⟩ := hx
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact h2,
    CFSG.GH74.GLS.Stage2.Final.ModelBlock.sylowMap e S, ?_, ?_⟩
  · rw [CFSG.GH74.GLS.Stage2.Final.ModelBlock.coe_sylowMap]
    exact ⟨x, hxS, rfl⟩
  · intro s hs
    rw [CFSG.GH74.GLS.Stage2.Final.ModelBlock.coe_sylowMap] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    show e s' * e x = e x * e s'
    rw [← map_mul, ← map_mul, hxc s' hs']

namespace Ivk93Cfg

variable {J : Type} [Group J] [Finite J] {x : J} {q : ℕ} {L₁ L₂ : Subgroup J}

theorem mul_self_eq_one (h : Ivk93Cfg x q L₁ L₂) : x * x = 1 := by
  rw [← pow_two, ← h.ord]
  exact pow_orderOf_eq_one x

theorem ne_one (h : Ivk93Cfg x q L₁ L₂) : x ≠ 1 := by
  intro h1
  have := h.ord
  rw [h1, orderOf_one] at this
  omega

theorem le₁ (h : Ivk93Cfg x q L₁ L₂) : L₁ ≤ centralizer ({x} : Set J) := h.comp₁.1

theorem le₂ (h : Ivk93Cfg x q L₁ L₂) : L₂ ≤ centralizer ({x} : Set J) := h.comp₂.1

theorem symm (h : Ivk93Cfg x q L₁ L₂) : Ivk93Cfg x q L₂ L₁ :=
  ⟨h.ord, h.odd, h.five, h.ne.symm, h.comp₂, h.comp₁, h.mem₂, h.mem₁, h.sl₂, h.sl₁⟩

theorem perfect₁ (h : Ivk93Cfg x q L₁ L₂) : Group.IsPerfect ↥L₁ := by
  have h1 := CatalogueBAlternating.pComponent_perfect h.comp₁.2
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe h.le₁).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe h.le₁).surjective

theorem perfect₂ (h : Ivk93Cfg x q L₁ L₂) : Group.IsPerfect ↥L₂ := h.symm.perfect₁

theorem card₁ (h : Ivk93Cfg x q L₁ L₂) :
    Nat.card ↥L₁ = q * (q ^ 2 - 1) * Nat.card ↥(pPrimeCore 2 ↥L₁) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥L₁), card_of_hasSL2Model h.sl₁]

theorem card₂ (h : Ivk93Cfg x q L₁ L₂) :
    Nat.card ↥L₂ = q * (q ^ 2 - 1) * Nat.card ↥(pPrimeCore 2 ↥L₂) := h.symm.card₁

theorem sl2_card_ge (h : Ivk93Cfg x q L₁ L₂) : 120 ≤ q * (q ^ 2 - 1) := by
  have := sl2_card_mono h.five
  norm_num at this
  omega

theorem card_ge₁ (h : Ivk93Cfg x q L₁ L₂) : 120 ≤ Nat.card ↥L₁ := by
  rw [h.card₁]
  have h1 : 1 ≤ Nat.card ↥(pPrimeCore 2 ↥L₁) := Nat.card_pos
  have h2 := h.sl2_card_ge
  nlinarith

theorem nontrivial₁ (h : Ivk93Cfg x q L₁ L₂) : Nontrivial ↥L₁ := by
  have h1 := h.card_ge₁
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have := Nat.card_of_subsingleton (1 : ↥L₁)
  omega

theorem not_solvable₁ (h : Ivk93Cfg x q L₁ L₂) : ¬ Group.IsSolvable ↥L₁ := by
  have := h.perfect₁
  have := h.nontrivial₁
  exact Group.IsPerfect.not_isSolvable ↥L₁

theorem false_of_solvable (h : Ivk93Cfg x q L₁ L₂)
    (hs : Group.IsSolvable ↥(centralizer ({x} : Set J))) : False :=
  h.not_solvable₁ (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion h.le₁) (Subgroup.inclusion_injective h.le₁))

theorem false_of_card_cent_dvd (h : Ivk93Cfg x q L₁ L₂) {N : ℕ}
    (hC : Nat.card ↥(centralizer ({x} : Set J)) ∣ N)
    (hN : ∀ q : ℕ, 5 ≤ q → ¬ q * (q ^ 2 - 1) ∣ N) : False := by
  have h1 : Nat.card ↥L₁ ∣ Nat.card ↥(centralizer ({x} : Set J)) := Subgroup.card_dvd_of_le h.le₁
  have h2 : q * (q ^ 2 - 1) ∣ Nat.card ↥L₁ := ⟨_, h.card₁⟩
  exact hN q h.five (h2.trans (h1.trans hC))

theorem false_of_card_group (h : Ivk93Cfg x q L₁ L₂) {N : ℕ} (hJ : Nat.card J ∣ N)
    (hN : ∀ q : ℕ, 5 ≤ q → ¬ q * (q ^ 2 - 1) ∣ N) : False := by
  have h1 : Nat.card ↥L₁ ∣ Nat.card J := Subgroup.card_subgroup_dvd_card _
  have h2 : q * (q ^ 2 - 1) ∣ Nat.card ↥L₁ := ⟨_, h.card₁⟩
  exact hN q h.five (h2.trans (h1.trans hJ))

theorem false_of_derived_le (h : Ivk93Cfg x q L₁ L₂) {F : Subgroup J} (hF : Nat.card ↥F < 120)
    (hD : ∀ a ∈ centralizer ({x} : Set J), ∀ b ∈ centralizer ({x} : Set J), ⁅a, b⁆ ∈ F) :
    False := by
  have hKF : L₁ ≤ F := by
    have hp : ⁅L₁, L₁⁆ = L₁ := Subgroup.isPerfect_iff.mp h.perfect₁
    rw [← hp]
    exact Subgroup.commutator_le.mpr fun a ha b hb => hD a (h.le₁ ha) b (h.le₁ hb)
  have h1 : Nat.card ↥L₁ ≤ Nat.card ↥F := Subgroup.card_le_of_le hKF
  have h2 := h.card_ge₁
  omega

theorem exists_nonabelian_two₁ (h : Ivk93Cfg x q L₁ L₂) :
    ∃ P : Subgroup J, P ≤ L₁ ∧ IsPGroup 2 ↥P ∧ ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model h.sl₁
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact h.odd
  obtain ⟨Q, hQ, a, ha, b, hb, hab⟩ := sl2_exists_quaternion hodd
  obtain ⟨S', hQS'⟩ := (hQ.map e.toMonoidHom).exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective
    (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L₁)) 2 S'
  have hSS' : (S : Subgroup ↥L₁).map (QuotientGroup.mk' (pPrimeCore 2 ↥L₁)) = (S' : Subgroup _) := by
    rw [← hS]
    rfl
  have hna : ∃ s ∈ (S : Subgroup ↥L₁), ∃ t ∈ (S : Subgroup ↥L₁), s * t ≠ t * s := by
    by_contra hcon
    have hcom : ∀ s ∈ (S : Subgroup ↥L₁), ∀ t ∈ (S : Subgroup ↥L₁), s * t = t * s :=
      fun s hs t ht => by
        by_contra hne
        exact hcon ⟨s, hs, t, ht, hne⟩
    apply hab
    have ha' : e a ∈ (S' : Subgroup _) := hQS' ⟨a, ha, rfl⟩
    have hb' : e b ∈ (S' : Subgroup _) := hQS' ⟨b, hb, rfl⟩
    rw [← hSS'] at ha' hb'
    obtain ⟨s, hs, hsa⟩ := ha'
    obtain ⟨t, ht, htb⟩ := hb'
    apply e.injective
    rw [map_mul, map_mul, ← hsa, ← htb]
    show QuotientGroup.mk' (pPrimeCore 2 ↥L₁) s * QuotientGroup.mk' (pPrimeCore 2 ↥L₁) t =
      QuotientGroup.mk' (pPrimeCore 2 ↥L₁) t * QuotientGroup.mk' (pPrimeCore 2 ↥L₁) s
    rw [← map_mul, ← map_mul, hcom s hs t ht]
  obtain ⟨s, hs, t, ht, hst⟩ := hna
  refine ⟨(S : Subgroup ↥L₁).map L₁.subtype, ?_, S.2.map _, (s : J), ⟨s, hs, rfl⟩, (t : J),
    ⟨t, ht, rfl⟩, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · intro hc
    exact hst (Subtype.ext hc)

theorem false_of_abelian_sylow (h : Ivk93Cfg x q L₁ L₂) (hab : CFSG.Walter.HasAbelianSylowTwo J) :
    False := by
  obtain ⟨H, -, hH2, a, ha, b, hb, hab'⟩ := h.exists_nonabelian_two₁
  obtain ⟨P, hP⟩ := hH2.exists_le_sylow
  apply hab'
  have hc := (hab P).is_comm.comm
  exact hc ⟨a, hP ha⟩ ⟨b, hP hb⟩ |> congrArg Subtype.val

theorem commute_bar (h : Ivk93Cfg x q L₁ L₂) :
    ∀ a ∈ (L₁.subgroupOf (centralizer ({x} : Set J))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set J)))),
      ∀ b ∈ (L₂.subgroupOf (centralizer ({x} : Set J))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set J)))), a * b = b * a := by
  rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
  refine commute_map_of_ne_pComponent h.comp₁.2 h.comp₂.2 ?_ hk hl
  intro heq
  apply h.ne
  have := Subgroup.subgroupOf_inj.mp heq
  rwa [inf_eq_left.mpr h.le₁, inf_eq_left.mpr h.le₂] at this

theorem card_bar₁ (h : Ivk93Cfg x q L₁ L₂) :
    Nat.card ↥((L₁.subgroupOf (centralizer ({x} : Set J))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set J))))) = q * (q ^ 2 - 1) := by
  obtain ⟨e, -⟩ := UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal h.le₁
    h.comp₁.2.choose_spec.2.1
  rw [← Nat.card_congr e.toEquiv, card_of_hasSL2Model h.sl₁]

theorem pair_card (h : Ivk93Cfg x q L₁ L₂) :
    (q * (q ^ 2 - 1)) ^ 2 ≤ 2 * Nat.card ↥(centralizer ({x} : Set J)) := by
  set C := centralizer ({x} : Set J) with hC
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set A₁ := (L₁.subgroupOf C).map π with hA₁
  set A₂ := (L₂.subgroupOf C).map π with hA₂
  have hc := h.commute_bar
  have h1 : Nat.card ↥A₁ = q * (q ^ 2 - 1) := h.card_bar₁
  have h2 : Nat.card ↥A₂ = q * (q ^ 2 - 1) := h.symm.card_bar₁
  have hi : Nat.card ↥(A₁ ⊓ A₂) ≤ 2 := by
    obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model h.sl₁
    obtain ⟨e', -⟩ := UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal h.le₁
      h.comp₁.2.choose_spec.2.1
    have hodd : Odd (Nat.card F) := by rw [hFq]; exact h.odd
    have h2F : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
    let ψ : SL(2, F) ≃* ↥A₁ := e.trans e'
    refine le_trans (Nat.card_le_card_of_injective
      (fun u : ↥(A₁ ⊓ A₂) => (⟨ψ.symm ⟨(u : _ ⧸ _), u.2.1⟩, ?_⟩ : ↥(Subgroup.center SL(2, F)))) ?_)
      (le_of_eq (CFSG.RankThree.SubgroupLists.natCard_center_sl2 h2F))
    · rw [Subgroup.mem_center_iff]
      intro g
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact hc _ (ψ g).2 _ u.2.2
    · intro u v huv
      have := congrArg (fun w : ↥(Subgroup.center SL(2, F)) => ψ (w : SL(2, F))) huv
      simp only [MulEquiv.apply_symm_apply] at this
      exact Subtype.ext (Subtype.mk.inj this)
  have := card_mul_le_of_commute A₁ A₂ hc hi
  rw [h1, h2] at this
  have h3 : Nat.card (↥C ⧸ pPrimeCore 2 ↥C) ≤ Nat.card ↥C :=
    Nat.le_of_dvd Nat.card_pos ⟨_, Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥C)⟩
  nlinarith [sq (q * (q ^ 2 - 1))]

theorem false_of_pair_card (h : Ivk93Cfg x q L₁ L₂)
    (hN : Nat.card ↥(centralizer ({x} : Set J)) < 7200) : False := by
  have h1 := h.pair_card
  have h2 := h.sl2_card_ge
  nlinarith

theorem of_equiv {J' : Type} [Group J'] [Finite J'] (Φ : J ≃* J') (h : Ivk93Cfg x q L₁ L₂) :
    Ivk93Cfg (Φ x) q (L₁.map Φ.toMonoidHom) (L₂.map Φ.toMonoidHom) := by
  have hc := map_centralizer_singleton_equiv' Φ x
  have hsl : ∀ {L : Subgroup J}, HasSL2Model (↥L ⧸ pPrimeCore 2 ↥L) (fun r => r = q) →
      HasSL2Model (↥(L.map Φ.toMonoidHom) ⧸ pPrimeCore 2 ↥(L.map Φ.toMonoidHom))
        (fun r => r = q) := by
    intro L hL
    obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := hL
    exact ⟨F, hF, hFin, hq, ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)).symm.trans e⟩⟩
  refine ⟨?_, h.odd, h.five, ?_, ?_, ?_, ⟨x, h.mem₁, rfl⟩, ⟨x, h.mem₂, rfl⟩, hsl h.sl₁, hsl h.sl₂⟩
  · rw [MulEquiv.orderOf_eq]
    exact h.ord
  · intro heq
    exact h.ne (Subgroup.map_injective Φ.injective heq)
  · rw [← hc]
    exact ⟨Subgroup.map_mono h.le₁, (isPComponent_subgroupOf_map_iff' Φ h.le₁).1 h.comp₁.2⟩
  · rw [← hc]
    exact ⟨Subgroup.map_mono h.le₂, (isPComponent_subgroupOf_map_iff' Φ h.le₂).1 h.comp₂.2⟩

end Ivk93Cfg

end CFSG.GH74.GLS.IVK.Proofs2
