module

public import CFSG.CGT.T75M.SzData
public import CFSG.CGT.T75M.SzOut
public import CFSG.CGT.Timmesfeld75.Lemma27
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorus

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open scoped commutatorElement

section Action

variable {G : Type} [Group G]

@[expose] def conjAction (X U : Subgroup G) (hU : ∀ x ∈ X, ∀ m ∈ U, x * m * x⁻¹ ∈ U) :
    ↥X →* MulAut ↥U where
  toFun x :=
    { toFun := fun m => ⟨x * m * (x : G)⁻¹, hU x x.2 m m.2⟩
      invFun := fun m => ⟨(x : G)⁻¹ * m * x, by
        have := hU (x : G)⁻¹ (X.inv_mem x.2) m m.2
        simpa using this⟩
      left_inv := fun m => Subtype.ext (by simp [mul_assoc])
      right_inv := fun m => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun m n => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext m
    simp
  map_mul' x y := by
    ext m
    simp [mul_assoc]

@[simp] theorem conjAction_apply (X U : Subgroup G) (hU : ∀ x ∈ X, ∀ m ∈ U, x * m * x⁻¹ ∈ U)
    (x : ↥X) (m : ↥U) : ((conjAction X U hU x m : ↥U) : G) = x * m * (x : G)⁻¹ := rfl

end Action


section Pair

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

omit hN in
theorem eq_bot_of_forall_comm (hS : Sec3 T T₁) {m : G} (hm : m ∈ cfgM T T₁)
    (hc : ∀ x ∈ T ⊔ T₁, x * m = m * x) : m = 1 := by
  obtain ⟨t, htT, htM⟩ := IsConcreteLE.not_le_iff_exists.1 hS.not_le_cfgM
  obtain ⟨x₀, hx₀, hT₁⟩ := hS.conj
  obtain ⟨t₁, ht₁, ht₁M⟩ := IsConcreteLE.not_le_iff_exists.1 (hS.not_conj_le_cfgM hx₀)
  have ht₁T₁ : t₁ ∈ T₁ := hT₁ ▸ ht₁
  have hL : m ∈ normIn T T₁ := by
    rw [← hS.cfg.cfgM_inf_centralizer htT htM]
    exact ⟨hm, Subgroup.mem_centralizer_singleton_iff.2 (hc t (Subgroup.mem_sup_left htT)).symm⟩
  have hL₁ : m ∈ normIn T₁ T := by
    have ht₁M' : t₁ ∉ cfgM T₁ T := by rw [cfgM_symm]; exact ht₁M
    have := hS.cfg.symm.cfgM_inf_centralizer ht₁T₁ ht₁M'
    rw [← this, cfgM_symm]
    exact ⟨hm, Subgroup.mem_centralizer_singleton_iff.2 (hc t₁ (Subgroup.mem_sup_right ht₁T₁)).symm⟩
  have h : m ∈ T ⊓ T₁ := ⟨normIn_le _ _ hL, normIn_le _ _ hL₁⟩
  rw [hS.cfg.inf, Subgroup.mem_bot] at h
  exact h

theorem eq_bot_or_le_card_of_invariant (hS : Sec3 T T₁) {a : ℕ}
    (ha : 1 ≤ a) (e : XQ ≃* Sz a) {U : Subgroup G} (hUM : U ≤ cfgM T T₁)
    (hU : ∀ x ∈ T ⊔ T₁, ∀ m ∈ U, x * m * x⁻¹ ∈ U) :
    U = ⊥ ∨ 2 ^ (4 * (2 * a + 1)) ≤ Nat.card U := by
  classical
  have hK : CFSG.BenderSuzuki.IsBenderGroup XQ := isBenderGroup_of_mulEquiv_sz ha e
  have hsimple : IsSimpleGroup XQ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hK
  have hker : (cfgM T T₁).subgroupOf (T ⊔ T₁) ≤ (conjAction (T ⊔ T₁) U hU).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    ext m
    have hxM : (x : G) ∈ cfgM T T₁ := Subgroup.mem_subgroupOf.1 hx
    have hcomm : (x : G) * m = m * x :=
      elemAbelian_mul_comm hS.cfg.isElemAbelian_cfgM hxM (hUM m.2)
    simp only [conjAction_apply, MulAut.one_apply]
    rw [hcomm]; simp
  let ρ : XQ →* MulAut ↥U := QuotientGroup.lift _ (conjAction (T ⊔ T₁) U hU) hker
  rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with h | h
  · right
    have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hU2 : IsPGroup 2 U :=
      (isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM).to_le hUM
    obtain ⟨d, hd⟩ := hU2.exists_card_eq
    have hdiv : Nat.card (Sz a) ∣ Nat.card XQ := by
      rw [Nat.card_congr e.toEquiv]
    have := lemma27_sz ha hdiv ρ hinj hd
    rw [hd]
    exact Nat.pow_le_pow_right (by norm_num) this
  · left
    rw [eq_bot_iff]
    intro m hm
    rw [Subgroup.mem_bot]
    refine eq_bot_of_forall_comm hS (hUM hm) fun x hx => ?_
    have h1 : QuotientGroup.mk (⟨x, hx⟩ : ↥(T ⊔ T₁)) ∈ ρ.ker := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at h1
    have h2 : conjAction (T ⊔ T₁) U hU ⟨x, hx⟩ = 1 := h1
    have h3 := congrArg (fun τ : MulAut ↥U => ((τ ⟨m, hm⟩ : ↥U) : G)) h2
    simp only [conjAction_apply, MulAut.one_apply] at h3
    calc x * m = x * m * x⁻¹ * x := by group
      _ = m * x := by rw [h3]

end Pair


section Comm

variable {G : Type} [Group G]

@[expose] def commHom (A : Subgroup G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (u : G)
    (hu : u ∈ Subgroup.normalizer (A : Set G)) : ↥A →* ↥A where
  toFun a := ⟨a * (u * (a : G)⁻¹ * u⁻¹),
    A.mul_mem a.2 ((Subgroup.mem_normalizer_iff.1 hu _).1 (A.inv_mem a.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    have hp : u * (a : G)⁻¹ * u⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hu _).1 (A.inv_mem a.2)
    have hq : u * (b : G)⁻¹ * u⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hu _).1 (A.inv_mem b.2)
    have h1 : (b : G) * (u * (a : G)⁻¹ * u⁻¹) = (u * (a : G)⁻¹ * u⁻¹) * b := hA _ b.2 _ hp
    have h2 : (u * (b : G)⁻¹ * u⁻¹) * (u * (a : G)⁻¹ * u⁻¹) =
        (u * (a : G)⁻¹ * u⁻¹) * (u * (b : G)⁻¹ * u⁻¹) := hA _ hq _ hp
    show (a : G) * b * (u * ((a : G) * b)⁻¹ * u⁻¹) =
      (a : G) * (u * (a : G)⁻¹ * u⁻¹) * ((b : G) * (u * (b : G)⁻¹ * u⁻¹))
    calc (a : G) * b * (u * ((a : G) * b)⁻¹ * u⁻¹)
        = (a : G) * b * ((u * (b : G)⁻¹ * u⁻¹) * (u * (a : G)⁻¹ * u⁻¹)) := by group
      _ = (a : G) * b * ((u * (a : G)⁻¹ * u⁻¹) * (u * (b : G)⁻¹ * u⁻¹)) := by rw [h2]
      _ = (a : G) * ((b : G) * (u * (a : G)⁻¹ * u⁻¹)) * (u * (b : G)⁻¹ * u⁻¹) := by
        simp only [mul_assoc]
      _ = (a : G) * ((u * (a : G)⁻¹ * u⁻¹) * b) * (u * (b : G)⁻¹ * u⁻¹) := by rw [h1]
      _ = (a : G) * (u * (a : G)⁻¹ * u⁻¹) * ((b : G) * (u * (b : G)⁻¹ * u⁻¹)) := by
        simp only [mul_assoc]

theorem commHom_apply (A : Subgroup G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (u : G)
    (hu : u ∈ Subgroup.normalizer (A : Set G)) (a : ↥A) :
    ((commHom A hA u hu a : ↥A) : G) = a * u * (a : G)⁻¹ * u⁻¹ := by
  show (a : G) * (u * (a : G)⁻¹ * u⁻¹) = _
  simp only [mul_assoc]

theorem mem_ker_commHom (A : Subgroup G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (u : G)
    (hu : u ∈ Subgroup.normalizer (A : Set G)) (a : ↥A) :
    a ∈ (commHom A hA u hu).ker ↔ (a : G) * u = u * a := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg Subtype.val h
    rw [commHom_apply] at this
    have h2 : (a : G) * u * (a : G)⁻¹ * u⁻¹ = 1 := this
    calc (a : G) * u = (a : G) * u * (a : G)⁻¹ * u⁻¹ * (u * a) := by group
      _ = u * a := by rw [h2, one_mul]
  · intro h
    apply Subtype.ext
    rw [commHom_apply]
    show (a : G) * u * (a : G)⁻¹ * u⁻¹ = 1
    rw [h]; group

end Comm


section Card

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem card_cfgM_eq_mul (c : Cfg T T₁) :
    Nat.card (cfgM T T₁) = Nat.card (normIn T T₁) * Nat.card (normIn T₁ T) := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p : ↥(normIn T T₁) × ↥(normIn T₁ T) =>
    (⟨(p.1 : G) * p.2, (cfgM T T₁).mul_mem (Cfg.normIn_le_cfgM_left T T₁ p.1.2)
      (Cfg.normIn_le_cfgM_right T T₁ p.2.2)⟩ : ↥(cfgM T T₁))) ⟨?_, ?_⟩)
  · rintro ⟨⟨l, hl⟩, ⟨x, hx⟩⟩ ⟨⟨l', hl'⟩, ⟨x', hx'⟩⟩ h
    have h1 : l * x = l' * x' := congrArg Subtype.val h
    have h2 : l'⁻¹ * l ∈ T ⊓ T₁ := by
      refine ⟨T.mul_mem (T.inv_mem (normIn_le _ _ hl')) (normIn_le _ _ hl), ?_⟩
      have : l'⁻¹ * l = x' * x⁻¹ := by
        calc l'⁻¹ * l = l'⁻¹ * (l * x) * x⁻¹ := by group
          _ = l'⁻¹ * (l' * x') * x⁻¹ := by rw [h1]
          _ = x' * x⁻¹ := by group
      rw [this]
      exact T₁.mul_mem (normIn_le _ _ hx') (T₁.inv_mem (normIn_le _ _ hx))
    rw [c.inf, Subgroup.mem_bot, inv_mul_eq_one] at h2
    subst h2
    have h3 : x = x' := mul_left_cancel h1
    subst h3
    rfl
  · rintro ⟨m, hm⟩
    obtain ⟨l, hl, x, hx, rfl⟩ := c.mem_cfgM_iff.1 hm
    exact ⟨(⟨l, hl⟩, ⟨x, hx⟩), rfl⟩

end Card


section Trick

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

theorem two_pow_le_card_normIn (hS : Sec3 T T₁) {a : ℕ}
    (ha : 1 ≤ a) (e : XQ ≃* Sz a) : 2 ^ (2 * (2 * a + 1)) ≤ Nat.card (normIn T T₁) := by
  have hM : cfgM T T₁ ≠ ⊥ := fun h =>
    hS.cfg.ne (le_bot_iff.1 ((Cfg.normIn_le_cfgM_left T T₁).trans h.le))
  rcases eq_bot_or_le_card_of_invariant hS ha e (le_refl _)
    (fun x hx m hm => hS.cfg.conj_mem_cfgM hx hm) with h | h
  · exact absurd h hM
  · have h1 : Nat.card (cfgM T T₁) = Nat.card (normIn T T₁) ^ 2 := by
      rw [card_cfgM_eq_mul hS.cfg, card_normIn_right hS, sq]
    rw [h1] at h
    have h2 : (2 ^ (2 * (2 * a + 1))) ^ 2 ≤ Nat.card (normIn T T₁) ^ 2 := by
      rw [← pow_mul]
      calc 2 ^ (2 * (2 * a + 1) * 2) = 2 ^ (4 * (2 * a + 1)) := by congr 1; ring
        _ ≤ _ := h
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h2

omit [Finite G] hN in
theorem comm_conj_eq (hS : Sec3 T T₁) {u : G}
    (huM : u ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G))
    (hX : ∀ x ∈ T ⊔ T₁, ⁅x, u⁆ ∈ cfgM T T₁) {x : G} (hx : x ∈ T ⊔ T₁) {m : G}
    (hm : m ∈ cfgM T T₁) :
    x * (m * u * m⁻¹ * u⁻¹) * x⁻¹ = (x * m * x⁻¹) * u * (x * m * x⁻¹)⁻¹ * u⁻¹ := by
  have hMab : ∀ m ∈ cfgM T T₁, ∀ n ∈ cfgM T T₁, m * n = n * m := fun m hm n hn =>
    elemAbelian_mul_comm hS.cfg.isElemAbelian_cfgM hm hn
  have hm' : x * m * x⁻¹ ∈ cfgM T T₁ := hS.cfg.conj_mem_cfgM hx hm
  have hc : x * u * x⁻¹ * u⁻¹ ∈ cfgM T T₁ := by
    have := hX x hx
    rwa [commutatorElement_def] at this
  have hp : u * (x * m * x⁻¹)⁻¹ * u⁻¹ ∈ cfgM T T₁ :=
    (Subgroup.mem_normalizer_iff.1 huM _).1 ((cfgM T T₁).inv_mem hm')
  have hcp := hMab _ hc _ hp
  have hxu : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
  calc x * (m * u * m⁻¹ * u⁻¹) * x⁻¹
      = (x * m * x⁻¹) * (x * u * x⁻¹) * (x * m * x⁻¹)⁻¹ * (x * u * x⁻¹)⁻¹ := by group
    _ = (x * m * x⁻¹) * ((x * u * x⁻¹ * u⁻¹) * u) * (x * m * x⁻¹)⁻¹ *
        ((x * u * x⁻¹ * u⁻¹) * u)⁻¹ := by rw [← hxu]
    _ = (x * m * x⁻¹) * ((x * u * x⁻¹ * u⁻¹) * (u * (x * m * x⁻¹)⁻¹ * u⁻¹)) *
        (x * u * x⁻¹ * u⁻¹)⁻¹ := by group
    _ = (x * m * x⁻¹) * ((u * (x * m * x⁻¹)⁻¹ * u⁻¹) * (x * u * x⁻¹ * u⁻¹)) *
        (x * u * x⁻¹ * u⁻¹)⁻¹ := by rw [hcp]
    _ = (x * m * x⁻¹) * u * (x * m * x⁻¹)⁻¹ * u⁻¹ := by group


theorem comm_of_index_le (hS : Sec3 T T₁) {a : ℕ} (ha : 1 ≤ a)
    (e : XQ ≃* Sz a) {u : G}
    (huM : u ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G))
    (hX : ∀ x ∈ T ⊔ T₁, ⁅x, u⁆ ∈ cfgM T T₁)
    (hc : Nat.card T ≤ 2 ^ (2 * a + 1) * Nat.card ↥(T ⊓ Subgroup.centralizer ({u} : Set G))) :
    ∀ m ∈ cfgM T T₁, m * u = u * m := by
  classical
  have hMab : ∀ m ∈ cfgM T T₁, ∀ n ∈ cfgM T T₁, m * n = n * m := fun m hm n hn =>
    elemAbelian_mul_comm hS.cfg.isElemAbelian_cfgM hm hn
  let φ := commHom (cfgM T T₁) hMab u huM
  let U : Subgroup G := φ.range.map (cfgM T T₁).subtype
  have hUM : U ≤ cfgM T T₁ := Subgroup.map_subtype_le _
  have hUmem : ∀ m ∈ cfgM T T₁, m * u * m⁻¹ * u⁻¹ ∈ U := fun m hm =>
    ⟨φ ⟨m, hm⟩, ⟨⟨m, hm⟩, rfl⟩, by simp [φ, commHom_apply]⟩
  have hUinv : ∀ x ∈ T ⊔ T₁, ∀ w ∈ U, x * w * x⁻¹ ∈ U := by
    rintro x hx w ⟨_, ⟨m, rfl⟩, rfl⟩
    have h1 := comm_conj_eq hS huM hX hx m.2
    have h2 := hUmem (x * m * x⁻¹) (hS.cfg.conj_mem_cfgM hx m.2)
    have h3 : x * ((φ m : ↥(cfgM T T₁)) : G) * x⁻¹ = (x * m * x⁻¹) * u * (x * m * x⁻¹)⁻¹ * u⁻¹ := by
      rw [commHom_apply]; exact h1
    simp only [Subgroup.coe_subtype]
    rw [h3]
    exact h2
  rcases eq_bot_or_le_card_of_invariant hS ha e hUM hUinv with hbot | hbig
  · intro m hm
    have h1 := hUmem m hm
    rw [hbot, Subgroup.mem_bot] at h1
    calc m * u = (m * u * m⁻¹ * u⁻¹) * (u * m) := by group
      _ = u * m := by rw [h1, one_mul]
  · exfalso
    set L := normIn T T₁ with hLdef
    set L₁ := normIn T₁ T with hL₁def
    set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hCdef
    set q : ℕ := 2 ^ (2 * a + 1) with hq
    have hLT : L ≤ T := normIn_le T T₁
    have hL₁M : L₁ ≤ cfgM T T₁ := Cfg.normIn_le_cfgM_right T T₁
    have hLM : L ≤ cfgM T T₁ := Cfg.normIn_le_cfgM_left T T₁
    have hLC : Nat.card L ≤ q * Nat.card ↥(L ⊓ C) := by
      have hC'pos : 0 < Nat.card ↥(T ⊓ C) := Nat.card_pos
      have hTrel := Subgroup.relIndex_mul_card (H := T ⊓ C) (K := T)
      rw [inf_eq_left.2 (inf_le_left : T ⊓ C ≤ T)] at hTrel
      have hrelq : (T ⊓ C).relIndex T ≤ q := by
        by_contra hlt
        push Not at hlt
        have := Nat.mul_lt_mul_of_lt_of_le hlt (le_refl (Nat.card ↥(T ⊓ C))) hC'pos
        omega
      have hrelne : (T ⊓ C).relIndex T ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hTrel
        have : 0 < Nat.card T := Nat.card_pos
        omega
      have hle := Subgroup.relIndex_le_of_le_right hLT hrelne
      have hLrel := Subgroup.relIndex_mul_card (H := T ⊓ C) (K := L)
      have hinf : T ⊓ C ⊓ L = L ⊓ C := by
        ext x
        simp only [Subgroup.mem_inf]
        constructor
        · rintro ⟨⟨_, hxC⟩, hxL⟩; exact ⟨hxL, hxC⟩
        · rintro ⟨hxL, hxC⟩; exact ⟨⟨hLT hxL, hxC⟩, hxL⟩
      rw [hinf] at hLrel
      calc Nat.card L = (T ⊓ C).relIndex L * Nat.card ↥(L ⊓ C) := hLrel.symm
        _ ≤ q * Nat.card ↥(L ⊓ C) := Nat.mul_le_mul_right _ (hle.trans hrelq)
    obtain ⟨x₀, hx₀, -, hL₁eq⟩ := exists_normIn_right_eq hS
    have hC₁ : Nat.card ↥(L ⊓ C) ≤ Nat.card ↥(L₁ ⊓ C) := by
      refine Nat.card_le_card_of_injective
        (fun m : ↥(L ⊓ C) => (⟨x₀ * (m : G) * x₀⁻¹, ?_⟩ : ↥(L₁ ⊓ C))) ?_
      · have hmem : x₀ * (m : G) * x₀⁻¹ ∈ conjSubgroup x₀ L := by
          rw [mem_conjSubgroup]
          have e : x₀⁻¹ * (x₀ * (m : G) * x₀⁻¹) * x₀ = m := by group
          rw [e]; exact m.2.1
        have hL₁eq' : L₁ = conjSubgroup x₀ L := hL₁eq
        have h₁ : x₀ * (m : G) * x₀⁻¹ ∈ L₁ := by rw [hL₁eq']; exact hmem
        have hm : (m : G) * u = u * m := Subgroup.mem_centralizer_singleton_iff.1 m.2.2
        have h1 := comm_conj_eq hS huM hX hx₀ (hLM m.2.1)
        have h2 : (m : G) * u * (m : G)⁻¹ * u⁻¹ = 1 := by rw [hm]; group
        rw [h2, mul_one, mul_inv_cancel] at h1
        have h3 : (x₀ * (m : G) * x₀⁻¹) * u * (x₀ * (m : G) * x₀⁻¹)⁻¹ * u⁻¹ = 1 := h1.symm
        refine Subgroup.mem_inf.2 ⟨h₁, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        calc x₀ * (m : G) * x₀⁻¹ * u
            = ((x₀ * (m : G) * x₀⁻¹) * u * (x₀ * (m : G) * x₀⁻¹)⁻¹ * u⁻¹) *
              (u * (x₀ * (m : G) * x₀⁻¹)) := by group
          _ = u * (x₀ * (m : G) * x₀⁻¹) := by rw [h3, one_mul]
      · intro m n h
        have := congrArg Subtype.val h
        simp only at this
        exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
    have hker : Nat.card ↥(L ⊓ C) * Nat.card ↥(L₁ ⊓ C) ≤ Nat.card φ.ker := by
      rw [← Nat.card_prod]
      refine Nat.card_le_card_of_injective
        (fun p : ↥(L ⊓ C) × ↥(L₁ ⊓ C) =>
          (⟨⟨(p.1 : G) * p.2, (cfgM T T₁).mul_mem (hLM p.1.2.1) (hL₁M p.2.2.1)⟩, ?_⟩ :
            ↥φ.ker)) ?_
      · rw [mem_ker_commHom]
        have h1 : (p.1 : G) * u = u * p.1 := Subgroup.mem_centralizer_singleton_iff.1 p.1.2.2
        have h2 : (p.2 : G) * u = u * p.2 := Subgroup.mem_centralizer_singleton_iff.1 p.2.2.2
        show (p.1 : G) * p.2 * u = u * ((p.1 : G) * p.2)
        calc (p.1 : G) * p.2 * u = (p.1 : G) * (p.2 * u) := by rw [mul_assoc]
          _ = (p.1 : G) * (u * p.2) := by rw [h2]
          _ = ((p.1 : G) * u) * p.2 := by rw [mul_assoc]
          _ = (u * p.1) * p.2 := by rw [h1]
          _ = u * ((p.1 : G) * p.2) := by rw [mul_assoc]
      · rintro ⟨⟨b, hb⟩, ⟨c, hc'⟩⟩ ⟨⟨b', hb'⟩, ⟨c', hc''⟩⟩ h
        have h1 : b * c = b' * c' := congrArg Subtype.val (congrArg Subtype.val h)
        have h2 : b'⁻¹ * b ∈ T ⊓ T₁ := by
          refine ⟨T.mul_mem (T.inv_mem (hLT hb'.1)) (hLT hb.1), ?_⟩
          have : b'⁻¹ * b = c' * c⁻¹ := by
            calc b'⁻¹ * b = b'⁻¹ * (b * c) * c⁻¹ := by group
              _ = b'⁻¹ * (b' * c') * c⁻¹ := by rw [h1]
              _ = c' * c⁻¹ := by group
          rw [this]
          exact T₁.mul_mem (normIn_le _ _ hc''.1) (T₁.inv_mem (normIn_le _ _ hc'.1))
        rw [hS.cfg.inf, Subgroup.mem_bot, inv_mul_eq_one] at h2
        subst h2
        have h3 : c = c' := mul_left_cancel h1
        subst h3
        rfl
    have hmain := Subgroup.card_ker_mul_card_range φ
    have hMc : Nat.card ↥(cfgM T T₁) = Nat.card L * Nat.card L₁ := card_cfgM_eq_mul hS.cfg
    have hL₁c : Nat.card L₁ = Nat.card L := card_normIn_right hS
    have hUc : Nat.card U = Nat.card φ.range :=
      Subgroup.card_map_of_injective (cfgM T T₁).subtype_injective
    have hnpos : 0 < Nat.card ↥(L ⊓ C) := Nat.card_pos
    have hrange : Nat.card φ.range ≤ q ^ 2 := by
      have h1 : Nat.card φ.range * (Nat.card ↥(L ⊓ C) * Nat.card ↥(L ⊓ C)) ≤
          Nat.card φ.range * Nat.card φ.ker := by
        refine Nat.mul_le_mul_left _ ?_
        exact (Nat.mul_le_mul_left _ hC₁).trans hker
      have h2 : Nat.card φ.range * Nat.card φ.ker = Nat.card L * Nat.card L := by
        rw [mul_comm, hmain, hMc, hL₁c]
      have h3 : Nat.card L * Nat.card L ≤
          (q * Nat.card ↥(L ⊓ C)) * (q * Nat.card ↥(L ⊓ C)) := Nat.mul_le_mul hLC hLC
      have h4 : Nat.card φ.range * (Nat.card ↥(L ⊓ C) * Nat.card ↥(L ⊓ C)) ≤
          q ^ 2 * (Nat.card ↥(L ⊓ C) * Nat.card ↥(L ⊓ C)) := by
        calc _ ≤ Nat.card φ.range * Nat.card φ.ker := h1
          _ = Nat.card L * Nat.card L := h2
          _ ≤ (q * Nat.card ↥(L ⊓ C)) * (q * Nat.card ↥(L ⊓ C)) := h3
          _ = q ^ 2 * (Nat.card ↥(L ⊓ C) * Nat.card ↥(L ⊓ C)) := by ring
      exact Nat.le_of_mul_le_mul_right h4 (Nat.mul_pos hnpos hnpos)
    have h5 : 2 ^ (4 * (2 * a + 1)) ≤ q ^ 2 := by
      calc 2 ^ (4 * (2 * a + 1)) ≤ Nat.card U := hbig
        _ = Nat.card φ.range := hUc
        _ ≤ q ^ 2 := hrange
    have h6 : q ^ 2 = 2 ^ (2 * (2 * a + 1)) := by
      rw [hq, ← pow_mul, mul_comm]
    rw [h6] at h5
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h5
    omega

end Trick

end CFSG.CGT.T75M
