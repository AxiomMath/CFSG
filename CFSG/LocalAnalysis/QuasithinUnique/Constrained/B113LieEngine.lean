module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CharTwoTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.QuasithinUnique.B113Lie

open CFSG.Open CFSG.QuasithinUnique

@[expose] def OvergroupsAt (X : Type*) [Group X] (U : Subgroup X) : Prop :=
  ∀ Y : Subgroup X, U ≤ Y → Y ≠ ⊤ → CharTwo Y

@[expose] def OddAutAt (X : Type*) [Group X] (U : Subgroup X) : Prop :=
  ∀ φ : MulAut X, (∀ u ∈ U, φ u = u) → Odd (orderOf φ) → φ = 1

@[expose] def SylowFacts (X : Type*) [Group X] (U : Subgroup X) : Prop :=
  IsSylowTwoOf U ⊤ ∧ OvergroupsAt X U ∧ OddAutAt X U

structure ParabolicData (X : Type*) [Group X] (U : Subgroup X) (Ps : Set (Subgroup X)) :
    Prop where
  sylow : IsSylowTwoOf U ⊤
  le : ∀ P ∈ Ps, U ≤ P ∧ P ≠ ⊤
  cover : ∀ A : Subgroup X, U ≤ A → A ≠ ⊤ → ∃ P ∈ Ps, A ≤ P
  charTwo : ∀ P ∈ Ps, CharTwo P
  gen : sSup Ps = ⊤
  inv : ∀ α : MulAut X, (∀ u ∈ U, α u = u) → Odd (orderOf α) → ∀ P ∈ Ps,
    P.map α.toMonoidHom = P

theorem aut_pow_apply {X : Type*} [Group X] {α : MulAut X} {x c : X} (hc : α c = c)
    (h : α x = x * c) (k : ℕ) : (α ^ k) x = x * c ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, h, map_pow, hc, pow_succ']
    group

section Engine

variable {X : Type*} [Group X] [Finite X] {U : Subgroup X} {Ps : Set (Subgroup X)}

omit [Finite X] in
theorem ParabolicData.pCoreOf_le (h : ParabolicData X U Ps) {P : Subgroup X} (hP : P ∈ Ps) :
    pCoreOf 2 P ≤ U :=
  EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h.sylow (h.le P hP).1)

theorem ParabolicData.overgroupsAt (h : ParabolicData X U Ps) : OvergroupsAt X U := by
  intro Y hUY hY
  obtain ⟨P, hP, hYP⟩ := h.cover Y hUY hY
  have hQU := h.pCoreOf_le hP
  have hQ2 : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hPn : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hQY : pCoreOf 2 P ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQU.trans hUY) (hYP.trans hPn) hQ2
  intro y ⟨hyY, hyC⟩
  have hyC' : y ∈ Subgroup.centralizer (pCoreOf 2 P : Set X) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hQY) hyC
  exact hQY (h.charTwo P hP ⟨hYP hyY, hyC'⟩)

theorem ParabolicData.oddAutAt (h : ParabolicData X U Ps) : OddAutAt X U := by
  intro α hα hodd
  have key : ∀ P ∈ Ps, ∀ x ∈ P, α x = x := by
    intro P hP x hx
    have hQU := h.pCoreOf_le hP
    have hQ2 : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
    have hPn : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set X) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
    have hmap := h.inv α hα hodd P hP
    have hαP : ∀ y ∈ P, α y ∈ P := fun y hy => by
      rw [← hmap]
      exact ⟨y, hy, rfl⟩
    have hcP : x⁻¹ * α x ∈ P := P.mul_mem (P.inv_mem hx) (hαP x hx)
    have hcC : x⁻¹ * α x ∈ Subgroup.centralizer (pCoreOf 2 P : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hxq : x * q * x⁻¹ ∈ pCoreOf 2 P := (Subgroup.mem_normalizer_iff.1 (hPn hx) q).1 hq
      have h1 : α (x * q * x⁻¹) = x * q * x⁻¹ := hα _ (hQU hxq)
      rw [map_mul, map_mul, map_inv, hα q (hQU hq)] at h1
      have h3 : (x⁻¹ * α x) * q * (x⁻¹ * α x)⁻¹ = q := by
        calc (x⁻¹ * α x) * q * (x⁻¹ * α x)⁻¹
            = x⁻¹ * (α x * q * (α x)⁻¹) * x := by group
          _ = x⁻¹ * (x * q * x⁻¹) * x := by rw [h1]
          _ = q := by group
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    have hcQ : x⁻¹ * α x ∈ pCoreOf 2 P := h.charTwo P hP ⟨hcP, hcC⟩
    set c := x⁻¹ * α x with hc
    have hαc : α c = c := hα c (hQU hcQ)
    have hαx : α x = x * c := by rw [hc]; group
    have hpow := aut_pow_apply hαc hαx (orderOf α)
    rw [pow_orderOf_eq_one] at hpow
    have hcn : c ^ orderOf α = 1 := by
      have : x = x * c ^ orderOf α := by simpa using hpow
      simpa using this
    obtain ⟨k, hk⟩ := hQ2 ⟨c, hcQ⟩
    have hck : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hcop : Nat.Coprime (orderOf α) (2 ^ k) := Nat.Coprime.pow_right k hodd.coprime_two_right
    have hord : orderOf c = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hcn)
        (orderOf_dvd_of_pow_eq_one hck)
    have hc1 : c = 1 := orderOf_eq_one_iff.1 hord
    rw [hαx, hc1, mul_one]
  have hfix : (⊤ : Subgroup X) ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id X) := by
    rw [← h.gen]
    exact sSup_le fun P hP x hx => key P hP x hx
  ext x
  exact hfix (Subgroup.mem_top x)

theorem ParabolicData.sylowFacts (h : ParabolicData X U Ps) : SylowFacts X U :=
  ⟨h.sylow, h.overgroupsAt, h.oddAutAt⟩

end Engine

section Coatoms

variable {X : Type*} [Group X] [Finite X]

theorem ParabolicData.of_coatoms {U : Subgroup X} {Ps : Set (Subgroup X)}
    (hU : IsSylowTwoOf U ⊤) (hU1 : U ≠ ⊥) (hX : pCoreOf 2 (⊤ : Subgroup X) = ⊥)
    (hco : ∀ P ∈ Ps, P ⋖ ⊤ ∧ U ≤ P) (htwo : ∃ P ∈ Ps, ∃ Q ∈ Ps, P ≠ Q)
    (hcover : ∀ A : Subgroup X, U ≤ A → A ≠ ⊤ → ∃ P ∈ Ps, A ≤ P)
    (hchar : ∀ P ∈ Ps, CharTwo P) : ParabolicData X U Ps where
  sylow := hU
  le P hP := ⟨(hco P hP).2, (hco P hP).1.lt.ne⟩
  cover := hcover
  charTwo := hchar
  gen := by
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := htwo
    have hsup : P ⊔ Q = ⊤ := by
      rcases (hco P hP).1.eq_or_eq (le_sup_left : P ≤ P ⊔ Q) le_top with h | h
      · have hQP : Q ≤ P := h ▸ le_sup_right
        rcases (hco Q hQ).1.eq_or_eq hQP le_top with h' | h'
        · exact absurd h' hPQ
        · exact absurd h' (hco P hP).1.lt.ne
      · exact h
    exact top_le_iff.1 (hsup ▸ sup_le (le_sSup hP) (le_sSup hQ))
  inv α hα _ P hP := by
    have hUP := (hco P hP).2
    have hRU : pCoreOf 2 P ≤ U :=
      EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le hU hUP)
    have hR2 : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
    have hPn : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set X) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
    have hR1 : pCoreOf 2 P ≠ ⊥ := by
      intro hR
      apply hU1
      refine eq_bot_iff.2 fun u hu => ?_
      have hup : u ∈ P ⊓ Subgroup.centralizer (pCoreOf 2 P : Set X) := by
        refine ⟨hUP hu, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
        rw [hR] at hq
        rw [Subgroup.mem_bot.1 hq]
        simp
      have := hchar P hP hup
      rwa [hR] at this
    have hN : Subgroup.normalizer (pCoreOf 2 P : Set X) ≠ ⊤ := by
      intro htop
      apply hR1
      have hn : ((pCoreOf 2 P).subgroupOf ⊤).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).2 htop.ge
      have := CFSG.LieType.BorelTits.le_pCoreOf 2 le_top hn hR2
      rw [hX] at this
      exact eq_bot_iff.2 this
    have hNP : Subgroup.normalizer (pCoreOf 2 P : Set X) = P := by
      rcases (hco P hP).1.eq_or_eq hPn le_top with h | h
      · exact h
      · exact absurd h hN
    have hRα : (pCoreOf 2 P).map α.toMonoidHom = pCoreOf 2 P := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [show α.toMonoidHom y = y from hα y (hRU hy)]
        exact hy
      · intro hx
        exact ⟨x, hx, hα x (hRU hx)⟩
    conv_lhs => rw [← hNP]
    rw [Subgroup.map_equiv_normalizer_eq, hRα, hNP]

end Coatoms

theorem map_eq_of_fixes {X : Type*} [Group X] {U : Subgroup X} {α : MulAut X}
    (h : ∀ u ∈ U, α u = u) : U.map α.toMonoidHom = U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [show α.toMonoidHom y = y from h y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, h x hx⟩

section Pair

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem ParabolicData.of_pair {U P₀ P₁ : Subgroup Y} (hU : IsSylowTwoOf U ⊤)
    (hUP₀ : U ≤ P₀) (hUP₁ : U ≤ P₁) (h₀ : P₀ ≠ ⊤) (h₁ : P₁ ≠ ⊤) (hgen : P₀ ⊔ P₁ = ⊤)
    (hcover : ∀ A : Subgroup Y, U ≤ A → A ≠ ⊤ → A ≤ P₀ ∨ A ≤ P₁)
    (hc₀ : CharTwo P₀) (hc₁ : CharTwo P₁)
    (hinv : ∀ α : MulAut Y, U.map α.toMonoidHom = U →
      P₀.map α.toMonoidHom = P₀ ∧ P₁.map α.toMonoidHom = P₁) :
    ParabolicData Y U {P₀, P₁} where
  sylow := hU
  le P hP := by
    rcases hP with rfl | rfl
    · exact ⟨hUP₀, h₀⟩
    · exact ⟨hUP₁, h₁⟩
  cover A hUA hA := by
    rcases hcover A hUA hA with h | h
    · exact ⟨P₀, Or.inl rfl, h⟩
    · exact ⟨P₁, Or.inr rfl, h⟩
  charTwo P hP := by
    rcases hP with rfl | rfl
    · exact hc₀
    · exact hc₁
  gen := by rw [sSup_pair, hgen]
  inv α hα _ P hP := by
    obtain ⟨h0, h1⟩ := hinv α (map_eq_of_fixes hα)
    rcases hP with rfl | rfl
    · exact h0
    · exact h1

end Pair

section Ambient

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem cover_subgroupOf {Γ U P₀ P₁ : Subgroup M} (hUΓ : U ≤ Γ)
    (hcont : ∀ A : Subgroup M, U ≤ A → A ≤ Γ → A ≠ Γ → A ≤ P₀ ∨ A ≤ P₁) :
    ∀ A : Subgroup ↥Γ, U.subgroupOf Γ ≤ A → A ≠ ⊤ → A ≤ P₀.subgroupOf Γ ∨ A ≤ P₁.subgroupOf Γ := by
  intro A hUA hA
  have hUA' : U ≤ A.map Γ.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hUΓ]
    exact Subgroup.map_mono hUA
  have hAΓ : A.map Γ.subtype ≤ Γ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hAne : A.map Γ.subtype ≠ Γ := by
    intro h
    apply hA
    apply Subgroup.map_injective Γ.subtype_injective
    rw [h, Subgroup.map_top, Subgroup.range_subtype]
  rcases hcont _ hUA' hAΓ hAne with h | h
  · exact Or.inl (Subgroup.map_le_iff_le_comap.1 h)
  · exact Or.inr (Subgroup.map_le_iff_le_comap.1 h)

theorem ParabolicData.of_ambient_pair {Γ U P₀ P₁ : Subgroup M} (hU : IsSylowTwoOf U Γ)
    (hUP₀ : U ≤ P₀) (hUP₁ : U ≤ P₁) (hP₀ : P₀ ≤ Γ) (hP₁ : P₁ ≤ Γ) (h₀ : P₀ ≠ Γ) (h₁ : P₁ ≠ Γ)
    (hgen : P₀ ⊔ P₁ = Γ)
    (hcont : ∀ A : Subgroup M, U ≤ A → A ≤ Γ → A ≠ Γ → A ≤ P₀ ∨ A ≤ P₁)
    (hc₀ : CharTwo (P₀.subgroupOf Γ)) (hc₁ : CharTwo (P₁.subgroupOf Γ))
    (hinv : ∀ α : MulAut ↥Γ, (U.subgroupOf Γ).map α.toMonoidHom = U.subgroupOf Γ →
      (P₀.subgroupOf Γ).map α.toMonoidHom = P₀.subgroupOf Γ ∧
        (P₁.subgroupOf Γ).map α.toMonoidHom = P₁.subgroupOf Γ) :
    ParabolicData ↥Γ (U.subgroupOf Γ) {P₀.subgroupOf Γ, P₁.subgroupOf Γ} := by
  have hne : ∀ {Q : Subgroup M}, Q ≤ Γ → Q ≠ Γ → Q.subgroupOf Γ ≠ ⊤ := fun hQ hQne h =>
    hQne (le_antisymm hQ (Subgroup.subgroupOf_eq_top.1 h))
  refine ParabolicData.of_pair (Setup.X6.isSylowTwoOf_subgroupOf_top hU)
    (Subgroup.subgroupOf_mono Γ hUP₀) (Subgroup.subgroupOf_mono Γ hUP₁) (hne hP₀ h₀)
    (hne hP₁ h₁) ?_ (cover_subgroupOf hU.1 hcont) hc₀ hc₁ hinv
  apply Subgroup.map_injective Γ.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hP₀,
    Subgroup.map_subgroupOf_eq_of_le hP₁, hgen, Subgroup.map_top, Subgroup.range_subtype]

end Ambient

section Transport

variable {X X' : Type*} [Group X] [Group X']

theorem map_symm_map' (e : X ≃* X') (Y : Subgroup X') :
    (Y.map e.symm.toMonoidHom).map e.toMonoidHom = Y := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩

theorem map_ne_top (e : X ≃* X') {Y : Subgroup X} (hY : Y ≠ ⊤) : Y.map e.toMonoidHom ≠ ⊤ := by
  intro h
  apply hY
  have := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rwa [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X by
    ext x; simp, Subgroup.map_id, Subgroup.map_top_of_surjective _ e.symm.surjective] at this

theorem OvergroupsAt.map (e : X ≃* X') {U : Subgroup X} (h : OvergroupsAt X U) :
    OvergroupsAt X' (U.map e.toMonoidHom) := by
  intro Y hUY hY
  have hUY' : U ≤ Y.map e.symm.toMonoidHom := by
    intro u hu
    exact ⟨e u, hUY ⟨u, hu, rfl⟩, by simp⟩
  have := Ch1.charTwo_map_mulEquiv e (h _ hUY' (map_ne_top e.symm hY))
  rwa [map_symm_map'] at this

theorem OddAutAt.map (e : X ≃* X') {U : Subgroup X} (h : OddAutAt X U) :
    OddAutAt X' (U.map e.toMonoidHom) := by
  intro φ' hφ' hodd
  have hord : orderOf (MulAut.congr e.symm φ') = orderOf φ' :=
    MulEquiv.orderOf_eq (MulAut.congr e.symm) φ'
  have h1 : MulAut.congr e.symm φ' = 1 := by
    refine h _ (fun u hu => ?_) (hord ▸ hodd)
    have := hφ' (e u) ⟨u, hu, rfl⟩
    simp [MulAut.congr_apply, this]
  ext x'
  have := congrArg (fun ψ : MulAut X => e (ψ (e.symm x'))) h1
  simpa [MulAut.congr_apply] using this

variable [Finite X] [Finite X']

theorem isSylowTwoOf_map_top (e : X ≃* X') {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := by
  have := Setup.X6.isSylowOf_map_injective (p := 2) e.toMonoidHom e.injective
    (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU)
  rw [Subgroup.map_top_of_surjective _ e.surjective] at this
  exact Setup.X6.isSylowTwoOf_iff_isSylowOf.2 this

theorem SylowFacts.map (e : X ≃* X') {U : Subgroup X} (h : SylowFacts X U) :
    SylowFacts X' (U.map e.toMonoidHom) :=
  ⟨isSylowTwoOf_map_top e h.1, h.2.1.map e, h.2.2.map e⟩

end Transport

theorem SylowFacts.of_isSylow {X : Type*} [Group X] [Finite X] {U₀ U : Subgroup X}
    (h₀ : SylowFacts X U₀) (hU : IsSylowTwoOf U ⊤) : SylowFacts X U := by
  obtain ⟨k, -, hk⟩ := (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 h₀.1).exists_mem_conj
    (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have := h₀.map (MulAut.conj k)
  rwa [hconj] at this

theorem SylowFacts.of_mulEquiv_isSylow {X X' : Type*} [Group X] [Group X'] [Finite X] [Finite X']
    (e : X ≃* X') {U' : Subgroup X'} (h : SylowFacts X' U') {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) : SylowFacts X U :=
  SylowFacts.of_isSylow (h.map e.symm) hU

theorem isSylowTwoOf_top_of_sylow {X : Type*} [Group X] [Finite X] (P : Sylow 2 X) :
    IsSylowTwoOf (P : Subgroup X) ⊤ :=
  ⟨le_top, P.isPGroup', by
    rw [show ((P : Subgroup X).subgroupOf ⊤).index = (P : Subgroup X).index from
      Subgroup.relIndex_top_right _]
    exact P.not_dvd_index⟩

theorem overgroups_of_forall_sylowFacts {X : Type*} [Group X]
    (h : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → SylowFacts X T) :
    ∀ T Y : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ Y → Y ≠ ⊤ → CharTwo Y :=
  fun T Y hT hTY hY => (h T hT).2.1 Y hTY hY

theorem oddAut_of_forall_sylowFacts {X : Type*} [Group X] [Finite X]
    (h : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → SylowFacts X T) :
    ∀ (P : Sylow 2 X) (α : MulAut X), Odd (orderOf α) → (∀ t ∈ (P : Subgroup X), α t = t) →
      α = 1 :=
  fun P α hodd hfix => (h P (isSylowTwoOf_top_of_sylow P)).2.2 α hfix hodd

theorem map_one_aut {X : Type*} [Group X] (P : Subgroup X) :
    P.map (1 : MulAut X).toMonoidHom = P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem map_eq_self_of_odd_of_pair {X : Type*} [Group X] {α : MulAut X} (hodd : Odd (orderOf α))
    {P Q : Subgroup X} (hPQ : P ≠ Q)
    (hP : P.map α.toMonoidHom = P ∨ P.map α.toMonoidHom = Q)
    (hQ : Q.map α.toMonoidHom = P ∨ Q.map α.toMonoidHom = Q) :
    P.map α.toMonoidHom = P ∧ Q.map α.toMonoidHom = Q := by
  have hinj : ∀ A B : Subgroup X, A.map α.toMonoidHom = B.map α.toMonoidHom → A = B :=
    fun A B h => Subgroup.map_injective α.injective h
  have hmapα : ∀ (A : Subgroup X) (k : ℕ),
      A.map (α ^ (k + 1)).toMonoidHom = (A.map (α ^ k).toMonoidHom).map α.toMonoidHom := by
    intro A k
    rw [Subgroup.map_map, pow_succ']
    rfl
  by_contra hcon
  have hswap : P.map α.toMonoidHom = Q ∧ Q.map α.toMonoidHom = P := by
    rcases hP with hP | hP
    · rcases hQ with hQ | hQ
      · exact absurd (hinj _ _ (hP.trans hQ.symm)) hPQ
      · exact absurd ⟨hP, hQ⟩ hcon
    · rcases hQ with hQ | hQ
      · exact ⟨hP, hQ⟩
      · exact absurd (hinj _ _ (hP.trans hQ.symm)) hPQ
  have hpow : ∀ k : ℕ, P.map (α ^ (2 * k)).toMonoidHom = P := by
    intro k
    induction k with
    | zero => simpa using map_one_aut P
    | succ k ih =>
      have h1 : P.map (α ^ (2 * k + 1)).toMonoidHom = Q := by
        rw [hmapα, ih, hswap.1]
      have h2 : P.map (α ^ (2 * k + 1 + 1)).toMonoidHom = P := by
        rw [hmapα, h1, hswap.2]
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      exact h2
  obtain ⟨m, hm⟩ := hodd
  have h3 : P.map (α ^ orderOf α).toMonoidHom = P := by
    rw [pow_orderOf_eq_one]
    exact map_one_aut P
  have h4 : P.map (α ^ orderOf α).toMonoidHom = Q := by
    rw [hm, hmapα, hpow, hswap.1]
  exact hPQ (h3.symm.trans h4)

end CFSG.QuasithinUnique.B113Lie
