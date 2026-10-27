module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LE25Shape
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LModA
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LHom

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open

section GL4

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

theorem gl4_inv_or_triv (hV : finrank (ZMod 2) V = 4) {a g : V ≃ₗ[ZMod 2] V} (ha5 : a ^ 5 = 1)
    (hfix : ∀ v : V, a v = v → v = 0) (hg : g * g = 1) {k : ℕ} (hk : g * a * g⁻¹ = a ^ k) :
    g = 1 ∨ g * a * g⁻¹ = a⁻¹ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have ha1 : a ≠ 1 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hfix v (by rw [h]; rfl))
  have hord : orderOf a = 5 := orderOf_eq_prime ha5 ha1
  have hkk : a ^ (k * k) = a := by
    have h2 : g * a ^ k * g⁻¹ = a := by
      calc g * a ^ k * g⁻¹ = g * (g * a * g⁻¹) * g⁻¹ := by rw [hk]
        _ = (g * g) * a * (g * g)⁻¹ := by group
        _ = a := by rw [hg]; simp
    calc a ^ (k * k) = (a ^ k) ^ k := pow_mul a k k
      _ = (g * a * g⁻¹) ^ k := by rw [hk]
      _ = g * a ^ k * g⁻¹ := conj_pow
      _ = a := h2
  have hmod : k * k ≡ 1 [MOD 5] := by
    have := (pow_eq_pow_iff_modEq (x := a)).mp (hkk.trans (pow_one a).symm)
    rwa [hord] at this
  have hr : k % 5 = 1 ∨ k % 5 = 4 := by
    have h1 : (k * k) % 5 = 1 := hmod
    have h3 : (k * k) % 5 = ((k % 5) * (k % 5)) % 5 := Nat.mul_mod _ _ _
    have h2 : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases hh : k % 5 <;> omega
  have hak : a ^ k = a ^ (k % 5) := by rw [← hord, pow_mod_orderOf]
  rcases hr with h1 | h4
  · left
    rw [hak, h1, pow_one] at hk
    have hag : a * g = g * a := by
      calc a * g = (g * a * g⁻¹) * g := by rw [hk]
        _ = g * a := by group
    have htriv := commuting_two_elt_trivial (U := ⊤) ha5 hag (by rw [finrank_top, hV])
      (fun u _ => Submodule.mem_top) (fun u _ => Submodule.mem_top) (fun u _ hu => hfix u hu)
      (k := 1) (by rw [pow_one, sq]; exact hg)
    exact LinearEquiv.ext fun v => htriv v Submodule.mem_top
  · right
    rw [hak, h4] at hk
    rw [hk]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact ha5)

theorem gl4_prod_triv (hV : finrank (ZMod 2) V = 4) {a g g' : V ≃ₗ[ZMod 2] V} (ha5 : a ^ 5 = 1)
    (hfix : ∀ v : V, a v = v → v = 0) (hgg : (g * g') * (g * g') = 1)
    (hd : g = 1 ∨ g * a * g⁻¹ = a⁻¹) (hd' : g' = 1 ∨ g' * a * g'⁻¹ = a⁻¹) (hg1 : g ≠ 1)
    (hg1' : g' ≠ 1) : g * g' = 1 := by
  have hi : g * a * g⁻¹ = a⁻¹ := hd.resolve_left hg1
  have hi' : g' * a * g'⁻¹ = a⁻¹ := hd'.resolve_left hg1'
  have hc : (g * g') * a * (g * g')⁻¹ = a := by
    calc (g * g') * a * (g * g')⁻¹ = g * (g' * a * g'⁻¹) * g⁻¹ := by group
      _ = g * a⁻¹ * g⁻¹ := by rw [hi']
      _ = (g * a * g⁻¹)⁻¹ := by group
      _ = a := by rw [hi, inv_inv]
  have hag : a * (g * g') = (g * g') * a := by
    calc a * (g * g') = ((g * g') * a * (g * g')⁻¹) * (g * g') := by rw [hc]
      _ = (g * g') * a := by group
  have htriv := commuting_two_elt_trivial (U := ⊤) ha5 hag (by rw [finrank_top, hV])
    (fun u _ => Submodule.mem_top) (fun u _ => Submodule.mem_top) (fun u _ hu => hfix u hu)
    (k := 1) (by rw [pow_one, sq]; exact hgg)
  exact LinearEquiv.ext fun v => htriv v Submodule.mem_top

end GL4

section E25

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : Type*} [Group B]
  {ρ : B →* (V ≃ₗ[ZMod 2] V)} {x t z h : B}

theorem e25_dichotomy (H : HypM ρ x t z h) {M : Submodule (ZMod 2) V}
    (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ Jbar ρ x, Stable g M)
    (hpow : ∀ g ∈ Jbar ρ x, ∃ k : ℕ, ∀ v ∈ M, g v = (ρ x) ^ k • v) {s : B}
    (hs2 : ρ s * ρ s = 1) (hs : ρ s ∈ modA_stab M) :
    modA_restr M ⟨ρ s, hs⟩ = 1 ∨
      modA_restr M ⟨ρ s, hs⟩ * modA_resJ (Jbar ρ x) M sM ⟨ρ x, E25_rho_mem_Jbar ρ x⟩ *
        (modA_restr M ⟨ρ s, hs⟩)⁻¹ =
      (modA_resJ (Jbar ρ x) M sM ⟨ρ x, E25_rho_mem_Jbar ρ x⟩)⁻¹ := by
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [H.dim]; norm_num)
  set a₁ : M ≃ₗ[ZMod 2] M := modA_resJ (Jbar ρ x) M sM ⟨ρ x, E25_rho_mem_Jbar ρ x⟩ with ha₁
  set g₁ : M ≃ₗ[ZMod 2] M := modA_restr M ⟨ρ s, hs⟩ with hg₁
  have hinv : (ρ s)⁻¹ = ρ s := inv_eq_of_mul_eq_one_right hs2
  have hx5 : ρ x ^ 5 = 1 := by rw [← H.ord_x]; exact pow_orderOf_eq_one _
  have ha5 : a₁ ^ 5 = 1 := by
    have : (⟨ρ x, E25_rho_mem_Jbar ρ x⟩ : Jbar ρ x) ^ 5 = 1 := Subtype.ext hx5
    rw [ha₁, ← map_pow, this, map_one]
  have hfix : ∀ w : M, a₁ w = w → w = 0 := fun w hw =>
    Subtype.ext (H.fix w (congrArg Subtype.val hw))
  have hg2 : g₁ * g₁ = 1 := by
    have : (⟨ρ s, hs⟩ : modA_stab M) * ⟨ρ s, hs⟩ = 1 := Subtype.ext hs2
    rw [hg₁, ← map_mul, this, map_one]
  have hg' : ρ s * ρ x * ρ s ∈ Jbar ρ x := by
    have h1 := E25_Jbar_conj ρ x s (E25_rho_mem_Jbar ρ x)
    rwa [hinv] at h1
  obtain ⟨k, hk⟩ := hpow _ hg'
  have hpowk : ∀ (n : ℕ) (w : M), ((a₁ ^ n) w : V) = ((ρ x) ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ]
      exact ih (a₁ w)
  have hk' : g₁ * a₁ * g₁⁻¹ = a₁ ^ k := by
    rw [inv_eq_of_mul_eq_one_right hg2]
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [hpowk k w]
    exact hk w w.2
  exact gl4_inv_or_triv hM ha5 hfix hg2 hk'

theorem e25_summand_facts (H : HypM ρ x t z h) {M : Submodule (ZMod 2) V}
    (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ Jbar ρ x, Stable g M)
    (hpow : ∀ g ∈ Jbar ρ x, ∃ k : ℕ, ∀ v ∈ M, g v = (ρ x) ^ k • v) {s : B}
    (hs2 : ρ s * ρ s = 1) (hs : ρ s ∈ modA_stab M) :
    (rk (modA_restr M ⟨ρ s, hs⟩) = 0 ∨ rk (modA_restr M ⟨ρ s, hs⟩) = 2) ∧
      (rk (modA_restr M ⟨ρ s, hs⟩) = 0 ↔ ∀ v ∈ M, ρ s v = v) := by
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [H.dim]; norm_num)
  refine ⟨modA_E25_rk_summand H hM sM hpow hs2 hs, ⟨fun h0 v hv => ?_, fun hv => ?_⟩⟩
  · have h1 := modA_eq_one_of_rk_zero h0
    exact congrArg (fun f : M ≃ₗ[ZMod 2] M => ((f ⟨v, hv⟩ : M) : V)) h1
  · have : modA_restr M ⟨ρ s, hs⟩ = 1 :=
      LinearEquiv.ext fun u => Subtype.ext (hv u u.2)
    rw [this, modA_rk_one]

theorem e25_prod_triv (H : HypM ρ x t z h) {M : Submodule (ZMod 2) V}
    (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ Jbar ρ x, Stable g M)
    (hpow : ∀ g ∈ Jbar ρ x, ∃ k : ℕ, ∀ v ∈ M, g v = (ρ x) ^ k • v) {s s' : B}
    (hs2 : ρ s * ρ s = 1) (hs2' : ρ s' * ρ s' = 1) (hss : ρ (s * s') * ρ (s * s') = 1)
    (hs : ρ s ∈ modA_stab M) (hs' : ρ s' ∈ modA_stab M)
    (hT : ¬ ∀ v ∈ M, ρ s v = v) (hT' : ¬ ∀ v ∈ M, ρ s' v = v) :
    ∀ v ∈ M, ρ (s * s') v = v := by
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [H.dim]; norm_num)
  set a₁ : M ≃ₗ[ZMod 2] M := modA_resJ (Jbar ρ x) M sM ⟨ρ x, E25_rho_mem_Jbar ρ x⟩ with ha₁
  have hx5 : ρ x ^ 5 = 1 := by rw [← H.ord_x]; exact pow_orderOf_eq_one _
  have ha5 : a₁ ^ 5 = 1 := by
    have : (⟨ρ x, E25_rho_mem_Jbar ρ x⟩ : Jbar ρ x) ^ 5 = 1 := Subtype.ext hx5
    rw [ha₁, ← map_pow, this, map_one]
  have hfix : ∀ w : M, a₁ w = w → w = 0 := fun w hw =>
    Subtype.ext (H.fix w (congrArg Subtype.val hw))
  have hmul : (ρ (s * s') ∈ modA_stab M) := by rw [map_mul]; exact mul_mem hs hs'
  have hr : modA_restr M ⟨ρ (s * s'), hmul⟩ =
      modA_restr M ⟨ρ s, hs⟩ * modA_restr M ⟨ρ s', hs'⟩ := by
    rw [← map_mul]
    exact congrArg _ (Subtype.ext (map_mul ρ s s'))
  have hne : ∀ {r : B} (hr2 : ρ r * ρ r = 1) (hrM : ρ r ∈ modA_stab M),
      (¬ ∀ v ∈ M, ρ r v = v) → modA_restr M ⟨ρ r, hrM⟩ ≠ 1 := by
    intro r _ hrM hT1 h1
    apply hT1
    intro v hv
    exact congrArg (fun f : M ≃ₗ[ZMod 2] M => ((f ⟨v, hv⟩ : M) : V)) h1
  have hsq : ∀ {r : B} (hr2 : ρ r * ρ r = 1) (hrM : ρ r ∈ modA_stab M),
      modA_restr M ⟨ρ r, hrM⟩ * modA_restr M ⟨ρ r, hrM⟩ = 1 := by
    intro r hr2 hrM
    rw [← map_mul]
    have : (⟨ρ r, hrM⟩ : modA_stab M) * ⟨ρ r, hrM⟩ = 1 := Subtype.ext hr2
    rw [this, map_one]
  have hd := e25_dichotomy H hM sM hpow hs2 hs
  have hd' := e25_dichotomy H hM sM hpow hs2' hs'
  have hgg : (modA_restr M ⟨ρ s, hs⟩ * modA_restr M ⟨ρ s', hs'⟩) *
      (modA_restr M ⟨ρ s, hs⟩ * modA_restr M ⟨ρ s', hs'⟩) = 1 := by
    rw [← hr]
    exact hsq hss hmul
  haveI : Module.Finite (ZMod 2) M := inferInstance
  have h1 := gl4_prod_triv hM ha5 hfix hgg hd hd' (hne hs2 hs hT) (hne hs2' hs' hT')
  rw [← hr] at h1
  intro v hv
  exact congrArg (fun f : M ≃ₗ[ZMod 2] M => ((f ⟨v, hv⟩ : M) : V)) h1

end E25

section Abelian

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem e25_irred_restr {O' : Subgroup (V ≃ₗ[ZMod 2] V)} {M : Submodule (ZMod 2) V}
    (sM : ∀ g ∈ O', Stable g M)
    (hirr : ∀ N : Submodule (ZMod 2) V, N ≤ M → (∀ g ∈ O', Stable g N) → N = ⊥ ∨ N = M) :
    ∀ U : Submodule (ZMod 2) M, (∀ g ∈ (modA_resJ O' M sM).range, Stable g U) →
      U = ⊥ ∨ U = ⊤ := by
  intro U hU
  have hN : ∀ g ∈ O', Stable g (U.map M.subtype) := by
    intro g hg v hv
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨modA_resJ O' M sM ⟨g, hg⟩ u, hU _ ⟨⟨g, hg⟩, rfl⟩ u hu, ?_⟩
    rfl
  have hle : U.map M.subtype ≤ M := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  rcases hirr _ hle hN with h | h
  · left
    exact Submodule.map_injective_of_injective M.injective_subtype (by rw [h, Submodule.map_bot])
  · right
    refine Submodule.map_injective_of_injective M.injective_subtype ?_
    rw [h, Submodule.map_top, Submodule.range_subtype]

theorem e25_odd_card_sup {H : Type*} [Group H] [Finite H] {A B : Subgroup H}
    (hA : A.Normal) (hB : B.Normal) (hAo : Odd (Nat.card A)) (hBo : Odd (Nat.card B)) :
    Odd (Nat.card (A ⊔ B : Subgroup H)) := by
  have : A.Normal := hA
  have : B.Normal := hB
  have hindexOdd : Odd (A.relIndex (A ⊔ B)) := by
    rw [Subgroup.relIndex_sup_left]
    exact hBo.of_dvd_nat (A.relIndex_dvd_card B)
  have hwithin : Nat.card (A.subgroupOf (A ⊔ B)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show A ≤ A ⊔ B from le_sup_left)).toEquiv
  have hproduct := (A.subgroupOf (A ⊔ B)).index_mul_card
  have hindex : (A.subgroupOf (A ⊔ B)).index = A.relIndex (A ⊔ B) := rfl
  rw [hindex, hwithin] at hproduct
  rw [← hproduct]
  exact hindexOdd.mul hAo

theorem e25_odd_card_oddCore {H : Type*} [Group H] [Finite H] :
    Odd (Nat.card (standardComponentOddCore H)) := by
  classical
  have hbot : (⊥ : Subgroup H).Normal ∧ Odd (Nat.card (⊥ : Subgroup H)) :=
    ⟨inferInstance, by rw [Subgroup.card_bot]; decide⟩
  obtain ⟨M, -, hM⟩ := Finite.exists_le_maximal (α := Subgroup H)
    (p := fun N => N.Normal ∧ Odd (Nat.card N)) hbot
  have hle : ∀ N : Subgroup H, N.Normal → Odd (Nat.card N) → N ≤ M := by
    intro N hN hNo
    have : M.Normal := hM.prop.1
    have : N.Normal := hN
    have hsup := e25_odd_card_sup hM.prop.1 hN hM.prop.2 hNo
    have heq := hM.eq_of_le ⟨inferInstance, hsup⟩ le_sup_left
    exact heq ▸ le_sup_right
  have hEq : standardComponentOddCore H = M :=
    le_antisymm (sSup_le fun N hN => hle N hN.1 hN.2) (le_sSup hM.prop)
  rw [hEq]
  exact hM.prop.2

theorem e25_abelian {Y : Type*} [Group Y] [Finite Y] {ρ : Y →* (V ≃ₗ[ZMod 2] V)}
    {t u x h : Y} (H : HypYW ρ t u x h) (hxO : x ∈ standardComponentOddCore Y) :
    ∀ a ∈ Jbar ρ x, ∀ b ∈ Jbar ρ x, a * b = b * a := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [H.dim]; norm_num)
  have hx5 : ρ x ^ 5 = 1 := by
    rw [← map_pow, show x ^ 5 = 1 by rw [← H.ord_x]; exact pow_orderOf_eq_one x, map_one]
  set O' : Subgroup (V ≃ₗ[ZMod 2] V) := (standardComponentOddCore Y).map ρ with hO'
  have hodd : Odd (Nat.card O') := by
    have h1 : Nat.card O' = Nat.card (standardComponentOddCore Y) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective _ ρ H.inj).toEquiv).symm
    rw [h1]
    exact e25_odd_card_oddCore
  have hρx : ρ x ∈ O' := Subgroup.mem_map_of_mem _ hxO
  have hJO : Jbar ρ x ≤ O' := by
    unfold Jbar
    exact Subgroup.map_mono (Subgroup.normalClosure_le_normal (by simpa using hxO))
  suffices hab : ∀ a ∈ O', ∀ b ∈ O', a * b = b * a from fun a ha b hb => hab a (hJO ha) b (hJO hb)
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [H.dim]; norm_num)
  have hex : ∃ n, ∃ M : Submodule (ZMod 2) V, (∀ g ∈ O', Stable g M) ∧ M ≠ ⊥ ∧
      finrank (ZMod 2) M = n :=
    ⟨_, ⊤, fun g _ u _ => Submodule.mem_top, top_ne_bot, rfl⟩
  obtain ⟨M, sM, hMne, hMn⟩ := Nat.find_spec hex
  have hmin : ∀ N : Submodule (ZMod 2) V, (∀ g ∈ O', Stable g N) → N ≠ ⊥ →
      finrank (ZMod 2) M ≤ finrank (ZMod 2) N := fun N hN hNne => by
    rw [hMn]
    exact Nat.find_min' hex ⟨N, hN, hNne, rfl⟩
  have hirrM : ∀ N : Submodule (ZMod 2) V, N ≤ M → (∀ g ∈ O', Stable g N) → N = ⊥ ∨ N = M := by
    intro N hNM hN
    by_cases hNb : N = ⊥
    · exact Or.inl hNb
    · exact Or.inr (Submodule.eq_of_le_of_finrank_le hNM (hmin N hN hNb))
  have hfixU : ∀ U : Submodule (ZMod 2) V, (∀ g ∈ O', Stable g U) →
      4 ∣ finrank (ZMod 2) U :=
    fun U hU => four_dvd_finrank_of_stable hx5 (hU _ hρx) (fun u _ hu => H.fix u hu)
  have hdM := hfixU M sM
  have hpos : 0 < finrank (ZMod 2) M :=
    Nat.pos_of_ne_zero fun h0 => hMne (Submodule.finrank_eq_zero.1 h0)
  have hle8 : finrank (ZMod 2) M ≤ 8 := by
    rw [← H.dim]
    exact Submodule.finrank_le M
  have h48 : finrank (ZMod 2) M = 4 ∨ finrank (ZMod 2) M = 8 := by
    obtain ⟨k, hk⟩ := hdM
    omega
  rcases h48 with h4 | h8
  ·
    obtain ⟨M', hc, sM'⟩ := exists_stable_complement O' hodd M sM
    have hd' : finrank (ZMod 2) M' = 4 := by
      have := Submodule.finrank_add_eq_of_isCompl hc
      rw [H.dim, h4] at this
      omega
    have hirrM' : ∀ N : Submodule (ZMod 2) V, N ≤ M' → (∀ g ∈ O', Stable g N) →
        N = ⊥ ∨ N = M' := by
      intro N hNM hN
      by_cases hNb : N = ⊥
      · exact Or.inl hNb
      · right
        refine Submodule.eq_of_le_of_finrank_le hNM ?_
        have h4N := hfixU N hN
        have hpN : 0 < finrank (ZMod 2) N :=
          Nat.pos_of_ne_zero fun h0 => hNb (Submodule.finrank_eq_zero.1 h0)
        rw [hd']
        obtain ⟨k, hk⟩ := h4N
        omega
    have cyc : ∀ (P : Submodule (ZMod 2) V) (sP : ∀ g ∈ O', Stable g P),
        finrank (ZMod 2) P = 4 →
        (∀ N : Submodule (ZMod 2) V, N ≤ P → (∀ g ∈ O', Stable g N) → N = ⊥ ∨ N = P) →
        IsCyclic (modA_resJ O' P sP).range := by
      intro P sP hP hirr
      have hodd' : Odd (Nat.card (modA_resJ O' P sP).range) :=
        Odd.of_dvd_nat hodd (Subgroup.card_range_dvd _)
      exact isCyclic_of_irreducible_odd (modA_resJ O' P sP).range hodd' (j := 2)
        (by rw [hP]; norm_num) (e25_irred_restr sP hirr)
    have c₁ := cyc M sM h4 hirrM
    have c₂ := cyc M' sM' hd' hirrM'
    intro a ha b hb
    have hcomm : ∀ (P : Submodule (ZMod 2) V) (sP : ∀ g ∈ O', Stable g P),
        IsCyclic (modA_resJ O' P sP).range → ∀ v ∈ P, a (b v) = b (a v) := by
      intro P sP hcyc v hv
      haveI := hcyc
      letI : CommGroup (modA_resJ O' P sP).range := IsCyclic.commGroup
      have := mul_comm (⟨modA_resJ O' P sP ⟨a, ha⟩, ⟨_, rfl⟩⟩ : (modA_resJ O' P sP).range)
        ⟨modA_resJ O' P sP ⟨b, hb⟩, ⟨_, rfl⟩⟩
      exact congrArg (fun f : (modA_resJ O' P sP).range => ((f.1 ⟨v, hv⟩ : P) : V)) this
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨m, hm, m', hm', rfl⟩ := Submodule.mem_sup.1
      (hc.sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)))
    simp only [LinearEquiv.mul_apply, map_add]
    rw [hcomm M sM c₁ m hm, hcomm M' sM' c₂ m' hm']
  ·
    have hirrV : ∀ U : Submodule (ZMod 2) V, (∀ g ∈ O', Stable g U) → U = ⊥ ∨ U = ⊤ := by
      intro U hU
      by_cases hUb : U = ⊥
      · exact Or.inl hUb
      · refine Or.inr (Submodule.eq_top_of_finrank_eq ?_)
        have := hmin U hU hUb
        rw [h8] at this
        have h2 : finrank (ZMod 2) U ≤ 8 := by
          rw [← H.dim]
          exact Submodule.finrank_le U
        rw [H.dim]
        omega
    have hcyc := isCyclic_of_irreducible_odd O' hodd (j := 3) (by rw [H.dim]; norm_num) hirrV
    intro a ha b hb
    haveI := hcyc
    letI : CommGroup O' := IsCyclic.commGroup
    have := mul_comm (⟨a, ha⟩ : O') ⟨b, hb⟩
    exact congrArg Subtype.val this

end Abelian

section Ranks

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Type*} [Group Y] [Finite Y]
  {ρ : Y →* (V ≃ₗ[ZMod 2] V)} {t u x h : Y}

theorem e25_ranks (H : HypYW ρ t u x h) (hsh : E25Shape ρ x t) :
    (∀ j : Y, j * j = 1 → j ≠ 1 → 2 ≤ rk (ρ j)) ∧
    (∀ F : Subgroup Y, (∀ f ∈ F, f * f = 1) → Nat.card F = 4 →
      ∃ j ∈ F, j ≠ 1 ∧ 4 ≤ rk (ρ j)) := by
  have HM := H.toHypM
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [H.dim]; norm_num)
  obtain ⟨-, V₁, V₂, hd₁, hc, hV₂, hst, hperm, hact, -⟩ := hsh
  have hd₂ : finrank (ZMod 2) V₂ = 4 := by
    rw [hV₂]
    exact (LinearEquiv.finrank_map_eq (ρ t) V₁).trans hd₁
  have sV₁ : ∀ g ∈ Jbar ρ x, Stable g V₁ := fun g hg => (hst g hg).1
  have sV₂ : ∀ g ∈ Jbar ρ x, Stable g V₂ := fun g hg => (hst g hg).2
  have hp₁ : ∀ g ∈ Jbar ρ x, ∃ k : ℕ, ∀ v ∈ V₁, g v = (ρ x) ^ k • v := fun g hg => (hact g hg).1
  have hp₂ : ∀ g ∈ Jbar ρ x, ∃ k : ℕ, ∀ v ∈ V₂, g v = (ρ x) ^ k • v := fun g hg => (hact g hg).2
  have hinv2 : ∀ j : Y, j * j = 1 → ρ j * ρ j = 1 := by
    intro j hj
    rw [← map_mul, hj, map_one]
  have hswap_rk : ∀ j : Y, j * j = 1 → V₁.map (ρ j : V →ₗ[ZMod 2] V) = V₂ → rk (ρ j) = 4 := by
    intro j hj he
    exact modA_rk_swap hc hd₁ H.dim (hinv2 j hj) (fun v hv => he ▸ ⟨v, hv, rfl⟩)
  have htriv : ∀ j : Y, (∀ v ∈ V₁, ρ j v = v) → (∀ v ∈ V₂, ρ j v = v) → j = 1 := by
    intro j h1 h2
    apply H.inj
    rw [map_one]
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.1
      (hc.sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)))
    rw [map_add, h1 v₁ hv₁, h2 v₂ hv₂]
    rfl
  have hV₁ne : V₁ ≠ V₂ := by
    intro he
    have hbot : V₁ = ⊥ := by
      have := hc.disjoint
      rw [← he] at this
      exact disjoint_self.1 this
    rw [hbot, finrank_bot] at hd₁
    omega
  refine ⟨fun j hj2 hj1 => ?_, fun F hF2 hF4 => ?_⟩
  · rcases hperm j with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have m₁ := modA_mem_stab_of_map_eq e1
      have m₂ := modA_mem_stab_of_map_eq e2
      have hrk := modA_rk_add hc m₁ m₂
      obtain ⟨o₁, z₁⟩ := e25_summand_facts HM hd₁ sV₁ hp₁ (hinv2 j hj2) m₁
      obtain ⟨o₂, z₂⟩ := e25_summand_facts HM hd₂ sV₂ hp₂ (hinv2 j hj2) m₂
      by_cases h0 : rk (modA_restr V₁ ⟨ρ j, m₁⟩) = 0 ∧ rk (modA_restr V₂ ⟨ρ j, m₂⟩) = 0
      · exact absurd (htriv j (z₁.1 h0.1) (z₂.1 h0.2)) hj1
      · omega
    · rw [hswap_rk j hj2 e1]
      norm_num
  · by_cases hsw : ∃ f ∈ F, V₁.map (ρ f : V →ₗ[ZMod 2] V) = V₂
    · obtain ⟨f, hf, he⟩ := hsw
      refine ⟨f, hf, ?_, ?_⟩
      · intro hf1
        rw [hf1, map_one] at he
        exact hV₁ne (by simpa using he)
      · rw [hswap_rk f (hF2 f hf) he]
    ·
      have hpres : ∀ f ∈ F, ρ f ∈ modA_stab V₁ ∧ ρ f ∈ modA_stab V₂ := by
        intro f hf
        rcases hperm f with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact ⟨modA_mem_stab_of_map_eq e1, modA_mem_stab_of_map_eq e2⟩
        · exact absurd ⟨f, hf, e1⟩ hsw
      by_contra hno'
      have hno : ∀ j ∈ F, j ≠ 1 → rk (ρ j) < 4 := fun j hj hj1 =>
        lt_of_not_ge fun hge => hno' ⟨j, hj, hj1, hge⟩
      have hcomm : ∀ f ∈ F, ∀ g ∈ F, f * g = g * f := by
        intro f hf g hg
        have h1 := hF2 (f * g) (mul_mem hf hg)
        have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right (hF2 f hf)
        have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hF2 g hg)
        calc f * g = (f * g)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
          _ = g * f := by rw [mul_inv_rev, hfi, hgi]
      have key₁ : ∀ f ∈ F, ∀ g ∈ F, (¬ ∀ v ∈ V₁, ρ f v = v) → (¬ ∀ v ∈ V₁, ρ g v = v) →
          ∀ v ∈ V₁, ρ (f * g) v = v := fun f hf g hg hT hT' =>
        e25_prod_triv HM hd₁ sV₁ hp₁ (hinv2 f (hF2 f hf)) (hinv2 g (hF2 g hg))
          (hinv2 (f * g) (hF2 _ (mul_mem hf hg))) (hpres f hf).1 (hpres g hg).1 hT hT'
      have key₂ : ∀ f ∈ F, ∀ g ∈ F, (¬ ∀ v ∈ V₂, ρ f v = v) → (¬ ∀ v ∈ V₂, ρ g v = v) →
          ∀ v ∈ V₂, ρ (f * g) v = v := fun f hf g hg hT hT' =>
        e25_prod_triv HM hd₂ sV₂ hp₂ (hinv2 f (hF2 f hf)) (hinv2 g (hF2 g hg))
          (hinv2 (f * g) (hF2 _ (mul_mem hf hg))) (hpres f hf).2 (hpres g hg).2 hT hT'
      have hcls : ∀ f ∈ F, f ≠ 1 → ((∀ v ∈ V₁, ρ f v = v) ↔ ¬ ∀ v ∈ V₂, ρ f v = v) := by
        intro f hf hf1
        obtain ⟨o₁, z₁⟩ := e25_summand_facts HM hd₁ sV₁ hp₁ (hinv2 f (hF2 f hf)) (hpres f hf).1
        obtain ⟨o₂, z₂⟩ := e25_summand_facts HM hd₂ sV₂ hp₂ (hinv2 f (hF2 f hf)) (hpres f hf).2
        have hrk := modA_rk_add hc (hpres f hf).1 (hpres f hf).2
        have hlt := hno f hf hf1
        constructor
        · intro h1 h2
          exact hf1 (htriv f h1 h2)
        · intro hn2
          by_contra hn1
          have a1 : rk (modA_restr V₁ ⟨ρ f, (hpres f hf).1⟩) ≠ 0 := fun h0 => hn1 (z₁.1 h0)
          have a2 : rk (modA_restr V₂ ⟨ρ f, (hpres f hf).2⟩) ≠ 0 := fun h0 => hn2 (z₂.1 h0)
          omega
      have hclash : ∀ f ∈ F, ∀ g ∈ F, f ≠ 1 → g ≠ 1 → f * g ≠ 1 →
          ((∀ v ∈ V₁, ρ f v = v) ↔ (∀ v ∈ V₁, ρ g v = v)) → False := by
        intro f hf g hg hf1 hg1 hfg hiff
        by_cases hT : ∀ v ∈ V₁, ρ f v = v
        · have hTg := hiff.1 hT
          have hn2f := (hcls f hf hf1).1 hT
          have hn2g := (hcls g hg hg1).1 hTg
          have h2 := key₂ f hf g hg hn2f hn2g
          have h1 : ∀ v ∈ V₁, ρ (f * g) v = v := fun v hv => by
            rw [map_mul]
            exact (congrArg (ρ f) (hTg v hv)).trans (hT v hv)
          exact hfg (htriv _ h1 h2)
        · have hTg : ¬ ∀ v ∈ V₁, ρ g v = v := fun hg' => hT (hiff.2 hg')
          have h1 := key₁ f hf g hg hT hTg
          have h2f : ∀ v ∈ V₂, ρ f v = v := by
            by_contra hh
            exact hT ((hcls f hf hf1).2 hh)
          have h2g : ∀ v ∈ V₂, ρ g v = v := by
            by_contra hh
            exact hTg ((hcls g hg hg1).2 hh)
          have h2 : ∀ v ∈ V₂, ρ (f * g) v = v := fun v hv => by
            rw [map_mul]
            exact (congrArg (ρ f) (h2g v hv)).trans (h2f v hv)
          exact hfg (htriv _ h1 h2)
      obtain ⟨a, haF, ha1⟩ : ∃ a ∈ F, a ≠ 1 := by
        by_contra hh
        have : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 fun a ha =>
          by_contra fun h1 => hh ⟨a, ha, h1⟩
        rw [this, Subgroup.card_bot] at hF4
        omega
      have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hF2 a haF) ha1
      have hlt : zpowers a < F := by
        refine lt_of_le_of_ne ((Subgroup.zpowers_le).2 haF) fun hEq => ?_
        have : Nat.card F = 2 := by rw [← hEq, Nat.card_zpowers, ha2]
        omega
      obtain ⟨b, hbF, hbn⟩ := SetLike.exists_of_lt hlt
      have hb1 : b ≠ 1 := fun h1 => hbn (h1 ▸ one_mem _)
      have hab1 : a * b ≠ 1 := by
        intro h1
        apply hbn
        have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact inv_mem (mem_zpowers a)
      have habF : a * b ∈ F := mul_mem haF hbF
      have e1 : a * (a * b) = b := by rw [← mul_assoc, hF2 a haF, one_mul]
      have e2 : b * (a * b) = a :=
        calc b * (a * b) = (b * a) * b := (mul_assoc _ _ _).symm
          _ = (a * b) * b := by rw [hcomm b hbF a haF]
          _ = a * (b * b) := mul_assoc _ _ _
          _ = a := by rw [hF2 b hbF, mul_one]
      have hP₁ := hclash a haF b hbF ha1 hb1 hab1
      have hP₂ := hclash a haF (a * b) habF ha1 hab1 (by rw [e1]; exact hb1)
      have hP₃ := hclash b hbF (a * b) habF hb1 hab1 (by rw [e2]; exact ha1)
      tauto

end Ranks

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
