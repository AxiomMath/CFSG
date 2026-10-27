module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoYOneAlpha

public section

namespace CFSG.OddStandard.AltStdCycTwo.YOne

open Subgroup Equiv Equiv.Perm AltStdSec AltStdBal

section Proj

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem normalizer_le_normalizer_centralizer (J : Subgroup X) :
    normalizer (J : Set X) ≤ normalizer (centralizer (J : Set X) : Set X) := by
  intro g hg
  rw [mem_normalizer_iff]
  have key : ∀ g ∈ normalizer (J : Set X), ∀ c ∈ centralizer (J : Set X),
      g * c * g⁻¹ ∈ centralizer (J : Set X) := by
    intro g hg c hc
    rw [mem_centralizer_iff]
    intro j hj
    have hj' : g⁻¹ * j * g ∈ J := by
      have := (mem_normalizer_iff.1 (inv_mem hg) j).1 hj
      simpa using this
    have h1 := mem_centralizer_iff.1 hc _ hj'
    calc j * (g * c * g⁻¹) = g * ((g⁻¹ * j * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * j * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * j := by group
  intro c
  refine ⟨key g hg c, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h
  simpa [mul_assoc] using this

omit [Finite X] in
theorem le_centralizer_of_proj {J D P : Subgroup X} [Group.IsPerfect P]
    (hPJ : P ≤ normalizer (J : Set X)) (hDJ : D ≤ normalizer (J : Set X))
    (hDC : D ⊓ centralizer (J : Set X) = ⊥)
    (hproj : ∀ x ∈ P, ∃ d ∈ D, x * d⁻¹ ∈ centralizer (J : Set X))
    (S : Set X) (hSD : S ⊆ D) (hPS : ∀ x ∈ P, ∀ s ∈ S, x * s = s * x)
    (hQ : ∀ Q : Subgroup X, Group.IsPerfect Q → Q ≤ D → (∀ q ∈ Q, ∀ s ∈ S, q * s = s * q) →
      Q = ⊥) :
    P ≤ centralizer (J : Set X) := by
  classical
  have hNC := normalizer_le_normalizer_centralizer J
  have huniq : ∀ x : X, ∀ d ∈ D, ∀ d' ∈ D, x * d⁻¹ ∈ centralizer (J : Set X) →
      x * d'⁻¹ ∈ centralizer (J : Set X) → d = d' := by
    intro x d hd d' hd' h1 h2
    have h3 : d' * d⁻¹ ∈ D ⊓ centralizer (J : Set X) := by
      refine Subgroup.mem_inf.2 ⟨D.mul_mem hd' (D.inv_mem hd), ?_⟩
      have : d' * d⁻¹ = (x * d'⁻¹)⁻¹ * (x * d⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
    rw [hDC, mem_bot] at h3
    have := mul_inv_eq_one.1 h3
    exact this.symm
  choose! ψ hψD hψC using hproj
  have hψmul : ∀ x ∈ P, ∀ y ∈ P, ψ (x * y) = ψ x * ψ y := by
    intro x hx y hy
    refine huniq (x * y) _ (hψD _ (mul_mem hx hy)) _ (mul_mem (hψD x hx) (hψD y hy))
      (hψC _ (mul_mem hx hy)) ?_
    have h1 : x * (y * (ψ y)⁻¹) * x⁻¹ ∈ centralizer (J : Set X) :=
      (mem_normalizer_iff.1 (hNC (hPJ hx)) _).1 (hψC y hy)
    have : x * y * (ψ x * ψ y)⁻¹ = (x * (y * (ψ y)⁻¹) * x⁻¹) * (x * (ψ x)⁻¹) := by group
    rw [this]
    exact mul_mem h1 (hψC x hx)
  let f : P →* D :=
    { toFun := fun x => ⟨ψ x, hψD x x.2⟩
      map_one' := by
        apply Subtype.ext
        exact (huniq 1 _ (hψD 1 (one_mem P)) 1 (one_mem D) (hψC 1 (one_mem P))
          (by simp)).trans rfl
      map_mul' := fun x y => Subtype.ext (hψmul x x.2 y y.2) }
  have hfS : ∀ x ∈ P, ∀ s ∈ S, ψ x * s = s * ψ x := by
    intro x hx s hs
    obtain ⟨p, hp⟩ : ∃ p, ψ x = p := ⟨_, rfl⟩
    have hpD : p ∈ D := hp ▸ hψD x hx
    have hcC : x * p⁻¹ ∈ centralizer (J : Set X) := hp ▸ hψC x hx
    rw [hp]
    obtain ⟨c, hc⟩ : ∃ c, c = x * p⁻¹ := ⟨_, rfl⟩
    rw [← hc] at hcC
    have hp' : p = c⁻¹ * x := by rw [hc]; group
    have hsN : s ∈ normalizer (J : Set X) := hDJ (hSD hs)
    have h1 : s * c * s⁻¹ ∈ centralizer (J : Set X) :=
      (mem_normalizer_iff.1 (hNC hsN) c).1 hcC
    have hxs' : s * x * s⁻¹ = x := by rw [← hPS x hx s hs]; group
    have h2 : s * p * s⁻¹ * p⁻¹ ∈ D ⊓ centralizer (J : Set X) := by
      refine Subgroup.mem_inf.2 ⟨D.mul_mem (D.mul_mem (D.mul_mem (hSD hs) hpD)
        (D.inv_mem (hSD hs))) (D.inv_mem hpD), ?_⟩
      have : s * p * s⁻¹ * p⁻¹ = (s * c * s⁻¹)⁻¹ * c := by
        calc s * p * s⁻¹ * p⁻¹ = s * (c⁻¹ * x) * s⁻¹ * (c⁻¹ * x)⁻¹ := by rw [hp']
          _ = (s * c * s⁻¹)⁻¹ * (s * x * s⁻¹) * x⁻¹ * c := by group
          _ = (s * c * s⁻¹)⁻¹ * c := by rw [hxs']; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) hcC
    rw [hDC, mem_bot] at h2
    calc p * s = (s * p * s⁻¹ * p⁻¹)⁻¹ * s * p := by group
      _ = s * p := by rw [h2, inv_one, one_mul]
  have hQ' : f.range.map D.subtype = ⊥ := by
    have : Group.IsPerfect f.range := Group.IsPerfect.range f
    have : Group.IsPerfect (f.range.map D.subtype) := Group.IsPerfect.map _
    refine hQ _ this (map_subtype_le _) ?_
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ s hs
    exact hfS x x.2 s hs
  intro x hx
  have h1 : (f ⟨x, hx⟩ : X) = 1 := by
    have : (f ⟨x, hx⟩ : X) ∈ f.range.map D.subtype := ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    rw [hQ', mem_bot] at this
    exact this
  have h2 : ψ x = 1 := h1
  have := hψC x hx
  rwa [h2, inv_one, mul_one] at this

omit [Finite X] in
theorem exists_mul_inv_mem_centralizer [Finite X] {J : Subgroup X} (hJ : CFSG.IsComponent J)
    {x : X} (hx : x ∈ CFSG.layer X) : ∃ j ∈ J, x * j⁻¹ ∈ centralizer (J : Set X) := by
  obtain ⟨f, rfl⟩ := CFSG.LocalCores.exists_layerMul_eq hx
  set Jc : CFSG.LocalCores.ComponentIndex X := ⟨J, hJ⟩
  refine ⟨(f Jc : X), (f Jc).2, ?_⟩
  rw [CFSG.LocalCores.layerMul_eq_mul_update f Jc]
  rw [mem_centralizer_iff]
  intro k hk
  have h1 := CFSG.LocalCores.commute_layerMul_update f Jc (k := k) hk
  have h2 : (f Jc : X) * CFSG.LocalCores.layerMul X (Function.update f Jc 1) * (f Jc : X)⁻¹ =
      CFSG.LocalCores.layerMul X (Function.update f Jc 1) :=
    (CFSG.LocalCores.commute_layerMul_update f Jc (f Jc).2).symm.eq ▸ by group
  rw [h2]
  exact h1.eq

end Proj

section Six

variable {X : Type} [Group X] [Finite X] {t : X} {D : Subgroup X} {Ω : Type} [Fintype Ω]
  [DecidableEq Ω]

theorem LocalDatum.inf_centralizer_eq_bot (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω)
    {J : Subgroup X} (hDJ : D ≤ normalizer (J : Set X)) (hne : ⁅D, J⁆ ≠ ⊥) :
    D ⊓ centralizer (J : Set X) = ⊥ := by
  have := h.isSimpleGroup η
  have hNC := normalizer_le_normalizer_centralizer J
  have hn : ((D ⊓ centralizer (J : Set X)).subgroupOf D).Normal := by
    refine ⟨fun c hc d => ?_⟩
    have hc' : (c : X) ∈ D ⊓ centralizer (J : Set X) := hc
    show ((d * c * d⁻¹ : D) : X) ∈ D ⊓ centralizer (J : Set X)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_inf.2 ⟨D.mul_mem (D.mul_mem d.2 c.2) (D.inv_mem d.2),
      (mem_normalizer_iff.1 (hNC (hDJ d.2)) c).1 (Subgroup.mem_inf.1 hc').2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D ⊓ centralizer (J : Set X)).subgroupOf D)
    with h1 | h1
  · exact (Subgroup.subgroupOf_eq_bot.1 h1).eq_bot_of_le inf_le_left
  · exfalso
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro d hd
    exact (Subgroup.mem_inf.1 (Subgroup.subgroupOf_eq_top.1 h1 hd)).2

omit [Finite X] in
theorem LocalDatum.perfect_eq_bot_of_comm_D (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω)
    {s₁ s₂ s₃ s₄ : Ω} (h12 : s₁ ≠ s₂) (h13 : s₁ ≠ s₃) (h14 : s₁ ≠ s₄) (h23 : s₂ ≠ s₃)
    (h24 : s₂ ≠ s₄) (h34 : s₃ ≠ s₄) {Q : Subgroup X} [Group.IsPerfect Q] (hQD : Q ≤ D)
    (hQ : ∀ q ∈ Q, ∀ d : D, (((η d : alternatingGroup Ω) : Perm Ω) = swap s₁ s₂ * swap s₃ s₄ ∨
        ∀ s ∈ ({s₁, s₂, s₃, s₄} : Finset Ω), ((η d : alternatingGroup Ω) : Perm Ω) s = s) →
      q * d = d * q) : Q = ⊥ := by
  classical
  set S' : Finset Ω := {s₁, s₂, s₃, s₄} with hS'
  set ε : Perm Ω := swap s₁ s₂ * swap s₃ s₄ with hε
  have hεA : ε ∈ alternatingGroup Ω := by
    rw [Perm.mem_alternatingGroup, hε, Perm.sign_mul, Perm.sign_swap h12, Perm.sign_swap h34]
    decide
  have hS'c : S'.card = 4 := by
    rw [hS', Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_insert_of_notMem (by simp [h23, h24]),
      Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
  have hεfix : ∀ x, x ∉ S' → ε x = x := by
    intro x hx
    simp only [hS', Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    rw [hε, Perm.mul_apply, swap_apply_of_ne_of_ne hx.2.2.1 hx.2.2.2,
      swap_apply_of_ne_of_ne hx.1 hx.2.1]
  have hεmov : ∀ x, x ∈ S' → ε x ≠ x := by
    intro x hx
    simp only [hS', Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx, hε, Perm.mul_apply]
    · rw [swap_apply_of_ne_of_ne h13 h14, swap_apply_left]; exact h12.symm
    · rw [swap_apply_of_ne_of_ne h23 h24, swap_apply_right]; exact h12
    · rw [swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm h14) (Ne.symm h24)]; exact h34.symm
    · rw [swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm h13) (Ne.symm h23)]; exact h34
  set Q' : Subgroup (Perm Ω) :=
    ((Q.subgroupOf D).map η.toMonoidHom).map (alternatingGroup Ω).subtype with hQ'
  have : Group.IsPerfect (Q.subgroupOf D) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hQD).symm.toMonoidHom)
      (subgroupOfEquivOfLe hQD).symm.surjective
  have : Group.IsPerfect ((Q.subgroupOf D).map η.toMonoidHom) := Group.IsPerfect.map _
  have : Group.IsPerfect Q' := Group.IsPerfect.map _
  have hmem : ∀ g ∈ Q', ∃ q ∈ Q, ∃ hq : q ∈ D, g = ((η ⟨q, hq⟩ : alternatingGroup Ω) : Perm Ω) := by
    rintro _ ⟨_, ⟨⟨q, hqD⟩, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, hqD, rfl⟩
  have hcommη : ∀ q ∈ Q, ∀ (hq : q ∈ D) (g : alternatingGroup Ω),
      ((g : Perm Ω) = ε ∨ ∀ s ∈ S', (g : Perm Ω) s = s) →
      ((η ⟨q, hq⟩ : alternatingGroup Ω) : Perm Ω) * g = g * (η ⟨q, hq⟩ : alternatingGroup Ω) := by
    intro q hq hqD g hg
    have h1 := hQ q hq (η.symm g) (by simpa using hg)
    have h2 : (⟨q, hqD⟩ : D) * η.symm g = η.symm g * ⟨q, hqD⟩ := Subtype.ext h1
    have h3 := congrArg (fun d : D => ((η d : alternatingGroup Ω) : Perm Ω)) h2
    simpa using h3
  have hbot : Q' = ⊥ := by
    refine perfect_eq_bot_of_comm (ε := ε) (F := S'ᶜ) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Finset.card_compl, hS'c]
      have := h.card
      omega
    · intro x hx
      exact hεfix x (Finset.mem_compl.1 hx)
    · refine (Finset.card_le_card fun x hx => ?_).trans hS'c.le
      by_contra hxS
      exact (mem_moved.1 hx) (hεfix x hxS)
    · refine le_of_eq_of_le (Finset.card_eq_zero.2 ?_) (by norm_num)
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, not_not] at hx
      exact hεmov x hx.1 hx.2
    · intro g hg
      obtain ⟨q, hq, hqD, rfl⟩ := hmem g hg
      exact hcommη q hq hqD ⟨ε, hεA⟩ (Or.inl rfl)
    · intro g hg x hx y hy w hw hxy hyw hxw
      obtain ⟨q, hq, hqD, rfl⟩ := hmem g hg
      refine hcommη q hq hqD ⟨cyc3 x y w, mem_alt_cyc3 hxy hyw⟩ (Or.inr fun s hs => ?_)
      have hs' : s ∉ S'ᶜ := fun h' => (Finset.mem_compl.1 h') hs
      exact cyc3_apply_of_ne (fun e => hs' (e ▸ hx)) (fun e => hs' (e ▸ hy))
        (fun e => hs' (e ▸ hw))
  rw [eq_bot_iff]
  intro q hq
  have h1 : ((η ⟨q, hQD hq⟩ : alternatingGroup Ω) : Perm Ω) ∈ Q' :=
    ⟨_, ⟨⟨q, hQD hq⟩, hq, rfl⟩, rfl⟩
  rw [hbot, mem_bot] at h1
  have h2 : η ⟨q, hQD hq⟩ = 1 := Subtype.ext h1
  rw [MulEquiv.map_eq_one_iff] at h2
  exact mem_bot.2 (congrArg Subtype.val h2)

theorem LocalDatum.perfect_le_centralizer (h : LocalDatum t D Ω) (η : D ≃* alternatingGroup Ω)
    (hlook : AltLookupAt (Fintype.card Ω)) {s₁ s₂ s₃ s₄ : Ω} (h12 : s₁ ≠ s₂) (h13 : s₁ ≠ s₃)
    (h14 : s₁ ≠ s₄) (h23 : s₂ ≠ s₃) (h24 : s₂ ≠ s₄) (h34 : s₃ ≠ s₄)
    {P : Subgroup X} [Group.IsPerfect P] (hP : P ≤ CFSG.layer X)
    (hPD : ∀ x ∈ P, ∀ d : D, (((η d : alternatingGroup Ω) : Perm Ω) = swap s₁ s₂ * swap s₃ s₄ ∨
        ∀ s ∈ ({s₁, s₂, s₃, s₄} : Finset Ω), ((η d : alternatingGroup Ω) : Perm Ω) s = s) →
      x * d = d * x) :
    P ≤ centralizer (D : Set X) := by
  classical
  obtain ⟨hDE, K, hK, hDK, hle, hiff, hKK, hKt⟩ := h.alpha η
  set Kt := K.map (MulAut.conj t).toMonoidHom with hKtdef
  have hKtc : CFSG.IsComponent Kt := CFSG.LocalCores.isComponent_map_mulEquiv _ hK
  have hDKt : ⁅D, Kt⁆ ≠ ⊥ := (hiff Kt hKtc).2 (Or.inr rfl)
  set S : Set X := {x | ∃ hx : x ∈ D, ((η ⟨x, hx⟩ : alternatingGroup Ω) : Perm Ω) =
    swap s₁ s₂ * swap s₃ s₄ ∨ ∀ s ∈ ({s₁, s₂, s₃, s₄} : Finset Ω),
      ((η ⟨x, hx⟩ : alternatingGroup Ω) : Perm Ω) s = s} with hS
  have hSD : S ⊆ D := fun x hx => hx.1
  have hPS : ∀ x ∈ P, ∀ s ∈ S, x * s = s * x := by
    rintro x hx s ⟨hsD, hs⟩
    exact hPD x hx ⟨s, hsD⟩ hs
  have hQ : ∀ Q : Subgroup X, Group.IsPerfect Q → Q ≤ D → (∀ q ∈ Q, ∀ s ∈ S, q * s = s * q) →
      Q = ⊥ := by
    intro Q _ hQD hQS
    exact h.perfect_eq_bot_of_comm_D η h12 h13 h14 h23 h24 h34 hQD
      (fun q hq d hd => hQS q hq d ⟨d.2, hd⟩)
  have hJ : ∀ J : Subgroup X, CFSG.IsComponent J → ⁅D, J⁆ ≠ ⊥ →
      (∀ x ∈ CFSG.layer X, ∃ d ∈ D, x * d⁻¹ ∈ centralizer (J : Set X)) →
      P ≤ centralizer (J : Set X) := by
    intro J hJc hDJ hproj
    have hDN : D ≤ normalizer (J : Set X) := hDE.trans (CFSG.LocalCores.layer_le_normalizer hJc)
    exact le_centralizer_of_proj (hP.trans (CFSG.LocalCores.layer_le_normalizer hJc)) hDN
      (h.inf_centralizer_eq_bot η hDN hDJ) (fun x hx => hproj x (hP hx)) S hSD hPS hQ
  suffices hPK : P ≤ centralizer (K : Set X) ∧ P ≤ centralizer (Kt : Set X) by
    rw [Subgroup.le_centralizer_iff]
    refine hle.trans (sup_le ?_ ?_)
    · rw [← Subgroup.le_centralizer_iff]; exact hPK.1
    · rw [← Subgroup.le_centralizer_iff]; exact hPK.2
  by_cases hKK' : Kt = K
  · obtain ⟨hDK', hDc⟩ := hKK hKK'
    suffices hPK : P ≤ centralizer (K : Set X) from ⟨hPK, hKK' ▸ hPK⟩
    by_cases hKD : K = D
    · refine hJ K hK hDK fun x hx => ?_
      obtain ⟨j, hj, hjc⟩ := exists_mul_inv_mem_centralizer hK hx
      exact ⟨j, hKD ▸ hj, hjc⟩
    obtain ⟨N, φ, hI⟩ := h.altIdent η hlook hK hKK' hDK' hDc hKD
    obtain ⟨β, hβ⟩ := hI.bij
    have hPN : P ≤ normalizer (K : Set X) := hP.trans (CFSG.LocalCores.layer_le_normalizer hK)
    set P' : Subgroup (Perm (Fin N)) := (P.subgroupOf (normalizer (K : Set X))).map φ with hP'
    have : Group.IsPerfect (P.subgroupOf (normalizer (K : Set X))) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPN).symm.toMonoidHom)
        (subgroupOfEquivOfLe hPN).symm.surjective
    have : Group.IsPerfect P' := Group.IsPerfect.map _
    set S' : Finset Ω := {s₁, s₂, s₃, s₄} with hS'
    have hS'c : S'.card = 4 := by
      rw [hS', Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
        Finset.card_insert_of_notMem (by simp [h23, h24]),
        Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
    set b : Ω → Fin N := fun ω => (β ω : Fin N) with hb
    have hbinj : Function.Injective b := fun ω ω' e => β.injective (Subtype.ext e)
    set ε : Perm (Fin N) := swap (b s₁) (b s₂) * swap (b s₃) (b s₄) with hε
    set F₀ : Finset (Fin N) := S'ᶜ.image b with hF₀
    have hεA : swap s₁ s₂ * swap s₃ s₄ ∈ alternatingGroup Ω := by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap h12, Perm.sign_swap h34]
      decide
    have hε_d : φ ⟨η.symm ⟨_, hεA⟩, le_normalizer (hI.hD (η.symm ⟨_, hεA⟩).2)⟩ = ε := by
      rw [hβ, MulEquiv.apply_symm_apply, ofSubtype_permCongr_swap_mul_swap]
    have hcomm_φ : ∀ x (hx : x ∈ P), ∀ d : D, (((η d : alternatingGroup Ω) : Perm Ω) =
        swap s₁ s₂ * swap s₃ s₄ ∨ ∀ s ∈ S', ((η d : alternatingGroup Ω) : Perm Ω) s = s) →
        φ ⟨x, hPN hx⟩ * φ ⟨d, le_normalizer (hI.hD d.2)⟩ =
          φ ⟨d, le_normalizer (hI.hD d.2)⟩ * φ ⟨x, hPN hx⟩ := by
      intro x hx d hd
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hPD x hx d hd)
    have hmemP' : ∀ g ∈ P', ∃ x, ∃ hx : x ∈ P, g = φ ⟨x, hPN hx⟩ := by
      rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    have hbot : P' = ⊥ := by
      refine perfect_eq_bot_of_comm (ε := ε) (F := F₀) ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hF₀, Finset.card_image_of_injective _ hbinj, Finset.card_compl, hS'c]
        have := h.card
        omega
      · intro x hx
        obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.1 hx
        have hωS : ω ∉ S' := Finset.mem_compl.1 hω
        simp only [hS', Finset.mem_insert, Finset.mem_singleton, not_or] at hωS
        rw [hε, Perm.mul_apply, swap_apply_of_ne_of_ne (hbinj.ne hωS.2.2.1)
          (hbinj.ne hωS.2.2.2), swap_apply_of_ne_of_ne (hbinj.ne hωS.1) (hbinj.ne hωS.2.1)]
      · refine (Finset.card_le_card fun x hx => ?_).trans
          ((Finset.card_image_le (s := S') (f := b)).trans hS'c.le)
        rw [mem_moved] at hx
        by_contra hxS
        apply hx
        have hxs : ∀ s ∈ S', x ≠ b s := fun s hs e => hxS (Finset.mem_image.2 ⟨s, hs, e.symm⟩)
        rw [hε, Perm.mul_apply, swap_apply_of_ne_of_ne (hxs s₃ (by simp [hS']))
          (hxs s₄ (by simp [hS'])), swap_apply_of_ne_of_ne (hxs s₁ (by simp [hS']))
          (hxs s₂ (by simp [hS']))]
      · refine (Finset.card_le_card fun x hx => ?_).trans hI.moved
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hF₀] at hx
        rw [mem_moved]
        intro hτx
        set ω := β.symm ⟨x, hτx⟩ with hω
        have hbω : b ω = x := by simp [hb, hω]
        by_cases hωS : ω ∈ S'
        ·
          exfalso
          have hne : ε (b ω) ≠ b ω := by
            simp only [hS', Finset.mem_insert, Finset.mem_singleton] at hωS
            rw [hε, Perm.mul_apply]
            rcases hωS with e | e | e | e <;> rw [e]
            · rw [swap_apply_of_ne_of_ne (hbinj.ne h13) (hbinj.ne h14), swap_apply_left]
              exact hbinj.ne (Ne.symm h12)
            · rw [swap_apply_of_ne_of_ne (hbinj.ne h23) (hbinj.ne h24), swap_apply_right]
              exact hbinj.ne h12
            · rw [swap_apply_left, swap_apply_of_ne_of_ne (hbinj.ne (Ne.symm h14))
                (hbinj.ne (Ne.symm h24))]
              exact hbinj.ne (Ne.symm h34)
            · rw [swap_apply_right, swap_apply_of_ne_of_ne (hbinj.ne (Ne.symm h13))
                (hbinj.ne (Ne.symm h23))]
              exact hbinj.ne h34
          rw [hbω] at hne
          exact hne hx.2
        · exact hx.1 (Finset.mem_image.2 ⟨ω, Finset.mem_compl.2 hωS, hbω⟩)
      · intro g hg
        obtain ⟨x, hx, rfl⟩ := hmemP' g hg
        rw [← hε_d]
        exact hcomm_φ x hx _ (Or.inl (by rw [MulEquiv.apply_symm_apply]))
      · intro g hg x₁ hx₁ x₂ hx₂ x₃ hx₃ h12' h23' h13'
        obtain ⟨y, hy, rfl⟩ := hmemP' g hg
        obtain ⟨ω₁, hω₁, rfl⟩ := Finset.mem_image.1 hx₁
        obtain ⟨ω₂, hω₂, rfl⟩ := Finset.mem_image.1 hx₂
        obtain ⟨ω₃, hω₃, rfl⟩ := Finset.mem_image.1 hx₃
        have e12 : ω₁ ≠ ω₂ := fun e => h12' (by rw [e])
        have e23 : ω₂ ≠ ω₃ := fun e => h23' (by rw [e])
        set d : D := η.symm ⟨cyc3 ω₁ ω₂ ω₃, mem_alt_cyc3 e12 e23⟩ with hd
        have hdφ : φ ⟨d, le_normalizer (hI.hD d.2)⟩ = cyc3 (b ω₁) (b ω₂) (b ω₃) := by
          rw [hβ, hd, MulEquiv.apply_symm_apply, ofSubtype_permCongr_cyc3]
        rw [← hdφ]
        refine hcomm_φ y hy d (Or.inr fun s hs => ?_)
        rw [hd, MulEquiv.apply_symm_apply]
        have hs' : ∀ ω ∈ S'ᶜ, s ≠ ω := fun ω hω e => (Finset.mem_compl.1 hω) (e ▸ hs)
        exact cyc3_apply_of_ne (hs' ω₁ hω₁) (hs' ω₂ hω₂) (hs' ω₃ hω₃)
    intro x hx
    have h1 : φ ⟨x, hPN hx⟩ ∈ P' := ⟨⟨x, hPN hx⟩, hx, rfl⟩
    rw [hbot, mem_bot] at h1
    exact (hI.ker _).1 h1
  ·
    obtain ⟨hcomm, hDset⟩ := hKt hKK'
    have hKKt : K ≤ centralizer (Kt : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hKtK : Kt ≤ centralizer (K : Set X) := by
      rw [← Subgroup.le_centralizer_iff]
      exact hKKt
    have hdiag : ∀ k ∈ K, k * (t * k * t⁻¹) ∈ D := by
      intro k hk
      have : k * (t * k * t⁻¹) ∈ (D : Set X) := by rw [hDset]; exact ⟨k, hk, rfl⟩
      exact this
    have hkt : ∀ k ∈ K, t * k * t⁻¹ ∈ Kt := fun k hk => ⟨k, hk, by simp [MulAut.conj_apply]⟩
    refine ⟨hJ K hK hDK fun x hx => ?_, hJ Kt hKtc hDKt fun x hx => ?_⟩
    · obtain ⟨j, hj, hjc⟩ := exists_mul_inv_mem_centralizer hK hx
      refine ⟨j * (t * j * t⁻¹), hdiag j hj, ?_⟩
      have hu : (t * j * t⁻¹)⁻¹ ∈ centralizer (K : Set X) := inv_mem (hKtK (hkt j hj))
      have hju : j * (t * j * t⁻¹)⁻¹ * j⁻¹ = (t * j * t⁻¹)⁻¹ := by
        rw [mem_centralizer_iff.1 hu j hj]
        group
      have : x * (j * (t * j * t⁻¹))⁻¹ = (x * j⁻¹) * (j * (t * j * t⁻¹)⁻¹ * j⁻¹) := by group
      rw [this, hju]
      exact mul_mem hjc hu
    · obtain ⟨j', hj', hjc⟩ := exists_mul_inv_mem_centralizer hKtc hx
      obtain ⟨k, hk, rfl⟩ := hj'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hjc ⊢
      refine ⟨k * (t * k * t⁻¹), hdiag k hk, ?_⟩
      have : x * (k * (t * k * t⁻¹))⁻¹ = (x * (t * k * t⁻¹)⁻¹) * k⁻¹ := by group
      rw [this]
      exact mul_mem hjc (inv_mem (hKKt hk))

end Six

section Global

variable {G : Type} [Group G] [Finite G]

theorem layer_le_of_balance {H : Subgroup G} (hO : CFSG.oddCore H = ⊥) {a : G} (ha : a ∈ H)
    (ha2 : a * a = 1) {K : Subgroup G}
    (hK : CFSG.Assembly.IsComponentOf K (H ⊓ centralizer ({a} : Set G))) :
    K.subgroupOf H ≤ CFSG.layer H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a' : H := ⟨a, ha⟩
  set A : Subgroup H := zpowers a' with hA
  have hAp : IsPGroup 2 A := by
    have hord : orderOf a' ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [sq]; exact Subtype.ext ha2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  set C : Subgroup H := centralizer (A : Set H) with hC
  have hCeq : C = (H ⊓ centralizer ({a} : Set G)).comap H.subtype := by
    rw [hC, hA, zpowers_eq_closure, centralizer_closure]
    ext y
    simp only [mem_comap, Subgroup.coe_subtype, mem_inf, SetLike.coe_mem, true_and]
    rw [mem_centralizer_mk_iff]
  have hKH : K ≤ H := hK.1.trans inf_le_left
  have hKC : K.subgroupOf H ≤ C := by
    intro y hy
    rw [hCeq]
    exact hK.1 hy
  have hK1 : CFSG.IsComponent ((K.subgroupOf H).subgroupOf C) := by
    refine ⟨?_, ?_⟩
    · have hq : CFSG.IsQuasisimple K :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).1 hK.2.2
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((subgroupOfEquivOfLe hKH).symm.trans (subgroupOfEquivOfLe hKC).symm) hq
    · have h1 := hK.2.1.comap H.subtype
      rw [← hCeq] at h1
      exact (CFSG.Assembly.IsSubnormal.iff_subgroupOf hKC).1 h1
  have hbal := ClassicalInvolution.l2PrimeBalance H A hAp
  have hpp : CFSG.pPrimeCore 2 H = ⊥ := by
    rw [← ClassicalInvolution.QuaternionStructure.oddCore_eq_pPrimeCore_two]; exact hO
  rw [ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot hpp] at hbal
  have h2 : (K.subgroupOf H).subgroupOf C ≤ CFSG.pLayer C 2 :=
    le_sSup (CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hK1)
  have h3 := (Subgroup.map_mono (f := C.subtype) h2).trans hbal
  rwa [Subgroup.map_subgroupOf_eq_of_le hKC] at h3

omit [Finite G] in
theorem le_centralizer_of_corr {L : Subgroup G} {n : ℕ} (θ : L ≃* alternatingGroup (Fin n))
    {F₁ F₂ : Finset (Fin n)} (hI : 3 ≤ (F₁ ∩ F₂).card) (hU : F₁ ∪ F₂ = Finset.univ) {k : G}
    (h₁ : corr (X := G) θ (altSub F₁) ≤ centralizer ({k} : Set G))
    (h₂ : corr (X := G) θ (altSub F₂) ≤ centralizer ({k} : Set G)) :
    L ≤ centralizer ({k} : Set G) := by
  set ψ : alternatingGroup (Fin n) →* G := L.subtype.comp θ.symm.toMonoidHom with hψ
  set T : Subgroup (Perm (Fin n)) :=
    ((centralizer ({k} : Set G)).comap ψ).map (alternatingGroup (Fin n)).subtype with hT
  have hle : ∀ F : Finset (Fin n), corr (X := G) θ (altSub F) ≤ centralizer ({k} : Set G) →
      altSub F ≤ T := by
    intro F hF g hg
    have hgA := altSub_le_alternatingGroup F hg
    refine ⟨⟨g, hgA⟩, ?_, rfl⟩
    show ψ ⟨g, hgA⟩ ∈ centralizer ({k} : Set G)
    apply hF
    refine mem_corr.2 ⟨(θ.symm ⟨g, hgA⟩).2, ?_⟩
    show ((θ (θ.symm ⟨g, hgA⟩) : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ altSub F
    rw [MulEquiv.apply_symm_apply]
    exact hg
  have hsup : altSub (F₁ ∪ F₂) ≤ T := by
    rw [← altSub_sup_altSub hI]
    exact sup_le (hle F₁ h₁) (hle F₂ h₂)
  intro l hl
  have h1 : ((θ ⟨l, hl⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ T := by
    apply hsup
    rw [hU]
    exact mem_altSub.2 ⟨Perm.mem_alternatingGroup.1 (θ ⟨l, hl⟩).2, fun i hi =>
      absurd (Finset.mem_univ i) hi⟩
  obtain ⟨g, hg, hge⟩ := h1
  have h2 : g = θ ⟨l, hl⟩ := Subtype.ext hge
  have h3 : ψ g = l := by
    rw [h2, hψ]
    simp
  rw [← h3]
  exact hg

theorem not_quasisimple_le_centralizer {L Q : Subgroup G} {z : G} (d : Cyc L Q z)
    {K : Subgroup G} (hK : CFSG.IsQuasisimple K) (hKL : K ≤ centralizer (L : Set G)) : False := by
  obtain ⟨-, hnorm, hodd, -, hdecomp⟩ := oddPart_spec d.le d.pgroup d.odd_index d.cyclic
  set O' := oddPart (centralizer (L : Set G)) with hO'
  have hQc : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q := by
    intro q hq r hr
    have := d.cyclic
    have := (IsCyclic.isMulCommutative (α := Q)).is_comm.comm ⟨q, hq⟩ ⟨r, hr⟩
    exact congrArg Subtype.val this
  have hcomm : ∀ a ∈ centralizer (L : Set G), ∀ b ∈ centralizer (L : Set G),
      a * b * a⁻¹ * b⁻¹ ∈ O' := by
    intro a ha b hb
    obtain ⟨x, hx, q, hq, rfl⟩ := hdecomp a ha
    obtain ⟨y, hy, r, hr, rfl⟩ := hdecomp b hb
    have h1 : q * y * q⁻¹ ∈ O' := hnorm q (d.le hq) y hy
    have h2 : r * x⁻¹ * r⁻¹ ∈ O' := hnorm r (d.le hr) x⁻¹ (inv_mem hx)
    have h3 : q * r * q⁻¹ * r⁻¹ = 1 := by rw [hQc q hq r hr]; group
    have : x * q * (y * r) * (x * q)⁻¹ * (y * r)⁻¹ =
        x * (q * y * q⁻¹) * (q * r * q⁻¹ * r⁻¹) * (r * x⁻¹ * r⁻¹) * y⁻¹ := by group
    rw [this, h3, mul_one]
    exact mul_mem (mul_mem (mul_mem hx h1) h2) (inv_mem hy)
  have hKO : K ≤ O' := by
    rw [← (Subgroup.isPerfect_iff.1 hK.1)]
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact hcomm a (hKL ha) b (hKL hb)
  have hKodd : Odd (Nat.card K) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hKO)
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK
  have : Group.IsPerfect K := hK.1
  exact Group.IsPerfect.not_isSolvable K hsolv

end Global

section Points

variable {n : ℕ}

@[expose] def dtrans (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) :
    alternatingGroup (Fin n) :=
  ⟨swap a b * swap c d, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    decide⟩

variable {a b c d : Fin n} {hab : a ≠ b} {hcd : c ≠ d}

theorem coe_dtrans : ((dtrans a b c d hab hcd : alternatingGroup (Fin n)) : Perm (Fin n)) =
    swap a b * swap c d :=
  rfl

theorem dtrans_apply_of_ne {x : Fin n} (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d) :
    ((dtrans a b c d hab hcd : alternatingGroup (Fin n)) : Perm (Fin n)) x = x := by
  rw [coe_dtrans, Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb]

theorem dtrans_apply_ne (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) {x : Fin n}
    (hx : x = a ∨ x = b ∨ x = c ∨ x = d) :
    ((dtrans a b c d hab hcd : alternatingGroup (Fin n)) : Perm (Fin n)) x ≠ x := by
  rw [coe_dtrans, Perm.mul_apply]
  rcases hx with rfl | rfl | rfl | rfl
  · rw [swap_apply_of_ne_of_ne hac had, swap_apply_left]; exact hab.symm
  · rw [swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]; exact hab
  · rw [swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]; exact hcd.symm
  · rw [swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]; exact hcd

theorem mem_fixFin_dtrans (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) {x : Fin n} :
    x ∈ fixFin ((dtrans a b c d hab hcd : alternatingGroup (Fin n)) : Perm (Fin n)) ↔
      x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
  rw [mem_fixFin]
  constructor
  · intro hx
    by_contra hne
    simp only [not_and_or, not_not] at hne
    apply dtrans_apply_ne hac had hbc hbd (hab := hab) (hcd := hcd) _ hx
    rcases hne with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro ⟨h1, h2, h3, h4⟩
    exact dtrans_apply_of_ne h1 h2 h3 h4

theorem support_card_dtrans (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ((dtrans a b c d hab hcd : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = 4 := by
  have h : ((dtrans a b c d hab hcd : alternatingGroup (Fin n)) : Perm (Fin n)).support =
      {a, b, c, d} := by
    ext x
    rw [Perm.mem_support]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      by_contra hne
      simp only [not_or] at hne
      exact hx (dtrans_apply_of_ne hne.1 hne.2.1 hne.2.2.1 hne.2.2.2)
    · exact dtrans_apply_ne hac had hbc hbd
  rw [h, Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]),
    Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]

theorem orderOf_dtrans (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    orderOf (dtrans a b c d hab hcd) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [Subgroup.coe_pow, coe_dtrans, sq]
    have hdisj : (swap a b).Disjoint (swap c d) :=
      Perm.disjoint_swap_swap (by simp [hab, hac, had, hbc, hbd, hcd])
    calc swap a b * swap c d * (swap a b * swap c d)
        = swap a b * (swap c d * swap a b) * swap c d := by group
      _ = swap a b * (swap a b * swap c d) * swap c d := by rw [hdisj.commute.eq.symm]
      _ = 1 := by rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]
  · intro h
    have := congrArg (fun g : alternatingGroup (Fin n) => (g : Perm (Fin n)) a) h
    simp only [OneMemClass.coe_one, Perm.one_apply] at this
    exact dtrans_apply_ne hac had hbc hbd (hab := hab) (hcd := hcd) (Or.inl rfl) this

end Points

section NoBeta

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z : G}

@[expose] def dtE (hn : 8 ≤ n) : alternatingGroup (Fin n) :=
  dtrans ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩ (by simp) (by simp)

@[expose] def dtE₂ (hn : 8 ≤ n) : alternatingGroup (Fin n) :=
  dtrans ⟨4, by omega⟩ ⟨5, by omega⟩ ⟨6, by omega⟩ ⟨7, by omega⟩ (by simp) (by simp)

theorem mem_fixFin_dtE (hn : 8 ≤ n) {x : Fin n} :
    x ∈ fixFin ((dtE hn : alternatingGroup (Fin n)) : Perm (Fin n)) ↔ 4 ≤ (x : ℕ) := by
  rw [dtE, mem_fixFin_dtrans (by simp) (by simp) (by simp) (by simp)]
  simp only [ne_eq, Fin.ext_iff]
  omega

theorem mem_fixFin_dtE₂ (hn : 8 ≤ n) {x : Fin n} :
    x ∈ fixFin ((dtE₂ hn : alternatingGroup (Fin n)) : Perm (Fin n)) ↔
      (x : ℕ) < 4 ∨ 8 ≤ (x : ℕ) := by
  rw [dtE₂, mem_fixFin_dtrans (by simp) (by simp) (by simp) (by simp)]
  simp only [ne_eq, Fin.ext_iff]
  omega

theorem orderOf_dtE (hn : 8 ≤ n) : orderOf (dtE hn) = 2 :=
  orderOf_dtrans (by simp) (by simp) (by simp) (by simp)

theorem orderOf_dtE₂ (hn : 8 ≤ n) : orderOf (dtE₂ hn) = 2 :=
  orderOf_dtrans (by simp) (by simp) (by simp) (by simp)

theorem support_card_dtE (hn : 8 ≤ n) :
    ((dtE hn : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = 4 :=
  support_card_dtrans (by simp) (by simp) (by simp) (by simp)

theorem support_card_dtE₂ (hn : 8 ≤ n) :
    ((dtE₂ hn : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = 4 :=
  support_card_dtrans (by simp) (by simp) (by simp) (by simp)

@[expose] noncomputable def invE (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) : L :=
  θ.symm (dtE hn)

@[expose] noncomputable def invE₂ (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) : L :=
  θ.symm (dtE₂ hn)

omit [Finite G] in
theorem orderOf_invE (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) :
    orderOf (invE θ hn) = 2 := by
  rw [invE, MulEquiv.orderOf_eq, orderOf_dtE]

omit [Finite G] in
theorem orderOf_invE₂ (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) :
    orderOf (invE₂ θ hn) = 2 := by
  rw [invE₂, MulEquiv.orderOf_eq, orderOf_dtE₂]

omit [Finite G] in
theorem invE₂_mem_fixGroup (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) :
    ((invE₂ θ hn : L) : G) ∈ fixGroup θ (invE θ hn) := by
  refine mem_corr.2 ⟨(invE₂ θ hn).2, ?_⟩
  show ((θ (invE₂ θ hn) : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ _
  rw [invE₂, invE, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  refine mem_altSub.2 ⟨Perm.mem_alternatingGroup.1 (dtE₂ hn).2, fun i hi => ?_⟩
  rw [mem_fixFin_dtE] at hi
  rw [dtE₂, dtrans_apply_of_ne] <;> simp [Fin.ext_iff] <;> omega

omit [Finite G] in
theorem invE_mem_fixGroup (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) :
    ((invE θ hn : L) : G) ∈ fixGroup θ (invE₂ θ hn) := by
  refine mem_corr.2 ⟨(invE θ hn).2, ?_⟩
  show ((θ (invE θ hn) : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ _
  rw [invE₂, invE, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  refine mem_altSub.2 ⟨Perm.mem_alternatingGroup.1 (dtE hn).2, fun i hi => ?_⟩
  rw [mem_fixFin_dtE₂] at hi
  rw [dtE, dtrans_apply_of_ne] <;> simp [Fin.ext_iff] <;> omega

@[expose] noncomputable def etaW (θ : L ≃* alternatingGroup (Fin n)) (w : L) :
    (fixGroup θ w).subgroupOf (centralizer ({(w : G)} : Set G)) ≃*
      alternatingGroup (fixFin ((θ w : alternatingGroup (Fin n)) : Perm (Fin n))) :=
  (subgroupOfEquivOfLe (fixGroup_le_centralizer θ w)).trans (fixGroupEquiv θ _)

theorem ofSubtype_etaW (θ : L ≃* alternatingGroup (Fin n)) (w : L)
    (d : (fixGroup θ w).subgroupOf (centralizer ({(w : G)} : Set G))) :
    Perm.ofSubtype ((etaW θ w d : alternatingGroup
        (fixFin ((θ w : alternatingGroup (Fin n)) : Perm (Fin n)))) :
          Perm (fixFin ((θ w : alternatingGroup (Fin n)) : Perm (Fin n)))) =
      ((θ ⟨d, fixGroup_le θ w d.2⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) :=
  ofSubtype_fixGroupEquiv θ _ ⟨d, d.2⟩

theorem hn8_of_eleven {n : ℕ} (hn : 11 ≤ n) : 8 ≤ n :=
  le_trans (by norm_num) hn

end NoBeta

end CFSG.OddStandard.AltStdCycTwo.YOne
