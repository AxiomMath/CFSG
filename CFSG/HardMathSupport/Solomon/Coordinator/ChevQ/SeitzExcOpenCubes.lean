module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Frame
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwLayer
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInner

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh TauCeti

section Generic

variable {G : Type*} [Group G] {p : ℕ}

theorem exists_hyperplane_le_of_relIndex_le (hp : p.Prime) {D E : Subgroup G}
    (h1 : D.relIndex E ≤ p) (hE : Nat.card E = p ^ 3) :
    ∃ F : Subgroup G, F ≤ E ∧ F.relIndex E = p ∧ F ≤ D := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : D.relIndex E ∣ p ^ 3 := hE ▸ Subgroup.relIndex_dvd_card D E
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).1 h2
  have hi1 : i ≤ 1 := by
    by_contra h
    have h3 : p ^ 2 ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
    have h4 : p < p ^ 2 := by
      have := hp.two_le
      nlinarith
    omega
  interval_cases i
  · rw [pow_zero] at hi'
    obtain ⟨F, hFE, hF⟩ := exists_hyperplane_of_card hE
    exact ⟨F, hFE, hF, hFE.trans (Subgroup.relIndex_eq_one.1 hi')⟩
  · rw [pow_one] at hi'
    exact ⟨D ⊓ E, inf_le_right, by rw [Subgroup.inf_relIndex_right, hi'], inf_le_left⟩

theorem exists_hyperplane_le_of_relIndex (hp : p.Prime) {V D E : Subgroup G}
    (hD : D.relIndex V = p) (hEV : E ≤ V) (hE : Nat.card E = p ^ 3) :
    ∃ F : Subgroup G, F ≤ E ∧ F.relIndex E = p ∧ F ≤ D :=
  exists_hyperplane_le_of_relIndex_le hp
    (hD ▸ Subgroup.relIndex_le_of_le_right hEV (by rw [hD]; exact hp.ne_zero)) hE

theorem hyperClosure_le_of_le (hp : p.Prime) {K V E : Subgroup G} (hEV : E ≤ V)
    (hE : Nat.card E = p ^ 3) : hyperClosure p K V ≤ hyperClosure p K E := by
  rw [hyperClosure, Subgroup.closure_le]
  rintro k ⟨hk, D, -, hD, hDk⟩
  obtain ⟨F, hFE, hF, hFD⟩ := exists_hyperplane_le_of_relIndex hp hD hEV hE
  exact Subgroup.subset_closure ⟨hk, F, hFE, hF, fun f hf => hDk f (hFD hf)⟩

theorem HyperGen.of_le (hp : p.Prime) {K V E : Subgroup G} (h : HyperGen p K V) (hEV : E ≤ V)
    (hE : Nat.card E = p ^ 3) : HyperGen p K E :=
  h.trans (hyperClosure_le_of_le hp hEV hE)

theorem frame_factor_le_hyperClosure (hp : p.Prime) {V V₁ V₂ X : Subgroup G}
    (hV : Nat.card V = p ^ 4) (hV₁V : V₁ ≤ V) (hV₂V : V₂ ≤ V) (hV₂c : Nat.card V₂ = p ^ 2)
    (hdisj : Disjoint V₁ V₂) (hcomm : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a)
    (hXV₂ : ∀ g ∈ X, ∀ b ∈ V₂, g * b = b * g) (hpow : ∀ x ∈ V₁, x ^ p = 1)
    (hPG : X ≤ Subgroup.closure {g | g ∈ X ∧ ∃ x ∈ V₁, x ≠ 1 ∧ g * x = x * g}) :
    X ≤ hyperClosure p ⊤ V := by
  haveI := Fact.mk hp
  refine hPG.trans ?_
  rw [Subgroup.closure_le]
  rintro g ⟨hgX, x, hxV, hx1, hgx⟩
  set D : Subgroup G := Subgroup.zpowers x ⊔ V₂ with hD
  have hzx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hpow x hxV) hx1]
  have hzV : Subgroup.zpowers x ≤ V₁ := (Subgroup.zpowers_le).2 hxV
  have hdz : Disjoint (Subgroup.zpowers x) V₂ := hdisj.mono_left hzV
  have hcD : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb =>
    hcomm a (hzV ha) b hb
  have hDc : Nat.card D = p ^ 3 := by
    rw [hD, card_sup_eq_mul_of_commute_disjoint hcD hdz, hzx, hV₂c]
    ring
  have hDV : D ≤ V := sup_le (hzV.trans hV₁V) hV₂V
  have hDi : D.relIndex V = p := by
    have h2 := Subgroup.relIndex_mul_card D V
    rw [inf_of_le_left hDV, hDc, hV] at h2
    have hp0 : 0 < p ^ 3 := pow_pos hp.pos 3
    have : D.relIndex V * p ^ 3 = p * p ^ 3 := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  have hcent : D ≤ Subgroup.centralizer ({g} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Commute.zpow_left (show Commute x g from hgx.symm) n).eq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hXV₂ g hgX b hb).symm
  exact Subgroup.subset_closure ⟨Subgroup.mem_top g, D, hDV, hDi, fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.1 (hcent hf)⟩

theorem hyperGen_of_frame_layer (hp : p.Prime) {V V₁ V₂ X₁ X₂ P : Subgroup G}
    (hV : Nat.card V = p ^ 4) (hV₁V : V₁ ≤ V) (hV₂V : V₂ ≤ V) (hV₁c : Nat.card V₁ = p ^ 2)
    (hV₂c : Nat.card V₂ = p ^ 2) (hdisj : Disjoint V₁ V₂)
    (hcomm : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a) (hpow : ∀ x ∈ V, x ^ p = 1)
    (hX₁V₂ : ∀ g ∈ X₁, ∀ b ∈ V₂, g * b = b * g) (hX₂V₁ : ∀ g ∈ X₂, ∀ b ∈ V₁, g * b = b * g)
    (hPG₁ : X₁ ≤ Subgroup.closure {g | g ∈ X₁ ∧ ∃ x ∈ V₁, x ≠ 1 ∧ g * x = x * g})
    (hPG₂ : X₂ ≤ Subgroup.closure {g | g ∈ X₂ ∧ ∃ x ∈ V₂, x ≠ 1 ∧ g * x = x * g})
    (hclose : ∀ H : Subgroup G, X₁ ⊔ X₂ ≤ H →
      ¬ H ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup G) : Set G) → H = ⊤)
    (hlayer : LeviLayer G p V P)
    (hPX : ¬ P ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup G) : Set G)) :
    HyperGen p ⊤ V := by
  have hX₁ := frame_factor_le_hyperClosure hp hV hV₁V hV₂V hV₂c hdisj hcomm hX₁V₂
    (fun x hx => hpow x (hV₁V hx)) hPG₁
  have hX₂ := frame_factor_le_hyperClosure hp hV hV₂V hV₁V hV₁c hdisj.symm
    (fun a ha b hb => (hcomm b hb a ha).symm) hX₂V₁ (fun x hx => hpow x (hV₂V hx)) hPG₂
  have hP : P ≤ hyperClosure p ⊤ V := hlayer.le_hyperClosure hp hV
  have htop := hclose _ (sup_le hX₁ hX₂) fun hN => hPX (hP.trans hN)
  intro k _
  have hk : k ∈ hyperClosure p ⊤ V := by
    rw [htop]
    exact Subgroup.mem_top k
  exact hk

theorem hyperGen_of_sylowTorus {m : ℕ} (hp : p.Prime) (hS : SylowTorus G p m)
    {V : Subgroup G} (hVel : IsElemAbelian p V) (hVc : Nat.card V = p ^ m)
    (hV : HyperGen p ⊤ V) {E : Subgroup G} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) : HyperGen p ⊤ E := by
  obtain ⟨T, V0, -, hconj, -, hV0tor, hV0el, hV0c⟩ := hS.exists_torus
  obtain ⟨g, hg⟩ := hconj E (isPGroup_of_isElemAbelian hE)
  have hEV0 : E ≤ V0.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := hg hx
    have htp : t ^ p = 1 := by
      have h1 := hE.2 x hx
      rw [← hxt] at h1
      have : (MulAut.conj g) (t ^ p) = 1 := by
        rw [map_pow]
        exact h1
      exact (MulAut.conj g).injective (this.trans (map_one _).symm)
    exact ⟨t, hV0tor t ht htp, hxt⟩
  obtain ⟨x, hx⟩ := exists_conj_of_sylowTorus_cube hp hS hVel hVc hV0el hV0c
  have hV0 : HyperGen p ⊤ V0 := by
    rw [hx]
    exact hyperGen_conj x hV
  exact HyperGen.of_le hp (hyperGen_conj g hV0) hEV0 hEc

theorem hyperGen_of_map_central {X L : Type*} [Group X] [Group L] (hp : p.Prime) (π : X →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X)
    (hcop : ¬ p ∣ Nat.card π.ker) {A : Subgroup X} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hAc : Nat.card A = p ^ 3) (h : HyperGen p ⊤ (A.map π)) : HyperGen p ⊤ A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F₁, hF₁A, hF₁⟩ := exists_hyperplane_of_card hAc
  have hkerM : π.ker ≤ hyperClosure p ⊤ A := fun z hz =>
    Subgroup.subset_closure ⟨Subgroup.mem_top z, F₁, hF₁A, hF₁,
      fun f _ => Subgroup.mem_center_iff.1 (hker hz) f⟩
  have hgen : hyperClosure p ⊤ (A.map π) ≤ (hyperClosure p ⊤ A).map π := by
    rw [hyperClosure, Subgroup.closure_le]
    rintro ℓ ⟨-, F₀, -, hF₀, hF₀ℓ⟩
    obtain ⟨k, rfl⟩ := hπ ℓ
    refine ⟨k, Subgroup.subset_closure ⟨Subgroup.mem_top k, F₀.comap π ⊓ A, inf_le_right, ?_,
      ?_⟩, rfl⟩
    · rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]
      exact hF₀
    · intro f hf
      have hfA : f ∈ A := hf.2
      have hπf : π f * π k = π k * π f := hF₀ℓ (π f) hf.1
      set g : X := (k * f)⁻¹ * (f * k) with hg
      have hgk : g ∈ π.ker := by
        rw [MonoidHom.mem_ker, hg, map_mul, map_inv, map_mul, map_mul, hπf, inv_mul_cancel]
      have hgc : ∀ y : X, y * g = g * y := fun y => Subgroup.mem_center_iff.1 (hker hgk) y
      have hfk : f * k = k * f * g := by rw [hg]; group
      have hgp : g ^ p = 1 :=
        pow_eq_one_of_pow_commute hgc hfk p (by rw [hAp f hfA, one_mul, mul_one])
      have hg1 : g = 1 := by
        by_contra hne
        apply hcop
        have hne' : (⟨g, hgk⟩ : π.ker) ≠ 1 := fun h => hne (congrArg Subtype.val h)
        have hgp' : (⟨g, hgk⟩ : π.ker) ^ p = 1 := Subtype.ext hgp
        rw [← orderOf_eq_prime hgp' hne']
        exact orderOf_dvd_natCard _
      rw [hfk, hg1, mul_one]
  intro x _
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 (hgen (h (Subgroup.mem_top (π x))))
  have hz : m⁻¹ * x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
  have hx : m * (m⁻¹ * x) = x := by group
  rw [← hx]
  exact (hyperClosure p ⊤ A).mul_mem hm (hkerM hz)

theorem hyperGen_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H) {E : Subgroup G}
    (h : HyperGen p ⊤ (E.map e.toMonoidHom)) : HyperGen p ⊤ E := by
  have hAE : (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id E
    ext x
    simp
  have hdis : Disjoint (E.map e.toMonoidHom) e.symm.toMonoidHom.ker := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have h1 : e.symm x = 1 := hx.2
    rw [Subgroup.mem_bot]
    simpa using congrArg e h1
  have hle := map_hyperClosure_le_of_lift (p := p) hAE hdis
  intro x _
  apply hle
  exact ⟨e x, h (Subgroup.mem_top _), by simp⟩

theorem hyperGen_of_two_conj (X P : Subgroup G) (n : G) (hPX : P ≤ X)
    (hPnX : P ≤ X.map (MulAut.conj n).toMonoidHom)
    (hgen : ∀ M : Subgroup G, X ≤ M → X.map (MulAut.conj n).toMonoidHom ≤ M → M = ⊤)
    (hX : ∀ E : Subgroup G, E ≤ X → IsElemAbelian p E → Nat.card E = p ^ 3 →
      X ≤ hyperClosure p ⊤ E)
    {E₀ : Subgroup G} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3)
    (hconj : ∃ g : G, E₀.map (MulAut.conj g).toMonoidHom ≤ P) : HyperGen p ⊤ E₀ := by
  obtain ⟨g, hg⟩ := hconj
  set E := E₀.map (MulAut.conj g).toMonoidHom with hEdef
  have hEa : IsElemAbelian p E :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀ _
  have hEc : Nat.card E = p ^ 3 := by
    rw [hEdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hc]
  have h1 : X ≤ hyperClosure p ⊤ E := hX E (hg.trans hPX) hEa hEc
  set E' := E.map (MulAut.conj n⁻¹).toMonoidHom with hE'def
  have hE'X : E' ≤ X := by
    have := Subgroup.map_mono (f := (MulAut.conj n⁻¹).toMonoidHom) (hg.trans hPnX)
    rwa [map_conj_map_conj_inv] at this
  have hE'a : IsElemAbelian p E' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEa _
  have hE'c : Nat.card E' = p ^ 3 := by
    rw [hE'def, Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective, hEc]
  have h2 : X ≤ hyperClosure p ⊤ E' := hX E' hE'X hE'a hE'c
  have hE'n : E'.map (MulAut.conj n).toMonoidHom = E := by
    have := map_conj_map_conj_inv n⁻¹ E
    rwa [inv_inv] at this
  have h3 : X.map (MulAut.conj n).toMonoidHom ≤ hyperClosure p ⊤ E := by
    refine (Subgroup.map_mono h2).trans ?_
    have h4 := map_hyperClosure_le (p := p) (⊤ : Subgroup G) E' n
    rwa [hE'n] at h4
  have htop := hgen _ h1 h3
  have hE : HyperGen p ⊤ E := by
    intro k _
    show k ∈ hyperClosure p ⊤ E
    rw [htop]
    exact Subgroup.mem_top k
  have h5 := hyperGen_conj g⁻¹ hE
  have hE₀' : E.map (MulAut.conj g⁻¹).toMonoidHom = E₀ := map_conj_map_conj_inv g E₀
  rwa [hE₀'] at h5

theorem range_le_hyperClosure_of_hom {X : Type*} [Group X] [Finite X] (hp : p.Prime)
    (hcube : ∀ E : Subgroup X, IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    (Ψ : X →* G) (hΨcop : ¬ p ∣ Nat.card Ψ.ker) {E : Subgroup G} (hE : E ≤ Ψ.range)
    (hEa : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) : Ψ.range ≤ hyperClosure p ⊤ E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Ψ' : X →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEa.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEa.2 x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 3 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  have hcardE' : Nat.card E' = p ^ 3 := by
    rw [← card_map_eq_of_disjoint_ker Ψ' hdisE', hmapE', hcardE1]
  have hE' : HyperGen p ⊤ E' := hcube E' hE'ea hcardE'
  have hmapE : E'.map Ψ = E := by
    have h1 : E'.map Ψ = (E'.map Ψ').map Ψ.range.subtype := by
      rw [Subgroup.map_map]
      rfl
    rw [h1, hmapE', hE1def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hE]
  have hdisΨ : Disjoint E' Ψ.ker := hΨ'ker ▸ hdisE'
  rw [MonoidHom.range_eq_map]
  exact (Subgroup.map_mono hE').trans (map_hyperClosure_le_of_lift (p := p) hmapE hdisΨ)

theorem cubes_of_central_quotient {X L : Type*} [Group X] [Group L] [Finite X] (hp : p.Prime)
    (π : X →* L) (hπ : Function.Surjective π) (hπk : π.ker ≤ Subgroup.center X)
    (hπcop : ¬ p ∣ Nat.card π.ker)
    (hcube : ∀ E : Subgroup L, IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    (E : Subgroup X) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) : HyperGen p ⊤ E := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEbarea : IsElemAbelian p (E.map π) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE π
  have hcardEbar : Nat.card (E.map π) = p ^ 3 := by
    rw [card_map_eq_of_disjoint_ker π
      (CFSG.HardMathSupport.Lang.AnisoF4.disjoint_ker_of_exponent π hπcop hE.2), hEc]
  exact hyperGen_of_map_central hp π hπ hπk hπcop hE.2 hEc (hcube _ hEbarea hcardEbar)

theorem range_le_hyperClosure_of_cover {X L : Type*} [Group X] [Group L] [Finite X]
    (hp : p.Prime) (π : X →* L) (hπ : Function.Surjective π) (hπk : π.ker ≤ Subgroup.center X)
    (hπcop : ¬ p ∣ Nat.card π.ker)
    (hcube : ∀ E : Subgroup L, IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    (Ψ : X →* G) (hΨcop : ¬ p ∣ Nat.card Ψ.ker) {E : Subgroup G} (hE : E ≤ Ψ.range)
    (hEa : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) : Ψ.range ≤ hyperClosure p ⊤ E :=
  range_le_hyperClosure_of_hom hp (cubes_of_central_quotient hp π hπ hπk hπcop hcube) Ψ hΨcop
    hE hEa hEc

theorem hyperGen_prod {A B : Type*} [Group A] [Group B] (hp : p.Prime)
    (hA : ∀ F : Subgroup A, IsElemAbelian p F → Nat.card F ≤ p)
    (hBcube : ∀ E : Subgroup B, IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    (hBplane : ∀ E : Subgroup B, IsElemAbelian p E → Nat.card E = p ^ 2 →
      Subgroup.closure {h | ∃ x ∈ E, x ≠ 1 ∧ Commute h x} = ⊤)
    {E : Subgroup (A × B)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) :
    HyperGen p ⊤ E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hE₁ : IsElemAbelian p (E.map (MonoidHom.fst A B)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hE₂ : IsElemAbelian p (E.map (MonoidHom.snd A B)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hAH : ∀ a : A, ((a, 1) : A × B) ∈ hyperClosure p ⊤ E := by
    intro a
    have hle : ((⊥ : Subgroup A).comap (MonoidHom.fst A B)).relIndex E ≤ p := by
      rw [Subgroup.relIndex_comap, Subgroup.relIndex_bot_left]
      exact hA _ hE₁
    obtain ⟨F, hFE, hF, hFD⟩ := exists_hyperplane_le_of_relIndex_le hp hle hEc
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, F, hFE, hF, fun f hf => ?_⟩
    have h1 : f.1 = 1 := by
      have := hFD hf
      rwa [Subgroup.mem_comap, Subgroup.mem_bot] at this
    ext
    · simp [h1]
    · simp
  have hker : Nat.card ((⊥ : Subgroup B).comap (MonoidHom.snd A B) ⊓ E : Subgroup (A × B)) ≤ p := by
    set N := ((⊥ : Subgroup B).comap (MonoidHom.snd A B) ⊓ E : Subgroup (A × B)) with hN
    have hdis : Disjoint N (MonoidHom.fst A B).ker := by
      rw [Subgroup.disjoint_def]
      intro x hx hx1
      have h2 : x.2 = 1 := by
        have h3 : x ∈ (⊥ : Subgroup B).comap (MonoidHom.snd A B) := hx.1
        rwa [Subgroup.mem_comap, Subgroup.mem_bot] at h3
      have h1 : x.1 = 1 := hx1
      exact Prod.ext h1 h2
    have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hNa : IsElemAbelian p N :=
      ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hEcomm a.1 a.2.2 b.1 b.2.2),
       fun x hx => hE.2 x hx.2⟩
    rw [← card_map_eq_of_disjoint_ker _ hdis]
    exact hA _ (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hNa _)
  have hidx : ((⊥ : Subgroup B).comap (MonoidHom.snd A B)).relIndex E *
      Nat.card ((⊥ : Subgroup B).comap (MonoidHom.snd A B) ⊓ E : Subgroup (A × B)) = p ^ 3 :=
    hEc ▸ Subgroup.relIndex_mul_card _ _
  rw [Subgroup.relIndex_comap, Subgroup.relIndex_bot_left] at hidx
  have hE₂c : Nat.card (E.map (MonoidHom.snd A B)) = p ^ 3 ∨
      Nat.card (E.map (MonoidHom.snd A B)) = p ^ 2 := by
    have hd : Nat.card ((⊥ : Subgroup B).comap (MonoidHom.snd A B) ⊓ E : Subgroup (A × B)) ∣
        p ^ 3 := Dvd.intro_left _ hidx
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).1 hd
    have hi1 : i ≤ 1 := by
      by_contra h
      have h3 : p ^ 2 ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
      have h4 : p < p ^ 2 := by
        have := hp.two_le
        nlinarith
      omega
    interval_cases i
    · left
      rw [hi', pow_zero, mul_one] at hidx
      exact hidx
    · right
      rw [hi', pow_one] at hidx
      have : Nat.card (E.map (MonoidHom.snd A B)) * p = p ^ 2 * p := by rw [hidx]; ring
      exact Nat.eq_of_mul_eq_mul_right hp.pos this
  have hBH : ∀ b : B, ((1, b) : A × B) ∈ hyperClosure p ⊤ E := by
    have key : ∀ S : Set B, (Subgroup.closure S = ⊤) →
        (∀ k ∈ S, ((1, k) : A × B) ∈ hyperClosure p ⊤ E) →
        ∀ b : B, ((1, b) : A × B) ∈ hyperClosure p ⊤ E := by
      intro S hS hSk b
      have hle : Subgroup.closure S ≤ (hyperClosure p ⊤ E).comap (MonoidHom.inr A B) := by
        rw [Subgroup.closure_le]
        intro k hk
        exact hSk k hk
      have hb : b ∈ Subgroup.closure S := by
        rw [hS]
        exact Subgroup.mem_top b
      exact hle hb
    rcases hE₂c with h3 | h2
    · refine key {k | k ∈ (⊤ : Subgroup B) ∧ ∃ F : Subgroup B, F ≤ E.map (MonoidHom.snd A B) ∧
        F.relIndex (E.map (MonoidHom.snd A B)) = p ∧ ∀ f ∈ F, f * k = k * f}
        (eq_top_iff.2 (hBcube _ hE₂ h3)) ?_
      rintro k ⟨-, F₂, -, hF₂, hF₂k⟩
      refine Subgroup.subset_closure ⟨Subgroup.mem_top _, F₂.comap (MonoidHom.snd A B) ⊓ E,
        inf_le_right, ?_, ?_⟩
      · rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]
        exact hF₂
      · intro f hf
        have h1 : f.2 * k = k * f.2 := hF₂k f.2 hf.1
        ext
        · simp
        · simp [h1]
    · refine key {k | ∃ x ∈ E.map (MonoidHom.snd A B), x ≠ 1 ∧ Commute k x}
        (hBplane _ hE₂ h2) ?_
      rintro k ⟨x, hx, hx1, hkx⟩
      have hzx : Subgroup.zpowers x ≤ E.map (MonoidHom.snd A B) := (Subgroup.zpowers_le).2 hx
      have hzc : Nat.card (Subgroup.zpowers x) = p := by
        rw [Nat.card_zpowers, orderOf_eq_prime (hE₂.2 x hx) hx1]
      have hrel : (Subgroup.zpowers x).relIndex (E.map (MonoidHom.snd A B)) = p := by
        have h5 := Subgroup.relIndex_mul_card (Subgroup.zpowers x) (E.map (MonoidHom.snd A B))
        rw [inf_of_le_left hzx, hzc, h2] at h5
        have : (Subgroup.zpowers x).relIndex (E.map (MonoidHom.snd A B)) * p = p * p := by
          rw [h5]; ring
        exact Nat.eq_of_mul_eq_mul_right hp.pos this
      refine Subgroup.subset_closure ⟨Subgroup.mem_top _,
        (Subgroup.zpowers x).comap (MonoidHom.snd A B) ⊓ E, inf_le_right, ?_, ?_⟩
      · rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]
        exact hrel
      · intro f hf
        have hf2 : f.2 ∈ Subgroup.zpowers x := hf.1
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hf2
        have h1 : f.2 * k = k * f.2 := by
          rw [← hn]
          exact ((Commute.zpow_left hkx.symm n)).eq
        ext
        · simp
        · simp [h1]
  intro g _
  have hg : g = ((g.1, 1) : A × B) * ((1, g.2) : A × B) := by ext <;> simp
  rw [hg]
  exact (hyperClosure p ⊤ E).mul_mem (hAH g.1) (hBH g.2)

theorem hyperGen_prod_comm {A B : Type*} [CommGroup A] [Group B] (hp : p.Prime)
    (hBcube : ∀ E : Subgroup B, IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    (hBplane : ∀ E : Subgroup B, IsElemAbelian p E → Nat.card E = p ^ 2 →
      Subgroup.closure {h | ∃ x ∈ E, x ≠ 1 ∧ Commute h x} = ⊤)
    {E : Subgroup (A × B)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) :
    HyperGen p ⊤ E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hE₂ : IsElemAbelian p (E.map (MonoidHom.snd A B)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hAH : ∀ a : A, ((a, 1) : A × B) ∈ hyperClosure p ⊤ E := by
    intro a
    obtain ⟨F, hFE, hF⟩ := exists_hyperplane_of_card hEc
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, F, hFE, hF, fun f _ => ?_⟩
    ext
    · simp [mul_comm]
    · simp
  have hidx : ((⊥ : Subgroup B).comap (MonoidHom.snd A B)).relIndex E =
      Nat.card (E.map (MonoidHom.snd A B)) := by
    rw [Subgroup.relIndex_comap, Subgroup.relIndex_bot_left]
  have key : ∀ S : Set B, (Subgroup.closure S = ⊤) →
      (∀ k ∈ S, ((1, k) : A × B) ∈ hyperClosure p ⊤ E) →
      ∀ b : B, ((1, b) : A × B) ∈ hyperClosure p ⊤ E := by
    intro S hS hSk b
    have hle : Subgroup.closure S ≤ (hyperClosure p ⊤ E).comap (MonoidHom.inr A B) := by
      rw [Subgroup.closure_le]
      intro k hk
      exact hSk k hk
    have hb : b ∈ Subgroup.closure S := by
      rw [hS]
      exact Subgroup.mem_top b
    exact hle hb
  have hBH : ∀ b : B, ((1, b) : A × B) ∈ hyperClosure p ⊤ E := by
    by_cases hsmall : Nat.card (E.map (MonoidHom.snd A B)) ≤ p
    ·
      intro b
      obtain ⟨F, hFE, hF, hFD⟩ := exists_hyperplane_le_of_relIndex_le hp (hidx ▸ hsmall) hEc
      refine Subgroup.subset_closure ⟨Subgroup.mem_top _, F, hFE, hF, fun f hf => ?_⟩
      have h2 : f.2 = 1 := by
        have h3 := hFD hf
        rwa [Subgroup.mem_comap, Subgroup.mem_bot] at h3
      ext
      · simp
      · simp [h2]
    · have hd : Nat.card (E.map (MonoidHom.snd A B)) ∣ p ^ 3 := by
        rw [← hidx, ← hEc]
        exact Subgroup.relIndex_dvd_card _ _
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).1 hd
      have hi2 : 2 ≤ i := by
        by_contra h
        interval_cases i
        · rw [hi', pow_zero] at hsmall
          exact hsmall (by have := hp.two_le; omega)
        · rw [hi', pow_one] at hsmall
          exact hsmall le_rfl
      interval_cases i
      ·
        refine key {k | ∃ x ∈ E.map (MonoidHom.snd A B), x ≠ 1 ∧ Commute k x}
          (hBplane _ hE₂ hi') ?_
        rintro k ⟨x, hx, hx1, hkx⟩
        have hzx : Subgroup.zpowers x ≤ E.map (MonoidHom.snd A B) := (Subgroup.zpowers_le).2 hx
        have hzc : Nat.card (Subgroup.zpowers x) = p := by
          rw [Nat.card_zpowers, orderOf_eq_prime (hE₂.2 x hx) hx1]
        have hrel : (Subgroup.zpowers x).relIndex (E.map (MonoidHom.snd A B)) = p := by
          have h5 := Subgroup.relIndex_mul_card (Subgroup.zpowers x) (E.map (MonoidHom.snd A B))
          rw [inf_of_le_left hzx, hzc, hi'] at h5
          have : (Subgroup.zpowers x).relIndex (E.map (MonoidHom.snd A B)) * p = p * p := by
            rw [h5]; ring
          exact Nat.eq_of_mul_eq_mul_right hp.pos this
        refine Subgroup.subset_closure ⟨Subgroup.mem_top _,
          (Subgroup.zpowers x).comap (MonoidHom.snd A B) ⊓ E, inf_le_right, ?_, ?_⟩
        · rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]
          exact hrel
        · intro f hf
          have hf2 : f.2 ∈ Subgroup.zpowers x := hf.1
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hf2
          have h1 : f.2 * k = k * f.2 := by
            rw [← hn]
            exact ((Commute.zpow_left hkx.symm n)).eq
          ext
          · simp
          · simp [h1]
      ·
        refine key {k | k ∈ (⊤ : Subgroup B) ∧ ∃ F : Subgroup B,
          F ≤ E.map (MonoidHom.snd A B) ∧ F.relIndex (E.map (MonoidHom.snd A B)) = p ∧
            ∀ f ∈ F, f * k = k * f} (eq_top_iff.2 (hBcube _ hE₂ hi')) ?_
        rintro k ⟨-, F₂, -, hF₂, hF₂k⟩
        refine Subgroup.subset_closure ⟨Subgroup.mem_top _, F₂.comap (MonoidHom.snd A B) ⊓ E,
          inf_le_right, ?_, ?_⟩
        · rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]
          exact hF₂
        · intro f hf
          have h1 : f.2 * k = k * f.2 := hF₂k f.2 hf.1
          ext
          · simp
          · simp [h1]
  intro g _
  have hg : g = ((g.1, 1) : A × B) * ((1, g.2) : A × B) := by ext <;> simp
  rw [hg]
  exact (hyperClosure p ⊤ E).mul_mem (hAH g.1) (hBH g.2)

theorem hyperGen_of_two_covers {H₁ H₂ : Type*} [Group H₁] [Group H₂] [Finite H₁] [Finite H₂]
    (hp : p.Prime) (ψ₁ : H₁ →* G) (ψ₂ : H₂ →* G) (hk₁ : ¬ p ∣ Nat.card ψ₁.ker)
    (hk₂ : ¬ p ∣ Nat.card ψ₂.ker)
    (h₁ : ∀ F : Subgroup H₁, IsElemAbelian p F → Nat.card F = p ^ 3 → HyperGen p ⊤ F)
    (h₂ : ∀ F : Subgroup H₂, IsElemAbelian p F → Nat.card F = p ^ 3 → HyperGen p ⊤ F)
    (hclose : ∀ M : Subgroup G, ψ₁.range ≤ M → ψ₂.range ≤ M → M = ⊤)
    (P : Subgroup G) (hP₁ : P ≤ ψ₁.range) (hP₂ : P ≤ ψ₂.range) {E₀ : Subgroup G}
    (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3)
    (hconj : ∃ g : G, E₀.map (MulAut.conj g).toMonoidHom ≤ P) : HyperGen p ⊤ E₀ := by
  obtain ⟨g, hg⟩ := hconj
  set E := E₀.map (MulAut.conj g).toMonoidHom with hEdef
  have hEa : IsElemAbelian p E :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀ _
  have hEc : Nat.card E = p ^ 3 := by
    rw [hEdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hc]
  have htop := hclose _ (range_le_hyperClosure_of_hom hp h₁ ψ₁ hk₁ (hg.trans hP₁) hEa hEc)
    (range_le_hyperClosure_of_hom hp h₂ ψ₂ hk₂ (hg.trans hP₂) hEa hEc)
  have hE : HyperGen p ⊤ E := by
    intro k _
    show k ∈ hyperClosure p ⊤ E
    rw [htop]
    exact Subgroup.mem_top k
  have h5 := hyperGen_conj g⁻¹ hE
  have hE₀' : E.map (MulAut.conj g⁻¹).toMonoidHom = E₀ := map_conj_map_conj_inv g E₀
  rwa [hE₀'] at h5

end Generic

section Models

open CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.CTP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem hyperGen_statedProj_quadPlus {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) (h4 : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p))
    (hn : 3 ≤ n) (E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))))
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) : HyperGen p ⊤ E := by
  obtain ⟨V, _, _, _, Q, π, hπ⟩ := orthCover_plus (K := K) hn
    (MulEquiv.refl (StatedProj (StatedOmega (StatedQuadPlus n K))))
  exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux.hyperGen_of_orderOf_ge_four
    hπ hp hp2 (ExcHigh.natCast_ne_zero_of_not_dvd_card hp hpK) h4 hE hEc

theorem hyperGen_statedProj_sp {K : Type} [Field K] [Finite K] {p r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hr : 1 ≤ r) (hq : ¬ (p = 3 ∧ Nat.card K = 2))
    (E : Subgroup (StatedProj (StatedSp r K))) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) : HyperGen p ⊤ E := by
  classical
  by_cases h : ∃ W : Submodule K (Fin r ⊕ Fin r → K), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0) ∧
      ∀ g : StatedSp r K, proj r K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W
  · obtain ⟨W, hW0, hWiso, hWstab⟩ := h
    exact hyperGen_top_of_isotropic hp hp2 hpK hr hE hEc hW0 hWiso hWstab
  · refine hyperGen_top_of_aniso hp hp2 hpK hr hq hE hEc fun W hiso hstab => ?_
    by_contra hne
    exact h ⟨W, hne, hiso, hstab⟩

end Models

section E8

set_option linter.unusedSectionVars false

theorem exists_hyperGen_of_frame_E8 {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (hfr : E8FrameData q hv p)
    (hlay : ∀ V : Subgroup (Cat ⟨.E8 q, hv⟩), IsElemAbelian p V → Nat.card V = p ^ 4 →
      ∃ P : Subgroup (Cat ⟨.E8 q, hv⟩), LeviLayer _ p V P ∧ CFSG.Open.IsQuasisimple ↥P ∧
        ordTrialityD4 q.card ^ 2 < Nat.card ↥P) :
    ∃ V : Subgroup (Cat ⟨.E8 q, hv⟩), IsElemAbelian p V ∧ Nat.card V = p ^ 4 ∧
      HyperGen p ⊤ V := by
  obtain ⟨V₁, V₂, X₁, X₂, hV₁, hV₂, hV₁c, hV₂c, hdisj, hcomm, -, -, hXc, hX₁V₂, hX₂V₁,
    hPG₁, hPG₂, hXb₁, hXb₂, hclose, hsolv⟩ := hfr
  have hVel : IsElemAbelian p (V₁ ⊔ V₂) := isElemAbelian_sup_of_commute hV₁ hV₂ hcomm
  have hVc : Nat.card ↥(V₁ ⊔ V₂) = p ^ 4 := by
    rw [card_sup_eq_mul_of_commute_disjoint hcomm hdisj, hV₁c, hV₂c]
    ring
  obtain ⟨P, hlayer, hQS, hPbig⟩ := hlay (V₁ ⊔ V₂) hVel hVc
  haveI : Finite (Cat ⟨.E8 q, hv⟩) :=
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.finite_isSimpleGroup_cat_E8 hv).1
  have hXlt : Nat.card ↥(X₁ ⊔ X₂) < Nat.card ↥P := by
    have h1 := natCard_sup_le_mul_of_commute hXc
    have h2 : Nat.card ↥X₁ * Nat.card ↥X₂ ≤ ordTrialityD4 q.card ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul hXb₁ hXb₂
    exact lt_of_le_of_lt (h1.trans h2) hPbig
  have hPX := not_le_normalizer_of_isQuasisimple hQS hsolv hXlt
  exact ⟨V₁ ⊔ V₂, hVel, hVc, hyperGen_of_frame_layer hp hVc le_sup_left le_sup_right hV₁c hV₂c
    hdisj hcomm (fun x hx => hVel.2 x hx) hX₁V₂ hX₂V₁ hPG₁ hPG₂ hclose hlayer hPX⟩

theorem hyperGen_E8_three {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p) (h3 : orderOf ((q.card : ℕ) : ZMod p) = 3)
    {E₀ : Subgroup (Cat ⟨.E8 q, hv⟩)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3) :
    HyperGen p ⊤ E₀ := by
  have h7 := seven_le_of_orderOf_three hp hp5 h3
  obtain ⟨V, hVel, hVc, hV⟩ := exists_hyperGen_of_frame_E8 hv hp
    (e8FrameFactors_three q hv p hp h7 hpq h3)
    (fun V hV hVc => e8LeviPiece_three_of_layer E8Layer.e8E6LayerInput_proved q hv p hp h7 hpq h3
      V hV hVc)
  exact hyperGen_of_sylowTorus hp (sylowTorus_cat_E8_three hv hp h7 hpq h3) hVel hVc hV hE₀ hc

theorem hyperGen_E8_six {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (hpq : p ≠ q.p) (h6 : orderOf ((q.card : ℕ) : ZMod p) = 6)
    {E₀ : Subgroup (Cat ⟨.E8 q, hv⟩)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3) :
    HyperGen p ⊤ E₀ := by
  have h7 := seven_le_of_orderOf_six hp h6
  obtain ⟨V, hVel, hVc, hV⟩ := exists_hyperGen_of_frame_E8 hv hp
    (e8FrameFactors_six q hv p hp h7 hpq h6)
    (fun V hV hVc => e8LeviPiece_six_proved
      (E8Layer6.e8E6LayerInput6_of_twE8SCLayer E8Tw.twE8SCLayer_holds) q hv p hp h7 hpq h6
      V hV hVc)
  exact hyperGen_of_sylowTorus hp (sylowTorus_cat_E8_six hv hp h7 hpq h6) hVel hVc hV hE₀ hc

section Four

open CFSG.ComponentClassification CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut

theorem iSup_d8Chain_le_hyperClosure {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq1 : ¬ p ∣ Nat.card K - 1)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 8 K))),
      IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    (Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K)))
    (hrange : Ψ.range = ⨆ k, e8D8Chain K k)
    (E : Subgroup (adjointGroup .E8 K)) (hE : E ≤ ⨆ k, e8D8Chain K k)
    (hEa : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) :
    ⨆ k, e8D8Chain K k ≤ hyperClosure p ⊤ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hn3 : 3 ≤ 8 := by norm_num
  have : Nonempty (Fin 8 ⊕ Fin 8) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 8 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 8) (K := K) hn3
  set π := spinToStatedProj (quadPlus 8 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 8 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    rw [hZ]
    exact hcen
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := fun hd =>
    hcen (hd.trans (Subgroup.card_dvd_of_le hker))
  rw [← hrange]
  exact range_le_hyperClosure_of_cover hp π hπsurj hZ.le hπcop hcube Ψ hΨcop (hrange ▸ hE) hEa
    hEc

theorem e8FourSylow_exp (K : Type) [Field K] [Finite K] (p : ℕ) [hpF : Fact p.Prime]
    (h7 : 7 ≤ p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) :
    ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8D4Group K := by
  have hn3 : 3 ≤ 4 := by norm_num
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 4 K)) := finite_spinGroup_quadPlus_four K
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq2 : 2 ≤ Nat.card K :=
    Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.2 inferInstance)
  have hp2 : p ≠ 2 := by omega
  have hpq1 : ¬ p ∣ Nat.card K - 1 := not_dvd_pred_of_orderOf_eq_four hpF.out hq1 he
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D4_E8 K
  set w := weylWordElt .E8 K e8D4Word with hw
  set Ψ' : spinGroup (quadPlus 4 K) →* adjointGroup .E8 K :=
    (MulAut.conj w).toMonoidHom.comp Ψ with hΨ'
  have hΨ'range : Ψ'.range = e8D4Perp K := by
    rw [hΨ', MonoidHom.range_comp, hrange]
    rfl
  let ρ : Fin 2 → spinGroup (quadPlus 4 K) →* adjointGroup .E8 K := ![Ψ, Ψ']
  have hρk : ∀ i, (ρ i).ker ≤ Subgroup.center (spinGroup (quadPlus 4 K)) := by
    intro i
    fin_cases i
    · exact hker
    · intro x hx
      apply hker
      have h1 : (MulAut.conj w).toMonoidHom (Ψ x) = 1 := hx
      exact (MulAut.conj w).injective (h1.trans (map_one (MulAut.conj w)).symm)
  have hmemL : ∀ x, Ψ x ∈ e8D4Levi K := fun x => hrange ▸ ⟨x, rfl⟩
  have hmemP : ∀ x, Ψ' x ∈ e8D4Perp K := fun x => hΨ'range ▸ ⟨x, rfl⟩
  have hρc : Pairwise fun i j => ∀ x y, Commute (ρ i x) (ρ j y) := by
    intro i j hij x y
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact e8D4Levi_commute_perp _ (hmemL x) _ (hmemP y)
    · exact (e8D4Levi_commute_perp _ (hmemL y) _ (hmemP x)).symm
    · exact absurd rfl hij
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 4) (K := K) hn3
  set π := spinToStatedProj (quadPlus 4 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 4 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 4 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadPlus 4 K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadPlus hn3).commutator_eq_top
  have hcard : Nat.card (spinGroup (quadPlus 4 K)) =
      Nat.card (StatedProj (StatedOmega (StatedQuadPlus 4 K))) *
        Nat.card (Subgroup.center (spinGroup (quadPlus 4 K))) := by
    have e := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπsurj).toEquiv
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [e, hZ] at h
    exact h
  have hord : (Nat.card (adjointGroup .E8 K)).factorization p ≤
      2 * (Nat.card (spinGroup (quadPlus 4 K))).factorization p := by
    rw [factorization_card_E8_of_orderOf_eq_four hpF.out h7 he]
    have h1 := factorization_ordPOmegaPlus4_eq hpF.out hq2 he
    have h2 := factorization_ordPOmegaPlus4_le_card_proj (K := K) hpF.out h7 he
    have h3 : (Nat.card (StatedProj (StatedOmega (StatedQuadPlus 4 K)))).factorization p ≤
        (Nat.card (spinGroup (quadPlus 4 K))).factorization p :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (Dvd.intro _ hcard.symm) p
    omega
  obtain ⟨Q, -, hQ⟩ := exists_conj_le_frame_sylow_of_perfect ρ hρk hρc hperf hcen hord
  obtain ⟨g, hg⟩ := hQ E₀ hE₀p
  refine ⟨g, hg.trans ((map_noncommPiCoprod_le_iSup_range ρ hρc Q).trans ?_)⟩
  refine iSup_le fun i => ?_
  fin_cases i
  · exact (hrange.le.trans le_sup_left).trans e8D4Levi_sup_perp_le
  · exact (hΨ'range.le.trans le_sup_right).trans e8D4Levi_sup_perp_le

theorem hyperGen_adjoint_E8_four (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h7 : 7 ≤ p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    {E₀ : Subgroup (adjointGroup .E8 K)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3) :
    HyperGen p ⊤ E₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpK := not_dvd_of_orderOf_eq_four hp he
  have hpq1 := not_dvd_pred_of_orderOf_eq_four hp hq1 he
  exact hyperGen_of_two_conj (⨆ k, e8D8Chain K k) (e8D4Group K) (weylWordElt .E8 K e8Word)
    e8D4Group_le_d8 e8D4Group_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEa hEc => iSup_d8Chain_le_hyperClosure hp (by omega) hpq1
      (fun E' hE' hE'c => hyperGen_statedProj_quadPlus hp (by omega) hpK (by rw [he])
        (by norm_num) E' hE' hE'c)
      Ψ hker hrange E hE hEa hEc)
    hE₀ hc (e8FourSylow_exp K p h7 he E₀ hE₀.2)

theorem hyperGen_E8_four {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (h4 : orderOf ((q.card : ℕ) : ZMod p) = 4)
    {E₀ : Subgroup (Cat ⟨.E8 q, hv⟩)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3) :
    HyperGen p ⊤ E₀ := by
  obtain ⟨K, _, _, hKq, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have he : orderOf ((Nat.card K : ℕ) : ZMod p) = 4 := by
    rw [hKq]
    exact h4
  refine hyperGen_of_mulEquiv e ?_
  exact hyperGen_adjoint_E8_four K hp h7 he
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.injective, hc])

end Four

section Two

open scoped MatrixGroups
open CFSG.ComponentClassification CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut

theorem e8Two_conj_frame (K : Type) [Field K] [Finite K] (p : ℕ) [hpF : Fact p.Prime]
    (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K + 1) (E₀ : Subgroup (adjointGroup .E8 K))
    (hE₀p : ∀ x ∈ E₀, x ^ p = 1) :
    ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8FrameGroup K := by
  obtain ⟨ρ, hρi, hρr, hρc⟩ := e8Frame_hom (K := K)
  have hcomm : Pairwise fun i j => ∀ x y : SL(2, K), Commute (ρ i x) (ρ j y) := by
    intro i j hij x y
    exact hρc i j hij x y
  obtain ⟨Q, -, hQ⟩ := exists_conj_le_frame_sylow ρ hρi hcomm (by omega) hpq
    (by rw [factorization_card_E8_of_dvd_add_one hpF.out hp11 hpq])
  obtain ⟨g, hg⟩ := hQ E₀ hE₀p
  refine ⟨g, hg.trans ((map_noncommPiCoprod_le ρ hcomm Q).trans ?_)⟩
  simp only [e8FrameGroup, hρr]
  exact le_rfl

theorem hyperGen_adjoint_E8_two (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 8 K))),
      IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    {E₀ : Subgroup (adjointGroup .E8 K)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3) :
    HyperGen p ⊤ E₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  exact hyperGen_of_two_conj (⨆ k, e8D8Chain K k) (e8FrameGroup K) (weylWordElt .E8 K e8Word)
    e8FrameGroup_le_d8 e8FrameGroup_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEa hEc => iSup_d8Chain_le_hyperClosure hp (by omega) hpq1 hcube Ψ hker hrange E
      hE hEa hEc)
    hE₀ hc (e8Two_conj_frame K p hp11 hpq E₀ hE₀.2)

theorem hyperGen_E8_two {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) (h2 : orderOf ((q.card : ℕ) : ZMod p) = 2)
    (hcube : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card →
      ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 8 K))),
        IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    {E₀ : Subgroup (Cat ⟨.E8 q, hv⟩)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3) :
    HyperGen p ⊤ E₀ := by
  obtain ⟨K, _, _, hKq, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hKq]
    exact dvd_add_one_of_orderOf_eq_two hp h2
  refine hyperGen_of_mulEquiv e ?_
  exact hyperGen_adjoint_E8_two K hp hp11 hpq (hcube K hKq)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.injective, hc])

end Two

section E7Two

open scoped MatrixGroups
open CFSG.ComponentClassification CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge
  CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut

theorem e7Two_conj_frame (K : Type) [Field K] [Finite K] (p : ℕ) [hpF : Fact p.Prime]
    (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K + 1) (E₀ : Subgroup (adjointGroup .E7 K))
    (hE₀p : ∀ x ∈ E₀, x ^ p = 1) :
    ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K := by
  obtain ⟨ρ, hρi, hρr, hρc⟩ := e7Frame_hom (K := K)
  have hcomm : Pairwise fun i j => ∀ x y : SL(2, K), Commute (ρ i x) (ρ j y) := by
    intro i j hij x y
    exact hρc i j hij x y
  obtain ⟨Q, -, hQ⟩ := exists_conj_le_frame_sylow ρ hρi hcomm (by omega) hpq
    (by rw [factorization_card_E7_of_dvd_add_one hpF.out hp11 hpq])
  obtain ⟨g, hg⟩ := hQ E₀ hE₀p
  refine ⟨g, hg.trans ((map_noncommPiCoprod_le ρ hcomm Q).trans ?_)⟩
  simp only [e7FrameGroup, hρr]
  exact le_rfl

theorem e7A1D6_le_hyperClosure {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 6 K))),
      IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    (F : Subgroup (adjointGroup .E7 K)) (hF : F ≤ e7A1D6 K) (hFa : IsElemAbelian p F)
    (hFc : Nat.card F = p ^ 3) :
    e7A1D6 K ≤ hyperClosure p ⊤ F := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hpK0 : (p : K) ≠ 0 := ExcHigh.natCast_ne_zero_of_not_dvd_card hp hpK
  have hn3 : 3 ≤ 6 := by norm_num
  have : Nonempty (Fin 6 ⊕ Fin 6) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 6 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D6_E7 K
  obtain ⟨ρ, hρi, hρr⟩ := exists_sl2_hom_rootPairE7 (K := K) isRoot_e7Theta
  have hcentr : e7D6Group K ≤
      Subgroup.centralizer (rootPairE7 K e7Theta : Set (adjointGroup .E7 K)) := by
    refine iSup_le fun k => ?_
    intro y hy x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := e7Theta_orth k
    exact commutes_rootPair_of_noG2 (K := K) noG2_E7 isRoot_e7Theta (isRoot_single _ _)
      h1 h2 h3 h4 h5 x hx y hy
  have hcomm : ∀ (a : SL(2, K)) (t : spinGroup (Spin.quadPlus 6 K)), Commute (ρ a) (Ψ t) := by
    intro a t
    have hx : ρ a ∈ rootPairE7 K e7Theta := hρr ▸ ⟨a, rfl⟩
    have hy : Ψ t ∈ e7D6Group K := hrange ▸ ⟨t, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 (hcentr hy) _ hx
  let ψ : SL(2, K) × spinGroup (Spin.quadPlus 6 K) →* adjointGroup .E7 K :=
    MonoidHom.noncommCoprod ρ Ψ hcomm
  have hrangeψ : ψ.range = e7A1D6 K := by
    rw [MonoidHom.noncommCoprod_range, hρr, hrange, e7A1D6, sup_comm]
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 6) (K := K) hn3
  set π := spinToStatedProj (quadPlus 6 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 6 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 6 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    rw [hZ]
    exact hcen
  have hψker : ¬ p ∣ Nat.card ψ.ker := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
    obtain ⟨⟨a, s⟩, hxk⟩ := x
    have hxk' : ρ a * Ψ s = 1 := hxk
    have hxp : (a, s) ^ p = 1 := by
      have := pow_orderOf_eq_one (⟨(a, s), hxk⟩ : ψ.ker)
      rw [hx] at this
      exact congrArg Subtype.val this
    have hap : a ^ p = 1 := congrArg Prod.fst hxp
    have hsp : s ^ p = 1 := congrArg Prod.snd hxp
    have hacent : a ∈ Subgroup.center SL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro b
      have h1 : ρ a = (Ψ s)⁻¹ := eq_inv_of_mul_eq_one_left hxk'
      have h2 : Commute (ρ b) (ρ a) := by
        rw [h1]
        exact (hcomm b s).inv_right
      apply hρi
      rw [map_mul, map_mul]
      exact h2.eq
    obtain ⟨r, hr, hra⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hacent
    simp only [Fintype.card_fin] at hr
    have ha2 : a * a = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, ← hra, ← map_mul, ← pow_two, hr, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have ha1 : a = 1 := by
      have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
      have hd2 : orderOf a ∣ Nat.gcd 2 p :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rwa [pow_two])) (orderOf_dvd_of_pow_eq_one hap)
      rw [hcop] at hd2
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd2)
    have hΨs : Ψ s = 1 := by
      rw [ha1, map_one, one_mul] at hxk'
      exact hxk'
    have hs1 : s = 1 :=
      eq_one_of_pow_eq_one_of_not_dvd hcen (hker (MonoidHom.mem_ker.2 hΨs)) hsp
    have hx1 : (⟨(a, s), hxk⟩ : ψ.ker) = 1 := Subtype.ext (Prod.ext ha1 hs1)
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hH : ∀ F' : Subgroup (SL(2, K) × spinGroup (Spin.quadPlus 6 K)), IsElemAbelian p F' →
      Nat.card F' = p ^ 3 → HyperGen p ⊤ F' := fun F' hF' hc =>
    hyperGen_prod hp (fun F'' hF'' => card_le_of_isElemAbelian_specialLinear_two hpK0 hF'')
      (cubes_of_central_quotient hp π hπsurj hZ.le hπcop hcube)
      (fun F'' hF'' hc'' => closure_centralizers_spinPlus_plane hp hp5 hpK hpq1 (by norm_num) F''
        hF'' hc'') hF' hc
  rw [← hrangeψ]
  exact range_le_hyperClosure_of_hom hp hH ψ hψker (hrangeψ ▸ hF) hFa hFc

theorem hyperGen_adjoint_E7_two (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 6 K))),
      IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    {E₀ : Subgroup (adjointGroup .E7 K)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3) :
    HyperGen p ⊤ E₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact hyperGen_of_two_conj (e7A1D6 K) (e7FrameGroup K) (weylWordElt .E7 K e7Word)
    e7FrameGroup_le_e7A1D6 e7FrameGroup_le_conj_e7A1D6
    (fun M hX hn => eq_top_of_e7A1D6_le_of_conj_le M hX hn)
    (fun E hE hEa hEc => e7A1D6_le_hyperClosure hp (by omega) hpq hcube E hE hEa hEc)
    hE₀ hc (e7Two_conj_frame K p hp11 hpq E₀ hE₀.2)

theorem hyperGen_E7_two {q : PrimePower} (hv : (LieTypeIndex.E7 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) (h2 : orderOf ((q.card : ℕ) : ZMod p) = 2)
    (hcube : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card →
      ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 6 K))),
        IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    {E₀ : Subgroup (Cat ⟨.E7 q, hv⟩)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3) :
    HyperGen p ⊤ E₀ := by
  obtain ⟨K, _, _, hKq, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hKq]
    exact dvd_add_one_of_orderOf_eq_two hp h2
  refine hyperGen_of_mulEquiv e ?_
  exact hyperGen_adjoint_E7_two K hp hp11 hpq (hcube K hKq)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.injective, hc])

end E7Two

section TwE6Two

open scoped MatrixGroups
open CFSG.LieType.Chevalley.E6GraphLevi CFSG.Timmesfeld Matrix CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.HardMathSupport.Lang.AnisoF4

theorem cubes_unitarySL {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    {σ : K →+* K} (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2)
    (E : Subgroup (unitarySL σ)) (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) :
    HyperGen p ⊤ E := by
  have hU : UnitaryFieldData ℓ f K := ⟨(Fact.out : ℓ.Prime), hf, by rw [hK]; ring⟩
  let e := unitarySLEquivStated hK hσ
  refine hyperGen_of_mulEquiv e ?_
  have hE' : IsElemAbelian p (E.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE e.toMonoidHom
  have hcard' : Nat.card (E.map e.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hc]
  have hcomm : ∀ x ∈ E.map e.toMonoidHom, ∀ y ∈ E.map e.toMonoidHom, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hE'.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux.hyperGen_of_unitary_diag
    (n := 5) hU hp hpq hq2 (MonoidHom.id _) Function.surjective_id
    (fun g hg => ⟨1, by
      have hg1 : g = 1 := hg
      simp [hg1]⟩) hE' hcard'
    (fun x y hx hy => hcomm x hx y hy) (fun x hx => by
      obtain ⟨m, hm⟩ := hpq
      rw [hm, pow_mul, hE'.2 x hx, one_pow])

theorem twE6_su6_cubeCover (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (ℓ f : ℕ)
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (p : ℕ) [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H)
      (ψ : H →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
      ¬ p ∣ Nat.card ψ.ker ∧
      (∀ F : Subgroup H, IsElemAbelian p F → Nat.card F = p ^ 3 → HyperGen p ⊤ F) ∧
      frameTorusGroup σ.toRingHom ⊔ leviRootGroups σ.toRingHom ≤ ψ.range := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hf, hK'⟩
  haveI : CharP K ℓ := hU.charP
  set σ' : K →+* K := σ.toRingHom with hσ'def
  have hσ' : ∀ c, σ' c = c ^ (ℓ ^ f) := hσ
  have hσσ : ∀ c, σ' (σ' c) = c := fun c => by
    rw [hσ', hσ']
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  obtain ⟨c0, hc0⟩ := hU.exists_bar_ne
  have hbar : hU.bar c0 = σ' c0 := by rw [hU.bar_apply, hσ']
  have hε0 : c0 - σ' c0 ≠ 0 := sub_ne_zero.2 (fun h => hc0 (by rw [hbar]; exact h.symm))
  have hε : σ' (c0 - σ' c0) = -(c0 - σ' c0) := by rw [map_sub, hσσ]; ring
  obtain ⟨Ψ, hΨ⟩ := exists_isPsiTw σ' hσσ hε0 hε hℓ (by omega : 1 ≤ 2 * f) hK'
  have hperf : Group.IsPerfect (unitarySL σ') := isPerfect_unitarySL_gen hK hσ'
  have hC0 : (unitarySL σ').map Ψ ≤ graphFixedRootGroup TwistTag.E6 K σ' :=
    map_unitarySL_le_graphFixedRootGroup hΨ σ.surjective hperf
  have hM := orbitRankOneGroup_le_map hΨ hσσ hε0 hε
  let ΨU : unitarySL σ' →* ↥(graphFixedRootGroup TwistTag.E6 K σ') :=
    (Ψ.comp (unitarySL σ').subtype).codRestrict _ fun B => hC0 ⟨B, B.2, rfl⟩
  have hcomm : ∀ (A : SL(2, RingHom.eqLocusField σ' (RingHom.id K))) (B : unitarySL σ'),
      Commute (frameHom σ' 3 A) (ΨU B) := by
    intro A B
    apply Subtype.ext
    exact commute_frameHom_three σ' A (hΨ.range_le ⟨(B : SL(6, K)), rfl⟩)
  have hpq1 : ¬ p ∣ ℓ ^ f := fun hd =>
    hpF.out.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hd).mp hpq))
  refine ⟨SL(2, RingHom.eqLocusField σ' (RingHom.id K)) × unitarySL σ', inferInstance,
    inferInstance, (frameHom σ' 3).noncommCoprod ΨU hcomm, ?_, ?_, ?_⟩
  ·
    refine not_dvd_card_ker_sl2_coprod hpF.out (by omega) (frameHom σ' 3)
      (frameHom_injective σ' 3) ΨU hcomm ?_
    intro B hB hBp
    have hΨB : Ψ (B : SL(6, K)) = 1 := congrArg Subtype.val hB
    obtain ⟨r, hr6, hrB⟩ := hΨ.scalar_of_eq_one _ hΨB
    have hB1 : (B : SL(6, K)) ^ p = 1 := congrArg Subtype.val hBp
    have h1 : (Matrix.scalar (Fin 6) (r ^ p) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [map_pow, ← hrB, ← Matrix.SpecialLinearGroup.coe_pow, hB1,
        Matrix.SpecialLinearGroup.coe_one]
    have hrp : r ^ p = 1 := by
      have := congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M 0 0) h1
      simpa [Matrix.scalar_apply] using this
    have hr1 : r = 1 := by
      have hcop : Nat.Coprime 6 p := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpF.out]
        intro hd
        have h6 := Nat.le_of_dvd (by norm_num) hd
        interval_cases p
        · omega
        · exact absurd hpF.out (by norm_num)
      have := pow_gcd_eq_one.2 ⟨hr6, hrp⟩
      rwa [hcop, pow_one] at this
    apply Subtype.ext
    apply Subtype.ext
    rw [hrB, hr1]
    simp
  ·
    intro F hF hc
    have hpk : ¬ p ∣ Nat.card (RingHom.eqLocusField σ' (RingHom.id K)) := by
      rw [CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hℓ hf hK hσ']
      exact hpq1
    have hpk0 := ExcHigh.natCast_ne_zero_of_not_dvd_card hpF.out hpk
    have hpℓ : p ≠ ℓ := fun h => hpq1 (by rw [h]; exact dvd_pow_self ℓ (by omega))
    have hq2 : ℓ ^ f ≠ 2 := by
      intro h2
      rw [h2] at hpq
      have := Nat.le_of_dvd (by norm_num) hpq
      omega
    exact hyperGen_prod hpF.out
      (fun F' hF' => card_le_of_isElemAbelian_specialLinear_two hpk0 hF')
      (fun F' hF' hc' => cubes_unitarySL hK hf hσ' hpF.out hpq hq2 F' hF' hc')
      (fun F' hF' hc' => unitarySL_planeGen hK hf hσ' hpF.out (by omega) hpℓ (fun _ => hq2) F'
        hF' hc')
      hF hc
  ·
    have hYmem : ∀ y : ↥(graphFixedRootGroup TwistTag.E6 K σ'),
        (y : ModGL TwistTag.E6.tag K) ∈ (unitarySL σ').map Ψ →
          y ∈ ((frameHom σ' 3).noncommCoprod ΨU hcomm).range := by
      rintro y ⟨B, hB, hBy⟩
      refine ⟨(1, ⟨B, hB⟩), ?_⟩
      apply Subtype.ext
      rw [MonoidHom.noncommCoprod_apply]
      simp only [map_one, one_mul]
      exact hBy
    have hM0 := hM orb0 (by decide)
    have hM1 := hM orb1 (by decide)
    have hM2 := hM orbLeaf (by decide)
    unfold frameTorusGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => ?_
      rintro _ ⟨A, rfl⟩
      by_cases hi : i.val ≤ 2
      · exact hYmem _ (frameHom_mem_of_orbit hM0 hM1 hM2 i hi A)
      · have h3 : i = 3 := Fin.ext (by have h := i.2; have h3 : (3 : Fin 4).val = 3 := rfl; omega)
        subst h3
        exact ⟨(A, 1), by rw [MonoidHom.noncommCoprod_apply]; simp⟩
    · rintro _ ⟨pr, rfl⟩
      exact hYmem _ (by rw [coe_torusG]; exact torusAB_mem_of_orbit hM0 hM1 pr.1.2 pr.2.2)
    · intro y hy
      exact hYmem y ((sup_le (sup_le hM0 hM1) hM2) (Subgroup.mem_subgroupOf.1 hy))

theorem twE6_d4_cubeCover (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (ℓ f : ℕ)
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (p : ℕ) [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1)
    (hcube4 : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4
      (RingHom.eqLocusField σ.toRingHom (RingHom.id K))))), IsElemAbelian p E →
        Nat.card E = p ^ 3 → HyperGen p ⊤ E) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H)
      (ψ : H →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
      ¬ p ∣ Nat.card ψ.ker ∧
      (∀ F : Subgroup H, IsElemAbelian p F → Nat.card F = p ^ 3 → HyperGen p ⊤ F) ∧
      frameTorusGroup σ.toRingHom ⊔ centerRootGroup σ.toRingHom ≤ ψ.range := by
  classical
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hkcard : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = ℓ ^ f :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hℓ hf hK hσ'
  obtain ⟨Ψ, hΨker, hΨrange⟩ := exists_psi_d4 hℓ hf σ.toRingHom hkcard
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hpk : ¬ p ∣ Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) := by
    rw [hkcard]
    intro h
    have h1 : p ∣ ℓ ^ f + 1 - ℓ ^ f := Nat.dvd_sub hpq h
    rw [show ℓ ^ f + 1 - ℓ ^ f = 1 by omega] at h1
    exact hpF.out.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpq1 : ¬ p ∣ Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) - 1 := by
    rw [hkcard]
    intro h
    have h1 : p ∣ ℓ ^ f + 1 - (ℓ ^ f - 1) := Nat.dvd_sub hpq h
    rw [show ℓ ^ f + 1 - (ℓ ^ f - 1) = 2 by omega] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  haveI := finite_spinPlus_four (RingHom.eqLocusField σ.toRingHom (RingHom.id K))
  have hcen := not_dvd_card_center_spinPlus_four hpF.out (by omega) hpq1
  have hcomm : ∀ (t : ↥(normOne σ.toRingHom) × ↥(normOne σ.toRingHom))
      (x : spinGroup (Spin.quadPlus 4 (RingHom.eqLocusField σ.toRingHom (RingHom.id K)))),
      Commute (torusG σ.toRingHom t) (Ψ x) := fun t x => by
    have hmem : Ψ x ∈ d4Group σ.toRingHom := by
      rw [d4Group, ← hΨrange]
      exact ⟨x, rfl⟩
    exact torusG_commute_d4Group σ.toRingHom t (Ψ x) hmem
  let ψ := MonoidHom.noncommCoprod (torusG σ.toRingHom) Ψ hcomm
  have hdr : d4Group σ.toRingHom ≤ ψ.range := by
    rw [d4Group, ← hΨrange]
    rintro _ ⟨x, rfl⟩
    refine ⟨(1, x), ?_⟩
    change torusG σ.toRingHom 1 * Ψ x = Ψ x
    rw [map_one, one_mul]
  have htr : (torusG σ.toRingHom).range ≤ ψ.range := by
    rintro _ ⟨t, rfl⟩
    refine ⟨(t, 1), ?_⟩
    change torusG σ.toRingHom t * Ψ 1 = torusG σ.toRingHom t
    rw [map_one, mul_one]
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 4)
    (K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) hn3
  set π := spinToStatedProj (quadPlus 4 (RingHom.eqLocusField σ.toRingHom (RingHom.id K)))
    (range_spinMatrix_quadPlus hn3) with hπdef
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    rw [hZ]
    exact hcen
  refine ⟨_, inferInstance, inferInstance, ψ, ?_, ?_, ?_⟩
  · exact not_dvd_card_ker_noncommCoprod_tw hpF.out _ _ hcomm
      (not_dvd_card_ker_torusG σ.toRingHom hpF.out (by omega)) hΨker hcen
  · intro F hF hc
    exact hyperGen_prod_comm hpF.out (cubes_of_central_quotient hpF.out π hπsurj hZ.le hπcop hcube4)
      (fun F hF hc => closure_centralizers_spinPlus_plane hpF.out (by omega) hpk hpq1
        (by norm_num) F hF hc) hF hc
  · refine sup_le (sup_le (iSup_le fun i => ?_) htr) ?_
    · fin_cases i
      · exact (le_iSup (fun i => (d4Rho σ.toRingHom i).range) 0).trans hdr
      · exact (le_iSup (fun i => (d4Rho σ.toRingHom i).range) 2).trans hdr
      · exact (le_iSup (fun i => (d4Rho σ.toRingHom i).range) 3).trans hdr
      · exact (frameHom_three_le_d4Group σ.toRingHom).trans hdr
    · rintro y hy
      have hy' : (y : ModGL TwistTag.E6.tag K) ∈ orbitRankOneGroup TwistTag.E6 K σ.toRingHom
          ⟨3, by decide⟩ := hy
      obtain ⟨A, hA⟩ := orbitRankOneGroup_le_range_rankOneFix σ.toRingHom orbCenter
        orbCenter_card hy'
      have hyeq : y = centerHom σ.toRingHom A := Subtype.ext hA.symm
      rw [hyeq]
      exact hdr (Subgroup.mem_iSup_of_mem 1 ⟨A, rfl⟩)

theorem twE6_conj_frame_five {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h5 : 5 ∣ ℓ ^ f + 1) (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀e : IsElemAbelian 5 E₀) :
    ∃ g : twistedE6RootGroup K σ,
      E₀.map (MulAut.conj g).toMonoidHom ≤ frameTorusGroup σ.toRingHom := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hf, hK'⟩
  haveI : CharP K ℓ := hU.charP
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  obtain ⟨ψ₁, hk₁, -, hX₁⟩ := TwFive.twE6SU6Cover_five K σ ℓ f hℓ hf hK hσ 5 le_rfl h5
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨e₂⟩ := TwFive.exists_mulEquiv_sl2_su2 (K := K) hK σ.toRingHom hσ'
  let θ : SL(2, RingHom.eqLocusField σ.toRingHom (RingHom.id K)) × unitarySL σ.toRingHom ≃*
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K 2 ×
        CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K 6 :=
    e₂.prodCongr (unitarySLEquivStated hK hσ')
  obtain ⟨Ew, hEwe, hEwc, hEwle⟩ := TwFive.exists_elemAbelian_six hℓ hf K hK σ hσ h5
  have hEwr : Ew ≤ ψ₁.range := hEwle.trans (le_sup_left.trans hX₁)
  obtain ⟨Ew', hEw'e, hEw'm, hEw'c⟩ := TwFive.exists_lift_of_le_range ψ₁ hk₁ hEwr hEwe
  have hord := TwFive.five_hord hℓ hf hK σ hσ h5
  obtain ⟨g, E', hE'e, hE'm⟩ := TwFive.exists_conj_lift_elemAbelian ψ₁ hk₁ hord E₀ hE₀e
  obtain ⟨c, hc⟩ :=
    TwFive.exists_conj_le_toral_of_equiv hU h5 θ Ew' hEw'e (hEw'c.trans hEwc) E' hE'e
  refine ⟨(ψ₁ c)⁻¹ * g, ?_⟩
  rintro y ⟨e, he, rfl⟩
  have h1 : g * e * g⁻¹ ∈ E₀.map (MulAut.conj g).toMonoidHom :=
    ⟨e, he, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  rw [← hE'm] at h1
  obtain ⟨y', hy', hy'e⟩ := h1
  obtain ⟨z, hz, hzy⟩ := hc hy'
  have hzψ : ψ₁ z ∈ Ew := hEw'm ▸ ⟨z, hz, rfl⟩
  have hψ : g * e * g⁻¹ = ψ₁ c * ψ₁ z * (ψ₁ c)⁻¹ := by
    rw [← hy'e, ← hzy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hconj : (MulAut.conj ((ψ₁ c)⁻¹ * g)).toMonoidHom e = ψ₁ z := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, _root_.mul_inv_rev, inv_inv]
    calc (ψ₁ c)⁻¹ * g * e * (g⁻¹ * ψ₁ c) = (ψ₁ c)⁻¹ * (g * e * g⁻¹) * ψ₁ c := by group
      _ = ψ₁ z := by rw [hψ]; group
  rw [hconj]
  exact hEwle hzψ

theorem hyperGen_twE6_two_native (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (ℓ f : ℕ)
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1)
    (hcube4 : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4
      (RingHom.eqLocusField σ.toRingHom (RingHom.id K))))), IsElemAbelian p E →
        Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    {E₀ : Subgroup (twistedE6RootGroup K σ)} (hE₀ : IsElemAbelian p E₀)
    (hc : Nat.card E₀ = p ^ 3) : HyperGen p ⊤ E₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hconj : ∃ g : twistedE6RootGroup K σ,
      E₀.map (MulAut.conj g).toMonoidHom ≤ frameTorusGroup σ.toRingHom := by
    rcases Nat.lt_or_ge p 7 with h7 | h7
    · have hp5' : p = 5 := by
        interval_cases p
        · rfl
        · exact absurd hp (by norm_num)
      subst hp5'
      exact twE6_conj_frame_five hℓ hf K hK σ hσ hpq E₀ hE₀
    · exact exists_conj_le_frame_torusG hℓ hf K hK σ hσ h7 hpq E₀ hE₀.2
  obtain ⟨H₁, _, _, ψ₁, hk₁, hH₁, hX₁⟩ := twE6_su6_cubeCover K σ ℓ f hℓ hf hK hσ p hp5 hpq
  obtain ⟨H₂, _, _, ψ₂, hk₂, hH₂, hX₂⟩ := twE6_d4_cubeCover K σ ℓ f hℓ hf hK hσ p hp5 hpq hcube4
  have hX₁' : ∀ y : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      y ∈ leviRootGroups σ.toRingHom → y ∈ ψ₁.range := fun y hy =>
    hX₁ (Subgroup.mem_sup_right hy)
  have hX₂' : ∀ y : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      y ∈ centerRootGroup σ.toRingHom → y ∈ ψ₂.range := fun y hy =>
    hX₂ (Subgroup.mem_sup_right hy)
  have hclose : ∀ M : Subgroup ↥(twistedE6RootGroup K σ), ψ₁.range ≤ M → ψ₂.range ≤ M →
      M = ⊤ := by
    intro M hM₁ hM₂
    refine eq_top_of_orbitRankOneGroup_le M fun a => ?_
    refine le_map_subtype_of_mem (orbitRankOneGroup_le_graphFixedRootGroup' _ _) fun y hy => ?_
    match a, hy with
    | ⟨0, _⟩, hy =>
      exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))))
    | ⟨1, _⟩, hy =>
      exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hy))))
    | ⟨2, _⟩, hy =>
      exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right hy)))
    | ⟨3, _⟩, hy => exact hM₂ (hX₂' y (Subgroup.mem_subgroupOf.2 hy))
    | ⟨n + 4, h⟩, _ => exact absurd h (by change ¬ n + 4 < 4; omega)
  exact hyperGen_of_two_covers hp ψ₁ ψ₂ hk₁ hk₂ hH₁ hH₂ hclose (frameTorusGroup σ.toRingHom)
    (le_trans le_sup_left hX₁) (le_trans le_sup_left hX₂) hE₀ hc hconj

theorem hyperGen_twistedE6_two {q : PrimePower} (hv : (LieTypeIndex.twistedE6 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (h2 : orderOf ((q.card : ℕ) : ZMod p) = 2)
    (hcube4 : ∀ (k : Type) [Field k] [Finite k], Nat.card k = q.card →
      ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 k))),
        IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    {E₀ : Subgroup (Cat ⟨.twistedE6 q, hv⟩)} (hE₀ : IsElemAbelian p E₀)
    (hc : Nat.card E₀ = p ^ 3) : HyperGen p ⊤ E₀ := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hpq : p ∣ q.p ^ q.exponent + 1 := by
    rw [← PrimePower.card_def]
    exact dvd_add_one_of_orderOf_eq_two hp h2
  have hkcard : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = q.card := by
    rw [PrimePower.card_def]
    exact CFSG.RankThree.Chevalley.card_eqLocusField_of_pow q.prime_p q.exponent_pos hK hσ
  refine hyperGen_of_mulEquiv e ?_
  exact hyperGen_twE6_two_native K σ q.p q.exponent q.prime_p q.exponent_pos hK hσ hp hp5 hpq
    (hcube4 _ hkcard) (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.injective, hc])

end TwE6Two

section F4

open scoped MatrixGroups
open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge CFSG.AGLEmbeddingD2
  CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem f4Two_conj_frame (K : Type) [Field K] [Finite K] (p : ℕ) [hpF : Fact p.Prime]
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1) (E₀ : Subgroup (adjointGroup .F4 K))
    (hE₀p : ∀ x ∈ E₀, x ^ p = 1) :
    ∃ g : adjointGroup .F4 K, E₀.map (MulAut.conj g).toMonoidHom ≤ f4FrameGroup K := by
  obtain ⟨ρ, hρi, hρr, hρc⟩ := f4Frame_hom (K := K)
  have hcomm : Pairwise fun i j => ∀ x y : SL(2, K), Commute (ρ i x) (ρ j y) := by
    intro i j hij x y
    exact hρc i j hij x y
  obtain ⟨Q, -, hQ⟩ := exists_conj_le_frame_sylow ρ hρi hcomm hp5 hpq
    (by rw [factorization_card_F4_of_dvd_add_one hpF.out hp5 hpq])
  obtain ⟨g, hg⟩ := hQ E₀ hE₀p
  refine ⟨g, hg.trans ((map_noncommPiCoprod_le ρ hcomm Q).trans ?_)⟩
  simp only [f4FrameGroup, hρr]
  exact le_rfl

theorem iSup_b4Chain_le_hyperClosure {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (hodd : (2 : K) ≠ 0 → ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd 4 K))),
      IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    (E : Subgroup (adjointGroup .F4 K)) (hE : E ≤ ⨆ k, b4Chain K k)
    (hEa : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) :
    ⨆ k, b4Chain K k ≤ hyperClosure p ⊤ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  by_cases h2 : (2 : K) = 0
  ·
    have hc : ringChar K = 2 := by
      have hd : ringChar K ∣ 2 := ringChar.dvd (by exact_mod_cast h2)
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hd
    have : CharP K 2 := ringChar.of_eq hc
    have hK2 : Nat.card K = 2 ^ (n : ℕ) := by rw [hK, hc]
    have hK4 : 4 ≤ Nat.card K := by
      have := Nat.le_of_dvd (by omega) hpq
      omega
    obtain ⟨Ψ, hker, hrange, -, -⟩ := exists_psi_B4_F4_frame_even hK2 hK4
    have hcen : ¬ p ∣ Nat.card (Subgroup.center (StatedSp 4 K)) := by
      rw [CFSG.LieType.Universal.Symplectic.center_eq,
        show (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedSp 4 K) =
          CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 4 K from rfl,
        CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K (by norm_num)]
      intro hd
      have h2' := (Nat.dvd_prime Nat.prime_two).1 (hd.trans (Nat.gcd_dvd_left 2 _))
      omega
    have hΨcop : ¬ p ∣ Nat.card Ψ.ker := fun hd =>
      hcen (hd.trans (Subgroup.card_dvd_of_le hker))
    have hπcop : ¬ p ∣ Nat.card (proj 4 K).ker := fun hd =>
      hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (coprime_card_ker_proj (by norm_num) hp hp2) hd
        (dvd_refl p))
    rw [← hrange]
    exact range_le_hyperClosure_of_cover hp (proj 4 K)
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := 4) (K := K))
      ker_proj_le_center hπcop
      (fun E' hE' hE'c => hyperGen_statedProj_sp hp hp2 (natCast_ne_zero_of_not_dvd_card hp hpK)
        (by norm_num) (by omega) E' hE' hE'c)
      Ψ hΨcop (hrange ▸ hE) hEa hEc
  ·
    have hℓ2 : ringChar K ≠ 2 := by
      intro h
      apply h2
      have : CharP K 2 := h ▸ ringChar.charP K
      exact CharTwo.two_eq_zero
    obtain ⟨Ψ, hΨker, hΨrange, -, -⟩ := exists_psi_B4_F4_frame hℓ hℓ2 hK h2
    have hn3 : 3 ≤ 4 := by norm_num
    have : Nonempty (Fin 4 ⊕ Fin 4 ⊕ Unit) := ⟨Sum.inr (Sum.inr ())⟩
    have : Finite (spinGroup (quadOdd 4 K)) :=
      CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _
        (coe_ker_spinMatrix_quadOdd h2)
    obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadOdd (n := 4) h2 hn3
    set π := spinToStatedProj (quadOdd 4 K) (range_spinMatrix_quadOdd h2 hn3) with hπdef
    have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadOdd 4 K))) :=
      not_dvd_card_center_spin_of_not_dvd_pred (quadOdd 4 K) (range_spinMatrix_quadOdd h2 hn3)
        hZ hcomap
        (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadOdd_iff h2 x).mp hx)) hp2
        hpq1
    have hπcop : ¬ p ∣ Nat.card π.ker := by
      rw [hZ]
      exact hcen
    have hΨcop : ¬ p ∣ Nat.card Ψ.ker := fun hd =>
      hcen (hd.trans (Subgroup.card_dvd_of_le hΨker))
    rw [← hΨrange]
    exact range_le_hyperClosure_of_cover hp π hπsurj hZ.le hπcop (hodd h2) Ψ hΨcop
      (hΨrange ▸ hE) hEa hEc

theorem hyperGen_adjoint_F4_two (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (hodd : (2 : K) ≠ 0 → ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd 4 K))),
      IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    {E₀ : Subgroup (adjointGroup .F4 K)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3) :
    HyperGen p ⊤ E₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact hyperGen_of_two_conj (⨆ k, b4Chain K k) (f4FrameGroup K)
    (CFSG.LieType.Chevalley.weylElement .F4 K (f4Node 3)) f4FrameGroup_le_b4 f4FrameGroup_le_conj_b4
    (fun M hX hn => eq_top_of_b4Chain_le_of_conj_le M hX hn)
    (fun E hE hEa hEc => iSup_b4Chain_le_hyperClosure hp hp5 hpq hodd E hE hEa hEc)
    hE₀ hc (f4Two_conj_frame K p hp5 hpq E₀ hE₀.2)

theorem hyperGen_F4_two {q : PrimePower} (hv : (LieTypeIndex.F4 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (h2 : orderOf ((q.card : ℕ) : ZMod p) = 2)
    (hodd : q.p ≠ 2 → ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card →
      ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd 4 K))),
        IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    {E₀ : Subgroup (Cat ⟨.F4 q, hv⟩)} (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 3) :
    HyperGen p ⊤ E₀ := by
  obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hKq]
    exact dvd_add_one_of_orderOf_eq_two hp h2
  have hodd' : (2 : K) ≠ 0 → ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd 4 K))),
      IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E := by
    intro h2K
    refine hodd ?_ K hKq
    intro hq2
    apply h2K
    have : CharP K 2 := hq2 ▸ hchar
    exact CharTwo.two_eq_zero
  refine hyperGen_of_mulEquiv e ?_
  exact hyperGen_adjoint_F4_two K hp hp5 hpq hodd'
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.injective, hc])

end F4

end E8

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes
