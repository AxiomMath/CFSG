module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsForm
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsSetup
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsPairs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.Coordinator

section Diag

variable {K : Type} [Field K]

theorem scalar_eq_diagUnits (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c = diagUnits c c c := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagUnits]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem modNine_of_cube {π : Bool} {r : ℕ} (h : ModThree π (r ^ 3)) : ModNine π (r ^ 3) := by
  have h9 : r ^ 3 % 9 = (r % 9) ^ 3 % 9 := Nat.pow_mod r 3 9
  have h3 : r ^ 3 % 3 = (r % 9 % 3) ^ 3 % 3 := by
    rw [Nat.pow_mod, Nat.mod_mod_of_dvd r (by norm_num : 3 ∣ 9)]
  have hm : r % 9 < 9 := Nat.mod_lt _ (by norm_num)
  set m := r % 9
  cases π
  · change r ^ 3 % 3 = 2 at h
    change r ^ 3 % 9 = 8
    rw [h9]
    rw [h3] at h
    interval_cases m <;> simp_all
  · change r ^ 3 % 3 = 1 at h
    change r ^ 3 % 9 = 1
    rw [h9]
    rw [h3] at h
    interval_cases m <;> simp_all

variable {π : Bool} {p f : ℕ}

theorem modNine_of_orderOf (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) : ModNine π (p ^ f) := by
  obtain ⟨f₀, rfl⟩ := exists_three_mul hK hσ
  rw [show p ^ (3 * f₀) = (p ^ f₀) ^ 3 by ring] at hq ⊢
  exact modNine_of_cube hq

end Diag

section Fixed

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem IsFieldAt.commute_conjBy (M : LModel L π p f K ν) {x : X} {σ : K ≃+* K}
    {H : GL (Fin 3) K} (hx : IsFieldAt ν x σ H) {D : GL (Fin 3) K}
    (hD : D ∈ slPi π 3 (p ^ f) K) (hfix : frobGL σ D = D) :
    ((ν (M.conjBy hx.mem ⟨D, hD⟩) : ↥L) : X) * x =
      x * ((ν (M.conjBy hx.mem ⟨D, hD⟩) : ↥L) : X) :=
  hx.commute_of_eq (by
    rw [M.coe_conjBy, show H⁻¹ * (H * D * H⁻¹) * H = D by group, hfix])

theorem IsFieldAt.commute_conjBy_mod (M : LModel L π p f K ν)
    (hproj : ∀ s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K), ν s = 1) {x : X} {σ : K ≃+* K}
    {H : GL (Fin 3) K} (hx : IsFieldAt ν x σ H) {D : GL (Fin 3) K}
    (hD : D ∈ slPi π 3 (p ^ f) K) (hfix : frobGL σ D * D⁻¹ ∈ StatedScalars (Fin 3) K) :
    ((ν (M.conjBy hx.mem ⟨D, hD⟩) : ↥L) : X) * x =
      x * ((ν (M.conjBy hx.mem ⟨D, hD⟩) : ↥L) : X) :=
  hx.commute_of_mod M hproj (by
    rw [M.coe_conjBy, show H⁻¹ * (H * D * H⁻¹) * H = D by group]
    exact hfix)

theorem IsLiftAt.commute_conjBy_diag (M : LModel L π p f K ν) {x : X} {y : GL (Fin 3) K}
    (hx : IsLiftAt ν x y) {g z : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hz : z ∈ StatedScalars (Fin 3) K) {a b c : Kˣ} (hy : g⁻¹ * (y * z) * g = diagUnits a b c)
    {a' b' c' : Kˣ} (hD : diagUnits a' b' c' ∈ slPi π 3 (p ^ f) K) :
    ((ν (M.conjBy hg ⟨diagUnits a' b' c', hD⟩) : ↥L) : X) * x =
      x * ((ν (M.conjBy hg ⟨diagUnits a' b' c', hD⟩) : ↥L) : X) := by
  refine hx.commute_of_commute ?_
  rw [M.coe_conjBy]
  have hyz : y = g * diagUnits a b c * g⁻¹ * z⁻¹ := by
    rw [← hy]
    group
  have hc := diagUnits_commute a b c a' b' c'
  have hz' := commute_of_mem_statedScalars (inv_mem hz)
  rw [hyz]
  calc g * diagUnits a b c * g⁻¹ * z⁻¹ * (g * diagUnits a' b' c' * g⁻¹)
      = g * diagUnits a b c * g⁻¹ * (z⁻¹ * (g * diagUnits a' b' c' * g⁻¹)) := by group
    _ = g * diagUnits a b c * g⁻¹ * ((g * diagUnits a' b' c' * g⁻¹) * z⁻¹) := by
        rw [hz' (g * diagUnits a' b' c' * g⁻¹)]
    _ = g * (diagUnits a b c * diagUnits a' b' c') * g⁻¹ * z⁻¹ := by group
    _ = g * (diagUnits a' b' c' * diagUnits a b c) * g⁻¹ * z⁻¹ := by rw [hc]
    _ = g * diagUnits a' b' c' * g⁻¹ * (g * diagUnits a b c * g⁻¹ * z⁻¹) := by group

end Fixed

section Outer

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type}
  [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem LModel.exists_scalar_tau (M : LModel L π p f K ν) {τ : K} (hτ : τ ^ 3 = 1) :
    ∃ t : Kˣ, (t : K) = τ ∧ Matrix.GeneralLinearGroup.scalar (Fin 3) t ∈ slPi π 3 (p ^ f) K := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  exact ⟨Units.mk0 τ hτ0, rfl, scalar_mem_slPi_of_cube M.piField M.modThree hτ⟩

theorem LModel.exists_isE9Pair (M : LModel L π p f K ν) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    ∃ (D : GL (Fin 3) K) (hD : D ∈ slPi π 3 (p ^ f) K),
      (D = cycThree ∨ D ∈ StatedScalars (Fin 3) K) ∧
      IsE9Pair L ((ν (M.conjBy hg ⟨diagTau hτ, diagTau_mem_slPi M.hπ M.hq' hτ⟩) : ↥L) : X)
        ((ν (M.conjBy hg ⟨D, hD⟩) : ↥L) : X) := by
  rcases M.cases with hinj | ⟨-, hproj⟩
  · obtain ⟨t, ht, htS⟩ := M.exists_scalar_tau hτ
    refine ⟨_, htS, Or.inr ⟨t, rfl⟩, M.isE9Pair_of_exact hinj ?_⟩
    simp only [M.coe_conjBy]
    exact (isPairExact_diagTau_scalar hτ hτ1 ht).conj g
  · refine ⟨cycThree, cycThree_mem_slPi M.hπ, Or.inl rfl, M.isE9Pair_of_mod hproj ?_⟩
    simp only [M.coe_conjBy]
    exact (isPairMod_diagTau_cycThree hτ hτ1).conj g

theorem LModel.three_le_of_isFieldAt [L.Normal] (M : LModel L π p f K ν) {x : X}
    (hx3 : x ^ 3 = 1) {σ : K ≃+* K} {H : GL (Fin 3) K} (hx : IsFieldAt ν x σ H) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  obtain ⟨D, hD, hDc, hpair⟩ := M.exists_isE9Pair hx.mem hτ hτ1
  refine hpair.three_le hx3 (M.not_mem_of_isFieldAt hx)
    (hx.commute_conjBy M _ (frobGL_diagTau hx.order hτ)) (hx.commute_conjBy M hD ?_)
  rcases hDc with rfl | ⟨c, rfl⟩
  · exact frobGL_cycThree σ
  · refine frobGL_scalar_of_pow_three hx.order ?_
    have h3 := (mem_slPi_iff M.hπ).1 hD
    rw [det_scalar] at h3
    exact h3.2

theorem LModel.three_le_of_mem_centralizer (M : LModel L π p f K ν) {x : X}
    (hx3 : x ^ 3 = 1) (hxL : x ∉ L) (hxC : x ∈ centralizer (L : Set X)) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  obtain ⟨D, hD, -, hpair⟩ := M.exists_isE9Pair (one_mem (glPi π 3 (p ^ f) K)) hτ hτ1
  exact hpair.three_le hx3 hxL (mem_centralizer_iff.1 hxC _ hpair.1)
    (mem_centralizer_iff.1 hxC _ hpair.2.1)

theorem LModel.three_le_of_cover_diag (M : LModel L π p f K ν) (hinj : Function.Injective ν)
    {x : X} (hx3 : x ^ 3 = 1) (hxL : x ∉ L) {y : GL (Fin 3) K} (hx : IsLiftAt ν x y)
    {g z : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) (hz : z ∈ StatedScalars (Fin 3) K)
    {a b c : Kˣ} (hy : g⁻¹ * (y * z) * g = diagUnits a b c) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  obtain ⟨t, ht, htS⟩ := M.exists_scalar_tau hτ
  obtain ⟨u, -, hu⟩ := diagTau_eq_diagUnits' hτ
  have hpair : IsE9Pair L
      ((ν (M.conjBy hg ⟨diagTau hτ, diagTau_mem_slPi M.hπ M.hq' hτ⟩) : ↥L) : X)
      ((ν (M.conjBy hg ⟨_, htS⟩) : ↥L) : X) := by
    refine M.isE9Pair_of_exact hinj ?_
    simp only [M.coe_conjBy]
    exact (isPairExact_diagTau_scalar hτ hτ1 ht).conj g
  refine hpair.three_le hx3 hxL ?_ ?_
  · have h := hx.commute_conjBy_diag M hg hz hy (a' := u) (b' := u ^ 2) (c' := 1)
      (by rw [← hu]; exact diagTau_mem_slPi M.hπ M.hq' hτ)
    have e : M.conjBy hg ⟨diagTau hτ, diagTau_mem_slPi M.hπ M.hq' hτ⟩ =
        M.conjBy hg ⟨diagUnits u (u ^ 2) 1, by rw [← hu]; exact diagTau_mem_slPi M.hπ M.hq' hτ⟩ :=
      congrArg (M.conjBy hg) (Subtype.ext hu)
    rw [e]
    exact h
  · have h := hx.commute_conjBy_diag M hg hz hy (a' := t) (b' := t) (c' := t)
      (by rw [← scalar_eq_diagUnits]; exact htS)
    have e : M.conjBy hg ⟨_, htS⟩ =
        M.conjBy hg ⟨diagUnits t t t, by rw [← scalar_eq_diagUnits]; exact htS⟩ :=
      congrArg (M.conjBy hg) (Subtype.ext (scalar_eq_diagUnits t))
    rw [e]
    exact h

end Outer

section Conj

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem LModel.exists_conj_diag (M : LModel L π p f K ν) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) {a b c : Kˣ} (hD : diagUnits a b c ∈ slPi π 3 (p ^ f) K) :
    ∃ l ∈ L, l * ((ν ⟨diagUnits a b c, hD⟩ : ↥L) : X) * l⁻¹ =
      ((ν (M.conjBy hg ⟨diagUnits a b c, hD⟩) : ↥L) : X) := by
  obtain ⟨k, hk, hkD⟩ := exists_slPi_conj_diagUnits M.piField hg
  refine ⟨((ν ⟨k, hk⟩ : ↥L) : X), (ν ⟨k, hk⟩).2, ?_⟩
  have e : (⟨k, hk⟩ : ↥(slPi π 3 (p ^ f) K)) * ⟨diagUnits a b c, hD⟩ * ⟨k, hk⟩⁻¹ =
      M.conjBy hg ⟨diagUnits a b c, hD⟩ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, M.coe_conjBy]
    exact hkD a b c)
  rw [← e, map_mul, map_mul, map_inv]
  rfl

end Conj

section CoverInner

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X} {π : Bool} {p f : ℕ}
  {K : Type} [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem LModel.exists_conj_diagTau_of_cover (M : LModel L π p f K ν)
    (hinj : Function.Injective ν) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {u : X} (huL : u ∈ L)
    (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (huZ : u ∉ (center ↥L).map L.subtype) :
    ∃ l ∈ L, l * ((ν ⟨diagTau hτ, diagTau_mem_slPi M.hπ M.hq' hτ⟩ : ↥L) : X) * l⁻¹ = u := by
  obtain ⟨s, hs⟩ := M.surj ⟨u, huL⟩
  have hsu : ((ν s : ↥L) : X) = u := by rw [hs]
  have hs3 : (s : GL (Fin 3) K) ^ 3 = 1 := by
    have : s ^ 3 = 1 := hinj (by
      rw [map_pow, map_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, hsu, hu3, Subgroup.coe_one])
    rw [← SubgroupClass.coe_pow, this, OneMemClass.coe_one]
  have hs1 : (s : GL (Fin 3) K) ≠ 1 := by
    intro h1
    apply hu1
    rw [← hsu, show s = 1 from Subtype.ext h1, map_one, Subgroup.coe_one]
  have hsZ : (s : GL (Fin 3) K) ∉ zPi π 3 (p ^ f) K := by
    intro hz
    apply huZ
    have hsc := mem_statedScalars_of_mem_zPi M.piField M.modThree hτ hτ1 hz
    exact ⟨ν s, M.map_mem_center (M.mem_center_of_mem_statedScalars hsc), hsu⟩
  have hso : orderOf (s : GL (Fin 3) K) = 3 := orderOf_eq_prime hs3 hs1
  obtain ⟨g, hg, hD⟩ := rank3II_4_10_three M.piField M.modThree hτ hτ1 s.2 hsZ hso
  obtain ⟨w, -, hw⟩ := diagTau_eq_diagUnits' hτ
  have hDs : diagUnits w (w ^ 2) 1 ∈ slPi π 3 (p ^ f) K := by
    rw [← hw]
    exact diagTau_mem_slPi M.hπ M.hq' hτ
  obtain ⟨l, hl, hlD⟩ := M.exists_conj_diag hg hDs
  refine ⟨l, hl, ?_⟩
  have e1 : (⟨diagTau hτ, diagTau_mem_slPi M.hπ M.hq' hτ⟩ : ↥(slPi π 3 (p ^ f) K)) =
      ⟨diagUnits w (w ^ 2) 1, hDs⟩ := Subtype.ext hw
  have e2 : M.conjBy hg ⟨diagUnits w (w ^ 2) 1, hDs⟩ = s := by
    apply Subtype.ext
    rw [M.coe_conjBy]
    show g * diagUnits w (w ^ 2) 1 * g⁻¹ = (s : GL (Fin 3) K)
    rw [← hw, ← hD]
    group
  have e3 : ν ⟨diagTau hτ, diagTau_mem_slPi M.hπ M.hq' hτ⟩ = ν ⟨diagUnits w (w ^ 2) 1, hDs⟩ :=
    congrArg ν e1
  rw [e3, hlD, e2, hsu]

theorem LModel.false_of_cover_inner (h : T29Setup X L x) (M : LModel L π p f K ν)
    (hinj : Function.Injective ν) (hZ3 : Nat.card (center ↥L) ∣ 3) (hxL : x ∈ L)
    (hxZ : x ∉ (center ↥L).map L.subtype) : False := by
  haveI hLn : L.Normal := h.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  obtain ⟨P, hxP⟩ : ∃ P : Sylow 3 X, x ∈ (P : Subgroup X) := by
    have hp : IsPGroup 3 (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.ord, pow_one])
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    exact ⟨P, hP (mem_zpowers x)⟩
  obtain ⟨z, hz⟩ := h.exists_omegaCentral hxP
  have hP3 : IsPGroup 3 (P : Subgroup X) := P.isPGroup'
  have hnc : ¬ IsCyclic ↥((P : Subgroup X) ⊓ L) := by
    obtain ⟨D, hD, -, hpair⟩ := M.exists_isE9Pair (one_mem (glPi π 3 (p ^ f) K)) hτ hτ1
    obtain ⟨hE, hE9, hEL⟩ := hpair.elemAbelian
    set E := zpowers ((ν (M.conjBy (one_mem (glPi π 3 (p ^ f) K))
      ⟨diagTau hτ, diagTau_mem_slPi M.hπ M.hq' hτ⟩) : ↥L) : X) ⊔
      zpowers ((ν (M.conjBy (one_mem (glPi π 3 (p ^ f) K)) ⟨D, hD⟩) : ↥L) : X)
    have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
    obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
    set E' := E.map (MulAut.conj g).toMonoidHom
    have hE'P : E' ≤ (P : Subgroup X) ⊓ L := by
      rintro _ ⟨e, he, rfl⟩
      refine ⟨?_, hLn.conj_mem e (hEL he) g⟩
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨e, hEQ he, rfl⟩
    intro hcyc
    haveI : IsCyclic ↥(E'.subgroupOf ((P : Subgroup X) ⊓ L)) := Subgroup.isCyclic _
    haveI : IsCyclic ↥E' := isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hE'P).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hE'P).surjective
    have h3 : Nat.card E' ≤ 3 := card_le_three_of_isCyclic (fun w => by
      obtain ⟨_, ⟨e, he, rfl⟩⟩ := w
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        OneMemClass.coe_one]
      rw [conj_pow, hE.2 e he, mul_one, mul_inv_cancel])
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9] at h3
    omega
  obtain ⟨U, hUS, hU, hU9, hUn⟩ := exists_normal_E9 hP3 inf_le_left
    (fun g hg => inf_normalizer_le_normalizer_inf ⟨le_normalizer hg,
      le_normalizer_of_normal hg⟩) hnc
  have hUL : U ≤ L := hUS.trans inf_le_right
  have hUP : U ≤ (P : Subgroup X) := hUS.trans inf_le_left
  obtain ⟨u, huU, huZ⟩ : ∃ u ∈ U, u ∉ (center ↥L).map L.subtype := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ (center ↥L).map L.subtype := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective L.subtype_injective, hU9] at h1
    have := Nat.le_of_dvd (by norm_num) hZ3
    omega
  have hu3 : u ^ 3 = 1 := hU.2 u huU
  have hu1 : u ≠ 1 := fun h1 => huZ (h1 ▸ one_mem _)
  have hx1 : x ≠ 1 := T29Setup.ne_one h
  have hxZ' : x ∉ (center ↥L).map L.subtype := hxZ
  obtain ⟨l₁, hl₁, hl₁u⟩ := M.exists_conj_diagTau_of_cover hinj hτ hτ1 (hUL huU) hu3 hu1 huZ
  obtain ⟨l₂, hl₂, hl₂x⟩ :=
    M.exists_conj_diagTau_of_cover hinj hτ hτ1 hxL (T29Setup.pow_three h) hx1 hxZ'
  have hux : u = (l₁ * l₂⁻¹) * x * (l₁ * l₂⁻¹)⁻¹ := by
    rw [← hl₁u, ← hl₂x]
    group
  have hk := three_le_of_mem_normal_E9 h.pRank_top_eq hz hUP hU hU9 hUn huU
  have hle := le_pRank_centralizer_of_mulEquiv (MulAut.conj (l₁ * l₂⁻¹)) x
  simp only [MulAut.conj_apply] at hle
  rw [← hux] at hle
  have := h.cent
  omega

end CoverInner

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
