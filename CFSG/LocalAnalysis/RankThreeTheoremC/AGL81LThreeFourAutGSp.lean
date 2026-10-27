module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutDefs
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTorus
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

variable {q : ℕ} [Fact q.Prime]

private lemma three_ne_zero_zmod (hq3 : q ≠ 3) : (3 : ZMod q) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hq3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h')

private lemma exists_cube_root (h1 : q % 3 = 1) : ∃ ω : ZMod q, ω ^ 2 + ω + 1 = 0 := by
  have h3 : 3 ∣ Fintype.card (ZMod q)ˣ := by
    rw [ZMod.card_units]
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 h3
  have hu3 : (u : ZMod q) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : (u : ZMod q) ≠ 1 := by
    intro h
    rw [Units.val_eq_one.mp h, orderOf_one] at hu
    norm_num at hu
  refine ⟨u, ?_⟩
  have h : ((u : ZMod q) - 1) * ((u : ZMod q) ^ 2 + u + 1) = 0 := by linear_combination hu3
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hu1)

private lemma comm_on_invariant (hq3 : q ≠ 3) {W : Type} [AddCommGroup W] [Module (ZMod q) W]
    [Module.Finite (ZMod q) W] {T : Subgroup (Module.End (ZMod q) W)ˣ} (hT : IsPGroup 3 T)
    {U : Submodule (ZMod q) W} (hU : Module.finrank (ZMod q) U ≤ 2)
    (hinv : ∀ t ∈ T, ∀ u ∈ U, (t : Module.End (ZMod q) W) u ∈ U)
    {a b : (Module.End (ZMod q) W)ˣ} (ha : a ∈ T) (hb : b ∈ T) {u : W} (hu : u ∈ U) :
    (a : Module.End (ZMod q) W) ((b : Module.End (ZMod q) W) u) =
      (b : Module.End (ZMod q) W) ((a : Module.End (ZMod q) W) u) := by
  have hq : q.Prime := Fact.out
  have hpq : (3 : ℕ) ≠ q := fun h => hq3 h.symm
  have hcard : ¬ 3 ∣ Nat.card (ZMod q) := by
    rw [Nat.card_zmod]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h)
  have hcop : Nat.Coprime q 3 := (Nat.coprime_primes hq Nat.prime_three).mpr hq3
  have hord : 0 < orderOf (q : ZMod 3) := by
    have := orderOf_pos (ZMod.unitOfCoprime q hcop)
    rwa [← orderOf_units, ZMod.coe_unitOfCoprime] at this
  let ρ : ↥T →* Module.End (ZMod q) U :=
    { toFun := fun t => (t.1 : Module.End (ZMod q) W).restrict (hinv t.1 t.2)
      map_one' := by ext x; simp
      map_mul' := by intro s t; ext x; simp }
  have hP : IsPGroup 3 ρ.toHomUnits.range :=
    hT.of_surjective ρ.toHomUnits.rangeRestrict ρ.toHomUnits.rangeRestrict_surjective
  have hab : IsMulCommutative ρ.toHomUnits.range :=
    RankFourTheoremC.isMulCommutative_of_isPGroup_GL (p := 3) ⟨1, rfl⟩ hcard hord
      (fun j => by rw [Nat.card_zmod]; exact dvd_pow_sub_one_iff_orderOf_dvd hq hpq j)
      ((Nat.div_le_self _ _).trans_lt (by omega)) hP
  have h := hab.is_comm.comm ⟨ρ.toHomUnits ⟨a, ha⟩, ⟨a, ha⟩, rfl⟩
    ⟨ρ.toHomUnits ⟨b, hb⟩, ⟨b, hb⟩, rfl⟩
  have h' := congrArg (fun x : ρ.toHomUnits.range =>
    ((((x : (Module.End (ZMod q) U)ˣ) : Module.End (ZMod q) U) ⟨u, hu⟩ : U) : W)) h
  simpa [ρ] using h'

private lemma exists_central_isometry {W : Type} [AddCommGroup W] [Module (ZMod q) W]
    [Module.Finite (ZMod q) W] (B : LinearMap.BilinForm (ZMod q) W) {u₀ v₀ : W}
    (h₀ : B u₀ v₀ ≠ 0) {T : Subgroup (Module.End (ZMod q) W)ˣ} (hT : IsPGroup 3 T)
    (hsim : ∀ t ∈ T, ∃ c : ZMod q, ∀ u v : W,
      B ((t : Module.End (ZMod q) W) u) ((t : Module.End (ZMod q) W) v) = c * B u v)
    (hna : ¬ IsMulCommutative T) :
    ∃ f : Module.End (ZMod q) W,
      (∀ t ∈ T, ∀ w, f ((t : Module.End (ZMod q) W) w) = (t : Module.End (ZMod q) W) (f w)) ∧
      (∀ w, f (f (f w)) = w) ∧ (∃ w, f w ≠ w) ∧ ∀ u v : W, B (f u) (f v) = B u v := by
  choose μ hμ using hsim
  have huniq : ∀ α β : ZMod q, α * B u₀ v₀ = β * B u₀ v₀ → α = β :=
    fun α β h => mul_right_cancel₀ h₀ h
  have hone : μ 1 T.one_mem = 1 := huniq _ _ (by rw [← hμ, one_mul]; simp)
  have hmul : ∀ s t : ↥T, μ (s * t).1 (s * t).2 = μ s.1 s.2 * μ t.1 t.2 := by
    intro s t
    apply huniq
    rw [mul_assoc, ← hμ t.1 t.2, ← hμ s.1 s.2, ← hμ]
    rfl
  let lam : ↥T →* ZMod q :=
    { toFun := fun t => μ t.1 t.2
      map_one' := hone
      map_mul' := hmul }
  have hN : lam.toHomUnits.ker ≠ ⊥ := by
    intro hN
    have hinj := (MonoidHom.ker_eq_bot_iff _).mp hN
    exact hna ⟨⟨fun s t => hinj (by rw [map_mul, map_mul, mul_comm])⟩⟩
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  have hNZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN
  have hdvd : 3 ∣ Nat.card ↥(lam.toHomUnits.ker ⊓ Subgroup.center ↥T) := by
    rcases (hT.to_subgroup (lam.toHomUnits.ker ⊓ Subgroup.center ↥T)).card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hNZ
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  refine ⟨(((x : ↥T) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W), fun t ht w => ?_,
    fun w => ?_, ?_, fun u v => ?_⟩
  · have h := congrArg (fun g : ↥T => ((g : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) w)
      (Subgroup.mem_center_iff.mp x.2.2 ⟨t, ht⟩)
    exact h.symm
  · have h := congrArg (fun y : ↥(lam.toHomUnits.ker ⊓ Subgroup.center ↥T) =>
      (((y : ↥T) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) w) hx3
    simpa [pow_succ] using h
  · by_contra h
    push Not at h
    have h1 : x = 1 := Subtype.ext (Subtype.ext (Units.ext (LinearMap.ext h)))
    rw [h1, orderOf_one] at hx
    norm_num at hx
  · have hker : lam (x : ↥T) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp x.2.1)
      simpa using this
    rw [hμ _ (x : ↥T).2]
    have h1 : μ ((x : ↥T) : (Module.End (ZMod q) W)ˣ) (x : ↥T).2 = 1 := hker
    rw [h1, one_mul]

private lemma comm_of_central_isometry (hq3 : q ≠ 3) {ω : ZMod q} (hω : ω ^ 2 + ω + 1 = 0)
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W = 4) (B : LinearMap.BilinForm (ZMod q) W)
    (hnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0)
    {T : Subgroup (Module.End (ZMod q) W)ˣ} (hT : IsPGroup 3 T) {f : Module.End (ZMod q) W}
    (hfT : ∀ t ∈ T, ∀ w, f ((t : Module.End (ZMod q) W) w) = (t : Module.End (ZMod q) W) (f w))
    (hf3 : ∀ w, f (f (f w)) = w) (hf1 : ∃ w, f w ≠ w) (hiso : ∀ u v : W, B (f u) (f v) = B u v) :
    IsMulCommutative T := by
  have h3 : (3 : ZMod q) ≠ 0 := three_ne_zero_zmod hq3
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    exact h3 (by linear_combination hω)
  have hω2 : ω ^ 2 ≠ 1 := fun h => hω1 (by linear_combination hω3 - ω * h)
  have hω4 : ω ^ 2 * ω ^ 2 ≠ 1 := fun h => hω1 (by linear_combination h - ω * hω3)
  have hωω2 : ω ≠ ω ^ 2 := fun h => hω1 (by linear_combination (1 + ω) * h + hω3)
  have hinv : ∀ α : ZMod q, ∀ t ∈ T, ∀ u ∈ f.eigenspace α,
      (t : Module.End (ZMod q) W) u ∈ f.eigenspace α := by
    intro α t ht u hu
    rw [Module.End.mem_eigenspace_iff] at hu ⊢
    rw [hfT t ht, hu, map_smul]
  have hdec : ∀ w : W, ∃ x ∈ f.eigenspace 1, ∃ y ∈ f.eigenspace ω, ∃ z ∈ f.eigenspace (ω ^ 2),
      x + y + z = w := by
    intro w
    refine ⟨(3 : ZMod q)⁻¹ • (w + f w + f (f w)), ?_,
      (3 : ZMod q)⁻¹ • (w + ω ^ 2 • f w + ω • f (f w)), ?_,
      (3 : ZMod q)⁻¹ • (w + ω • f w + ω ^ 2 • f (f w)), ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, map_smul, map_add, map_add, hf3]
      module
    · rw [Module.End.mem_eigenspace_iff, map_smul, map_add, map_add, map_smul, map_smul, hf3]
      linear_combination (norm := module) -(((3 : ZMod q)⁻¹ * hω3) • f w)
    · rw [Module.End.mem_eigenspace_iff, map_smul, map_add, map_add, map_smul, map_smul, hf3]
      linear_combination (norm := module) -(((3 : ZMod q)⁻¹ * hω3) • f w) -
        ((3 : ZMod q)⁻¹ * ω * hω3) • f (f w)
    · linear_combination (norm := module) (inv_mul_cancel₀ h3) • w +
        ((3 : ZMod q)⁻¹ * hω) • f w + ((3 : ZMod q)⁻¹ * hω) • f (f w)
  have horth : ∀ α β : ZMod q, α * β ≠ 1 → ∀ u ∈ f.eigenspace α, ∀ v ∈ f.eigenspace β,
      B u v = 0 := by
    intro α β hαβ u hu v hv
    rw [Module.End.mem_eigenspace_iff] at hu hv
    have h := hiso u v
    simp only [hu, hv, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    have h' : (α * β - 1) * B u v = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hαβ)
  have hrad : ∀ v : W, (∀ x ∈ f.eigenspace 1, B v x = 0) → (∀ y ∈ f.eigenspace ω, B v y = 0) →
      (∀ z ∈ f.eigenspace (ω ^ 2), B v z = 0) → v = 0 := by
    intro v h1 h2 h3
    refine hnd v fun w => ?_
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := hdec w
    rw [map_add, map_add, h1 x hx, h2 y hy, h3 z hz, add_zero, add_zero]
  have hle : ∀ α β : ZMod q,
      (∀ v ∈ f.eigenspace α, (∀ z ∈ f.eigenspace β, B v z = 0) → v = 0) →
      Module.finrank (ZMod q) (f.eigenspace α) ≤ Module.finrank (ZMod q) (f.eigenspace β) := by
    intro α β h
    have hφ : Function.Injective (B.domRestrict₁₂ (f.eigenspace α) (f.eigenspace β)) := by
      refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
      exact Subtype.ext (h v v.2 fun z hz => LinearMap.congr_fun hv ⟨z, hz⟩)
    exact (LinearMap.finrank_le_finrank_of_injective hφ).trans_eq Subspace.dual_finrank_eq
  have hle12 : Module.finrank (ZMod q) (f.eigenspace ω) ≤
      Module.finrank (ZMod q) (f.eigenspace (ω ^ 2)) :=
    hle ω (ω ^ 2) fun v hv h => hrad v
      (fun x hx => horth ω 1 (by rwa [mul_one]) v hv x hx)
      (fun y hy => horth ω ω (by rwa [← sq]) v hv y hy) h
  have hle21 : Module.finrank (ZMod q) (f.eigenspace (ω ^ 2)) ≤
      Module.finrank (ZMod q) (f.eigenspace ω) :=
    hle (ω ^ 2) ω fun v hv h => hrad v
      (fun x hx => horth (ω ^ 2) 1 (by rwa [mul_one]) v hv x hx) h
      (fun z hz => horth (ω ^ 2) (ω ^ 2) hω4 v hv z hz)
  have hind := Module.End.eigenspaces_iSupIndep f
  have hd12 : Disjoint (f.eigenspace ω) (f.eigenspace (ω ^ 2)) := hind.pairwiseDisjoint hωω2
  have hd0 : Disjoint (f.eigenspace 1) (f.eigenspace ω ⊔ f.eigenspace (ω ^ 2)) := by
    have := hind.disjoint_biSup (x := 1) (y := {ω, ω ^ 2}) (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hω1.symm, hω2.symm⟩)
    rwa [iSup_pair] at this
  have hsum : Module.finrank (ZMod q) (f.eigenspace 1) + Module.finrank (ZMod q) (f.eigenspace ω) +
      Module.finrank (ZMod q) (f.eigenspace (ω ^ 2)) ≤ 4 := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (f.eigenspace ω) (f.eigenspace (ω ^ 2))
    have e2 := Submodule.finrank_sup_add_finrank_inf_eq (f.eigenspace 1)
      (f.eigenspace ω ⊔ f.eigenspace (ω ^ 2))
    rw [hd12.eq_bot, finrank_bot] at e1
    rw [hd0.eq_bot, finrank_bot] at e2
    have e3 := Submodule.finrank_le (f.eigenspace 1 ⊔ (f.eigenspace ω ⊔ f.eigenspace (ω ^ 2)))
    omega
  have hm : 0 < Module.finrank (ZMod q) (f.eigenspace ω) := by
    obtain ⟨w₀, hw₀⟩ := hf1
    by_contra h0
    have e1 : f.eigenspace ω = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have e2 : f.eigenspace (ω ^ 2) = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    obtain ⟨x, hx, y, hy, z, hz, hxyz⟩ := hdec w₀
    rw [e1, Submodule.mem_bot] at hy
    rw [e2, Submodule.mem_bot] at hz
    subst hy hz
    rw [Module.End.mem_eigenspace_iff, one_smul] at hx
    apply hw₀
    rw [← hxyz, add_zero, add_zero, hx]
  have hd₀ : Module.finrank (ZMod q) (f.eigenspace 1) ≤ 2 := by omega
  have hd₁ : Module.finrank (ZMod q) (f.eigenspace ω) ≤ 2 := by omega
  have hd₂ : Module.finrank (ZMod q) (f.eigenspace (ω ^ 2)) ≤ 2 := by omega
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro w
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := hdec w
  simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, map_add]
  rw [comm_on_invariant hq3 hT hd₀ (hinv 1) a.2 b.2 hx,
    comm_on_invariant hq3 hT hd₁ (hinv ω) a.2 b.2 hy,
    comm_on_invariant hq3 hT hd₂ (hinv (ω ^ 2)) a.2 b.2 hz]

theorem similitudeThreeAbelian {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    SimilitudeThreeAbelian q := by
  intro W _ _ _ hW B hnd _ T hT hsim
  have hq : q.Prime := Fact.out
  have hpq : (3 : ℕ) ≠ q := fun h => hq3 h.symm
  have hq0 : q % 3 ≠ 0 := by
    intro h
    rcases hq.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h) with h' | h' <;> omega
  rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with h1 | h2
  · obtain ⟨ω, hω⟩ := exists_cube_root h1
    by_contra hna
    haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod q) (by omega)
    obtain ⟨u₀, hu₀⟩ := exists_ne (0 : W)
    obtain ⟨v₀, hv₀⟩ : ∃ v₀, B u₀ v₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hu₀ (hnd u₀ h)
    obtain ⟨f, hfT, hf3, hf1, hiso⟩ := exists_central_isometry B hv₀ hT hsim hna
    exact hna (comm_of_central_isometry hq3 hω hW B hnd hT hfT hf3 hf1 hiso)
  · have he : orderOf (q : ZMod 3) = 2 := by
      rw [← ZMod.natCast_mod, h2]
      exact orderOf_eq_prime (by decide) (by decide)
    have hne : Module.finrank (ZMod q) W / orderOf (q : ZMod 3) < 3 := by
      rw [hW, he]
      norm_num
    exact RankFourTheoremC.isMulCommutative_of_isPGroup_GL (p := 3) ⟨1, rfl⟩
      (by
        rw [Nat.card_zmod]
        exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h))
      (by rw [he]; norm_num)
      (fun j => by rw [Nat.card_zmod]; exact dvd_pow_sub_one_iff_orderOf_dvd hq hpq j) hne hT

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
