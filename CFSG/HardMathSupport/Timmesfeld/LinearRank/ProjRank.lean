module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.Monomial
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.PermOrbitCount
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.TwistedCount
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.GLValuation
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.TorusBound

public section

namespace CFSG.HardMathSupport.Timmesfeld.LinearRank

open Matrix Equiv CFSG.Open CFSG.SectionRank.OddCover CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b

variable {K : Type} [Field K] {n : ℕ}

abbrev PGL (n : ℕ) (K : Type) [Field K] : Type := GL (Fin n) K ⧸ Subgroup.center (GL (Fin n) K)

@[expose] noncomputable def projMono (n : ℕ) (K : Type) [Field K] : MonoGroup n K →* PGL n K :=
  (QuotientGroup.mk' (Subgroup.center (GL (Fin n) K))).comp (monoHom n K)

@[expose] noncomputable def torusProj (n : ℕ) (K : Type) [Field K] : (Fin n → Kˣ) →* PGL n K :=
  (projMono n K).comp SemidirectProduct.inl

theorem mem_center_iff {A : GL (Fin n) K} :
    A ∈ Subgroup.center (GL (Fin n) K) ↔
      ∃ c : Kˣ, A = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  simp only [MonoidHom.mem_range]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem projMono_eq_one_iff {x : MonoGroup n K} :
    projMono n K x = 1 ↔ ∃ c : Kˣ, monoHom n K x = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  rw [← mem_center_iff]
  exact QuotientGroup.eq_one_iff _

theorem right_eq_one_of_projMono_eq_one {x : MonoGroup n K} (h : projMono n K x = 1) :
    x.right = 1 := by
  obtain ⟨c, hc⟩ := projMono_eq_one_iff.mp h
  exact right_eq_one_of_scalar hc

theorem torusProj_eq_one_iff {d : Fin n → Kˣ} :
    torusProj n K d = 1 ↔ ∃ c : Kˣ, ∀ i, d i = c := by
  rw [torusProj, MonoidHom.comp_apply, projMono_eq_one_iff]
  simp only [monoHom_inl]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, diagHom_eq_scalar_iff.mp hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, diagHom_eq_scalar_iff.mpr hc⟩

@[expose] noncomputable def monoImage (n : ℕ) (K : Type) [Field K] : Subgroup (PGL n K) :=
  (projMono n K).range

@[expose] noncomputable def torusImage (n : ℕ) (K : Type) [Field K] : Subgroup (PGL n K) :=
  (torusProj n K).range

@[expose] noncomputable def monoPerm (n : ℕ) (K : Type) [Field K] :
    monoImage n K →* Perm (Fin n) :=
  MonoidHom.liftOfSurjective (projMono n K).rangeRestrict
    (projMono n K).rangeRestrict_surjective
    ⟨SemidirectProduct.rightHom, fun x hx => by
      rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
      rw [MonoidHom.mem_ker]
      exact right_eq_one_of_projMono_eq_one hx⟩

theorem monoPerm_apply (x : MonoGroup n K) :
    monoPerm n K ((projMono n K).rangeRestrict x) = x.right := by
  erw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

theorem monoPerm_eq_one_iff (y : monoImage n K) :
    monoPerm n K y = 1 ↔ (y : PGL n K) ∈ torusImage n K := by
  obtain ⟨x, rfl⟩ := (projMono n K).rangeRestrict_surjective y
  rw [monoPerm_apply]
  constructor
  · intro hx
    have : x = SemidirectProduct.inl x.left := by
      conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, hx, map_one, mul_one]
    exact ⟨x.left, by simp [torusProj, MonoidHom.comp_apply, ← this]⟩
  · rintro ⟨d, hd⟩
    have h1 : projMono n K (SemidirectProduct.inl d)⁻¹ * projMono n K x = 1 := by
      have : projMono n K x = projMono n K (SemidirectProduct.inl d) := by
        exact hd.symm
      rw [this]
      simp
    rw [← map_inv, ← map_mul] at h1
    have h2 := right_eq_one_of_projMono_eq_one h1
    simpa using h2

theorem center_le_range_monoHom :
    Subgroup.center (GL (Fin n) K) ≤ (monoHom n K).range := by
  intro z hz
  obtain ⟨c, rfl⟩ := mem_center_iff.mp hz
  exact ⟨SemidirectProduct.inl (fun _ => c), by rw [monoHom_inl, diagHom_const]⟩

theorem not_dvd_index_monoImage [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card Kˣ) : ¬ p ∣ (monoImage n K).index := by
  have h1 : monoImage n K =
      (monoHom n K).range.map (QuotientGroup.mk' (Subgroup.center (GL (Fin n) K))) := by
    rw [monoImage, projMono, MonoidHom.range_comp]
  have h2 := Subgroup.index_map_eq (H := (monoHom n K).range)
    (QuotientGroup.mk'_surjective (Subgroup.center (GL (Fin n) K)))
    (by rw [QuotientGroup.ker_mk']; exact center_le_range_monoHom)
  rw [h1, h2]
  refine not_dvd_index_of_card_eq hp _ ?_
  rw [Nat.card_congr (MonoidHom.ofInjective monoHom_injective).toEquiv.symm, card_monoGroup,
    factorization_card_GL_eq hp hp2 hpK]

theorem torusImage_comm : ∀ a ∈ torusImage n K, ∀ b ∈ torusImage n K, a * b = b * a := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem torus_fix_bound [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (F : Subgroup (Perm (Fin n))) (S : Subgroup (PGL n K))
    (hF : IsElemAbelian p F) (hS : IsElemAbelian p S) (hSH : S ≤ torusImage n K)
    (hfix : ∀ h ∈ S, ∀ e : monoImage n K, monoPerm n K e ∈ F →
      (e : PGL n K) * h * (e : PGL n K)⁻¹ = h) :
    Nat.card S * Nat.card F ≤ p ^ (n - 1) := by
  classical
  set S' : Subgroup (Fin n → Kˣ) := S.comap (torusProj n K) with hS'
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.1.is_comm.comm (⟨a, ha⟩ : F) ⟨b, hb⟩)
  have hC : ∀ c : Kˣ, (fun _ => c) ∈ S' := fun c => by
    rw [hS', Subgroup.mem_comap, torusProj_eq_one_iff.mpr ⟨c, fun _ => rfl⟩]
    exact S.one_mem
  have hpow : ∀ d ∈ S', ∃ c : Kˣ, ∀ i, d i ^ p = c := by
    intro d hd
    have h1 : torusProj n K (d ^ p) = 1 := by
      rw [map_pow]
      exact hS.2 _ hd
    obtain ⟨c, hc⟩ := torusProj_eq_one_iff.mp h1
    exact ⟨c, fun i => by simpa using hc i⟩
  have hFt : ∀ σ ∈ F, ∀ d ∈ S', ∃ c : Kˣ, ∀ i, d (σ i) = c * d i := by
    intro σ hσ d hd
    set e : monoImage n K := (projMono n K).rangeRestrict (SemidirectProduct.inr σ⁻¹) with he
    have heF : monoPerm n K e ∈ F := by
      rw [he, monoPerm_apply]
      simpa using F.inv_mem hσ
    have h1 := hfix _ hd e heF
    have h2 : (e : PGL n K) * torusProj n K d * (e : PGL n K)⁻¹ =
        torusProj n K (permAct n K σ⁻¹ d) := by
      have hY := permGL_mul_diagHom_mul_inv σ⁻¹ d
      change (QuotientGroup.mk (monoHom n K (SemidirectProduct.inr σ⁻¹)) : PGL n K) *
        QuotientGroup.mk (monoHom n K (SemidirectProduct.inl d)) *
        (QuotientGroup.mk (monoHom n K (SemidirectProduct.inr σ⁻¹)))⁻¹ =
        QuotientGroup.mk (monoHom n K (SemidirectProduct.inl (permAct n K σ⁻¹ d)))
      rw [monoHom_inl, monoHom_inr, monoHom_inl, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, hY]
    rw [h2] at h1
    generalize hd' : permAct n K σ⁻¹ d = d' at h1
    have h3 : torusProj n K (d' * d⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    obtain ⟨c, hc⟩ := torusProj_eq_one_iff.mp h3
    refine ⟨c, fun i => ?_⟩
    have := hc i
    have h4 : d' i = d (σ i) := by
      rw [← hd', permAct_apply]
      rfl
    simp only [Pi.mul_apply, Pi.inv_apply, h4] at this
    rw [← this]
    group
  have hcard : Nat.card S' = Nat.card Kˣ * Nat.card S := by
    let Θ' : S' →* PGL n K := (torusProj n K).comp S'.subtype
    have hrange : Θ'.range = S := by
      ext s
      constructor
      · rintro ⟨⟨d, hd⟩, rfl⟩
        exact hd
      · intro hs
        obtain ⟨d, hd⟩ := hSH hs
        exact ⟨⟨d, by rw [hS', Subgroup.mem_comap, hd]; exact hs⟩, hd⟩
    have hker : Nat.card Θ'.ker = Nat.card Kˣ := by
      symm
      refine Nat.card_eq_of_bijective
        (fun c : Kˣ => (⟨⟨fun _ => c, hC c⟩, ?_⟩ : Θ'.ker)) ⟨?_, ?_⟩
      · exact torusProj_eq_one_iff.mpr ⟨c, fun _ => rfl⟩
      · intro c₁ c₂ h
        have := congrFun (congrArg (fun x : Θ'.ker => (x.1.1 : Fin n → Kˣ)) h) ⟨0, hn⟩
        exact this
      · rintro ⟨⟨d, hd⟩, hk⟩
        obtain ⟨c, hc⟩ := torusProj_eq_one_iff.mp (MonoidHom.mem_ker.mp hk)
        exact ⟨c, Subtype.ext (Subtype.ext (funext fun i => (hc i).symm))⟩
    have h1 := Subgroup.card_ker_mul_card_range Θ'
    have h2 : Nat.card Θ'.range = Nat.card S :=
      congrArg (fun H : Subgroup (PGL n K) => Nat.card H) hrange
    rw [hker, h2] at h1
    exact h1.symm
  have h1 := card_twisted_le hp hn F hFc S' hC hpow hFt
  have h2 := card_sq_mul_pow_orbits_le hp hp2 F hFc hF.2
  set m := Nat.card (MulAction.orbitRel.Quotient F (Fin n))
  have hpos : 0 < Nat.card Kˣ := Nat.card_pos
  rw [hcard] at h1
  have h3 : Nat.card S * p ≤ Nat.card F * p ^ m := by
    have : Nat.card Kˣ * (Nat.card S * p) ≤ Nat.card Kˣ * (Nat.card F * p ^ m) := by
      calc Nat.card Kˣ * (Nat.card S * p) = Nat.card Kˣ * Nat.card S * p := by ring
        _ ≤ Nat.card Kˣ * Nat.card F * p ^ m := h1
        _ = Nat.card Kˣ * (Nat.card F * p ^ m) := by ring
    exact Nat.le_of_mul_le_mul_left this hpos
  have h4 : Nat.card S * Nat.card F * p ≤ p ^ n := by
    calc Nat.card S * Nat.card F * p = (Nat.card S * p) * Nat.card F := by ring
      _ ≤ (Nat.card F * p ^ m) * Nat.card F := Nat.mul_le_mul_right _ h3
      _ = Nat.card F ^ 2 * p ^ m := by ring
      _ ≤ p ^ n := h2
  have h5 : p ^ n = p ^ (n - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h5] at h4
  exact Nat.le_of_mul_le_mul_right h4 hp.pos

theorem pRank_pgl_le [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card Kˣ)
    (hn : 0 < n) : CFSG.Open.pRank p (⊤ : Subgroup (PGL n K)) ≤ n - 1 :=
  pRank_le_of_torus_normalizer hp (monoImage n K) (torusImage n K) torusImage_comm
    (not_dvd_index_monoImage hp hp2 hpK) (monoPerm n K) monoPerm_eq_one_iff
    (fun F S hF hS hSH hfix => torus_fix_bound hp hp2 hn F S hF hS hSH hfix)

theorem card_le_of_pRank_le {G : Type*} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    (h : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ k) (E : Subgroup G) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 g g.2)⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hP
  have := CFSG.SectionRank.le_pRank hp.one_lt (le_top : E ≤ ⊤) hE hj
  rw [hj]
  exact Nat.pow_le_pow_right hp.pos (this.trans h)

theorem card_le_of_scalar_kernel [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card Kˣ) (hn : 0 < n) {G : Type*} [Group G]
    (U : Subgroup (GL (Fin n) K)) (ρ : U →* G)
    (hker : ∀ A : U, ρ A = 1 ↔ (A : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K))
    (E : Subgroup G) (hEρ : E ≤ ρ.range) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ (n - 1) := by
  classical
  let ψ : U →* PGL n K := (QuotientGroup.mk' (Subgroup.center (GL (Fin n) K))).comp U.subtype
  have hψ : ∀ A : U, ψ A = 1 ↔ ρ A = 1 := fun A => by
    rw [hker]
    exact QuotientGroup.eq_one_iff _
  let θ : ρ.range →* PGL n K := MonoidHom.liftOfSurjective ρ.rangeRestrict
    ρ.rangeRestrict_surjective ⟨ψ, fun A hA => by
      rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hA
      exact (hψ A).2 hA⟩
  have hθ : ∀ A : U, θ (ρ.rangeRestrict A) = ψ A := fun A => by
    erw [MonoidHom.liftOfRightInverse_comp_apply]
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨A, rfl⟩ := ρ.rangeRestrict_surjective y
    rw [MonoidHom.mem_ker, hθ, hψ] at hy
    rw [Subgroup.mem_bot]
    exact Subtype.ext hy
  let E₀ : Subgroup ρ.range := E.subgroupOf ρ.range
  have hE₀ : IsElemAbelian p E₀ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · refine Subtype.ext (Subtype.ext ?_)
      have := hE.1.is_comm.comm (⟨a.1.1, a.2⟩ : E) ⟨b.1.1, b.2⟩
      simpa using congrArg Subtype.val this
    · exact Subtype.ext (hE.2 x.1 hx)
  have hcard : Nat.card E₀ = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEρ).toEquiv
  have h1 := card_le_of_pRank_le hp (pRank_pgl_le hp hp2 hpK hn) (E₀.map θ)
    (CFSG.SectionRank.isElemAbelian_map hE₀ θ)
  rw [Subgroup.card_map_of_injective hθinj, hcard] at h1
  exact h1

end CFSG.HardMathSupport.Timmesfeld.LinearRank
