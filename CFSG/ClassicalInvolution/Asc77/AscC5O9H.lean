module

public import CFSG.ClassicalInvolution.Asc77.AscC5O9

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_kerLayer' {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {c g n : G}
    (hn : n ∈ kerLayer Ω c) : g * n * g⁻¹ ∈ kerLayer Ω (g * c * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · have h := Subgroup.mem_centralizer_singleton_iff.mp hn.1
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc g * n * g⁻¹ * (g * c * g⁻¹) = g * (n * c) * g⁻¹ := by group
      _ = g * (c * n) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * (g * n * g⁻¹) := by group
  · have h := trivialOnQuot_conjSub hn.2 g
    rwa [← exactLayer_conj hΩ] at h

theorem conjSub_kerLayer {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (c g : G) :
    conjSub g (kerLayer Ω c) = kerLayer Ω (g * c * g⁻¹) := by
  ext n
  rw [mem_conjSub_iff]
  constructor
  · intro hn
    have := conj_mem_kerLayer' hΩ (g := g) hn
    simpa [mul_assoc] using this
  · intro hn
    have := conj_mem_kerLayer' hΩ (g := g⁻¹) hn
    simpa [mul_assoc] using this

theorem conj_mem_oddCore_kerLayer' {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {c g o : G}
    (ho : o ∈ oddCoreIn (kerLayer Ω c)) :
    g * o * g⁻¹ ∈ oddCoreIn (kerLayer Ω (g * c * g⁻¹)) := by
  rw [← conjSub_kerLayer hΩ, oddCoreIn_conjSub_eq]
  exact ⟨o, ho, rfl⟩

theorem conj_mem_hSub {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {c τ c' τ' g y : G}
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G))
    (hτ' : τ' ∈ Subgroup.centralizer ({c'} : Set G)) (hc : g * c * g⁻¹ = c')
    (hgτ : g * τ * g⁻¹ ∈ hSub hΩ c' τ' hτ') (hy : y ∈ hSub hΩ c τ hτ) :
    g * y * g⁻¹ ∈ hSub hΩ c' τ' hτ' := by
  obtain ⟨w, ⟨k, rfl⟩, v, ⟨x, hx, o, ho, rfl⟩, rfl⟩ := hy
  have hx' : g * x * g⁻¹ ∈ exactLayer Ω c' := by
    rw [← hc, exactLayer_conj hΩ]
    exact ⟨x, hx, rfl⟩
  have ho' : g * o * g⁻¹ ∈ oddCoreIn (kerLayer Ω c') := by
    rw [← hc]; exact conj_mem_oddCore_kerLayer' hΩ ho
  have e : g * ((fun i : ℤ => τ ^ i) k * (x * o)) * g⁻¹ =
      (g * τ * g⁻¹) ^ k * ((g * x * g⁻¹) * (g * o * g⁻¹)) := by
    simp only [conj_zpow]
    group
  rw [e]
  exact mul_mem (zpow_mem hgτ k) (mul_mem (le_hSub_layer hΩ hτ' hx') (le_hSub_odd hΩ hτ' ho'))

theorem hSub_le_centralizer {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {c τ : G}
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G)) :
    hSub hΩ c τ hτ ≤ Subgroup.centralizer ({c} : Set G) := by
  rintro _ ⟨w, ⟨k, rfl⟩, v, ⟨x, hx, o, ho, rfl⟩, rfl⟩
  exact mul_mem (zpow_mem hτ k) (mul_mem (exactLayer_le_centralizer Ω c hx)
    (oddCoreIn_le _ ho).1)

omit [Finite G] in
theorem mem_centralizer_z_of {a z x : G} (ha : x ∈ Subgroup.centralizer ({a} : Set G))
    (haz : x ∈ Subgroup.centralizer ({a * z} : Set G)) :
    x ∈ Subgroup.centralizer ({z} : Set G) := by
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp ha
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp haz
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc x * z = a⁻¹ * (a * x) * z := by group
    _ = a⁻¹ * (x * a) * z := by rw [h1]
    _ = a⁻¹ * (x * (a * z)) := by group
    _ = a⁻¹ * ((a * z) * x) := by rw [h2]
    _ = z * x := by group

theorem hSub_inf_le {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {z a τ σ : G}
    (hτ : τ ∈ Subgroup.centralizer ({a} : Set G))
    (hσ : σ ∈ Subgroup.centralizer ({a * z} : Set G)) :
    hSub hΩ a τ hτ ⊓ hSub hΩ (a * z) σ hσ ≤ Subgroup.centralizer ({z} : Set G) :=
  fun _ hx => mem_centralizer_z_of (hSub_le_centralizer hΩ hτ hx.1)
    (hSub_le_centralizer hΩ hσ hx.2)

variable {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

structure Swaps (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ a τ σ : G) : Prop where
  ctx : Ctx p f Ω K K' W S R R' z t u₁ u₂ a
  τG : ∃ c : G, c * z * c⁻¹ = τ
  τa : τ * a = a * τ
  τz : τ * z = z * τ
  τn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ
  aτ : ¬ ∃ g : G, g * z * g⁻¹ = a * τ
  τX : τ ∈ exactLayer Ω (a * z)
  τK : conjSub τ K = K'
  σG : ∃ c : G, c * z * c⁻¹ = σ
  σa : σ * a = a * σ
  σz : σ * z = z * σ
  σn : ∀ h : G, h * (a * z) = (a * z) * h → h * z * h⁻¹ ≠ σ
  aσ : ¬ ∃ g : G, g * z * g⁻¹ = (a * z) * σ
  σX : σ ∈ exactLayer Ω a
  m : ∃ m ∈ exactLayer Ω (a * z), m * z * m⁻¹ = τ ∧ m * τ * m⁻¹ = z

namespace Swaps

variable {τ σ : G}

theorem τC (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ) :
    τ ∈ Subgroup.centralizer ({a} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr D.τa

theorem σC (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ) :
    σ ∈ Subgroup.centralizer ({a * z} : Set G) := by
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc σ * (a * z) = (σ * a) * z := by group
    _ = a * (σ * z) := by rw [D.σa]; group
    _ = a * z * σ := by rw [D.σz]; group

end Swaps

@[expose] def hBig {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (z a τ σ : G)
    (hτ : τ ∈ Subgroup.centralizer ({a} : Set G))
    (hσ : σ ∈ Subgroup.centralizer ({a * z} : Set G)) : Subgroup G :=
  mulSub (hSub hΩ a τ hτ ⊓ hSub hΩ (a * z) σ hσ)
    (oddCoreIn (Subgroup.centralizer ({z} : Set G)))
    (fun _ hx _ ho => conj_mem_oddCoreIn (hSub_inf_le hΩ hτ hσ hx) ho)

namespace Ctx

theorem mem_hSub_of_conj [IsSimpleGroup G] (hM : ModelFacts p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {τ : G}
    (hτC : τ ∈ Subgroup.centralizer ({a} : Set G)) (hτG : ∃ c : G, c * z * c⁻¹ = τ)
    (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ) (haτ : ¬ ∃ g : G, g * z * g⁻¹ = a * τ)
    {b : G} (hba : b * a = a * b) (hbG : ∃ c : G, c * z * c⁻¹ = b)
    (hbn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ b) :
    b ∈ hSub C.hyp.std.setting.stand.hyp.conjInvariant a τ hτC := by
  have hτa : τ * a = a * τ := Subgroup.mem_centralizer_singleton_iff.mp hτC
  rcases C.two_orbits hM hτa hτG hτn haτ hba hbG with ⟨h, hh, hhz⟩ | ⟨x, hx, n, hn, hodd, hxn⟩
  · exact absurd hhz (hbn h hh)
  · have hnO := C.mem_oddCore_of_odd hM.centerless hn hodd
    rw [← hxn]
    have hΩ := C.hyp.std.setting.stand.hyp.conjInvariant
    have hxH := le_hSub_layer hΩ hτC hx
    have hnH := le_hSub_odd hΩ hτC hnO
    exact mul_mem (mul_mem (mul_mem hxH hnH) (mem_hSub_self hΩ hτC)) (inv_mem (mul_mem hxH hnH))

theorem norm_fix_z [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {g : G}
    (hg : g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :
        Subgroup G) : Set G)) : g * z * g⁻¹ = z := by
  have hm := (Subgroup.mem_normalizer_iff.mp hg z).mp (T7T.z_mem_centralizer_of_hyp C.hyp)
  rcases C.hA0 _ hm with h | h | h | h
  · exfalso; apply C.hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · exact absurd h (C.not_conj_z g)
  · exact h
  · exact absurd h (C.swap.not_conj_z g)

theorem norm_a_cases [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {g : G}
    (hg : g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :
        Subgroup G) : Set G)) : g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a * z := by
  have hm := (Subgroup.mem_normalizer_iff.mp hg a).mp C.haA
  have hgz := C.norm_fix_z hg
  rcases C.hA0 _ hm with h | h | h | h
  · exfalso; apply C.ha1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · exact Or.inl h
  · exfalso
    apply C.not_conj_z g⁻¹
    calc g⁻¹ * z * g⁻¹⁻¹ = g⁻¹ * (g * a * g⁻¹) * g := by rw [h]; group
      _ = a := by group
  · exact Or.inr h

end Ctx

namespace Swaps

variable {τ σ : G}

theorem a_not_mem_hBig [IsSimpleGroup G] (hM : ModelFacts p f)
    (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ) :
    a ∉ hBig D.ctx.hyp.std.setting.stand.hyp.conjInvariant z a τ σ D.τC D.σC := by
  have C := D.ctx
  rintro ⟨h, hh, o, ho, hao⟩
  have hΩ := D.ctx.hyp.std.setting.stand.hyp.conjInvariant
  have hha : h * a = a * h :=
    Subgroup.mem_centralizer_singleton_iff.mp (hSub_le_centralizer hΩ D.τC hh.1)
  have he : h = a * o⁻¹ := by rw [hao]; group
  have hhia : h⁻¹ * a = a * h⁻¹ := by
    calc h⁻¹ * a = h⁻¹ * (a * h) * h⁻¹ := by group
      _ = h⁻¹ * (h * a) * h⁻¹ := by rw [hha]
      _ = a * h⁻¹ := by group
  have hoa : o * a = a * o := by
    have e : o = h⁻¹ * a := by rw [hao]; group
    rw [e]
    calc h⁻¹ * a * a = (a * h⁻¹) * a := by rw [hhia]
      _ = a * (h⁻¹ * a) := by group
  have hodd : Odd (orderOf o) := by
    have h1 : orderOf o ∣ Nat.card (oddCoreIn (Subgroup.centralizer ({z} : Set G))) := by
      have := orderOf_dvd_natCard (⟨o, ho⟩ : oddCoreIn (Subgroup.centralizer ({z} : Set G)))
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat (odd_card_oddCoreIn _) h1
  obtain ⟨j, hj⟩ := hodd
  have hcomm : Commute a o⁻¹ := by
    show a * o⁻¹ = o⁻¹ * a
    calc a * o⁻¹ = o⁻¹ * (o * a) * o⁻¹ := by group
      _ = o⁻¹ * (a * o) * o⁻¹ := by rw [hoa]
      _ = o⁻¹ * a := by group
  have hapow : a ^ (2 * j + 1) = a := by
    rw [pow_succ, pow_mul, sq, C.ha2, one_pow, one_mul]
  have hopow : o ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one o
  have hpow : h ^ (2 * j + 1) = a := by
    rw [he, hcomm.mul_pow, hapow, inv_pow, hopow, inv_one, mul_one]
  have haH : a ∈ hSub hΩ a τ D.τC := by
    have := pow_mem hh.1 (2 * j + 1)
    rwa [hpow] at this
  obtain ⟨cτ, hcτ⟩ := D.τG
  exact C.a_not_mem_hSub hM D.τC hcτ D.τn haH

theorem conj_mem_hInf [IsSimpleGroup G] (hM : ModelFacts p f)
    (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ) {g y : G}
    (hg : g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :
        Subgroup G) : Set G))
    (hy : y ∈ hSub D.ctx.hyp.std.setting.stand.hyp.conjInvariant a τ D.τC ⊓
      hSub D.ctx.hyp.std.setting.stand.hyp.conjInvariant (a * z) σ D.σC) :
    g * y * g⁻¹ ∈ hSub D.ctx.hyp.std.setting.stand.hyp.conjInvariant a τ D.τC ⊓
      hSub D.ctx.hyp.std.setting.stand.hyp.conjInvariant (a * z) σ D.σC := by
  have C := D.ctx
  have hΩ := D.ctx.hyp.std.setting.stand.hyp.conjInvariant
  have hgz := C.norm_fix_z hg
  obtain ⟨cτ, hcτ⟩ := D.τG
  obtain ⟨cσ, hcσ⟩ := D.σG
  have hconjG : ∀ (w c : G), c * z * c⁻¹ = w → (g * c) * z * (g * c)⁻¹ = g * w * g⁻¹ := by
    intro w c hc
    calc (g * c) * z * (g * c)⁻¹ = g * (c * z * c⁻¹) * g⁻¹ := by group
      _ = g * w * g⁻¹ := by rw [hc]
  have hpull : ∀ (b b' w : G), g * b * g⁻¹ = b' →
      (∀ h : G, h * b = b * h → h * z * h⁻¹ ≠ w) →
      ∀ h : G, h * b' = b' * h → h * z * h⁻¹ ≠ g * w * g⁻¹ := by
    intro b b' w hb hn h hh hhz
    apply hn (g⁻¹ * h * g)
    · calc g⁻¹ * h * g * b = g⁻¹ * (h * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * (h * b') * g := by rw [hb]
        _ = g⁻¹ * (b' * h) * g := by rw [hh]
        _ = g⁻¹ * ((g * b * g⁻¹) * h) * g := by rw [hb]
        _ = b * (g⁻¹ * h * g) := by group
    · calc g⁻¹ * h * g * z * (g⁻¹ * h * g)⁻¹ = g⁻¹ * (h * (g * z * g⁻¹) * h⁻¹) * g := by group
        _ = g⁻¹ * (g * w * g⁻¹) * g := by rw [hgz, hhz]
        _ = w := by group
  have hcomm : ∀ (b b' w : G), g * b * g⁻¹ = b' → w * b = b * w →
      (g * w * g⁻¹) * b' = b' * (g * w * g⁻¹) := by
    intro b b' w hb hw
    rw [← hb]
    calc g * w * g⁻¹ * (g * b * g⁻¹) = g * (w * b) * g⁻¹ := by group
      _ = g * (b * w) * g⁻¹ := by rw [hw]
      _ = g * b * g⁻¹ * (g * w * g⁻¹) := by group
  have hσaz : σ * (a * z) = (a * z) * σ := Subgroup.mem_centralizer_singleton_iff.mp D.σC
  have hτaz : τ * (a * z) = (a * z) * τ := by
    calc τ * (a * z) = (τ * a) * z := by group
      _ = a * (τ * z) := by rw [D.τa]; group
      _ = (a * z) * τ := by rw [D.τz]; group
  rcases C.norm_a_cases hg with ha | ha
  · have haz : g * (a * z) * g⁻¹ = a * z := by
      calc g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) := by group
        _ = a * z := by rw [ha, hgz]
    have hgτ : g * τ * g⁻¹ ∈ hSub hΩ a τ D.τC :=
      C.mem_hSub_of_conj hM D.τC D.τG D.τn D.aτ (hcomm a a τ ha D.τa) ⟨g * cτ, hconjG τ cτ hcτ⟩
        (hpull a a τ ha D.τn)
    have hgσ : g * σ * g⁻¹ ∈ hSub hΩ (a * z) σ D.σC :=
      C.swap.mem_hSub_of_conj hM D.σC D.σG D.σn D.aσ (hcomm (a * z) (a * z) σ haz hσaz)
        ⟨g * cσ, hconjG σ cσ hcσ⟩ (hpull (a * z) (a * z) σ haz D.σn)
    exact ⟨conj_mem_hSub hΩ D.τC D.τC ha hgτ hy.1,
      conj_mem_hSub hΩ D.σC D.σC haz hgσ hy.2⟩
  · have haz : g * (a * z) * g⁻¹ = a := by
      calc g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) := by group
        _ = a := by rw [ha, hgz, C.mul_z_mul_z]
    have hgτ : g * τ * g⁻¹ ∈ hSub hΩ (a * z) σ D.σC :=
      C.swap.mem_hSub_of_conj hM D.σC D.σG D.σn D.aσ (hcomm a (a * z) τ ha D.τa)
        ⟨g * cτ, hconjG τ cτ hcτ⟩ (hpull a (a * z) τ ha D.τn)
    have hgσ : g * σ * g⁻¹ ∈ hSub hΩ a τ D.τC :=
      C.mem_hSub_of_conj hM D.τC D.τG D.τn D.aτ (hcomm (a * z) a σ haz hσaz)
        ⟨g * cσ, hconjG σ cσ hcσ⟩ (hpull (a * z) a σ haz D.σn)
    exact ⟨conj_mem_hSub hΩ D.σC D.τC haz hgσ hy.2,
      conj_mem_hSub hΩ D.τC D.σC ha hgτ hy.1⟩

theorem conj_mem_hBig [IsSimpleGroup G] (hM : ModelFacts p f)
    (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ) {c y : G} (hc : c * z * c⁻¹ = z)
    (hy : y ∈ hBig D.ctx.hyp.std.setting.stand.hyp.conjInvariant z a τ σ D.τC D.σC) :
    c * y * c⁻¹ ∈ hBig D.ctx.hyp.std.setting.stand.hyp.conjInvariant z a τ σ D.τC D.σC := by
  have C := D.ctx
  have hΩ := D.ctx.hyp.std.setting.stand.hyp.conjInvariant
  obtain ⟨o₁, ho₁, hg⟩ := C.frattini hc
  obtain ⟨h, hh, o, ho, rfl⟩ := hy
  set g := o₁⁻¹ * c with hgdef
  have hcz : c ∈ Subgroup.centralizer ({z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc c * z = (c * z * c⁻¹) * c := by group
      _ = z * c := by rw [hc]
  have ho₁z : o₁ ∈ Subgroup.centralizer ({z} : Set G) := oddCoreIn_le _ ho₁
  have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := mul_mem (inv_mem ho₁z) hcz
  have hh' := conj_mem_hInf hM D hg hh
  have hh'z := hSub_inf_le hΩ D.τC D.σC hh'
  have ho' : g * o * g⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
    conj_mem_oddCoreIn hgz ho
  have ho₁' : (g * h * g⁻¹)⁻¹ * o₁ * (g * h * g⁻¹)⁻¹⁻¹ ∈
      oddCoreIn (Subgroup.centralizer ({z} : Set G)) := conj_mem_oddCoreIn (inv_mem hh'z) ho₁
  refine ⟨g * h * g⁻¹, hh', ((g * h * g⁻¹)⁻¹ * o₁ * (g * h * g⁻¹)⁻¹⁻¹) * (g * o * g⁻¹) * o₁⁻¹,
    mul_mem (mul_mem ho₁' ho') (inv_mem ho₁), ?_⟩
  rw [hgdef]
  group

theorem extremal_mem_hBig [IsSimpleGroup G] (hM : ModelFacts p f)
    (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ) {g : G}
    (hg : (g⁻¹ * a * g) * z = z * (g⁻¹ * a * g)) :
    a⁻¹ * (g⁻¹ * a * g) ∈
      hBig D.ctx.hyp.std.setting.stand.hyp.conjInvariant z a τ σ D.τC D.σC := by
  have C := D.ctx
  have hΩ := D.ctx.hyp.std.setting.stand.hyp.conjInvariant
  obtain ⟨hzY, -, -, -, -, -⟩ := C.om5
  obtain ⟨hzY', -, -, -, -, -⟩ := C.swap.om5
  set H := hBig hΩ z a τ σ D.τC D.σC with hH
  have hzH₀ : z ∈ hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC :=
    ⟨le_hSub_layer hΩ D.τC hzY, le_hSub_layer hΩ D.σC hzY'⟩
  have hτH₀ : τ ∈ hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC :=
    ⟨mem_hSub_self hΩ D.τC, le_hSub_layer hΩ D.σC D.τX⟩
  have hzH : z ∈ H := le_mulSub_left _ hzH₀
  have hτH : τ ∈ H := le_mulSub_left _ hτH₀
  have hOH : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ H := le_mulSub_right _
  have hconj : ∀ c : G, c * z * c⁻¹ = z → a⁻¹ * (c * a * c⁻¹) ∈ H := by
    intro c hc
    obtain ⟨o, ho, h | h⟩ := C.conj_a_mem hc
    · rw [h]
      have e : a⁻¹ * (a * o) = o := by group
      rw [e]; exact hOH ho
    · rw [h]
      have e : a⁻¹ * (a * z * o) = z * o := by group
      rw [e]; exact mul_mem hzH (hOH ho)
  obtain ⟨m, hmX, hmz, hmτ⟩ := D.m
  have hm : m * (a * z) = (a * z) * m :=
    Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω (a * z) hmX)
  have hg' : (g⁻¹ * a * g⁻¹⁻¹) * z = z * (g⁻¹ * a * g⁻¹⁻¹) := by rw [inv_inv]; exact hg
  rcases C.pair_count hM D.τa D.τG D.τn D.aτ hm hmz hmτ hg' with ⟨c, hc, hca⟩ | ⟨c, hc, hca⟩
  · rw [inv_inv] at hca
    rw [← hca]
    exact hconj c hc
  · rw [inv_inv] at hca
    rw [← hca]
    have e : a⁻¹ * (c * (a * z * τ) * c⁻¹) = (a⁻¹ * (c * a * c⁻¹)) * (c * (z * τ) * c⁻¹) := by
      group
    rw [e]
    exact mul_mem (hconj c hc) (conj_mem_hBig hM D hc (mul_mem hzH hτH))

end Swaps

end CFSG.ClassicalInvolution.Asc77.C5O
