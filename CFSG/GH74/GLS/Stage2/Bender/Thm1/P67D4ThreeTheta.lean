module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4BypassCore
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Phi36Plane

public section

open Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section Generic

variable {Y : Type} [Group Y]

theorem mul_mul_inv_mem_commutator_of_mem {C : Subgroup Y} {c u : Y} (hc : c ∈ C)
    (hu : u ∈ ⁅C, C⁆) : c * u * c⁻¹ ∈ ⁅C, C⁆ := by
  have h1 : (MulAut.conj c).toMonoidHom '' (C : Set Y) ⊆ C := by
    rintro _ ⟨a, ha, rfl⟩
    exact C.mul_mem (C.mul_mem hc ha) (C.inv_mem hc)
  have h2 : ⁅C.map (MulAut.conj c).toMonoidHom, C.map (MulAut.conj c).toMonoidHom⁆ ≤ ⁅C, C⁆ :=
    Subgroup.commutator_mono (fun y hy => by
      obtain ⟨a, ha, rfl⟩ := hy
      exact h1 ⟨a, ha, rfl⟩) (fun y hy => by
      obtain ⟨a, ha, rfl⟩ := hy
      exact h1 ⟨a, ha, rfl⟩)
  rw [← Subgroup.map_commutator] at h2
  exact h2 ⟨u, hu, rfl⟩

theorem fix_pointwise_of_quasisimple_line (hcen : Subgroup.center Y = ⊥) {r : ℕ}
    {V Z : Subgroup (MulAut Y)} (h2 : N2Cfg Y r V Z) (h3 : N3Full Y V Z) {x : Y}
    (hx1 : (MulAut.conj x : MulAut Y) ≠ 1)
    (hxV : (MulAut.conj x : MulAut Y) ∈ V)
    (hqs : CFSG.IsQuasisimple
      ↥(⁅centralizer ({x} : Set Y), centralizer ({x} : Set Y)⁆ : Subgroup Y)) :
    ∀ z ∈ Z, ∀ u ∈ (⁅centralizer ({x} : Set Y), centralizer ({x} : Set Y)⁆ : Subgroup Y),
      z u = u := by
  obtain ⟨-, -, -, -, hZab, -, -, -, hcomm⟩ := h2
  set F : Subgroup Y := fixSub (MulAut.conj x) with hF
  have hFC : F = centralizer ({x} : Set Y) := by
    ext c
    rw [hF, mem_fixSub, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc c * x = x * c * x⁻¹ * x := by rw [h]
        _ = x * c := by group
    · intro h
      calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [h]
        _ = c := by group
  set L : Subgroup Y := ⁅centralizer ({x} : Set Y), centralizer ({x} : Set Y)⁆ with hL
  have hLF : L ≤ F := by
    rw [hFC, hL, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hLnorm : ∀ c ∈ F, ∀ u ∈ L, c * u * c⁻¹ ∈ L := fun c hc u hu =>
    mul_mul_inv_mem_commutator_of_mem (hFC ▸ hc) hu
  set N₀ : Subgroup Y := (Z.comap (MulAut.conj : Y →* MulAut Y)) ⊓ F with hN₀
  have hN₀mem : ∀ c : Y, c ∈ N₀ ↔ MulAut.conj c ∈ Z ∧ c ∈ F := fun c => Iff.rfl
  have hN₀F : N₀ ≤ F := inf_le_right
  have hN₀norm : ∀ f ∈ F, ∀ y ∈ N₀, f * y * f⁻¹ ∈ N₀ := by
    intro f hf y hy
    obtain ⟨hyZ, hyF⟩ := (hN₀mem y).1 hy
    have hgN := h3 _ hxV hx1 f hf
    have h1 := (Subgroup.mem_normalizer_iff.1 hgN _).1 hyZ
    refine (hN₀mem _).2 ⟨?_, F.mul_mem (F.mul_mem hf hyF) (F.inv_mem hf)⟩
    simpa [map_mul, map_inv] using h1
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    mulAut_conj_injective_of_center_bot hcen
  have hN₀ab : ∀ a ∈ N₀, ∀ b ∈ N₀, a * b = b * a := by
    intro a ha b hb
    apply hinj
    simp only [map_mul]
    exact hZab _ ((hN₀mem a).1 ha).1 _ ((hN₀mem b).1 hb).1
  have hcommL := abelian_normal_commutes_of_quasisimple F L hLF hLnorm hqs N₀ hN₀F hN₀norm hN₀ab
  intro z hz u hu
  have hzF : ∀ c ∈ F, z c ∈ F := by
    intro c hc
    rw [hF, mem_fixSub] at hc ⊢
    have h1 := congrArg (fun t : MulAut Y => t c) (hcomm _ hxV z hz)
    simp only [MulAut.mul_apply] at h1
    rw [h1, hc]
  have hφmem : ∀ c ∈ F, c * z c⁻¹ ∈ N₀ := by
    intro c hc
    have hnorm := h3 _ hxV hx1 c hc
    have h1 := (Subgroup.mem_normalizer_iff.1 hnorm z).1 hz
    have h4 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ ∈ Z :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hz)
    have h5 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (c * z c⁻¹) := by
      have : z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (z c⁻¹) := by
        have := mulAut_conj_conj z c⁻¹
        simpa [map_inv] using this
      calc MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹
          = MulAut.conj c * (z * (MulAut.conj c)⁻¹ * z⁻¹) := by group
        _ = MulAut.conj (c * z c⁻¹) := by rw [this, map_mul]
    rw [h5] at h4
    refine (hN₀mem _).2 ⟨h4, F.mul_mem hc ?_⟩
    rw [map_inv]
    exact F.inv_mem (hzF c hc)
  have hperf : commutator ↥L = ⊤ := Group.isPerfect_def.1 hqs.1
  let φ : ↥L →* ↥N₀ :=
    { toFun := fun a => ⟨(a : Y) * z (a : Y)⁻¹, hφmem a (hLF a.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        have hb := hφmem b (hLF b.2)
        have hc : ((b : Y) * z (b : Y)⁻¹) * (a : Y) = (a : Y) * ((b : Y) * z (b : Y)⁻¹) :=
          hcommL _ hb a a.2
        have hab := hN₀ab _ hb _ (hφmem a (hLF a.2))
        change (a : Y) * (b : Y) * z ((a : Y) * (b : Y))⁻¹ =
          ((a : Y) * z (a : Y)⁻¹) * ((b : Y) * z (b : Y)⁻¹)
        calc (a : Y) * (b : Y) * z ((a : Y) * (b : Y))⁻¹
            = (a : Y) * ((b : Y) * z (b : Y)⁻¹) * z (a : Y)⁻¹ := by
              rw [mul_inv_rev, map_mul]
              group
          _ = ((b : Y) * z (b : Y)⁻¹) * (a : Y) * z (a : Y)⁻¹ := by rw [hc]
          _ = ((b : Y) * z (b : Y)⁻¹) * ((a : Y) * z (a : Y)⁻¹) := by group
          _ = ((a : Y) * z (a : Y)⁻¹) * ((b : Y) * z (b : Y)⁻¹) := hab }
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    have hZcomm : ∀ u v : ↥N₀, u * v = v * u := fun u v => Subtype.ext (hN₀ab _ u.2 _ v.2)
    rw [hZcomm (φ a) (φ b)]
    simp
  have h1 : φ ⟨u, hu⟩ = 1 := by
    have : (⟨u, hu⟩ : ↥L) ∈ φ.ker := hker ▸ Subgroup.mem_top _
    exact this
  have h2 : u * z u⁻¹ = 1 := congrArg Subtype.val h1
  have h3' : z u⁻¹ = u⁻¹ := by
    have := congrArg (fun t => u⁻¹ * t) h2
    simpa using this
  have := congrArg (fun t => t⁻¹) h3'
  simpa using this

end Generic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

theorem inner_of_singular_line {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 3 V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hx1 : x ≠ 1)
    (hxV : (MulAut.conj x : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈ V)
    (hdata : SingularCentralizerData σ (p ^ f) x) :
    ∀ z ∈ Z, z ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
  classical
  intro z hz
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := mulAut_conj_injective_of_center_bot hcen
  have hx1' : (MulAut.conj x : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≠ 1 :=
    fun h => hx1 (hinj (by rw [h, map_one]))
  have hfix := fix_pointwise_of_quasisimple_line hcen h2 h3 hx1' hxV hdata.1 z hz
  obtain ⟨t3, ht3⟩ := pow_three_mem_range_of_fixes_singular hp hf K hK σ hσ hdata z hfix
  obtain ⟨-, -, -, -, -, -, hZcop, -, -⟩ := h2
  by_cases hz1 : z = 1
  · exact ⟨1, by rw [map_one, hz1]⟩
  have hdvd : orderOf z ∣ Nat.card Z := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : Z)
    rwa [← Subgroup.orderOf_coe] at this
  have hcop : Nat.Coprime 3 (orderOf z) :=
    Nat.Coprime.coprime_dvd_right hdvd hZcop.symm
  have hord1 : 1 < orderOf z := by
    rcases Nat.lt_or_ge 1 (orderOf z) with h | h
    · exact h
    · exfalso
      have : orderOf z = 1 := by
        have := orderOf_pos z
        omega
      exact hz1 (orderOf_eq_one_iff.1 this)
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hord1
  refine ⟨t3 ^ k, ?_⟩
  rw [map_pow, ht3, ← pow_mul, ← pow_mod_orderOf, hk, pow_one]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
