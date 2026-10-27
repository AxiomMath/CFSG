module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHFixed

public section

namespace CFSG.EvenSporadicStandard.M24Std.DResH

open Subgroup Fixed

namespace Heisenberg

variable {V : Type*} [CommGroup V]

def cube (x : MulAut V) (v : V) : V := v * x v * x (x v)

theorem cube_mul (x : MulAut V) (u v : V) : cube x (u * v) = cube x u * cube x v := by
  simp only [cube, map_mul]
  ac_rfl

theorem apply_cube (x : MulAut V) (hx : x * x * x = 1) (v : V) : x (cube x v) = cube x v := by
  have h3 : x (x (x v)) = v := by
    have := congrArg (fun f : MulAut V => f v) hx
    simpa using this
  simp only [cube, map_mul, h3]
  ac_rfl

theorem cube_of_fixed (hV2 : ∀ v : V, v * v = 1) (x : MulAut V) {v : V} (hv : x v = v) :
    cube x v = v := by
  simp only [cube, hv]
  rw [hV2 v, one_mul]

theorem cube_mem {x : MulAut V} {U : Subgroup V} (hU : ∀ u ∈ U, x u ∈ U) {u : V} (hu : u ∈ U) :
    cube x u ∈ U :=
  U.mul_mem (U.mul_mem hu (hU u hu)) (hU _ (hU u hu))

theorem cube_eq_one_of_conj (ζ y x : MulAut V) (hx : x = ζ * y) (hcomm : ζ * y = y * ζ)
    (hζ : ∀ v : V, v * ζ v * ζ (ζ v) = 1) {c : V} (hc : y c = c) : cube x c = 1 := by
  subst hx
  have h1 : (ζ * y) c = ζ c := by simp [hc]
  have h2 : (ζ * y) ((ζ * y) c) = ζ (ζ c) := by
    rw [h1]
    have : y (ζ c) = ζ c := by
      have := congrArg (fun f : MulAut V => f c) hcomm
      simp only [MulAut.mul_apply, hc] at this
      exact this.symm
    simp [this]
  rw [cube, h2, h1]
  exact hζ c

theorem cube_omega (ω : MulAut V) (hω3 : ω * ω * ω = 1) (hωfpf : ∀ v : V, ω v = v → v = 1)
    (v : V) : v * ω v * ω (ω v) = 1 :=
  hωfpf _ (apply_cube ω hω3 v)

theorem cube_omega_sq (ω : MulAut V) (hω3 : ω * ω * ω = 1) (hωfpf : ∀ v : V, ω v = v → v = 1)
    (v : V) : v * (ω * ω) v * (ω * ω) ((ω * ω) v) = 1 := by
  have h3 : ∀ y, ω (ω (ω y)) = y := fun y => by
    have := congrArg (fun f : MulAut V => f y) hω3
    simpa using this
  have h := cube_omega ω hω3 hωfpf v
  simp only [MulAut.mul_apply, h3]
  rw [mul_right_comm]
  exact h

theorem cube_sum (hV2 : ∀ v : V, v * v = 1) (ω β : MulAut V) (hω3 : ω * ω * ω = 1)
    (hωfpf : ∀ v : V, ω v = v → v = 1) (hωβ : β * ω = ω * β) (v : V) :
    cube β v * cube (ω * β) v * cube (ω * ω * β) v = v := by
  have h3 : ∀ y, ω (ω (ω y)) = y := fun y => by
    have := congrArg (fun f : MulAut V => f y) hω3
    simpa using this
  have hβω : ∀ y, β (ω y) = ω (β y) := fun y => by
    have := congrArg (fun f : MulAut V => f y) hωβ
    simpa using this
  have e1 := cube_omega ω hω3 hωfpf (β v)
  have e2 := cube_omega ω hω3 hωfpf (β (β v))
  have e3 : v * v * v = v := by rw [hV2 v, one_mul]
  simp only [cube, MulAut.mul_apply, hβω, h3]
  calc v * β v * β (β v) * (v * ω (β v) * ω (ω (β (β v)))) *
        (v * ω (ω (β v)) * ω (β (β v)))
      = (v * v * v) * (β v * ω (β v) * ω (ω (β v))) *
        (β (β v) * ω (ω (β (β v))) * ω (β (β v))) := by ac_rfl
    _ = v := by
      rw [e3, e1, mul_one, mul_right_comm (β (β v)), e2, mul_one]

theorem mul_cube_of_comm {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    a * b * (a * b) * (a * b) = a * a * a * (b * b * b) := by
  have hc : Commute a b := h
  have := hc.mul_pow 3
  simpa only [pow_three'] using this

theorem card_le_of_apply [Finite V] (U : Subgroup V) (α x y : MulAut V)
    (hUα : ∀ u ∈ U, α u ∈ U) (h : y * α = α * x) :
    Nat.card (U ⊓ fixedSubgroupAut x : Subgroup V) ≤
      Nat.card (U ⊓ fixedSubgroupAut y : Subgroup V) := by
  refine Nat.card_le_card_of_injective
    (fun c : (U ⊓ fixedSubgroupAut x : Subgroup V) => (⟨α c, ?_⟩ :
      (U ⊓ fixedSubgroupAut y : Subgroup V))) ?_
  · obtain ⟨hcU, hcx⟩ := mem_inf.1 c.2
    refine mem_inf.2 ⟨hUα _ hcU, mem_fixedSubgroupAut.2 ?_⟩
    have h1 := congrArg (fun f : MulAut V => f c) h
    have hcx' : x c = c := mem_fixedSubgroupAut.1 hcx
    simpa [hcx'] using h1
  · intro c c' hcc
    exact Subtype.ext (α.injective (congrArg Subtype.val hcc))

theorem card_decomp [Finite V] (hV2 : ∀ v : V, v * v = 1) (x0 x1 x2 : MulAut V) (U : Subgroup V)
    (h0 : x0 * x0 * x0 = 1) (h1 : x1 * x1 * x1 = 1) (h2 : x2 * x2 * x2 = 1)
    (hU0 : ∀ u ∈ U, x0 u ∈ U) (hU1 : ∀ u ∈ U, x1 u ∈ U) (hU2 : ∀ u ∈ U, x2 u ∈ U)
    (h01 : ∀ c, x1 c = c → cube x0 c = 1) (h02 : ∀ c, x2 c = c → cube x0 c = 1)
    (h10 : ∀ c, x0 c = c → cube x1 c = 1) (h12 : ∀ c, x2 c = c → cube x1 c = 1)
    (h20 : ∀ c, x0 c = c → cube x2 c = 1) (h21 : ∀ c, x1 c = c → cube x2 c = 1)
    (hsum : ∀ v, cube x0 v * cube x1 v * cube x2 v = v) :
    Nat.card U = Nat.card (U ⊓ fixedSubgroupAut x0 : Subgroup V) *
      (Nat.card (U ⊓ fixedSubgroupAut x1 : Subgroup V) *
        Nat.card (U ⊓ fixedSubgroupAut x2 : Subgroup V)) := by
  let S0 : Subgroup V := U ⊓ fixedSubgroupAut x0
  let S1 : Subgroup V := U ⊓ fixedSubgroupAut x1
  let S2 : Subgroup V := U ⊓ fixedSubgroupAut x2
  have mem0 : ∀ a : V, a ∈ S0 ↔ a ∈ U ∧ x0 a = a := fun a => by
    rw [mem_inf, mem_fixedSubgroupAut]
  have mem1 : ∀ a : V, a ∈ S1 ↔ a ∈ U ∧ x1 a = a := fun a => by
    rw [mem_inf, mem_fixedSubgroupAut]
  have mem2 : ∀ a : V, a ∈ S2 ↔ a ∈ U ∧ x2 a = a := fun a => by
    rw [mem_inf, mem_fixedSubgroupAut]
  let F : S0 × S1 × S2 → U := fun p =>
    ⟨p.1.1 * p.2.1.1 * p.2.2.1, U.mul_mem (U.mul_mem ((mem0 _).1 p.1.2).1 ((mem1 _).1 p.2.1.2).1)
      ((mem2 _).1 p.2.2.2).1⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨c', hc'⟩⟩ h
      have h' : a * b * c = a' * b' * c' := congrArg Subtype.val h
      have e0 : ∀ a b c : V, x0 a = a → x1 b = b → x2 c = c → cube x0 (a * b * c) = a :=
        fun a b c ha hb hc => by
          rw [cube_mul, cube_mul, cube_of_fixed hV2 x0 ha, h01 b hb, h02 c hc, mul_one, mul_one]
      have e1 : ∀ a b c : V, x0 a = a → x1 b = b → x2 c = c → cube x1 (a * b * c) = b :=
        fun a b c ha hb hc => by
          rw [cube_mul, cube_mul, cube_of_fixed hV2 x1 hb, h10 a ha, h12 c hc, one_mul, mul_one]
      have e2 : ∀ a b c : V, x0 a = a → x1 b = b → x2 c = c → cube x2 (a * b * c) = c :=
        fun a b c ha hb hc => by
          rw [cube_mul, cube_mul, cube_of_fixed hV2 x2 hc, h20 a ha, h21 b hb, one_mul, one_mul]
      obtain ⟨-, fa⟩ := (mem0 a).1 ha
      obtain ⟨-, fb⟩ := (mem1 b).1 hb
      obtain ⟨-, fc⟩ := (mem2 c).1 hc
      obtain ⟨-, fa'⟩ := (mem0 a').1 ha'
      obtain ⟨-, fb'⟩ := (mem1 b').1 hb'
      obtain ⟨-, fc'⟩ := (mem2 c').1 hc'
      have ea : a = a' := by
        rw [← e0 a b c fa fb fc, ← e0 a' b' c' fa' fb' fc', h']
      have eb : b = b' := by
        rw [← e1 a b c fa fb fc, ← e1 a' b' c' fa' fb' fc', h']
      have ec : c = c' := by
        rw [← e2 a b c fa fb fc, ← e2 a' b' c' fa' fb' fc', h']
      subst ea eb ec
      rfl
    · rintro ⟨u, hu⟩
      refine ⟨(⟨cube x0 u, (mem0 _).2 ⟨cube_mem hU0 hu, apply_cube x0 h0 u⟩⟩,
        ⟨cube x1 u, (mem1 _).2 ⟨cube_mem hU1 hu, apply_cube x1 h1 u⟩⟩,
        ⟨cube x2 u, (mem2 _).2 ⟨cube_mem hU2 hu, apply_cube x2 h2 u⟩⟩), ?_⟩
      exact Subtype.ext (hsum u)
  have hcard := Nat.card_congr (Equiv.ofBijective F hF)
  rw [← hcard, Nat.card_prod, Nat.card_prod]

theorem fixedSubgroupAut_invariant {x y : MulAut V} (h : x * y = y * x) :
    ∀ u ∈ fixedSubgroupAut x, y u ∈ fixedSubgroupAut x := by
  intro u hu
  rw [mem_fixedSubgroupAut] at hu ⊢
  have := congrArg (fun f : MulAut V => f u) h
  simp only [MulAut.mul_apply, hu] at this
  exact this

end Heisenberg

open Heisenberg

theorem card_eq_cube_of_heisenberg {V : Type*} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v * v = 1) (ω α β : MulAut V) (hω3 : ω * ω * ω = 1)
    (hωfpf : ∀ v : V, ω v = v → v = 1) (hβ3 : β * β * β = 1) (hωβ : β * ω = ω * β)
    (hωα : α * ω = ω * α) (hαβ : α * β = ω * β * α) (U : Subgroup V)
    (hUω : ∀ u ∈ U, ω u ∈ U) (hUβ : ∀ u ∈ U, β u ∈ U) (hUα : ∀ u ∈ U, α u ∈ U) :
    Nat.card U = Nat.card (U ⊓ fixedSubgroupAut β : Subgroup V) ^ 3 := by
  have hc : Commute ω β := hωβ.symm
  have hcω : Commute ω ω := Commute.refl ω
  have hc1 : Commute ω (ω * β) := hcω.mul_right hc
  have hcω2 : Commute ω (ω * ω) := hcω.mul_right hcω
  have hc2 : Commute ω (ω * ω * β) := hcω2.mul_right hc
  have hd0 : Commute (ω * ω) β := hc.mul_left hc
  have hd1 : Commute (ω * ω) (ω * β) := hc1.mul_left hc1
  have hd2 : Commute (ω * ω) (ω * ω * β) := hc2.mul_left hc2
  have hx1 : (ω * β) * (ω * β) * (ω * β) = 1 := by
    rw [mul_cube_of_comm hc.eq, hω3, hβ3, mul_one]
  have hx2 : (ω * ω * β) * (ω * ω * β) * (ω * ω * β) = 1 := by
    rw [mul_cube_of_comm hd0.eq, hβ3, mul_one]
    calc ω * ω * (ω * ω) * (ω * ω) = (ω * ω * ω) * (ω * ω * ω) := by group
      _ = 1 := by rw [hω3, one_mul]
  have hζ1 := cube_omega ω hω3 hωfpf
  have hζ2 := cube_omega_sq ω hω3 hωfpf
  have hx01 : β = ω * ω * (ω * β) := by
    calc β = (ω * ω * ω) * β := by rw [hω3, one_mul]
      _ = ω * ω * (ω * β) := by group
  have hx02 : β = ω * (ω * ω * β) := by
    calc β = (ω * ω * ω) * β := by rw [hω3, one_mul]
      _ = ω * (ω * ω * β) := by group
  have hx12 : ω * β = ω * ω * (ω * ω * β) := by
    calc ω * β = ((ω * ω * ω) * ω) * β := by rw [hω3, one_mul]
      _ = ω * ω * (ω * ω * β) := by group
  have hcard := card_decomp hV2 β (ω * β) (ω * ω * β) U hβ3 hx1 hx2 hUβ
    (fun u hu => hUω _ (hUβ u hu)) (fun u hu => hUω _ (hUω _ (hUβ u hu)))
    (fun c hc' => cube_eq_one_of_conj (ω * ω) (ω * β) β hx01 hd1.eq hζ2 hc')
    (fun c hc' => cube_eq_one_of_conj ω (ω * ω * β) β hx02 hc2.eq hζ1 hc')
    (fun c hc' => cube_eq_one_of_conj ω β (ω * β) rfl hc.eq hζ1 hc')
    (fun c hc' => cube_eq_one_of_conj (ω * ω) (ω * ω * β) (ω * β) hx12 hd2.eq hζ2 hc')
    (fun c hc' => cube_eq_one_of_conj (ω * ω) β (ω * ω * β) rfl hd0.eq hζ2 hc')
    (fun c hc' => cube_eq_one_of_conj ω (ω * β) (ω * ω * β) (mul_assoc ω ω β) hc1.eq hζ1 hc')
    (cube_sum hV2 ω β hω3 hωfpf hωβ)
  have r1 : (ω * β) * α = α * β := hαβ.symm
  have r2 : (ω * ω * β) * α = α * (ω * β) := by
    calc (ω * ω * β) * α = ω * (ω * β * α) := by group
      _ = ω * (α * β) := by rw [hαβ]
      _ = (ω * α) * β := by group
      _ = (α * ω) * β := by rw [hωα]
      _ = α * (ω * β) := by group
  have r3 : β * α = α * (ω * ω * β) := by
    have hα2 : α * (ω * ω) = (ω * ω) * α := by
      calc α * (ω * ω) = (α * ω) * ω := by group
        _ = (ω * α) * ω := by rw [hωα]
        _ = ω * (α * ω) := by group
        _ = ω * (ω * α) := by rw [hωα]
        _ = (ω * ω) * α := by group
    calc β * α = (ω * ω * ω) * β * α := by rw [hω3, one_mul]
      _ = (ω * ω) * (ω * β * α) := by group
      _ = (ω * ω) * (α * β) := by rw [hαβ]
      _ = ((ω * ω) * α) * β := by group
      _ = (α * (ω * ω)) * β := by rw [hα2]
      _ = α * (ω * ω * β) := by group
  have c01 := card_le_of_apply U α β (ω * β) hUα r1
  have c12 := card_le_of_apply U α (ω * β) (ω * ω * β) hUα r2
  have c20 := card_le_of_apply U α (ω * ω * β) β hUα r3
  have e1 : Nat.card (U ⊓ fixedSubgroupAut (ω * β) : Subgroup V) =
      Nat.card (U ⊓ fixedSubgroupAut β : Subgroup V) := le_antisymm (c12.trans c20) c01
  have e2 : Nat.card (U ⊓ fixedSubgroupAut (ω * ω * β) : Subgroup V) =
      Nat.card (U ⊓ fixedSubgroupAut β : Subgroup V) := le_antisymm c20 (c01.trans c12)
  rw [hcard, e1, e2]
  ring

theorem false_of_two_heisenberg {V : Type*} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v * v = 1)
    (hV : Nat.card V = 2 ^ 12) (ω α β γ δ : MulAut V)
    (hω3 : ω * ω * ω = 1) (hωfpf : ∀ v : V, ω v = v → v = 1)
    (hβ3 : β * β * β = 1) (hδ3 : δ * δ * δ = 1)
    (hωα : α * ω = ω * α) (hωβ : β * ω = ω * β) (hωγ : γ * ω = ω * γ) (hωδ : δ * ω = ω * δ)
    (hβγ : β * γ = γ * β) (hβδ : β * δ = δ * β)
    (hαβ : α * β = ω * β * α) (hγδ : γ * δ = ω * δ * γ ∨ γ * δ = ω⁻¹ * δ * γ) : False := by
  have h1 := card_eq_cube_of_heisenberg hV2 ω α β hω3 hωfpf hβ3 hωβ hωα hαβ ⊤
    (fun _ _ => mem_top _) (fun _ _ => mem_top _) (fun _ _ => mem_top _)
  rw [Subgroup.card_top, hV, top_inf_eq] at h1
  obtain ⟨ω', h3', hfpf', hδω', hγω', hβω', hγδ'⟩ : ∃ ω' : MulAut V, ω' * ω' * ω' = 1 ∧
      (∀ v : V, ω' v = v → v = 1) ∧ δ * ω' = ω' * δ ∧ γ * ω' = ω' * γ ∧ β * ω' = ω' * β ∧
      γ * δ = ω' * δ * γ := by
    rcases hγδ with h | h
    · exact ⟨ω, hω3, hωfpf, hωδ, hωγ, hωβ, h⟩
    · refine ⟨ω⁻¹, ?_, ?_, ?_, ?_, ?_, h⟩
      · calc ω⁻¹ * ω⁻¹ * ω⁻¹ = (ω * ω * ω)⁻¹ := by group
          _ = 1 := by rw [hω3, inv_one]
      · intro v hv
        apply hωfpf
        have h2 : ω (ω⁻¹ v) = v := by simp
        rw [hv] at h2
        exact h2
      · exact (Commute.inv_right (show Commute δ ω from hωδ)).eq
      · exact (Commute.inv_right (show Commute γ ω from hωγ)).eq
      · exact (Commute.inv_right (show Commute β ω from hωβ)).eq
  have h2 := card_eq_cube_of_heisenberg hV2 ω' γ δ h3' hfpf' hδ3 hδω' hγω' hγδ'
    (fixedSubgroupAut β) (fixedSubgroupAut_invariant hβω') (fixedSubgroupAut_invariant hβδ)
    (fixedSubgroupAut_invariant hβγ)
  have hdvd : Nat.card (fixedSubgroupAut β ⊓ fixedSubgroupAut δ : Subgroup V) ∣ 2 ^ 12 := by
    rw [← hV]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [h2, hk'] at h1
  have h3 : (2 : ℕ) ^ 12 = 2 ^ (9 * k) := by
    rw [h1]
    ring
  have := Nat.pow_right_injective (le_refl 2) h3
  omega

end CFSG.EvenSporadicStandard.M24Std.DResH
