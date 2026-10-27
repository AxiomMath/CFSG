module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Twin
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMShape

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open scoped commutatorElement

section Class2

variable {G : Type*} [Group G]

theorem comm_two_class2 (x y c : G) (hyx : y * x = c * (x * y)) (hcy : c * y = y * c) :
    y * y * x = c * c * (x * (y * y)) := by
  have hyc : y * c = c * y := hcy.symm
  calc y * y * x = y * (y * x) := by group
    _ = y * (c * (x * y)) := by rw [hyx]
    _ = c * (y * x) * y := by rw [← mul_assoc y c, hyc]; group
    _ = c * (c * (x * y)) * y := by rw [hyx]
    _ = c * c * (x * (y * y)) := by group

theorem comm_commute_two (x c : G) (hcx : c * x = x * c) :
    x * x * (c * c) = c * c * (x * x) := by
  have hxc : x * c = c * x := hcx.symm
  calc x * x * (c * c) = x * (x * c) * c := by group
    _ = x * (c * x) * c := by rw [hxc]
    _ = (x * c) * x * c := by group
    _ = (c * x) * x * c := by rw [hxc]
    _ = c * (x * (x * c)) := by group
    _ = c * (x * (c * x)) := by rw [hxc]
    _ = c * ((x * c) * x) := by group
    _ = c * ((c * x) * x) := by rw [hxc]
    _ = c * c * (x * x) := by group

theorem pow_three_class2 (x y c : G) (hyx : y * x = c * (x * y)) (hcx : c * x = x * c)
    (hcy : c * y = y * c) : (x * y) ^ 3 = c ^ 3 * (x ^ 3 * y ^ 3) := by
  have hxc : x * c = c * x := hcx.symm
  have h2 := comm_two_class2 x y c hyx hcy
  have h4 := comm_commute_two x c hcx
  calc (x * y) ^ 3 = x * (y * x) * y * x * y := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = x * (c * (x * y)) * y * x * y := by rw [hyx]
    _ = c * (x * x) * (y * y * x) * y := by
      rw [show x * (c * (x * y)) = c * (x * (x * y)) by rw [← mul_assoc x c, hxc]; group]
      group
    _ = c * (x * x) * (c * c * (x * (y * y))) * y := by rw [h2]
    _ = c * (x * x * (c * c)) * (x * (y * y)) * y := by group
    _ = c * (c * c * (x * x)) * (x * (y * y)) * y := by rw [h4]
    _ = c ^ 3 * (x ^ 3 * y ^ 3) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem pow_three_comm_class2 (x y c : G) (hyx : y * x = c * (x * y)) (hcy : c * y = y * c) :
    y ^ 3 * x = c ^ 3 * (x * y ^ 3) := by
  have hyc : y * c = c * y := hcy.symm
  have h2 := comm_two_class2 x y c hyx hcy
  have hycc : y * (c * c) = c * c * y := by
    calc y * (c * c) = (y * c) * c := by group
      _ = (c * y) * c := by rw [hyc]
      _ = c * (y * c) := by group
      _ = c * (c * y) := by rw [hyc]
      _ = c * c * y := by group
  calc y ^ 3 * x = y * (y * y * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = y * (c * c * (x * (y * y))) := by rw [h2]
    _ = (y * (c * c)) * (x * (y * y)) := by group
    _ = (c * c * y) * (x * (y * y)) := by rw [hycc]
    _ = c * c * (y * x) * (y * y) := by group
    _ = c * c * (c * (x * y)) * (y * y) := by rw [hyx]
    _ = c ^ 3 * (x * y ^ 3) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem exp3_of_class2 (S : Set G) (h3 : ∀ a ∈ S, a ^ 3 = 1)
    (hc : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ⁅⁅a, b⁆, c⁆ = 1) :
    ∀ q ∈ Subgroup.closure S, q ^ 3 = 1 := by
  have mulc : ∀ {z w : G}, (∀ h ∈ Subgroup.closure S, z * h = h * z) →
      (∀ h ∈ Subgroup.closure S, w * h = h * w) →
      ∀ h ∈ Subgroup.closure S, z * w * h = h * (z * w) := by
    intro z w hz hw h hh
    rw [mul_assoc, hw h hh, ← mul_assoc, hz h hh, mul_assoc]
  have invc : ∀ {z : G}, (∀ h ∈ Subgroup.closure S, z * h = h * z) →
      ∀ h ∈ Subgroup.closure S, z⁻¹ * h = h * z⁻¹ := by
    intro z hz h hh
    have h1 := hz h hh
    calc z⁻¹ * h = z⁻¹ * (h * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * h) * z⁻¹ := by rw [← h1]
      _ = h * z⁻¹ := by group
  have s1 : ∀ a ∈ S, ∀ b ∈ S, ∀ h ∈ Subgroup.closure S, ⁅a, b⁆ * h = h * ⁅a, b⁆ := by
    intro a ha b hb h hh
    induction hh using Subgroup.closure_induction with
    | mem c hcS => exact commutatorElement_eq_one_iff_mul_comm.1 (hc a ha b hb c hcS)
    | one => rw [mul_one, one_mul]
    | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
    | inv x _ hx =>
      have h1 : ⁅a, b⁆ * x⁻¹ = x⁻¹ * ⁅a, b⁆ := by
        calc ⁅a, b⁆ * x⁻¹ = x⁻¹ * (x * ⁅a, b⁆) * x⁻¹ := by group
          _ = x⁻¹ * (⁅a, b⁆ * x) * x⁻¹ := by rw [hx]
          _ = x⁻¹ * ⁅a, b⁆ := by group
      exact h1
  have s2 : ∀ q ∈ Subgroup.closure S, ∀ b ∈ S, ∀ h ∈ Subgroup.closure S,
      ⁅q, b⁆ * h = h * ⁅q, b⁆ := by
    intro q hq b hb
    induction hq using Subgroup.closure_induction with
    | mem a ha => exact s1 a ha b hb
    | one => intro h _; rw [commutatorElement_one_left, one_mul, mul_one]
    | mul x y hx hy ihx ihy =>
      have e : ⁅x * y, b⁆ = (x * ⁅y, b⁆ * x⁻¹) * ⁅x, b⁆ := by
        simp only [commutatorElement_def]; group
      have e2 : x * ⁅y, b⁆ * x⁻¹ = ⁅y, b⁆ := by
        have := ihy x hx
        calc x * ⁅y, b⁆ * x⁻¹ = (x * ⁅y, b⁆) * x⁻¹ := by group
          _ = (⁅y, b⁆ * x) * x⁻¹ := by rw [← this]
          _ = ⁅y, b⁆ := by group
      rw [e, e2]
      exact mulc ihy ihx
    | inv x hx ihx =>
      have e : ⁅x⁻¹, b⁆ = x⁻¹ * ⁅x, b⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
      have e2 : x⁻¹ * ⁅x, b⁆⁻¹ * x = ⁅x, b⁆⁻¹ := by
        have h1 := invc ihx
        have := h1 x hx
        calc x⁻¹ * ⁅x, b⁆⁻¹ * x = x⁻¹ * (⁅x, b⁆⁻¹ * x) := by group
          _ = x⁻¹ * (x * ⁅x, b⁆⁻¹) := by rw [this]
          _ = ⁅x, b⁆⁻¹ := by group
      rw [e, e2]
      exact invc ihx
  have s3 : ∀ q ∈ Subgroup.closure S, ∀ q' ∈ Subgroup.closure S, ∀ h ∈ Subgroup.closure S,
      ⁅q, q'⁆ * h = h * ⁅q, q'⁆ := by
    intro q hq q' hq'
    induction hq' using Subgroup.closure_induction with
    | mem b hb => exact s2 q hq b hb
    | one => intro h _; rw [commutatorElement_one_right, one_mul, mul_one]
    | mul x y hx hy ihx ihy =>
      have e : ⁅q, x * y⁆ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      have e2 : x * ⁅q, y⁆ * x⁻¹ = ⁅q, y⁆ := by
        have := ihy x hx
        calc x * ⁅q, y⁆ * x⁻¹ = (x * ⁅q, y⁆) * x⁻¹ := by group
          _ = (⁅q, y⁆ * x) * x⁻¹ := by rw [← this]
          _ = ⁅q, y⁆ := by group
      rw [e, e2]
      exact mulc ihx ihy
    | inv x hx ihx =>
      have e : ⁅q, x⁻¹⁆ = x⁻¹ * ⁅q, x⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
      have e2 : x⁻¹ * ⁅q, x⁆⁻¹ * x = ⁅q, x⁆⁻¹ := by
        have h1 := invc ihx
        have := h1 x hx
        calc x⁻¹ * ⁅q, x⁆⁻¹ * x = x⁻¹ * (⁅q, x⁆⁻¹ * x) := by group
          _ = x⁻¹ * (x * ⁅q, x⁆⁻¹) := by rw [this]
          _ = ⁅q, x⁆⁻¹ := by group
      rw [e, e2]
      exact invc ihx
  intro q hq
  induction hq using Subgroup.closure_induction with
  | mem a ha => exact h3 a ha
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hcxy : ∀ h ∈ Subgroup.closure S, ⁅y, x⁆ * h = h * ⁅y, x⁆ := s3 y hy x hx
    have hyx : y * x = ⁅y, x⁆ * (x * y) := by simp only [commutatorElement_def]; group
    have hcx := hcxy x hx
    have hcy := hcxy y hy
    rw [pow_three_class2 x y ⁅y, x⁆ hyx hcx hcy]
    have h5 := pow_three_comm_class2 x y ⁅y, x⁆ hyx hcy
    rw [ihy, one_mul, mul_one] at h5
    have hc3 : ⁅y, x⁆ ^ 3 = 1 := by
      calc ⁅y, x⁆ ^ 3 = ⁅y, x⁆ ^ 3 * x * x⁻¹ := by group
        _ = x * x⁻¹ := by rw [← h5]
        _ = 1 := by group
    rw [hc3, ihx, ihy]; group
  | inv x hx ihx =>
    calc x⁻¹ ^ 3 = (x ^ 3)⁻¹ := by group
      _ = 1 := by rw [ihx, inv_one]

end Class2

section CubeFix

variable {J ι : Type*} [Group J] [MulAction J ι]

theorem cube_fix_of_class2 {s : J} {P : Set J} (hPC : ∀ t ∈ P, t * s = s * t)
    (hP3 : ∀ t ∈ P, t ^ 3 = 1)
    (hK3 : ∀ t₁ ∈ P, ∀ t₂ ∈ P, ∀ t₃ ∈ P, ∀ f : ι, s • f = f → ⁅⁅t₁, t₂⁆, t₃⁆ • f = f) :
    ∀ q ∈ Subgroup.closure P, ∀ f : ι, s • f = f → q ^ 3 • f = f := by
  classical
  set C : Subgroup J := Subgroup.centralizer ({s} : Set J) with hC
  have hCs : ∀ {g : J}, g ∈ C ↔ g * s = s * g := Subgroup.mem_centralizer_singleton_iff
  have hfix : ∀ {g : J}, g ∈ C → ∀ f : ι, s • f = f → s • g • f = g • f := by
    intro g hg f hf
    rw [← mul_smul, ← hCs.1 hg, mul_smul, hf]
  let K : Subgroup C :=
    { carrier := {g | ∀ f : ι, s • f = f → (g : J) • f = f}
      mul_mem' := by
        intro a b ha hb f hf
        rw [Subgroup.coe_mul, mul_smul, hb f hf, ha f hf]
      one_mem' := by
        intro f _
        simp
      inv_mem' := by
        intro a ha f hf
        rw [Subgroup.coe_inv]
        have := ha f hf
        rw [inv_smul_eq_iff, this] }
  haveI hKn : K.Normal := by
    refine ⟨fun k hk h f hf => ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, Subgroup.coe_inv]
    have h1 : (h : J)⁻¹ • f = (h : J)⁻¹ • f := rfl
    have h2 : s • (h : J)⁻¹ • f = (h : J)⁻¹ • f := by
      have := hfix (C.inv_mem h.2) f hf
      exact this
    rw [hk _ h2, smul_inv_smul]
  let P' : Set C := {g | (g : J) ∈ P}
  have key : ∀ q ∈ Subgroup.closure P', q ^ 3 ∈ K := by
    intro q hq
    have hmem : QuotientGroup.mk' K q ∈ Subgroup.closure ((QuotientGroup.mk' K) '' P') := by
      rw [← MonoidHom.map_closure]
      exact Subgroup.mem_map_of_mem _ hq
    have h := exp3_of_class2 ((QuotientGroup.mk' K) '' P') ?_ ?_ _ hmem
    · rw [← map_pow] at h
      exact (QuotientGroup.eq_one_iff _).1 h
    · rintro _ ⟨g, hg, rfl⟩
      rw [← map_pow]
      have : g ^ 3 = 1 := Subtype.ext (by simpa using hP3 _ hg)
      rw [this, map_one]
    · rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩ _ ⟨g₃, hg₃, rfl⟩
      have e : ⁅⁅QuotientGroup.mk' K g₁, QuotientGroup.mk' K g₂⁆, QuotientGroup.mk' K g₃⁆ =
          QuotientGroup.mk' K ⁅⁅g₁, g₂⁆, g₃⁆ := by
        simp only [commutatorElement_def, map_mul, map_inv]
      rw [e]
      refine (QuotientGroup.eq_one_iff _).2 ?_
      intro f hf
      have := hK3 _ hg₁ _ hg₂ _ hg₃ f hf
      simpa [commutatorElement_def] using this
  intro q hq f hf
  have hlift : ∀ q ∈ Subgroup.closure P, ∃ hq : q ∈ C, (⟨q, hq⟩ : C) ∈ Subgroup.closure P' := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem t ht => exact ⟨hCs.2 (hPC t ht), Subgroup.subset_closure ht⟩
    | one => exact ⟨C.one_mem, Subgroup.one_mem _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      exact ⟨C.mul_mem hx1 hy1, Subgroup.mul_mem _ hx2 hy2⟩
    | inv x _ hx =>
      obtain ⟨hx1, hx2⟩ := hx
      exact ⟨C.inv_mem hx1, Subgroup.inv_mem _ hx2⟩
  obtain ⟨hqC, hq'⟩ := hlift q hq
  have := key _ hq' f hf
  simpa using this

end CubeFix

section Twins

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (PConstrainedShape)

variable {J R ι : Type*} [Group J] [Group R] [MulAction J ι] [MulAction R ι]

theorem isPGroup_three_of_cube_mem {H K : Subgroup J} (hK : IsPGroup 3 K)
    (h : ∀ q ∈ H, q ^ 3 ∈ K) : IsPGroup 3 H := by
  intro q
  obtain ⟨k, hk⟩ := hK ⟨(q : J) ^ 3, h q q.2⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have h1 : ((q : J) ^ 3) ^ 3 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ', pow_mul]
  exact h1

theorem pConstrainedShape_of_twins (φ : J →* R) (e : ι → R) (s : J)
    (hφ : ∀ (g : J) (i : ι), φ g • i = g • i) (hφinj : Function.Injective φ)
    (hconj : ∀ (r : R) (i : ι), e (r • i) = r * e i * r⁻¹)
    (hK1 : ∀ a : ι, s • a = a → ∃ b, TabFi23.Twin e (φ s) a b)
    (hK2 : ∀ a b a' b', TabFi23.Twin e (φ s) a b → TabFi23.Twin e (φ s) a' b' →
      e a' * e b' = e a * e b →
      (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = e a • b) ∨ (a' = e a • b ∧ b' = a))
    (hprod : ∀ a b, TabFi23.Twin e (φ s) a b → ∃ t : J, φ t = e a * e b ∧ t * s = s * t)
    (hcube : ∀ a b, TabFi23.Twin e (φ s) a b → (e a * e b) ^ 3 = 1)
    (hK3 : ∀ a₁ b₁ a₂ b₂ a₃ b₃, TabFi23.Twin e (φ s) a₁ b₁ → TabFi23.Twin e (φ s) a₂ b₂ →
      TabFi23.Twin e (φ s) a₃ b₃ → ∀ f : ι, s • f = f →
      ⁅⁅e a₁ * e b₁, e a₂ * e b₂⁆, e a₃ * e b₃⁆ • f = f)
    (hKF : ∀ H : Subgroup J, (∀ g ∈ H, g * s = s * g ∧ ∀ f : ι, s • f = f → g • f = f) →
      IsPGroup 3 H) :
    PConstrainedShape 3 (Subgroup.centralizer ({s} : Set J)) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : R, x = φ s := ⟨_, rfl⟩
  rw [← hx] at hK1 hK2 hprod hcube hK3
  obtain ⟨C, hC⟩ : ∃ C : Subgroup J, C = Subgroup.centralizer ({s} : Set J) := ⟨_, rfl⟩
  rw [← hC]
  have hCs : ∀ {g : J}, g ∈ C ↔ g * s = s * g := fun {g} => by
    rw [hC]; exact Subgroup.mem_centralizer_singleton_iff
  have hxg : ∀ {g : J}, g * s = s * g → φ g * x = x * φ g := fun {g} h => by
    rw [hx, ← map_mul, ← map_mul, h]
  obtain ⟨P, hP⟩ : ∃ P : Set J, ∀ t, t ∈ P ↔
      (t * s = s * t ∧ ∃ a b, TabFi23.Twin e x a b ∧ φ t = e a * e b) := ⟨_, fun _ => Iff.rfl⟩
  have hPC : ∀ t ∈ P, t * s = s * t := fun t ht => ((hP t).1 ht).1
  have hP3 : ∀ t ∈ P, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨-, a, b, hab, hφt⟩ := (hP t).1 ht
    apply hφinj
    rw [map_pow, hφt, map_one]
    exact hcube a b hab
  have hK3' : ∀ t₁ ∈ P, ∀ t₂ ∈ P, ∀ t₃ ∈ P, ∀ f : ι, s • f = f → ⁅⁅t₁, t₂⁆, t₃⁆ • f = f := by
    intro t₁ h₁ t₂ h₂ t₃ h₃ f hf
    obtain ⟨-, a₁, b₁, h₁, e₁⟩ := (hP t₁).1 h₁
    obtain ⟨-, a₂, b₂, h₂, e₂⟩ := (hP t₂).1 h₂
    obtain ⟨-, a₃, b₃, h₃, e₃⟩ := (hP t₃).1 h₃
    rw [← hφ]
    simp only [map_commutatorElement, e₁, e₂, e₃]
    exact hK3 _ _ _ _ _ _ h₁ h₂ h₃ f hf
  have hN3 := cube_fix_of_class2 (s := s) (P := P) hPC hP3 hK3'
  have hNC : Subgroup.closure P ≤ C := (Subgroup.closure_le C).2 fun t ht => hCs.2 (hPC t ht)
  have hNn : ∀ g ∈ C, ∀ q ∈ Subgroup.closure P, g * q * g⁻¹ ∈ Subgroup.closure P := by
    intro g hg q hq
    have hg' : g * s = s * g := hCs.1 hg
    induction hq using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨hts, a, b, hab, hφt⟩ := (hP t).1 ht
      refine Subgroup.subset_closure ((hP _).2 ⟨hCs.1 (C.mul_mem (C.mul_mem hg (hCs.2 hts))
        (C.inv_mem hg)), g • a, g • b, ?_, ?_⟩)
      · have := TabFi23.twin_smul hconj (hxg hg') hab
        rwa [hφ, hφ] at this
      · rw [map_mul, map_mul, map_inv, hφt, TabFi23.rho_smul hconj, hφ, hφ]
    | one => simpa using (Subgroup.closure P).one_mem
    | mul y z _ _ hy hz =>
      have : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hy
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup J,
      Z = C ⊓ Subgroup.centralizer ((Subgroup.closure P : Subgroup J) : Set J) := ⟨_, rfl⟩
  have hZmem : ∀ z, z ∈ Z ↔ z ∈ C ∧ ∀ q ∈ Subgroup.closure P, z * q = q * z := fun z => by
    rw [hZ, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact and_congr_right fun _ => forall₂_congr fun q hq => by
      exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hZC : Z ≤ C := fun z hz => ((hZmem z).1 hz).1
  have hZn : ∀ g ∈ C, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
    intro g hg z hz
    obtain ⟨hzC, hzc⟩ := (hZmem z).1 hz
    refine (hZmem _).2 ⟨C.mul_mem (C.mul_mem hg hzC) (C.inv_mem hg), fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g ∈ Subgroup.closure P := by
      simpa using hNn g⁻¹ (C.inv_mem hg) q hq
    have h1 := hzc (g⁻¹ * q * g) hq'
    calc g * z * g⁻¹ * q = g * (z * (g⁻¹ * q * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * q * g) * z) * g⁻¹ := by rw [h1]
      _ = q * (g * z * g⁻¹) := by group
  let K : Subgroup J :=
    { carrier := {g | g * s = s * g ∧ ∀ f : ι, s • f = f → g • f = f}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, fun f hf => ?_⟩
        · rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
        · rw [mul_smul, hb' f hf, ha' f hf]
      one_mem' := ⟨by simp, fun f _ => one_smul J f⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨?_, fun f hf => ?_⟩
        · calc a⁻¹ * s = a⁻¹ * (s * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * s) * a⁻¹ := by rw [ha]
            _ = s * a⁻¹ := by group
        · rw [inv_smul_eq_iff, ha' f hf] }
  have hKp : IsPGroup 3 K := hKF K fun g hg => hg
  have hq3 : ∀ q ∈ C, (∀ f : ι, s • f = f → q ^ 3 • f = f) → q ^ 3 ∈ K := fun q hq hf =>
    ⟨hCs.1 (C.pow_mem hq 3), hf⟩
  have hNp : IsPGroup 3 (Subgroup.closure P) :=
    isPGroup_three_of_cube_mem hKp fun q hq => hq3 q (hNC hq) (hN3 q hq)
  have hK2b : ∀ a b, TabFi23.Twin e x a b → e a • b ≠ a ∧ e a • b ≠ b := by
    intro a b hab
    obtain ⟨-, -, -, hnc, -⟩ := hab
    constructor
    · intro h
      have h1 := hconj (e a) b
      rw [h] at h1
      apply hnc
      have h2 : e b = e a := by
        calc e b = (e a)⁻¹ * (e a * e b * (e a)⁻¹) * e a := by group
          _ = (e a)⁻¹ * e a * e a := by rw [← h1]
          _ = e a := by group
      rw [h2]
    · intro h
      have h1 := hconj (e a) b
      rw [h] at h1
      apply hnc
      calc e a * e b = e a * e b * (e a)⁻¹ * e a := by group
        _ = e b * e a := by rw [← h1]
  have hZ3 : ∀ z ∈ Z, ∀ f : ι, s • f = f → z ^ 3 • f = f := by
    intro z hz f hf
    obtain ⟨hzC, hzc⟩ := (hZmem z).1 hz
    obtain ⟨b, hb⟩ := hK1 f hf
    have hcent : ∀ a b, TabFi23.Twin e x a b → φ z * (e a * e b) = (e a * e b) * φ z := by
      intro a b hab
      obtain ⟨t, ht, hts⟩ := hprod a b hab
      have htP : t ∈ P := (hP t).2 ⟨hts, a, b, hab, ht⟩
      have := hzc t (Subgroup.subset_closure htP)
      rw [← ht, ← map_mul, ← map_mul, this]
    have h := TabFi23.smul_cube_of_cent hconj (fun a b => e a • b) hK2 hK2b
      (hxg (hCs.1 hzC)) hcent hb
    rw [← hφ, map_pow, pow_three, mul_smul, mul_smul]
    exact h
  have hZp : IsPGroup 3 Z :=
    isPGroup_three_of_cube_mem hKp fun z hz => hq3 z (hZC hz) (hZ3 z hz)
  have hZnorm : Z ≤ Subgroup.normalizer ((Subgroup.closure P : Subgroup J) : Set J) := fun z hz =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun q hq => (((hZmem z).1 hz).2 q hq).symm)
  refine ⟨Z ⊔ Subgroup.closure P, sup_le hZC hNC, ?_, hZp.to_sup_of_normal_right' hNp hZnorm, ?_⟩
  · intro g hg q hq
    have hmap : (Z ⊔ Subgroup.closure P).map (MulAut.conj g).toMonoidHom ≤
        Z ⊔ Subgroup.closure P := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        exact hZn g hg z hz
      · rintro _ ⟨y, hy, rfl⟩
        exact hNn g hg y hy
    exact hmap ⟨q, hq, rfl⟩
  · have hleL : Z ≤ Z ⊔ Subgroup.closure P := le_sup_left
    have hleR : Subgroup.closure P ≤ Z ⊔ Subgroup.closure P := le_sup_right
    intro z hz
    have hzN : ∀ q ∈ Subgroup.closure P, z * q = q * z := fun q hq =>
      (Subgroup.mem_centralizer_iff.1 hz.2 q (hleR hq)).symm
    exact hleL ((hZmem z).2 ⟨hz.1, hzN⟩)

end Twins

end CFSG.HardMathSupport.Dickson.I271.TabFi24
