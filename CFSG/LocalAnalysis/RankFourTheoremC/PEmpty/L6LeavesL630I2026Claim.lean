module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630I2026Str

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026

section Commutators

variable {G : Type*} [Group G]

theorem comm_mul_of_central {g g' s : G} (h : g' * s * g'⁻¹ * s⁻¹ ∈ Subgroup.center G) :
    g * g' * s * (g * g')⁻¹ * s⁻¹ = (g' * s * g'⁻¹ * s⁻¹) * (g * s * g⁻¹ * s⁻¹) := by
  have hc := Subgroup.mem_center_iff.mp h g
  calc g * g' * s * (g * g')⁻¹ * s⁻¹
      = g * (g' * s * g'⁻¹ * s⁻¹) * (s * g⁻¹ * s⁻¹) := by group
    _ = (g' * s * g'⁻¹ * s⁻¹) * g * (s * g⁻¹ * s⁻¹) := by rw [hc]
    _ = _ := by group

theorem comm_inv_of_central {g s : G} (h : g * s * g⁻¹ * s⁻¹ ∈ Subgroup.center G) :
    g⁻¹ * s * g⁻¹⁻¹ * s⁻¹ = (g * s * g⁻¹ * s⁻¹)⁻¹ := by
  have hc := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ h) g⁻¹
  calc g⁻¹ * s * g⁻¹⁻¹ * s⁻¹ = g⁻¹ * (g * s * g⁻¹ * s⁻¹)⁻¹ * g := by group
    _ = (g * s * g⁻¹ * s⁻¹)⁻¹ * g⁻¹ * g := by rw [hc]
    _ = _ := by group

end Commutators

section ClaimB

variable {G : Type} [Group G] {S : Subgroup G} {α β γ δ z : G}

@[expose] def commNormalizer (S : Subgroup G) : Subgroup G where
  carrier := {g | ∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ Subgroup.center G}
  one_mem' := by
    intro s _
    simp only [inv_one, one_mul, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  mul_mem' := by
    intro g g' hg hg' s hs
    rw [comm_mul_of_central (hg' s hs)]
    exact Subgroup.mul_mem _ (hg' s hs) (hg s hs)
  inv_mem' := by
    intro g hg s hs
    rw [comm_inv_of_central (hg s hs)]
    exact Subgroup.inv_mem _ (hg s hs)

theorem comm_sq_eq_one {g s : G} (hP : QDPres S α β γ δ z) (hzc : z ∈ Subgroup.center G)
    (hs : s ∈ S) (hc : g * s * g⁻¹ * s⁻¹ ∈ Subgroup.center G) :
    (g * s * g⁻¹ * s⁻¹) * (g * s * g⁻¹ * s⁻¹) = 1 := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = g * s * g⁻¹ * s⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hc ⊢
  have h1 : g * s * g⁻¹ = c * s := by rw [hcdef]; group
  have h2 : g * (s * s) * g⁻¹ = c * c * (s * s) := by
    calc g * (s * s) * g⁻¹ = (g * s * g⁻¹) * (g * s * g⁻¹) := by group
      _ = (c * s) * (c * s) := by rw [h1]
      _ = c * (s * c) * s := by simp only [mul_assoc]
      _ = c * (c * s) * s := by rw [Subgroup.mem_center_iff.mp hc s]
      _ = c * c * (s * s) := by simp only [mul_assoc]
  have h3 : g * (s * s) * g⁻¹ = s * s := by
    rcases hP.sq s hs with h | h
    · rw [h]
      group
    · rw [h, Subgroup.mem_center_iff.mp hzc g]
      group
  rw [h3] at h2
  have h4 : c * c * (s * s) = 1 * (s * s) := by rw [← h2, one_mul]
  exact mul_right_cancel h4

open Classical in
noncomputable def bit (c : G) : ZMod 2 := if c = 1 then 0 else 1

theorem bit_eq_zero_iff {c : G} : bit c = 0 ↔ c = 1 := by
  unfold bit
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

theorem bit_mul {c c' : G} (hz : z * z = 1) (hz1 : z ≠ 1) (hc : c = 1 ∨ c = z)
    (hc' : c' = 1 ∨ c' = z) : bit (c * c') = bit c + bit c' := by
  classical
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;> simp [bit, hz, hz1] <;> decide

noncomputable def theta (x : Fin 4 → G) (g : G) : Fin 4 → ZMod 2 :=
  fun i => bit (g * x i * g⁻¹ * (x i)⁻¹)

theorem claimB (hP : QDPres S α β γ δ z) (hzc : z ∈ Subgroup.center G)
    (hC : ∀ g : G, (∀ s ∈ S, g * s = s * g) → g ∈ Subgroup.center G)
    (hsz : ∀ c ∈ Subgroup.center G, c * c = 1 → c = 1 ∨ c = z)
    {g : G} (hg : g ∈ commNormalizer S) : ∃ s₀ ∈ S, g * s₀⁻¹ ∈ Subgroup.center G := by
  classical
  let x : Fin 4 → G := ![α, β, γ, δ]
  have hx : ∀ i, x i ∈ S := by
    intro i
    fin_cases i
    · exact hP.α_mem
    · exact hP.β_mem
    · exact hP.γ_mem
    · exact hP.δ_mem
  have hSN : S ≤ commNormalizer S := by
    intro s hs t ht
    rcases hP.comm s hs t ht with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact hzc
  have hcz : ∀ h ∈ commNormalizer S, ∀ s ∈ S,
      h * s * h⁻¹ * s⁻¹ = 1 ∨ h * s * h⁻¹ * s⁻¹ = z := fun h hh s hs =>
    hsz _ (hh s hs) (comm_sq_eq_one hP hzc hs (hh s hs))
  have hadd : ∀ h ∈ commNormalizer S, ∀ h' ∈ commNormalizer S,
      theta x (h * h') = theta x h + theta x h' := by
    intro h hh h' hh'
    funext i
    simp only [theta, Pi.add_apply]
    rw [comm_mul_of_central (hh' _ (hx i)),
      bit_mul hP.zz hP.z_ne (hcz h' hh' _ (hx i)) (hcz h hh _ (hx i)), add_comm]
  have hker : ∀ h ∈ commNormalizer S, theta x h = 0 → h ∈ Subgroup.center G := by
    intro h hh h0
    apply hC
    have hgen : ∀ i, x i * h = h * x i := by
      intro i
      have h1 := congrFun h0 i
      simp only [theta, Pi.zero_apply, bit_eq_zero_iff] at h1
      have h2 : h * x i = x i * h := by
        calc h * x i = h * x i * h⁻¹ * (x i)⁻¹ * x i * h := by group
          _ = 1 * x i * h := by rw [h1]
          _ = x i * h := by rw [one_mul]
      exact h2.symm
    have hle : S ≤ Subgroup.centralizer {h} := by
      rw [hP.gen, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hy with rfl | rfl | rfl | rfl
      · exact hgen 0
      · exact hgen 1
      · exact hgen 2
      · exact hgen 3
    intro s hs
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hs)).symm
  let Θ : ↥S →* Multiplicative (Fin 4 → ZMod 2) :=
    { toFun := fun s => Multiplicative.ofAdd (theta x (s : G))
      map_one' := by
        apply congrArg Multiplicative.ofAdd
        funext i
        simp [theta, bit]
      map_mul' := fun s s' => congrArg Multiplicative.ofAdd
        (hadd s (hSN s.2) s' (hSN s'.2)) }
  have hkerΘ : ∀ s : ↥S, s ∈ Θ.ker ↔ (s : G) = 1 ∨ (s : G) = z := by
    intro s
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h0 : theta x (s : G) = 0 := h
      apply hP.center s.1 s.2
      intro t ht
      exact ((Subgroup.mem_center_iff.mp (hker s (hSN s.2) h0)) t).symm
    · intro h
      apply congrArg Multiplicative.ofAdd
      funext i
      rcases h with h | h
      · simp [theta, bit, h]
      · have := Subgroup.mem_center_iff.mp hzc (x i)
        have h1 : z * x i * z⁻¹ * (x i)⁻¹ = 1 := by
          rw [← this]
          group
        simp [theta, bit, h, h1]
  have hkc : Nat.card Θ.ker = 2 := by
    rw [Nat.card_eq_two_iff' (1 : ↥Θ.ker)]
    refine ⟨⟨⟨z, hP.z_mem⟩, (hkerΘ _).mpr (Or.inr rfl)⟩, ?_, ?_⟩
    · intro h
      exact hP.z_ne (congrArg (fun y : ↥Θ.ker => ((y : ↥S) : G)) h)
    · intro y hy
      have h1 := (hkerΘ y.1).mp y.2
      rcases h1 with h1 | h1
      · exact absurd (Subtype.ext (Subtype.ext h1)) hy
      · exact Subtype.ext (Subtype.ext h1)
  have hcard := Subgroup.card_ker_mul_card_range Θ
  rw [hkc, hP.card] at hcard
  have hrange : Nat.card Θ.range = 16 := by omega
  have hall : Nat.card (Multiplicative (Fin 4 → ZMod 2)) = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have htop : Θ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, hall])
  obtain ⟨s, hs⟩ : ∃ s : ↥S, Θ s = Multiplicative.ofAdd (theta x g) := by
    have : Multiplicative.ofAdd (theta x g) ∈ Θ.range := by
      rw [htop]
      trivial
    exact this
  have hs' : theta x (s : G) = theta x g := hs
  refine ⟨s, s.2, ?_⟩
  apply hker (g * (s : G)⁻¹) (Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (hSN s.2)))
  have h1 := hadd (g * (s : G)⁻¹) (Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (hSN s.2)))
    (s : G) (hSN s.2)
  rw [inv_mul_cancel_right, hs'] at h1
  funext i
  have h2 := congrFun h1 i
  simp only [Pi.add_apply] at h2
  simpa using h2

end ClaimB

section PCount

variable {G : Type} [Group G]

@[expose, instance_reducible] def conjAct (P U : Subgroup G)
    (hU : ∀ p ∈ P, ∀ x ∈ U, p * x * p⁻¹ ∈ U) : MulAction ↥P ↥U where
  smul p x := ⟨p * x * p⁻¹, hU p p.2 x x.2⟩
  one_smul x := Subtype.ext (by
    show ((1 : ↥P) : G) * (x : G) * ((1 : ↥P) : G)⁻¹ = (x : G)
    simp)
  mul_smul p q x := Subtype.ext (by
    show ((p * q : ↥P) : G) * (x : G) * ((p * q : ↥P) : G)⁻¹ =
      (p : G) * ((q : G) * (x : G) * (q : G)⁻¹) * (p : G)⁻¹
    simp [mul_assoc])

theorem card_modEq_conj {P U : Subgroup G} [Finite U] (hP : Nat.card P = 5)
    (hU : ∀ p ∈ P, ∀ x ∈ U, p * x * p⁻¹ ∈ U) :
    Nat.card U ≡ Nat.card ↥(U ⊓ Subgroup.centralizer (P : Set G)) [MOD 5] := by
  letI := conjAct P U hU
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPg : IsPGroup 5 ↥P := IsPGroup.of_card (n := 1) (by simpa using hP)
  have h := hPg.card_modEq_card_fixedPoints ↥U
  have hfix : Nat.card (MulAction.fixedPoints ↥P ↥U) =
      Nat.card ↥(U ⊓ Subgroup.centralizer (P : Set G)) := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨(x.1 : G), x.1.2, Subgroup.mem_centralizer_iff.mpr (fun p hp => by
          have h1 : ((⟨p, hp⟩ : ↥P) • x.1 : ↥U) = x.1 := x.2 ⟨p, hp⟩
          have h2 : p * (x.1 : G) * p⁻¹ = (x.1 : G) := congrArg Subtype.val h1
          calc p * (x.1 : G) = p * (x.1 : G) * p⁻¹ * p := by group
            _ = (x.1 : G) * p := by rw [h2])⟩
        invFun := fun y => ⟨⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩, fun p => by
          apply Subtype.ext
          have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp y.2).2 (p : G) p.2
          show (p : G) * (y : G) * (p : G)⁻¹ = (y : G)
          rw [h1]
          group⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hfix] at h
  exact h

theorem eq_zpowers_or_eq [Finite G] {S U : Subgroup G} {α β γ δ z : G} (hpres : QDPres S α β γ δ z)
    (hUS : U ≤ S) (hzU : z ∈ U) (hmod : Nat.card U ≡ 2 [MOD 5]) :
    U = Subgroup.zpowers z ∨ U = S := by
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hpres.zz
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hpres.z_ne
  have hzU' : Subgroup.zpowers z ≤ U := by rw [Subgroup.zpowers_le]; exact hzU
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hzord]
  have hdvd : Nat.card U ∣ 2 ^ 5 := by
    have h1 := Subgroup.card_dvd_of_le hUS
    rw [hpres.card] at h1
    simpa using h1
  obtain ⟨m, hm, hCm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h5 : 2 ^ m % 5 = 2 := by
    rw [← hCm]
    exact hmod
  have hm15 : m = 1 ∨ m = 5 := by
    interval_cases m
    · norm_num at h5
    · exact Or.inl rfl
    · norm_num at h5
    · norm_num at h5
    · norm_num at h5
    · exact Or.inr rfl
  rcases hm15 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hzU' (by rw [hzcard, hCm]; norm_num)).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hUS (by rw [hpres.card, hCm]; norm_num)

theorem fixed_of_pres [Finite G] {S P : Subgroup G} {α β γ δ z : G} (hP5 : Nat.card P = 5)
    (hSP : ∀ p ∈ P, ∀ s ∈ S, p * s * p⁻¹ ∈ S) (hpres : QDPres S α β γ δ z)
    (hzc : z ∈ Subgroup.center G) (hnc : ¬ ∀ p ∈ P, ∀ s ∈ S, p * s = s * p) :
    ∀ s ∈ S, (∀ p ∈ P, p * s = s * p) → s = 1 ∨ s = z := by
  intro s hs hsP
  have hmod := card_modEq_conj hP5 hSP
  rw [hpres.card] at hmod
  have hCS : S ⊓ Subgroup.centralizer (P : Set G) ≤ S := inf_le_left
  have hzC : z ∈ S ⊓ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_inf.mpr ⟨hpres.z_mem,
      Subgroup.mem_centralizer_iff.mpr fun p _ => Subgroup.mem_center_iff.mp hzc p⟩
  have hmod2 : Nat.card ↥(S ⊓ Subgroup.centralizer (P : Set G)) ≡ 2 [MOD 5] := by
    have h32 : (32 : ℕ) ≡ 2 [MOD 5] := by decide
    exact hmod.symm.trans h32
  have hsC : s ∈ S ⊓ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_inf.mpr ⟨hs, Subgroup.mem_centralizer_iff.mpr hsP⟩
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hpres.zz
  rcases eq_zpowers_or_eq hpres hCS hzC hmod2 with h | h
  · rw [h] at hsC
    exact mem_zpowers_of_sq_one hz2 hpres.z_ne hsC
  · exfalso
    apply hnc
    intro p hp t ht
    have ht' : t ∈ S ⊓ Subgroup.centralizer (P : Set G) := by rw [h]; exact ht
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht').2 p hp

end PCount

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026
