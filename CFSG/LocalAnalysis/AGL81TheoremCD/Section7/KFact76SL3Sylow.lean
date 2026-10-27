module

public import CFSG.Open.StatedCenterThree
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.CentralOmega.Linear
import CFSG.RankThree.PartTwo.Sec4.Hering432Basic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open Matrix CFSG.Open.StatedCenterThree CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega
open CFSG.RankThree.PartTwo.Sec4

variable {K : Type} [Field K]

theorem mem_center_of_commute_diagGL_cyc3GL {H : Subgroup (GL (Fin 3) K)} {ω : Kˣ}
    (hord : orderOf ω = 3) (hD : diagGL ω ∈ H) (hC : cyc3GL ∈ H) {x : H}
    (hxd : x * ⟨diagGL ω, hD⟩ = ⟨diagGL ω, hD⟩ * x)
    (hxc : x * ⟨cyc3GL, hC⟩ = ⟨cyc3GL, hC⟩ * x) : x ∈ Subgroup.center H := by
  have hω1 : (ω : K) ≠ 1 := fun h => by
    rw [Units.val_eq_one.mp h, orderOf_one] at hord
    omega
  have hωi : ((ω⁻¹ : Kˣ) : K) ≠ 1 := fun h => hω1 (by
    rw [inv_eq_one.mp (Units.val_eq_one.mp h), Units.val_one])
  have hωω : (ω : K) ≠ ((ω⁻¹ : Kˣ) : K) := fun h => by
    have h2 : ω ^ 2 = 1 := by
      rw [sq]
      nth_rw 2 [Units.ext h]
      exact mul_inv_cancel ω
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at h3
    omega
  have hinj : Function.Injective ![(ω : K), ((ω⁻¹ : Kˣ) : K), 1] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  set M : Matrix (Fin 3) (Fin 3) K := ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have h1 : M * diagonal ![(ω : K), ((ω⁻¹ : Kˣ) : K), 1] =
      diagonal ![(ω : K), ((ω⁻¹ : Kˣ) : K), 1] * M :=
    congrArg (fun y : H => ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hxd
  have hdiag := eq_diagonal_of_commute hinj h1
  have h2 : diagonal (fun i => M i i) * cyc3 = cyc3 * diagonal (fun i => M i i) := by
    rw [← hdiag]
    exact congrArg (fun y : H => ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hxc
  obtain ⟨e1, e2⟩ := eq_of_diagonal_commute_cyc3 h2
  have hMs : M = M 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [hdiag, smul_one_eq_diagonal]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact e1
    · exact e2
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  change ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
    M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [hMs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem exists_sylow_three_center_le_of_isSLThreePiAt {X : Type} [Group X] {q : ℕ}
    (hX : IsSLThreePiAt X q) :
    (∃ P : Sylow 3 X, ∀ x : X, x ^ 3 = 1 → (∀ p ∈ (P : Subgroup X), x * p = p * x) →
      x ∈ Subgroup.center X) ∧ Nat.card (Subgroup.center X) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, h⟩ := hX
  obtain ⟨H, ⟨ψ⟩, ω, hord, hD, hC, hS, hZ⟩ : ∃ H : Subgroup (GL (Fin 3) K), Nonempty (X ≃* H) ∧
      ∃ ω : Kˣ, orderOf ω = 3 ∧ diagGL ω ∈ H ∧ cyc3GL ∈ H ∧
        GeneralLinearGroup.scalar (Fin 3) ω ∈ H ∧ Nat.card (Subgroup.center H) = 3 := by
    rcases h with ⟨hK, hq3, ⟨ψ⟩⟩ | ⟨hK, hq3, ⟨ψ⟩⟩
    ·
      have h3 : 3 ∣ Nat.card Kˣ := by
        rw [Nat.card_units, hK]
        omega
      obtain ⟨ω, hord⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
      have hω : ω ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
      exact ⟨_, ⟨ψ⟩, ω, hord,
        CFSG.Open.StatedAPI.statedSU_le_statedSL 3 2 K (diagGL_mem (by norm_num) hω),
        CFSG.Open.StatedAPI.statedSU_le_statedSL 3 2 K (cyc3GL_mem (by norm_num)),
        CFSG.Open.StatedAPI.statedSU_le_statedSL 3 2 K
          (scalar_mem (by norm_num) (by norm_num) hω),
        card_center_statedSL_three (by rw [hK]; omega)⟩
    ·
      have hq0 : q ≠ 0 := by omega
      have hq1 : 3 ∣ q + 1 := by omega
      have h3 : 3 ∣ Nat.card Kˣ := by
        rw [Nat.card_units, hK]
        obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
        have : (3 * k + 2) ^ 2 = 3 * (3 * k ^ 2 + 4 * k + 1) + 1 := by ring
        rw [this, Nat.add_sub_cancel]
        exact dvd_mul_right _ _
      obtain ⟨ω, hord⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
      have hω : ω ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
      have hωq : ω ^ (q + 1) = 1 := by
        obtain ⟨m, hm⟩ := hq1
        rw [hm, pow_mul, hω, one_pow]
      exact ⟨_, ⟨ψ⟩, ω, hord, diagGL_mem hq0 hωq, cyc3GL_mem hq0, scalar_mem hq0 hq1 hω,
        card_center_statedSU_three hK hq1⟩
  have hω : ω ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
  set d : H := ⟨diagGL ω, hD⟩
  set c : H := ⟨cyc3GL, hC⟩
  set s : H := ⟨GeneralLinearGroup.scalar (Fin 3) ω, hS⟩
  have hsZ : s ∈ Subgroup.center H := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (GeneralLinearGroup.scalar_commute ω (g : GL (Fin 3) K)).symm
  have hs3 : s ^ 3 = 1 := Subtype.ext (by
    change GeneralLinearGroup.scalar (Fin 3) ω ^ 3 = 1
    rw [← map_pow, hω, map_one])
  have hE : IsPGroup 3 (Subgroup.closure {d, c}) :=
    isPGroup_closure_of_conj_eq_mul hsZ hs3 (Subtype.ext (diagGL_pow_three hω))
      (Subtype.ext cyc3GL_pow_three) (Subtype.ext (cyc3GL_conj_diagGL hω))
  obtain ⟨P, hP⟩ := (hE.map ψ.symm.toMonoidHom).exists_le_sylow
  refine ⟨⟨P, fun x _ hx => ?_⟩, ?_⟩
  · have hmem : ∀ y ∈ ({d, c} : Set H), ψ.symm y ∈ (P : Subgroup X) := fun y hy =>
      hP (Subgroup.mem_map_of_mem _ (Subgroup.subset_closure hy))
    have hxd := congrArg ψ (hx _ (hmem d (Set.mem_insert _ _)))
    have hxc := congrArg ψ (hx _ (hmem c (Set.mem_insert_of_mem _ rfl)))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at hxd hxc
    have hψ := mem_center_of_commute_diagGL_cyc3GL hord hD hC hxd hxc
    rw [Subgroup.mem_center_iff] at hψ ⊢
    intro g
    apply ψ.injective
    rw [map_mul, map_mul]
    exact hψ (ψ g)
  · rw [Nat.card_congr (Subgroup.centerCongr ψ).toEquiv]
    exact hZ

theorem exists_conj_eq_zpowers_of_isSLThreePiAt {G : Type} [Group G] [Finite G] {q : ℕ}
    {A : Subgroup G} (hA : Nat.card A = 3)
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set G) →
      A.map (MulAut.conj g).toMonoidHom = A)
    {z : G} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hSL : IsSLThreePiAt ↥(Subgroup.centralizer ({z} : Set G)) q) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, -, hAC⟩ := Hering432.exists_sylow_le_center_of_weaklyClosed hA hwc
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  set N := Subgroup.centralizer ({z} : Set G) with hN
  obtain ⟨⟨P₀, hP₀⟩, hZ3⟩ := exists_sylow_three_center_le_of_isSLThreePiAt hSL
  have hzN : z ∈ N := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set z' : N := ⟨z, hzN⟩ with hz'
  have hz'Z : z' ∈ Subgroup.center N := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hz'ord : orderOf z' = 3 := by rw [← Subgroup.orderOf_coe]; exact hzord
  have hZeq : Subgroup.center N = Subgroup.zpowers z' :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz'Z)
      (by rw [hZ3, Nat.card_zpowers, hz'ord])).symm
  have hZP : Subgroup.center N ≤ (P₀ : Subgroup N) :=
    IsPGroup.le_sylow_of_normal (IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])) P₀
  obtain ⟨Q, hQ⟩ := (P₀.isPGroup'.map N.subtype).exists_le_sylow
  have hzQ : z ∈ (Q : Subgroup G) := hQ (Subgroup.mem_map_of_mem N.subtype (hZP hz'Z))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hPQ : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = Q := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g, ?_⟩
  have hA' : Nat.card (A.map (MulAut.conj g).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA]
  have hA'C : ∀ a ∈ A.map (MulAut.conj g).toMonoidHom, ∀ y ∈ (Q : Subgroup G), y * a = a * y := by
    rintro _ ⟨a, ha, rfl⟩ y hy
    rw [← hPQ] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    have hpa := Subgroup.mem_centralizer_iff.mp (hAC ha) p hp
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * p * g⁻¹ * (g * a * g⁻¹) = g * (p * a) * g⁻¹ := by group
      _ = g * (a * p) * g⁻¹ := by rw [hpa]
      _ = g * a * g⁻¹ * (g * p * g⁻¹) := by group
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers z := by
    intro a ha
    have haN : a ∈ N := Subgroup.mem_centralizer_singleton_iff.mpr (hA'C a ha z hzQ).symm
    have ha3 : a ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := A.map (MulAut.conj g).toMonoidHom) (x := ⟨a, ha⟩)
      rw [hA'] at h
      exact congrArg Subtype.val h
    have hcen := hP₀ ⟨a, haN⟩ (Subtype.ext ha3) fun p hp =>
      Subtype.ext (hA'C a ha p (hQ (Subgroup.mem_map_of_mem N.subtype hp))).symm
    rw [hZeq] at hcen
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcen
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hzord, hA'])

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
