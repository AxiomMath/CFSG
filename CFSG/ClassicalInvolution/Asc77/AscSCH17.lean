module

public import CFSG.ClassicalInvolution.Asc77.AscSCH16
public import CFSG.RankThree.CentralLift.DefiningTools
public import CFSG.ClassicalInvolution.Asc77.AscSCH06

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.SectionRank.OddCover CFSG.RankThree.CentralLift

variable {K : Type} [Field K]

@[expose] def psiDiag : Kˣ × Kˣ × Kˣ →* (Fin 4 → Kˣ) where
  toFun u := ![u.1, u.1⁻¹ * u.2.1, u.2.1⁻¹ * u.2.2, u.2.2⁻¹]
  map_one' := by
    ext i
    fin_cases i <;> simp
  map_mul' a b := by
    ext i
    fin_cases i <;> simp <;> ac_rfl

theorem psiDiag_injective : Function.Injective (psiDiag : Kˣ × Kˣ × Kˣ →* (Fin 4 → Kˣ)) := by
  rintro ⟨a₁, a₂, a₃⟩ ⟨b₁, b₂, b₃⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h3 := congrFun h 3
  simp only [psiDiag, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_three, Fin.isValue] at h0 h1 h3
  have e1 : a₁ = b₁ := h0
  subst e1
  have e2 : a₂ = b₂ := by simpa using h1
  subst e2
  have e3 : a₃ = b₃ := inv_injective h3
  rw [e3]

@[expose] noncomputable def torusPsi : Kˣ × Kˣ × Kˣ →* GL (Fin 4) K := (diagHom 4).comp psiDiag

theorem torusPsi_injective : Function.Injective (torusPsi : Kˣ × Kˣ × Kˣ →* GL (Fin 4) K) :=
  (diagHom_injective 4).comp psiDiag_injective

@[expose] noncomputable def torY₁ (m : Kˣ) : GL (Fin 4) K := diagHom 4 ![m, m⁻¹, 1, 1]

@[expose] noncomputable def torY₂ (m : Kˣ) : GL (Fin 4) K := diagHom 4 ![1, m, m⁻¹, 1]

@[expose] noncomputable def torY₃ (m : Kˣ) : GL (Fin 4) K := diagHom 4 ![1, 1, m, m⁻¹]

theorem torusPsi_zpow (m : Kˣ) (a b c : ℤ) :
    torusPsi (m ^ a, m ^ b, m ^ c) = torY₁ m ^ a * torY₂ m ^ b * torY₃ m ^ c := by
  have h : ((m ^ a, m ^ b, m ^ c) : Kˣ × Kˣ × Kˣ) =
      (m, 1, 1) ^ a * (1, m, 1) ^ b * (1, 1, m) ^ c := by
    ext <;> simp
  rw [h, map_mul, map_mul, map_zpow, map_zpow, map_zpow]
  have e1 : (torusPsi (m, 1, 1) : GL (Fin 4) K) = torY₁ m := by
    show diagHom 4 (psiDiag (m, 1, 1)) = diagHom 4 ![m, m⁻¹, 1, 1]
    congr 1
    funext i
    fin_cases i <;> simp [psiDiag]
  have e2 : (torusPsi (1, m, 1) : GL (Fin 4) K) = torY₂ m := by
    show diagHom 4 (psiDiag (1, m, 1)) = diagHom 4 ![1, m, m⁻¹, 1]
    congr 1
    funext i
    fin_cases i <;> simp [psiDiag]
  have e3 : (torusPsi (1, 1, m) : GL (Fin 4) K) = torY₃ m := by
    show diagHom 4 (psiDiag (1, 1, m)) = diagHom 4 ![1, 1, m, m⁻¹]
    congr 1
    funext i
    fin_cases i <;> simp [psiDiag]
  rw [e1, e2, e3]

section Torus

variable (m : Kˣ)

@[expose] noncomputable def torusM : Subgroup (GL (Fin 4) K) :=
  ((Subgroup.zpowers m).prod ((Subgroup.zpowers m).prod (Subgroup.zpowers m))).map torusPsi

theorem card_torusM : Nat.card (torusM m : Subgroup (GL (Fin 4) K)) = orderOf m ^ 3 := by
  rw [torusM, Subgroup.card_map_of_injective torusPsi_injective,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_zpowers]
  ring

theorem torusM_le_closure : (torusM m : Subgroup (GL (Fin 4) K)) ≤
    Subgroup.closure ({torY₁ m, torY₂ m, torY₃ m} : Set (GL (Fin 4) K)) := by
  rintro _ ⟨u, ⟨hu₁, hu₂, hu₃⟩, rfl⟩
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hu₁
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 hu₂
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.1 hu₃
  have : torusPsi u = torY₁ m ^ a * torY₂ m ^ b * torY₃ m ^ c := by
    rw [← torusPsi_zpow, ha, hb, hc]
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure
    (by simp)) _) (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _))
    (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem torusM_diag {x : GL (Fin 4) K} (hx : x ∈ torusM m) : ∃ d : Fin 4 → Kˣ, x = diagHom 4 d := by
  obtain ⟨u, -, rfl⟩ := hx
  exact ⟨psiDiag u, rfl⟩

theorem cyc4_conj_mem_torusM {x : GL (Fin 4) K} (hx : x ∈ torusM m) :
    cyc4GL * x * cyc4GL⁻¹ ∈ torusM m := by
  obtain ⟨⟨u₁, u₂, u₃⟩, ⟨hu₁, hu₂, hu₃⟩, rfl⟩ := hx
  refine ⟨(u₂⁻¹ * u₃, u₁ * u₂⁻¹ * u₃, u₃), ⟨?_, ?_, hu₃⟩, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hu₂) hu₃
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu₁ (Subgroup.inv_mem _ hu₂)) hu₃
  · show diagHom 4 (psiDiag (u₂⁻¹ * u₃, u₁ * u₂⁻¹ * u₃, u₃)) =
      cyc4GL * diagHom 4 (psiDiag (u₁, u₂, u₃)) * cyc4GL⁻¹
    rw [cyc4GL_conj_diag]
    congr 1
    funext i
    fin_cases i <;> apply Units.ext <;> simp [psiDiag] <;> field_simp

end Torus

section Weyl

variable (m : Kˣ)

theorem torY₁_comm_torY₂ : torY₁ m * torY₂ m = torY₂ m * (torY₁ m : GL (Fin 4) K) := by
  unfold torY₁ torY₂
  rw [← map_mul, ← map_mul, mul_comm]

theorem torY₁_comm_torY₃ : torY₁ m * torY₃ m = torY₃ m * (torY₁ m : GL (Fin 4) K) := by
  unfold torY₁ torY₃
  rw [← map_mul, ← map_mul, mul_comm]

theorem torY₂_comm_torY₃ : torY₂ m * torY₃ m = torY₃ m * (torY₂ m : GL (Fin 4) K) := by
  unfold torY₂ torY₃
  rw [← map_mul, ← map_mul, mul_comm]

theorem w02_torY₁ : w02GL * torY₁ m * w02GL⁻¹ = (torY₂ m : GL (Fin 4) K)⁻¹ := by
  rw [torY₁, w02GL_conj_diag, torY₂, ← map_inv]
  congr 1
  funext i
  fin_cases i <;> simp

theorem w02_torY₂ : w02GL * torY₂ m * w02GL⁻¹ = (torY₁ m : GL (Fin 4) K)⁻¹ := by
  rw [torY₂, w02GL_conj_diag, torY₁, ← map_inv]
  congr 1
  funext i
  fin_cases i <;> simp

theorem w13_torY₂ : w13GL * torY₂ m * w13GL⁻¹ = (torY₃ m : GL (Fin 4) K)⁻¹ := by
  rw [torY₂, w13GL_conj_diag, torY₃, ← map_inv]
  congr 1
  funext i
  fin_cases i <;> simp

theorem w13_torY₃ : w13GL * torY₃ m * w13GL⁻¹ = (torY₂ m : GL (Fin 4) K)⁻¹ := by
  rw [torY₃, w13GL_conj_diag, torY₂, ← map_inv]
  congr 1
  funext i
  fin_cases i <;> simp

theorem w01_torY₁ : w01GL * torY₁ m * w01GL⁻¹ = (torY₁ m : GL (Fin 4) K)⁻¹ := by
  rw [torY₁, w01GL_conj_diag, ← map_inv]
  congr 1
  funext i
  fin_cases i <;> simp

theorem w01_torY₃ : w01GL * torY₃ m * w01GL⁻¹ = (torY₃ m : GL (Fin 4) K) := by
  rw [torY₃, w01GL_conj_diag]
  congr 1

end Weyl

theorem cyc4GL_pow_three : (cyc4GL : GL (Fin 4) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_cyc4GL, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc4Mat, pow_succ, Matrix.mul_apply, Fin.sum_univ_four]

theorem cyc4GL_not_mem_torusM (m : Kˣ) : (cyc4GL : GL (Fin 4) K) ∉ torusM m := by
  intro h
  obtain ⟨d, hd⟩ := torusM_diag m h
  have := congrFun (congrFun (congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K))
    hd) 1) 0
  simp [coe_cyc4GL, cyc4Mat, coe_diagHom] at this

section Main

variable {E : Type*} [Group E]

theorem ker_eq_bot_of_monomial_torus (m : Kˣ) (H : Subgroup (GL (Fin 4) K)) [Finite H]
    (hY₁ : torY₁ m ∈ H) (hY₂ : torY₂ m ∈ H) (hY₃ : torY₃ m ∈ H) (hc : cyc4GL ∈ H)
    (h02 : w02GL ∈ H) (h13 : w13GL ∈ H) (h01 : w01GL ∈ H)
    (hord : (Nat.card H).factorization 3 ≤ 3 * (orderOf m).factorization 3 + 1)
    [Finite E] [Group.IsPerfect E] (π : E →* H) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup 3 π.ker) : π.ker = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hclos : Subgroup.closure ({torY₁ m, torY₂ m, torY₃ m} : Set (GL (Fin 4) K)) ≤ H :=
    (Subgroup.closure_le _).2 (by rintro _ (rfl | rfl | rfl) <;> assumption)
  have hT : torusM m ≤ H := (torusM_le_closure m).trans hclos
  have hcc : (⟨cyc4GL, hc⟩ : H) ∈ Subgroup.normalizer (((torusM m).subgroupOf H : Subgroup H) :
      Set H) := by
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    exact cyc4_conj_mem_torusM m hx
  refine ker_eq_bot_of_torus_three_le (by norm_num) π hπ hC hCp ⟨torY₁ m, hY₁⟩ ⟨torY₂ m, hY₂⟩
    ⟨torY₃ m, hY₃⟩ ⟨cyc4GL, hc⟩ ⟨w01GL, h01⟩ (Subtype.ext (torY₁_comm_torY₂ m))
    (Subtype.ext (torY₁_comm_torY₃ m)) (Subtype.ext (torY₂_comm_torY₃ m)) ⟨w02GL, h02⟩
    ⟨w13GL, h13⟩ ⟨w01GL, h01⟩ (Subtype.ext (w02_torY₁ m)) (Subtype.ext (w02_torY₂ m))
    (Subtype.ext (w13_torY₂ m)) (Subtype.ext (w13_torY₃ m)) (Subtype.ext (w01_torY₁ m))
    (Subtype.ext (w01_torY₃ m)) ((torusM m).subgroupOf H) ?_ hcc
    (Subtype.ext w01GL_conj_cyc4GL) ?_ ?_
  · intro t ht
    obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hut⟩ := ht
    have hut' : torusPsi u = (t : GL (Fin 4) K) := hut
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hu₁
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 hu₂
    obtain ⟨c, hc'⟩ := Subgroup.mem_zpowers_iff.1 hu₃
    have : t = (⟨torY₁ m, hY₁⟩ : H) ^ a * ⟨torY₂ m, hY₂⟩ ^ b * ⟨torY₃ m, hY₃⟩ ^ c := by
      apply Subtype.ext
      rw [← hut', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow,
        Subgroup.coe_zpow, ← torusPsi_zpow, ha, hb, hc']
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure
      (by simp)) _) (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _))
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
  · intro t ht hct
    obtain ⟨d, hd⟩ := torusM_diag m (show (t : GL (Fin 4) K) ∈ torusM m from ht)
    have h1 : (cyc4GL : GL (Fin 4) K) * (t : GL (Fin 4) K) * cyc4GL⁻¹ = (t : GL (Fin 4) K) :=
      congrArg Subtype.val hct
    rw [hd, cyc4GL_conj_diag] at h1
    have h2 := diagHom_injective 4 h1
    have e0 := congrFun h2 0
    have e1 := congrFun h2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at e0 e1
    apply Subtype.ext
    show (w01GL : GL (Fin 4) K) * (t : GL (Fin 4) K) * w01GL⁻¹ = (t : GL (Fin 4) K)
    rw [hd, w01GL_conj_diag]
    congr 1
    funext i
    fin_cases i <;> simp <;> first | exact e1.symm | exact e1
  · have hcT : (⟨cyc4GL, hc⟩ : H) ∉ (torusM m).subgroupOf H := fun h =>
      cyc4GL_not_mem_torusM m h
    have hcp : (⟨cyc4GL, hc⟩ : H) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, cyc4GL_pow_three]; rfl)
    have h1 := factorization_sup_zpowers_ge ((torusM m).subgroupOf H) ⟨cyc4GL, hc⟩ hcc hcT hcp
    have hcardT : Nat.card ((torusM m).subgroupOf H) = orderOf m ^ 3 := by
      rw [← card_torusM m]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
    rw [hcardT, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h1
    omega

end Main

end CFSG.ClassicalInvolution.Asc77.SCH
