module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Frame
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Fuse
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Bound

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open CFSG Subgroup Equiv

namespace Gam

section GroupOnly

variable {X : Type} [Group X]

private theorem mem_pair_iff {s t g : X} :
    g ∈ centralizer ({s, t} : Set X) ↔ s * g = g * s ∧ t * g = g * t := by
  simp [mem_centralizer_iff]

private theorem mem_C_t {s t g : X} (hg : g ∈ centralizer ({s, t} : Set X)) :
    g ∈ centralizer ({t} : Set X) :=
  centralizer_le (by simp) hg

private theorem mem_C_s {s t g : X} (hg : g ∈ centralizer ({s, t} : Set X)) :
    g ∈ centralizer ({s} : Set X) :=
  centralizer_le (by simp) hg

private theorem conj_comm {n a b : X} (h : a * b = b * a) :
    n * a * n⁻¹ * (n * b * n⁻¹) = n * b * n⁻¹ * (n * a * n⁻¹) := by
  calc n * a * n⁻¹ * (n * b * n⁻¹) = n * (a * b) * n⁻¹ := by group
    _ = n * (b * a) * n⁻¹ := by rw [h]
    _ = n * b * n⁻¹ * (n * a * n⁻¹) := by group

private theorem comm_t {s t y : X} (hs2 : s * s = 1) (h1 : s * y = y * s)
    (h2 : s * t * y = y * (s * t)) : t * y = y * t := by
  calc t * y = s * (s * t) * y := by rw [← mul_assoc s s t, hs2, one_mul]
    _ = s * (s * t * y) := mul_assoc _ _ _
    _ = s * (y * (s * t)) := by rw [h2]
    _ = (s * y) * (s * t) := (mul_assoc _ _ _).symm
    _ = (y * s) * (s * t) := by rw [h1]
    _ = y * (s * (s * t)) := mul_assoc _ _ _
    _ = y * t := by rw [← mul_assoc s s t, hs2, one_mul]

private theorem conj_mem {s t n g : X} (hs2 : s * s = 1) (hnt : n * t * n⁻¹ = s)
    (hns : n * s * n⁻¹ = s * t) (hg : g ∈ centralizer ({s, t} : Set X)) :
    n * g * n⁻¹ ∈ centralizer ({s, t} : Set X) := by
  obtain ⟨hgs, hgt⟩ := mem_pair_iff.mp hg
  have h1 : s * (n * g * n⁻¹) = n * g * n⁻¹ * s := by
    have := conj_comm (n := n) hgt
    rwa [hnt] at this
  have h2 : s * t * (n * g * n⁻¹) = n * g * n⁻¹ * (s * t) := by
    have := conj_comm (n := n) hgs
    rwa [hns] at this
  exact mem_pair_iff.mpr ⟨h1, comm_t hs2 h1 h2⟩

private theorem conj_inv_mem {s t n g : X} (hnt : n * t * n⁻¹ = s)
    (hns : n * s * n⁻¹ = s * t) (hg : g ∈ centralizer ({s, t} : Set X)) :
    n⁻¹ * g * n ∈ centralizer ({s, t} : Set X) := by
  obtain ⟨hgs, hgt⟩ := mem_pair_iff.mp hg
  have e1 : n⁻¹ * s * n = t := by rw [← hnt]; group
  have e2 : n⁻¹ * (s * t) * n = s := by rw [← hns]; group
  have hgst : s * t * g = g * (s * t) := by
    calc s * t * g = s * (t * g) := mul_assoc _ _ _
      _ = s * (g * t) := by rw [hgt]
      _ = (s * g) * t := (mul_assoc _ _ _).symm
      _ = (g * s) * t := by rw [hgs]
      _ = g * (s * t) := mul_assoc _ _ _
  have h1 : t * (n⁻¹ * g * n) = n⁻¹ * g * n * t := by
    have := conj_comm (n := n⁻¹) hgs
    simpa only [inv_inv, e1] using this
  have h2 : s * (n⁻¹ * g * n) = n⁻¹ * g * n * s := by
    have := conj_comm (n := n⁻¹) hgst
    simpa only [inv_inv, e2] using this
  exact mem_pair_iff.mpr ⟨h2, h1⟩

private def Lam (M : Subgroup X) (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)) (s t : X) :
    Subgroup X where
  carrier := {y | y ∈ centralizer ({s, t} : Set X) ∧ y ∈ M ∧ rhoX ρ y ∈ Stab6}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by
    rw [rhoX_mul (le_normalizer ha.2.1) (le_normalizer hb.2.1)]
    exact mul_mem ha.2.2 hb.2.2⟩
  one_mem' := ⟨one_mem _, one_mem _, by rw [rhoX_one]; exact one_mem _⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, inv_mem ha.2.1, by
    rw [rhoX_inv (le_normalizer ha.2.1)]
    exact inv_mem ha.2.2⟩

private theorem Lam_le {M : Subgroup X} {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} {s t : X} :
    Lam M ρ s t ≤ centralizer ({s, t} : Set X) := fun _ hy => hy.1

private theorem mem_sup_Lam {M : Subgroup X} {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)}
    {s t : X} {A : Subgroup X} {u v : X} (hu : u ∈ A)
    (huΓ : u ∈ centralizer ({s, t} : Set X)) (huM : u ∈ M)
    (hvΓ : v ∈ centralizer ({s, t} : Set X)) (hvM : v ∈ M)
    (h : (rhoX ρ u)⁻¹ * rhoX ρ v ∈ Stab6) : v ∈ A ⊔ Lam M ρ s t := by
  have hl : u⁻¹ * v ∈ Lam M ρ s t :=
    ⟨mul_mem (inv_mem huΓ) hvΓ, mul_mem (inv_mem huM) hvM, by
      rw [rhoX_mul (le_normalizer (inv_mem huM)) (le_normalizer hvM),
        rhoX_inv (le_normalizer huM)]
      exact h⟩
  have := mul_mem (mem_sup_left hu) (mem_sup_right hl : u⁻¹ * v ∈ A ⊔ Lam M ρ s t)
  rwa [mul_inv_cancel_left] at this

private theorem mem_sup_Lam_of_eq {M : Subgroup X}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)}
    {s t : X} {A : Subgroup X} {u v : X} (hu : u ∈ A)
    (huΓ : u ∈ centralizer ({s, t} : Set X)) (huM : u ∈ M)
    (hvΓ : v ∈ centralizer ({s, t} : Set X)) (hvM : v ∈ M)
    (h : rhoX ρ v = rhoX ρ u) : v ∈ A ⊔ Lam M ρ s t :=
  mem_sup_Lam hu huΓ huM hvΓ hvM (by rw [h, inv_mul_cancel]; exact one_mem _)

end GroupOnly

section PermFacts

private theorem p_comm_σ₀ (i : Fin 4) : p i * σ₀ = σ₀ * p i := by
  unfold σ₀
  exact Commute.mul_right (Commute.mul_right (p_comm i 0) (p_comm i 1)) (p_comm i 2)

private theorem p12_mul_self : p 1 * p 2 * (p 1 * p 2) = 1 := by
  calc p 1 * p 2 * (p 1 * p 2) = p 1 * (p 2 * p 1) * p 2 := by group
    _ = p 1 * (p 1 * p 2) * p 2 := by rw [p_comm 2 1]
    _ = (p 1 * p 1) * (p 2 * p 2) := by group
    _ = 1 := by rw [p_mul_self, p_mul_self, one_mul]

private theorem σ₀_mul_p12 : σ₀ * (p 1 * p 2) = p 0 := by
  calc σ₀ * (p 1 * p 2) = p 0 * (p 1 * p 2 * (p 1 * p 2)) := by simp only [σ₀, mul_assoc]
    _ = p 0 := by rw [p12_mul_self, mul_one]

private theorem p12_mul_p02 : p 1 * p 2 * (p 0 * p 2) = p 0 * p 1 := by
  calc p 1 * p 2 * (p 0 * p 2) = p 1 * (p 2 * p 0) * p 2 := by group
    _ = p 1 * (p 0 * p 2) * p 2 := by rw [p_comm 2 0]
    _ = p 1 * p 0 * (p 2 * p 2) := by group
    _ = p 0 * p 1 := by rw [p_mul_self, mul_one, p_comm 1 0]

private theorem sign_p0 : Perm.sign (p 0) = -1 := by
  unfold p
  exact Perm.sign_swap (by simp [Fin.ext_iff])

end PermFacts

end Gam

open Gam

variable {X : Type} [Group X] [Finite X] {M : Subgroup X}
  {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} {t s : X} {H Q : Subgroup X}

namespace Ctx

variable (Z : Ctx M θ ρ t s H Q)
include Z

private theorem gam_N {g : X} (hg : g ∈ centralizer ({s, t} : Set X)) :
    g ∈ normalizer (M : Set X) :=
  Z.mem_normalizer_of_mem_C (mem_C_t hg)

private theorem gam_comm_σ₀ {g : X} (hg : g ∈ centralizer ({s, t} : Set X)) :
    rhoX ρ g * σ₀ = σ₀ * rhoX ρ g := by
  have hgN := Z.gam_N hg
  have h := congrArg (rhoX ρ) (mem_pair_iff.mp hg).1
  rw [rhoX_mul Z.s_mem_N hgN, rhoX_mul hgN Z.s_mem_N, Z.hρs] at h
  exact h.symm

private noncomputable def rhoG : ↥(centralizer ({s, t} : Set X)) →* Perm (Fin 9) :=
  ρ.comp (inclusion fun _ hg => Z.gam_N hg)

private theorem rhoG_apply (γ : ↥(centralizer ({s, t} : Set X))) : Z.rhoG γ = rhoX ρ γ :=
  (rhoX_of_mem (Z.gam_N γ.2)).symm

private theorem gam_ker :
    ∀ R : Subgroup ↥(centralizer ({s, t} : Set X)), R ≤ Z.rhoG.ker → IsPGroup 2 R →
      Nat.card R ≤ 2 := by
  intro R hRk hR2
  have h1 : IsPGroup 2 (R.map (centralizer ({s, t} : Set X)).subtype) :=
    hR2.of_equiv (equivMapOfInjective R _ (centralizer ({s, t} : Set X)).subtype_injective)
  have hRt : R.map (centralizer ({s, t} : Set X)).subtype ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨γ, -, rfl⟩
    exact mem_C_t γ.2
  have hRs : R.map (centralizer ({s, t} : Set X)).subtype ≤ centralizer ({s} : Set X) := by
    rintro _ ⟨γ, -, rfl⟩
    exact mem_C_s γ.2
  have hR1 : ∀ r ∈ R.map (centralizer ({s, t} : Set X)).subtype, rhoX ρ r = 1 := by
    rintro _ ⟨γ, hγ, rfl⟩
    have h := hRk hγ
    rwa [MonoidHom.mem_ker, Z.rhoG_apply] at h
  have h2 := Z.kernel_bound hRt hRs hR1 h1
  rwa [card_subtype] at h2

private theorem Lam_odd : Odd (Nat.card ↥(Lam M ρ s t)) := by
  refine odd_card_of_forall_mem_odd_orderOf fun y hy => ?_
  obtain ⟨-, hyM, hyS⟩ := hy
  have hyN : y ∈ normalizer (M : Set X) := le_normalizer hyM
  have h3 : (rhoX ρ y) ^ 3 = 1 := Stab6_alt_pow_three hyS (Z.rho_mem_alt hyM)
  have h3M : y ^ 3 ∈ M := pow_mem hyM 3
  have h31 : ρ ⟨y ^ 3, le_normalizer h3M⟩ = 1 := by
    rw [← rhoX_of_mem (le_normalizer h3M), Z.rhoX_pow hyN, h3]
  have hodd := odd_orderOf_of_rho_eq_one Z.hρ h3M h31
  have hdvd : orderOf y ∣ 3 * orderOf (y ^ 3) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  exact Odd.of_dvd_nat (Odd.mul (by decide) hodd) hdvd

private theorem Lam_normal {g l : X} (hg : g ∈ centralizer ({s, t} : Set X))
    (hl : l ∈ Lam M ρ s t) : g * l * g⁻¹ ∈ Lam M ρ s t := by
  obtain ⟨hlΓ, hlM, hlS⟩ := hl
  have hgN := Z.gam_N hg
  refine ⟨mul_mem (mul_mem hg hlΓ) (inv_mem hg), (mem_normalizer_iff.mp hgN l).mp hlM, ?_⟩
  rw [rhoX_conj hgN (le_normalizer hlM)]
  exact Zs_conj_Stab6 (Z.gam_comm_σ₀ hg) hlS

end Ctx

namespace IsFrame

variable {Z : Ctx M θ ρ t s H Q} {w₀ w₁ x : X} (F : IsFrame Z w₀ w₁ x)
include F

private theorem gam_gen_mem (i : Fin 5) :
    ![s, t, w₀, w₁, x] i ∈ centralizer ({s, t} : Set X) := by
  rw [mem_pair_iff]
  exact ⟨F.E5.comm 0 i, F.E5.comm 1 i⟩

private theorem gam_A_le :
    closure (Set.range ![s, t, w₀, w₁, x]) ≤ centralizer ({s, t} : Set X) := by
  rw [closure_le]
  rintro _ ⟨i, rfl⟩
  exact F.gam_gen_mem i

private theorem gam_rho_even {τ : Perm (Fin 9)} (hτ : τ ∈ alternatingGroup (Fin 9))
    (hcomm : τ * σ₀ = σ₀ * τ) : ∃ y ∈ centralizer ({s, t} : Set X), rhoX ρ y = τ := by
  have hsA : s ∈ closure (Set.range ![s, t, w₀, w₁, x]) := subset_closure ⟨0, rfl⟩
  have htA : t ∈ closure (Set.range ![s, t, w₀, w₁, x]) := subset_closure ⟨1, rfl⟩
  have hBA : zpowers s ⊔ zpowers t ≤ closure (Set.range ![s, t, w₀, w₁, x]) :=
    sup_le (zpowers_le.mpr hsA) (zpowers_le.mpr htA)
  have hB2 : IsPGroup 2 ↥(zpowers s ⊔ zpowers t) := F.E5.isPGroup_closure.to_le hBA
  have hBN : zpowers s ⊔ zpowers t ≤ normalizer (M : Set X) :=
    sup_le (zpowers_le.mpr Z.s_mem_N) (zpowers_le.mpr Z.t_mem_N)
  have hb : ∀ (g : X) (hg : g ∈ zpowers s ⊔ zpowers t),
      τ * ρ ⟨g, hBN hg⟩ = ρ ⟨g, hBN hg⟩ * τ := by
    let K : Subgroup X := ((centralizer ({τ} : Set (Perm (Fin 9)))).comap ρ).map
      (normalizer (M : Set X)).subtype
    have hsK : s ∈ K := ⟨⟨s, Z.s_mem_N⟩, by
      show ρ ⟨s, Z.s_mem_N⟩ ∈ centralizer ({τ} : Set (Perm (Fin 9)))
      rw [mem_centralizer_singleton_iff, ← rhoX_of_mem Z.s_mem_N, Z.hρs]
      exact hcomm.symm, rfl⟩
    have htK : t ∈ K := ⟨⟨t, Z.t_mem_N⟩, by
      show ρ ⟨t, Z.t_mem_N⟩ ∈ centralizer ({τ} : Set (Perm (Fin 9)))
      rw [mem_centralizer_singleton_iff, ← rhoX_of_mem Z.t_mem_N, Z.rho_t]
      simp, rfl⟩
    have hBK : zpowers s ⊔ zpowers t ≤ K := sup_le (zpowers_le.mpr hsK) (zpowers_le.mpr htK)
    intro g hg
    obtain ⟨k, hk, hkg⟩ := hBK hg
    have hk' : ρ k * τ = τ * ρ k := mem_centralizer_singleton_iff.mp hk
    have hkk : k = ⟨g, hBN hg⟩ := Subtype.ext hkg
    rw [← hkk]
    exact hk'.symm
  obtain ⟨y, hyC, hyθ⟩ := Z.hρ.exists_lift_of_isPGroup hBN hB2 (b := ⟨τ, hτ⟩) hb
  have hyΓ : (y : X) ∈ centralizer ({s, t} : Set X) := by
    refine centralizer_le ?_ hyC
    exact Set.insert_subset_iff.mpr ⟨mem_sup_left (mem_zpowers s),
      Set.singleton_subset_iff.mpr (mem_sup_right (mem_zpowers t))⟩
  refine ⟨y, hyΓ, ?_⟩
  rw [rhoX_of_mem (le_normalizer y.2), Z.hρ.apply_of_mem (by norm_num) y, hyθ]

private theorem gam_rho {τ : Perm (Fin 9)} (hcomm : τ * σ₀ = σ₀ * τ) :
    ∃ y ∈ centralizer ({s, t} : Set X), rhoX ρ y = τ := by
  by_cases hτ : τ ∈ alternatingGroup (Fin 9)
  · exact F.gam_rho_even hτ hcomm
  · have hsΓ : s ∈ centralizer ({s, t} : Set X) := F.gam_A_le (subset_closure ⟨0, rfl⟩)
    have hw₀Γ : w₀ ∈ centralizer ({s, t} : Set X) := F.gam_A_le (subset_closure ⟨2, rfl⟩)
    have ha₀Γ : s * w₀ ∈ centralizer ({s, t} : Set X) := mul_mem hsΓ hw₀Γ
    have ha₀ρ : rhoX ρ (s * w₀) = p 0 := by
      rw [rhoX_mul Z.s_mem_N (le_normalizer F.w₀M), Z.hρs, F.ρw₀, σ₀_mul_p12]
    have hτ' : Perm.sign τ = -1 := by
      rw [Perm.mem_alternatingGroup] at hτ
      exact (Int.units_eq_one_or _).resolve_left hτ
    have hev : τ * p 0 ∈ alternatingGroup (Fin 9) := by
      rw [Perm.mem_alternatingGroup, map_mul, hτ', sign_p0]
      decide
    have hc : τ * p 0 * σ₀ = σ₀ * (τ * p 0) := by
      calc τ * p 0 * σ₀ = τ * (p 0 * σ₀) := mul_assoc _ _ _
        _ = τ * (σ₀ * p 0) := by rw [p_comm_σ₀ 0]
        _ = (τ * σ₀) * p 0 := (mul_assoc _ _ _).symm
        _ = (σ₀ * τ) * p 0 := by rw [hcomm]
        _ = σ₀ * (τ * p 0) := mul_assoc _ _ _
    obtain ⟨y, hyΓ, hy⟩ := F.gam_rho_even hev hc
    refine ⟨y * (s * w₀), mul_mem hyΓ ha₀Γ, ?_⟩
    rw [rhoX_mul (Z.gam_N hyΓ) (Z.gam_N ha₀Γ), hy, ha₀ρ, mul_assoc, p_mul_self, mul_one]

private theorem gam_range :
    Z.rhoG.range = centralizer ({σ₀} : Set (Perm (Fin 9))) := by
  ext τ
  rw [MonoidHom.mem_range, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨γ, rfl⟩
    rw [Z.rhoG_apply]
    exact Z.gam_comm_σ₀ γ.2
  · intro hτ
    obtain ⟨y, hyΓ, hy⟩ := F.gam_rho hτ
    exact ⟨⟨y, hyΓ⟩, by rw [Z.rhoG_apply]; exact hy⟩

private theorem gam_hEΛ {γ : X} (hγ : γ ∈ centralizer ({s, t} : Set X)) :
    ∀ e ∈ closure (Set.range ![s, t, w₀, w₁, x]),
      γ * e * γ⁻¹ ∈ closure (Set.range ![s, t, w₀, w₁, x]) ⊔ Lam M ρ s t := by
  have hγN := Z.gam_N hγ
  have hcomm := Z.gam_comm_σ₀ hγ
  have hγs := (mem_pair_iff.mp hγ).1
  have hγt := (mem_pair_iff.mp hγ).2
  have hsA : s ∈ closure (Set.range ![s, t, w₀, w₁, x]) := subset_closure ⟨0, rfl⟩
  have htA : t ∈ closure (Set.range ![s, t, w₀, w₁, x]) := subset_closure ⟨1, rfl⟩
  have hw₀A : w₀ ∈ closure (Set.range ![s, t, w₀, w₁, x]) := subset_closure ⟨2, rfl⟩
  have hw₁A : w₁ ∈ closure (Set.range ![s, t, w₀, w₁, x]) := subset_closure ⟨3, rfl⟩
  have hxA : x ∈ closure (Set.range ![s, t, w₀, w₁, x]) := subset_closure ⟨4, rfl⟩
  have hw₀Γ := F.gam_A_le hw₀A
  have hw₁Γ := F.gam_A_le hw₁A
  have hxΓ := F.gam_A_le hxA
  have hconjΓ : ∀ {g : X}, g ∈ centralizer ({s, t} : Set X) →
      γ * g * γ⁻¹ ∈ centralizer ({s, t} : Set X) :=
    fun hg => mul_mem (mul_mem hγ hg) (inv_mem hγ)
  have hconjM : ∀ {g : X}, g ∈ M → γ * g * γ⁻¹ ∈ M :=
    fun hg => (mem_normalizer_iff.mp hγN _).mp hg
  have hρconj : ∀ {g : X}, g ∈ M →
      rhoX ρ (γ * g * γ⁻¹) = rhoX ρ γ * rhoX ρ g * (rhoX ρ γ)⁻¹ :=
    fun hg => rhoX_conj hγN (le_normalizer hg)
  have hs' : γ * s * γ⁻¹ ∈ closure (Set.range ![s, t, w₀, w₁, x]) ⊔ Lam M ρ s t := by
    rw [← hγs, mul_inv_cancel_right]
    exact mem_sup_left hsA
  have ht' : γ * t * γ⁻¹ ∈ closure (Set.range ![s, t, w₀, w₁, x]) ⊔ Lam M ρ s t := by
    rw [← hγt, mul_inv_cancel_right]
    exact mem_sup_left htA
  have hw₀' : γ * w₀ * γ⁻¹ ∈ closure (Set.range ![s, t, w₀, w₁, x]) ⊔ Lam M ρ s t := by
    have hρ' : rhoX ρ (γ * w₀ * γ⁻¹) = rhoX ρ γ * (p 1 * p 2) * (rhoX ρ γ)⁻¹ := by
      rw [hρconj F.w₀M, F.ρw₀]
    have hvΓ := hconjΓ hw₀Γ
    have hvM := hconjM F.w₀M
    rcases Zs_conj_U12 hcomm with h | h | h
    · exact mem_sup_Lam_of_eq hw₀A hw₀Γ F.w₀M hvΓ hvM (by rw [hρ', h, F.ρw₀])
    · exact mem_sup_Lam_of_eq hw₁A hw₁Γ F.w₁M hvΓ hvM (by rw [hρ', h, F.ρw₁])
    · exact mem_sup_Lam_of_eq (mul_mem hw₀A hw₁A) (mul_mem hw₀Γ hw₁Γ) (mul_mem F.w₀M F.w₁M)
        hvΓ hvM (by
          rw [hρ', h, rhoX_mul (le_normalizer F.w₀M) (le_normalizer F.w₁M), F.ρw₀, F.ρw₁,
            p12_mul_p02])
  have hw₁' : γ * w₁ * γ⁻¹ ∈ closure (Set.range ![s, t, w₀, w₁, x]) ⊔ Lam M ρ s t := by
    have hρ' : rhoX ρ (γ * w₁ * γ⁻¹) = rhoX ρ γ * (p 0 * p 2) * (rhoX ρ γ)⁻¹ := by
      rw [hρconj F.w₁M, F.ρw₁]
    have hvΓ := hconjΓ hw₁Γ
    have hvM := hconjM F.w₁M
    rcases Zs_conj_U02 hcomm with h | h | h
    · exact mem_sup_Lam_of_eq hw₀A hw₀Γ F.w₀M hvΓ hvM (by rw [hρ', h, F.ρw₀])
    · exact mem_sup_Lam_of_eq hw₁A hw₁Γ F.w₁M hvΓ hvM (by rw [hρ', h, F.ρw₁])
    · exact mem_sup_Lam_of_eq (mul_mem hw₀A hw₁A) (mul_mem hw₀Γ hw₁Γ) (mul_mem F.w₀M F.w₁M)
        hvΓ hvM (by
          rw [hρ', h, rhoX_mul (le_normalizer F.w₀M) (le_normalizer F.w₁M), F.ρw₀, F.ρw₁,
            p12_mul_p02])
  have hx' : γ * x * γ⁻¹ ∈ closure (Set.range ![s, t, w₀, w₁, x]) ⊔ Lam M ρ s t := by
    refine mem_sup_Lam hxA hxΓ F.xM (hconjΓ hxΓ) (hconjM F.xM) ?_
    rw [hρconj F.xM, F.ρx]
    exact (Zs_conj_πx hcomm).1
  let T : Subgroup X :=
    (closure (Set.range ![s, t, w₀, w₁, x]) ⊔ Lam M ρ s t).comap (MulAut.conj γ).toMonoidHom
  have hT : closure (Set.range ![s, t, w₀, w₁, x]) ≤ T := by
    rw [closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hs'
    · exact ht'
    · exact hw₀'
    · exact hw₁'
    · exact hx'
  intro e he
  exact hT he

theorem exists_conj_gamma {n : X} (hnt : n * t * n⁻¹ = s) (hns : n * s * n⁻¹ = s * t) :
    ∃ f ∈ centralizer ({s, t} : Set X),
      (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj n).toMonoidHom =
        (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj f).toMonoidHom :=
  frattini_E32 Z.rhoG F.gam_range Z.gam_ker F.gam_A_le F.E5.isPGroup_closure
    (F.E5.card_closure_of_injective F.mono_injective) (Λ := Lam M ρ s t) Lam_le
    (fun g hg l hl => Z.Lam_normal hg hl) Z.Lam_odd (fun γ hγ e he => F.gam_hEΛ hγ e he)
    (fun g hg => conj_mem Z.hs2 hnt hns hg) (fun g hg => conj_inv_mem hnt hns hg)

end IsFrame

end CFSG.ComponentClassification.SolMax.Sig36.E32
