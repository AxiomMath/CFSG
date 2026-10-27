module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx37
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic8
public import CFSG.LieType.Multipliers.KernelStructure
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx29

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h t : G}

theorem mem_N_decomp (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {g : G} (hg : g ∈ S ⊔ zpowers h) :
    ∃ s ∈ S, ∃ i : ℤ, g = s * h ^ i := by
  have hprod := hs.h_prod
  have hkey : ∀ (i : ℤ) (s' : G), s' ∈ S → ∃ s'' ∈ S, ∃ k : ℤ, h ^ i * s' = s'' * h ^ k := by
    intro i s' hs'
    have h1 : h ^ i * s' ∈ (zpowers h : Set G) * (S : Set G) :=
      Set.mul_mem_mul (Subgroup.zpow_mem _ (Subgroup.mem_zpowers h) i) hs'
    rw [← hprod] at h1
    obtain ⟨s'', hs'', y, hy, hyy⟩ := h1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨s'', hs'', k, hyy.symm⟩
  let Psub : Subgroup G :=
    { carrier := {g | ∃ s ∈ S, ∃ i : ℤ, g = s * h ^ i}
      mul_mem' := by
        rintro a b ⟨s₁, hs₁, i, rfl⟩ ⟨s₂, hs₂, j, rfl⟩
        obtain ⟨s₃, hs₃, k, hk⟩ := hkey i s₂ hs₂
        refine ⟨s₁ * s₃, mul_mem hs₁ hs₃, k + j, ?_⟩
        calc s₁ * h ^ i * (s₂ * h ^ j) = s₁ * (h ^ i * s₂) * h ^ j := by group
          _ = s₁ * (s₃ * h ^ k) * h ^ j := by rw [hk]
          _ = s₁ * s₃ * h ^ (k + j) := by rw [zpow_add]; group
      one_mem' := ⟨1, one_mem _, 0, by simp⟩
      inv_mem' := by
        rintro a ⟨s, hs₁, i, rfl⟩
        obtain ⟨s₃, hs₃, k, hk⟩ := hkey (-i) s⁻¹ (inv_mem hs₁)
        refine ⟨s₃, hs₃, k, ?_⟩
        calc (s * h ^ i)⁻¹ = h ^ (-i) * s⁻¹ := by group
          _ = s₃ * h ^ k := hk }
  have hle : S ⊔ zpowers h ≤ Psub := by
    apply sup_le
    · intro s hs'
      exact ⟨s, hs', 0, by simp⟩
    · rw [zpowers_le]
      exact ⟨1, one_mem _, 1, by simp⟩
  exact hle hg

theorem h_mem_normalizer_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    h ∈ normalizer ((Aof S K₁ W₂ h : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact (hs.A_conj hII hq hrec hk ha).1
  · intro ha
    have := (hs.A_conj hII hq hrec hk ha).2
    have e : h⁻¹ * (h * a * h⁻¹) * h = a := by group
    rwa [e] at this

theorem N_le_normalizer_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    S ⊔ zpowers h ≤ normalizer ((Aof S K₁ W₂ h : Subgroup G) : Set G) := by
  apply sup_le
  · intro s hsS
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hs.A_normS hII hq hrec hsS ha
    · intro ha
      have := hs.A_normS hII hq hrec (inv_mem hsS) ha
      have e : s⁻¹ * (s * a * s⁻¹) * s⁻¹⁻¹ = a := by group
      rwa [e] at this
  · rw [zpowers_le]
    exact hs.h_mem_normalizer_A hII hq hrec hk

theorem orderOf_conjAut_h (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) :
    orderOf (Basic.conjAut (Aof S K₁ W₂ h) h (hs.h_mem_normalizer_A hII hq hrec hk)) = 3 := by
  have hAW := hs.A_le_W hII hq hrec (le_refl _) hk
  have hzA : z ∈ Aof S K₁ W₂ h := hs.U_le_A hII hq hrec (le_refl _) hk hs.z_mem
  apply orderOf_eq_prime
  · have e3 : ∀ σ : MulAut ↥(Aof S K₁ W₂ h), σ ^ 3 = σ * σ * σ := fun σ => by
      simp only [pow_succ, pow_zero, one_mul]
    rw [e3]
    ext a
    show h * (h * (h * (a : G) * h⁻¹) * h⁻¹) * h⁻¹ = a
    have hcen := hs.h_cube a (hAW a.2)
    have e3' : h ^ 3 = h * h * h := by simp only [pow_succ, pow_zero, one_mul]
    rw [e3'] at hcen
    calc h * (h * (h * (a : G) * h⁻¹) * h⁻¹) * h⁻¹ = (h * h * h) * a * (h * h * h)⁻¹ := by group
      _ = (a * (h * h * h)) * (h * h * h)⁻¹ := by rw [hcen]
      _ = a := by group
  · intro h1
    apply hs.h_move
    have h2 : h * z * h⁻¹ = z := by
      have := congrArg (fun f : MulAut ↥(Aof S K₁ W₂ h) => ((f ⟨z, hzA⟩ : ↥(Aof S K₁ W₂ h)) : G)) h1
      exact this
    have h3 : h * z = z * h := by
      calc h * z = (h * z * h⁻¹) * h := by group
        _ = z * h := by rw [h2]
    calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
      _ = h⁻¹ * (h * z) := by rw [h3]
      _ = z := by group

@[expose] def prodEquivZ4Z4 :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃* Bg.TwoGroups.Z4Z4 where
  toFun p := Multiplicative.ofAdd (Multiplicative.toAdd p.1, Multiplicative.toAdd p.2)
  invFun q := (Multiplicative.ofAdd (Multiplicative.toAdd q).1,
    Multiplicative.ofAdd (Multiplicative.toAdd q).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem A_equiv_Z4Z4 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) :
    Nonempty (↥(Aof S K₁ W₂ h) ≃* Bg.TwoGroups.Z4Z4) := by
  obtain ⟨x, hVx, hxo, hx'o, hbot, hz⟩ := hs.xdata hII hq hk
  have hxV : x ∈ Vof S K₁ W₂ := hVx ▸ Subgroup.mem_zpowers x
  have hxA : x ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left hxV
  have hyA : h⁻¹ * x * h ∈ Aof S K₁ W₂ h := (hs.A_conj hII hq hrec hk hxA).2
  have hcomm : Commute x (h⁻¹ * x * h) := hs.A_comm hII hq hrec _ hxA _ hyA
  have hx4 : x ^ 4 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hy4 : (h⁻¹ * x * h) ^ 4 = 1 := by rw [← hx'o]; exact pow_orderOf_eq_one _
  have hx2 : x ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hxo]; norm_num)
  have hy2 : (h⁻¹ * x * h) ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hx'o]; norm_num)
  have hxy2 : x ^ 2 * (h⁻¹ * x * h) ^ 2 ≠ 1 := by
    intro h1
    apply hs.h_move
    have e : x ^ 2 * (h⁻¹ * x * h) ^ 2 = z * (h⁻¹ * z * h) := by
      rw [hz, pow_two, pow_two]
      group
    rw [e] at h1
    have h2 : h⁻¹ * z * h = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right hs.z_sq
  have hcard : Nat.card ↥(Aof S K₁ W₂ h) ≤ 16 := by
    have := hs.card_A hII hq hrec hk
    omega
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.nonempty_mulEquiv_zmod_four_four (Aof S K₁ W₂ h) hcard
    hxA hyA hcomm hx4 hy4 hx2 hy2 hxy2
  exact ⟨e.trans prodEquivZ4Z4⟩

theorem cent_N_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) {g : G}
    (hg : g ∈ S ⊔ zpowers h) (hc : ∀ a ∈ Aof S K₁ W₂ h, g * a = a * g) :
    g ∈ Aof S K₁ W₂ h ⊔ zpowers (h ^ 3) := by
  have hNA := hs.N_le_normalizer_A hII hq hrec hk
  have hhN : h ∈ S ⊔ zpowers h := Subgroup.mem_sup_right (Subgroup.mem_zpowers h)
  obtain ⟨s, hsS, i, hgi⟩ := hs.mem_N_decomp hg
  have hsN : s ∈ S ⊔ zpowers h := Subgroup.mem_sup_left hsS
  let f := Basic.conjHom (Aof S K₁ W₂ h) (S ⊔ zpowers h) hNA
  have hord3 := hs.orderOf_conjAut_h hII hq hrec hk
  have hσ : f ⟨h, hhN⟩ = Basic.conjAut (Aof S K₁ W₂ h) h (hs.h_mem_normalizer_A hII hq hrec hk) := rfl
  have hσ3 : (f ⟨h, hhN⟩) ^ 3 = 1 := by
    rw [hσ]
    have := pow_orderOf_eq_one (Basic.conjAut (Aof S K₁ W₂ h) h (hs.h_mem_normalizer_A hII hq hrec hk))
    rwa [hord3] at this
  have hf1 : f ⟨g, hg⟩ = 1 := by
    ext a
    show g * (a : G) * g⁻¹ = a
    calc g * (a : G) * g⁻¹ = (a * g) * g⁻¹ := by rw [hc a a.2]
      _ = a := by group
  have hdecomp : (⟨g, hg⟩ : ↥(S ⊔ zpowers h)) = ⟨s, hsN⟩ * ⟨h, hhN⟩ ^ i := by
    apply Subtype.ext
    simpa [Subgroup.coe_mul, Subgroup.coe_zpow] using hgi
  have h2 : f ⟨s, hsN⟩ * (f ⟨h, hhN⟩) ^ i = 1 := by
    rw [← map_zpow, ← map_mul, ← hdecomp]
    exact hf1
  have hτ : f ⟨s, hsN⟩ = (f ⟨h, hhN⟩) ^ (-i) := by
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left h2
  have hpow3 : ∀ j : ℤ, ((f ⟨h, hhN⟩) ^ j) ^ 3 = 1 := fun j => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ3, one_zpow]
  have hτ3 : (f ⟨s, hsN⟩) ^ 3 = 1 := by
    rw [hτ]
    exact hpow3 (-i)
  obtain ⟨k₂, hk₂⟩ := (IsPGroup.iff_orderOf.1 (hs.S_pgroup hII)) ⟨s, hsS⟩
  have hk₂' : orderOf (⟨s, hsN⟩ : ↥(S ⊔ zpowers h)) = 2 ^ k₂ := by
    rw [← hk₂]
    exact (Subgroup.orderOf_mk s hsN).trans (Subgroup.orderOf_mk s hsS).symm
  have hdvd2 : orderOf (f ⟨s, hsN⟩) ∣ 2 ^ k₂ := by
    rw [← hk₂']
    exact orderOf_map_dvd f _
  have hdvd3 : orderOf (f ⟨s, hsN⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one hτ3
  have hcop : Nat.Coprime (2 ^ k₂) 3 := Nat.Coprime.pow_left _ (by norm_num)
  have hord1 : orderOf (f ⟨s, hsN⟩) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd2 hcop) hdvd3
  have hτ1 : f ⟨s, hsN⟩ = 1 := orderOf_eq_one_iff.1 hord1
  have hσi : (f ⟨h, hhN⟩) ^ i = 1 := by
    rw [hτ1, one_mul] at h2
    exact h2
  have h3i : ((3 : ℕ) : ℤ) ∣ i := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := f ⟨h, hhN⟩) (i := i)).2 hσi
    rwa [hσ, hord3] at this
  obtain ⟨q, hqq⟩ := h3i
  have hsA : s ∈ Aof S K₁ W₂ h := by
    rw [← hs.cent_eq hII hq hrec]
    refine Subgroup.mem_inf.2 ⟨hsS, Subgroup.mem_centralizer_iff.2 (fun a ha => ?_)⟩
    have h5 := congrArg (fun F : MulAut ↥(Aof S K₁ W₂ h) => ((F ⟨a, ha⟩ : ↥(Aof S K₁ W₂ h)) : G)) hτ1
    have h6 : s * a * s⁻¹ = a := h5
    calc a * s = (s * a * s⁻¹) * s := by rw [h6]
      _ = s * a := by group
  have hgq : g = s * (h ^ 3) ^ q := by
    rw [hgi, hqq]
    have : h ^ ((3 : ℕ) * q : ℤ) = (h ^ 3) ^ q := by
      rw [zpow_mul]
      simp
    push_cast at this ⊢
    rw [this]
  rw [hgq]
  exact mul_mem (Subgroup.mem_sup_left hsA)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) q))

theorem conjHom_ker_iff (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1))
    {Sg : Subgroup G} (hSg : Sig810 S K₁ W₂ h t Sg)
    (hSgN : Sg ≤ normalizer ((Aof S K₁ W₂ h : Subgroup G) : Set G)) (x : ↥Sg) :
    Basic.conjHom (Aof S K₁ W₂ h) Sg hSgN x = 1 ↔ (x : G) ∈ zpowers (h ^ 3) := by
  have hAW := hs.A_le_W hII hq hrec (le_refl _) hk
  have hcen : ∀ a ∈ Aof S K₁ W₂ h, ∀ j : ℤ, (h ^ 3) ^ j * a = a * (h ^ 3) ^ j := by
    intro a ha j
    have h1 : Commute (h ^ 3) a := hs.h_cube a (hAW ha)
    exact (h1.zpow_left j).eq
  constructor
  · intro hx
    have hc : ∀ a ∈ Aof S K₁ W₂ h, (x : G) * a = a * (x : G) := by
      intro a ha
      have h5 := congrArg (fun F : MulAut ↥(Aof S K₁ W₂ h) => ((F ⟨a, ha⟩ : ↥(Aof S K₁ W₂ h)) : G)) hx
      have h6 : (x : G) * a * (x : G)⁻¹ = a := h5
      calc (x : G) * a = ((x : G) * a * (x : G)⁻¹) * (x : G) := by group
        _ = a * (x : G) := by rw [h6]
    have hxN : (x : G) ∈ S ⊔ zpowers h := by
      have := hSg.2.2.1
      exact this ▸ Subgroup.mem_sup_right x.2
    have hxA := hs.cent_N_A hII hq hrec hk hxN hc
    obtain ⟨c, hc', a', ha', hca⟩ := Basic.mem_sup_of_le_normalizer' (A := zpowers (h ^ 3))
      (B := Aof S K₁ W₂ h)
      (Basic.le_normalizer_of_commute' (fun a ha b hb => by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (hcen a ha j).symm))
      (sup_comm (Aof S K₁ W₂ h) (zpowers (h ^ 3)) ▸ hxA)
    have hhSg : h ∈ Sg := hSg.1 (Subgroup.mem_sup_left (Subgroup.mem_zpowers h))
    have hcSg : c ∈ Sg := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
      exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ hhSg 3) j
    have ha'Sg : a' ∈ Sg := by
      have : a' = c⁻¹ * (x : G) := by rw [hca]; group
      rw [this]
      exact mul_mem (inv_mem hcSg) x.2
    have ha'1 : a' = 1 := by
      have : a' ∈ Aof S K₁ W₂ h ⊓ Sg := Subgroup.mem_inf.2 ⟨ha', ha'Sg⟩
      rwa [hSg.2.1, Subgroup.mem_bot] at this
    rw [ha'1, mul_one] at hca
    rw [hca]
    exact hc'
  · intro hx
    ext a
    show (x : G) * (a : G) * (x : G)⁻¹ = a
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← hj]
    calc (h ^ 3) ^ j * (a : G) * ((h ^ 3) ^ j)⁻¹ = ((a : G) * (h ^ 3) ^ j) * ((h ^ 3) ^ j)⁻¹ := by
          rw [hcen a a.2 j]
      _ = (a : G) := by group

theorem unique_Sigma (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1))
    {Sg Sg' : Subgroup G} (h1 : Sig810 S K₁ W₂ h t Sg) (h2 : Sig810 S K₁ W₂ h t Sg') :
    ∃ α : MulAut ↥(Aof S K₁ W₂ h),
      (∀ x ∈ Sg, ∃ x' ∈ Sg', ∀ a b : ↥(Aof S K₁ W₂ h), (b : G) = x * a * x⁻¹ →
        ((α b : ↥(Aof S K₁ W₂ h)) : G) = x' * ((α a : ↥(Aof S K₁ W₂ h)) : G) * x'⁻¹) ∧
      (∀ x' ∈ Sg', ∃ x ∈ Sg, ∀ a b : ↥(Aof S K₁ W₂ h), (b : G) = x * a * x⁻¹ →
        ((α b : ↥(Aof S K₁ W₂ h)) : G) = x' * ((α a : ↥(Aof S K₁ W₂ h)) : G) * x'⁻¹) := by
  have hNA := hs.N_le_normalizer_A hII hq hrec hk
  have hSgN : Sg ≤ normalizer ((Aof S K₁ W₂ h : Subgroup G) : Set G) :=
    (le_sup_right.trans h1.2.2.1.symm.le).trans hNA
  have hSgN' : Sg' ≤ normalizer ((Aof S K₁ W₂ h : Subgroup G) : Set G) :=
    (le_sup_right.trans h2.2.2.1.symm.le).trans hNA
  exact Basic.exists_alpha (A := Aof S K₁ W₂ h) (Sg := Sg) (Sg' := Sg') (h := h)
    (hs.A_comm hII hq hrec) (hs.A_equiv_Z4Z4 hII hq hrec hk) hSgN hSgN'
    (hs.h_mem_normalizer_A hII hq hrec hk) (hs.orderOf_conjAut_h hII hq hrec hk)
    (fun x => hs.conjHom_ker_iff hII hq hrec hk h1 hSgN x)
    (fun x => hs.conjHom_ker_iff hII hq hrec hk h2 hSgN' x) h1.2.2.2 h2.2.2.2

end Setup8

theorem lemma_8_10 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity) :
    Lemma8_10 := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS7 hC E₁ E₂ hE
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  obtain ⟨Sg, hSg⟩ := hs.exists_Sigma hII hq hrec hP8 hS7 hE hC
  refine ⟨Sg, hSg.1, hSg.2.1, hSg.2.2.1, hSg.2.2.2, ?_⟩
  intro Sg' h1' h2' h3' h4'
  exact hs.unique_Sigma hII hq hrec hk hSg ⟨h1', h2', h3', h4'⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
