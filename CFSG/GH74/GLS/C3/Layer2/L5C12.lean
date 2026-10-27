module

public import CFSG.GH74.GLS.C3.Layer2.L5C11
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5054

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem n24L_mul_chk : mulClosedChkP n24L = true :=
  Certificates.certificate5054.1

theorem n24L_inv_chk : invClosedChkP n24L = true :=
  Certificates.certificate5054.2.1

theorem one_mem_n24L : (1 : Perm (Fin 16)) ∈ n24L :=
  Certificates.certificate5054.2.2.1

theorem n24L_nodup : n24L.Nodup :=
  Certificates.certificate5054.2.2.2.1

theorem n24L_length : n24L.length = 24 :=
  Certificates.certificate5054.2.2.2.2.1

theorem yHat_mem_n24L : yHat ∈ n24L :=
  Certificates.certificate5054.2.2.2.2.2.1

theorem actF_T5_cases_chk :
    allT5.all (fun t => decide ((∀ i : Fin 16, actF t i = i) ∨
    (∀ i : Fin 16, actF t i = yHat i))) = true :=
  Certificates.certificate5054.2.2.2.2.2.2

theorem actF_T5_cases {t : Amb 5} (ht : t ∈ T5) :
    (∀ i : Fin 16, actF t i = i) ∨ (∀ i : Fin 16, actF t i = yHat i) := by
  have h := actF_T5_cases_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h t (mem_allT5.2 ht)

@[expose] def N24subG : Subgroup (Perm (Fin 16)) :=
  lsubP n24L one_mem_n24L n24L_mul_chk n24L_inv_chk

theorem card_N24subG : Nat.card N24subG = 24 := by
  rw [natCard_eq_length N24subG n24L n24L_nodup (fun p => Iff.rfl)]
  exact n24L_length

section Nprime

variable {h : IsAConfig 5 x K T Q S a} (c : Coord5 h)

abbrev Coord5.N :
    Subgroup G := normalizer ((c.lift Rm : Subgroup G) : Set G)

@[expose] noncomputable def Coord5.Nprime :
    Subgroup G := (N24subG.comap c.rhoG).map c.N.subtype

variable {c}

theorem Coord5.mem_Nprime
    {n : G} :
    n ∈ c.Nprime ↔ ∃ hn : n ∈ c.N, c.rhoG ⟨n, hn⟩ ∈ n24L := by
  unfold Coord5.Nprime
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨hn, hr⟩
    exact ⟨⟨n, hn⟩, hr, rfl⟩

theorem Coord5.Nprime_le_N :
    c.Nprime ≤ c.N := fun _ hn => (Coord5.mem_Nprime.1 hn).1

theorem Coord5.rhoG_R_eq_one
    {r : G} (hr : r ∈ c.lift Rm) : c.rhoG ⟨r, Coord5.R_le_N c hr⟩ = 1 :=
  Equiv.ext fun i => Coord5.rhoG_R c hr i

theorem Coord5.R_le_Nprime :
    c.lift Rm ≤ c.Nprime := fun r hr =>
  Coord5.mem_Nprime.2 ⟨Coord5.R_le_N c hr, by rw [Coord5.rhoG_R_eq_one hr]; exact one_mem_n24L⟩

theorem Coord5.T_le_Nprime :
    T ≤ c.Nprime := fun t ht =>
  Coord5.mem_Nprime.2 ⟨Coord5.T_le_N c ht, by
    rcases actF_T5_cases (c.rco_mem_T5 ht) with h1 | h1
    · have : c.rhoG ⟨t, Coord5.T_le_N c ht⟩ = 1 :=
        Equiv.ext fun i => by rw [Coord5.rhoG_T c ht, h1]; rfl
      rw [this]; exact one_mem_n24L
    · have : c.rhoG ⟨t, Coord5.T_le_N c ht⟩ = yHat :=
        Equiv.ext fun i => by rw [Coord5.rhoG_T c ht, h1]
      rw [this]; exact yHat_mem_n24L⟩

end Nprime

section S1

variable {h : IsAConfig 5 x K T Q S a} (c : Coord5 h)

@[expose] noncomputable def Coord5.rhoNp :
    ↥c.Nprime →* Perm (Fin 16) :=
  c.rhoG.comp (Subgroup.inclusion Coord5.Nprime_le_N)

variable {c}

theorem Coord5.rhoNp_apply
    (n : ↥c.Nprime) :
    c.rhoNp n = c.rhoG ⟨n.1, Coord5.Nprime_le_N n.2⟩ := rfl

theorem Coord5.rhoNp_ker :
    c.rhoNp.ker = (c.lift Rm).subgroupOf c.Nprime := by
  ext ⟨n, hn⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    have hnN : n ∈ c.N := Coord5.Nprime_le_N hn
    apply Coord5.Rg_cent (c := c)
    intro r hr
    have hr' := Coord5.exists_liftEl c hr
    have hj : c.rhoG ⟨n, hnN⟩ (idx16 (c.rco r)) = idx16 (c.rco r) := by
      have := congrArg (fun p : Perm (Fin 16) => p (idx16 (c.rco r))) h1
      simpa [Coord5.rhoNp_apply] using this
    have hspec : r = n * r * n⁻¹ := by
      have := Coord5.rhoG_spec c ⟨n, hnN⟩ (idx16 (c.rco r))
      rw [hj, ← hr'] at this
      exact this
    calc n * r = (n * r * n⁻¹) * n := by group
      _ = r * n := by rw [← hspec]
  · intro h1
    show c.rhoG ⟨n, Coord5.Nprime_le_N hn⟩ = 1
    exact Coord5.rhoG_R_eq_one h1

theorem Coord5.card_Nprime
    (hex : ∀ A ∈ n24L, ∃ n : ↥c.N, c.rhoG n = A) :
    Nat.card c.Nprime = 384 := by
  have hrange : c.rhoNp.range = N24subG := by
    ext A
    constructor
    · rintro ⟨n, rfl⟩
      exact (Coord5.mem_Nprime.1 n.2).2
    · intro hA
      obtain ⟨m, hm⟩ := hex A hA
      have hm' : c.rhoG ⟨m.1, m.2⟩ ∈ n24L := by
        have : (⟨m.1, m.2⟩ : ↥c.N) = m := rfl
        rw [this, hm]; exact hA
      exact ⟨⟨m.1, Coord5.mem_Nprime.2 ⟨m.2, hm'⟩⟩, by rw [Coord5.rhoNp_apply]; exact hm⟩
  have h1 := Subgroup.card_ker_mul_card_range c.rhoNp
  rw [Coord5.rhoNp_ker, hrange, card_N24subG] at h1
  have h2 : Nat.card ((c.lift Rm).subgroupOf c.Nprime) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Coord5.R_le_Nprime).toEquiv]
    exact Coord5.card_lift_Rm (c := c)
  rw [h2] at h1
  omega

theorem factorization_384 : (384 : ℕ).factorization 2 = 7 := by
  have h : (384 : ℕ) = 2 ^ 7 * 3 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]

theorem Coord5.exists_S1
    (hT : IsPGroup 2 ↥T) (hex : ∀ A ∈ n24L, ∃ n : ↥c.N, c.rhoG n = A) :
    ∃ S₁ : Subgroup G, IsSylow2In S₁ c.Nprime ∧ T ≤ S₁ ∧ Nat.card S₁ = 128 := by
  obtain ⟨S₁, hS₁, hTS₁⟩ := exists_sylow2_ge hT (Coord5.T_le_Nprime (c := c))
  refine ⟨S₁, hS₁, hTS₁, ?_⟩
  have hcard := Sylow.card_eq_multiplicity (sylow2ToSylow hS₁)
  simp only [coe_sylow2ToSylow] at hcard
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₁.1).toEquiv, Coord5.card_Nprime hex,
    factorization_384] at hcard
  rw [hcard]
  norm_num

end S1

structure C1Facts2 : Prop where
  d8_unique : ∀ D : Subgroup (Perm (Fin 16)), D ≤ N24subG → Nat.card D = 8 → yHat ∈ D →
    ∀ d, d ∈ D ↔ d ∈ d8L
  g72_dvd : ∀ N : Subgroup (Perm (Fin 16)),
    (∀ m ∈ N, IsLinG m ∧ ∀ V ∈ fam0G, V.image m ∈ fam0G) → Nat.card N ∣ 72
  cHat_gen : ∀ N : Subgroup (Perm (Fin 16)),
    (∀ m ∈ N, IsLinG m ∧ PplG.image m = PplG ∧ ∀ V ∈ fam0G, V.image m ∈ fam0G) →
      (∀ A ∈ n24L, A ∈ N) → (∃ m ∈ N, m ∉ n24L) → cHat ∈ N
  cHat_v4 : ∀ v ∈ v4L, cHat * v * cHat⁻¹ ∈ v4L
  v4_normal : ∀ m ∈ n24L, ∀ v ∈ v4L, m * v * m⁻¹ ∈ v4L
  v4_sub_d8 : ∀ v ∈ v4L, v ∈ d8L
  d8_sub_n24 : ∀ d ∈ d8L, d ∈ n24L

section S1data

variable {h : IsAConfig 5 x K T Q S a} (c : Coord5 h)

open Classical in
@[expose] noncomputable def Coord5.rhoT
    (n : G) : Perm (Fin 16) :=
  if hn : n ∈ c.N then c.rhoG ⟨n, hn⟩ else 1

variable {c}

theorem Coord5.rhoT_of_mem
    {n : G} (hn : n ∈ c.N) : c.rhoT n = c.rhoG ⟨n, hn⟩ := by
  simp [Coord5.rhoT, hn]

theorem Coord5.rhoG_ker :
    c.rhoG.ker = (c.lift Rm).subgroupOf c.N := by
  ext ⟨n, hn⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    apply Coord5.Rg_cent (c := c)
    intro r hr
    have hr' := Coord5.exists_liftEl c hr
    have hj : c.rhoG ⟨n, hn⟩ (idx16 (c.rco r)) = idx16 (c.rco r) := by
      have := congrArg (fun p : Perm (Fin 16) => p (idx16 (c.rco r))) h1
      simpa using this
    have hspec : r = n * r * n⁻¹ := by
      have := Coord5.rhoG_spec c ⟨n, hn⟩ (idx16 (c.rco r))
      rw [hj, ← hr'] at this
      exact this
    calc n * r = (n * r * n⁻¹) * n := by group
      _ = r * n := by rw [← hspec]
  · intro h1
    exact Coord5.rhoG_R_eq_one h1

structure Coord5.S1Data
    (c : Coord5 h) (S₁ : Subgroup G) : Prop where
  card : Nat.card S₁ = 128
  hT : T ≤ S₁
  hN : S₁ ≤ c.N
  ker : ∀ s ∈ S₁, c.rhoT s = 1 → s ∈ c.lift Rm
  range : ∀ s ∈ S₁, c.rhoT s ∈ d8L
  surj : ∀ d ∈ d8L, ∃ s ∈ S₁, c.rhoT s = d

theorem Coord5.exists_S1Data
    (hF : C1Facts2) (hT : IsPGroup 2 ↥T)
    (hex : ∀ A ∈ n24L, ∃ n : ↥c.N, c.rhoG n = A) : ∃ S₁ : Subgroup G, c.S1Data S₁ := by
  obtain ⟨S₁, hSyl, hTS, hcard⟩ := Coord5.exists_S1 hT hex
  have hRS : c.lift Rm ≤ S₁ := (Coord5.Rg_le_T (c := c)).trans hTS
  have hSN' : S₁ ≤ c.Nprime := hSyl.1
  have hSN : S₁ ≤ c.N := hSN'.trans Coord5.Nprime_le_N
  let ρ₁ : ↥S₁ →* Perm (Fin 16) := c.rhoNp.comp (Subgroup.inclusion hSN')
  have hρ₁ : ∀ s : ↥S₁, ρ₁ s = c.rhoT (s : G) := fun s => by
    rw [Coord5.rhoT_of_mem (hSN s.2)]
    rfl
  have hker : ρ₁.ker = (c.lift Rm).subgroupOf S₁ := by
    ext ⟨s, hs⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : c.rhoNp ⟨s, hSN' hs⟩ = 1 ↔ s ∈ c.lift Rm := by
      have := SetLike.ext_iff.1 (Coord5.rhoNp_ker (c := c)) ⟨s, hSN' hs⟩
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf] at this
      exact this
    exact h1
  have hR16 : Nat.card ((c.lift Rm).subgroupOf S₁) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS).toEquiv]
    exact Coord5.card_lift_Rm (c := c)
  have hcardD : Nat.card ρ₁.range = 8 := by
    have := Subgroup.card_ker_mul_card_range ρ₁
    rw [hker, hR16] at this
    have h128 : Nat.card ↥S₁ = 128 := hcard
    omega
  have hDle : ρ₁.range ≤ N24subG := by
    rintro _ ⟨s, rfl⟩
    show ρ₁ s ∈ n24L
    exact (Coord5.mem_Nprime.1 (hSN' s.2)).2
  obtain ⟨yG, hyT, hy⟩ := c.exists_T_rco yy5_mem
  have hyN : yG ∈ c.N := Coord5.T_le_N c hyT
  have hyρ : c.rhoG ⟨yG, hyN⟩ = yHat := Equiv.ext fun i => by
    rw [Coord5.rhoG_T c hyT, hy, actF_yy5]
  have hyD : yHat ∈ ρ₁.range := ⟨⟨yG, hTS hyT⟩, by rw [hρ₁, Coord5.rhoT_of_mem hyN, hyρ]⟩
  have hD := hF.d8_unique ρ₁.range hDle hcardD hyD
  refine ⟨S₁, hcard, hTS, hSN, ?_, ?_, ?_⟩
  · intro s hs h1
    have : ρ₁ ⟨s, hs⟩ = 1 := by rw [hρ₁]; exact h1
    have h2 : (⟨s, hs⟩ : ↥S₁) ∈ ρ₁.ker := this
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  · intro s hs
    have : c.rhoT s ∈ ρ₁.range := ⟨⟨s, hs⟩, hρ₁ ⟨s, hs⟩⟩
    exact (hD _).1 this
  · intro d hd
    obtain ⟨⟨s, hs⟩, hsd⟩ := (hD d).2 hd
    exact ⟨s, hs, by rw [← hρ₁ ⟨s, hs⟩]; exact hsd⟩

end S1data

end CFSG.GH74.GLS.C3.Layer2.L5
