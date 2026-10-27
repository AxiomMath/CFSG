module

public import CFSG.GH74.GLS.C3.Layer1.BkW5Rho
public import CFSG.GH74.GLS.C3.Layer1.BkW5Odd
public import CFSG.GH74.GLS.C3.Layer2.L5C12

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.W5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
open scoped commutatorElement
open CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfigW 5 x K T Q S a}

namespace Coord

theorem R_sylow_centralizer
    (c : Coord h) : IsSylow2In (c.lift Rm) (centralizer ((c.lift Rm : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := aconfigW_five_R_sylow_centralizer h
  rw [R_eq_lift (c := c)] at h1
  exact isSylowOf_iff.1 h1

theorem card_cent_R (c : Coord h) :
    ∃ m : ℕ, Odd m ∧ Nat.card ↥(centralizer ((c.lift Rm : Subgroup G) : Set G)) = 16 * m := by
  have hS := R_sylow_centralizer c
  set C := centralizer ((c.lift Rm : Subgroup G) : Set G) with hC
  have h1 := Subgroup.card_mul_index ((c.lift Rm).subgroupOf C)
  have h2 : Nat.card ((c.lift Rm).subgroupOf C) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv]
    exact card_lift_Rm (c := c)
  rw [h2] at h1
  refine ⟨((c.lift Rm).subgroupOf C).index, ?_, h1.symm⟩
  have h3 : ¬ 2 ∣ ((c.lift Rm).subgroupOf C).index := hS.2.2
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h3)

theorem cent_R_le_N (c : Coord h) :
    centralizer ((c.lift Rm : Subgroup G) : Set G) ≤ c.N :=
  Subgroup.centralizer_le_normalizer _

theorem rhoG_eq_one_iff
    {c : Coord h} {n : G} (hn : n ∈ c.N) :
    c.rhoG ⟨n, hn⟩ = 1 ↔ n ∈ centralizer ((c.lift Rm : Subgroup G) : Set G) := by
  constructor
  · intro h1
    rw [mem_centralizer_iff]
    intro r hr
    have hr' := exists_liftEl c hr
    have hj : c.rhoG ⟨n, hn⟩ (idx16 (c.rco r)) = idx16 (c.rco r) := by
      have := congrArg (fun p : Perm (Fin 16) => p (idx16 (c.rco r))) h1
      simpa using this
    have hspec : r = n * r * n⁻¹ := by
      have := rhoG_spec c ⟨n, hn⟩ (idx16 (c.rco r))
      rw [hj, ← hr'] at this
      exact this
    calc r * n = (n * r * n⁻¹) * n := by rw [← hspec]
      _ = n * r := by group
  · intro h1
    refine Equiv.ext fun i => ?_
    apply liftEl_inj c
    rw [rhoG_spec c ⟨n, hn⟩ i]
    have := mem_centralizer_iff.1 h1 (c.liftEl i) (c.liftEl_mem i)
    rw [Equiv.Perm.one_apply, ← this]
    group

theorem rhoG_ker
    {c : Coord h} :
    c.rhoG.ker = (centralizer ((c.lift Rm : Subgroup G) : Set G)).subgroupOf c.N := by
  ext ⟨n, hn⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact rhoG_eq_one_iff hn

section Nprime

variable (c : Coord h)

@[expose] noncomputable def Nprime :
    Subgroup G :=
  (N24subG.comap c.rhoG).map c.N.subtype

variable {c}

theorem mem_Nprime
    {n : G} :
    n ∈ c.Nprime ↔ ∃ hn : n ∈ c.N, c.rhoG ⟨n, hn⟩ ∈ n24L := by
  unfold Nprime
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨hn, hr⟩
    exact ⟨⟨n, hn⟩, hr, rfl⟩

theorem Nprime_le_N :
    c.Nprime ≤ c.N := fun _ hn => (mem_Nprime.1 hn).1

theorem rhoG_R_eq_one
    {r : G} (hr : r ∈ c.lift Rm) : c.rhoG ⟨r, R_le_N c hr⟩ = 1 :=
  Equiv.ext fun i => rhoG_R c hr i

theorem cent_R_le_Nprime :
    centralizer ((c.lift Rm : Subgroup G) : Set G) ≤ c.Nprime := fun n hn =>
  mem_Nprime.2 ⟨cent_R_le_N c hn, by
    rw [(rhoG_eq_one_iff (cent_R_le_N c hn)).2 hn]
    exact one_mem_n24L⟩

theorem T_le_Nprime :
    T ≤ c.Nprime := fun t ht =>
  mem_Nprime.2 ⟨T_le_N c ht, by
    rcases actF_T5_cases (rco_mem_T5 c ht) with h1 | h1
    · have : c.rhoG ⟨t, T_le_N c ht⟩ = 1 :=
        Equiv.ext fun i => by rw [rhoG_T c ht, h1]; rfl
      rw [this]; exact one_mem_n24L
    · have : c.rhoG ⟨t, T_le_N c ht⟩ = yHat :=
        Equiv.ext fun i => by rw [rhoG_T c ht, h1]
      rw [this]; exact yHat_mem_n24L⟩

end Nprime

section S1

variable (c : Coord h)

@[expose] noncomputable def rhoNp :
    ↥c.Nprime →* Perm (Fin 16) :=
  c.rhoG.comp (Subgroup.inclusion Nprime_le_N)

variable {c}

theorem rhoNp_apply
    (n : ↥c.Nprime) :
    c.rhoNp n = c.rhoG ⟨n.1, Nprime_le_N n.2⟩ := rfl

theorem rhoNp_ker :
    c.rhoNp.ker = (centralizer ((c.lift Rm : Subgroup G) : Set G)).subgroupOf c.Nprime := by
  ext ⟨n, hn⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact rhoG_eq_one_iff (Nprime_le_N hn)

theorem factorization_384_mul {m : ℕ} (hm : Odd m) : (384 * m).factorization 2 = 7 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  have hm2 : ¬ 2 ∣ m := by
    have := Nat.odd_iff.1 hm
    omega
  rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply, factorization_384,
    Nat.factorization_eq_zero_of_not_dvd hm2]

theorem card_Nprime
    (hex : ∀ A ∈ n24L, ∃ n : ↥c.N, c.rhoG n = A) :
    ∃ m : ℕ, Odd m ∧ Nat.card c.Nprime = 384 * m := by
  obtain ⟨m, hm, hcardC⟩ := card_cent_R c
  have hrange : c.rhoNp.range = N24subG := by
    ext A
    constructor
    · rintro ⟨n, rfl⟩
      exact (mem_Nprime.1 n.2).2
    · intro hA
      obtain ⟨n', hn'⟩ := hex A hA
      have hm' : c.rhoG ⟨n'.1, n'.2⟩ ∈ n24L := by
        have : (⟨n'.1, n'.2⟩ : ↥c.N) = n' := rfl
        rw [this, hn']; exact hA
      exact ⟨⟨n'.1, mem_Nprime.2 ⟨n'.2, hm'⟩⟩, by rw [rhoNp_apply]; exact hn'⟩
  have h1 := Subgroup.card_ker_mul_card_range c.rhoNp
  rw [rhoNp_ker, hrange, card_N24subG] at h1
  have h2 : Nat.card ((centralizer ((c.lift Rm : Subgroup G) : Set G)).subgroupOf c.Nprime) =
      16 * m := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe cent_R_le_Nprime).toEquiv]
    exact hcardC
  rw [h2] at h1
  exact ⟨m, hm, by omega⟩

theorem exists_S1
    (hT : IsPGroup 2 ↥T)
    (hex : ∀ A ∈ n24L, ∃ n : ↥c.N, c.rhoG n = A) :
    ∃ S₁ : Subgroup G, IsSylow2In S₁ c.Nprime ∧ T ≤ S₁ ∧ Nat.card S₁ = 128 := by
  obtain ⟨S₁, hS₁, hTS₁⟩ := exists_sylow2_ge hT (T_le_Nprime (c := c))
  refine ⟨S₁, hS₁, hTS₁, ?_⟩
  obtain ⟨m, hm, hcard'⟩ := card_Nprime hex
  have hcard := Sylow.card_eq_multiplicity (sylow2ToSylow hS₁)
  simp only [coe_sylow2ToSylow] at hcard
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₁.1).toEquiv, hcard',
    factorization_384_mul hm] at hcard
  rw [hcard]
  norm_num

end S1

section S1data

open Classical in
@[expose] noncomputable def rhoT
    (c : Coord h) (n : G) : Perm (Fin 16) :=
  if hn : n ∈ c.N then c.rhoG ⟨n, hn⟩ else 1

theorem rhoT_of_mem
    {c : Coord h} {n : G} (hn : n ∈ c.N) : c.rhoT n = c.rhoG ⟨n, hn⟩ := by
  simp [rhoT, hn]

structure S1Data
    (c : Coord h) (S₁ : Subgroup G) : Prop where
  card : Nat.card S₁ = 128
  hT : T ≤ S₁
  hN : S₁ ≤ c.N
  ker : ∀ s ∈ S₁, c.rhoT s = 1 → s ∈ c.lift Rm
  range : ∀ s ∈ S₁, c.rhoT s ∈ d8L
  surj : ∀ d ∈ d8L, ∃ s ∈ S₁, c.rhoT s = d

theorem mem_R_of_rho_one
    (c : Coord h) {B : Subgroup G} (hB : IsPGroup 2 ↥B) (hRB : c.lift Rm ≤ B) {s : G} (hsB : s ∈ B)
    (hsN : s ∈ c.N) (hs : c.rhoG ⟨s, hsN⟩ = 1) : s ∈ c.lift Rm := by
  have hsC : s ∈ centralizer ((c.lift Rm : Subgroup G) : Set G) := (rhoG_eq_one_iff hsN).1 hs
  have hS := R_sylow_centralizer c
  have hle : c.lift Rm ⊔ zpowers s ≤ B := sup_le hRB (zpowers_le.2 hsB)
  have hle2 : c.lift Rm ⊔ zpowers s ≤ centralizer ((c.lift Rm : Subgroup G) : Set G) :=
    sup_le hS.1 (zpowers_le.2 hsC)
  have heq := sylow2_eq_of_le hS (hB.to_le hle) le_sup_left hle2
  have : s ∈ c.lift Rm ⊔ zpowers s := Subgroup.mem_sup_right (mem_zpowers s)
  rw [heq] at this
  exact this

theorem exists_S1Data
    {c : Coord h} (hF : C1Facts2) (hT : IsPGroup 2 ↥T)
    (hex : ∀ A ∈ n24L, ∃ n : ↥c.N, c.rhoG n = A) : ∃ S₁ : Subgroup G, c.S1Data S₁ := by
  obtain ⟨S₁, hSyl, hTS, hcard⟩ := exists_S1 hT hex
  have hRS : c.lift Rm ≤ S₁ := (Rg_le_T (c := c)).trans hTS
  have hSN' : S₁ ≤ c.Nprime := hSyl.1
  have hSN : S₁ ≤ c.N := hSN'.trans Nprime_le_N
  have hp : IsPGroup 2 ↥S₁ := hSyl.2.1
  let ρ₁ : ↥S₁ →* Perm (Fin 16) := c.rhoNp.comp (Subgroup.inclusion hSN')
  have hρ₁ : ∀ s : ↥S₁, ρ₁ s = c.rhoT (s : G) := fun s => by
    rw [rhoT_of_mem (hSN s.2)]
    rfl
  have hker : ρ₁.ker = (c.lift Rm).subgroupOf S₁ := by
    ext ⟨s, hs⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      refine mem_R_of_rho_one c hp hRS hs (hSN hs) ?_
      exact h1
    · intro h1
      exact rhoG_R_eq_one h1
  have hR16 : Nat.card ((c.lift Rm).subgroupOf S₁) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS).toEquiv]
    exact card_lift_Rm (c := c)
  have hcardD : Nat.card ρ₁.range = 8 := by
    have := Subgroup.card_ker_mul_card_range ρ₁
    rw [hker, hR16] at this
    have h128 : Nat.card ↥S₁ = 128 := hcard
    omega
  have hDle : ρ₁.range ≤ N24subG := by
    rintro _ ⟨s, rfl⟩
    show ρ₁ s ∈ n24L
    exact (mem_Nprime.1 (hSN' s.2)).2
  obtain ⟨yG, hyT, hy⟩ := exists_T_rco c yy5_mem
  have hyN : yG ∈ c.N := T_le_N c hyT
  have hyρ : c.rhoG ⟨yG, hyN⟩ = yHat := Equiv.ext fun i => by
    rw [rhoG_T c hyT, hy, actF_yy5]
  have hyD : yHat ∈ ρ₁.range := ⟨⟨yG, hTS hyT⟩, by rw [hρ₁, rhoT_of_mem hyN, hyρ]⟩
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

section S1G

theorem R_le_S1
    {c : Coord h} {S₁ : Subgroup G} (hS : c.S1Data S₁) : c.lift Rm ≤ S₁ :=
  (Rg_le_T (c := c)).trans hS.hT

theorem S1_sylow
    {c : Coord h}
    (hF : C1Facts2) (hRed : c.Red) {S₁ : Subgroup G} (hS : c.S1Data S₁) :
    IsSylow2In S₁ c.N := by
  have hp : IsPGroup 2 ↥S₁ := IsPGroup.of_card (n := 7) (by rw [hS.card]; norm_num)
  refine ⟨hS.hN, hp, ?_⟩
  have hdvd : Nat.card c.rhoG.range ∣ 72 := by
    apply hF.g72_dvd
    rintro m ⟨n, rfl⟩
    exact rho_stable hRed n
  obtain ⟨m, hm, hcardC⟩ := card_cent_R c
  have hker16 : Nat.card ((centralizer ((c.lift Rm : Subgroup G) : Set G)).subgroupOf c.N) =
      16 * m := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cent_R_le_N c)).toEquiv]
    exact hcardC
  have hker : 16 * m * Nat.card c.rhoG.range = Nat.card ↥c.N := by
    have h0 := Subgroup.card_ker_mul_card_range c.rhoG
    rw [rhoG_ker, hker16] at h0
    exact h0
  have h128 : Nat.card ((S₁.subgroupOf c.N)) = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.hN).toEquiv]
    exact hS.card
  have e1 := Subgroup.card_mul_index (S₁.subgroupOf c.N)
  rw [h128] at e1
  rintro ⟨k, hk⟩
  have hk' : (S₁.subgroupOf c.N).index = 2 * k := hk
  rw [hk'] at e1
  have h16 : 16 * k = m * Nat.card c.rhoG.range := by
    have h1 : 16 * (m * Nat.card c.rhoG.range) = 16 * (16 * k) := by
      calc 16 * (m * Nat.card c.rhoG.range) = 16 * m * Nat.card c.rhoG.range := by ring
        _ = Nat.card ↥c.N := hker
        _ = 128 * (2 * k) := e1.symm
        _ = 16 * (16 * k) := by ring
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h1).symm
  have hcop : Nat.Coprime 16 m := by
    have h2m : Nat.Coprime 2 m := Nat.coprime_two_left.2 hm
    have := Nat.Coprime.pow_left 4 h2m
    norm_num at this
    exact this
  have h16r : 16 ∣ Nat.card c.rhoG.range :=
    hcop.dvd_of_dvd_mul_left ⟨k, by rw [h16]⟩
  have : 16 ∣ 72 := h16r.trans hdvd
  omega

end S1G

end Coord

end CFSG.GH74.GLS.C3.Layer1.Bk.W5
