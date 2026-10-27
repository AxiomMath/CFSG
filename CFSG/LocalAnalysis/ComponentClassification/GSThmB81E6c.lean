module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81E6b
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Z
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace E6

variable {G : Type} [Group G]

theorem mem_zpowers_of_mul_self {w y : G} (hw : w * w = 1) (hy : y ∈ zpowers w) :
    y = 1 ∨ y = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : w = 1
  · subst h1
    rw [zpowers_one_eq_bot, mem_bot] at hy
    exact Or.inl hy
  · exact mem_zpowers_two (orderOf_eq_prime (by rw [sq, hw]) h1) hy

theorem inf_zpowers_eq_bot {A : Subgroup G} {w : G} (hw : w * w = 1) (hwA : w ∉ A) :
    A ⊓ zpowers w = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rcases mem_zpowers_of_mul_self hw (mem_inf.mp hy).2 with rfl | rfl
  · exact one_mem _
  · exact absurd (mem_inf.mp hy).1 hwA

theorem comm_zpowers {A : Subgroup G} {w : G} (hw : w * w = 1)
    (hAw : ∀ x ∈ A, x * w = w * x) : ∀ x ∈ A, ∀ y ∈ zpowers w, x * y = y * x := by
  intro x hx y hy
  rcases mem_zpowers_of_mul_self hw hy with rfl | rfl
  · rw [mul_one, one_mul]
  · exact hAw x hx

theorem mul_self_of_mem_sup_zpowers {A : Subgroup G} {w : G} (hA : ∀ x ∈ A, x * x = 1)
    (hw : w * w = 1) (hAw : ∀ x ∈ A, x * w = w * x) : ∀ x ∈ A ⊔ zpowers w, x * x = 1 := by
  have hwN : zpowers w ≤ normalizer (A : Set G) :=
    Seven.le_normalizer_of_commute (comm_zpowers hw hAw)
  intro x hx
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left A (zpowers w) hwN] at hx
  obtain ⟨a, ha, y, hy, rfl⟩ := hx
  beta_reduce
  rcases mem_zpowers_of_mul_self hw hy with h1 | h1 <;> rw [h1]
  · rw [mul_one]
    exact hA a ha
  · calc a * w * (a * w) = a * (w * a) * w := by group
      _ = a * (a * w) * w := by rw [hAw a ha]
      _ = (a * a) * (w * w) := by group
      _ = 1 := by rw [hA a ha, hw, one_mul]

theorem card_sup_zpowers {A : Subgroup G} {w : G} (hw : w * w = 1) (hwA : w ∉ A)
    (hAw : ∀ x ∈ A, x * w = w * x) : Nat.card ↥(A ⊔ zpowers w) = Nat.card A * 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw1 : w ≠ 1 := fun h1 => hwA (h1 ▸ one_mem A)
  rw [Seven.card_sup_of_commute (comm_zpowers hw hAw) (inf_zpowers_eq_bot hw hwA),
    Nat.card_zpowers, orderOf_eq_prime (by rw [sq, hw]) hw1]

theorem comm_of_mem_sup_zpowers {A : Subgroup G} {w η : G} (hAη : ∀ x ∈ A, x * η = η * x)
    (hwη : w * η = η * w) : ∀ x ∈ A ⊔ zpowers w, x * η = η * x := by
  have hle : A ⊔ zpowers w ≤ centralizer ({η} : Set G) := by
    refine sup_le (fun x hx => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_iff]
      rintro _ rfl
      exact (hAη x hx).symm
    · rw [mem_centralizer_iff]
      rintro _ rfl
      exact hwη.symm
  intro x hx
  exact (mem_centralizer_iff.mp (hle hx) η rfl).symm

theorem comm_of_mul_self {A : Subgroup G} (hA : ∀ x ∈ A, x * x = 1) :
    ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  intro x hx y hy
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hA x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hA y hy)
  calc x * y = x⁻¹ * y⁻¹ := by rw [hxi, hyi]
    _ = (y * x)⁻¹ := by group
    _ = y * x := inv_eq_of_mul_eq_one_right (hA _ (mul_mem hy hx))

end E6

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

section Rank

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
include hv I F

omit F in
theorem card_elem_le_U {E : Subgroup H} (hEU : E ≤ h.U81 v) (hE : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  push Not at hlt
  have hES : ¬ E ≤ h.S := fun hES => absurd (d.card_elem_le I.rk hES hE) (by omega)
  obtain ⟨w, hwE, hwS⟩ := Set.not_subset.mp hES
  have hcomm := E6.comm_of_mul_self hE
  have hw2 : w * w = 1 := hE w hwE
  set E₀ := E ⊓ h.S with hE₀
  have hEeq : E ≤ E₀ ⊔ zpowers w := by
    intro e he
    by_cases heS : e ∈ h.S
    · exact mem_sup_left (mem_inf.mpr ⟨he, heS⟩)
    · have h1 : w⁻¹ * e ∈ h.S := by
        rcases mem_U_cases hv (hEU he) with h2 | ⟨s₁, hs₁, rfl⟩
        · exact absurd h2 heS
        rcases mem_U_cases hv (hEU hwE) with h2 | ⟨s₂, hs₂, rfl⟩
        · exact absurd h2 hwS
        rw [show (s₂ * v)⁻¹ * (s₁ * v) = v⁻¹ * (s₂⁻¹ * s₁) * v⁻¹⁻¹ by group]
        exact (mem_normalizer_iff.mp (inv_mem hv.mem_N) _).mp (mul_mem (inv_mem hs₂) hs₁)
      have he' : e = w * (w⁻¹ * e) := by group
      rw [he']
      exact mul_mem (mem_sup_right (mem_zpowers w))
        (mem_sup_left (mem_inf.mpr ⟨mul_mem (inv_mem hwE) he, h1⟩))
  have hE₀w : ∀ x ∈ E₀, x * w = w * x := fun x hx => hcomm x (mem_inf.mp hx).1 w hwE
  have hcardE : Nat.card E ≤ Nat.card E₀ * 2 := by
    rw [← E6.card_sup_zpowers hw2 (fun h1 => hwS (mem_inf.mp h1).2) hE₀w]
    exact card_le_of_le hEeq
  have hE₀2 : IsPGroup 2 E₀ := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, sq, OneMemClass.coe_one]
    exact hE x (mem_inf.mp x.2).1)⟩
  obtain ⟨k, hk⟩ := hE₀2.exists_card_eq
  have hk5 : 4 ≤ k := by
    by_contra hk4
    push Not at hk4
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 4) (G := ↥E₀)
    (by rw [hk]; exact pow_dvd_pow 2 hk5)
  set F' : Subgroup H := F₀.map E₀.subtype with hF'
  have hF'card : Nat.card F' = 16 := by
    rw [hF', card_map_of_injective E₀.subtype_injective, hF₀]
    norm_num
  have hF'E₀ : F' ≤ E₀ := map_subtype_le _
  have hF'w : ∀ x ∈ F', x * w = w * x := fun x hx => hE₀w x (hF'E₀ hx)
  have hE'card : Nat.card ↥(F' ⊔ zpowers w) = 32 := by
    rw [E6.card_sup_zpowers hw2 (fun h1 => hwS (mem_inf.mp (hF'E₀ h1)).2) hF'w, hF'card]
  have hE'E : F' ⊔ zpowers w ≤ E := sup_le (hF'E₀.trans inf_le_left) (zpowers_le.mpr hwE)
  have hE'S := le_S_of_le_U hv I.rk (hE'E.trans hEU) (fun e he => hE e (hE'E he)) hE'card
  exact hwS (hE'S (mem_sup_right (mem_zpowers w)))

theorem card_elem_le_H {E : Subgroup H} (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hT'⟩ := isSylow_U hv I.rk I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, sq, OneMemClass.coe_one]
    exact hE x x.2)⟩
  obtain ⟨P, hP⟩ := hE2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P T'
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  have hE'U : E' ≤ h.U81 v := by
    rw [← hT', ← hg]
    rintro _ ⟨e, he, rfl⟩
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    exact smul_mem_pointwise_smul _ _ _ (hP he)
  have h1 := card_elem_le_U hv I hE'U (by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, hE e he, map_one])
  rwa [hE', card_map_of_injective (MulAut.conj g).injective] at h1

end Rank

theorem exists_gen_mod_innA (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hJo : CFSec8JOrder) (hOut : CF81E6Out) (T : Subgroup H) (hTW : T ≤ h.W) :
    ∃ t₀ : ↥h.W, (t₀ : H) ∈ T ∧ ∀ t (ht : t ∈ T), ∃ k : ℤ,
      (H₁.psiW t₀ ^ k)⁻¹ * H₁.psiW ⟨t, hTW ht⟩ ∈
        Cat8.innA (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA := by
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Hyp52.Sec8Case.exists_params h.toHyp52 H₁.kloc.case8
  obtain ⟨hNn, φ, hφ⟩ := hOut _ p f hp hp2 hf hK H₁.kloc.rhoA
    (H₁.kloc.rhoA_admQ hCF1 hCF2 hJo hp hp2 hf hJ)
  set N := Cat8.innA (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA with hN
  set π := QuotientGroup.mk' N with hπ
  have hcyc : IsCyclic (MulAut (h.K ⧸ pPrimeCore 2 h.K) ⧸ N) := by
    refine ⟨⟨π φ, fun x => ?_⟩⟩
    obtain ⟨ψ, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨k, hk⟩ := hφ ψ
    refine ⟨k, ?_⟩
    show π φ ^ k = π ψ
    rw [← map_zpow]
    exact (QuotientGroup.eq).mpr hk
  set Sub := (T.subgroupOf h.W).map (π.comp H₁.psiW) with hSub
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Sub)
  obtain ⟨t₀, ht₀, hgt⟩ := mem_map.mp g.2
  refine ⟨t₀, ht₀, fun t ht => ?_⟩
  have htS : (π.comp H₁.psiW) ⟨t, hTW ht⟩ ∈ Sub :=
    mem_map_of_mem _ (show (⟨t, hTW ht⟩ : ↥h.W) ∈ T.subgroupOf h.W from ht)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨_, htS⟩)
  refine ⟨k, ?_⟩
  have h1 := congrArg Subtype.val hk
  rw [SubgroupClass.coe_zpow, ← hgt, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_zpow]
    at h1
  exact (QuotientGroup.eq).mp h1

theorem psiW_B {y : H} (hy : y ∈ h.B) : H₁.psiW ⟨y, le_normalizer hy⟩ = 1 := by
  have hV := H₁.kloc.V_eq_K
  have h1 : y ∈ coreActionKernel h.K := hV ▸ H₁.B_sylow_kernel.1 hy
  exact Eight.mem_ker_oddBarAction.mpr h1


end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
