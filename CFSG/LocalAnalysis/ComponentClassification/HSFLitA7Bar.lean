module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7T
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitConjOrbit

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem cycleType_eq_of_sq {σ : Perm (Fin 7)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    σ.cycleType = Multiset.replicate (σ.support.card / 2) 2 := by
  have ho : orderOf σ = 2 := orderOf_eq_prime h2 h1
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hn
  have hs := Equiv.Perm.sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hs
  rw [hn, ← hs]
  congr 1
  omega

theorem index_centralizer_swap_swap :
    (centralizer {(swap (0 : Fin 7) 2 * swap 1 3)}).index = 105 := by
  have h4 : (swap (0 : Fin 7) 2 * swap 1 3).support.card = 4 := by decide
  have hc : Nat.card (centralizer {(swap (0 : Fin 7) 2 * swap 1 3)}) = 48 := by
    rw [Equiv.Perm.nat_card_centralizer, cycleType_eq_of_sq (by decide) (by decide), h4]
    simp [Nat.factorial]
  have h := (centralizer {(swap (0 : Fin 7) 2 * swap 1 3)}).card_mul_index
  rw [hc, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have : (7 : ℕ).factorial = 48 * 105 := by decide
  rw [this] at h
  omega

theorem eq_top_of_alternatingGroup_le {H : Subgroup (Perm (Fin 7))}
    (hA : alternatingGroup (Fin 7) ≤ H) {σ : Perm (Fin 7)} (hσ : σ ∈ H)
    (hodd : Equiv.Perm.sign σ = -1) : H = ⊤ := by
  have hdvd : H.index ∣ 2 := alternatingGroup.index_eq_two (α := Fin 7) ▸ index_dvd_of_le hA
  have hne : H.index ≠ 2 := by
    intro h2
    have := Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2
    have hσA : σ ∈ alternatingGroup (Fin 7) := this ▸ hσ
    rw [Equiv.Perm.mem_alternatingGroup, hodd] at hσA
    exact absurd hσA (by decide)
  have h1 : H.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd h hne
  exact index_eq_one.mp h1

theorem mem_normalizer_of_conj_mem {X : Type*} [Group X] [Finite X] {P : Subgroup X} {g : X}
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) : g ∈ normalizer (P : Set X) := by
  have hle : P.map (MulAut.conj g).toMonoidHom ≤ P := by
    rintro _ ⟨p, hp, rfl⟩
    exact hg p hp
  have heq : P.map (MulAut.conj g).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro h
  refine ⟨hg h, fun hh => ?_⟩
  rw [← heq] at hh
  obtain ⟨p, hp, hpe⟩ := hh
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hpe
  have : p = h := by
    have := congrArg (fun u => g⁻¹ * u * g) hpe
    simpa [mul_assoc] using this
  rw [← this]
  exact hp

theorem card_eq_two_pow_of_maximal {X : Type*} [Group X] [Finite X] {Y P : Subgroup X}
    (hPY : P ≤ Y) (hP : IsPGroup 2 P)
    (hmax : ∀ Q : Subgroup X, IsPGroup 2 Q → P ≤ Q → Q ≤ Y → Q ≤ P) :
    Nat.card P = 2 ^ (Nat.card Y).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf Y) := hP.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have hQX : IsPGroup 2 ((Q : Subgroup Y).map Y.subtype) := Q.isPGroup'.map _
  have hPQ : P ≤ (Q : Subgroup Y).map Y.subtype := fun p hp => ⟨⟨p, hPY hp⟩, hQ hp, rfl⟩
  have heq : (Q : Subgroup Y).map Y.subtype = P :=
    le_antisymm (hmax _ hQX hPQ (map_subtype_le _)) hPQ
  rw [← heq, card_map_of_injective (subtype_injective _), Sylow.card_eq_multiplicity]

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

variable (Λ : A7Sigma S.t S.L S.data)

theorem centralizer_le_normalizer_L :
    centralizer ({S.t} : Set X) ≤ normalizer (S.L : Set X) :=
  S.data.config.le_normalizer

@[expose] noncomputable def ΨC : centralizer ({S.t} : Set X) →* Perm (Fin 7) :=
  Λ.Ψ.comp (inclusion S.centralizer_le_normalizer_L)

@[expose] noncomputable def act (g : X) : Perm (Fin 7) :=
  open Classical in
  if h : g ∈ centralizer ({S.t} : Set X) then S.ΨC Λ ⟨g, h⟩ else 1

theorem act_of_mem {g : X} (hg : g ∈ centralizer ({S.t} : Set X)) :
    S.act Λ g = S.ΨC Λ ⟨g, hg⟩ := by
  simp [act, hg]

theorem act_mul {g h : X} (hg : g ∈ centralizer ({S.t} : Set X))
    (hh : h ∈ centralizer ({S.t} : Set X)) : S.act Λ (g * h) = S.act Λ g * S.act Λ h := by
  rw [S.act_of_mem Λ hg, S.act_of_mem Λ hh, S.act_of_mem Λ (mul_mem hg hh), ← map_mul]
  rfl

theorem act_inv {g : X} (hg : g ∈ centralizer ({S.t} : Set X)) : S.act Λ g⁻¹ = (S.act Λ g)⁻¹ := by
  rw [S.act_of_mem Λ hg, S.act_of_mem Λ (inv_mem hg), ← map_inv]
  rfl

theorem act_one : S.act Λ 1 = 1 := by
  rw [S.act_of_mem Λ (one_mem _), show (⟨1, _⟩ : centralizer ({S.t} : Set X)) = 1 from rfl,
    map_one]

theorem act_conj {g h : X} (hg : g ∈ centralizer ({S.t} : Set X))
    (hh : h ∈ centralizer ({S.t} : Set X)) :
    S.act Λ (g * h * g⁻¹) = S.act Λ g * S.act Λ h * (S.act Λ g)⁻¹ := by
  rw [S.act_mul Λ (mul_mem hg hh) (inv_mem hg), S.act_mul Λ hg hh, S.act_inv Λ hg]

theorem act_pow {g : X} (hg : g ∈ centralizer ({S.t} : Set X)) (n : ℕ) :
    S.act Λ (g ^ n) = S.act Λ g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, S.act_one Λ]
  | succ n ih => rw [pow_succ, S.act_mul Λ (pow_mem hg n) hg, ih, pow_succ]

theorem act_of_mem_T {g : X} (hg : g ∈ S.data.T) : S.act Λ g = S.data.ψ ⟨g, hg⟩ := by
  rw [S.act_of_mem Λ (S.data.T_le_centralizer hg), Λ.Ψ_T]
  rfl

theorem act_eq_one_iff {g : X} (hg : g ∈ centralizer ({S.t} : Set X)) :
    S.act Λ g = 1 ↔ g ∈ coreActionKernel S.L := by
  rw [S.act_of_mem Λ hg]
  exact Λ.Ψ_eq_one_iff _

theorem act_t : S.act Λ S.t = 1 := by
  rw [S.act_of_mem_T Λ S.data.t_mem_T, S.ψ_t]

theorem t_mem_centralizer : S.t ∈ centralizer ({S.t} : Set X) :=
  mem_centralizer_singleton_iff.mpr rfl

theorem eq_one_or_eq_t_of_mem_K {g : X} (hg : g ∈ S.data.K) : g = 1 ∨ g = S.t := by
  by_contra hne
  push Not at hne
  have hsub : ({1, S.t, g} : Set X) ⊆ (S.data.K : Set X) := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact one_mem _
    · exact S.data.t_mem_K
    · exact hg
  have h3 : ({1, S.t, g} : Set X).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, S.t, g, S.t_ne_one.symm, hne.1.symm, hne.2.symm, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, S.card_K] at h1
  omega

theorem eq_one_or_eq_t_of_act_eq_one {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({S.t} : Set X)) (hact : ∀ p ∈ P, S.act Λ p = 1) {p : X}
    (hp : p ∈ P) : p = 1 ∨ p = S.t := by
  obtain ⟨c, hc, hcP⟩ := S.data.exists_conj_le_T hP hPC
  have hcpT : c * p * c⁻¹ ∈ S.data.T := hcP ⟨p, hp, rfl⟩
  have hcpK : c * p * c⁻¹ ∈ S.data.K := by
    refine ⟨hcpT, ?_⟩
    have h1 : S.act Λ (c * p * c⁻¹) = 1 := by
      rw [S.act_conj Λ hc (hPC hp), hact p hp, mul_one, mul_inv_cancel]
    exact (S.act_eq_one_iff Λ (S.data.T_le_centralizer hcpT)).mp h1
  have htc : c⁻¹ * S.t * c = S.t := by
    have := mem_centralizer_singleton_iff.mp hc
    calc c⁻¹ * S.t * c = c⁻¹ * (S.t * c) := by group
      _ = c⁻¹ * (c * S.t) := by rw [this]
      _ = S.t := by group
  rcases S.eq_one_or_eq_t_of_mem_K hcpK with h | h
  · left
    calc p = c⁻¹ * (c * p * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · right
    calc p = c⁻¹ * (c * p * c⁻¹) * c := by group
      _ = S.t := by rw [h, htc]

theorem isPGroup_zpowers_of_sq {G : Type*} [Group G] {g : G} (hg2 : g ^ 2 = 1) :
    IsPGroup 2 (zpowers g) := by
  intro h
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← hn, ← zpow_natCast, ← zpow_mul,
    mul_comm, zpow_mul, zpow_natCast, hg2, one_zpow]

theorem eq_one_or_eq_t_of_sq {g : X} (hg : g ∈ centralizer ({S.t} : Set X)) (hact : S.act Λ g = 1)
    (hg2 : g ^ 2 = 1) : g = 1 ∨ g = S.t := by
  refine S.eq_one_or_eq_t_of_act_eq_one Λ (isPGroup_zpowers_of_sq hg2) (zpowers_le.mpr hg)
    (fun p hp => ?_) (mem_zpowers g)
  rcases eq_one_or_eq_of_mem_zpowers hg2 hp with rfl | rfl
  · exact S.act_one Λ
  · exact hact

theorem act_zpow {g : X} (hg : g ∈ centralizer ({S.t} : Set X)) (n : ℤ) :
    S.act Λ (g ^ n) = S.act Λ g ^ n := by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, S.act_pow Λ hg]
  · rw [zpow_negSucc, zpow_negSucc, S.act_inv Λ (pow_mem hg _), S.act_pow Λ hg]

theorem range_ΨC : (S.ΨC Λ).range = ⊤ := by
  refine eq_top_of_alternatingGroup_le ?_ (σ := c0)
    ⟨⟨S.k, S.data.T_le_centralizer S.k_mem⟩, ?_⟩ (by decide)
  · intro σ hσ
    obtain ⟨q, hq⟩ := Λ.iso.surjective ⟨σ, hσ⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨l, S.data.config.le_centralizer l.2⟩, ?_⟩
    change Λ.Ψ ⟨(l : X), _⟩ = σ
    rw [Λ.Ψ_of_mem l, hq]
  · change Λ.Ψ ⟨S.k, _⟩ = c0
    rw [← Λ.Ψ_T ⟨S.k, S.k_mem⟩]
    exact S.ψ_k

theorem exists_act_eq (σ : Perm (Fin 7)) :
    ∃ g ∈ centralizer ({S.t} : Set X), S.act Λ g = σ := by
  have : σ ∈ (S.ΨC Λ).range := by rw [S.range_ΨC Λ]; exact mem_top σ
  obtain ⟨⟨g, hg⟩, hgσ⟩ := this
  exact ⟨g, hg, by rw [S.act_of_mem Λ hg, hgσ]⟩

theorem exists_normalizer_act_eq {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({S.t} : Set X)) (htP : S.t ∈ P) {σ : Perm (Fin 7)}
    (hσ : ∀ p ∈ P, ∃ p' ∈ P, S.act Λ p' = σ * S.act Λ p * σ⁻¹) :
    ∃ g ∈ centralizer ({S.t} : Set X), (∀ p ∈ P, g * p * g⁻¹ ∈ P) ∧
      ∃ p₀ ∈ P, S.act Λ g = S.act Λ p₀ * σ := by
  let Y : Subgroup X :=
    { carrier := {c | c ∈ centralizer ({S.t} : Set X) ∧ ∃ p ∈ P, S.act Λ c = S.act Λ p}
      mul_mem' := by
        rintro a b ⟨ha, p, hp, hap⟩ ⟨hb, q, hq, hbq⟩
        exact ⟨mul_mem ha hb, p * q, mul_mem hp hq,
          by rw [S.act_mul Λ ha hb, S.act_mul Λ (hPC hp) (hPC hq), hap, hbq]⟩
      one_mem' := ⟨one_mem _, 1, one_mem _, rfl⟩
      inv_mem' := by
        rintro a ⟨ha, p, hp, hap⟩
        exact ⟨inv_mem ha, p⁻¹, inv_mem hp, by rw [S.act_inv Λ ha, S.act_inv Λ (hPC hp), hap]⟩ }
  have hPY : P ≤ Y := fun p hp => ⟨hPC hp, p, hp, rfl⟩
  obtain ⟨g₀, hg₀, hg₀σ⟩ := S.exists_act_eq Λ σ
  have hP'Y : P.map (MulAut.conj g₀).toMonoidHom ≤ Y := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨p', hp', hp'σ⟩ := hσ p hp
    exact ⟨mul_mem (mul_mem hg₀ (hPC hp)) (inv_mem hg₀), p', hp',
      by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
         rw [S.act_conj Λ hg₀ (hPC hp), hg₀σ, hp'σ]⟩
  have hmax : ∀ Q : Subgroup X, IsPGroup 2 Q → P ≤ Q → Q ≤ Y → Q ≤ P := by
    intro Q hQ hPQ hQY q hq
    obtain ⟨hqC, p, hp, hqp⟩ := hQY hq
    have hpq : p⁻¹ * q ∈ Q := mul_mem (inv_mem (hPQ hp)) hq
    have hpqC : p⁻¹ * q ∈ centralizer ({S.t} : Set X) := mul_mem (inv_mem (hPC hp)) hqC
    have hact1 : S.act Λ (p⁻¹ * q) = 1 := by
      rw [S.act_mul Λ (inv_mem (hPC hp)) hqC, S.act_inv Λ (hPC hp), hqp, inv_mul_cancel]
    have hZ : IsPGroup 2 (zpowers (p⁻¹ * q)) := hQ.to_le (zpowers_le.mpr hpq)
    have hq' : q = p * (p⁻¹ * q) := by group
    rcases S.eq_one_or_eq_t_of_act_eq_one Λ hZ (zpowers_le.mpr hpqC) (fun r hr => by
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hr
        rw [S.act_zpow Λ hpqC, hact1, one_zpow]) (mem_zpowers _) with h | h
    · rw [hq', h, mul_one]
      exact hp
    · rw [hq', h]
      exact mul_mem hp htP
  have hcardP := card_eq_two_pow_of_maximal hPY hP hmax
  have hcardP' : Nat.card (P.map (MulAut.conj g₀).toMonoidHom) =
      2 ^ (Nat.card Y).factorization 2 := by
    rw [card_map_of_injective (MulAut.conj g₀).injective, hcardP]
  obtain ⟨y, ⟨hyC, p₀, hp₀, hyp₀⟩, hyP⟩ := exists_conj_eq_of_card_eq hP'Y hPY hcardP' hcardP
  refine ⟨y * g₀, mul_mem hyC hg₀, fun p hp => ?_, p₀, hp₀,
    by rw [S.act_mul Λ hyC hg₀, hyp₀, hg₀σ]⟩
  have : y * (g₀ * p * g₀⁻¹) * y⁻¹ ∈ P := by
    rw [← hyP]
    exact ⟨g₀ * p * g₀⁻¹, ⟨p, hp, rfl⟩, rfl⟩
  simpa [mul_assoc] using this

theorem act_z : S.act Λ S.z = a0 ^ 2 := by rw [S.act_of_mem_T Λ S.z_mem.1, S.ψ_z]

theorem act_k : S.act Λ S.k = c0 := by rw [S.act_of_mem_T Λ S.k_mem, S.ψ_k]

end A7Base

end CFSG.ComponentClassification.HSFLit
