module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Perm
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3SigmaC
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Key
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.Sec13

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem conj_mem_sup {S Zc : Subgroup Γ} (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g) {x : Γ}
    (hx : ∀ s ∈ S, x * s * x⁻¹ ∈ S ⊔ Zc) : ∀ h ∈ S ⊔ Zc, x * h * x⁻¹ ∈ S ⊔ Zc := by
  have hZn : Zc.Normal := ⟨fun n hn h => by rw [hZc n hn h, mul_inv_cancel_right]; exact hn⟩
  intro h hh
  obtain ⟨s, hs, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hh
  have e : x * (s * k) * x⁻¹ = (x * s * x⁻¹) * k := by
    calc x * (s * k) * x⁻¹ = x * (k * s) * x⁻¹ := by rw [hZc k hk s]
      _ = (x * k) * s * x⁻¹ := by group
      _ = (k * x) * s * x⁻¹ := by rw [hZc k hk x]
      _ = k * (x * s * x⁻¹) := by group
      _ = (x * s * x⁻¹) * k := by rw [hZc k hk]
  rw [e]
  exact (S ⊔ Zc).mul_mem (hx s hs) (Subgroup.mem_sup_right hk)

theorem mem_normalizer_sup {S Zc : Subgroup Γ} (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g) {x : Γ}
    (hx : ∀ s ∈ S, x * s * x⁻¹ ∈ S ⊔ Zc) (hx' : ∀ s ∈ S, x⁻¹ * s * x ∈ S ⊔ Zc) :
    x ∈ Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_mem_sup hZc hx h hh
  · intro hh
    have := conj_mem_sup hZc (x := x⁻¹) (by simpa using hx') _ hh
    simpa [mul_assoc] using this

theorem normalizes_of_commutator_eq {S P : Subgroup Γ} (hSP : ⁅S, P⁆ = S) {p : Γ} (hp : p ∈ P) :
    ∀ s ∈ S, p * s * p⁻¹ ∈ S := by
  intro s hs
  have h1 : ⁅p, s⁆ ∈ ⁅P, S⁆ := Subgroup.commutator_mem_commutator hp hs
  rw [Subgroup.commutator_comm, hSP] at h1
  have e : p * s * p⁻¹ = ⁅p, s⁆ * s := by rw [commutatorElement_def]; group
  rw [e]
  exact S.mul_mem h1 hs

theorem mem_normalizer_of_commutator {Zc S P : Subgroup Γ}
    (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g) (hSP : ⁅S, P⁆ = S) {p : Γ} (hp : p ∈ P) :
    p ∈ Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ) :=
  mem_normalizer_sup hZc (fun s hs => Subgroup.mem_sup_left (normalizes_of_commutator_eq hSP hp s hs))
    (fun s hs => by
      have h := normalizes_of_commutator_eq hSP (P.inv_mem hp) s hs
      rw [inv_inv] at h
      exact Subgroup.mem_sup_left h)

theorem comm_sup_mem_Zc {S Zc : Subgroup Γ} {z : Γ} (hF : Q8D8Facts S z) (hz : z ∈ Zc)
    (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g) {t : Γ} (ht : t ∈ S ⊔ Zc) {s : Γ} (hs : s ∈ S) :
    t * s * t⁻¹ * s⁻¹ ∈ Zc := by
  have hZn : Zc.Normal := ⟨fun n hn h => by rw [hZc n hn h, mul_inv_cancel_right]; exact hn⟩
  obtain ⟨s1, hs1, k1, hk1, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ht
  have e : s1 * k1 * s * (s1 * k1)⁻¹ * s⁻¹ = s1 * s * s1⁻¹ * s⁻¹ := by
    have hk' : k1 * s * k1⁻¹ = s := by rw [← hZc k1 hk1 s, mul_inv_cancel_right]
    calc s1 * k1 * s * (s1 * k1)⁻¹ * s⁻¹ = s1 * (k1 * s * k1⁻¹) * s1⁻¹ * s⁻¹ := by group
      _ = s1 * s * s1⁻¹ * s⁻¹ := by rw [hk']
  rw [e]
  rcases hF.comm_mem s1 hs1 s hs with h | h
  · rw [h]; exact Zc.one_mem
  · rw [h]; exact hz

theorem T_le_sup {Zc : Subgroup Γ} (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    {X P S : Subgroup Γ} (hPX : P ≤ X) (hP : Nat.card P = 5) (hSO : S ≤ pCoreOf 2 X)
    (hSP : ⁅S, P⁆ = S) {z : Γ} (hF : Q8D8Facts S z) (hz : z ∈ Zc)
    {Ψ : ↥S →* Multiplicative Sp4.V4} (hΨ : PsiSpec S z Ψ)
    (hZ2 : ∀ k ∈ Zc, k * k = 1 → k = 1 ∨ k = z)
    (hF1 : ∀ g : Γ, (∀ s ∈ S, g * s = s * g) → g ∈ Zc) :
    pCoreOf 2 X ≤ S ⊔ Zc := by
  by_contra hnot
  have hSle : S ≤ S ⊔ Zc := le_sup_left
  have hZle : Zc ≤ S ⊔ Zc := le_sup_right
  have hTX : pCoreOf 2 X ≤ X := pCoreOf_two_le X
  have hST : S ≤ pCoreOf 2 X := hSO
  obtain ⟨σ, hσ⟩ := exists_sigma hF hΨ hZc hz
  have hR0T : (S ⊔ Zc) ⊓ pCoreOf 2 X ≤ pCoreOf 2 X := inf_le_right
  have hSR0 : S ≤ (S ⊔ Zc) ⊓ pCoreOf 2 X := le_inf hSle hST
  have hR0ne : (S ⊔ Zc) ⊓ pCoreOf 2 X ≠ pCoreOf 2 X := by
    intro h
    exact hnot (calc pCoreOf 2 X = (S ⊔ Zc) ⊓ pCoreOf 2 X := h.symm
      _ ≤ S ⊔ Zc := inf_le_left)
  obtain ⟨t, htT, htR0, htN⟩ :=
    exists_mem_normalizer_not_mem (pCoreOf_two_isPGroup X) hR0T hR0ne
  have hM0conj : ∀ m ∈ pCoreOf 2 X ⊓ Subgroup.normalizer (((S ⊔ Zc) ⊓ pCoreOf 2 X : Subgroup Γ) : Set Γ),
      ∀ s ∈ S, m * s * m⁻¹ ∈ S ⊔ Zc := by
    intro m hm s hs
    have hmN := (Subgroup.mem_inf.mp hm).2
    have := (Subgroup.mem_normalizer_iff.mp hmN s).mp (hSR0 hs)
    exact (Subgroup.mem_inf.mp this).1
  have hM0N : ∀ m ∈ pCoreOf 2 X ⊓ Subgroup.normalizer (((S ⊔ Zc) ⊓ pCoreOf 2 X : Subgroup Γ) : Set Γ),
      m ∈ Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ) := by
    intro m hm
    refine mem_normalizer_sup hZc (hM0conj m hm) (fun s hs => ?_)
    have h := hM0conj m⁻¹ (Subgroup.inv_mem _ hm) s hs
    rwa [inv_inv] at h
  have hPN : ∀ p ∈ P, p ∈ Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ) :=
    fun p hp => mem_normalizer_of_commutator hZc hSP hp
  have hPR0 : ∀ p ∈ P, p ∈ Subgroup.normalizer
      (((S ⊔ Zc) ⊓ pCoreOf 2 X : Subgroup Γ) : Set Γ) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hpX : p ∈ X := hPX hp
    have h1 : h ∈ S ⊔ Zc ↔ p * h * p⁻¹ ∈ S ⊔ Zc := Subgroup.mem_normalizer_iff.mp (hPN p hp) h
    have h2 : h ∈ pCoreOf 2 X ↔ p * h * p⁻¹ ∈ pCoreOf 2 X := by
      constructor
      · intro hh
        exact pCoreOf_two_conj X hpX hh
      · intro hh
        have h3 := pCoreOf_two_conj X (X.inv_mem hpX) hh
        have e : p⁻¹ * (p * h * p⁻¹) * p⁻¹⁻¹ = h := by group
        rwa [e] at h3
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
  have hM0Nn : pCoreOf 2 X ⊓ Subgroup.normalizer (((S ⊔ Zc) ⊓ pCoreOf 2 X : Subgroup Γ) : Set Γ) ≤
      Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ) := hM0N
  have hMσ2 : IsPGroup 2 ↥((pCoreOf 2 X ⊓ Subgroup.normalizer
      (((S ⊔ Zc) ⊓ pCoreOf 2 X : Subgroup Γ) : Set Γ)).subgroupOf
        (Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ))) := by
    have h1 : IsPGroup 2 ↥(pCoreOf 2 X ⊓ Subgroup.normalizer
        (((S ⊔ Zc) ⊓ pCoreOf 2 X : Subgroup Γ) : Set Γ)) :=
      (pCoreOf_two_isPGroup X).to_le inf_le_left
    exact IsPGroup.of_injective h1 (Subgroup.subgroupOfEquivOfLe hM0Nn).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hM0Nn).injective
  have hK2 := hMσ2.map σ
  have hex : ∃ p, ∃ hp : p ∈ P, σ ⟨p, hPN p hp⟩ ≠ 1 := by
    by_contra hno
    push Not at hno
    have hle : ⁅S, P⁆ ≤ Subgroup.zpowers z := by
      rw [Subgroup.commutator_le]
      intro s hs p hp
      have hcomm := (hσ ⟨p, hPN p hp⟩).mp (hno p hp)
      obtain ⟨s0, hs0, k, hk, hpk⟩ := key_K hF hΨ hZc hz hZ2 hF1 hcomm
      have hk' : k * s⁻¹ * k⁻¹ = s⁻¹ := by rw [← hZc k hk s⁻¹, mul_inv_cancel_right]
      have hpk' : p = s0 * k := hpk
      have e : s * p * s⁻¹ * p⁻¹ = s * s0 * s⁻¹ * s0⁻¹ := by
        rw [hpk']
        calc s * (s0 * k) * s⁻¹ * (s0 * k)⁻¹ = s * s0 * (k * s⁻¹ * k⁻¹) * s0⁻¹ := by group
          _ = s * s0 * s⁻¹ * s0⁻¹ := by rw [hk']
      rw [commutatorElement_def, e]
      rcases hF.comm_mem s hs s0 hs0 with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers z
    have hS' : S ≤ Subgroup.zpowers z := calc S = ⁅S, P⁆ := hSP.symm
      _ ≤ _ := hle
    have h32 : Nat.card S ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hS'
    have hz2 : Nat.card (Subgroup.zpowers z) ≤ 2 := by
      rw [Nat.card_zpowers]
      have : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hF.z_mul_self)
      exact Nat.le_of_dvd (by norm_num) this
    rw [hF.card_eq] at h32
    omega
  obtain ⟨p, hpP, hσp⟩ := hex
  have hpn := hPN p hpP
  have hτ5 : σ ⟨p, hpn⟩ ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨p, hpn⟩ : ↥(Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ))) ^ 5 = 1 := by
      apply Subtype.ext
      show p ^ 5 = 1
      have h := pow_card_eq_one' (x := (⟨p, hpP⟩ : ↥P))
      rw [hP] at h
      exact congrArg Subtype.val h
    rw [this, map_one]
  have hnormK : ∀ k ∈ (((pCoreOf 2 X ⊓ Subgroup.normalizer
      (((S ⊔ Zc) ⊓ pCoreOf 2 X : Subgroup Γ) : Set Γ)).subgroupOf
        (Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ))).map σ),
      σ ⟨p, hpn⟩ * k * (σ ⟨p, hpn⟩)⁻¹ ∈ (((pCoreOf 2 X ⊓ Subgroup.normalizer
      (((S ⊔ Zc) ⊓ pCoreOf 2 X : Subgroup Γ) : Set Γ)).subgroupOf
        (Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ))).map σ) := by
    intro k hk
    obtain ⟨m, hmM, rfl⟩ := Subgroup.mem_map.mp hk
    refine Subgroup.mem_map.mpr ⟨⟨p, hpn⟩ * m * ⟨p, hpn⟩⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf]
    have hm0 := Subgroup.mem_subgroupOf.mp hmM
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact pCoreOf_two_conj X (hPX hpP) (Subgroup.mem_inf.mp hm0).1
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hPR0 p hpP) (Subgroup.mem_inf.mp hm0).2)
        (Subgroup.inv_mem _ (hPR0 p hpP))
  have hKbot := perm6_two_group_trivial _ hK2 (σ ⟨p, hpn⟩) hτ5 hσp hnormK
  have htM0 : t ∈ pCoreOf 2 X ⊓ Subgroup.normalizer
      (((S ⊔ Zc) ⊓ pCoreOf 2 X : Subgroup Γ) : Set Γ) :=
    Subgroup.mem_inf.mpr ⟨htT, Subgroup.mem_normalizer_iff.mpr htN⟩
  have htNn := hM0N t htM0
  have hσt : σ ⟨t, htNn⟩ = 1 := by
    have h1 : σ ⟨t, htNn⟩ ∈ (((pCoreOf 2 X ⊓ Subgroup.normalizer
        (((S ⊔ Zc) ⊓ pCoreOf 2 X : Subgroup Γ) : Set Γ)).subgroupOf
          (Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ))).map σ) :=
      Subgroup.mem_map.mpr ⟨⟨t, htNn⟩, Subgroup.mem_subgroupOf.mpr htM0, rfl⟩
    rw [hKbot] at h1
    exact Subgroup.mem_bot.mp h1
  have hcomm := (hσ ⟨t, htNn⟩).mp hσt
  obtain ⟨s0, hs0, k, hk, htk⟩ := key_K hF hΨ hZc hz hZ2 hF1 hcomm
  apply htR0
  have htk' : t = s0 * k := htk
  have hs0T : s0 ∈ pCoreOf 2 X := hST hs0
  have hkT : k ∈ pCoreOf 2 X := by
    have e : k = s0⁻¹ * t := by rw [htk']; group
    rw [e]
    exact (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem hs0T) htT
  have hkR0 : k ∈ (S ⊔ Zc) ⊓ pCoreOf 2 X := Subgroup.mem_inf.mpr ⟨hZle hk, hkT⟩
  rw [htk']
  exact ((S ⊔ Zc) ⊓ pCoreOf 2 X).mul_mem (hSR0 hs0) hkR0

theorem partA {Zc : Subgroup Γ} (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    (hZ2 : ∀ k ∈ Zc, k * k = 1 → ∀ k' ∈ Zc, k' * k' = 1 → k = 1 ∨ k' = 1 ∨ k = k')
    {X P S : Subgroup Γ} (hPX : P ≤ X) (hP : Nat.card P = 5) (hSX : S ≤ X)
    (hSO : S ≤ pCoreOf 2 X) (hSP : ⁅S, P⁆ = S)
    (hQ8 : CFSG.LocalAnalysis.RankThreeTheoremC.smallRankIsQ8D8 S)
    (hF1 : ∀ g : Γ, (∀ s ∈ S, g * s = s * g) → g ∈ Zc) :
    rankThreePrimeCore 2 X ≤ Zc ∧
    (∀ _ : ((rankThreePrimeCore 2 X ⊔ pCoreOf 2 X).subgroupOf X).Normal,
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.IsInvolvedIn
        (↥X ⧸ (rankThreePrimeCore 2 X ⊔ pCoreOf 2 X).subgroupOf X) (Equiv.Perm (Fin 6))) := by
  obtain ⟨z, i, j, r, t, hF, hG⟩ := q8d8_exists hQ8
  have hz : z ∈ Zc := hF1 z ((hF.center_iff z hF.z_mem).mpr (Or.inr rfl))
  have hZ2' : ∀ k ∈ Zc, k * k = 1 → k = 1 ∨ k = z := by
    intro k hk hkk
    rcases hZ2 k hk hkk z hz hF.z_mul_self with h | h | h
    · exact Or.inl h
    · exact absurd h hF.z_ne_one
    · exact Or.inr h
  obtain ⟨Ψ, hΨ⟩ := psi_exists hF
  refine ⟨?_, ?_⟩
  · intro y hy
    apply hF1
    intro s hs
    exact primeCore_two_commute_pCore X hy (hSO hs)
  · intro hN
    have hT := T_le_sup hZc hPX hP hSO hSP hF hz hΨ hZ2' hF1
    obtain ⟨σ, hσ⟩ := exists_sigma hF hΨ hZc hz
    have hZn : Zc.Normal := ⟨fun n hn h => by rw [hZc n hn h, mul_inv_cancel_right]; exact hn⟩
    have hXN : ∀ x ∈ X, x ∈ Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ) := by
      intro x hx
      refine mem_normalizer_sup hZc (fun s hs => ?_) (fun s hs => ?_)
      · exact hT (pCoreOf_two_conj X hx (hSO hs))
      · have h := hT (pCoreOf_two_conj X (X.inv_mem hx) (hSO hs))
        rwa [inv_inv] at h
    let ρ : ↥X →* Equiv.Perm (Fin 6) :=
      σ.comp (Subgroup.inclusion (fun x hx => hXN x hx))
    have hker : ρ.ker = (rankThreePrimeCore 2 X ⊔ pCoreOf 2 X).subgroupOf X := by
      ext ⟨x, hx⟩
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show σ ⟨x, hXN x hx⟩ = 1 ↔ x ∈ rankThreePrimeCore 2 X ⊔ pCoreOf 2 X
      constructor
      · intro h1
        have hcomm := (hσ ⟨x, hXN x hx⟩).mp h1
        obtain ⟨s0, hs0, k, hk, hxk⟩ := key_K hF hΨ hZc hz hZ2' hF1 hcomm
        have hxk' : x = s0 * k := hxk
        have hs0T : s0 ∈ pCoreOf 2 X := hSO hs0
        have hkX : k ∈ X := by
          have e : k = s0⁻¹ * x := by rw [hxk']; group
          rw [e]
          exact X.mul_mem (X.inv_mem (hSX hs0)) hx
        have hkYT : k ∈ rankThreePrimeCore 2 X ⊔ pCoreOf 2 X := inf_central_le_sup X hZc hkX hk
        rw [hxk']
        exact (rankThreePrimeCore 2 X ⊔ pCoreOf 2 X).mul_mem (Subgroup.mem_sup_right hs0T) hkYT
      · intro hxYT
        refine (hσ ⟨x, hXN x hx⟩).mpr ?_
        intro s hs
        obtain ⟨y, hy, t', ht', hxe⟩ := (mem_sup_primeCore_pCore X).mp hxYT
        have hsT : s ∈ pCoreOf 2 X := hSO hs
        have hwT : t' * s * t'⁻¹ ∈ pCoreOf 2 X :=
          pCoreOf_two_conj X (pCoreOf_two_le X ht') hsT
        have hyw : y * (t' * s * t'⁻¹) = (t' * s * t'⁻¹) * y :=
          primeCore_two_commute_pCore X hy hwT
        have e : x * s * x⁻¹ * s⁻¹ = t' * s * t'⁻¹ * s⁻¹ := by
          rw [hxe]
          calc y * t' * s * (y * t')⁻¹ * s⁻¹ = y * (t' * s * t'⁻¹) * y⁻¹ * s⁻¹ := by group
            _ = (t' * s * t'⁻¹) * y * y⁻¹ * s⁻¹ := by rw [hyw]
            _ = t' * s * t'⁻¹ * s⁻¹ := by group
        show x * s * x⁻¹ * s⁻¹ ∈ Zc
        rw [e]
        exact comm_sup_mem_Zc hF hz hZc (hT ht') hs
    refine ⟨ρ.range, ⊥, Subgroup.normal_bot, ⟨?_⟩⟩
    exact (QuotientGroup.quotientBot).trans
      ((QuotientGroup.quotientKerEquivRange ρ).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
