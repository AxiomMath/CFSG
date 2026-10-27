module

public import CFSG.CGT.PushingUpLit.BHS6.SixEightSetup

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

namespace AltSetup

variable {E : Subgroup Γ} {n : ℕ} (M : AltSetup E n) {p : Fin 3 → Fin n}

@[expose] def blockSub (p : Fin 3 → Fin n) (g : ↥E) : Subgroup Γ :=
  Subgroup.closure ((M.wSub p : Set Γ) ∪ {(g : Γ)})

variable {M}

theorem Ψ_zpow {g : ↥E} (hgd : M.Ψ g = triCyc p) (k : ℤ) : M.Ψ (g ^ k) = triCyc p ^ k := by
  rw [map_zpow, hgd]

theorem conj_zpow_mem_wSub (hp : Function.Injective p) {g : ↥E} (hgd : M.Ψ g = triCyc p) (k : ℤ)
    {w : Γ} (hw : w ∈ M.wSub p) : (g : Γ) ^ k * w * ((g : Γ) ^ k)⁻¹ ∈ M.wSub p := by
  have := M.conj_mem_wSub (g ^ k) (by
    rw [Ψ_zpow hgd]
    exact (setStab (triSet p)).zpow_mem (triCyc_mem_setStab hp) k) hw
  simpa using this

theorem mem_blockSub_iff (hp : Function.Injective p) {g : ↥E} (hgd : M.Ψ g = triCyc p) {x : Γ} :
    x ∈ M.blockSub p g ↔ ∃ w ∈ M.wSub p, ∃ k : ℤ, x = w * (g : Γ) ^ k := by
  constructor
  · intro hx
    unfold blockSub at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 0, by simp⟩
      · rw [Set.mem_singleton_iff] at hy
        exact ⟨1, (M.wSub p).one_mem, 1, by simp [hy]⟩
    | one => exact ⟨1, (M.wSub p).one_mem, 0, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨w, hw, k, rfl⟩ := hy
      obtain ⟨w', hw', l, rfl⟩ := hz
      refine ⟨w * ((g : Γ) ^ k * w' * ((g : Γ) ^ k)⁻¹),
        (M.wSub p).mul_mem hw (conj_zpow_mem_wSub hp hgd k hw'), k + l, ?_⟩
      rw [zpow_add]
      group
    | inv y _ hy =>
      obtain ⟨w, hw, k, rfl⟩ := hy
      refine ⟨(g : Γ) ^ (-k) * w⁻¹ * ((g : Γ) ^ (-k))⁻¹,
        by simpa using conj_zpow_mem_wSub hp hgd (-k) ((M.wSub p).inv_mem hw), -k, ?_⟩
      group
  · rintro ⟨w, hw, k, rfl⟩
    have h1 : w ∈ M.blockSub p g := Subgroup.subset_closure (Or.inl hw)
    have h2 : (g : Γ) ∈ M.blockSub p g := Subgroup.subset_closure (Or.inr rfl)
    exact (M.blockSub p g).mul_mem h1 ((M.blockSub p g).zpow_mem h2 k)

theorem blockSub_le_E (hp : Function.Injective p) {g : ↥E} (hgd : M.Ψ g = triCyc p) :
    M.blockSub p g ≤ E := by
  intro x hx
  obtain ⟨w, hw, k, rfl⟩ := (mem_blockSub_iff hp hgd).1 hx
  exact E.mul_mem (M.wSub_le_E hw) (E.zpow_mem g.2 k)

theorem Ψ_mul_zpow {g : ↥E} (hgd : M.Ψ g = triCyc p) {w : Γ} (hw : w ∈ M.wSub p) (k : ℤ)
    (hx : w * (g : Γ) ^ k ∈ E) : M.Ψ ⟨w * (g : Γ) ^ k, hx⟩ = triCyc p ^ k := by
  have h1 : (⟨w * (g : Γ) ^ k, hx⟩ : ↥E) = ⟨w, M.wSub_le_E hw⟩ * g ^ k := rfl
  rw [h1, map_mul, M.Ψ_eq_one_of_mem (M.wSub_le_W hw), one_mul, Ψ_zpow hgd]

theorem zpow_eq_one_of_dvd {g : ↥E} (hg3 : g ^ 3 = 1) {k : ℤ} (h : (3 : ℤ) ∣ k) : g ^ k = 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [zpow_mul]
  have : g ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hg3]
  rw [this, one_zpow]

theorem three_dvd_of_triCyc_zpow_eq_one (hp : Function.Injective p) {k : ℤ}
    (h : triCyc p ^ k = 1) : (3 : ℤ) ∣ k := by
  have := orderOf_dvd_iff_zpow_eq_one.2 h
  rwa [(triCyc_isThreeCycle hp).orderOf] at this

theorem mem_wSub_of_mem_blockSub_W (hp : Function.Injective p) {g : ↥E} (hg3 : g ^ 3 = 1)
    (hgd : M.Ψ g = triCyc p) {x : Γ} (hx : x ∈ M.blockSub p g) (hxW : x ∈ M.W) :
    x ∈ M.wSub p := by
  obtain ⟨w, hw, k, rfl⟩ := (mem_blockSub_iff hp hgd).1 hx
  have hxE : w * (g : Γ) ^ k ∈ E := blockSub_le_E hp hgd hx
  have h1 := Ψ_mul_zpow hgd hw k hxE
  have h2 := (M.mem_W_iff ⟨_, hxE⟩).1 hxW
  rw [h2] at h1
  have h3 := zpow_eq_one_of_dvd hg3 (three_dvd_of_triCyc_zpow_eq_one hp h1.symm)
  have h4 : (g : Γ) ^ k = 1 := by
    have := congrArg (fun x : ↥E => (x : Γ)) h3
    simpa using this
  rw [h4, mul_one]
  exact hw

theorem mem_blockSub_of_cube_eq_one (hp : Function.Injective p) {g : ↥E} (hg3 : g ^ 3 = 1)
    (hgd : M.Ψ g = triCyc p) (e : ↥E) (he : M.Ψ e ∈ Subgroup.zpowers (triCyc p))
    (he3 : e ^ 3 = 1) : (e : Γ) ∈ M.blockSub p g := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 he
  set u : ↥E := e * g ^ (-j) with hu
  have hΨu : M.Ψ u = 1 := by
    rw [hu, map_mul, Ψ_zpow hgd, ← hj, ← zpow_add, add_neg_cancel, zpow_zero]
  have huW : (u : Γ) ∈ M.W := (M.mem_W_iff u).2 hΨu
  have heq : e = u * g ^ j := by
    rw [hu, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  set G₁ : ↥E := g ^ j with hG₁
  have hG₁3 : G₁ ^ 3 = 1 := by
    rw [hG₁, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hg3]
  have hnorm : u * (G₁ * u * G₁⁻¹) * (G₁ ^ 2 * u * (G₁ ^ 2)⁻¹) = 1 := by
    have h1 : e ^ 3 = u * (G₁ * u * G₁⁻¹) * (G₁ ^ 2 * u * (G₁ ^ 2)⁻¹) * G₁ ^ 3 := by
      rw [heq]
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [he3, hG₁3, mul_one] at h1
    exact h1.symm
  set uW : ↥M.W := ⟨(u : Γ), huW⟩ with huWdef
  have hN : uW * M.conjW G₁ uW * M.conjW (G₁ ^ 2) uW = 1 := by
    apply Subtype.ext
    have := congrArg (fun x : ↥E => (x : Γ)) hnorm
    simpa [AltSetup.conjW, huWdef] using this
  have hβ : M.βe uW * coreAct n (M.Ψ G₁) (M.βe uW) * coreAct n (M.Ψ (G₁ ^ 2)) (M.βe uW) = 1 := by
    have := congrArg M.βe hN
    rwa [map_mul, map_mul, map_one, M.βe_conjW, M.βe_conjW] at this
  have hσ : ∀ j' ∈ (Finset.univ : Finset (Fin n)), j' ∉ triSet p → (triCyc p ^ j) j' = j' :=
    fun j' _ hj' => Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (triCyc_apply_of_notMem hj') j
  have hΨG : M.Ψ G₁ = triCyc p ^ j := by rw [hG₁, Ψ_zpow hgd]
  have hmem : M.βe uW ∈ suppSub (triSet p) := by
    refine mem_suppSub_of_norm (σ := triCyc p ^ j) (fun j' hj' => hσ j' (Finset.mem_univ _) hj') ?_
    rw [map_pow, hΨG] at hβ
    exact hβ
  have hwS : (u : Γ) ∈ M.wSub p := ⟨huW, hmem⟩
  rw [mem_blockSub_iff hp hgd]
  refine ⟨u, hwS, j, ?_⟩
  rw [heq]
  rfl

theorem conj_blockSub_mem_wSub (hp : Function.Injective p) {g : ↥E} (hgd : M.Ψ g = triCyc p)
    {x : Γ} (hx : x ∈ M.blockSub p g) {w' : Γ} (hw' : w' ∈ M.wSub p) :
    x * w' * x⁻¹ ∈ M.wSub p := by
  obtain ⟨w, hw, k, rfl⟩ := (mem_blockSub_iff hp hgd).1 hx
  have h1 : w * (g : Γ) ^ k * w' * (w * (g : Γ) ^ k)⁻¹ =
      w * ((g : Γ) ^ k * w' * ((g : Γ) ^ k)⁻¹) * w⁻¹ := by group
  rw [h1]
  exact (M.wSub p).mul_mem ((M.wSub p).mul_mem hw (conj_zpow_mem_wSub hp hgd k hw'))
    ((M.wSub p).inv_mem hw)

theorem blockSub_le_normalizer_wSub (hp : Function.Injective p) {g : ↥E}
    (hgd : M.Ψ g = triCyc p) :
    M.blockSub p g ≤ Subgroup.normalizer (M.wSub p : Set Γ) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro w'
  refine ⟨fun hw' => conj_blockSub_mem_wSub hp hgd hx hw', fun hw' => ?_⟩
  have hxi : x⁻¹ ∈ M.blockSub p g := (M.blockSub p g).inv_mem hx
  have := conj_blockSub_mem_wSub hp hgd hxi hw'
  simpa [mul_assoc] using this

theorem pCoreOf_blockSub (hp : Function.Injective p) {g : ↥E} (hg3 : g ^ 3 = 1)
    (hgd : M.Ψ g = triCyc p) : pCoreOf 2 (M.blockSub p g) = M.wSub p := by
  apply le_antisymm
  · intro x hx
    have hxF : x ∈ M.blockSub p g := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hx
    obtain ⟨k₂, hk₂⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2
      (M.blockSub p g) ⟨x, hx⟩
    have hk₂' : x ^ 2 ^ k₂ = 1 := by
      have := congrArg (fun y : ↥(pCoreOf 2 (M.blockSub p g)) => (y : Γ)) hk₂
      simpa using this
    obtain ⟨w, hw, k, hxk⟩ := (mem_blockSub_iff hp hgd).1 hxF
    have hxE : x ∈ E := blockSub_le_E hp hgd hxF
    have hΨx : M.Ψ ⟨x, hxE⟩ = triCyc p ^ k := by
      have := Ψ_mul_zpow hgd hw k (hxk ▸ hxE)
      simpa [hxk] using this
    have h1 : (M.Ψ ⟨x, hxE⟩) ^ 2 ^ k₂ = 1 := by
      rw [← map_pow]
      have : (⟨x, hxE⟩ : ↥E) ^ 2 ^ k₂ = 1 := Subtype.ext (by simpa using hk₂')
      rw [this, map_one]
    rw [hΨx, ← zpow_natCast, ← zpow_mul] at h1
    have h2 := three_dvd_of_triCyc_zpow_eq_one hp h1
    have hcop : IsCoprime (3 : ℤ) ((2 : ℤ) ^ k₂) := by
      apply IsCoprime.pow_right
      rw [Int.isCoprime_iff_gcd_eq_one]
      norm_num
    have h3 : (3 : ℤ) ∣ k := by
      have : (3 : ℤ) ∣ k * (2 : ℤ) ^ k₂ := by simpa using h2
      exact hcop.dvd_of_dvd_mul_right this
    have h4 := zpow_eq_one_of_dvd hg3 h3
    have h5 : (g : Γ) ^ k = 1 := by
      have := congrArg (fun y : ↥E => (y : Γ)) h4
      simpa using this
    rw [hxk, h5, mul_one]
    exact hw
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · intro w hw
      exact Subgroup.subset_closure (Or.inl hw)
    · exact blockSub_le_normalizer_wSub hp hgd
    · exact M.hW2.to_le M.wSub_le_W

theorem exists_commutator_eq (hp : Function.Injective p) {g : ↥E} (hgd : M.Ψ g = triCyc p)
    {w : Γ} (hw : w ∈ M.wSub p) : ∃ u ∈ M.wSub p, (g : Γ) * u * (g : Γ)⁻¹ * u⁻¹ = w := by
  obtain ⟨hwW, hwv⟩ := hw
  obtain ⟨v, hv, hvw⟩ := exists_coreAct_triCyc_mul_inv hp hwv
  set uW : ↥M.W := M.βe.symm v with huWdef
  have huW : M.βe uW = v := M.βe.apply_symm_apply v
  refine ⟨(uW : Γ), ⟨uW.2, ?_⟩, ?_⟩
  · have : (⟨(uW : Γ), uW.2⟩ : ↥M.W) = uW := rfl
    rw [this, huW]
    exact hv
  · have key : M.conjW g uW * uW⁻¹ = ⟨w, hwW⟩ := by
      apply M.βe.injective
      rw [map_mul, map_inv, M.βe_conjW, hgd, huW]
      exact hvw
    have := congrArg (fun x : ↥M.W => (x : Γ)) key
    simpa [AltSetup.conjW] using this

theorem g_mem_blockSub {g : ↥E} : (g : Γ) ∈ M.blockSub p g :=
  Subgroup.subset_closure (Or.inr rfl)

theorem wSub_le_blockSub {g : ↥E} : M.wSub p ≤ M.blockSub p g := fun _ hw =>
  Subgroup.subset_closure (Or.inl hw)

theorem commutator_wSub_blockSub (hp : Function.Injective p) {g : ↥E} (hgd : M.Ψ g = triCyc p) :
    ⁅M.wSub p, M.blockSub p g⁆ = M.wSub p := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 := conj_blockSub_mem_wSub hp hgd hb ha
    have h2 : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    refine (M.wSub p).mul_mem ha ?_
    have := conj_blockSub_mem_wSub hp hgd hb ((M.wSub p).inv_mem ha)
    simpa [mul_assoc] using this
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := exists_commutator_eq hp hgd hw
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator g_mem_blockSub hu

theorem opResidual_blockSub (hp : Function.Injective p) {g : ↥E} (hg3 : g ^ 3 = 1)
    (hgd : M.Ψ g = triCyc p) : opResidual 2 (M.blockSub p g) = M.blockSub p g := by
  apply le_antisymm (opResidual_le 2 _)
  have hg3' : (g : Γ) ^ 3 = 1 := by
    have := congrArg (fun x : ↥E => (x : Γ)) hg3
    simpa using this
  have hgodd : (orderOf (g : Γ)).Coprime 2 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hg3') (by decide)
  have hgop : (g : Γ) ∈ opResidual 2 (M.blockSub p g) :=
    mem_opResidual_of_coprime g_mem_blockSub hgodd
  have hwop : ∀ w ∈ M.wSub p, w ∈ opResidual 2 (M.blockSub p g) := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := exists_commutator_eq hp hgd hw
    have h1 : u * (g : Γ) * u⁻¹ ∈ opResidual 2 (M.blockSub p g) := by
      refine mem_opResidual_of_coprime ?_ ?_
      · exact (M.blockSub p g).mul_mem ((M.blockSub p g).mul_mem (wSub_le_blockSub hu)
          g_mem_blockSub) ((M.blockSub p g).inv_mem (wSub_le_blockSub hu))
      · have h2 : u * (g : Γ) * u⁻¹ = (MulAut.conj u) (g : Γ) := by simp [MulAut.conj_apply]
        rw [h2, MulEquiv.orderOf_eq]
        exact hgodd
    have h3 : (g : Γ) * u * (g : Γ)⁻¹ * u⁻¹ = (g : Γ) * (u * (g : Γ) * u⁻¹)⁻¹ := by group
    rw [h3]
    exact (opResidual 2 (M.blockSub p g)).mul_mem hgop ((opResidual 2 _).inv_mem h1)
  intro x hx
  obtain ⟨w, hw, k, rfl⟩ := (mem_blockSub_iff hp hgd).1 hx
  exact (opResidual 2 _).mul_mem (hwop w hw) ((opResidual 2 _).zpow_mem hgop k)

theorem sq_eq_one_of_mem_W {w : Γ} (hw : w ∈ M.W) : w ^ 2 = 1 := by
  apply congrArg Subtype.val (M.βe.injective _ : (⟨w, hw⟩ : ↥M.W) ^ 2 = 1)
  rw [map_pow, map_one]
  apply vcoord_ext
  intro j
  rw [pow_two, vcoord_mul, vcoord_one]
  exact CharTwo.add_self_eq_zero _

theorem mem_setStab_triSet_of_mem_normalizer (hp : Function.Injective p) {s : Equiv.Perm (Fin n)}
    (hs : s ∈ Subgroup.normalizer (Subgroup.zpowers (triCyc p) : Set (Equiv.Perm (Fin n)))) :
    s ∈ setStab (triSet p) := by
  have key : ∀ s ∈ Subgroup.normalizer (Subgroup.zpowers (triCyc p) :
      Set (Equiv.Perm (Fin n))), ∀ j ∈ triSet p, s j ∈ triSet p := by
    intro s hs j hj
    by_contra hsj
    have hd : triCyc p ∈ Subgroup.zpowers (triCyc p) := Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
      ((Subgroup.mem_normalizer_iff.1 hs _).1 hd)
    have h1 : (s * triCyc p * s⁻¹) (s j) = s (triCyc p j) := by simp
    have h2 : triCyc p j ≠ j := by
      obtain ⟨i, rfl⟩ := mem_triSet.1 hj
      rw [triCyc_apply hp]
      exact fun h => by
        have := hp h
        fin_cases i <;> simp at this
    have h3 : s (triCyc p j) ≠ s j := fun h => h2 (s.injective h)
    rw [← hk] at h1
    have h4 : (triCyc p ^ k) (s j) = s j := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
      (triCyc_apply_of_notMem hsj) k
    exact h3 (h1.symm.trans h4)
  rw [mem_setStab]
  intro j
  refine ⟨fun hj => ?_, fun hj => key s hs j hj⟩
  by_contra hjn
  apply hjn
  have := key s⁻¹ ((Subgroup.normalizer _).inv_mem hs) _ hj
  simpa using this

theorem conj_blockSub_mem {B : Subgroup Γ} (hBE : B ≤ Subgroup.normalizer (E : Set Γ))
    (hBW : B ≤ Subgroup.normalizer (M.W : Set Γ)) (S : ↥B →* Equiv.Perm (Fin n))
    (hS : ∀ (y : ↥B) (w : ↥M.W) (hw : (y : Γ) * w * (y : Γ)⁻¹ ∈ M.W),
      M.βe ⟨(y : Γ) * w * (y : Γ)⁻¹, hw⟩ = coreAct n (S y) (M.βe w))
    (hSd : ∀ y : ↥B, S y ∈ Subgroup.normalizer
      (Subgroup.zpowers (triCyc p) : Set (Equiv.Perm (Fin n))))
    (hp : Function.Injective p) {g : ↥E} (hg3 : g ^ 3 = 1) (hgd : M.Ψ g = triCyc p) {y : Γ}
    (hy : y ∈ B) {x : Γ} (hx : x ∈ M.blockSub p g) : y * x * y⁻¹ ∈ M.blockSub p g := by
  set yB : ↥B := ⟨y, hy⟩ with hyB
  have hs : S yB ∈ setStab (triSet p) := mem_setStab_triSet_of_mem_normalizer hp (hSd yB)
  have hyW : y ∈ Subgroup.normalizer (M.W : Set Γ) := hBW hy
  have hw : ∀ w ∈ M.wSub p, y * w * y⁻¹ ∈ M.wSub p := by
    intro w hw
    obtain ⟨hwW, hwv⟩ := hw
    have hW' : y * w * y⁻¹ ∈ M.W := (Subgroup.mem_normalizer_iff.mp hyW w).mp hwW
    refine ⟨hW', ?_⟩
    have := hS yB ⟨w, hwW⟩ hW'
    rw [this]
    exact coreAct_mem_suppSub hs hwv
  have hyg : y * (g : Γ) * y⁻¹ ∈ M.blockSub p g := by
    have he' : y * (g : Γ) * y⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hBE hy) g).mp g.2
    have h1 := M.Ψ_conj hyW (s := S yB) (fun w hw' => hS yB w hw') g he'
    have h2 : M.Ψ ⟨y * (g : Γ) * y⁻¹, he'⟩ ∈ Subgroup.zpowers (triCyc p) := by
      rw [h1, hgd]
      exact (Subgroup.mem_normalizer_iff.1 (hSd yB) _).1 (Subgroup.mem_zpowers _)
    have h3 : (⟨y * (g : Γ) * y⁻¹, he'⟩ : ↥E) ^ 3 = 1 := by
      apply Subtype.ext
      have hg3' : (g : Γ) ^ 3 = 1 := by
        have := congrArg (fun x : ↥E => (x : Γ)) hg3
        simpa using this
      show (y * (g : Γ) * y⁻¹) ^ 3 = 1
      rw [conj_pow, hg3']
      group
    exact mem_blockSub_of_cube_eq_one hp hg3 hgd _ h2 h3
  obtain ⟨w, hwS, k, rfl⟩ := (mem_blockSub_iff hp hgd).1 hx
  have h4 : y * (w * (g : Γ) ^ k) * y⁻¹ = (y * w * y⁻¹) * (y * (g : Γ) * y⁻¹) ^ k := by
    rw [conj_zpow]
    group
  rw [h4]
  exact (M.blockSub p g).mul_mem (wSub_le_blockSub (hw w hwS))
    ((M.blockSub p g).zpow_mem hyg k)

theorem commutator_blockSub_eq {B : Subgroup Γ} (hBE : B ≤ Subgroup.normalizer (E : Set Γ))
    (hBW : B ≤ Subgroup.normalizer (M.W : Set Γ)) (S : ↥B →* Equiv.Perm (Fin n))
    (hS : ∀ (y : ↥B) (w : ↥M.W) (hw : (y : Γ) * w * (y : Γ)⁻¹ ∈ M.W),
      M.βe ⟨(y : Γ) * w * (y : Γ)⁻¹, hw⟩ = coreAct n (S y) (M.βe w))
    (hSd : ∀ y : ↥B, S y ∈ Subgroup.normalizer
      (Subgroup.zpowers (triCyc p) : Set (Equiv.Perm (Fin n))))
    (hp : Function.Injective p) {g : ↥E} (hg3 : g ^ 3 = 1) (hgd : M.Ψ g = triCyc p)
    (hy₀ : ∃ y₀ : ↥B, S y₀ = Equiv.swap (p 0) (p 2)) :
    ⁅M.blockSub p g, B⁆ = M.blockSub p g := by
  classical
  obtain ⟨y₀B, hy₀⟩ := hy₀
  set y₀ : Γ := (y₀B : Γ) with hy₀def
  have hy₀B : y₀ ∈ B := y₀B.2
  have hyW : y₀ ∈ Subgroup.normalizer (M.W : Set Γ) := hBW hy₀B
  set N₀ : Subgroup Γ := ⁅M.blockSub p g, B⁆ with hN₀
  have hFnorm : M.blockSub p g ≤ Subgroup.normalizer (N₀ : Set Γ) :=
    Subgroup.normalizer_commutator_ge_left _ _
  have hle : N₀ ≤ M.blockSub p g := by
    rw [hN₀, Subgroup.commutator_le]
    intro f hf y hy
    have h1 := conj_blockSub_mem hBE hBW S hS hSd hp hg3 hgd hy ((M.blockSub p g).inv_mem hf)
    have : ⁅f, y⁆ = f * (y * f⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact (M.blockSub p g).mul_mem hf h1
  have hg0 : (g : Γ) ∈ M.blockSub p g := g_mem_blockSub
  have hs₀ : ∀ (w : ↥M.W) (hw : y₀ * (w : Γ) * y₀⁻¹ ∈ M.W),
      M.βe ⟨y₀ * (w : Γ) * y₀⁻¹, hw⟩ = coreAct n (Equiv.swap (p 0) (p 2)) (M.βe w) := by
    intro w hw
    have := hS y₀B w hw
    rwa [hy₀] at this
  have hcomm : ∀ w : ↥M.W, ∃ hc : ⁅(w : Γ), y₀⁆ ∈ M.W,
      M.βe ⟨⁅(w : Γ), y₀⁆, hc⟩ = M.βe w * coreAct n (Equiv.swap (p 0) (p 2)) (M.βe w) := by
    intro w
    have hc1 : y₀ * (w : Γ)⁻¹ * y₀⁻¹ ∈ M.W := by
      have := (Subgroup.mem_normalizer_iff.mp hyW ((w⁻¹ : ↥M.W) : Γ)).mp (w⁻¹).2
      simpa using this
    have hc : ⁅(w : Γ), y₀⁆ ∈ M.W := by
      have h1 : ⁅(w : Γ), y₀⁆ = (w : Γ) * (y₀ * (w : Γ)⁻¹ * y₀⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [h1]
      exact M.W.mul_mem w.2 hc1
    refine ⟨hc, ?_⟩
    have h2 : (⟨⁅(w : Γ), y₀⁆, hc⟩ : ↥M.W) = w * ⟨y₀ * (w : Γ)⁻¹ * y₀⁻¹, hc1⟩ := by
      apply Subtype.ext
      show ⁅(w : Γ), y₀⁆ = (w : Γ) * (y₀ * (w : Γ)⁻¹ * y₀⁻¹)
      simp only [commutatorElement_def]
      group
    have h3 : (⟨y₀ * (w : Γ)⁻¹ * y₀⁻¹, hc1⟩ : ↥M.W) = ⟨y₀ * ((w⁻¹ : ↥M.W) : Γ) * y₀⁻¹, by
        simpa using hc1⟩ := rfl
    rw [h2, map_mul, h3, hs₀ (w⁻¹) (by simpa using hc1), map_inv]
    congr 2
    exact coreMod_inv_eq _
  have h01 : p 0 ≠ p 1 := fun h => by simpa using hp h
  have h02 : p 0 ≠ p 2 := fun h => by simpa using hp h
  have h12 : p 1 ≠ p 2 := fun h => by simpa using hp h
  have hpair : ∀ a b : Fin 3, pairVec (p a) (p b) ∈ suppSub (triSet p) := fun a b =>
    pairVec_mem_suppSub (p_mem_triSet a) (p_mem_triSet b)
  obtain ⟨w₁, hw₁W, hw₁S, hw₁β⟩ := M.exists_wSub_of_mem_suppSub (hpair 0 1)
  have hs₀p0 : Equiv.swap (p 0) (p 2) (p 0) = p 2 := Equiv.swap_apply_left _ _
  have hs₀p1 : Equiv.swap (p 0) (p 2) (p 1) = p 1 :=
    Equiv.swap_apply_of_ne_of_ne h01.symm h12
  obtain ⟨hc₁, hc₁β⟩ := hcomm ⟨w₁, hw₁W⟩
  have hc₁β' : M.βe ⟨⁅w₁, y₀⁆, hc₁⟩ = pairVec (p 0) (p 2) := by
    rw [hc₁β, hw₁β, coreAct_pairVec, hs₀p0, hs₀p1, pairVec_comm (p 0) (p 1),
      pairVec_comm (p 2) (p 1)]
    exact pairVec_mul (p 1) (p 0) (p 2)
  have hu₀₂N : ⁅w₁, y₀⁆ ∈ N₀ :=
    Subgroup.commutator_mem_commutator (wSub_le_blockSub hw₁S) hy₀B
  have hgN : ∀ (u : Γ), u ∈ N₀ → (g : Γ) * u * (g : Γ)⁻¹ ∈ N₀ := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hFnorm hg0) u).mp hu
  have hdp : ∀ a b : Fin 3, coreAct n (triCyc p) (pairVec (p a) (p b)) =
      pairVec (p (a + 1)) (p (b + 1)) := fun a b => by
    rw [coreAct_pairVec, triCyc_apply hp, triCyc_apply hp]
  have hconjg : ∀ (u : Γ) (hu : u ∈ M.W), (g : Γ) * u * (g : Γ)⁻¹ ∈ M.W ∧
      ∀ hu' : (g : Γ) * u * (g : Γ)⁻¹ ∈ M.W,
        M.βe ⟨(g : Γ) * u * (g : Γ)⁻¹, hu'⟩ = coreAct n (triCyc p) (M.βe ⟨u, hu⟩) := by
    intro u hu
    refine ⟨M.conj_mem g hu, fun hu' => ?_⟩
    have := M.βe_conjW g ⟨u, hu⟩
    rw [hgd] at this
    exact this
  have hu₁W := (hconjg _ hc₁).1
  have hu₁β : M.βe ⟨(g : Γ) * ⁅w₁, y₀⁆ * (g : Γ)⁻¹, hu₁W⟩ = pairVec (p 1) (p 0) := by
    rw [(hconjg _ hc₁).2 hu₁W, hc₁β', hdp 0 2]
    rfl
  have hu₁N := hgN _ hu₀₂N
  have hu₂W := (hconjg _ hu₁W).1
  have hu₂β : M.βe ⟨(g : Γ) * ((g : Γ) * ⁅w₁, y₀⁆ * (g : Γ)⁻¹) * (g : Γ)⁻¹, hu₂W⟩ =
      pairVec (p 2) (p 1) := by
    rw [(hconjg _ hu₁W).2 hu₂W, hu₁β, hdp 1 0]
    rfl
  have hu₂N := hgN _ hu₁N
  have hwN : ∀ w ∈ M.wSub p, w ∈ N₀ := by
    intro w hw
    obtain ⟨hwW, hwv⟩ := hw
    rcases eq_one_or_pairVec hp hwv with h | h | h | h
    · have : w = 1 := M.eq_of_βe_eq hwW M.W.one_mem (by rw [h]; exact (map_one M.βe).symm)
      rw [this]
      exact N₀.one_mem
    · have : w = (g : Γ) * ⁅w₁, y₀⁆ * (g : Γ)⁻¹ :=
        M.eq_of_βe_eq hwW hu₁W (by rw [h, hu₁β, pairVec_comm])
      rw [this]
      exact hu₁N
    · have : w = (g : Γ) * ((g : Γ) * ⁅w₁, y₀⁆ * (g : Γ)⁻¹) * (g : Γ)⁻¹ :=
        M.eq_of_βe_eq hwW hu₂W (by rw [h, hu₂β, pairVec_comm])
      rw [this]
      exact hu₂N
    · have : w = ⁅w₁, y₀⁆ := M.eq_of_βe_eq hwW hc₁ (by rw [h, hc₁β'])
      rw [this]
      exact hu₀₂N
  have he₀N : ⁅(g : Γ), y₀⁆ ∈ N₀ := Subgroup.commutator_mem_commutator hg0 hy₀B
  have he₀F := hle he₀N
  have he₀E : ⁅(g : Γ), y₀⁆ ∈ E := blockSub_le_E hp hgd he₀F
  have hΨe₀ : M.Ψ ⟨⁅(g : Γ), y₀⁆, he₀E⟩ = triCyc p ^ 2 := by
    have hmem : y₀ * ((g⁻¹ : ↥E) : Γ) * y₀⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hBE hy₀B) _).mp (g⁻¹).2
    have h1 := M.Ψ_conj hyW (s := Equiv.swap (p 0) (p 2)) hs₀ (g⁻¹) hmem
    have h2 : (⟨⁅(g : Γ), y₀⁆, he₀E⟩ : ↥E) = g * ⟨y₀ * ((g⁻¹ : ↥E) : Γ) * y₀⁻¹, hmem⟩ := by
      apply Subtype.ext
      show ⁅(g : Γ), y₀⁆ = (g : Γ) * (y₀ * ((g⁻¹ : ↥E) : Γ) * y₀⁻¹)
      simp only [commutatorElement_def, Subgroup.coe_inv]
      group
    have h3 : Equiv.swap (p 0) (p 2) * (triCyc p)⁻¹ * (Equiv.swap (p 0) (p 2))⁻¹ = triCyc p := by
      have := swap_mul_triCyc_mul_swap hp
      calc Equiv.swap (p 0) (p 2) * (triCyc p)⁻¹ * (Equiv.swap (p 0) (p 2))⁻¹ =
          (Equiv.swap (p 0) (p 2) * triCyc p * Equiv.swap (p 0) (p 2))⁻¹ := by
            simp [mul_inv_rev, Equiv.swap_inv, mul_assoc]
        _ = triCyc p := by rw [this, inv_inv]
    rw [h2, map_mul, h1, map_inv, hgd, h3, pow_two]
  obtain ⟨w, hw, k, hek⟩ := (mem_blockSub_iff hp hgd).1 he₀F
  have hΨk : M.Ψ ⟨⁅(g : Γ), y₀⁆, he₀E⟩ = triCyc p ^ k := by
    have h := Ψ_mul_zpow hgd hw k (hek ▸ he₀E)
    have e : (⟨⁅(g : Γ), y₀⁆, he₀E⟩ : ↥E) = ⟨w * (g : Γ) ^ k, hek ▸ he₀E⟩ :=
      Subtype.ext hek
    rw [e]
    exact h
  have hk2 : (3 : ℤ) ∣ k - 2 := by
    apply three_dvd_of_triCyc_zpow_eq_one hp
    have h : triCyc p ^ k = triCyc p ^ (2 : ℤ) := by
      rw [← hΨk, hΨe₀, zpow_ofNat]
    rw [zpow_sub, h, mul_inv_cancel]
  have hgk : g ^ k = g ^ (2 : ℤ) := by
    have h5 : g ^ (k - 2) = 1 := zpow_eq_one_of_dvd hg3 hk2
    rw [zpow_sub] at h5
    exact mul_inv_eq_one.mp h5
  have hg3' : (g : Γ) ^ 3 = 1 := by
    have := congrArg (fun x : ↥E => (x : Γ)) hg3
    simpa using this
  have hg2N : (g : Γ) ^ 2 ∈ N₀ := by
    have hgk' : (g : Γ) ^ k = (g : Γ) ^ (2 : ℤ) := by
      have := congrArg (fun x : ↥E => (x : Γ)) hgk
      simpa using this
    have h6 : (g : Γ) ^ 2 = w⁻¹ * ⁅(g : Γ), y₀⁆ := by
      rw [hek, hgk']
      group
    rw [h6]
    exact N₀.mul_mem (N₀.inv_mem (hwN w hw)) he₀N
  have hgN₀ : (g : Γ) ∈ N₀ := by
    have h4 : (g : Γ) = ((g : Γ) ^ 2) ^ 2 := by
      calc (g : Γ) = (g : Γ) * (g : Γ) ^ 3 := by rw [hg3', mul_one]
        _ = ((g : Γ) ^ 2) ^ 2 := by group
    rw [h4]
    exact N₀.pow_mem hg2N 2
  apply le_antisymm hle
  intro x hx
  obtain ⟨w', hw', k', rfl⟩ := (mem_blockSub_iff hp hgd).1 hx
  exact N₀.mul_mem (hwN w' hw') (N₀.zpow_mem hgN₀ k')

end AltSetup

end CFSG.CGT.PushingUpLit.BHS6
