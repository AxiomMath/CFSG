module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL5

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even
open scoped Pointwise


theorem conj_closure_mem {G : Type*} [Group G] (S : Set G) (w : G)
    (hS : ∀ x ∈ S, w * x * w⁻¹ ∈ Subgroup.closure S) :
    ∀ v ∈ Subgroup.closure S, w * v * w⁻¹ ∈ Subgroup.closure S := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simpa using one_mem _
  | mul x y _ _ hx hy =>
    have e : w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
    rw [e]; exact mul_mem hx hy
  | inv x _ hx =>
    have e : w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem hx

theorem normalizer_conj_of_commute {G : Type*} [Group G] (U : Subgroup G) [Finite U] {w x : G}
    (hx : x ∈ Subgroup.normalizer (U : Set G)) (hw : ∀ u ∈ U, Commute w u) :
    w⁻¹ * x * w ∈ Subgroup.normalizer (U : Set G) := by
  refine mem_normalizer_of_forall_conj_mem U fun u hu => ?_
  have h1 : w * u * w⁻¹ = u := by rw [(hw u hu).eq, mul_inv_cancel_right]
  have hu' : x * u * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hx u).1 hu
  have h2 : w * (x * u * x⁻¹) * w⁻¹ = x * u * x⁻¹ := by
    rw [(hw _ hu').eq, mul_inv_cancel_right]
  have e : w⁻¹ * x * w * u * (w⁻¹ * x * w)⁻¹ = x * u * x⁻¹ := by
    calc w⁻¹ * x * w * u * (w⁻¹ * x * w)⁻¹ = w⁻¹ * (x * (w * u * w⁻¹) * x⁻¹) * w := by group
      _ = w⁻¹ * (x * u * x⁻¹) * w := by rw [h1]
      _ = x * u * x⁻¹ := by
        have h3 := congrArg (fun z => w⁻¹ * z * w) h2
        simpa [mul_assoc] using h3.symm
  rw [e]; exact hu'

section Borel

variable {K : Type} [Field K] [Finite K]

theorem xUnit_mem_leviUnip {J : Set (Fin Tag.D4.rank)} {j : Fin Tag.D4.rank} (hj : j ∈ J) (c : K) :
    xUnit Tag.D4 K j c ∈ parabolicLeviUnipotent Tag.D4 K J := by
  have hx : xUnit Tag.D4 K j c ∈ rootSubgroup Tag.D4 K (Pi.single j 1) := by
    rw [← pinnedX_single]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  refine Subgroup.mem_iSup_of_mem (Pi.single j 1) (Subgroup.mem_iSup_of_mem ?_ hx)
  refine ⟨⟨isRoot_single Tag.D4 j, fun i hi => ?_⟩, isRoot_single Tag.D4 j, ?_⟩
  · have : i ≠ j := fun h => hi (h ▸ hj)
    simp [Pi.single_apply, this]
  · rw [height_single]; exact one_pos

theorem mem_borel_of_normalizes {J : Set (Fin Tag.D4.rank)}
    (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank))) {w : ModGL Tag.D4 K}
    (hw : w ∈ parabolicSubgroup Tag.D4 K J)
    (hwU : ∀ j ∈ J, w ∈ Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K))) :
    w ∈ borelGroup Tag.D4 K := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  have hwC : w ∈ adjointGroup Tag.D4 K := parabolicSubgroup_le_adjointGroup _ _ _ hw
  have hV : ∀ v ∈ parabolicLeviUnipotent Tag.D4 K J,
      w * v * w⁻¹ ∈ parabolicLeviUnipotent Tag.D4 K J := by
    intro v hv
    have hcl := conj_closure_mem {x | ∃ j ∈ J, ∃ c : K, x = xUnit Tag.D4 K j c} w (by
      rintro _ ⟨j, hj, c, rfl⟩
      have h1 := (Subgroup.mem_normalizer_iff.1 (hwU j hj) (xUnit Tag.D4 K j c)).1
        (xUnit_mem_Uk j c)
      obtain ⟨c', hc'⟩ := mem_Uk.1 h1
      exact Subgroup.subset_closure ⟨j, hj, c', hc'.symm⟩) v (leviUnip_le hJ hv)
    exact (Subgroup.closure_le _).2 (by
      rintro _ ⟨j, hj, c, rfl⟩; exact xUnit_mem_leviUnip hj c) hcl
  have hU : ∀ u ∈ posUnipotent Tag.D4 K, w * u * w⁻¹ ∈ posUnipotent Tag.D4 K := by
    intro u hu
    have hu' : u ∈ (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) *
        (parabolicLeviUnipotent Tag.D4 K J : Set (ModGL Tag.D4 K)) := by
      rw [← posUnipotent_eq_mul_parabolic J]; exact hu
    obtain ⟨q, hq, v, hv, rfl⟩ := hu'
    have hq' : w * q * w⁻¹ ∈ parabolicRadical Tag.D4 K J :=
      (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical J hw) q).1 hq
    have e : w * (q * v) * w⁻¹ = (w * q * w⁻¹) * (w * v * w⁻¹) := by group
    rw [e]
    have hmem : (w * q * w⁻¹) * (w * v * w⁻¹) ∈
        (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) *
          (parabolicLeviUnipotent Tag.D4 K J : Set (ModGL Tag.D4 K)) := ⟨_, hq', _, hV v hv, rfl⟩
    rw [← posUnipotent_eq_mul_parabolic J] at hmem
    exact hmem
  have hN : w ∈ Subgroup.normalizer (posUnipotent Tag.D4 K : Set (ModGL Tag.D4 K)) :=
    mem_normalizer_of_forall_conj_mem (posUnipotent Tag.D4 K) hU
  rw [← (borel_self_normalizers Tag.D4 K).1]
  exact ⟨hwC, hN⟩

theorem Q_le_borel (J : Set (Fin Tag.D4.rank)) :
    parabolicRadical Tag.D4 K J ≤ borelGroup Tag.D4 K :=
  (parabolicRadical_le_posUnipotent J).trans le_sup_right

theorem conj_Q_mem (J : Set (Fin Tag.D4.rank)) {s q : ModGL Tag.D4 K}
    (hs : s ∈ parabolicSubgroup Tag.D4 K J) (hq : q ∈ parabolicRadical Tag.D4 K J) :
    s⁻¹ * q * s ∈ parabolicRadical Tag.D4 K J := by
  have := (semiDirect_levi (K := K) J).Q_norm s⁻¹ (inv_mem hs) q hq
  simpa using this

end Borel

section Key

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

variable {J : Set (Fin Tag.D4.rank)} {g : ModGL Tag.D4 K} {a : Fin Tag.D4.rank → Kˣ}
  {σ : K ≃+* K} {ε : ℕ}

theorem key_of_split (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K J, phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K J)
    {y s : ModGL Tag.D4 K} (hy : y ∈ parabolicSubgroup Tag.D4 K J) (hs : s ∈ parabolicLevi Tag.D4 K J)
    (h1 : ∀ j ∈ J, s⁻¹ * (semiDirect_levi (K := K) J).proj y * s ∈
      Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K)))
    (h2 : ∀ j ∈ J, s⁻¹ * (semiDirect_levi (K := K) J).bar (phiG g a σ ε) s ∈
      Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K))) :
    s⁻¹ * y * s ∈ borelGroup Tag.D4 K ∧ s⁻¹ * phiG g a σ ε s ∈ borelGroup Tag.D4 K := by
  have hS := semiDirect_levi (K := K) J
  have hsP : s ∈ parabolicSubgroup Tag.D4 K J := hS.M_le hs
  have hsP' : s⁻¹ ∈ parabolicSubgroup Tag.D4 K J := inv_mem hsP
  constructor
  · have hmM : hS.proj y ∈ parabolicLevi Tag.D4 K J := hS.proj_mem hy
    have hq : y * (hS.proj y)⁻¹ ∈ parabolicRadical Tag.D4 K J := hS.mul_proj_inv_mem hy
    have e : s⁻¹ * y * s = (s⁻¹ * (y * (hS.proj y)⁻¹) * s) * (s⁻¹ * hS.proj y * s) := by group
    rw [e]
    refine mul_mem (Q_le_borel J (conj_Q_mem J hsP hq)) (mem_borel_of_normalizes hJ ?_ h1)
    exact mul_mem (mul_mem hsP' (hS.M_le hmM)) hsP
  · have hφs : phiG g a σ ε s ∈ parabolicSubgroup Tag.D4 K J := hφP s hsP
    have hmM : hS.proj (phiG g a σ ε s) ∈ parabolicLevi Tag.D4 K J := hS.proj_mem hφs
    have hq : phiG g a σ ε s * (hS.proj (phiG g a σ ε s))⁻¹ ∈ parabolicRadical Tag.D4 K J :=
      hS.mul_proj_inv_mem hφs
    have e : s⁻¹ * phiG g a σ ε s = (s⁻¹ * (phiG g a σ ε s * (hS.proj (phiG g a σ ε s))⁻¹) * s) *
        (s⁻¹ * hS.proj (phiG g a σ ε s)) := by group
    rw [e]
    refine mul_mem (Q_le_borel J (conj_Q_mem J hsP hq)) (mem_borel_of_normalizes hJ ?_ h2)
    exact mul_mem hsP' (hS.M_le hmM)

theorem bar_normalizes (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hg : g ∈ borelGroup Tag.D4 K) (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J)
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K J, phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K J)
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K J, phiG g a σ ε q ∈ parabolicRadical Tag.D4 K J)
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K J, phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {k : Fin Tag.D4.rank} (hk : k ∈ J) {x : ModGL Tag.D4 K} (hx : x ∈ parabolicLevi Tag.D4 K J)
    (hbx : (semiDirect_levi (K := K) J).bar (phiG g a σ ε) x = x)
    (hxk : x ∈ Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K))) :
    x ∈ Subgroup.normalizer (Uk K ((d4Rho ^ ε) k) : Set (ModGL Tag.D4 K)) := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  have hS := semiDirect_levi (K := K) J
  refine mem_normalizer_of_forall_conj_mem _ fun u hu => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := bar_Uk_surj hJ hg hJρ hφP hφQ hφ3 hk u hu
  have hx₀' : x * x₀ * x⁻¹ ∈ Uk K k := (Subgroup.mem_normalizer_iff.1 hxk x₀).1 hx₀
  have hx₀M : x₀ ∈ parabolicLevi Tag.D4 K J := Lk_le_levi hk (Uk_le_Lk _ hx₀)
  have := hS.bar_conj (phiG g a σ ε) hφP (hS.M_le hx) (hS.M_le hx₀M)
  rw [hbx] at this
  rw [← this]
  exact bar_Uk_le hJ hg hJρ hk hx₀'

theorem commute_Lk {i j : Fin Tag.D4.rank} (hi : i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hj : j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) (hij : i ≠ j) {x x' : ModGL Tag.D4 K}
    (hx : x ∈ Lk K i) (hx' : x' ∈ Lk K j) : Commute x x' := by
  obtain ⟨X, rfl⟩ := mem_Lk.1 hx
  obtain ⟨Y, rfl⟩ := mem_Lk.1 hx'
  exact commute_rho_outer hi hj hij X Y

theorem rho_cycle {ε : ℕ} (hε : ε = 1 ∨ ε = 2) {k j : Fin Tag.D4.rank}
    (hk : k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) (hj : j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) :
    (d4Rho ^ ε) k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ∧ (d4Rho ^ ε) k ≠ k ∧
      (d4Rho ^ ε) ((d4Rho ^ ε) k) ≠ k ∧ (d4Rho ^ ε) ((d4Rho ^ ε) k) ≠ (d4Rho ^ ε) k ∧
      (d4Rho ^ ε) ((d4Rho ^ ε) ((d4Rho ^ ε) k)) = k ∧
      (j = k ∨ j = (d4Rho ^ ε) k ∨ j = (d4Rho ^ ε) ((d4Rho ^ ε) k)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk hj ⊢
  rcases hε with rfl | rfl <;> rcases hk with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    decide

theorem levi_key_three (hK2 : ringChar K ≠ 2) (hg : g ∈ borelGroup Tag.D4 K) (hε : ε = 1 ∨ ε = 2)
    (hJρ : ∀ i, i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ↔
      (d4Rho ^ ε) i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {y : ModGL Tag.D4 K} (hy : y ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hy2 : y * y = 1) (hφy : phiG g a σ ε y = y) :
    ∃ s ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      s⁻¹ * y * s ∈ borelGroup Tag.D4 K ∧ s⁻¹ * phiG g a σ ε s ∈ borelGroup Tag.D4 K := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  set J : Set (Fin Tag.D4.rank) := {0, 1, 3} with hJdef
  have hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)) := Or.inr rfl
  have hS := semiDirect_levi (K := K) J
  have hmM : hS.proj y ∈ parabolicLevi Tag.D4 K J := hS.proj_mem hy
  have hmP : hS.proj y ∈ parabolicSubgroup Tag.D4 K J := hS.M_le hmM
  have hm2 : hS.proj y * hS.proj y = 1 := by
    rw [← hS.proj_mul hy hy, hy2, hS.proj_of_mem_M (one_mem _)]
  have hbarm : hS.bar (phiG g a σ ε) (hS.proj y) = hS.proj y := by
    rw [hS.bar_proj _ hφP hφQ hy]
    unfold IsSemiDirect.bar
    rw [hφy]
  obtain ⟨k₀, hk₀, e, he⟩ := split_three hK2 hmM hm2
  obtain ⟨hk₁, hne1, hne2, hne12, hcyc, -⟩ := rho_cycle hε hk₀ hk₀
  have hk₁J : (d4Rho ^ ε) k₀ ∈ J := hk₁
  have hk₂J : (d4Rho ^ ε) ((d4Rho ^ ε) k₀) ∈ J := (hJρ _).1 hk₁J
  have hbar_mul : ∀ {x x' : ModGL Tag.D4 K}, x ∈ parabolicSubgroup Tag.D4 K J →
      x' ∈ parabolicSubgroup Tag.D4 K J →
      hS.bar (phiG g a σ ε) (x * x') = hS.bar (phiG g a σ ε) x * hS.bar (phiG g a σ ε) x' :=
    fun hx hx' => hS.bar_mul _ hφP hx hx'
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : ModGL Tag.D4 K, t₀ = ρ k₀ e := ⟨_, rfl⟩
  obtain ⟨t₁, ht₁def⟩ : ∃ t₁ : ModGL Tag.D4 K, t₁ = hS.bar (phiG g a σ ε) t₀ := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂def⟩ : ∃ t₂ : ModGL Tag.D4 K, t₂ = hS.bar (phiG g a σ ε) t₁ := ⟨_, rfl⟩
  have ht₀ : t₀ ∈ Lk K k₀ := ⟨e, ht₀def.symm⟩
  have ht₁ : t₁ ∈ Lk K ((d4Rho ^ ε) k₀) := by
    rw [ht₁def]; exact bar_Lk_le hJ hg hJρ hφP hk₀ ht₀
  have ht₂ : t₂ ∈ Lk K ((d4Rho ^ ε) ((d4Rho ^ ε) k₀)) := by
    rw [ht₂def]; exact bar_Lk_le hJ hg hJρ hφP hk₁J ht₁
  have hbar3 : hS.bar (phiG g a σ ε) t₂ = t₀ := by
    rw [ht₂def, ht₁def]
    exact hS.bar_bar_bar _ hφP hφQ hφ3 (Lk_le_levi hk₀ ht₀)
  have ht₀M : t₀ ∈ parabolicLevi Tag.D4 K J := Lk_le_levi hk₀ ht₀
  have ht₁M : t₁ ∈ parabolicLevi Tag.D4 K J := Lk_le_levi hk₁J ht₁
  have ht₂M : t₂ ∈ parabolicLevi Tag.D4 K J := Lk_le_levi hk₂J ht₂
  have c01 : Commute t₀ t₁ := commute_Lk hk₀ hk₁ (Ne.symm hne1) ht₀ ht₁
  have c02 : Commute t₀ t₂ := commute_Lk hk₀ hk₂J (Ne.symm hne2) ht₀ ht₂
  have c12 : Commute t₁ t₂ := commute_Lk hk₁ hk₂J (Ne.symm hne12) ht₁ ht₂
  have hsM : t₀ * t₁ * t₂ ∈ parabolicLevi Tag.D4 K J := mul_mem (mul_mem ht₀M ht₁M) ht₂M
  have hsP : t₀ * t₁ * t₂ ∈ parabolicSubgroup Tag.D4 K J := hS.M_le hsM
  have hbs : hS.bar (phiG g a σ ε) (t₀ * t₁ * t₂) = t₀ * t₁ * t₂ := by
    rw [hbar_mul (hS.M_le (mul_mem ht₀M ht₁M)) (hS.M_le ht₂M), hbar_mul (hS.M_le ht₀M) (hS.M_le ht₁M),
      ← ht₁def, ← ht₂def, hbar3]
    calc t₁ * t₂ * t₀ = t₁ * (t₂ * t₀) := by group
      _ = t₁ * (t₀ * t₂) := by rw [c02.symm.eq]
      _ = (t₁ * t₀) * t₂ := by group
      _ = (t₀ * t₁) * t₂ := by rw [c01.symm.eq]
  have hnM : (t₀ * t₁ * t₂)⁻¹ * hS.proj y * (t₀ * t₁ * t₂) ∈ parabolicLevi Tag.D4 K J :=
    mul_mem (mul_mem (inv_mem hsM) hmM) hsM
  have hbn : hS.bar (phiG g a σ ε) ((t₀ * t₁ * t₂)⁻¹ * hS.proj y * (t₀ * t₁ * t₂)) =
      (t₀ * t₁ * t₂)⁻¹ * hS.proj y * (t₀ * t₁ * t₂) := by
    rw [hbar_mul (mul_mem (inv_mem hsP) hmP) hsP, hbar_mul (inv_mem hsP) hmP,
      hS.bar_inv _ hφP hsP, hbs, hbarm]
  have hn0 : (t₀ * t₁ * t₂)⁻¹ * hS.proj y * (t₀ * t₁ * t₂) ∈
      Subgroup.normalizer (Uk K k₀ : Set (ModGL Tag.D4 K)) := by
    have hme : t₀⁻¹ * hS.proj y * t₀ ∈ Subgroup.normalizer (Uk K k₀ : Set (ModGL Tag.D4 K)) := by
      refine mem_normalizer_of_forall_conj_mem _ fun u hu => ?_
      obtain ⟨c, rfl⟩ := mem_Uk.1 hu
      obtain ⟨c', hc'⟩ := he c
      rw [ht₀def, hc']
      exact xUnit_mem_Uk _ _
    have e1 : (t₀ * t₁ * t₂)⁻¹ * hS.proj y * (t₀ * t₁ * t₂) =
        (t₁ * t₂)⁻¹ * (t₀⁻¹ * hS.proj y * t₀) * (t₁ * t₂) := by group
    rw [e1]
    refine normalizer_conj_of_commute _ hme fun u hu => ?_
    exact (commute_Lk hk₁ hk₀ hne1 ht₁ (Uk_le_Lk _ hu)).mul_left
      (commute_Lk hk₂J hk₀ hne2 ht₂ (Uk_le_Lk _ hu))
  have hn1 := bar_normalizes hJ hg hJρ hφP hφQ hφ3 hk₀ hnM hbn hn0
  have hn2 := bar_normalizes hJ hg hJρ hφP hφQ hφ3 hk₁J hnM hbn hn1
  refine ⟨t₀ * t₁ * t₂, hsM, key_of_split hJ hφP hy hsM (fun j hj => ?_) (fun j hj => ?_)⟩
  · rcases (rho_cycle hε hk₀ hj).2.2.2.2.2 with rfl | rfl | rfl
    · exact hn0
    · exact hn1
    · exact hn2
  · rw [hbs, inv_mul_cancel]; exact one_mem _

end Key

end CFSG.LocalAnalysis.GLTheoremA
