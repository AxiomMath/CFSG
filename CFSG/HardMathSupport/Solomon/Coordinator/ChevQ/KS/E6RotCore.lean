module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6RotAlg
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6RotDefs
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_StructAct
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FamilyRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem closure_commute {G : Type*} [Group G] {s : Set G} (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∀ a ∈ Subgroup.closure s, ∀ b ∈ Subgroup.closure s, a * b = b * a := by
  have hcomm : Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.closure s : Set G) := by
    rw [Subgroup.centralizer_closure]
    refine (Subgroup.closure_le _).2 fun a ha => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact fun b hb => hc b hb a ha
  intro a ha b hb
  exact Subgroup.mem_centralizer_iff.1 (hcomm hb) a ha

variable {S : Type*} [Group S] {X : Type} [Group X] [Finite X]

def rotConj (ψ : S →* X) (x : X) (i : ℕ) : S →* X :=
  (MulAut.conj ((x ^ i)⁻¹)).toMonoidHom.comp ψ

theorem rotConj_apply (ψ : S →* X) (x : X) (i : ℕ) (s : S) :
    rotConj ψ x i s = (x ^ i)⁻¹ * ψ s * x ^ i := by
  simp only [rotConj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

theorem rotConj_zero (ψ : S →* X) (x : X) : rotConj ψ x 0 = ψ := by
  ext s
  simp [rotConj_apply]

theorem rotConj_injective {ψ : S →* X} (hψ : Function.Injective ψ) (x : X) (i : ℕ) :
    Function.Injective (rotConj ψ x i) := by
  intro a b h
  rw [rotConj_apply, rotConj_apply] at h
  apply hψ
  simpa using h

theorem rotConj_range (ψ : S →* X) (x : X) (i : ℕ) :
    (rotConj ψ x i).range = CFSG.Open.GLBConj (x ^ i) ψ.range := by
  rw [rotConj, MonoidHom.range_comp]
  rfl

theorem mem_rotConj_range (ψ : S →* X) (x : X) (i : ℕ) (a : X) :
    a ∈ CFSG.Open.GLBConj (x ^ i) ψ.range ↔ ∃ s, rotConj ψ x i s = a := by
  rw [← rotConj_range]
  exact MonoidHom.mem_range

structure RotSetup (B L : Subgroup X) (x : X) (ψ : S →* X) : Prop where
  elem : CFSG.Open.IsElemAbelian 3 B
  comp : CFSG.Open.IsComponentOf L ⊤
  xB : x ∈ B
  xn : x ∉ Subgroup.normalizer (L : Set X)
  inj : Function.Injective ψ
  range : ψ.range = L

namespace RotSetup

variable {B L : Subgroup X} {x : X} {ψ : S →* X} (h : RotSetup B L x ψ)

include h

theorem x_cube : x ^ 3 = 1 := h.elem.2 x h.xB

theorem cross_commute {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) (s s' : S) :
    rotConj ψ x i s * rotConj ψ x j s' = rotConj ψ x j s' * rotConj ψ x i s := by
  have hM : CFSG.Open.GLBConj (x ^ i) L ∈ i112Orbit B L := i112_gLBConj_mem_orbit (B.pow_mem h.xB i)
  have hN : CFSG.Open.GLBConj (x ^ j) L ∈ i112Orbit B L := i112_gLBConj_mem_orbit (B.pow_mem h.xB j)
  rcases i112_conj_eq_or_commute h.comp hM hN with he | hc
  · exact absurd (i112_conj_pow_injOn Nat.prime_three h.elem h.xB h.xn hi hj he) hij
  · refine hc _ ?_ _ ?_
    · rw [← h.range, ← rotConj_range]
      exact ⟨s, rfl⟩
    · rw [← h.range, ← rotConj_range]
      exact ⟨s', rfl⟩

end RotSetup

def rotComp : Fin 5 → ℕ := ![0, 1, 1, 2, 2]

def rotElt (d : RotData S) : Fin 5 → S := ![d.g₁ * d.g₂ ^ 2, d.g₁, d.g₂, d.g₁, d.g₂]

def rotGen (d : RotData S) (ψ : S →* X) (x : X) : Fin 5 → X :=
  fun i => rotConj ψ x (rotComp i) (rotElt d i)

theorem rotComp_lt (i : Fin 5) : rotComp i < 3 := by
  fin_cases i <;> simp [rotComp]

theorem rotElt_commute (d : RotData S) (i j : Fin 5) :
    rotElt d i * rotElt d j = rotElt d j * rotElt d i := by
  have hc : Commute d.g₁ d.g₂ := d.g_comm
  have hu1 : Commute (d.g₁ * d.g₂ ^ 2) d.g₁ := (Commute.refl d.g₁).mul_left (hc.symm.pow_left 2)
  have hu2 : Commute (d.g₁ * d.g₂ ^ 2) d.g₂ := hc.mul_left ((Commute.refl d.g₂).pow_left 2)
  fin_cases i <;> fin_cases j <;> simp only [rotElt] <;> first
    | rfl
    | exact (Commute.refl _).eq
    | exact hc.eq
    | exact hc.symm.eq
    | exact hu1.eq
    | exact hu1.symm.eq
    | exact hu2.eq
    | exact hu2.symm.eq

theorem zpow_u (d : RotData S) (n : ℤ) :
    (d.g₁ * d.g₂ ^ 2) ^ n = d.g₁ ^ n * d.g₂ ^ (2 * n) := by
  have hc : Commute d.g₁ (d.g₂ ^ 2) := (show Commute d.g₁ d.g₂ from d.g_comm).pow_right 2
  rw [hc.mul_zpow, zpow_mul, zpow_ofNat]

theorem commute_of_mul_mul_eq_one {G : Type*} [Group G] {a b c y : G} (h : a * (b * c) = 1)
    (hb : Commute y b) (hc : Commute y c) : Commute y a := by
  have : a = (b * c)⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [this]
  exact (hb.mul_right hc).inv_right

theorem mem_center_of_forall_commute {ψ' : S →* X} (hψ' : Function.Injective ψ') {s : S}
    (h : ∀ s' : S, ψ' s * ψ' s' = ψ' s' * ψ' s) : s ∈ Subgroup.center S := by
  rw [Subgroup.mem_center_iff]
  intro s'
  apply hψ'
  rw [map_mul, map_mul]
  exact (h s').symm

namespace RotSetup

variable {B L : Subgroup X} {x : X} {ψ : S →* X} (h : RotSetup B L x ψ)

include h

theorem rotGen_commute (d : RotData S) (i j : Fin 5) :
    rotGen d ψ x i * rotGen d ψ x j = rotGen d ψ x j * rotGen d ψ x i := by
  by_cases hij : rotComp i = rotComp j
  · simp only [rotGen]
    rw [hij, ← map_mul, ← map_mul, rotElt_commute d i j]
  · exact h.cross_commute (rotComp_lt i) (rotComp_lt j) hij _ _

theorem rotGen_rel (d : RotData S) (e : Fin 5 → ℤ)
    (hprod : (List.ofFn fun i => rotGen d ψ x i ^ e i).prod = 1) (i : Fin 5) : (3 : ℤ) ∣ e i := by
  have hexp : (List.ofFn fun i => rotGen d ψ x i ^ e i).prod =
      rotConj ψ x 0 ((d.g₁ * d.g₂ ^ 2) ^ e 0) *
        (rotConj ψ x 1 (d.g₁ ^ e 1 * d.g₂ ^ e 2) * rotConj ψ x 2 (d.g₁ ^ e 3 * d.g₂ ^ e 4)) := by
    simp [List.ofFn_succ, rotGen, rotComp, rotElt, map_zpow, map_mul, mul_assoc]
  rw [hexp] at hprod
  set a := rotConj ψ x 0 ((d.g₁ * d.g₂ ^ 2) ^ e 0) with ha
  set b := rotConj ψ x 1 (d.g₁ ^ e 1 * d.g₂ ^ e 2) with hb
  set c := rotConj ψ x 2 (d.g₁ ^ e 3 * d.g₂ ^ e 4) with hc
  have hprod2 : b * (c * a) = 1 := by
    calc b * (c * a) = a⁻¹ * (a * (b * c)) * a := by group
      _ = 1 := by rw [hprod]; group
  have hprod3 : c * (a * b) = 1 := by
    calc c * (a * b) = (a * b)⁻¹ * (a * (b * c)) * (a * b) := by group
      _ = 1 := by rw [hprod]; group
  have hA : (d.g₁ * d.g₂ ^ 2) ^ e 0 ∈ Subgroup.center S := by
    refine mem_center_of_forall_commute (rotConj_injective h.inj x 0) fun s' => ?_
    have hyb : Commute (rotConj ψ x 0 s') b :=
      h.cross_commute (by norm_num) (by norm_num) (by norm_num) s' _
    have hyc : Commute (rotConj ψ x 0 s') c :=
      h.cross_commute (by norm_num) (by norm_num) (by norm_num) s' _
    exact (commute_of_mul_mul_eq_one hprod hyb hyc).symm.eq
  have hB : d.g₁ ^ e 1 * d.g₂ ^ e 2 ∈ Subgroup.center S := by
    refine mem_center_of_forall_commute (rotConj_injective h.inj x 1) fun s' => ?_
    have hyc : Commute (rotConj ψ x 1 s') c :=
      h.cross_commute (by norm_num) (by norm_num) (by norm_num) s' _
    have hya : Commute (rotConj ψ x 1 s') a :=
      h.cross_commute (by norm_num) (by norm_num) (by norm_num) s' _
    exact (commute_of_mul_mul_eq_one hprod2 hyc hya).symm.eq
  have hC : d.g₁ ^ e 3 * d.g₂ ^ e 4 ∈ Subgroup.center S := by
    refine mem_center_of_forall_commute (rotConj_injective h.inj x 2) fun s' => ?_
    have hya : Commute (rotConj ψ x 2 s') a :=
      h.cross_commute (by norm_num) (by norm_num) (by norm_num) s' _
    have hyb : Commute (rotConj ψ x 2 s') b :=
      h.cross_commute (by norm_num) (by norm_num) (by norm_num) s' _
    exact (commute_of_mul_mul_eq_one hprod3 hya hyb).symm.eq
  rw [zpow_u] at hA
  fin_cases i
  · exact (d.g_indep _ _ hA).1
  · exact (d.g_indep _ _ hB).1
  · exact (d.g_indep _ _ hB).2
  · exact (d.g_indep _ _ hC).1
  · exact (d.g_indep _ _ hC).2

theorem rotGen_commute_t (d : RotData S) (i : Fin 5) :
    rotGen d ψ x i * ψ d.t = ψ d.t * rotGen d ψ x i := by
  by_cases h0 : rotComp i = 0
  · have hi : i = 0 := by
      fin_cases i <;> simp [rotComp] at h0 ⊢
    subst hi
    simp only [rotGen, rotComp, rotElt, Matrix.cons_val_zero, rotConj_zero]
    rw [← map_mul, ← map_mul, d.t_comm]
  · have := h.cross_commute (rotComp_lt i) (by norm_num : 0 < 3) h0 (rotElt d i) d.t
    simpa [rotGen, rotConj_zero] using this

theorem closure_rotGen_le_centralizer (d : RotData S) :
    Subgroup.closure (Set.range (rotGen d ψ x)) ≤ Subgroup.centralizer ({ψ d.t} : Set X) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact h.rotGen_commute_t d i

theorem closure_rotGen_commute (d : RotData S) :
    ∀ a ∈ Subgroup.closure (Set.range (rotGen d ψ x)), ∀ b ∈ Subgroup.closure
      (Set.range (rotGen d ψ x)), a * b = b * a := by
  apply closure_commute
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact h.rotGen_commute d i j

end RotSetup

theorem isPGroup_two_zpowers {g : X} (hg1 : g ≠ 1) (hg2 : g ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  have h2 : orderOf g = 2 := orderOf_eq_prime hg2 hg1
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, h2, pow_one]

theorem mem_normalizer_zpowers_of_commute {g f : X} (hf : f * g = g * f) :
    f ∈ Subgroup.normalizer ((Subgroup.zpowers g : Subgroup X) : Set X) := by
  refine Subgroup.centralizer_le_normalizer ((Subgroup.zpowers g : Subgroup X) : Set X) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact ((Commute.zpow_left (show Commute g f from hf.symm) n)).eq

def rotZ (ψ : S →* X) (x : X) (i : ℕ) : Subgroup X := (Subgroup.center S).map (rotConj ψ x i)

def rotZz (ψ : S →* X) (x : X) : Subgroup X :=
  Subgroup.closure (⋃ i : Fin 3, (rotZ ψ x i : Set X))

theorem mem_rotZ {ψ : S →* X} {x : X} {i : ℕ} {a : X} :
    a ∈ rotZ ψ x i ↔ ∃ c ∈ Subgroup.center S, rotConj ψ x i c = a := Subgroup.mem_map

theorem rotZ_le_rotZz (ψ : S →* X) (x : X) (i : Fin 3) : rotZ ψ x i ≤ rotZz ψ x :=
  fun _ ha => Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, ha⟩)

theorem rotConj_succ_conj (ψ : S →* X) (x : X) (i : ℕ) (s : S) :
    x⁻¹ * rotConj ψ x i s * x = rotConj ψ x (i + 1) s := by
  simp only [rotConj_apply, pow_succ, mul_inv_rev]
  group

theorem rotConj_three (ψ : S →* X) {x : X} (hx3 : x ^ 3 = 1) (s : S) :
    rotConj ψ x 3 s = rotConj ψ x 0 s := by
  simp [rotConj_apply, hx3]

namespace RotSetup

variable {B L : Subgroup X} {x : X} {ψ : S →* X} (h : RotSetup B L x ψ)

include h

theorem rotZ_commute {i j : ℕ} (hi : i < 3) (hj : j < 3) {a b : X} (ha : a ∈ rotZ ψ x i)
    (hb : b ∈ rotZ ψ x j) : a * b = b * a := by
  obtain ⟨c, hc, rfl⟩ := mem_rotZ.1 ha
  obtain ⟨c', hc', rfl⟩ := mem_rotZ.1 hb
  by_cases hij : i = j
  · subst hij
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hc c']
  · exact h.cross_commute hi hj hij c c'

theorem rotZz_commute : ∀ a ∈ rotZz ψ x, ∀ b ∈ rotZz ψ x, a * b = b * a := by
  apply closure_commute
  intro a ha b hb
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hb
  exact h.rotZ_commute i.2 j.2 hi hj

theorem rotZz_conj_mem {a : X} (ha : a ∈ rotZz ψ x) : x⁻¹ * a * x ∈ rotZz ψ x := by
  have hx3 := h.x_cube
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
    obtain ⟨c, hc, rfl⟩ := mem_rotZ.1 hi
    rw [rotConj_succ_conj]
    fin_cases i
    · exact rotZ_le_rotZz ψ x 1 (mem_rotZ.2 ⟨c, hc, rfl⟩)
    · exact rotZ_le_rotZz ψ x 2 (mem_rotZ.2 ⟨c, hc, rfl⟩)
    · exact rotZ_le_rotZz ψ x 0 (mem_rotZ.2 ⟨c, hc, by
        simpa using (rotConj_three ψ hx3 c).symm⟩)
  | one => simpa using (rotZz ψ x).one_mem
  | mul a b ha hb iha ihb =>
    have : x⁻¹ * (a * b) * x = (x⁻¹ * a * x) * (x⁻¹ * b * x) := by group
    rw [this]
    exact (rotZz ψ x).mul_mem iha ihb
  | inv a ha iha =>
    have : x⁻¹ * a⁻¹ * x = (x⁻¹ * a * x)⁻¹ := by group
    rw [this]
    exact (rotZz ψ x).inv_mem iha

end RotSetup

theorem eps_mul {G : Type*} [Group G] {p q p' q' : G} (hpq : p * q = q * p)
    (hp'q : p' * q = q * p') : (p * q)⁻¹ * (p' * q') = (p⁻¹ * p') * (q⁻¹ * q') := by
  have h1 : Commute q p := hpq.symm
  have h2 : Commute q p' := hp'q.symm
  have h3 : Commute q⁻¹ (p⁻¹ * p') := (h1.inv_inv).mul_right h2.inv_left
  calc (p * q)⁻¹ * (p' * q') = q⁻¹ * (p⁻¹ * p') * q' := by group
    _ = (p⁻¹ * p') * q⁻¹ * q' := by rw [h3.eq]
    _ = (p⁻¹ * p') * (q⁻¹ * q') := by group

namespace RotSetup

variable {B L : Subgroup X} {x : X} {ψ : S →* X} (h : RotSetup B L x ψ)

include h

theorem rotZz_gen {a : X} (ha : a ∈ rotZz ψ x) :
    ∃ z ∈ rotZ ψ x 0, ∃ d ∈ rotZz ψ x, a = z * (d⁻¹ * (x⁻¹ * d * x)) := by
  have hcomm := h.rotZz_commute
  have hinv : ∀ a ∈ rotZz ψ x, x⁻¹ * a * x ∈ rotZz ψ x := fun a ha => h.rotZz_conj_mem ha
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
    obtain ⟨c, hc, rfl⟩ := mem_rotZ.1 hi
    have hz : rotConj ψ x 0 c ∈ rotZ ψ x 0 := mem_rotZ.2 ⟨c, hc, rfl⟩
    have hz1 : x⁻¹ * rotConj ψ x 0 c * x = rotConj ψ x 1 c := rotConj_succ_conj ψ x 0 c
    have hz2 : x⁻¹ * rotConj ψ x 1 c * x = rotConj ψ x 2 c := rotConj_succ_conj ψ x 1 c
    have hz1m : rotConj ψ x 1 c ∈ rotZz ψ x := rotZ_le_rotZz ψ x 1 (mem_rotZ.2 ⟨c, hc, rfl⟩)
    have hz0m : rotConj ψ x 0 c ∈ rotZz ψ x := rotZ_le_rotZz ψ x 0 hz
    fin_cases i
    · exact ⟨_, hi, 1, (rotZz ψ x).one_mem, by group⟩
    · refine ⟨_, hz, _, hz0m, ?_⟩
      simp only [Fin.mk_one, Fin.val_one] 
      rw [hz1]
      group
    · refine ⟨_, hz, rotConj ψ x 0 c * rotConj ψ x 1 c, (rotZz ψ x).mul_mem hz0m hz1m, ?_⟩
      have hcz : rotConj ψ x 0 c * rotConj ψ x 1 c = rotConj ψ x 1 c * rotConj ψ x 0 c :=
        hcomm _ hz0m _ hz1m
      have e1 : x⁻¹ * (rotConj ψ x 0 c * rotConj ψ x 1 c) * x =
          rotConj ψ x 1 c * rotConj ψ x 2 c := by
        calc x⁻¹ * (rotConj ψ x 0 c * rotConj ψ x 1 c) * x
            = (x⁻¹ * rotConj ψ x 0 c * x) * (x⁻¹ * rotConj ψ x 1 c * x) := by group
          _ = _ := by rw [hz1, hz2]
      simp only [Fin.reduceFinMk]
      rw [e1, mul_inv_rev]
      have hc' : Commute (rotConj ψ x 1 c)⁻¹ (rotConj ψ x 0 c)⁻¹ :=
        (Commute.inv_inv (show Commute (rotConj ψ x 1 c) (rotConj ψ x 0 c) from hcz.symm))
      calc rotConj ψ x 2 c = rotConj ψ x 0 c * ((rotConj ψ x 0 c)⁻¹ *
            ((rotConj ψ x 1 c)⁻¹ * (rotConj ψ x 1 c)) * rotConj ψ x 2 c) := by group
        _ = rotConj ψ x 0 c * ((rotConj ψ x 1 c)⁻¹ * (rotConj ψ x 0 c)⁻¹ *
            (rotConj ψ x 1 c * rotConj ψ x 2 c)) := by
          rw [hc'.eq]; group
  | one => exact ⟨1, (rotZ ψ x 0).one_mem, 1, (rotZz ψ x).one_mem, by group⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨z₁, hz₁, d₁, hd₁, rfl⟩ := iha
    obtain ⟨z₂, hz₂, d₂, hd₂, rfl⟩ := ihb
    refine ⟨z₁ * z₂, (rotZ ψ x 0).mul_mem hz₁ hz₂, d₁ * d₂, (rotZz ψ x).mul_mem hd₁ hd₂, ?_⟩
    have e : x⁻¹ * (d₁ * d₂) * x = (x⁻¹ * d₁ * x) * (x⁻¹ * d₂ * x) := by group
    rw [e, eps_mul (hcomm _ hd₁ _ hd₂) (hcomm _ (hinv _ hd₁) _ hd₂)]
    have hε₁ : d₁⁻¹ * (x⁻¹ * d₁ * x) ∈ rotZz ψ x :=
      (rotZz ψ x).mul_mem ((rotZz ψ x).inv_mem hd₁) (hinv _ hd₁)
    have hz₂m : z₂ ∈ rotZz ψ x := rotZ_le_rotZz ψ x 0 hz₂
    have := hcomm _ hε₁ _ hz₂m
    calc z₁ * (d₁⁻¹ * (x⁻¹ * d₁ * x)) * (z₂ * (d₂⁻¹ * (x⁻¹ * d₂ * x)))
        = z₁ * ((d₁⁻¹ * (x⁻¹ * d₁ * x)) * z₂) * (d₂⁻¹ * (x⁻¹ * d₂ * x)) := by group
      _ = z₁ * (z₂ * (d₁⁻¹ * (x⁻¹ * d₁ * x))) * (d₂⁻¹ * (x⁻¹ * d₂ * x)) := by rw [this]
      _ = z₁ * z₂ * ((d₁⁻¹ * (x⁻¹ * d₁ * x)) * (d₂⁻¹ * (x⁻¹ * d₂ * x))) := by group
  | inv a ha iha =>
    obtain ⟨z, hz, d, hd, rfl⟩ := iha
    refine ⟨z⁻¹, (rotZ ψ x 0).inv_mem hz, d⁻¹, (rotZz ψ x).inv_mem hd, ?_⟩
    have hdd : d * (x⁻¹ * d * x) = (x⁻¹ * d * x) * d := hcomm _ hd _ (hinv _ hd)
    have hzm : z ∈ rotZz ψ x := rotZ_le_rotZz ψ x 0 hz
    have hε : d⁻¹ * (x⁻¹ * d * x) ∈ rotZz ψ x :=
      (rotZz ψ x).mul_mem ((rotZz ψ x).inv_mem hd) (hinv _ hd)
    have hzε := hcomm _ hzm _ hε
    have hε' : (d⁻¹ * (x⁻¹ * d * x))⁻¹ = (d⁻¹)⁻¹ * (x⁻¹ * d⁻¹ * x) := by
      have hc : Commute d (x⁻¹ * d * x) := hdd
      calc (d⁻¹ * (x⁻¹ * d * x))⁻¹ = (x⁻¹ * d * x)⁻¹ * d := by group
        _ = d * (x⁻¹ * d * x)⁻¹ := hc.inv_right.eq.symm
        _ = _ := by group
    calc (z * (d⁻¹ * (x⁻¹ * d * x)))⁻¹ = (d⁻¹ * (x⁻¹ * d * x))⁻¹ * z⁻¹ := by group
      _ = z⁻¹ * (d⁻¹ * (x⁻¹ * d * x))⁻¹ := by
        have : Commute z (d⁻¹ * (x⁻¹ * d * x)) := hzε
        exact this.inv_inv.eq.symm
      _ = z⁻¹ * ((d⁻¹)⁻¹ * (x⁻¹ * d⁻¹ * x)) := by rw [hε']

theorem rotZ_card_le (d : RotData S) : Nat.card (rotZ ψ x 0) ≤ 3 := by
  rw [rotZ, Subgroup.card_map_of_injective (rotConj_injective h.inj x 0)]
  exact d.center_card

def rotProd : S × (S × S) →* X :=
  (rotConj ψ x 0).noncommCoprod
    ((rotConj ψ x 1).noncommCoprod (rotConj ψ x 2)
      (fun a b => (h.cross_commute (by norm_num) (by norm_num) (by norm_num) a b : _)))
    (fun a bc => by
      obtain ⟨b, c⟩ := bc
      exact (Commute.mul_right
        (show Commute (rotConj ψ x 0 a) (rotConj ψ x 1 b) from
          h.cross_commute (by norm_num) (by norm_num) (by norm_num) a b)
        (show Commute (rotConj ψ x 0 a) (rotConj ψ x 2 c) from
          h.cross_commute (by norm_num) (by norm_num) (by norm_num) a c)))

theorem rotProd_apply (s₀ s₁ s₂ : S) :
    rotProd h (s₀, (s₁, s₂)) = rotConj ψ x 0 s₀ * (rotConj ψ x 1 s₁ * rotConj ψ x 2 s₂) := by
  rfl

theorem closure_rotGen_le_range (d : RotData S) :
    Subgroup.closure (Set.range (rotGen d ψ x)) ≤ (rotProd h).range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe]
  fin_cases i
  · exact ⟨(d.g₁ * d.g₂ ^ 2, (1, 1)), by simp [rotProd_apply, rotGen, rotComp, rotElt]⟩
  · exact ⟨(1, (d.g₁, 1)), by simp [rotProd_apply, rotGen, rotComp, rotElt]⟩
  · exact ⟨(1, (d.g₂, 1)), by simp [rotProd_apply, rotGen, rotComp, rotElt]⟩
  · exact ⟨(1, (1, d.g₁)), by simp [rotProd_apply, rotGen, rotComp, rotElt]⟩
  · exact ⟨(1, (1, d.g₂)), by simp [rotProd_apply, rotGen, rotComp, rotElt]⟩

end RotSetup

theorem commute_of_eq_mul_mul₁ {G : Type*} [Group G] {e a b c y : G} (he : e = a * (b * c))
    (hy : Commute y e) (hb : Commute y b) (hc : Commute y c) : Commute y a := by
  have : a = e * (b * c)⁻¹ := by rw [he]; group
  rw [this]
  exact hy.mul_right (hb.mul_right hc).inv_right

theorem commute_of_eq_mul_mul₂ {G : Type*} [Group G] {e a b c y : G} (he : e = a * (b * c))
    (hy : Commute y e) (ha : Commute y a) (hc : Commute y c) : Commute y b := by
  have : b = a⁻¹ * e * c⁻¹ := by rw [he]; group
  rw [this]
  exact (ha.inv_right.mul_right hy).mul_right hc.inv_right

theorem commute_of_eq_mul_mul₃ {G : Type*} [Group G] {e a b c y : G} (he : e = a * (b * c))
    (hy : Commute y e) (ha : Commute y a) (hb : Commute y b) : Commute y c := by
  have : c = (a * b)⁻¹ * e := by rw [he]; group
  rw [this]
  exact (ha.mul_right hb).inv_right.mul_right hy

namespace RotSetup

variable {B L : Subgroup X} {x : X} {ψ : S →* X} (h : RotSetup B L x ψ)

include h

theorem commute_Bc {e : X} (he : e ∈ i112Bc B L) {i : ℕ} (hi : i < 3) (s : S) :
    Commute (rotConj ψ x i s) e := by
  have hmem : rotConj ψ x i s ∈ i112J B L := by
    refine i112_le_J (L := L) (B.pow_mem h.xB i) ?_
    rw [← h.range]
    exact (mem_rotConj_range ψ x i _).2 ⟨s, rfl⟩
  exact Subgroup.mem_centralizer_iff.1 he.2 _ hmem

theorem inf_Bc_le (d : RotData S) {E : Subgroup X}
    (hE : E ≤ Subgroup.closure (Set.range (rotGen d ψ x))) :
    E ⊓ i112Bc B L ≤ rotZz ψ x ⊓ Subgroup.centralizer ({x} : Set X) := by
  intro e he
  obtain ⟨heE, heBc⟩ := he
  obtain ⟨⟨s₀, s₁, s₂⟩, hs⟩ := h.closure_rotGen_le_range d (hE heE)
  have he' : e = rotConj ψ x 0 s₀ * (rotConj ψ x 1 s₁ * rotConj ψ x 2 s₂) := by
    rw [← hs, rotProd_apply]
  have hy : ∀ i : ℕ, i < 3 → ∀ s' : S, Commute (rotConj ψ x i s') e := fun i hi s' =>
    h.commute_Bc heBc hi s'
  have hc01 := fun s' => h.cross_commute (i := 0) (j := 1) (by norm_num) (by norm_num)
    (by norm_num) s'
  have hc02 := fun s' => h.cross_commute (i := 0) (j := 2) (by norm_num) (by norm_num)
    (by norm_num) s'
  have hc10 := fun s' => h.cross_commute (i := 1) (j := 0) (by norm_num) (by norm_num)
    (by norm_num) s'
  have hc12 := fun s' => h.cross_commute (i := 1) (j := 2) (by norm_num) (by norm_num)
    (by norm_num) s'
  have hc20 := fun s' => h.cross_commute (i := 2) (j := 0) (by norm_num) (by norm_num)
    (by norm_num) s'
  have hc21 := fun s' => h.cross_commute (i := 2) (j := 1) (by norm_num) (by norm_num)
    (by norm_num) s'
  have h0 : rotConj ψ x 0 s₀ ∈ rotZ ψ x 0 := by
    refine mem_rotZ.2 ⟨s₀, ?_, rfl⟩
    refine mem_center_of_forall_commute (rotConj_injective h.inj x 0) fun s' => ?_
    exact (commute_of_eq_mul_mul₁ he' (hy 0 (by norm_num) s') (hc01 s' _) (hc02 s' _)).symm.eq
  have h1 : rotConj ψ x 1 s₁ ∈ rotZ ψ x 1 := by
    refine mem_rotZ.2 ⟨s₁, ?_, rfl⟩
    refine mem_center_of_forall_commute (rotConj_injective h.inj x 1) fun s' => ?_
    exact (commute_of_eq_mul_mul₂ he' (hy 1 (by norm_num) s') (hc10 s' _) (hc12 s' _)).symm.eq
  have h2 : rotConj ψ x 2 s₂ ∈ rotZ ψ x 2 := by
    refine mem_rotZ.2 ⟨s₂, ?_, rfl⟩
    refine mem_center_of_forall_commute (rotConj_injective h.inj x 2) fun s' => ?_
    exact (commute_of_eq_mul_mul₃ he' (hy 2 (by norm_num) s') (hc20 s' _) (hc21 s' _)).symm.eq
  refine ⟨?_, ?_⟩
  · rw [he']
    exact (rotZz ψ x).mul_mem (rotZ_le_rotZz ψ x 0 h0)
      ((rotZz ψ x).mul_mem (rotZ_le_rotZz ψ x 1 h1) (rotZ_le_rotZz ψ x 2 h2))
  · show e ∈ Subgroup.centralizer ({x} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (i116pI_comm h.elem h.xB heBc.1).symm

theorem card_inf_Bc_le (d : RotData S) {E : Subgroup X}
    (hE : E ≤ Subgroup.closure (Set.range (rotGen d ψ x))) :
    Nat.card ↥(E ⊓ i112Bc B L) ≤ 3 := by
  have h1 := Subgroup.card_le_of_le (h.inf_Bc_le d hE)
  have h2 := card_inf_centralizer_le x (rotZz ψ x) (rotZ ψ x 0) h.rotZz_commute
    (fun a ha => h.rotZz_conj_mem ha) (fun a ha => h.rotZz_gen ha)
  exact h1.trans (h2.trans (h.rotZ_card_le d))

theorem closure_rotGen_commute_Bc (d : RotData S) :
    ∀ a ∈ Subgroup.closure (Set.range (rotGen d ψ x)), ∀ b ∈ i112Bc B L, a * b = b * a := by
  intro a ha b hb
  have : Subgroup.closure (Set.range (rotGen d ψ x)) ≤ Subgroup.centralizer ({b} : Set X) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (h.commute_Bc hb (rotComp_lt i) (rotElt d i)).symm.eq.symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (this ha)

theorem isElemAbelian_of_le_closure (d : RotData S) {E : Subgroup X}
    (hE : E ≤ Subgroup.closure (Set.range (rotGen d ψ x))) (hE3 : ∀ g ∈ E, g ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 E :=
  ⟨⟨⟨fun a b => Subtype.ext (h.closure_rotGen_commute d a (hE a.2) b (hE b.2))⟩⟩, hE3⟩

end RotSetup

theorem int_mod_three_of_dvd_pow (k : ℤ) (h : (3 : ℤ) ∣ k ^ 3 - 1) : k % 3 = 1 := by
  have h1 : ((k : ZMod 3)) ^ 3 = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k ^ 3 - 1) 3).2 h
    push_cast at this
    exact sub_eq_zero.1 this
  have h2 : (k : ZMod 3) = 1 := by
    generalize (k : ZMod 3) = a at h1
    revert a
    decide
  have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 k 3).1 (by simpa using h2.symm)
  omega

theorem mod_three_of_pow_three (d : RotData S) (φ : MulAut S) (k : ℤ) (hk₁ : φ d.g₁ = d.g₁ ^ k)
    (hφ3 : ∀ s, φ (φ (φ s)) = s) : k % 3 = 1 := by
  have hpow : ∀ n : ℤ, φ (d.g₁ ^ n) = d.g₁ ^ (k * n) := fun n => by
    rw [map_zpow, hk₁, ← zpow_mul]
  have h1 : φ (φ (φ d.g₁)) = d.g₁ ^ (k * (k * k)) := by
    rw [hk₁, hpow, hpow]
  have h2 : d.g₁ ^ (k ^ 3 - 1) = 1 := by
    rw [zpow_sub_one, show k ^ 3 = k * (k * k) by ring, ← h1, hφ3]
    group
  have h3 : d.g₁ ^ (k ^ 3 - 1) * d.g₂ ^ (0 : ℤ) ∈ Subgroup.center S := by
    rw [zpow_zero, mul_one, h2]
    exact (Subgroup.center S).one_mem
  exact int_mod_three_of_dvd_pow k (d.g_indep _ _ h3).1

namespace RotSetup

variable {B L : Subgroup X} {x : X} {ψ : S →* X} (h : RotSetup B L x ψ)

include h

theorem conj_rotConj {y : X} (hyB : y ∈ B) (φ : MulAut S)
    (hy : ∀ s : S, y * ψ s * y⁻¹ = ψ (φ s)) (i : ℕ) (s : S) :
    y * rotConj ψ x i s * y⁻¹ = rotConj ψ x i (φ s) := by
  have hcomm : Commute y (x ^ i) := i116pI_comm h.elem hyB (B.pow_mem h.xB i)
  have h1 : y * (x ^ i)⁻¹ = (x ^ i)⁻¹ * y := hcomm.inv_right.eq
  have h2 : x ^ i * y⁻¹ = y⁻¹ * x ^ i := hcomm.symm.inv_right.eq
  rw [rotConj_apply, rotConj_apply, ← hy]
  calc y * ((x ^ i)⁻¹ * ψ s * x ^ i) * y⁻¹ = (y * (x ^ i)⁻¹) * ψ s * (x ^ i * y⁻¹) := by group
    _ = ((x ^ i)⁻¹ * y) * ψ s * (y⁻¹ * x ^ i) := by rw [h1, h2]
    _ = (x ^ i)⁻¹ * (y * ψ s * y⁻¹) * x ^ i := by group

end RotSetup

theorem phi_rotElt (d : RotData S) (φ : MulAut S) (k : ℤ) (hk₁ : φ d.g₁ = d.g₁ ^ k)
    (hk₂ : φ d.g₂ = d.g₂ ^ k) (i : Fin 5) : φ (rotElt d i) = rotElt d i ^ k := by
  fin_cases i
  · simp only [rotElt, Fin.zero_eta, Matrix.cons_val_zero]
    rw [map_mul, map_pow, hk₁, hk₂, zpow_u, ← zpow_natCast, ← zpow_mul]
    congr 2
    push_cast
    ring
  all_goals simp [rotElt, hk₁, hk₂]

namespace RotSetup

variable {B L : Subgroup X} {x : X} {ψ : S →* X} (h : RotSetup B L x ψ)

include h

theorem gen_action (d : RotData S) {y : X} (hyB : y ∈ B) (φ : MulAut S)
    (hy : ∀ s : S, y * ψ s * y⁻¹ = ψ (φ s)) (k : ℤ) (hk₁ : φ d.g₁ = d.g₁ ^ k)
    (hk₂ : φ d.g₂ = d.g₂ ^ k) (i : Fin 5) :
    y * rotGen d ψ x i * y⁻¹ = rotGen d ψ x i ^ k := by
  rw [rotGen, h.conj_rotConj hyB φ hy, phi_rotElt d φ k hk₁ hk₂ i, map_zpow]

theorem closure_action (d : RotData S) {y : X} (hyB : y ∈ B) (φ : MulAut S)
    (hy : ∀ s : S, y * ψ s * y⁻¹ = ψ (φ s)) (k : ℤ) (hk₁ : φ d.g₁ = d.g₁ ^ k)
    (hk₂ : φ d.g₂ = d.g₂ ^ k) :
    ∀ r ∈ Subgroup.closure (Set.range (rotGen d ψ x)), y * r * y⁻¹ = r ^ k := by
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    exact h.gen_action d hyB φ hy k hk₁ hk₂ i
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab : Commute a b := h.closure_rotGen_commute d a ha b hb
    rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group, iha, ihb,
      hab.mul_zpow]
  | inv a ha iha =>
    rw [show y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ by group, iha, inv_zpow]

theorem E_commute_y (d : RotData S) {y : X} (hyB : y ∈ B) (φ : MulAut S)
    (hy : ∀ s : S, y * ψ s * y⁻¹ = ψ (φ s)) (k : ℤ) (hk₁ : φ d.g₁ = d.g₁ ^ k)
    (hk₂ : φ d.g₂ = d.g₂ ^ k) (hk3 : k % 3 = 1) {E : Subgroup X}
    (hE : E ≤ Subgroup.closure (Set.range (rotGen d ψ x))) (hE3 : ∀ g ∈ E, g ^ 3 = 1) :
    ∀ e ∈ E, e * y = y * e := by
  intro e he
  have h1 := h.closure_action d hyB φ hy k hk₁ hk₂ e (hE he)
  have h2 : e ^ k = e := by
    obtain ⟨m, hm⟩ : ∃ m, k = 3 * m + 1 := ⟨k / 3, by omega⟩
    rw [hm, zpow_add, zpow_mul, zpow_ofNat, hE3 e he, one_zpow, one_mul, zpow_one]
  rw [h2] at h1
  exact (mul_inv_eq_iff_eq_mul.1 h1).symm

theorem inner_of_mem_sup (d : RotData S) {E : Subgroup X}
    (hE : E ≤ Subgroup.closure (Set.range (rotGen d ψ x))) :
    ∀ f ∈ E ⊔ i112Bc B L, ∃ s : S, ∀ s' : S, f * ψ s' * f⁻¹ = ψ (s * s' * s⁻¹) := by
  intro f hf
  have hsup : E ⊔ i112Bc B L = Subgroup.closure ((E : Set X) ∪ (i112Bc B L : Set X)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hsup] at hf
  induction hf using Subgroup.closure_induction with
  | mem f hf =>
    rcases hf with hfE | hfB
    · obtain ⟨⟨s₀, s₁, s₂⟩, hs⟩ := h.closure_rotGen_le_range d (hE hfE)
      have hf' : f = rotConj ψ x 0 s₀ * (rotConj ψ x 1 s₁ * rotConj ψ x 2 s₂) := by
        rw [← hs, rotProd_apply]
      refine ⟨s₀, fun s' => ?_⟩
      have hm : Commute (rotConj ψ x 1 s₁ * rotConj ψ x 2 s₂) (rotConj ψ x 0 s') :=
        Commute.mul_left
          (show Commute (rotConj ψ x 1 s₁) (rotConj ψ x 0 s') from
            h.cross_commute (by norm_num) (by norm_num) (by norm_num) s₁ s')
          (show Commute (rotConj ψ x 2 s₂) (rotConj ψ x 0 s') from
            h.cross_commute (by norm_num) (by norm_num) (by norm_num) s₂ s')
      have hψ0 : ∀ s, rotConj ψ x 0 s = ψ s := fun s => by simp [rotConj_apply]
      rw [hf', ← hψ0 s', ← hψ0 (s₀ * s' * s₀⁻¹), map_mul, map_mul, map_inv]
      calc rotConj ψ x 0 s₀ * (rotConj ψ x 1 s₁ * rotConj ψ x 2 s₂) * rotConj ψ x 0 s' *
            (rotConj ψ x 0 s₀ * (rotConj ψ x 1 s₁ * rotConj ψ x 2 s₂))⁻¹
          = rotConj ψ x 0 s₀ * ((rotConj ψ x 1 s₁ * rotConj ψ x 2 s₂) * rotConj ψ x 0 s' *
              (rotConj ψ x 1 s₁ * rotConj ψ x 2 s₂)⁻¹) * (rotConj ψ x 0 s₀)⁻¹ := by group
        _ = rotConj ψ x 0 s₀ * rotConj ψ x 0 s' * (rotConj ψ x 0 s₀)⁻¹ := by
          rw [mul_inv_eq_iff_eq_mul.2 hm.eq]
    · refine ⟨1, fun s' => ?_⟩
      have := h.commute_Bc hfB (i := 0) (by norm_num) s'
      rw [rotConj_zero] at this
      simp only [map_one, one_mul, inv_one, mul_one]
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm.eq
  | one => exact ⟨1, fun s' => by simp⟩
  | mul f g hf hg ihf ihg =>
    obtain ⟨s₁, hs₁⟩ := ihf
    obtain ⟨s₂, hs₂⟩ := ihg
    refine ⟨s₁ * s₂, fun s' => ?_⟩
    have : f * g * ψ s' * (f * g)⁻¹ = f * (g * ψ s' * g⁻¹) * f⁻¹ := by group
    rw [this, hs₂, hs₁]
    congr 1
    group
  | inv f hf ihf =>
    obtain ⟨s, hs⟩ := ihf
    refine ⟨s⁻¹, fun s' => ?_⟩
    have h1 := hs (s⁻¹ * s' * s)
    have h2 : s * (s⁻¹ * s' * s) * s⁻¹ = s' := by group
    rw [h2] at h1
    have h3 : f⁻¹ * ψ s' * f = ψ (s⁻¹ * s' * s) := by
      rw [← h1]; group
    rw [inv_inv, h3, inv_inv]

end RotSetup

theorem rot_core (d : RotData S) {B L : Subgroup X} {x : X} {ψ : S →* X}
    (h : RotSetup B L x ψ) :
    ∃ E : Subgroup X, (∀ g ∈ E, g ^ 3 = 1) ∧ E ≤ Subgroup.closure (Set.range (rotGen d ψ x)) ∧
      CFSG.Open.IsElemAbelian 3 (E ⊔ i112Bc B L) ∧
      E ⊔ i112Bc B L ≤ Subgroup.normalizer ((Subgroup.zpowers (ψ d.t) : Subgroup X) : Set X) ∧
      3 ^ (CFSG.Open.pRank 3 (i112Bc B L) + 4) ≤ Nat.card ↥(E ⊔ i112Bc B L) := by
  obtain ⟨E, hE3, hEcl, hEcard⟩ :=
    exists_elemAbelian_of_commute (rotGen d ψ x) (h.rotGen_commute d) (h.rotGen_rel d)
  have hEel : CFSG.Open.IsElemAbelian 3 E := h.isElemAbelian_of_le_closure d hEcl hE3
  have hBcel : CFSG.Open.IsElemAbelian 3 (i112Bc B L) := isElemAbelian_of_le h.elem i112Bc_le_B
  have hc : ∀ a ∈ E, ∀ b ∈ i112Bc B L, a * b = b * a := fun a ha b hb =>
    h.closure_rotGen_commute_Bc d a (hEcl ha) b hb
  obtain ⟨b, hb⟩ := exists_card_eq_of_isElemAbelian Nat.prime_three hBcel
  have hrk : CFSG.Open.pRank 3 (i112Bc B L) = b := pRank_eq_of_card (by norm_num : 1 < 3) hBcel hb
  have hW : CFSG.Open.pRank 3 (E ⊓ i112Bc B L) ≤ 1 := by
    refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 3) fun E' hE' _ => ?_
    calc Nat.card E' ≤ Nat.card ↥(E ⊓ i112Bc B L) := Subgroup.card_le_of_le hE'
      _ ≤ 3 := h.card_inf_Bc_le d hEcl
      _ = 3 ^ 1 := by norm_num
  obtain ⟨hFel, hcard⟩ := card_mul_le_card_sup_mul_pow Nat.prime_three hEel hBcel hc le_rfl hW
  refine ⟨E, hE3, hEcl, hFel, ?_, ?_⟩
  · refine sup_le (fun e he => ?_) (fun e he => ?_)
    · refine mem_normalizer_zpowers_of_commute ?_
      have := h.closure_rotGen_le_centralizer d (hEcl he)
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    · refine mem_normalizer_zpowers_of_commute ?_
      have := h.commute_Bc he (i := 0) (by norm_num) d.t
      rw [rotConj_zero] at this
      exact this.symm.eq
  · rw [hrk]
    have h1 : 3 ^ (b + 4) * 3 ≤ Nat.card ↥(E ⊔ i112Bc B L) * 3 := by
      calc 3 ^ (b + 4) * 3 = 3 ^ 5 * 3 ^ b := by ring
        _ ≤ Nat.card E * Nat.card (i112Bc B L) := Nat.mul_le_mul hEcard hb.ge
        _ ≤ Nat.card ↥(E ⊔ i112Bc B L) * 3 ^ 1 := hcard
        _ = Nat.card ↥(E ⊔ i112Bc B L) * 3 := by norm_num
    exact Nat.le_of_mul_le_mul_right h1 (by norm_num)

theorem rot_rank_four (d : RotData S) {B L : Subgroup X} (hB : CFSG.Open.IsElemAbelian 3 B)
    (hLc : CFSG.Open.IsComponentOf L ⊤) {x : X} (hxB : x ∈ B)
    (hxn : x ∉ Subgroup.normalizer (L : Set X)) (ψ : S →* X) (hψ : Function.Injective ψ)
    (hψL : ψ.range = L) :
    ∃ F T : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T ∧ CFSG.Open.IsElemAbelian 3 F ∧
      F ≤ Subgroup.normalizer (T : Set X) ∧
      3 ^ (CFSG.Open.pRank 3 (i112Bc B L) + 4) ≤ Nat.card F := by
  have h : RotSetup B L x ψ := ⟨hB, hLc, hxB, hxn, hψ, hψL⟩
  obtain ⟨E, -, -, hFel, hFN, hFcard⟩ := rot_core d h
  have ht1 : ψ d.t ≠ 1 := by
    intro h1
    apply d.t_not_central
    have : d.t = 1 := hψ (by rw [h1, map_one])
    rw [this]
    exact (Subgroup.center S).one_mem
  have ht2 : (ψ d.t) ^ 2 = 1 := by rw [← map_pow, d.t_sq, map_one]
  refine ⟨E ⊔ i112Bc B L, Subgroup.zpowers (ψ d.t), ?_, isPGroup_two_zpowers ht1 ht2, hFel, hFN,
    hFcard⟩
  rw [Ne, Subgroup.zpowers_eq_bot]
  exact ht1

theorem rot_rank_five (d : RotData S) {B L : Subgroup X} (hB : CFSG.Open.IsElemAbelian 3 B)
    (hLc : CFSG.Open.IsComponentOf L ⊤) {x : X} (hxB : x ∈ B)
    (hxn : x ∉ Subgroup.normalizer (L : Set X)) (ψ : S →* X) (hψ : Function.Injective ψ)
    (hψL : ψ.range = L) {y : X} (hyB : y ∈ B) (φ : MulAut S)
    (hy : ∀ s : S, y * ψ s * y⁻¹ = ψ (φ s)) (k : ℤ) (hk₁ : φ d.g₁ = d.g₁ ^ k)
    (hk₂ : φ d.g₂ = d.g₂ ^ k) (hkt : φ d.t = d.t) (hnin : ∀ s : S, φ ≠ MulAut.conj s) :
    ∃ F T : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T ∧ CFSG.Open.IsElemAbelian 3 F ∧
      F ≤ Subgroup.normalizer (T : Set X) ∧
      3 ^ (CFSG.Open.pRank 3 (i112Bc B L) + 5) ≤ Nat.card F := by
  have h : RotSetup B L x ψ := ⟨hB, hLc, hxB, hxn, hψ, hψL⟩
  obtain ⟨E, hE3, hEcl, hFel, hFN, hFcard⟩ := rot_core d h
  have hy3 : y ^ 3 = 1 := hB.2 y hyB
  have hφ3 : ∀ s, φ (φ (φ s)) = s := by
    intro s
    apply hψ
    calc ψ (φ (φ (φ s))) = y * ψ (φ (φ s)) * y⁻¹ := (hy (φ (φ s))).symm
      _ = y * (y * ψ (φ s) * y⁻¹) * y⁻¹ := by rw [hy (φ s)]
      _ = y * (y * (y * ψ s * y⁻¹) * y⁻¹) * y⁻¹ := by rw [hy s]
      _ = (y * y * y) * ψ s * (y * y * y)⁻¹ := by group
      _ = ψ s := by
        have e3 : y * y * y = 1 := by
          calc y * y * y = y ^ 3 := (pow_three' y).symm
            _ = 1 := hy3
        rw [e3]; group
  have hk3 := mod_three_of_pow_three d φ k hk₁ hφ3
  have hyc : ∀ e ∈ E, e * y = y * e := h.E_commute_y d hyB φ hy k hk₁ hk₂ hk3 hEcl hE3
  have hBy : ∀ b ∈ i112Bc B L, b * y = y * b := fun b hb =>
    i116pI_comm h.elem (i112Bc_le_B hb) hyB
  have hFy : ∀ f ∈ E ⊔ i112Bc B L, f * y = y * f := by
    intro f hf
    have : E ⊔ i112Bc B L ≤ Subgroup.centralizer ({y} : Set X) :=
      sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.2 (hyc e he))
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hBy b hb))
    exact Subgroup.mem_centralizer_singleton_iff.1 (this hf)
  have hyF : y ∉ E ⊔ i112Bc B L := by
    intro hyF
    obtain ⟨s, hs⟩ := h.inner_of_mem_sup d hEcl y hyF
    refine hnin s (MulEquiv.ext fun s' => hψ ?_)
    rw [← hy, hs]
    simp [MulAut.conj_apply]
  have hy1 : y ≠ 1 := fun h1 => hyF (h1 ▸ (E ⊔ i112Bc B L).one_mem)
  have hzp : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  have hdisj : Disjoint (E ⊔ i112Bc B L) (Subgroup.zpowers y) := by
    rw [disjoint_iff]
    have hdvd : Nat.card ↥((E ⊔ i112Bc B L) ⊓ Subgroup.zpowers y) ∣ 3 := by
      rw [← hzp]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge
        (inf_le_right : (E ⊔ i112Bc B L) ⊓ Subgroup.zpowers y ≤ _) (by rw [h1, hzp])
      exact hyF ((heq ▸ Subgroup.mem_zpowers y : y ∈ (E ⊔ i112Bc B L) ⊓ _).1)
  have hcomm : ∀ f ∈ E ⊔ i112Bc B L, ∀ z ∈ Subgroup.zpowers y, f * z = z * f := by
    intro f hf z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_right (show Commute f y from hFy f hf) n).eq
  have hcardF : Nat.card ↥(E ⊔ i112Bc B L ⊔ Subgroup.zpowers y) =
      Nat.card ↥(E ⊔ i112Bc B L) * 3 := by
    rw [card_sup_of_commute_of_disjoint hcomm hdisj, hzp]
  have ht1 : ψ d.t ≠ 1 := by
    intro h1
    apply d.t_not_central
    have : d.t = 1 := hψ (by rw [h1, map_one])
    rw [this]
    exact (Subgroup.center S).one_mem
  have ht2 : (ψ d.t) ^ 2 = 1 := by rw [← map_pow, d.t_sq, map_one]
  have hyt : y * ψ d.t = ψ d.t * y := by
    have := hy d.t
    rw [hkt] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  refine ⟨E ⊔ i112Bc B L ⊔ Subgroup.zpowers y, Subgroup.zpowers (ψ d.t), ?_,
    isPGroup_two_zpowers ht1 ht2, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact ht1
  · exact CFSG.Open.IsElemAbelian.sup_of_commute hFel (CFSG.Open.isElemAbelian_zpowers hy3) hcomm
  · refine sup_le hFN ?_
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_zpowers_of_commute hyt
  · rw [hcardF]
    calc 3 ^ (CFSG.Open.pRank 3 (i112Bc B L) + 5)
        = 3 ^ (CFSG.Open.pRank 3 (i112Bc B L) + 4) * 3 := by ring
      _ ≤ Nat.card ↥(E ⊔ i112Bc B L) * 3 := Nat.mul_le_mul_right 3 hFcard

end KSFourU
end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
